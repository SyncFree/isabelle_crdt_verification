theory MVregister
imports 
"../framework/induction"
"../framework/helper" 
"../framework/convergence" 
begin

datatype 'a updateArgs = Assign "'a list"

type_synonym 'a payload = "('a option \<times> versionVector) set"

definition incVersions :: "'a payload \<Rightarrow> replicaId \<Rightarrow> versionVector" where
"incVersions pl myId = (
    let V = snd ` pl;
        vv = supSet V in
        (incVV myId vv)
)"                            

definition assign :: "'a payload \<Rightarrow> replicaId \<Rightarrow> 'a list \<Rightarrow> 'a payload" where
"assign pl myId R = (if R=[] then pl else let V = incVersions pl myId in (Some ` set R) \<times> {V})"


fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"update (Assign R) r pl = (assign pl r R)"

fun getValue :: "unit \<Rightarrow> 'a payload \<Rightarrow> ('a \<times> versionVector )set" where
"getValue _ pl = {(x,v). (Some x, v) \<in> pl}"

definition compareSingle :: "('a option \<times> versionVector) \<Rightarrow> 'a payload \<Rightarrow> bool" where
"compareSingle x B = (case x of (a,v) \<Rightarrow> (\<exists>(b,w)\<in>B. v < w) \<or> (\<exists>(b,w)\<in>B. v=w \<and> a=b))"

definition compare :: "'a payload \<Rightarrow> 'a payload \<Rightarrow> bool" where
"compare A B = (\<forall>x\<in>A. compareSingle x B)"

definition merge :: "'a payload \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"merge A B = (
    let A' = {(x,V). (x,V)\<in>A \<and> (\<forall>(y, W)\<in>B. V \<parallel> W \<or> V \<ge> W)};
        B' = {(y, W). (y,W)\<in>B \<and> (\<forall>(x, V)\<in>A. W \<parallel> V \<or> W \<ge> V)} in
        A' \<union> B'
)"

definition mvRegister where
"mvRegister = \<lparr> 
      t_compare = compare,
      t_merge   = merge,
      t_initial = {(None, vvZero)},
      t_update  = update,
      t_query   = getValue       
  \<rparr>"


definition mvRegisterSpec :: "('a updateArgs, unit, ('a \<times> versionVector) set) crdtSpecification" where
"mvRegisterSpec H _ = 
   ({(x,c). (\<exists>r l v. x\<in>set l \<and> (v, Assign l)\<in>set(H r)
    \<and> (\<forall>rr. c\<guillemotright>rr = length (filter (\<lambda>e. updArgs e \<noteq> Assign [] \<and> updVersion e \<le> v ) (H rr)))
    \<and> \<not>(\<exists>l' vv. l' \<noteq> [] \<and> vv>v \<and> (vv, Assign l')\<in>allUpdates H))})"


definition noElementDominated where 
"noElementDominated S = (\<forall>(a,v)\<in>S. \<forall>(b,w)\<in>S. \<not> v<w)"

definition vvZeroIffNone where 
"vvZeroIffNone S = (\<forall>(a,v)\<in>S. v=vvZero \<longleftrightarrow> a=None)"

definition invariant where 
"invariant S = (
      S\<noteq>{}
    \<and> finite S
    \<and> vvZeroIffNone S
    \<and> noElementDominated S)"



lemma compareRefl: "compare A A"
by (auto simp add: compare_def compareSingle_def)

lemma compareTrans: "compare A B \<Longrightarrow> compare B C \<Longrightarrow> compare A C"
apply (auto simp add: compare_def compareSingle_def)
apply (case_tac " \<exists>(ba, y)\<in>B. b < y")
apply clarsimp
apply (subgoal_tac "(\<exists>(b, y)\<in>C. ba < y) \<or> (\<exists>(b, w)\<in>C. ba = w \<and> aa = b) ")
apply clarsimp
apply safe
apply (subgoal_tac "b < ba")
apply (metis (full_types) less_trans splitI)
apply force+
done




lemma noElementDominatedContradiction: 
  "\<lbrakk>noElementDominated A; (x, vx) \<in> A; vq < vx; (q, vq) \<in> A\<rbrakk> \<Longrightarrow> False"
by (auto simp add: noElementDominated_def)

lemma compareExistsSmaller:
"\<lbrakk>compare A B; (x,vx)\<in>A; (x,vx)\<notin>B\<rbrakk> \<Longrightarrow> \<exists>(q,vq)\<in>B. vx < vq"
apply (auto simp add: compare_def compareSingle_def)
done

lemma compareAntiSym1:
assumes "compare A B"
    and "compare B A"
    and "noElementDominated A"
    and "(x,vx) \<in> A"
shows "(x, vx) \<in> B"
proof (rule ccontr)
assume "(x, vx) \<notin> B"

have "\<exists>(q,vq)\<in>B. vx < vq" using `compare A B`  `(x, vx) \<in> A` `(x, vx) \<notin> B`  by (rule compareExistsSmaller)
from this obtain q vq where "(q,vq)\<in>B"  "vx < vq"  by force
  
then show "False" 
  proof cases
    assume "(q,vq)\<in>A"
    then show "False" using `(x, vx) \<in> A` `(q,vq)\<in>B`  `vx < vq` `noElementDominated A` by (metis noElementDominatedContradiction)
  next
    assume "(q,vq)\<notin>A"
    have "\<exists>(w,vw)\<in>A. vq < vw" using `compare B A`  `(q, vq) \<in> B` `(q, vq) \<notin> A`  by (rule compareExistsSmaller)
    from this obtain w vw where "(w,vw)\<in>A" "vq < vw" by force
    then have "vx < vw" using `vx < vq` `vq < vw` by (metis less_trans)
    then show "False" using `(w,vw)\<in>A` `(x,vx)\<in>A` `noElementDominated A` by (metis noElementDominatedContradiction)
  qed 
qed

lemma compareAntiSym:
assumes "compare A B"
    and "compare B A"
    and "noElementDominated A"
    and "noElementDominated B"
shows "A = B"
proof - 
  show "A = B" using assms by (auto simp add: compareAntiSym1)
qed

lemma compareAntiSymInv:
assumes "compare A B"
    and "compare B A"
    and "invariant A"
    and "invariant B"
shows "A = B"
proof - 
  show "A = B" using assms by (auto simp add: compareAntiSym invariant_def)
qed



definition removeSmallerElementsH :: "'a payload \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"removeSmallerElementsH xs ys = {x\<in>xs. \<forall>(y,w)\<in>ys. \<not>(snd x)<w}"

definition removeSmallerElements :: "'a payload \<Rightarrow> 'a payload" where
"removeSmallerElements xs = removeSmallerElementsH xs xs"

definition mergeAlt where
"mergeAlt A B = removeSmallerElements (A \<union> B)"

lemma removeSmallerElementsSplit1:"removeSmallerElements (xs \<union> ys) = (removeSmallerElementsH xs  (xs \<union> ys)) \<union> (removeSmallerElementsH ys  (xs \<union> ys))"
apply (unfold removeSmallerElements_def removeSmallerElementsH_def)
apply auto
done

lemma removeSmallerElementsHself2: "noElementDominated xs \<Longrightarrow> removeSmallerElementsH xs  (xs \<union> ys) = removeSmallerElementsH xs ys"
apply (unfold removeSmallerElementsH_def)
apply auto
by (metis noElementDominatedContradiction)


lemma removeSmallerElementsSplit2:"\<lbrakk>noElementDominated xs; noElementDominated ys\<rbrakk> \<Longrightarrow> 
  removeSmallerElements (xs \<union> ys) = (removeSmallerElementsH xs ys) \<union> (removeSmallerElementsH ys  xs)"
apply (subst removeSmallerElementsSplit1)
apply (subst removeSmallerElementsHself2)
apply assumption
apply (rule_tac t="xs \<union> ys" and s="ys \<union> xs" in ssubst)
apply (rule Un_commute)
apply (subst removeSmallerElementsHself2)
by auto

lemma mergeAltPart: "\<lbrakk>noElementDominated A; noElementDominated B \<rbrakk> \<Longrightarrow> 
    {(x,V). (x,V)\<in>A \<and> (\<forall>(y, W)\<in>B. V \<parallel> W \<or> V \<ge> W)} = removeSmallerElementsH A B"
apply (unfold removeSmallerElementsH_def)
apply auto
apply (metis (lifting) le_less splitD vvParallel vvParallel3)
by (metis split_conv vvParallel3)


lemma mergeAlt: "\<lbrakk>noElementDominated xs; noElementDominated ys\<rbrakk> \<Longrightarrow> merge xs ys = mergeAlt xs ys"
apply (unfold merge_def mergeAlt_def)
apply (simp add: Let_def)
apply (subst mergeAltPart)
apply assumption+
apply (subst mergeAltPart)
apply assumption+
apply (subst removeSmallerElementsSplit2)
apply simp_all
done



lemma merge_finite: "\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> finite (merge A B)"
by (auto simp add: merge_def)

lemma merge_nonempty_existsMax: "\<lbrakk>finite A; A\<noteq>{}\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. \<forall>y\<in>A. \<not>x<(y::versionVector)"
apply (induct A rule: finite_induct)
apply clarsimp
apply (case_tac "F={}")
apply clarsimp
apply clarsimp
by (metis less_trans)

lemma merge_nonempty_existsMax2: "\<lbrakk>finite A; A\<noteq>{}\<rbrakk> \<Longrightarrow> \<exists>(x,vx)\<in>A. \<forall>(y,vy)\<in>A. \<not>vx<(vy::versionVector)"
apply (subgoal_tac "\<exists>vx\<in>(snd`A). \<forall>vy\<in>(snd`A). \<not>vx<vy")
defer
apply (rule merge_nonempty_existsMax)
apply force+
done

lemma removeSmallerNonempty: "\<lbrakk>finite A; A\<noteq>{}\<rbrakk> \<Longrightarrow> removeSmallerElements A \<noteq> {}"
apply (frule(1) merge_nonempty_existsMax2)
apply (auto simp add: removeSmallerElements_def removeSmallerElementsH_def) 
done

lemma merge_nonempty: "\<lbrakk>A\<noteq>{};B \<noteq>{};finite A; finite B; noElementDominated A; noElementDominated B\<rbrakk> \<Longrightarrow> merge A B \<noteq> {}"
apply (unfold mergeAlt mergeAlt_def)
apply (rule removeSmallerNonempty)
apply force+
done

lemma mergeSubset: "merge A B \<subseteq> A \<union> B" 
by (auto simp add: merge_def)

lemma merge_vvZeroIffNone: "\<lbrakk>invariant A; invariant B\<rbrakk> \<Longrightarrow> vvZeroIffNone (merge A B)"
apply (unfold invariant_def)
apply clarsimp
apply (unfold  vvZeroIffNone_def)
by (metis Un_iff set_mp mergeSubset)



lemma removeSmallerNoDominated: "noElementDominated (removeSmallerElements A)"
apply (unfold noElementDominated_def removeSmallerElements_def removeSmallerElementsH_def)
apply auto
done

lemma merge_invariant: "\<lbrakk>invariant A; invariant B\<rbrakk> \<Longrightarrow> invariant (merge A B)"
apply (unfold invariant_def)
apply safe
apply (metis merge_nonempty)
apply (metis merge_finite)
apply (metis invariant_def merge_vvZeroIffNone)
apply (simp add: vvZeroIffNone_def mergeAlt mergeAlt_def)
by (metis removeSmallerNoDominated)


lemma merge_prop1: "\<lbrakk>invariant A; invariant B\<rbrakk> \<Longrightarrow> compare A (merge A B)"
apply (subst mergeAlt)
apply (simp add: invariant_def)
apply (simp add: invariant_def)
apply (unfold mergeAlt_def compare_def compareSingle_def)
apply (unfold removeSmallerElements_def removeSmallerElementsH_def)
apply auto
apply (drule_tac x="aa" in spec)
apply (drule_tac x="ba" in spec)
apply auto
apply (metis noElementDominatedContradiction invariant_def)
apply (metis noElementDominatedContradiction invariant_def)

apply (drule_tac x="aa" in spec)
apply (drule_tac x="ba" in spec)
apply auto
apply (metis less_trans noElementDominatedContradiction invariant_def)
by (metis noElementDominatedContradiction invariant_def)


lemma merge_commute: "merge A B = merge B A"
by (auto simp add: merge_def)

lemma merge_prop2: "\<lbrakk>compare Y X; compare Z X; invariant X; invariant Y; invariant Z \<rbrakk> \<Longrightarrow> compare (merge Y Z) X"
apply (subst mergeAlt)
apply (simp add: invariant_def)
apply (simp add: invariant_def)
apply (unfold mergeAlt_def compare_def compareSingle_def)
apply (unfold removeSmallerElements_def removeSmallerElementsH_def)
apply auto
done

  


lemma incVVIncreases: "\<lbrakk>finite A; (a,va)\<in>A \<rbrakk> \<Longrightarrow> va < incVersions A r"
apply (auto simp add: incVersions_def)
apply (subgoal_tac "va \<in> (snd ` A)")
apply (subgoal_tac "va \<le> supSet (snd ` A)")
apply (metis incVVGreater le_less_trans)
apply (metis finite_imageI supSetSmaller)
apply force
done

lemma assignIncreases: "invariant A \<Longrightarrow> compare A (assign A r xs)"
apply (auto simp add: assign_def compare_def compareSingle_def)
apply (metis ex_in_conv image_is_empty set_empty)
apply (metis incVVIncreases invariant_def)+
done

lemma assignInvariant: "invariant A \<Longrightarrow> invariant (assign A r R)"
apply (auto simp add: assign_def compare_def compareSingle_def invariant_def)
apply (simp add: vvZeroIffNone_def)
apply (metis incVVIncreases less_asym' vvZeroLess)
apply (auto simp add: noElementDominated_def)
done






lemma crdtProps: "crdtProperties mvRegister (\<lambda>H pl. invariant pl)"
apply (rule unfoldCrdtProperties)
apply (auto simp add: mvRegister_def)
apply (case_tac args)
apply auto
apply (metis assignIncreases)
apply (metis compareRefl)
apply (metis compareTrans)
apply (metis compareAntiSymInv)
apply (metis compareAntiSymInv)
apply (metis MVregister.merge_commute)
apply (metis MVregister.merge_commute)
apply (metis merge_prop1)
apply (metis merge_prop2)
apply (simp add: invariant_def vvZeroIffNone_def noElementDominated_def)
apply (metis merge_invariant)
apply (metis assignInvariant update.simps updateArgs.exhaust)
done


definition mvRegisterInvariant  where
"mvRegisterInvariant H pl = ((\<forall>x c. (Some x, c)\<in>pl 
  \<longleftrightarrow> (\<exists>r l v. x\<in>set l \<and> (v, Assign l)\<in>set(H r)
    \<and> (\<forall>rr. c\<guillemotright>rr = length (filter (\<lambda>e. updArgs e \<noteq> Assign [] \<and> updVersion e \<le> v ) (H rr)))
    \<and> \<not>(\<exists>l' vv. l' \<noteq> [] \<and> vv>v \<and> (vv, Assign l')\<in>allUpdates H)))
  \<and> (\<forall>x. (None,x)\<in>pl \<longleftrightarrow> x=vvZero \<and> H = (\<lambda>r. [])))"


end

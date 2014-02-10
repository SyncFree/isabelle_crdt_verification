theory ORset
imports ORsetSimple 
"../framework/simulations"
"../framework/helper" 
"../framework/convergence" 
begin

type_synonym 'a payload = "('a \<times> versionVector) set \<times> ('a \<times> versionVector) set \<times> versionVector"


abbreviation elements :: "'a payload \<Rightarrow> ('a \<times> versionVector) set" where
"elements x \<equiv> fst x"

abbreviation tombstones :: "'a payload \<Rightarrow> ('a \<times> versionVector) set" where
"tombstones x \<equiv> fst (snd x)"

abbreviation versionVec :: "'a payload \<Rightarrow> versionVector" where
"versionVec x \<equiv> snd (snd x)"

definition add :: "replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a \<Rightarrow> 'a payload" where 
"add myId pl e = (let vv = incVV myId (versionVec pl) in 
      (elements pl \<union> {(e,vv)}, tombstones pl, vv))"

definition remove :: "replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a \<Rightarrow> 'a payload" where
"remove myId pl e = (let R = {(e',n). (e',n)\<in>elements pl \<and> e'=e} in 
    (elements pl - R, tombstones pl \<union> R, incVV myId (versionVec pl)))"

definition merge  :: "'a payload \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"merge A B = ((elements A - tombstones B) \<union> (elements B - tombstones A), tombstones A \<union> tombstones B, sup (versionVec A) (versionVec B))"

definition contains :: "'a payload \<Rightarrow> 'a \<Rightarrow> bool" where
"contains pl e = (\<exists>n. (e,n)\<in>elements pl)"

definition getElements :: "'a payload \<Rightarrow> 'a set" where
"getElements pl = {e. contains pl e}"

fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
  "update (Add e) r pl = add r pl e"
| "update (Remove e) r pl = remove r pl e"

fun getValue :: "'a queryArgs \<Rightarrow> 'a payload \<Rightarrow> 'a result" where
  "getValue (Contains e) pl = ContainsResult (contains pl e)"
| "getValue (GetElements) pl = GetElementsResult (getElements pl)"

definition compare :: "'a payload \<Rightarrow> 'a payload \<Rightarrow> bool" where
"compare A B = (versionVec A \<le> versionVec B \<and> (elements A \<union> tombstones A) \<subseteq> (elements B \<union> tombstones B) \<and> (tombstones A \<subseteq> tombstones B))"


definition ORset where
"ORset = \<lparr> 
      t_compare = compare,
      t_merge   = merge,
      t_initial = ({}, {}, vvZero),
      t_update  = update,
      t_query   = getValue       
  \<rparr>"

(* example, that merge is not idempotent *)
lemma "\<exists>x. merge x x \<noteq> x"
apply (rule_tac x="({(x,vvZero)},{(x,vvZero)},vvZero)" in exI)
apply (auto simp add: merge_def)
done

definition elementsAndTombstonesDisjoint where 
"elementsAndTombstonesDisjoint x = (elements x \<inter> tombstones x = {})"

definition elemetsSmallerVersionVec where
"elemetsSmallerVersionVec x = ((\<forall>(a,av)\<in>elements x. av \<le> versionVec x) \<and> (\<forall>(a,av)\<in>tombstones x. av \<le> versionVec x))"

definition invariant :: "'a payload \<Rightarrow> bool" where
"invariant x = (elementsAndTombstonesDisjoint x \<and> elemetsSmallerVersionVec x)"

lemma ORsetSimple_crdtProps: "crdtProperties ORset (\<lambda>UH pl. invariant pl)"
apply (rule unfoldCrdtProperties)
apply (case_tac args)
apply (auto simp add: ORset_def add_def remove_def Let_def incVVGreaterEq compare_def)
apply (auto simp add: invariant_def elementsAndTombstonesDisjoint_def) 
apply (auto simp add: merge_def)
apply (simp add: sup_commute)
apply (simp add: elemetsSmallerVersionVec_def)
apply (simp add: elemetsSmallerVersionVec_def)
apply auto
apply (metis le_supI1 split_conv)
apply (metis le_supI2 split_conv)
apply (metis le_supI1 split_conv)
apply (metis le_supI2 split_conv)
apply (case_tac args, auto)
apply (auto simp add: add_def remove_def Let_def)
apply (auto simp add: elemetsSmallerVersionVec_def)
apply (rotate_tac -1)
apply (drule_tac x="(ac, incVV rx b)" in bspec)
apply auto
apply (metis incVVGreater less_le_not_le)
apply (case_tac args, auto)
apply (auto simp add: add_def remove_def Let_def)
apply (metis (full_types) incVVGreaterEq order_trans split_conv)
apply (metis (full_types) incVVGreaterEq order_trans split_conv)
apply (case_tac args, auto)
apply (auto simp add: add_def remove_def Let_def)
apply (metis (full_types) incVVGreaterEq order_trans split_conv)+
done


fun couplingInv :: "'a ORsetSimple.payload \<Rightarrow> 'a payload \<Rightarrow> bool" where
"couplingInv (Ea, Ta, Va) (Eb, Tb, Vb) = (
  Ea = Eb - Tb \<and> Ta = Tb \<and> Va = Vb
  \<and> (\<forall>(x,v)\<in>Eb. v\<le>Vb)
  \<and> (\<forall>(x,v)\<in>Tb. v\<le>Vb)
)"

lemma setSpecValid: "crdtSpecificationValid ORset setSpec"
apply (rule_tac crdtA="ORsetSimple" and Inv="couplingInv" in simulation)
apply (metis setSpecValid)
apply (simp add: couplingQuery_def ORset_def ORsetSimple_def)
apply auto
apply (case_tac args)
apply (auto simp add:  ORset.contains_def ORsetSimple.contains_def ORset.getElements_def ORsetSimple.getElements_def)

apply (auto simp add: coupling_def)

apply (simp add: couplingInitial_def ORset_def ORsetSimple_def)

apply (simp add: couplingUpdate_def ORset_def ORsetSimple_def)
apply auto
apply (case_tac args)
apply (auto simp add: ORset.add_def ORset.remove_def ORsetSimple.add_def ORsetSimple.remove_def Let_def)
apply (metis (full_types) incVVGreater less_le_not_le split_conv)
apply (force intro: incVVGreaterEq order_trans)+

apply (auto simp add: couplingMerge_def ORset_def ORsetSimple_def merge_def)
apply (force intro: le_supI1 le_supI2)+
done

end



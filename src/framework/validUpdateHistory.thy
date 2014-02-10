theory validUpdateHistory
imports specifications
begin

definition allUpdates :: "'ua updateHistory \<Rightarrow>  ('ua update) set" where
"allUpdates H = (\<Union>r\<in>UNIV. set (H r))"

lemma allUpdates2: "allUpdates H = {y. \<exists>r. y\<in> set(H r)}"
by (auto simp add: allUpdates_def)


lemma inAllUpdatesI[intro]: "x\<in>set(H r) \<Longrightarrow> x \<in> allUpdates H"
by (metis (lifting) allUpdates2 mem_Collect_eq)

lemma notinAllUpdatesI[intro]: "(\<And>r. x \<notin>set(H r)) \<Longrightarrow> x \<notin> allUpdates H"
apply (auto simp add: allUpdates2)
done

definition "allVersions H = fst ` allUpdates H"

lemma inAllVersionsI[intro]: "(v,y)\<in>set(H r) \<Longrightarrow> v \<in> allVersions H"
by (metis allVersions_def fst_eqD image_iff inAllUpdatesI)


lemma notinAllVersionsI[intro]: "(\<And>r y. (v,y) \<notin>set(H r)) \<Longrightarrow> v \<notin> allVersions H"
by (metis allVersions_def image_iff notinAllUpdatesI pair_collapse)

lemma inAllVersions: "v \<in> allVersions H \<Longrightarrow> \<exists>y r. (v,y)\<in>set(H r)"
by (metis notinAllVersionsI)

lemma notinAllVersions: "v \<notin> allVersions H \<Longrightarrow> (v,y) \<notin> set(H r)"
by (metis inAllVersionsI)

definition validUpdateHistory_versionVectorR :: "'ua updateHistory \<Rightarrow> bool" where
"validUpdateHistory_versionVectorR H = (\<forall>v r args i. 
    i<length(H r) \<and> H r ! i = (v,args) \<longrightarrow> v\<guillemotright>r = Suc i)"

definition validUpdateHistory_localMax :: "'ua updateHistory \<Rightarrow> bool" where
"validUpdateHistory_localMax H = (\<forall>r v. 
    v\<in>allVersions H \<longrightarrow> (length (H r) \<ge> v\<guillemotright>r))"

definition validUpdateHistory_monotonicSame :: "'ua updateHistory \<Rightarrow> bool" where
"validUpdateHistory_monotonicSame H = (\<forall>r v1 v2 y1 y2. 
      (v1,y1) \<in> set (H r) \<and> (v2,y2) \<in> set (H r) \<and> v1\<guillemotright>r<v2\<guillemotright>r\<longrightarrow> v1<v2)"

definition validUpdateHistory_monotonicOther :: "'ua updateHistory \<Rightarrow> bool" where
"validUpdateHistory_monotonicOther H = (\<forall>r1 r2 v1 v2 y1 y2. 
        r1\<noteq>r2 \<and> (v1,y1) \<in> set (H r1) \<and> (v2,y2) \<in> set (H r2) \<and> v1\<guillemotright>r1\<le>v2\<guillemotright>r1\<longrightarrow> v1<v2)"


definition validUpdateHistory :: "'ua updateHistory \<Rightarrow> bool" where
"validUpdateHistory H = (
    validUpdateHistory_versionVectorR H
  \<and> validUpdateHistory_localMax H
  \<and> validUpdateHistory_monotonicSame H
  \<and> validUpdateHistory_monotonicOther H
)"

lemma validUpdateHistory_getLocalMax: "validUpdateHistory H \<Longrightarrow> validUpdateHistory_localMax H"
by (metis validUpdateHistory_def)


lemma validUpdateHistory_monotonic_H1: "
(va, ya) \<in> set (H rb) \<Longrightarrow>
    (vb, yb) \<in> set (H rb) \<Longrightarrow>
    validUpdateHistory_versionVectorR H \<Longrightarrow>   
    va \<guillemotright> rb = vb \<guillemotright> rb \<Longrightarrow> va \<le> vb
"
apply (unfold in_set_conv_nth)
apply (auto simp add: validUpdateHistory_versionVectorR_def)
apply (metis gr0_conv_Suc  nat.inject order_refl prod.inject)
done

lemma validUpdateHistory_monotonic: "\<lbrakk>
validUpdateHistory H;
(va, ya) \<in> set (H ra);
(vb, yb) \<in> set (H rb);
va\<guillemotright>ra \<le> vb\<guillemotright>ra
\<rbrakk> \<Longrightarrow> va \<le> vb"
apply (case_tac "ra=rb")
apply (auto simp add: validUpdateHistory_def validUpdateHistory_monotonicSame_def)
apply (case_tac "va \<guillemotright> rb = vb \<guillemotright> rb")
apply auto
apply (metis validUpdateHistory_monotonic_H1)
apply (metis le_less)
apply (auto simp add: validUpdateHistory_def validUpdateHistory_monotonicOther_def)
by (metis le_less)

lemma validUpdateHistory_monotonic2: "\<lbrakk>
validUpdateHistory H;
(va, ya) \<in> set (H ra);
(vb, yb) \<in> set (H rb);
va\<guillemotright>ra < vb\<guillemotright>ra
\<rbrakk> \<Longrightarrow> va < vb"
apply (case_tac "ra=rb")
apply (auto simp add: validUpdateHistory_def validUpdateHistory_monotonicSame_def)
apply (case_tac "va \<guillemotright> rb = vb \<guillemotright> rb")
apply auto
apply metis
apply (auto simp add: validUpdateHistory_def validUpdateHistory_monotonicOther_def)
by (metis nat_less_le)

lemma validUpdateHistory_monotonicOther: "\<lbrakk>
validUpdateHistory H;
ra \<noteq> rb;
(va, ya) \<in> set (H ra);
(vb, yb) \<in> set (H rb);
va\<guillemotright>ra \<le> vb\<guillemotright>ra
\<rbrakk> \<Longrightarrow> va < vb"
apply (auto simp add: validUpdateHistory_def validUpdateHistory_monotonicOther_def)
by metis


lemma validUpdateHistory_localMax: "\<lbrakk>
validUpdateHistory H;
v\<in>allVersions H
\<rbrakk> \<Longrightarrow> length (H r) \<ge> v\<guillemotright>r"
by (metis validUpdateHistory_getLocalMax validUpdateHistory_localMax_def)

lemma isPrefixRefl: "isPrefix xs xs"
apply (simp add: isPrefixTake)
done

lemma isPrefixAppend: "isPrefix xs (xs@ys)"
apply (simp add: isPrefixTake)
done


lemma isPrefixAppend2: "isPrefix xs ys \<Longrightarrow> isPrefix xs (ys@zs)"
apply (auto simp add: isPrefixTake)
by (metis le_cases take_all)


lemma isPrefixFilter: "\<lbrakk>
\<forall>i j. j\<le>i \<and> i<length xs \<and> P (xs!i) \<longrightarrow> P (xs!j)
\<rbrakk> \<Longrightarrow> isPrefix [x\<leftarrow>xs . P x] xs"
apply (induct xs rule: rev_induct)
apply clarsimp
apply (drule_tac meta_mp)
apply clarsimp
apply (drule_tac x="i" in spec)
apply (drule_tac x="j" in spec)
apply clarsimp
apply (metis le_less_trans nth_append)

apply (case_tac "P x")
apply (rule_tac t=" (filter P (xs @ [x]))" and s="xs@[x]" in ssubst)
apply clarsimp
apply (rule filter_True)
apply clarsimp
apply (unfold in_set_conv_nth)
apply clarsimp
apply (drule_tac x="length xs" in spec)
apply (drule_tac x="i" in spec)
apply clarsimp
apply (metis nth_append)
apply (metis isPrefixRefl)
(*case \<not>P x*)
apply clarsimp
by (metis isPrefixAppend2)

lemma validUpdateHistory_versionVectorR: "validUpdateHistory H \<Longrightarrow> H r ! j = (v, y) \<Longrightarrow>j<length(H r) \<Longrightarrow> v\<guillemotright>r = Suc j"
apply (auto simp add: validUpdateHistory_def validUpdateHistory_versionVectorR_def)
done

lemma validUpdateHistory_mono1: "validUpdateHistory H \<Longrightarrow> H r ! j = (a, b) \<Longrightarrow> j < i \<Longrightarrow> i < length (H r) \<Longrightarrow> H r ! i = (x, y) \<Longrightarrow> a < x"
apply (auto simp add: validUpdateHistory_def validUpdateHistory_monotonicSame_def)
apply (drule_tac x="r" in spec)
apply (drule_tac x="a" in spec)
apply (drule_tac x="x" in spec)
apply auto
apply (metis in_set_conv_nth less_trans)
apply (metis in_set_conv_nth)
by (metis Suc_less_eq less_trans validUpdateHistory_versionVectorR_def)

lemma validUpdateHistory_mono: "validUpdateHistory H \<Longrightarrow> H r ! j = (a, b) \<Longrightarrow> j \<le> i \<Longrightarrow> i < length (H r) \<Longrightarrow> H r ! i = (x, y) \<Longrightarrow> a \<le> x"
by (metis eq_iff less_imp_le nat_less_le prod.inject validUpdateHistory_mono1)


lemma updateHistoryFilterInvisiblePrefix: "validUpdateHistory H \<Longrightarrow> isPrefix (updateHistoryFilterInvisible H v r) (H r)"
apply (auto simp add: updateHistoryFilterInvisible_def)
apply (rule isPrefixFilter)
apply clarsimp
apply (rule_tac y=x in order_trans)
apply (metis validUpdateHistory_mono)
apply simp
done

lemma isPrefixLen: "isPrefix xs ys \<Longrightarrow> length xs \<le> length ys"
by (metis isPrefixTake nat_le_linear take_all)

lemma isPrefixNth: "isPrefix xs ys \<Longrightarrow> i< length xs \<Longrightarrow> xs!i = x \<Longrightarrow> ys!i = x"
by (metis isPrefixTake nth_take)

lemma takeFilter: "\<lbrakk>
\<And>x. x\<in>set (take j xs) \<Longrightarrow> P x
\<rbrakk> \<Longrightarrow> take j (filter P xs) = take j xs"
apply (induct xs rule: rev_induct)
apply clarsimp
apply (drule meta_mp)
apply (drule_tac x="xa" in meta_spec)
apply (erule meta_mp)
apply force
apply (case_tac "j \<le> length xs")
apply clarsimp
apply (subgoal_tac "j \<le> length (take j (filter P xs))")
apply (metis le_cases take_all)
apply clarsimp
apply clarsimp
done

lemma validUpdateHistoryFilterLen: "validUpdateHistory H 
\<Longrightarrow> fst (H r ! (j - 1)) \<le> v
\<Longrightarrow> j \<le> length (H r)
\<Longrightarrow> j \<le> length [(vv, args)\<leftarrow>H r . vv \<le> v]"
apply (subgoal_tac "isPrefix (take j (H r)) [(vv, args)\<leftarrow>H r . vv \<le> v]")
apply (drule isPrefixLen)
apply clarsimp
apply (metis min_max.inf_absorb1 min_max.inf_commute)
apply (subst isPrefixTake)
apply clarsimp
apply (rule_tac t="(min (length (H r)) j)" and s="j" in ssubst)
apply (metis min_max.inf_absorb1 min_max.inf_commute)
apply (rule takeFilter)
apply clarsimp
apply (unfold in_set_conv_nth)
apply clarsimp
apply (case_tac "H r ! (j - Suc 0)")
apply clarsimp
apply (rule_tac y="aa" in order_trans)
apply (rule_tac ya="b" and ra="r" and yb="ba" and rb="r" in validUpdateHistory_monotonic)
apply assumption
apply (metis less_le_trans nth_mem)
apply (metis One_nat_def diff_less gr_implies_not0 less_imp_diff_less linorder_neqE_nat not_less nth_mem zero_less_one)
apply (subst validUpdateHistory_versionVectorR)
apply assumption+
apply (metis leD less_trans linorder_neqE_nat)
apply (subst validUpdateHistory_versionVectorR)
apply assumption+
apply (metis diff_Suc_less diff_self_eq_0 le_neq_implies_less less_imp_diff_less)
apply auto
done

lemma validUpdateHistoryFilterInvisible_H1: "
validUpdateHistory H \<Longrightarrow> 
(va, y) \<in> set (H ra) \<Longrightarrow> 
va \<guillemotright> r = Suc n \<Longrightarrow> 
Suc n \<le> length (H r) \<Longrightarrow> 
H r ! n = (v, x) \<Longrightarrow> 
v \<le> va
"
apply (metis (hide_lams, mono_tags) Suc_le_eq in_set_conv_nth order_refl validUpdateHistory_monotonic validUpdateHistory_versionVectorR)
done


lemma validUpdateHistoryFilterInvisible: "validUpdateHistory H \<Longrightarrow> validUpdateHistory (updateHistoryFilterInvisible H v)"
apply (subst validUpdateHistory_def)
apply (auto)


apply (auto simp add:  validUpdateHistory_versionVectorR_def) 
apply (subgoal_tac "H r ! i = (va, args)")
apply (subgoal_tac "va\<guillemotright>r = Suc i")
apply metis
apply (rule validUpdateHistory_versionVectorR)
apply assumption+
apply (metis isPrefixLen less_le_trans updateHistoryFilterInvisiblePrefix)
apply (metis isPrefixNth updateHistoryFilterInvisiblePrefix)

apply (auto simp add: validUpdateHistory_localMax_def)
apply (drule inAllVersions)
apply (auto simp add: updateHistoryFilterInvisible_def)
apply (case_tac "va\<guillemotright>r")
apply clarsimp
apply (subgoal_tac "va\<guillemotright>r \<le> length (H r)")
apply (case_tac "H r ! (va\<guillemotright>r - 1)")
apply clarsimp
apply (rule validUpdateHistoryFilterLen)
apply assumption
apply clarsimp
(*TODO*)
apply (rule_tac y=va in order_trans)
apply (metis validUpdateHistoryFilterInvisible_H1)
apply simp
apply simp
apply (metis inAllVersionsI validUpdateHistory_localMax)


apply (auto simp add: validUpdateHistory_monotonicSame_def)
apply (metis validUpdateHistory_monotonic2)
apply (auto simp add: validUpdateHistory_monotonicOther_def)
apply (metis validUpdateHistory_monotonicOther)
done


lemma validUpdateHistoryEmpty: "validUpdateHistory (\<lambda>r. [])"
apply (auto simp add: validUpdateHistory_def
 validUpdateHistory_versionVectorR_def
 validUpdateHistory_localMax_def
 validUpdateHistory_monotonicSame_def
 validUpdateHistory_monotonicOther_def
 allVersions_def allUpdates_def)
done


definition "validUpdateHistoryH_localVersionMax version = (\<forall>r rr. (version r)\<guillemotright>r \<ge> (version rr)\<guillemotright>r)"
definition "validUpdateHistoryH_versionUpperBound H version = (\<forall>v r. v\<in>allVersions H \<longrightarrow> v\<guillemotright>r \<le> (version r)\<guillemotright>r)"
definition "validUpdateHistoryH_versionMono H version = (\<forall>v r y r2. (v,y)\<in>set (H r) \<and> v\<guillemotright>r\<le>version r2\<guillemotright>r \<longrightarrow> v \<le> (version r2))"
definition "validUpdateHistoryH_length H version = (\<forall>r. length(H r) = version r \<guillemotright>r)"

definition validUpdateHistoryH_inv where 
"validUpdateHistoryH_inv H version = (
  validUpdateHistory H
  \<and> validUpdateHistoryH_localVersionMax version
  \<and> validUpdateHistoryH_versionUpperBound H version 
  \<and> validUpdateHistoryH_length H version
  \<and> validUpdateHistoryH_versionMono H version
)"

lemma validUpdateHistoryH1: "validUpdateHistoryH_inv H v \<Longrightarrow> validUpdateHistory H"
by (simp add: validUpdateHistoryH_inv_def)

lemma validUpdateHistoryH_localVersionMax: "validUpdateHistoryH_inv H v \<Longrightarrow> (v r)\<guillemotright>r \<ge> (v rr)\<guillemotright>r"
apply (simp add: validUpdateHistoryH_inv_def validUpdateHistoryH_localVersionMax_def)
done

lemma validUpdateHistoryH_versionUpperBound: "validUpdateHistoryH_inv H vs \<Longrightarrow> v\<in>allVersions H \<Longrightarrow> v\<guillemotright>r \<le> (vs r)\<guillemotright>r"
apply (simp add: validUpdateHistoryH_inv_def validUpdateHistoryH_versionUpperBound_def)
done

lemma validUpdateHistoryH_versionUpperBound2: "validUpdateHistoryH_inv H vs \<Longrightarrow> (v,y)\<in>set (H r) \<Longrightarrow> v\<guillemotright>r \<le> (vs r)\<guillemotright>r"
by (metis inAllVersionsI validUpdateHistoryH_versionUpperBound)

lemma validUpdateHistoryH_versionMono: "\<lbrakk>
validUpdateHistoryH_inv H version;
(v,y)\<in>set (H r);
v\<guillemotright>r \<le> version ra\<guillemotright>r
\<rbrakk> \<Longrightarrow>  v\<le>version ra"
by (metis validUpdateHistoryH_inv_def validUpdateHistoryH_versionMono_def)

lemma validUpdateHistoryH_versionMono2: "\<lbrakk>
validUpdateHistoryH_inv H version;
(v,y)\<in>set (H r)
\<rbrakk> \<Longrightarrow>  v\<le>version r"
by (metis validUpdateHistoryH_versionMono validUpdateHistoryH_versionUpperBound2)


-- "approximation of valid trace"
fun validTraceFun where
  "validTraceFun EmptyTrace = True"
| "validTraceFun (Trace tr (Update r a)) = validTraceFun tr"
| "validTraceFun (Trace tr (MergePayload r v pl)) = (validTraceFun tr 
      \<and> (\<forall>r. v\<guillemotright>r \<le> (replicaVersion tr r) \<guillemotright>r)
      \<and> (\<exists>V. v=supSet V \<and> V \<subseteq> allVersions (updateHistory tr)))"

definition "validTrace = validTraceFun"

lemma validTraceStep: "validTrace (Trace tr a) \<Longrightarrow> validTrace tr"
apply (case_tac a)
apply (auto simp add: validTrace_def)
done

lemma validTraceMerge2: "validTrace (Trace tr (MergePayload rr v pl)) \<Longrightarrow> v\<guillemotright>r \<le> (replicaVersion tr r) \<guillemotright>r"
apply (auto simp add: validTrace_def)
done


lemma validTraceMerge3: "validTrace (Trace tr (MergePayload rr v pl)) \<Longrightarrow> \<exists>V. v=supSet V \<and> V \<subseteq> allVersions (updateHistory tr)"
apply (auto simp add: validTrace_def)
done


lemma validUpdateHistoryH: "validUpdateHistoryH_inv (updateHistory tr) (replicaVersion tr) \<Longrightarrow>
        validUpdateHistory (updateHistory tr)"
by (metis updateHistory_def validUpdateHistoryH1)

lemma versionVecComponentSupset: "finite V \<Longrightarrow> V\<noteq>{} \<Longrightarrow> v \<guillemotright> ra \<le> supSet V \<guillemotright> ra \<Longrightarrow>  \<exists>vm\<in>V. v \<guillemotright> ra \<le> vm \<guillemotright> ra"
apply (induct rule:finite_induct)
apply auto
apply (case_tac "F={}")
apply auto
apply (unfold supSetInsert versionVectorSupComponent)
apply (case_tac "v \<guillemotright> ra \<le> x \<guillemotright> ra")
apply auto
apply (subgoal_tac " v \<guillemotright> ra \<le> supSet F \<guillemotright> ra")
apply auto
done

lemma allVersionsInitial[simp]: "allVersions (\<lambda>r. []) = {}"
apply (simp add: allVersions_def allUpdates_def)
done


lemma allUpdatesFinite: "finite (allUpdates H)"
apply (auto simp add: allUpdates_def)
done

lemma allVersionsFinite: "finite (allVersions H)"
apply (auto simp add: allVersions_def allUpdates_def)
done

lemma validTrace2validUpdateHistoryH: "validTrace tr \<Longrightarrow> validUpdateHistoryH_inv (updateHistory tr) (replicaVersion tr) "
apply (induct tr)
apply auto
apply (simp add: validUpdateHistoryH_inv_def validUpdateHistoryEmpty
  validUpdateHistoryH_localVersionMax_def validUpdateHistoryH_versionUpperBound_def   validUpdateHistoryH_versionMono_def validUpdateHistoryH_length_def) 

apply (drule meta_mp)
apply (metis validTraceStep)


apply (case_tac action)
apply auto

-- "case update"
apply (subst updateHistory_Update)
apply (subst validUpdateHistoryH_inv_def)
apply auto
apply (subst validUpdateHistory_def)
apply auto

apply (auto simp add:  validUpdateHistory_versionVectorR_def)
apply (case_tac "i < length (updateHistory tr replicaId)")
apply clarsimp
apply (metis append_eq_conv_conj nth_take validUpdateHistoryH validUpdateHistory_versionVectorR)
apply (subgoal_tac "i = length (updateHistory tr replicaId)")
apply clarsimp
apply (metis validUpdateHistoryH_inv_def validUpdateHistoryH_length_def)
apply clarsimp
apply (metis validUpdateHistoryH validUpdateHistory_versionVectorR)

apply (auto simp add:  validUpdateHistory_localMax_def)
apply (auto simp add: allVersions_def allUpdates_def)
apply (case_tac "r = replicaId")
apply auto
apply (metis eq_iff validUpdateHistoryH_inv_def validUpdateHistoryH_length_def)
apply (metis le_SucI notinAllVersions validUpdateHistoryH1 validUpdateHistory_localMax)
apply (metis inAllVersionsI le_Suc_eq validUpdateHistoryH validUpdateHistory_localMax)
apply (case_tac " ra = replicaId")
apply auto
apply (metis validUpdateHistoryH_inv_def validUpdateHistoryH_length_def validUpdateHistoryH_localVersionMax)
apply (metis notinAllVersions validUpdateHistoryH1 validUpdateHistory_localMax)
apply (metis notinAllVersions validUpdateHistoryH1 validUpdateHistory_localMax)

apply (auto simp add:  validUpdateHistory_monotonicSame_def)
apply (metis Suc_lessD validUpdateHistoryH_versionMono2 versionVectorNotLessEqI)
apply (metis incVVGreater le_neq_trans less_trans validUpdateHistoryH_versionMono2)
apply (metis validUpdateHistoryH1 validUpdateHistory_monotonic2)
apply (metis validUpdateHistoryH1 validUpdateHistory_monotonic2)

apply (auto simp add:  validUpdateHistory_monotonicOther_def)
apply (metis not_less_eq_eq notinAllVersions validUpdateHistoryH_versionUpperBound)
apply (metis validUpdateHistoryH1 validUpdateHistory_monotonicOther)
apply (metis incVVGreater le_less_trans validUpdateHistoryH_inv_def validUpdateHistoryH_versionMono_def)
apply (metis validUpdateHistoryH1 validUpdateHistory_monotonicOther)
apply (metis validUpdateHistoryH1 validUpdateHistory_monotonicOther)

apply (auto simp add: validUpdateHistoryH_localVersionMax_def)
apply (metis le_SucI validUpdateHistoryH_localVersionMax)
apply (metis validUpdateHistoryH_localVersionMax)
apply (metis validUpdateHistoryH_localVersionMax)

apply (auto simp add: validUpdateHistoryH_versionUpperBound_def allVersions_def allUpdates_def)
apply (case_tac "r = ra")
apply auto
apply (metis le_SucI validUpdateHistoryH_versionUpperBound2)
apply (metis le_SucI notinAllVersions validUpdateHistoryH_versionUpperBound)
apply (case_tac "r = replicaId")
apply auto
apply (metis validUpdateHistoryH_localVersionMax)
apply (metis notinAllVersions validUpdateHistoryH_versionUpperBound)
apply (metis notinAllVersions validUpdateHistoryH_versionUpperBound)

apply (auto simp add: validUpdateHistoryH_length_def)
apply (metis validUpdateHistoryH_inv_def validUpdateHistoryH_length_def)

apply (auto simp add: validUpdateHistoryH_versionMono_def)
apply (metis incVVGreaterEq order_trans validUpdateHistoryH_versionMono2)
apply (metis not_less_eq_eq validUpdateHistoryH_localVersionMax)
apply (metis validUpdateHistoryH_versionMono)
apply (metis incVVGreaterEq less_eq_versionVector_def less_le_trans not_le validUpdateHistoryH_versionMono)
apply (metis validUpdateHistoryH_versionMono)



-- "CASE merge"
apply (subst validUpdateHistoryH_inv_def)
apply (auto simp add: Let_def)
apply (subst validUpdateHistory_def)
apply auto

apply (metis validUpdateHistoryH1 validUpdateHistory_def)

apply (metis validUpdateHistoryH1 validUpdateHistory_getLocalMax)

apply (metis validUpdateHistoryH1 validUpdateHistory_def)

apply (metis validUpdateHistoryH1 validUpdateHistory_def)

apply (auto simp add: validUpdateHistoryH_localVersionMax_def)
apply (auto simp add: versionVectorSupComponent)
apply (metis min_max.le_supI2 validUpdateHistoryH_localVersionMax)

apply (metis validTraceMerge2)
apply (metis validUpdateHistoryH_localVersionMax)
apply (metis validUpdateHistoryH_localVersionMax)

apply (auto simp add: validUpdateHistoryH_versionUpperBound_def)
apply (auto simp add: versionVectorSupComponent)
apply (metis min_max.le_supI2 validUpdateHistoryH_versionUpperBound)
apply (metis validUpdateHistoryH_versionUpperBound)

apply (auto simp add: validUpdateHistoryH_length_def)
apply (auto simp add: versionVectorSupComponent)
apply (metis min_max.sup_absorb2 validTraceMerge2 validUpdateHistoryH_inv_def validUpdateHistoryH_length_def)
apply (metis validUpdateHistoryH_inv_def validUpdateHistoryH_length_def)

apply (simp add:  validUpdateHistoryH_versionMono_def)

apply auto
apply (subst less_eq_versionVector_def)
apply (unfold versionVectorSupComponent)
apply auto
apply (case_tac "v\<guillemotright>r \<le> (replicaVersion tr r2 \<guillemotright> r)")
apply (metis min_max.le_supI2 validUpdateHistoryH_versionMono versionVectorLessEqE)
apply (subgoal_tac "v \<guillemotright> r \<le> versionVector \<guillemotright> r")
apply (subgoal_tac "v \<le> versionVector")
apply (metis min_max.le_supI1 versionVectorLessEqE)
defer
apply force
apply (metis validUpdateHistoryH_versionMono)


apply (frule validTraceMerge3)
apply clarsimp
apply (subgoal_tac "\<exists>vm\<in>V. v\<guillemotright>r \<le> vm\<guillemotright>r")
apply clarsimp
apply (rule_tac y="vm" in supSetSmaller2)
apply (metis allVersionsFinite rev_finite_subset)
apply assumption
apply (subgoal_tac "vm \<in> allVersions (updateHistory tr)")
apply (metis inAllVersions validUpdateHistoryH validUpdateHistory_monotonic)
apply (metis set_mp)
apply (rule versionVecComponentSupset)
apply (metis allVersionsFinite rev_finite_subset)
apply (metis sup_bot_left supSetEmpty versionVectorSupComponent)
apply auto
done


definition validTraceInvariant where
"validTraceInvariant tr s = (
  validTrace tr
  \<and> (\<forall>vv pl. (vv,pl)\<in>history s \<longrightarrow> (\<exists>V. vv = supSet V \<and> V \<subseteq> allVersions (updateHistory tr)))
  \<and> (\<forall>vv pl r. (vv,pl)\<in>history s \<longrightarrow> vv \<guillemotright> r \<le> replicaVersion tr r \<guillemotright> r)
  \<and> (\<forall>r. replicaVV s r = replicaVersion tr r)
  \<and> (\<forall>r. \<exists>pl. (replicaVV s r, pl) \<in> history s)
)"

lemma validTraceInvariant1: "validTraceInvariant tr s \<Longrightarrow> validTrace tr"
apply (auto simp add: validTraceInvariant_def)
done

lemma validTraceInvariant_supSet: "\<lbrakk>
validTraceInvariant tr s;
(vv,pl)\<in>history s
\<rbrakk> \<Longrightarrow> \<exists>V. vv = supSet V \<and> V \<subseteq> allVersions (updateHistory tr)"
by (metis validTraceInvariant_def)

lemma validTraceInvariant_supSet_replicaVV: "\<lbrakk>
validTraceInvariant tr s
\<rbrakk> \<Longrightarrow> \<exists>V. replicaVV s r = supSet V \<and> V \<subseteq> allVersions (updateHistory tr)"
apply (auto simp add: validTraceInvariant_def)
done

lemma validTraceInvariant_bound: "\<lbrakk>
validTraceInvariant tr s;
(vv,pl)\<in>history s
\<rbrakk> \<Longrightarrow> vv \<guillemotright> r \<le> replicaVersion tr r \<guillemotright> r"
apply (auto simp add: validTraceInvariant_def)
done

lemma validTraceInvariant_replicaVV: "\<lbrakk>
validTraceInvariant tr s
\<rbrakk> \<Longrightarrow> replicaVV s r = replicaVersion tr r"
apply (auto simp add: validTraceInvariant_def)
done

lemma validTraceInvariant_history: "\<lbrakk>
validTraceInvariant tr s
\<rbrakk> \<Longrightarrow> \<exists>pl. (replicaVV s r, pl) \<in> history s "
by (metis validTraceInvariant_def)       

lemma updateHistoryMono: "validTrace tr \<Longrightarrow> (x,y) \<in> set (updateHistory tr r) \<Longrightarrow> (x,y) \<in> set (updateHistory (Trace tr a) r)"
apply (subst updateHistory_def)
apply (subst updateHistoryH.simps)
apply (subst updateHistory_def[symmetric])+
apply (case_tac a)
apply auto
done

lemma stepsToValidTrace: "\<lbrakk>
steps crdt tr (initialState crdt) s
(*crdtProperties crdt*)
\<rbrakk> \<Longrightarrow> validTraceInvariant tr s"
apply (induct tr arbitrary: s) 
apply (erule steps.cases)
apply auto
apply (simp add: validTraceInvariant_def validTrace_def initialState_def bot_versionVector_def)

apply (erule steps.cases)
apply auto
apply (drule_tac x="s2" in meta_spec)
apply (drule meta_mp)
apply assumption
apply (frule validTraceInvariant1)
apply (drule validTrace2validUpdateHistoryH)


apply (subst validTraceInvariant_def)
apply (erule step.cases)
apply (unfold doUpdateState)
apply (auto simp add: validTrace_def)

apply (unfold validTrace_def[symmetric])
apply (metis validTraceInvariant1)

(* apply (case_tac "history s vv") *)

apply (rule_tac x="{incVV r (replicaVV s r)}" in exI)
apply (simp add: updateHistory_Update Let_def)
apply (rule_tac y="args" in inAllVersionsI)
apply auto
apply (metis stepsReplicaVersion)


apply (frule(1) validTraceInvariant_supSet)
apply clarsimp
apply (rule_tac x="V" in exI)
apply clarsimp
apply (cut_tac v=x and H="updateHistory as" in inAllVersions)
apply force
apply clarsimp
apply (rule_tac y=y and r=ra in inAllVersionsI)
apply (metis updateHistoryMono validTraceInvariant1)


apply (metis eq_iff validTraceInvariant_replicaVV)
apply (metis le_Suc_eq validTraceInvariant_def)
apply (metis validTraceInvariant_def)
apply (metis validTraceInvariant_def)
apply (metis validTraceInvariant_replicaVV)
apply (metis validTraceInvariant_replicaVV)
apply (metis validTraceInvariant_history)
apply (metis validTraceInvariant1)
apply (metis validTraceInvariant_def)
apply (metis validTraceInvariant_def)


apply (frule(1) validTraceInvariant_supSet)
apply (frule_tac r="r" in validTraceInvariant_supSet_replicaVV)
apply clarsimp
apply (rule_tac x="V \<union> Va" in exI)
apply auto
apply (rule supSupSet)
apply (metis allVersionsFinite finite_subset)
apply (metis allVersionsFinite finite_subset)

apply (metis validTraceInvariant_def)
apply (metis order_refl stepsReplicaVersion)
apply (auto simp add: versionVectorSupComponent)
apply (metis le_max_iff_disj validTraceInvariant_bound)
apply (metis validTraceInvariant_bound)
apply (metis validTraceInvariant_def)
apply (metis validTraceInvariant_def)

apply (metis stepsReplicaVersion)
apply (metis validTraceInvariant_replicaVV)
apply (metis validTraceInvariant_history)
done

end

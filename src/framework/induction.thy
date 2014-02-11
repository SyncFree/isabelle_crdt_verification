theory induction
imports specifications validUpdateHistory
begin



definition historyUnion :: "'ua updateHistory \<Rightarrow> 'ua updateHistory \<Rightarrow> 'ua updateHistory" where 
"historyUnion H1 H2 = (\<lambda>r. if length (H1 r) \<le> length (H2 r) then H2 r else H1 r)"


definition consistentHistories :: "'ua updateHistory \<Rightarrow> 'ua updateHistory \<Rightarrow> bool" where
"consistentHistories H1 H2 = (\<forall>r. isPrefix (H1 r) (H2 r) \<or> isPrefix (H2 r) (H1 r))"



lemma consistentHistoriesCases: "\<lbrakk>
consistentHistories H1 H2;
consistentHistories H1 H2 \<Longrightarrow> isPrefix (H1 r) (H2 r) \<Longrightarrow> P;
consistentHistories H1 H2 \<Longrightarrow> isPrefix (H2 r) (H1 r) \<Longrightarrow> P
\<rbrakk> \<Longrightarrow> P"
apply (auto simp add: consistentHistories_def)
done

lemma consistentHistories_commute: "consistentHistories A B = consistentHistories B A"
apply (auto simp add: consistentHistories_def)
done

lemma historyUnion_commute: "consistentHistories A B \<Longrightarrow> historyUnion A B = historyUnion B A"
apply (auto simp add: historyUnion_def)
apply (rule ext)
apply (erule_tac r="r" in consistentHistoriesCases)
apply (metis isPrefixLen isPrefixTake take_all)+
done

(* Some definitions *)
definition updateHistoryInvariant_initial where
"updateHistoryInvariant_initial crdt Inv = (Inv (\<lambda>r. []) (t_initial crdt))"

definition updateHistoryInvariant_merge where
"updateHistoryInvariant_merge crdt Inv = (\<forall>H1 pl1 H2 pl2. 
    validUpdateHistory H1 
  \<and> validUpdateHistory H2 
  \<and> Inv H1 pl1 
  \<and> Inv H2 pl2 
  \<and> consistentHistories H1 H2 
    \<longrightarrow> Inv (historyUnion H1 H2) (t_merge crdt pl1 pl2))"

definition "versionIsTop v H = (v = supSet (allVersions H))"

definition updateHistoryInvariant_update where
"updateHistoryInvariant_update crdt Inv = (\<forall>H pl r v args.
    validUpdateHistory H 
  \<and> Inv H pl 
  \<and> versionIsTop v H
    \<longrightarrow> Inv (H(r := (H r)@[(incVV r v, args)])) (t_update crdt args r pl))"

definition updateHistoryInvariant_all where
"updateHistoryInvariant_all crdt Inv = (
    updateHistoryInvariant_initial crdt Inv
  \<and> updateHistoryInvariant_merge crdt Inv 
  \<and> updateHistoryInvariant_update crdt Inv)"

lemma updateHistoryInvariant_bot: "updateHistoryInvariant_all crdt P 
 \<Longrightarrow> P (\<lambda>r. []) (t_initial crdt)"
apply (simp add: updateHistoryInvariant_all_def updateHistoryInvariant_initial_def)
done

lemma updateHistoryInvariant_merge: "\<lbrakk>
updateHistoryInvariant_all crdt P;
validUpdateHistory Ha;
validUpdateHistory Hb;
P Ha pla;
P Hb plb;
consistentHistories Ha Hb
\<rbrakk> \<Longrightarrow> P (historyUnion Ha Hb) (t_merge crdt pla plb)"
apply (auto simp add: updateHistoryInvariant_all_def updateHistoryInvariant_merge_def)
done

lemma updateHistoryInvariant_update: "\<lbrakk>
updateHistoryInvariant_all crdt P;
validUpdateHistory H;
validUpdateHistory (H(r := (H r)@[(incVV r v, args)]));
P H pl;
versionIsTop v H
\<rbrakk> \<Longrightarrow> P (H(r := (H r)@[(incVV r v, args)])) (t_update crdt args r pl)"
apply (auto simp add: updateHistoryInvariant_all_def updateHistoryInvariant_update_def)
done



lemma stepsFromInitialStateInduct[induct set: steps]: "\<lbrakk>
steps crdt tr (initialState crdt) s;
P EmptyTrace (initialState crdt);
\<And>tr sa sb r args sc. P tr sa 
  \<Longrightarrow> steps crdt tr (initialState crdt) sa 
  \<Longrightarrow> validUpdateHistory (updateHistory (Trace tr (Update r args))) 
  \<Longrightarrow> P (Trace tr (Update r args)) (doUpdateState r (incVV r) (t_update crdt args r) sa);
\<And>tr sa sb r pl vv sc. P tr sa 
  \<Longrightarrow> steps crdt tr (initialState crdt) sa
  \<Longrightarrow> (vv,pl) \<in> history sa
  \<Longrightarrow> P (Trace tr (MergePayload r vv pl)) (doUpdateState r (sup vv) (t_merge crdt pl) sa)
\<rbrakk> \<Longrightarrow> P tr s"
apply (erule rev_mp)
apply (induct tr arbitrary: s)
apply clarsimp
apply (erule steps.cases)
apply simp
apply simp

apply (case_tac action)

(* update *)
apply clarsimp
apply (erule steps.cases)
apply simp
apply simp
apply (drule_tac x="s2" in meta_spec)
apply clarsimp
apply (erule step.cases)
apply simp
apply (metis stepsToValidTrace validTrace2validUpdateHistoryH validTraceFun.simps(2) validTraceInvariant1 validTrace_def validUpdateHistoryH)
apply simp

(* merge *)
apply clarsimp
apply (erule steps.cases)
apply simp
apply simp
apply (drule_tac x="s2" in meta_spec)
apply clarsimp
apply (erule step.cases)
apply simp
apply (simp add: Let_def)
done

lemma visibleUpdateHistoryIncVVUpdate2: "\<lbrakk>
steps crdt tr (initialState crdt) sa 
\<rbrakk>\<Longrightarrow>
       visibleUpdateHistory (Trace tr (Update r args)) (incVV r (replicaVV sa r)) 
     = (visibleUpdateHistory tr (replicaVV sa r))(r := visibleUpdateHistory tr (replicaVV sa r) r@[(incVV r (replicaVV sa r), args)])"
apply (rule ext)
apply clarsimp
apply (rule conjI)
apply clarsimp
apply (simp add: visibleUpdateHistory_def)
apply (unfold updateHistory_Update)
apply clarsimp
apply (auto simp add: updateHistoryFilterInvisible_def)
apply (rule filter_cong)
apply auto
apply (metis stepsReplicaVersion stepsToValidTrace validTrace2validUpdateHistoryH validTraceInvariant1 validUpdateHistoryH_versionMono2)
apply (metis incVVGreaterEq order_trans)
apply (metis stepsReplicaVersion)
apply (metis eq_iff stepsReplicaVersion)
apply (simp add: visibleUpdateHistory_def)
apply (unfold updateHistory_Update)
apply (auto simp add: updateHistoryFilterInvisible_def)
apply (rule filter_cong)
apply auto
apply (metis inAllVersionsI incVVr2 less_eq_versionVector_def stepsReplicaVersion stepsToValidTrace validTrace2validUpdateHistoryH validTraceInvariant1 validUpdateHistoryH_versionUpperBound)
apply (metis incVVGreaterEq order_trans)
done




lemma supSetVisibleUpdateHistory: "supSet (allVersions (visibleUpdateHistory tr vv)) \<le> vv"
apply (rule_tac supSetBigger)                             
apply (auto simp add: visibleUpdateHistory_def updateHistoryFilterInvisible_def allVersions_def allUpdates_def)
done


lemma stepsIncVVreplicaVersion: "\<lbrakk>
steps crdt tr (initialState crdt) sa;
(v,pl) \<in> history sa
\<rbrakk> \<Longrightarrow> \<not> incVV r (replicaVersion tr r) \<le> v"
apply (rule_tac r="r" in versionVectorNotLessEqI)
apply clarsimp
apply (subst less_Suc_eq_le)
by (metis stepsToValidTrace validTraceInvariant_bound)

lemma currentPayloadInHistory: "steps crdt tr (initialState crdt) sa
       \<Longrightarrow> (replicaVV sa r, replicaPayload sa r) \<in> history sa "
apply (induct rule: stepsFromInitialStateInduct)
apply auto
apply (simp add: initialState_def)
done

lemma filterEqualsTakeWhile: "\<lbrakk>
\<And>i j. i<j \<Longrightarrow> j < length xs \<Longrightarrow> P (xs!j) \<Longrightarrow> P (xs!i)
\<rbrakk> \<Longrightarrow> filter P xs = takeWhile P xs"
apply (induct xs)
apply clarsimp
apply auto
apply (metis One_nat_def Suc_less_eq diff_Suc_1 nth_Cons_Suc)
apply (rule filter_False)
apply clarsimp
apply (metis Suc_less_eq diff_Suc_Suc in_set_conv_nth minus_nat.diff_0 nth_Cons_0 zero_less_Suc)
done

lemma updateHistoryFilterInvisibleTakeWhile: "\<lbrakk>
validUpdateHistory H
\<rbrakk> \<Longrightarrow> updateHistoryFilterInvisible H vv r = takeWhile (\<lambda>(v,y). v\<le>vv) (H r)"
apply (auto simp add: updateHistoryFilterInvisible_def)
apply (rule filterEqualsTakeWhile)
apply auto
by (metis le_eq_less_or_eq order_trans validUpdateHistory_mono)

lemma isPrefixTakeWhile: "isPrefix (takeWhile P xs) (takeWhile Q xs) \<or> isPrefix (takeWhile Q xs) (takeWhile P xs)"
apply (auto simp add: isPrefixTake)
apply (induct xs)
apply auto
done


lemma isPrefixUpdateHistoryFilterInvisible: "\<lbrakk>
validUpdateHistory H
\<rbrakk> \<Longrightarrow> isPrefix (updateHistoryFilterInvisible H va r) (updateHistoryFilterInvisible H vb r)
 \<or> isPrefix (updateHistoryFilterInvisible H vb r) (updateHistoryFilterInvisible H va r)"
apply (unfold updateHistoryFilterInvisibleTakeWhile)
by (rule isPrefixTakeWhile)

lemma stepsToValidUpdateHistory: "steps crdt tr (initialState crdt) s \<Longrightarrow> validUpdateHistory (updateHistory tr)"
by (metis stepsToValidTrace validTrace2validUpdateHistoryH validTraceInvariant1 validUpdateHistoryH1)

lemma consistentHistoriesVisibleUpdateHistory: "steps crdt tr (initialState crdt) s \<Longrightarrow> consistentHistories (visibleUpdateHistory tr va) (visibleUpdateHistory tr vb)"
apply (subst consistentHistories_def)
apply (auto simp add: visibleUpdateHistory_def)
by (metis isPrefixUpdateHistoryFilterInvisible stepsToValidUpdateHistory)



lemma replicaVVMax: "steps crdt tr (initialState crdt) s
       \<Longrightarrow> (va, pla) \<in> history s
       \<Longrightarrow> va\<guillemotright>r \<le> replicaVV s r\<guillemotright>r"
by (metis stepsReplicaVersion stepsToValidTrace validTraceInvariant_bound)


lemma updateHistoryMono2: "steps crdt tr (initialState crdt) s \<Longrightarrow>
       (va, pla) \<in> history s \<Longrightarrow>
       (x, arg) \<in> set (updateHistory tr r)
       \<Longrightarrow> x \<guillemotright> r \<le> va \<guillemotright> r
       \<Longrightarrow> x \<le> va"
apply (induct  arbitrary: va pla r arg x rule: stepsFromInitialStateInduct)
apply simp
apply (unfold updateHistory_Update)
apply auto
apply (case_tac "x = incVV r (replicaVersion tr r)")
apply auto
apply (metis eq_iff stepsReplicaVersion)
apply (rule ccontr)
apply (unfold stepsReplicaVersion)
apply (frule_tac validUpdateHistory_monotonic)
apply simp_all
apply auto

apply (case_tac "ra = r")
apply auto
apply (metis not_less_eq_eq replicaVVMax)
apply (simp add: versionVectorSupComponent)
apply (metis le_max_iff_disj le_supI1 le_supI2 stepsToValidTrace validTraceInvariant_history)
done

lemma historyUnionSimp_H1: "\<lbrakk>
steps crdt tr (initialState crdt) s;
(va, pla) \<in> history s
\<rbrakk> \<Longrightarrow>visibleUpdateHistory tr va r
    = take (va\<guillemotright>r) (updateHistory tr r)"
apply (subgoal_tac "va\<guillemotright>r \<le> length (updateHistory tr r)")
defer
apply (metis (hide_lams, no_types) stepsToValidTrace validTrace2validUpdateHistoryH validTraceInvariant_def validUpdateHistoryH_inv_def validUpdateHistoryH_length_def)
apply (frule_tac stepsToValidUpdateHistory)
apply (simp add: visibleUpdateHistory_def updateHistoryFilterInvisibleTakeWhile)
apply (rule takeWhile_eq_take_P_nth)
apply auto
apply (subgoal_tac "a\<guillemotright>r = Suc i")
apply (metis (hide_lams, no_types) Suc_leI leD le_less_linear le_less_trans nth_mem induction.updateHistoryMono2)
apply (metis less_le_trans validUpdateHistory_versionVectorR)
apply (metis lessI validUpdateHistory_versionVectorR versionVectorNotLessEqI)
done


lemma historyUnionSimp_H2: "\<lbrakk>
steps crdt tr (initialState crdt) s;
(va, pla) \<in> history s;
(vb, plb) \<in> history s
\<rbrakk> \<Longrightarrow>visibleUpdateHistory tr (sup va vb) r
    = take (max (va\<guillemotright>r) (vb\<guillemotright>r)) (updateHistory tr r)"
apply (subgoal_tac "va\<guillemotright>r \<le> length (updateHistory tr r)")
defer
apply (metis (hide_lams, no_types) stepsToValidTrace validTrace2validUpdateHistoryH validTraceInvariant_def validUpdateHistoryH_inv_def validUpdateHistoryH_length_def)
apply (subgoal_tac "vb\<guillemotright>r \<le> length (updateHistory tr r)")
defer
apply (metis (hide_lams, no_types) stepsToValidTrace validTrace2validUpdateHistoryH validTraceInvariant_def validUpdateHistoryH_inv_def validUpdateHistoryH_length_def)

apply (frule_tac stepsToValidUpdateHistory)
apply (simp add: visibleUpdateHistory_def updateHistoryFilterInvisibleTakeWhile)
apply (rule takeWhile_eq_take_P_nth)
apply auto
apply (subgoal_tac "a\<guillemotright>r = Suc i")
apply (case_tac "i < va\<guillemotright>r")
apply (subgoal_tac "a \<le> va")
apply (metis le_supI1)


apply (metis (hide_lams, no_types) Suc_leI nth_mem induction.updateHistoryMono2)
apply (case_tac "i < vb\<guillemotright>r")
apply auto
apply (subgoal_tac "a \<le> vb")
apply (metis le_supI2)

apply (metis (hide_lams, no_types) Suc_leI in_set_conv_nth less_le_trans induction.updateHistoryMono2)
apply (metis validUpdateHistory_versionVectorR)
apply (case_tac "(va \<guillemotright> r) \<le> (vb \<guillemotright> r)")
apply auto
apply (metis lessI min_max.le_iff_sup not_le versionVectorSupComponent validUpdateHistory_versionVectorR versionVectorLessEqE)
apply (metis Suc_le_lessD le_Suc_eq max_def validUpdateHistory_versionVectorR versionVectorNotLessEqI versionVectorSupComponent)
done

lemma historyUnionSimp: "\<lbrakk>
steps crdt tr (initialState crdt) s;
(va, pla) \<in> history s;
(vb, plb) \<in> history s
\<rbrakk> \<Longrightarrow>(historyUnion (visibleUpdateHistory tr va) (visibleUpdateHistory tr vb))
    = (visibleUpdateHistory tr (sup va vb))"
apply (rule ext)
apply (rename_tac r)
apply (simp add: historyUnion_def)
apply (unfold historyUnionSimp_H1)
apply (unfold historyUnionSimp_H2)
apply auto
apply (metis min_le_iff_disj min_max.le_supI1 min_max.sup_commute min_max.sup_absorb1 take_all)
apply (metis max_def min_max.inf_commute min_max.le_infI1)
done

lemma allVersionsFilter[simp]: "allVersions (\<lambda>r. filter (\<lambda>(v,y). P v) (H r)) = {v\<in>allVersions H. P v}"
apply (auto simp add: allVersions_def allUpdates_def)
apply (subgoal_tac "(a,b)\<in> {x \<in> set (H r). case x of (v, y) \<Rightarrow> P v}")
apply force+
done

lemma stepsStateInvInduct: "\<lbrakk>
steps crdt tr (initialState crdt) s;
updateHistoryInvariant_all crdt Inv
\<rbrakk> \<Longrightarrow> (\<forall>v pl. (v,pl) \<in> history s \<longrightarrow> Inv (visibleUpdateHistory tr v) pl)" 
apply (induct rule: stepsFromInitialStateInduct)
(* initial *)
apply clarsimp
apply (rule_tac t="(visibleUpdateHistory EmptyTrace v)" and s="(\<lambda>r. [])" in ssubst)
apply (simp add: visibleUpdateHistory_def updateHistoryFilterInvisible_def)
apply (rule_tac t="pl" and s="t_initial crdt" in ssubst)
apply (simp add: initialState_def)
apply (case_tac " v = vvZero")
apply clarsimp+
apply (metis updateHistoryInvariant_bot)
apply (metis updateHistoryInvariant_bot)

(* update *)
apply clarsimp
apply (case_tac " v \<noteq> incVV r (replicaVV sa r)")
apply clarsimp
apply (rule_tac t=" (visibleUpdateHistory (Trace tr (Update r args)) v)"
  and s="visibleUpdateHistory tr v" in ssubst)
apply (simp add: visibleUpdateHistory_def)
apply (subst updateHistory_Update)
apply (simp add: updateHistoryFilterInvisible_def)
apply (rule ext)
apply (case_tac "ra = r")
apply auto
apply (metis stepsIncVVreplicaVersion)

apply (drule_tac H="visibleUpdateHistory tr (replicaVV sa r)"
  and r="r"
  and v="replicaVV sa r"
  and args="args"
  and pl="replicaPayload sa r"
  in  updateHistoryInvariant_update)
prefer 5
apply (subst visibleUpdateHistoryIncVVUpdate2)
apply assumption
apply clarsimp
apply (metis stepsToValidUpdateHistory validUpdateHistoryFilterInvisible visibleUpdateHistory_def)
apply (subst visibleUpdateHistory_def)
apply (metis validUpdateHistoryFilterInvisible visibleUpdateHistoryIncVVUpdate2 visibleUpdateHistory_def)

apply (metis currentPayloadInHistory)

apply (simp add: versionIsTop_def)
apply (rule antisym)
apply (cut_tac s="sa" and tr="tr" and r="r" in validTraceInvariant_supSet_replicaVV)
apply (metis stepsToValidTrace)
apply clarsimp
apply (rule supSetSubSet)
apply (metis allVersionsFinite)
apply (simp add: visibleUpdateHistory_def updateHistoryFilterInvisible_def)
apply auto
apply (rule supSetSmaller)
apply (metis allVersionsFinite finite_subset)
apply assumption
apply (rule supSetVisibleUpdateHistory)
apply (metis order_refl stepsIncVVreplicaVersion stepsReplicaVersion)

(* Merge *)
apply (rule_tac
  t="(visibleUpdateHistory (Trace tr (MergePayload r vv pl)) (sup vv (replicaVV sa r)))"
  and s="(visibleUpdateHistory tr (sup vv (replicaVV sa r)))"
  in ssubst)
apply (metis updateHistory_Merge visibleUpdateHistory_def)
apply (frule_tac 
  Ha="(visibleUpdateHistory tr vv)"
  and pla="pl"
  and Hb="(visibleUpdateHistory tr (replicaVV sa r))"
  and plb="replicaPayload sa r"
  in updateHistoryInvariant_merge)
apply (metis stepsToValidTrace validTrace2validUpdateHistoryH validTraceInvariant1 validUpdateHistoryFilterInvisible validUpdateHistoryH1 visibleUpdateHistory_def)
apply (metis stepsToValidTrace validTrace2validUpdateHistoryH validTraceInvariant1 validUpdateHistoryFilterInvisible validUpdateHistoryH1 visibleUpdateHistory_def)
apply metis
apply (metis currentPayloadInHistory)
apply (metis consistentHistoriesVisibleUpdateHistory)
apply (metis currentPayloadInHistory historyUnionSimp)
apply (metis updateHistory_Merge visibleUpdateHistory_def)
done

definition invariantImpliesSpec where
"invariantImpliesSpec crdt Inv spec = (\<forall>H pl qa. validUpdateHistory H \<and> Inv H pl \<longrightarrow> t_query crdt qa pl = spec H qa)"


theorem showCrdtSpecificationValid: "\<lbrakk>
invariantImpliesSpec crdt Inv spec;
updateHistoryInvariant_all crdt Inv
\<rbrakk> \<Longrightarrow> crdtSpecificationValid crdt spec"
apply (auto simp add: crdtSpecificationValid_def)
apply (unfold invariantImpliesSpec_def)
apply (drule_tac x="(visibleUpdateHistory tr (replicaVV s r))" in spec)
apply (drule_tac x="replicaPayload s r" in spec)
apply (drule_tac x="qa" in spec)
apply (drule_tac mp)
apply auto
apply (metis stepsToValidTrace validTrace2validUpdateHistoryH validTraceInvariant1 validUpdateHistoryFilterInvisible validUpdateHistoryH1 visibleUpdateHistory_def)
apply (metis currentPayloadInHistory stepsStateInvInduct)
done


lemma consistentHistoriesNth: "
consistentHistories H1 H2 \<Longrightarrow>
H2 r ! n = x \<Longrightarrow> 
n < length (H1 r) \<Longrightarrow>
n < length (H2 r) \<Longrightarrow>
H1 r ! n = x"
apply (erule_tac r=r in consistentHistoriesCases)
apply (metis isPrefixNth)+
done


lemma consistentHistories_H1: "
validUpdateHistory Ha \<Longrightarrow>
validUpdateHistory Hb \<Longrightarrow>
consistentHistories Ha Hb \<Longrightarrow>
(v1, y1) \<in> set (Hb r1) \<Longrightarrow> 
v1 \<guillemotright> r1 \<le> v2 \<guillemotright> r1 \<Longrightarrow> 
(v2, y2) \<in> set (Ha r2) \<Longrightarrow> 
(v1, y1) \<in> set (Ha r1)"
apply (frule_tac v=v2 and r=r1 in validUpdateHistory_localMax)
apply (metis inAllVersionsI)
apply (unfold in_set_conv_nth)
apply auto
apply (rule_tac x=i in exI)
apply auto
apply (metis leD less_le_trans not_less_eq validUpdateHistory_versionVectorR)
apply (rule consistentHistoriesNth)
apply assumption+
apply auto
apply (metis (hide_lams, no_types) lessI less_le_trans validUpdateHistory_versionVectorR)
done

lemma historyUnionValid: "\<lbrakk>
validUpdateHistory H1;
validUpdateHistory H2;
consistentHistories H1 H2
\<rbrakk> \<Longrightarrow> validUpdateHistory (historyUnion H1 H2)
"
apply (subst validUpdateHistory_def)
apply (auto simp add: historyUnion_def)
apply (auto simp add: validUpdateHistory_versionVectorR_def)
apply (metis validUpdateHistory_versionVectorR)
apply (metis validUpdateHistory_versionVectorR)
apply (auto simp add: validUpdateHistory_localMax_def)
apply (drule inAllVersions)
apply auto
apply (erule_tac r=ra in consistentHistoriesCases)
apply (metis (mono_tags) isPrefixLen notinAllVersions validUpdateHistory_localMax)
apply (case_tac "\<not>(length (H1 ra) \<le> length (H2 ra))")
apply simp
apply (metis notinAllVersions order_trans validUpdateHistory_localMax)
apply simp
apply (metis notinAllVersions validUpdateHistory_localMax)
apply (drule inAllVersions)
apply clarsimp
apply (case_tac "length (H1 ra) \<le> length (H2 ra)")
apply simp
apply (metis linear notinAllVersions order_trans validUpdateHistory_localMax)
apply (case_tac "\<not>(length (H1 ra) \<le> length (H2 ra))")
apply auto
apply (metis notinAllVersions validUpdateHistory_localMax)
apply (auto simp add: validUpdateHistory_monotonicSame_def)
apply (metis validUpdateHistory_monotonic2)
apply (metis validUpdateHistory_monotonic2)
apply (auto simp add: validUpdateHistory_monotonicOther_def)
apply (metis validUpdateHistory_monotonicOther)
apply (subgoal_tac "(v1, y1) \<in> set (H1 r1)")
apply (metis validUpdateHistory_monotonicOther)
apply (metis consistentHistories_H1)
apply (subgoal_tac "(v1, y1) \<in> set (H2 r1)")
apply (metis validUpdateHistory_monotonicOther)
apply (metis consistentHistories_H1 consistentHistories_commute)
apply (metis validUpdateHistory_monotonicOther)
done

end

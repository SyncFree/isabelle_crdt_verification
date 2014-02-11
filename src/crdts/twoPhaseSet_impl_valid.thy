theory twoPhaseSet_impl_valid
imports 
twoPhaseSet_impl
"../framework/induction"
"../framework/helper"
begin

definition Inv where
"Inv H pl = (\<forall>x. (x\<in>fst pl \<longleftrightarrow> (\<exists>e\<in>allUpdates H. updArgs(e) = Add x)) 
  \<and> (x\<in>snd pl \<longleftrightarrow> (\<exists>e\<in>allUpdates H. updArgs(e) = Remove x)))"

lemma "crdtSpecificationValid twoPhaseSet twoPhaseSetSpec"
apply (rule_tac Inv="Inv" in showCrdtSpecificationValid)
(* show that invariant implies spec *)
apply (simp add: twoPhaseSet_def twoPhaseSetSpec_def Inv_def invariantImpliesSpec_def)

(* show that invariant is maintained *)
apply (auto simp add: updateHistoryInvariant_all_def)

(* initial*)
apply (auto simp add: updateHistoryInvariant_initial_def)
apply (simp add: Inv_def twoPhaseSet_def)

(* merge *) 
apply (auto simp add: updateHistoryInvariant_merge_def)
apply (simp add: Inv_def twoPhaseSet_def)
apply auto

(* update *)
apply (auto simp add: updateHistoryInvariant_update_def)
apply (simp add: Inv_def twoPhaseSet_def)
apply (case_tac args)
apply auto
done

end


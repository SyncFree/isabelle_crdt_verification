theory twoPhaseSet2_impl_valid
imports 
twoPhaseSet2_impl
"../framework/induction"
"../framework/helper"  
begin


definition Inv where
"Inv H pl = (\<forall>x. (x\<in>fst pl \<longleftrightarrow> (\<exists>e\<in>allUpdates H. updArgs(e) = Add x)) 
  \<and> (x\<in>snd pl \<longleftrightarrow> (\<exists>e\<in>allUpdates H. updArgs(e) = Remove x \<and> (\<exists>f\<in>allUpdates H. updArgs(f) = Add(x) \<and> f \<prec> e))))"

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
apply (drule_tac x=x in spec) 
apply (drule_tac x=x in spec)
apply (metis consistentHistoriesHappensBefore2 fst_conv snd_conv)
apply (metis (hide_lams, no_types) consistentHistoriesHappensBefore fst_conv snd_conv)

(* update *)
apply (auto simp add: updateHistoryInvariant_update_def)
apply (simp add: Inv_def twoPhaseSet_def)
apply (case_tac args)
apply auto
apply (metis laterVersionNotInAllUpdates_incVV)
apply (metis fst_conv snd_conv versionIsTopGreaterHistory2_incVV)
done



end


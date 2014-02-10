theory gset_impl_valid
imports 
gset_impl
"../framework/induction"
"../framework/helper" 
begin

definition gSetInvariant where
"gSetInvariant H pl = (\<forall>x. x\<in> pl \<longleftrightarrow> (\<exists>e\<in>allUpdates H. updArgs(e) = x))"

lemma "crdtSpecificationValid gSet gSetSpec"
apply (rule_tac Inv="gSetInvariant" in showCrdtSpecificationValid)
(* show that invariant implies spec *)
apply (simp add: gSet_def lookup_def gSetSpec_def gSetInvariant_def  invariantImpliesSpec_def)

(* show that invariant is maintained *)
apply (auto simp add: updateHistoryInvariant_all_def)

(* initial*)
apply (auto simp add: updateHistoryInvariant_initial_def)
apply (simp add: gSetInvariant_def gSet_def)

(* merge *) 
apply (auto simp add: updateHistoryInvariant_merge_def)
apply (auto simp add: gSetInvariant_def gSet_def)

(* update *)
apply (auto simp add: updateHistoryInvariant_update_def)
apply (auto simp add: gSetInvariant_def gSet_def add_def)
done

end


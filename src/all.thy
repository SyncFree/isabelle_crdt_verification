theory all
imports Main
"framework/replicas"
"framework/supSet"
"framework/versionvectors"
"framework/systemModel"
"framework/finalSetFold"
"framework/convergence"
"framework/specifications"
"framework/validUpdateHistory"
"framework/induction"
"framework/simulations"
"framework/helper"

(* case studies *)
"crdts/gset_impl"
"crdts/gset_impl_convergence"
"crdts/gset_impl_valid"
"crdts/gset_spec"
"crdts/IncrementOnlyCounter_impl"
"crdts/IncrementOnlyCounter_impl_convergence"
"crdts/IncrementOnlyCounter_impl_valid"
"crdts/IncrementOnlyCounter_spec"
"crdts/MVregister2_impl"
"crdts/MVregister2_impl_convergence"
"crdts/MVregister2_impl_valid"
"crdts/MVregister2_spec"
"crdts/MVregister_impl"
"crdts/MVregister_impl_convergence"
"crdts/MVregister_impl_valid"
"crdts/MVregisterSingle_spec"
"crdts/MVregisterSingle_impl"
"crdts/MVregisterSingle_impl_convergence"
"crdts/MVregisterSingle_impl_valid"
"crdts/MVregister_spec"
"crdts/ORset_impl"
"crdts/ORset_impl_convergence"
"crdts/ORset_impl_valid"
"crdts/ORset_optimized"
"crdts/ORset_optimized_convergence"
"crdts/ORset_optimized_valid"
"crdts/ORset_simple"
"crdts/ORset_simple_convergence"
"crdts/ORset_simple_valid"
"crdts/ORset_spec"
"crdts/PNCounter_impl"
"crdts/PNCounter_impl_convergence"
"crdts/PNCounter_impl_valid"
"crdts/PNCounter_spec"
"crdts/twoPhaseSet2_impl"
"crdts/twoPhaseSet2_impl_convergence"
"crdts/twoPhaseSet2_impl_valid"
"crdts/twoPhaseSet2_spec"
"crdts/twoPhaseSet_impl"
"crdts/twoPhaseSet_impl_convergence"
"crdts/twoPhaseSet_impl_valid"
"crdts/twoPhaseSet_spec"
begin



(* lemma using all important theorems, so that they are not marked as unused *)
lemma dummyUsage: "True"
apply (cut_tac IncrementOnlyCounter_impl_convergence.crdtProps)
apply (cut_tac IncrementOnlyCounter_impl_valid.specValid)
apply (cut_tac MVregister_impl_convergence.crdtProps)
apply (cut_tac MVregister_impl_convergence.crdtProps)
apply (cut_tac MVregister_impl_valid.specValid)
apply (cut_tac ORset_impl_convergence.ORsetSimple_crdtProps)
apply (cut_tac ORset_impl_valid.setSpecValid)
apply (cut_tac ORset_optimized_convergence.ORsetSimple_crdtProps)
apply (cut_tac ORset_optimized_valid.setSpecValid)
apply (cut_tac ORset_simple_convergence.ORsetSimple_crdtProps)
apply (cut_tac PNCounter_impl_convergence.ORsetSimple_crdtProps)
apply (cut_tac counterSpecValid)
apply (cut_tac gset_impl_convergence.ORsetSimple_crdtProps)
apply (cut_tac twoPhaseSet_impl_convergence.ORsetSimple_crdtProps)
apply (cut_tac twoPhaseSet2_impl_convergence.ORsetSimple_crdtProps)

apply (cut_tac MVregister2_impl_convergence.crdtProps)
apply (cut_tac MVregisterSingle_impl_convergence.crdtProps)
apply (cut_tac MVregisterSingle_impl_valid.specValid)

apply (auto simp add: IncrementOnlyCounter_impl_convergence.crdtProps) 
done

lemma dummyUsage2: "False \<Longrightarrow> True"
apply (cut_tac convergent_crdt2)
apply (cut_tac convergent_crdt)
apply (cut_tac semilatticePropertiesFromTypeclass)
apply (cut_tac semilatticeProperties_defaultOrder)
apply (cut_tac compareIffMerge)
apply (cut_tac historyUnionValid)
apply (auto)
done


unused_thms Main -






end

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
"crdts/IncrementOnlyCounter"
"crdts/PNCounter"

"crdts/gset"
"crdts/twoPhaseSet"
"crdts/twoPhaseSet2"

"crdts/ORsetSimple"
"crdts/ORset"
"crdts/ORsetOptimized"
"crdts/ORsetOptimizedConvergence"
"crdts/ORsetOptimizedValid"

"crdts/MVregisterSimple"
"crdts/MVregister"
begin




lemma dummyUsage: "True"
apply (cut_tac IncrementOnlyCounter.crdtProps)
apply (cut_tac IncrementOnlyCounter.specValid)
apply (cut_tac MVregister.crdtProps)
apply (cut_tac MVregisterSimple.crdtProps)
apply (cut_tac MVregisterSimple.specValid)
apply (cut_tac ORset.ORsetSimple_crdtProps)
apply (cut_tac ORset.setSpecValid)
apply (cut_tac ORsetOptimizedConvergence.ORsetSimple_crdtProps)
apply (cut_tac ORsetOptimizedValid.setSpecValid)
apply (cut_tac ORsetSimple.ORsetSimple_crdtProps)
apply (cut_tac PNCounter.ORsetSimple_crdtProps)
apply (cut_tac counterSpecValid)
apply (cut_tac gset.ORsetSimple_crdtProps)
apply (cut_tac twoPhaseSet.ORsetSimple_crdtProps)
apply (cut_tac twoPhaseSet2.ORsetSimple_crdtProps)

apply (auto simp add: IncrementOnlyCounter.crdtProps) 
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

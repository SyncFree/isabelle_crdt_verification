theory ORset_simple_convergence
imports 
ORset_simple
"../framework/convergence" 
begin


lemma ORsetSimple_crdtProps: "crdtProperties ORsetSimple (\<lambda>UH pl. True)"
apply (rule unfoldCrdtProperties)
apply (case_tac args)
apply (auto simp add: ORsetSimple_def add_def remove_def Let_def incVVGreaterEq)
apply (simp add: sup_commute)
done


end


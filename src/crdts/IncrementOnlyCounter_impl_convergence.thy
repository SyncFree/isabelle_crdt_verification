theory IncrementOnlyCounter_impl_convergence
imports 
IncrementOnlyCounter_impl
"../framework/convergence"
begin

lemma crdtProps: "crdtProperties incrementOnlyCounter (\<lambda>UH pl. True)"
apply (rule unfoldCrdtProperties)
apply (case_tac args)
apply (auto simp add: incrementOnlyCounter_def increment_def)
apply (simp add: incVVGreaterEq)
apply (simp add: sup_commute)
done

end

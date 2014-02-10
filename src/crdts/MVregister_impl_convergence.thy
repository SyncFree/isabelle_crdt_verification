theory MVregister_impl_convergence
imports 
MVregister_impl
"../framework/convergence" 
begin


lemma crdtProps: "crdtProperties mvRegister (\<lambda>H pl. True)"
apply (rule unfoldCrdtProperties)
apply (auto simp add: mvRegister_def)
apply (case_tac args, auto)
apply (metis incVVGreaterEq)
apply (case_tac args, auto)
apply (metis sup.commute)
done

end

theory twoPhaseSet_impl_convergence
imports 
twoPhaseSet_impl
"../framework/convergence" 
begin

lemma ORsetSimple_crdtProps: "crdtProperties twoPhaseSet (\<lambda>UH pl. True)"
apply (rule unfoldCrdtProperties)
apply (auto simp add: twoPhaseSet_def)
apply (case_tac args, auto)+
done

end


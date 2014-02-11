theory PNCounter_impl_convergence
imports 
PNCounter_impl
"../framework/convergence" 
begin


lemma ORsetSimple_crdtProps: "crdtProperties pnCounter (\<lambda>UH pl. True)"
apply (rule unfoldCrdtProperties)
apply (case_tac args)
apply (auto simp add: pnCounter_def)
apply (metis order_trans)
apply (metis order_trans)
apply (rule ext)
apply (metis antisym)
apply (rule ext)
apply (metis antisym)
done


end

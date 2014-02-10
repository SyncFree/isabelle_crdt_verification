theory gset_impl_convergence
imports 
gset_impl
"../framework/convergence" 
begin

lemma ORsetSimple_crdtProps: "crdtProperties gSet (\<lambda>UH pl. True)"
apply (rule unfoldCrdtProperties)
apply (auto simp add: gSet_def add_def)
done


end


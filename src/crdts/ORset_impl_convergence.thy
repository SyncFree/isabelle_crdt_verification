theory ORset_impl_convergence
imports
ORset_impl
"../framework/convergence" 
begin


(* example, that merge is not idempotent in general *)
lemma "\<exists>x. merge x x \<noteq> x"
apply (rule_tac x="({(x,vvZero)},{(x,vvZero)},vvZero)" in exI)
apply (auto simp add: merge_def)
done

definition elementsAndTombstonesDisjoint where 
"elementsAndTombstonesDisjoint x = (elements x \<inter> tombstones x = {})"

definition elemetsSmallerVersionVec where
"elemetsSmallerVersionVec x = ((\<forall>(a,av)\<in>elements x. av \<le> versionVec x) \<and> (\<forall>(a,av)\<in>tombstones x. av \<le> versionVec x))"

definition invariant :: "'a payload \<Rightarrow> bool" where
"invariant x = (elementsAndTombstonesDisjoint x \<and> elemetsSmallerVersionVec x)"

lemma ORsetSimple_crdtProps: "crdtProperties ORset (\<lambda>UH pl. invariant pl)"
apply (rule unfoldCrdtProperties)
apply (case_tac args)
apply (auto simp add: ORset_def add_def remove_def Let_def incVVGreaterEq compare_def)
apply (auto simp add: invariant_def elementsAndTombstonesDisjoint_def) 
apply (auto simp add: merge_def)
apply (simp add: sup_commute)
apply (simp add: elemetsSmallerVersionVec_def)
apply (simp add: elemetsSmallerVersionVec_def)
apply auto
apply (metis le_supI1 split_conv)
apply (metis le_supI2 split_conv)
apply (metis le_supI1 split_conv)
apply (metis le_supI2 split_conv)
apply (case_tac args, auto)
apply (auto simp add: add_def remove_def Let_def)
apply (auto simp add: elemetsSmallerVersionVec_def)
apply (rotate_tac -1)
apply (drule_tac x="(ac, incVV rx b)" in bspec)
apply auto
apply (metis incVVGreater less_le_not_le)
apply (case_tac args, auto)
apply (auto simp add: add_def remove_def Let_def)
apply (metis (full_types) incVVGreaterEq order_trans split_conv)
apply (metis (full_types) incVVGreaterEq order_trans split_conv)
apply (case_tac args, auto)
apply (auto simp add: add_def remove_def Let_def)
apply (metis (full_types) incVVGreaterEq order_trans split_conv)+
done


end



theory ORset_impl_valid
imports
ORset_spec
ORset_simple_valid
ORset_impl
"../framework/simulations"
begin



fun couplingInv :: "'a ORset_simple.payload \<Rightarrow> 'a payload \<Rightarrow> bool" where
"couplingInv (Ea, Ta, Va) (Eb, Tb, Vb) = (
  Ea = Eb - Tb \<and> Ta = Tb \<and> Va = Vb
  \<and> (\<forall>(x,v)\<in>Eb. v\<le>Vb)
  \<and> (\<forall>(x,v)\<in>Tb. v\<le>Vb)
)"

lemma setSpecValid: "crdtSpecificationValid ORset setSpec"
apply (rule_tac crdtA="ORsetSimple" and Inv="couplingInv" in simulation)
apply (metis setSpecValid)
apply (simp add: couplingQuery_def ORset_def ORsetSimple_def)
apply auto
apply (case_tac args)
apply (auto simp add:  ORset_impl.contains_def ORset_simple.contains_def ORset_impl.getElements_def ORset_simple.getElements_def)

apply (auto simp add: coupling_def)

apply (simp add: couplingInitial_def ORset_def ORsetSimple_def)

apply (simp add: couplingUpdate_def ORset_def ORsetSimple_def)
apply auto
apply (case_tac args)
apply (auto simp add: ORset_impl.add_def ORset_impl.remove_def ORset_simple.add_def ORset_simple.remove_def Let_def)
apply (metis (full_types) incVVGreater less_le_not_le split_conv)
apply (force intro: incVVGreaterEq order_trans)+

apply (auto simp add: couplingMerge_def ORset_def ORsetSimple_def merge_def)
apply (force intro: le_supI1 le_supI2)+
done

end



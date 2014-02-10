theory gset_impl
imports 
gset_spec
"../framework/induction"
"../framework/helper" 
"../framework/convergence" 
begin


definition add :: "'a \<Rightarrow> replicaId \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"add x r = insert x"

definition lookup :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
"lookup x pl = (x\<in>pl)"

definition gSet :: "('a set, 'a, 'a, bool) stateBasedType" where
"gSet = \<lparr> 
      t_compare = op\<subseteq>,
      t_merge   = op\<union>,
      t_initial = {},
      t_update  = add,
      t_query   = lookup      
  \<rparr>"

end


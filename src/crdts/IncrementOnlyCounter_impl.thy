theory IncrementOnlyCounter_impl
imports 
IncrementOnlyCounter_spec
"../framework/systemModel" 
begin


(* Increment-Only Counter, specification 6 in A comprehensive study of Convergent and Commutative Replicated Data Types*)

definition increment :: "unit \<Rightarrow> replicaId \<Rightarrow> versionVector \<Rightarrow> versionVector" where
"increment _ r = incVV r"

definition getValue :: "unit \<Rightarrow> versionVector \<Rightarrow> nat" where
"getValue _ v =  (\<Sum>r\<in>UNIV. v\<guillemotright>r)"

definition incrementOnlyCounter :: "(versionVector, unit, unit, nat) stateBasedType" where
"incrementOnlyCounter = \<lparr> 
      t_compare = op\<le>,
      t_merge   = sup,
      t_initial = vvZero,
      t_update  = increment,
      t_query   = getValue       
  \<rparr>"

end


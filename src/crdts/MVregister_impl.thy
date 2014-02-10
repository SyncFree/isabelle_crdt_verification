theory MVregister_impl
imports 
MVregister_spec
begin

(* Multi-Value register, inefficient implementation, 
behavior similar to specification 10 in A comprehensive study of Convergent and Commutative Replicated Data Types,
except for the case of assigning an empty list of elements
*)

type_synonym 'a payload = "versionVector \<times> ('a list \<times> versionVector) set"

fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"update (Assign l) r (V,S) = (incVV r V, S \<union> {(l, incVV r V)})"

fun getValue :: "unit \<Rightarrow> 'a payload \<Rightarrow> ('a \<times> versionVector )set" where
"getValue _ (V,S) = {(x,v). \<exists>l. x\<in>set l \<and> (l,v)\<in>S \<and> (\<forall>vv\<in>snd`S. \<not>v<vv)}"

definition mvRegister where
"mvRegister = \<lparr> 
      t_compare = (\<lambda>x y. fst x \<le> fst y \<and> snd x \<subseteq> snd y),
      t_merge   = (\<lambda>x y. (sup (fst x) (fst y), snd x \<union> snd y)),
      t_initial = (vvZero, {}),
      t_update  = update,
      t_query   = getValue       
  \<rparr>"

end

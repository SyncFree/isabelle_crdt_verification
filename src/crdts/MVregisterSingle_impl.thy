theory MVregisterSingle_impl
imports 
MVregisterSingle_spec 
begin

type_synonym 'a payload = "versionVector \<times> ('a \<times> versionVector) set"

fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"update (Assign x) r (V,S) = (incVV r V, S \<union> {(x, incVV r V)})"

fun getValue :: "unit \<Rightarrow> 'a payload \<Rightarrow> 'a set" where
"getValue _ (V,S) = fst ` {(x,v)\<in>S. \<not>(\<exists>(x',v')\<in>S. v < v')}"

definition mvRegister where
"mvRegister = \<lparr> 
      t_compare = (\<lambda>x y. fst x \<le> fst y \<and> snd x \<subseteq> snd y),
      t_merge   = (\<lambda>x y. (sup (fst x) (fst y), snd x \<union> snd y)),
      t_initial = (vvZero, {}),
      t_update  = update,
      t_query   = getValue       
  \<rparr>"



end

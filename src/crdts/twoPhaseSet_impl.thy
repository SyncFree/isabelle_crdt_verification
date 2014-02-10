theory twoPhaseSet_impl
imports 
twoPhaseSet_spec
begin

type_synonym 'a payload = "'a set \<times> 'a set"

fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
  "update (Add x) r (E,T) = (insert x E, T)"
| "update (Remove x) r (E,T) = (E, insert x T)"

fun lookup :: "'a \<Rightarrow> 'a payload \<Rightarrow> bool" where
"lookup x (E,T) = (x\<in>E \<and> x\<notin>T)"

definition twoPhaseSet :: "('a payload, 'a updateArgs, 'a, bool) stateBasedType" where
"twoPhaseSet = \<lparr> 
      t_compare = (\<lambda>x y. fst x \<subseteq> fst y \<and> snd x \<subseteq> snd y),
      t_merge   = (\<lambda>x y. (fst x \<union> fst y, snd x \<union> snd y)),
      t_initial = ({},{}),
      t_update  = update,
      t_query   = lookup      
  \<rparr>"

end


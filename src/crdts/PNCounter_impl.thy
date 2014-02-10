theory PNCounter_impl
imports 
PNCounter_spec
begin

type_synonym payload = "(replicaId \<Rightarrow> int) \<times> (replicaId \<Rightarrow> int)"

fun update :: "int \<Rightarrow> replicaId \<Rightarrow> payload \<Rightarrow> payload" where
 "update x r (p,n) = (if x \<ge> 0 then (p(r:=p r + x), n) else (p, n(r:=n r - x)))"

fun getValue :: "unit \<Rightarrow> payload \<Rightarrow> int" where
"getValue _ (p,n) = ((\<Sum>r\<in>UNIV. p r) - (\<Sum>r\<in>UNIV. n r))"

definition pnCounter where
"pnCounter = \<lparr> 
      t_compare = (\<lambda>x y. \<forall>r. fst x r \<le> fst y r \<and> snd x r \<le> snd y r),
      t_merge   = (\<lambda>x y. (\<lambda>r. max (fst x r) (fst y r), \<lambda>r. max (snd x r) (snd y r))),
      t_initial = (\<lambda>r. 0, \<lambda>r. 0),
      t_update  = update,
      t_query   = getValue       
  \<rparr>"


end

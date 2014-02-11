theory MVregister2_impl
imports 
MVregister2_spec
begin

(* Multi-Value register, based on specification 10 in A comprehensive study of Convergent and Commutative Replicated Data Types
The bug in the original description was fixed by ignoring assignments of the empty list.
*)

type_synonym 'a payload = "('a option \<times> versionVector) set"

definition incVersions :: "'a payload \<Rightarrow> replicaId \<Rightarrow> versionVector" where
"incVersions pl myId = (
    let V = snd ` pl;
        vv = supSet V in
        (incVV myId vv)
)"                            

definition assign :: "'a payload \<Rightarrow> replicaId \<Rightarrow> 'a list \<Rightarrow> 'a payload" where
"assign pl myId R = (if R=[] then pl else let V = incVersions pl myId in (Some ` set R) \<times> {V})"


fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"update (Assign R) r pl = (assign pl r R)"

fun getValue :: "unit \<Rightarrow> 'a payload \<Rightarrow> ('a \<times> versionVector )set" where
"getValue _ pl = {(x,v). (Some x, v) \<in> pl}"

definition compareSingle :: "('a option \<times> versionVector) \<Rightarrow> 'a payload \<Rightarrow> bool" where
"compareSingle x B = (case x of (a,v) \<Rightarrow> (\<exists>(b,w)\<in>B. v < w) \<or> (\<exists>(b,w)\<in>B. v=w \<and> a=b))"

definition compare :: "'a payload \<Rightarrow> 'a payload \<Rightarrow> bool" where
"compare A B = (\<forall>x\<in>A. compareSingle x B)"

definition merge :: "'a payload \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"merge A B = (
    let A' = {(x,V). (x,V)\<in>A \<and> (\<forall>(y, W)\<in>B. V \<parallel> W \<or> V \<ge> W)};
        B' = {(y, W). (y,W)\<in>B \<and> (\<forall>(x, V)\<in>A. W \<parallel> V \<or> W \<ge> V)} in
        A' \<union> B'
)"

definition mvRegister where
"mvRegister = \<lparr> 
      t_compare = compare,
      t_merge   = merge,
      t_initial = {(None, vvZero)},
      t_update  = update,
      t_query   = getValue       
  \<rparr>"


end

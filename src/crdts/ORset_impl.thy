theory ORset_impl
imports
ORset_spec
"../framework/simulations"
"../framework/helper" 
"../framework/convergence" 
begin

type_synonym 'a payload = "('a \<times> versionVector) set \<times> ('a \<times> versionVector) set \<times> versionVector"


abbreviation elements :: "'a payload \<Rightarrow> ('a \<times> versionVector) set" where
"elements x \<equiv> fst x"

abbreviation tombstones :: "'a payload \<Rightarrow> ('a \<times> versionVector) set" where
"tombstones x \<equiv> fst (snd x)"

abbreviation versionVec :: "'a payload \<Rightarrow> versionVector" where
"versionVec x \<equiv> snd (snd x)"

definition add :: "replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a \<Rightarrow> 'a payload" where 
"add myId pl e = (let vv = incVV myId (versionVec pl) in 
      (elements pl \<union> {(e,vv)}, tombstones pl, vv))"

definition remove :: "replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a \<Rightarrow> 'a payload" where
"remove myId pl e = (let R = {(e',n). (e',n)\<in>elements pl \<and> e'=e} in 
    (elements pl - R, tombstones pl \<union> R, incVV myId (versionVec pl)))"

definition merge  :: "'a payload \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"merge A B = ((elements A - tombstones B) \<union> (elements B - tombstones A), tombstones A \<union> tombstones B, sup (versionVec A) (versionVec B))"

definition contains :: "'a payload \<Rightarrow> 'a \<Rightarrow> bool" where
"contains pl e = (\<exists>n. (e,n)\<in>elements pl)"

definition getElements :: "'a payload \<Rightarrow> 'a set" where
"getElements pl = {e. contains pl e}"

fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
  "update (Add e) r pl = add r pl e"
| "update (Remove e) r pl = remove r pl e"

fun getValue :: "'a queryArgs \<Rightarrow> 'a payload \<Rightarrow> 'a result" where
  "getValue (Contains e) pl = ContainsResult (contains pl e)"
| "getValue (GetElements) pl = GetElementsResult (getElements pl)"

definition compare :: "'a payload \<Rightarrow> 'a payload \<Rightarrow> bool" where
"compare A B = (versionVec A \<le> versionVec B \<and> (elements A \<union> tombstones A) \<subseteq> (elements B \<union> tombstones B) \<and> (tombstones A \<subseteq> tombstones B))"


definition ORset where
"ORset = \<lparr> 
      t_compare = compare,
      t_merge   = merge,
      t_initial = ({}, {}, vvZero),
      t_update  = update,
      t_query   = getValue       
  \<rparr>"


end



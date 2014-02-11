theory ORset_simple
imports ORset_spec 
begin

(* simpler version of OR-set (but takes more space, queries take more time)
Difference to the ORset_impl is, that elements are not removed from the Elements set when they are added to the tombstone set
Here all sets are increasing, so semilattice properties are trivial.
*)

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
    (elements pl, tombstones pl \<union> R, incVV myId (versionVec pl)))"

definition contains :: "'a payload \<Rightarrow> 'a \<Rightarrow> bool" where
"contains pl e = (\<exists>n. (e,n)\<in>elements pl \<and> (e,n)\<notin>tombstones pl)"

definition getElements :: "'a payload \<Rightarrow> 'a set" where
"getElements pl = {e. contains pl e}"

fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
  "update (Add e) r pl = add r pl e"
| "update (Remove e) r pl = remove r pl e"

fun getValue :: "'a queryArgs \<Rightarrow> 'a payload \<Rightarrow> 'a result" where
  "getValue (Contains e) pl = ContainsResult (contains pl e)"
| "getValue (GetElements) pl = GetElementsResult (getElements pl)"

definition ORsetSimple where
"ORsetSimple = \<lparr> 
      t_compare = (\<lambda>A B. elements A \<subseteq> elements B \<and> tombstones A \<subseteq> tombstones B \<and> versionVec A \<le> versionVec B),
      t_merge   = (\<lambda>A B. (elements A \<union> elements B, tombstones A \<union> tombstones B, sup (versionVec A) (versionVec B))),
      t_initial = ({}, {}, vvZero),
      t_update  = update,
      t_query   = getValue       
  \<rparr>"


end


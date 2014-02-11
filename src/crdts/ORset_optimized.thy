theory ORset_optimized
imports 
ORset_spec
begin

(*
Observed-Remove Set, specification 3 in "An optimized Conflict-free Replicated Set"
*)

type_synonym 'a payload = "(versionVector \<times> ('a \<times> nat \<times> replicaId) set)"

abbreviation versionVec :: "'a payload \<Rightarrow> versionVector" where
"versionVec x \<equiv> fst x"

abbreviation elements :: "'a payload \<Rightarrow> ('a \<times> nat \<times> replicaId) set" where
"elements x \<equiv> (snd x)"

fun contains :: "'a payload \<Rightarrow> 'a \<Rightarrow> bool" where
"contains pl e = (\<exists>c i. (e,c,i)\<in>elements pl)"

definition getElements :: "'a payload \<Rightarrow> 'a set" where
"getElements pl = {e. \<exists>c i. (e,c,i)\<in>elements pl}"

definition add :: "replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a \<Rightarrow> 'a payload" where
"add r pl e = (
    let c   = (versionVec pl)\<guillemotright>r + 1;
        Old = {(e',c',r'). e=e'\<and> r=r' \<and> (e,c',r)\<in>elements pl \<and> c' < c}
    in (incVV r (versionVec pl), elements pl \<union> {(e,c,r)} - Old))"

definition remove :: "replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a \<Rightarrow> 'a payload" where
"remove myId pl e = (let R = {(e',c,i). e=e' \<and> (e',c,i)\<in>elements pl} in 
    (versionVec pl, elements pl - R))"

fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
  "update (Add e) r pl = add r pl e"
| "update (Remove e) r pl = remove r pl e"

fun getValue :: "'a queryArgs \<Rightarrow> 'a payload \<Rightarrow> 'a result" where
  "getValue (Contains e) pl = ContainsResult (contains pl e)"
| "getValue (GetElements) pl = GetElementsResult (getElements pl)"

definition compare2:: "'a payload \<Rightarrow> 'a payload \<Rightarrow> bool" where
"compare2 A B = (
    versionVec A \<le> versionVec B 
  \<and> (\<forall>c i. ((c > (versionVec B)\<guillemotright>i \<or> (\<exists>e. (e, c, i) \<in> elements B)) 
           \<longrightarrow> (c > (versionVec A) \<guillemotright> i \<or> (\<exists>e. (e, c, i) \<in> elements A)))) 
  \<and> (\<forall>e1 e2 c i. (e1,c,i)\<in>elements A \<and> (e2,c,i)\<in>elements B \<longrightarrow> e1=e2)
)"

definition merge:: "'a payload \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"merge A B = (
  let M   = elements A \<inter> elements B;
      M'  = {(e,c,i). (e,c,i)\<in>elements A - elements B \<and> c > (versionVec B)\<guillemotright>i};
      M'' = {(e,c,i). (e,c,i)\<in>elements B - elements A \<and> c > (versionVec A)\<guillemotright>i};
      U   = M \<union> M' \<union> M'';
      Old = {(e,c,i). (e,c,i)\<in>U \<and> (\<exists>c'. (e,c',i)\<in>U \<and> c < c')}
  in (sup (versionVec A) (versionVec B), U - Old)
)"

definition ORsetOpt where
"ORsetOpt = \<lparr> 
      t_compare = compare2,
      t_merge   = merge,
      t_initial = (vvZero, {}),
      t_update  = update,
      t_query   = getValue        
  \<rparr>"

(* original compare function *)
definition compare:: "'a payload \<Rightarrow> 'a payload \<Rightarrow> bool" where
"compare A B = (
  let R  = {(c,i). 0<c \<and> c \<le> (versionVec A)\<guillemotright>i \<and> \<not>(\<exists>e. (e,c,i)\<in>elements A)};
      R' = {(c,i). 0<c \<and> c \<le> (versionVec B)\<guillemotright>i \<and> \<not>(\<exists>e. (e,c,i)\<in>elements B)}
  in versionVec A \<le> versionVec B \<and> R \<subseteq> R'
)"

end


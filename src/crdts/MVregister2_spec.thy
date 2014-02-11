theory MVregister2_spec
imports 
"../framework/specifications"
begin

(* MVregister2 is similar to MVregister, but assignments of the empty list are ignored *)

datatype 'a updateArgs = Assign "'a list"

definition mvRegisterSpec :: "('a updateArgs, unit, ('a \<times> versionVector) set) crdtSpecification" where
"mvRegisterSpec H _ = 
   ({(x,c). (\<exists>r l v. x\<in>set l \<and> (v, Assign l)\<in>set(H r)
    \<and> (\<forall>rr. c\<guillemotright>rr = length (filter (\<lambda>e. updArgs e \<noteq> Assign [] \<and> updVersion e \<le> v ) (H rr)))
    \<and> \<not>(\<exists>l' vv. l' \<noteq> [] \<and> vv>v \<and> (vv, Assign l')\<in>allUpdates H))})"



end

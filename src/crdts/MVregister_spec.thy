theory MVregister_spec
imports 
"../framework/specifications" 
begin

datatype 'a updateArgs = Assign "'a list"
type_synonym 'a returnType = "('a \<times> versionVector) set"

definition mvRegisterSpec :: "('a updateArgs, unit, 'a returnType) crdtSpecification" where
"mvRegisterSpec H _ = {(x,v). 
       (\<forall>vv\<in>allVersions H. \<not>v<vv) 
    \<and> (\<exists>l. x\<in>set l \<and> (v,Assign l)\<in>allUpdates H)}"


end

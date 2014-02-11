theory MVregisterSingle_spec
imports 
"../framework/specifications" 
begin

datatype 'a updateArgs = Assign 'a
type_synonym 'a returnType = "'a set"

definition mvRegisterSpec :: "('a updateArgs, unit, 'a returnType) crdtSpecification" where
"mvRegisterSpec H _ = {(x). \<exists>e\<in>allUpdates H. updArgs(e) = Assign x \<and> \<not>(\<exists>f\<in>allUpdates H. e \<prec> f)}"

end

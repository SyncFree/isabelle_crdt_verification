theory twoPhaseSet_spec
imports 
"../framework/specifications"
begin

datatype 'a updateArgs = Add 'a | Remove 'a

(* x is in the set when there is an add operation and no remove operation *)
definition twoPhaseSetSpec :: "('a updateArgs,'a,bool) crdtSpecification" where
"twoPhaseSetSpec H x = (\<exists>e\<in>allUpdates H. updArgs(e) = Add x \<and> \<not>(\<exists>e\<in>allUpdates H. updArgs(e) = Remove x))"


end


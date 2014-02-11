theory twoPhaseSet2_spec
imports 
"../framework/specifications"
begin

(*
same as twoPhaseSet, but remove only has an effect if element is in the set
*)

datatype 'a updateArgs = Add 'a | Remove 'a

(* x is in the set when there is an add operation and no remove operation with an add operation before the remove *)
definition twoPhaseSetSpec :: "('a updateArgs,'a,bool) crdtSpecification" where
"twoPhaseSetSpec H x = ((\<exists>e\<in>allUpdates H. updArgs(e) = Add x) \<and> \<not>(\<exists>e\<in>allUpdates H. updArgs(e) = Remove x 
  \<and> (\<exists>f\<in>allUpdates H. updArgs(f) = Add(x) \<and> f \<prec> e)))" 


end


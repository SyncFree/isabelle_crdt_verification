theory gset_spec
imports 
"../framework/induction"
"../framework/helper" 
"../framework/convergence" 
begin

(* x is in the set when there is an add operation *)
definition gSetSpec :: "('a,'a,bool) crdtSpecification" where
"gSetSpec H x = (\<exists>e\<in>allUpdates H. updArgs(e) = x)"


end


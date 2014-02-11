theory PNCounter_spec
imports 
"../framework/specifications"
begin

definition pnCounterSpec :: "(int,unit,int) crdtSpecification" where
"pnCounterSpec H q = (\<Sum>e\<in>allUpdates H. updArgs(e))"

end

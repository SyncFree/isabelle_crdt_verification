theory IncrementOnlyCounter_spec
imports 
"../framework/specifications" 
begin

(* getValue returns the number of updates *)
definition counterSpec :: "(unit,unit,nat) crdtSpecification" where
"counterSpec H q = card(allUpdates H)"

end


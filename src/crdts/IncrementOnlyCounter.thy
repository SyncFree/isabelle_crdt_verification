theory IncrementOnlyCounter
imports 
"../framework/induction" 
"../framework/helper" 
"../framework/convergence"
begin



definition increment :: "unit \<Rightarrow> replicaId \<Rightarrow> versionVector \<Rightarrow> versionVector" where
"increment _ r = incVV r"

definition getValue :: "unit \<Rightarrow> versionVector \<Rightarrow> nat" where
"getValue _ v =  (\<Sum>r\<in>UNIV. v\<guillemotright>r)"

definition incrementOnlyCounter :: "(versionVector, unit, unit, nat) stateBasedType" where
"incrementOnlyCounter = \<lparr> 
      t_compare = op\<le>,
      t_merge   = sup,
      t_initial = vvZero,
      t_update  = increment,
      t_query   = getValue       
  \<rparr>"

(* convergence *)


lemma crdtProps: "crdtProperties incrementOnlyCounter (\<lambda>UH pl. True)"
apply (rule unfoldCrdtProperties)
apply (case_tac args)
apply (auto simp add: incrementOnlyCounter_def increment_def)
apply (simp add: incVVGreaterEq)
apply (simp add: sup_commute)
done




(* specification *)

(* getValue returns the number of updates *)
definition counterSpec :: "(unit,unit,nat) crdtSpecification" where
"counterSpec H q = card(allUpdates H)"

definition counterInvariant where
"counterInvariant H pl = (\<forall>r. pl\<guillemotright>r = length (H r))"


lemma invariantImpliesSpec:
assumes "validUpdateHistory H"
    and "counterInvariant H pl"
  shows "t_query incrementOnlyCounter qa pl = counterSpec H qa"
proof -
  have "(\<Sum>r\<in>UNIV. length (H r)) = card (\<Union>r. set (H r))" 
    using `validUpdateHistory H` 
    by (metis cardToLength)
  then have "(\<Sum>r\<in>UNIV. length (H r)) = card (allUpdates H)"
    by (metis allUpdates_def)
  thus ?thesis 
    using `counterInvariant H pl`
    by (simp add: counterInvariant_def incrementOnlyCounter_def getValue_def counterSpec_def allUpdates_def)
qed


theorem specValid: "crdtSpecificationValid incrementOnlyCounter counterSpec"
apply (rule_tac Inv="counterInvariant" in showCrdtSpecificationValid)
(* show that invariant implies spec *)
apply (metis invariantImpliesSpec invariantImpliesSpec_def)

(* show that invariant is maintained *)
apply (auto simp add: updateHistoryInvariant_all_def)

(* initial*)
apply (auto simp add: updateHistoryInvariant_initial_def)
apply (simp add: counterInvariant_def incrementOnlyCounter_def)

(* merge *) 
apply (auto simp add: updateHistoryInvariant_merge_def)
apply (simp add: counterInvariant_def incrementOnlyCounter_def)
apply clarsimp
apply (subst versionVectorSupComponent)
apply (auto simp add: historyUnion_def)

(* update *)
apply (auto simp add: updateHistoryInvariant_update_def)
apply (auto simp add: counterInvariant_def incrementOnlyCounter_def increment_def)
done




end


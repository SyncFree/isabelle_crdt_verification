theory simulations
imports specifications
begin

(*
when there is a bisimulation between two crdts
*)

definition couplingInitial where
"couplingInitial Inv crdtA crdtB = Inv (t_initial crdtA) (t_initial crdtB)"

definition couplingUpdate where
"couplingUpdate Inv crdtA crdtB = (\<forall>plA plB args r. Inv plA plB \<longrightarrow> Inv (t_update crdtA args r plA) (t_update crdtB args r plB))"

definition couplingMerge where
"couplingMerge Inv crdtA crdtB = (\<forall>plA1 plB1 plA2 plB2. Inv plA1 plB1 \<and> Inv plA2 plB2  \<longrightarrow> Inv (t_merge crdtA plA1 plA2) (t_merge crdtB plB1 plB2))"

definition couplingQuery where
"couplingQuery Inv crdtA crdtB = (\<forall>plA plB args. Inv plA plB \<longrightarrow> t_query crdtA args plA = t_query crdtB args plB)"

definition coupling where
"coupling Inv crdtA crdtB = (
    couplingInitial Inv crdtA crdtB
  \<and> couplingUpdate Inv crdtA crdtB
  \<and> couplingMerge Inv crdtA crdtB
)"

lemma simulationH: "\<lbrakk>
steps crdtA trA (initialState crdtA) sA;
coupling Inv crdtA crdtB
\<rbrakk> \<Longrightarrow> \<exists>trB sB. steps crdtB trB (initialState crdtB) sB
  \<and> updateHistory trA = updateHistory trB
  \<and> replicaVersion trA = replicaVersion trB
  \<and> (\<forall>r. Inv (replicaPayload sA r) (replicaPayload sB r))
  \<and> (\<forall>v plA. (v,plA)\<in>history sA \<longrightarrow> (\<exists>plB. (v,plB)\<in>history sB \<and> Inv plA plB))"
apply (induct rule: stepsInitialInduct2)
(* initial *)
apply (rule_tac x="EmptyTrace" in exI)
apply (rule_tac x="initialState crdtB" in exI)
apply auto
apply (metis start)
apply (simp add: coupling_def couplingInitial_def initialState_def)
apply (simp add: initialState_def)
apply (simp add: coupling_def couplingInitial_def initialState_def)

(* update *)
apply (rule_tac x="Trace trB (Update r args)" in exI)
apply (rule exI)
apply (rule conjI)
apply (erule steps.step)
apply (rule step.update)
apply (auto simp add: Let_def)
apply (simp add: updateHistory_Update)
apply (simp add: coupling_def couplingUpdate_def)
apply (rule_tac x="t_update crdtB args r (replicaPayload sB r)" in exI)
apply auto
apply (metis stepsReplicaVersion)
apply (simp add: coupling_def couplingUpdate_def)
apply metis

(* merge *)
apply (frule_tac x="vv" in spec)
apply (drule_tac x="pl" in spec)
apply (drule(1) mp)
apply (erule exE)
apply (rule_tac x="Trace trB (MergePayload r vv plB)" in exI)
apply (rule exI)
apply (rule conjI)
apply (erule steps.step)
apply (rule step.merge)
apply (auto simp add: Let_def)
apply (simp add: coupling_def couplingMerge_def)
apply (metis couplingMerge_def coupling_def stepsReplicaVersion)
apply metis
done

theorem simulation: "\<lbrakk>
crdtSpecificationValid crdtA spec;
couplingQuery Inv crdtB crdtA;
coupling Inv crdtB crdtA
\<rbrakk> \<Longrightarrow> crdtSpecificationValid crdtB spec"
apply (auto simp add: crdtSpecificationValid_def)
apply (frule(1) simulationH)
apply auto
by (metis couplingQuery_def stepsReplicaVersion visibleUpdateHistory_def)

end

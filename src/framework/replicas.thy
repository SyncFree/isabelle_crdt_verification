theory replicas
imports Main
begin







text "Assume a fixed number of replicas:"

definition replicaCount :: nat where "replicaCount = (SOME i. i>0)"



lemma replicaCountGreaterZero[simp]: "replicaCount > 0"
by (unfold replicaCount_def, rule someI, auto)

typedef replicaId = "{x::nat. x < replicaCount}"
by (rule_tac x="0" in exI, auto)

instantiation replicaId :: equal begin
definition "equal_replicaId x y = (Rep_replicaId x = Rep_replicaId y)"
instance proof
qed (auto simp add: equal_replicaId_def  Rep_replicaId_inject)
end


definition replicaId0 where "replicaId0 = Abs_replicaId 0"

instantiation replicaId :: enum begin
definition enum_replicaId     :: "replicaId list" where 
  "enum_replicaId = map Abs_replicaId [0..<replicaCount]"
definition enum_all_replicaId :: "(replicaId \<Rightarrow> bool) \<Rightarrow> bool" where 
  "enum_all_replicaId P = (\<forall>r. P r)"
definition enum_ex_replicaId  :: "(replicaId \<Rightarrow> bool) \<Rightarrow> bool" where 
  "enum_ex_replicaId P = (\<exists>r. P r)" 
instance proof
show "(UNIV::replicaId set) = set enum_class.enum"
  apply (auto simp add: enum_replicaId_def)
  apply (case_tac x)
  apply auto
  done
show "distinct (enum_class.enum::replicaId list)"
  apply (auto simp add: enum_replicaId_def)
  apply (rule card_distinct)
  apply auto
  apply (subst card_image)
  apply (simp add: inj_on_def Abs_replicaId_inject)
  apply clarsimp
  done 
fix P::"replicaId\<Rightarrow>bool"
show "enum_class.enum_all P = Ball UNIV P"
  by (auto simp add: enum_all_replicaId_def)
show "enum_class.enum_ex P = Bex UNIV P"
  by (auto simp add: enum_ex_replicaId_def)
qed
end


end

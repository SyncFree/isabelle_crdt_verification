theory finalSetFold
imports Main
begin


inductive_set closure :: "('a\<Rightarrow>'a\<Rightarrow>'a)\<Rightarrow>'a set \<Rightarrow>'a set"
for f::"'a\<Rightarrow>'a\<Rightarrow>'a" and S::"'a set"
where
start: "x\<in>S \<Longrightarrow> x\<in>closure f S"
| closed: "x\<in>closure f S \<Longrightarrow> y\<in>closure f S \<Longrightarrow> f x y \<in> closure f S"

lemma closureMono2: "x \<in> closure f A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<in> closure f B"
apply (induct rule: closure.induct)
apply (metis closure.start in_mono)
apply (metis closure.closed)
done


definition commutativeOn :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set\<Rightarrow> bool" where 
"commutativeOn f S = (\<forall>x\<in>closure f S. \<forall>y\<in>closure f S. \<forall>z\<in>closure f S. f x (f y z) = f y (f x z))"

definition "idempotentOn f S = (\<forall>x\<in>closure f S. \<forall>y\<in>closure f S. f x (f x y) = f x y)"

lemma commutativeOnPart: "commutativeOn f A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> commutativeOn f B"
apply (auto simp add: commutativeOn_def)
by (metis closureMono2)

lemma commutativeOnPart2: "commutativeOn f (insert x A) \<Longrightarrow> commutativeOn f A"
by (metis commutativeOnPart subset_insertI)

lemma onS_fun_left_comm: "\<lbrakk>
commutativeOn f S;
x\<in>closure f S; y\<in>closure f S; z\<in>closure f S
\<rbrakk> \<Longrightarrow> f x (f y z) = f y (f x z)"
apply (simp add: commutativeOn_def)
done

lemma fold_graph_y_in_closure:
  "fold_graph f z A y \<Longrightarrow> commutativeOn f (insert z A) \<Longrightarrow> y\<in>closure f (insert z A)"
apply (induct set: fold_graph)
apply (metis closure.start insertI1)
apply (drule meta_mp)
apply (metis (full_types) commutativeOnPart2 insert_commute)
apply (metis (mono_tags) closure.closed closure.start closureMono2 insertI1 insert_mono subset_insertI)
done


lemma cl_fold_graph_insertE_aux:
  "fold_graph f z A y \<Longrightarrow> commutativeOn f (insert z A) \<Longrightarrow> a \<in> A \<Longrightarrow> \<exists>y'. y = f a y' \<and> fold_graph f z (A - {a}) y' \<and> y'\<in>closure f (insert z A)"
apply (induct set: fold_graph)
apply clarsimp
apply (case_tac "a\<in>A")
apply (drule meta_mp)
apply (metis commutativeOnPart2 insert_commute)
apply (drule meta_mp)
apply auto
apply (rule_tac x="f x y'" in exI)
apply auto
apply (rule_tac f=f in onS_fun_left_comm)
apply assumption
apply (metis closure.start insertCI)
apply (metis closure.start insertCI)
apply (metis (full_types) closureMono2 insert_mono subset_insertI)
apply (metis empty_iff fold_graph.simps insert_Diff insert_Diff_if insert_iff)
apply (metis (mono_tags) closure.closed closure.start closureMono2 insert_mono insert_subset subset_insertI)

apply (rule_tac x="y" in exI)
apply auto
apply (frule fold_graph_y_in_closure)
apply (metis (full_types) commutativeOnPart2 insert_commute)
apply (metis (full_types) closureMono2 insert_commute subset_insertI)
done

lemma cl_fold_graph_insertE: "\<lbrakk>
fold_graph f z (insert x A) v;
commutativeOn f (insert z (insert x A));
x \<notin> A
\<rbrakk> \<Longrightarrow> \<exists>y. v = f x y \<and> fold_graph f z A y"
apply (frule_tac a=x in cl_fold_graph_insertE_aux)
apply auto
done

lemma cl_fold_graph_determ:
  "fold_graph f z A x \<Longrightarrow> fold_graph f z A y \<Longrightarrow>
  commutativeOn f (insert z A) \<Longrightarrow> y = x"
apply (induct arbitrary: y set: fold_graph)
apply (metis empty_fold_graphE)
apply (frule cl_fold_graph_insertE)
apply simp
apply simp
apply clarsimp
apply (drule_tac x=yb in meta_spec)
apply auto
apply (drule meta_mp)
apply (metis (full_types) commutativeOnPart2 insert_commute)
apply clarsimp
done

lemma cl_fold_equality:
  "fold_graph f z A y \<Longrightarrow> commutativeOn f (insert z A) \<Longrightarrow> finite A \<Longrightarrow> Finite_Set.fold f z A = y"
apply (simp add: Finite_Set.fold_def)
apply (blast intro: cl_fold_graph_determ)
done

lemma cl_fold_graph_fold: "\<lbrakk>
finite A;
commutativeOn f (insert z A)
\<rbrakk> \<Longrightarrow> fold_graph f z A (Finite_Set.fold f z A)"
by (metis (full_types) cl_fold_equality finite_imp_fold_graph)

lemma cl_fold_equality2:
"Finite_Set.fold f z A = y \<Longrightarrow>
 commutativeOn f (insert z A)  \<Longrightarrow>
 finite A \<Longrightarrow>
 fold_graph f z A y"
apply (unfold Finite_Set.fold_def)
apply auto
apply (rule_tac a="Finite_Set.fold f z A" in theI)
apply (metis cl_fold_graph_fold)
by (metis cl_fold_equality)



lemma cl_fold_insert [simp]: "\<lbrakk>
finite A;
x \<notin> A;
commutativeOn f (insert z (insert x A))
\<rbrakk> \<Longrightarrow> Finite_Set.fold f z (insert x A) = f x (Finite_Set.fold f z A)"
apply (rule cl_fold_equality)
apply (metis cl_fold_graph_fold commutativeOnPart2 fold_graph.insertI insert_commute)
apply auto
done


lemma fold_in_closure: " commutativeOn f (insert z F) \<Longrightarrow>
finite F \<Longrightarrow>
Finite_Set.fold f z F \<in> closure f (insert z F)"
by (metis cl_fold_equality2 fold_graph_y_in_closure)

lemma fold_in_closure2: " commutativeOn f S \<Longrightarrow>
finite F \<Longrightarrow>
F \<subseteq> S \<Longrightarrow>
z\<in>S \<Longrightarrow>
Finite_Set.fold f z F \<in> closure f S"
by (metis (mono_tags) closureMono2 commutativeOnPart fold_in_closure insert_subset)

lemma cl_fold_insert_remove: "\<lbrakk>
finite A; 
commutativeOn f (insert z (insert x A))
\<rbrakk> \<Longrightarrow> Finite_Set.fold f z (insert x A) = f x (Finite_Set.fold f z (A - {x}))"
by (metis (lifting, no_types) DiffD2 finite_Diff cl_fold_insert insertI1 insert_Diff_single)

lemma idemPotent: "\<lbrakk>
idempotentOn f S;
x\<in>closure f S;
y\<in>closure f S
\<rbrakk> \<Longrightarrow> f x (f x y) = f x y"
apply (simp add: idempotentOn_def)
done

lemma cl_fold_insert_idem: "\<lbrakk>
finite S;
commutativeOn f (S \<union> {x,b});
idempotentOn f (S \<union> {x,b})
\<rbrakk> \<Longrightarrow> Finite_Set.fold f b (insert x S) = f x (Finite_Set.fold f b S)"
apply (case_tac "x\<in>S")
apply auto
defer
apply (metis cl_fold_insert insert_commute)
apply (rule_tac 
  t="(Finite_Set.fold f b S)" and 
  s="(Finite_Set.fold f b (insert x (S - {x})))" 
  in ssubst)
apply simp
apply (metis insert_absorb)
apply (rule sym)
apply (subst cl_fold_insert)
apply simp+
apply (metis insert_commute)
apply (subst idemPotent[where f=f])
apply assumption
apply (metis closure.start insertI1)
apply (rule fold_in_closure2)
apply assumption
apply force
apply clarsimp
apply clarsimp
by (metis cl_fold_insert_remove insert_commute)

end


theory ORsetOptimizedConvergence
imports ORsetOptimized 
"../framework/helper" 
"../framework/convergence" 
begin 


definition invariant_c_unique :: "'a payload \<Rightarrow> bool" where
"invariant_c_unique A = (\<forall>e i c1 c2. (e,c1,i)\<in>elements A \<and> (e,c2,i)\<in>elements A \<longrightarrow> c1=c2)"

definition invariant_e_unique :: "'a payload \<Rightarrow> bool" where
"invariant_e_unique A = (\<forall>e1 e2 i c. (e1,c,i)\<in>elements A \<and> (e2,c,i)\<in>elements A \<longrightarrow> e1=e2)"

definition invariant_c_upper_bound :: "'a payload \<Rightarrow> bool" where
"invariant_c_upper_bound A = (\<forall>e c i. (e,c,i)\<in>elements A \<longrightarrow> c\<le>(versionVec A)\<guillemotright>i)"

definition invariant_c_lower_bound :: "'a payload \<Rightarrow> bool" where
"invariant_c_lower_bound A = (\<forall>e c i. (e,c,i)\<in>elements A \<longrightarrow> 0<c)"

definition invariant :: "'a payload \<Rightarrow> bool" where
"invariant A = (invariant_c_unique A \<and> invariant_e_unique A \<and>invariant_c_upper_bound A \<and> invariant_c_lower_bound A)"

lemma invariantUnfold: "invariant A = (
  (\<forall>e i c1 c2. (e,c1,i)\<in>elements A \<and> (e,c2,i)\<in>elements A \<longrightarrow> c1=c2)
\<and> (\<forall>e1 e2 i c. (e1,c,i)\<in>elements A \<and> (e2,c,i)\<in>elements A \<longrightarrow> e1=e2)
\<and> (\<forall>e c i. (e,c,i)\<in>elements A \<longrightarrow> c\<le>(versionVec A)\<guillemotright>i)
\<and> (\<forall>e c i. (e,c,i)\<in>elements A \<longrightarrow> 0<c)
)"
by (simp add: invariant_def invariant_c_unique_def invariant_e_unique_def invariant_c_upper_bound_def invariant_c_lower_bound_def)


lemma invariantLowerBound: "invariant (va,A) \<Longrightarrow> (e,c,i)\<in>A \<Longrightarrow> 0<c"
apply (auto simp add: invariant_def invariant_c_lower_bound_def)
done

lemma invariantUpperBound: "invariant (va,A) \<Longrightarrow> (e,c,i)\<in>A \<Longrightarrow> c\<le>va\<guillemotright>i"
apply (auto simp add: invariant_def invariant_c_upper_bound_def)
done

lemma invariantCunique: "invariant (va,A) \<Longrightarrow> (e,c1,i)\<in>A \<Longrightarrow> (e,c2,i)\<in>A \<Longrightarrow> c1 = c2"
apply (auto simp add: invariant_def invariant_c_unique_def)
done

lemma invariantEunique: "invariant (va,A) \<Longrightarrow> (e1,c,i)\<in>A \<Longrightarrow> (e2,c,i)\<in>A \<Longrightarrow> e1 = e2"
apply (auto simp add: invariant_def invariant_e_unique_def)
done

(* slightly easier merge function *)
definition merge2:: "'a payload \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"merge2 A B = (
  let M   = elements A \<inter> elements B;
      M'  = {(e,c,i). (e,c,i)\<in>elements A \<and> c > (versionVec B)\<guillemotright>i};
      M'' = {(e,c,i). (e,c,i)\<in>elements B \<and> c > (versionVec A)\<guillemotright>i};
      U   = M \<union> M' \<union> M'';
      U' = Set.filter (\<lambda>(e,c,i). (\<forall>c'. (e,c',i)\<in>U \<longrightarrow> c' \<le> c)) U
  in (sup (versionVec A) (versionVec B), U')
)"

lemma setFilterAlt:"Set.filter f A = A - {x. x\<in>A \<and> \<not>f x}"
by auto

lemma mergeAlt: "merge A B = merge2 A B"
apply (unfold merge_def merge2_def Let_def)
apply (subst setFilterAlt)
apply fastforce
done


lemma compareRefl: "invariant A \<Longrightarrow> compare2 A A"
apply (auto simp add: compare2_def invariant_def invariant_e_unique_def)
done

lemma compareTrans: "\<lbrakk>compare2 x y; compare2 y z; invariant x; invariant y; invariant z\<rbrakk> \<Longrightarrow> compare2 x z"
apply (case_tac x)
apply (case_tac y)
apply (case_tac z)
apply clarsimp
apply (rename_tac vx x vy y vz z)
apply (auto simp add: compare2_def)
apply metis
apply metis
by (metis invariantUpperBound le_less_trans not_less versionVectorLessEqE)


lemma compareAntisym: "invariant x \<Longrightarrow> invariant y \<Longrightarrow> compare2 x y \<Longrightarrow> compare2 y x \<Longrightarrow> x = y"
apply (case_tac x)
apply (case_tac y)
apply clarsimp
apply (rename_tac vx x vy y)
apply (auto simp add: compare2_def)
by (metis invariantUpperBound not_less)+


lemma mergeSym2: "merge A B = merge B A"
apply (auto simp add: merge_def sup.commute)
done

lemma mergeMono1: "invariant A \<Longrightarrow> invariant B \<Longrightarrow> compare2 A (merge A B)"
apply (case_tac A)
apply (case_tac B)
apply clarsimp
apply (rename_tac va A vb B)
apply (auto simp add: mergeAlt merge2_def)
apply (auto simp add: compare2_def)
apply (metis less_trans nat_neq_iff sup_ge1 versionVectorNotLessEqI)
apply (metis invariantEunique)
apply (metis invariantEunique)
by (metis invariantUpperBound not_less)


lemma mergeInvariant: "\<lbrakk>invariant A; invariant B\<rbrakk> \<Longrightarrow> invariant (merge A B)"
apply (case_tac A)
apply (case_tac B)
apply (rename_tac av ae bv be)
apply (subst invariantUnfold)
apply (simp add: mergeAlt merge2_def)
apply safe
apply (simp add: antisym)+
apply (metis invariantEunique)
apply (metis invariantUpperBound not_less)
apply (metis invariantUpperBound not_less)
apply (metis invariantUpperBound not_less)
apply (metis invariantUpperBound not_less)
apply (metis invariantEunique)
apply (metis invariantUpperBound not_less)
apply (metis invariantUpperBound not_less)
apply (metis invariantEunique)
apply (metis invariantUpperBound order_trans sup_ge2 versionVectorLessEqE)
apply (metis invariantUpperBound order_trans sup_ge1 versionVectorLessEqE)
apply (metis invariantUpperBound order_trans sup_ge2 versionVectorLessEqE)
apply (metis invariantLowerBound)
apply (metis le0 leD neq0_conv)
by (metis invariantLowerBound)


lemma mergeIsLeastUpperBound: "\<lbrakk>
compare2 y x;
compare2 z x;
invariant x;
invariant y;
invariant z
\<rbrakk> \<Longrightarrow> compare2 (merge y z) x"
apply (unfold mergeAlt)
apply (case_tac x)
apply (case_tac y)
apply (case_tac z)
apply (rename_tac xv xe yv ye zv ze)
apply (auto simp add: merge2_def compare2_def)
apply (metis le_less_trans le_sup_iff less_eq_versionVector_def)
defer
apply metis
apply metis
apply metis
apply (rename_tac ccc iii eee)
apply (rotate_tac -1)
apply (drule_tac x="eee" in spec)
apply (subst versionVectorSupComponent)
apply auto
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply (metis invariantCunique le_eq_less_or_eq)
apply (metis invariantCunique order_refl)
apply (metis invariantCunique le_eq_less_or_eq)
apply (metis (hide_lams, mono_tags) invariantCunique invariantUpperBound nat_less_le order_trans)
apply (metis (hide_lams, mono_tags) invariantCunique invariantUpperBound nat_less_le order_trans)
by (metis invariantCunique le_eq_less_or_eq)


lemma invariantBot: "invariant (vvZero, {})"
by (auto simp add: invariantUnfold)





lemma addInvariant: "invariant pl \<Longrightarrow> invariant (add r pl e)"
apply (auto simp add: invariantUnfold add_def Let_def le_imp_less_Suc)
apply (metis Suc_n_not_le_n)
apply (metis Suc_n_not_le_n)
apply (metis Suc_n_not_le_n)
apply (metis Suc_n_not_le_n)
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply metis
apply (metis incVVGreaterEq le_less_trans less_eq_versionVector_def not_less)
apply (metis incVVGreaterEq le_less_trans less_eq_versionVector_def not_less)
apply metis
apply metis
apply metis
done

lemma addIncreases:"invariant pl \<Longrightarrow> compare2 pl (add r pl e)"
apply (case_tac pl)
apply clarsimp
apply (rename_tac va A)
apply (auto simp add: invariantUnfold add_def Let_def compare2_def)
apply (metis incVVGreaterEq)
apply (metis incVVGreater le_less_trans less_versionVector_def)
apply (metis Suc_n_not_le_n)
apply (metis Suc_n_not_le_n)
apply metis
apply metis
apply metis
by metis

lemma removeInvariant: "invariant pl \<Longrightarrow> invariant (remove r pl e)"
apply (auto simp add: invariantUnfold remove_def Let_def)
apply metis
by metis

lemma removeIncreases:"invariant pl \<Longrightarrow> compare2 pl (remove r pl e)"
apply (case_tac pl)
apply (auto simp add: invariantUnfold remove_def Let_def compare2_def)
by metis



theorem ORsetSimple_crdtProps: "crdtProperties ORsetOpt (\<lambda>H pl. invariant pl)"
apply (auto simp add: crdtProperties_def)


apply (simp add: monotonicUpdates_def ORsetOpt_def)
apply clarsimp
apply (case_tac args, auto)
apply (metis addIncreases)
apply (metis removeIncreases)

apply (auto simp add: semilatticeProperties_def)
apply (simp add: compareReflexive_def ORsetOpt_def)
apply (metis compareRefl)
apply (simp add: compareTransitive_def ORsetOpt_def)
apply (metis compareTrans)
apply (simp add: compareAntisym_def ORsetOpt_def)
apply (metis compareAntisym prod.inject)
apply (simp add: mergeCommute_def ORsetOpt_def)
apply (metis mergeSym2)
apply (simp add: mergeUpperBound_def ORsetOpt_def)
apply (metis mergeMono1)
apply (simp add: mergeLeastUpperBound_def ORsetOpt_def)
apply (metis mergeIsLeastUpperBound)


apply (auto simp add: invariantPreserving_def  ORsetOpt_def invariantInitial_def invariantMerge_def invariantUpdate_def invariantUpdateOther_def)
apply (metis invariantBot)
apply (metis mergeInvariant)
apply (metis addInvariant removeInvariant update.simps(1) update.simps(2) updateArgs.exhaust)
done

lemma compareToMerge: "\<lbrakk>
invariant (va,A); invariant (vb,B);
compare2 (va,A) (vb,B)
\<rbrakk> \<Longrightarrow>  merge (va,A) (vb,B) = (vb, B)"
apply (unfold compare2_def mergeAlt merge2_def)
apply (auto simp add: sup_absorb1 sup_absorb2)
apply (metis invariantUpperBound less_le_trans versionVectorNotLessEqI)
apply metis
apply metis
apply (metis invariantCunique le_eq_less_or_eq)
apply (metis invariantUpperBound less_le_trans versionVectorNotLessEqI)
by (metis invariantCunique le_eq_less_or_eq)


lemma mergeToCompare: "\<lbrakk>
invariant (va,A); invariant (vb,B);
merge (va,A) (vb,B) = (vb, B)
\<rbrakk> \<Longrightarrow>  compare2 (va,A) (vb,B)"
apply (unfold compare2_def mergeAlt merge2_def)
apply (auto simp add: sup_absorb1 sup_absorb2)
apply (metis le_iff_sup)
apply (metis less_le_trans not_leE sup_commute sup_ge2 versionVectorNotLessEqI)
apply (rule ccontr)
apply (subgoal_tac "(e,c,i) \<notin>  Set.filter
             (\<lambda>(e, c, i).
                 \<forall>c'. ((e, c', i) \<in> A \<and> (e, c', i) \<in> B \<longrightarrow> c' \<le> c) \<and> ((e, c', i) \<in> A \<and> vb \<guillemotright> i < c' \<longrightarrow> c' \<le> c) \<and> ((e, c', i) \<in> B \<and> va \<guillemotright> i < c' \<longrightarrow> c' \<le> c))
             (A \<inter> B \<union> {(e, c, i). (e, c, i) \<in> A \<and> vb \<guillemotright> i < c} \<union> {(e, c, i). (e, c, i) \<in> B \<and> va \<guillemotright> i < c})")
apply simp
apply (thin_tac "Set.filter ?f ?x = ?y")
apply clarsimp
apply (rule ccontr)
apply (subgoal_tac "(e2,c,i) \<notin> Set.filter
        (\<lambda>(e, c, i). \<forall>c'. ((e, c', i) \<in> A \<and> (e, c', i) \<in> B \<longrightarrow> c' \<le> c) \<and> ((e, c', i) \<in> A \<and> vb \<guillemotright> i < c' \<longrightarrow> c' \<le> c) \<and> ((e, c', i) \<in> B \<and> va \<guillemotright> i < c' \<longrightarrow> c' \<le> c))
        (A \<inter> B \<union> {(e, c, i). (e, c, i) \<in> A \<and> vb \<guillemotright> i < c} \<union> {(e, c, i). (e, c, i) \<in> B \<and> va \<guillemotright> i < c})")
apply simp
apply (thin_tac "Set.filter ?f ?x = ?y")
apply auto
apply (metis invariantEunique)
apply (metis invariantUpperBound leD)
by (metis invariantUpperBound leD)


lemma compareIffMerge: "\<lbrakk>
invariant A; invariant B
\<rbrakk> \<Longrightarrow> compare2 A B \<longleftrightarrow> merge A B = B"
apply (case_tac A)
apply (case_tac B)
by (metis compareToMerge mergeToCompare)

end

theory versionvectors
imports Main replicas supSet
begin

(* version vectors*)
datatype versionVector = VersionVector "replicaId \<Rightarrow> nat"

definition vvZero :: "versionVector" where 
"vvZero = VersionVector (\<lambda>r. 0)"

fun vvRep :: "versionVector \<Rightarrow> (replicaId \<Rightarrow> nat)" where
"vvRep (VersionVector f) = f"

fun vvGet :: "versionVector \<Rightarrow> replicaId \<Rightarrow> nat" (infixr "\<guillemotright>" 100) where
"vvGet (VersionVector f) r = f r"

fun vvSet :: "versionVector \<Rightarrow> replicaId \<Rightarrow> nat \<Rightarrow> versionVector" ("_\<guillemotright>'(_ := _ ')" 101) where
"vvSet (VersionVector f) r n = VersionVector (f(r := n))"

fun vvUpdate :: "(nat \<Rightarrow> nat) \<Rightarrow> replicaId \<Rightarrow> versionVector \<Rightarrow> versionVector" where
"vvUpdate f r vv = (vv\<guillemotright>(r:= f (vv\<guillemotright>r)))"

definition component :: "replicaId \<Rightarrow> versionVector \<Rightarrow> nat" where
"component r v = v\<guillemotright>r"

definition incVV :: "replicaId \<Rightarrow> versionVector \<Rightarrow> versionVector" where
"incVV rep vv = (vv\<guillemotright>(rep := vv\<guillemotright>rep + 1))"

definition decVV :: "replicaId \<Rightarrow> versionVector \<Rightarrow> versionVector" where
"decVV rep vv = (vv\<guillemotright>(rep := vv\<guillemotright>rep - 1))"




(*partial order on versionVectors*)
instantiation versionVector :: order begin
definition less_eq_versionVector  :: "versionVector \<Rightarrow> versionVector \<Rightarrow> bool" where
  "less_eq_versionVector x y = (\<forall>r. x\<guillemotright>r \<le> y\<guillemotright>r)"

definition less_versionVector :: "versionVector \<Rightarrow> versionVector \<Rightarrow> bool" where
  "less_versionVector x y = (x\<noteq>y \<and> (\<forall>r. (x\<guillemotright>r) \<le> (y\<guillemotright>r)))"
instance proof
  fix x::versionVector
  fix y::versionVector
  fix z::versionVector
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    apply (auto simp add: less_versionVector_def less_eq_versionVector_def)
    apply (case_tac x)
    apply (case_tac y)
    apply clarsimp
    apply (rename_tac x y)
    by (metis ext le_antisym)
  show "x \<le> x"
    by (auto simp add: less_eq_versionVector_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" 
    apply (auto simp add: less_eq_versionVector_def )
    apply (drule_tac x="r" in spec)+
    by (metis le_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    apply (auto simp add: less_eq_versionVector_def )
    apply (case_tac x)
    apply (case_tac y)
    apply clarsimp
    apply (rename_tac x y)
    apply (rule ext)
    apply (drule_tac x="xa" in spec)+
    by (metis le_antisym)
  qed
end

instantiation versionVector :: semilattice_sup begin
definition "sup_versionVector a b = VersionVector (\<lambda>r. max (a\<guillemotright>r) (b\<guillemotright>r))"
instance proof
qed (auto simp add: less_eq_versionVector_def sup_versionVector_def)
end

instantiation versionVector :: order_bot begin
definition "bot_versionVector = vvZero"
instance proof
fix a::versionVector
show "bot \<le> a" by (auto simp add: less_eq_versionVector_def bot_versionVector_def vvZero_def)
qed
end


definition vvParallel (infixr "\<parallel>" 65) where
"vvParallel x y = ((\<exists>r. x\<guillemotright>r < y\<guillemotright>r) \<and> (\<exists>r. y\<guillemotright>r < x\<guillemotright>r))"


lemma vvParallel: "x\<parallel>y = (\<not>x\<le>y \<and> \<not>y\<le>x)"
apply (auto simp add: vvParallel_def less_eq_versionVector_def)
by (metis not_less)+

lemma vvParallel3[simp]: "x\<parallel>y \<or> y \<le> x = (\<not>x<y)"
apply (auto simp add: vvParallel)
by (metis less_le)



lemma incVVGreater: "vv < incVV r vv"
apply (unfold less_versionVector_def less_eq_versionVector_def incVV_def)
apply (case_tac vv)
apply clarsimp
by (metis fun_upd_same n_not_Suc_n)

lemma incVVGreaterEq: "vv \<le> incVV r vv"
by (metis incVVGreater less_le)


lemma versionVectorLessEqI[intro]: 
assumes "\<And>r. (a\<guillemotright>r) \<le> (b\<guillemotright>r)"
shows "a \<le> b"
by (metis assms less_eq_versionVector_def)

lemma versionVectorLess[intro]: 
assumes "a\<le>b"
   and "(a\<guillemotright>r) < (b\<guillemotright>r)"
shows "a < b"
by (metis assms(1) assms(2) le_neq_trans less_irrefl)

lemma versionVectorNotLessEqI[intro]: 
assumes "(a\<guillemotright>r) > (b\<guillemotright>r)"
shows "\<not> a \<le> b"
by (metis assms less_le_not_le less_versionVector_def versionVectorLess)

lemma versionVectorLessEqE[elim]: 
assumes "a \<le> b"
shows "(a\<guillemotright>r) \<le> (b\<guillemotright>r)"
by (metis assms less_eq_versionVector_def)





lemma versionVectorSupComponent: "(sup v1 v2)\<guillemotright>r = max (v1\<guillemotright>r) (v2\<guillemotright>r)"
by (metis sup_versionVector_def vvGet.simps)

lemma vvComponentToGet[simp]: "component r v = v\<guillemotright>r"
by (rule component_def)

lemma vvRepToGet[simp]: "vvRep v r = v\<guillemotright>r"
by (metis vvGet.simps vvRep.cases vvRep.simps)

lemma versionVectorEq: "(v = w) = (\<forall>r. (v\<guillemotright>r) = (w\<guillemotright>r))"
apply (case_tac v)
apply (case_tac w)
apply auto
done

lemma versionVectorSetSame[simp]: "v\<guillemotright>(r:=x)\<guillemotright>r = x"
by (metis fun_upd_same vvRep.cases vvRep.simps vvRepToGet vvSet.simps)

lemma versionVectorSetOther[simp]: "r1 \<noteq> r2 \<Longrightarrow> v\<guillemotright>(r1:=x)\<guillemotright>r2 = v\<guillemotright>r2"
by (metis fun_upd_apply vvRep.cases vvRep.simps vvRepToGet vvSet.simps)

lemma versionVectorSet[simp]: "v\<guillemotright>(r1:=x)\<guillemotright>r2 = (if r1=r2 then x else v\<guillemotright>r2)"
by auto

lemma vvZeroGet[simp]: "vvZero\<guillemotright>r = 0"
apply (unfold vvZero_def)
apply auto
done


lemma incVVr1[simp]: "((incVV r v)\<guillemotright>r) = (v\<guillemotright>r) + 1"
by (auto simp add: incVV_def)

lemma incVVr2[simp]:  "ra\<noteq>r \<Longrightarrow>((incVV r v)\<guillemotright>ra) = (v\<guillemotright>ra)"
by (auto simp add: incVV_def)

lemma componentSimp[simp]:"(\<lambda>v. v \<guillemotright> r) = component r"
by auto

lemma vvZeroLess: "a \<noteq> vvZero \<Longrightarrow> vvZero < a"
by (metis bot_less bot_versionVector_def)

lemma supSet_versionVectorComponent: "finite V \<Longrightarrow> ((supSet V)\<guillemotright> r) = supSet ((\<lambda>v. (v\<guillemotright>r)) ` V)"
apply (induct V rule: finite_induct)
apply (simp add: bot_versionVector_def bot_nat_def)
apply (subst supSetInsert)
apply simp
apply (subst image_insert)
apply (subst supSetInsert)
apply auto
apply (metis sup_max versionVectorSupComponent)
done


end



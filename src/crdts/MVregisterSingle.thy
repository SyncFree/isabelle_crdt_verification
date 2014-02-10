theory MVregisterSingle
imports induction helper convergence 
begin

datatype 'a updateArgs = Assign 'a
type_synonym 'a returnType = "'a set"

definition mvRegisterSpec :: "('a updateArgs, unit, 'a returnType) crdtSpecification" where
"mvRegisterSpec H _ = {(x). \<exists>e\<in>allUpdates H. updArgs(e) = Assign x \<and> \<not>(\<exists>f\<in>allUpdates H. e \<prec> f)}"

type_synonym 'a payload = "versionVector \<times> ('a \<times> versionVector) set"

fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
"update (Assign x) r (V,S) = (incVV r V, S \<union> {(x, incVV r V)})"

fun getValue :: "unit \<Rightarrow> 'a payload \<Rightarrow> 'a set" where
"getValue _ (V,S) = fst ` {(x,v)\<in>S. \<not>(\<exists>(x',v')\<in>S. v < v')}"

definition mvRegister where
"mvRegister = \<lparr> 
      t_compare = (\<lambda>x y. fst x \<le> fst y \<and> snd x \<subseteq> snd y),
      t_merge   = (\<lambda>x y. (sup (fst x) (fst y), snd x \<union> snd y)),
      t_initial = (vvZero, {}),
      t_update  = update,
      t_query   = getValue       
  \<rparr>"

lemma crdtProps: "crdtProperties mvRegister (\<lambda>H pl. True)"
apply (rule unfoldCrdtProperties)
apply (auto simp add: mvRegister_def)
apply (case_tac args, auto)
apply (metis incVVGreaterEq)
apply (case_tac args, auto)
apply (metis sup.commute)
done


definition mvRegisterInvariant :: "('a updateArgs) updateHistory \<Rightarrow> 'a payload \<Rightarrow> bool" where
"mvRegisterInvariant H pl = (
    (\<forall>v x. (x,v)\<in>snd pl \<longleftrightarrow> (\<exists>a\<in>allUpdates H. updVersion(a)=v \<and> updArgs(a) = Assign x))
  \<and> fst pl = updateHistoryVersion H)"

lemma mvRegisterInvariant1: "mvRegisterInvariant H pl \<Longrightarrow>
(x,v)\<in>snd pl \<Longrightarrow>
\<exists>a\<in>allUpdates H. updVersion(a)=v \<and> updArgs(a) = Assign x"
apply (auto simp add: mvRegisterInvariant_def)
done

lemma mvRegisterInvariant2: "mvRegisterInvariant H pl \<Longrightarrow>
\<exists>a\<in>allUpdates H. updVersion(a)=v \<and> updArgs(a) = Assign x \<Longrightarrow>
(x,v)\<in>snd pl"
apply (auto simp add: mvRegisterInvariant_def)
done

lemma mvRegisterInvariant3: "mvRegisterInvariant H pl \<Longrightarrow>
(v, Assign x)\<in>allUpdates H \<Longrightarrow>
(x,v)\<in>snd pl"
apply (frule_tac v=v and x=x in mvRegisterInvariant2)
apply auto
apply force
done

lemma mvRegisterInvariantVersion: "mvRegisterInvariant H pl \<Longrightarrow>
fst pl = updateHistoryVersion H
"
apply (auto simp add: mvRegisterInvariant_def)
done

lemma specValid: "crdtSpecificationValid mvRegister mvRegisterSpec"
apply (rule_tac Inv="mvRegisterInvariant" in showCrdtSpecificationValid)

(* invariant impies spec *)
apply (simp add: mvRegister_def mvRegisterSpec_def mvRegisterInvariant_def invariantImpliesSpec_def)
apply auto
apply (metis fst_conv snd_conv split_conv updateArgs.exhaust)
thm imageI
apply (cut_tac x="(x,a)" and f=fst and A="{(x, v). (\<exists>a\<in>allUpdates H. updVersion a = v \<and> updArgs a = Assign x) \<and> (\<forall>x\<in>b. \<not> (case x of (x', x) \<Rightarrow> v < x))}" in imageI)
apply auto
apply (metis fst_conv snd_conv)


apply (auto simp add:  updateHistoryInvariant_all_def)
(* invariant initial *)
apply (simp add:  updateHistoryInvariant_initial_def)
apply (simp add:  mvRegisterInvariant_def mvRegister_def)

(* merge *)
apply (auto simp add: updateHistoryInvariant_merge_def)
apply (subst mvRegisterInvariant_def)
apply (simp add: mvRegister_def)
apply auto
apply (metis Un_iff mvRegisterInvariant1 snd_eqD)
apply (metis Un_iff mvRegisterInvariant1 snd_eqD)
apply (metis mvRegisterInvariant3 snd_eqD)
apply (metis mvRegisterInvariant3 snd_eqD)

apply (metis fst_conv mvRegisterInvariantVersion updateHistoryVersion_historyUnion)

(* update *)
apply (auto simp add: updateHistoryInvariant_update_def)
apply (subst mvRegisterInvariant_def)
apply (simp add: mvRegister_def)
apply (case_tac args)
apply auto
apply (metis fst_eqD mvRegisterInvariant_def versionIsTopToUpdateHistoryVersion)
apply (metis mvRegisterInvariant1 snd_conv)
apply (metis mvRegisterInvariant1 snd_conv)
apply (metis fst_conv mvRegisterInvariant_def versionIsTopToUpdateHistoryVersion)
apply (metis mvRegisterInvariant3 snd_eqD)
apply (metis mvRegisterInvariant3 snd_eqD)
apply (metis fst_conv mvRegisterInvariant_def updateHistoryVersionUpdate)
done


end

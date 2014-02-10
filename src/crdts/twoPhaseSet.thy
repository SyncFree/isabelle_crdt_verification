theory twoPhaseSet
imports 
"../framework/induction"
"../framework/helper" 
"../framework/convergence" 
begin

type_synonym 'a payload = "'a set \<times> 'a set"

datatype 'a updateArgs = Add 'a | Remove 'a

fun update :: "'a updateArgs \<Rightarrow> replicaId \<Rightarrow> 'a payload \<Rightarrow> 'a payload" where
  "update (Add x) r (E,T) = (insert x E, T)"
| "update (Remove x) r (E,T) = (E, insert x T)"

fun lookup :: "'a \<Rightarrow> 'a payload \<Rightarrow> bool" where
"lookup x (E,T) = (x\<in>E \<and> x\<notin>T)"

definition twoPhaseSet :: "('a payload, 'a updateArgs, 'a, bool) stateBasedType" where
"twoPhaseSet = \<lparr> 
      t_compare = (\<lambda>x y. fst x \<subseteq> fst y \<and> snd x \<subseteq> snd y),
      t_merge   = (\<lambda>x y. (fst x \<union> fst y, snd x \<union> snd y)),
      t_initial = ({},{}),
      t_update  = update,
      t_query   = lookup      
  \<rparr>"

(* convergence *)
lemma ORsetSimple_crdtProps: "crdtProperties twoPhaseSet (\<lambda>UH pl. True)"
apply (rule unfoldCrdtProperties)
apply (auto simp add: twoPhaseSet_def)
apply (case_tac args, auto)+
done


(* specification *)

(* x is in the set when there is an add operation and no remove operation *)
definition twoPhaseSetSpec :: "('a updateArgs,'a,bool) crdtSpecification" where
"twoPhaseSetSpec H x = (\<exists>e\<in>allUpdates H. updArgs(e) = Add x \<and> \<not>(\<exists>e\<in>allUpdates H. updArgs(e) = Remove x))"

definition Inv where
"Inv H pl = (\<forall>x. (x\<in>fst pl \<longleftrightarrow> (\<exists>e\<in>allUpdates H. updArgs(e) = Add x)) 
  \<and> (x\<in>snd pl \<longleftrightarrow> (\<exists>e\<in>allUpdates H. updArgs(e) = Remove x)))"

lemma "crdtSpecificationValid twoPhaseSet twoPhaseSetSpec"
apply (rule_tac Inv="Inv" in showCrdtSpecificationValid)
(* show that invariant implies spec *)
apply (simp add: twoPhaseSet_def twoPhaseSetSpec_def Inv_def invariantImpliesSpec_def)

(* show that invariant is maintained *)
apply (auto simp add: updateHistoryInvariant_all_def)

(* initial*)
apply (auto simp add: updateHistoryInvariant_initial_def)
apply (simp add: Inv_def twoPhaseSet_def)

(* merge *) 
apply (auto simp add: updateHistoryInvariant_merge_def)
apply (simp add: Inv_def twoPhaseSet_def)
apply auto

(* update *)
apply (auto simp add: updateHistoryInvariant_update_def)
apply (simp add: Inv_def twoPhaseSet_def)
apply (case_tac args)
apply auto
done

end


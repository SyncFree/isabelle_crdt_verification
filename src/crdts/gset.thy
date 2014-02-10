theory gset
imports 
"../framework/induction"
"../framework/helper" 
"../framework/convergence" 
begin


definition add :: "'a \<Rightarrow> replicaId \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"add x r = insert x"

definition lookup :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where
"lookup x pl = (x\<in>pl)"

definition gSet :: "('a set, 'a, 'a, bool) stateBasedType" where
"gSet = \<lparr> 
      t_compare = op\<subseteq>,
      t_merge   = op\<union>,
      t_initial = {},
      t_update  = add,
      t_query   = lookup      
  \<rparr>"

(* convergence *)
lemma ORsetSimple_crdtProps: "crdtProperties gSet (\<lambda>UH pl. True)"
apply (rule unfoldCrdtProperties)
apply (auto simp add: gSet_def add_def)
done


(* specification *)

(* x is in the set when there is an add operation *)
definition gSetSpec :: "('a,'a,bool) crdtSpecification" where
"gSetSpec H x = (\<exists>e\<in>allUpdates H. updArgs(e) = x)"

definition gSetInvariant where
"gSetInvariant H pl = (\<forall>x. x\<in> pl \<longleftrightarrow> (\<exists>e\<in>allUpdates H. updArgs(e) = x))"

lemma "crdtSpecificationValid gSet gSetSpec"
apply (rule_tac Inv="gSetInvariant" in showCrdtSpecificationValid)
(* show that invariant implies spec *)
apply (simp add: gSet_def lookup_def gSetSpec_def gSetInvariant_def  invariantImpliesSpec_def)

(* show that invariant is maintained *)
apply (auto simp add: updateHistoryInvariant_all_def)

(* initial*)
apply (auto simp add: updateHistoryInvariant_initial_def)
apply (simp add: gSetInvariant_def gSet_def)

(* merge *) 
apply (auto simp add: updateHistoryInvariant_merge_def)
apply (auto simp add: gSetInvariant_def gSet_def)

(* update *)
apply (auto simp add: updateHistoryInvariant_update_def)
apply (auto simp add: gSetInvariant_def gSet_def add_def)
done

end


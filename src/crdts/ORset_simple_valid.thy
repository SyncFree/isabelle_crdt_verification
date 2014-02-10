theory ORset_simple_valid
imports ORset_spec
ORset_simple
"../framework/induction"
"../framework/helper"  
begin


definition ORsetInv :: "('a updateArgs) updateHistory \<Rightarrow> 'a payload \<Rightarrow> bool" where
"ORsetInv H pl = (\<forall>v x. 
    ((x,v)\<in>elements pl \<longleftrightarrow> (\<exists>a\<in>allUpdates H. updVersion(a)=v \<and> updArgs(a) = Add x))
  \<and> ((x,v)\<in>tombstones pl \<longleftrightarrow> (\<exists>a\<in>allUpdates H. \<exists>r\<in>allUpdates H. a \<prec> r \<and> updVersion(a)=v \<and> updArgs(a) = Add x \<and> updArgs(r) = Remove x))
  \<and> versionVec pl = updateHistoryVersion H)"

lemma OrSetInv_inElement: "ORsetInv H (E,T,V) \<Longrightarrow> (x,v)\<in>E \<Longrightarrow> \<exists>a\<in>allUpdates H. updVersion(a)=v \<and> updArgs(a) = Add x"
apply (auto simp add: ORsetInv_def)
done

lemma OrSetInv_notinElement: "ORsetInv H (E,T,V) \<Longrightarrow> (x,v)\<notin>E \<Longrightarrow> a\<in>allUpdates H \<Longrightarrow> updVersion(a)=v \<Longrightarrow> updArgs(a) \<noteq> Add x"
apply (auto simp add: ORsetInv_def)
done

lemma OrSetInv_notinElement2: "ORsetInv H (E,T,V) \<Longrightarrow> (x,v)\<notin>E \<Longrightarrow> (v,Add x)\<in>allUpdates H \<Longrightarrow> False"
by (metis OrSetInv_notinElement fst_conv snd_conv)

lemma OrSetInv_inTombstones: "ORsetInv H (E,T,V) \<Longrightarrow> (x,v)\<in>T \<Longrightarrow> \<exists>a\<in>allUpdates H. \<exists>r\<in>allUpdates H. a \<prec> r \<and> updVersion(a)=v \<and> updArgs(a) = Add x \<and> updArgs(r) = Remove x"
apply (auto simp add: ORsetInv_def)
done

lemma OrSetInv_inTombstonesI: "ORsetInv H (E,T,V) \<Longrightarrow> (va, Add x)\<in>allUpdates H \<Longrightarrow> (vr, Remove x)\<in>allUpdates H \<Longrightarrow> va < vr
  \<Longrightarrow> (x,va)\<in>T"
apply (auto simp add: ORsetInv_def)
by (metis fst_conv snd_conv)

lemma OrSetInv_notinTombstones: "ORsetInv H (E,T,V) \<Longrightarrow> (x,v)\<notin>T \<Longrightarrow> a\<in>allUpdates H \<Longrightarrow> r\<in>allUpdates H \<Longrightarrow> a \<prec> r \<Longrightarrow> updVersion(a)=v 
 \<Longrightarrow> updArgs(a) = Add x \<Longrightarrow> updArgs(r) \<noteq> Remove x"
apply (auto simp add: ORsetInv_def)
done

lemma OrSetInv_version: "ORsetInv H (E,T,V) \<Longrightarrow> V=updateHistoryVersion H"
apply (auto simp add: ORsetInv_def)
done


lemma counterSpecValid_invImpliesSpec: "validUpdateHistory H \<Longrightarrow> ORsetInv H (E, T, V) \<Longrightarrow> contains (E, T, V) xx = setSpecContains H xx"
apply (auto simp add: contains_def setSpecContains_def ORsetInv_def)
done





lemma setSpecValid: "crdtSpecificationValid ORsetSimple setSpec"
apply (rule_tac Inv="ORsetInv" in showCrdtSpecificationValid)
apply (simp add: ORsetSimple_def invariantImpliesSpec_def)
apply auto
apply (case_tac qa)
apply clarsimp
apply (rename_tac E T V xx)
apply (metis counterSpecValid_invImpliesSpec)
apply clarsimp
apply (auto simp add: getElements_def)
apply (metis counterSpecValid_invImpliesSpec)
apply (metis counterSpecValid_invImpliesSpec)

apply (auto simp add: updateHistoryInvariant_all_def)

(* initial *)
apply (simp add:  updateHistoryInvariant_initial_def ORsetSimple_def ORsetInv_def)

(* merge *)
apply (simp add: updateHistoryInvariant_merge_def ORsetSimple_def)
apply clarsimp
apply (rename_tac H1 E1 T1 V1 H2 E2 T2 V2)
apply (subst ORsetInv_def)
apply (auto simp add:)
apply (metis OrSetInv_inElement Un_iff)
apply (metis OrSetInv_inElement Un_iff)
apply (metis OrSetInv_notinElement fst_eqD snd_eqD)
apply (metis OrSetInv_notinElement fst_eqD snd_eqD)
apply (metis (full_types) OrSetInv_inTombstones Un_iff)
apply (metis (full_types) OrSetInv_inTombstones Un_iff)
apply (metis OrSetInv_notinTombstones fst_conv snd_conv)
apply (metis OrSetInv_notinTombstones consistentHistoriesHappensBefore fst_conv snd_conv)
apply (metis OrSetInv_notinTombstones consistentHistoriesHappensBefore2 fst_conv snd_conv)
apply (metis OrSetInv_notinTombstones fst_conv snd_conv)

apply (metis OrSetInv_version updateHistoryVersion_historyUnion)

(* update *)
apply (simp add: updateHistoryInvariant_update_def ORsetSimple_def)
apply clarsimp
apply (rename_tac E T V r v args)
apply (subst ORsetInv_def)
apply (case_tac args)
(*add x*)
apply (auto simp add: add_def Let_def)
apply (metis OrSetInv_version versionIsTopToUpdateHistoryVersion)
apply (metis OrSetInv_inElement)
apply (metis OrSetInv_inElement)
apply (metis OrSetInv_version versionIsTopToUpdateHistoryVersion)
apply (metis OrSetInv_notinElement2)
apply (metis OrSetInv_notinElement2)
apply (metis OrSetInv_inTombstones Pair_inject snd_conv surjective_pairing)
apply (metis incVVGreaterEq versionIsTopGreaterHistory less_le_not_le notinAllUpdatesI order_trans)
apply (metis OrSetInv_inTombstonesI)
apply (metis OrSetInv_version updateHistoryVersionUpdate)
(*remove x*)
apply (auto simp add: remove_def)
apply (metis OrSetInv_inElement)
apply (metis OrSetInv_notinElement2)
apply (metis OrSetInv_inTombstones)
apply (frule(1) OrSetInv_inElement)
apply clarsimp
apply (metis fst_conv incVVGreater versionIsTopGreaterHistory le_less_trans notinAllUpdatesI snd_conv)
apply (metis OrSetInv_notinElement2)
apply (metis OrSetInv_notinElement2)
apply (metis OrSetInv_inTombstonesI)
apply (metis OrSetInv_version updateHistoryVersionUpdate)
done


end


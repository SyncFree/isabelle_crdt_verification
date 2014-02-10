theory MVregister_impl_valid
imports 
MVregister_impl
"../framework/induction"
"../framework/helper" 
begin


definition mvRegisterInvariant :: "('a updateArgs) updateHistory \<Rightarrow> 'a payload \<Rightarrow> bool" where
"mvRegisterInvariant H pl = (
    (\<forall>v l. (l,v)\<in>snd pl \<longleftrightarrow> (\<exists>a\<in>allUpdates H. updVersion(a)=v \<and> updArgs(a) = Assign l))
  \<and> fst pl = updateHistoryVersion H)"

lemma mvRegisterInvariant1: "mvRegisterInvariant H pl \<Longrightarrow>
(l,v)\<in>snd pl \<Longrightarrow>
\<exists>a\<in>allUpdates H. updVersion(a)=v \<and> updArgs(a) = Assign l"
apply (auto simp add: mvRegisterInvariant_def)
done

lemma mvRegisterInvariant2: "mvRegisterInvariant H pl \<Longrightarrow>
\<exists>a\<in>allUpdates H. updVersion(a)=v \<and> updArgs(a) = Assign l \<Longrightarrow>
(l,v)\<in>snd pl"
apply (auto simp add: mvRegisterInvariant_def)
done

lemma mvRegisterInvariant3: "mvRegisterInvariant H pl \<Longrightarrow>
(v, Assign l)\<in>allUpdates H \<Longrightarrow>
(l,v)\<in>snd pl"
apply (frule_tac v=v and l=l in mvRegisterInvariant2)
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
apply (metis fst_eqD inAllUpdatesI notinAllVersionsI snd_conv updateArgs.exhaust)
apply (metis allUpdatesToReplica fst_conv notinAllVersions pair_collapse snd_conv)


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

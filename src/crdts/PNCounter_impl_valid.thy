theory PNCounter_impl_valid
imports 
PNCounter_impl
"../framework/induction"
"../framework/helper"  
begin

definition pnCounterInvariant where
"pnCounterInvariant H pl = (\<forall>r. (fst pl) r = listsum (map updArgs (filter (\<lambda>x. updArgs x \<ge> 0) (H r))) 
                              \<and> (snd pl) r = listsum (map (\<lambda>x. -updArgs(x)) (filter (\<lambda>x. updArgs x < 0) (H r))))"


lemma setsumRemove: "\<lbrakk>
finite A;
x\<in>A;
B = A - {x};
gx = g x;
\<And>x. x\<in>B \<Longrightarrow> f x = g x
\<rbrakk> \<Longrightarrow> setsum g A = gx + setsum f B"
apply auto
by (metis setsum_diff1')


lemma setsumPerReplica: "\<lbrakk>
finite S;
\<And>x. x\<in>S \<Longrightarrow> \<exists>r. x\<in>T r;
\<And>x r. x\<in>T r \<Longrightarrow> x\<in>S;
\<And>ra rb. ra\<noteq>rb \<Longrightarrow> T ra \<inter> T rb = {}
\<rbrakk> \<Longrightarrow> setsum f {x \<in> S. P x} = (\<Sum>r\<in>(UNIV::replicaId set). setsum f {x \<in> T r. P x}) "
apply (induct arbitrary: T rule:finite_induct)
apply auto
apply (subgoal_tac "\<forall>r. (\<Sum>x | x \<in> T r \<and> P x. f x) = 0")
apply auto
apply (rule_tac t="{x. x\<in>T r \<and> P x}" and s="{}" in ssubst)
apply clarsimp
apply metis
apply simp
apply (rename_tac y F T)
apply (case_tac "P y")
apply (rule_tac t="{x. (x = y \<or> x \<in> F) \<and> P x}" 
  and s="insert y {x. x \<in> F \<and> P x}" in ssubst)
apply force
apply clarsimp
apply (subgoal_tac "\<exists>r. y \<in> T r")
apply (erule exE)
apply (drule_tac x="T(r:=T r - {y})" in meta_spec)
apply (drule meta_mp)
apply clarsimp
apply metis
apply (drule meta_mp)
apply clarsimp
apply (metis Diff_iff IntI empty_iff insertCI)
apply (drule meta_mp)
apply clarsimp
apply (metis Int_Diff Int_commute empty_Diff)
apply clarsimp
apply (rule_tac t="\<lambda>rr. {x \<in> T rr. P x}"
  and s="\<lambda>rr. if rr=r then insert y {x\<in>T r. x\<noteq>y \<and> P x} else {x \<in> T rr. P x}" in ssubst)
apply (rule ext)
apply auto


apply (rule_tac t="(\<Sum>ra\<in>UNIV. setsum f {x \<in> if ra = r then T r - {y} else T ra. P x})"
  and s="(setsum f {x \<in> T r - {y}. P x}) + (\<Sum>ra\<in>UNIV-{r}. setsum f {x \<in> T ra. P x})" in ssubst)
apply (rule_tac x="r" in setsumRemove)
apply auto
apply (rule_tac t=" (\<Sum>ra\<in>UNIV. setsum f (if ra = r then insert y {x \<in> T r. x \<noteq> y \<and> P x} else {x \<in> T ra. P x}))"
  and s="setsum f ( insert y {x \<in> T r. x \<noteq> y \<and> P x}) + (\<Sum>ra\<in>UNIV-{r}. setsum f {x \<in> T ra. P x})" in ssubst)
apply (rule_tac x="r" in setsumRemove)
apply auto
apply (subst ab_semigroup_add_class.add_ac(1)[symmetric])
apply (rule_tac f="op+" in equalArgs2)
apply (rule setsum.insert[symmetric])
apply (rule_tac B="F" in finite_subset)
apply auto

(* case \<not> P y *)
apply (subgoal_tac "\<exists>r. y \<in> T r")
apply (erule exE)
apply (drule_tac x="T(r:=T r - {y})" in meta_spec)
apply (drule meta_mp)
apply auto
apply metis
apply (drule meta_mp)
apply (metis (mono_tags) Diff_iff Int_iff emptyE insertI1)
apply (drule meta_mp)
apply force

apply (rule_tac t="{x. (x = y \<or> x \<in> F) \<and> P x}"
  and s="{x. x\<in>F \<and> P x}" in ssubst)
apply auto

apply (subgoal_tac "\<forall>ra. {x \<in> if ra = r then T r - {y} else T ra. P x} = {x\<in>T ra. P x}")
apply auto
done

lemma setsumToListsum: "validUpdateHistory H \<Longrightarrow>
setsum f {x \<in> set (H r). P x}
= listsum (map f (filter P (H r)))"
by (metis distinct_filter listsum_distinct_conv_setsum_set set_filter updateHistoryDistinct)

lemma setsumToListsumPerReplica: "validUpdateHistory H \<Longrightarrow>setsum f (allUpdates H) = (\<Sum>x\<in>UNIV. listsum (map f (H x)))"
apply (rule_tac t="(allUpdates H)" and s="{x\<in>(allUpdates H). True}" in ssubst)
apply simp
apply (subst setsumPerReplica[where T="\<lambda>r. set (H r)"])
apply (metis allUpdatesFinite)
apply (metis notinAllUpdatesI)
apply (metis inAllUpdatesI)
apply auto
apply (metis validUpdateHistory_distinct)
apply (rule_tac f="setsum" in equalArgs2)
apply (rule ext)
apply (cut_tac f=f and H=H and r=r and P="\<lambda>x. True" in setsumToListsum)
apply assumption
apply auto
done


lemma becomesPrefix_Equal: "isPrefix xs (ys @ [y]) \<Longrightarrow> \<not> isPrefix xs ys \<Longrightarrow> xs=(ys@[y])"
apply (unfold isPrefixTake)
by (metis append_eq_conv_conj append_take_drop_id butlast_append butlast_snoc)


lemma prefixListsum: "\<lbrakk>
isPrefix xs ys;
\<And>x. x\<in>set ys \<Longrightarrow> (x::int)\<ge>0
\<rbrakk> \<Longrightarrow> listsum xs \<le> listsum ys"
apply (induct ys rule:rev_induct)
apply auto
apply (metis bot_unique eq_iff listsum_simps(1) prefixSubset2 set_empty2)
apply (case_tac "isPrefix xs xsa")
apply auto
apply (metis add_increasing2)
apply (frule(1) becomesPrefix_Equal)
apply auto
done

lemma isPrefixMap[intro]: "\<lbrakk>
isPrefix xs ys
\<rbrakk> \<Longrightarrow> isPrefix (map f xs) (map f ys)"
by (metis (full_types) isPrefixTake length_map take_map)


lemma listsumSplit: "listsum (map f xs) = listsum (map f [x\<leftarrow>xs . 0 \<le> (f x::int)]) - listsum (map (\<lambda>x. -f x) [x\<leftarrow>xs . 0 > f x])"
apply (induct xs)
apply auto
done

lemma counterSpecValid: "crdtSpecificationValid pnCounter pnCounterSpec"
apply (rule_tac Inv="pnCounterInvariant" in showCrdtSpecificationValid)

(* invariant implies spec *)
apply (simp add: pnCounterInvariant_def pnCounterSpec_def pnCounter_def invariantImpliesSpec_def)
apply auto
apply (rename_tac P N)
apply (subst setsumToListsumPerReplica)
apply assumption
apply (subst Big_Operators.setsum_subtractf[symmetric])

apply (rule_tac f="setsum" in equalArgs2)
apply (rule ext)
apply auto
apply (rule sym)
apply (subst listsumSplit)
apply auto


apply (auto simp add:  updateHistoryInvariant_all_def)
                                                              
(* initial *)
apply (auto simp add: updateHistoryInvariant_initial_def pnCounterInvariant_def)
apply (simp add: pnCounter_def)
apply (simp add: pnCounter_def)

(* merge *) 
apply (auto simp add: updateHistoryInvariant_merge_def pnCounterInvariant_def pnCounter_def)

  (* merge positive component *)
  apply (erule_tac r="r" in consistentHistoriesCases3)
  apply (rule min_max.sup_absorb2)
  apply (rule prefixListsum)
  apply auto
  
  (* negative component *)
  apply (erule_tac r="r" in consistentHistoriesCases3)
  apply (rule min_max.sup_absorb2)
  apply (rule prefixListsum)
  apply auto

(* update *)
apply (simp add: updateHistoryInvariant_update_def pnCounterInvariant_def pnCounter_def)
done


end

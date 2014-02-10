theory helper
imports induction
begin
(*
Helper lemmas for making the inductions easier
*)

lemma equalArgs2: "xa = xb \<Longrightarrow> ya = yb \<Longrightarrow> f xa ya = f xb yb"
by auto

lemma cardinalitySplit1: "\<lbrakk>
finite C;
A \<union> B = C;
A \<inter> B = {}
\<rbrakk> \<Longrightarrow> card A + card B = card C"
by (metis card_Un_disjoint finite_Un)


lemma showDistinct[intro]: "\<lbrakk>
\<And>i j. i<length xs \<Longrightarrow> j<i \<Longrightarrow> xs!i\<noteq>xs!j 
\<rbrakk> \<Longrightarrow> distinct xs"
by (metis distinct_conv_nth nat_neq_iff)

lemma updateHistoryDistinct: "validUpdateHistory H \<Longrightarrow> distinct (H r)"
apply (rule showDistinct)
apply (case_tac "H r ! i")
apply (case_tac "H r ! j")
apply (subgoal_tac "aa\<guillemotright>r < a\<guillemotright>r")
apply clarsimp
by (metis Suc_less_eq less_trans validUpdateHistory_versionVectorR)

lemma updateHistoryCard[simp]: "validUpdateHistory H \<Longrightarrow> card (set (H r)) = length (H r)"
by (metis distinct_card updateHistoryDistinct)


lemma cardinalitySplit3: "\<lbrakk>
finite T;
\<And>rx ry. rx \<noteq> ry \<Longrightarrow> S rx \<inter> S ry = {};
\<And>r. finite (S r)
\<rbrakk> \<Longrightarrow> card (\<Union>r\<in>T. (S r)) = (\<Sum>r\<in>T. card (S r))"
apply (induct rule: finite_induct)
apply simp
apply auto
apply (drule meta_mp)
apply clarsimp
apply (rule_tac t="(\<Sum>r\<in>F. card (S r))" and s=" card (\<Union>x\<in>F. S x)" in ssubst)
apply simp
apply (rule cardinalitySplit1[symmetric])
apply auto
by (metis (full_types) Int_iff equals0D)


lemma validUpdateHistory_distinct: "validUpdateHistory H \<Longrightarrow> rx \<noteq> ry \<Longrightarrow> (vx, x) \<in> set (H rx) \<Longrightarrow> (vy, y) \<in> set (H ry) \<Longrightarrow> vx\<noteq>vy"
by (metis le_less less_versionVector_def validUpdateHistory_monotonicOther)

lemma cardToLength: "validUpdateHistory H \<Longrightarrow> (\<Sum>r\<in>UNIV. length (H r)) = card (\<Union>r. set (H r))"
apply (subst cardinalitySplit3)
apply (metis finite_UNIV)
apply auto
by (metis validUpdateHistory_distinct)

lemma isPrefixHistoryUnion[simp]: "isPrefix (Ha r) (Hb r) \<Longrightarrow> historyUnion Ha Hb r = Hb r"
by (metis historyUnion_def isPrefixLen)

lemma isPrefixHistoryUnion2[simp]: "isPrefix (Hb r) (Ha r) \<Longrightarrow> historyUnion Ha Hb r = Ha r"
by (metis append_Nil2 append_take_drop_id drop_eq_Nil historyUnion_def isPrefixTake)

lemma isPrefixFilter2[intro]: "isPrefix xs ys \<Longrightarrow> isPrefix (filter P xs) (filter P ys)"
apply (auto simp add: isPrefixTake)
by (metis append_take_drop_id filter_append isPrefixAppend isPrefixTake)

lemma consistentHistoriesCases2: "\<lbrakk>
consistentHistories H1 H2;
consistentHistories H1 H2 \<Longrightarrow> isPrefix (H1 r) (H2 r) \<Longrightarrow> P (H1 r) (H2 r) (H2 r);
consistentHistories H1 H2 \<Longrightarrow> isPrefix (H2 r) (H1 r) \<Longrightarrow> P (H1 r) (H2 r) (H1 r)
\<rbrakk> \<Longrightarrow> P (H1 r) (H2 r) (historyUnion H1 H2 r)"
apply (auto simp add: consistentHistories_def)
by (metis (full_types) isPrefixHistoryUnion isPrefixHistoryUnion2)

lemma consistentHistoriesCases3: "\<lbrakk>
consistentHistories H1 H2;
\<And>H1 H2. consistentHistories H1 H2 \<Longrightarrow> isPrefix (H1 r) (H2 r) \<Longrightarrow> P (H1 r) (H2 r) (H2 r);
\<And>H1 H2. consistentHistories H1 H2 \<Longrightarrow> P (H1 r) (H2 r) (historyUnion H1 H2 r) \<Longrightarrow> P (H2 r) (H1 r) (historyUnion H1 H2 r)
\<rbrakk> \<Longrightarrow> P (H1 r) (H2 r) (historyUnion H1 H2 r)"
apply (rule consistentHistoriesCases2)
apply assumption+
by (metis consistentHistories_commute isPrefixHistoryUnion)

lemma allUpdatesInitial[simp]: "allUpdates (\<lambda>r. []) = {}"
by (metis all_not_in_conv empty_set notinAllUpdatesI)

definition updateHistoryVersion where
"updateHistoryVersion H = VersionVector (\<lambda>r. length (H r))"


lemma updateHistoryVersionInitial[simp]: "updateHistoryVersion (\<lambda>r. []) = vvZero"
apply (auto simp add: updateHistoryVersion_def vvZero_def)
done

lemma prefixSubset1: "x \<in> set xs \<Longrightarrow> isPrefix xs ys \<Longrightarrow> x \<in> set ys"
apply (auto simp add: isPrefixTake)
by (metis in_set_takeD)

lemma prefixSubset2: "isPrefix xs ys \<Longrightarrow> set xs \<subseteq> set ys"
apply auto
by (metis prefixSubset1)

lemma isPrefixSmaller: "length xs \<le> length ys \<Longrightarrow> isPrefix ys xs \<Longrightarrow> xs=ys"
apply (auto simp add: isPrefixTake)
done


lemma allUpdatesUnion[simp]: "consistentHistories H1 H2 \<Longrightarrow> allUpdates (historyUnion H1 H2) = allUpdates H1 \<union> allUpdates H2"
apply (auto simp add: historyUnion_def allUpdates_def)
apply (metis (full_types))
apply (rule_tac x="r" in exI)
apply (metis consistentHistories_def isPrefixSmaller prefixSubset1)
apply (metis consistentHistories_def isPrefixLen prefixSubset1)
done


lemma consistentHistoriesContentSame: "consistentHistories H1 H2 \<Longrightarrow>
       i < length (H1 r) \<Longrightarrow>  i < length (H2 r) \<Longrightarrow> (H1 r)!i = (H2 r)!i"
apply (erule consistentHistoriesCases2)
apply (metis isPrefixNth)+
done

lemma consistentHistoriesHappensBefore: "\<lbrakk>
consistentHistories H1 H2;
validUpdateHistory H1;
validUpdateHistory H2;
va < vb;  
(va, ya) \<in> allUpdates H1;
(vb, yb) \<in> allUpdates H2
\<rbrakk> \<Longrightarrow> (va, ya) \<in> allUpdates H2"
apply (auto simp add: allUpdates_def)
apply (rule_tac x="r" in exI)
apply (frule_tac v="vb" and H="H2" and r="r" in validUpdateHistory_localMax)
apply (metis inAllVersionsI)
apply (unfold in_set_conv_nth)
apply clarsimp
apply (subgoal_tac "i < length (H2 r)")
apply (rule_tac x="i" in exI)
apply auto
apply (metis consistentHistoriesContentSame)
apply (subgoal_tac "vb\<guillemotright>r\<ge>va\<guillemotright>r")
apply (metis le_neq_trans lessI less_asym not_leE order_trans validUpdateHistory_versionVectorR)
apply (metis less_versionVector_def)
done

lemma consistentHistoriesHappensBefore2: "
consistentHistories H2 H1
\<Longrightarrow> validUpdateHistory H1
\<Longrightarrow> validUpdateHistory H2
\<Longrightarrow> va < vb  
\<Longrightarrow> (va, ya) \<in> allUpdates H1 
\<Longrightarrow> (vb, yb) \<in> allUpdates H2
\<Longrightarrow> (va, ya) \<in> allUpdates H2"
by (metis consistentHistoriesHappensBefore consistentHistories_commute)


lemma allUpdatesAdd[simp]: "allUpdates (H(r := H r @ [y])) = allUpdates H \<union> {y}"
apply (auto simp add: allUpdates_def)
apply (case_tac "ra=r")
apply auto
done

lemma versionIsTopToUpdateHistoryVersion: "validUpdateHistory H \<Longrightarrow> versionIsTop v H \<Longrightarrow> v=updateHistoryVersion H"
apply (auto simp add: versionIsTop_def updateHistoryVersion_def)
apply (subst versionVectorEq)
apply auto
apply (subst supSet_versionVectorComponent)
apply (metis allVersionsFinite)
apply auto
apply (rule antisym)
apply (rule supSetBigger)
apply (metis allVersionsFinite finite_imageI)
apply auto
apply (metis validUpdateHistory_localMax)
apply (case_tac "length (H r)")
apply clarsimp
apply (rule supSetSmaller)
apply (metis allVersionsFinite finite_imageI)
apply (auto simp add: allVersions_def allUpdates_def)
apply (case_tac "H r!nat")
apply (subgoal_tac "a\<guillemotright>r = Suc nat")
apply (metis (full_types) allUpdates_def allVersions_def image_iff inAllVersionsI lessI nth_mem vvComponentToGet)
apply (metis lessI validUpdateHistory_versionVectorR)
done

lemma versionIsTopComponent: "validUpdateHistory H \<Longrightarrow> versionIsTop v H \<Longrightarrow> v\<guillemotright>r = length (H r)"
apply (frule(1) versionIsTopToUpdateHistoryVersion)
apply (auto simp add: updateHistoryVersion_def)
done

lemma versionIsTopGreaterHistory: "validUpdateHistory H \<Longrightarrow> versionIsTop v H \<Longrightarrow> (vv, y) \<in> set (H ra) \<Longrightarrow> vv\<le>v"
by (metis inAllVersionsI versionIsTopComponent validUpdateHistory_localMax versionVectorLessEqI)

lemma updateHistoryVersionUpdate: "updateHistoryVersion (H(r := H r @ [y])) = incVV r (updateHistoryVersion H)"
apply (auto simp add: updateHistoryVersion_def versionVectorEq)
done



lemma allUpdatesToReplica: "e \<in> allUpdates H \<Longrightarrow> \<exists>r. e\<in>set (H r)"
by (metis notinAllUpdatesI)

lemma allUpdatesToReplicaE: "e \<in> allUpdates H \<Longrightarrow> (\<And>r. e\<in>set (H r) \<Longrightarrow> Q) \<Longrightarrow> Q"
by (metis allUpdatesToReplica)

lemma lessMinusOne: "x\<le>y \<Longrightarrow> 0<y \<Longrightarrow> (x::nat) - (Suc 0) < y"
by (metis Suc_pred diff_le_self le_neq_implies_less less_imp_diff_less n_not_Suc_n)


lemma isPrefix_inFirstPart: "\<lbrakk>
x \<in> set ys;
isPrefix xs ys;
\<And>i. i\<ge> length xs \<Longrightarrow> i < length ys \<Longrightarrow> ys!i \<noteq> x
\<rbrakk> \<Longrightarrow> x \<in> set xs"
by (metis in_set_conv_nth isPrefixNth not_leE)


lemma listNth_inSet: "xs!i = x \<Longrightarrow> i < length xs \<Longrightarrow> x \<in> set xs"
by fastforce

lemma filterNth: "filter P xs ! i = x \<Longrightarrow> i < length (filter P xs) \<Longrightarrow> \<exists>j<length xs. xs!j = x"
apply auto
apply (induct xs rule: rev_induct)
apply auto
apply (case_tac "i < length (filter P xs)")
apply auto
apply (rule_tac x=j in exI)
apply (simp add: nth_append)
apply (rule_tac x="length xs" in exI)
apply clarsimp
apply (metis linorder_neqE_nat not_less_eq nth_append_length)
apply (rule_tac x=j in exI)
apply (simp add: nth_append)
done

lemma filterNth2: "\<exists>f. (\<forall>i<length(filter P xs). f i < length xs \<and> xs!(f i) = filter P xs!i) \<and> (\<forall>i j. i < j \<and> j < length(filter P xs) \<longrightarrow> f i < f j)"
apply (induct xs rule: rev_induct)
apply clarsimp
apply auto
apply (rule_tac x="f(length(filter P xs) := length xs)" in exI)
apply auto
apply (metis less_SucE less_SucI)
apply (metis less_antisym nth_append)
apply (rule_tac x=f in exI)
apply auto
apply (metis nth_append)
done


lemma versionIsTopGreaterHistory2: "
validUpdateHistory H \<Longrightarrow>       
versionIsTop v H \<Longrightarrow>
(vv, y) \<in> allUpdates H \<Longrightarrow>
vv \<le> v"
apply (metis allUpdatesToReplicaE versionIsTopGreaterHistory)
done

lemma versionIsTopGreaterHistory2_incVV: "
validUpdateHistory H \<Longrightarrow>       
versionIsTop v H \<Longrightarrow>
(vv, y) \<in> allUpdates H \<Longrightarrow>
vv < incVV r v"
apply (metis incVVGreater le_less_trans versionIsTopGreaterHistory2)
done

lemma laterVersionNotInAllUpdates: "
validUpdateHistory H \<Longrightarrow>       
versionIsTop v H \<Longrightarrow>
(vv, y) \<in> allUpdates H \<Longrightarrow>
v < vv \<Longrightarrow> 
P"
apply (metis less_le_not_le versionIsTopGreaterHistory2)
done

lemma laterVersionNotInAllUpdates_incVV: "
validUpdateHistory H \<Longrightarrow>       
versionIsTop v H \<Longrightarrow>
(vv, y) \<in> allUpdates H \<Longrightarrow>
incVV r v < vv \<Longrightarrow> 
P"
apply (metis incVVGreaterEq laterVersionNotInAllUpdates le_less_trans)
done

lemma updateHistoryVersion_historyUnion: "
V1 = updateHistoryVersion H1 \<Longrightarrow>
V2 = updateHistoryVersion H2 \<Longrightarrow>
sup V1 V2 = updateHistoryVersion (historyUnion H1 H2)"
apply (auto simp add: updateHistoryVersion_def historyUnion_def sup_versionVector_def)
apply force
done


end


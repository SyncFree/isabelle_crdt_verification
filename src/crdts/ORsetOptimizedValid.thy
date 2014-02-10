theory ORsetOptimizedValid
imports ORsetOptimized 
"../framework/helper"
begin

(*sledgehammer_params [fact_filter=mash, provers = e spass remote_vampire z3 remote_e_sine]*)


abbreviation "addOperations xs \<equiv> [e\<leftarrow>xs. \<exists>x. updArgs(e) = Add x]"

definition "existsAddOperationWithoutRemove x r H = (\<exists>e.
  e\<in>set (H r) 
  \<and> updArgs(e) = Add x 
  \<and> \<not>(\<exists>f\<in>allUpdates H. updArgs(f) = Remove x \<and> e \<prec> f))"

(* versionVec = number of add operations on replica*)
definition 
"invA H pl = (\<forall>r. versionVec pl\<guillemotright>r = length (addOperations (H r)))"

definition 
"invB H pl = (\<forall>x r. (if existsAddOperationWithoutRemove x r H
  then (\<exists>c. (x,c,r) \<in> elements pl)
  else (\<forall>c. (x,c,r) \<notin> elements pl)))"

definition 
"invC H pl = (\<forall>x c r. (x,c,r)\<in>elements pl \<longrightarrow> 
          0<c 
        \<and> c\<le>length(addOperations (H r)) 
        \<and> updArgs(addOperations (H r) ! (c - 1)) = Add x
        \<and> (\<forall>i<length(addOperations(H r)). i \<ge> c \<longrightarrow> updArgs(addOperations(H r)!i) \<noteq> Add x))"




definition Inv :: "('a updateArgs) updateHistory \<Rightarrow> 'a payload \<Rightarrow> bool" where
"Inv H pl = (invA H pl \<and> invB H pl \<and> invC H pl)"

lemma invA: "Inv H (V,E) \<Longrightarrow> V\<guillemotright>r = length (addOperations (H r))"
apply (auto simp add: Inv_def invA_def)
done

lemma invC_min: "Inv H (V,E) \<Longrightarrow> (x,c,r)\<in>E \<Longrightarrow> 0<c"
apply (auto simp add: Inv_def invC_def)
done


lemma invC_max: "Inv H (V,E) \<Longrightarrow> (x,c,r)\<in>E \<Longrightarrow> c\<le>length(addOperations(H r))"
apply (auto simp add: Inv_def invC_def)
done

lemma invC_updArgs: "Inv H (V,E) \<Longrightarrow> (x,c,r)\<in>E \<Longrightarrow> updArgs(addOperations (H r) ! (c - 1)) = Add x"
apply (auto simp add: Inv_def invC_def)
done

lemma invC_updArgs2: "Inv H (V,E) \<Longrightarrow> (x,c,r)\<in>E \<Longrightarrow> updArgs(addOperations (H r) ! (c - Suc 0)) = Add x"
apply (auto simp add: Inv_def invC_def)
done


lemma invC_updArgsMax: "Inv H (V,E) \<Longrightarrow> 
(x,c,r)\<in>E \<Longrightarrow> 
i\<ge>c \<Longrightarrow>
i<length(addOperations(H r)) \<Longrightarrow>
updArgs(addOperations(H r)!i) \<noteq> Add x"
apply (auto simp add: Inv_def invC_def)
done


lemma invC2: "Inv H (V,E) \<Longrightarrow> (x,c,r)\<in>E \<Longrightarrow> c \<le> V\<guillemotright>r"
apply (auto simp add: Inv_def invC_def invA_def)
done



lemma invB_H: "Inv H (V,E) \<Longrightarrow> (if existsAddOperationWithoutRemove x r H
  then (\<exists>c. (x,c,r) \<in> E)
  else (\<forall>c. (x,c,r) \<notin> E))"
apply (unfold Inv_def invB_def)
apply clarsimp
apply (drule_tac x=x in spec)
apply (drule_tac x=r in spec)
apply auto
done


lemma invB: "Inv H (V,E) \<Longrightarrow>
    ((existsAddOperationWithoutRemove x r H) \<longrightarrow>
     (\<exists>c. 0<c \<and> c\<le>length(addOperations (H r)) \<and> (x,c,r) \<in> E \<and> updArgs(addOperations (H r) ! (c - 1)) = Add x
        \<and> (\<forall>i<length(addOperations(H r)). i \<ge> c \<longrightarrow> updArgs(addOperations(H r)!i) \<noteq> Add x))) \<and>
    (\<not> (existsAddOperationWithoutRemove x r H) \<longrightarrow> (\<forall>c. (x,c,r)\<notin>E))"
apply (frule_tac x=x and r=r in invB_H)
apply auto
apply (rule_tac x=c in exI)
apply auto
apply (metis invC_min)
apply (metis invA invC2)
apply (erule(1) invC_updArgs2)
apply (metis (lifting, mono_tags) invC_updArgsMax)
done

lemma invB_notZero1a: "(x,c,r)\<in>E \<Longrightarrow> Inv H (V,E) \<Longrightarrow> i<length(addOperations(H r)) \<Longrightarrow> i \<ge> c \<Longrightarrow> updArgs(addOperations(H r)!i) = Add x \<Longrightarrow> P"
apply (metis (lifting, mono_tags) invC_updArgsMax)
done

lemma invB_notZero1: "(x,c,r)\<in>E \<Longrightarrow> Inv H (V,E) \<Longrightarrow> (c > 0 \<and> updArgs(addOperations (H r) ! (c - 1)) = Add x
        \<and> (\<forall>i<length(addOperations(H r)). i \<ge> c \<longrightarrow> updArgs(addOperations(H r)!i) \<noteq> Add x))"
apply auto
apply (metis invC_min)
apply (erule(1) invC_updArgs2)
apply (erule(4) invB_notZero1a)
done

lemma invB_zero: "\<forall>c. (x,c,r)\<notin>E \<Longrightarrow> Inv H (V,E) \<Longrightarrow> \<not>existsAddOperationWithoutRemove x r H"
apply (frule invB)
apply auto
done


lemma invB_notExists: "\<forall>c. (x,c,r) \<notin>E \<Longrightarrow> Inv H (V,E) \<Longrightarrow>  \<not> existsAddOperationWithoutRemove x r H"
apply (auto simp add: Inv_def invB_def)
by (metis snd_conv)

lemma invB_exists: "(x,c,r)\<in>E \<Longrightarrow> Inv H (V,E) \<Longrightarrow> existsAddOperationWithoutRemove x r H"
apply (auto simp add: Inv_def invB_def)
by (metis snd_conv)


lemma cUnique1: "\<lbrakk>
(x,ca,r)\<in>E;
(x,cb,r)\<in>E;
Inv H (V,E);
ca < cb
\<rbrakk> \<Longrightarrow> P"
apply (frule(1) invC_updArgs[where c=cb])
apply (frule(1) invC_updArgsMax[where c=ca and i="cb - 1"])
apply auto
apply (frule(1) invC_max[where c=cb])
apply auto
done

lemma cUnique: "\<lbrakk>
(x,ca,r)\<in>E;
(x,cb,r)\<in>E;
Inv H (V,E)
\<rbrakk> \<Longrightarrow> ca = cb"
by (metis (full_types) cUnique1 linorder_neqE_nat)

lemma notExistsAddOperationWithoutRemove: "(v, Add x) \<in> set (H r) \<Longrightarrow> \<not> existsAddOperationWithoutRemove x r H \<Longrightarrow> \<exists>vv>v. (vv, Remove x) \<in> allUpdates H"
apply (auto simp add: existsAddOperationWithoutRemove_def)
apply (drule_tac x="v" in spec)
apply auto
done

lemma inAddOperations: "(v, Add x) \<in> set (H r) \<Longrightarrow> (v, Add x) \<in> set (addOperations(H r))"
apply auto
done


lemma existsAddOperationWithoutRemove_AddOther:" 
existsAddOperationWithoutRemove xa ra (H(r := H r @ [(incVV r v, Add x)])) \<Longrightarrow>  
xa\<noteq> x \<Longrightarrow>
existsAddOperationWithoutRemove xa ra H"
apply (case_tac "r=ra")
apply (auto simp add: existsAddOperationWithoutRemove_def)
done

lemma notExistsAddOperationWithoutRemove_AddOther:" 
\<not> existsAddOperationWithoutRemove xa ra (H(r := H r @ [(incVV r v, Add x)])) \<Longrightarrow>  
xa\<noteq> x \<Longrightarrow>
\<not> existsAddOperationWithoutRemove xa ra H"
apply (case_tac "r=ra")
apply (auto simp add: existsAddOperationWithoutRemove_def)
done


lemma existsAddOperationWithoutRemove_AddOtherReplica: "
existsAddOperationWithoutRemove xa ra (H(r := H r @ [(incVV r v, Add x)])) \<Longrightarrow> 
ra \<noteq> r \<Longrightarrow> 
existsAddOperationWithoutRemove xa ra H"
apply (auto simp add: existsAddOperationWithoutRemove_def)
done

lemma notExistsAddOperationWithoutRemove_AddOtherReplica: "
\<not>existsAddOperationWithoutRemove xa ra (H(r := H r @ [(incVV r v, Add x)])) \<Longrightarrow> 
ra \<noteq> r \<Longrightarrow> 
\<not>existsAddOperationWithoutRemove xa ra H"
apply (auto simp add: existsAddOperationWithoutRemove_def)
done


(* if both E are 0, then there is no add operation without remove *)
lemma bothZero_notExistsAddOperationWithoutRemove: "
       Inv H1 (V1,E1) \<Longrightarrow>
       Inv H2 (V2,E2) \<Longrightarrow>
       consistentHistories H1 H2 \<Longrightarrow>
       \<forall>c. (x, c, r) \<notin> E1 \<Longrightarrow> 
       \<forall>c. (x, c, r) \<notin> E2 \<Longrightarrow> 
       \<not>existsAddOperationWithoutRemove x r (historyUnion H1 H2)"
apply (frule(1) invB_notExists)
apply (frule(1) invB_notExists[where H=H2])
apply auto
apply (erule_tac r=r in consistentHistoriesCases2)
apply (auto simp add: existsAddOperationWithoutRemove_def )
done


lemma inAddOperations1: "
        c \<le> length (addOperations (H1 r)) \<Longrightarrow>
        \<forall>i<length (addOperations (H2 r)). c \<le> i \<longrightarrow> updArgs (addOperations (H2 r) ! i) \<noteq> Add x \<Longrightarrow>
        isPrefix (H1 r) (H2 r) \<Longrightarrow>
        (a, Add x) \<in> set (addOperations(H2 r)) \<Longrightarrow> 
        (a, Add x) \<in> set (addOperations(H1 r))"
apply (rule isPrefix_inFirstPart)
apply assumption
apply (erule isPrefixFilter2)
apply auto
done

lemma inAddOperations2: "
        c \<le> length (addOperations (Ha r)) \<Longrightarrow>
        isPrefix (Ha r) (Hb r) \<Longrightarrow>
        \<forall>i<length (addOperations (Hb r)). c \<le> i \<longrightarrow> updArgs (addOperations (Hb r) ! i) \<noteq> Add x \<Longrightarrow>
        (a, Add x) \<in> set (Hb r) \<Longrightarrow> 
        (a, Add x) \<in> set (Ha r)"
apply (drule inAddOperations)
apply (frule(3) inAddOperations1)
apply auto
done

(* Case: one E is 0, other is outdated (smaller than the number of add operations in the first history) *)
lemma setSpecValid_H1: "
       \<forall> c. (x,c,r) \<notin> E1 \<Longrightarrow> 
       (x,c,r) \<in> E2 \<Longrightarrow>
       c \<le> length (addOperations (H1 r)) \<Longrightarrow>
       Inv H1 (V1, E1) \<Longrightarrow>
       Inv H2 (V2, E2) \<Longrightarrow>
       consistentHistories H1 H2 \<Longrightarrow>       
       \<not>existsAddOperationWithoutRemove x r (historyUnion H1 H2)"
apply (drule(1) invB_notZero1)
apply auto
apply (frule(1) invB_zero)
apply (erule_tac r=r in consistentHistoriesCases2)
apply (auto simp add: existsAddOperationWithoutRemove_def)
apply (drule_tac x="a" in spec)
apply (drule mp)
apply (erule(3) inAddOperations2)
apply (metis UnI1)
done



lemma lengthAddOperationsGreaterZero: "\<lbrakk>
Inv H (V, E);
(x,c,r) \<in> E
\<rbrakk> \<Longrightarrow> 0 < length (addOperations (H r))"
apply (metis (lifting, mono_tags) invA invC2 invC_min neq0_conv not_less)
done

lemma invImpliesSpec: "invariantImpliesSpec ORsetOpt Inv setSpec" 
apply (auto simp add: invariantImpliesSpec_def)
apply (rename_tac v E qa)
apply (simp add: ORsetOpt_def)
apply (subgoal_tac "\<forall>x. setSpecContains H x \<longleftrightarrow> (\<exists>c r. (x,c,r) \<in> E)")
apply (case_tac qa)
apply (auto simp add: getElements_def)

apply (auto simp add: setSpecContains_def)
apply (metis fst_eqD invB_H notExistsAddOperationWithoutRemove notinAllUpdatesI snd_conv)
apply (metis existsAddOperationWithoutRemove_def inAllUpdatesI invB_exists)
done


lemma setSpecValid_H_add1: "
validUpdateHistory H \<Longrightarrow>
       Inv H (V, E) \<Longrightarrow>
       (xa, c, r) \<in> E \<Longrightarrow> 
 i < Suc (length (addOperations (H r))) \<Longrightarrow> 
c \<le> i \<Longrightarrow> 
x \<noteq> xa \<Longrightarrow> 
updArgs ((addOperations (H r) @ [(incVV r v, Add x)]) ! i) \<noteq> Add xa
"
apply (case_tac "i < length (addOperations (H r))")
apply (subgoal_tac "updArgs ((addOperations (H r)) ! i) \<noteq> Add xa")
apply (metis nth_append)
apply (erule(3) invC_updArgsMax)
apply (subgoal_tac "i = length (addOperations (H r))")
apply clarsimp
apply auto
done


lemma listNthFirst: "0<c \<Longrightarrow> c \<le> length xs \<Longrightarrow> (xs@[x])!(c - Suc 0) = xs ! (c-Suc 0)"
apply (metis Suc_le_lessD Suc_pred nth_append)
done

lemma setSpecValid_H_add2: "
validUpdateHistory H \<Longrightarrow>
Inv H (V, E) \<Longrightarrow> 
(xa, c, r) \<in> E \<Longrightarrow>  
updArgs ((addOperations (H r) @ [(incVV r v, Add x)]) ! (c - Suc 0)) = Add xa
"
apply (frule(1) lengthAddOperationsGreaterZero)
apply (frule(1) invC_max)
apply auto
apply (subst listNthFirst)
apply (metis invB_notZero1)
apply simp
apply (erule(1) invC_updArgs2)
done


lemma listFilterNth: "xs ! i = x \<Longrightarrow>
i < length xs \<Longrightarrow>
P x \<Longrightarrow>
\<exists>j<length(filter P xs). (filter P xs)!j=x"
apply (induct xs arbitrary:i)
apply auto
apply (case_tac i)
apply auto
apply (metis Suc_less_eq nth_Cons_Suc)
apply (case_tac i)
apply auto
done


lemma setSpecValid_H_remove1a: "
validUpdateHistory H \<Longrightarrow>
Inv H (V, E) \<Longrightarrow>
(x, c, r) \<in> E \<Longrightarrow>
addOperations (H r) ! (c - Suc 0) = (v, Add x) \<Longrightarrow>            
\<not> a \<le> v \<Longrightarrow> 
i < length (H r) \<Longrightarrow> 
H r ! i = (a, Add x) \<Longrightarrow>  
addOperations (H r) ! j = (a, Add x) \<Longrightarrow>
c - Suc 0 < j
"
apply (rule ccontr)
apply (subgoal_tac "c - Suc 0 < length(addOperations(H r))")
defer
apply (metis (lifting, mono_tags) invC_max lengthAddOperationsGreaterZero lessMinusOne)
apply (subgoal_tac "j < length(addOperations(H r))")
defer
apply (metis (lifting, no_types) Suc_lessD less_trans_Suc linorder_neqE_nat)

apply (cut_tac P="\<lambda>e. \<exists>x. updArgs(e) = Add x" and xs="H r" in filterNth2)
apply clarsimp
apply (frule_tac j="f j" and r=r and a=a and b="Add x" and i="f (c - Suc 0)" and x=v and y="Add x" in validUpdateHistory_mono)
apply auto
apply (metis (lifting) less_or_eq_imp_le linorder_neqE_nat)
done

lemma setSpecValid_H_remove1: "
validUpdateHistory H \<Longrightarrow>
Inv H (V, E) \<Longrightarrow>
(x, c, r) \<in> E \<Longrightarrow> 
addOperations (H r) ! (c - Suc 0) = (v, Add x)  \<Longrightarrow>       
(vv, Remove x) \<in> allUpdates H \<Longrightarrow> 
v < vv \<Longrightarrow> 
False"
apply (frule(1) invB_exists)
apply (auto simp add: existsAddOperationWithoutRemove_def)
apply (case_tac "a\<le>v")
apply (metis fst_conv le_less_trans snd_conv)
apply (unfold in_set_conv_nth)
apply clarsimp
apply (subgoal_tac "\<exists>j. j < length (addOperations(H r)) \<and> (addOperations(H r)) ! j = (a, Add x)")
defer
apply (erule(1) listFilterNth)
apply simp
apply clarsimp
apply (subgoal_tac "c - Suc 0 < j")
apply (metis (mono_tags) One_nat_def Suc_le_eq Suc_pred' invB_notZero1 snd_def split_conv)
apply (erule(7) setSpecValid_H_remove1a)
done



lemma isPrefixNth2: "
isPrefix xs ys \<Longrightarrow>
i < length (filter P xs) \<Longrightarrow>
filter P xs ! i = filter P ys ! i"
by (metis isPrefixFilter2 isPrefixNth)


lemma isPrefix_C_lengthAddOperations:"
Inv H2 (V2, E2) \<Longrightarrow>
(x, c2, r) \<in> E2 \<Longrightarrow> 
isPrefix (H2 r) (H1 r) \<Longrightarrow> 
c2 \<le> length (addOperations (H1 r))
"
apply (rule_tac y= "length (addOperations (H2 r))" in order_trans)
apply (metis (lifting, mono_tags) invC_max)
apply (rule isPrefixLen)
apply (erule isPrefixFilter2)
done

lemma smallerC_notIsPrefix: "
    Inv H1 (V1, E1) \<Longrightarrow>
    Inv H2 (V2, E2) \<Longrightarrow>
    (x, c1, r) \<in> E1 \<Longrightarrow>
    (x, c2, r) \<in> E2 \<Longrightarrow> 
    c1 < c2 \<Longrightarrow> 
    \<not> isPrefix (H2 r) (H1 r)
"
apply auto
apply (frule(2) isPrefix_C_lengthAddOperations)
apply (frule(1) invC_updArgsMax[where i="c2 - 1" and c=c1])
apply auto
apply (subgoal_tac "updArgs (addOperations (H2 r) ! (c2 - Suc 0)) = Add x")
apply (subgoal_tac "(addOperations (H1 r) ! (c2 - Suc 0)) = (addOperations (H2 r) ! (c2 - Suc 0))")
apply clarsimp
apply (rule isPrefixNth2[symmetric])
apply simp
apply (rule lessMinusOne)
apply (erule(1) invC_max)
apply (erule(1) lengthAddOperationsGreaterZero)
apply (erule(1) invC_updArgs2)
done

lemma cSmaller_H1: "
Inv H1 (V1, E1) \<Longrightarrow>
Inv H2 (V2, E2) \<Longrightarrow>
consistentHistories H1 H2 \<Longrightarrow>
(x, c1, r) \<in> E1 \<Longrightarrow> 
(x, c2, r) \<in> E2 \<Longrightarrow> 
c1 < c2 \<Longrightarrow>  
length (addOperations (H1 r)) < c2
"
apply (rule ccontr)
apply (erule_tac r=r in consistentHistoriesCases2)
apply (frule(1) invC_updArgsMax[where i="c2 - 1"])
apply simp
apply auto
apply (subgoal_tac "updArgs (addOperations (H2 r) ! (c2 - Suc 0)) = Add x")
apply (subgoal_tac "(addOperations (H1 r) ! (c2 - Suc 0)) = (addOperations (H2 r) ! (c2 - Suc 0))")
apply clarsimp
apply (rule isPrefixNth2)
apply simp
apply simp
apply (erule(1) invC_updArgs2)
apply (metis (hide_lams, no_types) smallerC_notIsPrefix)
done

lemma inHistoryUnionAddOperations2: "consistentHistories H1 H2 \<Longrightarrow> x \<in> set (addOperations(H1 r)) \<Longrightarrow> x \<in> set (historyUnion H1 H2 r)"
apply (erule consistentHistoriesCases2)
apply auto
apply (metis prefixSubset1)
done

lemma invC_max2: "Inv H1 (V1, E1) \<Longrightarrow> (x, c, r) \<in> E1 \<Longrightarrow>  c - Suc 0 < length (addOperations(H1 r))"
apply (frule(1) invC_max)
apply (metis invB_notZero1 le_0_eq lessMinusOne neq0_conv)
done

lemma invC_updArgs_version: "Inv H1 (V1, E1) \<Longrightarrow> (x, c, r) \<in> E1 \<Longrightarrow> \<exists>v. addOperations(H1 r)!(c - 1) = (v, Add x)"
apply (case_tac "addOperations(H1 r)!(c - 1)")
apply (frule(1) invC_updArgs2)
apply auto
done

lemma consistentHistories_same: "
consistentHistories H1 H2 \<Longrightarrow>
Inv H1 (V1, E1) \<Longrightarrow>
(x, c, r) \<in> E1 \<Longrightarrow>
Inv H2 (V2, E2) \<Longrightarrow> 
(x, c, r) \<in> E2 \<Longrightarrow> 
addOperations (H1 r) ! (c - 1) = addOperations (H2 r) ! (c - 1)
"
apply (erule consistentHistoriesCases2)
apply (erule isPrefixNth2)
apply (simp add: invC_max2)
apply (erule isPrefixNth2[symmetric])
apply (simp add: invC_max2)
done

lemma invC_updArgs_version_Two: "
consistentHistories H1 H2 \<Longrightarrow>
Inv H1 (V1, E1) \<Longrightarrow> (x, c, r) \<in> E1 \<Longrightarrow>
Inv H2 (V2, E2) \<Longrightarrow> (x, c, r) \<in> E2 \<Longrightarrow>
\<exists>v. addOperations(H1 r)!(c - 1) = (v, Add x) \<and> addOperations(H2 r)!(c - 1) = (v, Add x)"
apply (case_tac "addOperations(H1 r)!(c - 1)")
apply (frule(1) invC_updArgs2)
apply auto
apply (frule(4) consistentHistories_same)
apply simp
done


lemma inAllVersions3: "(v, y) \<in> allUpdates H \<Longrightarrow> v \<in> allVersions H"
apply (simp add: allVersions_def)
apply force
done

lemma inFilterConditionHolds: "j < length (filter P ys) \<Longrightarrow> filter P ys ! j = x \<Longrightarrow> P x"
apply (metis Set.filter_def listNth_inSet member_filter set_filter)
done

lemma isPrefixDistinctFilterLength: "
isPrefix xs ys \<Longrightarrow>
filter P ys!j = x \<Longrightarrow>
i < length xs \<Longrightarrow>
xs!i = x \<Longrightarrow>
j < length(filter P ys) \<Longrightarrow>
distinct ys \<Longrightarrow>
length (filter P xs) > j
"
apply (subgoal_tac "P x")
prefer 2
apply (metis inFilterConditionHolds)
apply (subgoal_tac "\<exists>k<length(filter P xs). filter P xs!k = x")
prefer 2
apply (metis listFilterNth)
apply clarsimp
apply (metis (full_types) distinct_filter isPrefixNth2 less_trans linear nat_less_le nth_eq_iff_index_eq)
done


lemma setSpecValid_H3a: "
validUpdateHistory H1 \<Longrightarrow>
Inv H1 (V1, E1) \<Longrightarrow>
(x, c, r) \<in> E1 \<Longrightarrow>
length (addOperations (H2 r)) < c \<Longrightarrow>
isPrefix (H2 r) (H1 r) \<Longrightarrow>
addOperations (H1 r) ! (c - Suc 0) = (v, Add x) \<Longrightarrow>
H1 r ! j = (v, Add x) \<Longrightarrow> 
length (H2 r) \<le> j
"
apply (rule ccontr)
apply (unfold not_le)
apply (subgoal_tac "H2 r ! j = (v, Add x)")
prefer 2
apply (metis isPrefixNth)
apply (frule(3) isPrefixDistinctFilterLength)
apply (erule(1) invC_max2)
apply (metis updateHistoryDistinct)
apply simp
done

lemma setSpecValid_H3: "
(x, c, r) \<in> E1 \<Longrightarrow> 
(x, c, r) \<notin> E2 \<Longrightarrow> 
length (addOperations (H2 r)) < c \<Longrightarrow> 
validUpdateHistory H1 \<Longrightarrow>
validUpdateHistory H2 \<Longrightarrow>
Inv H1 (V1, E1) \<Longrightarrow>
Inv H2 (V2, E2) \<Longrightarrow>
consistentHistories H1 H2 \<Longrightarrow>
\<not> existsAddOperationWithoutRemove x r (historyUnion H1 H2) \<Longrightarrow>
\<forall>c'. ((x, c', r) \<in> E1 \<longrightarrow> (x, c', r) \<notin> E2) \<and>
    ((x, c', r) \<in> E1 \<longrightarrow> (x, c', r) \<in> E2 \<or> \<not> length (addOperations (H2 r)) < c') \<and> ((x, c', r) \<in> E2 \<longrightarrow> (x, c', r) \<in> E1 \<or> \<not> length (addOperations (H1 r)) < c') \<or>
    \<not> c < c' \<Longrightarrow>
False
"
apply (drule_tac x=c in spec)
apply auto
apply (erule_tac r=r in consistentHistoriesCases2)
apply (frule(2) isPrefix_C_lengthAddOperations)
apply simp
apply (frule(1) invC_updArgs_version)
apply clarsimp
apply (simp add: existsAddOperationWithoutRemove_def)
apply (drule_tac x=v in spec)
apply (drule mp)
apply (metis (lifting, mono_tags) filter_is_subset invC_max2 listNth_inSet subset_code(1))
apply auto
apply (erule(5) setSpecValid_H_remove1)
apply (frule filterNth)
apply (erule(1) invC_max2)
apply clarsimp
apply (subgoal_tac "v\<guillemotright>r = j+1")
prefer 2
apply (metis Suc_eq_plus1 validUpdateHistory_versionVectorR)
apply (subgoal_tac "a\<guillemotright>r \<ge> j+1")
prefer 2
apply (metis less_versionVector_def)
apply (frule_tac v=a and H=H2 and r=r in validUpdateHistory_localMax)
apply (erule inAllVersions3)
apply (subgoal_tac "length(H2 r) \<le> j")
apply simp
apply (erule(6) setSpecValid_H3a)
done


lemma setSpecValid_H4: "
Inv H (V, E) \<Longrightarrow> 
(x, c, r) \<in> E \<Longrightarrow> 
addOperations (H r) ! (c - Suc 0) = y \<Longrightarrow> 
y \<in> set (H r)
"
apply (frule filterNth)
apply (simp add: invC_max2)
apply clarsimp
apply (metis nth_mem)
done

lemma setSpecValid_H5: "
validUpdateHistory H2 \<Longrightarrow>
Inv H1 (V1, E1) \<Longrightarrow>
(x, c, r) \<in> E1 \<Longrightarrow> 
length (addOperations (H2 r)) < c \<Longrightarrow> 
isPrefix (H1 r) (H2 r) \<Longrightarrow> 
P"

apply (frule(2) isPrefix_C_lengthAddOperations)
apply (metis not_le)
done



lemma setSpecValid: "crdtSpecificationValid ORsetOpt setSpec"
apply (rule_tac Inv="Inv" in showCrdtSpecificationValid)

apply (rule invImpliesSpec)


(**)
apply (auto simp add: updateHistoryInvariant_all_def)

(* initial *)
apply (simp add: updateHistoryInvariant_initial_def ORsetOpt_def Inv_def invA_def invB_def existsAddOperationWithoutRemove_def invC_def)

(* update*)
defer
apply (simp add: updateHistoryInvariant_update_def ORsetOpt_def)
apply auto
apply (subst Inv_def)
apply (case_tac args)
apply (rename_tac H V E r v args x)
defer
apply (rename_tac H V E r v args x)
prefer 3
apply auto

(*update, Add x, invA*)
apply (simp add: invA_def)
apply (simp add: add_def invA)

(*update, Add x, invB*)
apply (simp add: invB_def)
apply auto
apply (simp add: add_def)
apply (case_tac "xa = x")
apply (case_tac "ra = r")
apply clarsimp
apply (metis less_not_refl3)
apply clarsimp
apply (metis existsAddOperationWithoutRemove_AddOtherReplica invB_H)
apply clarsimp
apply (metis existsAddOperationWithoutRemove_AddOther invB_H)

apply (simp add: add_def)
apply (case_tac "x=xa")
apply clarsimp
apply (case_tac "ra = r")
apply clarsimp
apply (simp add: existsAddOperationWithoutRemove_def)
apply (drule_tac x="incVV r v" in spec)
apply auto
apply (metis laterVersionNotInAllUpdates_incVV)
apply (metis laterVersionNotInAllUpdates_incVV)
apply (metis laterVersionNotInAllUpdates_incVV)
apply (metis invB_H notExistsAddOperationWithoutRemove_AddOtherReplica)
apply (metis invB_H notExistsAddOperationWithoutRemove_AddOther)


(* update, Add x, invC *)
apply (simp add: invC_def add_def)
apply auto
apply (metis eq_iff invA)
apply (metis (lifting, mono_tags) invA nth_append_length snd_eqD)
apply (metis invA less_Suc_eq_le not_less_eq_eq)
apply (metis eq_iff invA)
apply (metis (lifting, mono_tags) invA nth_append_length snd_eqD)
apply (metis invA less_Suc_eq_le not_less_eq_eq)
apply (metis invC_min)
apply (metis invA invC2 le_SucI)
apply (metis (lifting, mono_tags) setSpecValid_H_add2)
apply (case_tac "x=xa")
apply clarsimp
apply (simp add: setSpecValid_H_add1)
apply (metis invC_min)
apply (metis invA invC2 le_SucI)
apply (simp add: setSpecValid_H_add2)
apply (simp add: setSpecValid_H_add1)
apply (metis invC2 le_imp_less_Suc)
apply (simp add: setSpecValid_H_add2)
apply (metis invC2 le_imp_less_Suc)
apply (metis invC_min)
apply (metis invA invC2)
apply (erule(1) invC_updArgs2)
apply (erule(4) invB_notZero1a)


(* Remove x, invA*)
apply (simp add: invA_def remove_def invA)


(* Remove x, invB *)
apply (simp add: invB_def remove_def)
apply auto

apply (simp add: existsAddOperationWithoutRemove_def)
apply auto
apply (case_tac "ra = r")
apply auto
apply (metis fst_eqD invB_H notExistsAddOperationWithoutRemove snd_eqD)
apply (metis fst_eqD invB_H notExistsAddOperationWithoutRemove snd_eqD)
apply (case_tac "ra = r")
apply auto
apply (case_tac "xa = x")
apply auto
apply (metis inAllUpdatesI versionIsTopGreaterHistory2_incVV)
apply (metis fst_eqD invB_H notExistsAddOperationWithoutRemove snd_eqD)
apply (case_tac "xa = x")
apply auto
apply (metis inAllUpdatesI versionIsTopGreaterHistory2_incVV)
apply (metis fst_eqD invB_H notExistsAddOperationWithoutRemove snd_eqD)


apply (simp add: existsAddOperationWithoutRemove_def)
apply (case_tac "ra = r")
apply auto
apply (case_tac "xa = x")
apply auto
apply (case_tac "addOperations (H r) ! (c - 1)")
apply (drule_tac x=a in spec)
apply (drule mp)
apply (frule(1) invC_updArgs)
apply clarsimp
apply (erule(2) setSpecValid_H4)
apply clarsimp
apply (frule(1) invC_updArgs)
apply clarsimp
apply (erule(5) setSpecValid_H_remove1)
apply (case_tac "ra = r")
apply auto
apply (case_tac "xa = x")
apply auto
apply (frule(1) invB_exists)
apply (simp add: existsAddOperationWithoutRemove_def)
apply auto


(*Remove x, invC*)
apply (simp add: invC_def remove_def)
apply (auto simp add: invC2 invC_max invC_min invC_updArgs2 invC_updArgsMax)



(* Merge *)
apply (simp add: updateHistoryInvariant_merge_def ORsetOpt_def merge_def)
apply clarsimp
apply (rename_tac H1 V1 E1 H2 V2 E2)

apply (subst Inv_def)
apply auto

(*merge, invA*)
apply (simp add: invA_def)
apply (auto)
apply (subst versionVectorSupComponent)
apply (unfold invA)
apply (erule_tac r=r in consistentHistoriesCases2)
apply (rule max_absorb2)
apply (rule isPrefixLen)
apply (erule isPrefixFilter2)
apply (rule max_absorb1)
apply (rule isPrefixLen)            
apply (erule isPrefixFilter2)

(*merge, invB*)             
apply (simp add: invB_def)
apply auto
                          
apply (case_tac "\<exists>c1. (x, c1, r) \<in> E1")
apply (case_tac "\<exists>c2. (x, c2, r) \<in> E2")
apply clarsimp
apply (case_tac "c1=c2")
apply clarsimp
apply (rule_tac x=c2 in exI)
apply auto
apply (metis cUnique nat_neq_iff)
apply (metis cUnique1)
apply (metis cUnique1)

apply (case_tac "c1<c2")
apply (rule_tac x=c2 in exI)
apply auto
apply (erule(5) cSmaller_H1)
apply (metis cUnique nat_neq_iff)
apply (metis cUnique1)
apply (metis cUnique1)
apply (metis cUnique1)
apply (metis (hide_lams, no_types) cUnique less_trans nat_neq_iff)
apply (metis cUnique1)

apply (case_tac "c1>c2") (* case similar to previous*)
apply (rule_tac x=c1 in exI)
apply clarsimp
apply auto
apply (metis (lifting, mono_tags) cSmaller_H1 consistentHistories_commute)
apply (metis cUnique nat_neq_iff)
apply (metis cUnique1)
apply (metis cUnique1)
apply (metis cUnique1)
apply (metis (hide_lams, no_types) cUnique nat_neq_iff)
apply (metis (hide_lams, no_types) cUnique less_trans nat_neq_iff)

apply (rule_tac x=c1 in exI)
apply auto
apply (erule_tac P="existsAddOperationWithoutRemove x r (historyUnion H1 H2)" in rev_notE) 
apply (subst historyUnion_commute)
apply simp
apply (unfold not_less)
apply (erule(4) setSpecValid_H1)
apply (metis consistentHistories_commute)

apply (metis cUnique1)

apply (case_tac "\<exists>c2. (x, c2, r) \<in> E2")
apply clarsimp
apply (rule_tac x=c2 in exI)
apply auto
apply (erule_tac P="existsAddOperationWithoutRemove x r (historyUnion H1 H2)" in rev_notE) 
apply (erule(1) setSpecValid_H1)
apply simp+
apply (metis cUnique le_eq_less_or_eq)
apply (metis bothZero_notExistsAddOperationWithoutRemove)

apply (drule_tac x=c in spec)
apply auto
apply (simp add: existsAddOperationWithoutRemove_def)
apply (frule(4) invC_updArgs_version_Two)
apply clarsimp
apply (drule_tac x=v in spec)
apply (drule mp)
apply (metis (lifting, mono_tags) inHistoryUnionAddOperations2 invC_max2 nth_mem)
apply auto
apply (metis (lifting, mono_tags) setSpecValid_H_remove1)
apply (metis (lifting, mono_tags) setSpecValid_H_remove1)

apply (erule(8) setSpecValid_H3)
apply force
apply (erule(6) setSpecValid_H3)
apply (metis consistentHistories_commute)
apply (metis historyUnion_commute)
apply auto

(* case merge, invC *)
apply (simp add: invC_def)
apply auto
apply (metis invC_min)

apply (erule consistentHistoriesCases2)
apply (metis (lifting, mono_tags) invC_max)
apply (metis (lifting, mono_tags) invC_max)

apply (erule consistentHistoriesCases2)
apply (erule(1) invC_updArgs2)+

apply (erule_tac r=r in consistentHistoriesCases2)
apply (metis (lifting, mono_tags) invC_updArgsMax isPrefixHistoryUnion)
apply (metis (lifting, mono_tags) invC_updArgsMax isPrefixHistoryUnion2)

apply (erule_tac r=r in consistentHistoriesCases2)
apply (erule(2) isPrefix_C_lengthAddOperations)
apply (metis (lifting, mono_tags) invC_max)

apply (erule_tac r=r in consistentHistoriesCases2)
apply (erule(4) setSpecValid_H5)
apply (erule(1) invC_updArgs2)

apply (erule_tac r=r in consistentHistoriesCases2)
apply (simp)
apply clarsimp
apply (metis (lifting, mono_tags) invB_notZero1)

apply (erule_tac r=r in consistentHistoriesCases2)
apply (metis (lifting, mono_tags) invC_max)
apply (metis (lifting, mono_tags) setSpecValid_H5)

apply (erule_tac r=r in consistentHistoriesCases2)
apply (erule(1) invC_updArgs2)
apply (metis (lifting, mono_tags) setSpecValid_H5)

apply (erule_tac r=r in consistentHistoriesCases2)
apply simp
apply (metis (lifting, mono_tags) invB_notZero1)
apply simp
done


end

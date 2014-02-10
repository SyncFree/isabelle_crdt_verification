theory convergence
imports systemModel finalSetFold
begin

(*
here we show, that some relaxed semilattice properties on a state based type 
imply convergence
*)

type_synonym ('pl, 'ua) crdtInvariant = "'ua updateHistory \<Rightarrow> 'pl \<Rightarrow> bool"

definition monotonicUpdates ::"('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> ('pl,'ua) crdtInvariant \<Rightarrow> bool" where
"monotonicUpdates crdt Inv = (\<forall>UH args pl r. Inv UH pl \<longrightarrow> pl \<le>[crdt] t_update crdt args r pl)"

lemma monotonicUpdates: "monotonicUpdates crdt Inv \<Longrightarrow>
Inv UH pl \<Longrightarrow> 
 pl \<le>[crdt] t_update crdt args r pl"
apply (auto simp add: monotonicUpdates_def)
done
                                           

(* semilattice properties: *)
definition "compareReflexive crdt Inv \<equiv> (\<forall>UH x. Inv UH x \<longrightarrow> 
  x \<le>[crdt] x)"
definition "compareTransitive crdt Inv \<equiv> (\<forall>UH x y z. Inv UH x \<and> Inv UH y \<and> Inv UH z \<and> 
  x \<le>[crdt] y \<and> y \<le>[crdt] z \<longrightarrow> x \<le>[crdt] z)"
definition "compareAntisym crdt Inv\<equiv> (\<forall>UH x y. Inv UH x \<and> Inv UH y  \<and> 
  x\<le>[crdt]y \<and> y\<le>[crdt]x \<longrightarrow> x=y)"
definition "mergeCommute crdt Inv = (\<forall>UH x y. Inv UH x \<and> Inv UH y \<longrightarrow> 
  x \<squnion>[crdt] y = y \<squnion>[crdt] x)"
definition "mergeUpperBound crdt Inv \<equiv> (\<forall>UH x y. Inv UH x \<and> Inv UH y \<longrightarrow> 
  x \<le>[crdt] x \<squnion>[crdt] y)"
definition "mergeLeastUpperBound crdt Inv \<equiv> (\<forall>UH x y z. Inv UH x \<and> Inv UH y \<and> Inv UH z \<and>
  x\<le>[crdt]z \<and> y\<le>[crdt]z \<longrightarrow> x \<squnion>[crdt] y \<le>[crdt] z)"


definition semilatticeProperties ::"('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> ('pl,'ua) crdtInvariant \<Rightarrow> bool" where
"semilatticeProperties crdt Inv = (
        compareReflexive crdt Inv
      \<and> compareTransitive crdt Inv
      \<and> compareAntisym crdt Inv
      \<and> mergeCommute crdt Inv
      \<and> mergeUpperBound crdt Inv
      \<and> mergeLeastUpperBound crdt Inv
)"

find_consts "'ua updateHistory"
(* invariant preservance properties *)
definition "invariantInitial crdt Inv \<equiv> 
  (Inv initialUpdateHistory (t_initial crdt))"
definition "invariantMerge crdt Inv \<equiv> 
  (\<forall>UH x y. Inv UH x \<and> Inv UH y \<longrightarrow> Inv UH (t_merge crdt x y))"
definition "invariantUpdate crdt Inv \<equiv> (\<forall>args UH x rx v. Inv UH x \<longrightarrow> 
  Inv (UH(rx:=UH rx@[(v,args)])) (t_update crdt args rx x))"
definition "invariantUpdateOther crdt Inv \<equiv> (\<forall>args UH ry x v. Inv UH x  \<longrightarrow> 
  Inv (UH(ry:=UH ry@[(v,args)])) x)"


definition invariantPreserving ::"('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> ('pl,'ua) crdtInvariant \<Rightarrow> bool" where
"invariantPreserving crdt Inv = (
        invariantInitial crdt Inv
      \<and> invariantMerge crdt Inv
      \<and> invariantUpdate crdt Inv
      \<and> invariantUpdateOther crdt Inv
)"


definition crdtProperties where
"crdtProperties crdt Inv = (
    monotonicUpdates crdt Inv
  \<and> semilatticeProperties crdt Inv
  \<and> invariantPreserving crdt Inv
)"

lemma unfoldCrdtProperties: "\<lbrakk>
(* monotonic updates*)
\<And>  UH args pl r. Inv UH pl \<Longrightarrow> pl \<le>[crdt] t_update crdt args r pl;
(* semilattice properties*)
\<And>UH x. Inv UH x \<longrightarrow> 
  x \<le>[crdt] x;
\<And>UH x y z. Inv UH x \<and> Inv UH y \<and> Inv UH z \<and> 
  x \<le>[crdt] y \<and> y \<le>[crdt] z \<longrightarrow> x \<le>[crdt] z;
\<And>UH x y. Inv UH x \<and> Inv UH y  \<and> 
  x\<le>[crdt]y \<and> y\<le>[crdt]x \<longrightarrow> x=y;
\<And>UH x y. Inv UH x \<and> Inv UH y \<longrightarrow> 
  x \<squnion>[crdt] y = y \<squnion>[crdt] x;
\<And>UH x y. Inv UH x \<and> Inv UH y \<longrightarrow> 
  x \<le>[crdt] x \<squnion>[crdt] y;
\<And>UH x y z. Inv UH x \<and> Inv UH y \<and> Inv UH z \<and>
  x\<le>[crdt]z \<and> y\<le>[crdt]z \<longrightarrow> x \<squnion>[crdt] y \<le>[crdt] z;
(* invariant preserving*)
Inv initialUpdateHistory (t_initial crdt);
\<And>UH x y. Inv UH x \<and> Inv UH y \<Longrightarrow> Inv UH (t_merge crdt x y);
\<And>args UH x rx v. Inv UH x \<Longrightarrow>
  Inv (UH(rx:=UH rx@[(v,args)])) (t_update crdt args rx x);
\<And>args UH ry x v. Inv UH x  \<Longrightarrow>
  Inv (UH(ry:=UH ry@[(v,args)])) x
\<rbrakk> \<Longrightarrow> crdtProperties crdt Inv"
apply (unfold crdtProperties_def invariantPreserving_def monotonicUpdates_def
  invariantInitial_def invariantMerge_def invariantUpdate_def invariantUpdateOther_def semilatticeProperties_def
  compareReflexive_def compareTransitive_def compareAntisym_def mergeCommute_def mergeUpperBound_def mergeLeastUpperBound_def
)
apply safe
apply metis+
done




lemma crdtProperties_monotonicUpdates: "crdtProperties crdt Inv \<Longrightarrow> monotonicUpdates crdt Inv"
by (simp add: crdtProperties_def)
lemma crdtProperties_semilatticeProperties: "crdtProperties crdt Inv \<Longrightarrow> semilatticeProperties crdt Inv"
by (simp add: crdtProperties_def)
lemma crdtProperties_invariantPreserving: "crdtProperties crdt Inv \<Longrightarrow> invariantPreserving crdt Inv"
by (simp add: crdtProperties_def)


lemma invariantInitialI: "invariantPreserving crdt Inv
\<Longrightarrow>  Inv initialUpdateHistory (t_initial crdt)"
apply (auto simp add: invariantPreserving_def invariantInitial_def)
done

lemma invariantInitialI2: "invariantPreserving crdt Inv
\<Longrightarrow>  Inv (\<lambda>r. []) (t_initial crdt)"
apply (drule invariantInitialI)
apply (simp add: initialUpdateHistory_def)
done


lemma invariantMergeI[simp]: "\<lbrakk>
invariantPreserving crdt Inv;
Inv UH x; 
Inv UH y
\<rbrakk> \<Longrightarrow> Inv UH (t_merge crdt x y)"
apply (auto simp add: invariantPreserving_def invariantMerge_def)
done

lemma invariantUpdateI: "\<lbrakk>
invariantPreserving crdt Inv;
Inv UH x
\<rbrakk> \<Longrightarrow>  Inv (UH(rx:=UH rx@[(v,args)])) (t_update crdt args rx x)"
apply (auto simp add: invariantPreserving_def invariantUpdate_def)
done

lemma invariantUpdateI2: "\<lbrakk>
invariantPreserving crdt Inv;
Inv (updateHistory tr) x
\<rbrakk> \<Longrightarrow>  Inv (updateHistory (Trace tr (Update rx args))) (t_update crdt args rx x)"
apply (subst updateHistory_Update)
apply (erule(1)  invariantUpdateI)
done


lemma invariantUpdateOtherI: "\<lbrakk>
invariantPreserving crdt Inv;
Inv UH x
\<rbrakk> \<Longrightarrow>  Inv (UH(r:=UH r@[(v,args)])) x"
apply (auto simp add: invariantPreserving_def invariantUpdateOther_def)
done


lemma invariantUpdateOtherI2: "\<lbrakk>
invariantPreserving crdt Inv;
Inv (updateHistory tr) x
\<rbrakk> \<Longrightarrow>  Inv (updateHistory (Trace tr (Update r args))) x"
apply (subst updateHistory_Update)
apply (erule(1) invariantUpdateOtherI)
done


lemma semilatticePropertiesFromTypeclass: "\<lbrakk>
t_merge crdt = sup;
t_compare crdt = op\<le>
\<rbrakk> \<Longrightarrow> semilatticeProperties (crdt::('pl::semilattice_sup, 'ua, 'qa, 'r) stateBasedType) Inv" 
apply (auto simp add: semilatticeProperties_def)
apply (auto simp add:  
 compareReflexive_def
 compareTransitive_def
 compareAntisym_def
 mergeCommute_def
 mergeUpperBound_def
 mergeLeastUpperBound_def)
apply (metis sup_commute)
done

lemma compareReflexiveI: "\<lbrakk>
semilatticeProperties crdt Inv;
Inv UH x 
\<rbrakk> \<Longrightarrow>  x \<le>[crdt] x"
by (metis compareReflexive_def semilatticeProperties_def)


lemma compareTransitiveI: "\<lbrakk>
x \<le>[crdt] y; 
y \<le>[crdt] z;
semilatticeProperties crdt Inv;
Inv UH x; 
Inv UH y; 
Inv UH z
\<rbrakk> \<Longrightarrow> x \<le>[crdt] z"
apply (unfold compareTransitive_def semilatticeProperties_def)
by (metis (full_types))


lemma compareAntisymI: "\<lbrakk>
x\<le>[crdt]y;
y\<le>[crdt]x;
semilatticeProperties crdt Inv;
Inv UH x;
Inv UH y
\<rbrakk> \<Longrightarrow> x=y"
by (metis compareAntisym_def semilatticeProperties_def)


lemma mergeCommuteI: "\<lbrakk>
semilatticeProperties crdt Inv;
Inv UH x;
Inv UH y
\<rbrakk> \<Longrightarrow> x \<squnion>[crdt] y = y \<squnion>[crdt] x"
by (metis mergeCommute_def semilatticeProperties_def)


lemma mergeUpperBoundI: "\<lbrakk>
semilatticeProperties crdt Inv;
Inv UH x;
Inv UH y
\<rbrakk> \<Longrightarrow>  x \<le>[crdt] x \<squnion>[crdt] y"
by (metis mergeUpperBound_def semilatticeProperties_def)

lemma mergeLeastUpperBoundI: "\<lbrakk>
x\<le>[crdt]z;
y\<le>[crdt]z;
semilatticeProperties crdt Inv;
Inv UH x;
Inv UH y;
Inv UH z
\<rbrakk> \<Longrightarrow>x \<squnion>[crdt] y \<le>[crdt] z"
apply (auto simp add: mergeLeastUpperBound_def semilatticeProperties_def)
done

lemma mergeAbsorb1: "\<lbrakk>
x \<le>[crdt] y;
semilatticeProperties crdt Inv;
invariantPreserving crdt Inv;
Inv UH x;
Inv UH y
\<rbrakk> \<Longrightarrow> t_merge crdt x y = y"
apply (rule_tac crdt=crdt and Inv=Inv in compareAntisymI)
apply (metis compareReflexiveI mergeLeastUpperBoundI)
apply (metis mergeCommuteI mergeUpperBoundI)
apply auto
done

lemma mergeAbsorb2: "\<lbrakk>
x \<le>[crdt] y;
semilatticeProperties crdt Inv;
invariantPreserving crdt Inv;
Inv UH x;
Inv UH y
\<rbrakk> \<Longrightarrow> t_merge crdt y x = y"
by (metis mergeAbsorb1 mergeCommuteI)


lemma lessMerge1: "\<lbrakk>
x \<le>[crdt] y;
semilatticeProperties crdt Inv;
invariantPreserving crdt Inv;
Inv UH x;
Inv UH y;
Inv UH z
\<rbrakk> \<Longrightarrow> x \<le>[crdt] y \<squnion>[crdt] z"
apply (erule compareTransitiveI)
apply (rule mergeUpperBoundI)
apply simp+
done

lemma lessMerge2: "\<lbrakk>
x \<le>[crdt] z;
semilatticeProperties crdt Inv;
invariantPreserving crdt Inv;
Inv UH x;
Inv UH y;
Inv UH z
\<rbrakk> \<Longrightarrow> x \<le>[crdt] y \<squnion>[crdt] z"
by (metis lessMerge1 mergeCommuteI)


lemma mergeIdem: "\<lbrakk>
semilatticeProperties crdt Inv;
invariantPreserving crdt Inv;
Inv UH x
\<rbrakk> \<Longrightarrow> t_merge crdt x x = x"
by (metis compareReflexiveI mergeAbsorb1)

lemma mergeAssoc_H1: "
semilatticeProperties crdt Inv \<Longrightarrow> 
invariantPreserving crdt Inv \<Longrightarrow> 
Inv UH x \<Longrightarrow> 
Inv UH y \<Longrightarrow> 
Inv UH z \<Longrightarrow> 
y \<le>[crdt] x \<squnion>[crdt] (y \<squnion>[crdt] z)"
apply (rule_tac Inv=Inv and UH=UH in lessMerge2)
apply (rule_tac Inv=Inv and UH=UH in lessMerge1)
apply auto
apply (metis compareReflexiveI)
done

lemma mergeAssoc_H2: "
semilatticeProperties crdt Inv \<Longrightarrow> 
invariantPreserving crdt Inv \<Longrightarrow> 
Inv UH x \<Longrightarrow> 
Inv UH y \<Longrightarrow> 
Inv UH z \<Longrightarrow> 
x \<le>[crdt] x \<squnion>[crdt] (y \<squnion>[crdt] z)"
apply (rule_tac Inv=Inv and UH=UH in lessMerge1)
apply auto
apply (metis compareReflexiveI)
done

lemma mergeAssoc_H3: "
semilatticeProperties crdt Inv \<Longrightarrow> 
invariantPreserving crdt Inv \<Longrightarrow> 
Inv UH x \<Longrightarrow> 
Inv UH y \<Longrightarrow> 
Inv UH z \<Longrightarrow> 
z \<le>[crdt] x \<squnion>[crdt] (y \<squnion>[crdt] z)"
apply (rule_tac Inv=Inv and UH=UH in lessMerge2)
apply (rule_tac Inv=Inv and UH=UH in lessMerge2)
apply auto
apply (metis compareReflexiveI)
done

lemma mergeAssoc: "\<lbrakk>
semilatticeProperties crdt Inv;
invariantPreserving crdt Inv;
Inv UH x;
Inv UH y;
Inv UH z
\<rbrakk> \<Longrightarrow> x \<squnion>[crdt] (y \<squnion>[crdt] z) = (x \<squnion>[crdt] y) \<squnion>[crdt] z"
apply (rule_tac crdt=crdt and Inv=Inv and UH=UH in compareAntisymI)
apply (rule_tac Inv=Inv and UH=UH in  mergeLeastUpperBoundI)
apply (metis invariantMergeI lessMerge1 mergeUpperBoundI)
apply (rule_tac Inv=Inv and UH=UH in  mergeLeastUpperBoundI)
apply (metis invariantMergeI mergeAssoc_H3 mergeCommuteI)
apply (metis compareReflexiveI invariantMergeI lessMerge2)
apply auto
apply (rule_tac Inv=Inv and UH=UH in  mergeLeastUpperBoundI)
apply (rule_tac Inv=Inv and UH=UH in mergeLeastUpperBoundI)
apply (metis mergeAssoc_H2)
apply (metis mergeAssoc_H1)
apply auto
apply (metis mergeAssoc_H3)
done

lemma mergeIdem2: "\<lbrakk>
semilatticeProperties crdt Inv;
invariantPreserving crdt Inv;
Inv UH x;
Inv UH y
\<rbrakk> \<Longrightarrow> x \<squnion>[crdt] (x \<squnion>[crdt] y) = x \<squnion>[crdt] y"
by (metis mergeAssoc mergeIdem)


lemma mergeMono: "\<lbrakk>
semilatticeProperties crdt Inv;
invariantPreserving crdt Inv;
xa \<le>[crdt] xb;
ya \<le>[crdt] yb;
Inv UH xa;
Inv UH ya;
Inv UH xb;
Inv UH yb
\<rbrakk> \<Longrightarrow> xa \<squnion>[crdt] ya \<le>[crdt] xb \<squnion>[crdt] yb"
apply (rule mergeLeastUpperBoundI)
defer
defer
apply assumption+
apply auto
apply (metis lessMerge1)
apply (metis lessMerge2)
done

lemma mergeMono2: "\<lbrakk>
semilatticeProperties crdt Inv;
invariantPreserving crdt Inv;
ya \<le>[crdt] yb;
Inv UH x;
Inv UH ya;
Inv UH yb
\<rbrakk> \<Longrightarrow> x \<squnion>[crdt] ya \<le>[crdt] x \<squnion>[crdt] yb"
apply (rule mergeMono)
apply assumption+
apply auto
apply (metis compareReflexiveI)
done


lemma currentStateSubsetHistory: "\<lbrakk>
steps crdt tr (initialState crdt) s
\<rbrakk> \<Longrightarrow> (replicaVV s r, replicaPayload s r) \<in> history s"
apply (induct arbitrary: r rule: stepsInitialInduct2)
apply (auto simp add: initialState_def)
done

lemma initialStateSubsetHistory: "\<lbrakk>
steps crdt tr (initialState crdt) s
\<rbrakk> \<Longrightarrow> (vvZero, t_initial crdt) \<in> history s"
apply (induct rule: stepsInitialInduct2)
apply (auto simp add: initialState_def)
done


(* invariant is preserved with steps *)
lemma invariantPreserving: "\<lbrakk>
steps crdt tr (initialState crdt) s;
invariantPreserving crdt Inv;
(v,pl) \<in> history s
\<rbrakk> \<Longrightarrow> Inv (updateHistory tr) pl"
apply (induct arbitrary: v pl rule: stepsInitialInduct2)
apply auto

(*initial*)
apply (simp add: initialState_def)
apply auto
apply (metis invariantInitialI2)

(* update *)
apply (subst updateHistory_Update)
apply (metis currentStateSubsetHistory invariantUpdateI)

(* update Other*)
apply (subst updateHistory_Update)
apply (metis invariantUpdateOtherI)

(* merge*)
apply (metis currentStateSubsetHistory invariantMergeI)
done

lemma invariantPreserving2: "\<lbrakk>
steps crdt tr (initialState crdt) s;
invariantPreserving crdt Inv;
pl \<in> snd ` history s
\<rbrakk> \<Longrightarrow> Inv (updateHistory tr) pl"
by (auto simp add: invariantPreserving)

lemma invariantPreserving3: "\<lbrakk>
steps crdt tr (initialState crdt) s;
invariantPreserving crdt Inv;
pl \<in> snd ` history s
\<rbrakk> \<Longrightarrow> Inv (updateHistory tr) pl"
by (auto simp add: invariantPreserving)


lemma invariantPreservingInitial: "\<lbrakk>
steps crdt tr (initialState crdt) s;
invariantPreserving crdt Inv
\<rbrakk> \<Longrightarrow> Inv (updateHistory tr) (t_initial crdt)"
by (metis initialStateSubsetHistory invariantPreserving)

lemma invariantPreservingCurrentState: "\<lbrakk>
steps crdt tr (initialState crdt) s;
invariantPreserving crdt Inv
\<rbrakk> \<Longrightarrow> Inv (updateHistory tr) (replicaPayload s r)"
by (metis currentStateSubsetHistory invariantPreserving)

lemma invariantPreservingInitial2: "\<lbrakk>
steps crdt tr (initialState crdt) s;
invariantPreserving crdt Inv
\<rbrakk> \<Longrightarrow> Inv (updateHistory tr) (t_initial crdt)"
by (metis initialStateSubsetHistory invariantPreserving)

lemma invariantPreservingCurrentState2: "\<lbrakk>
steps crdt tr (initialState crdt) s;
invariantPreserving crdt Inv;
UH = (updateHistory tr);
pl = (replicaPayload s r)
\<rbrakk> \<Longrightarrow> Inv UH pl"
by (metis currentStateSubsetHistory invariantPreserving)


definition mergeAll :: "('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> 'pl set \<Rightarrow> 'pl" where
"mergeAll crdt = Finite_Set.fold (t_merge crdt) (t_initial crdt)"

lemma mergeAll_0[simp]: "mergeAll crdt {} = t_initial crdt"
by (metis fold_empty mergeAll_def)


lemma crdtInvariantClosure: "\<lbrakk>
x\<in>closure (t_merge crdt) S;
crdtProperties crdt Inv;
\<And>x. x\<in>S \<Longrightarrow> Inv UH x
\<rbrakk> \<Longrightarrow> Inv UH x"
apply (induct rule: closure.induct)
apply auto
by (metis crdtProperties_def invariantMergeI)



lemma crdtCommutativeOn: "\<lbrakk>
crdtProperties crdt Inv;
\<And>y. y \<in> S \<Longrightarrow> Inv UH y
\<rbrakk> \<Longrightarrow> commutativeOn (t_merge crdt) S"
apply (auto simp add: commutativeOn_def)
apply (rename_tac a b c)
apply (rule_tac t="b \<squnion>[crdt] c" and s="c \<squnion>[crdt] b" in ssubst)
apply (metis crdtInvariantClosure crdtProperties_def mergeCommuteI)
apply (subst mergeAssoc[where Inv=Inv and UH=UH])
apply (metis crdtProperties_def)
apply (metis crdtProperties_def)
apply (simp add: crdtInvariantClosure)+
apply (rule mergeCommuteI[where Inv=Inv and UH=UH])
apply (metis crdtProperties_def)
apply (metis crdtInvariantClosure crdtProperties_def invariantMergeI)
apply (simp add: crdtInvariantClosure)
done

lemma crdtIdempotentOn: "\<lbrakk>
crdtProperties crdt Inv;
\<And>y. y \<in> S \<Longrightarrow> Inv UH y
\<rbrakk> \<Longrightarrow> idempotentOn (t_merge crdt) S"
apply (auto simp add: idempotentOn_def)
apply (rule mergeIdem2[where Inv=Inv and UH=UH])
apply (metis crdtProperties_def)
apply (metis crdtProperties_def)
apply (metis crdtInvariantClosure)+
done

lemma mergeAll_insert: "\<lbrakk>
crdtProperties crdt Inv;
finite S;
Inv UH x;
Inv UH (t_initial crdt);
\<And>y. y\<in>S \<Longrightarrow> Inv UH y
\<rbrakk> \<Longrightarrow> mergeAll crdt (insert x S) = x \<squnion>[crdt] (mergeAll crdt S)"
apply (auto simp add: mergeAll_def)
apply (rule cl_fold_insert_idem)
apply assumption
apply (erule crdtCommutativeOn)
apply auto
apply (erule crdtIdempotentOn)
apply auto
done


lemma mergeAll_1: "\<lbrakk>
crdtProperties crdt Inv;
Inv UH (t_initial crdt);
Inv UH x;
t_initial crdt \<le>[crdt] x
\<rbrakk> \<Longrightarrow> mergeAll crdt {x} = x"
apply (subst mergeAll_insert)
apply assumption
apply auto
by (metis crdtProperties_def mergeAbsorb2)


lemma localVVMax: "\<lbrakk>
steps crdt tr (initialState crdt) s;
(v,pl) \<in> history s
\<rbrakk> \<Longrightarrow> v\<guillemotright>r \<le> replicaVV s r\<guillemotright>r"
apply (induct arbitrary:r v pl  rule: stepsInitialInduct3)

apply (simp add: initialState_def)

apply auto
apply (metis currentStateSubsetHistory)
apply (metis le_SucI)
apply (unfold versionVectorSupComponent)
apply auto
apply (metis currentStateSubsetHistory)
apply (metis sup_absorb2 sup_max)
done

lemma incVVNotInHistory: "\<lbrakk>
steps crdt tr (initialState crdt) s
\<rbrakk> \<Longrightarrow> (incVV r (replicaVV s r),pl) \<notin> history s"
apply (rule ccontr)
apply clarsimp
apply (frule(1) localVVMax[where r=r])
apply (simp add: incVV_def)
done

lemma finiteHistory: "\<lbrakk>
steps crdt tr (initialState crdt) s
\<rbrakk> \<Longrightarrow> finite (history s)"
apply (induct rule: stepsInitialInduct)
apply (auto simp add: initialState_def)
done

lemma greaterInitial: "\<lbrakk>
steps crdt tr (initialState crdt) s;
crdtProperties crdt Inv;
(v,pl) \<in> history s
\<rbrakk> \<Longrightarrow> t_initial crdt \<le>[crdt] pl"
apply (induct arbitrary: v pl  rule: stepsInitialInduct3)
apply (simp add: initialState_def)
apply (metis (full_types) compareReflexiveI crdtProperties_invariantPreserving crdtProperties_semilatticeProperties invariantInitialI)
apply auto

apply (rule_tac y="replicaPayload s r"  and Inv=Inv and UH="updateHistory (Trace tr (Update r args))" in compareTransitiveI)
apply (metis currentStateSubsetHistory)
apply (rule_tac Inv=Inv and UH="updateHistory tr" in monotonicUpdates)
apply (erule crdtProperties_monotonicUpdates)
apply (metis (full_types) crdtProperties_invariantPreserving invariantPreservingCurrentState)
apply (metis crdtProperties_semilatticeProperties)
apply (metis crdtProperties_invariantPreserving invariantPreservingInitial)
apply (metis (full_types) crdtProperties_invariantPreserving invariantPreservingCurrentState invariantUpdateOtherI2)
apply (metis (mono_tags) crdtProperties_invariantPreserving invariantPreservingCurrentState invariantUpdateI2)

apply (rule_tac Inv=Inv and UH="updateHistory tr" in  lessMerge1)
apply auto
apply (metis crdtProperties_semilatticeProperties)
apply (metis crdtProperties_invariantPreserving)
apply (metis crdtProperties_invariantPreserving invariantPreservingInitial)
apply (metis (full_types) crdtProperties_invariantPreserving invariantPreserving)
by (metis (full_types) crdtProperties_invariantPreserving invariantPreservingCurrentState)



lemma mergeAll1b: "
 steps crdt tr (initialState crdt) s \<Longrightarrow>
    crdtProperties crdt Inv \<Longrightarrow>
    (v, pl) \<in> history s \<Longrightarrow> mergeAll crdt {pl} = pl
"
apply (rule mergeAll_1[where crdt=crdt and Inv=Inv and UH="updateHistory tr"])
  apply auto
  apply (metis crdtProperties_def invariantPreservingInitial)
  apply (metis crdtProperties_invariantPreserving invariantPreserving)
  apply (metis greaterInitial)
done


definition historyInvariant :: "('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> 'pl history \<Rightarrow> bool" where
"historyInvariant crdt H = (\<forall>H1 H2. H1 \<subseteq> H \<and> H2 \<subseteq> H \<and> supSet (fst ` H1) \<le> supSet (fst ` H2) 
  \<longrightarrow> mergeAll crdt (snd ` H1) \<le>[crdt] mergeAll crdt (snd ` H2))"

lemma useHistoryInvariant: "\<lbrakk>
historyInvariant crdt H;
Ha \<subseteq> H;
Hb \<subseteq> H;
supSet (fst ` Ha) \<le> supSet (fst ` Hb)
\<rbrakk> \<Longrightarrow> mergeAll crdt (snd ` Ha) \<le>[crdt] mergeAll crdt (snd ` Hb)"
apply (auto simp add: historyInvariant_def)
done


lemma mergeAllInitial: "\<lbrakk>
H \<subseteq> {(vvZero, t_initial crdt)};
crdtProperties crdt Inv;
Inv UH (t_initial crdt)
\<rbrakk> \<Longrightarrow> (mergeAll crdt (snd ` H)) = t_initial crdt"
apply (drule subset_singletonD)
apply auto
apply (rule mergeAll_1)
apply assumption
apply auto
by (metis compareReflexiveI crdtProperties_def)


lemma supSet_H1a: " 
finite A \<Longrightarrow>
(\<And>a. a \<in> A \<Longrightarrow> a\<noteq>incVV r x \<Longrightarrow>  a \<guillemotright> r \<le> x \<guillemotright> r) \<Longrightarrow>
    supSet (insert (x \<guillemotright> r) (component r ` (A - {incVV r x}))) = x\<guillemotright>r"
apply (subst supSetInsert, force)
apply (rule sup_absorb1)
apply (rule supSetBigger)
apply auto
by metis


lemma supSet_H1b: "r \<noteq> ra \<Longrightarrow> (insert (x \<guillemotright> ra) (component ra ` (A - {incVV r x}))) = (insert (x \<guillemotright> ra) (component ra ` A))"
apply auto
done

lemma  supSet_H1:"\<lbrakk>
supSet A \<le> supSet B;
X = (A - {incVV r x}) \<union> {x};
Y = (B - {incVV r x}) \<union> {x};
finite A;
finite B;
\<And>a. a\<in>A \<Longrightarrow> a\<noteq>incVV r x \<Longrightarrow> a\<guillemotright>r \<le> x\<guillemotright>r;
\<And>a. a\<in>B \<Longrightarrow> a\<noteq>incVV r x \<Longrightarrow> a\<guillemotright>r \<le> x\<guillemotright>r
\<rbrakk> \<Longrightarrow> supSet X \<le> supSet Y"
apply (auto simp add: less_eq_versionVector_def)
apply (unfold supSet_versionVectorComponent)
apply (subst supSet_versionVectorComponent, force)
apply (subst supSet_versionVectorComponent, force)
apply auto
apply (case_tac "r=ra")
apply auto
apply (subst supSet_H1a, force, force)
apply (subst supSet_H1a, force, force)
apply simp
apply (simp add: supSet_H1b)
apply (subst supSetInsert, force)
apply (subst supSetInsert, force)
apply (metis le_refl sup_mono)
done

lemma  supSet_H1c:"\<lbrakk>
supSet A \<le> supSet B;
X = (A - {incVV r x});
Y = (B - {incVV r x}) \<union> {x};
finite A;
finite B;
\<And>a. a\<in>A \<Longrightarrow> a\<noteq>incVV r x \<Longrightarrow> a\<guillemotright>r \<le> x\<guillemotright>r;
\<And>a. a\<in>B \<Longrightarrow> a\<noteq>incVV r x \<Longrightarrow> a\<guillemotright>r \<le> x\<guillemotright>r
\<rbrakk> \<Longrightarrow> supSet X \<le> supSet Y"
apply (rule_tac y="supSet (X \<union> {x})" in order_trans)
apply clarsimp
apply (metis finite_Diff finite_insert subset_insertI supSetSubSet)
apply (erule supSet_H1)
apply auto
done


lemma stepsToHistory_H2: "
steps crdt tr (initialState crdt) s \<Longrightarrow>
H1 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
fst ` (H1 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))}) = fst ` H1 - {incVV r (replicaVV s r)}
"
apply auto
apply (case_tac "(incVV r (replicaVV s r), b) \<in> history s")
apply auto
by (metis (full_types) incVVNotInHistory)

lemma invariantMergeAll: "\<lbrakk>
finite S;
crdtProperties crdt Inv;
Inv UH (t_initial crdt);
\<And>x. x\<in>S \<Longrightarrow> Inv UH x
\<rbrakk> \<Longrightarrow> Inv UH (mergeAll crdt S)"
apply (induct rule: finite_induct)
apply clarsimp
apply (subst mergeAll_insert[where Inv=Inv])
apply auto
by (metis crdtProperties_def invariantMergeI)


lemma invariantMergeAllHistory: "
 steps crdt (Trace tr (Update r args)) (initialState crdt)
        \<lparr>replicaPayload = (replicaPayload s)(r := t_update crdt args r (replicaPayload s r)), replicaVV = (replicaVV s)(r := incVV r (replicaVV s r)),
           history = insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)
        \<rparr> \<Longrightarrow>
       crdtProperties crdt Inv \<Longrightarrow>
       H \<subseteq> snd ` (insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)) \<Longrightarrow>
       Inv (updateHistory (Trace tr (Update r args))) (mergeAll crdt H)
"
apply (frule finiteHistory)
apply (rule invariantMergeAll)
apply auto
apply (metis finite.insertI finite_imageI finite_subset)
apply (metis (hide_lams, no_types) crdtProperties_invariantPreserving invariantPreservingInitial)
apply (erule invariantPreserving3)
apply auto
by (metis crdtProperties_invariantPreserving)


lemma stepsToHistory_H3a1: "
steps crdt (Trace tr (Update r args)) (initialState crdt)
           \<lparr>replicaPayload = (replicaPayload s)(r := t_update crdt args r (replicaPayload s r)), replicaVV = (replicaVV s)(r := incVV r (replicaVV s r)),
              history = insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)
           \<rparr> \<Longrightarrow>
          H1 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
          invariantPreserving crdt Inv \<Longrightarrow> (v, pl) \<in> H1 \<Longrightarrow> Inv (updateHistory (Trace tr (Update r args)))  pl
"
apply (case_tac "(v,pl) = (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))")
apply auto
apply (metis fun_upd_same invariantPreservingCurrentState systemState.select_convs(1))
apply (frule_tac v=v and pl=pl in  invariantPreserving)
apply simp
apply force
apply clarsimp
apply (frule_tac v=v and pl=pl in  invariantPreserving)
apply simp
apply force
apply clarsimp
done

lemma stepsToHistory_H3a: "steps crdt (Trace tr (Update r args)) (initialState crdt)
     \<lparr>replicaPayload = (replicaPayload s)(r := t_update crdt args r (replicaPayload s r)), replicaVV = (replicaVV s)(r := incVV r (replicaVV s r)),
        history = insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)
    \<rparr> \<Longrightarrow>
    crdtProperties crdt Inv \<Longrightarrow>
    H1 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
   Inv (updateHistory (Trace tr (Update r args))) (mergeAll crdt (snd ` H1))"
apply (frule crdtProperties_invariantPreserving)
apply (rule invariantMergeAll)
apply (frule finiteHistory)
apply auto
apply (metis (full_types) finite_imageI finite_insert finite_subset)
apply (metis invariantPreservingInitial )
apply (erule(3) stepsToHistory_H3a1)
done


lemma stepsToHistory_H3b: "
        steps crdt (Trace tr (Update r args)) (initialState crdt)
         \<lparr>replicaPayload = (replicaPayload s)(r := t_update crdt args r (replicaPayload s r)), replicaVV = (replicaVV s)(r := incVV r (replicaVV s r)),
            history = insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)
        \<rparr> \<Longrightarrow>
        crdtProperties crdt Inv \<Longrightarrow>
        H1 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
        y \<in> snd ` (H1 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))}) \<Longrightarrow>
        Inv (updateHistory (Trace tr (Update r args))) y
"
  apply (erule invariantPreserving3)
  apply (metis crdtProperties_invariantPreserving)
  apply (force intro: image_mono in_mono insert_compr set_diff_eq subset_insert_iff)
done

lemma stepsToHistory_H3c: "
    steps crdt (Trace tr (Update r args)) (initialState crdt)
     \<lparr>replicaPayload = (replicaPayload s)(r := t_update crdt args r (replicaPayload s r)), replicaVV = (replicaVV s)(r := incVV r (replicaVV s r)),
        history = insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)
        \<rparr> \<Longrightarrow>
    crdtProperties crdt Inv \<Longrightarrow>
    H1 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
    Inv (updateHistory (Trace tr (Update r args)))
     (mergeAll crdt (snd ` (H1 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))})))
"
apply (rule invariantMergeAll)
apply (frule finiteHistory)
apply (metis (hide_lams, no_types) finite_Diff finite_imageI finite_subset systemState.select_convs(3))
apply assumption
apply (metis (hide_lams, no_types) crdtProperties_invariantPreserving invariantPreservingInitial)
apply (erule(3) stepsToHistory_H3b)
done

lemma stepsToHistory_H3: "
 steps crdt tr (initialState crdt) s \<Longrightarrow>
       steps crdt (Trace tr (Update r args)) (initialState crdt)
        \<lparr>replicaPayload = (replicaPayload s)(r := t_update crdt args r (replicaPayload s r)), replicaVV = (replicaVV s)(r := incVV r (replicaVV s r)),
           history = insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)
           \<rparr> \<Longrightarrow>
       
       crdtProperties crdt Inv \<Longrightarrow>
       H1 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
      
       (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) \<in> H1 \<Longrightarrow>
       mergeAll crdt (snd ` H1) = t_update crdt args r (replicaPayload s r) \<squnion>[crdt] mergeAll crdt (insert (replicaPayload s r) (snd ` (H1 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))})))
"

apply (subst mergeAll_insert[where Inv=Inv and UH="(updateHistory (Trace tr (Update r args)))"])
  apply simp
  apply (frule finiteHistory)
  apply (metis (hide_lams, no_types) finite_Diff finite_imageI finite_insert rev_finite_subset)
  apply (metis (full_types) crdtProperties_invariantPreserving invariantPreservingCurrentState invariantUpdateOtherI2)
  apply (metis crdtProperties_invariantPreserving invariantPreservingInitial)
  apply (erule(3) stepsToHistory_H3b)


apply (subst mergeAssoc[where Inv=Inv and UH="(updateHistory (Trace tr (Update r args)))"])
  apply (metis crdtProperties_semilatticeProperties)
  apply (metis crdtProperties_invariantPreserving)
  apply (metis (full_types) crdtProperties_def invariantPreservingCurrentState invariantUpdateI2)
  apply (metis (full_types) crdtProperties_def invariantPreservingCurrentState invariantUpdateOtherI2)
  apply (erule(2) stepsToHistory_H3c)

apply (subst mergeAbsorb2[where Inv=Inv and UH="(updateHistory (Trace tr (Update r args)))"])
  apply (metis monotonicUpdates crdtProperties_invariantPreserving crdtProperties_monotonicUpdates invariantPreservingCurrentState2)
  apply (metis crdtProperties_semilatticeProperties)
  apply (metis crdtProperties_invariantPreserving)
  apply (metis (full_types) crdtProperties_invariantPreserving invariantPreservingCurrentState invariantUpdateOtherI2)
  apply (metis crdtProperties_invariantPreserving invariantPreservingCurrentState2 invariantUpdateI2)


apply (subst mergeAll_insert[symmetric, where Inv=Inv and UH="(updateHistory (Trace tr (Update r args)))"])
  apply assumption
  apply (frule finiteHistory)
  apply (metis (hide_lams, no_types) finite_Diff finite_imageI finite_insert finite_subset)
  apply (metis crdtProperties_def stepsToHistory_H3a1)
  apply (metis crdtProperties_invariantPreserving invariantPreservingInitial2)
  apply (erule(3) stepsToHistory_H3b)  

apply (subgoal_tac "(snd ` H1) =
    (insert (t_update crdt args r (replicaPayload s r)) (snd ` (H1 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))})))")
apply simp
apply force
done


lemma stepsToHistory_H3d: "
 steps crdt tr (initialState crdt) s \<Longrightarrow>
       steps crdt (Trace tr (Update r args)) (initialState crdt)
        \<lparr>replicaPayload = (replicaPayload s)(r := t_update crdt args r (replicaPayload s r)), replicaVV = (replicaVV s)(r := incVV r (replicaVV s r)),
           history = insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)
           \<rparr> \<Longrightarrow>
       crdtProperties crdt Inv \<Longrightarrow>
       H1 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
       (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) \<in> H1 \<Longrightarrow>
    Inv (updateHistory (Trace tr (Update r args)))
        (mergeAll crdt (insert (replicaPayload s r) (snd ` (H1 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))}))))
"
apply (rule invariantMergeAll)
apply (frule finiteHistory)
apply (metis (hide_lams, full_types) finite_imageI finite_insert finite_subset fun_upd_image)
apply assumption
apply (metis (hide_lams, no_types) crdtProperties_invariantPreserving invariantPreservingInitial)
apply (case_tac "x = replicaPayload s r")
apply clarsimp
apply (metis (full_types) crdtProperties_invariantPreserving invariantPreservingCurrentState invariantUpdateOtherI2)
apply (erule(2) stepsToHistory_H3b)
apply clarsimp
done


lemma stepsToHistory_H4: "
steps crdt tr (initialState crdt) s \<Longrightarrow>
       steps crdt (Trace tr (Update r args)) (initialState crdt)
        \<lparr>replicaPayload = (replicaPayload s)(r := t_update crdt args r (replicaPayload s r)), replicaVV = (replicaVV s)(r := incVV r (replicaVV s r)),
           history = insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)
           \<rparr> \<Longrightarrow>
       historyInvariant crdt (history s) \<Longrightarrow>
       crdtProperties crdt Inv \<Longrightarrow>
       H1 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
       H2 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
       supSet (fst ` H1) \<le> supSet (fst ` H2) \<Longrightarrow>
       (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) \<in> H1 \<Longrightarrow>
       (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) \<in> H2 \<Longrightarrow> 
       mergeAll crdt (snd ` H1) \<le>[crdt] mergeAll crdt (snd ` H2)
"

apply (cut_tac 
  Ha="(H1 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))}) \<union> {(replicaVV s r, replicaPayload s r)}"
  and Hb="(H2 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))}) \<union> {(replicaVV s r, replicaPayload s r)}"
  and crdt=crdt and H="history s"
  in useHistoryInvariant)
apply assumption
apply (clarsimp, rule conjI)
apply (metis currentStateSubsetHistory)
apply force
apply (clarsimp, rule conjI)
apply (metis currentStateSubsetHistory)
apply (metis subset_insert_iff)
apply (erule_tac x="replicaVV s r" and r=r in supSet_H1)
apply clarsimp
apply (unfold stepsToHistory_H2)
apply simp
apply simp
apply (unfold stepsToHistory_H2)
apply simp
apply (metis finiteHistory finite_imageI finite_insert finite_subset)
apply (metis finiteHistory finite_imageI finite_insert finite_subset)
apply clarsimp
apply (metis in_mono insertE localVVMax prod.inject)
apply clarsimp
apply (metis in_mono insertE localVVMax prod.inject)
apply clarsimp

apply (subst stepsToHistory_H3)
apply assumption+
apply (subst stepsToHistory_H3)
apply assumption+
apply (rule_tac Inv=Inv and UH="updateHistory (Trace tr (Update r args))" in mergeMono2)
apply (metis crdtProperties_semilatticeProperties)
apply (metis crdtProperties_invariantPreserving)
apply assumption
apply (metis (full_types) crdtProperties_invariantPreserving invariantPreservingCurrentState invariantUpdateI2)
apply (erule(4) stepsToHistory_H3d)
apply (erule(4) stepsToHistory_H3d)
done



lemma mergeAllSmaller: "\<lbrakk>
finite B;
crdtProperties crdt Inv;
y\<in>B;
x \<le>[crdt] y;
Inv UH x;
 Inv UH (t_initial crdt);
\<And>y. y\<in>B \<Longrightarrow> Inv UH y
\<rbrakk> \<Longrightarrow> x \<le>[crdt] mergeAll crdt B"
apply (rule_tac t="B" and s="insert y (B - {y})" in ssubst)
apply force
apply (subst mergeAll_insert[where Inv=Inv])
apply assumption+
apply force
apply assumption+
apply (metis Diff_iff)
apply (erule_tac lessMerge1)
apply (erule crdtProperties_semilatticeProperties)
apply (erule crdtProperties_invariantPreserving)
apply auto
apply (rule invariantMergeAll)
apply auto
done

lemma initialSmallerMergeAll: "\<lbrakk>
finite B;
crdtProperties crdt Inv;
 Inv UH (t_initial crdt);
\<And>y. y\<in>B \<Longrightarrow> Inv UH y
\<rbrakk> \<Longrightarrow> t_initial crdt \<le>[crdt] mergeAll crdt B"
apply (induct arbitrary:  rule: finite_induct)
apply auto
apply (metis (full_types) compareReflexiveI crdtProperties_def)
apply (subst mergeAll_insert)
apply assumption
apply auto
by (metis crdtProperties_def invariantMergeAll lessMerge2)

lemma mergeAllSmallerQuasiSubset: "\<lbrakk>
finite A;
finite B;
\<And>y. y\<in>A \<Longrightarrow> \<exists>x\<in>B. y \<le>[crdt] x;
 Inv UH (t_initial crdt);
\<And>y. y\<in>A \<Longrightarrow> Inv UH y;
\<And>y. y\<in>B \<Longrightarrow> Inv UH y;
crdtProperties crdt Inv
\<rbrakk> \<Longrightarrow> mergeAll crdt A \<le>[crdt] mergeAll crdt B"
apply (induct arbitrary:  rule: finite_induct)
apply auto
apply (metis (full_types) initialSmallerMergeAll)
apply (subst mergeAll_insert)
apply assumption
apply auto
apply (rule_tac Inv=Inv and UH=UH in mergeLeastUpperBoundI)
apply auto
apply (drule_tac x=x in meta_spec)
apply clarsimp
apply (erule(3) mergeAllSmaller)
apply force
apply force
apply force
apply (metis crdtProperties_semilatticeProperties)
apply (metis invariantMergeAll)
apply (metis invariantMergeAll)
done

lemma mergeAllSmallerSubset: "\<lbrakk>
finite B;
A \<subseteq> B;
 Inv UH (t_initial crdt);
\<And>y. y\<in>B \<Longrightarrow> Inv UH y;
crdtProperties crdt Inv
\<rbrakk> \<Longrightarrow> mergeAll crdt A \<le>[crdt] mergeAll crdt B"
apply (rule mergeAllSmallerQuasiSubset)
apply auto
apply (metis rev_finite_subset)
by (metis compareReflexiveI crdtProperties_def set_rev_mp)





lemma stepsToHistory_H5: "steps crdt tr (initialState crdt) s \<Longrightarrow>
       steps crdt (Trace tr (Update r args)) (initialState crdt)
        \<lparr>replicaPayload = (replicaPayload s)(r := t_update crdt args r (replicaPayload s r)), replicaVV = (replicaVV s)(r := incVV r (replicaVV s r)),
           history = insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s)
           \<rparr> \<Longrightarrow>
       historyInvariant crdt (history s) \<Longrightarrow>
       crdtProperties crdt Inv \<Longrightarrow>
       H1 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
       H2 \<subseteq> insert (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) (history s) \<Longrightarrow>
       supSet (fst ` H1) \<le> supSet (fst ` H2) \<Longrightarrow>
       (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) \<notin> H1 \<Longrightarrow>
       H1 \<subseteq> history s \<Longrightarrow>
       (incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) \<in> H2 \<Longrightarrow>
       mergeAll crdt (insert (replicaPayload s r) (snd ` (H2 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))}))) \<le>[crdt]
       mergeAll crdt (snd ` H2)
"
apply (subst mergeAll_insert[where UH="updateHistory (Trace tr (Update r args))"])
apply assumption+
apply (frule finiteHistory, rule finite_imageI)
apply (metis finite_Diff finite_insert finite_subset)
apply (metis crdtProperties_invariantPreserving currentStateSubsetHistory invariantPreserving invariantUpdateOtherI2)
apply (metis crdtProperties_invariantPreserving invariantPreservingInitial2)
apply (erule_tac Inv=Inv in invariantPreserving3)
apply (metis crdtProperties_invariantPreserving)
apply force

apply (rule_tac Inv=Inv and UH="updateHistory (Trace tr (Update r args))" in mergeLeastUpperBoundI)
apply (rule_tac y=" t_update crdt args r (replicaPayload s r)" and Inv=Inv and UH="updateHistory (Trace tr (Update r args))" in mergeAllSmaller)
apply (frule finiteHistory, rule finite_imageI)
apply (metis finite_insert finite_subset)
apply force
apply force
apply (metis crdtProperties_invariantPreserving crdtProperties_monotonicUpdates invariantPreservingCurrentState2 monotonicUpdates_def)
apply (metis crdtProperties_invariantPreserving invariantPreservingCurrentState2 invariantUpdateOtherI2)
apply (metis crdtProperties_invariantPreserving invariantPreservingInitial2)
apply (erule_tac Inv=Inv in invariantPreserving3)
apply (metis crdtProperties_invariantPreserving)
apply clarsimp
apply force
apply (rule_tac Inv=Inv and UH="updateHistory (Trace tr (Update r args))" in mergeAllSmallerSubset)
apply (metis (hide_lams, no_types) finiteHistory finite_imageI finite_insert finite_subset)
apply clarsimp
apply (metis image_iff snd_eqD)
apply (metis crdtProperties_invariantPreserving invariantPreservingInitial2)
apply (erule_tac Inv=Inv in invariantPreserving3)
apply (metis crdtProperties_invariantPreserving)
apply clarsimp
apply force
apply simp

apply (metis crdtProperties_semilatticeProperties)
apply (metis (full_types) crdtProperties_invariantPreserving invariantPreservingCurrentState invariantUpdateOtherI2)
apply (metis (hide_lams, no_types) stepsToHistory_H3c)
apply (metis (hide_lams, no_types) stepsToHistory_H3a)
done


lemma notSubsetInsertX: "
\<not> H \<subseteq> S \<Longrightarrow>
H \<subseteq> insert x S \<Longrightarrow>
x\<in>H
 "
apply auto
done

lemma supSetExtractSup: "
       steps crdt tr (initialState crdt) s \<Longrightarrow>
       H \<subseteq> insert (sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r) (history s) \<Longrightarrow>
       \<not> H \<subseteq> history s \<Longrightarrow>
       supSet (fst ` H) = supSet (fst ` (H - {(sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r)} 
          \<union> {(vv, pl), (replicaVV s r, replicaPayload s r)}))
"
apply (frule finiteHistory)
apply (drule(1) notSubsetInsertX)
apply auto
apply (subst supSetInsert)
apply (metis (hide_lams, full_types) finite_imageI finite_insert finite_subset fun_upd_image)
apply (subst supSetInsert)
apply (metis (hide_lams, full_types) finite_imageI finite_insert finite_subset fun_upd_image)
apply (subst sup_assoc[symmetric])
apply (subst supSetInsert[symmetric])
apply (metis (hide_lams, full_types) finite_imageI finite_insert finite_subset fun_upd_image)
apply (rule_tac t="insert (sup vv (replicaVV s r)) (fst ` (H - {(sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r)}))"
  and s="fst ` H" in ssubst)
apply force
apply (rule refl)
done

lemma mergeAllExtractMerge: "
steps crdt tr (initialState crdt) s \<Longrightarrow>
       (vv, pl) \<in> history s \<Longrightarrow>
       crdtProperties crdt Inv \<Longrightarrow>
       H \<subseteq> insert (sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r) (history s) \<Longrightarrow>
       \<not> H \<subseteq> history s \<Longrightarrow>
       mergeAll crdt (snd ` H) =
       mergeAll crdt (snd ` (H - {(sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r)} \<union> {(vv, pl), (replicaVV s r, replicaPayload s r)}))
"
apply (frule finiteHistory)
apply (drule(1) notSubsetInsertX)
apply auto
apply (subst mergeAll_insert[where Inv=Inv and UH="updateHistory tr"])
  apply assumption
  apply (metis (hide_lams, full_types) finite_imageI finite_insert finite_subset fun_upd_image)
  apply (metis crdtProperties_invariantPreserving invariantPreserving)
  apply (metis crdtProperties_invariantPreserving invariantPreservingInitial)
  apply (erule insertE)
  apply clarsimp
  apply (metis crdtProperties_invariantPreserving invariantPreservingCurrentState)
  apply (erule invariantPreserving2)
  apply (metis crdtProperties_invariantPreserving)
  apply force

apply (subst mergeAll_insert[where Inv=Inv and UH="updateHistory tr"])
  apply assumption
  apply (metis (hide_lams, full_types) finite_imageI finite_insert finite_subset fun_upd_image)
  apply (metis crdtProperties_invariantPreserving invariantPreservingCurrentState)
  apply (metis crdtProperties_invariantPreserving invariantPreservingInitial)
  apply (erule invariantPreserving2)
  apply (metis crdtProperties_invariantPreserving)
  apply force

apply (subst mergeAssoc[where Inv=Inv and UH="updateHistory tr"])
  apply (metis crdtProperties_semilatticeProperties)
  apply (metis crdtProperties_invariantPreserving)
  apply (metis crdtProperties_invariantPreserving invariantPreserving)
  apply (metis crdtProperties_invariantPreserving invariantPreservingCurrentState)
  apply (rule invariantMergeAll)
    apply (metis finite.insertI finite_Diff finite_imageI rev_finite_subset)
    apply metis
    apply (metis crdtProperties_invariantPreserving invariantPreservingInitial)
    apply (erule invariantPreserving2)
    apply (metis crdtProperties_invariantPreserving)
    apply force

apply (subst mergeAll_insert[symmetric, where Inv=Inv and UH="updateHistory tr"])
  apply assumption
  apply (metis (hide_lams, full_types) finite_imageI finite_insert finite_subset fun_upd_image)
  apply (metis crdtProperties_invariantPreserving invariantMergeI invariantPreserving invariantPreservingCurrentState)
  apply (metis crdtProperties_invariantPreserving invariantPreservingInitial)
  apply (erule invariantPreserving2)
  apply (metis crdtProperties_invariantPreserving)
  apply force

apply (rule_tac t=" (snd ` H)" 
  and s="(insert (pl \<squnion>[crdt] replicaPayload s r) (snd ` (H - {(sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r)})))"
  in ssubst)
apply force
apply (rule refl)
done





lemma stepsToHistory: "\<lbrakk>
steps crdt tr (initialState crdt) s;
crdtProperties crdt Inv
\<rbrakk> \<Longrightarrow> historyInvariant crdt (history s)"
apply (induct  rule: stepsInitialInduct3)


(* initial *)
apply (subst historyInvariant_def)
apply auto
apply (simp add: initialState_def)
apply (subst mergeAllInitial[where Inv=Inv and UH="initialUpdateHistory"])
apply auto
apply (metis crdtProperties_def invariantInitialI)
apply (subst mergeAllInitial[where Inv=Inv and UH="initialUpdateHistory"])
apply auto
apply (metis crdtProperties_def invariantInitialI)
apply (metis (full_types) compareReflexiveI crdtProperties_def invariantInitialI)

(* step *)
apply (subst historyInvariant_def)
apply auto
apply (case_tac "(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) \<in> H1")
apply (case_tac "(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) \<in> H2")

(* case: new element in both H1 and H2: *)
apply (erule(8) stepsToHistory_H4)

(* case: new element only in H1: *)

(* this case cannot happen, because of versions *)

apply (subgoal_tac "supSet (fst ` H1)\<guillemotright>r > supSet (fst ` H2)\<guillemotright>r")
apply (metis versionVectorNotLessEqI)
apply (subst supSet_versionVectorComponent)
apply (metis (hide_lams, no_types) finiteHistory finite_imageI finite_insert finite_subset)
apply (subst supSet_versionVectorComponent)
apply (metis (hide_lams, no_types) finiteHistory finite_imageI finite_insert finite_subset)

apply (rule_tac t="supSet ((\<lambda>v. v \<guillemotright> r) ` fst ` H1)" and s="Suc (replicaVV s r\<guillemotright>r)" in ssubst)
apply (rule antisym)
apply (rule supSetBigger)
apply (rule finite_imageI, rule finite_imageI)
apply (metis finiteHistory finite_insert finite_subset)
apply auto
apply (case_tac "a = incVV r (replicaVV s r)")
apply clarsimp
apply (rule le_SucI)
apply (erule_tac pl=b in localVVMax)
apply force
apply (rule supSetSmaller)
apply (rule finite_imageI, rule finite_imageI)
apply (metis finiteHistory finite_insert finite_subset)
apply (rule_tac x="incVV r (replicaVV s r)" in rev_image_eqI)
apply (rule_tac x="(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))" in image_eqI)
apply simp
apply simp
apply simp
apply (subst less_Suc_eq_le)
apply (rule supSetBigger)
apply (rule finite_imageI, rule finite_imageI)
apply (metis finiteHistory finite_insert finite_subset)
apply (unfold image_iff)
apply clarsimp
apply (erule_tac pl=b in localVVMax)
apply (metis set_mp subset_insert)

(* case: new element is not in H1 *)

apply (subgoal_tac "H1 \<subseteq> history s")
prefer 2
apply force

apply (case_tac "(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r)) \<in> H2")

(* case: new element only in H2 *)



apply (cut_tac 
  Ha="H1"
  and Hb="(H2 - {(incVV r (replicaVV s r), t_update crdt args r (replicaPayload s r))}) \<union> {(replicaVV s r, replicaPayload s r)}"
  and crdt=crdt and H="history s"
  in useHistoryInvariant)
apply assumption
apply assumption
apply (clarsimp, rule conjI)
apply (metis currentStateSubsetHistory)
apply force
apply (erule_tac x="replicaVV s r" and r=r in supSet_H1c)
apply (subst Diff_triv)
apply clarsimp
apply (metis incVVNotInHistory set_mp)
apply simp
apply clarsimp
apply (metis (hide_lams, no_types) stepsToHistory_H2)

apply (metis finiteHistory finite_imageI finite_subset)
apply (metis finiteHistory finite_imageI finite_insert finite_subset)
apply clarsimp
apply (metis in_mono localVVMax )
apply clarsimp
apply (metis in_mono insertE localVVMax prod.inject)
apply clarsimp

apply (erule_tac Inv=Inv and UH="updateHistory (Trace tr (Update r args))" in compareTransitiveI)
apply (erule(9) stepsToHistory_H5)
apply (metis crdtProperties_semilatticeProperties)
apply (metis (hide_lams, no_types) stepsToHistory_H3a)
apply (rule invariantMergeAllHistory)
apply assumption+
apply auto
apply (metis currentStateSubsetHistory image_iff snd_eqD)

apply (rule invariantMergeAllHistory)
apply assumption+
apply auto

(* case, H1 and H2 only from old history *)

apply (metis (hide_lams, no_types) subset_insert useHistoryInvariant)


(* case merge: *)

apply (subst historyInvariant_def)
apply auto

apply (case_tac "H1 \<subseteq> history s")
apply (case_tac "H2 \<subseteq> history s")
(* case H1 and H2 only have old elements *)
apply (metis useHistoryInvariant)

(* case, new element only in H1 *)
apply (frule_tac 
  crdt=crdt 
  and Ha="H1"
  and Hb="H2 - {(sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r)} \<union> {(vv,pl),(replicaVV s r, replicaPayload s r)}"
  in useHistoryInvariant)
apply assumption
apply (force intro: currentStateSubsetHistory)
apply (simp add: supSetExtractSup)
apply (simp add: mergeAllExtractMerge)

apply (case_tac "H2 \<subseteq> history s")
(*case, new element only in H1*)
apply (frule_tac 
  crdt=crdt 
  and Ha="H1 - {(sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r)} \<union> {(vv,pl),(replicaVV s r, replicaPayload s r)}"
  and Hb="H2"
  in useHistoryInvariant)
apply (force intro: currentStateSubsetHistory)
apply assumption
apply (simp add: supSetExtractSup)
apply (simp add: mergeAllExtractMerge)

apply (frule_tac 
  crdt=crdt 
  and Ha="H1 - {(sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r)} \<union> {(vv,pl),(replicaVV s r, replicaPayload s r)}"
  and Hb="H2 - {(sup vv (replicaVV s r), pl \<squnion>[crdt] replicaPayload s r)} \<union> {(vv,pl),(replicaVV s r, replicaPayload s r)}"
  in useHistoryInvariant)
apply (force intro: currentStateSubsetHistory)
apply (force intro: currentStateSubsetHistory)
apply (simp add: supSetExtractSup)
apply (simp add: mergeAllExtractMerge)
done



theorem convergence: "\<lbrakk>
steps crdt tr (initialState crdt) s;
crdtProperties crdt Inv;
(va, pla)\<in>history s;
(vb, plb)\<in>history s;
va \<le> vb
\<rbrakk> \<Longrightarrow> pla \<le>[crdt] plb"
apply (frule(1) stepsToHistory)
apply (frule_tac 
  crdt=crdt 
  and Ha="{(va, pla)}"
  and Hb="{(vb, plb)}"
  in useHistoryInvariant)
apply (auto simp add: mergeAll1b)
done

theorem convergenceEq: "\<lbrakk>
steps crdt tr (initialState crdt) s;
crdtProperties crdt Inv;
(v, pla)\<in>history s;
(v, plb)\<in>history s
\<rbrakk> \<Longrightarrow> pla = plb"
apply (rule_tac crdt=crdt and Inv=Inv and UH="updateHistory tr" in compareAntisymI)
apply (erule(3) convergence)
apply simp
apply (erule(3) convergence)
apply simp
apply (metis crdtProperties_semilatticeProperties)
apply (metis crdtProperties_invariantPreserving invariantPreserving)
apply (metis crdtProperties_invariantPreserving invariantPreserving)
done

definition convergent_crdt :: "('pl,'ua','qa,'r) stateBasedType \<Rightarrow> bool" where
"convergent_crdt crdt = (\<forall>tr s v pl v' pl'. 
  steps crdt tr (initialState crdt) s 
\<and> (v , pl ) \<in> history s 
\<and> (v', pl') \<in> history s 
\<and> v=v' \<longrightarrow> pl=pl')"

definition convergent_crdt2 :: "('pl,'ua','qa,'r) stateBasedType \<Rightarrow> bool" where
"convergent_crdt2 crdt = (\<forall>tr s v pl v' pl'. 
  steps crdt tr (initialState crdt) s 
\<and> (v , pl ) \<in> history s 
\<and> (v', pl') \<in> history s 
\<and> v\<le>v' \<longrightarrow> pl\<le>[crdt]pl')"

lemma convergent_crdt: "crdtProperties crdt Inv \<Longrightarrow> convergent_crdt crdt"
apply (auto simp add: convergent_crdt_def)
by (metis convergenceEq)

lemma convergent_crdt2: "crdtProperties crdt Inv \<Longrightarrow> convergent_crdt2 crdt"
apply (auto simp add: convergent_crdt2_def)
by (metis convergence)


definition mergeIdem where
"mergeIdem crdt Inv = (\<forall>x H. Inv H x \<longrightarrow> x \<squnion>[crdt] x = x)"


lemma mergeIdem3: "\<lbrakk>
mergeIdem crdt Inv;
Inv H x
\<rbrakk> \<Longrightarrow> x \<squnion>[crdt] x = x"
apply (auto simp add: mergeIdem_def)
done

definition compareIsDefault where
"compareIsDefault crdt Inv = (\<forall>x y H. Inv H x \<and> Inv H y \<longrightarrow> (x\<le>[crdt]y) \<longleftrightarrow> (x \<squnion>[crdt] y = y))"

lemma compareToMerge: "
compareIsDefault crdt Inv \<Longrightarrow> 
Inv H x \<Longrightarrow>
Inv H y \<Longrightarrow>
(x\<le>[crdt]y) = (x \<squnion>[crdt] y = y)"
apply (auto simp add: compareIsDefault_def)
done

lemma compareToMerge2: " 
x\<le>[crdt]y \<Longrightarrow> 
compareIsDefault crdt Inv \<Longrightarrow>
Inv H x \<Longrightarrow>
Inv H y \<Longrightarrow>
(x \<squnion>[crdt] y = y)"
apply (auto simp add: compareIsDefault_def)
done



definition mergeAssoc where
"mergeAssoc crdt Inv = (\<forall>H x y z. Inv H x \<and>Inv H y \<and>Inv H z  \<longrightarrow>   
  x \<squnion>[crdt] (y \<squnion>[crdt] z) = (x \<squnion>[crdt] y) \<squnion>[crdt] z)"

lemma mergeAssoc2: "
mergeAssoc crdt Inv \<Longrightarrow>
Inv H x \<Longrightarrow> 
Inv H y \<Longrightarrow> 
Inv H z \<Longrightarrow>
x \<squnion>[crdt] (y \<squnion>[crdt] z) = (x \<squnion>[crdt] y) \<squnion>[crdt] z
"
apply (auto simp add: mergeAssoc_def)
done


lemma semilatticeProperties_defaultOrder: "\<lbrakk>
compareIsDefault crdt Inv;
mergeIdem crdt Inv;
mergeAssoc crdt Inv;
mergeCommute crdt Inv;
invariantPreserving crdt Inv
\<rbrakk> \<Longrightarrow> semilatticeProperties crdt Inv"
apply (auto simp add: semilatticeProperties_def)

apply (auto simp add: compareReflexive_def)
apply (metis compareToMerge mergeIdem3)

apply (auto simp add: compareTransitive_def)
apply (subst compareToMerge[where Inv=Inv])
apply auto
apply (drule(3) compareToMerge2)+
apply (rule_tac t="z" and s="y \<squnion>[crdt] z" in ssubst) 
apply simp
apply (rule_tac t="x \<squnion>[crdt] (y \<squnion>[crdt] z) = y \<squnion>[crdt] z" and s="x \<squnion>[crdt] (y \<squnion>[crdt] z) = (x \<squnion>[crdt] y) \<squnion>[crdt] z" in ssubst)
apply simp
apply (erule(3) mergeAssoc2)

apply (auto simp add: compareAntisym_def)
apply (drule(3) compareToMerge2)+
apply (metis mergeCommute_def)

apply (auto simp add: mergeUpperBound_def)
apply (subst compareToMerge[where Inv=Inv])
apply auto
apply (metis (full_types) mergeAssoc2 mergeIdem_def)

apply (auto simp add: mergeLeastUpperBound_def)
apply (subst compareToMerge[where Inv=Inv])
apply auto
apply (drule(3) compareToMerge2)+
apply (metis (full_types) mergeAssoc2)
done

end


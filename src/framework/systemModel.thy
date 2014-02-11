theory systemModel
imports Main supSet versionvectors
begin


(*
datatype for state based CRDTs 
'pl payload type
'ua update argument type
'qa query argument type
'r return type for queries   
*)
record ('pl, 'ua, 'qa, 'r) stateBasedType = 
      t_compare :: "'pl \<Rightarrow> 'pl \<Rightarrow> bool" (* less-than operation *)
      t_merge   :: "'pl \<Rightarrow> 'pl \<Rightarrow> 'pl" (* merge computes least upper bound*)
      t_initial :: "'pl" (* initial payload *)
      t_update  ::"'ua \<Rightarrow> replicaId \<Rightarrow> 'pl \<Rightarrow> 'pl" (* update operation :: argument => old payload => new payload *)
      t_query   ::"'qa \<Rightarrow> 'pl \<Rightarrow> 'r" (* query operation :: argument => payload => result *)


abbreviation crdtLessThan ("_ \<le>[_]/ _" [51,100,51] 50) where
"x \<le>[crdt] y \<equiv> t_compare crdt x y"


abbreviation crdtSup ("_ \<squnion>[_]/ _" [52,100,52] 51) where
"x \<squnion>[crdt] y \<equiv> t_merge crdt x y"


(* semantics *)


type_synonym 'pl history = "(versionVector \<times> 'pl) set"

record 'pl systemState = 
  replicaPayload :: "replicaId \<Rightarrow> 'pl"
  replicaVV :: "replicaId \<Rightarrow> versionVector"
  history :: "'pl history"


datatype ('ua, 'pl) action = 
   Update replicaId 'ua                        -- "replica, parameter"
 | MergePayload replicaId versionVector 'pl   -- "target, source versionVector, source Payload"

(* A trace is a finite list of actions*)
datatype ('ua, 'pl) trace = 
    EmptyTrace
  | Trace "('ua, 'pl) trace" "('ua, 'pl) action"

fun traceAppend ::"('ua, 'pl) trace \<Rightarrow> ('ua, 'pl) trace \<Rightarrow> ('ua, 'pl) trace" (infixr "@@" 60) where
  "traceAppend tr EmptyTrace = tr"
| "traceAppend tr (Trace tr2 a) = Trace (traceAppend tr tr2) a"


definition initialState :: "('pl,'ua,'qa,'r) stateBasedType \<Rightarrow> ('pl) systemState" where
"initialState crdt = \<lparr> 
  replicaPayload= (\<lambda>r. t_initial crdt), 
  replicaVV=(\<lambda>r. vvZero), 
  history={(vvZero, t_initial crdt)} 
\<rparr>"


fun updateState :: "replicaId \<Rightarrow> (versionVector \<Rightarrow> versionVector) \<Rightarrow> ('pl \<Rightarrow> 'pl) 
                        \<Rightarrow> ('pl) systemState \<Rightarrow> ('pl) systemState" where
"updateState rep updateVV updatePl state = (
  let newPl = updatePl (replicaPayload state rep);
      newVV = updateVV (replicaVV state rep) in
\<lparr>
  replicaPayload = (replicaPayload state)(rep:= newPl),
  replicaVV      = (replicaVV state)(rep:= newVV),
  history        = (history state) \<union> {(newVV, newPl)}
\<rparr>)"

fun doUpdateState :: "replicaId \<Rightarrow> (versionVector \<Rightarrow> versionVector) \<Rightarrow> ('pl \<Rightarrow> 'pl) \<Rightarrow> ('pl) systemState \<Rightarrow> ('pl) systemState" where
"doUpdateState rep newVV newPl state = \<lparr>
                  replicaPayload = (replicaPayload state)(rep:=(newPl (replicaPayload state rep))),
                  replicaVV      = (replicaVV state)(rep:= (newVV (replicaVV state rep))),
                  history        = (history state) \<union> {(newVV (replicaVV state rep), newPl (replicaPayload state rep))}                  
                \<rparr>"

lemma doUpdateState: "updateState = doUpdateState"
apply (rule ext)+
apply (auto simp add: Let_def)
done

inductive step :: "('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> ('ua, 'pl) action \<Rightarrow> ('pl) systemState \<Rightarrow>  ('pl) systemState \<Rightarrow> bool" where
  update: "step crdt (Update r args) s (updateState r (incVV r) (t_update crdt args r) s)"
| merge:  "(vv,pl)\<in>history s  \<Longrightarrow> step crdt (MergePayload r vv pl) s (updateState r (sup vv) (t_merge crdt pl) s)"

inductive steps :: "('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> ('ua, 'pl) trace \<Rightarrow> ('pl) systemState \<Rightarrow>  ('pl) systemState \<Rightarrow> bool" where
  start: "steps crdt EmptyTrace s s"
| step: "\<lbrakk>steps crdt as s1 s2; step crdt a s2 s3 \<rbrakk> \<Longrightarrow> steps crdt (Trace as a) s1 s3"


fun result :: "('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> ('pl) systemState \<Rightarrow> replicaId \<Rightarrow> 'qa \<Rightarrow>'r" where
  "result crdt state r args = (t_query crdt args (replicaPayload state r))"
                           

fun abstractState :: "('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> 'pl \<Rightarrow> 'qa \<Rightarrow> 'r" where
 "abstractState crdt pl args = (t_query crdt args pl)"


-- "induction rule, when starting in initial state"
lemma stepsInitialInduct[induct set: steps]: "\<lbrakk>
steps crdt tr (initialState crdt) s;
P crdt EmptyTrace (initialState crdt);
\<And>tr s r args. P crdt tr s \<Longrightarrow> P crdt (Trace tr (Update r args)) (doUpdateState r (incVV r) (t_update crdt args r) s);
\<And>tr s r vv pl. P crdt tr s \<Longrightarrow> (vv,pl) \<in> history s \<Longrightarrow> P crdt (Trace tr (MergePayload r vv pl)) (doUpdateState r (sup vv) (t_merge crdt pl) s)
\<rbrakk> \<Longrightarrow> P crdt tr s"
apply (induct tr arbitrary: s)
apply (erule steps.cases)
apply clarsimp
apply clarsimp
apply (erule steps.cases)
apply clarsimp
apply (erule step.cases)
apply (auto simp add: doUpdateState)
done

lemma stepsInitialInduct2[induct set: steps]: "\<lbrakk>
steps crdt tr (initialState crdt) s;
P crdt EmptyTrace (initialState crdt);
\<And>tr s r args. steps crdt tr (initialState crdt) s \<Longrightarrow>  P crdt tr s \<Longrightarrow> P crdt (Trace tr (Update r args)) (doUpdateState r (incVV r) (t_update crdt args r) s);
\<And>tr s r vv pl. steps crdt tr (initialState crdt) s \<Longrightarrow> P crdt tr s \<Longrightarrow> (vv,pl) \<in> history s \<Longrightarrow> P crdt (Trace tr (MergePayload r vv pl)) (doUpdateState r (sup vv) (t_merge crdt pl) s)
\<rbrakk> \<Longrightarrow> P crdt tr s"
apply (induct tr arbitrary: s)
apply (erule steps.cases)
apply clarsimp
apply clarsimp
apply (erule steps.cases)
apply clarsimp
apply (erule step.cases)
apply (auto simp add: doUpdateState)
done

lemma stepsInitialInduct3[induct set: steps]: "\<lbrakk>
steps crdt tr (initialState crdt) s;
P crdt EmptyTrace (initialState crdt);
\<And>tr s r args. steps crdt tr (initialState crdt) s \<Longrightarrow> 
  steps crdt (Trace tr (Update r args)) (initialState crdt) (doUpdateState r (incVV r) (t_update crdt args r) s) \<Longrightarrow> 
  P crdt tr s \<Longrightarrow> P crdt (Trace tr (Update r args)) (doUpdateState r (incVV r) (t_update crdt args r) s);
\<And>tr s r vv pl. steps crdt tr (initialState crdt) s \<Longrightarrow> 
  steps crdt (Trace tr (MergePayload r vv pl)) (initialState crdt) (doUpdateState r (sup vv) (t_merge crdt pl) s) \<Longrightarrow>
  P crdt tr s \<Longrightarrow> (vv,pl) \<in> history s \<Longrightarrow> P crdt (Trace tr (MergePayload r vv pl)) (doUpdateState r (sup vv) (t_merge crdt pl) s)
\<rbrakk> \<Longrightarrow> P crdt tr s"
apply (induct tr arbitrary: s)
apply (erule steps.cases)
apply clarsimp
apply clarsimp
apply (erule steps.cases)
apply clarsimp
apply (erule step.cases)
apply (auto simp del: doUpdateState.simps updateState.simps)
apply (unfold doUpdateState[symmetric])
apply (metis steps.step update)
apply (metis steps.step merge)
done



type_synonym 'ua updateHistory = "replicaId \<Rightarrow> (versionVector \<times> 'ua) list"


fun replicaVersion :: "('ua, 'pl) trace \<Rightarrow> replicaId \<Rightarrow> versionVector" where
  "replicaVersion EmptyTrace r = vvZero"
| "replicaVersion (Trace tr (Update r args)) ra = (
      if r=ra then incVV r (replicaVersion tr r) 
      else replicaVersion tr ra)"
| "replicaVersion (Trace tr (MergePayload r vv pl)) ra = (
      if r=ra then sup vv (replicaVersion tr r) 
      else replicaVersion tr ra)"


lemma stepsReplicaVersion: "\<lbrakk>
steps crdt tr (initialState crdt) s
\<rbrakk> \<Longrightarrow> replicaVersion tr r = replicaVV s r"
apply (induct rule: stepsInitialInduct)
apply (simp add: initialState_def)
apply auto
done

definition initialUpdateHistory :: "'ua updateHistory" where 
"initialUpdateHistory = (\<lambda>r. [])"

fun updateHistoryH2 :: "('ua, 'pl) trace \<Rightarrow> 'ua updateHistory" where
  "updateHistoryH2 EmptyTrace = initialUpdateHistory"
| "updateHistoryH2  (Trace tra (Update r args)) = 
      (updateHistoryH2 tra)(r := updateHistoryH2 tra r @ [(replicaVersion (Trace tra (Update r args)) r, args)])"
| "updateHistoryH2 (Trace tra (MergePayload r vv pl)) = updateHistoryH2 tra"


fun updateHistoryH :: "('ua, 'pl) trace \<Rightarrow> 'ua updateHistory" where
"updateHistoryH tr = (case tr of
    EmptyTrace \<Rightarrow> initialUpdateHistory
  | (Trace tra (Update r args)) \<Rightarrow> 
      (updateHistoryH tra)(r := updateHistoryH tra r @ [(replicaVersion tr r, args)])
  | (Trace tra (MergePayload r vv pl)) \<Rightarrow> updateHistoryH tra
)"



definition "updateHistory tr = (updateHistoryH tr)"


lemma updateHistoryEmptyTrace[simp]: "updateHistory EmptyTrace = (\<lambda>r. [])"
apply (auto simp add: updateHistory_def initialUpdateHistory_def)
done

lemma updateHistory_Update: "updateHistory (Trace tr (Update r args)) 
  = ((updateHistory tr)(r := updateHistory tr r @ [(replicaVersion (Trace tr (Update r args)) r, args)]))"
apply (subst updateHistory_def)
apply (subst updateHistoryH.simps)
apply (subst updateHistory_def[symmetric])+
apply auto
done

lemma updateHistory_Merge[simp]: "updateHistory (Trace tr (MergePayload r vv pl)) = updateHistory tr"
apply (subst updateHistory_def)
apply (subst updateHistoryH.simps)
apply (subst updateHistory_def[symmetric])+
apply auto
done


definition updateHistoryFilterInvisible :: "'ua updateHistory \<Rightarrow> versionVector \<Rightarrow> 'ua updateHistory" where
"updateHistoryFilterInvisible H v = (\<lambda>r. filter (\<lambda>(vv,args). vv\<le>v) (H r))"

fun isPrefix where
  "isPrefix [] ys = True"
| "isPrefix (x#xs) [] = False"
| "isPrefix (x#xs) (y#ys) = (x=y \<and> isPrefix xs ys)"

lemma isPrefixTake: "isPrefix xs ys \<longleftrightarrow> (take (length xs) ys = xs)"
apply (induct xs arbitrary: ys)
apply clarsimp
apply (case_tac ys)
apply auto
done

definition visibleUpdateHistory :: "('ua, 'pl) trace \<Rightarrow> versionVector \<Rightarrow> 'ua updateHistory" where
"visibleUpdateHistory tr v = updateHistoryFilterInvisible (updateHistory tr) v"


end


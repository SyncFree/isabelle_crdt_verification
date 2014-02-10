theory specifications
imports systemModel
begin


type_synonym ('ua,'qa,'r) crdtSpecification = "'ua updateHistory \<Rightarrow> 'qa \<Rightarrow> 'r"

definition crdtSpecificationValid :: "('pl, 'ua, 'qa, 'r) stateBasedType \<Rightarrow> ('ua,'qa,'r) crdtSpecification \<Rightarrow> bool" where
"crdtSpecificationValid crdt spec = (\<forall>tr s r qa. 
  steps crdt tr (initialState crdt) s \<longrightarrow> t_query crdt qa (replicaPayload s r) = spec (visibleUpdateHistory tr (replicaVV s r)) qa)"


type_synonym 'a update = "(versionVector \<times> 'a)"

abbreviation updArgs :: "'a update \<Rightarrow> 'a" where
"updArgs upd \<equiv> snd upd"


abbreviation updVersion :: "'a update \<Rightarrow> versionVector" where
"updVersion upd \<equiv> fst upd"


abbreviation happensBefore :: "'a update \<Rightarrow> 'a update \<Rightarrow> bool" (infixr "\<prec>" 50) where
"a \<prec> b \<equiv> (fst a < fst b)"

definition allUpdates :: "'ua updateHistory \<Rightarrow>  ('ua update) set" where
"allUpdates H = (\<Union>r\<in>UNIV. set (H r))"

definition "allVersions H = fst ` allUpdates H"


end

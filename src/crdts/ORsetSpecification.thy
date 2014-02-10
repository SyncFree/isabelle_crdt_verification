theory ORsetSpecification
imports 
"../framework/induction"
"../framework/helper" 
"../framework/convergence" 
begin

datatype 'a updateArgs = Add 'a | Remove 'a
datatype 'a queryArgs = Contains 'a | GetElements
datatype 'a result =  ContainsResult bool | GetElementsResult "'a set"

definition setSpecContains where
"setSpecContains H x = (\<exists>a\<in>allUpdates H. updArgs a = Add x 
            \<and> \<not>(\<exists>r\<in>allUpdates H. a \<prec> r \<and> updArgs r = Remove x))"

fun setSpec :: "('a updateArgs) updateHistory \<Rightarrow> 'a queryArgs \<Rightarrow> 'a result" where
  "setSpec H (Contains x) = ContainsResult(setSpecContains H x)"
| "setSpec H GetElements = GetElementsResult {x. setSpecContains H x}"

end

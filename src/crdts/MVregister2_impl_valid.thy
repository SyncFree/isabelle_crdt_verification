theory MVregister2_impl_valid
imports 
MVregister2_impl
begin

definition mvRegisterInvariant  where
"mvRegisterInvariant H pl = ((\<forall>x c. (Some x, c)\<in>pl 
  \<longleftrightarrow> (\<exists>r l v. x\<in>set l \<and> (v, Assign l)\<in>set(H r)
    \<and> (\<forall>rr. c\<guillemotright>rr = length (filter (\<lambda>e. updArgs e \<noteq> Assign [] \<and> updVersion e \<le> v ) (H rr)))
    \<and> \<not>(\<exists>l' vv. l' \<noteq> [] \<and> vv>v \<and> (vv, Assign l')\<in>allUpdates H)))
  \<and> (\<forall>x. (None,x)\<in>pl \<longleftrightarrow> x=vvZero \<and> H = (\<lambda>r. [])))"

(* no proof *)

end

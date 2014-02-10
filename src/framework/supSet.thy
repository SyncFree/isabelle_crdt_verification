theory supSet 
imports Main
begin



lemma sup_bot_right[simp]: "sup v bot = (v::'a::{semilattice_sup,order_bot})"
by (metis bot_least le_iff_sup sup.commute)

lemma sup_bot_left[simp]:  "sup bot v = (v::'a::{semilattice_sup,order_bot})"
by (metis bot_least le_iff_sup)


(* supSet *)

definition supSet ::"'a set \<Rightarrow> 'a::{semilattice_sup,order_bot}" where
"supSet = Finite_Set.fold sup bot"

lemma supSetEmpty[simp]: "supSet {} = bot"
apply (auto simp add: supSet_def)
done


lemma supSetOne[simp]: "supSet {v} = v"
apply (auto simp add: supSet_def)
apply (metis comp_fun_idem.fold_insert_idem2 comp_fun_idem_sup finite.emptyI fold_empty supSet.sup_bot_right)
done

lemma supSetInsert: "finite S \<Longrightarrow> supSet (insert x S) = sup x (supSet S)"
apply (auto simp add: supSet_def)
apply (metis comp_fun_idem.fold_insert_idem comp_fun_idem_sup)
done

lemma supSetSmaller: "finite S \<Longrightarrow> x\<in>S \<Longrightarrow> x \<le> supSet S"
apply (induct S rule: finite_induct)
apply (auto simp add: supSet_def)
apply (metis sup.cobounded1 supSetInsert supSet_def)
apply (metis sup.coboundedI2 supSetInsert supSet_def)
done


lemma supSetSmaller2: "finite S \<Longrightarrow> y\<in>S \<Longrightarrow> x\<le>y \<Longrightarrow> x \<le> supSet S"
apply (frule(1) supSetSmaller)
by (metis order_trans)

definition smallerElems :: "'a::semilattice_sup \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"smallerElems x S = {y\<in>S. y \<le> x}"

lemma supSetBigger: "finite S \<Longrightarrow> (\<And>x. x\<in>S \<Longrightarrow> x\<le>v) \<Longrightarrow> supSet S \<le> v"
apply (induct S rule: finite_induct)
apply (auto simp add: supSet_def)
apply (metis sup.bounded_iff supSetInsert supSet_def)
done


lemma supSupSet: "finite A \<Longrightarrow> finite B \<Longrightarrow> sup (supSet A) (supSet B) = supSet (A \<union> B)"
apply (induct A rule: finite_induct)
apply auto
apply (auto simp add: supSetInsert)
by (metis sup_commute sup_left_commute)

lemma supForward1: "sup (x::'a::semilattice_sup) y = y \<Longrightarrow> x \<le> y"
by (metis sup_ge1)


lemma supSetSubSet: "finite B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> supSet A \<le> supSet B"
by (metis (full_types) Un_absorb1 rev_finite_subset supForward1 supSupSet)

lemma  "y \<le> z \<Longrightarrow> sup x y \<le> sup (x::'a::semilattice_sup) z"
by (metis order_refl sup_mono)


end



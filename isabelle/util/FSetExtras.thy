theory FSetExtras
  imports "HOL-Library.Finite_Map"
begin

(* Small general-purpose facts about finite sets and finite maps that
   HOL-Library does not provide directly. *)


(* ========================================================================== *)
(* Disjointness (empty intersection)                                          *)
(* ========================================================================== *)

(* Intersecting with a subset of a disjoint set. *)
lemma empty_inter_subset:
  fixes A B C :: "'a fset"
  assumes "A |\<inter>| C = {||}"
      and "B |\<subseteq>| C"
  shows "A |\<inter>| B = {||}"
  using assms by (metis inf_mono le_bot order_refl)

(* Monotone variant: disjointness descends to subsets on both sides. *)
lemma empty_inter_mono:
  fixes A B A' B' :: "'a fset"
  assumes "A |\<subseteq>| A'"
      and "B |\<subseteq>| B'"
      and "A' |\<inter>| B' = {||}"
  shows "A |\<inter>| B = {||}"
  using assms by (metis inf_mono le_bot)

(* Subtracting a set makes the result disjoint from it. *)
lemma fminus_finter_disjoint:
  fixes A B :: "'a fset"
  shows "(A |-| B) |\<inter>| B = {||}"
  by (rule fset_eqI) auto


(* ========================================================================== *)
(* Finite maps                                                                *)
(* ========================================================================== *)

(* Membership in the union of an fset of fsets. *)
lemma fmember_ffUnion_iff:
  "x |\<in>| ffUnion A \<longleftrightarrow> (\<exists>X. X |\<in>| A \<and> x |\<in>| X)"
  by (induction A) auto

(* An fmupd contributes at most one entry's worth to a union over the range. *)
lemma ffUnion_fmran_fmupd_member:
  assumes "x |\<in>| ffUnion (f |`| fmran (fmupd k v m))"
  shows "x |\<in>| f v \<or> x |\<in>| ffUnion (f |`| fmran m)"
proof -
  obtain e where e_ran: "e |\<in>| fmran (fmupd k v m)" and x_in: "x |\<in>| f e"
    using assms unfolding fmember_ffUnion_iff by auto
  obtain k' where lk: "fmlookup (fmupd k v m) k' = Some e"
    using e_ran by (auto simp: fmlookup_ran_iff)
  show ?thesis
  proof (cases "k' = k")
    case True
    then have "e = v" using lk by simp
    then show ?thesis using x_in by simp
  next
    case False
    then have "fmlookup m k' = Some e" using lk by simp
    then have "e |\<in>| fmran m" by (rule fmranI)
    then have "f e |\<in>| f |`| fmran m" by simp
    then have "x |\<in>| ffUnion (f |`| fmran m)"
      unfolding fmember_ffUnion_iff using x_in by blast
    then show ?thesis by simp
  qed
qed

(* Adding a right-biased singleton whose key is fresh is just fmupd. *)
lemma fmadd_singleton_fresh:
  assumes "k |\<notin>| fmdom M"
  shows "fmupd k v fmempty ++\<^sub>f M = fmupd k v M"
proof (rule fmap_ext)
  fix n
  show "fmlookup (fmupd k v fmempty ++\<^sub>f M) n = fmlookup (fmupd k v M) n"
    using assms by (cases "n = k") auto
qed

end

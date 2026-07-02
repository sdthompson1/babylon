theory FmapDisjointUnion
  imports "HOL-Library.Finite_Map" "HOL-Library.Multiset"
begin

(* Generic machinery for the disjoint union of a *list* of finite maps.

   A list of finite maps is "disjoint" when the domains are pairwise disjoint;
   in that case the union is order-independent (each key is defined by exactly
   one element). fmunion_disjoint_all packages the check and the union: it
   returns the union when the domains are pairwise disjoint, or the sorted
   list of multiply-defined keys otherwise.

   This serves linking: merge_all_substs (core/MergeAllSubsts.thy)
   runs it on the modules' abstract-type substitutions, and link_modules runs
   it on each of the declaration/definition maps of a CoreModule. Nothing here
   is specific to substitutions - it is plain finite-map algebra. *)


(* ========================================================================== *)
(* Disjointness of two finite maps                                            *)
(* ========================================================================== *)

(* Two finite maps are disjoint when their domains do not overlap. *)
definition fmdisjoint :: "('k, 'v) fmap \<Rightarrow> ('k, 'v) fmap \<Rightarrow> bool" where
  "fmdisjoint m1 m2 \<equiv> fmdom m1 |\<inter>| fmdom m2 = {||}"

lemma fmdisjoint_sym:
  "fmdisjoint m1 m2 = fmdisjoint m2 m1"
  unfolding fmdisjoint_def by auto

lemma fmdisjoint_empty [simp]:
  "fmdisjoint fmempty m"
  "fmdisjoint m fmempty"
  unfolding fmdisjoint_def by auto

(* A shared domain key contradicts disjointness. *)
lemma fmdisjoint_not_both:
  assumes "fmdisjoint m1 m2"
      and "n |\<in>| fmdom m1"
      and "n |\<in>| fmdom m2"
    shows False
  using assms unfolding fmdisjoint_def by auto

(* When two finite maps are disjoint, ++f is order-immaterial (no overlap),
   so the two biasings agree. *)
lemma fmdisjoint_add_commute:
  assumes "fmdisjoint m1 m2"
  shows "m1 ++\<^sub>f m2 = m2 ++\<^sub>f m1"
proof (rule fmap_ext)
  fix n
  show "fmlookup (m1 ++\<^sub>f m2) n = fmlookup (m2 ++\<^sub>f m1) n"
    using assms fmdisjoint_not_both by fastforce
qed


(* ========================================================================== *)
(* Pairwise disjointness of a list of finite maps                             *)
(* ========================================================================== *)

(* This returns true if a list of finite maps are pairwise disjoint. It is
   efficiently executable; see code equation below. *)
definition fmdisjoint_list :: "('k, 'v) fmap list \<Rightarrow> bool" where
  "fmdisjoint_list ms \<equiv>
     \<forall>i j. i < length ms \<and> j < length ms \<and> i \<noteq> j \<longrightarrow> fmdisjoint (ms ! i) (ms ! j)"

(* The pairwise condition on a cons splits into "s is disjoint from every later
   element" plus "the tail is pairwise disjoint". (We keep the index form for
   the tail because duplicate non-empty elements must register as a conflict.) *)
lemma fmdisjoint_list_Cons:
  "fmdisjoint_list (s # ss) \<longleftrightarrow>
     (\<forall>t \<in> set ss. fmdisjoint s t) \<and> fmdisjoint_list ss"
proof
  assume L: "fmdisjoint_list (s # ss)"
  have head: "\<forall>t \<in> set ss. fmdisjoint s t"
  proof
    fix t assume "t \<in> set ss"
    then obtain j where j: "j < length ss" "ss ! j = t" by (auto simp: in_set_conv_nth)
    have "fmdisjoint ((s # ss) ! 0) ((s # ss) ! Suc j)"
      using L j unfolding fmdisjoint_list_def by fastforce
    thus "fmdisjoint s t" using j by simp
  qed
  moreover have "fmdisjoint_list ss"
    unfolding fmdisjoint_list_def
  proof (intro allI impI)
    fix i j assume "i < length ss \<and> j < length ss \<and> i \<noteq> j"
    then have "fmdisjoint ((s # ss) ! Suc i) ((s # ss) ! Suc j)"
      using L unfolding fmdisjoint_list_def by fastforce
    thus "fmdisjoint (ss ! i) (ss ! j)" by simp
  qed
  ultimately show "(\<forall>t \<in> set ss. fmdisjoint s t) \<and> fmdisjoint_list ss" ..
next
  assume R: "(\<forall>t \<in> set ss. fmdisjoint s t) \<and> fmdisjoint_list ss"
  show "fmdisjoint_list (s # ss)"
    unfolding fmdisjoint_list_def
  proof (intro allI impI)
    fix i j assume ij: "i < length (s # ss) \<and> j < length (s # ss) \<and> i \<noteq> j"
    show "fmdisjoint ((s # ss) ! i) ((s # ss) ! j)"
    proof (cases i; cases j)
      fix j' assume "i = 0" "j = Suc j'"
      then show ?thesis using R ij by (auto simp: fmdisjoint_sym)
    next
      fix i' assume "i = Suc i'" "j = 0"
      then show ?thesis using R ij by (auto simp: fmdisjoint_sym)
    next
      fix i' j' assume "i = Suc i'" "j = Suc j'"
      then show ?thesis using R ij unfolding fmdisjoint_list_def by auto
    next
      assume "i = 0" "j = 0" then show ?thesis using ij by simp
    qed
  qed
qed

(* Pairwise disjointness, recast as counting: the domains are pairwise disjoint
   exactly when each key k lies in the domain of at most one list element
   (counting multiplicity - a repeated non-empty element hits twice). *)
lemma fmdisjoint_list_filter_char:
  "fmdisjoint_list ms \<longleftrightarrow> (\<forall>k. length (filter (\<lambda>s. k |\<in>| fmdom s) ms) \<le> 1)"
proof -
  have fin: "finite {i. i < length ms \<and> k |\<in>| fmdom (ms ! i)}" for k
    by (rule finite_subset[of _ "{..<length ms}"]) auto
  have len_card: "length (filter (\<lambda>s. k |\<in>| fmdom s) ms)
                    = card {i. i < length ms \<and> k |\<in>| fmdom (ms ! i)}" for k
    by (rule length_filter_conv_card)
  show ?thesis
  proof
    assume L: "fmdisjoint_list ms"
    show "\<forall>k. length (filter (\<lambda>s. k |\<in>| fmdom s) ms) \<le> 1"
    proof
      fix k
      have "\<forall>i \<in> {i. i < length ms \<and> k |\<in>| fmdom (ms ! i)}.
            \<forall>j \<in> {i. i < length ms \<and> k |\<in>| fmdom (ms ! i)}. i = j"
      proof (intro ballI)
        fix i j
        assume i_in: "i \<in> {i. i < length ms \<and> k |\<in>| fmdom (ms ! i)}"
           and j_in: "j \<in> {i. i < length ms \<and> k |\<in>| fmdom (ms ! i)}"
        show "i = j"
        proof (rule ccontr)
          assume "i \<noteq> j"
          then have "fmdisjoint (ms ! i) (ms ! j)"
            using L i_in j_in unfolding fmdisjoint_list_def by auto
          then show False
            using fmdisjoint_not_both i_in j_in by auto
        qed
      qed
      then have "card {i. i < length ms \<and> k |\<in>| fmdom (ms ! i)} \<le> Suc 0"
        using fin[of k] by (simp add: card_le_Suc0_iff_eq)
      then show "length (filter (\<lambda>s. k |\<in>| fmdom s) ms) \<le> 1"
        using len_card[of k] by linarith
    qed
  next
    assume R: "\<forall>k. length (filter (\<lambda>s. k |\<in>| fmdom s) ms) \<le> 1"
    show "fmdisjoint_list ms"
      unfolding fmdisjoint_list_def
    proof (intro allI impI)
      fix i j assume ij: "i < length ms \<and> j < length ms \<and> i \<noteq> j"
      show "fmdisjoint (ms ! i) (ms ! j)"
      proof (rule ccontr)
        assume "\<not> fmdisjoint (ms ! i) (ms ! j)"
        then obtain k where k: "k |\<in>| fmdom (ms ! i)" "k |\<in>| fmdom (ms ! j)"
          unfolding fmdisjoint_def by auto
        have sub: "{i, j} \<subseteq> {i'. i' < length ms \<and> k |\<in>| fmdom (ms ! i')}"
          using ij k by auto
        have "card {i, j} \<le> card {i'. i' < length ms \<and> k |\<in>| fmdom (ms ! i')}"
          using card_mono[OF fin[of k] sub] .
        moreover have "card {i, j} = 2" using ij by auto
        moreover have "card {i'. i' < length ms \<and> k |\<in>| fmdom (ms ! i')} \<le> 1"
          using R by (simp add: len_card[symmetric])
        ultimately show False by linarith
      qed
    qed
  qed
qed

(* Pairwise domain-disjointness depends only on the multiset of inputs. *)
lemma fmdisjoint_list_mset_cong:
  assumes "mset ms = mset ms'"
  shows "fmdisjoint_list ms = fmdisjoint_list ms'"
proof -
  have "mset (filter (\<lambda>s. k |\<in>| fmdom s) ms) = mset (filter (\<lambda>s. k |\<in>| fmdom s) ms')" for k
    using assms by simp
  then have "length (filter (\<lambda>s. k |\<in>| fmdom s) ms)
               = length (filter (\<lambda>s. k |\<in>| fmdom s) ms')" for k
    by (metis size_mset)
  then show ?thesis by (simp add: fmdisjoint_list_filter_char)
qed


(* ========================================================================== *)
(* Executable one-pass disjointness check                                     *)
(* ========================================================================== *)

(* Accumulate the domains seen so far into a single set of keys; a conflict is
   a key already seen. Returns Some (accumulated keys) on success, None on
   overlap. As a side effect the success result is exactly the domain of the
   union of all the maps. *)
fun fmdisjoint_acc :: "'k fset \<Rightarrow> ('k, 'v) fmap list \<Rightarrow> 'k fset option" where
  "fmdisjoint_acc acc [] = Some acc"
| "fmdisjoint_acc acc (s # ss) =
     (if fmdom s |\<inter>| acc = {||}
      then fmdisjoint_acc (acc |\<union>| fmdom s) ss
      else None)"

definition fmdisjoint_list_exec :: "('k, 'v) fmap list \<Rightarrow> bool" where
  "fmdisjoint_list_exec ms \<equiv> fmdisjoint_acc {||} ms \<noteq> None"

(* Generalized invariant for the one-pass checker: starting from an accumulator
   set of keys acc, the check succeeds exactly when acc is disjoint from every
   element's domain and the elements are pairwise domain-disjoint. *)
lemma fmdisjoint_acc_None_iff:
  "fmdisjoint_acc acc ss \<noteq> None \<longleftrightarrow>
     (\<forall>s \<in> set ss. fmdom s |\<inter>| acc = {||}) \<and> fmdisjoint_list ss"
proof (induction ss arbitrary: acc)
  case Nil
  show ?case by (simp add: fmdisjoint_list_def)
next
  case (Cons s ss)
  show ?case
  proof (cases "fmdom s |\<inter>| acc = {||}")
    case overlap: True
    have step: "fmdisjoint_acc acc (s # ss) = fmdisjoint_acc (acc |\<union>| fmdom s) ss"
      using overlap by simp
    show ?thesis
    proof
      assume "fmdisjoint_acc acc (s # ss) \<noteq> None"
      then have rec: "fmdisjoint_acc (acc |\<union>| fmdom s) ss \<noteq> None" using step by simp
      from Cons.IH[of "acc |\<union>| fmdom s"] rec
      have accs_rest: "\<forall>t \<in> set ss. fmdom t |\<inter>| (acc |\<union>| fmdom s) = {||}"
        and pair_rest: "fmdisjoint_list ss" by auto
      \<comment> \<open>acc disjoint from every element of s#ss.\<close>
      have acc_all: "\<forall>t \<in> set (s # ss). fmdom t |\<inter>| acc = {||}"
        using accs_rest overlap by auto
      \<comment> \<open>s disjoint from every tail element (the accumulator carried fmdom s).\<close>
      have head: "\<forall>t \<in> set ss. fmdisjoint s t"
        using accs_rest unfolding fmdisjoint_def
        by (metis fmdisjoint_def fmdisjoint_sym inf_sup_distrib1 sup_eq_bot_iff)
      have "fmdisjoint_list (s # ss)"
        using head pair_rest fmdisjoint_list_Cons by blast
      with acc_all show
        "(\<forall>t \<in> set (s # ss). fmdom t |\<inter>| acc = {||}) \<and> fmdisjoint_list (s # ss)" by blast
    next
      assume rhs: "(\<forall>t \<in> set (s # ss). fmdom t |\<inter>| acc = {||}) \<and> fmdisjoint_list (s # ss)"
      have acc_all: "\<forall>t \<in> set (s # ss). fmdom t |\<inter>| acc = {||}" using rhs by blast
      have head: "\<forall>t \<in> set ss. fmdisjoint s t"
        using rhs fmdisjoint_list_Cons by blast
      have pair_rest: "fmdisjoint_list ss"
        using rhs fmdisjoint_list_Cons by blast
      \<comment> \<open>Establish the IH premise for acc |\<union>| fmdom s on the tail.\<close>
      have accs_rest: "\<forall>t \<in> set ss. fmdom t |\<inter>| (acc |\<union>| fmdom s) = {||}"
      proof
        fix t assume t_in: "t \<in> set ss"
        have "fmdom t |\<inter>| acc = {||}" using acc_all t_in by simp
        moreover have "fmdom t |\<inter>| fmdom s = {||}"
          using head t_in unfolding fmdisjoint_def by auto
        ultimately show "fmdom t |\<inter>| (acc |\<union>| fmdom s) = {||}"
          by (simp add: inf_sup_distrib1)
      qed
      from Cons.IH[of "acc |\<union>| fmdom s"] accs_rest pair_rest
      have "fmdisjoint_acc (acc |\<union>| fmdom s) ss \<noteq> None" by blast
      thus "fmdisjoint_acc acc (s # ss) \<noteq> None" using step by simp
    qed
  next
    case False
    \<comment> \<open>Head-check fails: the accumulator already overlaps s's domain.\<close>
    have "fmdisjoint_acc acc (s # ss) = None" using False by auto
    moreover have "\<not> (fmdom s |\<inter>| acc = {||})" using False by simp
    ultimately show ?thesis by auto
  qed
qed

(* fmdisjoint_list is defined by a quantifier over index pairs (not executable).
   The one-pass fmdisjoint_acc computes the same predicate; this is registered
   as its code equation. *)
lemma fmdisjoint_list_code [code]:
  "fmdisjoint_list ms = fmdisjoint_list_exec ms"
  unfolding fmdisjoint_list_exec_def
  using fmdisjoint_acc_None_iff[of "{||}" ms]
  by auto


(* ========================================================================== *)
(* The union of a list of finite maps                                         *)
(* ========================================================================== *)

(* The right-biased union of a list of finite maps.
   Under fmdisjoint_list, this is a disjoint union (so the list order is
   immaterial). Executable as written. *)
definition fmlist_union :: "('k, 'v) fmap list \<Rightarrow> ('k, 'v) fmap" where
  "fmlist_union ms = foldr (++\<^sub>f) ms fmempty"

(* fmlist_union of a cons is the head added onto the union of the tail. *)
lemma fmlist_union_Cons:
  "fmlist_union (s # ss) = s ++\<^sub>f fmlist_union ss"
  unfolding fmlist_union_def by simp

(* Under pairwise disjointness each key is defined by at most one element, so a
   union lookup is exactly "some element defines it" - a property of the *set*
   of elements, with no reference to their order. *)
lemma fmlist_union_lookup:
  assumes "fmdisjoint_list ss"
  shows "fmlookup (fmlist_union ss) k = Some v \<longleftrightarrow> (\<exists>s \<in> set ss. fmlookup s k = Some v)"
  using assms
proof (induction ss arbitrary: v)
  case Nil
  show ?case by (simp add: fmlist_union_def)
next
  case (Cons x xs)
  have head: "\<forall>t \<in> set xs. fmdisjoint x t"
    and tail: "fmdisjoint_list xs"
    using Cons.prems fmdisjoint_list_Cons by blast+
  show ?case
  proof (cases "k |\<in>| fmdom (fmlist_union xs)")
    case True
    \<comment> \<open>k is defined by the tail union, hence by some tail element, hence (by
       disjointness) not by x: the cons lookup is the tail lookup.\<close>
    obtain w where w: "fmlookup (fmlist_union xs) k = Some w"
      using True by (auto simp: fmlookup_dom_iff)
    then obtain s where s: "s \<in> set xs" "fmlookup s k = Some w"
      using Cons.IH[OF tail] by blast
    have k_in_s: "k |\<in>| fmdom s" using s(2) by (auto simp: fmlookup_dom_iff)
    have x_none: "fmlookup x k = None"
    proof (cases "fmlookup x k")
      case None then show ?thesis .
    next
      case (Some a)
      then have "k |\<in>| fmdom x" by (auto simp: fmlookup_dom_iff)
      then have False
        using head s(1) k_in_s fmdisjoint_not_both by metis
      then show ?thesis ..
    qed
    have look: "fmlookup (fmlist_union (x # xs)) k = fmlookup (fmlist_union xs) k"
      using True by (simp add: fmlist_union_Cons)
    show ?thesis
    proof
      assume "fmlookup (fmlist_union (x # xs)) k = Some v"
      then have "fmlookup (fmlist_union xs) k = Some v" using look by simp
      then show "\<exists>s \<in> set (x # xs). fmlookup s k = Some v"
        using Cons.IH[OF tail] by auto
    next
      assume "\<exists>s \<in> set (x # xs). fmlookup s k = Some v"
      then obtain s' where s': "s' \<in> set (x # xs)" "fmlookup s' k = Some v" by blast
      have "s' \<noteq> x" using s'(2) x_none by auto
      then have "s' \<in> set xs" using s'(1) by simp
      then have "fmlookup (fmlist_union xs) k = Some v"
        using s'(2) Cons.IH[OF tail] by blast
      then show "fmlookup (fmlist_union (x # xs)) k = Some v" using look by simp
    qed
  next
    case False
    then have tail_none: "fmlookup (fmlist_union xs) k = None"
      by (simp add: fmdom_notD)
    have look: "fmlookup (fmlist_union (x # xs)) k = fmlookup x k"
      using False by (simp add: fmlist_union_Cons)
    have no_tail: "\<not> (\<exists>s \<in> set xs. fmlookup s k = Some v)"
      using Cons.IH[OF tail] tail_none by (metis option.distinct(1))
    show ?thesis using look no_tail by auto
  qed
qed

(* On disjoint inputs the union is determined by the SET of inputs: two
   mset-equal lists have equal unions. *)
lemma fmlist_union_mset_cong:
  assumes m: "mset ss = mset ss'"
      and disj: "fmdisjoint_list ss"
  shows "fmlist_union ss = fmlist_union ss'"
proof (intro fmap_ext)
  fix k
  have disj': "fmdisjoint_list ss'"
    using fmdisjoint_list_mset_cong[OF m] disj by simp
  have set_eq: "set ss = set ss'"
    using m mset_eq_setD by blast
  show "fmlookup (fmlist_union ss) k = fmlookup (fmlist_union ss') k"
  proof (cases "fmlookup (fmlist_union ss) k")
    case None
    have "fmlookup (fmlist_union ss') k = None"
    proof (cases "fmlookup (fmlist_union ss') k")
      case (Some v)
      then have "\<exists>s \<in> set ss. fmlookup s k = Some v"
        using fmlist_union_lookup[OF disj'] set_eq by blast
      then have "fmlookup (fmlist_union ss) k = Some v"
        using fmlist_union_lookup[OF disj] by blast
      then show ?thesis using None by simp
    qed simp
    then show ?thesis using None by simp
  next
    case (Some v)
    then have "\<exists>s \<in> set ss'. fmlookup s k = Some v"
      using fmlist_union_lookup[OF disj] set_eq by blast
    then have "fmlookup (fmlist_union ss') k = Some v"
      using fmlist_union_lookup[OF disj'] by blast
    then show ?thesis using Some by simp
  qed
qed


(* ========================================================================== *)
(* Multiply-defined keys (the error payload)                                  *)
(* ========================================================================== *)

(* The keys defined by more than one input map. Same one-pass seen-keys shape
   as fmdisjoint_acc, but collecting the repeated keys instead of failing on
   the first one. Purely diagnostic: no theorem depends on its result
   (fmdisjoint_list, via fmdisjoint_acc, is what feeds the disjointness test).
   Executable as written. *)
fun fmdup_keys_acc :: "'k fset \<Rightarrow> ('k, 'v) fmap list \<Rightarrow> 'k fset" where
  "fmdup_keys_acc acc [] = {||}"
| "fmdup_keys_acc acc (s # ss) =
     (fmdom s |\<inter>| acc) |\<union>| fmdup_keys_acc (acc |\<union>| fmdom s) ss"

definition fmdup_keys :: "('k::linorder, 'v) fmap list \<Rightarrow> 'k list" where
  "fmdup_keys ms = sorted_list_of_fset (fmdup_keys_acc {||} ms)"


(* ========================================================================== *)
(* The fused operation: check-and-union                                       *)
(* ========================================================================== *)

(* The n-ary disjoint union of a list of finite maps: Inr of the union if all
   domains are pairwise disjoint, else Inl of the multiply-defined keys.
   Executable via fmdisjoint_list_code, fmlist_union and fmdup_keys. *)
definition fmunion_disjoint_all
    :: "('k::linorder, 'v) fmap list \<Rightarrow> ('k list, ('k, 'v) fmap) sum" where
  "fmunion_disjoint_all ms =
     (if fmdisjoint_list ms then Inr (fmlist_union ms) else Inl (fmdup_keys ms))"

lemma fmunion_disjoint_all_Inr:
  "fmdisjoint_list ms \<Longrightarrow> fmunion_disjoint_all ms = Inr (fmlist_union ms)"
  unfolding fmunion_disjoint_all_def by simp

lemma fmunion_disjoint_all_Inl:
  "\<not> fmdisjoint_list ms \<Longrightarrow> fmunion_disjoint_all ms = Inl (fmdup_keys ms)"
  unfolding fmunion_disjoint_all_def by simp

(* The success characterization: the result is Inr u exactly when the domains
   are pairwise disjoint and u is the union. *)
lemma fmunion_disjoint_all_Inr_iff:
  "fmunion_disjoint_all ms = Inr u \<longleftrightarrow> fmdisjoint_list ms \<and> u = fmlist_union ms"
  unfolding fmunion_disjoint_all_def by auto

(* The failure characterization: some Inl exactly when the domains overlap. *)
lemma fmunion_disjoint_all_Inl_iff:
  "(\<exists>ks. fmunion_disjoint_all ms = Inl ks) \<longleftrightarrow> \<not> fmdisjoint_list ms"
  unfolding fmunion_disjoint_all_def by auto

(* Permutation-invariance: success/failure and the union depend only on the
   multiset of inputs. (Stated over Inr: on failure a different ordering may
   list the duplicate keys differently.) *)
lemma fmunion_disjoint_all_perm:
  assumes m: "mset ms = mset ms'"
  shows "fmunion_disjoint_all ms = Inr u \<longleftrightarrow> fmunion_disjoint_all ms' = Inr u"
proof (cases "fmdisjoint_list ms")
  case True
  then have "fmlist_union ms = fmlist_union ms'"
    using fmlist_union_mset_cong[OF m] by simp
  then show ?thesis
    using True fmdisjoint_list_mset_cong[OF m]
    by (simp add: fmunion_disjoint_all_Inr_iff)
next
  case False
  then show ?thesis
    using fmdisjoint_list_mset_cong[OF m]
    by (simp add: fmunion_disjoint_all_Inr_iff)
qed

end

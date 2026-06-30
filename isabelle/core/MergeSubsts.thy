theory MergeSubsts
  imports MergeSubstsHelpers LinkError
begin

(* The merge_substs operation to merge two type substitutions. *)

(* The problem being solved here is that when linking CoreModules, we need to merge
   their CM_TypeSubsts (abstract type definitions).

   For example, if module 1 defines "type A = B;" and module 2 defines "type B = i32;",
   we need to merge these to get a new type substitution [A := i32, B := i32] in which
   each type is fully resolved.

   Below, we define "merge_substs" which accomplishes this. 

   We use STRICT linking semantics: if the same abstract type T is defined in BOTH
   substitutions, that is a multiple-definition error (LinkConflict), regardless of whether
   the two definitions agree. So a successful merge requires the two domains to be DISJOINT.

   If merge_substs s1 s2 returns Inr \<sigma>, then \<sigma> is the unique idempotent closure of the
   union of s1 and s2 (see `is_subst_closure`, defined in MergeSubstsPrelims.thy).
   Otherwise, either the domains overlap (LinkConflict) or the equation set's dependency
   relation is cyclic (LinkCycle, a user error).

   merge_substs is a non-executable specification only; the "merge_all_substs" function
   (defined elsewhere) provides an executable version.

   We also prove some properties: merge_substs is commutative, associative, and the
   empty subst is an identity (merging with the empty subst has no effect).
*)


(* ========================================================================== *)
(* Definition of merge_substs *)
(* ========================================================================== *)

(* The union of two substitutions is well-defined (order-immaterial) when their
   domains are disjoint. We take the right-biased ++f as the canonical representative. *)
abbreviation subst_union :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> TypeSubst" where
  "subst_union s1 s2 \<equiv> s1 ++\<^sub>f s2"

(* Given a substitution u satisfying acyclic_subst_deps u, there exists a
   unique substitution \<sigma> satisfying is_subst_closure u \<sigma>. *)
(* See also: MergeSubstPrelims.thy for definition of is_subst_closure, and
   MergeSubstHelpers.thy for proofs. *)
lemma subst_closure_exists_unique:
  assumes "acyclic_subst_deps u"
  shows "\<exists>!\<sigma>. is_subst_closure u \<sigma>"
  using assms resolve_subst_is_closure subst_closure_unique by auto

(* merge_substs s1 s2:
   - LinkConflict if s1 and s2 share an abstract type (overlapping domains);
   - LinkCycle if the equation set's dependency relation is cyclic (no unique
     idempotent closure);
   - otherwise the (unique) idempotent closure of the union of the two equation
     sets.
  The use of THE is justified by subst_closure_exists_unique. *)
definition merge_substs :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> (LinkError, TypeSubst) sum" where
  "merge_substs s1 s2 =
     (if \<not> disjoint_subst s1 s2 then Inl LinkConflict
      else if \<not> acyclic_subst_deps (subst_union s1 s2) then Inl LinkCycle
      else Inr (THE \<sigma>. is_subst_closure (subst_union s1 s2) \<sigma>))"

(* merge_substs s1 s2 is Inr \<sigma> exactly when s1,s2 are domain-disjoint, have acyclic
   union, and \<sigma> is the (unique) idempotent closure of their union. *)
lemma merge_substs_eq_Inr_iff:
  "merge_substs s1 s2 = Inr \<sigma> \<longleftrightarrow>
     disjoint_subst s1 s2 \<and> acyclic_subst_deps (subst_union s1 s2)
       \<and> is_subst_closure (subst_union s1 s2) \<sigma>"
proof
  assume "merge_substs s1 s2 = Inr \<sigma>"
  then have disj: "disjoint_subst s1 s2"
        and acyc: "acyclic_subst_deps (subst_union s1 s2)"
        and the_eq: "(THE \<sigma>'. is_subst_closure (subst_union s1 s2) \<sigma>') = \<sigma>"
    unfolding merge_substs_def by (auto split: if_splits)
  have "is_subst_closure (subst_union s1 s2) \<sigma>"
    by (metis acyc local.the_eq subst_closure_exists_unique the_equality)
  thus "disjoint_subst s1 s2
      \<and> acyclic_subst_deps (subst_union s1 s2)
      \<and> is_subst_closure (subst_union s1 s2) \<sigma>" using acyc disj by simp
next
  assume "disjoint_subst s1 s2 \<and> acyclic_subst_deps (subst_union s1 s2)
            \<and> is_subst_closure (subst_union s1 s2) \<sigma>"
  thus "merge_substs s1 s2 = Inr \<sigma>"
    using merge_substs_def subst_closure_exists_unique the_equality
    by metis
qed


(* ========================================================================== *)
(* Algebraic laws                                                             *)
(* ========================================================================== *)

(* merge_substs is commutative *)
lemma merge_substs_commute:
  "merge_substs s1 s2 = merge_substs s2 s1"
proof (cases "disjoint_subst s1 s2")
  case False
  then have "\<not> disjoint_subst s2 s1" by (simp add: disjoint_subst_sym)
  with False show ?thesis unfolding merge_substs_def by simp
next
  case True
  then have disj2: "disjoint_subst s2 s1" by (simp add: disjoint_subst_sym)
  have union_eq: "subst_union s1 s2 = subst_union s2 s1"
    using disjoint_subst_add_commute[OF True] .
  show ?thesis
    unfolding merge_substs_def
    using True disj2 union_eq by simp
qed

(* fmempty is an identity: merging with the empty substitution returns the
   other one (when it is idempotent). *)
lemma merge_substs_empty_left:
  assumes "idempotent_subst s"
  shows "merge_substs fmempty s = Inr s"
proof -
  have "is_subst_closure (subst_union fmempty s) s"
    using is_subst_closure_self[OF assms] by simp
  moreover have "acyclic_subst_deps (subst_union fmempty s)"
    using idempotent_subst_acyclic[OF assms] by simp
  ultimately show ?thesis
    by (simp add: merge_substs_eq_Inr_iff)
qed

lemma merge_substs_empty_right:
  assumes "idempotent_subst s"
  shows "merge_substs s fmempty = Inr s"
  using merge_substs_empty_left[OF assms] merge_substs_commute by simp


(* -------------------------------------------------------------------------- *)
(* Associativity: helpers *)
(* -------------------------------------------------------------------------- *)

(* The symmetric condition under which a grouping of merge_substs over s1, s2, s3
   reaches a final result: the three domains are pairwise disjoint and the combined
   raw union is acyclic. Manifestly invariant under reordering, which is what makes
   the two groupings agree on reachability. *)
definition merge_reachable :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> bool" where
  "merge_reachable s1 s2 s3 \<equiv>
       disjoint_subst s1 s2 \<and> disjoint_subst s1 s3 \<and> disjoint_subst s2 s3
     \<and> acyclic_subst_deps (s1 ++\<^sub>f s2 ++\<^sub>f s3)"

(* merge_reachable is symmetric in all the ways we need: it is invariant under any
   permutation of the three substitutions (disjointness is symmetric and ++f on
   pairwise-disjoint maps is order-immaterial). We only need the two reorderings that
   relate the left and right groupings. *)
lemma merge_reachable_rotate:
  "merge_reachable s1 s2 s3 = merge_reachable s2 s3 s1"
proof (cases "disjoint_subst s1 s2 \<and> disjoint_subst s1 s3 \<and> disjoint_subst s2 s3")
  case True
  \<comment> \<open>With pairwise-disjoint domains every key lies in at most one map, so the combined
      union is independent of order; both sides then have identical disjointness and
      acyclicity. \<close>
  have union_eq: "s1 ++\<^sub>f s2 ++\<^sub>f s3 = s2 ++\<^sub>f s3 ++\<^sub>f s1"
  proof (intro fmap_ext)
    fix n
    from True show "fmlookup (s1 ++\<^sub>f s2 ++\<^sub>f s3) n = fmlookup (s2 ++\<^sub>f s3 ++\<^sub>f s1) n"
      unfolding disjoint_subst_def
      by (metis True disjoint_subst_add_commute fmadd_assoc)
  qed
  show ?thesis
    unfolding merge_reachable_def
    using True union_eq by (metis disjoint_subst_sym)
next
  case False
  \<comment> \<open>Some pair overlaps; both groupings are unreachable. \<close>
  then show ?thesis
    unfolding merge_reachable_def by (metis disjoint_subst_sym)
qed

(* The left grouping (merge s1 s2, then merge the result with s3) reaches a final
   result exactly when merge_reachable holds. *)
lemma merge_substs_left_reachable_iff:
  "(\<exists>a r. merge_substs s1 s2 = Inr a \<and> merge_substs a s3 = Inr r)
   \<longleftrightarrow> merge_reachable s1 s2 s3"
proof
  assume "\<exists>a r. merge_substs s1 s2 = Inr a \<and> merge_substs a s3 = Inr r"
  then obtain a r where ab: "merge_substs s1 s2 = Inr a"
    and ar: "merge_substs a s3 = Inr r" by blast
  have disj12: "disjoint_subst s1 s2"
   and acyc12: "acyclic_subst_deps (s1 ++\<^sub>f s2)"
   and cl_a:   "is_subst_closure (s1 ++\<^sub>f s2) a"
    using ab merge_substs_eq_Inr_iff by auto
  have disj_a3: "disjoint_subst a s3"
   and acyc_a3: "acyclic_subst_deps (a ++\<^sub>f s3)"
    using ar merge_substs_eq_Inr_iff by auto
  have dom_a: "fmdom a = fmdom (s1 ++\<^sub>f s2)"
    using cl_a unfolding is_subst_closure_def by simp
  \<comment> \<open>Pairwise disjointness: dom a = dom s1 \<union> dom s2, disjoint from dom s3. \<close>
  have disj13: "disjoint_subst s1 s3" and disj23: "disjoint_subst s2 s3"
    using disj_a3 dom_a unfolding disjoint_subst_def by auto
  have disj12_3: "fmdom (s1 ++\<^sub>f s2) |\<inter>| fmdom s3 = {||}"
    using disj_a3 dom_a unfolding disjoint_subst_def by simp
  have "acyclic_subst_deps ((s1 ++\<^sub>f s2) ++\<^sub>f s3)"
    using acyclic_subst_deps_transfer[OF acyc12 disj12_3 cl_a acyc_a3] .
  then show "merge_reachable s1 s2 s3"
    unfolding merge_reachable_def using disj12 disj13 disj23 by simp
next
  assume reach: "merge_reachable s1 s2 s3"
  then have disj12: "disjoint_subst s1 s2" and disj13: "disjoint_subst s1 s3"
    and disj23: "disjoint_subst s2 s3"
    and acyc123: "acyclic_subst_deps ((s1 ++\<^sub>f s2) ++\<^sub>f s3)"
    unfolding merge_reachable_def by auto
  \<comment> \<open>dom(s1 ++f s2) is disjoint from dom s3. \<close>
  have disj12_3: "fmdom (s1 ++\<^sub>f s2) |\<inter>| fmdom s3 = {||}"
    using disj13 disj23 unfolding disjoint_subst_def by auto
  \<comment> \<open>merge_substs s1 s2 succeeds: disjoint, and acyclic (sub-union of the acyclic whole). \<close>
  have acyc12: "acyclic_subst_deps (s1 ++\<^sub>f s2)"
    using acyclic_subst_deps_left[OF disj12_3 acyc123] .
  obtain a where cl_a: "is_subst_closure (s1 ++\<^sub>f s2) a"
    using acyc12 subst_closure_exists_unique by blast
  have ab: "merge_substs s1 s2 = Inr a"
    using disj12 acyc12 cl_a merge_substs_eq_Inr_iff by simp
  \<comment> \<open>merge_substs a s3 succeeds: dom a = dom(s1 ++f s2) disjoint from s3, and a ++f s3
      acyclic by the converse transfer. \<close>
  have dom_a: "fmdom a = fmdom (s1 ++\<^sub>f s2)"
    using cl_a unfolding is_subst_closure_def by simp
  have disj_a3: "disjoint_subst a s3"
    using disj12_3 dom_a unfolding disjoint_subst_def by simp
  have acyc_a3: "acyclic_subst_deps (a ++\<^sub>f s3)"
    using acyclic_subst_deps_transfer_converse[OF disj12_3 cl_a acyc123] .
  obtain r where cl_r: "is_subst_closure (a ++\<^sub>f s3) r"
    using acyc_a3 subst_closure_exists_unique by blast
  have "merge_substs a s3 = Inr r"
    using disj_a3 acyc_a3 cl_r merge_substs_eq_Inr_iff by simp
  with ab show "\<exists>a r. merge_substs s1 s2 = Inr a \<and> merge_substs a s3 = Inr r" by blast
qed


(* -------------------------------------------------------------------------- *)
(* Associativity: main results *)
(* -------------------------------------------------------------------------- *)

(* Associativity in the success case *)
lemma merge_substs_assoc:
  assumes ab:    "merge_substs s1 s2 = Inr a"
      and bc:    "merge_substs s2 s3 = Inr b"
      and r:     "merge_substs a s3 = Inr r"
      and r':    "merge_substs s1 b = Inr r'"
  shows "r = r'"
proof -
  \<comment> \<open>Unpack the merges we need. \<close>
  have acyc12: "acyclic_subst_deps (s1 ++\<^sub>f s2)"
   and cl_a:   "is_subst_closure (s1 ++\<^sub>f s2) a"
    using ab merge_substs_eq_Inr_iff by auto
  have disj_a3: "disjoint_subst a s3"
   and acyc_a3: "acyclic_subst_deps (a ++\<^sub>f s3)"
   and cl_r:    "is_subst_closure (a ++\<^sub>f s3) r"
    using r merge_substs_eq_Inr_iff by auto
  have acyc23: "acyclic_subst_deps (s2 ++\<^sub>f s3)"
   and cl_b:   "is_subst_closure (s2 ++\<^sub>f s3) b"
    using bc merge_substs_eq_Inr_iff by auto
  have cl_r':   "is_subst_closure (s1 ++\<^sub>f b) r'"
    using r' merge_substs_eq_Inr_iff by auto

  \<comment> \<open>a has the same domain as the raw union s1 ++f s2 (it is its closure), so the
      disjointness of a and s3 is exactly disjointness of (s1 ++f s2) and s3. \<close>
  have dom_a: "fmdom a = fmdom (s1 ++\<^sub>f s2)"
    using cl_a unfolding is_subst_closure_def by simp
  have disj12_3: "fmdom (s1 ++\<^sub>f s2) |\<inter>| fmdom s3 = {||}"
    using disj_a3 dom_a unfolding disjoint_subst_def by simp

  \<comment> \<open>The combined raw union is acyclic, recovered from the acyclic a ++f s3. \<close>
  have acyc: "acyclic_subst_deps ((s1 ++\<^sub>f s2) ++\<^sub>f s3)"
    using acyclic_subst_deps_transfer[OF acyc12 disj12_3 cl_a acyc_a3] .

  \<comment> \<open>Left side: absorb a back into s1 ++f s2 (a on the left of a ++f s3). \<close>
  have r_closes: "is_subst_closure ((s1 ++\<^sub>f s2) ++\<^sub>f s3) r"
    using is_subst_closure_absorb[OF acyc12 disj12_3 cl_a cl_r] .

  \<comment> \<open>Right side: absorb b back into s2 ++f s3 (b on the right of s1 ++f b). No
      consistency or commuting needed. \<close>
  have r'_closes: "is_subst_closure (s1 ++\<^sub>f (s2 ++\<^sub>f s3)) r'"
    using is_subst_closure_absorb_right[OF acyc23 cl_b cl_r'] .

  \<comment> \<open>Both r and r' close the same acyclic raw union; conclude by uniqueness. \<close>
  have "is_subst_closure ((s1 ++\<^sub>f s2) ++\<^sub>f s3) r'"
    using r'_closes by simp
  with subst_closure_unique[OF acyc r_closes] show "r = r'" by blast
qed

(* Associativity in the failure case: the left grouping reaches a final result iff
   the right grouping does. Together with merge_substs_assoc (equal results when both
   reach one), this is full associativity up to the choice of error: both groupings
   succeed with the same substitution, or both fail (possibly with different
   LinkErrors). *)
theorem merge_substs_assoc_fails:
  "(\<exists>a r. merge_substs s1 s2 = Inr a \<and> merge_substs a s3 = Inr r)
   \<longleftrightarrow>
   (\<exists>b r. merge_substs s2 s3 = Inr b \<and> merge_substs s1 b = Inr r)"
proof -
  \<comment> \<open>Both sides characterized by merge_reachable, related by a rotation. \<close>
  have L: "(\<exists>a r. merge_substs s1 s2 = Inr a \<and> merge_substs a s3 = Inr r)
            = merge_reachable s1 s2 s3"
    by (rule merge_substs_left_reachable_iff)
  \<comment> \<open>The outer merge in the right grouping has its inner result on the right; commute
      it to the left so the same left-characterization applies. \<close>
  have comm: "\<And>b. merge_substs s1 b = merge_substs b s1" using merge_substs_commute by simp
  have R: "(\<exists>b r. merge_substs s2 s3 = Inr b \<and> merge_substs s1 b = Inr r)
            = merge_reachable s2 s3 s1"
    using merge_substs_left_reachable_iff[of s2 s3 s1] comm by simp
  show ?thesis using L R merge_reachable_rotate by blast
qed

end

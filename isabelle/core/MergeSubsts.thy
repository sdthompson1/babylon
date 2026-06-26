theory MergeSubsts
  imports MergeSubstsHelpers LinkError
begin

(* The merge_substs operation to merge two type substitutions. *)

(* The problem being solved here is that when linking CoreModules, we need to merge 
   their CM_TypeSubsts (abstract type definitions).

   For example, if module 1 defines "type A = B;" and module 2 defines "type B = i32;",
   we need to merge these to get a new type substitution [A := i32, B := i32] in which
   each type is fully resolved.

   Below, we define "merge_substs" which accomplishes this. If merge_substs s1 s2
   returns Inr \<sigma>, then \<sigma> is the unique idempotent closure of the union of s1 and s2 (see
   is_subst_closure, defined in MergeSubstPrelims.thy). Otherwise, either s1 and s2 are
   inconsistent (map the same abstract type T to different concrete realizations - which
   can't happen if the input modules were built from the same source program), or there
   is a dependency cycle (which is a user error).

   merge_substs is a non-executable specification only; the "merge_all_substs" function
   (defined elsewhere) provides an executable version.

   We also prove some properties, e.g. merge_substs is associative, commutative,
   idempotent (merging a subst with itself returns the same subst), and the
   empty subst is an identity (merging with the empty subst has no effect).
*)


(* ========================================================================== *)
(* Definition of merge_substs *)
(* ========================================================================== *)

(* The union of two substitutions is well-defined (order-immaterial) when they
   are consistent. We take the right-biased ++f as the canonical representative. *)
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
   - LinkConflict if s1 and s2 disagree on a shared abstract type;
   - LinkCycle if the equation set's dependency relation is cyclic (no unique
     idempotent closure);
   - otherwise the (unique) idempotent closure of the union of the two equation
     sets.
  The use of THE is justified by subst_closure_exists_unique. *)
definition merge_substs :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> (LinkError, TypeSubst) sum" where
  "merge_substs s1 s2 =
     (if \<not> consistent_subst s1 s2 then Inl LinkConflict
      else if \<not> acyclic_subst_deps (subst_union s1 s2) then Inl LinkCycle
      else Inr (THE \<sigma>. is_subst_closure (subst_union s1 s2) \<sigma>))"

(* merge_substs s1 s2 is Inr \<sigma> exactly when s1,s2 are consistent, have acyclic union,
   and \<sigma> is the (unique) idempotent closure of their union. *)
lemma merge_substs_eq_Inr_iff:
  "merge_substs s1 s2 = Inr \<sigma> \<longleftrightarrow>
     consistent_subst s1 s2 \<and> acyclic_subst_deps (subst_union s1 s2)
       \<and> is_subst_closure (subst_union s1 s2) \<sigma>"
proof
  assume "merge_substs s1 s2 = Inr \<sigma>"
  then have cons: "consistent_subst s1 s2"
        and acyc: "acyclic_subst_deps (subst_union s1 s2)"
        and the_eq: "(THE \<sigma>'. is_subst_closure (subst_union s1 s2) \<sigma>') = \<sigma>"
    unfolding merge_substs_def by (auto split: if_splits)
  have "is_subst_closure (subst_union s1 s2) \<sigma>"
    by (metis acyc local.the_eq subst_closure_exists_unique the_equality)
  thus "consistent_subst s1 s2
      \<and> acyclic_subst_deps (subst_union s1 s2)
      \<and> is_subst_closure (subst_union s1 s2) \<sigma>" using acyc cons by simp
next
  assume "consistent_subst s1 s2 \<and> acyclic_subst_deps (subst_union s1 s2)
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
proof (cases "consistent_subst s1 s2")
  case False
  then have "\<not> consistent_subst s2 s1" by (simp add: consistent_subst_sym)
  with False show ?thesis unfolding merge_substs_def by simp
next
  case True
  then have cons2: "consistent_subst s2 s1" by (simp add: consistent_subst_sym)
  have union_eq: "subst_union s1 s2 = subst_union s2 s1"
    using consistent_subst_add_commute[OF True] .
  show ?thesis
    unfolding merge_substs_def
    using True cons2 union_eq by simp
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

(* Idempotence: merging an idempotent substitution with itself returns it. *)
lemma merge_substs_idem:
  assumes "idempotent_subst s"
  shows "merge_substs s s = Inr s"
proof -
  have "is_subst_closure (subst_union s s) s"
    using is_subst_closure_self[OF assms] by simp
  moreover have "acyclic_subst_deps (subst_union s s)"
    using idempotent_subst_acyclic[OF assms] by simp
  moreover have "consistent_subst s s"
    unfolding consistent_subst_def by simp
  ultimately show ?thesis
    using merge_substs_eq_Inr_iff by simp
qed

(* merge_substs is associative (when linking succeeds). *)
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
  have cons_a3: "consistent_subst a s3"
   and acyc_a3: "acyclic_subst_deps (a ++\<^sub>f s3)"
   and cl_r:    "is_subst_closure (a ++\<^sub>f s3) r"
    using r merge_substs_eq_Inr_iff by auto
  have acyc23: "acyclic_subst_deps (s2 ++\<^sub>f s3)"
   and cl_b:   "is_subst_closure (s2 ++\<^sub>f s3) b"
    using bc merge_substs_eq_Inr_iff by auto
  have cl_r':   "is_subst_closure (s1 ++\<^sub>f b) r'"
    using r' merge_substs_eq_Inr_iff by auto

  \<comment> \<open>The combined raw union is acyclic, recovered from the acyclic a ++f s3. \<close>
  have acyc: "acyclic_subst_deps ((s1 ++\<^sub>f s2) ++\<^sub>f s3)"
    using acyclic_subst_deps_transfer[OF acyc12 cons_a3 cl_a acyc_a3] .

  \<comment> \<open>Left side: absorb a back into s1 ++f s2 (a on the left of a ++f s3). \<close>
  have r_closes: "is_subst_closure ((s1 ++\<^sub>f s2) ++\<^sub>f s3) r"
    using is_subst_closure_absorb[OF acyc12 cons_a3 cl_a cl_r] .

  \<comment> \<open>Right side: absorb b back into s2 ++f s3 (b on the right of s1 ++f b). No
      consistency or commuting needed. \<close>
  have r'_closes: "is_subst_closure (s1 ++\<^sub>f (s2 ++\<^sub>f s3)) r'"
    using is_subst_closure_absorb_right[OF acyc23 cl_b cl_r'] .

  \<comment> \<open>Both r and r' close the same acyclic raw union; conclude by uniqueness. \<close>
  have "is_subst_closure ((s1 ++\<^sub>f s2) ++\<^sub>f s3) r'"
    using r'_closes by simp
  with subst_closure_unique[OF acyc r_closes] show "r = r'" by blast
qed

end

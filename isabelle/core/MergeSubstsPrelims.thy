theory MergeSubstsPrelims
  imports TypeSubst
begin

(* Preliminary definitions and lemmas for merge_substs. *)

(* ========================================================================== *)
(* The dependency relation on a substitution, and its acyclicity              *)
(* ========================================================================== *)

(* The abstract-type dependency relation of a substitution u: the pair (T', T)
   is an edge when T and T' are both domain variables and T' occurs in the
   realization of T (so "T depends on T'"). The orientation - (T', T) for the
   edge "T depends on T'" - makes wf recurse from a dependent to its dependency,
   matching the resolution order. *)
definition subst_dep_rel :: "TypeSubst \<Rightarrow> (string \<times> string) set" where
  "subst_dep_rel u =
     {(T', T) | T T'. T |\<in>| fmdom u \<and> T' |\<in>| fmdom u
                    \<and> T' \<in> type_tyvars (the (fmlookup u T))}"

(* Acyclicity of the dependency relation: the spec-facing condition (clause (2)
   of merge_substs's success characterization). *)
definition acyclic_subst_deps :: "TypeSubst \<Rightarrow> bool" where
  "acyclic_subst_deps u \<equiv> acyclic (subst_dep_rel u)"

(* The dependency relation is contained in the (finite) domain square. *)
lemma subst_dep_rel_subset:
  "subst_dep_rel u \<subseteq> fset (fmdom u) \<times> fset (fmdom u)"
  unfolding subst_dep_rel_def by auto

lemma finite_subst_dep_rel:
  "finite (subst_dep_rel u)"
  by (rule finite_subset[OF subst_dep_rel_subset]) simp

(* Bridge to well-foundedness: on the finite domain carrier, acyclicity is
   well-foundedness (HOL's finite_acyclic_wf). This is the only fact about the
   relation that the existence and uniqueness proofs consume. *)
lemma acyclic_subst_deps_wf:
  assumes "acyclic_subst_deps u"
  shows "wf (subst_dep_rel u)"
  using assms finite_subst_dep_rel finite_acyclic_wf
  unfolding acyclic_subst_deps_def by blast


(* ========================================================================== *)
(* An idempotent substitution satisfies acyclic_subst_deps *)
(* ========================================================================== *)

(* Helper: An idempotent substitution has an empty dependency relation: no domain
   variable occurs in any range value, so there are no edges. *)
lemma idempotent_subst_dep_rel_empty:
  assumes "idempotent_subst s"
  shows "subst_dep_rel s = {}"
proof -
  have "\<And>T T'. T |\<in>| fmdom s \<Longrightarrow> T' |\<in>| fmdom s \<Longrightarrow>
               T' \<notin> type_tyvars (the (fmlookup s T))"
  proof -
    fix T T' assume T_dom: "T |\<in>| fmdom s" and T'_dom: "T' |\<in>| fmdom s"
    obtain ty where ty: "fmlookup s T = Some ty" using T_dom by (auto simp: fmlookup_dom_iff)
    then have "ty \<in> fmran' s" by (auto simp: fmran'_def)
    then have "type_tyvars ty \<subseteq> subst_range_tyvars s"
      unfolding subst_range_tyvars_def by auto
    with assms have "type_tyvars ty \<inter> fset (fmdom s) = {}"
      unfolding idempotent_subst_def by auto
    with T'_dom ty show "T' \<notin> type_tyvars (the (fmlookup s T))" by auto
  qed
  thus ?thesis unfolding subst_dep_rel_def by auto
qed

(* It follows that an idempotent subst satisfies acyclic_subst_deps
   (an empty relation is trivially acyclic) *)
lemma idempotent_subst_acyclic:
  assumes "idempotent_subst s"
  shows "acyclic_subst_deps s"
  unfolding acyclic_subst_deps_def
  using idempotent_subst_dep_rel_empty[OF assms]
  by (simp add: wf_acyclic)


(* ========================================================================== *)
(* Definition: The idempotent closure of a substitution *)
(* ========================================================================== *)

(* is_subst_closure u \<sigma>: \<sigma> is the idempotent closure of the equation set u.
   That is, \<sigma> is idempotent (domain/range-disjoint), has the same domain as u,
   and resolves each of u's equations fully (\<sigma>(T) equals u(T) with \<sigma> applied to
   its right-hand side). This is the unique fixed point that merging targets. *)
definition is_subst_closure :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> bool" where
  "is_subst_closure u \<sigma> \<equiv>
       idempotent_subst \<sigma>
     \<and> fmdom \<sigma> = fmdom u
     \<and> (\<forall>T ty. fmlookup u T = Some ty \<longrightarrow> fmlookup \<sigma> T = Some (apply_subst \<sigma> ty))"


(* ========================================================================== *)
(* An idempotent substitution is its own idempotent closure *)
(* ========================================================================== *)

lemma is_subst_closure_self:
  assumes "idempotent_subst s"
  shows "is_subst_closure s s"
  unfolding is_subst_closure_def
  using assms idempotent_subst_fixes_range[OF assms] by auto


(* ========================================================================== *)
(* Disjoint substitutions *)
(* ========================================================================== *)

(* Two substitutions are disjoint when their domains do not overlap. *)
definition disjoint_subst :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> bool" where
  "disjoint_subst s1 s2 \<equiv> fmdom s1 |\<inter>| fmdom s2 = {||}"

lemma disjoint_subst_sym:
  "disjoint_subst s1 s2 = disjoint_subst s2 s1"
  unfolding disjoint_subst_def by auto

lemma disjoint_subst_empty [simp]:
  "disjoint_subst fmempty s"
  "disjoint_subst s fmempty"
  unfolding disjoint_subst_def by auto

(* A shared domain variable contradicts disjointness. *)
lemma disjoint_subst_not_both:
  assumes "disjoint_subst s1 s2"
      and "n |\<in>| fmdom s1"
      and "n |\<in>| fmdom s2"
    shows False
  using assms unfolding disjoint_subst_def by auto

(* When two substitutions are disjoint, ++f is order-immaterial (no overlap),
   so the two biasings agree. *)
lemma disjoint_subst_add_commute:
  assumes "disjoint_subst s1 s2"
  shows "s1 ++\<^sub>f s2 = s2 ++\<^sub>f s1"
proof (rule fmap_ext)
  fix n
  show "fmlookup (s1 ++\<^sub>f s2) n = fmlookup (s2 ++\<^sub>f s1) n"
    using assms disjoint_subst_not_both by fastforce
qed

end

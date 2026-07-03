theory MergeSubstsPrelims
  imports TypeSubst
begin

(* Preliminary definitions and lemmas for merge_all_substs (MergeAllSubsts.thy). *)


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
   of merge_all_substs's success characterization). *)
definition acyclic_subst_deps :: "TypeSubst \<Rightarrow> bool" where
  "acyclic_subst_deps u \<equiv> acyclic (subst_dep_rel u)"

(* The dependency relation is contained in the (finite) domain square. *)
lemma subst_dep_rel_subset:
  "subst_dep_rel u \<subseteq> fset (fmdom u) \<times> fset (fmdom u)"
  unfolding subst_dep_rel_def by auto

(* The dependency relation is finite *)
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
(* An idempotent substitution satisfies acyclic_subst_deps                    *)
(* ========================================================================== *)

(* An idempotent substitution has an empty dependency relation: no domain
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

(* Hence, an idempotent subst satisfies acyclic_subst_deps
   (an empty relation is trivially acyclic). *)
lemma idempotent_subst_acyclic:
  assumes "idempotent_subst s"
  shows "acyclic_subst_deps s"
  unfolding acyclic_subst_deps_def
  using idempotent_subst_dep_rel_empty[OF assms]
  by (simp add: wf_acyclic)


(* ========================================================================== *)
(* The idempotent closure of a substitution *)
(* ========================================================================== *)

(* is_subst_closure u \<sigma>: \<sigma> is the idempotent closure of the equation set u.
   That is, \<sigma> is idempotent (domain/range-disjoint), has the same domain as u,
   and resolves each of u's equations fully (\<sigma>(T) equals u(T) with \<sigma> applied to
   its right-hand side). *)
(* See also SubstClosureExistsUnique.thy for conditions for \<sigma> to exist and be unique. *)
definition is_subst_closure :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> bool" where
  "is_subst_closure u \<sigma> \<equiv>
       idempotent_subst \<sigma>
     \<and> fmdom \<sigma> = fmdom u
     \<and> (\<forall>T ty. fmlookup u T = Some ty \<longrightarrow> fmlookup \<sigma> T = Some (apply_subst \<sigma> ty))"

(* An idempotent substitution is its own idempotent closure. *)
lemma is_subst_closure_self:
  assumes "idempotent_subst s"
  shows "is_subst_closure s s"
  unfolding is_subst_closure_def
  using assms idempotent_subst_fixes_range[OF assms] by auto

(* The range of a closure only mentions LEFTOVER names: type variables that
   occur in u's range but are not resolved by u itself. In particular the
   closure introduces no name that the raw equations could not introduce -
   which is what lets a capture-avoidance check on the raw inputs of a link
   transfer to the merged (closed) substitution. Proved by well-founded
   induction on u's dependency relation, in the style of
   closure_absorb_var_raw (SubstAbsorption.thy). *)
lemma is_subst_closure_range_tyvars:
  assumes acyc: "acyclic_subst_deps u"
      and cl: "is_subst_closure u \<sigma>"
  shows "subst_range_tyvars \<sigma> \<subseteq> subst_range_tyvars u - fset (fmdom u)"
proof -
  have wf: "wf (subst_dep_rel u)" using acyc by (rule acyclic_subst_deps_wf)
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl unfolding is_subst_closure_def by simp
  have main: "\<forall>ty. fmlookup \<sigma> T = Some ty \<longrightarrow>
                type_tyvars ty \<subseteq> subst_range_tyvars u - fset (fmdom u)" for T
  proof (induction T rule: wf_induct_rule[OF wf])
    case (1 T)
    show ?case
    proof (intro allI impI)
      fix ty assume \<sigma>T: "fmlookup \<sigma> T = Some ty"
      then have "T |\<in>| fmdom \<sigma>" by (rule fmdomI)
      then have T_domu: "T |\<in>| fmdom u" using dom_\<sigma> by simp
      then obtain uty where uT: "fmlookup u T = Some uty"
        by (auto simp: fmlookup_dom_iff)
      have ty_eq: "ty = apply_subst \<sigma> uty"
        using cl uT \<sigma>T unfolding is_subst_closure_def by auto
      show "type_tyvars ty \<subseteq> subst_range_tyvars u - fset (fmdom u)"
      proof
        fix x assume "x \<in> type_tyvars ty"
        then have x_in: "x \<in> type_tyvars (apply_subst \<sigma> uty)" using ty_eq by simp
        from type_tyvars_apply_subst_decompose[OF x_in]
        show "x \<in> subst_range_tyvars u - fset (fmdom u)"
        proof (elim disjE conjE bexE)
          \<comment> \<open>x survives from u's raw right-hand side, outside the domain.\<close>
          assume x_uty: "x \<in> type_tyvars uty" and x_nodom: "x |\<notin>| fmdom \<sigma>"
          have "uty \<in> fmran' u" using uT by (rule fmran'I)
          then have "x \<in> subst_range_tyvars u"
            using x_uty unfolding subst_range_tyvars_def by auto
          then show ?thesis using x_nodom dom_\<sigma> by auto
        next
          \<comment> \<open>x was introduced by resolving a dependency a of T; recurse on a.\<close>
          fix a assume a_uty: "a \<in> type_tyvars uty" and a_dom: "a |\<in>| fmdom \<sigma>"
            and x_a: "x \<in> type_tyvars (apply_subst \<sigma> (CoreTy_Var a))"
          have a_domu: "a |\<in>| fmdom u" using a_dom dom_\<sigma> by simp
          have edge: "(a, T) \<in> subst_dep_rel u"
            unfolding subst_dep_rel_def using T_domu a_domu a_uty uT by auto
          obtain aty where \<sigma>a: "fmlookup \<sigma> a = Some aty"
            using a_dom by (auto simp: fmlookup_dom_iff)
          have "apply_subst \<sigma> (CoreTy_Var a) = aty" using \<sigma>a by simp
          then have x_aty: "x \<in> type_tyvars aty" using x_a by simp
          from "1.IH"[OF edge] \<sigma>a x_aty show ?thesis by blast
        qed
      qed
    qed
  qed
  show ?thesis
  proof
    fix x assume "x \<in> subst_range_tyvars \<sigma>"
    then obtain ty where "ty \<in> fmran' \<sigma>" and x_ty: "x \<in> type_tyvars ty"
      unfolding subst_range_tyvars_def by auto
    then obtain T where "fmlookup \<sigma> T = Some ty"
      by (auto simp: fmlookup_ran'_iff)
    then show "x \<in> subst_range_tyvars u - fset (fmdom u)"
      using main x_ty by blast
  qed
qed


end

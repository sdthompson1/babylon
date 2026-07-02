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
(* The idempotent closure of a substitution *)
(* ========================================================================== *)

(* is_subst_closure u \<sigma>: \<sigma> is the idempotent closure of the equation set u.
   That is, \<sigma> is idempotent (domain/range-disjoint), has the same domain as u,
   and resolves each of u's equations fully (\<sigma>(T) equals u(T) with \<sigma> applied to
   its right-hand side). *)
(* See also SubstClosureExistsUnique.thy for conditions for this to exist and be unique. *)
definition is_subst_closure :: "TypeSubst \<Rightarrow> TypeSubst \<Rightarrow> bool" where
  "is_subst_closure u \<sigma> \<equiv>
       idempotent_subst \<sigma>
     \<and> fmdom \<sigma> = fmdom u
     \<and> (\<forall>T ty. fmlookup u T = Some ty \<longrightarrow> fmlookup \<sigma> T = Some (apply_subst \<sigma> ty))"


end

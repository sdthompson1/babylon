theory SubstAbsorption
  imports MergeSubstsPrelims
begin

(* ========================================================================== *)
(* Closure absorption over a raw union                                        *)
(*                                                                            *)
(* The engine of the whole-program well-typedness theorem:                    *)
(* let \<sigma> be the closure of a substitution u (one sub-link's merged             *)
(* substitution, e.g. link A), and \<tau> the closure of a LARGER raw union         *)
(* p ++f u (the whole program's, e.g. link (A \<union> B)). Then applying \<sigma> first is  *)
(* a no-op under \<tau>:                                                           *)
(*                                                                            *)
(*     apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty                     *)
(*                                                                            *)
(* This is what lets a module normalized with its sub-link's substitution be  *)
(* re-normalized with the whole program's: the two-step resolution agrees     *)
(* with the one-step one.                                                     *)
(* ========================================================================== *)

(* Absorption on a single domain variable of u, by well-founded induction on
   u's dependency relation. *)
lemma closure_absorb_var_raw:
  assumes acyc: "acyclic_subst_deps u"
      and cl_u: "is_subst_closure u \<sigma>"
      and cl_pu: "is_subst_closure (p ++\<^sub>f u) \<tau>"
      and v_dom: "v |\<in>| fmdom u"
  shows "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var v)) = apply_subst \<tau> (CoreTy_Var v)"
proof -
  have wf: "wf (subst_dep_rel u)" using acyc by (rule acyclic_subst_deps_wf)
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  show ?thesis
  using v_dom proof (induction v rule: wf_induct_rule[OF wf])
    case (1 v)
    then have v_domu: "v |\<in>| fmdom u" by simp
    then obtain ty where ty_u: "fmlookup u v = Some ty"
      by (auto simp: fmlookup_dom_iff)
    have \<sigma>_v: "fmlookup \<sigma> v = Some (apply_subst \<sigma> ty)"
      using cl_u ty_u unfolding is_subst_closure_def by blast
    have lhs: "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var v))
             = apply_subst \<tau> (apply_subst \<sigma> ty)"
      using \<sigma>_v by simp
    \<comment> \<open>Step 1: \<tau> absorbs \<sigma> on ty, via the IH at every dependency of v.\<close>
    have absorb_ty: "apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
    proof -
      have pt: "\<And>x. x \<in> type_tyvars ty \<Longrightarrow>
                  apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var x)) = apply_subst \<tau> (CoreTy_Var x)"
      proof -
        fix x assume x_in: "x \<in> type_tyvars ty"
        show "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var x)) = apply_subst \<tau> (CoreTy_Var x)"
        proof (cases "x |\<in>| fmdom u")
          case False
          then have "fmlookup \<sigma> x = None" using dom_\<sigma> by (simp add: fmdom_notD)
          then show ?thesis by simp
        next
          case True
          have edge: "(x, v) \<in> subst_dep_rel u"
            unfolding subst_dep_rel_def using v_domu True x_in ty_u by auto
          show ?thesis using "1.IH"[OF edge True] .
        qed
      qed
      have "apply_subst (compose_subst \<tau> \<sigma>) ty = apply_subst \<tau> ty"
      proof (rule apply_subst_cong_on_tyvars_val)
        fix x assume "x \<in> type_tyvars ty"
        from pt[OF this]
        show "apply_subst (compose_subst \<tau> \<sigma>) (CoreTy_Var x) = apply_subst \<tau> (CoreTy_Var x)"
          using compose_subst_correct by presburger
      qed
      then show ?thesis by (simp add: compose_subst_correct)
    qed
    \<comment> \<open>Step 2: u wins at v in the raw union p ++f u, so \<tau> closes u's own
        equation at v directly.\<close>
    have tau_v: "apply_subst \<tau> ty = apply_subst \<tau> (CoreTy_Var v)"
    proof -
      have "fmlookup (p ++\<^sub>f u) v = Some ty"
        by (simp add: ty_u v_domu)
      then have "fmlookup \<tau> v = Some (apply_subst \<tau> ty)"
        using cl_pu unfolding is_subst_closure_def by blast
      then show ?thesis by simp
    qed
    show ?case using lhs absorb_ty tau_v by simp
  qed
qed

(* Absorption lifted from variables to arbitrary types. *)
lemma closure_absorb_type_raw:
  assumes acyc: "acyclic_subst_deps u"
      and cl_u: "is_subst_closure u \<sigma>"
      and cl_pu: "is_subst_closure (p ++\<^sub>f u) \<tau>"
  shows "apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
proof -
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  have "apply_subst (compose_subst \<tau> \<sigma>) ty = apply_subst \<tau> ty"
  proof (rule apply_subst_cong_on_tyvars_val)
    fix x assume "x \<in> type_tyvars ty"
    have "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var x)) = apply_subst \<tau> (CoreTy_Var x)"
    proof (cases "x |\<in>| fmdom u")
      case False
      then have "fmlookup \<sigma> x = None" using dom_\<sigma> by (simp add: fmdom_notD)
      then show ?thesis by simp
    next
      case True
      then show ?thesis using closure_absorb_var_raw[OF acyc cl_u cl_pu] by simp
    qed
    then show "apply_subst (compose_subst \<tau> \<sigma>) (CoreTy_Var x) = apply_subst \<tau> (CoreTy_Var x)"
      using compose_subst_correct by presburger
  qed
  then show ?thesis by (simp add: compose_subst_correct)
qed

end

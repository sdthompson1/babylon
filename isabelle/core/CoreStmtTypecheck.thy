theory CoreStmtTypecheck
  imports CoreTypecheck CoreTypeProps
begin

(* ========================================================================== *)
(* Impure function-call typechecking                                          *)
(*                                                                            *)
(* A term-level function call (core_term_type CoreTm_FunctionCall) rejects    *)
(* calls that take Ref parameters or are marked FI_Impure. But at the         *)
(* outermost position on the rhs of an Assign or a VarDecl(Var), the source   *)
(* language does allow such calls. This helper typechecks such a call         *)
(* occurring at the outermost position. It returns None for any term that    *)
(* is not a CoreTm_FunctionCall, so callers can fall back to core_term_type. *)
(*                                                                            *)
(* For each argument:                                                         *)
(*   - Ref parameter: argument must be a writable lvalue of the expected      *)
(*     (substituted) type.                                                    *)
(*   - Var parameter: argument is typechecked via core_term_type, so nested   *)
(*     calls stay pure.                                                       *)
(* ========================================================================== *)

definition core_impure_call_type ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> string \<Rightarrow> CoreType list \<Rightarrow> CoreTerm list \<Rightarrow> CoreType option" where
  "core_impure_call_type env ghost fnName tyArgs tmArgs =
    (case fmlookup (TE_Functions env) fnName of
       None \<Rightarrow> None
     | Some funInfo \<Rightarrow>
         if length tyArgs \<noteq> length (FI_TyArgs funInfo) then None
         else if \<not> list_all (is_well_kinded env) tyArgs then None
         else if ghost = NotGhost
                 \<and> (\<not> list_all (is_runtime_type env) tyArgs
                    \<or> FI_Ghost funInfo = Ghost) then None
         else if length tmArgs \<noteq> length (FI_TmArgs funInfo) then None
         else
           let tySubst = fmap_of_list (zip (FI_TyArgs funInfo) tyArgs);
               expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo);
               varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)
           in if list_all2 (\<lambda>(tm, vor) expectedTy.
                    case vor of
                      Var \<Rightarrow>
                        (case core_term_type env ghost tm of
                           None \<Rightarrow> False
                         | Some actualTy \<Rightarrow> actualTy = expectedTy)
                    | Ref \<Rightarrow>
                        is_writable_lvalue env tm
                        \<and> core_term_type env ghost tm = Some expectedTy)
                  (zip tmArgs varOrRefs) expectedArgTypes
              then Some (apply_subst tySubst (FI_ReturnType funInfo))
              else None)"


(* The type produced by an optional cast applied to a call's return value.
   None: no cast; the result type is the call's return type.
   Some t: cast the return value to t; valid only as an integer cast (mirroring
   core_term_type's CoreTm_Cast rule), with t runtime in NotGhost mode. *)
definition cast_result_type ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreType \<Rightarrow> CoreType option \<Rightarrow> CoreType option" where
  "cast_result_type env ghost retTy castOpt =
    (case castOpt of
       None \<Rightarrow> Some retTy
     | Some t \<Rightarrow>
         if is_integer_type retTy \<and> is_integer_type t
            \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env t)
         then Some t else None)"

(* A convenient corollary of core_impure_call_type = Some: the function is
   looked up, and every argument term typechecks to *some* type via
   core_term_type. This is enough for several downstream proofs (erasure,
   fuel-monotonicity, preservation) that only need to know the arguments are
   well-typed rather than the full Var/Ref-respecting check. *)
lemma core_impure_call_type_args_typed:
  assumes "core_impure_call_type env ghost fnName tyArgs tmArgs = Some ty"
  shows "\<exists>fi. fmlookup (TE_Functions env) fnName = Some fi
              \<and> length tmArgs = length (FI_TmArgs fi)
              \<and> list_all (\<lambda>tm. \<exists>t. core_term_type env ghost tm = Some t) tmArgs"
proof -
  from assms have unfolded:
    "(case fmlookup (TE_Functions env) fnName of
        None \<Rightarrow> None
      | Some fi \<Rightarrow>
          if length tyArgs \<noteq> length (FI_TyArgs fi) then None
          else if \<not> list_all (is_well_kinded env) tyArgs then None
          else if ghost = NotGhost
                  \<and> (\<not> list_all (is_runtime_type env) tyArgs
                     \<or> FI_Ghost fi = Ghost) then None
          else if length tmArgs \<noteq> length (FI_TmArgs fi) then None
          else
            let tySubst = fmap_of_list (zip (FI_TyArgs fi) tyArgs);
                expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs fi);
                varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)
            in if list_all2 (\<lambda>(tm, vor) expectedTy.
                     case vor of
                       Var \<Rightarrow>
                         (case core_term_type env ghost tm of
                            None \<Rightarrow> False
                          | Some actualTy \<Rightarrow> actualTy = expectedTy)
                     | Ref \<Rightarrow>
                         is_writable_lvalue env tm
                         \<and> core_term_type env ghost tm = Some expectedTy)
                   (zip tmArgs varOrRefs) expectedArgTypes
               then Some (apply_subst tySubst (FI_ReturnType fi))
               else None) = Some ty"
    unfolding core_impure_call_type_def by simp
  from unfolded obtain fi where
    fi_lookup: "fmlookup (TE_Functions env) fnName = Some fi"
    by (cases "fmlookup (TE_Functions env) fnName") auto
  from unfolded fi_lookup have body:
    "(if length tyArgs \<noteq> length (FI_TyArgs fi) then None
      else if \<not> list_all (is_well_kinded env) tyArgs then None
      else if ghost = NotGhost
              \<and> (\<not> list_all (is_runtime_type env) tyArgs
                 \<or> FI_Ghost fi = Ghost) then None
      else if length tmArgs \<noteq> length (FI_TmArgs fi) then None
      else
        let tySubst = fmap_of_list (zip (FI_TyArgs fi) tyArgs);
            expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs fi);
            varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)
        in if list_all2 (\<lambda>(tm, vor) expectedTy.
                 case vor of
                   Var \<Rightarrow>
                     (case core_term_type env ghost tm of
                        None \<Rightarrow> False
                      | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 | Ref \<Rightarrow>
                     is_writable_lvalue env tm
                     \<and> core_term_type env ghost tm = Some expectedTy)
               (zip tmArgs varOrRefs) expectedArgTypes
           then Some (apply_subst tySubst (FI_ReturnType fi))
           else None) = Some ty"
    by simp
  have len_tmArgs: "length tmArgs = length (FI_TmArgs fi)"
    using body by (metis option.distinct(1))
  from body len_tmArgs
  have after_ifs:
    "(let tySubst = fmap_of_list (zip (FI_TyArgs fi) tyArgs);
          expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs fi);
          varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)
      in if list_all2 (\<lambda>(tm, vor) expectedTy.
               case vor of
                 Var \<Rightarrow>
                   (case core_term_type env ghost tm of
                      None \<Rightarrow> False
                    | Some actualTy \<Rightarrow> actualTy = expectedTy)
               | Ref \<Rightarrow>
                   is_writable_lvalue env tm
                   \<and> core_term_type env ghost tm = Some expectedTy)
             (zip tmArgs varOrRefs) expectedArgTypes
         then Some (apply_subst tySubst (FI_ReturnType fi))
         else None) = Some ty"
    by (meson option.distinct(1))
  from after_ifs have argTms_l2:
    "list_all2 (\<lambda>(tm, vor) expectedTy.
                  case vor of
                    Var \<Rightarrow>
                      (case core_term_type env ghost tm of
                         None \<Rightarrow> False
                       | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  | Ref \<Rightarrow>
                      is_writable_lvalue env tm
                      \<and> core_term_type env ghost tm = Some expectedTy)
               (zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)))
               (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
                    (FI_TmArgs fi))"
    by (simp add: Let_def split: if_splits)

  have args_typed:
    "list_all (\<lambda>tm. \<exists>t. core_term_type env ghost tm = Some t) tmArgs"
    unfolding list_all_length
  proof (intro allI impI)
    fix i assume i_lt: "i < length tmArgs"
    with len_tmArgs have i_lt_fi: "i < length (FI_TmArgs fi)" by simp
    have i_lt_zip: "i < length (zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)))"
      using i_lt len_tmArgs by simp

    obtain n ti vor where fi_arg_eq: "FI_TmArgs fi ! i = (n, ti, vor)"
      by (cases "FI_TmArgs fi ! i") auto
    have zip_nth: "zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)) ! i
                    = (tmArgs ! i, vor)"
      using i_lt i_lt_fi fi_arg_eq by simp
    have expected_nth:
      "(map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
            (FI_TmArgs fi)) ! i
          = apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ti"
      using i_lt_fi fi_arg_eq by simp

    have nth_check:
      "(case vor of
          Var \<Rightarrow>
            (case core_term_type env ghost (tmArgs ! i) of
               None \<Rightarrow> False
             | Some actualTy \<Rightarrow> actualTy = apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ti)
        | Ref \<Rightarrow>
            is_writable_lvalue env (tmArgs ! i)
            \<and> core_term_type env ghost (tmArgs ! i)
                = Some (apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ti))"
      using list_all2_nthD2[OF argTms_l2, of i] i_lt_zip zip_nth expected_nth
      by simp

    show "\<exists>t. core_term_type env ghost (tmArgs ! i) = Some t"
      using nth_check by (cases vor; auto split: option.splits)
  qed
  from fi_lookup len_tmArgs args_typed show ?thesis by blast
qed


(* A stronger corollary of core_impure_call_type = Some: produce the full set
   of function-call facts the TypeSoundness Assign proof uses from the pure
   core_term_type case, including a *pure-shape* list_all2 relating each
   argument to its expected type via core_term_type. This works because in
   core_impure_call_type, Ref arguments also require
   `core_term_type env ghost tm = Some expectedTy` (in addition to being
   writable lvalues), so every argument — Var or Ref — has a corresponding
   core_term_type entry. *)
lemma core_impure_call_type_fn_facts:
  assumes "core_impure_call_type env ghost fnName tyArgs tmArgs = Some ty"
  shows "\<exists>funInfo.
            fmlookup (TE_Functions env) fnName = Some funInfo
            \<and> length tyArgs = length (FI_TyArgs funInfo)
            \<and> list_all (is_well_kinded env) tyArgs
            \<and> (ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs)
            \<and> (ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost)
            \<and> length tmArgs = length (FI_TmArgs funInfo)
            \<and> ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                               (FI_ReturnType funInfo)
            \<and> list_all2 (\<lambda>tm expectedTy.
                  case core_term_type env ghost tm of
                    None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
                tmArgs
                (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))
            \<and> (\<forall>i < length tmArgs.
                 snd (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i))"
proof -
  from assms have unfolded:
    "(case fmlookup (TE_Functions env) fnName of
        None \<Rightarrow> None
      | Some fi \<Rightarrow>
          if length tyArgs \<noteq> length (FI_TyArgs fi) then None
          else if \<not> list_all (is_well_kinded env) tyArgs then None
          else if ghost = NotGhost
                  \<and> (\<not> list_all (is_runtime_type env) tyArgs
                     \<or> FI_Ghost fi = Ghost) then None
          else if length tmArgs \<noteq> length (FI_TmArgs fi) then None
          else
            let tySubst = fmap_of_list (zip (FI_TyArgs fi) tyArgs);
                expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs fi);
                varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)
            in if list_all2 (\<lambda>(tm, vor) expectedTy.
                     case vor of
                       Var \<Rightarrow>
                         (case core_term_type env ghost tm of
                            None \<Rightarrow> False
                          | Some actualTy \<Rightarrow> actualTy = expectedTy)
                     | Ref \<Rightarrow>
                         is_writable_lvalue env tm
                         \<and> core_term_type env ghost tm = Some expectedTy)
                   (zip tmArgs varOrRefs) expectedArgTypes
               then Some (apply_subst tySubst (FI_ReturnType fi))
               else None) = Some ty"
    unfolding core_impure_call_type_def by simp
  from unfolded obtain fi where
    fi_lookup: "fmlookup (TE_Functions env) fnName = Some fi"
    by (cases "fmlookup (TE_Functions env) fnName") auto
  from unfolded fi_lookup have body:
    "(if length tyArgs \<noteq> length (FI_TyArgs fi) then None
      else if \<not> list_all (is_well_kinded env) tyArgs then None
      else if ghost = NotGhost
              \<and> (\<not> list_all (is_runtime_type env) tyArgs
                 \<or> FI_Ghost fi = Ghost) then None
      else if length tmArgs \<noteq> length (FI_TmArgs fi) then None
      else
        let tySubst = fmap_of_list (zip (FI_TyArgs fi) tyArgs);
            expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs fi);
            varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)
        in if list_all2 (\<lambda>(tm, vor) expectedTy.
                 case vor of
                   Var \<Rightarrow>
                     (case core_term_type env ghost tm of
                        None \<Rightarrow> False
                      | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 | Ref \<Rightarrow>
                     is_writable_lvalue env tm
                     \<and> core_term_type env ghost tm = Some expectedTy)
               (zip tmArgs varOrRefs) expectedArgTypes
           then Some (apply_subst tySubst (FI_ReturnType fi))
           else None) = Some ty"
    by simp
  have len_tyArgs: "length tyArgs = length (FI_TyArgs fi)"
    using body by (metis option.distinct(1))
  from body len_tyArgs have tyArgs_wk: "list_all (is_well_kinded env) tyArgs"
    by (metis option.distinct(1))
  from body len_tyArgs tyArgs_wk have not_ghost_cond:
    "\<not> (ghost = NotGhost
        \<and> (\<not> list_all (is_runtime_type env) tyArgs
           \<or> FI_Ghost fi = Ghost))"
    by (metis option.distinct(1))
  from body len_tyArgs tyArgs_wk not_ghost_cond have len_tmArgs:
    "length tmArgs = length (FI_TmArgs fi)"
    by (metis option.distinct(1))
  from body len_tyArgs tyArgs_wk not_ghost_cond len_tmArgs
  have after_ifs:
    "(let tySubst = fmap_of_list (zip (FI_TyArgs fi) tyArgs);
          expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs fi);
          varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)
      in if list_all2 (\<lambda>(tm, vor) expectedTy.
               case vor of
                 Var \<Rightarrow>
                   (case core_term_type env ghost tm of
                      None \<Rightarrow> False
                    | Some actualTy \<Rightarrow> actualTy = expectedTy)
               | Ref \<Rightarrow>
                   is_writable_lvalue env tm
                   \<and> core_term_type env ghost tm = Some expectedTy)
             (zip tmArgs varOrRefs) expectedArgTypes
         then Some (apply_subst tySubst (FI_ReturnType fi))
         else None) = Some ty"
    by auto
  from after_ifs have argTms_l2_impure:
    "list_all2 (\<lambda>(tm, vor) expectedTy.
                  case vor of
                    Var \<Rightarrow>
                      (case core_term_type env ghost tm of
                         None \<Rightarrow> False
                       | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  | Ref \<Rightarrow>
                      is_writable_lvalue env tm
                      \<and> core_term_type env ghost tm = Some expectedTy)
               (zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)))
               (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
                    (FI_TmArgs fi))"
    by (simp add: Let_def split: if_splits)
  from after_ifs have fn_ty_eq:
    "ty = apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) (FI_ReturnType fi)"
    by (simp add: Let_def split: if_splits)

  \<comment> \<open>Derive the pure-shape list_all2: every argument (whether Var or Ref)
      satisfies core_term_type ... = Some expectedTy, because the impure
      check requires it in both branches. \<close>
  have argTms_l2_pure:
    "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type env ghost tm of
                    None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
               tmArgs
               (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
                    (FI_TmArgs fi))"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length tmArgs
            = length (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
                          (FI_TmArgs fi))"
      using len_tmArgs by simp
  next
    fix i assume i_lt: "i < length tmArgs"
    with len_tmArgs have i_lt_fi: "i < length (FI_TmArgs fi)" by simp
    have i_lt_zip:
      "i < length (zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)))"
      using i_lt len_tmArgs by simp
    obtain n ti vor where fi_arg_eq: "FI_TmArgs fi ! i = (n, ti, vor)"
      by (cases "FI_TmArgs fi ! i") auto
    have zip_nth:
      "zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)) ! i = (tmArgs ! i, vor)"
      using i_lt i_lt_fi fi_arg_eq by simp
    have expected_nth:
      "(map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
            (FI_TmArgs fi)) ! i
          = apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ti"
      using i_lt_fi fi_arg_eq by simp
    have nth_check:
      "(case vor of
          Var \<Rightarrow>
            (case core_term_type env ghost (tmArgs ! i) of
               None \<Rightarrow> False
             | Some actualTy \<Rightarrow>
                 actualTy = apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ti)
        | Ref \<Rightarrow>
            is_writable_lvalue env (tmArgs ! i)
            \<and> core_term_type env ghost (tmArgs ! i)
                = Some (apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ti))"
      using list_all2_nthD2[OF argTms_l2_impure, of i] i_lt_zip zip_nth expected_nth
      by simp
    show "case core_term_type env ghost (tmArgs ! i) of
            None \<Rightarrow> False
          | Some actualTy \<Rightarrow>
              actualTy = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
                             (FI_TmArgs fi) ! i"
      using nth_check expected_nth by (cases vor; auto split: option.splits)
  qed

  have ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs"
    using not_ghost_cond by blast
  have ng_fn: "ghost = NotGhost \<longrightarrow> FI_Ghost fi \<noteq> Ghost"
    using not_ghost_cond by blast

  \<comment> \<open>Extract the Ref-position lvalue witness from the impure list_all2. \<close>
  have ref_args_lvalues:
    "\<forall>i < length tmArgs.
       snd (snd (FI_TmArgs fi ! i)) = Ref
         \<longrightarrow> is_writable_lvalue env (tmArgs ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < length tmArgs" and ref: "snd (snd (FI_TmArgs fi ! i)) = Ref"
    with len_tmArgs have i_lt_fi: "i < length (FI_TmArgs fi)" by simp
    have i_lt_zip:
      "i < length (zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)))"
      using i_lt len_tmArgs by simp
    obtain n ti vor where fi_arg_eq: "FI_TmArgs fi ! i = (n, ti, vor)"
      by (cases "FI_TmArgs fi ! i") auto
    from ref fi_arg_eq have vor_eq: "vor = Ref" by simp
    have zip_nth:
      "zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs fi)) ! i = (tmArgs ! i, vor)"
      using i_lt i_lt_fi fi_arg_eq by simp
    have expected_nth:
      "(map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
            (FI_TmArgs fi)) ! i
          = apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ti"
      using i_lt_fi fi_arg_eq by simp
    from list_all2_nthD2[OF argTms_l2_impure, of i] i_lt_zip zip_nth expected_nth vor_eq
    show "is_writable_lvalue env (tmArgs ! i)" by simp
  qed

  from fi_lookup len_tyArgs tyArgs_wk ng_tyArgs ng_fn len_tmArgs fn_ty_eq
       argTms_l2_pure ref_args_lvalues
  show ?thesis by blast
qed


(* cast_result_type is preserved under adding type variables to the environment:
   it depends on env only through is_runtime_type, which is monotone. *)
lemma cast_result_type_irrelevant_tyvar:
  assumes "cast_result_type env ghost retTy castOpt = Some ty"
  shows "cast_result_type
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>)
           ghost retTy castOpt = Some ty"
  using assms unfolding cast_result_type_def
  by (cases castOpt) (auto split: if_splits simp: is_runtime_type_extend_runtime_tyvars)


(* The impure-call typecheck is preserved under adding type variables to the
   environment. The embedded checks (fmlookup TE_Functions / is_well_kinded /
   is_runtime_type / core_term_type / is_writable_lvalue) are all unchanged or
   monotone under this extension, and the returned type does not depend on the
   tyvar sets, so a successful check stays successful with the same result. *)
lemma core_impure_call_type_irrelevant_tyvar:
  assumes "core_impure_call_type env ghost fnName tyArgs tmArgs = Some ty"
  shows "core_impure_call_type
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>)
           ghost fnName tyArgs tmArgs = Some ty"
proof -
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from core_impure_call_type_fn_facts[OF assms] obtain funInfo where
    fi: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs" and
    fn_ng: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    len_tm: "length tmArgs = length (FI_TmArgs funInfo)" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)" and
    l2_pure: "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type env ghost tm of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
                tmArgs
                (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))" and
    ref_lv: "\<forall>i < length tmArgs.
                snd (snd (FI_TmArgs funInfo ! i)) = Ref
                  \<longrightarrow> is_writable_lvalue env (tmArgs ! i)"
    by blast

  \<comment> \<open>Transfer the embedded checks to the extended environment.\<close>
  have fns_eq: "TE_Functions ?env' = TE_Functions env" by simp
  have wk': "list_all (is_well_kinded ?env') tyArgs"
    using wk is_well_kinded_extend_tyvars by (fastforce simp: list_all_iff)
  have rt': "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') tyArgs"
    using rt is_runtime_type_extend_runtime_tyvars by (fastforce simp: list_all_iff)
  have l2_pure': "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type ?env' ghost tm of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
                tmArgs
                (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))"
    using l2_pure core_term_type_irrelevant_tyvar
    by (elim list_all2_mono) (auto split: option.splits)

  \<comment> \<open>Rebuild the full per-argument (Var/Ref) check for the extended env, by
      proving each index from the pure list and the Ref-lvalue witnesses.\<close>
  let ?P' = "\<lambda>(tm, vor) expectedTy.
                 case vor of
                   Var \<Rightarrow> (case core_term_type ?env' ghost tm of None \<Rightarrow> False
                            | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 | Ref \<Rightarrow> is_writable_lvalue ?env' tm
                          \<and> core_term_type ?env' ghost tm = Some expectedTy"
  let ?zts = "zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo))"
  let ?exps = "map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                    (FI_TmArgs funInfo)"
  have len_zts: "length ?zts = length ?exps" using len_tm by simp
  have nth_pred: "\<And>i. i < length ?zts \<Longrightarrow> ?P' (?zts ! i) (?exps ! i)"
  proof -
    fix i assume i_lt: "i < length ?zts"
    hence i_lt_tm: "i < length tmArgs" using len_tm by simp
    with len_tm have i_lt_fi: "i < length (FI_TmArgs funInfo)" by simp
    obtain n ti vor where fi_arg: "FI_TmArgs funInfo ! i = (n, ti, vor)"
      by (cases "FI_TmArgs funInfo ! i") auto
    have zip_nth: "?zts ! i = (tmArgs ! i, vor)"
      using i_lt_tm i_lt_fi fi_arg by simp
    have exp_nth: "?exps ! i = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti"
      using i_lt_fi fi_arg by simp
    have pure_i: "case core_term_type ?env' ghost (tmArgs ! i) of None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti"
      using list_all2_nthD[OF l2_pure'] i_lt_tm len_tm exp_nth by metis
    show "?P' (?zts ! i) (?exps ! i)"
    proof (cases vor)
      case Var
      with zip_nth exp_nth pure_i show ?thesis by simp
    next
      case Ref
      have "is_writable_lvalue env (tmArgs ! i)"
        using ref_lv i_lt_tm fi_arg Ref by simp
      hence writ': "is_writable_lvalue ?env' (tmArgs ! i)" by simp
      from pure_i have
        "core_term_type ?env' ghost (tmArgs ! i)
           = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti)"
        by (auto split: option.splits)
      with Ref zip_nth exp_nth writ' show ?thesis by simp
    qed
  qed
  have l2_full': "list_all2 ?P' ?zts ?exps"
    using len_zts nth_pred by (simp add: list_all2_conv_all_nth)

  show ?thesis
    unfolding core_impure_call_type_def
    using fi wk' rt' fn_ng len_ty len_tm l2_full' ty_eq
    by (auto simp: fns_eq Let_def)
qed


(* ========================================================================== *)
(* Statement typechecking                                                     *)
(*                                                                            *)
(* A statement transforms the type environment (e.g. VarDecl adds a new       *)
(* variable). The typechecking function returns the resulting environment,     *)
(* or None if ill-typed.                                                      *)
(*                                                                            *)
(* The GhostOrNot parameter represents the ghost context:                     *)
(*   - Ghost context: only ghost statements are allowed                       *)
(*   - NotGhost context: both ghost and non-ghost statements are allowed      *)
(* ========================================================================== *)

function core_statement_type :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreStatement \<Rightarrow> CoreTyEnv option"
and core_statement_list_type :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreStatement list \<Rightarrow> CoreTyEnv option"
where

  (* Variable declaration (Var).
     The initializer is an ordinary (pure) term. Impure function-call
     initializers use CoreStmt_VarDeclCall instead. *)
  "core_statement_type env ghost (CoreStmt_VarDecl declGhost varName Var varTy initTm) =
    (if (ghost = Ghost \<longrightarrow> declGhost = Ghost)
        \<and> is_well_kinded env varTy
        \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
        \<and> core_term_type env declGhost initTm = Some varTy
     then Some (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := (if declGhost = Ghost
                                       then finsert varName (TE_GhostLocals env)
                                       else fminus (TE_GhostLocals env) {|varName|}),
                      TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>)
     else None)"

  (* Variable declaration initialized from an impure function call.
     The variable type is explicit (and must be well-kinded, and runtime in
     NotGhost mode, exactly as for CoreStmt_VarDecl). The call is typechecked by
     core_impure_call_type, and the (optionally cast) return type must equal the
     declared variable type. *)
| "core_statement_type env ghost (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms) =
    (if (ghost = Ghost \<longrightarrow> declGhost = Ghost)
        \<and> is_well_kinded env varTy
        \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
     then (case core_impure_call_type env declGhost fnName tyArgs argTms of
             Some retTy \<Rightarrow>
               if cast_result_type env declGhost retTy castOpt = Some varTy
               then Some (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                TE_GhostLocals := (if declGhost = Ghost
                                                 then finsert varName (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|varName|}),
                                TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>)
               else None
           | None \<Rightarrow> None)
     else None)"

  (* Variable declaration (Ref).
     The rhs must be a syntactic lvalue with the declared type. The new ref
     becomes const iff its base is read-only (a const local or a global). *)
| "core_statement_type env ghost (CoreStmt_VarDecl declGhost varName Ref varTy initTm) =
    (if (ghost = Ghost \<longrightarrow> declGhost = Ghost)
        \<and> is_well_kinded env varTy
        \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
        \<and> is_lvalue initTm
        \<and> core_term_type env declGhost initTm = Some varTy
     then Some (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := (if declGhost = Ghost
                                       then finsert varName (TE_GhostLocals env)
                                       else fminus (TE_GhostLocals env) {|varName|}),
                      TE_ConstLocals := (if is_writable_lvalue env initTm
                                        then fminus (TE_ConstLocals env) {|varName|}
                                        else finsert varName (TE_ConstLocals env)) \<rparr>)
     else None)"

  (* Assignment.
     The rhs is an ordinary (pure) term. Impure function-call rhs's use
     CoreStmt_AssignCall instead. *)
| "core_statement_type env ghost (CoreStmt_Assign assignGhost lhsTm rhsTm) =
    (if (ghost = Ghost \<longrightarrow> assignGhost = Ghost)
        \<and> is_writable_lvalue env lhsTm
     then (case core_term_type env assignGhost lhsTm of
             Some lhsTy \<Rightarrow>
               if core_term_type env assignGhost rhsTm = Some lhsTy
               then Some env
               else None
           | None \<Rightarrow> None)
     else None)"

  (* Assignment whose rhs is an impure function call.
     The lhs must be a writable lvalue; the call's (optionally cast) return type
     must equal the lhs type. *)
| "core_statement_type env ghost (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms) =
    (if (ghost = Ghost \<longrightarrow> assignGhost = Ghost)
        \<and> is_writable_lvalue env lhsTm
     then (case core_term_type env assignGhost lhsTm of
             Some lhsTy \<Rightarrow>
               (case core_impure_call_type env assignGhost fnName tyArgs argTms of
                  Some retTy \<Rightarrow>
                    if cast_result_type env assignGhost retTy castOpt = Some lhsTy
                    then Some env else None
                | None \<Rightarrow> None)
           | None \<Rightarrow> None)
     else None)"

  (* Return: the term must have the expected return type.
     We require ghost = TE_FunctionGhost env:
       - In a ghost function, we always typecheck in Ghost mode, so both are Ghost.
       - In a non-ghost function, Return is only allowed in NotGhost mode
         (not inside a Ghost block). *)
| "core_statement_type env ghost (CoreStmt_Return tm) =
    (if ghost = TE_FunctionGhost env
        \<and> core_term_type env ghost tm = Some (TE_ReturnType env)
     then Some env
     else None)"

  (* Swap: both sides must be writable lvalues of the same type *)
| "core_statement_type env ghost (CoreStmt_Swap swapGhost lhsTm rhsTm) =
    (if (ghost = Ghost \<longrightarrow> swapGhost = Ghost)
        \<and> is_writable_lvalue env lhsTm
        \<and> is_writable_lvalue env rhsTm
     then (case core_term_type env swapGhost lhsTm of
             Some lhsTy \<Rightarrow>
               if core_term_type env swapGhost rhsTm = Some lhsTy
               then Some env
               else None
           | None \<Rightarrow> None)
     else None)"

  (* Assert: condition must be bool; proof body typechecks in Ghost context.
     When a condition is present ("assert condTm"), we install condTm as
     TE_ProofGoal so that top-level CoreStmt_Fix statements in proofBody can peel
     its leading Quant_Forall quantifiers. When the condition is absent
     ("assert *"), the asserted goal is the current proof goal, so TE_ProofGoal
     is left unchanged. In both cases the result env is the original env, so the
     goal (and any Fix-introduced locals) do not escape the assert. *)
| "core_statement_type env ghost (CoreStmt_Assert condOpt proofBody) =
    (let goalEnv = (case condOpt of Some condTm \<Rightarrow> env \<lparr> TE_ProofGoal := Some condTm \<rparr>
                                  | None \<Rightarrow> env);
         condOk = (case condOpt of Some condTm \<Rightarrow> core_term_type env Ghost condTm = Some CoreTy_Bool
                                 | None \<Rightarrow> True)
     in (if condOk
         then (case core_statement_list_type goalEnv Ghost proofBody of
                 Some _ \<Rightarrow> Some env
               | None \<Rightarrow> None)
         else None))"

  (* Assume: term must be bool *)
| "core_statement_type env ghost (CoreStmt_Assume tm) =
    (if core_term_type env Ghost tm = Some CoreTy_Bool
     then Some env
     else None)"

  (* ShowHide: no-op *)
| "core_statement_type env ghost (CoreStmt_ShowHide _ _) = Some env"

  (* Pattern match.
     The scrutinee must typecheck. Each pattern must be compatible with the
     scrutinee type, and the pattern list must be regular (no duplicates and
     no patterns after a wildcard). Each arm's statement list must typecheck
     under the same env (match arms run in their own scope, so bindings they
     introduce are discarded on exit).
     Note: exhaustiveness is NOT checked; a non-exhaustive match that finds no
     matching arm at runtime is a runtime error, not a type error. In
     particular, an empty match is allowed and always fails at runtime. *)
| "core_statement_type env ghost (CoreStmt_Match matchGhost scrut arms) =
    (if ghost = Ghost \<longrightarrow> matchGhost = Ghost
     then (case core_term_type env matchGhost scrut of
             None \<Rightarrow> None
           | Some scrutTy \<Rightarrow>
               let pats = map fst arms;
                   bodies = map snd arms
               in if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
                  else if list_all (\<lambda>body. core_statement_list_type
                                              (env \<lparr> TE_ProofGoal := None \<rparr>)
                                              matchGhost body \<noteq> None) bodies
                       then Some env
                       else None)
     else None)"

  (* While loop.
     The condition must be Bool, checked in the loop's ghost mode (since it's
     runtime-evaluated when whileGhost = NotGhost). Invariants are specification
     only (never evaluated at runtime) so they're checked in Ghost mode, as is
     the decreases term. The decreases term's type must be one for which
     is_valid_decreases_type holds (integer or lexicographic record of same).
     The body typechecks as a statement list in whileGhost mode; its result
     env is discarded (body scope is popped via restore_scope at runtime). *)
| "core_statement_type env ghost (CoreStmt_While whileGhost condTm invars decrTm body) =
    (if ghost = Ghost \<longrightarrow> whileGhost = Ghost
     then (case core_term_type env whileGhost condTm of
             Some CoreTy_Bool \<Rightarrow>
               if list_all (\<lambda>inv. core_term_type env Ghost inv = Some CoreTy_Bool) invars
               then (case core_term_type env Ghost decrTm of
                       Some decrTy \<Rightarrow>
                         if is_valid_decreases_type decrTy
                         then (case core_statement_list_type
                                      (env \<lparr> TE_ProofGoal := None \<rparr>) whileGhost body of
                                 Some _ \<Rightarrow> Some env
                               | None \<Rightarrow> None)
                         else None
                     | None \<Rightarrow> None)
               else None
           | _ \<Rightarrow> None)
     else None)"

  (* Obtain: "obtain x of type T where P(x)". Introduces a ghost local x (like a
     CoreStmt_VarDecl with declGhost = Ghost), so it is allowed in any ambient
     context: x goes into TE_GhostLocals, where only ghost code can see it. The
     type T must be well-kinded and the predicate P must typecheck to Bool in the
     env extended with x. The resulting env keeps x in scope. *)
| "core_statement_type env ghost (CoreStmt_Obtain varName varTy condTm) =
    (if is_well_kinded env varTy
     then let env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                            TE_GhostLocals := finsert varName (TE_GhostLocals env),
                            TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>
          in if core_term_type env' Ghost condTm = Some CoreTy_Bool
             then Some env'
             else None
     else None)"

  (* Fix: "fix x : T". Only valid in Ghost mode and at the immediate top level
     of an enclosing assert's proof body (tracked by TE_ProofGoal). The current 
     goal must be a universally-quantified term whose bound-variable type is exactly T
     (the quantifier's own bound name is irrelevant). The fixed variable is a ghost,
     const local (it is a spec-only, non-assignable witness). Stripping the
     Quant_Forall and storing the body as the new TE_ProofGoal lets a following
     Fix peel the next quantifier. The goal body is carried unchanged (it still
     refers to the quantifier's original bound name); this is sound because
     TE_ProofGoal is only consumed structurally. *)
| "core_statement_type env ghost (CoreStmt_Fix varName varTy) =
    (case TE_ProofGoal env of
       Some (CoreTm_Quantifier Quant_Forall _ qVarTy bodyTm) \<Rightarrow>
         (if ghost = Ghost \<and> qVarTy = varTy \<and> is_well_kinded env varTy
          then Some (env \<lparr> TE_LocalVars   := fmupd varName varTy (TE_LocalVars env),
                            TE_GhostLocals := finsert varName (TE_GhostLocals env),
                            TE_ConstLocals := finsert varName (TE_ConstLocals env),
                            TE_ProofGoal   := Some bodyTm \<rparr>)
          else None)
     | _ \<Rightarrow> None)"

  (* Use: "use e". Only valid in Ghost mode and at the immediate top level of
     an enclosing assert's proof body. Supplies a witness for an existential
     goal: TE_ProofGoal must be a Quant_Exists whose bound-variable type equals
     the type of e (the bound name is irrelevant). No variable is brought into
     scope; we strip the Quant_Exists and store the body as the new TE_ProofGoal
     so a following Fix/Use peels the next quantifier. As with Fix, the body is
     carried unchanged (TE_ProofGoal is only consumed structurally). *)
| "core_statement_type env ghost (CoreStmt_Use witnessTm) =
    (case TE_ProofGoal env of
       Some (CoreTm_Quantifier Quant_Exists _ qVarTy bodyTm) \<Rightarrow>
         (if ghost = Ghost \<and> core_term_type env ghost witnessTm = Some qVarTy
          then Some (env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>)
          else None)
     | _ \<Rightarrow> None)"

  (* Statement lists *)
| "core_statement_list_type env _ [] = Some env"
| "core_statement_list_type env ghost (stmt # stmts) =
    (case core_statement_type env ghost stmt of
       Some env' \<Rightarrow> core_statement_list_type env' ghost stmts
     | None \<Rightarrow> None)"

  by pat_completeness auto
  termination
  proof (relation "measure (\<lambda>x. case x of
      Inl (_, _, stmt) \<Rightarrow> size stmt
    | Inr (_, _, stmts) \<Rightarrow> size_list size stmts)"; (simp; fail)?)
    \<comment> \<open>CoreStmt_Match arm bodies are smaller than the whole match statement. \<close>
    fix env :: CoreTyEnv
    fix ghost :: GhostOrNot
    fix matchGhost :: GhostOrNot
    fix scrut :: CoreTerm
    fix arms :: "(CorePattern \<times> CoreStatement list) list"
    fix x2 x xa z
    assume xa_eq: "xa = map snd arms" and z_in: "z \<in> set xa"
    from xa_eq z_in obtain a where "(a, z) \<in> set arms" by auto
    hence "size_prod (\<lambda>y. 0) (size_list size) (a, z)
             \<le> size_list (size_prod (\<lambda>y. 0) (size_list size)) arms"
      by (simp add: size_list_estimation')
    hence z_le: "size_list size z \<le> size_list (size_prod (\<lambda>y. 0) (size_list size)) arms"
      by simp
    show "(Inr (env \<lparr> TE_ProofGoal := None \<rparr>, matchGhost, z),
           Inl (env, ghost, CoreStmt_Match matchGhost scrut arms))
          \<in> measure (\<lambda>y. case y of
              Inl (_, _, stmt) \<Rightarrow> size stmt
            | Inr (_, _, stmts) \<Rightarrow> size_list size stmts)"
      using z_le by simp
  qed


(* ========================================================================== *)
(* Ambient-ghost weakening                                                    *)
(*                                                                            *)
(* If a statement typechecks in Ghost mode, then it can be promoted to        *)
(* NotGhost mode and still typecheck -- provided that we are within an        *)
(* executable function (TE_FunctionGhost is NotGhost) and not inside an       *)
(* assert proof-block (TE_ProofGoal is None).                                 *)
(* ========================================================================== *)

lemma core_statement_type_ghost_to_notghost:
  assumes "core_statement_type env Ghost stmt = Some env'"
    and "TE_FunctionGhost env = NotGhost"
    and "TE_ProofGoal env = None"
  shows "core_statement_type env NotGhost stmt = Some env'"
  using assms
  by (cases "(env, Ghost, stmt)" rule: core_statement_type.cases)
     (auto simp: Let_def split: VarOrRef.splits option.splits if_splits CoreType.splits)


(* ========================================================================== *)
(* Well-formedness and return type preservation                               *)
(* ========================================================================== *)

(* core_statement_type preserves tyenv_well_formed *)
lemma core_statement_type_preserves_well_formed:
  assumes "core_statement_type env ghost stmt = Some env'"
    and "tyenv_well_formed env"
  shows "tyenv_well_formed env'"
using assms proof (cases stmt)
  case (CoreStmt_VarDecl declGhost varName varOrRef varTy initTm)
  show ?thesis proof (cases varOrRef)
    case Var
    from assms CoreStmt_VarDecl Var obtain
      wk: "is_well_kinded env varTy" and
      rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy"
      by (auto split: if_splits)
    show ?thesis proof (cases declGhost)
      case NotGhost
      from rt NotGhost have "is_runtime_type env varTy" by simp
      from tyenv_well_formed_add_var[OF assms(2) wk this]
      have wf': "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                          TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>)" .
      from assms CoreStmt_VarDecl Var NotGhost have env'_eq:
        "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                      TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
        by (auto split: if_splits)
      from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf']
      have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>
                                  \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>)" .
      hence "tyenv_well_formed env'" using env'_eq by simp
      thus ?thesis .
    next
      case Ghost
      from tyenv_well_formed_add_ghost_var[OF assms(2) wk]
      have wf': "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                          TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>)" .
      from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf']
      have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>
                                  \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>)" .
      with assms CoreStmt_VarDecl Var Ghost show ?thesis
        by (auto split: if_splits)
    qed
  next
    case Ref
    from assms CoreStmt_VarDecl Ref obtain
      wk: "is_well_kinded env varTy" and
      rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy"
      by (auto split: if_splits)
    show ?thesis proof (cases declGhost)
      case NotGhost
      from rt NotGhost have "is_runtime_type env varTy" by simp
      from tyenv_well_formed_add_var[OF assms(2) wk this]
      have wf': "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                          TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>)" .
      from assms CoreStmt_VarDecl Ref NotGhost have env'_eq:
        "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                      TE_ConstLocals := (if is_writable_lvalue env initTm
                                        then fminus (TE_ConstLocals env) {|varName|}
                                        else finsert varName (TE_ConstLocals env)) \<rparr>"
        by (auto split: if_splits)
      from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf']
      have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>
                                  \<lparr> TE_ConstLocals := (if is_writable_lvalue env initTm
                                                      then fminus (TE_ConstLocals env) {|varName|}
                                                      else finsert varName (TE_ConstLocals env)) \<rparr>)" .
      hence "tyenv_well_formed env'" using env'_eq by simp
      thus ?thesis .
    next
      case Ghost
      from tyenv_well_formed_add_ghost_var[OF assms(2) wk]
      have wf': "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                          TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>)" .
      from assms CoreStmt_VarDecl Ref Ghost have env'_eq:
        "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := finsert varName (TE_GhostLocals env),
                      TE_ConstLocals := (if is_writable_lvalue env initTm
                                        then fminus (TE_ConstLocals env) {|varName|}
                                        else finsert varName (TE_ConstLocals env)) \<rparr>"
        by (auto split: if_splits)
      from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf']
      have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>
                                  \<lparr> TE_ConstLocals := (if is_writable_lvalue env initTm
                                                      then fminus (TE_ConstLocals env) {|varName|}
                                                      else finsert varName (TE_ConstLocals env)) \<rparr>)" .
      hence "tyenv_well_formed env'" using env'_eq by simp
      thus ?thesis .
    qed
  qed
next
  case (CoreStmt_Assign assignGhost lhsTm rhsTm)
  with assms show ?thesis by (auto split: if_splits option.splits)
next
  case (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms)
  with assms have "env' = env" by (auto split: if_splits option.splits)
  with assms show ?thesis by simp
next
  case (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
  \<comment> \<open>The variable type is explicit and (by the rule) well-kinded, and runtime in
      NotGhost mode; env extends like VarDecl(Var).\<close>
  from assms CoreStmt_VarDeclCall obtain retTy where
    wk: "is_well_kinded env varTy" and
    rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    ct: "core_impure_call_type env declGhost fnName tyArgs argTms = Some retTy" and
    cast: "cast_result_type env declGhost retTy castOpt = Some varTy" and
    env'_eq:
      "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                    TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env)
                                     else fminus (TE_GhostLocals env) {|varName|}),
                    TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits option.splits)
  show ?thesis
  proof (cases declGhost)
    case NotGhost
    from rt NotGhost have rt': "is_runtime_type env varTy" by simp
    from tyenv_well_formed_add_var[OF assms(2) wk rt']
    have wf': "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                        TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>)" .
    from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf'] NotGhost show ?thesis
      by (simp add: env'_eq)
  next
    case Ghost
    from tyenv_well_formed_add_ghost_var[OF assms(2) wk]
    have wf': "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                        TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>)" .
    from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf'] Ghost show ?thesis
      by (simp add: env'_eq)
  qed
next
  case (CoreStmt_Fix varName varTy)
  from assms CoreStmt_Fix obtain bodyTm where
    wk: "is_well_kinded env varTy" and env'_eq:
    "env' = env \<lparr> TE_LocalVars   := fmupd varName varTy (TE_LocalVars env),
                   TE_GhostLocals := finsert varName (TE_GhostLocals env),
                   TE_ConstLocals := finsert varName (TE_ConstLocals env),
                   TE_ProofGoal   := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  from tyenv_well_formed_add_ghost_var[OF assms(2) wk]
  have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                  TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>)" .
  from tyenv_well_formed_TE_ProofGoal_irrelevant[OF
        tyenv_well_formed_TE_ConstLocals_irrelevant[OF this]]
  have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                 TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>
                              \<lparr> TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>
                              \<lparr> TE_ProofGoal := Some bodyTm \<rparr>)" .
  thus ?thesis using env'_eq by simp
next
  case (CoreStmt_Obtain varName varTy condTm)
  from assms CoreStmt_Obtain obtain
    wk: "is_well_kinded env varTy"
    by (auto simp: Let_def split: if_splits)
  from tyenv_well_formed_add_ghost_var[OF assms(2) wk]
  have wf': "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                      TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>)" .
  from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf']
  have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                 TE_GhostLocals := finsert varName (TE_GhostLocals env) \<rparr>
                              \<lparr> TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>)" .
  with assms CoreStmt_Obtain show ?thesis
    by (auto simp: Let_def split: if_splits)
next
  case (CoreStmt_Use witnessTm)
  from assms CoreStmt_Use obtain bodyTm where
    env'_eq: "env' = env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  from tyenv_well_formed_TE_ProofGoal_irrelevant[OF assms(2)]
  show ?thesis unfolding env'_eq .
next
  case (CoreStmt_Swap _ _ _)
  with assms have "env' = env" by (auto split: if_splits option.splits)
  with assms show ?thesis by simp
next
  case (CoreStmt_Return _)
  with assms have "env' = env" by (auto split: if_splits)
  with assms show ?thesis by simp
next
  case (CoreStmt_Assert _ _)
  with assms have "env' = env" by (auto simp: Let_def split: if_splits option.splits)
  with assms show ?thesis by simp
next
  case (CoreStmt_Assume _)
  with assms have "env' = env" by (auto split: if_splits)
  with assms show ?thesis by simp
next
  case (CoreStmt_While _ _ _ _ _)
  with assms have "env' = env" by (auto split: if_splits option.splits CoreType.splits)
  with assms show ?thesis by simp
next
  case (CoreStmt_Match _ _ _)
  with assms have "env' = env" by (auto simp: Let_def split: if_splits option.splits)
  with assms show ?thesis by simp
next
  case (CoreStmt_ShowHide _ _)
  with assms have "env' = env" by simp
  with assms show ?thesis by simp
qed

(* core_statement_type preserves TE_ReturnType *)
lemma core_statement_type_preserves_return_type:
  assumes "core_statement_type env ghost stmt = Some env'"
  shows "TE_ReturnType env' = TE_ReturnType env"
using assms proof (cases stmt)
  case (CoreStmt_VarDecl declGhost varName varOrRef varTy initTm)
  show ?thesis proof (cases varOrRef)
    case Var
    with assms CoreStmt_VarDecl show ?thesis by (auto split: if_splits)
  next
    case Ref
    with assms CoreStmt_VarDecl show ?thesis by (auto split: if_splits)
  qed
next
  case (CoreStmt_Assign assignGhost lhsTm rhsTm)
  with assms show ?thesis by (auto split: if_splits option.splits)
next
  case (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms)
  with assms show ?thesis by (auto split: if_splits option.splits)
next
  case (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
  with assms show ?thesis by (auto split: if_splits option.splits)
next
  case (CoreStmt_Fix _ _) with assms show ?thesis
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
next
  case (CoreStmt_Obtain _ _ _) with assms show ?thesis
    by (auto simp: Let_def split: if_splits)
next
  case (CoreStmt_Use _) with assms show ?thesis
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
next
  case (CoreStmt_Swap _ _ _)
  with assms show ?thesis by (auto split: if_splits option.splits)
next
  case (CoreStmt_Return _)
  with assms show ?thesis by (auto split: if_splits)
next
  case (CoreStmt_Assert _ _)
  with assms show ?thesis by (auto simp: Let_def split: if_splits option.splits)
next
  case (CoreStmt_Assume _)
  with assms show ?thesis by (auto split: if_splits)
next
  case (CoreStmt_While _ _ _ _ _)
  with assms show ?thesis by (auto split: if_splits option.splits CoreType.splits)
next
  case (CoreStmt_Match _ _ _)
  with assms show ?thesis by (auto simp: Let_def split: if_splits option.splits)
next
  case (CoreStmt_ShowHide _ _)
  with assms show ?thesis by simp
qed

(* core_statement_list_type preserves TE_ReturnType *)
lemma core_statement_list_type_preserves_return_type:
  assumes "core_statement_list_type env ghost stmts = Some env'"
  shows "TE_ReturnType env' = TE_ReturnType env"
using assms proof (induction stmts arbitrary: env)
  case Nil
  then show ?case by simp
next
  case (Cons stmt stmts)
  from Cons.prems obtain env_mid where
    mid: "core_statement_type env ghost stmt = Some env_mid" and
    rest: "core_statement_list_type env_mid ghost stmts = Some env'"
    by (auto split: option.splits)
  from core_statement_type_preserves_return_type[OF mid]
  have "TE_ReturnType env_mid = TE_ReturnType env" .
  with Cons.IH[OF rest] show ?case by simp
qed

(* core_statement_list_type preserves tyenv_well_formed *)
lemma core_statement_list_type_preserves_well_formed:
  assumes "core_statement_list_type env ghost stmts = Some env'"
    and "tyenv_well_formed env"
  shows "tyenv_well_formed env'"
using assms proof (induction stmts arbitrary: env)
  case Nil
  then show ?case by simp
next
  case (Cons stmt stmts)
  from Cons.prems obtain env_mid where
    mid: "core_statement_type env ghost stmt = Some env_mid" and
    rest: "core_statement_list_type env_mid ghost stmts = Some env'"
    by (auto split: option.splits)
  from core_statement_type_preserves_well_formed[OF mid Cons.prems(2)]
  have "tyenv_well_formed env_mid" .
  from Cons.IH[OF rest this] show ?case .
qed


(* ========================================================================== *)
(* Fixed fields: typechecking preserves the fixed fields of the environment   *)
(* ========================================================================== *)

lemma core_statement_type_fixed_eq:
  assumes "core_statement_type env ghost stmt = Some env'"
  shows "tyenv_fixed_eq env env'"
using assms proof (cases stmt)
  case (CoreStmt_VarDecl declGhost varName varOrRef varTy initTm)
  show ?thesis proof (cases varOrRef)
    case Var
    from assms CoreStmt_VarDecl Var have env'_eq:
      "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                    TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env)
                                     else fminus (TE_GhostLocals env) {|varName|}),
                    TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
      by (auto split: if_splits)
    show ?thesis unfolding env'_eq tyenv_fixed_eq_def by simp
  next
    case Ref
    from assms CoreStmt_VarDecl Ref have env'_eq:
      "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                    TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env)
                                     else fminus (TE_GhostLocals env) {|varName|}),
                    TE_ConstLocals := (if is_writable_lvalue env initTm
                                      then fminus (TE_ConstLocals env) {|varName|}
                                      else finsert varName (TE_ConstLocals env)) \<rparr>"
      by (auto split: if_splits)
    show ?thesis unfolding env'_eq tyenv_fixed_eq_def by simp
  qed
next
  case (CoreStmt_Assign assignGhost lhsTm rhsTm)
  with assms have "env' = env" by (auto split: if_splits option.splits)
  thus ?thesis by (simp add: tyenv_fixed_eq_refl)
next
  case (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms)
  with assms have "env' = env" by (auto split: if_splits option.splits)
  thus ?thesis by (simp add: tyenv_fixed_eq_refl)
next
  case (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
  from assms CoreStmt_VarDeclCall have env'_eq:
    "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := (if declGhost = Ghost
                                   then finsert varName (TE_GhostLocals env)
                                   else fminus (TE_GhostLocals env) {|varName|}),
                  TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits option.splits)
  show ?thesis unfolding env'_eq tyenv_fixed_eq_def by simp
next
  case (CoreStmt_Fix varName varTy)
  from assms CoreStmt_Fix obtain bodyTm where
    "env' = env \<lparr> TE_LocalVars   := fmupd varName varTy (TE_LocalVars env),
                   TE_GhostLocals := finsert varName (TE_GhostLocals env),
                   TE_ConstLocals := finsert varName (TE_ConstLocals env),
                   TE_ProofGoal   := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  thus ?thesis unfolding tyenv_fixed_eq_def by simp
next
  case (CoreStmt_Obtain varName varTy condTm)
  from assms CoreStmt_Obtain have env'_eq:
    "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := finsert varName (TE_GhostLocals env),
                  TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto simp: Let_def split: if_splits)
  show ?thesis unfolding env'_eq tyenv_fixed_eq_def by simp
next
  case (CoreStmt_Use witnessTm)
  from assms CoreStmt_Use obtain bodyTm where
    "env' = env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  thus ?thesis unfolding tyenv_fixed_eq_def by simp
next
  case (CoreStmt_Swap _ _ _)
  with assms have "env' = env" by (auto split: if_splits option.splits)
  thus ?thesis by (simp add: tyenv_fixed_eq_refl)
next
  case (CoreStmt_Return _)
  with assms have "env' = env" by (auto split: if_splits)
  thus ?thesis by (simp add: tyenv_fixed_eq_refl)
next
  case (CoreStmt_Assert _ _)
  with assms have "env' = env" by (auto simp: Let_def split: if_splits option.splits)
  thus ?thesis by (simp add: tyenv_fixed_eq_refl)
next
  case (CoreStmt_Assume _)
  with assms have "env' = env" by (auto split: if_splits)
  thus ?thesis by (simp add: tyenv_fixed_eq_refl)
next
  case (CoreStmt_While _ _ _ _ _)
  with assms have "env' = env" by (auto split: if_splits option.splits CoreType.splits)
  thus ?thesis by (simp add: tyenv_fixed_eq_refl)
next
  case (CoreStmt_Match _ _ _)
  with assms have "env' = env" by (auto simp: Let_def split: if_splits option.splits)
  thus ?thesis by (simp add: tyenv_fixed_eq_refl)
next
  case (CoreStmt_ShowHide _ _)
  with assms have "env' = env" by simp
  thus ?thesis by (simp add: tyenv_fixed_eq_refl)
qed

lemma core_statement_list_type_fixed_eq:
  assumes "core_statement_list_type env ghost stmts = Some env'"
  shows "tyenv_fixed_eq env env'"
using assms proof (induction stmts arbitrary: env)
  case Nil
  then show ?case by (simp add: tyenv_fixed_eq_refl)
next
  case (Cons stmt stmts)
  from Cons.prems obtain env_mid where
    mid: "core_statement_type env ghost stmt = Some env_mid" and
    rest: "core_statement_list_type env_mid ghost stmts = Some env'"
    by (auto split: option.splits)
  from core_statement_type_fixed_eq[OF mid]
  have "tyenv_fixed_eq env env_mid" .
  with tyenv_fixed_eq_trans Cons.IH[OF rest] show ?case by blast
qed


(* ========================================================================== *)
(* Tyvar weakening for statements                                             *)
(*                                                                            *)
(* Adding (unused) type variables to the environment does not change what     *)
(* core_statement_type accepts; the resulting environment is the original     *)
(* result with the same extra type variables added. This mirrors              *)
(* core_term_type_irrelevant_tyvar (CoreTypecheck.thy). The variant phrased    *)
(* with extend_env_with_tyvars is in ExtendEnvWithTyvars.thy (which imports    *)
(* this theory).                                                              *)
(*                                                                            *)
(* Embedded checks are handled as follows: terms via                          *)
(* core_term_type_irrelevant_tyvar; impure calls via                          *)
(* core_impure_call_type_irrelevant_tyvar; types via is_well_kinded_extend_   *)
(* tyvars / is_runtime_type_extend_runtime_tyvars; writability via            *)
(* is_writable_lvalue_irrelevant_tyvar; pattern compatibility via             *)
(* pattern_compatible_cong_env; the purely syntactic is_lvalue and the        *)
(* env-free is_valid_decreases_type are unchanged. For VarDecl / Obtain / Fix *)
(* the local-variable record updates commute with the tyvar-set update, so    *)
(* the result env carries the extras through unchanged.                       *)
(* ========================================================================== *)

lemma core_statement_type_irrelevant_tyvar:
  "core_statement_type env ghost stmt = Some env' \<Longrightarrow>
   core_statement_type
     (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
            TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>) ghost stmt
   = Some (env' \<lparr> TE_TypeVars := TE_TypeVars env' |\<union>| extraTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env' |\<union>| extraRT \<rparr>)"
and core_statement_list_type_irrelevant_tyvar:
  "core_statement_list_type env ghost stmts = Some env' \<Longrightarrow>
   core_statement_list_type
     (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
            TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>) ghost stmts
   = Some (env' \<lparr> TE_TypeVars := TE_TypeVars env' |\<union>| extraTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env' |\<union>| extraRT \<rparr>)"
proof (induction env ghost stmt and env ghost stmts
       arbitrary: env' and env'
       rule: core_statement_type_core_statement_list_type.induct)
  \<comment> \<open>Local shorthand for "add the extra type variables": ?ext e adds extraTV /
      extraRT to e's tyvar sets. It only touches TE_TypeVars / TE_RuntimeTypeVars,
      so it commutes with every other record update below.\<close>
  \<comment> \<open>VarDecl (Var): adds a local; the local-var updates commute with ?ext.\<close>
  case (1 env ghost declGhost varName varTy initTm)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  from "1.prems" have conds:
    "(ghost = Ghost \<longrightarrow> declGhost = Ghost)
       \<and> is_well_kinded env varTy
       \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
       \<and> core_term_type env declGhost initTm = Some varTy"
    by (auto split: if_splits)
  hence wk: "is_well_kinded ?env1 varTy"
    using is_well_kinded_extend_tyvars by fastforce
  from conds have rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?env1 varTy"
    using is_runtime_type_extend_runtime_tyvars by fastforce
  from conds have rhs:
    "core_term_type ?env1 declGhost initTm = Some varTy"
    using core_term_type_irrelevant_tyvar by blast
  from "1.prems" conds have env'_eq:
    "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := (if declGhost = Ghost
                                   then finsert varName (TE_GhostLocals env)
                                   else fminus (TE_GhostLocals env) {|varName|}),
                  TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits)
  from conds wk rt rhs show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>VarDeclCall: adds a local of the (optionally cast) call return type. The
      call check and cast both survive ?ext; local-var updates commute with it.\<close>
  case (2 env ghost declGhost varName varTy castOpt fnName tyArgs argTms)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  from "2.prems" obtain retTy where
    gh: "ghost = Ghost \<longrightarrow> declGhost = Ghost" and
    wk: "is_well_kinded env varTy" and
    rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    ct: "core_impure_call_type env declGhost fnName tyArgs argTms = Some retTy" and
    cast: "cast_result_type env declGhost retTy castOpt = Some varTy" and
    env'_eq:
      "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                    TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env)
                                     else fminus (TE_GhostLocals env) {|varName|}),
                    TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits option.splits)
  have wk': "is_well_kinded ?env1 varTy"
    using wk is_well_kinded_extend_tyvars by fastforce
  have rt': "declGhost = NotGhost \<longrightarrow> is_runtime_type ?env1 varTy"
    using rt is_runtime_type_extend_runtime_tyvars by fastforce
  have ct': "core_impure_call_type ?env1 declGhost fnName tyArgs argTms = Some retTy"
    using ct core_impure_call_type_irrelevant_tyvar by blast
  have cast': "cast_result_type ?env1 declGhost retTy castOpt = Some varTy"
    using cast cast_result_type_irrelevant_tyvar by blast
  from gh wk' rt' ct' cast' show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>VarDecl (Ref): the rhs must be an lvalue; same commutation.\<close>
  case (3 env ghost declGhost varName varTy initTm)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  from "3.prems" have conds:
    "(ghost = Ghost \<longrightarrow> declGhost = Ghost)
       \<and> is_well_kinded env varTy
       \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
       \<and> is_lvalue initTm
       \<and> core_term_type env declGhost initTm = Some varTy"
    by (auto split: if_splits)
  hence wk: "is_well_kinded ?env1 varTy"
    using is_well_kinded_extend_tyvars by fastforce
  from conds have rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type ?env1 varTy"
    using is_runtime_type_extend_runtime_tyvars by fastforce
  from conds have rhs: "core_term_type ?env1 declGhost initTm = Some varTy"
    using core_term_type_irrelevant_tyvar by blast
  from "3.prems" conds have env'_eq:
    "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                  TE_GhostLocals := (if declGhost = Ghost
                                   then finsert varName (TE_GhostLocals env)
                                   else fminus (TE_GhostLocals env) {|varName|}),
                  TE_ConstLocals := (if is_writable_lvalue env initTm
                                    then fminus (TE_ConstLocals env) {|varName|}
                                    else finsert varName (TE_ConstLocals env)) \<rparr>"
    by (auto split: if_splits)
  from conds wk rt rhs show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>Assign: env unchanged.\<close>
  case (4 env ghost assignGhost lhsTm rhsTm)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  from "4.prems" obtain lhsTy where
    wl: "is_writable_lvalue env lhsTm" and
    gh: "ghost = Ghost \<longrightarrow> assignGhost = Ghost" and
    lhs: "core_term_type env assignGhost lhsTm = Some lhsTy" and
    rhs: "core_term_type env assignGhost rhsTm = Some lhsTy" and
    env'_eq: "env' = env"
    by (auto split: if_splits option.splits)
  let ?env1 = "?ext env"
  have lhs': "core_term_type ?env1 assignGhost lhsTm = Some lhsTy"
    using lhs core_term_type_irrelevant_tyvar by blast
  have rhs': "core_term_type ?env1 assignGhost rhsTm = Some lhsTy"
    using rhs core_term_type_irrelevant_tyvar by blast
  from gh wl lhs' rhs' show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>AssignCall: env unchanged. The call check and cast both survive ?ext.\<close>
  case (5 env ghost assignGhost lhsTm castOpt fnName tyArgs argTms)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  from "5.prems" have
    pre: "(ghost = Ghost \<longrightarrow> assignGhost = Ghost) \<and> is_writable_lvalue env lhsTm"
    by (simp split: if_splits)
  hence gh: "ghost = Ghost \<longrightarrow> assignGhost = Ghost" and wl: "is_writable_lvalue env lhsTm"
    by simp_all
  from "5.prems" pre obtain lhsTy where
    lhs: "core_term_type env assignGhost lhsTm = Some lhsTy"
    by (simp split: option.splits)
  from "5.prems" pre lhs obtain retTy where
    ct: "core_impure_call_type env assignGhost fnName tyArgs argTms = Some retTy"
    by (simp split: option.splits)
  from "5.prems" pre lhs ct have
    cast: "cast_result_type env assignGhost retTy castOpt = Some lhsTy" and
    env'_eq: "env' = env"
    by (simp split: if_splits)+
  have lhs': "core_term_type ?env1 assignGhost lhsTm = Some lhsTy"
    using lhs core_term_type_irrelevant_tyvar by blast
  have ct': "core_impure_call_type ?env1 assignGhost fnName tyArgs argTms = Some retTy"
    using ct core_impure_call_type_irrelevant_tyvar by blast
  have cast': "cast_result_type ?env1 assignGhost retTy castOpt = Some lhsTy"
    using cast cast_result_type_irrelevant_tyvar by blast
  from gh wl lhs' ct' cast' show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>Return: env unchanged. TE_ReturnType / TE_FunctionGhost survive ?ext.\<close>
  case (6 env ghost tm)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  from "6.prems" have
    gh: "ghost = TE_FunctionGhost env" and
    tm: "core_term_type env ghost tm = Some (TE_ReturnType env)" and
    env'_eq: "env' = env"
    by (auto split: if_splits)
  let ?env1 = "?ext env"
  have tm': "core_term_type ?env1 ghost tm = Some (TE_ReturnType env)"
    using tm core_term_type_irrelevant_tyvar by blast
  from gh tm' show ?case by (simp add: env'_eq)
next
  \<comment> \<open>Swap: env unchanged.\<close>
  case (7 env ghost swapGhost lhsTm rhsTm)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  from "7.prems" obtain lhsTy where
    gh: "ghost = Ghost \<longrightarrow> swapGhost = Ghost" and
    wl: "is_writable_lvalue env lhsTm" and
    wr: "is_writable_lvalue env rhsTm" and
    lhs: "core_term_type env swapGhost lhsTm = Some lhsTy" and
    rhs: "core_term_type env swapGhost rhsTm = Some lhsTy" and
    env'_eq: "env' = env"
    by (auto split: if_splits option.splits)
  let ?env1 = "?ext env"
  have lhs': "core_term_type ?env1 swapGhost lhsTm = Some lhsTy"
    using lhs core_term_type_irrelevant_tyvar by blast
  have rhs': "core_term_type ?env1 swapGhost rhsTm = Some lhsTy"
    using rhs core_term_type_irrelevant_tyvar by blast
  from gh wl wr lhs' rhs' show ?case by (simp add: env'_eq)
next
  \<comment> \<open>Assert: env unchanged; body checked under goalEnv, which installs
      TE_ProofGoal := Some condTm when a condition is present, or leaves env
      unchanged for "assert *" (condOpt = None). ?ext commutes with goalEnv.\<close>
  case (8 env ghost condOpt proofBody)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  let ?goalEnv = "\<lambda>e. case condOpt of Some condTm \<Rightarrow> e \<lparr> TE_ProofGoal := Some condTm \<rparr>
                                     | None \<Rightarrow> e"
  let ?condOk = "case condOpt of Some condTm \<Rightarrow> core_term_type env Ghost condTm = Some CoreTy_Bool
                               | None \<Rightarrow> True"
  from "8.prems" obtain bodyEnv where
    condOk: "?condOk" and
    body: "core_statement_list_type (?goalEnv env) Ghost proofBody = Some bodyEnv" and
    env'_eq: "env' = env"
    by (auto simp: Let_def split: if_splits option.splits)
  \<comment> \<open>?ext commutes with the goal-env update, in either branch of condOpt.\<close>
  have shape: "?ext (?goalEnv env) = ?goalEnv ?env1"
    by (cases condOpt) simp_all
  from "8.IH"[OF refl refl condOk body] shape have body':
    "core_statement_list_type (?goalEnv ?env1) Ghost proofBody = Some (?ext bodyEnv)"
    by argo
  \<comment> \<open>The condition (if any) still typechecks under the extended env.\<close>
  have condOk': "case condOpt of
                   Some condTm \<Rightarrow> core_term_type ?env1 Ghost condTm = Some CoreTy_Bool
                 | None \<Rightarrow> True"
    using condOk core_term_type_irrelevant_tyvar by (cases condOpt) auto
  from condOk' body' show ?case by (simp add: env'_eq Let_def)
next
  \<comment> \<open>Assume: env unchanged.\<close>
  case (9 env ghost tm)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  from "9.prems" have
    tm: "core_term_type env Ghost tm = Some CoreTy_Bool" and env'_eq: "env' = env"
    by (auto split: if_splits)
  let ?env1 = "?ext env"
  have tm': "core_term_type ?env1 Ghost tm = Some CoreTy_Bool"
    using tm core_term_type_irrelevant_tyvar by blast
  from tm' show ?case by (simp add: env'_eq)
next
  \<comment> \<open>ShowHide: env unchanged, no embedded checks.\<close>
  case (10 env ghost sh name)
  from "10.prems" have "env' = env" by simp
  thus ?case by simp
next
  \<comment> \<open>Match: env unchanged; pattern_compatible depends only on TE_DataCtors, and
      each arm body is checked under TE_ProofGoal := None.\<close>
  case (11 env ghost matchGhost scrut arms)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  from "11.prems" obtain scrutTy where
    gh: "ghost = Ghost \<longrightarrow> matchGhost = Ghost" and
    scrut: "core_term_type env matchGhost scrut = Some scrutTy" and
    pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    bodies: "list_all (\<lambda>body. core_statement_list_type (env \<lparr> TE_ProofGoal := None \<rparr>)
                                  matchGhost body \<noteq> None) (map snd arms)" and
    env'_eq: "env' = env"
    by (auto simp: Let_def split: if_splits option.splits)
  have scrut': "core_term_type ?env1 matchGhost scrut = Some scrutTy"
    using scrut core_term_type_irrelevant_tyvar by blast
  have dc_eq: "TE_DataCtors ?env1 = TE_DataCtors env" by simp
  have pats': "list_all (\<lambda>p. pattern_compatible ?env1 p scrutTy) (map fst arms)"
    using pats pattern_compatible_cong_env[OF dc_eq] by (simp add: list_all_iff)
  \<comment> \<open>The double-negated form of pats, as it appears in the IH premises.\<close>
  have pats_nn: "\<not> \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)"
    using pats by simp
  \<comment> \<open>Each arm body still typechecks (to *some* env) under the extended env.
      ?ext commutes with the TE_ProofGoal := None update.\<close>
  have goal_shape: "?ext (env \<lparr> TE_ProofGoal := None \<rparr>)
                      = ?env1 \<lparr> TE_ProofGoal := None \<rparr>" by simp
  have bodies': "list_all (\<lambda>body. core_statement_list_type (?env1 \<lparr> TE_ProofGoal := None \<rparr>)
                                     matchGhost body \<noteq> None) (map snd arms)"
    unfolding list_all_iff
  proof (rule ballI)
    fix body assume body_in: "body \<in> set (map snd arms)"
    with bodies have "core_statement_list_type (env \<lparr> TE_ProofGoal := None \<rparr>) matchGhost body \<noteq> None"
      by (metis (mono_tags, lifting) in_set_conv_decomp list_all_append list_all_simps(1))
    then obtain bEnv where
      bsome: "core_statement_list_type (env \<lparr> TE_ProofGoal := None \<rparr>) matchGhost body = Some bEnv"
      by blast
    from "11.IH"[OF gh scrut refl refl pats_nn body_in bsome] goal_shape
    have "core_statement_list_type (?env1 \<lparr> TE_ProofGoal := None \<rparr>) matchGhost body
            = Some (?ext bEnv)"
      by argo
    thus "core_statement_list_type (?env1 \<lparr> TE_ProofGoal := None \<rparr>) matchGhost body \<noteq> None"
      by simp
  qed
  from gh scrut' pats' bodies' show ?case
    by (simp add: env'_eq Let_def)
next
  \<comment> \<open>While: env unchanged; condition / invariants / decreases are terms, body is a list.\<close>
  case (12 env ghost whileGhost condTm invars decrTm body)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  from "12.prems" obtain decrTy bodyEnv where
    gh: "ghost = Ghost \<longrightarrow> whileGhost = Ghost" and
    cond: "core_term_type env whileGhost condTm = Some CoreTy_Bool" and
    invs: "list_all (\<lambda>inv. core_term_type env Ghost inv = Some CoreTy_Bool) invars" and
    decr: "core_term_type env Ghost decrTm = Some decrTy" and
    decr_valid: "is_valid_decreases_type decrTy" and
    body: "core_statement_list_type (env \<lparr> TE_ProofGoal := None \<rparr>) whileGhost body = Some bodyEnv" and
    env'_eq: "env' = env"
    by (auto split: if_splits option.splits CoreType.splits)
  have cond': "core_term_type ?env1 whileGhost condTm = Some CoreTy_Bool"
    using cond core_term_type_irrelevant_tyvar by blast
  have invs': "list_all (\<lambda>inv. core_term_type ?env1 Ghost inv = Some CoreTy_Bool) invars"
    using invs core_term_type_irrelevant_tyvar by (simp add: list_all_iff)
  have decr': "core_term_type ?env1 Ghost decrTm = Some decrTy"
    using decr core_term_type_irrelevant_tyvar by blast
  have goal_shape: "?ext (env \<lparr> TE_ProofGoal := None \<rparr>)
                      = ?env1 \<lparr> TE_ProofGoal := None \<rparr>" by simp
  from "12.IH"[OF gh cond refl invs decr decr_valid body] goal_shape have body':
    "core_statement_list_type (?env1 \<lparr> TE_ProofGoal := None \<rparr>) whileGhost body
       = Some (?ext bodyEnv)"
    by argo
  from gh cond' invs' decr' decr_valid body' show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>Obtain: adds a ghost local; condTm checked under the extended env.\<close>
  case (13 env ghost varName varTy condTm)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  let ?envX = "\<lambda>e. e \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars e),
                        TE_GhostLocals := finsert varName (TE_GhostLocals e),
                        TE_ConstLocals := fminus (TE_ConstLocals e) {|varName|} \<rparr>"
  from "13.prems" have
    wk: "is_well_kinded env varTy" and
    cond: "core_term_type (?envX env) Ghost condTm = Some CoreTy_Bool" and
    env'_eq: "env' = ?envX env"
    by (auto simp: Let_def split: if_splits)
  have wk': "is_well_kinded ?env1 varTy"
    using wk is_well_kinded_extend_tyvars by fastforce
  have shape: "?ext (?envX env) = ?envX ?env1" by simp
  have "core_term_type (?ext (?envX env)) Ghost condTm = Some CoreTy_Bool"
    using cond core_term_type_irrelevant_tyvar by blast
  hence cond': "core_term_type (?envX ?env1) Ghost condTm = Some CoreTy_Bool"
    by (simp only: shape)
  from wk' cond' show ?case
    by (simp add: env'_eq Let_def)
next
  \<comment> \<open>Fix: requires a Quant_Forall goal; adds a ghost const local and updates the goal.\<close>
  case (14 env ghost varName varTy)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  from "14.prems" obtain qName bodyTm where
    goal: "TE_ProofGoal env = Some (CoreTm_Quantifier Quant_Forall qName varTy bodyTm)" and
    gh: "ghost = Ghost" and wk: "is_well_kinded env varTy" and
    env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                            TE_GhostLocals := finsert varName (TE_GhostLocals env),
                            TE_ConstLocals := finsert varName (TE_ConstLocals env),
                            TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  let ?env1 = "?ext env"
  have goal': "TE_ProofGoal ?env1 = Some (CoreTm_Quantifier Quant_Forall qName varTy bodyTm)"
    using goal by simp
  have wk': "is_well_kinded ?env1 varTy"
    using wk is_well_kinded_extend_tyvars by fastforce
  from gh goal' wk' show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>Use: requires a Quant_Exists goal; updates the goal, env otherwise unchanged.\<close>
  case (15 env ghost witnessTm)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  from "15.prems" obtain qName qVarTy bodyTm where
    goal: "TE_ProofGoal env = Some (CoreTm_Quantifier Quant_Exists qName qVarTy bodyTm)" and
    gh: "ghost = Ghost" and
    wit: "core_term_type env ghost witnessTm = Some qVarTy" and
    env'_eq: "env' = env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  let ?env1 = "?ext env"
  have goal': "TE_ProofGoal ?env1 = Some (CoreTm_Quantifier Quant_Exists qName qVarTy bodyTm)"
    using goal by simp
  have wit': "core_term_type ?env1 ghost witnessTm = Some qVarTy"
    using wit core_term_type_irrelevant_tyvar by blast
  from gh goal' wit' show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>Empty statement list.\<close>
  case (16 env ghost)
  from "16.prems" have "env' = env" by simp
  thus ?case by simp
next
  \<comment> \<open>Cons: thread the env through head then tail.\<close>
  case (17 env ghost stmt stmts)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  from "17.prems" obtain envMid where
    head: "core_statement_type env ghost stmt = Some envMid" and
    tail: "core_statement_list_type envMid ghost stmts = Some env'"
    by (auto split: option.splits)
  from "17.IH"(1)[OF head] have head':
    "core_statement_type (?ext env) ghost stmt
       = Some (?ext envMid)" .
  from "17.IH"(2)[OF head tail] have tail':
    "core_statement_list_type (?ext envMid) ghost stmts
       = Some (?ext env')" .
  from head' tail' show ?case by simp
qed

end


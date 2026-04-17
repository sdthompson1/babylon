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

definition core_impure_call_type :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreTerm \<Rightarrow> CoreType option" where
  "core_impure_call_type env ghost tm =
    (case tm of
       CoreTm_FunctionCall fnName tyArgs tmArgs \<Rightarrow>
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
                   else None)
     | _ \<Rightarrow> None)"


(* A convenient corollary of core_impure_call_type = Some: the function is
   looked up, and every argument term typechecks to *some* type via
   core_term_type. This is enough for several downstream proofs (erasure,
   fuel-monotonicity, preservation) that only need to know the arguments are
   well-typed rather than the full Var/Ref-respecting check. *)
lemma core_impure_call_type_args_typed:
  assumes "core_impure_call_type env ghost tm = Some ty"
      and "tm = CoreTm_FunctionCall fnName tyArgs tmArgs"
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
  assumes "core_impure_call_type env ghost tm = Some ty"
      and "tm = CoreTm_FunctionCall fnName tyArgs tmArgs"
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
     The rhs may be an impure function call at the outermost position; nested
     calls must still be pure (handled by core_term_type). *)
  "core_statement_type env ghost (CoreStmt_VarDecl declGhost varName Var varTy initTm) =
    (if (ghost = Ghost \<longrightarrow> declGhost = Ghost)
        \<and> is_well_kinded env varTy
        \<and> (declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy)
        \<and> (core_impure_call_type env declGhost initTm = Some varTy
           \<or> core_term_type env declGhost initTm = Some varTy)
     then Some (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                      TE_GhostLocals := (if declGhost = Ghost
                                       then finsert varName (TE_GhostLocals env)
                                       else fminus (TE_GhostLocals env) {|varName|}),
                      TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>)
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
     The rhs may be an impure function call at the outermost position; nested
     calls must still be pure (handled by core_term_type). *)
| "core_statement_type env ghost (CoreStmt_Assign assignGhost lhsTm rhsTm) =
    (if (ghost = Ghost \<longrightarrow> assignGhost = Ghost)
        \<and> is_writable_lvalue env lhsTm
     then (case core_term_type env assignGhost lhsTm of
             Some lhsTy \<Rightarrow>
               if core_impure_call_type env assignGhost rhsTm = Some lhsTy
                  \<or> core_term_type env assignGhost rhsTm = Some lhsTy
               then Some env
               else None
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

  (* Assert: condition must be bool; proof body typechecks in Ghost context *)
| "core_statement_type env ghost (CoreStmt_Assert condTm proofBody) =
    (if core_term_type env Ghost condTm = Some CoreTy_Bool
     then (case core_statement_list_type env Ghost proofBody of
             Some _ \<Rightarrow> Some env
           | None \<Rightarrow> None)
     else None)"

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
                  else if \<not> patterns_regular pats then None
                  else if list_all (\<lambda>body. core_statement_list_type env matchGhost body \<noteq> None) bodies
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
                         then (case core_statement_list_type env whileGhost body of
                                 Some _ \<Rightarrow> Some env
                               | None \<Rightarrow> None)
                         else None
                     | None \<Rightarrow> None)
               else None
           | _ \<Rightarrow> None)
     else None)"

  (* TODO: remaining statement forms *)
| "core_statement_type _ _ (CoreStmt_Fix _ _) = undefined"
| "core_statement_type _ _ (CoreStmt_Obtain _ _ _) = undefined"
| "core_statement_type _ _ (CoreStmt_Use _) = undefined"

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
    show "(Inr (env, matchGhost, z),
           Inl (env, ghost, CoreStmt_Match matchGhost scrut arms))
          \<in> measure (\<lambda>y. case y of
              Inl (_, _, stmt) \<Rightarrow> size stmt
            | Inr (_, _, stmts) \<Rightarrow> size_list size stmts)"
      using z_le by simp
  qed


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
  case (CoreStmt_Fix _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Obtain _ _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Use _) with assms show ?thesis sorry
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
  with assms have "env' = env" by (auto split: if_splits option.splits)
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
  case (CoreStmt_Fix _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Obtain _ _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Use _) with assms show ?thesis sorry
next
  case (CoreStmt_Swap _ _ _)
  with assms show ?thesis by (auto split: if_splits option.splits)
next
  case (CoreStmt_Return _)
  with assms show ?thesis by (auto split: if_splits)
next
  case (CoreStmt_Assert _ _)
  with assms show ?thesis by (auto split: if_splits option.splits)
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
  case (CoreStmt_Fix _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Obtain _ _ _) with assms show ?thesis sorry
next
  case (CoreStmt_Use _) with assms show ?thesis sorry
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
  with assms have "env' = env" by (auto split: if_splits option.splits)
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

end


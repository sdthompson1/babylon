theory CoreStmtTypecheckLemmas
  imports CoreStmtTypecheck CoreTypecheckLemmas
begin

(* ========================================================================== *)
(* Typechecking of impure calls and casts *)
(* ========================================================================== *)

(* cast_result_type in any mode implies cast_result_type in Ghost mode. *)
lemma cast_result_type_imp_Ghost:
  assumes "cast_result_type env ghost retTy castOpt = Some ty"
  shows "cast_result_type env Ghost retTy castOpt = Some ty"
  using assms by (auto simp: cast_result_type_def split: option.splits if_splits)

(* Various facts that follow from core_impure_call_type being Some, including
   a list_all2 relating each argument type to its expected type via core_term_type. *)
lemma core_impure_call_type_fn_facts:
  assumes "core_impure_call_type env ghost fnName tyArgs tmArgs = Some ty"
  shows "\<exists>funInfo.
            fmlookup (TE_Functions env) fnName = Some funInfo
            \<and> length tyArgs = length (FI_TyArgs funInfo)
            \<and> list_all (is_well_kinded env) tyArgs
            \<and> list_all is_complete_type tyArgs
            \<and> (ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs)
            \<and> (ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost)
            \<and> length tmArgs = length (FI_TmArgs funInfo)
            \<and> ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                               (FI_ReturnType funInfo)
            \<and> list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) tmArgs
                (zip (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                          (FI_TmArgs funInfo))
                     (map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)))
            \<and> (\<forall>i < length tmArgs.
                 fst (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i)
                       \<and> ghost_lvalue_ok env (param_mode ghost (snd (snd (FI_TmArgs funInfo ! i))))
                                          (tmArgs ! i))
            \<and> (FI_Impure funInfo \<longrightarrow> ghost = NotGhost \<and> TE_FunctionImpure env)"
proof -
  from assms obtain fi where
    fi_lookup: "fmlookup (TE_Functions env) fnName = Some fi"
    by (auto simp: core_impure_call_type_def split: option.splits)
  let ?tySubst = "fmap_of_list (zip (FI_TyArgs fi) tyArgs)"
  let ?vors = "map (\<lambda>(_, vor, _). vor) (FI_TmArgs fi)"
  let ?exps = "map (\<lambda>(ty, _). apply_subst ?tySubst ty) (FI_TmArgs fi)"
  let ?modes = "map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs fi)"
  from assms fi_lookup have
    len_tyArgs: "length tyArgs = length (FI_TyArgs fi)" and
    tyArgs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyArgs_cp: "list_all is_complete_type tyArgs" and
    not_ghost_cond: "\<not> (ghost = NotGhost
                        \<and> (\<not> list_all (is_runtime_type env) tyArgs \<or> FI_Ghost fi = Ghost))" and
    not_impure_cond: "\<not> (FI_Impure fi \<and> (ghost = Ghost \<or> \<not> TE_FunctionImpure env))" and
    len_tmArgs: "length tmArgs = length (FI_TmArgs fi)" and
    argTms_l2_impure:
      "list_all2 (\<lambda>(tm, vor) (expectedTy, mode).
                    case vor of
                      Var \<Rightarrow>
                        core_term_type env mode tm = Some expectedTy
                    | Ref \<Rightarrow>
                        is_writable_lvalue env tm
                        \<and> ghost_lvalue_ok env mode tm
                        \<and> core_term_type env mode tm = Some expectedTy)
                 (zip tmArgs ?vors) (zip ?exps ?modes)" and
    fn_ty_eq: "ty = apply_subst ?tySubst (FI_ReturnType fi)"
    by (auto simp: core_impure_call_type_def Let_def split: if_splits)

  \<comment> \<open>Per-index view of the impure check, with the i-th parameter destructured. \<close>
  have nth_check:
    "\<And>i ti vor gh. i < length tmArgs \<Longrightarrow> FI_TmArgs fi ! i = (ti, vor, gh) \<Longrightarrow>
       (case vor of
          Var \<Rightarrow>
            core_term_type env (param_mode ghost gh) (tmArgs ! i)
              = Some (apply_subst ?tySubst ti)
        | Ref \<Rightarrow>
            is_writable_lvalue env (tmArgs ! i)
            \<and> ghost_lvalue_ok env (param_mode ghost gh) (tmArgs ! i)
            \<and> core_term_type env (param_mode ghost gh) (tmArgs ! i)
                = Some (apply_subst ?tySubst ti))"
  proof -
    fix i ti vor gh
    assume i_lt: "i < length tmArgs" and fi_arg_eq: "FI_TmArgs fi ! i = (ti, vor, gh)"
    with len_tmArgs have i_lt_fi: "i < length (FI_TmArgs fi)" by simp
    have i_lt_zip: "i < length (zip tmArgs ?vors)" using i_lt len_tmArgs by simp
    have zip_nth: "zip tmArgs ?vors ! i = (tmArgs ! i, vor)"
      using i_lt i_lt_fi fi_arg_eq by simp
    have expected_nth:
      "zip ?exps ?modes ! i = (apply_subst ?tySubst ti, param_mode ghost gh)"
      using i_lt_fi fi_arg_eq by simp
    show "(case vor of
             Var \<Rightarrow>
               core_term_type env (param_mode ghost gh) (tmArgs ! i) 
                 = Some (apply_subst ?tySubst ti)
           | Ref \<Rightarrow>
               is_writable_lvalue env (tmArgs ! i)
               \<and> ghost_lvalue_ok env (param_mode ghost gh) (tmArgs ! i)
               \<and> core_term_type env (param_mode ghost gh) (tmArgs ! i)
                   = Some (apply_subst ?tySubst ti))"
      using list_all2_nthD2[OF argTms_l2_impure, of i] i_lt_zip zip_nth expected_nth
      by simp
  qed

  \<comment> \<open>Derive the pure-shape check: every argument (whether Var or Ref)
      satisfies core_term_type ... = Some expectedTy in its own mode, because
      the impure check requires it in both branches. \<close>
  have argTms_l2_pure: "list_all2 (\<lambda>tm (expectedTy, mode).
                            core_term_type env mode tm = Some expectedTy) tmArgs (zip ?exps ?modes)"
    unfolding list_all2_case_prod_conv_all_nth
  proof (intro conjI allI impI)
    show "length tmArgs = length (zip ?exps ?modes)"
      using len_tmArgs by simp
  next
    fix i assume i_lt: "i < length tmArgs"
    with len_tmArgs have i_lt_fi: "i < length (FI_TmArgs fi)" by simp
    obtain ti vor gh where fi_arg_eq: "FI_TmArgs fi ! i = (ti, vor, gh)"
      by (cases "FI_TmArgs fi ! i") auto
    have expected_nth:
      "zip ?exps ?modes ! i = (apply_subst ?tySubst ti, param_mode ghost gh)"
      using i_lt_fi fi_arg_eq by simp
    show "core_term_type env (snd (zip ?exps ?modes ! i)) (tmArgs ! i)
            = Some (fst (zip ?exps ?modes ! i))"
      using nth_check[OF i_lt fi_arg_eq] expected_nth
      by (cases vor; auto split: option.splits)
  qed

  have ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs"
    using not_ghost_cond by blast
  have ng_fn: "ghost = NotGhost \<longrightarrow> FI_Ghost fi \<noteq> Ghost"
    using not_ghost_cond by blast

  \<comment> \<open>Extract the Ref-position lvalue and ghost-discipline witnesses from the
      impure list_all2. \<close>
  have ref_args_lvalues:
    "\<forall>i < length tmArgs.
       fst (snd (FI_TmArgs fi ! i)) = Ref
         \<longrightarrow> is_writable_lvalue env (tmArgs ! i)
             \<and> ghost_lvalue_ok env (param_mode ghost (snd (snd (FI_TmArgs fi ! i)))) (tmArgs ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < length tmArgs" and ref: "fst (snd (FI_TmArgs fi ! i)) = Ref"
    obtain ti vor gh where fi_arg_eq: "FI_TmArgs fi ! i = (ti, vor, gh)"
      by (cases "FI_TmArgs fi ! i") auto
    from ref fi_arg_eq have vor_eq: "vor = Ref" by simp
    from nth_check[OF i_lt fi_arg_eq] vor_eq fi_arg_eq
    show "is_writable_lvalue env (tmArgs ! i)
          \<and> ghost_lvalue_ok env (param_mode ghost (snd (snd (FI_TmArgs fi ! i)))) (tmArgs ! i)"
      by simp
  qed

  have impure_ok: "FI_Impure fi \<longrightarrow> ghost = NotGhost \<and> TE_FunctionImpure env"
    using not_impure_cond by (cases ghost) auto

  from fi_lookup len_tyArgs tyArgs_wk tyArgs_cp ng_tyArgs ng_fn len_tmArgs fn_ty_eq
       argTms_l2_pure ref_args_lvalues impure_ok
  show ?thesis by blast
qed

(* What a typed impure call says about its function and its arguments, with the
   arguments typed in Ghost mode. (As core_impure_call_type_fn_facts, without
   the facts that depend on the mode.) *)
lemma core_impure_call_type_fn_facts_Ghost:
  assumes "core_impure_call_type env ghost fnName tyArgs tmArgs = Some ty"
  shows "\<exists>funInfo.
            fmlookup (TE_Functions env) fnName = Some funInfo
            \<and> length tyArgs = length (FI_TyArgs funInfo)
            \<and> list_all (is_well_kinded env) tyArgs
            \<and> list_all is_complete_type tyArgs
            \<and> length tmArgs = length (FI_TmArgs funInfo)
            \<and> ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                               (FI_ReturnType funInfo)
            \<and> list_all2 (\<lambda>tm expectedTy.
                  core_term_type env Ghost tm = Some expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))
            \<and> (\<forall>i < length tmArgs.
                 fst (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i))"
proof -
  from core_impure_call_type_fn_facts[OF assms] obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    cp: "list_all is_complete_type tyArgs" and
    len_tm: "length tmArgs = length (FI_TmArgs funInfo)" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                             (FI_ReturnType funInfo)" and
    args: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) tmArgs
                (zip (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                          (FI_TmArgs funInfo))
                     (map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)))" and
    refs: "\<forall>i < length tmArgs.
                 fst (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i)
                       \<and> ghost_lvalue_ok env (param_mode ghost (snd (snd (FI_TmArgs funInfo ! i))))
                                          (tmArgs ! i)"
    by blast
  have args_g: "list_all2 (\<lambda>tm expectedTy. core_term_type env Ghost tm = Some expectedTy)
                tmArgs
                (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))"
    by (rule args_typed_imp_Ghost[OF args]) simp
  from refs have refs_g: "\<forall>i < length tmArgs.
                 fst (snd (FI_TmArgs funInfo ! i)) = Ref
                   \<longrightarrow> is_writable_lvalue env (tmArgs ! i)"
    by blast
  from fn_lookup len_ty wk cp len_tm ty_eq args_g refs_g show ?thesis by blast
qed

(* The return type produced by core_impure_call_type is well-kinded (and, in
   NotGhost mode, a runtime type) in a well-formed env. *)
lemma core_impure_call_type_well_kinded_and_runtime:
  assumes ct: "core_impure_call_type env ghost fnName tyArgs tmArgs = Some retTy"
    and wf: "tyenv_well_formed env"
  shows "is_well_kinded env retTy
         \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env retTy)"
proof -
  from core_impure_call_type_fn_facts[OF ct] obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyargs_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs" and
    not_ghost_fn: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    ty_eq: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                (FI_ReturnType funInfo)"
    by blast
  show ?thesis
    unfolding ty_eq
    using fun_return_type_specialized_well_kinded[OF wf fn_lookup len_tyargs tyargs_wk]
          fun_return_type_specialized_runtime[OF wf fn_lookup len_tyargs]
          tyargs_rt not_ghost_fn
    by blast
qed

(* cast_result_type is preserved under adding type variables to the environment:
   it depends on env only through cast_ok and is_runtime_type, both monotone. *)
lemma cast_result_type_irrelevant_tyvar:
  assumes "cast_result_type env ghost retTy castOpt = Some ty"
  shows "cast_result_type
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>)
           ghost retTy castOpt = Some ty"
  using assms unfolding cast_result_type_def
  by (cases castOpt)
     (auto split: if_splits simp: is_runtime_type_extend_runtime_tyvars cast_ok_extend_tyvars)

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
  \<comment> \<open>The per-argument check, parameterised by the env it runs in.\<close>
  let ?P = "\<lambda>e. \<lambda>(tm, vor) (expectedTy, mode).
               case vor of
                 Var \<Rightarrow> core_term_type e mode tm = Some expectedTy
               | Ref \<Rightarrow> is_writable_lvalue e tm
                        \<and> ghost_lvalue_ok e mode tm
                        \<and> core_term_type e mode tm = Some expectedTy"
  have args_mono: "list_all2 (?P env) xs ys \<Longrightarrow> list_all2 (?P ?env') xs ys" for xs ys
    by (erule list_all2_mono)
       (auto split: VarOrRef.splits prod.splits intro: core_term_type_irrelevant_tyvar)
  have wk_mono: "list_all (is_well_kinded env) ts \<Longrightarrow> list_all (is_well_kinded ?env') ts" for ts
    using is_well_kinded_extend_tyvars by (fastforce simp: list_all_iff)
  have rt_mono: "list_all (is_runtime_type env) ts \<Longrightarrow> list_all (is_runtime_type ?env') ts" for ts
    using is_runtime_type_extend_runtime_tyvars by (fastforce simp: list_all_iff)
  from assms show ?thesis
    unfolding core_impure_call_type_def
    by (auto simp: Let_def wk_mono rt_mono args_mono split: option.splits if_splits)
qed


(* ========================================================================== *)
(* Fixed fields: typechecking preserves the fixed fields of the environment   *)
(* ========================================================================== *)

lemma core_statement_type_fixed_eq:
  assumes "core_statement_type env ghost stmt = Some env'"
  shows "tyenv_fixed_eq env env'"
  using assms
  by (cases "(env, ghost, stmt)" rule: core_statement_type.cases)
     (auto simp: tyenv_fixed_eq_def Let_def
           split: VarOrRef.splits option.splits if_splits CoreType.splits
                  CoreTerm.splits Quantifier.splits)

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

(* core_statement_type preserves TE_ReturnType *)
corollary core_statement_type_preserves_return_type:
  assumes "core_statement_type env ghost stmt = Some env'"
  shows "TE_ReturnType env' = TE_ReturnType env"
  using assms core_statement_type_fixed_eq tyenv_fixed_eq_def by auto

(* core_statement_list_type preserves TE_ReturnType *)
corollary core_statement_list_type_preserves_return_type:
  assumes "core_statement_list_type env ghost stmts = Some env'"
  shows "TE_ReturnType env' = TE_ReturnType env"
  using assms core_statement_list_type_fixed_eq tyenv_fixed_eq_def by auto

(* Typing a concatenation: type the first list, then the second in the
   resulting env. *)
lemma core_statement_list_type_append:
  "core_statement_list_type env ghost (stmts1 @ stmts2)
     = (case core_statement_list_type env ghost stmts1 of
          None \<Rightarrow> None
        | Some env1 \<Rightarrow> core_statement_list_type env1 ghost stmts2)"
  by (induction stmts1 arbitrary: env) (simp_all split: option.splits)


(* ========================================================================== *)
(* Ambient-ghost weakening *)
(* ========================================================================== *)

(* If there is no proof goal, typechecking a statement or statement-list does not
   create one. *)
lemma core_statement_type_preserves_proof_goal_none:
  assumes "core_statement_type env ghost stmt = Some env'"
    and "TE_ProofGoal env = None"
  shows "TE_ProofGoal env' = None"
  using assms
  by (cases "(env, ghost, stmt)" rule: core_statement_type.cases)
     (auto simp: Let_def
           split: VarOrRef.splits option.splits if_splits CoreType.splits
                  CoreTerm.splits Quantifier.splits)

(* If a statement (or statement list) typechecks in Ghost mode, then it can 
   be promoted to NotGhost mode and still typecheck -- provided that we are
   within an executable function (TE_FunctionGhost is NotGhost) and not 
   inside an assert proof-block (TE_ProofGoal is None). *)
lemma core_statement_type_ghost_to_notghost:
  "core_statement_type env Ghost stmt = Some env' \<Longrightarrow>
   TE_FunctionGhost env = NotGhost \<Longrightarrow>
   TE_ProofGoal env = None \<Longrightarrow>
   core_statement_type env NotGhost stmt = Some env'"
and core_statement_list_type_ghost_to_notghost:
  "core_statement_list_type env Ghost stmts = Some env' \<Longrightarrow>
   TE_FunctionGhost env = NotGhost \<Longrightarrow>
   TE_ProofGoal env = None \<Longrightarrow>
   core_statement_list_type env NotGhost stmts = Some env'"
proof (induction env Ghost stmt and env Ghost stmts
       arbitrary: env' and env'
       rule: core_statement_type_core_statement_list_type.induct
       [case_names VarDeclVar VarDeclCall VarDeclRef Assign AssignCall Return
                   Swap Assert Assume ShowHide Match While Obtain Fix Use Block
                   Nil Cons])
  \<comment> \<open>Block: re-check the body under NotGhost via the list IH. The body runs under
      TE_ProofTopLevel := False, which preserves TE_FunctionGhost / TE_ProofGoal.\<close>
  case (Block env body)
  from Block.prems(1) obtain bodyEnv where
    body: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) Ghost body = Some bodyEnv" and
    env'_eq: "env' = env"
    by (auto split: option.splits)
  \<comment> \<open>TE_ProofTopLevel := False touches neither TE_FunctionGhost nor TE_ProofGoal.\<close>
  have fg': "TE_FunctionGhost (env \<lparr> TE_ProofTopLevel := False \<rparr>) = NotGhost"
    using Block.prems(2) by simp
  have pg': "TE_ProofGoal (env \<lparr> TE_ProofTopLevel := False \<rparr>) = None"
    using Block.prems(3) by simp
  have "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body = Some bodyEnv"
    by (simp add: Block.hyps body fg' pg')
  thus ?case by (simp add: env'_eq)
next
  \<comment> \<open>Cons: promote the head, then thread the two invariants into the tail. The
      head preserves TE_FunctionGhost (a fixed field) and TE_ProofGoal = None.\<close>
  case (Cons env stmt stmts)
  from Cons.prems(1) obtain envMid where
    head: "core_statement_type env Ghost stmt = Some envMid" and
    tail: "core_statement_list_type envMid Ghost stmts = Some env'"
    by (auto split: option.splits)
  have head': "core_statement_type env NotGhost stmt = Some envMid"
    by (simp add: Cons.hyps(1) Cons.prems(2,3) head)
  from core_statement_type_fixed_eq[OF head] Cons.prems(2)
  have fg_mid: "TE_FunctionGhost envMid = NotGhost" by (simp add: tyenv_fixed_eq_def)
  from core_statement_type_preserves_proof_goal_none[OF head Cons.prems(3)]
  have pg_mid: "TE_ProofGoal envMid = None" .
  have "core_statement_list_type envMid NotGhost stmts = Some env'"
    by (simp add: Cons.hyps(2) fg_mid head pg_mid tail)
  with head' show ?case by simp
qed (auto simp: Let_def
          split: VarOrRef.splits option.splits if_splits CoreType.splits)


(* ========================================================================== *)
(* Well-formedness preservation *)
(* ========================================================================== *)

(* core_statement_type preserves tyenv_well_formed *)
lemma core_statement_type_preserves_well_formed:
  assumes "core_statement_type env ghost stmt = Some env'"
    and "tyenv_well_formed env"
  shows "tyenv_well_formed env'"
using assms proof (cases stmt)
  case (CoreStmt_VarDecl declGhost varName varOrRef varTy initTm)
  \<comment> \<open>Both forms declare a local of type varTy; they differ only in TE_ConstLocals.\<close>
  show ?thesis proof (cases varOrRef)
    case Var
    from assms CoreStmt_VarDecl Var have
      wk: "is_well_kinded env varTy" and
      rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
      env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                             TE_GhostLocals := (if declGhost = Ghost
                                              then finsert varName (TE_GhostLocals env)
                                              else fminus (TE_GhostLocals env) {|varName|}),
                             TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
      by (auto split: if_splits)
    show ?thesis unfolding env'_eq
      by (rule tyenv_well_formed_declare_var[OF assms(2) wk rt])
  next
    case Ref
    from assms CoreStmt_VarDecl Ref have
      wk: "is_well_kinded env varTy" and
      rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
      env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                             TE_GhostLocals := (if declGhost = Ghost
                                              then finsert varName (TE_GhostLocals env)
                                              else fminus (TE_GhostLocals env) {|varName|}),
                             TE_ConstLocals := (if is_writable_lvalue env initTm
                                               then fminus (TE_ConstLocals env) {|varName|}
                                               else finsert varName (TE_ConstLocals env)) \<rparr>"
      by (auto split: if_splits)
    show ?thesis unfolding env'_eq
      by (rule tyenv_well_formed_declare_var[OF assms(2) wk rt])
  qed
next
  case (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
  \<comment> \<open>The variable type is explicit and (by the rule) well-kinded, and runtime in
      NotGhost mode; env extends like VarDecl(Var).\<close>
  from assms CoreStmt_VarDeclCall have
    wk: "is_well_kinded env varTy" and
    rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    env'_eq:
      "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                    TE_GhostLocals := (if declGhost = Ghost
                                     then finsert varName (TE_GhostLocals env)
                                     else fminus (TE_GhostLocals env) {|varName|}),
                    TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits option.splits)
  show ?thesis unfolding env'_eq
    by (rule tyenv_well_formed_declare_var[OF assms(2) wk rt])
next
  case (CoreStmt_Fix varName varTy)
  from assms CoreStmt_Fix obtain bodyTm where
    wk: "is_well_kinded env varTy" and env'_eq:
    "env' = env \<lparr> TE_LocalVars   := fmupd varName varTy (TE_LocalVars env),
                   TE_GhostLocals := finsert varName (TE_GhostLocals env),
                   TE_ConstLocals := finsert varName (TE_ConstLocals env),
                   TE_ProofGoal   := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  show ?thesis unfolding env'_eq
    by (rule tyenv_well_formed_TE_ProofGoal_irrelevant
               [OF tyenv_well_formed_declare_ghost[OF assms(2) wk]])
next
  case (CoreStmt_Obtain varName varTy condTm)
  from assms CoreStmt_Obtain have wk: "is_well_kinded env varTy"
    by (auto simp: Let_def split: if_splits)
  from tyenv_well_formed_declare_ghost[OF assms(2) wk]
  have "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                 TE_GhostLocals := finsert varName (TE_GhostLocals env),
                                 TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>)" .
  with assms CoreStmt_Obtain show ?thesis
    by (auto simp: Let_def split: if_splits)
next
  case (CoreStmt_Use witnessTm)
  from assms CoreStmt_Use obtain bodyTm where
    env'_eq: "env' = env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  from tyenv_well_formed_TE_ProofGoal_irrelevant[OF assms(2)]
  show ?thesis unfolding env'_eq .
  \<comment> \<open>Every other statement leaves the env unchanged.\<close>
qed (use assms in \<open>auto simp: Let_def split: if_splits option.splits CoreType.splits\<close>)

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
(* Tyvar weakening for statements                                             *)
(* ========================================================================== *)

(* Adding (unused) type variables to the environment does not change what
   core_statement_type accepts, and the resulting environment is the original
   result with the extra type variables added. *)

(* This mirrors core_term_type_irrelevant_tyvar (CoreTypecheckLemmas.thy). The
   variant phrased with extend_env_with_tyvars is in ExtendEnvWithTyvars.thy
   (which imports this theory). *)

lemma has_valid_decreases_type_irrelevant_tyvar:
  assumes "has_valid_decreases_type env decr"
  shows "has_valid_decreases_type
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>) decr"
proof (cases decr)
  case None
  then show ?thesis by simp
next
  case (Some tm)
  from assms Some obtain ty where
    t: "core_term_type env Ghost tm = Some ty" and v: "is_valid_decreases_type ty"
    by (auto split: option.splits)
  from core_term_type_irrelevant_tyvar[OF t] v Some show ?thesis by simp
qed

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
       \<and> (declGhost = NotGhost \<longrightarrow> is_complete_type varTy)
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
    cp: "declGhost = NotGhost \<longrightarrow> is_complete_type varTy" and
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
  from gh wk' rt' cp ct' cast' show ?case
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
       \<and> ghost_lvalue_ok env declGhost initTm
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
    glv: "ghost_lvalue_ok env assignGhost lhsTm" and
    lhs: "core_term_type env assignGhost lhsTm = Some lhsTy" and
    cp: "assignGhost = NotGhost \<longrightarrow> is_complete_type lhsTy" and
    rhs: "core_term_type env assignGhost rhsTm = Some lhsTy" and
    env'_eq: "env' = env"
    by (auto split: if_splits option.splits)
  let ?env1 = "?ext env"
  have lhs': "core_term_type ?env1 assignGhost lhsTm = Some lhsTy"
    using lhs core_term_type_irrelevant_tyvar by blast
  have rhs': "core_term_type ?env1 assignGhost rhsTm = Some lhsTy"
    using rhs core_term_type_irrelevant_tyvar by blast
  from gh wl glv lhs' cp rhs' show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>AssignCall: env unchanged. The call check and cast both survive ?ext.\<close>
  case (5 env ghost assignGhost lhsTm castOpt fnName tyArgs argTms)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  from "5.prems" have
    pre: "(ghost = Ghost \<longrightarrow> assignGhost = Ghost) \<and> is_writable_lvalue env lhsTm
            \<and> ghost_lvalue_ok env assignGhost lhsTm"
    by (simp split: if_splits)
  hence gh: "ghost = Ghost \<longrightarrow> assignGhost = Ghost" and wl: "is_writable_lvalue env lhsTm"
    and glv: "ghost_lvalue_ok env assignGhost lhsTm"
    by simp_all
  from "5.prems" pre obtain lhsTy where
    lhs: "core_term_type env assignGhost lhsTm = Some lhsTy"
    by (simp split: option.splits)
  from "5.prems" pre lhs obtain retTy where
    ct: "core_impure_call_type env assignGhost fnName tyArgs argTms = Some retTy"
    by (simp split: option.splits)
  from "5.prems" pre lhs ct have
    cp: "assignGhost = NotGhost \<longrightarrow> is_complete_type lhsTy" and
    cast: "cast_result_type env assignGhost retTy castOpt = Some lhsTy" and
    env'_eq: "env' = env"
    by (simp split: if_splits)+
  have lhs': "core_term_type ?env1 assignGhost lhsTm = Some lhsTy"
    using lhs core_term_type_irrelevant_tyvar by blast
  have ct': "core_impure_call_type ?env1 assignGhost fnName tyArgs argTms = Some retTy"
    using ct core_impure_call_type_irrelevant_tyvar by blast
  have cast': "cast_result_type ?env1 assignGhost retTy castOpt = Some lhsTy"
    using cast cast_result_type_irrelevant_tyvar by blast
  from gh wl glv lhs' cp ct' cast' show ?case
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
    glvL: "ghost_lvalue_ok env swapGhost lhsTm" and
    glvR: "ghost_lvalue_ok env swapGhost rhsTm" and
    lhs: "core_term_type env swapGhost lhsTm = Some lhsTy" and
    cp: "swapGhost = NotGhost \<longrightarrow> is_complete_type lhsTy" and
    rhs: "core_term_type env swapGhost rhsTm = Some lhsTy" and
    env'_eq: "env' = env"
    by (auto split: if_splits option.splits)
  let ?env1 = "?ext env"
  have lhs': "core_term_type ?env1 swapGhost lhsTm = Some lhsTy"
    using lhs core_term_type_irrelevant_tyvar by blast
  have rhs': "core_term_type ?env1 swapGhost rhsTm = Some lhsTy"
    using rhs core_term_type_irrelevant_tyvar by blast
  from gh wl wr glvL glvR lhs' cp rhs' show ?case by (simp add: env'_eq)
next
  \<comment> \<open>Assert: env unchanged; body checked under goalEnv, which sets
      TE_ProofGoal to condTm when a condition is present, or keeps the current goal
      for "assert *" (condOpt = None), and sets TE_ProofTopLevel := True.
      ?ext commutes with goalEnv.\<close>
  case (8 env ghost condOpt proofBody)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  \<comment> \<open>?goalEnv computes the new goal directly from its argument, so it agrees with
      the form Isabelle unfolds the rule into for both env and ?env1.\<close>
  let ?goalEnv = "\<lambda>e. e \<lparr> TE_ProofGoal := (case condOpt of Some condTm \<Rightarrow> Some condTm
                                                          | None \<Rightarrow> TE_ProofGoal e),
                          TE_ProofTopLevel := True \<rparr>"
  let ?condOk = "case condOpt of
                   Some condTm \<Rightarrow> core_term_type env Ghost condTm = Some CoreTy_Bool
                 | None \<Rightarrow> TE_ProofGoal env \<noteq> None"
  from "8.prems" obtain bodyEnv where
    condOk: "?condOk" and
    body: "core_statement_list_type (?goalEnv env) Ghost proofBody = Some bodyEnv" and
    env'_eq: "env' = env"
    by (auto simp: Let_def split: if_splits option.splits)
  \<comment> \<open>?ext commutes with the goal-env update; the new goal (which in the None branch
      reads TE_ProofGoal of the argument) is unchanged by ?ext.\<close>
  have shape: "?ext (?goalEnv env) = ?goalEnv ?env1"
    by (cases condOpt) simp_all
  from "8.IH"[OF refl refl refl condOk body] shape have body':
    "core_statement_list_type (?goalEnv ?env1) Ghost proofBody = Some (?ext bodyEnv)"
    by argo
  \<comment> \<open>The condition (if any) still typechecks under the extended env, and the
      "assert *" side-condition (current goal present) is preserved by ?ext.\<close>
  have condOk': "case condOpt of
                   Some condTm \<Rightarrow> core_term_type ?env1 Ghost condTm = Some CoreTy_Bool
                 | None \<Rightarrow> TE_ProofGoal ?env1 \<noteq> None"
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
  \<comment> \<open>ShowHide: env unchanged; TE_Functions is untouched by ?ext.\<close>
  case (10 env ghost sh name)
  from "10.prems" have "env' = env" and "name |\<in>| fmdom (TE_Functions env)"
    by (simp_all split: if_splits)
  thus ?case by simp
next
  \<comment> \<open>Match: env unchanged; pattern_compatible depends only on TE_DataCtors, and
      each arm body is checked under TE_ProofTopLevel := False.\<close>
  case (11 env ghost matchGhost scrut arms)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  from "11.prems" obtain scrutTy where
    gh: "ghost = Ghost \<longrightarrow> matchGhost = Ghost" and
    scrut: "core_term_type env matchGhost scrut = Some scrutTy" and
    pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    bodies: "list_all (\<lambda>body. core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>)
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
      ?ext commutes with the TE_ProofTopLevel := False update.\<close>
  have goal_shape: "?ext (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                      = ?env1 \<lparr> TE_ProofTopLevel := False \<rparr>" by simp
  have bodies': "list_all (\<lambda>body. core_statement_list_type (?env1 \<lparr> TE_ProofTopLevel := False \<rparr>)
                                     matchGhost body \<noteq> None) (map snd arms)"
    unfolding list_all_iff
  proof (rule ballI)
    fix body assume body_in: "body \<in> set (map snd arms)"
    from bodies[unfolded list_all_iff] body_in
    have "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) matchGhost body \<noteq> None"
      by blast
    then obtain bEnv where
      bsome: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) matchGhost body = Some bEnv"
      by blast
    from "11.IH"[OF gh scrut refl refl pats_nn body_in bsome] goal_shape
    have "core_statement_list_type (?env1 \<lparr> TE_ProofTopLevel := False \<rparr>) matchGhost body
            = Some (?ext bEnv)"
      by argo
    thus "core_statement_list_type (?env1 \<lparr> TE_ProofTopLevel := False \<rparr>) matchGhost body \<noteq> None"
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
  from "12.prems" obtain bodyEnv where
    gh: "ghost = Ghost \<longrightarrow> whileGhost = Ghost" and
    cond: "core_term_type env whileGhost condTm = Some CoreTy_Bool" and
    invs: "list_all (\<lambda>inv. core_term_type env Ghost inv = Some CoreTy_Bool) invars" and
    decr: "has_valid_decreases_type env decrTm" and
    body: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) whileGhost body = Some bodyEnv" and
    env'_eq: "env' = env"
    by (auto split: if_splits option.splits CoreType.splits)
  have cond': "core_term_type ?env1 whileGhost condTm = Some CoreTy_Bool"
    using cond core_term_type_irrelevant_tyvar by blast
  have invs': "list_all (\<lambda>inv. core_term_type ?env1 Ghost inv = Some CoreTy_Bool) invars"
    using invs core_term_type_irrelevant_tyvar by (simp add: list_all_iff)
  have decr': "has_valid_decreases_type ?env1 decrTm"
    using decr has_valid_decreases_type_irrelevant_tyvar by blast
  have goal_shape: "?ext (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                      = ?env1 \<lparr> TE_ProofTopLevel := False \<rparr>" by simp
  from "12.IH"[OF gh cond refl invs decr body] goal_shape have body':
    "core_statement_list_type (?env1 \<lparr> TE_ProofTopLevel := False \<rparr>) whileGhost body
       = Some (?ext bodyEnv)"
    by argo
  from gh cond' invs' decr' body' show ?case
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
    topLevel: "TE_ProofTopLevel env" and
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
  have topLevel': "TE_ProofTopLevel ?env1"
    using topLevel by simp
  from gh goal' wk' topLevel' show ?case
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
    topLevel: "TE_ProofTopLevel env" and
    env'_eq: "env' = env \<lparr> TE_ProofGoal := Some bodyTm \<rparr>"
    by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
  let ?env1 = "?ext env"
  have goal': "TE_ProofGoal ?env1 = Some (CoreTm_Quantifier Quant_Exists qName qVarTy bodyTm)"
    using goal by simp
  have wit': "core_term_type ?env1 ghost witnessTm = Some qVarTy"
    using wit core_term_type_irrelevant_tyvar by blast
  have topLevel': "TE_ProofTopLevel ?env1"
    using topLevel by simp
  from gh goal' wit' topLevel' show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>Block: env unchanged; body is a list checked under TE_ProofTopLevel := False.\<close>
  case (16 env ghost body)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  let ?env1 = "?ext env"
  from "16.prems" obtain bodyEnv where
    body: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) ghost body = Some bodyEnv" and
    env'_eq: "env' = env"
    by (auto split: option.splits)
  have goal_shape: "?ext (env \<lparr> TE_ProofTopLevel := False \<rparr>)
                      = ?env1 \<lparr> TE_ProofTopLevel := False \<rparr>" by simp
  from "16.IH"[OF body] goal_shape have body':
    "core_statement_list_type (?env1 \<lparr> TE_ProofTopLevel := False \<rparr>) ghost body
       = Some (?ext bodyEnv)"
    by argo
  from body' show ?case
    by (simp add: env'_eq)
next
  \<comment> \<open>Empty statement list.\<close>
  case (17 env ghost)
  from "17.prems" have "env' = env" by simp
  thus ?case by simp
next
  \<comment> \<open>Cons: thread the env through head then tail.\<close>
  case (18 env ghost stmt stmts)
  let ?ext = "\<lambda>e :: CoreTyEnv.
                e \<lparr> TE_TypeVars := TE_TypeVars e |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars e |\<union>| extraRT \<rparr>"
  from "18.prems" obtain envMid where
    head: "core_statement_type env ghost stmt = Some envMid" and
    tail: "core_statement_list_type envMid ghost stmts = Some env'"
    by (auto split: option.splits)
  from "18.IH"(1)[OF head] have head':
    "core_statement_type (?ext env) ghost stmt
       = Some (?ext envMid)" .
  from "18.IH"(2)[OF head tail] have tail':
    "core_statement_list_type (?ext envMid) ghost stmts
       = Some (?ext env')" .
  from head' tail' show ?case by simp
qed



end

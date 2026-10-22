theory MatchCompilePassSimStmts
  imports MatchCompilePassSimTerms
begin

(* The simulation for the match compilation pass: the statement, statement
   list and function call cases of the induction step. See
   MatchCompilePassSimTerms.thy for the setting. *)


section \<open>Statement lists and single statements\<close>

(* A statement list that ends in a Return is not affected by what follows. *)
lemma interp_statement_list_append_Return:
  assumes "interp_statement_list d f s xs = Inr (Return s1 v)"
  shows "interp_statement_list d f s (xs @ ys) = Inr (Return s1 v)"
  using assms
proof (induction xs arbitrary: s f)
  case Nil
  then show ?case by (cases f) simp_all
next
  case (Cons x xs)
  then obtain f0 where f_eq: "f = Suc f0" by (cases f) simp_all
  show ?case
  proof (cases "interp_statement d f0 s x")
    case (Inl err)
    with Cons.prems f_eq show ?thesis by simp
  next
    case (Inr r)
    show ?thesis
    proof (cases r)
      case (Continue s')
      with Cons.prems f_eq Inr have "interp_statement_list d f0 s' xs = Inr (Return s1 v)" by simp
      from Cons.IH[OF this] Inr Continue f_eq show ?thesis by simp
    next
      case (Return s'' v')
      with Cons.prems f_eq Inr show ?thesis by simp
    qed
  qed
qed

(* Two statement lists that run one after the other, at some fuel. *)
lemma interp_statement_list_append_Continue:
  assumes "interp_statement_list d f s xs = Inr (Continue s1)"
      and "interp_statement_list d g s1 ys = Inr r"
  shows "\<exists>h. interp_statement_list d h s (xs @ ys) = Inr r"
  using assms
proof (induction xs arbitrary: s f)
  case Nil
  then have "s1 = s" by (cases f) simp_all
  with Nil.prems(2) show ?case by auto
next
  case (Cons x xs)
  then obtain f0 where f_eq: "f = Suc f0" by (cases f) simp_all
  show ?case
  proof (cases "interp_statement d f0 s x")
    case (Inl err)
    with Cons.prems f_eq show ?thesis by simp
  next
    case (Inr r0)
    show ?thesis
    proof (cases r0)
      case (Continue s')
      with Cons.prems(1) f_eq Inr have "interp_statement_list d f0 s' xs = Inr (Continue s1)" by simp
      from Cons.IH[OF this Cons.prems(2)] obtain h0 where
        h0: "interp_statement_list d h0 s' (xs @ ys) = Inr r" by blast
      let ?H = "max f0 h0"
      have x': "interp_statement d ?H s x = Inr (Continue s')"
        by (rule interp_statement_Inr_more_fuel[OF Inr[unfolded Continue]]) simp
      have rest': "interp_statement_list d ?H s' (xs @ ys) = Inr r"
        by (rule interp_statement_list_Inr_more_fuel[OF h0]) simp
      have "interp_statement_list d (Suc ?H) s ((x # xs) @ ys) = Inr r"
        using x' rest' by simp
      thus ?thesis by blast
    next
      case (Return s'' v')
      with Cons.prems(1) f_eq Inr show ?thesis by simp
    qed
  qed
qed

(* The result of a one-statement list is the result of the statement. *)
lemma interp_statement_list_single_D:
  assumes "interp_statement_list d f s [stmt] = Inr r"
  shows "\<exists>f'. interp_statement d f' s stmt = Inr r"
proof -
  from assms obtain f0 where f_eq: "f = Suc f0" by (cases f) simp_all
  show ?thesis
  proof (cases "interp_statement d f0 s stmt")
    case (Inl err)
    with assms f_eq show ?thesis by simp
  next
    case (Inr r0)
    show ?thesis
    proof (cases r0)
      case (Continue s')
      with assms f_eq Inr have "r = Continue s'" by (cases f0) simp_all
      with Inr Continue show ?thesis by blast
    next
      case (Return s' v)
      with assms f_eq Inr show ?thesis by auto
    qed
  qed
qed

(* The result of a successful call, built from its parts (the converse of
   interp_function_call_InrE, for a function without a contract). *)
lemma interp_function_call_I:
  assumes "fmlookup (IS_Functions state) fnName = Some f"
      and "length argTms = length (IF_Args f)"
      and "length argTys = length (IF_TyArgs f)"
      and "fold process_one_arg
             (zip (IF_Args f) (zip (map (interp_writable_lvalue d fuel state) argTms)
                                   (map (interp_term d fuel state) argTms)))
             (Inr (state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty, IS_ConstLocals := {||},
                           IS_TyArgs := fmap_of_list (zip (IF_TyArgs f)
                                          (map (apply_subst (IS_TyArgs state)) argTys)) \<rparr>))
           = Inr preCallState"
      and "IF_Requires f = []" and "IF_Ensures f = []"
      and "call_body (interp_statement_list d fuel) state f
             (map (interp_writable_lvalue d fuel state) argTms)
             (map (interp_term d fuel state) argTms) preCallState = Inr r"
  shows "interp_function_call d (Suc fuel) state fnName argTys argTms = Inr r"
  using assms by (simp add: Let_def checked_call_no_contract)

(* Lists of argument results that agree wherever the first succeeds, and
   whose first all succeed, are equal. *)
lemma results_agree_eq:
  assumes "length ys = length xs"
      and "\<And>i v. i < length xs \<Longrightarrow> xs ! i = Inr v \<Longrightarrow> ys ! i = Inr v"
      and "\<And>x. x \<in> set xs \<Longrightarrow> \<exists>v. x = Inr v"
  shows "ys = xs"
proof (rule nth_equalityI[OF assms(1)])
  fix i assume i_lt: "i < length ys"
  with assms(1) have "xs ! i \<in> set xs" by simp
  with assms(3) obtain v where "xs ! i = Inr v" by blast
  with assms(2) i_lt assms(1) show "ys ! i = xs ! i" by simp
qed


context match_compile_sim
begin

section \<open>Statements\<close>

(* The compiled statement list of a statement that is kept as one statement. *)
lemma stmt_sim_single:
  assumes "match_compile_statement stmt = [stmt']"
      and "\<And>env env' storeTyping (full :: 'w InterpState) res.
       TE_Functions env = TE_Functions genv \<Longrightarrow> IS_Functions full = funs \<Longrightarrow>
       state_matches_env full env storeTyping \<Longrightarrow> tyenv_well_formed env \<Longrightarrow>
       TE_ProofGoal env = None \<Longrightarrow>
       core_statement_type env NotGhost stmt = Some env' \<Longrightarrow>
       core_statement_ghost_free stmt \<Longrightarrow> core_statement_match_scrutinees_ok stmt \<Longrightarrow>
       interp_statement d (Suc fuel) full stmt = Inr res \<Longrightarrow>
       \<exists>fuel'. interp_statement d (Suc fuel') (mc_state full) stmt' = Inr (mc_result res)"
  shows "stmt_sim (Suc fuel) stmt"
proof (rule stmt_simI)
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume "TE_Functions env = TE_Functions genv" "IS_Functions full = funs"
    "state_matches_env full env storeTyping" "tyenv_well_formed env" "TE_ProofGoal env = None"
    "core_statement_type env NotGhost stmt = Some env'"
    "core_statement_ghost_free stmt" "core_statement_match_scrutinees_ok stmt"
    "interp_statement d (Suc fuel) full stmt = Inr res"
  from assms(2)[OF this] obtain f1 where
    "interp_statement d (Suc f1) (mc_state full) stmt' = Inr (mc_result res)" by blast
  from interp_statement_list_single[OF this]
  show "\<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement stmt)
                 = Inr (mc_result res)"
    unfolding assms(1) by blast
qed

lemma sim_VarDecl_Var:
  assumes IH: "term_sim fuel initTm"
  shows "stmt_sim (Suc fuel) (CoreStmt_VarDecl g x Var ty initTm)"
proof (rule stmt_sim_single)
  show "match_compile_statement (CoreStmt_VarDecl g x Var ty initTm)
          = [CoreStmt_VarDecl g x Var ty (match_compile_term initTm)]" by simp
next
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_statement_type env NotGhost (CoreStmt_VarDecl g x Var ty initTm) = Some env'"
    and gf: "core_statement_ghost_free (CoreStmt_VarDecl g x Var ty initTm)"
    and ok: "core_statement_match_scrutinees_ok (CoreStmt_VarDecl g x Var ty initTm)"
    and ev: "interp_statement d (Suc fuel) full (CoreStmt_VarDecl g x Var ty initTm) = Inr res"
  from gf have g: "g = NotGhost" by simp
  from typing g have t: "core_term_type env NotGhost initTm = Some ty" by (auto split: if_splits)
  from ok have ok': "core_term_match_scrutinees_ok initTm" by simp
  from ev obtain v where v: "interp_term d fuel full initTm = Inr v"
    and res_eq: "res = Continue (bind_mutable_local x v full)"
    by (auto split: sum.splits)
  from term_simD[OF IH fe fs sme wf t ok' v] obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term initTm) = Inr v" by auto
  have "interp_statement d (Suc f1) (mc_state full) (CoreStmt_VarDecl g x Var ty (match_compile_term initTm))
          = Inr (mc_result res)"
    using f1 res_eq by simp
  thus "\<exists>fuel'. interp_statement d (Suc fuel') (mc_state full)
                  (CoreStmt_VarDecl g x Var ty (match_compile_term initTm)) = Inr (mc_result res)"
    by blast
qed

lemma sim_VarDecl_Ref:
  assumes IH: "term_sim fuel initTm" and IHl: "lvalue_sim fuel initTm"
  shows "stmt_sim (Suc fuel) (CoreStmt_VarDecl g x Ref ty initTm)"
proof (rule stmt_sim_single)
  show "match_compile_statement (CoreStmt_VarDecl g x Ref ty initTm)
          = [CoreStmt_VarDecl g x Ref ty (match_compile_term initTm)]" by simp
next
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_statement_type env NotGhost (CoreStmt_VarDecl g x Ref ty initTm) = Some env'"
    and gf: "core_statement_ghost_free (CoreStmt_VarDecl g x Ref ty initTm)"
    and ok: "core_statement_match_scrutinees_ok (CoreStmt_VarDecl g x Ref ty initTm)"
    and ev: "interp_statement d (Suc fuel) full (CoreStmt_VarDecl g x Ref ty initTm) = Inr res"
  from gf have g: "g = NotGhost" by simp
  from typing g have t: "core_term_type env NotGhost initTm = Some ty" and lv: "is_lvalue initTm"
    by (auto split: if_splits)
  from ok have ok': "core_term_match_scrutinees_ok initTm" by simp
  let ?init' = "match_compile_term initTm"
  from lv obtain base where base: "lvalue_base_name initTm = Some base"
    unfolding is_lvalue_def by auto
  have base': "lvalue_base_name ?init' = Some base"
    using base lvalue_base_name_match_compile_term[OF lv] by simp
  show "\<exists>fuel'. interp_statement d (Suc fuel') (mc_state full)
                  (CoreStmt_VarDecl g x Ref ty ?init') = Inr (mc_result res)"
  proof (cases "base |\<in>| IS_ConstLocals full
                \<or> (fmlookup (IS_Locals full) base = None \<and> fmlookup (IS_Refs full) base = None)")
    case True
    \<comment> \<open>A read-only base: the value is copied.\<close>
    from ev base True obtain v where v: "interp_term d fuel full initTm = Inr v"
      and res_eq: "res = Continue (bind_const_local x v full)"
      by (auto split: sum.splits)
    from term_simD[OF IH fe fs sme wf t ok' v] obtain f1 where
      f1: "interp_term d f1 (mc_state full) ?init' = Inr v" by auto
    have "interp_statement d (Suc f1) (mc_state full) (CoreStmt_VarDecl g x Ref ty ?init')
            = Inr (mc_result res)"
      using f1 res_eq base' True by simp
    thus ?thesis by blast
  next
    case False
    \<comment> \<open>A writable base: the ref aliases it.\<close>
    from ev base False obtain ap where ap: "interp_writable_lvalue d fuel full initTm = Inr ap"
      and res_eq: "res = Continue (bind_ref x ap full)"
      by (auto split: sum.splits)
    from lvalue_simD[OF IHl fe fs sme wf t ok' ap] obtain f1 where
      f1: "interp_writable_lvalue d f1 (mc_state full) ?init' = Inr ap" by auto
    have "interp_statement d (Suc f1) (mc_state full) (CoreStmt_VarDecl g x Ref ty ?init')
            = Inr (mc_result res)"
      using f1 res_eq base' False by auto
    thus ?thesis by blast
  qed
qed

(* The typing of an impure call gives the hypotheses of the call claim. *)
lemma impure_call_facts:
  assumes fe: "TE_Functions env = TE_Functions genv"
      and c: "core_impure_call_type env NotGhost fnName tyArgs argTms = Some retTy"
  shows "\<exists>funInfo.
           fmlookup (TE_Functions env) fnName = Some funInfo
           \<and> list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
               argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                           (FI_TmArgs funInfo))
           \<and> length tyArgs = length (FI_TyArgs funInfo)
           \<and> list_all (is_well_kinded env) tyArgs
           \<and> (\<forall>i < length argTms.
                fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow> is_writable_lvalue env (argTms ! i))"
proof -
  from core_impure_call_type_fn_facts[OF c] obtain funInfo where
    fi: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    len_args: "length argTms = length (FI_TmArgs funInfo)" and
    args: "list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy) argTms
             (zip (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                       (FI_TmArgs funInfo))
                  (map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs funInfo)))" and
    refs: "\<forall>i < length argTms.
             fst (snd (FI_TmArgs funInfo ! i)) = Ref
               \<longrightarrow> is_writable_lvalue env (argTms ! i)
                 \<and> ghost_lvalue_ok env (param_mode NotGhost (snd (snd (FI_TmArgs funInfo ! i))))
                                    (argTms ! i)"
    by blast
  from funs_match_compilable_info[OF fmc fi[unfolded fe]] have ngp: "no_ghost_params funInfo" by simp
  let ?expected = "map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo)"
  have modes: "map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs funInfo)
                 = replicate (length (FI_TmArgs funInfo)) NotGhost"
    using param_modes_no_ghost[OF ngp[unfolded no_ghost_params_def]] .
  have args': "list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
                 argTms ?expected"
  proof (rule list_all2_all_nthI)
    show "length argTms = length ?expected" using len_args by simp
    fix i assume i_lt: "i < length argTms"
    hence i_lt_f: "i < length (FI_TmArgs funInfo)" using len_args by simp
    have "zip ?expected (map (\<lambda>(_, _, gh). param_mode NotGhost gh) (FI_TmArgs funInfo)) ! i
            = (?expected ! i, NotGhost)"
      using i_lt_f by (simp add: modes nth_zip)
    with list_all2_nthD[OF args i_lt]
    show "core_term_type env NotGhost (argTms ! i) = Some (?expected ! i)" by simp
  qed
  from fi args' len_ty wk refs show ?thesis by blast
qed

lemma sim_VarDeclCall:
  assumes IH: "call_sim fuel fnName tyArgs argTms"
  shows "stmt_sim (Suc fuel) (CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs argTms)"
proof (rule stmt_sim_single)
  show "match_compile_statement (CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs argTms)
          = [CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs (map match_compile_term argTms)]" by simp
next
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_statement_type env NotGhost
                   (CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs argTms) = Some env'"
    and gf: "core_statement_ghost_free (CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs argTms)"
    and ok: "core_statement_match_scrutinees_ok
               (CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs argTms)"
    and ev: "interp_statement d (Suc fuel) full
               (CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs argTms) = Inr res"
  from gf have g: "g = NotGhost" by simp
  from typing g obtain retTy where
    c: "core_impure_call_type env NotGhost fnName tyArgs argTms = Some retTy"
    by (auto split: if_splits option.splits)
  from impure_call_facts[OF fe c] obtain funInfo where
    fi: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    args: "list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
             argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                         (FI_TmArgs funInfo))" and
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    refs: "\<forall>i < length argTms.
             fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow> is_writable_lvalue env (argTms ! i)"
    by blast
  from ok have ok': "list_all core_term_match_scrutinees_ok argTms" by simp
  from ev obtain newFull retVal v where
    call: "interp_function_call d fuel full fnName tyArgs argTms = Inr (newFull, retVal)" and
    cast: "apply_cast_opt castOpt retVal = Inr v" and
    res_eq: "res = Continue (bind_mutable_local x v newFull)"
    by (auto split: sum.splits)
  from call_simD[OF IH fe fs sme wf fi args len_ty wk refs ok' call] obtain f1 where
    f1: "interp_function_call d f1 (mc_state full) fnName tyArgs (map match_compile_term argTms)
           = Inr (mc_state newFull, retVal)" by auto
  have "interp_statement d (Suc f1) (mc_state full)
          (CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs (map match_compile_term argTms))
        = Inr (mc_result res)"
    using f1 cast res_eq by simp
  thus "\<exists>fuel'. interp_statement d (Suc fuel') (mc_state full)
                  (CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs (map match_compile_term argTms))
                = Inr (mc_result res)"
    by blast
qed

lemma sim_Assign:
  assumes IHl: "lvalue_sim fuel lhs" and IH: "term_sim fuel rhs"
  shows "stmt_sim (Suc fuel) (CoreStmt_Assign g lhs rhs)"
proof (rule stmt_sim_single)
  show "match_compile_statement (CoreStmt_Assign g lhs rhs)
          = [CoreStmt_Assign g (match_compile_term lhs) (match_compile_term rhs)]" by simp
next
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_statement_type env NotGhost (CoreStmt_Assign g lhs rhs) = Some env'"
    and gf: "core_statement_ghost_free (CoreStmt_Assign g lhs rhs)"
    and ok: "core_statement_match_scrutinees_ok (CoreStmt_Assign g lhs rhs)"
    and ev: "interp_statement d (Suc fuel) full (CoreStmt_Assign g lhs rhs) = Inr res"
  from gf have g: "g = NotGhost" by simp
  from typing g obtain lhsTy where
    tl: "core_term_type env NotGhost lhs = Some lhsTy" and
    tr: "core_term_type env NotGhost rhs = Some lhsTy"
    by (auto split: if_splits option.splits)
  from ok have okl: "core_term_match_scrutinees_ok lhs" and okr: "core_term_match_scrutinees_ok rhs"
    by simp_all
  from ev obtain addr path v newVal where
    ap: "interp_writable_lvalue d fuel full lhs = Inr (addr, path)" and
    v: "interp_term d fuel full rhs = Inr v" and
    upd: "update_value_at_path (IS_Store full ! addr) path v = Inr newVal" and
    res_eq: "res = Continue (full \<lparr> IS_Store := (IS_Store full)[addr := newVal] \<rparr>)"
    by (auto simp: Let_def split: sum.splits)
  from lvalue_simD[OF IHl fe fs sme wf tl okl ap] obtain f1 where
    f1: "interp_writable_lvalue d f1 (mc_state full) (match_compile_term lhs) = Inr (addr, path)" by auto
  from term_simD[OF IH fe fs sme wf tr okr v] obtain f2 where
    f2: "interp_term d f2 (mc_state full) (match_compile_term rhs) = Inr v" by auto
  let ?F = "max f1 f2"
  have f1': "interp_writable_lvalue d ?F (mc_state full) (match_compile_term lhs) = Inr (addr, path)"
    by (rule interp_writable_lvalue_Inr_more_fuel[OF f1]) simp
  have f2': "interp_term d ?F (mc_state full) (match_compile_term rhs) = Inr v"
    by (rule interp_term_Inr_more_fuel[OF f2]) simp
  have "interp_statement d (Suc ?F) (mc_state full)
          (CoreStmt_Assign g (match_compile_term lhs) (match_compile_term rhs)) = Inr (mc_result res)"
    using f1' f2' upd res_eq by (simp add: Let_def)
  thus "\<exists>fuel'. interp_statement d (Suc fuel') (mc_state full)
                  (CoreStmt_Assign g (match_compile_term lhs) (match_compile_term rhs))
                = Inr (mc_result res)"
    by blast
qed

lemma sim_AssignCall:
  assumes IHl: "lvalue_sim fuel lhs" and IH: "call_sim fuel fnName tyArgs argTms"
  shows "stmt_sim (Suc fuel) (CoreStmt_AssignCall g lhs castOpt fnName tyArgs argTms)"
proof (rule stmt_sim_single)
  show "match_compile_statement (CoreStmt_AssignCall g lhs castOpt fnName tyArgs argTms)
          = [CoreStmt_AssignCall g (match_compile_term lhs) castOpt fnName tyArgs
               (map match_compile_term argTms)]" by simp
next
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_statement_type env NotGhost
                   (CoreStmt_AssignCall g lhs castOpt fnName tyArgs argTms) = Some env'"
    and gf: "core_statement_ghost_free (CoreStmt_AssignCall g lhs castOpt fnName tyArgs argTms)"
    and ok: "core_statement_match_scrutinees_ok (CoreStmt_AssignCall g lhs castOpt fnName tyArgs argTms)"
    and ev: "interp_statement d (Suc fuel) full
               (CoreStmt_AssignCall g lhs castOpt fnName tyArgs argTms) = Inr res"
  from gf have g: "g = NotGhost" by simp
  from typing g obtain lhsTy retTy where
    tl: "core_term_type env NotGhost lhs = Some lhsTy" and
    c: "core_impure_call_type env NotGhost fnName tyArgs argTms = Some retTy"
    by (auto split: if_splits option.splits)
  from impure_call_facts[OF fe c] obtain funInfo where
    fi: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    args: "list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
             argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                         (FI_TmArgs funInfo))" and
    len_ty: "length tyArgs = length (FI_TyArgs funInfo)" and
    wk: "list_all (is_well_kinded env) tyArgs" and
    refs: "\<forall>i < length argTms.
             fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow> is_writable_lvalue env (argTms ! i)"
    by blast
  from ok have okl: "core_term_match_scrutinees_ok lhs"
    and oka: "list_all core_term_match_scrutinees_ok argTms" by simp_all
  from ev obtain addr path newFull retVal v newVal where
    ap: "interp_writable_lvalue d fuel full lhs = Inr (addr, path)" and
    call: "interp_function_call d fuel full fnName tyArgs argTms = Inr (newFull, retVal)" and
    cast: "apply_cast_opt castOpt retVal = Inr v" and
    upd: "update_value_at_path (IS_Store newFull ! addr) path v = Inr newVal" and
    res_eq: "res = Continue (newFull \<lparr> IS_Store := (IS_Store newFull)[addr := newVal] \<rparr>)"
    by (auto simp: Let_def split: sum.splits)
  from lvalue_simD[OF IHl fe fs sme wf tl okl ap] obtain f1 where
    f1: "interp_writable_lvalue d f1 (mc_state full) (match_compile_term lhs) = Inr (addr, path)" by auto
  from call_simD[OF IH fe fs sme wf fi args len_ty wk refs oka call] obtain f2 where
    f2: "interp_function_call d f2 (mc_state full) fnName tyArgs (map match_compile_term argTms)
           = Inr (mc_state newFull, retVal)" by auto
  let ?F = "max f1 f2"
  have f1': "interp_writable_lvalue d ?F (mc_state full) (match_compile_term lhs) = Inr (addr, path)"
    by (rule interp_writable_lvalue_Inr_more_fuel[OF f1]) simp
  have f2': "interp_function_call d ?F (mc_state full) fnName tyArgs (map match_compile_term argTms)
               = Inr (mc_state newFull, retVal)"
    by (rule interp_function_call_Inr_more_fuel[OF f2]) simp
  have "interp_statement d (Suc ?F) (mc_state full)
          (CoreStmt_AssignCall g (match_compile_term lhs) castOpt fnName tyArgs
             (map match_compile_term argTms)) = Inr (mc_result res)"
    using f1' f2' cast upd res_eq by (simp add: Let_def)
  thus "\<exists>fuel'. interp_statement d (Suc fuel') (mc_state full)
                  (CoreStmt_AssignCall g (match_compile_term lhs) castOpt fnName tyArgs
                     (map match_compile_term argTms)) = Inr (mc_result res)"
    by blast
qed

lemma sim_Swap:
  assumes IHl: "lvalue_sim fuel lhs" and IHr: "lvalue_sim fuel rhs"
  shows "stmt_sim (Suc fuel) (CoreStmt_Swap g lhs rhs)"
proof (rule stmt_sim_single)
  show "match_compile_statement (CoreStmt_Swap g lhs rhs)
          = [CoreStmt_Swap g (match_compile_term lhs) (match_compile_term rhs)]" by simp
next
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_statement_type env NotGhost (CoreStmt_Swap g lhs rhs) = Some env'"
    and gf: "core_statement_ghost_free (CoreStmt_Swap g lhs rhs)"
    and ok: "core_statement_match_scrutinees_ok (CoreStmt_Swap g lhs rhs)"
    and ev: "interp_statement d (Suc fuel) full (CoreStmt_Swap g lhs rhs) = Inr res"
  from gf have g: "g = NotGhost" by simp
  from typing g obtain lhsTy where
    tl: "core_term_type env NotGhost lhs = Some lhsTy" and
    tr: "core_term_type env NotGhost rhs = Some lhsTy"
    by (auto split: if_splits option.splits)
  from ok have okl: "core_term_match_scrutinees_ok lhs" and okr: "core_term_match_scrutinees_ok rhs"
    by simp_all
  from ev obtain l r newFull where
    l: "interp_writable_lvalue d fuel full lhs = Inr l" and
    r: "interp_writable_lvalue d fuel full rhs = Inr r" and
    sw: "perform_swap full l r = Inr newFull" and
    res_eq: "res = Continue newFull"
    by (auto split: sum.splits)
  from lvalue_simD[OF IHl fe fs sme wf tl okl l] obtain f1 where
    f1: "interp_writable_lvalue d f1 (mc_state full) (match_compile_term lhs) = Inr l" by auto
  from lvalue_simD[OF IHr fe fs sme wf tr okr r] obtain f2 where
    f2: "interp_writable_lvalue d f2 (mc_state full) (match_compile_term rhs) = Inr r" by auto
  let ?F = "max f1 f2"
  have f1': "interp_writable_lvalue d ?F (mc_state full) (match_compile_term lhs) = Inr l"
    by (rule interp_writable_lvalue_Inr_more_fuel[OF f1]) simp
  have f2': "interp_writable_lvalue d ?F (mc_state full) (match_compile_term rhs) = Inr r"
    by (rule interp_writable_lvalue_Inr_more_fuel[OF f2]) simp
  have sw': "perform_swap (mc_state full) l r = Inr (mc_state newFull)"
    using perform_swap_mc[of full l r] sw by simp
  have "interp_statement d (Suc ?F) (mc_state full)
          (CoreStmt_Swap g (match_compile_term lhs) (match_compile_term rhs)) = Inr (mc_result res)"
    using f1' f2' sw' res_eq by simp
  thus "\<exists>fuel'. interp_statement d (Suc fuel') (mc_state full)
                  (CoreStmt_Swap g (match_compile_term lhs) (match_compile_term rhs))
                = Inr (mc_result res)"
    by blast
qed

lemma sim_Return:
  assumes IH: "term_sim fuel tm"
  shows "stmt_sim (Suc fuel) (CoreStmt_Return tm)"
proof (rule stmt_sim_single)
  show "match_compile_statement (CoreStmt_Return tm) = [CoreStmt_Return (match_compile_term tm)]" by simp
next
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and typing: "core_statement_type env NotGhost (CoreStmt_Return tm) = Some env'"
    and ok: "core_statement_match_scrutinees_ok (CoreStmt_Return tm)"
    and ev: "interp_statement d (Suc fuel) full (CoreStmt_Return tm) = Inr res"
  from typing have t: "core_term_type env NotGhost tm = Some (TE_ReturnType env)"
    by (auto split: if_splits)
  from ok have ok': "core_term_match_scrutinees_ok tm" by simp
  from ev obtain v where v: "interp_term d fuel full tm = Inr v" and res_eq: "res = Return full v"
    by (auto split: sum.splits)
  from term_simD[OF IH fe fs sme wf t ok' v] obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term tm) = Inr v" by auto
  have "interp_statement d (Suc f1) (mc_state full) (CoreStmt_Return (match_compile_term tm))
          = Inr (mc_result res)"
    using f1 res_eq by simp
  thus "\<exists>fuel'. interp_statement d (Suc fuel') (mc_state full)
                  (CoreStmt_Return (match_compile_term tm)) = Inr (mc_result res)"
    by blast
qed

(* Ghost-only statements are not ghost-free. *)
lemma sim_not_ghost_free:
  assumes "\<not> core_statement_ghost_free stmt"
  shows "stmt_sim fuel stmt"
  using assms by (intro stmt_simI) simp

(* The state after a statement list that was run in a scope, back in the
   enclosing scope, matches the enclosing environment. *)
lemma restore_scope_matches:
  assumes sme: "state_matches_env full env storeTyping"
      and wf: "tyenv_well_formed env"
      and ng: "TE_ProofGoal env = None"
      and typing: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body = Some envB"
      and ev: "interp_statement_list d fuel full body = Inr (Continue s1)"
  shows "state_matches_env (restore_scope full s1) env storeTyping"
proof -
  let ?env1 = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  have sme1: "state_matches_env full ?env1 storeTyping" using sme by simp
  have wf1: "tyenv_well_formed ?env1"
    using wf by (simp add: tyenv_well_formed_TE_ProofTopLevel_irrelevant)
  have ng1: "TE_ProofGoal ?env1 = None" using ng by simp
  from interp_statement_list_sound[OF sme1 wf1, THEN mp, OF conjI[OF typing ng1], of d fuel] ev
  obtain st1 where sme_s1: "state_matches_env s1 envB st1"
    and ext: "storeTyping_extends storeTyping st1"
    by auto
  from interp_statement_list_static[OF ev] have
    g_eq: "IS_Globals s1 = IS_Globals full" and
    f_eq: "IS_Functions s1 = IS_Functions full" and
    c_eq: "IS_DataCtorsByType s1 = IS_DataCtorsByType full"
    by (simp_all add: static_parts_eq_def)
  from core_statement_list_type_fixed_eq[OF typing] have
    dc: "TE_DataCtors env = TE_DataCtors envB" and
    dt: "TE_Datatypes env = TE_Datatypes envB"
    unfolding tyenv_fixed_eq_def by simp_all
  show ?thesis
    by (rule restore_scope_sound[OF sme sme_s1 ext g_eq f_eq c_eq dc dt])
qed

lemma sim_Block:
  assumes IHs: "stmts_sim fuel body"
  shows "stmt_sim (Suc fuel) (CoreStmt_Block body)"
proof (rule stmt_sim_single)
  show "match_compile_statement (CoreStmt_Block body)
          = [CoreStmt_Block (match_compile_statement_list body)]" by simp
next
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and ng: "TE_ProofGoal env = None"
    and typing: "core_statement_type env NotGhost (CoreStmt_Block body) = Some env'"
    and gf: "core_statement_ghost_free (CoreStmt_Block body)"
    and ok: "core_statement_match_scrutinees_ok (CoreStmt_Block body)"
    and ev: "interp_statement d (Suc fuel) full (CoreStmt_Block body) = Inr res"
  let ?env1 = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  from typing obtain envB where t: "core_statement_list_type ?env1 NotGhost body = Some envB"
    by (auto split: option.splits)
  from gf have gf': "core_statement_list_ghost_free body" by simp
  from ok have ok': "core_statement_list_match_scrutinees_ok body" by simp
  have fe1: "TE_Functions ?env1 = TE_Functions genv" using fe by simp
  have sme1: "state_matches_env full ?env1 storeTyping" using sme by simp
  have wf1: "tyenv_well_formed ?env1" using wf by (simp add: tyenv_well_formed_TE_ProofTopLevel_irrelevant)
  have ng1: "TE_ProofGoal ?env1 = None" using ng by simp
  from ev obtain r0 where r0: "interp_statement_list d fuel full body = Inr r0"
    and res_eq: "res = scope_result full r0"
    by (cases "interp_statement_list d fuel full body") (auto split: ExecResult.splits)
  from stmts_simD[OF IHs fe1 fs sme1 wf1 ng1 t gf' ok' r0] obtain f1 where
    f1: "interp_statement_list d f1 (mc_state full) (match_compile_statement_list body) = Inr (mc_result r0)"
    by auto
  have "interp_statement d (Suc f1) (mc_state full) (CoreStmt_Block (match_compile_statement_list body))
          = Inr (mc_result res)"
    using interp_Block_scope_result[OF f1] res_eq by simp
  thus "\<exists>fuel'. interp_statement d (Suc fuel') (mc_state full)
                  (CoreStmt_Block (match_compile_statement_list body)) = Inr (mc_result res)"
    by blast
qed

lemma sim_While:
  assumes IH: "term_sim fuel condTm" and IHs: "stmts_sim fuel body"
      and IHw: "stmt_sim fuel (CoreStmt_While g condTm invars decrTm body)"
  shows "stmt_sim (Suc fuel) (CoreStmt_While g condTm invars decrTm body)"
proof (rule stmt_simI)
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and ng: "TE_ProofGoal env = None"
    and typing: "core_statement_type env NotGhost (CoreStmt_While g condTm invars decrTm body) = Some env'"
    and gf: "core_statement_ghost_free (CoreStmt_While g condTm invars decrTm body)"
    and ok: "core_statement_match_scrutinees_ok (CoreStmt_While g condTm invars decrTm body)"
    and ev: "interp_statement d (Suc fuel) full (CoreStmt_While g condTm invars decrTm body) = Inr res"
  let ?env1 = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  let ?W = "CoreStmt_While g condTm invars decrTm body"
  let ?W' = "CoreStmt_While g (match_compile_term condTm) (map match_compile_term invars)
               (map_option match_compile_term decrTm) (match_compile_statement_list body)"
  from gf have g: "g = NotGhost" and inv: "invars = []" and decr: "decrTm = None"
    and gf_body: "core_statement_list_ghost_free body" by simp_all
  from typing g obtain envB where
    tc: "core_term_type env NotGhost condTm = Some CoreTy_Bool" and
    tb: "core_statement_list_type ?env1 NotGhost body = Some envB"
    by (auto split: if_splits option.splits CoreType.splits)
  from ok have okc: "core_term_match_scrutinees_ok condTm"
    and okb: "core_statement_list_match_scrutinees_ok body" by simp_all
  have fe1: "TE_Functions ?env1 = TE_Functions genv" using fe by simp
  have sme1: "state_matches_env full ?env1 storeTyping" using sme by simp
  have wf1: "tyenv_well_formed ?env1" using wf by (simp add: tyenv_well_formed_TE_ProofTopLevel_irrelevant)
  have ng1: "TE_ProofGoal ?env1 = None" using ng by simp
  have W'_eq: "match_compile_statement ?W = [?W']" by simp
  \<comment> \<open>The evaluation of the original loop: the empty invariant list and the
     absent decreases-term always pass.\<close>
  from ev inv decr obtain fuel0 where fuel_eq: "fuel = Suc fuel0" by (cases fuel) simp_all
  from ev inv decr fuel_eq obtain cv where cv: "interp_term d fuel full condTm = Inr cv"
    by (auto simp: conditions_error_def split: sum.splits)
  from term_simD[OF IH fe fs sme wf tc okc cv] obtain f1 where
    f1: "interp_term d f1 (mc_state full) (match_compile_term condTm) = Inr cv" by auto
  show "\<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement ?W)
                 = Inr (mc_result res)"
  proof (cases "cv = CV_Bool False")
    case True
    with ev inv decr fuel_eq cv have res_eq: "res = Continue full"
      by (simp add: conditions_error_def)
    have "interp_statement d (Suc (Suc f1)) (mc_state full) ?W' = Inr (mc_result res)"
      using f1 True res_eq inv decr
      by (simp add: conditions_error_def interp_term_Inr_more_fuel[OF f1, of "Suc f1"])
    from interp_statement_list_single[OF this] show ?thesis unfolding W'_eq by blast
  next
    case False
    with ev inv decr fuel_eq cv have cv_true: "cv = CV_Bool True"
      by (auto simp: conditions_error_def split: CoreValue.splits bool.splits)
    from ev inv decr fuel_eq cv cv_true obtain r0 where
      r0: "interp_statement_list d fuel full body = Inr r0"
      by (auto simp: conditions_error_def split: sum.splits)
    from stmts_simD[OF IHs fe1 fs sme1 wf1 ng1 tb gf_body okb r0] obtain f2 where
      f2: "interp_statement_list d f2 (mc_state full) (match_compile_statement_list body)
             = Inr (mc_result r0)" by auto
    show ?thesis
    proof (cases r0)
      case (Return s1 v)
      with ev inv decr fuel_eq cv cv_true r0 have res_eq: "res = Return (restore_scope full s1) v"
        by (simp add: conditions_error_def)
      let ?F = "Suc (max f1 f2)"
      have f1': "interp_term d ?F (mc_state full) (match_compile_term condTm) = Inr cv"
        by (rule interp_term_Inr_more_fuel[OF f1]) simp
      have f2': "interp_statement_list d ?F (mc_state full) (match_compile_statement_list body)
                   = Inr (mc_result r0)"
        by (rule interp_statement_list_Inr_more_fuel[OF f2]) simp
      have "interp_statement d (Suc ?F) (mc_state full) ?W' = Inr (mc_result res)"
        using f1' f2' cv_true Return res_eq inv decr by (simp add: conditions_error_def)
      from interp_statement_list_single[OF this] show ?thesis unfolding W'_eq by blast
    next
      case (Continue s1)
      let ?full2 = "restore_scope full s1"
      from ev inv decr fuel_eq cv cv_true r0 Continue have
        rec: "interp_statement d fuel ?full2 ?W = Inr res"
        by (simp add: conditions_error_def)
      have sme2: "state_matches_env ?full2 env storeTyping"
        using restore_scope_matches[OF sme wf ng tb] r0 Continue by simp
      have fs2: "IS_Functions ?full2 = funs"
        using interp_statement_list_static[OF r0] Continue fs by (simp add: static_parts_eq_def)
      from stmt_simD[OF IHw fe fs2 sme2 wf ng typing gf ok rec] obtain f3 where
        "interp_statement_list d f3 (mc_state ?full2) (match_compile_statement ?W) = Inr (mc_result res)"
        by auto
      from interp_statement_list_single_D[OF this[unfolded W'_eq]] obtain f3' where
        f3: "interp_statement d f3' (mc_state ?full2) ?W' = Inr (mc_result res)" by blast
      let ?F = "Suc (max f1 (max f2 f3'))"
      have f1': "interp_term d ?F (mc_state full) (match_compile_term condTm) = Inr cv"
        by (rule interp_term_Inr_more_fuel[OF f1]) simp
      have f2': "interp_statement_list d ?F (mc_state full) (match_compile_statement_list body)
                   = Inr (mc_result r0)"
        by (rule interp_statement_list_Inr_more_fuel[OF f2]) simp
      have f3'': "interp_statement d ?F (restore_scope (mc_state full) (mc_state s1)) ?W'
                    = Inr (mc_result res)"
        using interp_statement_Inr_more_fuel[OF f3, of ?F] by simp
      have "interp_statement d (Suc ?F) (mc_state full) ?W' = Inr (mc_result res)"
        using f1' f2' f3'' cv_true Continue inv decr by (simp add: conditions_error_def)
      from interp_statement_list_single[OF this] show ?thesis unfolding W'_eq by blast
    qed
  qed
qed

lemma sim_Match_stmt:
  assumes IH: "term_sim fuel scrut" and IHs: "\<And>stmts. stmts_sim fuel stmts"
  shows "stmt_sim (Suc fuel) (CoreStmt_Match g scrut arms)"
proof (rule stmt_simI)
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and ng: "TE_ProofGoal env = None"
    and typing: "core_statement_type env NotGhost (CoreStmt_Match g scrut arms) = Some env'"
    and gf: "core_statement_ghost_free (CoreStmt_Match g scrut arms)"
    and ok: "core_statement_match_scrutinees_ok (CoreStmt_Match g scrut arms)"
    and ev: "interp_statement d (Suc fuel) full (CoreStmt_Match g scrut arms) = Inr res"
  let ?env1 = "env \<lparr> TE_ProofTopLevel := False \<rparr>"
  let ?arms' = "map (\<lambda>(p, body). (p, match_compile_statement_list body)) arms"
  from gf have g: "g = NotGhost"
    and gf_arms: "list_all (\<lambda>(_, body). core_statement_list_ghost_free body) arms" by simp_all
  from typing g obtain scrutTy where
    s_ty: "core_term_type env NotGhost scrut = Some scrutTy" and
    pats: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    bodies: "list_all (\<lambda>body. core_statement_list_type ?env1 NotGhost body \<noteq> None) (map snd arms)"
    by (auto simp: Let_def split: option.splits if_splits)
  from ok have ok_s: "core_term_match_scrutinees_ok scrut"
    and ok_arms: "list_all (\<lambda>(_, body). core_statement_list_match_scrutinees_ok body) arms"
    and var_or_flat: "arms_flat arms \<or> (\<exists>x. scrut = CoreTm_Var x)" by simp_all
  have fe1: "TE_Functions ?env1 = TE_Functions genv" using fe by simp
  have sme1: "state_matches_env full ?env1 storeTyping" using sme by simp
  have wf1: "tyenv_well_formed ?env1" using wf by (simp add: tyenv_well_formed_TE_ProofTopLevel_irrelevant)
  have ng1: "TE_ProofGoal ?env1 = None" using ng by simp
  from ev obtain sv where sv: "interp_term d fuel full scrut = Inr sv"
    by (cases "interp_term d fuel full scrut") auto
  from ev sv obtain armStmts where arm: "find_matching_arm sv arms = Inr armStmts"
    by (cases "find_matching_arm sv arms") auto
  from ev sv arm obtain r0 where r0: "interp_statement_list d fuel full armStmts = Inr r0"
    by (cases "interp_statement_list d fuel full armStmts") auto
  have res_eq: "res = scope_result full r0"
    using interp_Match_scope_result[OF sv arm r0] ev by simp
  from find_matching_arm_in_arms[OF arm] obtain p where arm_in: "(p, armStmts) \<in> set arms" by auto
  from bodies arm_in obtain envB where
    tb: "core_statement_list_type ?env1 NotGhost armStmts = Some envB"
    by (auto simp: list_all_iff)
  from gf_arms arm_in have gfb: "core_statement_list_ghost_free armStmts" by (auto simp: list_all_iff)
  from ok_arms arm_in have okb: "core_statement_list_match_scrutinees_ok armStmts"
    by (auto simp: list_all_iff)
  from stmts_simD[OF IHs fe1 fs sme1 wf1 ng1 tb gfb okb r0] obtain f2 where
    f2: "interp_statement_list d f2 (mc_state full) (match_compile_statement_list armStmts)
           = Inr (mc_result r0)" by auto
  have arm': "find_matching_arm sv ?arms' = Inr (match_compile_statement_list armStmts)"
    by (rule find_matching_arm_map[OF arm])
  show "\<exists>fuel'. interp_statement_list d fuel' (mc_state full)
                  (match_compile_statement (CoreStmt_Match g scrut arms)) = Inr (mc_result res)"
  proof (cases "arms_flat arms")
    case True
    from term_simD[OF IH fe fs sme wf s_ty ok_s sv] obtain f1 where
      f1: "interp_term d f1 (mc_state full) (match_compile_term scrut) = Inr sv" by auto
    let ?F = "max f1 f2"
    have f1': "interp_term d ?F (mc_state full) (match_compile_term scrut) = Inr sv"
      by (rule interp_term_Inr_more_fuel[OF f1]) simp
    have f2': "interp_statement_list d ?F (mc_state full) (match_compile_statement_list armStmts)
                 = Inr (mc_result r0)"
      by (rule interp_statement_list_Inr_more_fuel[OF f2]) simp
    have run: "interp_statement d (Suc ?F) (mc_state full)
                 (CoreStmt_Match g (match_compile_term scrut) ?arms') = Inr (mc_result res)"
      using interp_Match_scope_result[OF f1' arm' f2'] res_eq by simp
    have compiled_eq: "match_compile_statement (CoreStmt_Match g scrut arms)
                         = [CoreStmt_Match g (match_compile_term scrut) ?arms']"
      using True by (simp add: Let_def)
    from interp_statement_list_single[OF run] show ?thesis unfolding compiled_eq by blast
  next
    case False
    with var_or_flat obtain x where scrut_eq: "scrut = CoreTm_Var x" by auto
    have ne: "arms \<noteq> []" using False by (cases arms) (auto simp: arms_flat_def)
    have ne': "?arms' \<noteq> []" using ne by simp
    have pats': "list_all (\<lambda>(p, _). pattern_compatible env p scrutTy) ?arms'"
      using pats by (auto simp: list_all_iff)
    from sv scrut_eq obtain n where sv': "interp_term d (Suc n) full (CoreTm_Var x) = Inr sv"
      by (cases fuel) auto
    have s_ty': "core_term_type env NotGhost (CoreTm_Var x) = Some scrutTy"
      using s_ty scrut_eq by simp
    have tree: "match_tree_eval (var_env full) (compile_match_tree (CoreTm_Var x) ?arms')
                  = arms_first_match sv ?arms'"
      by (rule compile_match_tree_eval[OF sme wf s_ty' pats' ne' sv'])
    have "arms_first_match sv ?arms' = Some (match_compile_statement_list armStmts)"
      unfolding arms_first_match_find_matching_arm arm' by simp
    with tree have tree': "match_tree_eval (var_env (mc_state full))
                             (compile_match_tree (CoreTm_Var x) ?arms')
                           = Some (match_compile_statement_list armStmts)"
      by simp
    have sv_mc: "interp_term d (Suc f2) (mc_state full) (CoreTm_Var x) = Inr sv"
      using sv' by (simp only: interp_term_Var_mc interp_term_Var_fuel[of d f2 full x d n])
    have compiled_eq: "match_compile_statement (CoreStmt_Match g scrut arms)
                         = compile_match_statement g (CoreTm_Var x) ?arms'"
      using False scrut_eq by (simp add: Let_def)
    show ?thesis
    proof (cases "compile_match_tree (CoreTm_Var x) ?arms'")
      case (MT_Leaf b)
      \<comment> \<open>The first arm always matches: the compiled statement is a match with
         one wildcard arm, whose body is the compiled body of that arm.\<close>
      with tree' have b_eq: "b = match_compile_statement_list armStmts" by simp
      have f2s: "interp_statement_list d (Suc f2) (mc_state full)
                   (match_compile_statement_list armStmts) = Inr (mc_result r0)"
        by (rule interp_statement_list_Inr_more_fuel[OF f2]) simp
      have run2: "interp_statement d (Suc (Suc f2)) (mc_state full)
                    (CoreStmt_Match g (CoreTm_Var x) [(CorePat_Wildcard, b)]) = Inr (mc_result res)"
        using interp_Match_scope_result[OF sv_mc _ f2s, of "[(CorePat_Wildcard, b)]" g] b_eq res_eq
        by simp
      have compiled_eq2: "match_compile_statement (CoreStmt_Match g scrut arms)
                            = [CoreStmt_Match g (CoreTm_Var x) [(CorePat_Wildcard, b)]]"
        unfolding compiled_eq compile_match_statement_def MT_Leaf by (simp add: Let_def)
      from interp_statement_list_single[OF run2] show ?thesis unfolding compiled_eq2 by blast
    next
      case (MT_Test s arms'')
      from match_tree_to_statements_exec[OF tree' f2, of g] obtain f3 where
        f3: "interp_statement_list d f3 (mc_state full)
               (match_tree_to_statements g (compile_match_tree (CoreTm_Var x) ?arms'))
             = Inr (case compile_match_tree (CoreTm_Var x) ?arms' of
                      MT_Leaf _ \<Rightarrow> mc_result r0
                    | MT_Test _ _ \<Rightarrow> scope_result (mc_state full) (mc_result r0))"
        by blast
      have f3': "interp_statement_list d f3 (mc_state full)
                   (match_tree_to_statements g (compile_match_tree (CoreTm_Var x) ?arms'))
                 = Inr (scope_result (mc_state full) (mc_result r0))"
        using f3 by (simp add: MT_Test)
      have compiled_eq3: "match_compile_statement (CoreStmt_Match g scrut arms)
                            = match_tree_to_statements g (compile_match_tree (CoreTm_Var x) ?arms')"
        unfolding compiled_eq compile_match_statement_def by (simp add: MT_Test)
      show ?thesis
        unfolding compiled_eq3 res_eq mc_result_scope_result using f3' by blast
    qed
  qed
qed


section \<open>Statement lists\<close>

lemma sim_stmts_Nil: "stmts_sim (Suc fuel) []"
proof (rule stmts_simI)
  fix full :: "'w InterpState" and res
  assume "interp_statement_list d (Suc fuel) full [] = Inr res"
  hence "res = Continue full" by simp
  hence "interp_statement_list d (Suc fuel) (mc_state full) (match_compile_statement_list [])
           = Inr (mc_result res)" by simp
  thus "\<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement_list [])
                 = Inr (mc_result res)" by blast
qed

lemma sim_stmts_Cons:
  assumes IH: "stmt_sim fuel stmt" and IHs: "stmts_sim fuel stmts"
  shows "stmts_sim (Suc fuel) (stmt # stmts)"
proof (rule stmts_simI)
  fix env env' storeTyping and full :: "'w InterpState" and res
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and ng: "TE_ProofGoal env = None"
    and typing: "core_statement_list_type env NotGhost (stmt # stmts) = Some env'"
    and gf: "core_statement_list_ghost_free (stmt # stmts)"
    and ok: "core_statement_list_match_scrutinees_ok (stmt # stmts)"
    and ev: "interp_statement_list d (Suc fuel) full (stmt # stmts) = Inr res"
  from typing obtain env1 where
    t1: "core_statement_type env NotGhost stmt = Some env1" and
    t2: "core_statement_list_type env1 NotGhost stmts = Some env'"
    by (auto split: option.splits)
  from gf have gf1: "core_statement_ghost_free stmt" and gf2: "core_statement_list_ghost_free stmts"
    by simp_all
  from ok have ok1: "core_statement_match_scrutinees_ok stmt"
    and ok2: "core_statement_list_match_scrutinees_ok stmts" by simp_all
  from ev obtain r1 where r1: "interp_statement d fuel full stmt = Inr r1" by (auto split: sum.splits)
  from stmt_simD[OF IH fe fs sme wf ng t1 gf1 ok1 r1] obtain f1 where
    f1: "interp_statement_list d f1 (mc_state full) (match_compile_statement stmt) = Inr (mc_result r1)"
    by auto
  show "\<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement_list (stmt # stmts))
                 = Inr (mc_result res)"
  proof (cases r1)
    case (Return s1 v)
    with ev r1 have res_eq: "res = Return s1 v" by simp
    have "interp_statement_list d f1 (mc_state full)
            (match_compile_statement stmt @ match_compile_statement_list stmts) = Inr (mc_result res)"
      using interp_statement_list_append_Return[OF f1[unfolded Return mc_result.simps]] res_eq by simp
    thus ?thesis by auto
  next
    case (Continue s1)
    with ev r1 have rest: "interp_statement_list d fuel s1 stmts = Inr res" by simp
    \<comment> \<open>The state after the first statement matches the environment after it.\<close>
    from interp_statement_sound[OF sme wf, THEN mp, OF conjI[OF t1 ng], of d fuel] r1 Continue
    obtain st1 where sme1: "state_matches_env s1 env1 st1" by auto
    have wf1: "tyenv_well_formed env1" by (rule core_statement_type_preserves_well_formed[OF t1 wf])
    have ng1: "TE_ProofGoal env1 = None" by (rule core_statement_type_preserves_proof_goal_none[OF t1 ng])
    have fe1: "TE_Functions env1 = TE_Functions genv"
      using core_statement_type_fixed_eq[OF t1] fe unfolding tyenv_fixed_eq_def by simp
    have fs1: "IS_Functions s1 = funs"
      using interp_statement_static[OF r1] Continue fs by (simp add: static_parts_eq_def)
    from stmts_simD[OF IHs fe1 fs1 sme1 wf1 ng1 t2 gf2 ok2 rest] obtain f2 where
      f2: "interp_statement_list d f2 (mc_state s1) (match_compile_statement_list stmts)
             = Inr (mc_result res)" by auto
    from interp_statement_list_append_Continue[OF f1[unfolded Continue mc_result.simps] f2]
    show ?thesis by simp
  qed
qed

end

end

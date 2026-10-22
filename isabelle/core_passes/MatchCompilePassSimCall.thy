theory MatchCompilePassSimCall
  imports MatchCompilePassSimStmts
begin

(* The simulation for the match compilation pass: the function call case of
   the induction step. See MatchCompilePassSimTerms.thy for the setting.

   A call evaluates its arguments, binds them in a fresh frame, runs the body
   (or the extern function) and restores the caller's frame. The compiled
   call does the same with the compiled arguments and the compiled body, and
   the frame operations commute with mc_state. The callee's frame matches the
   callee's body environment by the argument lemma of the type soundness
   proof (fold_process_one_arg_sound), which is what the induction hypothesis
   for the body needs. *)


section \<open>Argument results\<close>

(* The ref results that an extern call passes on (those of the Ref
   parameters) only depend on the results at Ref positions. *)
lemma ref_results_selection_eq:
  assumes "length refs' = length refs" and "length args = length refs"
      and "\<And>i. i < length args \<Longrightarrow> snd (args ! i) = Ref \<Longrightarrow> refs' ! i = refs ! i"
  shows "map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError) (zip args refs')
         = map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError) (zip args refs)"
proof (rule nth_equalityI)
  show "length (map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError) (zip args refs'))
        = length (map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError) (zip args refs))"
    using assms(1,2) by simp
next
  fix i
  assume "i < length (map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError) (zip args refs'))"
  hence i_lt: "i < length args" using assms(1,2) by simp
  obtain name vr where a_eq: "args ! i = (name, vr)" by (cases "args ! i")
  show "map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError) (zip args refs') ! i
        = map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError) (zip args refs) ! i"
  proof (cases vr)
    case Var
    with i_lt assms(1,2) a_eq show ?thesis by simp
  next
    case Ref
    with assms(3)[OF i_lt] a_eq have "refs' ! i = refs ! i" by simp
    with i_lt assms(1,2) a_eq show ?thesis by simp
  qed
qed


context match_compile_sim
begin

section \<open>The arguments of a call at one fuel\<close>

(* The compiled argument, evaluated at fuel n in the compiled state, agrees
   with the original argument (as a term and as an lvalue) wherever the
   original succeeds at fuel `fuel`. *)
definition args_agree :: "nat \<Rightarrow> 'w InterpState \<Rightarrow> nat \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "args_agree fuel full n tm \<longleftrightarrow>
     (\<forall>v. interp_term d fuel full tm = Inr v
          \<longrightarrow> interp_term d n (mc_state full) (match_compile_term tm) = Inr v)
   \<and> (\<forall>r. interp_writable_lvalue d fuel full tm = Inr r
          \<longrightarrow> interp_writable_lvalue d n (mc_state full) (match_compile_term tm) = Inr r)"

lemma args_agree_mono:
  "args_agree fuel full n tm \<Longrightarrow> n \<le> n' \<Longrightarrow> args_agree fuel full n' tm"
  unfolding args_agree_def
  using interp_term_Inr_more_fuel interp_writable_lvalue_Inr_more_fuel by blast

lemma args_agree_term:
  "args_agree fuel full n tm \<Longrightarrow> interp_term d fuel full tm = Inr v
   \<Longrightarrow> interp_term d n (mc_state full) (match_compile_term tm) = Inr v"
  unfolding args_agree_def by blast

lemma args_agree_lvalue:
  "args_agree fuel full n tm \<Longrightarrow> interp_writable_lvalue d fuel full tm = Inr r
   \<Longrightarrow> interp_writable_lvalue d n (mc_state full) (match_compile_term tm) = Inr r"
  unfolding args_agree_def by blast

(* By the induction hypotheses, all the arguments of a call agree at one
   fuel. *)
lemma compiled_args_one_fuel:
  assumes IH_tm: "\<And>tm. term_sim fuel tm" and IH_lv: "\<And>tm. lvalue_sim fuel tm"
      and fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
      and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
      and typed: "\<And>tm. tm \<in> set argTms \<Longrightarrow> \<exists>ty. core_term_type env NotGhost tm = Some ty"
      and ok: "list_all core_term_match_scrutinees_ok argTms"
  shows "\<exists>n. \<forall>tm \<in> set argTms. args_agree fuel full n tm"
proof (rule ex_fuel_all)
  fix tm assume tm_in: "tm \<in> set argTms"
  from typed[OF tm_in] obtain ty where t: "core_term_type env NotGhost tm = Some ty" by blast
  from ok tm_in have ok1: "core_term_match_scrutinees_ok tm" by (simp add: list_all_iff)
  have "\<exists>n1. \<forall>v. interp_term d fuel full tm = Inr v
                 \<longrightarrow> interp_term d n1 (mc_state full) (match_compile_term tm) = Inr v"
  proof (cases "interp_term d fuel full tm")
    case (Inl err)
    thus ?thesis by simp
  next
    case (Inr v)
    from term_simD[OF IH_tm fe fs sme wf t ok1 Inr] Inr show ?thesis by auto
  qed
  then obtain n1 where
    n1: "\<forall>v. interp_term d fuel full tm = Inr v
             \<longrightarrow> interp_term d n1 (mc_state full) (match_compile_term tm) = Inr v" by blast
  have "\<exists>n2. \<forall>r. interp_writable_lvalue d fuel full tm = Inr r
                 \<longrightarrow> interp_writable_lvalue d n2 (mc_state full) (match_compile_term tm) = Inr r"
  proof (cases "interp_writable_lvalue d fuel full tm")
    case (Inl err)
    thus ?thesis by simp
  next
    case (Inr r)
    from lvalue_simD[OF IH_lv fe fs sme wf t ok1 Inr] Inr show ?thesis by auto
  qed
  then obtain n2 where
    n2: "\<forall>r. interp_writable_lvalue d fuel full tm = Inr r
             \<longrightarrow> interp_writable_lvalue d n2 (mc_state full) (match_compile_term tm) = Inr r" by blast
  have "args_agree fuel full (max n1 n2) tm"
    unfolding args_agree_def
  proof (intro conjI allI impI)
    fix v assume "interp_term d fuel full tm = Inr v"
    with n1 have "interp_term d n1 (mc_state full) (match_compile_term tm) = Inr v" by blast
    thus "interp_term d (max n1 n2) (mc_state full) (match_compile_term tm) = Inr v"
      by (rule interp_term_Inr_more_fuel) simp
  next
    fix r assume "interp_writable_lvalue d fuel full tm = Inr r"
    with n2 have "interp_writable_lvalue d n2 (mc_state full) (match_compile_term tm) = Inr r" by blast
    thus "interp_writable_lvalue d (max n1 n2) (mc_state full) (match_compile_term tm) = Inr r"
      by (rule interp_writable_lvalue_Inr_more_fuel) simp
  qed
  thus "\<exists>n. args_agree fuel full n tm" by blast
next
  fix n n' tm
  assume "tm \<in> set argTms" and a: "args_agree fuel full n tm" and le: "n \<le> n'"
  from args_agree_mono[OF a le] show "args_agree fuel full n' tm" .
qed


section \<open>Function calls\<close>

lemma sim_call:
  assumes IH_tm: "\<And>tm. term_sim fuel tm" and IH_lv: "\<And>tm. lvalue_sim fuel tm"
      and IH_stmts: "\<And>stmts. stmts_sim fuel stmts"
  shows "call_sim (Suc fuel) fnName tyArgs argTms"
proof (rule call_simI)
  fix env storeTyping and full :: "'w InterpState" and funInfo newFull retVal
  assume fe: "TE_Functions env = TE_Functions genv" and fs: "IS_Functions full = funs"
    and sme: "state_matches_env full env storeTyping" and wf: "tyenv_well_formed env"
    and fi: "fmlookup (TE_Functions env) fnName = Some funInfo"
    and args_typed: "list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
         argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))"
    and len_ty: "length tyArgs = length (FI_TyArgs funInfo)"
    and wk: "list_all (is_well_kinded env) tyArgs"
    and refs_w: "\<forall>i < length argTms.
          fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow> is_writable_lvalue env (argTms ! i)"
    and ok: "list_all core_term_match_scrutinees_ok argTms"
    and ev: "interp_function_call d (Suc fuel) full fnName tyArgs argTms = Inr (newFull, retVal)"

  \<comment> \<open>Take the original call apart.\<close>
  let ?refsF = "map (interp_writable_lvalue d fuel full) argTms"
  let ?valsF = "map (interp_term d fuel full) argTms"
  from interp_function_call_InrE[OF ev] obtain f preF where
    f_lookup: "fmlookup (IS_Functions full) fnName = Some f" and
    len_args: "length argTms = length (IF_Args f)" and
    len_tys: "length tyArgs = length (IF_TyArgs f)" and
    foldF: "fold process_one_arg (zip (IF_Args f) (zip ?refsF ?valsF))
              (Inr (full \<lparr> IS_Locals := fmempty, IS_Refs := fmempty, IS_ConstLocals := {||},
                           IS_TyArgs := fmap_of_list (zip (IF_TyArgs f)
                                          (map (apply_subst (IS_TyArgs full)) tyArgs)) \<rparr>))
            = Inr preF" and
    bodyF: "call_body (interp_statement_list d fuel) full f ?refsF ?valsF preF
              = Inr (newFull, retVal)" .
  let ?tySubst = "fmap_of_list (zip (IF_TyArgs f) (map (apply_subst (IS_TyArgs full)) tyArgs))"
  let ?cleared = "full \<lparr> IS_Locals := fmempty, IS_Refs := fmempty, IS_ConstLocals := {||},
                         IS_TyArgs := ?tySubst \<rparr>"
  have f_lookup': "fmlookup funs fnName = Some f" using f_lookup fs by simp
  from funs_match_compilable_fun[OF fmc f_lookup'] have
    req: "IF_Requires f = []" and ens: "IF_Ensures f = []" and
    body_props: "\<And>body. IF_Body f = Inl body
                  \<Longrightarrow> core_statement_list_ghost_free body \<and> core_statement_list_match_scrutinees_ok body"
    by blast+
  from funs_match_compilable_info[OF fmc fi[unfolded fe]]
  have ngF: "FI_Ghost funInfo = NotGhost" by simp

  \<comment> \<open>The typing of the arguments.\<close>
  have len_args_fi: "length argTms = length (FI_TmArgs funInfo)"
    using list_all2_lengthD[OF args_typed] by simp
  let ?expTy = "\<lambda>i. apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                (fst (FI_TmArgs funInfo ! i))"
  have arg_ty: "core_term_type env NotGhost (argTms ! i) = Some (?expTy i)"
    if "i < length argTms" for i
    using list_all2_nthD[OF args_typed that] that len_args_fi by (simp add: case_prod_beta)
  have typed: "\<And>tm. tm \<in> set argTms \<Longrightarrow> \<exists>ty. core_term_type env NotGhost tm = Some ty"
    using arg_ty by (auto simp: in_set_conv_nth)

  \<comment> \<open>The compiled arguments agree with the original ones at some fuel F0.\<close>
  from compiled_args_one_fuel[OF IH_tm IH_lv fe fs sme wf typed ok] obtain F0 where
    F0: "\<forall>tm \<in> set argTms. args_agree fuel full F0 tm" by blast

  \<comment> \<open>The function of the state against its signature.\<close>
  have fes: "funs_exist_in_state full env" using sme unfolding state_matches_env_def by blast
  have abs_empty: "TE_AbstractTypes env = {||}" using sme unfolding state_matches_env_def by blast
  have fi_match: "fun_info_matches_interp_fun env funInfo f"
    using fes fi f_lookup unfolding funs_exist_in_state_def by (auto split: option.splits)
  have tyargs_eq: "FI_TyArgs funInfo = IF_TyArgs f"
    using fi_match unfolding fun_info_matches_interp_fun_def by simp
  have len_fi: "length (FI_TmArgs funInfo) = length (IF_Args f)"
    using fi_match unfolding fun_info_matches_interp_fun_def by (auto dest: list_all2_lengthD)

  \<comment> \<open>The callee's frame matches the callee's body environment (type soundness).\<close>
  have vals_sound: "\<forall>i < length (FI_TmArgs funInfo).
                      sound_term_result full env (?expTy i) (?valsF ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < length (FI_TmArgs funInfo)"
    hence i_lt': "i < length argTms" using len_args_fi by simp
    have "sound_term_result full env (?expTy i) (interp_term d fuel full (argTms ! i))"
      by (rule interp_term_sound[OF sme wf, THEN mp, OF arg_ty[OF i_lt']])
    thus "sound_term_result full env (?expTy i) (?valsF ! i)" using i_lt' by simp
  qed
  have lvals_sound: "\<forall>i < length (FI_TmArgs funInfo).
                       fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
                         sound_lvalue_result full env storeTyping (?expTy i) (?refsF ! i)"
  proof (intro allI impI)
    fix i assume i_lt: "i < length (FI_TmArgs funInfo)"
      and is_ref: "fst (snd (FI_TmArgs funInfo ! i)) = Ref"
    hence i_lt': "i < length argTms" using len_args_fi by simp
    have wlv: "is_writable_lvalue env (argTms ! i)" using refs_w i_lt' is_ref by blast
    have "sound_lvalue_result full env storeTyping (?expTy i)
            (interp_writable_lvalue d fuel full (argTms ! i))"
      by (rule interp_writable_lvalue_sound[OF sme wf, THEN mp, OF conjI[OF wlv arg_ty[OF i_lt']]])
    thus "sound_lvalue_result full env storeTyping (?expTy i) (?refsF ! i)" using i_lt' by simp
  qed
  note arg_sound = fold_process_one_arg_sound
                     [OF sme wf fi fi_match len_ty wk vals_sound lvals_sound len_args_fi]
  let ?envB = "body_env_for env (map fst (IF_Args f)) funInfo"
  obtain bodyST where sme_body: "state_matches_env preF ?envB bodyST"
    using arg_sound[unfolded tyargs_eq] foldF
    unfolding sound_arg_processing_result_def by auto
  have len_names: "length (map fst (IF_Args f)) = length (FI_TmArgs funInfo)" using len_fi by simp
  have wfB: "tyenv_well_formed ?envB"
    by (rule body_env_for_well_formed[OF wf fi abs_empty len_names])
  have ngB: "TE_ProofGoal ?envB = None" by (simp add: body_env_for_def)
  have feB: "TE_Functions ?envB = TE_Functions genv" by (simp add: body_env_for_def fe)
  have fsP: "IS_Functions preF = funs"
    using fold_process_one_arg_preserves_globals_funs[OF foldF] fs by simp

  \<comment> \<open>Binding the compiled arguments, at any fuel at which they agree, gives
      the compiled callee frame.\<close>
  have compiled_fold:
    "fold process_one_arg
       (zip (IF_Args (mc_interp_fun f))
            (zip (map (interp_writable_lvalue d G (mc_state full)) (map match_compile_term argTms))
                 (map (interp_term d G (mc_state full)) (map match_compile_term argTms))))
       (Inr ((mc_state full) \<lparr> IS_Locals := fmempty, IS_Refs := fmempty, IS_ConstLocals := {||},
                              IS_TyArgs := fmap_of_list (zip (IF_TyArgs (mc_interp_fun f))
                                             (map (apply_subst (IS_TyArgs (mc_state full))) tyArgs)) \<rparr>))
     = Inr (mc_state preF)"
    if agree: "\<forall>tm \<in> set argTms. args_agree fuel full G tm" for G
  proof -
    have "fold process_one_arg
            (zip (IF_Args f)
                 (zip (map (interp_writable_lvalue d G (mc_state full)) (map match_compile_term argTms))
                      (map (interp_term d G (mc_state full)) (map match_compile_term argTms))))
            (Inr (mc_state ?cleared)) = Inr (mc_state preF)"
    proof (rule fold_process_one_arg_mc[OF foldF])
      show "length (IF_Args f) = length ?refsF" using len_args by simp
      show "length ?refsF = length ?valsF" by simp
      show "length (map (interp_writable_lvalue d G (mc_state full)) (map match_compile_term argTms))
            = length ?refsF" by simp
      show "length (map (interp_term d G (mc_state full)) (map match_compile_term argTms))
            = length ?valsF" by simp
    next
      fix i v assume i_lt: "i < length ?valsF" and "?valsF ! i = Inr v"
      hence ev_i: "interp_term d fuel full (argTms ! i) = Inr v" by simp
      have "args_agree fuel full G (argTms ! i)"
        using bspec[OF agree nth_mem[of i argTms]] i_lt by simp
      from args_agree_term[OF this ev_i]
      show "map (interp_term d G (mc_state full)) (map match_compile_term argTms) ! i = Inr v"
        using i_lt by simp
    next
      fix i l assume i_lt: "i < length ?refsF" and "?refsF ! i = Inr l"
      hence ev_i: "interp_writable_lvalue d fuel full (argTms ! i) = Inr l" by simp
      have "args_agree fuel full G (argTms ! i)"
        using bspec[OF agree nth_mem[of i argTms]] i_lt by simp
      from args_agree_lvalue[OF this ev_i]
      show "map (interp_writable_lvalue d G (mc_state full)) (map match_compile_term argTms) ! i = Inr l"
        using i_lt by simp
    qed
    thus ?thesis by simp
  qed

  \<comment> \<open>The remaining ingredients of the compiled call.\<close>
  have lk: "fmlookup (IS_Functions (mc_state full)) fnName = Some (mc_interp_fun f)"
    by (simp add: f_lookup)
  have lenA: "length (map match_compile_term argTms) = length (IF_Args (mc_interp_fun f))"
    by (simp add: len_args)
  have lenT: "length tyArgs = length (IF_TyArgs (mc_interp_fun f))" by (simp add: len_tys)
  have req': "IF_Requires (mc_interp_fun f) = []" by (simp add: req)
  have ens': "IF_Ensures (mc_interp_fun f) = []" by (simp add: ens)

  show "\<exists>fuel'. interp_function_call d fuel' (mc_state full) fnName tyArgs
                  (map match_compile_term argTms) = Inr (mc_state newFull, retVal)"
  proof (cases "IF_Body f")
    case (Inl body)
    \<comment> \<open>A Babylon body: run the compiled body in the compiled frame.\<close>
    from bodyF Inl obtain postF where
      bodyEval: "interp_statement_list d fuel preF body = Inr (Return postF retVal)" and
      newFull_eq: "newFull = restore_scope full postF"
      by (auto simp: call_body_def split: sum.splits ExecResult.splits)
    from fi_match Inl have "core_statement_list_type ?envB (FI_Ghost funInfo) body \<noteq> None"
      unfolding fun_info_matches_interp_fun_def by simp
    then obtain envB' where bodyT: "core_statement_list_type ?envB NotGhost body = Some envB'"
      using ngF by auto
    from body_props[OF Inl] have gfB: "core_statement_list_ghost_free body"
      and okB: "core_statement_list_match_scrutinees_ok body" by simp_all
    from stmts_simD[OF IH_stmts feB fsP sme_body wfB ngB bodyT gfB okB bodyEval] obtain F1 where
      F1: "interp_statement_list d F1 (mc_state preF) (match_compile_statement_list body)
             = Inr (Return (mc_state postF) retVal)" by auto
    let ?G = "max F0 F1"
    have agreeG: "\<forall>tm \<in> set argTms. args_agree fuel full ?G tm"
      using F0 args_agree_mono[OF _ max.cobounded1] by blast
    have F1': "interp_statement_list d ?G (mc_state preF) (match_compile_statement_list body)
                 = Inr (Return (mc_state postF) retVal)"
      by (rule interp_statement_list_Inr_more_fuel[OF F1]) simp
    have cb: "call_body (interp_statement_list d ?G) (mc_state full) (mc_interp_fun f)
                (map (interp_writable_lvalue d ?G (mc_state full)) (map match_compile_term argTms))
                (map (interp_term d ?G (mc_state full)) (map match_compile_term argTms))
                (mc_state preF) = Inr (mc_state newFull, retVal)"
      unfolding call_body_def mc_interp_fun_simps using Inl F1' newFull_eq by simp
    have "interp_function_call d (Suc ?G) (mc_state full) fnName tyArgs (map match_compile_term argTms)
            = Inr (mc_state newFull, retVal)"
      by (rule interp_function_call_I[OF lk lenA lenT compiled_fold[OF agreeG] req' ens' cb])
    thus ?thesis by blast
  next
    case (Inr ext)
    \<comment> \<open>An extern function: it sees the same world and the same argument
        values, because the original run evaluated every argument
        successfully.\<close>
    have lenR: "length (IF_Args f) = length ?refsF" using len_args by simp
    have lenV: "length (IF_Args f) = length ?valsF" using len_args by simp
    note inv = fold_process_one_arg_inr_inversion[OF foldF lenR lenV]
    let ?refsG = "map (interp_writable_lvalue d F0 (mc_state full)) (map match_compile_term argTms)"
    let ?valsG = "map (interp_term d F0 (mc_state full)) (map match_compile_term argTms)"
    have vals_eq: "?valsG = ?valsF"
    proof (rule results_agree_eq)
      show "length ?valsG = length ?valsF" by simp
    next
      fix i v assume i_lt: "i < length ?valsF" and "?valsF ! i = Inr v"
      hence ev_i: "interp_term d fuel full (argTms ! i) = Inr v" by simp
      have "args_agree fuel full F0 (argTms ! i)"
        using bspec[OF F0 nth_mem[of i argTms]] i_lt by simp
      from args_agree_term[OF this ev_i] show "?valsG ! i = Inr v" using i_lt by simp
    next
      fix x assume "x \<in> set ?valsF"
      then obtain i where "i < length argTms" and "x = ?valsF ! i" by (auto simp: in_set_conv_nth)
      with inv len_args show "\<exists>v. x = Inr v" by auto
    qed
    have refs_eq: "map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError) (zip (IF_Args f) ?refsG)
                   = map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError) (zip (IF_Args f) ?refsF)"
    proof (rule ref_results_selection_eq)
      show "length ?refsG = length ?refsF" by simp
      show "length (IF_Args f) = length ?refsF" using len_args by simp
    next
      fix i assume i_lt: "i < length (IF_Args f)" and is_ref: "snd (IF_Args f ! i) = Ref"
      from inv i_lt is_ref obtain a p where r: "?refsF ! i = Inr (a, p)" by blast
      hence ev_i: "interp_writable_lvalue d fuel full (argTms ! i) = Inr (a, p)"
        using i_lt len_args by simp
      have "args_agree fuel full F0 (argTms ! i)"
        using bspec[OF F0 nth_mem[of i argTms]] i_lt len_args by simp
      from args_agree_lvalue[OF this ev_i]
      show "?refsG ! i = ?refsF ! i" using r i_lt len_args by simp
    qed
    obtain w upd rv where ext_eq: "ext (IS_World full) (rights ?valsF) = (w, upd, rv)"
      by (cases "ext (IS_World full) (rights ?valsF)") auto
    from bodyF Inr ext_eq obtain fin where
      aru: "apply_ref_updates (full \<lparr> IS_World := w \<rparr>)
              (rights (map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError)
                            (zip (IF_Args f) ?refsF))) upd = Inr fin" and
      nf: "newFull = fin" and rv: "retVal = rv"
      by (auto simp: call_body_def Let_def split: sum.splits)
    have aru': "apply_ref_updates ((mc_state full) \<lparr> IS_World := w \<rparr>)
                  (rights (map (\<lambda>((_, vr), rr). if vr = Ref then rr else Inl TypeError)
                                (zip (IF_Args f) ?refsF))) upd = Inr (mc_state fin)"
      using apply_ref_updates_mc[of "full \<lparr> IS_World := w \<rparr>"] aru by simp
    have cb: "call_body (interp_statement_list d F0) (mc_state full) (mc_interp_fun f) ?refsG ?valsG
                (mc_state preF) = Inr (mc_state newFull, retVal)"
      unfolding call_body_def mc_interp_fun_simps vals_eq refs_eq
      using Inr ext_eq aru' nf rv by (simp add: Let_def)
    have "interp_function_call d (Suc F0) (mc_state full) fnName tyArgs (map match_compile_term argTms)
            = Inr (mc_state newFull, retVal)"
      by (rule interp_function_call_I[OF lk lenA lenT compiled_fold[OF F0] req' ens' cb])
    thus ?thesis by blast
  qed
qed

end

end

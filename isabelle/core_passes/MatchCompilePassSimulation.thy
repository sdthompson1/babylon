theory MatchCompilePassSimulation
  imports MatchCompilePassSimCall "../interpreter/MakeInterpStateCorrect"
begin

(* The simulation theorem for the match compilation pass.

   If a statement list (or a function call) that is well-typed in NotGhost
   mode, ghost-free and has variable scrutinees runs to a result from a state
   that matches its environment, then the compiled statement list runs to the
   same result, with the function bodies compiled (mc_state, mc_result), from
   the compiled state, at some fuel. The fuel of the compiled run is
   existentially quantified because the compiled program nests extra Match
   nodes, each of which consumes fuel.

   The proof is one induction on the fuel for the six interpreter functions
   together (sim_all); the cases of the induction step are the sim_* lemmas of
   MatchCompilePassSimTerms.thy, MatchCompilePassSimStmts.thy and
   MatchCompilePassSimCall.thy.

   The last section lifts the theorem to the interpreter state built from a
   module (make_interp_state): the state of the compiled module is the
   compiled state of the original module, and its function table satisfies
   the hypothesis of the simulation. *)


context match_compile_sim
begin

section \<open>The induction\<close>

lemma sim_all:
  "(\<forall>tm. term_sim fuel tm) \<and> (\<forall>tms. terms_sim fuel tms) \<and> (\<forall>lv. lvalue_sim fuel lv)
   \<and> (\<forall>stmt. stmt_sim fuel stmt) \<and> (\<forall>stmts. stmts_sim fuel stmts)
   \<and> (\<forall>fnName tyArgs argTms. call_sim fuel fnName tyArgs argTms)"
proof (induction fuel)
  case 0
  show ?case by (simp add: sim_zero)
next
  case (Suc fuel)
  have IH_tm: "term_sim fuel tm" and IH_tms: "terms_sim fuel tms" and IH_lv: "lvalue_sim fuel lv"
    and IH_stmt: "stmt_sim fuel stmt" and IH_stmts: "stmts_sim fuel stmts"
    and IH_call: "call_sim fuel fnName tyArgs argTms"
    for tm tms lv stmt stmts fnName tyArgs argTms
    using Suc.IH by blast+

  have tm: "term_sim (Suc fuel) tm" for tm
  proof (cases tm)
    case (CoreTm_LitBool b)
    show ?thesis unfolding CoreTm_LitBool by (rule sim_LitBool)
  next
    case (CoreTm_LitInt i)
    show ?thesis unfolding CoreTm_LitInt by (rule sim_LitInt)
  next
    case (CoreTm_LitArray eTy tms)
    show ?thesis unfolding CoreTm_LitArray by (rule sim_LitArray[OF IH_tms])
  next
    case (CoreTm_Var x)
    show ?thesis unfolding CoreTm_Var by (rule sim_Var)
  next
    case (CoreTm_Cast ty tm')
    show ?thesis unfolding CoreTm_Cast by (rule sim_Cast[OF IH_tm])
  next
    case (CoreTm_Unop op tm')
    show ?thesis unfolding CoreTm_Unop by (rule sim_Unop[OF IH_tm])
  next
    case (CoreTm_Binop op tm1 tm2)
    show ?thesis unfolding CoreTm_Binop by (rule sim_Binop[OF IH_tm IH_tm])
  next
    case (CoreTm_Let x rhs body)
    show ?thesis unfolding CoreTm_Let by (rule sim_Let[OF IH_tm])
  next
    case (CoreTm_Quantifier q x ty body)
    show ?thesis unfolding CoreTm_Quantifier by (rule sim_Quantifier)
  next
    case (CoreTm_FunctionCall fnName tyArgs args)
    show ?thesis unfolding CoreTm_FunctionCall by (rule sim_FunctionCall[OF IH_call])
  next
    case (CoreTm_VariantCtor c tys tm')
    show ?thesis unfolding CoreTm_VariantCtor by (rule sim_VariantCtor[OF IH_tm])
  next
    case (CoreTm_Record flds)
    show ?thesis unfolding CoreTm_Record by (rule sim_Record[OF IH_tms])
  next
    case (CoreTm_RecordProj tm' f)
    show ?thesis unfolding CoreTm_RecordProj by (rule sim_RecordProj[OF IH_tm])
  next
    case (CoreTm_VariantProj tm' c)
    show ?thesis unfolding CoreTm_VariantProj by (rule sim_VariantProj[OF IH_tm])
  next
    case (CoreTm_ArrayProj arr idxs)
    show ?thesis unfolding CoreTm_ArrayProj by (rule sim_ArrayProj[OF IH_tm IH_tms])
  next
    case (CoreTm_Match scrut arms)
    show ?thesis unfolding CoreTm_Match by (rule sim_Match[OF IH_tm])
  next
    case (CoreTm_Sizeof tm')
    show ?thesis unfolding CoreTm_Sizeof by (rule sim_Sizeof[OF IH_tm])
  next
    case (CoreTm_Allocated ty tm')
    show ?thesis unfolding CoreTm_Allocated by (rule sim_Allocated)
  next
    case (CoreTm_Default ty)
    show ?thesis unfolding CoreTm_Default by (rule sim_Default)
  qed

  have tms: "terms_sim (Suc fuel) tms" for tms
  proof (cases tms)
    case Nil
    show ?thesis unfolding Nil by (rule sim_terms_Nil)
  next
    case (Cons tm tms')
    show ?thesis unfolding Cons by (rule sim_terms_Cons[OF IH_tm IH_tms])
  qed

  have lv: "lvalue_sim (Suc fuel) lv" for lv
    by (rule sim_lvalue[OF IH_lv IH_tms])

  have st: "stmt_sim (Suc fuel) stmt" for stmt
  proof (cases stmt)
    case (CoreStmt_VarDecl g x vr ty init)
    show ?thesis
    proof (cases vr)
      case Var
      show ?thesis unfolding CoreStmt_VarDecl Var by (rule sim_VarDecl_Var[OF IH_tm])
    next
      case Ref
      show ?thesis unfolding CoreStmt_VarDecl Ref by (rule sim_VarDecl_Ref[OF IH_tm IH_lv])
    qed
  next
    case (CoreStmt_VarDeclCall g x ty castOpt fnName tyArgs argTms)
    show ?thesis unfolding CoreStmt_VarDeclCall by (rule sim_VarDeclCall[OF IH_call])
  next
    case (CoreStmt_Fix x ty)
    show ?thesis unfolding CoreStmt_Fix by (rule sim_not_ghost_free) simp
  next
    case (CoreStmt_Obtain x ty cond)
    show ?thesis unfolding CoreStmt_Obtain by (rule sim_not_ghost_free) simp
  next
    case (CoreStmt_Use tm')
    show ?thesis unfolding CoreStmt_Use by (rule sim_not_ghost_free) simp
  next
    case (CoreStmt_Assign g lhs rhs)
    show ?thesis unfolding CoreStmt_Assign by (rule sim_Assign[OF IH_lv IH_tm])
  next
    case (CoreStmt_AssignCall g lhs castOpt fnName tyArgs argTms)
    show ?thesis unfolding CoreStmt_AssignCall by (rule sim_AssignCall[OF IH_lv IH_call])
  next
    case (CoreStmt_Swap g lhs rhs)
    show ?thesis unfolding CoreStmt_Swap by (rule sim_Swap[OF IH_lv IH_lv])
  next
    case (CoreStmt_Return tm')
    show ?thesis unfolding CoreStmt_Return by (rule sim_Return[OF IH_tm])
  next
    case (CoreStmt_Assert cond proof_body)
    show ?thesis unfolding CoreStmt_Assert by (rule sim_not_ghost_free) simp
  next
    case (CoreStmt_Assume tm')
    show ?thesis unfolding CoreStmt_Assume by (rule sim_not_ghost_free) simp
  next
    case (CoreStmt_While g cond invars decr body)
    show ?thesis unfolding CoreStmt_While by (rule sim_While[OF IH_tm IH_stmts IH_stmt])
  next
    case (CoreStmt_Match g scrut arms)
    show ?thesis unfolding CoreStmt_Match by (rule sim_Match_stmt[OF IH_tm IH_stmts])
  next
    case (CoreStmt_ShowHide sh x)
    show ?thesis unfolding CoreStmt_ShowHide by (rule sim_not_ghost_free) simp
  next
    case (CoreStmt_Block body)
    show ?thesis unfolding CoreStmt_Block by (rule sim_Block[OF IH_stmts])
  qed

  have sts: "stmts_sim (Suc fuel) stmts" for stmts
  proof (cases stmts)
    case Nil
    show ?thesis unfolding Nil by (rule sim_stmts_Nil)
  next
    case (Cons stmt stmts')
    show ?thesis unfolding Cons by (rule sim_stmts_Cons[OF IH_stmt IH_stmts])
  qed

  have call: "call_sim (Suc fuel) fnName tyArgs argTms" for fnName tyArgs argTms
    by (rule sim_call[OF IH_tm IH_lv IH_stmts])

  show ?case using tm tms lv st sts call by blast
qed

end


section \<open>The simulation theorems\<close>

(* The simulation for a statement list, e.g. a function body. The function
   table of the state and the function signatures of the environment must
   satisfy funs_match_compilable (no ghost functions or parameters, no
   contracts, ghost-free bodies with variable scrutinees); the last section
   shows that the state built from a ghost-free module with variable
   scrutinees does. *)
theorem match_compile_simulation:
  fixes full :: "'w InterpState"
  assumes fmc: "funs_match_compilable env (IS_Functions full)"
    and sme: "state_matches_env full env storeTyping"
    and wf: "tyenv_well_formed env"
    and ng: "TE_ProofGoal env = None"
    and T: "core_statement_list_type env NotGhost stmts = Some env'"
    and gf: "core_statement_list_ghost_free stmts"
    and ok: "core_statement_list_match_scrutinees_ok stmts"
    and H: "interp_statement_list d fuel full stmts = Inr res"
  shows "\<exists>fuel'. interp_statement_list d fuel' (mc_state full) (match_compile_statement_list stmts)
                 = Inr (mc_result res)"
proof -
  interpret match_compile_sim d env "IS_Functions full" by unfold_locales (rule fmc)
  from sim_all have "stmts_sim fuel stmts" by blast
  from stmts_simD[OF this refl refl sme wf ng T gf ok H] show ?thesis .
qed

(* The simulation for a function call (the hypotheses on the call are those
   of the type soundness theorem, interp_function_call_sound). *)
theorem match_compile_simulation_call:
  fixes full :: "'w InterpState"
  assumes fmc: "funs_match_compilable env (IS_Functions full)"
    and sme: "state_matches_env full env storeTyping"
    and wf: "tyenv_well_formed env"
    and fi: "fmlookup (TE_Functions env) fnName = Some funInfo"
    and args_typed: "list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
         argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))"
    and len_ty: "length tyArgs = length (FI_TyArgs funInfo)"
    and wk: "list_all (is_well_kinded env) tyArgs"
    and refs_w: "\<forall>i < length argTms.
          fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow> is_writable_lvalue env (argTms ! i)"
    and ok: "list_all core_term_match_scrutinees_ok argTms"
    and H: "interp_function_call d fuel full fnName tyArgs argTms = Inr (newFull, retVal)"
  shows "\<exists>fuel'. interp_function_call d fuel' (mc_state full) fnName tyArgs
                   (map match_compile_term argTms) = Inr (mc_state newFull, retVal)"
proof -
  interpret match_compile_sim d env "IS_Functions full" by unfold_locales (rule fmc)
  from sim_all have "call_sim fuel fnName tyArgs argTms" by blast
  from call_simD[OF this refl refl sme wf fi args_typed len_ty wk refs_w ok H] show ?thesis .
qed


section \<open>The interpreter state of the compiled module\<close>

lemma make_interp_fun_match_compile [simp]:
  "make_interp_fun info (match_compile_function f) (Inl (match_compile_statement_list body))
     = mc_interp_fun (make_interp_fun info f (Inl body))"
  "make_interp_fun info (match_compile_function f) (Inr ext)
     = mc_interp_fun (make_interp_fun info f (Inr ext))"
  by (simp_all add: make_interp_fun_def mc_interp_fun_def)

lemma build_interp_funs_match_compile:
  "build_interp_funs externs env (map (\<lambda>(n, f). (n, match_compile_function f)) pairs)
     = map_sum id (fmmap mc_interp_fun) (build_interp_funs externs env pairs)"
proof (induction pairs)
  case Nil
  show ?case by simp
next
  case (Cons p pairs)
  obtain n f where p: "p = (n, f)" by (cases p)
  show ?case
  proof (cases "fmlookup (TE_Functions env) n")
    case None
    with p show ?thesis by simp
  next
    case (Some info)
    show ?thesis
    proof (cases "build_interp_funs externs env pairs")
      case (Inl err)
      with p Some Cons.IH show ?thesis by simp
    next
      case (Inr acc)
      show ?thesis
      proof (cases "CF_Body f")
        case (Some body)
        with p \<open>fmlookup (TE_Functions env) n = Some info\<close> Inr Cons.IH show ?thesis
          by (simp add: fmmap_fmupd)
      next
        case None
        with p \<open>fmlookup (TE_Functions env) n = Some info\<close> Inr Cons.IH show ?thesis
          by (simp add: fmmap_fmupd split: option.splits)
      qed
    qed
  qed
qed

lemma sorted_list_of_fmap_fmmap:
  "sorted_list_of_fmap (fmmap g m) = map (\<lambda>(k, v). (k, g v)) (sorted_list_of_fmap m)"
proof -
  have "map (\<lambda>k. (k, the (fmlookup (fmmap g m) k))) (sorted_list_of_fset (fmdom m))
        = map (\<lambda>k. (k, g (the (fmlookup m k)))) (sorted_list_of_fset (fmdom m))"
    by (rule map_cong[OF refl]) (auto simp: fmlookup_dom_iff)
  thus ?thesis unfolding sorted_list_of_fmap_def by (simp add: comp_def case_prod_unfold)
qed

(* The interpreter state of the compiled module is the compiled interpreter
   state of the module. (For a normalized module; the pass does not commute
   with the normalization of a module with a non-empty type substitution,
   and the pipeline only runs it on linked, normalized modules.) *)
theorem make_interp_state_match_compile:
  assumes "CM_TypeSubst m = fmempty"
  shows "make_interp_state world externs externAlloc (match_compile_module m)
         = map_sum id mc_state (make_interp_state world externs externAlloc m)"
proof -
  have n1: "normalize_module m = m" by (rule normalize_module_id_when_empty[OF assms])
  have n2: "normalize_module (match_compile_module m) = match_compile_module m"
    by (rule normalize_module_id_when_empty) (simp add: assms)
  show ?thesis
    unfolding make_interp_state_def n1 n2 Let_def
    by (simp add: sorted_list_of_fmap_fmmap build_interp_funs_match_compile mc_state_def
                  base_interp_state_def split: sum.splits)
qed

(* The function table of the state built from a ghost-free module with
   variable scrutinees satisfies the hypothesis of the simulation. *)
theorem make_interp_state_funs_match_compilable:
  assumes gf: "core_module_ghost_free m"
      and ok: "core_module_match_scrutinees_ok m"
      and norm: "CM_TypeSubst m = fmempty"
      and mk: "make_interp_state world externs externAlloc m = Inr state"
  shows "funs_match_compilable (CM_TyEnv m) (IS_Functions state)"
proof -
  have n1: "normalize_module m = m" by (rule normalize_module_id_when_empty[OF norm])
  from mk obtain funs where
    bif: "build_interp_funs externs (CM_TyEnv m) (sorted_list_of_fmap (CM_Functions m)) = Inr funs" and
    fs: "IS_Functions state = funs"
    unfolding make_interp_state_def n1 Let_def by (auto split: sum.splits)
  show ?thesis
    unfolding funs_match_compilable_def
  proof (rule conjI)
    show "\<forall>name info. fmlookup (TE_Functions (CM_TyEnv m)) name = Some info
                    \<longrightarrow> FI_Ghost info = NotGhost \<and> no_ghost_params info"
      using gf unfolding core_module_ghost_free_def by blast
  next
    show "\<forall>name f. fmlookup (IS_Functions state) name = Some f
                 \<longrightarrow> IF_Requires f = [] \<and> IF_Ensures f = []
                   \<and> (\<forall>body. IF_Body f = Inl body
                              \<longrightarrow> core_statement_list_ghost_free body
                                \<and> core_statement_list_match_scrutinees_ok body)"
    proof (intro allI impI)
    fix name f assume lk: "fmlookup (IS_Functions state) name = Some f"
    from build_interp_funs_lookup_inv[OF bif lk[unfolded fs]] obtain info cf body where
      info: "fmlookup (TE_Functions (CM_TyEnv m)) name = Some info" and
      mem: "(name, cf) \<in> set (sorted_list_of_fmap (CM_Functions m))" and
      f_eq: "f = make_interp_fun info cf body" and
      body: "case CF_Body cf of
               Some stmts \<Rightarrow> body = Inl stmts
             | None \<Rightarrow> (\<exists>externFun. fmlookup externs name = Some externFun
                                   \<and> body = Inr externFun)"
      by blast
    from mem have cf_lk: "fmlookup (CM_Functions m) name = Some cf"
      by (simp add: sorted_list_of_fmap_mem_iff)
    from gf info have req: "FI_Requires info = []" and ens: "FI_Ensures info = []"
      unfolding core_module_ghost_free_def by blast+
    have bodies: "core_statement_list_ghost_free stmts \<and> core_statement_list_match_scrutinees_ok stmts"
      if "body = Inl stmts" for stmts
    proof -
      from body that have "CF_Body cf = Some stmts" by (cases "CF_Body cf") auto
      with gf ok cf_lk show ?thesis
        unfolding core_module_ghost_free_def core_module_match_scrutinees_ok_iff by blast
    qed
    show "IF_Requires f = [] \<and> IF_Ensures f = []
          \<and> (\<forall>body. IF_Body f = Inl body
                     \<longrightarrow> core_statement_list_ghost_free body
                       \<and> core_statement_list_match_scrutinees_ok body)"
      using req ens bodies by (simp add: f_eq make_interp_fun_def)
    qed
  qed
qed

(* Running a function of the compiled module is running it in the original
   module: the state built from the compiled module is the compiled state,
   and a call that succeeds in the original state succeeds in the compiled
   state, with the same return value and the compiled final state. *)
corollary match_compile_module_simulation:
  fixes state :: "'w InterpState"
  assumes wt: "core_module_well_typed m"
      and closed: "core_module_closed m"
      and gf: "core_module_ghost_free m"
      and ok: "core_module_match_scrutinees_ok m"
      and norm: "CM_TypeSubst m = fmempty"
      and externs_ok: "\<And>name info externFun.
            \<lbrakk> fmlookup (TE_Functions (CM_TyEnv m)) name = Some info;
              fmlookup externs name = Some externFun \<rbrakk>
            \<Longrightarrow> extern_fun_contract (CM_TyEnv m) info externFun"
      and mk: "make_interp_state world externs externAlloc m = Inr state"
      and fi: "fmlookup (TE_Functions (CM_TyEnv m)) fnName = Some funInfo"
      and args_typed: "list_all2 (\<lambda>tm expectedTy. core_term_type (CM_TyEnv m) NotGhost tm = Some expectedTy)
            argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                        (FI_TmArgs funInfo))"
      and len_ty: "length tyArgs = length (FI_TyArgs funInfo)"
      and wk: "list_all (is_well_kinded (CM_TyEnv m)) tyArgs"
      and refs_w: "\<forall>i < length argTms.
            fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow> is_writable_lvalue (CM_TyEnv m) (argTms ! i)"
      and ok_args: "list_all core_term_match_scrutinees_ok argTms"
      and run: "interp_function_call d fuel state fnName tyArgs argTms = Inr (newState, retVal)"
  shows "make_interp_state world externs externAlloc (match_compile_module m) = Inr (mc_state state)"
    and "\<exists>fuel'. interp_function_call d fuel' (mc_state state) fnName tyArgs
                   (map match_compile_term argTms) = Inr (mc_state newState, retVal)"
proof -
  show "make_interp_state world externs externAlloc (match_compile_module m) = Inr (mc_state state)"
    using make_interp_state_match_compile[OF norm, of world externs externAlloc] mk by simp
  have n1: "normalize_module m = m" by (rule normalize_module_id_when_empty[OF norm])
  have "state_matches_env state (CM_TyEnv (normalize_module m)) []"
  proof (rule make_interp_state_matches_env[OF wt closed _ mk])
    fix name info externFun
    assume "fmlookup (TE_Functions (CM_TyEnv (normalize_module m))) name = Some info"
      and "fmlookup externs name = Some externFun"
    thus "extern_fun_contract (CM_TyEnv (normalize_module m)) info externFun"
      unfolding n1 by (rule externs_ok)
  qed
  hence sme: "state_matches_env state (CM_TyEnv m) []" unfolding n1 .
  have wf: "tyenv_well_formed (CM_TyEnv m)"
    using core_module_well_typed_env_well_formed[OF wt] unfolding n1 .
  have fmc: "funs_match_compilable (CM_TyEnv m) (IS_Functions state)"
    by (rule make_interp_state_funs_match_compilable[OF gf ok norm mk])
  show "\<exists>fuel'. interp_function_call d fuel' (mc_state state) fnName tyArgs
                  (map match_compile_term argTms) = Inr (mc_state newState, retVal)"
    by (rule match_compile_simulation_call[OF fmc sme wf fi args_typed len_ty wk refs_w ok_args run])
qed

(* The same for a function without parameters, such as main. *)
corollary match_compile_module_simulation_noargs:
  fixes state :: "'w InterpState"
  assumes "core_module_well_typed m"
      and "core_module_closed m"
      and "core_module_ghost_free m"
      and "core_module_match_scrutinees_ok m"
      and "CM_TypeSubst m = fmempty"
      and "\<And>name info externFun.
            \<lbrakk> fmlookup (TE_Functions (CM_TyEnv m)) name = Some info;
              fmlookup externs name = Some externFun \<rbrakk>
            \<Longrightarrow> extern_fun_contract (CM_TyEnv m) info externFun"
      and "make_interp_state world externs externAlloc m = Inr state"
      and fi: "fmlookup (TE_Functions (CM_TyEnv m)) fnName = Some funInfo"
      and noargs: "FI_TmArgs funInfo = []" and notyargs: "FI_TyArgs funInfo = []"
      and run: "interp_function_call d fuel state fnName [] [] = Inr (newState, retVal)"
  shows "make_interp_state world externs externAlloc (match_compile_module m) = Inr (mc_state state)"
    and "\<exists>fuel'. interp_function_call d fuel' (mc_state state) fnName [] []
                   = Inr (mc_state newState, retVal)"
proof -
  show "make_interp_state world externs externAlloc (match_compile_module m) = Inr (mc_state state)"
    by (rule match_compile_module_simulation(1)[OF assms(1-7) fi _ _ _ _ _ run])
       (simp_all add: noargs notyargs)
  have "\<exists>fuel'. interp_function_call d fuel' (mc_state state) fnName []
                  (map match_compile_term []) = Inr (mc_state newState, retVal)"
    by (rule match_compile_module_simulation(2)[OF assms(1-7) fi _ _ _ _ _ run])
       (simp_all add: noargs notyargs)
  thus "\<exists>fuel'. interp_function_call d fuel' (mc_state state) fnName [] []
                  = Inr (mc_state newState, retVal)" by simp
qed

end

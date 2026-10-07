theory EraseGhostSimulation
  imports ErasedSteps "../interpreter/CoreInterpFuelMono"
begin

(* The simulation theorem for ghost erasure.

   If a statement list of a non-ghost function is well-typed in NotGhost mode,
   and runs to completion from the full state, then its erasure runs to
   completion from the related erased state, at the same depth and fuel,
   and the two results are related. See erase_ghost_simulation at the end.

   NotGhost typing is what says that executable code reads no ghost variable
   and calls no ghost function. For terms, only the fact that the term has a
   type in NotGhost mode is used (notghost_typed). For statements, the typing
   also gives the environment of the statements that follow.

   The proof is one induction on the fuel, at a fixed depth, over the six
   interpreter functions together:

    - a term in executable position gives the same value in both states;
    - so does a list of such terms;
    - an lvalue in executable position gives corresponding addresses, with the
      same path;
    - a statement that erases to one statement: that statement runs in the
      erased state, with a related result;
    - a statement list: its erasure runs in the erased state, with a related
      result;
    - a call of a function that is not ghost: the erased call (the same call
      without its ghost arguments) runs in the erased state and returns the
      same value, and the states after it are related.

   A statement that erases to nothing leaves the erased state where it is
   (GhostInvisible.thy); the rest of the list then runs with one unit of fuel
   to spare, which fuel monotonicity allows.

   A ghost argument of a call is evaluated, and bound to its parameter, in the
   full state only. Dropping it does not change the fuel that the other
   arguments get, because a call evaluates each argument with the same fuel. *)


(* ========================================================================== *)
(* Two more facts about the function table *)
(* ========================================================================== *)

(* The parameter names of each function of the state are distinct, and an
   external function does not depend on its ghost arguments. Both follow from
   funs_exist_in_state. *)
definition fun_param_names_distinct ::
    "(string, FunInfo) fmap \<Rightarrow> (string, 'w InterpFun) fmap \<Rightarrow> bool" where
  "fun_param_names_distinct funInfos funs \<equiv>
    \<forall>fnName info f.
      fmlookup funInfos fnName = Some info \<longrightarrow> fmlookup funs fnName = Some f \<longrightarrow>
        distinct (map fst (IF_Args f))"

definition extern_funs_ghost_independent ::
    "(string, FunInfo) fmap \<Rightarrow> (string, 'w InterpFun) fmap \<Rightarrow> bool" where
  "extern_funs_ghost_independent funInfos funs \<equiv>
    \<forall>fnName info f externFun.
      fmlookup funInfos fnName = Some info \<longrightarrow> fmlookup funs fnName = Some f \<longrightarrow>
      IF_Body f = Inr externFun \<longrightarrow>
        extern_fun_ghost_independent info externFun"

lemma funs_exist_in_state_matches:
  assumes "funs_exist_in_state state env"
    and "fmlookup (TE_Functions env) fnName = Some info"
    and "fmlookup (IS_Functions state) fnName = Some f"
  shows "fun_info_matches_interp_fun env info f"
proof -
  from assms(1,2)
  have "case fmlookup (IS_Functions state) fnName of
          None \<Rightarrow> False
        | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun"
    unfolding funs_exist_in_state_def by blast
  with assms(3) show ?thesis by simp
qed

lemma funs_exist_in_state_param_names_distinct:
  assumes "funs_exist_in_state state env"
  shows "fun_param_names_distinct (TE_Functions env) (IS_Functions state)"
  unfolding fun_param_names_distinct_def
proof (intro allI impI)
  fix fnName info f
  assume info: "fmlookup (TE_Functions env) fnName = Some info"
    and f: "fmlookup (IS_Functions state) fnName = Some f"
  from funs_exist_in_state_matches[OF assms info f]
  show "distinct (map fst (IF_Args f))"
    by (simp add: fun_info_matches_interp_fun_def)
qed

lemma funs_exist_in_state_extern_ghost_independent:
  assumes "funs_exist_in_state state env"
  shows "extern_funs_ghost_independent (TE_Functions env) (IS_Functions state)"
  unfolding extern_funs_ghost_independent_def
proof (intro allI impI)
  fix fnName info f externFun
  assume info: "fmlookup (TE_Functions env) fnName = Some info"
    and f: "fmlookup (IS_Functions state) fnName = Some f"
    and b: "IF_Body f = Inr externFun"
  from funs_exist_in_state_matches[OF assms info f] b
  show "extern_fun_ghost_independent info externFun"
    by (simp add: fun_info_matches_interp_fun_def extern_fun_contract_def)
qed


(* ========================================================================== *)
(* Leaving a scope *)
(* ========================================================================== *)

(* Leaving the scope of a While body, a Match arm or a Block. The results of
   the body are related in the environment that the body ended in; the results
   after leaving the scope are related in the starting one. *)
lemma scope_body_erased:
  assumes rel: "state_erased env emb full erased"
    and bodyT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) g body
                  = Some bodyEnv"
    and body: "interp_statement_list d fuel full body = Inr bodyRes"
    and inner: "result_erased bodyEnv emb bodyRes bodyResE"
  shows "result_erased env emb (scope_result full bodyRes)
           (scope_result erased bodyResE)"
proof -
  have "tyenv_fixed_eq (env \<lparr> TE_ProofTopLevel := False \<rparr>) bodyEnv"
    by (rule core_statement_list_type_fixed_eq[OF bodyT])
  then have fnsB: "TE_Functions bodyEnv = TE_Functions env"
    by (simp add: tyenv_fixed_eq_def)
  have len: "length (IS_Store full) \<le> length (IS_Store (result_state bodyRes))"
    by (rule frame_stepD(1)[OF interp_statement_list_frame[OF body]])
  show ?thesis by (rule result_erased_scope_exit[OF rel inner fnsB len])
qed


(* ========================================================================== *)
(* The induction *)
(* ========================================================================== *)

(* An environment genv and the function table funs of the full state are fixed
   outside the induction. Running statements changes neither the function
   signatures nor the function table, so every state and environment that the
   induction meets satisfies "TE_Functions env = TE_Functions genv" and
   "IS_Functions full = funs".

   The function signatures of genv are also the table that erasure uses to
   find the ghost arguments of calls. *)
lemma erase_ghost_simulation_aux:
  fixes genv :: CoreTyEnv
    and funs :: "(string, 'w InterpFun) fmap"
  assumes agree: "fun_param_flags_agree (TE_Functions genv) funs"
    and bodies: "fun_bodies_typed genv funs"
    and pure: "funs_respect_purity (TE_Functions genv) funs"
    and dist: "fun_param_names_distinct (TE_Functions genv) funs"
    and extern: "extern_funs_ghost_independent (TE_Functions genv) funs"
  shows "\<forall>env emb (full :: 'w InterpState) (erased :: 'w InterpState) v.
           TE_Functions env = TE_Functions genv \<longrightarrow>
           IS_Functions full = funs \<longrightarrow>
           state_erased env emb full erased \<longrightarrow>
           notghost_typed env tm \<longrightarrow>
           interp_term d fuel full tm = Inr v \<longrightarrow>
             interp_term d fuel erased (erase_ghost_term (TE_Functions genv) tm) = Inr v"
    and "\<forall>env emb (full :: 'w InterpState) (erased :: 'w InterpState) vs.
           TE_Functions env = TE_Functions genv \<longrightarrow>
           IS_Functions full = funs \<longrightarrow>
           state_erased env emb full erased \<longrightarrow>
           list_all (notghost_typed env) tms \<longrightarrow>
           interp_term_list d fuel full tms = Inr vs \<longrightarrow>
             interp_term_list d fuel erased (map (erase_ghost_term (TE_Functions genv)) tms)
               = Inr vs"
    and "\<forall>env emb (full :: 'w InterpState) (erased :: 'w InterpState) addr path.
           TE_Functions env = TE_Functions genv \<longrightarrow>
           IS_Functions full = funs \<longrightarrow>
           state_erased env emb full erased \<longrightarrow>
           notghost_typed env lvTm \<longrightarrow>
           interp_writable_lvalue d fuel full lvTm = Inr (addr, path) \<longrightarrow>
             (\<exists>i. interp_writable_lvalue d fuel erased
                    (erase_ghost_term (TE_Functions genv) lvTm) = Inr (i, path)
                  \<and> i < length emb \<and> emb ! i = addr)"
    and "\<forall>env env' emb (full :: 'w InterpState) (erased :: 'w InterpState) stmt' res.
           TE_Functions env = TE_Functions genv \<longrightarrow>
           IS_Functions full = funs \<longrightarrow>
           TE_FunctionGhost env = NotGhost \<longrightarrow>
           state_erased env emb full erased \<longrightarrow>
           core_statement_type env NotGhost stmt = Some env' \<longrightarrow>
           erase_ghost_statement (TE_Functions genv) stmt = [stmt'] \<longrightarrow>
           interp_statement d fuel full stmt = Inr res \<longrightarrow>
             (\<exists>resE. interp_statement d fuel erased stmt' = Inr resE
                     \<and> result_erased env' emb res resE)"
    and "\<forall>env env' emb (full :: 'w InterpState) (erased :: 'w InterpState) res.
           TE_Functions env = TE_Functions genv \<longrightarrow>
           IS_Functions full = funs \<longrightarrow>
           TE_FunctionGhost env = NotGhost \<longrightarrow>
           state_erased env emb full erased \<longrightarrow>
           core_statement_list_type env NotGhost stmts = Some env' \<longrightarrow>
           interp_statement_list d fuel full stmts = Inr res \<longrightarrow>
             (\<exists>resE. interp_statement_list d fuel erased
                       (erase_ghost_statement_list (TE_Functions genv) stmts)
                       = Inr resE
                     \<and> result_erased env' emb res resE)"
    and "\<forall>env emb (full :: 'w InterpState) (erased :: 'w InterpState)
            info newFull retVal.
           TE_Functions env = TE_Functions genv \<longrightarrow>
           IS_Functions full = funs \<longrightarrow>
           state_erased env emb full erased \<longrightarrow>
           fmlookup (TE_Functions env) fnName = Some info \<longrightarrow>
           FI_Ghost info = NotGhost \<longrightarrow>
           call_args_notghost env info argTms \<longrightarrow>
           interp_function_call d fuel full fnName argTys argTms = Inr (newFull, retVal) \<longrightarrow>
             (\<exists>newErased. interp_function_call d fuel erased fnName argTys
                            (erase_ghost_args (TE_Functions genv) fnName
                               (map (erase_ghost_term (TE_Functions genv)) argTms))
                            = Inr (newErased, retVal)
                          \<and> state_erased env emb newFull newErased)"
proof (induction fuel arbitrary: tm tms lvTm stmt stmts fnName argTys argTms rule: nat.induct)
  case zero
  {
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  next
    case 3 show ?case by simp
  next
    case 4 show ?case by simp
  next
    case 5 show ?case by simp
  next
    case 6 show ?case by simp
  }
next
  case (Suc fuel)
  note IH_term = Suc.IH(1)[rule_format]
  note IH_list = Suc.IH(2)[rule_format]
  note IH_lv = Suc.IH(3)[rule_format]
  note IH_stmt = Suc.IH(4)[rule_format]
  note IH_stmts = Suc.IH(5)[rule_format]
  note IH_call = Suc.IH(6)[rule_format]
  \<comment> \<open>The table that erasure uses, and the erasure of a term. \<close>
  let ?ft = "TE_Functions genv"
  let ?er = "erase_ghost_term ?ft"
  {
    \<comment> \<open>============================ Terms ============================ \<close>
    case (1 tm) show ?case
    proof (intro allI impI)
      fix env :: CoreTyEnv and emb :: "nat list"
        and full erased :: "'w InterpState" and v :: CoreValue
      assume fn_eq: "TE_Functions env = TE_Functions genv"
        and funs_eq: "IS_Functions full = funs"
        and rel: "state_erased env emb full erased"
        and W: "notghost_typed env tm"
        and H: "interp_term d (Suc fuel) full tm = Inr v"
      note D = state_erasedD[OF rel]
      note sub = IH_term[OF fn_eq funs_eq rel]
      note subs = IH_list[OF fn_eq funs_eq rel]

      \<comment> \<open>The erased term evaluates in the erased state as the term does in
          the full state. \<close>
      have eq: "interp_term d (Suc fuel) erased (?er tm) = interp_term d (Suc fuel) full tm"
      proof (cases tm)
        case (CoreTm_LitBool b)
        then show ?thesis by simp
      next
        case (CoreTm_LitInt n)
        then show ?thesis by simp
      next
        case (CoreTm_LitArray elemTy elems)
        have wgs: "list_all (notghost_typed env) elems"
          by (rule notghost_typed_LitArray[OF W[unfolded CoreTm_LitArray]])
        from H CoreTm_LitArray obtain vals where
          l: "interp_term_list d fuel full elems = Inr vals"
          by (cases "interp_term_list d fuel full elems") simp_all
        note lE = subs[OF wgs l]
        show ?thesis using l lE by (simp add: CoreTm_LitArray)
      next
        case (CoreTm_Var name)
        have ng: "\<not> tyenv_var_ghost env name"
          by (rule notghost_typed_Var[OF W[unfolded CoreTm_Var]])
        show ?thesis
          unfolding CoreTm_Var erase_ghost_term.simps by (rule erased_read_var[OF rel ng])
      next
        case (CoreTm_Cast targetTy operand)
        have W1: "notghost_typed env operand"
          by (rule notghost_typed_Cast[OF W[unfolded CoreTm_Cast]])
        from H CoreTm_Cast obtain x where s: "interp_term d fuel full operand = Inr x"
          by (cases "interp_term d fuel full operand") simp_all
        note sE = sub[OF W1 s]
        show ?thesis using s sE by (simp add: CoreTm_Cast)
      next
        case (CoreTm_Unop uop operand)
        have W1: "notghost_typed env operand"
          by (rule notghost_typed_Unop[OF W[unfolded CoreTm_Unop]])
        from H CoreTm_Unop obtain x where s: "interp_term d fuel full operand = Inr x"
          by (cases "interp_term d fuel full operand") simp_all
        note sE = sub[OF W1 s]
        show ?thesis using s sE by (simp add: CoreTm_Unop)
      next
        case (CoreTm_Binop bop lhs rhs)
        note Wb = notghost_typed_Binop[OF W[unfolded CoreTm_Binop]]
        have W1: "notghost_typed env lhs" by (rule Wb(1))
        have W2: "notghost_typed env rhs" by (rule Wb(2))
        from H CoreTm_Binop obtain x where s1: "interp_term d fuel full lhs = Inr x"
          by (cases "interp_term d fuel full lhs") simp_all
        note s1E = sub[OF W1 s1]
        show ?thesis
        proof (cases "short_circuit bop x")
          case (Some r)
          show ?thesis using s1 s1E Some by (simp add: CoreTm_Binop)
        next
          case None
          from H CoreTm_Binop s1 None obtain y where s2: "interp_term d fuel full rhs = Inr y"
            by (cases "interp_term d fuel full rhs") simp_all
          note s2E = sub[OF W2 s2]
          show ?thesis using s1 s1E None s2 s2E by (simp add: CoreTm_Binop)
        qed
      next
        case (CoreTm_Let var rhs body)
        \<comment> \<open>The environment of the body: the new variable is not ghost. \<close>
        from notghost_typed_Let[OF W[unfolded CoreTm_Let]] obtain rhsTy where
          T1: "core_term_type env NotGhost rhs = Some rhsTy" and
          W2: "notghost_typed
                 (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                        TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                        TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
                 body"
          by blast
        have W1: "notghost_typed env rhs" by (rule notghost_typedI[OF T1])
        let ?envL = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                           TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                           TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
        have tlv: "TE_LocalVars ?envL = fmupd var rhsTy (TE_LocalVars env)"
          and tgl: "TE_GhostLocals ?envL = fminus (TE_GhostLocals env) {|var|}"
          and fnsL: "TE_Functions ?envL = TE_Functions env"
          by simp_all
        note decl = notghost_decl_var_ghost[OF tlv tgl]
        note HL = H[unfolded CoreTm_Let interp_term_Let]
        from HL obtain x where s1: "interp_term d fuel full rhs = Inr x"
          by (cases "interp_term d fuel full rhs") simp_all
        note s1E = sub[OF W1 s1]
        from HL s1 have s2: "interp_term d fuel (bind_const_local var x full) body = Inr v"
          by (simp del: bind_const_local.simps)
        \<comment> \<open>The body runs with the new variable bound, in both states, to a
            new cell. \<close>
        have relL: "state_erased ?envL (emb @ [length (IS_Store full)])
                      (bind_const_local var x full) (bind_const_local var x erased)"
          by (rule state_erased_bind_both_fresh
                     [OF rel decl(1) decl(2) fnsL bind_const_local_step(1) bind_const_local_step(1)])
             (simp_all add: bind_const_local_step(2))
        have fnL: "TE_Functions ?envL = TE_Functions genv" using fn_eq by simp
        have funsL: "IS_Functions (bind_const_local var x full) = funs"
          using static_parts_eqD(2)[OF fresh_binding_stepD(1)[OF bind_const_local_step(1)]] funs_eq
          by auto
        note s2E = IH_term[OF fnL funsL relL W2 s2]
        show ?thesis
          unfolding CoreTm_Let erase_ghost_term.simps interp_term_Let
          using s1 s1E s2 s2E by simp
      next
        case (CoreTm_Quantifier q var varTy body)
        with W show ?thesis by simp
      next
        case (CoreTm_FunctionCall fnName tyArgs tmArgs)
        from notghost_typed_FunctionCall[OF W[unfolded CoreTm_FunctionCall]] obtain info where
          info: "fmlookup (TE_Functions env) fnName = Some info" and
          ngI: "FI_Ghost info = NotGhost" and
          cargs: "call_args_notghost env info tmArgs"
          by blast
        from H CoreTm_FunctionCall have pureF: "is_pure_fun full fnName"
          by (auto simp del: is_pure_fun.simps split: if_splits)
        from H CoreTm_FunctionCall pureF obtain newFull where
          c: "interp_function_call d fuel full fnName tyArgs tmArgs = Inr (newFull, v)"
          by (auto simp del: is_pure_fun.simps split: sum.splits prod.splits)
        \<comment> \<open>The erased call: the same call, without its ghost arguments. \<close>
        let ?argsE = "erase_ghost_args ?ft fnName (map ?er tmArgs)"
        from IH_call[OF fn_eq funs_eq rel info ngI cargs c] obtain newErased where
          cE: "interp_function_call d fuel erased fnName tyArgs ?argsE = Inr (newErased, v)"
          by blast
        have pureE: "is_pure_fun erased fnName"
          by (rule is_pure_fun_erased[OF D(4) info ngI pureF])
        show ?thesis using pureF pureE c cE
          by (simp add: CoreTm_FunctionCall del: is_pure_fun.simps)
      next
        case (CoreTm_VariantCtor ctorName tyArgs payload)
        have W1: "notghost_typed env payload"
          by (rule notghost_typed_VariantCtor[OF W[unfolded CoreTm_VariantCtor]])
        from H CoreTm_VariantCtor obtain x where s: "interp_term d fuel full payload = Inr x"
          by (cases "interp_term d fuel full payload") simp_all
        note sE = sub[OF W1 s]
        show ?thesis using s sE by (simp add: CoreTm_VariantCtor)
      next
        case (CoreTm_Record flds)
        have wgs: "list_all (notghost_typed env) (map snd flds)"
          by (rule notghost_typed_Record[OF W[unfolded CoreTm_Record]])
        from H CoreTm_Record obtain vals where
          l: "interp_term_list d fuel full (map snd flds) = Inr vals"
          by (cases "interp_term_list d fuel full (map snd flds)") simp_all
        note lE = subs[OF wgs l]
        \<comment> \<open>The erased record has the same field names, and the erased field
            terms. \<close>
        let ?fldsE = "map (\<lambda>(name, tm). (name, ?er tm)) flds"
        have fstE: "map fst ?fldsE = map fst flds" by (induction flds) auto
        have sndE: "map snd ?fldsE = map ?er (map snd flds)" by (induction flds) auto
        have eqE: "?er (CoreTm_Record flds) = CoreTm_Record ?fldsE" by simp
        have lE': "interp_term_list d fuel erased (map snd ?fldsE) = Inr vals"
          unfolding sndE by (rule lE)
        have fullV: "interp_term d (Suc fuel) full (CoreTm_Record flds)
                       = Inr (CV_Record (zip (map fst flds) vals))"
          using l by simp
        have erV: "interp_term d (Suc fuel) erased (CoreTm_Record ?fldsE)
                     = Inr (CV_Record (zip (map fst ?fldsE) vals))"
          using lE' by simp
        show ?thesis unfolding CoreTm_Record eqE fullV erV fstE by (rule refl)
      next
        case (CoreTm_RecordProj recTm fldName)
        have W1: "notghost_typed env recTm"
          by (rule notghost_typed_RecordProj[OF W[unfolded CoreTm_RecordProj]])
        from H CoreTm_RecordProj obtain x where s: "interp_term d fuel full recTm = Inr x"
          by (cases "interp_term d fuel full recTm") simp_all
        note sE = sub[OF W1 s]
        show ?thesis using s sE by (simp add: CoreTm_RecordProj)
      next
        case (CoreTm_VariantProj varTm ctorName)
        have W1: "notghost_typed env varTm"
          by (rule notghost_typed_VariantProj[OF W[unfolded CoreTm_VariantProj]])
        from H CoreTm_VariantProj obtain x where s: "interp_term d fuel full varTm = Inr x"
          by (cases "interp_term d fuel full varTm") simp_all
        note sE = sub[OF W1 s]
        show ?thesis using s sE by (simp add: CoreTm_VariantProj)
      next
        case (CoreTm_ArrayProj arr idxs)
        note Wa = notghost_typed_ArrayProj[OF W[unfolded CoreTm_ArrayProj]]
        have W1: "notghost_typed env arr" by (rule Wa(1))
        have wgs: "list_all (notghost_typed env) idxs" by (rule Wa(2))
        from H CoreTm_ArrayProj obtain x where s: "interp_term d fuel full arr = Inr x"
          by (cases "interp_term d fuel full arr") simp_all
        note sE = sub[OF W1 s]
        show ?thesis
        proof (cases x)
          case (CV_Array sizes elementMap)
          from H CoreTm_ArrayProj s CV_Array obtain ivs where
            l: "interp_term_list d fuel full idxs = Inr ivs"
            by (cases "interp_term_list d fuel full idxs") simp_all
          note lE = subs[OF wgs l]
          show ?thesis using s sE CV_Array l lE by (simp add: CoreTm_ArrayProj)
        qed (use s sE in \<open>simp_all add: CoreTm_ArrayProj\<close>)
      next
        case (CoreTm_Match scrut arms)
        note Wm = notghost_typed_Match[OF W[unfolded CoreTm_Match]]
        have W1: "notghost_typed env scrut" by (rule Wm(1))
        from H CoreTm_Match obtain sv where s: "interp_term d fuel full scrut = Inr sv"
          by (cases "interp_term d fuel full scrut") simp_all
        note sE = sub[OF W1 s]
        from H CoreTm_Match s obtain armTm where a: "find_matching_arm sv arms = Inr armTm"
          by (cases "find_matching_arm sv arms") simp_all
        from H CoreTm_Match s a have s2: "interp_term d fuel full armTm = Inr v" by simp
        have W2: "notghost_typed env armTm"
          by (rule Wm(2)[OF find_matching_arm_in_arms[OF a]])
        note s2E = sub[OF W2 s2]
        \<comment> \<open>The erased match chooses the erasure of the same arm. \<close>
        note aE = find_matching_arm_map
                    [where f = "erase_ghost_term (TE_Functions genv)", OF a]
        show ?thesis using s sE a aE s2 s2E by (simp add: CoreTm_Match)
      next
        case (CoreTm_Sizeof arr)
        have W1: "notghost_typed env arr"
          by (rule notghost_typed_Sizeof[OF W[unfolded CoreTm_Sizeof]])
        from H CoreTm_Sizeof obtain x where s: "interp_term d fuel full arr = Inr x"
          by (cases "interp_term d fuel full arr") simp_all
        note sE = sub[OF W1 s]
        show ?thesis using s sE by (simp add: CoreTm_Sizeof)
      next
        case (CoreTm_Allocated argTy arg)
        with W show ?thesis by simp
      next
        case (CoreTm_Old arg)
        with W show ?thesis by simp
      next
        case (CoreTm_Default dty)
        have dv: "default_value fuel erased (apply_subst (IS_TyArgs full) dty)
                    = default_value fuel full (apply_subst (IS_TyArgs full) dty)"
          by (rule default_value_cong_state(1)[OF D(2) D(9), rule_format])
        show ?thesis by (simp add: CoreTm_Default D(6) dv)
      qed
      show "interp_term d (Suc fuel) erased (?er tm) = Inr v" unfolding eq by (rule H)
    qed
  next
    \<comment> \<open>========================= Term lists ========================= \<close>
    case (2 tms) show ?case
    proof (intro allI impI)
      fix env :: CoreTyEnv and emb :: "nat list"
        and full erased :: "'w InterpState" and vs :: "CoreValue list"
      assume fn_eq: "TE_Functions env = TE_Functions genv"
        and funs_eq: "IS_Functions full = funs"
        and rel: "state_erased env emb full erased"
        and wgs: "list_all (notghost_typed env) tms"
        and H: "interp_term_list d (Suc fuel) full tms = Inr vs"
      have eq: "interp_term_list d (Suc fuel) erased (map ?er tms)
                  = interp_term_list d (Suc fuel) full tms"
      proof (cases tms)
        case Nil
        then show ?thesis by simp
      next
        case (Cons t rest)
        from wgs Cons
        have W1: "notghost_typed env t"
          and wgsR: "list_all (notghost_typed env) rest"
          by simp_all
        from H Cons obtain x where s1: "interp_term d fuel full t = Inr x"
          by (cases "interp_term d fuel full t") simp_all
        from H Cons s1 obtain xs where l: "interp_term_list d fuel full rest = Inr xs"
          by (cases "interp_term_list d fuel full rest") simp_all
        note s1E = IH_term[OF fn_eq funs_eq rel W1 s1]
        note lE = IH_list[OF fn_eq funs_eq rel wgsR l]
        show ?thesis using s1 s1E l lE by (simp add: Cons)
      qed
      show "interp_term_list d (Suc fuel) erased (map ?er tms) = Inr vs"
        unfolding eq by (rule H)
    qed
  next
    \<comment> \<open>========================== Lvalues ========================== \<close>
    case (3 lvTm) show ?case
    proof (intro allI impI)
      fix env :: CoreTyEnv and emb :: "nat list"
        and full erased :: "'w InterpState"
        and addr :: nat and path :: "LValuePath list"
      assume fn_eq: "TE_Functions env = TE_Functions genv"
        and funs_eq: "IS_Functions full = funs"
        and rel: "state_erased env emb full erased"
        and W: "notghost_typed env lvTm"
        and H: "interp_writable_lvalue d (Suc fuel) full lvTm = Inr (addr, path)"
      note lvs = IH_lv[OF fn_eq funs_eq rel]
      show "\<exists>i. interp_writable_lvalue d (Suc fuel) erased (?er lvTm) = Inr (i, path)
                \<and> i < length emb \<and> emb ! i = addr"
      proof (cases lvTm)
        case (CoreTm_Var name)
        have ng: "\<not> tyenv_var_ghost env name"
          by (rule notghost_typed_Var[OF W[unfolded CoreTm_Var]])
        show ?thesis
          unfolding CoreTm_Var erase_ghost_term.simps
          by (rule erased_lvalue_var[OF rel ng H[unfolded CoreTm_Var]])
      next
        case (CoreTm_RecordProj recTm fldName)
        have W1: "notghost_typed env recTm"
          by (rule notghost_typed_RecordProj[OF W[unfolded CoreTm_RecordProj]])
        from H CoreTm_RecordProj obtain path' where
          s: "interp_writable_lvalue d fuel full recTm = Inr (addr, path')" and
          p: "path = path' @ [LVPath_RecordProj fldName]"
          by (auto split: sum.splits prod.splits)
        from lvs[OF W1 s] obtain i where
          sE: "interp_writable_lvalue d fuel erased (?er recTm) = Inr (i, path')" and
          i_lt: "i < length emb" and ei: "emb ! i = addr"
          by blast
        from sE p
        have "interp_writable_lvalue d (Suc fuel) erased (?er lvTm) = Inr (i, path)"
          by (simp add: CoreTm_RecordProj)
        with i_lt ei show ?thesis by blast
      next
        case (CoreTm_VariantProj varTm ctorName)
        have W1: "notghost_typed env varTm"
          by (rule notghost_typed_VariantProj[OF W[unfolded CoreTm_VariantProj]])
        from H CoreTm_VariantProj obtain path' where
          s: "interp_writable_lvalue d fuel full varTm = Inr (addr, path')" and
          p: "path = path' @ [LVPath_VariantProj ctorName]"
          by (auto split: sum.splits prod.splits)
        from lvs[OF W1 s] obtain i where
          sE: "interp_writable_lvalue d fuel erased (?er varTm) = Inr (i, path')" and
          i_lt: "i < length emb" and ei: "emb ! i = addr"
          by blast
        from sE p
        have "interp_writable_lvalue d (Suc fuel) erased (?er lvTm) = Inr (i, path)"
          by (simp add: CoreTm_VariantProj)
        with i_lt ei show ?thesis by blast
      next
        case (CoreTm_ArrayProj arr idxs)
        note Wa = notghost_typed_ArrayProj[OF W[unfolded CoreTm_ArrayProj]]
        have W1: "notghost_typed env arr" by (rule Wa(1))
        have wgs: "list_all (notghost_typed env) idxs" by (rule Wa(2))
        from H CoreTm_ArrayProj obtain path' where
          s: "interp_writable_lvalue d fuel full arr = Inr (addr, path')"
          by (auto split: sum.splits prod.splits)
        from H CoreTm_ArrayProj s obtain ivs where
          l: "interp_term_list d fuel full idxs = Inr ivs"
          by (cases "interp_term_list d fuel full idxs") simp_all
        from H CoreTm_ArrayProj s l obtain indices where
          ii: "interpret_index_vals ivs = Inr indices" and
          p: "path = path' @ [LVPath_ArrayProj indices]"
          by (cases "interpret_index_vals ivs") auto
        from lvs[OF W1 s] obtain i where
          sE: "interp_writable_lvalue d fuel erased (?er arr) = Inr (i, path')" and
          i_lt: "i < length emb" and ei: "emb ! i = addr"
          by blast
        note lE = IH_list[OF fn_eq funs_eq rel wgs l]
        from sE lE ii p
        have "interp_writable_lvalue d (Suc fuel) erased (?er lvTm) = Inr (i, path)"
          by (simp add: CoreTm_ArrayProj)
        with i_lt ei show ?thesis by blast
      next
        case (CoreTm_Cast targetTy operand)
        have W1: "notghost_typed env operand"
          by (rule notghost_typed_Cast[OF W[unfolded CoreTm_Cast]])
        from H CoreTm_Cast obtain elemTy dims path' where
          tyA: "targetTy = CoreTy_Array elemTy dims" and
          s: "interp_writable_lvalue d fuel full operand = Inr (addr, path')" and
          p: "path = path' @ [LVPath_ArrayCast dims]"
          by (auto split: CoreType.splits sum.splits prod.splits)
        from lvs[OF W1 s] obtain i where
          sE: "interp_writable_lvalue d fuel erased (?er operand) = Inr (i, path')" and
          i_lt: "i < length emb" and ei: "emb ! i = addr"
          by blast
        from sE p tyA
        have "interp_writable_lvalue d (Suc fuel) erased (?er lvTm) = Inr (i, path)"
          by (simp add: CoreTm_Cast)
        with i_lt ei show ?thesis by blast
      qed (use H in simp_all)
    qed
  next
    \<comment> \<open>========================= Statements ========================= \<close>
    case (4 stmt) show ?case
    proof (intro allI impI)
      fix env env' :: CoreTyEnv and emb :: "nat list"
        and full erased :: "'w InterpState"
        and stmt' :: CoreStatement and res :: "'w ExecResult"
      assume fn_eq: "TE_Functions env = TE_Functions genv"
        and funs_eq: "IS_Functions full = funs"
        and fg: "TE_FunctionGhost env = NotGhost"
        and rel: "state_erased env emb full erased"
        and T: "core_statement_type env NotGhost stmt = Some env'"
        and E: "erase_ghost_statement ?ft stmt = [stmt']"
        and H: "interp_statement d (Suc fuel) full stmt = Inr res"
      note D = state_erasedD[OF rel]
      note sub = IH_term[OF fn_eq funs_eq rel]
      note lvs = IH_lv[OF fn_eq funs_eq rel]
      have fx: "tyenv_fixed_eq env env'" by (rule core_statement_type_fixed_eq[OF T])
      have fns: "TE_Functions env' = TE_Functions env"
        using fx by (simp add: tyenv_fixed_eq_def)

      \<comment> \<open>The environment in which the body of a While, Match or Block is typed. \<close>
      have fnB: "TE_Functions (env \<lparr> TE_ProofTopLevel := False \<rparr>) = TE_Functions genv"
        using fn_eq by simp
      have fgB: "TE_FunctionGhost (env \<lparr> TE_ProofTopLevel := False \<rparr>) = NotGhost"
        using fg by simp
      have relB: "state_erased (env \<lparr> TE_ProofTopLevel := False \<rparr>) emb full erased"
        using rel by simp

      show "\<exists>resE. interp_statement d (Suc fuel) erased stmt' = Inr resE
                   \<and> result_erased env' emb res resE"
      proof (cases stmt)
        case (CoreStmt_VarDecl g varName vr ty initTm)
        show ?thesis
        proof (cases g)
          case Ghost
          with E CoreStmt_VarDecl show ?thesis by simp
        next
          case NotGhost
          from E CoreStmt_VarDecl NotGhost
          have stmt'_eq: "stmt' = CoreStmt_VarDecl NotGhost varName vr ty (?er initTm)"
            by auto
          show ?thesis
          proof (cases vr)
            case Var
            from T CoreStmt_VarDecl NotGhost Var
            have tlv: "TE_LocalVars env' = fmupd varName ty (TE_LocalVars env)"
              and tgl: "TE_GhostLocals env' = fminus (TE_GhostLocals env) {|varName|}"
              and iT: "core_term_type env NotGhost initTm = Some ty"
              by (auto split: if_splits)
            have iW: "notghost_typed env initTm" by (rule notghost_typedI[OF iT])
            note decl = notghost_decl_var_ghost[OF tlv tgl]
            from Var H CoreStmt_VarDecl obtain initVal where
              iv: "interp_term d fuel full initTm = Inr initVal"
              by (auto split: sum.splits)
            note ivE = sub[OF iW iv]
            from Var H[symmetric] CoreStmt_VarDecl iv
            have cF: "is_continue res"
              and stepF: "fresh_binding_step varName initVal full (result_state res)"
              and ncF: "varName |\<notin>| IS_ConstLocals (result_state res)"
              by (simp_all add: fresh_binding_step_def static_parts_eq_def Let_def)
            have "\<exists>resE. interp_statement d (Suc fuel) erased stmt' = Inr resE"
              using ivE by (simp add: stmt'_eq Var Let_def)
            then obtain resE where
              HE: "interp_statement d (Suc fuel) erased stmt' = Inr resE"
              by blast
            from Var HE[symmetric] stmt'_eq ivE
            have cE: "is_continue resE"
              and stepE: "fresh_binding_step varName initVal erased (result_state resE)"
              and ncE: "varName |\<notin>| IS_ConstLocals (result_state resE)"
              by (simp_all add: fresh_binding_step_def static_parts_eq_def Let_def)
            have rel': "state_erased env' (emb @ [length (IS_Store full)])
                          (result_state res) (result_state resE)"
              by (rule state_erased_bind_both_fresh[OF rel decl(1) decl(2) fns stepF stepE])
                 (simp_all add: ncF ncE)
            have re: "result_erased env' emb res resE"
              by (rule result_erased_stateI[OF cF cE rel'])
            from HE re show ?thesis by blast
          next
            case Ref
            from T CoreStmt_VarDecl NotGhost Ref
            have tlv: "TE_LocalVars env' = fmupd varName ty (TE_LocalVars env)"
              and tgl: "TE_GhostLocals env' = fminus (TE_GhostLocals env) {|varName|}"
              and iT: "core_term_type env NotGhost initTm = Some ty"
              by (auto split: if_splits)
            have iW: "notghost_typed env initTm" by (rule notghost_typedI[OF iT])
            note decl = notghost_decl_var_ghost[OF tlv tgl]
            from Ref H CoreStmt_VarDecl obtain baseName where
              base: "lvalue_base_name initTm = Some baseName"
              by (cases "lvalue_base_name initTm") simp_all
            \<comment> \<open>The base variable is not ghost, so the test on it comes out the
                same in both states. \<close>
            have ngB: "\<not> tyenv_var_ghost env baseName"
              by (rule notghost_lvalue_base_not_ghost[OF base iW])
            note condEq = erased_base_readonly_iff[OF D(7) ngB]
            show ?thesis
            proof (cases "baseName |\<in>| IS_ConstLocals full
                          \<or> (fmlookup (IS_Locals full) baseName = None
                             \<and> fmlookup (IS_Refs full) baseName = None)")
              case True
              \<comment> \<open>Read-only base: both states copy the value into a new cell. \<close>
              have condE: "baseName |\<in>| IS_ConstLocals erased
                           \<or> (fmlookup (IS_Locals erased) baseName = None
                              \<and> fmlookup (IS_Refs erased) baseName = None)"
                unfolding condEq by (rule True)
              from Ref H CoreStmt_VarDecl base True obtain val where
                iv: "interp_term d fuel full initTm = Inr val"
                by (auto split: sum.splits)
              note ivE = sub[OF iW iv]
              from Ref H[symmetric] CoreStmt_VarDecl base True iv
              have cF: "is_continue res"
                and stepF: "fresh_binding_step varName val full (result_state res)"
                and inF: "varName |\<in>| IS_ConstLocals (result_state res)"
                by (simp_all add: fresh_binding_step_def static_parts_eq_def Let_def)
              have "\<exists>resE. interp_statement d (Suc fuel) erased stmt' = Inr resE"
                using base condE ivE by (auto simp: stmt'_eq Ref Let_def)
              then obtain resE where
                HE: "interp_statement d (Suc fuel) erased stmt' = Inr resE"
                by blast
              from Ref HE[symmetric] stmt'_eq base condE ivE
              have cE: "is_continue resE"
                and stepE: "fresh_binding_step varName val erased (result_state resE)"
                and inE: "varName |\<in>| IS_ConstLocals (result_state resE)"
                by (simp_all add: fresh_binding_step_def static_parts_eq_def Let_def)
              have rel': "state_erased env' (emb @ [length (IS_Store full)])
                            (result_state res) (result_state resE)"
                by (rule state_erased_bind_both_fresh[OF rel decl(1) decl(2) fns stepF stepE])
                   (simp_all add: inF inE)
              have re: "result_erased env' emb res resE"
                by (rule result_erased_stateI[OF cF cE rel'])
              from HE re show ?thesis by blast
            next
              case False
              \<comment> \<open>Writable base: both states alias the lvalue. \<close>
              have condE: "\<not> (baseName |\<in>| IS_ConstLocals erased
                              \<or> (fmlookup (IS_Locals erased) baseName = None
                                 \<and> fmlookup (IS_Refs erased) baseName = None))"
                unfolding condEq by (rule False)
              from Ref H CoreStmt_VarDecl base False obtain addrPath where
                lv0: "interp_writable_lvalue d fuel full initTm = Inr addrPath"
                by (auto split: sum.splits)
              obtain addr path where ap: "addrPath = (addr, path)" by (cases addrPath)
              from lv0 ap
              have wl: "interp_writable_lvalue d fuel full initTm = Inr (addr, path)"
                by simp
              from lvs[OF iW wl] obtain i where
                wlE: "interp_writable_lvalue d fuel erased (?er initTm) = Inr (i, path)" and
                i_lt: "i < length emb" and ei: "emb ! i = addr"
                by blast
              from Ref H[symmetric] CoreStmt_VarDecl base False wl
              have cF: "is_continue res"
                and stepF: "ref_binding_step varName addr path full (result_state res)"
                and ncF: "varName |\<notin>| IS_ConstLocals (result_state res)"
                by (simp_all add: ref_binding_step_def static_parts_eq_def)
              have "\<exists>resE. interp_statement d (Suc fuel) erased stmt' = Inr resE"
                using base condE wlE by (auto simp: stmt'_eq Ref)
              then obtain resE where
                HE: "interp_statement d (Suc fuel) erased stmt' = Inr resE"
                by blast
              from Ref HE[symmetric] stmt'_eq base condE wlE
              have cE: "is_continue resE"
                and stepE: "ref_binding_step varName i path erased (result_state resE)"
                and ncE: "varName |\<notin>| IS_ConstLocals (result_state resE)"
                by (simp_all add: ref_binding_step_def static_parts_eq_def)
              have rel': "state_erased env' emb
                            (result_state res) (result_state resE)"
                by (rule state_erased_bind_both_ref
                           [OF rel decl(1) decl(2) fns stepF stepE i_lt ei])
                   (simp_all add: ncF ncE)
              have re: "result_erased env' emb res resE"
                by (rule result_erased_state_same[OF cF cE rel'])
              from HE re show ?thesis by blast
            qed
          qed
        qed
      next
        case (CoreStmt_VarDeclCall g varName varTy castOpt fnName argTys argTms)
        show ?thesis
        proof (cases g)
          case Ghost
          with E CoreStmt_VarDeclCall show ?thesis by simp
        next
          case NotGhost
          \<comment> \<open>The erased call: the same call, without its ghost arguments. \<close>
          let ?argsE = "erase_ghost_args ?ft fnName (map ?er argTms)"
          from E CoreStmt_VarDeclCall NotGhost
          have stmt'_eq:
            "stmt' = CoreStmt_VarDeclCall NotGhost varName varTy castOpt fnName argTys ?argsE"
            by auto
          from T CoreStmt_VarDeclCall NotGhost obtain retTy where
            callT: "core_impure_call_type env NotGhost fnName argTys argTms = Some retTy"
            by (auto split: if_splits option.splits)
          from T CoreStmt_VarDeclCall NotGhost
          have tlv: "TE_LocalVars env' = fmupd varName varTy (TE_LocalVars env)"
            and tgl: "TE_GhostLocals env' = fminus (TE_GhostLocals env) {|varName|}"
            by (auto split: if_splits option.splits)
          note decl = notghost_decl_var_ghost[OF tlv tgl]
          from notghost_impure_call_typed[OF callT] obtain info where
            info: "fmlookup (TE_Functions env) fnName = Some info" and
            ngI: "FI_Ghost info = NotGhost" and
            cargs: "call_args_notghost env info argTms"
            by blast
          \<comment> \<open>Run the call in both states, then apply the cast, allocate and bind. \<close>
          from H CoreStmt_VarDeclCall obtain newFull retVal where
            call: "interp_function_call d fuel full fnName argTys argTms
                     = Inr (newFull, retVal)"
            by (auto split: sum.splits prod.splits)
          from IH_call[OF fn_eq funs_eq rel info ngI cargs call] obtain newErased where
            callE: "interp_function_call d fuel erased fnName argTys ?argsE
                      = Inr (newErased, retVal)" and
            rel1: "state_erased env emb newFull newErased"
            by blast
          from H CoreStmt_VarDeclCall call obtain initVal where
            cast: "apply_cast_opt castOpt retVal = Inr initVal"
            by (auto split: sum.splits)
          from H[symmetric] CoreStmt_VarDeclCall call cast
          have cF: "is_continue res"
            and stepF: "fresh_binding_step varName initVal newFull (result_state res)"
            and ncF: "varName |\<notin>| IS_ConstLocals (result_state res)"
            by (simp_all add: fresh_binding_step_def static_parts_eq_def Let_def)
          have "\<exists>resE. interp_statement d (Suc fuel) erased stmt' = Inr resE"
            using callE cast by (simp add: stmt'_eq Let_def)
          then obtain resE where
            HE: "interp_statement d (Suc fuel) erased stmt' = Inr resE"
            by blast
          from HE[symmetric] stmt'_eq callE cast
          have cE: "is_continue resE"
            and stepE: "fresh_binding_step varName initVal newErased (result_state resE)"
            and ncE: "varName |\<notin>| IS_ConstLocals (result_state resE)"
            by (simp_all add: fresh_binding_step_def static_parts_eq_def Let_def)
          have rel': "state_erased env' (emb @ [length (IS_Store newFull)])
                        (result_state res) (result_state resE)"
            by (rule state_erased_bind_both_fresh[OF rel1 decl(1) decl(2) fns stepF stepE])
               (simp_all add: ncF ncE)
          have re: "result_erased env' emb res resE"
            by (rule result_erased_stateI[OF cF cE rel'])
          from HE re show ?thesis by blast
        qed
      next
        case (CoreStmt_Fix fixName fixTy)
        with E show ?thesis by simp
      next
        case (CoreStmt_Obtain obName obTy condTm)
        with E show ?thesis by simp
      next
        case (CoreStmt_Use witnessTm)
        with E show ?thesis by simp
      next
        case (CoreStmt_Assign g lhsLv rhsTm)
        show ?thesis
        proof (cases g)
          case Ghost
          with E CoreStmt_Assign show ?thesis by simp
        next
          case NotGhost
          from E CoreStmt_Assign NotGhost
          have stmt'_eq: "stmt' = CoreStmt_Assign NotGhost (?er lhsLv) (?er rhsTm)" by auto
          from T CoreStmt_Assign NotGhost
          have lW: "notghost_typed env lhsLv"
            and rW: "notghost_typed env rhsTm"
            by (auto simp: notghost_typed_def split: if_splits option.splits)
          from T CoreStmt_Assign have env'_eq: "env' = env"
            by (auto split: if_splits option.splits)
          from H CoreStmt_Assign obtain addr path where
            wl: "interp_writable_lvalue d fuel full lhsLv = Inr (addr, path)"
            by (auto split: sum.splits)
          from H CoreStmt_Assign wl obtain rhsVal where
            rv: "interp_term d fuel full rhsTm = Inr rhsVal"
            by (auto split: sum.splits)
          from H CoreStmt_Assign wl rv obtain newVal where
            upd: "update_value_at_path (IS_Store full ! addr) path rhsVal = Inr newVal"
            by (auto simp: Let_def split: sum.splits)
          from lvs[OF lW wl] obtain i where
            wlE: "interp_writable_lvalue d fuel erased (?er lhsLv) = Inr (i, path)" and
            i_lt: "i < length emb" and ei: "emb ! i = addr"
            by blast
          note rvE = sub[OF rW rv]
          have cell: "IS_Store erased ! i = IS_Store full ! addr"
            by (rule erased_cell[OF rel i_lt ei])
          from H[symmetric] CoreStmt_Assign wl rv upd
          have cF: "is_continue res"
            and stepF: "store_write_step addr newVal full (result_state res)"
            by (simp_all add: store_write_step_def static_parts_eq_def Let_def)
          have "\<exists>resE. interp_statement d (Suc fuel) erased stmt' = Inr resE"
            using wlE rvE upd by (simp add: stmt'_eq cell Let_def)
          then obtain resE where
            HE: "interp_statement d (Suc fuel) erased stmt' = Inr resE"
            by blast
          from HE[symmetric] wlE rvE upd
          have cE: "is_continue resE"
            and stepE: "store_write_step i newVal erased (result_state resE)"
            by (simp_all add: stmt'_eq cell store_write_step_def static_parts_eq_def Let_def)
          have rel': "state_erased env emb (result_state res) (result_state resE)"
            by (rule state_erased_write_both[OF rel i_lt ei stepF stepE])
          have re: "result_erased env' emb res resE"
            unfolding env'_eq by (rule result_erased_state_same[OF cF cE rel'])
          from HE re show ?thesis by blast
        qed
      next
        case (CoreStmt_AssignCall g lhsLv castOpt fnName argTys argTms)
        show ?thesis
        proof (cases g)
          case Ghost
          with E CoreStmt_AssignCall show ?thesis by simp
        next
          case NotGhost
          let ?argsE = "erase_ghost_args ?ft fnName (map ?er argTms)"
          from E CoreStmt_AssignCall NotGhost
          have stmt'_eq:
            "stmt' = CoreStmt_AssignCall NotGhost (?er lhsLv) castOpt fnName argTys ?argsE"
            by auto
          from T CoreStmt_AssignCall NotGhost
          have lW: "notghost_typed env lhsLv"
            by (auto simp: notghost_typed_def split: if_splits option.splits)
          from T CoreStmt_AssignCall NotGhost obtain retTy where
            callT: "core_impure_call_type env NotGhost fnName argTys argTms = Some retTy"
            by (auto split: if_splits option.splits)
          from T CoreStmt_AssignCall have env'_eq: "env' = env"
            by (auto split: if_splits option.splits)
          from notghost_impure_call_typed[OF callT] obtain info where
            info: "fmlookup (TE_Functions env) fnName = Some info" and
            ngI: "FI_Ghost info = NotGhost" and
            cargs: "call_args_notghost env info argTms"
            by blast
          \<comment> \<open>Resolve the lhs, run the call, apply the cast, store. \<close>
          from H CoreStmt_AssignCall obtain addr path where
            wl: "interp_writable_lvalue d fuel full lhsLv = Inr (addr, path)"
            by (auto split: sum.splits)
          from H CoreStmt_AssignCall wl obtain newFull retVal where
            call: "interp_function_call d fuel full fnName argTys argTms
                     = Inr (newFull, retVal)"
            by (auto split: sum.splits prod.splits)
          from H CoreStmt_AssignCall wl call obtain rhsVal where
            cast: "apply_cast_opt castOpt retVal = Inr rhsVal"
            by (auto split: sum.splits)
          from H CoreStmt_AssignCall wl call cast obtain newVal where
            upd: "update_value_at_path (IS_Store newFull ! addr) path rhsVal = Inr newVal"
            by (auto simp: Let_def split: sum.splits)
          from lvs[OF lW wl] obtain i where
            wlE: "interp_writable_lvalue d fuel erased (?er lhsLv) = Inr (i, path)" and
            i_lt: "i < length emb" and ei: "emb ! i = addr"
            by blast
          from IH_call[OF fn_eq funs_eq rel info ngI cargs call] obtain newErased where
            callE: "interp_function_call d fuel erased fnName argTys ?argsE
                      = Inr (newErased, retVal)" and
            rel1: "state_erased env emb newFull newErased"
            by blast
          have cell: "IS_Store newErased ! i = IS_Store newFull ! addr"
            by (rule erased_cell[OF rel1 i_lt ei])
          from H[symmetric] CoreStmt_AssignCall wl call cast upd
          have cF: "is_continue res"
            and stepF: "store_write_step addr newVal newFull (result_state res)"
            by (simp_all add: store_write_step_def static_parts_eq_def Let_def)
          have "\<exists>resE. interp_statement d (Suc fuel) erased stmt' = Inr resE"
            using wlE callE cast upd by (simp add: stmt'_eq cell Let_def)
          then obtain resE where
            HE: "interp_statement d (Suc fuel) erased stmt' = Inr resE"
            by blast
          from HE[symmetric] wlE callE cast upd
          have cE: "is_continue resE"
            and stepE: "store_write_step i newVal newErased (result_state resE)"
            by (simp_all add: stmt'_eq cell store_write_step_def static_parts_eq_def Let_def)
          have rel': "state_erased env emb (result_state res) (result_state resE)"
            by (rule state_erased_write_both[OF rel1 i_lt ei stepF stepE])
          have re: "result_erased env' emb res resE"
            unfolding env'_eq by (rule result_erased_state_same[OF cF cE rel'])
          from HE re show ?thesis by blast
        qed
      next
        case (CoreStmt_Swap g lhsTm rhsTm)
        show ?thesis
        proof (cases g)
          case Ghost
          with E CoreStmt_Swap show ?thesis by simp
        next
          case NotGhost
          from E CoreStmt_Swap NotGhost
          have stmt'_eq: "stmt' = CoreStmt_Swap NotGhost (?er lhsTm) (?er rhsTm)" by auto
          from T CoreStmt_Swap NotGhost
          have lW: "notghost_typed env lhsTm"
            and rW: "notghost_typed env rhsTm"
            by (auto simp: notghost_typed_def split: if_splits option.splits)
          from T CoreStmt_Swap have env'_eq: "env' = env"
            by (auto split: if_splits option.splits)
          from H CoreStmt_Swap obtain lhsLv where
            lhs: "interp_writable_lvalue d fuel full lhsTm = Inr lhsLv"
            by (auto split: sum.splits)
          with H CoreStmt_Swap obtain rhsLv where
            rhs: "interp_writable_lvalue d fuel full rhsTm = Inr rhsLv"
            by (auto split: sum.splits)
          with H CoreStmt_Swap lhs obtain newFull where
            sw: "perform_swap full lhsLv rhsLv = Inr newFull"
            and res_eq: "res = Continue newFull"
            by (auto split: sum.splits)
          obtain addr1 path1 where l_eq: "lhsLv = (addr1, path1)" by (cases lhsLv)
          obtain addr2 path2 where r_eq: "rhsLv = (addr2, path2)" by (cases rhsLv)
          from lvs[OF lW lhs[unfolded l_eq]] obtain i1 where
            lhsE: "interp_writable_lvalue d fuel erased (?er lhsTm) = Inr (i1, path1)" and
            i1_lt: "i1 < length emb" and e1: "emb ! i1 = addr1"
            by blast
          from lvs[OF rW rhs[unfolded r_eq]] obtain i2 where
            rhsE: "interp_writable_lvalue d fuel erased (?er rhsTm) = Inr (i2, path2)" and
            i2_lt: "i2 < length emb" and e2: "emb ! i2 = addr2"
            by blast
          from perform_swap_erased[OF rel i1_lt e1 i2_lt e2 sw[unfolded l_eq r_eq]]
          obtain newErased where
            swE: "perform_swap erased (i1, path1) (i2, path2) = Inr newErased" and
            rel': "state_erased env emb newFull newErased"
            by blast
          have HE: "interp_statement d (Suc fuel) erased stmt' = Inr (Continue newErased)"
            using lhsE rhsE swE by (simp add: stmt'_eq del: perform_swap.simps)
          have re: "result_erased env' emb res (Continue newErased)"
            unfolding env'_eq res_eq by (rule result_erased_Continue_same[OF rel'])
          from HE re show ?thesis by blast
        qed
      next
        case (CoreStmt_Return retTm)
        from E CoreStmt_Return have stmt'_eq: "stmt' = CoreStmt_Return (?er retTm)" by auto
        from T CoreStmt_Return fg
        have rW: "notghost_typed env retTm"
          by (auto simp: notghost_typed_def split: if_splits)
        from T CoreStmt_Return have env'_eq: "env' = env"
          by (auto split: if_splits)
        from H CoreStmt_Return obtain x where s: "interp_term d fuel full retTm = Inr x"
          by (cases "interp_term d fuel full retTm") simp_all
        from H CoreStmt_Return s have res_eq: "res = Return full x" by auto
        note sE = sub[OF rW s]
        have HE: "interp_statement d (Suc fuel) erased stmt' = Inr (Return erased x)"
          using sE by (simp add: stmt'_eq)
        have re: "result_erased env' emb res (Return erased x)"
          unfolding env'_eq res_eq
          by (rule result_erased_Return_same[OF state_erased_heap[OF rel]])
        from HE re show ?thesis by blast
      next
        case (CoreStmt_Assert condOpt proofBody)
        with E show ?thesis by simp
      next
        case (CoreStmt_Assume asmTm)
        with E show ?thesis by simp
      next
        case (CoreStmt_While g condTm invars decr body)
        show ?thesis
        proof (cases g)
          case Ghost
          with E CoreStmt_While show ?thesis by simp
        next
          case NotGhost
          from E CoreStmt_While NotGhost
          have stmt'_eq: "stmt' = CoreStmt_While NotGhost (?er condTm) [] (CoreTm_LitBool False)
                                    (erase_ghost_statement_list ?ft body)"
            by auto
          from T CoreStmt_While have env'_eq: "env' = env"
            by (auto split: if_splits option.splits CoreType.splits)
          from T CoreStmt_While NotGhost
          have cW: "notghost_typed env condTm"
            by (auto simp: notghost_typed_def split: if_splits option.splits CoreType.splits)
          from T CoreStmt_While NotGhost obtain bodyEnv where
            bodyT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost body
                      = Some bodyEnv"
            by (auto split: if_splits option.splits CoreType.splits)
          \<comment> \<open>The full run succeeded, so its invariants were evaluated and all
              held. The erased loop has no invariants, so its check passes
              trivially (given some fuel, which the full run shows there is). \<close>
          from H CoreStmt_While obtain invarVals where
            iv: "interp_term_list d fuel full invars = Inr invarVals" and
            ie: "invariants_error invarVals = None"
            by (auto split: sum.splits option.splits)
          from iv have ivE: "interp_term_list d fuel erased [] = Inr []"
            by (cases fuel) simp_all
          have ieE: "invariants_error [] = None"
            by (simp add: invariants_error_def)
          note [simp] = iv ie ivE ieE
          from H CoreStmt_While obtain condVal where
            cv: "interp_term d fuel full condTm = Inr condVal"
            by (auto split: sum.splits)
          note cvE = sub[OF cW cv]
          show ?thesis
          proof (cases condVal)
            case (CV_Bool b)
            show ?thesis
            proof (cases b)
              case False
              with CoreStmt_While H cv CV_Bool have res_eq: "res = Continue full" by simp
              have HE: "interp_statement d (Suc fuel) erased stmt' = Inr (Continue erased)"
                using cvE CV_Bool False by (simp add: stmt'_eq)
              have re: "result_erased env' emb res (Continue erased)"
                unfolding env'_eq res_eq by (rule result_erased_Continue_same[OF rel])
              from HE re show ?thesis by blast
            next
              case True
              with CoreStmt_While H cv CV_Bool obtain bodyRes where
                body: "interp_statement_list d fuel full body = Inr bodyRes"
                by (auto split: sum.splits)
              \<comment> \<open>The body, in both states. \<close>
              from IH_stmts[OF fnB funs_eq fgB relB bodyT body] obtain bodyResE where
                bodyE: "interp_statement_list d fuel erased
                          (erase_ghost_statement_list ?ft body) = Inr bodyResE" and
                bre: "result_erased bodyEnv emb bodyRes bodyResE"
                by blast
              note sre = scope_body_erased[OF rel bodyT body bre]
              show ?thesis
              proof (cases bodyRes)
                case (Return state1 rv)
                from CoreStmt_While H cv CV_Bool True body Return
                have res_eq: "res = scope_result full bodyRes" by auto
                from result_erased_ReturnD[OF bre[unfolded Return]] obtain erased1 where
                  bE_eq: "bodyResE = Return erased1 rv"
                  by blast
                have HE: "interp_statement d (Suc fuel) erased stmt'
                            = Inr (scope_result erased bodyResE)"
                  using cvE CV_Bool True bodyE bE_eq by (simp add: stmt'_eq)
                have re: "result_erased env' emb res (scope_result erased bodyResE)"
                  unfolding env'_eq res_eq by (rule sre)
                from HE re show ?thesis by blast
              next
                case (Continue state1)
                from result_erased_ContinueD[OF bre[unfolded Continue]]
                obtain erased1 extra where
                  bE_eq: "bodyResE = Continue erased1" and
                  r1: "state_erased bodyEnv (emb @ extra) state1 erased1"
                  by blast
                \<comment> \<open>Both states leave the scope of the body, and the loop runs
                    again from the restored states. \<close>
                have "tyenv_fixed_eq (env \<lparr> TE_ProofTopLevel := False \<rparr>) bodyEnv"
                  by (rule core_statement_list_type_fixed_eq[OF bodyT])
                then have fnsB: "TE_Functions bodyEnv = TE_Functions env"
                  by (simp add: tyenv_fixed_eq_def)
                have len1: "length (IS_Store full) \<le> length (IS_Store state1)"
                  using frame_stepD(1)[OF interp_statement_list_frame[OF body]] Continue
                  by simp
                have rel_rs: "state_erased env emb (restore_scope full state1)
                                (restore_scope erased erased1)"
                  by (rule state_erased_restore_scope_both
                             [OF rel state_erased_heap[OF r1] fnsB len1])
                have funs_rs: "IS_Functions (restore_scope full state1) = funs"
                  using static_parts_eqD(2)[OF interp_statement_list_static[OF body]]
                        Continue funs_eq
                  by simp
                from CoreStmt_While H cv CV_Bool True body Continue
                have rec_eq: "interp_statement d fuel (restore_scope full state1)
                                (CoreStmt_While g condTm invars decr body) = Inr res"
                  by simp
                note T' = T[unfolded CoreStmt_While]
                note E' = E[unfolded CoreStmt_While]
                from IH_stmt[OF fn_eq funs_rs fg rel_rs T' E' rec_eq]
                obtain resE where
                  recE: "interp_statement d fuel (restore_scope erased erased1) stmt'
                           = Inr resE" and
                  re: "result_erased env' emb res resE"
                  by blast
                have HE: "interp_statement d (Suc fuel) erased stmt' = Inr resE"
                  using cvE CV_Bool True bodyE bE_eq recE by (simp add: stmt'_eq)
                from HE re show ?thesis by blast
              qed
            qed
          next
            \<comment> \<open>Non-bool cond value: TypeError, contradicts H. \<close>
            case CV_FiniteInt with CoreStmt_While H cv show ?thesis by simp
          next
            case CV_Variant with CoreStmt_While H cv show ?thesis by simp
          next
            case CV_Record with CoreStmt_While H cv show ?thesis by simp
          next
            case CV_Array with CoreStmt_While H cv show ?thesis by simp
          next
            case CV_Int with CoreStmt_While H cv show ?thesis by simp
          next
            case CV_Real with CoreStmt_While H cv show ?thesis by simp
          qed
        qed
      next
        case (CoreStmt_Match g scrutTm arms)
        show ?thesis
        proof (cases g)
          case Ghost
          with E CoreStmt_Match show ?thesis by simp
        next
          case NotGhost
          from E CoreStmt_Match NotGhost
          have stmt'_eq:
            "stmt' = CoreStmt_Match NotGhost (?er scrutTm)
                       (map (\<lambda>(pat, body). (pat, erase_ghost_statement_list ?ft body)) arms)"
            by auto
          from T CoreStmt_Match have env'_eq: "env' = env"
            by (auto split: if_splits option.splits)
          from T CoreStmt_Match NotGhost
          have sW: "notghost_typed env scrutTm"
            by (auto simp: notghost_typed_def split: if_splits option.splits)
          from H CoreStmt_Match obtain scrutVal where
            sv: "interp_term d fuel full scrutTm = Inr scrutVal"
            by (auto split: sum.splits)
          from H CoreStmt_Match sv obtain armStmts where
            arm: "find_matching_arm scrutVal arms = Inr armStmts"
            by (auto split: sum.splits)
          note mem = find_matching_arm_in_arms[OF arm]
          from match_arm_typed[OF T[unfolded CoreStmt_Match] mem] NotGhost obtain armEnv where
            armT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost
                     armStmts = Some armEnv"
            by auto
          from H CoreStmt_Match sv arm obtain bodyRes where
            body: "interp_statement_list d fuel full armStmts = Inr bodyRes"
            by (auto split: sum.splits)
          have res_eq: "res = scope_result full bodyRes"
            using H[unfolded CoreStmt_Match interp_Match_scope_result[OF sv arm body]]
            by simp
          \<comment> \<open>The erased Match chooses the erasure of the same arm. \<close>
          note svE = sub[OF sW sv]
          note armE = find_matching_arm_map
                        [where f = "erase_ghost_statement_list (TE_Functions genv)", OF arm]
          from IH_stmts[OF fnB funs_eq fgB relB armT body] obtain bodyResE where
            bodyE: "interp_statement_list d fuel erased
                      (erase_ghost_statement_list ?ft armStmts) = Inr bodyResE" and
            bre: "result_erased armEnv emb bodyRes bodyResE"
            by blast
          have HE: "interp_statement d (Suc fuel) erased stmt'
                      = Inr (scope_result erased bodyResE)"
            unfolding stmt'_eq by (rule interp_Match_scope_result[OF svE armE bodyE])
          have re: "result_erased env' emb res (scope_result erased bodyResE)"
            unfolding env'_eq res_eq by (rule scope_body_erased[OF rel armT body bre])
          from HE re show ?thesis by blast
        qed
      next
        case (CoreStmt_ShowHide sh name)
        with E show ?thesis by simp
      next
        case (CoreStmt_Block blockBody)
        from E CoreStmt_Block
        have stmt'_eq: "stmt' = CoreStmt_Block (erase_ghost_statement_list ?ft blockBody)"
          by auto
        from T CoreStmt_Block obtain bodyEnv where
          bodyT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) NotGhost
                    blockBody = Some bodyEnv"
          and env'_eq: "env' = env"
          by (auto split: option.splits)
        from H CoreStmt_Block obtain bodyRes where
          body: "interp_statement_list d fuel full blockBody = Inr bodyRes"
          by (auto split: sum.splits)
        have res_eq: "res = scope_result full bodyRes"
          using H[unfolded CoreStmt_Block interp_Block_scope_result[OF body]] by simp
        from IH_stmts[OF fnB funs_eq fgB relB bodyT body] obtain bodyResE where
          bodyE: "interp_statement_list d fuel erased
                    (erase_ghost_statement_list ?ft blockBody) = Inr bodyResE" and
          bre: "result_erased bodyEnv emb bodyRes bodyResE"
          by blast
        have HE: "interp_statement d (Suc fuel) erased stmt'
                    = Inr (scope_result erased bodyResE)"
          unfolding stmt'_eq by (rule interp_Block_scope_result[OF bodyE])
        have re: "result_erased env' emb res (scope_result erased bodyResE)"
          unfolding env'_eq res_eq by (rule scope_body_erased[OF rel bodyT body bre])
        from HE re show ?thesis by blast
      qed
    qed
  next
    \<comment> \<open>====================== Statement lists ====================== \<close>
    case (5 stmts) show ?case
    proof (intro allI impI)
      fix env env' :: CoreTyEnv and emb :: "nat list"
        and full erased :: "'w InterpState" and res :: "'w ExecResult"
      assume fn_eq: "TE_Functions env = TE_Functions genv"
        and funs_eq: "IS_Functions full = funs"
        and fg: "TE_FunctionGhost env = NotGhost"
        and rel: "state_erased env emb full erased"
        and T: "core_statement_list_type env NotGhost stmts = Some env'"
        and H: "interp_statement_list d (Suc fuel) full stmts = Inr res"
      show "\<exists>resE. interp_statement_list d (Suc fuel) erased
                     (erase_ghost_statement_list ?ft stmts)
                     = Inr resE
                   \<and> result_erased env' emb res resE"
      proof (cases stmts)
        case Nil
        with H have res_eq: "res = Continue full" by auto
        from T Nil have env'_eq: "env' = env" by simp
        have HE: "interp_statement_list d (Suc fuel) erased
                    (erase_ghost_statement_list ?ft stmts)
                    = Inr (Continue erased)"
          by (simp add: Nil)
        have re: "result_erased env' emb res (Continue erased)"
          unfolding env'_eq res_eq by (rule result_erased_Continue_same[OF rel])
        from HE re show ?thesis by blast
      next
        case (Cons stmt1 rest)
        from T Cons obtain envMid where
          T1: "core_statement_type env NotGhost stmt1 = Some envMid" and
          T2: "core_statement_list_type envMid NotGhost rest = Some env'"
          by (auto split: option.splits)
        from Cons H obtain res1 where
          r1: "interp_statement d fuel full stmt1 = Inr res1"
          by (auto split: sum.splits)
        \<comment> \<open>The first statement changes neither the function signatures, nor the
            ghost-ness of the enclosing function, nor the function table. \<close>
        have fx: "tyenv_fixed_eq env envMid" by (rule core_statement_type_fixed_eq[OF T1])
        have fn1: "TE_Functions envMid = TE_Functions genv"
          using fx fn_eq by (simp add: tyenv_fixed_eq_def)
        have fg1: "TE_FunctionGhost envMid = NotGhost"
          using fx fg by (simp add: tyenv_fixed_eq_def)
        have st1: "IS_Functions (result_state res1) = funs"
          using static_parts_eqD(2)[OF interp_statement_static[OF r1]] funs_eq by simp
        have agree': "fun_param_flags_agree (TE_Functions env) (IS_Functions full)"
          using agree by (simp add: fn_eq funs_eq)
        have pure': "funs_respect_purity (TE_Functions env) (IS_Functions full)"
          using pure by (simp add: fn_eq funs_eq)
        from erase_ghost_statement_shape[of "TE_Functions genv" stmt1] show ?thesis
        proof (elim disjE exE)
          \<comment> \<open>The first statement is deleted: the erased state does not move. \<close>
          assume er: "erase_ghost_statement ?ft stmt1 = []"
          from erased_statement_invisible[OF er T1 fg rel agree' pure' r1] obtain full1 where
            r1_eq: "res1 = Continue full1" and
            rel1: "state_erased envMid emb full1 erased"
            by blast
          from st1 r1_eq have funs1: "IS_Functions full1 = funs" by simp
          from Cons H r1 r1_eq
          have rec: "interp_statement_list d fuel full1 rest = Inr res" by simp
          from IH_stmts[OF fn1 funs1 fg1 rel1 T2 rec] obtain resE where
            recE: "interp_statement_list d fuel erased (erase_ghost_statement_list ?ft rest)
                     = Inr resE" and
            re: "result_erased env' emb res resE"
            by blast
          \<comment> \<open>The erased list has one statement fewer, and one more unit of fuel. \<close>
          have recE': "interp_statement_list d (Suc fuel) erased
                         (erase_ghost_statement_list ?ft rest) = Inr resE"
            by (rule interp_statement_list_more_fuel[OF recE]) simp_all
          have eqL: "erase_ghost_statement_list ?ft stmts
                       = erase_ghost_statement_list ?ft rest"
            by (simp add: Cons er)
          have HE: "interp_statement_list d (Suc fuel) erased
                      (erase_ghost_statement_list ?ft stmts) = Inr resE"
            unfolding eqL by (rule recE')
          from HE re show ?thesis by blast
        next
          \<comment> \<open>The first statement is kept: it runs in both states. \<close>
          fix stmt1' assume er: "erase_ghost_statement ?ft stmt1 = [stmt1']"
          from IH_stmt[OF fn_eq funs_eq fg rel T1 er r1] obtain res1E where
            r1E: "interp_statement d fuel erased stmt1' = Inr res1E" and
            re1: "result_erased envMid emb res1 res1E"
            by blast
          have eqL: "erase_ghost_statement_list ?ft stmts
                       = stmt1' # erase_ghost_statement_list ?ft rest"
            by (simp add: Cons er)
          show ?thesis
          proof (cases res1)
            case (Return state1 rv)
            from Cons H r1 Return have res_eq: "res = Return state1 rv" by auto
            from result_erased_ReturnD[OF re1[unfolded Return]] obtain erased1 where
              e1: "res1E = Return erased1 rv"
              by blast
            have HE: "interp_statement_list d (Suc fuel) erased
                        (erase_ghost_statement_list ?ft stmts) = Inr res1E"
              using r1E e1 by (simp add: eqL)
            have fns2: "TE_Functions env' = TE_Functions envMid"
              using core_statement_list_type_fixed_eq[OF T2] by (simp add: tyenv_fixed_eq_def)
            have re: "result_erased env' emb res res1E"
              unfolding res_eq by (rule result_erased_Return_env[OF re1[unfolded Return] fns2])
            from HE re show ?thesis by blast
          next
            case (Continue state1)
            from result_erased_ContinueD[OF re1[unfolded Continue]] obtain erased1 extra where
              e1: "res1E = Continue erased1" and
              rel1: "state_erased envMid (emb @ extra) state1 erased1"
              by blast
            from st1 Continue have funs1: "IS_Functions state1 = funs" by simp
            from Cons H r1 Continue
            have rec: "interp_statement_list d fuel state1 rest = Inr res" by simp
            from IH_stmts[OF fn1 funs1 fg1 rel1 T2 rec] obtain resE where
              recE: "interp_statement_list d fuel erased1 (erase_ghost_statement_list ?ft rest)
                       = Inr resE" and
              re2: "result_erased env' (emb @ extra) res resE"
              by blast
            have HE: "interp_statement_list d (Suc fuel) erased
                        (erase_ghost_statement_list ?ft stmts) = Inr resE"
              using r1E e1 recE by (simp add: eqL)
            have re: "result_erased env' emb res resE"
              by (rule result_erased_weaken[OF re2])
            from HE re show ?thesis by blast
          qed
        qed
      qed
    qed
  next
    \<comment> \<open>=========================== Calls =========================== \<close>
    case (6 fnName argTys argTms) show ?case
    proof (intro allI impI)
      fix env :: CoreTyEnv and emb :: "nat list"
        and full erased :: "'w InterpState" and info :: FunInfo
        and newFull :: "'w InterpState" and retVal :: CoreValue
      assume fn_eq: "TE_Functions env = TE_Functions genv"
        and funs_eq: "IS_Functions full = funs"
        and rel: "state_erased env emb full erased"
        and info: "fmlookup (TE_Functions env) fnName = Some info"
        and ngI: "FI_Ghost info = NotGhost"
        and cargs: "call_args_notghost env info argTms"
        and H: "interp_function_call d (Suc fuel) full fnName argTys argTms
                  = Inr (newFull, retVal)"
      note D = state_erasedD[OF rel]

      \<comment> \<open>Unfold the call in the full state enough to name each intermediate
          state. \<close>
      obtain f where f_lookup: "fmlookup (IS_Functions full) fnName = Some f"
        using H by (cases "fmlookup (IS_Functions full) fnName") simp_all
      from H f_lookup have len_eq: "length argTms = length (IF_Args f)"
        by (cases "length argTms = length (IF_Args f)") simp_all
      from H f_lookup len_eq have tyLen_eq: "length argTys = length (IF_TyArgs f)"
        by (cases "length argTys = length (IF_TyArgs f)") simp_all
      let ?refsF = "map (interp_writable_lvalue d fuel full) argTms"
      let ?valsF = "map (interp_term d fuel full) argTms"
      let ?tyArgs = "fmap_of_list (zip (IF_TyArgs f)
                                       (map (apply_subst (IS_TyArgs full)) argTys))"
      let ?clearedF = "full \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                              IS_ConstLocals := {||}, IS_TyArgs := ?tyArgs \<rparr>"
      let ?clearedE = "erased \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                IS_ConstLocals := {||}, IS_TyArgs := ?tyArgs \<rparr>"
      obtain preF where
        foldF: "fold process_one_arg (zip (IF_Args f) (zip ?refsF ?valsF)) (Inr ?clearedF)
                  = Inr preF"
        using H f_lookup len_eq tyLen_eq
        by (cases "fold process_one_arg (zip (IF_Args f) (zip ?refsF ?valsF)) (Inr ?clearedF)")
           (simp_all add: Let_def)

      \<comment> \<open>The function in the state, against its signature: the same Var/Ref
          flags, and distinct parameter names. The ghost flags of the
          parameters are those of the signature. \<close>
      have infoG: "fmlookup (TE_Functions genv) fnName = Some info"
        using info fn_eq by simp
      have f_lookup': "fmlookup funs fnName = Some f" using f_lookup funs_eq by simp
      note flags = fun_param_flags_agreeD[OF agree infoG f_lookup']
      have distF: "distinct (map fst (IF_Args f))"
        using dist infoG f_lookup' unfolding fun_param_names_distinct_def by blast
      from flags have lenF: "length (IF_Args f) = length (FI_TmArgs info)"
        by (rule map_eq_imp_length_eq)
      let ?flagsF = "param_ghost_flags info"
      have lenFlags: "length (IF_Args f) = length ?flagsF"
        by (simp add: param_ghost_flags_def lenF)

      \<comment> \<open>The erased call. Its arguments are the erasures of the arguments of
          the parameters that are not ghost; the erased function has exactly
          those parameters. \<close>
      let ?paramsE = "drop_ghost ?flagsF (IF_Args f)"
      let ?argsE = "erase_ghost_args ?ft fnName (map ?er argTms)"
      let ?lvE = "\<lambda>tm. interp_writable_lvalue d fuel erased (?er tm)"
      let ?tmE = "\<lambda>tm. interp_term d fuel erased (?er tm)"
      have paramsE_eq': "erase_ghost_args ?ft fnName (IF_Args f) = ?paramsE"
        by (simp add: erase_ghost_args_def infoG)
      have argsE_eq: "?argsE = map ?er (drop_ghost ?flagsF argTms)"
        by (simp add: erase_ghost_args_def infoG drop_ghost_map)
      have lenE: "length ?argsE = length ?paramsE"
        unfolding argsE_eq param_ghost_flags_def
        using length_drop_ghost_params[OF len_eq[unfolded lenF]]
              length_drop_ghost_params[OF lenF]
        by simp
      have refsE_eq: "map (interp_writable_lvalue d fuel erased) ?argsE
                        = map ?lvE (drop_ghost ?flagsF argTms)"
        unfolding argsE_eq by (simp add: comp_def)
      have valsE_eq: "map (interp_term d fuel erased) ?argsE
                        = map ?tmE (drop_ghost ?flagsF argTms)"
        unfolding argsE_eq by (simp add: comp_def)

      \<comment> \<open>The erased state holds the erased function. \<close>
      note lookE = funs_erased_lookup[OF D(4) info ngI f_lookup, unfolded fn_eq]

      \<comment> \<open>The environment of the callee's body. Its ghost variables are the
          callee's ghost parameters. \<close>
      let ?envB = "body_env_for genv (map fst (IF_Args f)) info"
      have fnBg: "TE_Functions ?envB = TE_Functions genv" by (simp add: body_env_for_facts)
      have fnB: "TE_Functions ?envB = TE_Functions env" by (simp add: body_env_for_facts fn_eq)
      have fgB: "TE_FunctionGhost ?envB = NotGhost"
        by (rule body_env_for_notghost[OF ngI])
      have pg: "\<forall>name vr gh. ((name, vr), gh) \<in> set (zip (IF_Args f) ?flagsF) \<longrightarrow>
                  (tyenv_var_ghost ?envB name \<longleftrightarrow> gh = Ghost)"
      proof (intro allI impI)
        fix name vr gh assume mem: "((name, vr), gh) \<in> set (zip (IF_Args f) ?flagsF)"
        from mem obtain n where "IF_Args f ! n = (name, vr)" and "?flagsF ! n = gh"
          and "n < length (IF_Args f)" and "n < length ?flagsF"
          by (auto simp: in_set_zip)
        then have mem': "(name, gh) \<in> set (zip (map fst (IF_Args f)) ?flagsF)"
          by (auto simp: in_set_zip intro!: exI[where x = n])
        have lenN: "length (map fst (IF_Args f)) = length (FI_TmArgs info)"
          by (simp add: lenF)
        show "tyenv_var_ghost ?envB name \<longleftrightarrow> gh = Ghost"
          by (rule body_env_for_param_ghost[OF ngI distF lenN mem'])
      qed

      \<comment> \<open>The argument of a parameter that is not ghost evaluates
          correspondingly in the two states. \<close>
      have vals: "\<forall>tm name vr. (tm, ((name, vr), NotGhost))
                                 \<in> set (zip argTms (zip (IF_Args f) ?flagsF)) \<longrightarrow>
                    (\<forall>x. interp_term d fuel full tm = Inr x
                         \<longrightarrow> interp_term d fuel erased (?er tm) = Inr x)"
      proof (intro allI impI)
        fix tm name vr x
        assume mem: "(tm, ((name, vr), NotGhost)) \<in> set (zip argTms (zip (IF_Args f) ?flagsF))"
          and s: "interp_term d fuel full tm = Inr x"
        have Wtm: "notghost_typed env tm"
          by (rule call_args_notghostD(1)[OF cargs flags mem refl])
        show "interp_term d fuel erased (?er tm) = Inr x"
          by (rule IH_term[OF fn_eq funs_eq rel Wtm s])
      qed
      have refs: "\<forall>tm name vr. (tm, ((name, vr), NotGhost))
                                 \<in> set (zip argTms (zip (IF_Args f) ?flagsF)) \<longrightarrow>
                    (\<forall>addr path. interp_writable_lvalue d fuel full tm = Inr (addr, path)
                       \<longrightarrow> (\<exists>i. interp_writable_lvalue d fuel erased (?er tm) = Inr (i, path)
                                \<and> i < length emb \<and> emb ! i = addr))"
      proof (intro allI impI)
        fix tm name vr addr path
        assume mem: "(tm, ((name, vr), NotGhost)) \<in> set (zip argTms (zip (IF_Args f) ?flagsF))"
          and s: "interp_writable_lvalue d fuel full tm = Inr (addr, path)"
        have Wtm: "notghost_typed env tm"
          by (rule call_args_notghostD(1)[OF cargs flags mem refl])
        show "\<exists>i. interp_writable_lvalue d fuel erased (?er tm) = Inr (i, path)
                  \<and> i < length emb \<and> emb ! i = addr"
          by (rule IH_lv[OF fn_eq funs_eq rel Wtm s])
      qed
      \<comment> \<open>An lvalue passed to a ghost Ref parameter is a ghost cell of the
          caller. \<close>
      have ghost_refs:
        "\<forall>tm name. (tm, ((name, Ref), Ghost)) \<in> set (zip argTms (zip (IF_Args f) ?flagsF)) \<longrightarrow>
           (\<forall>addr path. interp_writable_lvalue d fuel full tm = Inr (addr, path)
              \<longrightarrow> addr < length (IS_Store full) \<and> addr \<notin> set emb)"
      proof (intro allI impI)
        fix tm name addr path
        assume mem: "(tm, ((name, Ref), Ghost)) \<in> set (zip argTms (zip (IF_Args f) ?flagsF))"
          and s: "interp_writable_lvalue d fuel full tm = Inr (addr, path)"
        have glv: "ghost_lvalue_ok env Ghost tm"
          by (rule call_args_notghostD(2)[OF cargs flags mem refl refl])
        show "addr < length (IS_Store full) \<and> addr \<notin> set emb"
          by (rule conjI[OF ghost_lvalue_addr_separate(1)[OF D(8) glv s]
                            ghost_lvalue_addr_separate(2)[OF D(8) glv s]])
      qed

      \<comment> \<open>So the arguments are bound, all of them in the full state and those
          that erasure keeps in the erased state, giving related callee
          frames. \<close>
      have relC: "state_erased ?envB emb ?clearedF ?clearedE"
        by (rule state_erased_call_entry[OF rel fnB])
      then have relC': "state_erased ?envB (emb @ []) ?clearedF ?clearedE" by simp
      have lo: "length (IS_Store full) \<le> length (IS_Store ?clearedF)" by simp
      have ex: "\<forall>a \<in> set ([] :: nat list). length (IS_Store full) \<le> a" by simp
      from fold_process_one_arg_erased
             [where lvF = "interp_writable_lvalue d fuel full"
                and tmF = "interp_term d fuel full"
                and lvE = "\<lambda>tm. interp_writable_lvalue d fuel erased
                                  (erase_ghost_term (TE_Functions genv) tm)"
                and tmE = "\<lambda>tm. interp_term d fuel erased
                                  (erase_ghost_term (TE_Functions genv) tm)",
              OF lenFlags vals refs ghost_refs pg relC' lo ex foldF]
      obtain preE extraA where
        foldE0: "fold process_one_arg
                   (zip ?paramsE (zip (map ?lvE (drop_ghost ?flagsF argTms))
                                      (map ?tmE (drop_ghost ?flagsF argTms))))
                   (Inr ?clearedE)
                 = Inr preE" and
        relP: "state_erased ?envB (emb @ extraA) preF preE"
        by blast
      have foldE: "fold process_one_arg
                     (zip ?paramsE (zip (map (interp_writable_lvalue d fuel erased) ?argsE)
                                        (map (interp_term d fuel erased) ?argsE)))
                     (Inr ?clearedE)
                   = Inr preE"
        by (simp only: refsE_eq valsE_eq foldE0)

      show "\<exists>newErased. interp_function_call d (Suc fuel) erased fnName argTys ?argsE
                          = Inr (newErased, retVal)
                        \<and> state_erased env emb newFull newErased"
      proof (cases "IF_Body f")
        case (Inl bodyStmts)
        \<comment> \<open>Babylon body. \<close>
        from H f_lookup len_eq tyLen_eq foldF Inl
        obtain bodyRes where bodyEval:
          "interp_statement_list d fuel preF bodyStmts = Inr bodyRes"
          by (cases "interp_statement_list d fuel preF bodyStmts")
             (simp_all add: Let_def)
        show ?thesis
        proof (cases bodyRes)
          case (Continue _)
          with H f_lookup len_eq tyLen_eq foldF Inl bodyEval show ?thesis
            by (simp add: Let_def)
        next
          case (Return postF bodyRetVal)
          from H f_lookup len_eq tyLen_eq foldF Inl bodyEval Return
          have newFull_eq: "newFull = restore_scope full postF"
            and ret_eq: "retVal = bodyRetVal"
            by (simp_all add: Let_def)

          \<comment> \<open>The body is well-typed in the mode of the callee, which is
              NotGhost, so its erasure runs in the erased callee frame. \<close>
          from bodies infoG f_lookup' Inl
          have "core_statement_list_type ?envB (FI_Ghost info) bodyStmts \<noteq> None"
            unfolding fun_bodies_typed_def by blast
          then obtain envB' where
            bodyT: "core_statement_list_type ?envB NotGhost bodyStmts = Some envB'"
            by (auto simp: ngI)
          have funsP: "IS_Functions preF = funs"
            using fold_process_one_arg_preserves_globals_funs[OF foldF] funs_eq by simp
          from IH_stmts[OF fnBg funsP fgB relP bodyT bodyEval] obtain bodyResE where
            bodyE: "interp_statement_list d fuel preE
                      (erase_ghost_statement_list ?ft bodyStmts) = Inr bodyResE" and
            bre: "result_erased envB' (emb @ extraA) bodyRes bodyResE"
            by blast
          from result_erased_ReturnD[OF bre[unfolded Return]] obtain postE extra where
            bE_eq: "bodyResE = Return postE bodyRetVal" and
            h: "heap_erased envB' ((emb @ extraA) @ extra) postF postE"
            by blast
          from h have h': "heap_erased envB' (emb @ (extraA @ extra)) postF postE" by simp

          \<comment> \<open>Both callers get their frames back. \<close>
          have "tyenv_fixed_eq ?envB envB'"
            by (rule core_statement_list_type_fixed_eq[OF bodyT])
          then have fnsB1: "TE_Functions ?envB = TE_Functions envB'"
            by (simp add: tyenv_fixed_eq_def)
          have fnsB': "TE_Functions envB' = TE_Functions env"
            by (rule trans[OF fnsB1[symmetric] fnB])
          from fold_process_one_arg_frame[OF foldF] obtain extra0 where
            pre_store: "IS_Store preF = IS_Store full @ extra0"
            by auto
          have len1: "length (IS_Store full) \<le> length (IS_Store preF)"
            using pre_store by simp
          have len2: "length (IS_Store preF) \<le> length (IS_Store postF)"
            using frame_stepD(1)[OF interp_statement_list_frame[OF bodyEval]] Return by simp
          have len: "length (IS_Store full) \<le> length (IS_Store postF)"
            using len1 len2 by simp
          have relN: "state_erased env emb (restore_scope full postF)
                        (restore_scope erased postE)"
            by (rule state_erased_restore_scope_both[OF rel h' fnsB' len])
          have relN': "state_erased env emb newFull (restore_scope erased postE)"
            unfolding newFull_eq by (rule relN)
          have callE: "interp_function_call d (Suc fuel) erased fnName argTys ?argsE
                         = Inr (restore_scope erased postE, retVal)"
            using lookE lenE tyLen_eq foldE Inl bodyE bE_eq ret_eq
            by (simp add: Let_def paramsE_eq' D(6))
          from callE relN' show ?thesis by blast
        qed
      next
        case (Inr externFun)
        \<comment> \<open>Extern function. \<close>
        let ?refsXF = "rights (map (\<lambda>((_, vr), refResult).
                                        if vr = Ref then refResult else Inl TypeError)
                                   (zip (IF_Args f) ?refsF))"
        let ?refsXE = "rights (map (\<lambda>((_, vr), refResult).
                                        if vr = Ref then refResult else Inl TypeError)
                                   (zip ?paramsE (map ?lvE (drop_ghost ?flagsF argTms))))"
        obtain newWorld refUpdates externRetVal where
          ext_eq: "externFun (IS_World full) (rights ?valsF)
                     = (newWorld, refUpdates, externRetVal)"
          by (cases "externFun (IS_World full) (rights ?valsF)") auto
        let ?fullW = "full \<lparr> IS_World := newWorld \<rparr>"
        let ?erasedW = "erased \<lparr> IS_World := newWorld \<rparr>"
        from H f_lookup len_eq tyLen_eq foldF Inr ext_eq
        obtain finalState where
          final_eq: "apply_ref_updates ?fullW ?refsXF refUpdates = Inr finalState"
          and newFull_eq: "newFull = finalState"
          and ret_eq: "retVal = externRetVal"
          by (cases "apply_ref_updates ?fullW ?refsXF refUpdates") (simp_all add: Let_def)

        \<comment> \<open>Every argument has a value in the full state. \<close>
        have lenA: "length (IF_Args f) = length ?refsF" using len_eq by simp
        have lenB: "length ?refsF = length ?valsF" by simp
        have lenC: "length argTms = length ?refsF" by simp
        have allInr: "\<forall>tm \<in> set argTms. \<exists>v. interp_term d fuel full tm = Inr v"
        proof
          fix tm assume "tm \<in> set argTms"
          then have "interp_term d fuel full tm \<in> set ?valsF" by auto
          from fold_process_one_arg_all_ok[OF foldF lenA lenB this]
          show "\<exists>v. interp_term d fuel full tm = Inr v" by blast
        qed
        have lenV: "length (rights ?valsF) = length (FI_TmArgs info)"
        proof -
          have "\<forall>x \<in> set ?valsF. \<exists>v. x = Inr v" using allInr by auto
          from length_rights_all_inr[OF this] show ?thesis by (simp add: len_eq lenF)
        qed

        \<comment> \<open>The erased state passes the values of the arguments that erasure
            keeps, which are the values the full state computed for them. \<close>
        have valsE_drop: "rights (map (interp_term d fuel erased) ?argsE)
                            = drop_ghost ?flagsF (rights ?valsF)"
          unfolding valsE_eq
          by (rule extern_vals_erased_ghost
                     [where tmF = "interp_term d fuel full" and tmE = ?tmE,
                      OF lenFlags len_eq allInr vals])

        \<comment> \<open>The extern function does not depend on its ghost arguments. So the
            erased call returns the same world and value, and the ref updates
            of the Ref parameters that are not ghost. \<close>
        have gi: "extern_fun_ghost_independent info externFun"
          using extern infoG f_lookup' Inr
          unfolding extern_funs_ghost_independent_def by blast
        let ?rflags = "ref_param_ghost_flags info"
        have extE: "externFun (IS_World full) (drop_ghost ?flagsF (rights ?valsF))
                      = (newWorld, drop_ghost ?rflags refUpdates, externRetVal)"
          by (rule extern_fun_ghost_independentD[OF gi lenV ext_eq])

        \<comment> \<open>The lvalues passed in Ref positions: those of the parameters that
            are not ghost are at corresponding addresses in the two states;
            those of the ghost parameters are ghost cells of the full state. \<close>
        have keepR: "\<forall>tm name. (tm, ((name, Ref), NotGhost))
                                  \<in> set (zip argTms (zip (IF_Args f) ?flagsF)) \<longrightarrow>
                       (\<exists>addr path i. interp_writable_lvalue d fuel full tm = Inr (addr, path) \<and>
                                      interp_writable_lvalue d fuel erased (?er tm) = Inr (i, path) \<and>
                                      i < length emb \<and> emb ! i = addr)"
        proof (intro allI impI)
          fix tm name
          assume mem: "(tm, ((name, Ref), NotGhost)) \<in> set (zip argTms (zip (IF_Args f) ?flagsF))"
          have mem2: "(tm, (name, Ref)) \<in> set (zip argTms (IF_Args f))"
            by (rule in_set_zip_zipD[OF mem])
          from fold_process_one_arg_ref_lvalue_ok
                 [OF foldF len_eq[symmetric] lenC lenB refl mem2]
          obtain lval where lv0: "interp_writable_lvalue d fuel full tm = Inr lval"
            by blast
          obtain addr path where ap: "lval = (addr, path)" by (cases lval)
          from lv0 ap have s: "interp_writable_lvalue d fuel full tm = Inr (addr, path)"
            by simp
          from refs[rule_format, OF mem s] obtain i where
            sE: "interp_writable_lvalue d fuel erased (?er tm) = Inr (i, path)" and
            i_lt: "i < length emb" and ei: "emb ! i = addr"
            by blast
          from s sE i_lt ei
          show "\<exists>addr path i. interp_writable_lvalue d fuel full tm = Inr (addr, path) \<and>
                              interp_writable_lvalue d fuel erased (?er tm) = Inr (i, path) \<and>
                              i < length emb \<and> emb ! i = addr"
            by blast
        qed
        have ghostR: "\<forall>tm name. (tm, ((name, Ref), Ghost))
                                   \<in> set (zip argTms (zip (IF_Args f) ?flagsF)) \<longrightarrow>
                        (\<exists>addr path. interp_writable_lvalue d fuel full tm = Inr (addr, path) \<and>
                                     addr < length (IS_Store full) \<and> addr \<notin> set emb)"
        proof (intro allI impI)
          fix tm name
          assume mem: "(tm, ((name, Ref), Ghost)) \<in> set (zip argTms (zip (IF_Args f) ?flagsF))"
          have mem2: "(tm, (name, Ref)) \<in> set (zip argTms (IF_Args f))"
            by (rule in_set_zip_zipD[OF mem])
          from fold_process_one_arg_ref_lvalue_ok
                 [OF foldF len_eq[symmetric] lenC lenB refl mem2]
          obtain lval where lv0: "interp_writable_lvalue d fuel full tm = Inr lval"
            by blast
          obtain addr path where ap: "lval = (addr, path)" by (cases lval)
          from lv0 ap have s: "interp_writable_lvalue d fuel full tm = Inr (addr, path)"
            by simp
          from ghost_refs[rule_format, OF mem s] s
          show "\<exists>addr path. interp_writable_lvalue d fuel full tm = Inr (addr, path) \<and>
                            addr < length (IS_Store full) \<and> addr \<notin> set emb"
            by blast
        qed
        note xrefs = extern_refs_erased_ghost
                       [where lvF = "interp_writable_lvalue d fuel full" and lvE = ?lvE,
                        OF lenFlags len_eq keepR ghostR,
                        unfolded ref_param_ghost_flags_zip[OF flags]]

        \<comment> \<open>Both states get the new world. The full state then applies all
            the ref updates, and the erased state those of the Ref parameters
            that are not ghost. \<close>
        have relW: "state_erased env emb ?fullW ?erasedW"
          by (rule state_erased_set_world[OF rel])
        have lenW: "length (IS_Store full) = length (IS_Store ?fullW)" by simp
        from apply_ref_updates_erased_ghost[OF xrefs lenW relW final_eq]
        obtain newErased where
          finalE0: "apply_ref_updates ?erasedW ?refsXE (drop_ghost ?rflags refUpdates)
                      = Inr newErased" and
          relN: "state_erased env emb finalState newErased"
          by blast
        have finalE: "apply_ref_updates ?erasedW
                        (rights (map (\<lambda>((_, vr), refResult).
                                        if vr = Ref then refResult else Inl TypeError)
                                     (zip ?paramsE
                                          (map (interp_writable_lvalue d fuel erased) ?argsE))))
                        (drop_ghost ?rflags refUpdates)
                      = Inr newErased"
          using finalE0 by (simp only: refsE_eq)
        have relN': "state_erased env emb newFull newErased"
          unfolding newFull_eq by (rule relN)
        have callE: "interp_function_call d (Suc fuel) erased fnName argTys ?argsE
                       = Inr (newErased, retVal)"
          using lookE lenE tyLen_eq foldE Inr valsE_drop extE finalE ret_eq
          by (simp add: Let_def paramsE_eq' D(3) D(6))
        from callE relN' show ?thesis by blast
      qed
    qed
  }
qed


(* ========================================================================== *)
(* The simulation theorem *)
(* ========================================================================== *)

(* If a statement list of a non-ghost function is well-typed in
   NotGhost mode, and it runs to completion from the full state, then its
   erasure runs to completion from the erased state, at the same depth and
   fuel, with a related result.

   The hypothesis about the function table of the full state says that it
   matches the signatures of the environment, and that each body is well-typed
   in the mode of its function (funs_exist_in_state, which is part of the
   state invariant state_matches_env).

   Erasure reads the ghost flags of parameters from the function signatures of
   the environment. The functions of the erased state are erased with the same
   signatures (funs_erased, which is part of state_erased). *)
theorem erase_ghost_simulation:
  fixes full erased :: "'w InterpState"
  assumes fg: "TE_FunctionGhost env = NotGhost"
    and fes: "funs_exist_in_state full env"
    and rel: "state_erased env emb full erased"
    and T: "core_statement_list_type env NotGhost stmts = Some env'"
    and H: "interp_statement_list d fuel full stmts = Inr res"
  shows "\<exists>res'. interp_statement_list d fuel erased
                  (erase_ghost_statement_list (TE_Functions env) stmts) = Inr res'
              \<and> result_erased env' emb res res'"
  by (rule erase_ghost_simulation_aux(5)
             [OF funs_exist_in_state_param_flags_agree[OF fes]
                 funs_exist_in_state_bodies_typed[OF fes]
                 funs_exist_in_state_respect_purity[OF fes]
                 funs_exist_in_state_param_names_distinct[OF fes]
                 funs_exist_in_state_extern_ghost_independent[OF fes],
              rule_format, OF refl refl fg rel T H])

(* The same, with the whole state invariant as the hypothesis. *)
corollary erase_ghost_simulation_state_matches:
  fixes full erased :: "'w InterpState"
  assumes "TE_FunctionGhost env = NotGhost"
    and "state_matches_env full env storeTyping"
    and "state_erased env emb full erased"
    and "core_statement_list_type env NotGhost stmts = Some env'"
    and "interp_statement_list d fuel full stmts = Inr res"
  shows "\<exists>res'. interp_statement_list d fuel erased
                  (erase_ghost_statement_list (TE_Functions env) stmts) = Inr res'
              \<and> result_erased env' emb res res'"
proof -
  from assms(2) have fes: "funs_exist_in_state full env"
    by (simp add: state_matches_env_def)
  show ?thesis by (rule erase_ghost_simulation[OF assms(1) fes assms(3-5)])
qed

end

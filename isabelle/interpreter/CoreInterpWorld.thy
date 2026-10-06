theory CoreInterpWorld
  imports CoreInterpPreservation StateMatchesEnv
begin

(* Pure code leaves the world unchanged.

   The world (IS_World) is changed in one place only: a call to an extern
   function. The typing rules allow a call of an impure function only in executable
   code of an impure function (core_impure_call_type), and a pure extern function
   returns the world it was given (extern_fun_contract). So:

    - a call of a pure function leaves the world unchanged;
    - a statement that is typed in Ghost mode, or in a pure function, leaves
      the world unchanged.

   Terms do not return a state, so nothing needs to be proved about them. *)


(* ========================================================================== *)
(* The helper functions *)
(* ========================================================================== *)

lemma process_one_arg_world:
  assumes "process_one_arg arg (Inr state) = Inr state'"
  shows "IS_World state' = IS_World state"
proof -
  obtain name vr gh refRes valRes where arg_eq: "arg = ((name, vr, gh), refRes, valRes)"
    by (cases arg) auto
  show ?thesis
  proof (cases vr)
    case Var
    show ?thesis
    proof (cases valRes)
      case (Inl err)
      with arg_eq Var assms show ?thesis by simp
    next
      case (Inr val)
      let ?alloc = "alloc_store state val"
      from arg_eq Var Inr assms
      have state'_eq:
        "state' = (fst ?alloc) \<lparr> IS_Locals := fmupd name (snd ?alloc) (IS_Locals (fst ?alloc)),
                                  IS_Refs := fmdrop name (IS_Refs (fst ?alloc)),
                                  IS_ConstLocals := finsert name (IS_ConstLocals (fst ?alloc)) \<rparr>"
        by (simp add: case_prod_beta)
      have "IS_World (fst ?alloc) = IS_World state"
        by (simp add: Let_def)
      with state'_eq show ?thesis by simp
    qed
  next
    case Ref
    show ?thesis
    proof (cases refRes)
      case (Inl err)
      with arg_eq Ref assms show ?thesis by simp
    next
      case (Inr addrPath)
      obtain addr path where addrPath_eq: "addrPath = (addr, path)" by (cases addrPath)
      show ?thesis
      proof (cases valRes)
        case Inl
        with arg_eq Ref Inr addrPath_eq assms show ?thesis by simp
      next
        case (Inr v)
        from arg_eq Ref \<open>refRes = Inr addrPath\<close> addrPath_eq Inr assms
        have "state' = state \<lparr> IS_Locals := fmdrop name (IS_Locals state),
                                IS_Refs := fmupd name (addr, path) (IS_Refs state),
                                IS_ConstLocals := fminus (IS_ConstLocals state) {|name|} \<rparr>"
          by simp
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma fold_process_one_arg_world:
  assumes "fold process_one_arg args (Inr state) = Inr state'"
  shows "IS_World state' = IS_World state"
  using assms
proof (induction args arbitrary: state)
  case Nil
  then show ?case by simp
next
  case (Cons arg args)
  show ?case
  proof (cases "process_one_arg arg (Inr state)")
    case (Inl err)
    then have "fold process_one_arg (arg # args) (Inr state) = Inl err"
      by (simp add: fold_process_one_arg_error)
    with Cons.prems show ?thesis by simp
  next
    case (Inr state1)
    note step = process_one_arg_world[OF Inr]
    from Inr Cons.prems have "fold process_one_arg args (Inr state1) = Inr state'"
      by simp
    from Cons.IH[OF this] step show ?thesis by simp
  qed
qed

lemma apply_ref_updates_world:
  assumes "apply_ref_updates state lvs vs = Inr state'"
  shows "IS_World state' = IS_World state"
  using assms
proof (induction state lvs vs arbitrary: state' rule: apply_ref_updates.induct)
  case (1 state)
  then show ?case by simp
next
  case (2 state addr path rest_lvals newVal rest_vals)
  show ?case
  proof (cases "update_value_at_path (IS_Store state ! addr) path newVal")
    case (Inl err)
    with 2 show ?thesis by simp
  next
    case (Inr updated_val)
    let ?state1 = "state \<lparr> IS_Store := (IS_Store state)[addr := updated_val] \<rparr>"
    from Inr 2(2) have rec: "apply_ref_updates ?state1 rest_lvals rest_vals = Inr state'"
      by simp
    show ?thesis using "2.IH" Inr local.rec by fastforce
  qed
qed simp_all

lemma perform_swap_world:
  assumes "perform_swap state lv1 lv2 = Inr state'"
  shows "IS_World state' = IS_World state"
proof -
  obtain addr1 path1 where l: "lv1 = (addr1, path1)" by (cases lv1)
  obtain addr2 path2 where r: "lv2 = (addr2, path2)" by (cases lv2)
  from assms[unfolded l r, symmetric] show ?thesis
    by (auto simp: Let_def split: sum.splits)
qed


(* ========================================================================== *)
(* Facts about typing *)
(* ========================================================================== *)

(* The arm of a Match that is run is typed in the mode of the Match. *)
lemma match_arm_typed:
  assumes "core_statement_type env ghost (CoreStmt_Match g scrut arms) = Some env'"
    and "armStmts \<in> snd ` set arms"
  shows "\<exists>armEnv. core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) g armStmts
                    = Some armEnv"
proof -
  from assms(1) obtain scrutTy where
    sT: "core_term_type env g scrut = Some scrutTy"
    by (cases "core_term_type env g scrut") (simp_all split: if_splits)
  from sT assms
  have "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) g armStmts \<noteq> None"
    by (auto simp: Let_def list_all_iff split: if_splits)
  then show ?thesis by auto
qed

(* A call made in Ghost mode, or in a pure function, is a call of a pure
   function. *)
lemma pure_context_callee_pure:
  assumes "core_impure_call_type env g fnName tyArgs tmArgs = Some retTy"
    and "g = Ghost \<or> \<not> TE_FunctionImpure env"
  shows "\<exists>info. fmlookup (TE_Functions env) fnName = Some info \<and> \<not> FI_Impure info"
proof -
  from core_impure_call_type_fn_facts[OF assms(1)] obtain info where
    info: "fmlookup (TE_Functions env) fnName = Some info" and
    imp: "FI_Impure info \<longrightarrow> g = NotGhost \<and> TE_FunctionImpure env"
    by blast
  from imp assms(2) have "\<not> FI_Impure info" by auto
  with info show ?thesis by blast
qed


(* ========================================================================== *)
(* The function table *)
(* ========================================================================== *)

(* What the lemma below needs to know about the function table of the state:
   the body of each function is well-typed, in some environment that has the
   same function signatures and that records whether the function is impure;
   and a pure extern function returns the world it was given. It follows from
   funs_exist_in_state (see funs_exist_in_state_respect_purity below). *)
definition funs_respect_purity ::
    "(string, FunInfo) fmap \<Rightarrow> (string, 'w InterpFun) fmap \<Rightarrow> bool" where
  "funs_respect_purity funInfos funs \<equiv>
    \<forall>fnName info f.
      fmlookup funInfos fnName = Some info \<longrightarrow>
      fmlookup funs fnName = Some f \<longrightarrow>
        (case IF_Body f of
           Inl body \<Rightarrow>
             (\<exists>benv g. TE_Functions benv = funInfos
                     \<and> TE_FunctionImpure benv = FI_Impure info
                     \<and> core_statement_list_type benv g body \<noteq> None)
         | Inr externFun \<Rightarrow>
             \<not> FI_Impure info \<longrightarrow> (\<forall>world vals. fst (externFun world vals) = world))"

lemma funs_exist_in_state_respect_purity:
  assumes "funs_exist_in_state state env"
  shows "funs_respect_purity (TE_Functions env) (IS_Functions state)"
  unfolding funs_respect_purity_def
proof (intro allI impI)
  fix fnName info f
  assume info: "fmlookup (TE_Functions env) fnName = Some info"
    and f: "fmlookup (IS_Functions state) fnName = Some f"
  from assms info
  have "case fmlookup (IS_Functions state) fnName of
          None \<Rightarrow> False
        | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun"
    unfolding funs_exist_in_state_def by blast
  with f have m: "fun_info_matches_interp_fun env info f" by simp
  show "case IF_Body f of
          Inl body \<Rightarrow>
            (\<exists>benv g. TE_Functions benv = TE_Functions env
                    \<and> TE_FunctionImpure benv = FI_Impure info
                    \<and> core_statement_list_type benv g body \<noteq> None)
        | Inr externFun \<Rightarrow>
            \<not> FI_Impure info \<longrightarrow> (\<forall>world vals. fst (externFun world vals) = world)"
  proof (cases "IF_Body f")
    case (Inl body)
    let ?benv = "body_env_for env (map fst (IF_Args f)) info"
    from m Inl have t: "core_statement_list_type ?benv (FI_Ghost info) body \<noteq> None"
      by (simp add: fun_info_matches_interp_fun_def)
    have fns: "TE_Functions ?benv = TE_Functions env"
      and imp: "TE_FunctionImpure ?benv = FI_Impure info"
      by (simp_all add: body_env_for_def)
    from fns imp t
    have "\<exists>benv g. TE_Functions benv = TE_Functions env
                 \<and> TE_FunctionImpure benv = FI_Impure info
                 \<and> core_statement_list_type benv g body \<noteq> None"
      by blast
    then show ?thesis using Inl by simp
  next
    case (Inr externFun)
    from m Inr have c: "extern_fun_contract env info externFun"
      by (simp add: fun_info_matches_interp_fun_def)
    show ?thesis using Inr extern_fun_contract_pure_world[OF c] by auto
  qed
qed


(* ========================================================================== *)
(* The main induction *)
(* ========================================================================== *)

(* All three statements are proved together by induction on the fuel, at a
   fixed depth.

   The function signatures and the function table are fixed outside the
   induction (neither changes as statements run), so that the hypothesis
   about them need not be carried along.

   The hypothesis "g = Ghost or the enclosing function is pure" passes to
   the statements inside a statement: they are typed in the same environment
   (up to TE_ProofTopLevel), in a mode that is Ghost if g is. *)
lemma interp_world_aux:
  fixes funInfos :: "(string, FunInfo) fmap"
    and funs :: "(string, 'w InterpFun) fmap"
  assumes pure: "funs_respect_purity funInfos funs"
  shows "\<forall>env env' g (state :: 'w InterpState) res.
           TE_Functions env = funInfos \<longrightarrow>
           IS_Functions state = funs \<longrightarrow>
           (g = Ghost \<or> \<not> TE_FunctionImpure env) \<longrightarrow>
           core_statement_type env g stmt = Some env' \<longrightarrow>
           interp_statement d fuel state stmt = Inr res \<longrightarrow>
             IS_World (result_state res) = IS_World state"
    and "\<forall>env env' g (state :: 'w InterpState) res.
           TE_Functions env = funInfos \<longrightarrow>
           IS_Functions state = funs \<longrightarrow>
           (g = Ghost \<or> \<not> TE_FunctionImpure env) \<longrightarrow>
           core_statement_list_type env g stmts = Some env' \<longrightarrow>
           interp_statement_list d fuel state stmts = Inr res \<longrightarrow>
             IS_World (result_state res) = IS_World state"
    and "\<forall>info (state :: 'w InterpState) state' retVal.
           IS_Functions state = funs \<longrightarrow>
           fmlookup funInfos fnName = Some info \<longrightarrow>
           \<not> FI_Impure info \<longrightarrow>
           interp_function_call d fuel state fnName argTys argTms = Inr (state', retVal) \<longrightarrow>
             IS_World state' = IS_World state"
proof (induction fuel arbitrary: stmt stmts fnName argTys argTms rule: nat.induct)
  case zero
  {
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  next
    case 3 show ?case by simp
  }
next
  case (Suc fuel)
  note IH_stmt = Suc.IH(1)[rule_format]
  note IH_list = Suc.IH(2)[rule_format]
  note IH_call = Suc.IH(3)[rule_format]
  {
    case (1 stmt) show ?case
    proof (intro allI impI)
      fix env env' :: CoreTyEnv and g :: GhostOrNot
        and state :: "'w InterpState" and res :: "'w ExecResult"
      assume fn_eq: "TE_Functions env = funInfos"
        and funs_eq: "IS_Functions state = funs"
        and ok: "g = Ghost \<or> \<not> TE_FunctionImpure env"
        and T: "core_statement_type env g stmt = Some env'"
        and H: "interp_statement d (Suc fuel) state stmt = Inr res"

      \<comment> \<open>The environment in which the body of a While, Match or Block is typed. \<close>
      have fnB: "TE_Functions (env \<lparr> TE_ProofTopLevel := False \<rparr>) = funInfos"
        using fn_eq by simp

      show "IS_World (result_state res) = IS_World state"
      proof (cases stmt)
        case (CoreStmt_VarDecl gd varName vr ty initTm)
        show ?thesis
        proof (cases vr)
          case Var
          from Var H CoreStmt_VarDecl obtain initVal where
            iv: "interp_term d fuel state initTm = Inr initVal"
            by (auto split: sum.splits)
          from Var H[symmetric] CoreStmt_VarDecl iv show ?thesis
            by (simp add: Let_def)
        next
          case Ref
          \<comment> \<open>Two branches: const-base (copy) or writable-base (alias). \<close>
          from Ref H CoreStmt_VarDecl obtain baseName where
            base: "lvalue_base_name initTm = Some baseName"
            by (cases "lvalue_base_name initTm") simp_all
          show ?thesis
          proof (cases "baseName |\<in>| IS_ConstLocals state
                        \<or> (fmlookup (IS_Locals state) baseName = None
                           \<and> fmlookup (IS_Refs state) baseName = None)")
            case True
            with Ref H CoreStmt_VarDecl base obtain val where
              iv: "interp_term d fuel state initTm = Inr val"
              by (auto split: sum.splits)
            from Ref H[symmetric] CoreStmt_VarDecl base True iv show ?thesis
              by (simp add: Let_def)
          next
            case False
            with Ref H CoreStmt_VarDecl base obtain addrPath where
              lv: "interp_writable_lvalue d fuel state initTm = Inr addrPath"
              by (auto split: sum.splits)
            from Ref H[symmetric] CoreStmt_VarDecl base False lv show ?thesis
              by simp
          qed
        qed
      next
        case (CoreStmt_VarDeclCall gd varName varTy castOpt fnName argTys argTms)
        from T CoreStmt_VarDeclCall have gd_ok: "g = Ghost \<longrightarrow> gd = Ghost"
          by (auto split: if_splits)
        from T CoreStmt_VarDeclCall obtain retTy where
          callT: "core_impure_call_type env gd fnName argTys argTms = Some retTy"
          by (auto split: if_splits option.splits)
        have ok': "gd = Ghost \<or> \<not> TE_FunctionImpure env"
          using ok gd_ok by auto
        from pure_context_callee_pure[OF callT ok'] fn_eq obtain info where
          info: "fmlookup funInfos fnName = Some info" and np: "\<not> FI_Impure info"
          by auto
        \<comment> \<open>Run the call (giving newState), apply the cast, then alloc and bind. \<close>
        from H CoreStmt_VarDeclCall obtain newState retVal where
          call: "interp_function_call d fuel state fnName argTys argTms = Inr (newState, retVal)"
          by (auto split: sum.splits prod.splits)
        note w1 = IH_call[OF funs_eq info np call]
        from H CoreStmt_VarDeclCall call obtain initVal where
          cast: "apply_cast_opt castOpt retVal = Inr initVal"
          by (auto split: sum.splits)
        from H[symmetric] CoreStmt_VarDeclCall call cast
        have w2: "IS_World (result_state res) = IS_World newState"
          by (simp add: Let_def)
        show ?thesis using w1 w2 by simp
      next
        case (CoreStmt_Fix _ _) with H show ?thesis by simp
      next
        case (CoreStmt_Obtain varName varTy condTm)
        show ?thesis
        proof (cases d)
          case d_zero: 0
          with H CoreStmt_Obtain show ?thesis by simp
        next
          case d_Suc: (Suc d')
          from H[symmetric] CoreStmt_Obtain d_Suc obtain witness where
            res_eq: "res = Continue (bind_mutable_local varName witness state)"
            by (auto simp del: bind_mutable_local.simps split: sum.splits)
          show ?thesis by (simp add: res_eq Let_def)
        qed
      next
        case (CoreStmt_Use _) with H show ?thesis by simp
      next
        case (CoreStmt_Assign ga lhsLv rhsTm)
        from H CoreStmt_Assign obtain addr path where
          wl: "interp_writable_lvalue d fuel state lhsLv = Inr (addr, path)"
          by (auto split: sum.splits)
        from H CoreStmt_Assign wl obtain rhsVal where
          rv: "interp_term d fuel state rhsTm = Inr rhsVal"
          by (auto split: sum.splits)
        from H CoreStmt_Assign wl rv obtain newVal where
          upd: "update_value_at_path (IS_Store state ! addr) path rhsVal = Inr newVal"
          by (auto simp: Let_def split: sum.splits)
        from H[symmetric] CoreStmt_Assign wl rv upd show ?thesis
          by (simp add: Let_def)
      next
        case (CoreStmt_AssignCall ga lhsLv castOpt fnName argTys argTms)
        from T CoreStmt_AssignCall have ga_ok: "g = Ghost \<longrightarrow> ga = Ghost"
          by (auto split: if_splits)
        from T CoreStmt_AssignCall obtain retTy where
          callT: "core_impure_call_type env ga fnName argTys argTms = Some retTy"
          by (auto split: if_splits option.splits)
        have ok': "ga = Ghost \<or> \<not> TE_FunctionImpure env"
          using ok ga_ok by auto
        from pure_context_callee_pure[OF callT ok'] fn_eq obtain info where
          info: "fmlookup funInfos fnName = Some info" and np: "\<not> FI_Impure info"
          by auto
        \<comment> \<open>Resolve lhs, run the call (newState), apply cast, store. \<close>
        from H CoreStmt_AssignCall obtain addr path where
          wl: "interp_writable_lvalue d fuel state lhsLv = Inr (addr, path)"
          by (auto split: sum.splits)
        from H CoreStmt_AssignCall wl obtain newState retVal where
          call: "interp_function_call d fuel state fnName argTys argTms = Inr (newState, retVal)"
          by (auto split: sum.splits prod.splits)
        note w1 = IH_call[OF funs_eq info np call]
        from H CoreStmt_AssignCall wl call obtain rhsVal where
          cast: "apply_cast_opt castOpt retVal = Inr rhsVal"
          by (auto split: sum.splits)
        from H CoreStmt_AssignCall wl call cast obtain newVal where
          upd: "update_value_at_path (IS_Store newState ! addr) path rhsVal = Inr newVal"
          by (auto simp: Let_def split: sum.splits)
        from H[symmetric] CoreStmt_AssignCall wl call cast upd
        have w2: "IS_World (result_state res) = IS_World newState"
          by (simp add: Let_def)
        show ?thesis using w1 w2 by simp
      next
        case (CoreStmt_Swap gs lhsTm rhsTm)
        from H CoreStmt_Swap obtain lhsLv where
          lhs: "interp_writable_lvalue d fuel state lhsTm = Inr lhsLv"
          by (auto split: sum.splits)
        with H CoreStmt_Swap obtain rhsLv where
          rhs: "interp_writable_lvalue d fuel state rhsTm = Inr rhsLv"
          by (auto split: sum.splits)
        with H CoreStmt_Swap lhs obtain newState where
          sw: "perform_swap state lhsLv rhsLv = Inr newState"
          and res_eq: "res = Continue newState"
          by (auto split: sum.splits)
        show ?thesis using perform_swap_world[OF sw] by (simp add: res_eq)
      next
        case (CoreStmt_Return tm)
        from H CoreStmt_Return obtain v where res_eq: "res = Return state v"
          by (auto split: sum.splits)
        show ?thesis by (simp add: res_eq)
      next
        case (CoreStmt_Assert condOpt proofBody)
        have res_eq: "res = Continue state"
        proof (cases condOpt)
          case None
          with H CoreStmt_Assert show ?thesis by simp
        next
          case (Some condTm)
          from H CoreStmt_Assert Some obtain condVal where
            cv: "interp_term d fuel state condTm = Inr condVal"
            by (auto split: sum.splits)
          show ?thesis
          proof (cases condVal)
            case (CV_Bool b)
            with H CoreStmt_Assert Some cv show ?thesis by (cases b) simp_all
          next
            case CV_FiniteInt with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Variant with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Record with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Array with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Int with H CoreStmt_Assert Some cv show ?thesis by simp
          next
            case CV_Real with H CoreStmt_Assert Some cv show ?thesis by simp
          qed
        qed
        show ?thesis by (simp add: res_eq)
      next
        case (CoreStmt_Assume _)
        from H CoreStmt_Assume have res_eq: "res = Continue state" by simp
        show ?thesis by (simp add: res_eq)
      next
        case (CoreStmt_While gw condTm invars decr bodyStmts)
        from T CoreStmt_While have gw_ok: "g = Ghost \<longrightarrow> gw = Ghost"
          by (auto split: if_splits)
        from T CoreStmt_While obtain bodyEnv where
          bodyT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) gw bodyStmts
                    = Some bodyEnv"
          by (auto split: if_splits option.splits CoreType.splits)
        have okB: "gw = Ghost \<or> \<not> TE_FunctionImpure (env \<lparr> TE_ProofTopLevel := False \<rparr>)"
          using ok gw_ok by auto
        \<comment> \<open>The run succeeded, so the invariants were evaluated and all held.
            Evaluating them is evaluating terms, which cannot change the state. \<close>
        from H CoreStmt_While obtain invarVals where
          iv: "interp_term_list d fuel state invars = Inr invarVals" and
          ie: "invariants_error invarVals = None"
          by (auto split: sum.splits option.splits)
        note [simp] = iv ie
        from H CoreStmt_While obtain condVal where
          cv: "interp_term d fuel state condTm = Inr condVal"
          by (auto split: sum.splits)
        show ?thesis
        proof (cases condVal)
          case (CV_Bool b)
          show ?thesis
          proof (cases b)
            case False
            with CoreStmt_While H cv CV_Bool
            have res_eq: "res = Continue state" by simp
            show ?thesis by (simp add: res_eq)
          next
            case True
            with CoreStmt_While H cv CV_Bool
            obtain bodyRes where
              body: "interp_statement_list d fuel state bodyStmts = Inr bodyRes"
              by (auto split: sum.splits)
            note w1 = IH_list[OF fnB funs_eq okB bodyT body]
            show ?thesis
            proof (cases bodyRes)
              case (Return state1 v)
              from CoreStmt_While H cv CV_Bool True body Return
              have res_eq: "res = Return (restore_scope state state1) v" by simp
              show ?thesis using w1 Return by (simp add: res_eq)
            next
              case (Continue state1)
              let ?rs = "restore_scope state state1"
              have funs_rs: "IS_Functions ?rs = funs"
                using static_parts_eqD(2)[OF interp_statement_list_static[OF body]]
                      Continue funs_eq
                by simp
              \<comment> \<open>The loop runs again from the restored state. \<close>
              from CoreStmt_While H cv CV_Bool True body Continue
              have rec_eq: "interp_statement d fuel ?rs
                               (CoreStmt_While gw condTm invars decr bodyStmts) = Inr res"
                by simp
              note T' = T[unfolded CoreStmt_While]
              note w2 = IH_stmt[OF fn_eq funs_rs ok T' rec_eq]
              show ?thesis using w1 w2 Continue by simp
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
      next
        case (CoreStmt_Match gm scrutTm arms)
        from T CoreStmt_Match have gm_ok: "g = Ghost \<longrightarrow> gm = Ghost"
          by (auto split: if_splits)
        have okB: "gm = Ghost \<or> \<not> TE_FunctionImpure (env \<lparr> TE_ProofTopLevel := False \<rparr>)"
          using ok gm_ok by auto
        from H CoreStmt_Match obtain scrutVal where
          sv: "interp_term d fuel state scrutTm = Inr scrutVal"
          by (auto split: sum.splits)
        from H CoreStmt_Match sv obtain armStmts where
          arm: "find_matching_arm scrutVal arms = Inr armStmts"
          by (auto split: sum.splits)
        note mem = find_matching_arm_in_arms[OF arm]
        from match_arm_typed[OF T[unfolded CoreStmt_Match] mem] obtain armEnv where
          armT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) gm armStmts
                   = Some armEnv"
          by auto
        from H CoreStmt_Match sv arm obtain bodyRes where
          body: "interp_statement_list d fuel state armStmts = Inr bodyRes"
          by (auto split: sum.splits)
        note w1 = IH_list[OF fnB funs_eq okB armT body]
        show ?thesis
        proof (cases bodyRes)
          case (Return state1 v)
          from CoreStmt_Match H sv arm body Return
          have res_eq: "res = Return (restore_scope state state1) v" by simp
          show ?thesis using w1 Return by (simp add: res_eq)
        next
          case (Continue state1)
          from CoreStmt_Match H sv arm body Continue
          have res_eq: "res = Continue (restore_scope state state1)" by simp
          show ?thesis using w1 Continue by (simp add: res_eq)
        qed
      next
        case (CoreStmt_ShowHide _ _)
        from H CoreStmt_ShowHide have res_eq: "res = Continue state" by simp
        show ?thesis by (simp add: res_eq)
      next
        case (CoreStmt_Block blockBody)
        from T CoreStmt_Block obtain bodyEnv where
          bodyT: "core_statement_list_type (env \<lparr> TE_ProofTopLevel := False \<rparr>) g blockBody
                    = Some bodyEnv"
          by (auto split: option.splits)
        have okB: "g = Ghost \<or> \<not> TE_FunctionImpure (env \<lparr> TE_ProofTopLevel := False \<rparr>)"
          using ok by auto
        from H CoreStmt_Block obtain bodyRes where
          body: "interp_statement_list d fuel state blockBody = Inr bodyRes"
          by (auto split: sum.splits)
        note w1 = IH_list[OF fnB funs_eq okB bodyT body]
        show ?thesis
        proof (cases bodyRes)
          case (Return state1 v)
          from CoreStmt_Block H body Return
          have res_eq: "res = Return (restore_scope state state1) v" by simp
          show ?thesis using w1 Return by (simp add: res_eq)
        next
          case (Continue state1)
          from CoreStmt_Block H body Continue
          have res_eq: "res = Continue (restore_scope state state1)" by simp
          show ?thesis using w1 Continue by (simp add: res_eq)
        qed
      qed
    qed
  next
    case (2 stmts) show ?case
    proof (intro allI impI)
      fix env env' :: CoreTyEnv and g :: GhostOrNot
        and state :: "'w InterpState" and res :: "'w ExecResult"
      assume fn_eq: "TE_Functions env = funInfos"
        and funs_eq: "IS_Functions state = funs"
        and ok: "g = Ghost \<or> \<not> TE_FunctionImpure env"
        and T: "core_statement_list_type env g stmts = Some env'"
        and H: "interp_statement_list d (Suc fuel) state stmts = Inr res"
      show "IS_World (result_state res) = IS_World state"
      proof (cases stmts)
        case Nil
        with H have res_eq: "res = Continue state" by simp
        show ?thesis by (simp add: res_eq)
      next
        case (Cons stmt1 rest)
        from T Cons obtain envMid where
          T1: "core_statement_type env g stmt1 = Some envMid" and
          T2: "core_statement_list_type envMid g rest = Some env'"
          by (auto split: option.splits)
        from Cons H obtain res1 where
          r1: "interp_statement d fuel state stmt1 = Inr res1"
          by (auto split: sum.splits)
        note w1 = IH_stmt[OF fn_eq funs_eq ok T1 r1]
        show ?thesis
        proof (cases res1)
          case (Return state1 v)
          from Cons H r1 Return have res_eq: "res = Return state1 v" by simp
          show ?thesis using w1 Return by (simp add: res_eq)
        next
          case (Continue state1)
          \<comment> \<open>The first statement changes neither the function signatures, nor the
              impurity of the enclosing function, nor the function table. \<close>
          have fx: "tyenv_fixed_eq env envMid" by (rule core_statement_type_fixed_eq[OF T1])
          have fn1: "TE_Functions envMid = funInfos"
            using fx fn_eq by (simp add: tyenv_fixed_eq_def)
          have ok1: "g = Ghost \<or> \<not> TE_FunctionImpure envMid"
            using fx ok by (simp add: tyenv_fixed_eq_def)
          have funs1: "IS_Functions state1 = funs"
            using static_parts_eqD(2)[OF interp_statement_static[OF r1]] Continue funs_eq
            by simp
          from Cons H r1 Continue
          have rec: "interp_statement_list d fuel state1 rest = Inr res" by simp
          note w2 = IH_list[OF fn1 funs1 ok1 T2 rec]
          show ?thesis using w1 w2 Continue by simp
        qed
      qed
    qed
  next
    case (3 fnName argTys argTms) show ?case
    proof (intro allI impI)
      fix info :: FunInfo and state state' :: "'w InterpState" and retVal
      assume funs_eq: "IS_Functions state = funs"
        and info: "fmlookup funInfos fnName = Some info"
        and np: "\<not> FI_Impure info"
        and H: "interp_function_call d (Suc fuel) state fnName argTys argTms = Inr (state', retVal)"
      \<comment> \<open>Unfold the function-call body enough to name each intermediate state. \<close>
      obtain f where f_lookup: "fmlookup (IS_Functions state) fnName = Some f"
        using H by (cases "fmlookup (IS_Functions state) fnName") simp_all
      from H f_lookup have len_eq: "length argTms = length (IF_Args f)"
        by (cases "length argTms = length (IF_Args f)") simp_all
      from H f_lookup len_eq have tyLen_eq: "length argTys = length (IF_TyArgs f)"
        by (cases "length argTys = length (IF_TyArgs f)") simp_all
      let ?refResults = "map (interp_writable_lvalue d fuel state) argTms"
      let ?valResults = "map (interp_term d fuel state) argTms"
      let ?argTuples = "zip (IF_Args f) (zip ?refResults ?valResults)"
      let ?calleeTyArgs = "fmap_of_list (zip (IF_TyArgs f) (map (apply_subst (IS_TyArgs state)) argTys))"
      let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                     IS_ConstLocals := {||},
                                     IS_TyArgs := ?calleeTyArgs \<rparr>"
      obtain preCallState where
        fold_eq: "fold process_one_arg ?argTuples (Inr ?clearedState) = Inr preCallState"
        using H f_lookup len_eq tyLen_eq
        by (cases "fold process_one_arg ?argTuples (Inr ?clearedState)") (simp_all add: Let_def)
      have pre_w: "IS_World preCallState = IS_World state"
        using fold_process_one_arg_world[OF fold_eq] by simp
      have pre_funs: "IS_Functions preCallState = funs"
        using fold_process_one_arg_preserves_globals_funs[OF fold_eq] funs_eq by simp

      \<comment> \<open>What the function table says about this function. \<close>
      have f_lookup': "fmlookup funs fnName = Some f"
        using f_lookup funs_eq by simp
      from pure info f_lookup'
      have fp: "case IF_Body f of
                  Inl body \<Rightarrow>
                    (\<exists>benv g. TE_Functions benv = funInfos
                            \<and> TE_FunctionImpure benv = FI_Impure info
                            \<and> core_statement_list_type benv g body \<noteq> None)
                | Inr externFun \<Rightarrow>
                    \<not> FI_Impure info \<longrightarrow> (\<forall>world vals. fst (externFun world vals) = world)"
        unfolding funs_respect_purity_def by blast

      show "IS_World state' = IS_World state"
      proof (cases "IF_Body f")
        case (Inl bodyStmts)
        \<comment> \<open>Babylon body: it is typed in the environment of a pure function. \<close>
        from fp Inl obtain benv gb benv' where
          bf: "TE_Functions benv = funInfos" and
          bi: "TE_FunctionImpure benv = FI_Impure info" and
          bt: "core_statement_list_type benv gb bodyStmts = Some benv'"
          by auto
        have okb: "gb = Ghost \<or> \<not> TE_FunctionImpure benv"
          using bi np by simp
        from H f_lookup len_eq tyLen_eq fold_eq Inl
        obtain bodyRes where bodyEval:
          "interp_statement_list d fuel preCallState bodyStmts = Inr bodyRes"
          by (cases "interp_statement_list d fuel preCallState bodyStmts")
             (simp_all add: Let_def)
        note w = IH_list[OF bf pre_funs okb bt bodyEval]
        show ?thesis
        proof (cases bodyRes)
          case (Continue _)
          with H f_lookup len_eq tyLen_eq fold_eq Inl bodyEval show ?thesis
            by (simp add: Let_def)
        next
          case (Return postCallState bodyRetVal)
          from H f_lookup len_eq tyLen_eq fold_eq Inl bodyEval Return
          have state'_eq: "state' = restore_scope state postCallState"
            by (simp add: Let_def)
          from w Return pre_w show ?thesis by (simp add: state'_eq)
        qed
      next
        case (Inr externFun)
        \<comment> \<open>Extern function: a pure one returns the world it was given. \<close>
        let ?vals = "rights ?valResults"
        let ?refs = "rights (map (\<lambda>((_, vr, _), refResult).
                                      if vr = Ref then refResult else Inl TypeError)
                                 (zip (IF_Args f) ?refResults))"
        obtain newWorld refUpdates externRetVal where
          ext_eq: "externFun (IS_World state) ?vals = (newWorld, refUpdates, externRetVal)"
          by (cases "externFun (IS_World state) ?vals") auto
        from fp Inr np have "fst (externFun (IS_World state) ?vals) = IS_World state"
          by simp
        with ext_eq have nw: "newWorld = IS_World state" by simp
        let ?stateW = "state \<lparr> IS_World := newWorld \<rparr>"
        from H f_lookup len_eq tyLen_eq fold_eq Inr ext_eq
        obtain finalState where final_eq:
          "apply_ref_updates ?stateW ?refs refUpdates = Inr finalState"
          and state'_eq: "state' = finalState" and "retVal = externRetVal"
          by (cases "apply_ref_updates ?stateW ?refs refUpdates") (simp_all add: Let_def)
        from apply_ref_updates_world[OF final_eq] state'_eq nw show ?thesis
          by simp
      qed
    qed
  }
qed


(* ========================================================================== *)
(* The main results, in the form that callers use *)
(* ========================================================================== *)

(* A call of a pure function leaves the world unchanged. *)
theorem pure_function_call_keeps_world:
  assumes pure: "funs_respect_purity funInfos (IS_Functions state)"
    and info: "fmlookup funInfos fnName = Some info"
    and np: "\<not> FI_Impure info"
    and call: "interp_function_call d fuel state fnName argTys argTms = Inr (state', retVal)"
  shows "IS_World state' = IS_World state"
  by (rule interp_world_aux(3)[OF pure, rule_format, OF refl info np call])

(* A statement that is well-typed in Ghost mode, or in a pure function, leaves
   the world unchanged. *)
theorem pure_statement_keeps_world:
  assumes pure: "funs_respect_purity (TE_Functions env) (IS_Functions state)"
    and ok: "g = Ghost \<or> \<not> TE_FunctionImpure env"
    and T: "core_statement_type env g stmt = Some env'"
    and H: "interp_statement d fuel state stmt = Inr res"
  shows "IS_World (result_state res) = IS_World state"
  by (rule interp_world_aux(1)[OF pure, rule_format, OF refl refl ok T H])

theorem pure_statement_list_keeps_world:
  assumes pure: "funs_respect_purity (TE_Functions env) (IS_Functions state)"
    and ok: "g = Ghost \<or> \<not> TE_FunctionImpure env"
    and T: "core_statement_list_type env g stmts = Some env'"
    and H: "interp_statement_list d fuel state stmts = Inr res"
  shows "IS_World (result_state res) = IS_World state"
  by (rule interp_world_aux(2)[OF pure, rule_format, OF refl refl ok T H])

end

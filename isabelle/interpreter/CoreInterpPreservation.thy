theory CoreInterpPreservation
  imports CoreInterp
begin

(* The interpreter never modifies IS_Globals or IS_Functions. No clause in
   interp_term, interp_term_list, interp_writable_lvalue, interp_statement,
   interp_statement_list, or interp_function_call writes to those record
   fields, and none of the supporting helpers (alloc_store, process_one_arg,
   apply_ref_updates, perform_swap, restore_scope) do either. This lemma
   threads that observation through the mutual recursion so that callers
   can assume IS_Globals / IS_Functions are preserved across any successful
   interpreter run. *)

(* Helpers: IS_Globals / IS_Functions preservation for the leaf state
   transformers used inside the interpreter. *)

lemma alloc_store_preserves_globals_funs:
  "IS_Globals (fst (alloc_store state v)) = IS_Globals state"
  "IS_Functions (fst (alloc_store state v)) = IS_Functions state"
  by (simp_all add: Let_def)

lemma process_one_arg_preserves_globals_funs:
  assumes "process_one_arg arg (Inr state) = Inr state'"
  shows "IS_Globals state' = IS_Globals state \<and>
         IS_Functions state' = IS_Functions state"
proof -
  obtain name vr refRes valRes where arg_eq: "arg = ((name, vr), refRes, valRes)"
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
                                  IS_ConstNames := finsert name (IS_ConstNames (fst ?alloc)) \<rparr>"
        by (simp add: case_prod_beta)
      have "IS_Globals (fst ?alloc) = IS_Globals state"
           "IS_Functions (fst ?alloc) = IS_Functions state"
        by (simp_all add: alloc_store_preserves_globals_funs)
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
        have "state' = state \<lparr> IS_Refs := fmupd name (addr, path) (IS_Refs state) \<rparr>"
          by simp
        then show ?thesis by simp
      qed
    qed
  qed
qed

lemma fold_process_one_arg_error:
  "fold process_one_arg xs (Inl err) = Inl err"
  by (induct xs) simp_all

lemma fold_process_one_arg_preserves_globals_funs:
  assumes "fold process_one_arg args (Inr state) = Inr state'"
  shows "IS_Globals state' = IS_Globals state \<and>
         IS_Functions state' = IS_Functions state"
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
    from process_one_arg_preserves_globals_funs[OF Inr]
    have step: "IS_Globals state1 = IS_Globals state \<and>
                IS_Functions state1 = IS_Functions state" by simp
    from Inr Cons.prems have "fold process_one_arg args (Inr state1) = Inr state'"
      by simp
    from Cons.IH[OF this] step show ?thesis by simp
  qed
qed

lemma apply_ref_updates_preserves_globals_funs:
  assumes "apply_ref_updates state lvs vs = Inr state'"
  shows "IS_Globals state' = IS_Globals state \<and>
         IS_Functions state' = IS_Functions state"
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

lemma perform_swap_preserves_globals_funs:
  assumes "perform_swap state lv1 lv2 = Inr state'"
  shows "IS_Globals state' = IS_Globals state \<and>
         IS_Functions state' = IS_Functions state"
proof -
  obtain addr1 path1 where lv1_eq: "lv1 = (addr1, path1)" by (cases lv1)
  obtain addr2 path2 where lv2_eq: "lv2 = (addr2, path2)" by (cases lv2)
  from assms lv1_eq lv2_eq
  show ?thesis
    by (auto simp: Let_def split: sum.splits)
qed

lemma restore_scope_preserves_globals_funs:
  "IS_Globals (restore_scope old_state new_state) = IS_Globals new_state"
  "IS_Functions (restore_scope old_state new_state) = IS_Functions new_state"
  by simp_all


(* The main preservation theorem: interp_* never changes IS_Globals / IS_Functions.

   The six conjuncts are packaged into a single \<forall>-schematic statement so the
   mutual induction rule
     interp_term_interp_term_list_interp_writable_lvalue_interp_statement_
     interp_statement_list_interp_function_call.induct
   can be applied uniformly. Terms and lvalues don't produce states, so their
   conjuncts are trivially True. *)

definition exec_result_preserves_gf :: "'w InterpState \<Rightarrow> 'w ExecResult \<Rightarrow> bool" where
  "exec_result_preserves_gf state res \<equiv>
    (case res of
       Continue state' \<Rightarrow>
         IS_Globals state' = IS_Globals state \<and>
         IS_Functions state' = IS_Functions state
     | Return state' _ \<Rightarrow>
         IS_Globals state' = IS_Globals state \<and>
         IS_Functions state' = IS_Functions state)"

lemma exec_result_preserves_gf_Continue:
  "exec_result_preserves_gf state (Continue state') \<longleftrightarrow>
     IS_Globals state' = IS_Globals state \<and>
     IS_Functions state' = IS_Functions state"
  by (simp add: exec_result_preserves_gf_def)

lemma exec_result_preserves_gf_Return:
  "exec_result_preserves_gf state (Return state' v) \<longleftrightarrow>
     IS_Globals state' = IS_Globals state \<and>
     IS_Functions state' = IS_Functions state"
  by (simp add: exec_result_preserves_gf_def)

lemma interp_preserves_globals_funs:
  fixes dummy :: "'w InterpState"
  shows "\<forall>(state :: 'w InterpState) (val :: CoreValue).
           interp_term fuel state tm = Inr val \<longrightarrow> True"
    and "\<forall>(state :: 'w InterpState) (vals :: CoreValue list).
           interp_term_list fuel state tms = Inr vals \<longrightarrow> True"
    and "\<forall>(state :: 'w InterpState) (ap :: nat \<times> LValuePath list).
           interp_writable_lvalue fuel state lvTm = Inr ap \<longrightarrow> True"
    and "\<forall>(state :: 'w InterpState) res.
           interp_statement fuel state stmt = Inr res \<longrightarrow>
             exec_result_preserves_gf state res"
    and "\<forall>(state :: 'w InterpState) res.
           interp_statement_list fuel state stmts = Inr res \<longrightarrow>
             exec_result_preserves_gf state res"
    and "\<forall>(state :: 'w InterpState) state' retVal.
           interp_function_call fuel state fnName argTms = Inr (state', retVal) \<longrightarrow>
             IS_Globals state' = IS_Globals state \<and>
             IS_Functions state' = IS_Functions state"
proof (induction fuel arbitrary: tm tms lvTm stmt stmts fnName argTms rule: nat.induct)
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
  note IH_term = Suc.IH(1)
  note IH_term_list = Suc.IH(2)
  note IH_lvalue = Suc.IH(3)
  note IH_stmt = Suc.IH(4)
  note IH_stmt_list = Suc.IH(5)
  note IH_call = Suc.IH(6)
  {
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  next
    case 3 show ?case by simp
  next
    case (4 stmt) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and res :: "'w ExecResult"
      assume H: "interp_statement (Suc fuel) state stmt = Inr res"
      show "exec_result_preserves_gf state res"
      proof (cases stmt)
        case (CoreStmt_VarDecl g varName vr ty initTm)
        show ?thesis
        proof (cases g)
          case Ghost
          with H CoreStmt_VarDecl have
            "res = Continue (state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
                                      IS_Refs := fmdrop varName (IS_Refs state) \<rparr>)"
            by simp
          then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
        next
          case NotGhost
          show ?thesis
          proof (cases vr)
            case Var
            \<comment> \<open>Two sub-cases for initTm: function call (which may return a new
                state via interp_function_call) vs. plain term (state unchanged). \<close>
            show ?thesis
            proof (cases "\<exists>fn ts ams. initTm = CoreTm_FunctionCall fn ts ams")
              case True
              then obtain fn ts ams where init_eq: "initTm = CoreTm_FunctionCall fn ts ams" by blast
              from NotGhost Var H CoreStmt_VarDecl init_eq
              obtain newState initVal where
                call: "interp_function_call fuel state fn ams = Inr (newState, initVal)"
                by (auto split: sum.splits prod.splits)
              from IH_call call
              have call_gf: "IS_Globals newState = IS_Globals state \<and>
                             IS_Functions newState = IS_Functions state"
                by blast
              let ?alloc = "alloc_store newState initVal"
              from NotGhost Var H CoreStmt_VarDecl init_eq call
              have res_eq: "res = Continue ((fst ?alloc) \<lparr> IS_Locals :=
                               fmupd varName (snd ?alloc) (IS_Locals (fst ?alloc)) \<rparr>)"
                by (simp add: case_prod_beta)
              have alloc_gf: "IS_Globals (fst ?alloc) = IS_Globals newState"
                             "IS_Functions (fst ?alloc) = IS_Functions newState"
                by (simp_all add: alloc_store_preserves_globals_funs)
              from res_eq alloc_gf call_gf show ?thesis
                by (simp add: exec_result_preserves_gf_Continue)
            next
              case False
              with NotGhost Var H CoreStmt_VarDecl obtain initVal where
                iv: "interp_term fuel state initTm = Inr initVal"
                by (cases initTm; auto split: sum.splits)
              let ?alloc = "alloc_store state initVal"
              from NotGhost Var H CoreStmt_VarDecl False iv
              have res_eq: "res = Continue ((fst ?alloc) \<lparr> IS_Locals :=
                               fmupd varName (snd ?alloc) (IS_Locals (fst ?alloc)) \<rparr>)"
                by (cases initTm; simp_all add: case_prod_beta)
              have "IS_Globals (fst ?alloc) = IS_Globals state"
                   "IS_Functions (fst ?alloc) = IS_Functions state"
                by (simp_all add: alloc_store_preserves_globals_funs)
              with res_eq show ?thesis
                by (simp add: exec_result_preserves_gf_Continue)
            qed
          next
            case Ref
            \<comment> \<open>Two branches: const-base (copy) or writable-base (alias). \<close>
            from NotGhost Ref H CoreStmt_VarDecl obtain baseName where
              base: "lvalue_base_name initTm = Some baseName"
              by (cases "lvalue_base_name initTm") simp_all
            show ?thesis
            proof (cases "baseName |\<in>| IS_ConstNames state")
              case True
              with NotGhost Ref H CoreStmt_VarDecl base
              obtain val where
                iv: "interp_term fuel state initTm = Inr val"
                by (auto split: sum.splits)
              let ?alloc = "alloc_store state val"
              from NotGhost Ref H CoreStmt_VarDecl base True iv
              have res_eq: "res = Continue
                 ((fst ?alloc) \<lparr> IS_Locals :=
                                  fmupd varName (snd ?alloc) (IS_Locals (fst ?alloc)),
                                 IS_ConstNames :=
                                  finsert varName (IS_ConstNames (fst ?alloc)) \<rparr>)"
                by (simp add: case_prod_beta)
              have "IS_Globals (fst ?alloc) = IS_Globals state"
                   "IS_Functions (fst ?alloc) = IS_Functions state"
                by (simp_all add: alloc_store_preserves_globals_funs)
              with res_eq show ?thesis
                by (simp add: exec_result_preserves_gf_Continue)
            next
              case False
              with NotGhost Ref H CoreStmt_VarDecl base
              obtain addrPath where
                lv: "interp_writable_lvalue fuel state initTm = Inr addrPath"
                by (auto split: sum.splits)
              from NotGhost Ref H CoreStmt_VarDecl base False lv
              have res_eq: "res = Continue
                 (state \<lparr> IS_Refs := fmupd varName addrPath (IS_Refs state) \<rparr>)"
                by simp
              then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
            qed
          qed
        qed
      next
        case (CoreStmt_Assign g lhsLv rhsTm)
        show ?thesis
        proof (cases g)
          case Ghost
          with H CoreStmt_Assign have "res = Continue state" by simp
          then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
        next
          case NotGhost
          with H CoreStmt_Assign obtain addr path where
            lv: "interp_writable_lvalue fuel state lhsLv = Inr (addr, path)"
            by (auto split: sum.splits)
          \<comment> \<open>Two cases for rhsTm: function call vs. plain term. \<close>
          show ?thesis
          proof (cases "\<exists>fn ts ams. rhsTm = CoreTm_FunctionCall fn ts ams")
            case True
            then obtain fn ts ams where rhs_eq: "rhsTm = CoreTm_FunctionCall fn ts ams" by blast
            from NotGhost H CoreStmt_Assign lv rhs_eq
            obtain newState rhsVal where
              call: "interp_function_call fuel state fn ams = Inr (newState, rhsVal)"
              by (auto split: sum.splits prod.splits)
            from IH_call call
            have call_gf: "IS_Globals newState = IS_Globals state \<and>
                           IS_Functions newState = IS_Functions state"
              by blast
            from NotGhost H CoreStmt_Assign lv rhs_eq call
            obtain newVal where
              upd: "update_value_at_path (IS_Store newState ! addr) path rhsVal = Inr newVal"
              by (auto split: sum.splits)
            from NotGhost H CoreStmt_Assign lv rhs_eq call upd
            have res_eq: "res = Continue
                (newState \<lparr> IS_Store := (IS_Store newState)[addr := newVal] \<rparr>)"
              by (simp add: Let_def)
            from call_gf res_eq show ?thesis
              by (simp add: exec_result_preserves_gf_Continue)
          next
            case False
            with NotGhost H CoreStmt_Assign lv
            obtain rhsVal where
              rv: "interp_term fuel state rhsTm = Inr rhsVal"
              by (cases rhsTm; auto split: sum.splits)
            from NotGhost H CoreStmt_Assign lv False rv
            obtain newVal where
              upd: "update_value_at_path (IS_Store state ! addr) path rhsVal = Inr newVal"
              by (cases rhsTm; auto split: sum.splits)
            from NotGhost H CoreStmt_Assign lv False rv upd
            have res_eq: "res = Continue
                (state \<lparr> IS_Store := (IS_Store state)[addr := newVal] \<rparr>)"
              by (cases rhsTm; simp_all add: Let_def)
            then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
          qed
        qed
      next
        case (CoreStmt_Swap g lhsTm rhsTm)
        show ?thesis
        proof (cases g)
          case Ghost
          with H CoreStmt_Swap have "res = Continue state" by simp
          then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
        next
          case NotGhost
          with H CoreStmt_Swap obtain lhsLv where
            lhs: "interp_writable_lvalue fuel state lhsTm = Inr lhsLv"
            by (auto split: sum.splits)
          with NotGhost H CoreStmt_Swap obtain rhsLv where
            rhs: "interp_writable_lvalue fuel state rhsTm = Inr rhsLv"
            by (auto split: sum.splits)
          with NotGhost H CoreStmt_Swap lhs obtain newState where
            sw: "perform_swap state lhsLv rhsLv = Inr newState"
            and res_eq: "res = Continue newState"
            by (auto split: sum.splits)
          from perform_swap_preserves_globals_funs[OF sw] res_eq
          show ?thesis by (simp add: exec_result_preserves_gf_Continue)
        qed
      next
        case (CoreStmt_Return tm)
        with H obtain val where
          "interp_term fuel state tm = Inr val"
          and res_eq: "res = Return state val"
          by (auto split: sum.splits)
        then show ?thesis by (simp add: exec_result_preserves_gf_Return)
      next
        case (CoreStmt_While g condTm invars decr bodyStmts)
        show ?thesis
        proof (cases g)
          case Ghost
          with H CoreStmt_While have "res = Continue state" by simp
          then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
        next
          case NotGhost
          from NotGhost H CoreStmt_While obtain condVal where
            cv: "interp_term fuel state condTm = Inr condVal"
            by (auto split: sum.splits)
          show ?thesis
          proof (cases condVal)
            case (CV_Bool b)
            show ?thesis
            proof (cases b)
              case False
              with NotGhost CoreStmt_While H cv CV_Bool
              have "res = Continue state" by simp
              then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
            next
              case True
              with NotGhost CoreStmt_While H cv CV_Bool
              obtain bodyRes where
                body: "interp_statement_list fuel state bodyStmts = Inr bodyRes"
                by (auto split: sum.splits)
              from IH_stmt_list body
              have body_gf: "exec_result_preserves_gf state bodyRes" by blast
              show ?thesis
              proof (cases bodyRes)
                case (Continue state1)
                from body_gf Continue
                have gf1: "IS_Globals state1 = IS_Globals state \<and>
                           IS_Functions state1 = IS_Functions state"
                  by (simp add: exec_result_preserves_gf_Continue)
                let ?rs = "restore_scope state state1"
                have rs_gf:
                  "IS_Globals ?rs = IS_Globals state"
                  "IS_Functions ?rs = IS_Functions state"
                  using gf1 by (simp_all add: restore_scope_preserves_globals_funs)
                from NotGhost CoreStmt_While H cv CV_Bool True body Continue
                have rec_eq: "interp_statement fuel ?rs
                                 (CoreStmt_While NotGhost condTm invars decr bodyStmts) = Inr res"
                  by simp
                from IH_stmt rec_eq
                have rec_pres: "exec_result_preserves_gf ?rs res" by blast
                from rec_pres rs_gf show ?thesis
                  by (cases res) (simp_all add: exec_result_preserves_gf_def)
              next
                case (Return state1 v)
                from body_gf Return
                have gf1: "IS_Globals state1 = IS_Globals state \<and>
                           IS_Functions state1 = IS_Functions state"
                  by (simp add: exec_result_preserves_gf_Return)
                from NotGhost CoreStmt_While H cv CV_Bool True body Return
                have res_eq: "res = Return (restore_scope state state1) v"
                  by simp
                from res_eq gf1 show ?thesis
                  by (simp add: exec_result_preserves_gf_Return
                                restore_scope_preserves_globals_funs)
              qed
            qed
          next
            \<comment> \<open>Non-bool cond value: TypeError, contradicts H. \<close>
            case CV_FiniteInt with NotGhost CoreStmt_While H cv show ?thesis by simp
          next
            case CV_Variant with NotGhost CoreStmt_While H cv show ?thesis by simp
          next
            case CV_Record with NotGhost CoreStmt_While H cv show ?thesis by simp
          next
            case CV_Array with NotGhost CoreStmt_While H cv show ?thesis by simp
          qed
        qed
      next
        case (CoreStmt_Match g scrutTm arms)
        show ?thesis
        proof (cases g)
          case Ghost
          with H CoreStmt_Match have "res = Continue state" by simp
          then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
        next
          case NotGhost
          from NotGhost H CoreStmt_Match obtain scrutVal where
            sv: "interp_term fuel state scrutTm = Inr scrutVal"
            by (auto split: sum.splits)
          from NotGhost H CoreStmt_Match sv obtain armStmts where
            arm: "find_matching_arm scrutVal arms = Inr armStmts"
            by (auto split: sum.splits)
          from NotGhost H CoreStmt_Match sv arm obtain bodyRes where
            body: "interp_statement_list fuel state armStmts = Inr bodyRes"
            by (auto split: sum.splits)
          from IH_stmt_list body
          have body_gf: "exec_result_preserves_gf state bodyRes" by blast
          show ?thesis
          proof (cases bodyRes)
            case (Continue state1)
            from body_gf Continue
            have gf1: "IS_Globals state1 = IS_Globals state \<and>
                       IS_Functions state1 = IS_Functions state"
              by (simp add: exec_result_preserves_gf_Continue)
            from NotGhost CoreStmt_Match H sv arm body Continue
            have res_eq: "res = Continue (restore_scope state state1)" by simp
            from res_eq gf1 show ?thesis
              by (simp add: exec_result_preserves_gf_Continue
                            restore_scope_preserves_globals_funs)
          next
            case (Return state1 v)
            from body_gf Return
            have gf1: "IS_Globals state1 = IS_Globals state \<and>
                       IS_Functions state1 = IS_Functions state"
              by (simp add: exec_result_preserves_gf_Return)
            from NotGhost CoreStmt_Match H sv arm body Return
            have res_eq: "res = Return (restore_scope state state1) v" by simp
            from res_eq gf1 show ?thesis
              by (simp add: exec_result_preserves_gf_Return
                            restore_scope_preserves_globals_funs)
          qed
        qed
      next
        case (CoreStmt_Assert _ _) with H
        have "res = Continue state" by simp
        then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
      next
        case (CoreStmt_Assume _) with H
        have "res = Continue state" by simp
        then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
      next
        case (CoreStmt_ShowHide _ _) with H
        have "res = Continue state" by simp
        then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
      next
        case (CoreStmt_Fix _ _) with H show ?thesis by simp
      next
        case (CoreStmt_Obtain _ _ _) with H show ?thesis by simp
      next
        case (CoreStmt_Use _) with H show ?thesis by simp
      qed
    qed
  next
    case (5 stmts) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and res :: "'w ExecResult"
      assume H: "interp_statement_list (Suc fuel) state stmts = Inr res"
      show "exec_result_preserves_gf state res"
      proof (cases stmts)
        case Nil
        with H have "res = Continue state" by simp
        then show ?thesis by (simp add: exec_result_preserves_gf_Continue)
      next
        case (Cons stmt1 rest)
        with H obtain res1 where
          r1: "interp_statement fuel state stmt1 = Inr res1"
          by (auto split: sum.splits)
        show ?thesis
        proof (cases res1)
          case (Continue state1)
          from IH_stmt r1 Continue
          have gf1: "IS_Globals state1 = IS_Globals state \<and>
                     IS_Functions state1 = IS_Functions state"
            by (force simp: exec_result_preserves_gf_Continue)
          from Cons H r1 Continue
          have rec: "interp_statement_list fuel state1 rest = Inr res" by simp
          from IH_stmt_list rec have gf2: "exec_result_preserves_gf state1 res" by blast
          from gf1 gf2 show ?thesis
            by (cases res) (simp_all add: exec_result_preserves_gf_def)
        next
          case (Return state1 v)
          from IH_stmt r1 Return
          have gf1: "IS_Globals state1 = IS_Globals state \<and>
                     IS_Functions state1 = IS_Functions state"
            by (force simp: exec_result_preserves_gf_Return)
          from Cons H r1 Return have "res = Return state1 v" by simp
          with gf1 show ?thesis by (simp add: exec_result_preserves_gf_Return)
        qed
      qed
    qed
  next
    case (6 fnName argTms) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and state' :: "'w InterpState" and retVal
      assume H: "interp_function_call (Suc fuel) state fnName argTms = Inr (state', retVal)"
      \<comment> \<open>Unfold the function-call body enough to name each intermediate state. \<close>
      obtain f where f_lookup: "fmlookup (IS_Functions state) fnName = Some f"
        using H by (cases "fmlookup (IS_Functions state) fnName") simp_all
      from H f_lookup have len_eq: "length argTms = length (IF_Args f)"
        by (cases "length argTms = length (IF_Args f)") simp_all
      let ?refResults = "map (interp_writable_lvalue fuel state) argTms"
      let ?valResults = "map (interp_term fuel state) argTms"
      let ?argTuples = "zip (IF_Args f) (zip ?refResults ?valResults)"
      let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                     IS_ConstNames := {||} \<rparr>"
      have cleared_gf:
        "IS_Globals ?clearedState = IS_Globals state"
        "IS_Functions ?clearedState = IS_Functions state"
        by simp_all
      obtain preCallState where
        fold_eq: "fold process_one_arg ?argTuples (Inr ?clearedState) = Inr preCallState"
        using H f_lookup len_eq
        by (cases "fold process_one_arg ?argTuples (Inr ?clearedState)") (simp_all add: Let_def)
      from fold_process_one_arg_preserves_globals_funs[OF fold_eq] cleared_gf
      have pre_gf: "IS_Globals preCallState = IS_Globals state \<and>
                    IS_Functions preCallState = IS_Functions state"
        by simp
      show "IS_Globals state' = IS_Globals state \<and>
            IS_Functions state' = IS_Functions state"
      proof (cases "IF_Body f")
        case (Inl bodyStmts)
        \<comment> \<open>Babylon body. \<close>
        from H f_lookup len_eq fold_eq Inl
        obtain bodyRes where bodyEval:
          "interp_statement_list fuel preCallState bodyStmts = Inr bodyRes"
          by (cases "interp_statement_list fuel preCallState bodyStmts")
             (simp_all add: Let_def)
        show ?thesis
        proof (cases bodyRes)
          case (Continue _)
          with H f_lookup len_eq fold_eq Inl bodyEval show ?thesis
            by (simp add: Let_def)
        next
          case (Return postCallState bodyRetVal)
          from IH_stmt_list bodyEval Return
          have body_gf: "IS_Globals postCallState = IS_Globals preCallState \<and>
                         IS_Functions postCallState = IS_Functions preCallState"
            by (force simp: exec_result_preserves_gf_Return)
          from H f_lookup len_eq fold_eq Inl bodyEval Return
          have state'_eq: "state' = restore_scope state postCallState"
            by (simp add: Let_def)
          from state'_eq body_gf pre_gf
          show ?thesis
            by (simp add: restore_scope_preserves_globals_funs)
        qed
      next
        case (Inr externFun)
        \<comment> \<open>Extern function. \<close>
        let ?vals = "rights ?valResults"
        let ?refs = "rights (map (\<lambda>((_, vr), refResult).
                                      if vr = Ref then refResult else Inl TypeError)
                                 (zip (IF_Args f) ?refResults))"
        obtain newWorld refUpdates externRetVal where
          ext_eq: "externFun (IS_World state) ?vals = (newWorld, refUpdates, externRetVal)"
          by (cases "externFun (IS_World state) ?vals") auto
        let ?stateW = "state \<lparr> IS_World := newWorld \<rparr>"
        have stateW_gf:
          "IS_Globals ?stateW = IS_Globals state"
          "IS_Functions ?stateW = IS_Functions state"
          by simp_all
        from H f_lookup len_eq fold_eq Inr ext_eq
        obtain finalState where final_eq:
          "apply_ref_updates ?stateW ?refs refUpdates = Inr finalState"
          and state'_eq: "state' = finalState" and "retVal = externRetVal"
          by (cases "apply_ref_updates ?stateW ?refs refUpdates") (simp_all add: Let_def)
        from apply_ref_updates_preserves_globals_funs[OF final_eq] stateW_gf state'_eq
        show ?thesis by simp
      qed
    qed
  }
qed


(* Convenient corollaries that match how callers use them. *)

lemma interp_statement_list_preserves_globals:
  assumes "interp_statement_list fuel state stmts = Inr (Continue state')"
  shows "IS_Globals state' = IS_Globals state"
proof -
  from interp_preserves_globals_funs(5)[of fuel stmts] assms
  have "exec_result_preserves_gf state (Continue state')" by blast
  thus ?thesis by (simp add: exec_result_preserves_gf_Continue)
qed

lemma interp_statement_list_preserves_functions:
  assumes "interp_statement_list fuel state stmts = Inr (Continue state')"
  shows "IS_Functions state' = IS_Functions state"
proof -
  from interp_preserves_globals_funs(5)[of fuel stmts] assms
  have "exec_result_preserves_gf state (Continue state')" by blast
  thus ?thesis by (simp add: exec_result_preserves_gf_Continue)
qed

lemma interp_statement_list_return_preserves_globals:
  assumes "interp_statement_list fuel state stmts = Inr (Return state' retVal)"
  shows "IS_Globals state' = IS_Globals state"
proof -
  from interp_preserves_globals_funs(5)[of fuel stmts] assms
  have "exec_result_preserves_gf state (Return state' retVal)" by blast
  thus ?thesis by (simp add: exec_result_preserves_gf_Return)
qed

lemma interp_statement_list_return_preserves_functions:
  assumes "interp_statement_list fuel state stmts = Inr (Return state' retVal)"
  shows "IS_Functions state' = IS_Functions state"
proof -
  from interp_preserves_globals_funs(5)[of fuel stmts] assms
  have "exec_result_preserves_gf state (Return state' retVal)" by blast
  thus ?thesis by (simp add: exec_result_preserves_gf_Return)
qed

lemma interp_function_call_preserves_globals:
  assumes "interp_function_call fuel state fnName argTms = Inr (state', retVal)"
  shows "IS_Globals state' = IS_Globals state"
  using interp_preserves_globals_funs(6)[of fuel fnName argTms] assms by blast

lemma interp_function_call_preserves_functions:
  assumes "interp_function_call fuel state fnName argTms = Inr (state', retVal)"
  shows "IS_Functions state' = IS_Functions state"
  using interp_preserves_globals_funs(6)[of fuel fnName argTms] assms by blast

end

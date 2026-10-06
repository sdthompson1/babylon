theory CoreInterpPreservation
  imports CoreInterp
begin

(* The interpreter never changes IS_Globals, IS_Functions or IS_DefaultCtors,
   and a statement or a function call hands back the IS_TyArgs it was started
   with. *)


(* ========================================================================== *)
(* The helper functions *)
(* ========================================================================== *)

(* IS_Globals / IS_Functions / IS_TyArgs / IS_DefaultCtors preservation for the
   leaf state transformers used inside the interpreter. *)

lemma alloc_store_preserves_globals_funs:
  "IS_Globals (fst (alloc_store state v)) = IS_Globals state"
  "IS_Functions (fst (alloc_store state v)) = IS_Functions state"
  "IS_TyArgs (fst (alloc_store state v)) = IS_TyArgs state"
  "IS_DefaultCtors (fst (alloc_store state v)) = IS_DefaultCtors state"
  by (simp_all add: Let_def)

lemma process_one_arg_preserves_globals_funs:
  assumes "process_one_arg arg (Inr state) = Inr state'"
  shows "IS_Globals state' = IS_Globals state \<and>
         IS_Functions state' = IS_Functions state \<and>
         IS_TyArgs state' = IS_TyArgs state \<and>
         IS_DefaultCtors state' = IS_DefaultCtors state"
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
                                  IS_Refs := fmdrop name (IS_Refs (fst ?alloc)),
                                  IS_ConstLocals := finsert name (IS_ConstLocals (fst ?alloc)) \<rparr>"
        by (simp add: case_prod_beta)
      have "IS_Globals (fst ?alloc) = IS_Globals state"
           "IS_Functions (fst ?alloc) = IS_Functions state"
           "IS_DefaultCtors (fst ?alloc) = IS_DefaultCtors state"
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
        have "state' = state \<lparr> IS_Locals := fmdrop name (IS_Locals state),
                                IS_Refs := fmupd name (addr, path) (IS_Refs state),
                                IS_ConstLocals := fminus (IS_ConstLocals state) {|name|} \<rparr>"
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
         IS_Functions state' = IS_Functions state \<and>
         IS_TyArgs state' = IS_TyArgs state \<and>
         IS_DefaultCtors state' = IS_DefaultCtors state"
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
                IS_Functions state1 = IS_Functions state \<and>
                IS_TyArgs state1 = IS_TyArgs state \<and>
                IS_DefaultCtors state1 = IS_DefaultCtors state" by simp
    from Inr Cons.prems have "fold process_one_arg args (Inr state1) = Inr state'"
      by simp
    from Cons.IH[OF this] step show ?thesis by simp
  qed
qed

lemma apply_ref_updates_preserves_globals_funs:
  assumes "apply_ref_updates state lvs vs = Inr state'"
  shows "IS_Globals state' = IS_Globals state \<and>
         IS_Functions state' = IS_Functions state \<and>
         IS_TyArgs state' = IS_TyArgs state \<and>
         IS_DefaultCtors state' = IS_DefaultCtors state"
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
         IS_Functions state' = IS_Functions state \<and>
         IS_TyArgs state' = IS_TyArgs state \<and>
         IS_DefaultCtors state' = IS_DefaultCtors state"
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
  "IS_TyArgs (restore_scope old_state new_state) = IS_TyArgs old_state"
  by simp_all


(* ========================================================================== *)
(* The relation between two states *)
(* ========================================================================== *)

(* state' has the same globals, functions, type arguments and default
   constructors as state. *)
definition static_parts_eq :: "'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "static_parts_eq state state' \<equiv>
    IS_Globals state' = IS_Globals state \<and>
    IS_Functions state' = IS_Functions state \<and>
    IS_TyArgs state' = IS_TyArgs state \<and>
    IS_DefaultCtors state' = IS_DefaultCtors state"

lemma static_parts_eqD:
  assumes "static_parts_eq state state'"
  shows "IS_Globals state' = IS_Globals state"
    and "IS_Functions state' = IS_Functions state"
    and "IS_TyArgs state' = IS_TyArgs state"
    and "IS_DefaultCtors state' = IS_DefaultCtors state"
  using assms by (simp_all add: static_parts_eq_def)

lemma static_parts_eq_refl:
  "static_parts_eq state state"
  by (simp add: static_parts_eq_def)

lemma static_parts_eq_trans:
  assumes "static_parts_eq s1 s2" and "static_parts_eq s2 s3"
  shows "static_parts_eq s1 s3"
  using assms by (simp add: static_parts_eq_def)

(* Leaving a scope puts the type arguments of the outer state back, and keeps
   everything else. *)
lemma static_parts_eq_restore_scope:
  assumes "static_parts_eq state state'"
  shows "static_parts_eq state (restore_scope state state')"
  using assms by (simp add: static_parts_eq_def)

lemma static_parts_eq_bind_mutable_local:
  "static_parts_eq state (bind_mutable_local varName val state)"
  by (simp add: static_parts_eq_def Let_def)


(* ========================================================================== *)
(* The main preservation lemma *)
(* ========================================================================== *)

(* The state in which a statement finished. *)
fun result_state :: "'w ExecResult \<Rightarrow> 'w InterpState" where
  "result_state (Continue state) = state"
| "result_state (Return state _) = state"

(* All three statements are proved simultaneously by induction on the fuel.
   The depth is fixed: the statement, statement-list and function-call
   functions only ever call each other at the same depth. (Terms do not return
   a state, so nothing needs to be proved about them.) *)
lemma interp_static:
  fixes dummy :: "'w InterpState"
  shows "\<forall>(state :: 'w InterpState) res.
           interp_statement d fuel state stmt = Inr res \<longrightarrow>
             static_parts_eq state (result_state res)"
    and "\<forall>(state :: 'w InterpState) res.
           interp_statement_list d fuel state stmts = Inr res \<longrightarrow>
             static_parts_eq state (result_state res)"
    and "\<forall>(state :: 'w InterpState) state' retVal.
           interp_function_call d fuel state fnName argTys argTms = Inr (state', retVal) \<longrightarrow>
             static_parts_eq state state'"
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
  note IH_stmt = Suc.IH(1)
  note IH_stmt_list = Suc.IH(2)
  note IH_call = Suc.IH(3)
  {
    case (1 stmt) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and res :: "'w ExecResult"
      assume H: "interp_statement d (Suc fuel) state stmt = Inr res"
      show "static_parts_eq state (result_state res)"
      proof (cases stmt)
        case (CoreStmt_VarDecl g varName vr ty initTm)
        show ?thesis
        proof (cases vr)
          case Var
          from Var H CoreStmt_VarDecl obtain initVal where
            iv: "interp_term d fuel state initTm = Inr initVal"
            by (auto split: sum.splits)
          from Var H[symmetric] CoreStmt_VarDecl iv show ?thesis
            by (simp add: static_parts_eq_def Let_def)
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
              by (simp add: static_parts_eq_def Let_def)
          next
            case False
            with Ref H CoreStmt_VarDecl base obtain addrPath where
              lv: "interp_writable_lvalue d fuel state initTm = Inr addrPath"
              by (auto split: sum.splits)
            from Ref H[symmetric] CoreStmt_VarDecl base False lv show ?thesis
              by (simp add: static_parts_eq_def)
          qed
        qed
      next
        case (CoreStmt_VarDeclCall g varName varTy castOpt fnName argTys argTms)
        \<comment> \<open>Run the call (giving newState), apply the cast, then alloc and bind. \<close>
        from H CoreStmt_VarDeclCall obtain newState retVal where
          call: "interp_function_call d fuel state fnName argTys argTms = Inr (newState, retVal)"
          by (auto split: sum.splits prod.splits)
        from IH_call call have call_eq: "static_parts_eq state newState" by blast
        from H CoreStmt_VarDeclCall call obtain initVal where
          cast: "apply_cast_opt castOpt retVal = Inr initVal"
          by (auto split: sum.splits)
        from H[symmetric] CoreStmt_VarDeclCall call cast
        have "static_parts_eq newState (result_state res)"
          by (simp add: static_parts_eq_def Let_def)
        with call_eq show ?thesis by (rule static_parts_eq_trans)
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
          show ?thesis
            by (simp only: res_eq result_state.simps static_parts_eq_bind_mutable_local)
        qed
      next
        case (CoreStmt_Use _) with H show ?thesis by simp
      next
        case (CoreStmt_Assign g lhsLv rhsTm)
        from H CoreStmt_Assign obtain addr path where
          lv: "interp_writable_lvalue d fuel state lhsLv = Inr (addr, path)"
          by (auto split: sum.splits)
        from H CoreStmt_Assign lv obtain rhsVal where
          rv: "interp_term d fuel state rhsTm = Inr rhsVal"
          by (auto split: sum.splits)
        from H CoreStmt_Assign lv rv obtain newVal where
          upd: "update_value_at_path (IS_Store state ! addr) path rhsVal = Inr newVal"
          by (auto simp: Let_def split: sum.splits)
        from H[symmetric] CoreStmt_Assign lv rv upd show ?thesis
          by (simp add: static_parts_eq_def Let_def)
      next
        case (CoreStmt_AssignCall g lhsLv castOpt fnName argTys argTms)
        \<comment> \<open>Resolve lhs, run the call (newState), apply cast, store. \<close>
        from H CoreStmt_AssignCall obtain addr path where
          lv: "interp_writable_lvalue d fuel state lhsLv = Inr (addr, path)"
          by (auto split: sum.splits)
        from H CoreStmt_AssignCall lv obtain newState retVal where
          call: "interp_function_call d fuel state fnName argTys argTms = Inr (newState, retVal)"
          by (auto split: sum.splits prod.splits)
        from IH_call call have call_eq: "static_parts_eq state newState" by blast
        from H CoreStmt_AssignCall lv call obtain rhsVal where
          cast: "apply_cast_opt castOpt retVal = Inr rhsVal"
          by (auto split: sum.splits)
        from H CoreStmt_AssignCall lv call cast obtain newVal where
          upd: "update_value_at_path (IS_Store newState ! addr) path rhsVal = Inr newVal"
          by (auto simp: Let_def split: sum.splits)
        from H[symmetric] CoreStmt_AssignCall lv call cast upd
        have "static_parts_eq newState (result_state res)"
          by (simp add: static_parts_eq_def Let_def)
        with call_eq show ?thesis by (rule static_parts_eq_trans)
      next
        case (CoreStmt_Swap g lhsTm rhsTm)
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
        from perform_swap_preserves_globals_funs[OF sw] res_eq show ?thesis
          by (simp add: static_parts_eq_def)
      next
        case (CoreStmt_Return tm)
        with H obtain val where
          "interp_term d fuel state tm = Inr val"
          and res_eq: "res = Return state val"
          by (auto split: sum.splits)
        then show ?thesis by (simp add: static_parts_eq_refl)
      next
        case (CoreStmt_Assert condOpt proofBody)
        show ?thesis
        proof (cases condOpt)
          case None
          with H CoreStmt_Assert show ?thesis by simp
        next
          case (Some condTm)
          from H CoreStmt_Assert Some obtain condVal where
            cv: "interp_term d fuel state condTm = Inr condVal"
            by (auto split: sum.splits)
          have "res = Continue state"
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
          then show ?thesis by (simp add: static_parts_eq_refl)
        qed
      next
        case (CoreStmt_Assume _) with H
        have "res = Continue state" by simp
        then show ?thesis by (simp add: static_parts_eq_refl)
      next
        case (CoreStmt_While g condTm invars decr bodyStmts)
        \<comment> \<open>The run succeeded, so the invariants were evaluated and all held. \<close>
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
            have "res = Continue state" by simp
            then show ?thesis by (simp add: static_parts_eq_refl)
          next
            case True
            with CoreStmt_While H cv CV_Bool
            obtain bodyRes where
              body: "interp_statement_list d fuel state bodyStmts = Inr bodyRes"
              by (auto split: sum.splits)
            from IH_stmt_list body
            have body_eq: "static_parts_eq state (result_state bodyRes)" by blast
            show ?thesis
            proof (cases bodyRes)
              case (Continue state1)
              let ?rs = "restore_scope state state1"
              from body_eq Continue have eq1: "static_parts_eq state state1" by simp
              have eq_rs: "static_parts_eq state ?rs"
                by (rule static_parts_eq_restore_scope[OF eq1])
              from CoreStmt_While H cv CV_Bool True body Continue
              have rec_eq: "interp_statement d fuel ?rs
                               (CoreStmt_While g condTm invars decr bodyStmts) = Inr res"
                by simp
              from IH_stmt rec_eq
              have "static_parts_eq ?rs (result_state res)" by blast
              with eq_rs show ?thesis by (rule static_parts_eq_trans)
            next
              case (Return state1 v)
              from body_eq Return have eq1: "static_parts_eq state state1" by simp
              from CoreStmt_While H cv CV_Bool True body Return
              have res_eq: "res = Return (restore_scope state state1) v"
                by simp
              show ?thesis
                by (simp only: res_eq result_state.simps static_parts_eq_restore_scope[OF eq1])
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
        case (CoreStmt_Match g scrutTm arms)
        from H CoreStmt_Match obtain scrutVal where
          sv: "interp_term d fuel state scrutTm = Inr scrutVal"
          by (auto split: sum.splits)
        from H CoreStmt_Match sv obtain armStmts where
          arm: "find_matching_arm scrutVal arms = Inr armStmts"
          by (auto split: sum.splits)
        from H CoreStmt_Match sv arm obtain bodyRes where
          body: "interp_statement_list d fuel state armStmts = Inr bodyRes"
          by (auto split: sum.splits)
        from IH_stmt_list body
        have body_eq: "static_parts_eq state (result_state bodyRes)" by blast
        show ?thesis
        proof (cases bodyRes)
          case (Continue state1)
          from body_eq Continue have eq1: "static_parts_eq state state1" by simp
          from CoreStmt_Match H sv arm body Continue
          have res_eq: "res = Continue (restore_scope state state1)" by simp
          show ?thesis
            by (simp only: res_eq result_state.simps static_parts_eq_restore_scope[OF eq1])
        next
          case (Return state1 v)
          from body_eq Return have eq1: "static_parts_eq state state1" by simp
          from CoreStmt_Match H sv arm body Return
          have res_eq: "res = Return (restore_scope state state1) v" by simp
          show ?thesis
            by (simp only: res_eq result_state.simps static_parts_eq_restore_scope[OF eq1])
        qed
      next
        case (CoreStmt_ShowHide _ _) with H
        have "res = Continue state" by simp
        then show ?thesis by (simp add: static_parts_eq_refl)
      next
        case (CoreStmt_Block body)
        from H CoreStmt_Block obtain bodyRes where
          body: "interp_statement_list d fuel state body = Inr bodyRes"
          by (auto split: sum.splits)
        from IH_stmt_list body
        have body_eq: "static_parts_eq state (result_state bodyRes)" by blast
        show ?thesis
        proof (cases bodyRes)
          case (Continue state1)
          from body_eq Continue have eq1: "static_parts_eq state state1" by simp
          from CoreStmt_Block H body Continue
          have res_eq: "res = Continue (restore_scope state state1)" by simp
          show ?thesis
            by (simp only: res_eq result_state.simps static_parts_eq_restore_scope[OF eq1])
        next
          case (Return state1 v)
          from body_eq Return have eq1: "static_parts_eq state state1" by simp
          from CoreStmt_Block H body Return
          have res_eq: "res = Return (restore_scope state state1) v" by simp
          show ?thesis
            by (simp only: res_eq result_state.simps static_parts_eq_restore_scope[OF eq1])
        qed
      qed
    qed
  next
    case (2 stmts) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and res :: "'w ExecResult"
      assume H: "interp_statement_list d (Suc fuel) state stmts = Inr res"
      show "static_parts_eq state (result_state res)"
      proof (cases stmts)
        case Nil
        with H have "res = Continue state" by simp
        then show ?thesis by (simp add: static_parts_eq_refl)
      next
        case (Cons stmt1 rest)
        with H obtain res1 where
          r1: "interp_statement d fuel state stmt1 = Inr res1"
          by (auto split: sum.splits)
        from IH_stmt r1 have eq1: "static_parts_eq state (result_state res1)" by blast
        show ?thesis
        proof (cases res1)
          case (Continue state1)
          from eq1 Continue have step1: "static_parts_eq state state1" by simp
          from Cons H r1 Continue
          have rec: "interp_statement_list d fuel state1 rest = Inr res" by simp
          from IH_stmt_list rec have step2: "static_parts_eq state1 (result_state res)" by blast
          from step1 step2 show ?thesis by (rule static_parts_eq_trans)
        next
          case (Return state1 v)
          from Cons H r1 Return have "res = Return state1 v" by simp
          with eq1 Return show ?thesis by simp
        qed
      qed
    qed
  next
    case (3 fnName argTys argTms) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and state' :: "'w InterpState" and retVal
      assume H: "interp_function_call d (Suc fuel) state fnName argTys argTms = Inr (state', retVal)"
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
      \<comment> \<open>Binding the arguments installs the callee's type arguments, so IS_TyArgs is
          not preserved at this point; restore_scope puts the caller's back. \<close>
      from fold_process_one_arg_preserves_globals_funs[OF fold_eq]
      have pre_gf: "IS_Globals preCallState = IS_Globals state \<and>
                    IS_Functions preCallState = IS_Functions state \<and>
                    IS_DefaultCtors preCallState = IS_DefaultCtors state"
        by simp

      show "static_parts_eq state state'"
      proof (cases "IF_Body f")
        case (Inl bodyStmts)
        \<comment> \<open>Babylon body. \<close>
        from H f_lookup len_eq tyLen_eq fold_eq Inl
        obtain bodyRes where bodyEval:
          "interp_statement_list d fuel preCallState bodyStmts = Inr bodyRes"
          by (cases "interp_statement_list d fuel preCallState bodyStmts")
             (simp_all add: Let_def)
        show ?thesis
        proof (cases bodyRes)
          case (Continue _)
          with H f_lookup len_eq tyLen_eq fold_eq Inl bodyEval show ?thesis
            by (simp add: Let_def)
        next
          case (Return postCallState bodyRetVal)
          from IH_stmt_list bodyEval
          have "static_parts_eq preCallState (result_state bodyRes)" by blast
          with Return have body_eq: "static_parts_eq preCallState postCallState" by simp
          from H f_lookup len_eq tyLen_eq fold_eq Inl bodyEval Return
          have state'_eq: "state' = restore_scope state postCallState"
            by (simp add: Let_def)
          from state'_eq static_parts_eqD[OF body_eq] pre_gf show ?thesis
            by (simp add: static_parts_eq_def)
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
        from H f_lookup len_eq tyLen_eq fold_eq Inr ext_eq
        obtain finalState where final_eq:
          "apply_ref_updates ?stateW ?refs refUpdates = Inr finalState"
          and state'_eq: "state' = finalState" and "retVal = externRetVal"
          by (cases "apply_ref_updates ?stateW ?refs refUpdates") (simp_all add: Let_def)
        from apply_ref_updates_preserves_globals_funs[OF final_eq] state'_eq show ?thesis
          by (simp add: static_parts_eq_def)
      qed
    qed
  }
qed


(* ========================================================================== *)
(* Corollaries, in the form that callers use *)
(* ========================================================================== *)

theorem interp_statement_static:
  assumes "interp_statement d fuel state stmt = Inr res"
  shows "static_parts_eq state (result_state res)"
  by (rule interp_static(1)[rule_format, OF assms])

theorem interp_statement_list_static:
  assumes "interp_statement_list d fuel state stmts = Inr res"
  shows "static_parts_eq state (result_state res)"
  by (rule interp_static(2)[rule_format, OF assms])

theorem interp_function_call_static:
  assumes "interp_function_call d fuel state fnName argTys argTms = Inr (state', retVal)"
  shows "static_parts_eq state state'"
  by (rule interp_static(3)[rule_format, OF assms])

end

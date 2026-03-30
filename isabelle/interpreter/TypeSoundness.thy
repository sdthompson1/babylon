theory TypeSoundness
  imports StateMatchesEnv "../core/CoreTypecheck"
begin

(*-----------------------------------------------------------------------------*)
(* Definitions for type-soundness of interpreter results *)
(*-----------------------------------------------------------------------------*)

(* Type soundness for terms means that evaluating a well-typed term will either:
    - Succeed with a value of the correct type
    - Fail with RuntimeError
    - Fail with InsufficientFuel
   It will not:
    - Succeed with a value of the wrong type
    - Fail with TypeError *)

fun sound_error_result :: "InterpError \<Rightarrow> bool" where
  "sound_error_result TypeError = False"
| "sound_error_result RuntimeError = True"
| "sound_error_result InsufficientFuel = True"

fun sound_term_result :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> InterpError + CoreValue \<Rightarrow> bool" where
  "sound_term_result env ty (Inl err) = sound_error_result err"
| "sound_term_result env ty (Inr val) = value_has_type env val ty"

fun sound_term_results :: "CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> InterpError + CoreValue list \<Rightarrow> bool" where
  "sound_term_results env types (Inl err) = sound_error_result err"
| "sound_term_results env types (Inr vals) = list_all2 (value_has_type env) vals types"

fun sound_lvalue_result :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> InterpError + (nat \<times> LValuePath list) \<Rightarrow> bool" where
  "sound_lvalue_result state env ty (Inl err) = sound_error_result err"
| "sound_lvalue_result state env ty (Inr (addr, path)) =
    (addr < length (IS_Store state) \<and>
     (case get_value_at_path (IS_Store state ! addr) path of
       Inr v \<Rightarrow> value_has_type env v ty
     | Inl err \<Rightarrow> sound_error_result err))"


(*-----------------------------------------------------------------------------*)
(* Helper lemmas for type soundness *)
(*-----------------------------------------------------------------------------*)

(* Property of int_complement *)
lemma int_complement_fits:
  assumes "int_fits sign bits i"
  shows "int_fits sign bits (int_complement sign bits i)"
  using assms by (cases sign; cases bits; auto)

(* Type soundness for Cast *)
lemma type_soundness_cast:
  assumes state_env: "state_matches_env state env"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Cast target_ty operand) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_Cast target_ty operand))"
proof -
  (* Extract facts from typing *)
  from typing obtain operand_ty where
    operand_typing: "core_term_type env NotGhost operand = Some operand_ty"
    and operand_is_int: "is_integer_type operand_ty"
    and target_is_int: "is_integer_type target_ty"
    and ty_eq: "ty = target_ty"
    by (auto split: option.splits if_splits)

  (* Apply IH to operand *)
  from IH[OF operand_typing]
  have operand_sound: "sound_term_result env operand_ty (interp_term fuel state operand)"
    by simp

  (* Case split on operand result *)
  show ?thesis
  proof (cases "interp_term fuel state operand")
    case (Inr operand_val)
    (* Operand succeeded - extract type information *)
    from operand_sound Inr
    have operand_typed: "value_has_type env operand_val operand_ty"
      by simp

    (* Operand must be a finite integer type *)
    obtain src_sign src_bits i where
      operand_val_def: "operand_val = CV_FiniteInt src_sign src_bits i"
      using value_has_type_FiniteInt
      by (metis is_integer_type.elims(2) is_runtime_type.simps(4) operand_is_int operand_typed
          value_has_type_runtime)

    (* Target type must be a finite integer type (from is_integer_type + runtime type check) *)
    from target_is_int obtain tgt_sign tgt_bits where
      target_ty_def: "target_ty = CoreTy_FiniteInt tgt_sign tgt_bits"
        using Inr is_integer_type.elims(2) operand_typing typing by fastforce

    (* Case split on whether cast succeeds *)
    show ?thesis
    proof (cases "int_fits tgt_sign tgt_bits i")
      case True
      (* Cast succeeds - value has correct type *)
      have "interp_term (Suc fuel) state (CoreTm_Cast target_ty operand) =
            Inr (CV_FiniteInt tgt_sign tgt_bits i)"
        using Inr target_ty_def True operand_val_def by simp        
      with ty_eq target_ty_def True show ?thesis by auto
    next
      case False
      (* Cast fails with RuntimeError *)
      have "interp_term (Suc fuel) state (CoreTm_Cast target_ty operand) = Inl RuntimeError"
        using Inr target_ty_def False operand_val_def by simp
      thus ?thesis by simp
    qed
  next
    case (Inl err)
    then show ?thesis using operand_sound by auto
  qed
qed

(* Helper: generic_int_binop preserves types when operation fits *)
lemma generic_int_binop_sound:
  assumes "value_has_type env v1 (CoreTy_FiniteInt sign bits)"
      and "value_has_type env v2 (CoreTy_FiniteInt sign bits)"
  shows "sound_term_result env (CoreTy_FiniteInt sign bits) (generic_int_binop f v1 v2)"
proof -
  from assms obtain i1 i2 where
    v1_def: "v1 = CV_FiniteInt sign bits i1" and i1_fits: "int_fits sign bits i1" and
    v2_def: "v2 = CV_FiniteInt sign bits i2" and i2_fits: "int_fits sign bits i2"
    using value_has_type_FiniteInt by blast
  show ?thesis
  proof (cases "int_fits sign bits (f i1 i2)")
    case True
    then have "generic_int_binop f v1 v2 = Inr (CV_FiniteInt sign bits (f i1 i2))"
      using v1_def v2_def by simp
    then show ?thesis using True by simp
  next
    case False
    then have "generic_int_binop f v1 v2 = Inl RuntimeError"
      using v1_def v2_def by simp
    then show ?thesis by simp
  qed
qed

(* Helper: generic_int_cmp_binop produces bool *)
lemma generic_int_cmp_binop_sound:
  assumes "value_has_type env v1 (CoreTy_FiniteInt sign bits)"
      and "value_has_type env v2 (CoreTy_FiniteInt sign bits)"
  shows "sound_term_result env CoreTy_Bool (generic_int_cmp_binop f v1 v2)"
proof -
  from assms obtain i1 i2 where
    v1_def: "v1 = CV_FiniteInt sign bits i1" and
    v2_def: "v2 = CV_FiniteInt sign bits i2"
    using value_has_type_FiniteInt by blast
  have "generic_int_cmp_binop f v1 v2 = Inr (CV_Bool (f i1 i2))"
    using v1_def v2_def by simp
  then show ?thesis by simp
qed

(* Helper: generic_bool_binop produces bool *)
lemma generic_bool_binop_sound:
  assumes "value_has_type env v1 CoreTy_Bool"
      and "value_has_type env v2 CoreTy_Bool"
  shows "sound_term_result env CoreTy_Bool (generic_bool_binop f v1 v2)"
proof -
  from assms(1) obtain b1 where v1_def: "v1 = CV_Bool b1"
    using value_has_type_Bool by auto
  from assms(2) obtain b2 where v2_def: "v2 = CV_Bool b2"
    using value_has_type_Bool by auto
  have "generic_bool_binop f v1 v2 = Inr (CV_Bool (f b1 b2))"
    using v1_def v2_def by simp
  then show ?thesis by simp
qed

(* Type soundness for binary operators *)
lemma type_soundness_binop:
  assumes state_env: "state_matches_env state env"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Binop op lhs rhs) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_Binop op lhs rhs))"
proof -
  (* Extract facts from typing *)
  from typing obtain lhsTy rhsTy where
    lhs_typing: "core_term_type env NotGhost lhs = Some lhsTy" and
    rhs_typing: "core_term_type env NotGhost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)

  (* Apply IH to operands *)
  from IH[OF lhs_typing] have lhs_sound: "sound_term_result env lhsTy (interp_term fuel state lhs)" .
  from IH[OF rhs_typing] have rhs_sound: "sound_term_result env rhsTy (interp_term fuel state rhs)" .

  (* Case split on lhs evaluation *)
  show ?thesis
  proof (cases "interp_term fuel state lhs")
    case (Inl err)
    (* LHS failed - propagate error *)
    then have "interp_term (Suc fuel) state (CoreTm_Binop op lhs rhs) = Inl err" by simp
    with lhs_sound Inl show ?thesis by auto
  next
    case (Inr lhsVal)
    from lhs_sound Inr have lhs_typed: "value_has_type env lhsVal lhsTy" by simp

    (* Case split on rhs evaluation *)
    show ?thesis
    proof (cases "interp_term fuel state rhs")
      case (Inl err)
      (* RHS failed - propagate error *)
      then have "interp_term (Suc fuel) state (CoreTm_Binop op lhs rhs) = Inl err"
        using Inr by simp
      with rhs_sound Inl show ?thesis by auto
    next
      case (Inr rhsVal)
      from rhs_sound Inr have rhs_typed: "value_has_type env rhsVal rhsTy" by simp

      (* Both operands succeeded - now case split on operator category *)
      have interp_eq: "interp_term (Suc fuel) state (CoreTm_Binop op lhs rhs) = eval_binop op lhsVal rhsVal"
        using \<open>interp_term fuel state lhs = Inr lhsVal\<close> Inr by simp

      (* From typing and runtime type constraint, lhsTy must be runtime *)
      from value_has_type_runtime[OF lhs_typed] have lhsTy_rt: "is_runtime_type lhsTy" .
      from value_has_type_runtime[OF rhs_typed] have rhsTy_rt: "is_runtime_type rhsTy" .

      (* Simplify typing using the extracted lhsTy and rhsTy *)
      from typing lhs_typing rhs_typing have typing':
        "(if is_arithmetic_binop op
          then if is_numeric_type lhsTy \<and> lhsTy = rhsTy then Some lhsTy else None
          else if is_modulo_binop op
               then if is_integer_type lhsTy \<and> lhsTy = rhsTy then Some lhsTy else None
               else if is_bitwise_binop op \<or> is_shift_binop op
                    then if is_finite_integer_type lhsTy \<and> lhsTy = rhsTy then Some lhsTy else None
                    else if is_ordering_binop op
                         then if is_numeric_type lhsTy \<and> lhsTy = rhsTy then Some CoreTy_Bool else None
                         else if is_eq_neq_binop op
                              then if lhsTy = rhsTy \<and> (NotGhost = Ghost \<or> lhsTy = CoreTy_Bool \<or> is_numeric_type lhsTy)
                                   then Some CoreTy_Bool else None
                              else if is_logical_binop op
                                   then if lhsTy = CoreTy_Bool \<and> rhsTy = CoreTy_Bool then Some CoreTy_Bool else None
                                   else None) = Some ty"
        by simp

      show ?thesis
      proof (cases "is_arithmetic_binop op")
        case True
        (* Arithmetic: +, -, *, / *)
        from typing' True have
          numeric: "is_numeric_type lhsTy" and
          types_eq: "lhsTy = rhsTy" and
          ty_eq: "ty = lhsTy"
          by (auto split: if_splits)
        (* lhsTy is numeric and runtime, so must be FiniteInt *)
        from numeric lhsTy_rt obtain sign bits where
          lhsTy_def: "lhsTy = CoreTy_FiniteInt sign bits"
          by (cases lhsTy) auto
        from types_eq lhsTy_def have rhsTy_def: "rhsTy = CoreTy_FiniteInt sign bits" by simp
        from lhs_typed lhsTy_def have lhs_int: "value_has_type env lhsVal (CoreTy_FiniteInt sign bits)" by simp
        from rhs_typed rhsTy_def have rhs_int: "value_has_type env rhsVal (CoreTy_FiniteInt sign bits)" by simp

        show ?thesis
        proof (cases op)
          case CoreBinop_Add
          have "eval_binop op lhsVal rhsVal = generic_int_binop (\<lambda>x y. x + y) lhsVal rhsVal"
            using CoreBinop_Add by simp
          with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
          show ?thesis by simp
        next
          case CoreBinop_Subtract
          have "eval_binop op lhsVal rhsVal = generic_int_binop (\<lambda>x y. x - y) lhsVal rhsVal"
            using CoreBinop_Subtract by simp
          with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
          show ?thesis by simp
        next
          case CoreBinop_Multiply
          have "eval_binop op lhsVal rhsVal = generic_int_binop (\<lambda>x y. x * y) lhsVal rhsVal"
            using CoreBinop_Multiply by simp
          with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
          show ?thesis by simp
        next
          case CoreBinop_Divide
          show ?thesis
          proof (cases "is_zero rhsVal")
            case True
            then have "eval_binop op lhsVal rhsVal = Inl RuntimeError"
              using CoreBinop_Divide by simp
            with interp_eq show ?thesis by simp
          next
            case False
            then have "eval_binop op lhsVal rhsVal = generic_int_binop tdiv lhsVal rhsVal"
              using CoreBinop_Divide by simp
            with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
            show ?thesis by simp
          qed
        qed (use True in auto)  (* other cases contradicted by is_arithmetic_binop *)
      next
        case False
        note not_arith = False
        show ?thesis
        proof (cases "is_modulo_binop op")
          case True
          (* Modulo *)
          from typing' not_arith True have
            integer: "is_integer_type lhsTy" and
            types_eq: "lhsTy = rhsTy" and
            ty_eq: "ty = lhsTy"
            by (auto split: if_splits)
          from integer lhsTy_rt obtain sign bits where
            lhsTy_def: "lhsTy = CoreTy_FiniteInt sign bits"
            by (cases lhsTy) auto
          from types_eq lhsTy_def have rhsTy_def: "rhsTy = CoreTy_FiniteInt sign bits" by simp
          from lhs_typed lhsTy_def have lhs_int: "value_has_type env lhsVal (CoreTy_FiniteInt sign bits)" by simp
          from rhs_typed rhsTy_def have rhs_int: "value_has_type env rhsVal (CoreTy_FiniteInt sign bits)" by simp

          from True have op_eq: "op = CoreBinop_Modulo" by (cases op) auto
          show ?thesis
          proof (cases "is_zero rhsVal")
            case True
            then have "eval_binop op lhsVal rhsVal = Inl RuntimeError"
              using op_eq by simp
            with interp_eq show ?thesis by simp
          next
            case False
            then have "eval_binop op lhsVal rhsVal = generic_int_binop tmod lhsVal rhsVal"
              using op_eq by simp
            with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
            show ?thesis by simp
          qed
        next
          case False
          note not_modulo = False
          show ?thesis
          proof (cases "is_bitwise_binop op \<or> is_shift_binop op")
            case True
            (* Bitwise or shift *)
            from typing' not_arith not_modulo True have
              finite_int: "is_finite_integer_type lhsTy" and
              types_eq: "lhsTy = rhsTy" and
              ty_eq: "ty = lhsTy"
              by (auto split: if_splits)
            from finite_int obtain sign bits where
              lhsTy_def: "lhsTy = CoreTy_FiniteInt sign bits"
              by (cases lhsTy) auto
            from types_eq lhsTy_def have rhsTy_def: "rhsTy = CoreTy_FiniteInt sign bits" by simp
            from lhs_typed lhsTy_def have lhs_int: "value_has_type env lhsVal (CoreTy_FiniteInt sign bits)" by simp
            from rhs_typed rhsTy_def have rhs_int: "value_has_type env rhsVal (CoreTy_FiniteInt sign bits)" by simp

            show ?thesis
            proof (cases op)
              case CoreBinop_BitAnd
              have "eval_binop op lhsVal rhsVal = generic_int_binop (\<lambda>x y. and x y) lhsVal rhsVal"
                using CoreBinop_BitAnd by simp
              with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
              show ?thesis by simp
            next
              case CoreBinop_BitOr
              have "eval_binop op lhsVal rhsVal = generic_int_binop (\<lambda>x y. or x y) lhsVal rhsVal"
                using CoreBinop_BitOr by simp
              with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
              show ?thesis by simp
            next
              case CoreBinop_BitXor
              have "eval_binop op lhsVal rhsVal = generic_int_binop (\<lambda>x y. xor x y) lhsVal rhsVal"
                using CoreBinop_BitXor by simp
              with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
              show ?thesis by simp
            next
              case CoreBinop_ShiftLeft
              show ?thesis
              proof (cases "is_valid_shift lhsVal rhsVal")
                case False
                then have "eval_binop op lhsVal rhsVal = Inl RuntimeError"
                  using CoreBinop_ShiftLeft by simp
                with interp_eq show ?thesis by simp
              next
                case True
                then have "eval_binop op lhsVal rhsVal = generic_int_binop (\<lambda>x y. push_bit (nat y) x) lhsVal rhsVal"
                  using CoreBinop_ShiftLeft by simp
                with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
                show ?thesis by simp
              qed
            next
              case CoreBinop_ShiftRight
              show ?thesis
              proof (cases "is_valid_shift lhsVal rhsVal")
                case False
                then have "eval_binop op lhsVal rhsVal = Inl RuntimeError"
                  using CoreBinop_ShiftRight by simp
                with interp_eq show ?thesis by simp
              next
                case True
                then have "eval_binop op lhsVal rhsVal = generic_int_binop (\<lambda>x y. drop_bit (nat y) x) lhsVal rhsVal"
                  using CoreBinop_ShiftRight by simp
                with interp_eq ty_eq lhsTy_def generic_int_binop_sound[OF lhs_int rhs_int]
                show ?thesis by simp
              qed
            qed (use True in auto)  (* other cases contradicted *)
          next
            case False
            note not_bitwise_shift = False
            show ?thesis
            proof (cases "is_ordering_binop op")
              case True
              (* Ordering: <, <=, >, >= *)
              from typing' not_arith not_modulo not_bitwise_shift True have
                numeric: "is_numeric_type lhsTy" and
                types_eq: "lhsTy = rhsTy" and
                ty_eq: "ty = CoreTy_Bool"
                by (auto split: if_splits)
              from numeric lhsTy_rt obtain sign bits where
                lhsTy_def: "lhsTy = CoreTy_FiniteInt sign bits"
                by (cases lhsTy) auto
              from types_eq lhsTy_def have rhsTy_def: "rhsTy = CoreTy_FiniteInt sign bits" by simp
              from lhs_typed lhsTy_def have lhs_int: "value_has_type env lhsVal (CoreTy_FiniteInt sign bits)" by simp
              from rhs_typed rhsTy_def have rhs_int: "value_has_type env rhsVal (CoreTy_FiniteInt sign bits)" by simp

              show ?thesis
              proof (cases op)
                case CoreBinop_Less
                have "eval_binop op lhsVal rhsVal = generic_int_cmp_binop (\<lambda>x y. x < y) lhsVal rhsVal"
                  using CoreBinop_Less by simp
                with interp_eq ty_eq generic_int_cmp_binop_sound[OF lhs_int rhs_int]
                show ?thesis by simp
              next
                case CoreBinop_LessEqual
                have "eval_binop op lhsVal rhsVal = generic_int_cmp_binop (\<lambda>x y. x \<le> y) lhsVal rhsVal"
                  using CoreBinop_LessEqual by simp
                with interp_eq ty_eq generic_int_cmp_binop_sound[OF lhs_int rhs_int]
                show ?thesis by simp
              next
                case CoreBinop_Greater
                have "eval_binop op lhsVal rhsVal = generic_int_cmp_binop (\<lambda>x y. x > y) lhsVal rhsVal"
                  using CoreBinop_Greater by simp
                with interp_eq ty_eq generic_int_cmp_binop_sound[OF lhs_int rhs_int]
                show ?thesis by simp
              next
                case CoreBinop_GreaterEqual
                have "eval_binop op lhsVal rhsVal = generic_int_cmp_binop (\<lambda>x y. x \<ge> y) lhsVal rhsVal"
                  using CoreBinop_GreaterEqual by simp
                with interp_eq ty_eq generic_int_cmp_binop_sound[OF lhs_int rhs_int]
                show ?thesis by simp
              qed (use True in auto)
            next
              case False
              note not_ordering = False
              show ?thesis
              proof (cases "is_eq_neq_binop op")
                case True
                (* Equality/inequality *)
                from typing' not_arith not_modulo not_bitwise_shift not_ordering True have
                  types_eq: "lhsTy = rhsTy" and
                  ty_eq: "ty = CoreTy_Bool" and
                  type_constraint: "lhsTy = CoreTy_Bool \<or> is_numeric_type lhsTy"
                  by (auto split: if_splits)

                from True have op_cases: "op = CoreBinop_Equal \<or> op = CoreBinop_NotEqual"
                  by (cases op) auto

                show ?thesis
                proof (cases "lhsTy = CoreTy_Bool")
                  case True
                  (* Bool equality *)
                  from True types_eq have rhsTy_bool: "rhsTy = CoreTy_Bool" by simp
                  from lhs_typed True obtain b1 where lhsVal_def: "lhsVal = CV_Bool b1"
                    using value_has_type_Bool by blast
                  from rhs_typed rhsTy_bool obtain b2 where rhsVal_def: "rhsVal = CV_Bool b2"
                    using value_has_type_Bool by blast

                  from op_cases show ?thesis
                  proof
                    assume "op = CoreBinop_Equal"
                    then have "eval_binop op lhsVal rhsVal = Inr (CV_Bool (b1 = b2))"
                      using lhsVal_def rhsVal_def by simp
                    with interp_eq ty_eq show ?thesis by simp
                  next
                    assume "op = CoreBinop_NotEqual"
                    then have "eval_binop op lhsVal rhsVal = Inr (CV_Bool (b1 \<noteq> b2))"
                      using lhsVal_def rhsVal_def by simp
                    with interp_eq ty_eq show ?thesis by simp
                  qed
                next
                  case False
                  (* Numeric equality *)
                  from False type_constraint have numeric: "is_numeric_type lhsTy" by simp
                  from numeric lhsTy_rt obtain sign bits where
                    lhsTy_def: "lhsTy = CoreTy_FiniteInt sign bits"
                    by (cases lhsTy) auto
                  from types_eq lhsTy_def have rhsTy_def: "rhsTy = CoreTy_FiniteInt sign bits" by simp
                  from lhs_typed lhsTy_def have lhs_int: "value_has_type env lhsVal (CoreTy_FiniteInt sign bits)" by simp
                  from rhs_typed rhsTy_def have rhs_int: "value_has_type env rhsVal (CoreTy_FiniteInt sign bits)" by simp

                  from lhs_int obtain i1 where lhsVal_def: "lhsVal = CV_FiniteInt sign bits i1"
                    using value_has_type_FiniteInt by blast
                  from rhs_int obtain i2 where rhsVal_def: "rhsVal = CV_FiniteInt sign bits i2"
                    using value_has_type_FiniteInt by blast

                  from op_cases show ?thesis
                  proof
                    assume "op = CoreBinop_Equal"
                    then have "eval_binop op lhsVal rhsVal = generic_int_cmp_binop (\<lambda>x y. x = y) lhsVal rhsVal"
                      using lhsVal_def rhsVal_def by simp
                    with interp_eq ty_eq generic_int_cmp_binop_sound[OF lhs_int rhs_int]
                    show ?thesis by simp
                  next
                    assume "op = CoreBinop_NotEqual"
                    then have "eval_binop op lhsVal rhsVal = generic_int_cmp_binop (\<lambda>x y. x \<noteq> y) lhsVal rhsVal"
                      using lhsVal_def rhsVal_def by simp
                    with interp_eq ty_eq generic_int_cmp_binop_sound[OF lhs_int rhs_int]
                    show ?thesis by simp
                  qed
                qed
              next
                case False
                note not_eq_neq = False
                (* Must be logical *)
                from typing' not_arith not_modulo not_bitwise_shift not_ordering not_eq_neq have
                  logical: "is_logical_binop op" and
                  lhs_bool: "lhsTy = CoreTy_Bool" and
                  rhs_bool: "rhsTy = CoreTy_Bool" and
                  ty_eq: "ty = CoreTy_Bool"
                  by (auto split: if_splits)
                from lhs_typed lhs_bool have lhs_bool_typed: "value_has_type env lhsVal CoreTy_Bool" by simp
                from rhs_typed rhs_bool have rhs_bool_typed: "value_has_type env rhsVal CoreTy_Bool" by simp

                show ?thesis
                proof (cases op)
                  case CoreBinop_And
                  have "eval_binop op lhsVal rhsVal = generic_bool_binop (\<lambda>x y. x \<and> y) lhsVal rhsVal"
                    using CoreBinop_And by simp
                  with interp_eq ty_eq generic_bool_binop_sound[OF lhs_bool_typed rhs_bool_typed]
                  show ?thesis by simp
                next
                  case CoreBinop_Or
                  have "eval_binop op lhsVal rhsVal = generic_bool_binop (\<lambda>x y. x \<or> y) lhsVal rhsVal"
                    using CoreBinop_Or by simp
                  with interp_eq ty_eq generic_bool_binop_sound[OF lhs_bool_typed rhs_bool_typed]
                  show ?thesis by simp
                next
                  case CoreBinop_Implies
                  have "eval_binop op lhsVal rhsVal = generic_bool_binop (\<lambda>x y. x \<longrightarrow> y) lhsVal rhsVal"
                    using CoreBinop_Implies by simp
                  with interp_eq ty_eq generic_bool_binop_sound[OF lhs_bool_typed rhs_bool_typed]
                  show ?thesis by simp
                qed (use logical in auto)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

(* ========================================================================== *)
(* Helper lemmas for CoreTm_Let type soundness *)
(* ========================================================================== *)

(* After alloc_store + fmupd of locals, the new state matches the extended env.
   This is the key lemma for CoreTm_Let soundness. *)
lemma state_matches_env_add_local:
  assumes state_env: "state_matches_env state env"
    and val_typed: "value_has_type env val rhsTy"
    and state'_eq: "(state', addr) = alloc_store state val"
    and state''_eq: "state'' = state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state') \<rparr>"
    and env'_eq: "env' = env \<lparr> TE_TermVars := fmupd var rhsTy (TE_TermVars env),
                               TE_GhostVars := fminus (TE_GhostVars env) {|var|} \<rparr>"
  shows "state_matches_env state'' env'"
proof -
  (* Facts about alloc_store *)
  from state'_eq have addr_eq: "addr = length (IS_Store state)"
    and store'_eq: "IS_Store state' = IS_Store state @ [val]"
    and locals'_eq: "IS_Locals state' = IS_Locals state"
    and refs'_eq: "IS_Refs state' = IS_Refs state"
    and consts'_eq: "IS_Constants state' = IS_Constants state"
    and funs'_eq: "IS_Functions state' = IS_Functions state"
    by auto

  (* Facts about state'' *)
  have store''_eq: "IS_Store state'' = IS_Store state @ [val]"
    using state''_eq store'_eq by simp
  have locals''_eq: "IS_Locals state'' = fmupd var addr (IS_Locals state)"
    using state''_eq locals'_eq by simp
  have refs''_eq: "IS_Refs state'' = IS_Refs state"
    using state''_eq refs'_eq by simp
  have consts''_eq: "IS_Constants state'' = IS_Constants state"
    using state''_eq consts'_eq by simp
  have funs''_eq: "IS_Functions state'' = IS_Functions state"
    using state''_eq funs'_eq by simp

  (* The new address points to val *)
  have addr_valid: "addr < length (IS_Store state'')"
    using addr_eq store''_eq by simp
  have val_at_addr: "IS_Store state'' ! addr = val"
    using addr_eq store''_eq by (simp add: nth_append)

  (* Old addresses are still valid and point to the same values *)
  have old_addrs: "\<And>a. a < length (IS_Store state) \<Longrightarrow>
      a < length (IS_Store state'') \<and> IS_Store state'' ! a = IS_Store state ! a"
    using store''_eq by (simp add: nth_append)

  (* value_has_type is the same in env and env' *)
  have env'_fields: "TE_DataCtors env' = TE_DataCtors env"
                    "TE_Datatypes env' = TE_Datatypes env"
                    "TE_TypeVars env' = TE_TypeVars env"
    using env'_eq by simp_all
  have vht_eq: "\<And>v t. value_has_type env' v t = value_has_type env v t"
    using value_has_type_cong_env[OF env'_fields] .

  (* 1. vars_exist_in_state *)
  have "vars_exist_in_state state'' env'"
    unfolding vars_exist_in_state_def
  proof (intro allI impI, elim conjE)
    fix name ty
    assume lookup: "fmlookup (TE_TermVars env') name = Some ty"
      and not_ghost: "name |\<notin>| TE_GhostVars env'"
    show "term_var_in_state_with_type state'' env' name ty"
    proof (cases "name = var")
      case True
      (* The new variable - points to val at addr *)
      then have "ty = rhsTy" using lookup env'_eq by simp
      then show ?thesis
        using True locals''_eq addr_valid val_at_addr vht_eq val_typed
        unfolding term_var_in_state_with_type_def by simp
    next
      case False
      (* An existing variable *)
      then have "fmlookup (TE_TermVars env) name = Some ty"
        using lookup env'_eq by simp
      moreover have "name |\<notin>| TE_GhostVars env"
        using not_ghost env'_eq False by auto
      ultimately have old: "term_var_in_state_with_type state env name ty"
        using state_env unfolding state_matches_env_def vars_exist_in_state_def by blast
      (* Show the old variable is still valid in state'' *)
      (* Locals lookup is unchanged for name \<noteq> var *)
      have locals_name: "fmlookup (IS_Locals state'') name = fmlookup (IS_Locals state) name"
        using False locals''_eq by simp
      (* From the old state matching, extract what we know about name *)
      from old show ?thesis
      proof (cases "fmlookup (IS_Locals state) name")
        case (Some a)
        (* name is a local in old state, pointing to address a *)
        then have "a < length (IS_Store state) \<and> value_has_type env (IS_Store state ! a) ty"
          using old unfolding term_var_in_state_with_type_def by simp
        then have "a < length (IS_Store state'')" and
                  "IS_Store state'' ! a = IS_Store state ! a"
          using old_addrs by auto
        then show ?thesis using Some locals_name vht_eq old
          unfolding term_var_in_state_with_type_def by auto
      next
        case None
        show ?thesis
        proof (cases "fmlookup (IS_Refs state) name")
          case (Some addrPath)
          obtain aa ba where ap_eq: "addrPath = (aa, ba)" by (cases addrPath) auto
          (* From old, aa < length (IS_Store state) and get_value_at_path succeeds *)
          from old None Some ap_eq have ref_info:
            "aa < length (IS_Store state) \<and>
             (\<exists>v. get_value_at_path (IS_Store state ! aa) ba = Inr v \<and>
                  value_has_type env v ty)"
            unfolding term_var_in_state_with_type_def
            by (auto split: sum.splits)
          then have "IS_Store state'' ! aa = IS_Store state ! aa"
            and "aa < length (IS_Store state'')"
            using old_addrs by auto
          then show ?thesis using old None Some ap_eq locals_name refs''_eq consts''_eq
            ref_info vht_eq
            unfolding term_var_in_state_with_type_def by auto
        next
          case None2: None
          (* name is a constant *)
          then show ?thesis using old None locals_name refs''_eq consts''_eq vht_eq
            unfolding term_var_in_state_with_type_def
            by (smt (verit, best) case_optionE option.simps(4,5))
        qed
      qed
    qed
  qed

  (* 2. no_extra_vars *)
  moreover have "no_extra_vars state'' env'"
    unfolding no_extra_vars_def
  proof (intro allI impI)
    fix name
    assume ante: "fmlookup (TE_TermVars env') name = None \<or> name |\<in>| TE_GhostVars env'"
    show "fmlookup (IS_Locals state'') name = None \<and>
          fmlookup (IS_Refs state'') name = None \<and>
          fmlookup (IS_Constants state'') name = None"
    proof (cases "name = var")
      case True
      (* var is in TE_TermVars env', so the antecedent requires var \<in> TE_GhostVars env' *)
      then have "fmlookup (TE_TermVars env') var = Some rhsTy" using env'_eq by simp
      with ante True have "var |\<in>| TE_GhostVars env'" by simp
      (* But TE_GhostVars env' = fminus (TE_GhostVars env) {|var|}, so var \<notin> TE_GhostVars env' *)
      then show ?thesis using env'_eq by simp
    next
      case False
      (* name \<noteq> var, so TE_TermVars env' lookup = TE_TermVars env lookup *)
      then have tv_eq: "fmlookup (TE_TermVars env') name = fmlookup (TE_TermVars env) name"
        using env'_eq by simp
      (* name \<noteq> var, so name \<in> fminus S {|var|} iff name \<in> S *)
      have gv_iff: "name |\<in>| TE_GhostVars env' \<longleftrightarrow> name |\<in>| TE_GhostVars env"
        using False env'_eq by auto
      from ante tv_eq gv_iff
      have "fmlookup (TE_TermVars env) name = None \<or> name |\<in>| TE_GhostVars env"
        by simp
      then have "fmlookup (IS_Locals state) name = None \<and>
                 fmlookup (IS_Refs state) name = None \<and>
                 fmlookup (IS_Constants state) name = None"
        using state_env unfolding state_matches_env_def no_extra_vars_def by blast
      then show ?thesis using False locals''_eq refs''_eq consts''_eq by simp
    qed
  qed

  (* 3. funs_exist_in_state *)
  moreover have "funs_exist_in_state state'' env'"
    using state_env funs''_eq env'_eq
    unfolding state_matches_env_def funs_exist_in_state_def by simp

  (* 4. no_extra_funs *)
  moreover have "no_extra_funs state'' env'"
    using state_env funs''_eq env'_eq
    unfolding state_matches_env_def no_extra_funs_def by simp

  (* 5. non_consts_in_locals_or_refs *)
  moreover have "non_consts_in_locals_or_refs state'' env'"
    unfolding non_consts_in_locals_or_refs_def
  proof (intro allI impI, elim conjE)
    fix name
    assume tv: "fmlookup (TE_TermVars env') name \<noteq> None"
      and ng: "name |\<notin>| TE_GhostVars env'"
      and nc: "name |\<notin>| TE_ConstNames env'"
    show "fmlookup (IS_Locals state'') name \<noteq> None \<or>
          fmlookup (IS_Refs state'') name \<noteq> None"
    proof (cases "name = var")
      case True
      then show ?thesis using locals''_eq by simp
    next
      case False
      then have "fmlookup (TE_TermVars env) name \<noteq> None"
        using tv env'_eq by simp
      moreover have "name |\<notin>| TE_GhostVars env"
        using ng env'_eq False by auto
      moreover have "name |\<notin>| TE_ConstNames env"
        using nc env'_eq by simp
      ultimately have "fmlookup (IS_Locals state) name \<noteq> None \<or>
                       fmlookup (IS_Refs state) name \<noteq> None"
        using state_env
        unfolding state_matches_env_def non_consts_in_locals_or_refs_def by blast
      then show ?thesis using False locals''_eq refs''_eq by simp
    qed
  qed

  ultimately show ?thesis unfolding state_matches_env_def by auto
qed

(* Type soundness for let-bindings *)
lemma type_soundness_let:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>env' (state' :: 'w InterpState) tm' ty'.
                state_matches_env state' env' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result env' ty' (interp_term fuel state' tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Let var rhs body) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_Let var rhs body))"
proof -
  (* Extract facts from typing *)
  from typing obtain rhsTy where
    rhs_typing: "core_term_type env NotGhost rhs = Some rhsTy" and
    rhs_ground: "is_ground rhsTy" and
    body_typing: "core_term_type
        (env \<lparr> TE_TermVars := fmupd var rhsTy (TE_TermVars env),
               TE_GhostVars := fminus (TE_GhostVars env) {|var|} \<rparr>)
        NotGhost body = Some ty"
    by (auto split: option.splits if_splits)

  let ?env' = "env \<lparr> TE_TermVars := fmupd var rhsTy (TE_TermVars env),
                     TE_GhostVars := fminus (TE_GhostVars env) {|var|} \<rparr>"

  (* Apply IH to rhs *)
  from IH[OF state_env wf_env rhs_typing]
  have rhs_sound: "sound_term_result env rhsTy (interp_term fuel state rhs)" .

  show ?thesis
  proof (cases "interp_term fuel state rhs")
    case (Inl err)
    (* RHS failed - propagate error *)
    then have "interp_term (Suc fuel) state (CoreTm_Let var rhs body) = Inl err"
      by simp
    with rhs_sound Inl show ?thesis by auto
  next
    case (Inr rhsVal)
    (* RHS succeeded *)
    from rhs_sound Inr have rhs_typed: "value_has_type env rhsVal rhsTy" by simp

    (* Construct the new state *)
    obtain state' addr where alloc_eq: "(state', addr) = alloc_store state rhsVal"
      by (cases "alloc_store state rhsVal") auto
    let ?state'' = "state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state') \<rparr>"

    (* The interpreter result *)
    have interp_eq: "interp_term (Suc fuel) state (CoreTm_Let var rhs body) =
          interp_term fuel ?state'' body"
      using Inr alloc_eq by (simp add: case_prod_beta split: prod.splits)

    (* The new state matches the extended env *)
    have state''_env': "state_matches_env ?state'' ?env'"
      using state_matches_env_add_local[OF state_env rhs_typed alloc_eq refl refl] by simp

    (* The extended env is well-formed *)
    from value_has_type_runtime[OF rhs_typed] have rhs_rt: "is_runtime_type rhsTy" .
    have rhs_wk: "is_well_kinded env rhsTy"
      using core_term_type_well_kinded[OF rhs_typing wf_env] .
    have wf_env': "tyenv_well_formed ?env'"
      using tyenv_well_formed_add_var[OF wf_env rhs_wk rhs_ground rhs_rt] .

    (* Apply IH to body in extended env *)
    from IH[OF state''_env' wf_env' body_typing]
    have body_sound: "sound_term_result ?env' ty (interp_term fuel ?state'' body)" .

    (* sound_term_result env' = sound_term_result env, because value_has_type
       only depends on datatypes, not TE_TermVars/TE_GhostVars *)
    have env'_fields: "TE_DataCtors ?env' = TE_DataCtors env"
                       "TE_Datatypes ?env' = TE_Datatypes env"
                       "TE_TypeVars ?env' = TE_TypeVars env"
      by simp_all
    have "\<And>v t. value_has_type ?env' v t = value_has_type env v t"
      using value_has_type_cong_env[OF env'_fields] .
    hence "sound_term_result ?env' ty (interp_term fuel ?state'' body) =
           sound_term_result env ty (interp_term fuel ?state'' body)"
      by (cases "interp_term fuel ?state'' body") auto
    with interp_eq body_sound show ?thesis by simp
  qed
qed

(* Type soundness for unary operators *)
lemma type_soundness_unop:
  assumes state_env: "state_matches_env state env"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Unop unop operand) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_Unop unop operand))"
proof (cases unop)
  case CoreUnop_Negate
  (* Extract facts from typing *)
  from typing CoreUnop_Negate have
    operand_typing: "core_term_type env NotGhost operand = Some ty"
    and signed_numeric: "is_signed_numeric_type ty"
    by (auto split: option.splits if_splits)

  (* Apply IH to operand *)
  from IH[OF operand_typing]
  have operand_sound: "sound_term_result env ty (interp_term fuel state operand)"
    by simp

  (* Case split on operand result *)
  show ?thesis
  proof (cases "interp_term fuel state operand")
    case (Inl err)
    (* Operand failed - propagate the sound error *)
    then show ?thesis using operand_sound by auto
  next
    case (Inr operand_val)
    (* Operand succeeded - extract type information *)
    from operand_sound Inr
    have operand_typed: "value_has_type env operand_val ty"
      by simp

    (* Since ty is signed_numeric and runtime (from value_has_type),
       it must be CoreTy_FiniteInt Signed bits for some bits *)
    from value_has_type_runtime[OF operand_typed]
    have ty_runtime: "is_runtime_type ty" .

    (* is_signed_numeric_type + is_runtime_type => CoreTy_FiniteInt Signed _ *)
    from signed_numeric ty_runtime obtain bits where
      ty_def: "ty = CoreTy_FiniteInt Signed bits"
      using is_runtime_type.simps(4,5) is_signed_numeric_type.elims(2) by blast

    (* So the value must be CV_FiniteInt Signed bits i *)
    from operand_typed ty_def obtain i where
      operand_val_def: "operand_val = CV_FiniteInt Signed bits i"
      and i_fits: "int_fits Signed bits i"
      using value_has_type_FiniteInt by blast

    (* Now evaluate the negation *)
    show ?thesis
    proof (cases "int_fits Signed bits (-i)")
      case True
      (* Negation succeeds *)
      have result: "interp_term (Suc fuel) state (CoreTm_Unop CoreUnop_Negate operand) =
                    Inr (CV_FiniteInt Signed bits (-i))"
        using Inr operand_val_def True CoreUnop_Negate by simp
      have result_typed: "value_has_type env (CV_FiniteInt Signed bits (-i)) ty"
        using ty_def True by simp
      show ?thesis using result result_typed CoreUnop_Negate by simp
    next
      case False
      (* Negation overflows - RuntimeError *)
      have result: "interp_term (Suc fuel) state (CoreTm_Unop CoreUnop_Negate operand) =
                    Inl RuntimeError"
        using Inr operand_val_def False CoreUnop_Negate by simp
      show ?thesis using result CoreUnop_Negate by simp
    qed
  qed
next
  case CoreUnop_Complement
  (* Extract facts from typing *)
  from typing CoreUnop_Complement have
    operand_typing: "core_term_type env NotGhost operand = Some ty"
    and finite_int: "is_finite_integer_type ty"
    by (auto split: option.splits if_splits)

  (* Apply IH to operand *)
  from IH[OF operand_typing]
  have operand_sound: "sound_term_result env ty (interp_term fuel state operand)"
    by simp

  (* Case split on operand result *)
  show ?thesis
  proof (cases "interp_term fuel state operand")
    case (Inl err)
    then show ?thesis using operand_sound by auto
  next
    case (Inr operand_val)
    from operand_sound Inr
    have operand_typed: "value_has_type env operand_val ty"
      by simp

    (* is_finite_integer_type ty => ty = CoreTy_FiniteInt sign bits *)
    from finite_int obtain sign bits where
      ty_def: "ty = CoreTy_FiniteInt sign bits"
      by (cases ty) auto

    (* So the value must be CV_FiniteInt sign bits i *)
    from operand_typed ty_def obtain i where
      operand_val_def: "operand_val = CV_FiniteInt sign bits i"
      and i_fits: "int_fits sign bits i"
      using value_has_type_FiniteInt by blast

    (* Complement always succeeds *)
    have result: "interp_term (Suc fuel) state (CoreTm_Unop CoreUnop_Complement operand) =
                  Inr (CV_FiniteInt sign bits (int_complement sign bits i))"
      using Inr operand_val_def CoreUnop_Complement by simp
    have result_typed: "value_has_type env (CV_FiniteInt sign bits (int_complement sign bits i)) ty"
      using ty_def int_complement_fits[OF i_fits] by simp
    show ?thesis using result result_typed CoreUnop_Complement by simp
  qed
next
  case CoreUnop_Not
  (* Extract facts from typing *)
  from typing CoreUnop_Not have
    operand_typing: "core_term_type env NotGhost operand = Some CoreTy_Bool"
    and ty_eq: "ty = CoreTy_Bool"
    by (auto split: option.splits if_splits)

  (* Apply IH to operand *)
  from IH[OF operand_typing]
  have operand_sound: "sound_term_result env CoreTy_Bool (interp_term fuel state operand)"
    by simp

  (* Case split on operand result *)
  show ?thesis
  proof (cases "interp_term fuel state operand")
    case (Inl err)
    then show ?thesis using operand_sound ty_eq by auto
  next
    case (Inr operand_val)
    from operand_sound Inr
    have operand_typed: "value_has_type env operand_val CoreTy_Bool"
      by simp

    (* Value must be CV_Bool b *)
    from operand_typed obtain b where
      operand_val_def: "operand_val = CV_Bool b"
      using value_has_type_Bool by blast

    (* Not always succeeds *)
    have result: "interp_term (Suc fuel) state (CoreTm_Unop CoreUnop_Not operand) =
                  Inr (CV_Bool (\<not>b))"
      using Inr operand_val_def CoreUnop_Not by simp
    have result_typed: "value_has_type env (CV_Bool (\<not>b)) ty"
      using ty_eq by simp
    show ?thesis using result result_typed CoreUnop_Not by simp
  qed
qed


(* If two association lists are related by list_all2 with matching keys,
   then map_of on the first succeeds whenever map_of on the second does *)
lemma map_of_list_all2:
  assumes "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> P v t) xs ys"
    and "map_of ys name = Some t"
  shows "\<exists>v. map_of xs name = Some v \<and> P v t"
using assms proof (induction xs ys rule: list_all2_induct)
  case Nil
  then show ?case by simp
next
  case (Cons x xs y ys)
  obtain n1 v where x_eq: "x = (n1, v)" by (cases x) auto
  obtain n2 t' where y_eq: "y = (n2, t')" by (cases y) auto
  from Cons.hyps x_eq y_eq have name_eq: "n1 = n2" and rel: "P v t'" by auto
  show ?case
  proof (cases "name = n2")
    case True
    from Cons.prems y_eq True have "t = t'" by simp
    with name_eq True x_eq rel show ?thesis by auto
  next
    case False
    from Cons.prems y_eq False have "map_of ys name = Some t" by simp
    from Cons.IH[OF this] obtain v' where "map_of xs name = Some v'" "P v' t" by auto
    with name_eq False x_eq show ?thesis by auto
  qed
qed

(* Type soundness for record projection *)
lemma type_soundness_record_proj:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>env' (state' :: 'w InterpState) tm' ty'.
                state_matches_env state' env' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result env' ty' (interp_term fuel state' tm')"
    and typing: "core_term_type env NotGhost (CoreTm_RecordProj tm fldName) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_RecordProj tm fldName))"
proof -
  (* Extract facts from typing *)
  from typing obtain fieldTypes where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Record fieldTypes)" and
    fld_lookup: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)

  (* Apply IH to tm *)
  from IH[OF state_env wf_env tm_typing]
  have tm_sound: "sound_term_result env (CoreTy_Record fieldTypes) (interp_term fuel state tm)" .

  show ?thesis
  proof (cases "interp_term fuel state tm")
    case (Inl err)
    (* tm failed - propagate error *)
    then have "interp_term (Suc fuel) state (CoreTm_RecordProj tm fldName) = Inl err"
      by simp
    with tm_sound Inl show ?thesis by auto
  next
    case (Inr val)
    (* tm succeeded *)
    from tm_sound Inr have val_typed: "value_has_type env val (CoreTy_Record fieldTypes)" by simp

    (* Value must be CV_Record *)
    from val_typed obtain fieldValues where
      val_eq: "val = CV_Record fieldValues" and
      fields_rel: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t)
                     fieldValues fieldTypes"
      by (cases val) (auto split: CoreType.splits)

    (* map_of fieldValues fldName succeeds with the right type *)
    from map_of_list_all2[OF fields_rel fld_lookup]
    obtain fldVal where
      fld_val_lookup: "map_of fieldValues fldName = Some fldVal" and
      fld_val_typed: "value_has_type env fldVal ty" by auto

    (* The interpreter result *)
    have interp_eq: "interp_term (Suc fuel) state (CoreTm_RecordProj tm fldName) = Inr fldVal"
      using Inr val_eq fld_val_lookup by simp

    show ?thesis using interp_eq fld_val_typed by simp
  qed
qed


(* Type soundness for variant projection *)
lemma type_soundness_variant_proj:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>env' (state' :: 'w InterpState) tm' ty'.
                state_matches_env state' env' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result env' ty' (interp_term fuel state' tm')"
    and typing: "core_term_type env NotGhost (CoreTm_VariantProj tm ctorName) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_VariantProj tm ctorName))"
proof -
  (* Extract facts from typing *)
  from typing obtain dtName tyArgs dtName2 metavars payloadTy where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Name dtName tyArgs)" and
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, metavars, payloadTy)" and
    dt_eq: "dtName = dtName2" and
    len_eq: "length tyArgs = length metavars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip metavars tyArgs)) payloadTy"
    by (auto split: option.splits CoreType.splits prod.splits if_splits)

  (* Apply IH to tm *)
  from IH[OF state_env wf_env tm_typing]
  have tm_sound: "sound_term_result env (CoreTy_Name dtName tyArgs) (interp_term fuel state tm)" .

  show ?thesis
  proof (cases "interp_term fuel state tm")
    case (Inl err)
    (* tm failed - propagate error *)
    then have "interp_term (Suc fuel) state (CoreTm_VariantProj tm ctorName) = Inl err"
      by simp
    with tm_sound Inl show ?thesis by auto
  next
    case (Inr val)
    (* tm succeeded *)
    from tm_sound Inr
    have val_typed: "value_has_type env val (CoreTy_Name dtName tyArgs)" by simp

    (* Value must be CV_Variant *)
    from value_has_type_Name[OF val_typed] obtain actualCtor payload where
      val_eq: "val = CV_Variant actualCtor payload" by auto

    (* Extract typing facts from value_has_type for the variant *)
    from val_typed val_eq obtain dtName3 metavars3 payloadTy3 where
      val_ctor_lookup: "fmlookup (TE_DataCtors env) actualCtor = Some (dtName3, metavars3, payloadTy3)" and
      val_dt_eq: "dtName = dtName3" and
      val_len_eq: "length metavars3 = length tyArgs" and
      payload_typed: "value_has_type env payload
          (apply_subst (fmap_of_list (zip metavars3 tyArgs)) payloadTy3)"
      by (auto split: option.splits prod.splits)

    show ?thesis
    proof (cases "actualCtor = ctorName")
      case True
      (* Constructor names match - projection succeeds *)
      (* Both look up the same constructor, so metavars and payloadTy agree *)
      from val_ctor_lookup ctor_lookup True dt_eq val_dt_eq
      have "metavars3 = metavars" and "payloadTy3 = payloadTy"
        by auto
      hence "value_has_type env payload ty"
        using payload_typed ty_eq by simp

      moreover have "interp_term (Suc fuel) state (CoreTm_VariantProj tm ctorName) = Inr payload"
        using Inr val_eq True by simp

      ultimately show ?thesis by simp
    next
      case False
      (* Constructor names don't match - RuntimeError *)
      have "interp_term (Suc fuel) state (CoreTm_VariantProj tm ctorName) = Inl RuntimeError"
        using Inr val_eq False by simp
      then show ?thesis by simp
    qed
  qed
qed


(* If all values have type u64, interpret_index_vals succeeds *)
lemma interpret_index_vals_u64:
  assumes "list_all2 (value_has_type env) vals (replicate n (CoreTy_FiniteInt Unsigned IntBits_64))"
  shows "\<exists>indices. interpret_index_vals vals = Inr indices"
using assms proof (induction vals arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons v vs)
  from Cons.prems obtain n' where n_eq: "n = Suc n'" and
    v_typed: "value_has_type env v (CoreTy_FiniteInt Unsigned IntBits_64)" and
    vs_typed: "list_all2 (value_has_type env) vs (replicate n' (CoreTy_FiniteInt Unsigned IntBits_64))"
    by (cases n) auto
  from value_has_type_FiniteInt[OF v_typed] obtain i where
    v_eq: "v = CV_FiniteInt Unsigned IntBits_64 i" by auto
  from Cons.IH[OF vs_typed] obtain rest_indices where
    rest_eq: "interpret_index_vals vs = Inr rest_indices" by auto
  show ?case using v_eq rest_eq by simp
qed

(* Type soundness for array projection *)
lemma type_soundness_array_proj:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env"
    and wf_env: "tyenv_well_formed env"
    and IH_term: "\<And>env' (state' :: 'w InterpState) tm' ty'.
                state_matches_env state' env' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result env' ty' (interp_term fuel state' tm')"
    and IH_list: "\<And>env' (state' :: 'w InterpState) tms' types'.
                state_matches_env state' env' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results env' (map the types') (interp_term_list fuel state' tms')"
    and typing: "core_term_type env NotGhost (CoreTm_ArrayProj arr idxTms) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_ArrayProj arr idxTms))"
proof -
  (* Extract facts from typing *)
  from typing obtain elemTy dims where
    arr_typing: "core_term_type env NotGhost arr = Some (CoreTy_Array elemTy dims)" and
    len_eq: "length idxTms = length dims" and
    idxs_typed: "list_all (\<lambda>tm. core_term_type env NotGhost tm
                    = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)

  (* Apply IH to arr *)
  from IH_term[OF state_env wf_env arr_typing]
  have arr_sound: "sound_term_result env (CoreTy_Array elemTy dims) (interp_term fuel state arr)" .

  (* Prepare typing info for index terms to use IH_list *)
  let ?types = "map (core_term_type env NotGhost) idxTms"
  from idxs_typed have types_all_some: "list_all (\<lambda>ty. ty \<noteq> None) ?types"
    by (simp add: list_all_length)
  from IH_list[OF state_env wf_env] types_all_some
  have idx_sound: "sound_term_results env (map the ?types) (interp_term_list fuel state idxTms)"
    by simp

  (* The expected types are all u64 *)
  from idxs_typed have map_the_types: "map the ?types =
      replicate (length idxTms) (CoreTy_FiniteInt Unsigned IntBits_64)"
    by (induction idxTms) (auto simp: list_all_iff)

  show ?thesis
  proof (cases "interp_term fuel state arr")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_ArrayProj arr idxTms) = Inl err"
      by simp
    with arr_sound Inl show ?thesis by auto
  next
    case (Inr arrVal)
    from arr_sound Inr
    have arr_val_typed: "value_has_type env arrVal (CoreTy_Array elemTy dims)" by simp

    (* Value must be CV_Array *)
    from value_has_type_Array[OF arr_val_typed] obtain sizes valuesMap where
      arr_val_eq: "arrVal = CV_Array sizes valuesMap" and
      elems_typed: "\<forall>idx v. fmlookup valuesMap idx = Some v \<longrightarrow> value_has_type env v elemTy"
      by auto

    show ?thesis
    proof (cases "interp_term_list fuel state idxTms")
      case (Inl err)
      then have "interp_term (Suc fuel) state (CoreTm_ArrayProj arr idxTms) = Inl err"
        using Inr arr_val_eq by simp
      with idx_sound Inl show ?thesis by auto
    next
      case (Inr idxVals)
      from idx_sound Inr map_the_types
      have idxVals_typed: "list_all2 (value_has_type env) idxVals
          (replicate (length idxTms) (CoreTy_FiniteInt Unsigned IntBits_64))"
        by simp

      (* interpret_index_vals succeeds *)
      from interpret_index_vals_u64[OF idxVals_typed]
      obtain indices where interp_idx_eq: "interpret_index_vals idxVals = Inr indices" by auto

      show ?thesis
      proof (cases "fmlookup valuesMap indices")
        case None
        (* Out of bounds - RuntimeError *)
        then have "interp_term (Suc fuel) state (CoreTm_ArrayProj arr idxTms) = Inl RuntimeError"
          using \<open>interp_term fuel state arr = Inr arrVal\<close> arr_val_eq Inr interp_idx_eq
          by simp
        then show ?thesis by simp
      next
        case (Some result)
        have result_typed: "value_has_type env result elemTy"
          using elems_typed Some by simp
        have "interp_term (Suc fuel) state (CoreTm_ArrayProj arr idxTms) = Inr result"
          using \<open>interp_term fuel state arr = Inr arrVal\<close> arr_val_eq Inr interp_idx_eq Some
          by simp
        then show ?thesis using result_typed ty_eq by simp
      qed
    qed
  qed
qed


(* Path append: following a concatenated path is the same as following the first
   part and then following the second part on the result *)
lemma get_value_at_path_append:
  "get_value_at_path root (path @ rest) =
    (case get_value_at_path root path of
      Inr v \<Rightarrow> get_value_at_path v rest
    | Inl err \<Rightarrow> Inl err)"
proof (induction path arbitrary: root)
  case Nil
  then show ?case by simp
next
  case (Cons step path)
  show ?case
  proof (cases root)
    case (CV_Record flds)
    then show ?thesis
    proof (cases step)
      case (LVPath_RecordProj fldName)
      then show ?thesis using CV_Record Cons.IH
        by (simp split: option.splits)
    next
      case (LVPath_VariantProj x2)
      then show ?thesis using CV_Record by simp
    next
      case (LVPath_ArrayProj x3)
      then show ?thesis using CV_Record by simp
    qed
  next
    case (CV_Variant ctor payload)
    then show ?thesis
    proof (cases step)
      case (LVPath_RecordProj x1)
      then show ?thesis using CV_Variant by simp
    next
      case (LVPath_VariantProj expectedCtor)
      then show ?thesis using CV_Variant Cons.IH by simp
    next
      case (LVPath_ArrayProj x3)
      then show ?thesis using CV_Variant by simp
    qed
  next
    case (CV_Array sizes elementMap)
    then show ?thesis
    proof (cases step)
      case (LVPath_RecordProj x1)
      then show ?thesis using CV_Array by simp
    next
      case (LVPath_VariantProj x2)
      then show ?thesis using CV_Array by simp
    next
      case (LVPath_ArrayProj indices)
      then show ?thesis using CV_Array Cons.IH
        by (simp split: option.splits)
    qed
  next
    case (CV_Bool x)
    then show ?thesis by (cases step) auto
  next
    case (CV_FiniteInt x1 x2 x3)
    then show ?thesis by (cases step) auto
  qed
qed


(*-----------------------------------------------------------------------------*)
(* Main type soundness theorem *)
(*-----------------------------------------------------------------------------*)

theorem type_soundness:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env"
    and wf_env: "tyenv_well_formed env"
  shows interp_term_sound:
    "core_term_type env NotGhost tm = Some ty \<longrightarrow>
      sound_term_result env ty (interp_term fuel state tm)"
  and interp_term_list_sound:
    "map (core_term_type env NotGhost) tms = types \<and>
    list_all (\<lambda>ty. ty \<noteq> None) types \<longrightarrow>
      sound_term_results env (map the types) (interp_term_list fuel state tms)"
  and interp_lvalue_sound:
    "is_writable_lvalue env tm \<and> core_term_type env NotGhost tm = Some ty \<longrightarrow>
      sound_lvalue_result state env ty (interp_lvalue fuel state tm)"
  and interp_statement_sound:
    "undefined (interp_statement fuel state stmt)"  (* TODO: state properly *)
  and interp_function_call_sound:
    "undefined (interp_function_call fuel state fnName argTms)"  (* TODO: state properly *)
using assms 
proof (induction fuel arbitrary: state env tm ty tms types fnName argTms)
  case 0
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case by simp
  next
    case 4
    then show ?case sorry  (* requires proper definition *)
  next
    case 5
    then show ?case sorry  (* requires proper definition *)
  }
next
  case (Suc fuel)
  {
    (* interp_term_sound *)
    case 1
    show ?case proof (intro impI)

      (* Given a well-typed term *)
      assume typing: "core_term_type env NotGhost tm = Some ty"

      (* From IH, we know interp_term works properly for fuel;
         we need to prove it for (Suc fuel) *)
      have IH: "\<And>env' (state' :: 'w InterpState) tm' ty'. 
                  state_matches_env state' env' \<Longrightarrow>
                  tyenv_well_formed env' \<Longrightarrow>
                  core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                    sound_term_result env' ty' (interp_term fuel state' tm')"
        by (simp add: "1.prems"(1,2) Suc.IH(1))
        
      show "sound_term_result env ty (interp_term (Suc fuel) state tm)"
      proof (cases tm)
        (* Literal bool - evaluates to CV_Bool *)
        case (CoreTm_LitBool b)
        then show ?thesis using typing by auto
      next
        (* Literal int - evaluates to CV_FiniteInt if well-typed *)
        case (CoreTm_LitInt i)
        then show ?thesis using typing by auto
      next
        case (CoreTm_LitArray elemTms)
        then show ?thesis sorry  (* TODO *)
  
      next
        (* Variable/constant lookup *)
        case (CoreTm_Var varName) 
        have var_in_state: "term_var_in_state_with_type state env varName ty"
          using state_env state_matches_env_def vars_exist_in_state_def
          by (smt (verit, ccfv_threshold) "1.prems"(1) CoreTm_Var core_term_type.simps(4)
              option.case_eq_if option.distinct(1) option.expand option.sel typing) 
        show ?thesis proof (cases "fmlookup (IS_Locals state) varName")
          case None
          then show ?thesis proof (cases "fmlookup (IS_Refs state) varName")
            case None2: None
            (* Variable must be in Constants *)
            from var_in_state None None2 obtain val where
              const_lookup: "fmlookup (IS_Constants state) varName = Some val"
              and val_typed: "value_has_type env val ty"
              unfolding term_var_in_state_with_type_def
              by (auto split: option.splits sum.splits)
            have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName) = Inr val"
              using CoreTm_Var None None2 const_lookup by simp
            then show ?thesis using val_typed CoreTm_Var by simp
          next
            case (Some addrPath)
            (* Variable is a ref - need to dereference *)
            obtain addr path where addrPath_eq: "addrPath = (addr, path)"
              by (cases addrPath) auto
            from var_in_state None Some addrPath_eq obtain v where
              get_val: "get_value_at_path (IS_Store state ! addr) path = Inr v"
              and v_typed: "value_has_type env v ty"
              unfolding term_var_in_state_with_type_def
              by (auto split: option.splits sum.splits)
            have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName) = Inr v"
              using CoreTm_Var None Some addrPath_eq get_val by simp
            then show ?thesis using v_typed CoreTm_Var by simp
          qed
        next
          case (Some addr)
          then have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName)
                                      = Inr (IS_Store state ! addr)"
            using CoreTm_Var by simp
          have store_type: "addr < length (IS_Store state) \<and>
                   value_has_type env (IS_Store state ! addr) ty"
            using var_in_state Some term_var_in_state_with_type_def by force
          then show ?thesis
            using CoreTm_Var interp_result by auto
        qed

      next
        (* Cast - use helper lemma *)
        case (CoreTm_Cast targetTy operandTm)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_cast typing by blast 

      next
        (* Unary operator - use helper lemma *)
        case (CoreTm_Unop op operandTm)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_unop typing by blast

      next
        (* Binary operator - use helper lemma *)
        case (CoreTm_Binop op lhsTm rhsTm)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_binop typing by blast
      next
        (* Let-binding - use helper lemma *)
        case (CoreTm_Let var rhsTm bodyTm)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_let typing by blast
      next
        case (CoreTm_Quantifier x91 x92 x93 x94)
        then show ?thesis using typing by simp
      next
        case (CoreTm_FunctionCall x101 x102 x103)
        then show ?thesis sorry
      next
        case (CoreTm_VariantCtor x111 x112 x113)
        then show ?thesis sorry
      next
        case (CoreTm_Record x12)
        then show ?thesis sorry
      next
        case (CoreTm_RecordProj x131 x132)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_record_proj typing by blast
      next
        case (CoreTm_VariantProj x141 x142)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_variant_proj typing by blast
      next
        case (CoreTm_ArrayProj x151 x152)
        have IH_term: "\<And>env' (state' :: 'w InterpState) tm' ty'.
                state_matches_env state' env' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result env' ty' (interp_term fuel state' tm')"
          by (simp add: Suc.IH(1) "1.prems"(1,2))
        have IH_list: "\<And>env' (state' :: 'w InterpState) tms' types'.
                state_matches_env state' env' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results env' (map the types') (interp_term_list fuel state' tms')"
          by (simp add: Suc.IH(2) "1.prems"(1,2))
        from CoreTm_ArrayProj show ?thesis
          using type_soundness_array_proj[OF "1.prems"(1,2) IH_term IH_list] typing
          by blast
      next
        case (CoreTm_Match x161 x162)
        then show ?thesis sorry
      next
        case (CoreTm_Sizeof x17)
        then show ?thesis sorry
      next
        case (CoreTm_Allocated x18)
        then show ?thesis using typing by simp
      next
        case (CoreTm_Old x19)
        then show ?thesis using typing by simp
      qed
    qed
  next
    (* interp_term_list_sound *)
    case 2
    show ?case proof (intro impI, elim conjE)
      assume types_eq: "map (core_term_type env NotGhost) tms = types"
         and all_typed: "list_all (\<lambda>ty. ty \<noteq> None) types"
      show "sound_term_results env (map the types) (interp_term_list (Suc fuel) state tms)"
      proof (cases tms)
        case Nil
        then have "interp_term_list (Suc fuel) state tms = Inr []" by simp
        moreover from Nil types_eq have "map the types = []" by simp
        ultimately show ?thesis by simp
      next
        case (Cons tm tms')
        (* Get typing for head and tail *)
        from types_eq Cons obtain types' where
          types_cons: "types = core_term_type env NotGhost tm # types'"
          and types'_eq: "map (core_term_type env NotGhost) tms' = types'"
          by auto
        from all_typed types_cons have
          tm_typed_opt: "core_term_type env NotGhost tm \<noteq> None"
          and all_typed': "list_all (\<lambda>ty. ty \<noteq> None) types'"
          by auto
        from tm_typed_opt obtain tm_ty where
          tm_typing: "core_term_type env NotGhost tm = Some tm_ty"
          by auto

        (* Use IH for the head term *)
        from Suc.IH(1)[of state env tm tm_ty] "2.prems"
        have head_sound: "sound_term_result env tm_ty (interp_term fuel state tm)"
          using tm_typing by simp

        (* Use IH for the tail list *)
        from Suc.IH(2)[of state env tms' types'] "2.prems" types'_eq all_typed'
        have tail_sound: "sound_term_results env (map the types') (interp_term_list fuel state tms')"
          by simp

        (* Case split on head evaluation *)
        show ?thesis
        proof (cases "interp_term fuel state tm")
          case (Inl err)
          (* Head failed - propagate error *)
          from head_sound Inl have "sound_error_result err" by simp
          moreover have "interp_term_list (Suc fuel) state tms = Inl err"
            using Cons Inl by simp
          ultimately show ?thesis by simp
        next
          case (Inr val)
          (* Head succeeded *)
          from head_sound Inr have val_typed: "value_has_type env val tm_ty" by simp
          (* Case split on tail evaluation *)
          show ?thesis
          proof (cases "interp_term_list fuel state tms'")
            case (Inl err)
            (* Tail failed - propagate error *)
            from tail_sound Inl have "sound_error_result err" by simp
            moreover have "interp_term_list (Suc fuel) state tms = Inl err"
              using Cons Inr Inl by simp
            ultimately show ?thesis by simp
          next
            case (Inr vals)
            (* Both succeeded *)
            from tail_sound Inr
            have vals_typed: "list_all2 (value_has_type env) vals (map the types')" by simp
            have result: "interp_term_list (Suc fuel) state tms = Inr (val # vals)"
              using Cons \<open>interp_term fuel state tm = Inr val\<close> Inr by simp
            have "map the types = tm_ty # map the types'"
              using types_cons tm_typing by simp
            with val_typed vals_typed result show ?thesis by simp
          qed
        qed
      qed
    qed
  next
    (* interp_lvalue_sound *)
    case 3
    show ?case proof (intro impI, elim conjE)
      assume writable: "is_writable_lvalue env tm"
        and typing: "core_term_type env NotGhost tm = Some ty"

      have IH_lvalue: "\<And>env' (state' :: 'w InterpState) tm' ty'.
                state_matches_env state' env' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                is_writable_lvalue env' tm' \<and> core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_lvalue_result state' env' ty' (interp_lvalue fuel state' tm')"
        by (simp add: Suc.IH(3) "3.prems"(1,2))

      have IH_list: "\<And>env' (state' :: 'w InterpState) tms' types'.
                state_matches_env state' env' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results env' (map the types') (interp_term_list fuel state' tms')"
        by (simp add: Suc.IH(2) "3.prems"(1,2))

      show "sound_lvalue_result state env ty (interp_lvalue (Suc fuel) state tm)"
      proof (cases tm)
        (* Non-lvalue cases: is_writable_lvalue is False, contradiction *)
        case (CoreTm_LitBool x) then show ?thesis using writable by simp
      next case (CoreTm_LitInt x) then show ?thesis using writable by simp
      next case (CoreTm_LitArray x) then show ?thesis using writable by simp
      next case (CoreTm_Cast x1 x2) then show ?thesis using writable by simp
      next case (CoreTm_Unop x1 x2) then show ?thesis using writable by simp
      next case (CoreTm_Binop x1 x2 x3) then show ?thesis using writable by simp
      next case (CoreTm_Let x1 x2 x3) then show ?thesis using writable by simp
      next case (CoreTm_Quantifier x1 x2 x3 x4) then show ?thesis using writable by simp
      next case (CoreTm_FunctionCall x1 x2 x3) then show ?thesis using writable by simp
      next case (CoreTm_VariantCtor x1 x2 x3) then show ?thesis using writable by simp
      next case (CoreTm_Record x) then show ?thesis using writable by simp
      next case (CoreTm_Match x1 x2) then show ?thesis using writable by simp
      next case (CoreTm_Sizeof x) then show ?thesis using writable by simp
      next case (CoreTm_Allocated x) then show ?thesis using writable by simp
      next case (CoreTm_Old x) then show ?thesis using writable by simp
      next
        (* CoreTm_Var: base case for lvalues *)
        case (CoreTm_Var varName)
        from typing CoreTm_Var obtain varTy where
          var_lookup: "fmlookup (TE_TermVars env) varName = Some varTy" and
          not_ghost: "varName |\<notin>| TE_GhostVars env" and
          ty_eq: "ty = varTy"
          by (auto split: option.splits if_splits)
        from writable CoreTm_Var have not_const: "varName |\<notin>| TE_ConstNames env" by simp
        (* Variable is in IS_Locals or IS_Refs *)
        from "3.prems"(1) var_lookup not_ghost not_const
        have in_locals_or_refs:
          "fmlookup (IS_Locals state) varName \<noteq> None \<or>
           fmlookup (IS_Refs state) varName \<noteq> None"
          unfolding state_matches_env_def non_consts_in_locals_or_refs_def by blast
        (* Variable has correct type in state *)
        have var_in_state: "term_var_in_state_with_type state env varName ty"
          using "3.prems"(1) var_lookup not_ghost ty_eq
          unfolding state_matches_env_def vars_exist_in_state_def by blast
        show ?thesis
        proof (cases "fmlookup (IS_Locals state) varName")
          case (Some addr)
          then have interp_eq: "interp_lvalue (Suc fuel) state tm = Inr (addr, [])"
            using CoreTm_Var by simp
          from var_in_state Some have
            addr_valid: "addr < length (IS_Store state)" and
            val_typed: "value_has_type env (IS_Store state ! addr) ty"
            unfolding term_var_in_state_with_type_def by auto
          have "get_value_at_path (IS_Store state ! addr) [] = Inr (IS_Store state ! addr)"
            by simp
          then show ?thesis using interp_eq addr_valid val_typed by simp
        next
          case None
          (* Must be in IS_Refs *)
          from in_locals_or_refs None have "fmlookup (IS_Refs state) varName \<noteq> None" by simp
          then obtain addrPath where refs_lookup: "fmlookup (IS_Refs state) varName = Some addrPath"
            by auto
          obtain addr path where addrPath_eq: "addrPath = (addr, path)"
            by (cases addrPath) auto
          then have interp_eq: "interp_lvalue (Suc fuel) state tm = Inr (addr, path)"
            using CoreTm_Var None refs_lookup by simp
          from var_in_state None refs_lookup addrPath_eq have
            addr_valid: "addr < length (IS_Store state)" and
            path_ok: "case get_value_at_path (IS_Store state ! addr) path of
                        Inr v \<Rightarrow> value_has_type env v ty | Inl err \<Rightarrow> False"
            unfolding term_var_in_state_with_type_def
            by (auto split: sum.splits)
          (* path_ok with Inl \<Rightarrow> False means the path must succeed *)
          have "case get_value_at_path (IS_Store state ! addr) path of
                  Inr v \<Rightarrow> value_has_type env v ty | Inl err \<Rightarrow> sound_error_result err"
          proof (cases "get_value_at_path (IS_Store state ! addr) path")
            case (Inl err)
            then show ?thesis using path_ok by simp
          next
            case (Inr v)
            then show ?thesis using path_ok by simp
          qed
          then show ?thesis using interp_eq addr_valid by simp
        qed
      next
        (* CoreTm_RecordProj: extend path with record field *)
        case (CoreTm_RecordProj innerTm fldName)
        from typing CoreTm_RecordProj obtain fieldTypes where
          inner_typing: "core_term_type env NotGhost innerTm = Some (CoreTy_Record fieldTypes)" and
          fld_lookup: "map_of fieldTypes fldName = Some ty"
          by (auto split: option.splits CoreType.splits)
        from writable CoreTm_RecordProj have inner_writable: "is_writable_lvalue env innerTm"
          by simp
        from IH_lvalue[OF "3.prems"(1,2)] inner_writable inner_typing
        have inner_sound: "sound_lvalue_result state env (CoreTy_Record fieldTypes)
                             (interp_lvalue fuel state innerTm)"
          by simp
        show ?thesis
        proof (cases "interp_lvalue fuel state innerTm")
          case (Inl err)
          then have "interp_lvalue (Suc fuel) state tm = Inl err"
            using CoreTm_RecordProj by simp
          with inner_sound Inl show ?thesis by auto
        next
          case (Inr addrPath)
          obtain addr path where ap_eq: "addrPath = (addr, path)" by (cases addrPath) auto
          from inner_sound Inr ap_eq have
            addr_valid: "addr < length (IS_Store state)" and
            path_sound: "case get_value_at_path (IS_Store state ! addr) path of
                           Inr v \<Rightarrow> value_has_type env v (CoreTy_Record fieldTypes)
                         | Inl err \<Rightarrow> sound_error_result err"
            by auto
          have interp_eq: "interp_lvalue (Suc fuel) state tm =
              Inr (addr, path @ [LVPath_RecordProj fldName])"
            using CoreTm_RecordProj Inr ap_eq by simp
          (* Show the extended path is sound *)
          have "case get_value_at_path (IS_Store state ! addr)
                       (path @ [LVPath_RecordProj fldName]) of
                  Inr v \<Rightarrow> value_has_type env v ty
                | Inl err \<Rightarrow> sound_error_result err"
          proof (cases "get_value_at_path (IS_Store state ! addr) path")
            case (Inl err)
            (* Inner path failed — error propagates through append *)
            then have "get_value_at_path (IS_Store state ! addr)
                         (path @ [LVPath_RecordProj fldName]) = Inl err"
              using get_value_at_path_append by simp
            with path_sound Inl show ?thesis by simp
          next
            case (Inr v)
            (* Inner path succeeded *)
            from path_sound Inr have v_typed: "value_has_type env v (CoreTy_Record fieldTypes)"
              by simp
            from v_typed obtain fieldValues where
              v_eq: "v = CV_Record fieldValues" and
              fields_rel: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t)
                             fieldValues fieldTypes"
              by (cases v) (auto split: CoreType.splits)
            from map_of_list_all2[OF fields_rel fld_lookup]
            obtain fldVal where
              fld_val_lookup: "map_of fieldValues fldName = Some fldVal" and
              fld_val_typed: "value_has_type env fldVal ty" by auto
            have "get_value_at_path (IS_Store state ! addr)
                    (path @ [LVPath_RecordProj fldName]) = Inr fldVal"
              using get_value_at_path_append Inr v_eq fld_val_lookup by simp
            with fld_val_typed show ?thesis by simp
          qed
          then show ?thesis using interp_eq addr_valid by simp
        qed
      next
        (* CoreTm_VariantProj: extend path with variant projection *)
        case (CoreTm_VariantProj innerTm ctorName)
        from typing CoreTm_VariantProj obtain dtName tyArgs dtName2 metavars payloadTy where
          inner_typing: "core_term_type env NotGhost innerTm = Some (CoreTy_Name dtName tyArgs)" and
          ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, metavars, payloadTy)" and
          dt_eq: "dtName = dtName2" and
          len_eq: "length tyArgs = length metavars" and
          ty_eq: "ty = apply_subst (fmap_of_list (zip metavars tyArgs)) payloadTy"
          by (auto split: option.splits CoreType.splits prod.splits if_splits)
        from writable CoreTm_VariantProj have inner_writable: "is_writable_lvalue env innerTm"
          by simp
        from IH_lvalue[OF "3.prems"(1,2)] inner_writable inner_typing
        have inner_sound: "sound_lvalue_result state env (CoreTy_Name dtName tyArgs)
                             (interp_lvalue fuel state innerTm)"
          by simp
        show ?thesis
        proof (cases "interp_lvalue fuel state innerTm")
          case (Inl err)
          then have "interp_lvalue (Suc fuel) state tm = Inl err"
            using CoreTm_VariantProj by simp
          with inner_sound Inl show ?thesis by auto
        next
          case (Inr addrPath)
          obtain addr path where ap_eq: "addrPath = (addr, path)" by (cases addrPath) auto
          from inner_sound Inr ap_eq have
            addr_valid: "addr < length (IS_Store state)" and
            path_sound: "case get_value_at_path (IS_Store state ! addr) path of
                           Inr v \<Rightarrow> value_has_type env v (CoreTy_Name dtName tyArgs)
                         | Inl err \<Rightarrow> sound_error_result err"
            by auto
          have interp_eq: "interp_lvalue (Suc fuel) state tm =
              Inr (addr, path @ [LVPath_VariantProj ctorName])"
            using CoreTm_VariantProj Inr ap_eq by simp
          have "case get_value_at_path (IS_Store state ! addr)
                       (path @ [LVPath_VariantProj ctorName]) of
                  Inr v \<Rightarrow> value_has_type env v ty
                | Inl err \<Rightarrow> sound_error_result err"
          proof (cases "get_value_at_path (IS_Store state ! addr) path")
            case (Inl err)
            then have "get_value_at_path (IS_Store state ! addr)
                         (path @ [LVPath_VariantProj ctorName]) = Inl err"
              using get_value_at_path_append by simp
            with path_sound Inl show ?thesis by simp
          next
            case (Inr v)
            from path_sound Inr have v_typed: "value_has_type env v (CoreTy_Name dtName tyArgs)"
              by simp
            from value_has_type_Name[OF v_typed] obtain actualCtor payload where
              v_eq: "v = CV_Variant actualCtor payload" by auto
            from v_typed v_eq obtain dtName3 metavars3 payloadTy3 where
              val_ctor_lookup: "fmlookup (TE_DataCtors env) actualCtor =
                                 Some (dtName3, metavars3, payloadTy3)" and
              val_dt_eq: "dtName = dtName3" and
              val_len_eq: "length metavars3 = length tyArgs" and
              payload_typed: "value_has_type env payload
                  (apply_subst (fmap_of_list (zip metavars3 tyArgs)) payloadTy3)"
              by (auto split: option.splits prod.splits)
            show ?thesis
            proof (cases "actualCtor = ctorName")
              case True
              from val_ctor_lookup ctor_lookup True dt_eq val_dt_eq
              have "metavars3 = metavars" and "payloadTy3 = payloadTy" by auto
              hence payload_ty: "value_has_type env payload ty"
                using payload_typed ty_eq by simp
              have "get_value_at_path (IS_Store state ! addr)
                      (path @ [LVPath_VariantProj ctorName]) =
                    get_value_at_path payload []"
                using get_value_at_path_append Inr v_eq True by simp
              hence "get_value_at_path (IS_Store state ! addr)
                      (path @ [LVPath_VariantProj ctorName]) = Inr payload"
                by simp
              with payload_ty show ?thesis by simp
            next
              case False
              have "get_value_at_path (IS_Store state ! addr)
                      (path @ [LVPath_VariantProj ctorName]) = Inl RuntimeError"
                using get_value_at_path_append Inr v_eq False by simp
              then show ?thesis by simp
            qed
          qed
          then show ?thesis using interp_eq addr_valid by simp
        qed
      next
        (* CoreTm_ArrayProj: extend path with array index *)
        case (CoreTm_ArrayProj innerTm idxTms)
        from typing CoreTm_ArrayProj obtain elemTy dims where
          inner_typing: "core_term_type env NotGhost innerTm = Some (CoreTy_Array elemTy dims)" and
          len_eq: "length idxTms = length dims" and
          idxs_typed: "list_all (\<lambda>tm. core_term_type env NotGhost tm
                          = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
          ty_eq: "ty = elemTy"
          by (auto split: option.splits CoreType.splits if_splits)
        from writable CoreTm_ArrayProj have inner_writable: "is_writable_lvalue env innerTm"
          by simp
        from IH_lvalue[OF "3.prems"(1,2)] inner_writable inner_typing
        have inner_sound: "sound_lvalue_result state env (CoreTy_Array elemTy dims)
                             (interp_lvalue fuel state innerTm)"
          by simp
        (* Index terms *)
        let ?types = "map (core_term_type env NotGhost) idxTms"
        from idxs_typed have types_all_some: "list_all (\<lambda>ty. ty \<noteq> None) ?types"
          by (simp add: list_all_length)
        from IH_list[OF "3.prems"(1,2)] types_all_some
        have idx_sound: "sound_term_results env (map the ?types) (interp_term_list fuel state idxTms)"
          by simp
        from idxs_typed have map_the_types: "map the ?types =
            replicate (length idxTms) (CoreTy_FiniteInt Unsigned IntBits_64)"
          by (induction idxTms) (auto simp: list_all_iff)
        show ?thesis
        proof (cases "interp_lvalue fuel state innerTm")
          case (Inl err)
          then have "interp_lvalue (Suc fuel) state tm = Inl err"
            using CoreTm_ArrayProj by simp
          with inner_sound Inl show ?thesis by auto
        next
          case (Inr addrPath)
          obtain addr path where ap_eq: "addrPath = (addr, path)" by (cases addrPath) auto
          from inner_sound Inr ap_eq have
            addr_valid: "addr < length (IS_Store state)" and
            path_sound: "case get_value_at_path (IS_Store state ! addr) path of
                           Inr v \<Rightarrow> value_has_type env v (CoreTy_Array elemTy dims)
                         | Inl err \<Rightarrow> sound_error_result err"
            by auto
          show ?thesis
          proof (cases "interp_term_list fuel state idxTms")
            case (Inl err)
            then have "interp_lvalue (Suc fuel) state tm = Inl err"
              using CoreTm_ArrayProj \<open>interp_lvalue fuel state innerTm = Inr addrPath\<close>
                    ap_eq by simp
            with idx_sound Inl show ?thesis by auto
          next
            case (Inr idxVals)
            from idx_sound Inr map_the_types
            have idxVals_typed: "list_all2 (value_has_type env) idxVals
                (replicate (length idxTms) (CoreTy_FiniteInt Unsigned IntBits_64))"
              by simp
            from interpret_index_vals_u64[OF idxVals_typed]
            obtain indices where interp_idx_eq: "interpret_index_vals idxVals = Inr indices" by auto
            have interp_eq: "interp_lvalue (Suc fuel) state tm =
                Inr (addr, path @ [LVPath_ArrayProj indices])"
              using CoreTm_ArrayProj \<open>interp_lvalue fuel state innerTm = Inr addrPath\<close>
                    ap_eq Inr interp_idx_eq by simp
            have "case get_value_at_path (IS_Store state ! addr)
                         (path @ [LVPath_ArrayProj indices]) of
                    Inr v \<Rightarrow> value_has_type env v ty
                  | Inl err \<Rightarrow> sound_error_result err"
            proof (cases "get_value_at_path (IS_Store state ! addr) path")
              case (Inl err)
              then have "get_value_at_path (IS_Store state ! addr)
                           (path @ [LVPath_ArrayProj indices]) = Inl err"
                using get_value_at_path_append by simp
              with path_sound Inl show ?thesis by simp
            next
              case (Inr v)
              from path_sound Inr
              have v_typed: "value_has_type env v (CoreTy_Array elemTy dims)" by simp
              from value_has_type_Array[OF v_typed] obtain sizes valuesMap where
                v_eq: "v = CV_Array sizes valuesMap" and
                elems_typed: "\<forall>idx val. fmlookup valuesMap idx = Some val \<longrightarrow>
                               value_has_type env val elemTy"
                by auto
              show ?thesis
              proof (cases "fmlookup valuesMap indices")
                case None
                have "get_value_at_path (IS_Store state ! addr)
                        (path @ [LVPath_ArrayProj indices]) = Inl RuntimeError"
                  using get_value_at_path_append Inr v_eq None by simp
                then show ?thesis by simp
              next
                case (Some elemVal)
                have elem_typed: "value_has_type env elemVal elemTy"
                  using elems_typed Some by simp
                have "get_value_at_path (IS_Store state ! addr)
                        (path @ [LVPath_ArrayProj indices]) =
                      get_value_at_path elemVal []"
                  using get_value_at_path_append Inr v_eq Some by simp
                hence "get_value_at_path (IS_Store state ! addr)
                        (path @ [LVPath_ArrayProj indices]) = Inr elemVal"
                  by simp
                with elem_typed ty_eq show ?thesis by simp
              qed
            qed
            then show ?thesis using interp_eq addr_valid by simp
          qed
        qed
      qed
    qed
  next
    case 4
    then show ?case sorry
  next
    case 5
    then show ?case sorry
  }
qed

  

end

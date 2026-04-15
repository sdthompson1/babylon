theory TypeSoundness
  imports TypeSoundnessHelpers "../core/CoreTypeSubst"
begin

(*-----------------------------------------------------------------------------*)
(* Helper lemmas for type soundness *)
(*-----------------------------------------------------------------------------*)

(* Type soundness for Cast *)
lemma type_soundness_cast:
  assumes state_env: "state_matches_env state env storeTyping"
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

(* Type soundness for unary operators *)
lemma type_soundness_unop:
  assumes state_env: "state_matches_env state env storeTyping"
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
    have ty_runtime: "is_runtime_type env ty" .

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
  assumes state_env: "state_matches_env state env storeTyping"
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
      from value_has_type_runtime[OF lhs_typed] have lhsTy_rt: "is_runtime_type env lhsTy" .
      from value_has_type_runtime[OF rhs_typed] have rhsTy_rt: "is_runtime_type env rhsTy" .

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

(* Type soundness for let-bindings *)
lemma type_soundness_let:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result env' ty' (interp_term fuel state' tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Let var rhs body) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_Let var rhs body))"
proof -
  (* Extract facts from typing *)
  from typing obtain rhsTy where
    rhs_typing: "core_term_type env NotGhost rhs = Some rhsTy" and
    body_typing: "core_term_type
        (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
               TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
               TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
        NotGhost body = Some ty"
    by (auto simp: Let_def split: option.splits if_splits)

  let ?env' = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                     TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"

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
    let ?state'' = "state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                              IS_Refs := fmdrop var (IS_Refs state'),
                              IS_ConstLocals := finsert var (IS_ConstLocals state') \<rparr>"

    (* The interpreter result *)
    have interp_eq: "interp_term (Suc fuel) state (CoreTm_Let var rhs body) =
          interp_term fuel ?state'' body"
      using Inr alloc_eq by (simp add: case_prod_beta split: prod.splits)

    (* The new state matches the extended env under the extended storeTyping *)
    have state''_env': "state_matches_env ?state'' ?env' (storeTyping @ [rhsTy])"
      using state_matches_env_add_const_local[OF state_env rhs_typed alloc_eq refl refl]
      by simp

    (* The extended env is well-formed *)
    from value_has_type_runtime[OF rhs_typed] have rhs_rt: "is_runtime_type env rhsTy" .
    have rhs_wk: "is_well_kinded env rhsTy"
      using core_term_type_well_kinded[OF rhs_typing wf_env] .
    have wf_env': "tyenv_well_formed ?env'"
    proof -
      let ?env_mid = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                            TE_GhostLocals := fminus (TE_GhostLocals env) {|var|} \<rparr>"
      have "tyenv_well_formed ?env_mid"
        using tyenv_well_formed_add_var[OF wf_env rhs_wk rhs_rt] .
      moreover have "?env' = ?env_mid \<lparr> TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
        by simp
      ultimately show ?thesis
        using tyenv_well_formed_TE_ConstLocals_irrelevant by simp
    qed

    (* Apply IH to body in extended env *)
    from IH[OF state''_env' wf_env' body_typing]
    have body_sound: "sound_term_result ?env' ty (interp_term fuel ?state'' body)" .

    (* sound_term_result env' = sound_term_result env, because value_has_type
       only depends on datatypes, not TE_LocalVars/TE_GlobalVars/TE_GhostLocals *)
    have env'_fields: "TE_DataCtors ?env' = TE_DataCtors env"
                       "TE_Datatypes ?env' = TE_Datatypes env"
                       "TE_TypeVars ?env' = TE_TypeVars env"
                       "TE_GhostDatatypes ?env' = TE_GhostDatatypes env"
                       "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env"
      by simp_all
    have "\<And>v t. value_has_type ?env' v t = value_has_type env v t"
      using value_has_type_cong_env[OF env'_fields] .
    hence "sound_term_result ?env' ty (interp_term fuel ?state'' body) =
           sound_term_result env ty (interp_term fuel ?state'' body)"
      by (cases "interp_term fuel ?state'' body") auto
    with interp_eq body_sound show ?thesis by simp
  qed
qed

(* Type soundness for record projection *)
lemma type_soundness_record_proj:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
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
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result env' ty' (interp_term fuel state' tm')"
    and typing: "core_term_type env NotGhost (CoreTm_VariantProj tm ctorName) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_VariantProj tm ctorName))"
proof -
  (* Extract facts from typing *)
  from typing obtain dtName tyArgs dtName2 tyvars payloadTy where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Datatype dtName tyArgs)" and
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, tyvars, payloadTy)" and
    dt_eq: "dtName = dtName2" and
    len_eq: "length tyArgs = length tyvars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    by (auto split: option.splits CoreType.splits prod.splits if_splits)

  (* Apply IH to tm *)
  from IH[OF state_env wf_env tm_typing]
  have tm_sound: "sound_term_result env (CoreTy_Datatype dtName tyArgs) (interp_term fuel state tm)" .

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
    have val_typed: "value_has_type env val (CoreTy_Datatype dtName tyArgs)" by simp

    (* Value must be CV_Variant *)
    from value_has_type_Name[OF val_typed] obtain actualCtor payload where
      val_eq: "val = CV_Variant actualCtor payload" by auto

    (* Extract typing facts from value_has_type for the variant *)
    from val_typed val_eq obtain dtName3 tyvars3 payloadTy3 where
      val_ctor_lookup: "fmlookup (TE_DataCtors env) actualCtor = Some (dtName3, tyvars3, payloadTy3)" and
      val_dt_eq: "dtName = dtName3" and
      val_len_eq: "length tyvars3 = length tyArgs" and
      payload_typed: "value_has_type env payload
          (apply_subst (fmap_of_list (zip tyvars3 tyArgs)) payloadTy3)"
      by (auto split: option.splits prod.splits)

    show ?thesis
    proof (cases "actualCtor = ctorName")
      case True
      (* Constructor names match - projection succeeds *)
      (* Both look up the same constructor, so tyvars and payloadTy agree *)
      from val_ctor_lookup ctor_lookup True dt_eq val_dt_eq
      have "tyvars3 = tyvars" and "payloadTy3 = payloadTy"
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

(* Type soundness for array projection *)
lemma type_soundness_array_proj:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH_term: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result env' ty' (interp_term fuel state' tm')"
    and IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
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

(* Type soundness for CoreTm_Record *)
lemma type_soundness_record:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results env' (map the types') (interp_term_list fuel state' tms')"
    and typing: "core_term_type env NotGhost (CoreTm_Record flds) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_Record flds))"
proof -
  (* Extract facts from typing *)
  from typing obtain tys where
    distinct_names: "distinct (map fst flds)" and
    those_ok: "those (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits if_splits)

  (* Derive that each field term is typed *)
  from those_ok have la2: "list_all2 (\<lambda>x y. x = Some y)
      (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) tys"
    by (simp add: those_eq_Some)
  hence len_eq: "length tys = length flds" by (auto dest: list_all2_lengthD)

  (* Connect with interp_term_list's precondition *)
  define types where "types = map (core_term_type env NotGhost) (map snd flds)"
  have types_map: "types = map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds"
    unfolding types_def by (induction flds) auto
  have types_eq: "map (core_term_type env NotGhost) (map snd flds) = types"
    unfolding types_def by simp
  have all_typed: "list_all (\<lambda>ty. ty \<noteq> None) types"
  proof -
    from la2 have "\<forall>i < length flds.
        (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) ! i = Some (tys ! i)"
      using len_eq by (auto simp: list_all2_conv_all_nth)
    hence "\<forall>i < length types. types ! i \<noteq> None"
      using types_map by auto
    thus ?thesis by (simp add: list_all_length)
  qed

  (* The expected types from the list IH *)
  have the_types: "map the types = tys"
  proof (intro nth_equalityI)
    show "length (map the types) = length tys"
      using len_eq types_map by simp
  next
    fix i assume "i < length (map the types)"
    hence i_bound: "i < length flds" using len_eq types_map by simp
    from la2 i_bound len_eq have
      "(map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) ! i = Some (tys ! i)"
      by (auto simp: list_all2_conv_all_nth)
    thus "map the types ! i = tys ! i"
      using types_map i_bound by auto
  qed

  (* Apply the list IH *)
  from IH_list[OF state_env wf_env, of "map snd flds" types]
  have list_sound: "sound_term_results env (map the types) (interp_term_list fuel state (map snd flds))"
    using types_eq all_typed by simp

  (* Case split on list evaluation *)
  show ?thesis
  proof (cases "interp_term_list fuel state (map snd flds)")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_Record flds) = Inl err"
      by simp
    with list_sound Inl show ?thesis by auto
  next
    case (Inr vals)
    from list_sound Inr have vals_typed: "list_all2 (value_has_type env) vals (map the types)"
      by simp
    hence vals_typed': "list_all2 (value_has_type env) vals tys"
      using the_types by simp

    have interp_eq: "interp_term (Suc fuel) state (CoreTm_Record flds) =
          Inr (CV_Record (zip (map fst flds) vals))"
      using Inr by simp

    (* Show the result has the correct type *)
    have len_vals: "length vals = length flds"
      using vals_typed' len_eq by (auto dest: list_all2_lengthD)

    have names_vals: "map fst (zip (map fst flds) vals) = map fst flds"
      using len_vals by simp
    have names_tys: "map fst (zip (map fst flds) tys) = map fst flds"
      using len_eq by simp
    have vals_list: "map snd (zip (map fst flds) vals) = vals"
      using len_vals by simp
    have tys_list: "map snd (zip (map fst flds) tys) = tys"
      using len_eq by simp
    have "list_all2 (\<lambda>(name1, fldVal) (name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
            (zip (map fst flds) vals) (zip (map fst flds) tys)"
    proof (rule list_all2_all_nthI)
      show "length (zip (map fst flds) vals) = length (zip (map fst flds) tys)"
        using len_vals len_eq by simp
    next
      fix i assume i_bound: "i < length (zip (map fst flds) vals)"
      hence i_flds: "i < length flds" using len_vals by simp
      from vals_typed' i_flds len_eq have "value_has_type env (vals ! i) (tys ! i)"
        by (auto simp: list_all2_conv_all_nth)
      thus "(case zip (map fst flds) vals ! i of
              (name1, fldVal) \<Rightarrow> \<lambda>(name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
             (zip (map fst flds) tys ! i)"
        using i_flds len_vals len_eq by simp
    qed
    hence "value_has_type env (CV_Record (zip (map fst flds) vals))
                              (CoreTy_Record (zip (map fst flds) tys))"
      using distinct_names len_eq by simp

    with interp_eq ty_eq show ?thesis by simp
  qed
qed

(* Type soundness for CoreTm_VariantCtor *)
lemma type_soundness_variant_ctor:
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_VariantCtor ctorName tyArgs payload) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payload))"
proof -
  (* Extract facts from typing *)
  from typing obtain dtName tyvars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyargs_rt: "list_all (is_runtime_type env) tyArgs" and
    dt_nonghost: "dtName |\<notin>| TE_GhostDatatypes env"
    by (auto simp: Let_def split: option.splits prod.splits if_splits)

  define tySubst where "tySubst = fmap_of_list (zip tyvars tyArgs)"
  define payloadTyOpt where "payloadTyOpt = core_term_type env NotGhost payload"

  from typing ctor_lookup len_eq tyargs_wk tyargs_rt dt_nonghost
  have typing': "(case payloadTyOpt of
      None \<Rightarrow> None
    | Some actualPayloadTy \<Rightarrow>
        if actualPayloadTy = apply_subst tySubst payloadTy
        then Some (CoreTy_Datatype dtName tyArgs) else None) = Some ty"
    unfolding payloadTyOpt_def tySubst_def by (simp add: Let_def)

  from typing' obtain payloadActualTy where
    payloadTyOpt_eq: "payloadTyOpt = Some payloadActualTy" and
    payload_ty_eq: "payloadActualTy = apply_subst tySubst payloadTy" and
    ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
    by (cases payloadTyOpt) (auto split: if_splits)

  have payload_typing: "core_term_type env NotGhost payload = Some payloadActualTy"
    using payloadTyOpt_eq payloadTyOpt_def by simp

  (* IH on payload *)
  from IH[OF payload_typing]
  have payload_sound: "sound_term_result env payloadActualTy (interp_term fuel state payload)" .

  (* Case split on payload evaluation *)
  show ?thesis
  proof (cases "interp_term fuel state payload")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payload) = Inl err"
      by simp
    with payload_sound Inl show ?thesis by auto
  next
    case (Inr payloadVal)
    from payload_sound Inr have payload_typed: "value_has_type env payloadVal payloadActualTy" by simp

    have interp_eq: "interp_term (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payload) =
          Inr (CV_Variant ctorName payloadVal)"
      using Inr by simp

    (* Show the result has the correct type *)
    have "value_has_type env (CV_Variant ctorName payloadVal) (CoreTy_Datatype dtName tyArgs)"
      using ctor_lookup len_eq tyargs_wk tyargs_rt dt_nonghost payload_typed payload_ty_eq tySubst_def
      by simp

    with interp_eq ty_eq show ?thesis by simp
  qed
qed

(* Type soundness for CoreTm_Match *)
lemma type_soundness_match:
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Match scrut arms) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_Match scrut arms))"
proof -
  (* Extract facts from typing *)
  define scrutTyOpt where "scrutTyOpt = core_term_type env NotGhost scrut"

  from typing have typing': "(case scrutTyOpt of
      None \<Rightarrow> None
    | Some scrutTy \<Rightarrow>
        let pats = map fst arms; bodies = map snd arms
        in if arms = [] then None
           else if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
           else if \<not> patterns_regular pats then None
           else if \<not> patterns_exhaustive env scrutTy pats then None
           else (case core_term_type env NotGhost (snd (hd arms)) of
                   None \<Rightarrow> None
                 | Some resultTy \<Rightarrow>
                     if list_all (\<lambda>body. core_term_type env NotGhost body = Some resultTy) (tl bodies)
                     then Some resultTy else None)) = Some ty"
    unfolding scrutTyOpt_def by simp

  from typing' obtain scrutTy where
    scrutTyOpt_eq: "scrutTyOpt = Some scrutTy"
    by (cases scrutTyOpt) auto

  have scrut_typing: "core_term_type env NotGhost scrut = Some scrutTy"
    using scrutTyOpt_eq scrutTyOpt_def by simp

  from typing' scrutTyOpt_eq have typing'':
    "(let pats = map fst arms; bodies = map snd arms
      in if arms = [] then None
         else if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
         else if \<not> patterns_regular pats then None
         else if \<not> patterns_exhaustive env scrutTy pats then None
         else (case core_term_type env NotGhost (snd (hd arms)) of
                 None \<Rightarrow> None
               | Some resultTy \<Rightarrow>
                   if list_all (\<lambda>body. core_term_type env NotGhost body = Some resultTy)
                               (tl (map snd arms))
                   then Some resultTy else None)) = Some ty"
    by simp

  from typing'' have arms_nonempty: "arms \<noteq> []"
    by (cases arms) (simp_all add: Let_def)

  from typing'' arms_nonempty have
    pats_compat: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    pats_regular: "patterns_regular (map fst arms)" and
    pats_exhaustive: "patterns_exhaustive env scrutTy (map fst arms)"
    by (simp_all add: Let_def split: if_splits)

  define hd_ty_opt where "hd_ty_opt = core_term_type env NotGhost (snd (hd arms))"

  from typing'' arms_nonempty pats_compat pats_regular pats_exhaustive
  have typing''': "(case hd_ty_opt of
      None \<Rightarrow> None
    | Some resultTy \<Rightarrow>
        if list_all (\<lambda>body. core_term_type env NotGhost body = Some resultTy)
                    (tl (map snd arms))
        then Some resultTy else None) = Some ty"
    unfolding hd_ty_opt_def Let_def by presburger

  from typing''' obtain resultTy where
    hd_ty_opt_eq: "hd_ty_opt = Some resultTy" and
    ty_eq: "ty = resultTy"
    by (cases hd_ty_opt) (auto split: if_splits)

  have hd_typing: "core_term_type env NotGhost (snd (hd arms)) = Some resultTy"
    using hd_ty_opt_eq hd_ty_opt_def by simp

  from typing''' hd_ty_opt_eq ty_eq have
    tl_typing: "list_all (\<lambda>body. core_term_type env NotGhost body = Some resultTy) (tl (map snd arms))"
    by (simp split: if_splits)

  (* All arm bodies have type resultTy *)
  have all_arms_typed: "\<forall>arm \<in> set arms. core_term_type env NotGhost (snd arm) = Some resultTy"
  proof
    fix arm assume arm_in: "arm \<in> set arms"
    from arms_nonempty obtain a rest where arms_eq: "arms = a # rest" by (cases arms) auto
    show "core_term_type env NotGhost (snd arm) = Some resultTy"
    proof (cases "arm = a")
      case True then show ?thesis using hd_typing arms_eq by simp
    next
      case False
      from arm_in False arms_eq have "arm \<in> set rest" by simp
      hence "snd arm \<in> set (map snd rest)" by auto
      hence "snd arm \<in> set (tl (map snd arms))" using arms_eq by simp
      with tl_typing show ?thesis by (simp add: list_all_iff)
    qed
  qed

  (* IH on scrutinee *)
  from IH[OF scrut_typing]
  have scrut_sound: "sound_term_result env scrutTy (interp_term fuel state scrut)" .

  (* Case split on scrutinee evaluation *)
  show ?thesis
  proof (cases "interp_term fuel state scrut")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_Match scrut arms) = Inl err" by simp
    with scrut_sound Inl show ?thesis by auto
  next
    case (Inr scrutVal)
    from scrut_sound Inr have scrut_typed: "value_has_type env scrutVal scrutTy" by simp

    (* find_matching_arm succeeds by exhaustiveness *)
    from find_matching_arm_exhaustive[OF scrut_typed pats_exhaustive wf_env]
    obtain armBody where match_eq: "find_matching_arm scrutVal arms = Inr armBody" by auto

    (* armBody is the body of some arm in the list *)
    from find_matching_arm_in_set[OF match_eq]
    obtain pat where arm_in: "(pat, armBody) \<in> set arms" by auto

    (* armBody typechecks to resultTy *)
    have arm_typed: "core_term_type env NotGhost armBody = Some resultTy"
      using all_arms_typed arm_in by force

    (* IH on arm body *)
    from IH[OF arm_typed]
    have arm_sound: "sound_term_result env resultTy (interp_term fuel state armBody)" .

    (* Compute the result *)
    have "interp_term (Suc fuel) state (CoreTm_Match scrut arms) =
          interp_term fuel state armBody"
      using Inr match_eq by simp
    with arm_sound ty_eq show ?thesis by simp
  qed
qed

(* Type soundness for CoreTm_Sizeof *)
lemma type_soundness_sizeof:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Sizeof tm) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_Sizeof tm))"
proof -
  from typing obtain elemTy dims where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Array elemTy dims)" and
    ty_eq: "ty = sizeof_type dims"
    by (auto split: option.splits CoreType.splits if_splits)

  from IH[OF tm_typing]
  have tm_sound: "sound_term_result env (CoreTy_Array elemTy dims) (interp_term fuel state tm)" .

  show ?thesis
  proof (cases "interp_term fuel state tm")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_Sizeof tm) = Inl err" by simp
    with tm_sound Inl show ?thesis by auto
  next
    case (Inr val)
    from tm_sound Inr have val_typed: "value_has_type env val (CoreTy_Array elemTy dims)" by simp
    from val_typed obtain sizes valuesMap where
      val_eq: "val = CV_Array sizes valuesMap" and
      fmap_ok: "fmap_matches_sizes sizes valuesMap" and
      dims_ok: "sizes_match_dims sizes dims"
      by (cases val) (auto split: CoreType.splits)
    from fmap_ok have sv: "sizes_valid sizes" by (simp add: fmap_matches_sizes_def)
    have interp_eq: "interp_term (Suc fuel) state (CoreTm_Sizeof tm) =
          Inr (array_size_to_value sizes)"
      using Inr val_eq by simp
    have "value_has_type env (array_size_to_value sizes) (sizeof_type dims)"
      using array_size_to_value_has_sizeof_type[OF sv dims_ok] .
    with interp_eq ty_eq show ?thesis by simp
  qed
qed

(* Type soundness for CoreTm_LitArray *)
lemma type_soundness_lit_array:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results env' (map the types') (interp_term_list fuel state' tms')"
    and typing: "core_term_type env NotGhost (CoreTm_LitArray elemTy tms) = Some ty"
  shows "sound_term_result env ty (interp_term (Suc fuel) state (CoreTm_LitArray elemTy tms))"
proof -
  (* Extract facts from typing *)
  from typing have
    wk: "is_well_kinded env elemTy" and
    rt: "is_runtime_type env elemTy" and
    all_typed: "list_all (\<lambda>tm. core_term_type env NotGhost tm = Some elemTy) tms" and
    len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)

  (* Set up list IH precondition *)
  define types where "types = map (core_term_type env NotGhost) tms"
  have types_eq: "map (core_term_type env NotGhost) tms = types"
    by (simp add: types_def)
  have all_some: "list_all (\<lambda>ty. ty \<noteq> None) types"
    using all_typed by (auto simp: types_def list_all_iff)
  have the_types: "map the types = replicate (length tms) elemTy"
    using all_typed by (auto simp: types_def list_all_iff intro!: nth_equalityI)

  (* Apply list IH *)
  from IH_list[OF state_env wf_env, of tms types] types_eq all_some
  have list_sound: "sound_term_results env (replicate (length tms) elemTy)
                      (interp_term_list fuel state tms)"
    using the_types by simp

  (* Case split on list evaluation *)
  show ?thesis
  proof (cases "interp_term_list fuel state tms")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_LitArray elemTy tms) = Inl err" by simp
    with list_sound Inl show ?thesis by auto
  next
    case (Inr vals)
    from list_sound Inr
    have vals_typed: "list_all2 (value_has_type env) vals (replicate (length tms) elemTy)" by simp
    hence len_vals: "length vals = length tms" by (auto dest: list_all2_lengthD)
    hence vals_elem_typed: "\<And>i. i < length vals \<Longrightarrow> value_has_type env (vals ! i) elemTy"
      using vals_typed by (auto simp: list_all2_conv_all_nth)

    have interp_eq: "interp_term (Suc fuel) state (CoreTm_LitArray elemTy tms) =
          Inr (make_1d_array vals)"
      using Inr by simp

    (* Show make_1d_array vals has the right type *)
    define n where "n = int (length vals)"
    define fm where "fm = fmap_of_list (zip (map (\<lambda>i. [int i]) [0..<length vals]) vals)"

    have make_eq: "make_1d_array vals = CV_Array [n] fm"
      by (simp add: n_def fm_def)

    (* sizes_valid *)
    have n_nonneg: "n \<ge> 0" by (simp add: n_def)
    have n_fits: "n \<le> snd (int_range Unsigned IntBits_64)"
      using len_ok len_vals by (simp add: n_def)
    have sv: "sizes_valid [n]"
      using n_nonneg n_fits by (simp add: sizes_valid_def)

    (* fmap_matches_sizes *)
    have fm_dom: "fmdom fm = fset_of_list (all_indices [n])"
    proof -
      have keys: "map (\<lambda>i. [int i]) [0..<length vals] = all_indices [n]"
      proof -
        have "all_indices [n] = concat (map (\<lambda>i. [[i]]) (map int [0..<nat n]))"
          by (simp add: Let_def)
        also have "... = map (\<lambda>i. [i]) (map int [0..<nat n])"
          by (metis concat_map_singleton)
        also have "... = map (\<lambda>i. [int i]) [0..<nat n]" by (simp add: comp_def)
        also have "[0..<nat n] = [0..<length vals]" using n_nonneg by (simp add: n_def)
        finally show ?thesis by simp
      qed
      have "fmdom fm = fset_of_list (map fst (zip (map (\<lambda>i. [int i]) [0..<length vals]) vals))"
        unfolding fm_def by simp
      also have "... = fset_of_list (map (\<lambda>i. [int i]) [0..<length vals])"
        by (simp add: map_fst_zip_take len_vals)
      also have "... = fset_of_list (all_indices [n])"
        using keys by simp
      finally show ?thesis .
    qed
    have fms: "fmap_matches_sizes [n] fm"
      by (simp add: fmap_matches_sizes_def sv fm_dom)

    (* sizes_match_dims *)
    have smd: "sizes_match_dims [n] [CoreDim_Fixed (int (length tms))]"
      by (simp add: n_def len_vals)

    (* array_dims_well_kinded *)
    have adwk: "array_dims_well_kinded [CoreDim_Fixed (int (length tms))]"
      using len_ok by (simp add: array_dims_well_kinded_def)

    (* All values in fmap have type elemTy *)
    have fm_vals_typed: "\<forall>idx val. fmlookup fm idx = Some val \<longrightarrow> value_has_type env val elemTy"
    proof (intro allI impI)
      fix idx val assume lkup: "fmlookup fm idx = Some val"
      hence "map_of (zip (map (\<lambda>i. [int i]) [0..<length vals]) vals) idx = Some val"
        unfolding fm_def by (simp add: fmlookup_of_list)
      hence "(idx, val) \<in> set (zip (map (\<lambda>i. [int i]) [0..<length vals]) vals)"
        by (rule map_of_SomeD)
      hence "val \<in> set vals" by (auto simp: set_zip)
      then obtain i where "i < length vals" and "val = vals ! i"
        by (auto simp: in_set_conv_nth)
      thus "value_has_type env val elemTy"
        using vals_elem_typed by simp
    qed

    have "value_has_type env (CV_Array [n] fm) (CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))])"
      using wk rt fm_vals_typed adwk fms smd by simp

    with interp_eq make_eq ty_eq show ?thesis
      using sound_term_result.simps(2) by auto
  qed
qed


(*-----------------------------------------------------------------------------*)
(* Main type soundness theorem *)
(*-----------------------------------------------------------------------------*)

theorem type_soundness:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
  shows interp_term_sound:
    "core_term_type env NotGhost tm = Some ty \<longrightarrow>
      sound_term_result env ty (interp_term fuel state tm)"
  and interp_term_list_sound:
    "map (core_term_type env NotGhost) tms = types \<and>
    list_all (\<lambda>ty. ty \<noteq> None) types \<longrightarrow>
      sound_term_results env (map the types) (interp_term_list fuel state tms)"
  and interp_writable_lvalue_sound:
    "is_writable_lvalue env tm \<and> core_term_type env NotGhost tm = Some ty \<longrightarrow>
      sound_lvalue_result state env storeTyping ty (interp_writable_lvalue fuel state tm)"
  and interp_statement_sound:
    "core_statement_type env NotGhost stmt = Some env' \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement fuel state stmt)"
  and interp_statement_list_sound:
    "core_statement_list_type env NotGhost stmts = Some env' \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement_list fuel state stmts)"
  and interp_function_call_sound:
    "\<lbrakk> fmlookup (TE_Functions env) fnName = Some funInfo;
       FI_Ghost funInfo = NotGhost;
       list_all2 (\<lambda>tm expectedTy.
           case core_term_type env NotGhost tm of
             None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
         argTms (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo));
       retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo);
       length tyArgs = length (FI_TyArgs funInfo);
       list_all (is_well_kinded env) tyArgs;
       list_all (is_runtime_type env) tyArgs;
       \<forall>i < length argTms.
         (snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
          is_writable_lvalue env (argTms ! i))
     \<rbrakk> \<Longrightarrow> sound_function_call_result env storeTyping retTy (interp_function_call fuel state fnName argTms)"
using assms
proof (induction fuel arbitrary: state env storeTyping tm ty tms types fnName argTms stmt env' stmts funInfo tyArgs retTy)
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
    then show ?case by simp
  next
    case 5
    then show ?case by simp
  next
    case 6
    then show ?case by simp
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
      have IH: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                  state_matches_env state' env' storeTyping' \<Longrightarrow>
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
        case (CoreTm_LitArray elemTy elemTms)
        have IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results env' (map the types') (interp_term_list fuel state' tms')"
          by (simp add: Suc.IH(2) "1.prems"(1,2))
        from CoreTm_LitArray show ?thesis
          using type_soundness_lit_array[OF "1.prems"(1,2) IH_list] typing
          by simp
  
      next
        (* Variable/constant lookup *)
        case (CoreTm_Var varName)
        (* From typing, the variable exists in the type env *)
        from typing CoreTm_Var obtain varTy where
          var_lookup: "tyenv_lookup_var env varName = Some varTy" and
          not_ghost: "\<not> tyenv_var_ghost env varName" and
          ty_eq: "ty = varTy"
          by (auto split: option.splits if_splits)
        show ?thesis proof (cases "fmlookup (IS_Locals state) varName")
          case None
          then show ?thesis proof (cases "fmlookup (IS_Refs state) varName")
            case None2: None
            (* Variable must be in Globals. It must be a global in the type env. *)
            (* If it were a local, then non_consts or no_extra would place it in IS_Locals/IS_Refs *)
            show ?thesis
            proof (cases "fmlookup (TE_LocalVars env) varName")
              case (Some localTy)
              (* Local var not in IS_Locals or IS_Refs: contradicts non_consts/no_extra *)
              from var_lookup Some have "varTy = localTy"
                unfolding tyenv_lookup_var_def by simp
              (* If const local, it should still be in IS_Locals or IS_Refs via local_vars_exist *)
              from "1.prems"(1) Some not_ghost
              have "local_var_in_state_with_type state env storeTyping varName localTy"
                unfolding state_matches_env_def local_vars_exist_in_state_def
                by (simp add: tyenv_var_ghost_def)
              with None None2 show ?thesis
                unfolding local_var_in_state_with_type_def
                by (auto split: option.splits)
            next
              case None3: None
              (* Global variable *)
              from var_lookup None3 have global_lookup: "fmlookup (TE_GlobalVars env) varName = Some varTy"
                unfolding tyenv_lookup_var_def by simp
              from "1.prems"(1) global_lookup not_ghost
              have "global_var_in_state_with_type state env varName varTy"
                unfolding state_matches_env_def global_vars_exist_in_state_def
                by (simp add: None3 tyenv_var_ghost_def)
              then obtain val where
                const_lookup: "fmlookup (IS_Globals state) varName = Some val"
                and val_typed: "value_has_type env val varTy"
                unfolding global_var_in_state_with_type_def
                by (auto split: option.splits)
              have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName) = Inr val"
                using CoreTm_Var None None2 const_lookup by simp
              then show ?thesis using val_typed CoreTm_Var ty_eq by simp
            qed
          next
            case (Some addrPath)
            (* Variable is a ref - need to dereference *)
            obtain addr path where addrPath_eq: "addrPath = (addr, path)"
              by (cases addrPath) auto
            (* Must be a local var *)
            from var_lookup obtain localTy where
              local_or_global: "fmlookup (TE_LocalVars env) varName = Some localTy \<or>
                fmlookup (TE_GlobalVars env) varName = Some localTy"
              and ty_local: "varTy = localTy"
              unfolding tyenv_lookup_var_def by (auto split: option.splits)
            (* It's in IS_Refs, so it must be a non-ghost local.
               Proof by contrapositive of no_extra_local_vars: if varName were not in
               TE_LocalVars (or were ghost), then it would not be in IS_Refs. *)
            from "1.prems"(1) have nel: "no_extra_local_vars state env"
              unfolding state_matches_env_def by simp
            from Some have refs_some: "fmlookup (IS_Refs state) varName \<noteq> None" by simp
            have local_lookup: "fmlookup (TE_LocalVars env) varName \<noteq> None"
            proof (rule ccontr)
              assume "\<not> fmlookup (TE_LocalVars env) varName \<noteq> None"
              hence "fmlookup (TE_LocalVars env) varName = None" by simp
              with nel have "fmlookup (IS_Refs state) varName = None"
                unfolding no_extra_local_vars_def by blast
              with refs_some show False by simp
            qed
            then obtain localTy' where local_eq: "fmlookup (TE_LocalVars env) varName = Some localTy'"
              by auto
            from "1.prems"(1) local_eq not_ghost
            have local_in_state: "local_var_in_state_with_type state env storeTyping varName localTy'"
              unfolding state_matches_env_def local_vars_exist_in_state_def
              by (metis no_extra_local_vars_def refs_some)
            from var_lookup local_eq have "varTy = localTy'"
              unfolding tyenv_lookup_var_def by simp
            from local_in_state None Some addrPath_eq have
              addr_valid: "addr < length (IS_Store state)" and
              path_ty: "type_at_path env (storeTyping ! addr) path = Some localTy'"
              unfolding local_var_in_state_with_type_def
              by (auto split: option.splits)
            from state_env addr_valid
            have slot_typed: "value_has_type env (IS_Store state ! addr) (storeTyping ! addr)"
              unfolding state_matches_env_def store_well_typed_def
              using "1.prems"(1) state_matches_env_def store_well_typed_def by blast
            show ?thesis
            proof (cases "get_value_at_path (IS_Store state ! addr) path")
              case (Inl err)
              \<comment> \<open>Dangling ref: by get_value_at_path_error_is_runtime, must be RuntimeError.\<close>
              from get_value_at_path_error_is_runtime[OF slot_typed path_ty Inl]
              have err_eq: "err = RuntimeError" .
              have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName) = Inl RuntimeError"
                using CoreTm_Var None Some addrPath_eq Inl err_eq by simp
              then show ?thesis using CoreTm_Var by simp
            next
              case (Inr v)
              \<comment> \<open>Live ref: by get_value_at_path_type, value has type ty.\<close>
              from get_value_at_path_type[OF slot_typed Inr] obtain pathTy where
                "type_at_path env (storeTyping ! addr) path = Some pathTy"
                and v_typed: "value_has_type env v pathTy"
                by auto
              with path_ty have "value_has_type env v localTy'" by simp
              have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName) = Inr v"
                using CoreTm_Var None Some addrPath_eq Inr by simp
              then show ?thesis using \<open>value_has_type env v localTy'\<close> CoreTm_Var
                ty_eq \<open>varTy = localTy'\<close> by simp
            qed
          qed
        next
          case (Some addr)
          then have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName)
                                      = Inr (IS_Store state ! addr)"
            using CoreTm_Var by simp
          (* Must be a local var *)
          from var_lookup obtain localTy where
            local_eq: "fmlookup (TE_LocalVars env) varName = Some localTy"
            and local_ty: "varTy = localTy"
            unfolding tyenv_lookup_var_def
          proof (cases "fmlookup (TE_LocalVars env) varName")
            case lSome: (Some lt)
            then show ?thesis using that var_lookup unfolding tyenv_lookup_var_def by simp
          next
            case lNone: None
            (* If global, no_extra_global_vars says it's not in IS_Locals when ghost,
               and global_vars_exist says it's in IS_Globals. But we know it's in IS_Locals.
               From no_extra_local_vars: varName not in TE_LocalVars \<Longrightarrow> not in IS_Locals.
               Contradiction. *)
            from "1.prems"(1) lNone have "fmlookup (IS_Locals state) varName = None"
              unfolding state_matches_env_def no_extra_local_vars_def by simp
            with Some show ?thesis by simp
          qed
          from "1.prems"(1) local_eq not_ghost
          have local_in_state: "local_var_in_state_with_type state env storeTyping varName localTy"
            unfolding state_matches_env_def local_vars_exist_in_state_def
            by (simp add: tyenv_var_ghost_def)
          from local_in_state Some have addr_valid: "addr < length (IS_Store state)"
            and st_eq: "storeTyping ! addr = localTy"
            unfolding local_var_in_state_with_type_def by auto
          from state_env addr_valid st_eq
          have "value_has_type env (IS_Store state ! addr) localTy"
            unfolding state_matches_env_def store_well_typed_def
            using "1.prems"(1) state_matches_env_def store_well_typed_def by blast
          then show ?thesis
            using CoreTm_Var interp_result ty_eq local_ty by auto
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
        case (CoreTm_FunctionCall fnName tyArgs tmArgs)
        \<comment> \<open>Extract typing facts. We need all_var and not_impure below (for
            the purity proof), which are only produced on the pure path, so
            destructure core_term_type directly rather than via the shared
            helper. \<close>
        from typing CoreTm_FunctionCall obtain funInfo where
          fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
          len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
          tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
          all_var: "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)" and
          not_impure: "\<not> FI_Impure funInfo" and
          len_tmargs: "length tmArgs = length (FI_TmArgs funInfo)" and
          tyargs_rt: "list_all (is_runtime_type env) tyArgs" and
          ghost_ok2: "FI_Ghost funInfo \<noteq> Ghost"
          by (auto simp: Let_def split: option.splits if_splits)
        let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
        let ?expectedArgTypes = "map (\<lambda>(_, ty, _). apply_subst ?tySubst ty) (FI_TmArgs funInfo)"
        from typing CoreTm_FunctionCall fn_lookup len_tyargs tyargs_wk all_var not_impure
             len_tmargs tyargs_rt ghost_ok2 have
          args_check: "list_all2 (\<lambda>tm expectedTy.
              case core_term_type env NotGhost tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
            tmArgs ?expectedArgTypes" and
          ty_eq: "ty = apply_subst ?tySubst (FI_ReturnType funInfo)"
          by (auto simp: Let_def split: if_splits)
        have fn_not_ghost: "FI_Ghost funInfo = NotGhost"
          using ghost_ok2 by (cases "FI_Ghost funInfo") auto
        \<comment> \<open>Vacuous lvalue obligation: all args are Var. \<close>
        have ref_lvalues: "\<forall>i < length tmArgs.
                            snd (snd (FI_TmArgs funInfo ! i)) = Ref
                              \<longrightarrow> is_writable_lvalue env (tmArgs ! i)"
        proof (intro allI impI)
          fix i assume i_lt: "i < length tmArgs"
            and is_ref: "snd (snd (FI_TmArgs funInfo ! i)) = Ref"
          with len_tmargs have i_lt_fi: "i < length (FI_TmArgs funInfo)" by simp
          obtain n ti vor where fi_arg: "FI_TmArgs funInfo ! i = (n, ti, vor)"
            by (cases "FI_TmArgs funInfo ! i") auto
          from is_ref fi_arg have vor_eq: "vor = Ref" by simp
          from all_var i_lt_fi fi_arg
          have "(\<lambda>(_, _, vor). vor = Var) (n, ti, vor)"
            by (metis list_all_length)
          hence "vor = Var" by simp
          with vor_eq have False by simp
          thus "is_writable_lvalue env (tmArgs ! i)" by simp
        qed
        \<comment> \<open>Use interp_function_call_sound IH\<close>
        have IH_fc: "\<And>env' (state' :: 'w InterpState) storeTyping' fnName' argTms' funInfo' tyArgs' retTy'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                fmlookup (TE_Functions env') fnName' = Some funInfo' \<Longrightarrow>
                FI_Ghost funInfo' = NotGhost \<Longrightarrow>
                list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env' NotGhost tm of
                      None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  argTms' (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo') tyArgs')) ty)
                               (FI_TmArgs funInfo')) \<Longrightarrow>
                retTy' = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo') tyArgs')) (FI_ReturnType funInfo') \<Longrightarrow>
                length tyArgs' = length (FI_TyArgs funInfo') \<Longrightarrow>
                list_all (is_well_kinded env') tyArgs' \<Longrightarrow>
                list_all (is_runtime_type env') tyArgs' \<Longrightarrow>
                \<forall>i < length argTms'.
                  (snd (snd (FI_TmArgs funInfo' ! i)) = Ref \<longrightarrow>
                   is_writable_lvalue env' (argTms' ! i)) \<Longrightarrow>
                sound_function_call_result env' storeTyping' retTy' (interp_function_call fuel state' fnName' argTms')"
          using Suc.IH(6) by simp
        have fc_sound: "sound_function_call_result env storeTyping ty
                          (interp_function_call fuel state fnName tmArgs)"
          using IH_fc[OF "1.prems"(1,2) fn_lookup fn_not_ghost args_check ty_eq
                          len_tyargs tyargs_wk tyargs_rt ref_lvalues]
          by simp
        \<comment> \<open>The interpreter checks is_pure_fun then calls interp_function_call\<close>
        have pure: "is_pure_fun state fnName"
        proof -
          have "FI_Ghost funInfo = NotGhost" using ghost_ok2 by (cases "FI_Ghost funInfo") auto
          from "1.prems"(1) fn_lookup this obtain interpFun where
            if_lookup: "fmlookup (IS_Functions state) fnName = Some interpFun" and
            fi_match: "fun_info_matches_interp_fun env funInfo interpFun"
            unfolding state_matches_env_def funs_exist_in_state_def
            using case_optionE by blast
          from fi_match have len_eq: "length (FI_TmArgs funInfo) = length (IF_Args interpFun)"
            and vor_match: "list_all2 (\<lambda>(name1, _, vor1) (name2, vor2). name1 = name2 \<and> vor1 = vor2)
                                      (FI_TmArgs funInfo) (IF_Args interpFun)"
            unfolding fun_info_matches_interp_fun_def by auto
          have "\<not> list_ex (\<lambda>(_, vr). vr = Ref) (IF_Args interpFun)"
          proof -
            have "\<And>i. i < length (IF_Args interpFun) \<Longrightarrow> snd (IF_Args interpFun ! i) = Var"
            proof -
              fix i assume i_bound: "i < length (IF_Args interpFun)"
              obtain n a b where nab: "FI_TmArgs funInfo ! i = (n, a, b)"
                by (cases "FI_TmArgs funInfo ! i") auto
              from vor_match i_bound len_eq nab
              have "b = snd (IF_Args interpFun ! i)"
                using list_all2_nthD by fastforce
              moreover have "b = Var"
                using all_var i_bound len_eq nab by (auto simp: list_all_length)
              ultimately show "snd (IF_Args interpFun ! i) = Var" by simp
            qed
            thus ?thesis
              by (fastforce simp: list_ex_iff in_set_conv_nth split: prod.splits)
          qed
          moreover from fi_match not_impure have "\<not> IF_Impure interpFun"
            unfolding fun_info_matches_interp_fun_def by simp
          ultimately show ?thesis using if_lookup by simp
        qed
        show ?thesis
        proof (cases "interp_function_call fuel state fnName tmArgs")
          case (Inl err)
          from fc_sound Inl have "sound_error_result err" by simp
          moreover have "interp_term (Suc fuel) state tm = Inl err"
            using CoreTm_FunctionCall Inl pure by simp
          ultimately show ?thesis by simp
        next
          case (Inr result)
          obtain newState retVal where result_eq: "result = (newState, retVal)"
            by (cases result) auto
          from fc_sound Inr result_eq have "value_has_type env retVal ty" by simp
          moreover have "interp_term (Suc fuel) state tm = Inr retVal"
            using CoreTm_FunctionCall Inr result_eq pure by simp
          ultimately show ?thesis by simp
        qed
      next
        case (CoreTm_VariantCtor x111 x112 x113)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_variant_ctor typing by blast
      next
        case (CoreTm_Record x12)
        have IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results env' (map the types') (interp_term_list fuel state' tms')"
          by (simp add: Suc.IH(2) "1.prems"(1,2))
        from CoreTm_Record show ?thesis
          using type_soundness_record[OF "1.prems"(1,2) IH_list] typing
          by fastforce
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
        have IH_term: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result env' ty' (interp_term fuel state' tm')"
          by (simp add: Suc.IH(1) "1.prems"(1,2))
        have IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results env' (map the types') (interp_term_list fuel state' tms')"
          by (simp add: Suc.IH(2) "1.prems"(1,2))
        from CoreTm_ArrayProj show ?thesis
          using type_soundness_array_proj[OF "1.prems"(1,2) IH_term IH_list] typing
          by fastforce
      next
        case (CoreTm_Match x161 x162)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_match typing by blast
      next
        case (CoreTm_Sizeof x17)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_sizeof typing by blast
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
        have head_sound: "sound_term_result env tm_ty (interp_term fuel state tm)"
          using tm_typing
          using "2.prems"(1,2) Suc.IH(1) by auto

        (* Use IH for the tail list *)
        have tail_sound: "sound_term_results env (map the types') (interp_term_list fuel state tms')"
          using "2.prems"(1,2) Suc.IH(2) all_typed' types'_eq by auto

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
    (* interp_writable_lvalue_sound *)
    case 3
    show ?case proof (intro impI, elim conjE)
      assume writable: "is_writable_lvalue env tm"
        and typing: "core_term_type env NotGhost tm = Some ty"

      have IH_lvalue: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                is_writable_lvalue env' tm' \<and> core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_lvalue_result state' env' storeTyping' ty' (interp_writable_lvalue fuel state' tm')"
        by (simp add: Suc.IH(3) "3.prems"(1,2))

      have IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results env' (map the types') (interp_term_list fuel state' tms')"
        by (simp add: Suc.IH(2) "3.prems"(1,2))

      show "sound_lvalue_result state env storeTyping ty (interp_writable_lvalue (Suc fuel) state tm)"
      proof (cases tm)
        (* CoreTm_Var: base case for lvalues *)
        case (CoreTm_Var varName)
        from typing CoreTm_Var obtain varTy where
          var_lookup: "tyenv_lookup_var env varName = Some varTy" and
          not_ghost: "\<not> tyenv_var_ghost env varName" and
          ty_eq: "ty = varTy"
          by (auto split: option.splits if_splits)
        (* Variable is writable, so it must be a non-const local *)
        from writable CoreTm_Var have writable_var: "tyenv_var_writable env varName" by simp
        hence local_lookup: "fmlookup (TE_LocalVars env) varName \<noteq> None"
          and not_const: "varName |\<notin>| TE_ConstLocals env"
          unfolding tyenv_var_writable_def by auto
        (* Since it's a local, not_ghost means not in TE_GhostLocals *)
        from not_ghost local_lookup have not_ghost_local: "varName |\<notin>| TE_GhostLocals env"
          unfolding tyenv_var_ghost_def by (auto split: option.splits)
        (* Variable is in IS_Locals or IS_Refs *)
        from "3.prems"(1) local_lookup not_ghost_local not_const
        have in_locals_or_refs:
          "fmlookup (IS_Locals state) varName \<noteq> None \<or>
           fmlookup (IS_Refs state) varName \<noteq> None"
          unfolding state_matches_env_def non_consts_in_locals_or_refs_def by blast
        (* Variable has correct type in state as a local *)
        from local_lookup obtain localTy where
          local_lookup_eq: "fmlookup (TE_LocalVars env) varName = Some localTy" by auto
        from var_lookup local_lookup_eq have ty_local: "localTy = varTy"
          unfolding tyenv_lookup_var_def by simp
        have var_in_state: "local_var_in_state_with_type state env storeTyping varName ty"
          using "3.prems"(1) local_lookup_eq not_ghost ty_eq ty_local
          unfolding state_matches_env_def local_vars_exist_in_state_def
          by (simp add: not_ghost_local)
        from "3.prems"(1) not_const have not_const_state: "varName |\<notin>| IS_ConstLocals state"
          unfolding state_matches_env_def const_locals_match_def by simp
        show ?thesis
        proof (cases "fmlookup (IS_Locals state) varName")
          case (Some addr)
          then have interp_eq: "interp_writable_lvalue (Suc fuel) state tm = Inr (addr, [])"
            using CoreTm_Var not_const_state by simp
          from var_in_state Some have
            addr_valid: "addr < length (IS_Store state)" and
            st_eq: "storeTyping ! addr = ty"
            unfolding local_var_in_state_with_type_def by auto
          from st_eq have "type_at_path env (storeTyping ! addr) [] = Some ty" by simp
          with interp_eq addr_valid show ?thesis by simp
        next
          case None
          (* Must be in IS_Refs *)
          from in_locals_or_refs None have "fmlookup (IS_Refs state) varName \<noteq> None" by simp
          then obtain addrPath where refs_lookup: "fmlookup (IS_Refs state) varName = Some addrPath"
            by auto
          obtain addr path where addrPath_eq: "addrPath = (addr, path)"
            by (cases addrPath) auto
          then have interp_eq: "interp_writable_lvalue (Suc fuel) state tm = Inr (addr, path)"
            using CoreTm_Var None refs_lookup not_const_state by simp
          from var_in_state None refs_lookup addrPath_eq have
            addr_valid: "addr < length (IS_Store state)" and
            path_ty: "type_at_path env (storeTyping ! addr) path = Some ty"
            unfolding local_var_in_state_with_type_def
            by (auto split: option.splits)
          with interp_eq show ?thesis by simp
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
        have inner_sound: "sound_lvalue_result state env storeTyping (CoreTy_Record fieldTypes)
                             (interp_writable_lvalue fuel state innerTm)"
          by simp
        show ?thesis
        proof (cases "interp_writable_lvalue fuel state innerTm")
          case (Inl err)
          then have "interp_writable_lvalue (Suc fuel) state tm = Inl err"
            using CoreTm_RecordProj by simp
          with inner_sound Inl show ?thesis by auto
        next
          case (Inr addrPath)
          obtain addr path where ap_eq: "addrPath = (addr, path)" by (cases addrPath) auto
          from inner_sound Inr ap_eq have
            addr_valid: "addr < length (IS_Store state)" and
            inner_path_ty: "type_at_path env (storeTyping ! addr) path = Some (CoreTy_Record fieldTypes)"
            by auto
          have interp_eq: "interp_writable_lvalue (Suc fuel) state tm =
              Inr (addr, path @ [LVPath_RecordProj fldName])"
            using CoreTm_RecordProj Inr ap_eq by simp
          (* type_at_path extends: appending a RecordProj step descends into fieldTypes *)
          have "type_at_path env (storeTyping ! addr)
                  (path @ [LVPath_RecordProj fldName]) = Some ty"
            using type_at_path_append[OF inner_path_ty] fld_lookup by simp
          with interp_eq addr_valid show ?thesis by simp
        qed
      next
        (* CoreTm_VariantProj: extend path with variant projection *)
        case (CoreTm_VariantProj innerTm ctorName)
        from typing CoreTm_VariantProj obtain dtName tyArgs dtName2 tyvars payloadTy where
          inner_typing: "core_term_type env NotGhost innerTm = Some (CoreTy_Datatype dtName tyArgs)" and
          ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, tyvars, payloadTy)" and
          dt_eq: "dtName = dtName2" and
          len_eq: "length tyArgs = length tyvars" and
          ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
          by (auto split: option.splits CoreType.splits prod.splits if_splits)
        from writable CoreTm_VariantProj have inner_writable: "is_writable_lvalue env innerTm"
          by simp
        from IH_lvalue[OF "3.prems"(1,2)] inner_writable inner_typing
        have inner_sound: "sound_lvalue_result state env storeTyping (CoreTy_Datatype dtName tyArgs)
                             (interp_writable_lvalue fuel state innerTm)"
          by simp
        show ?thesis
        proof (cases "interp_writable_lvalue fuel state innerTm")
          case (Inl err)
          then have "interp_writable_lvalue (Suc fuel) state tm = Inl err"
            using CoreTm_VariantProj by simp
          with inner_sound Inl show ?thesis by auto
        next
          case (Inr addrPath)
          obtain addr path where ap_eq: "addrPath = (addr, path)" by (cases addrPath) auto
          from inner_sound Inr ap_eq have
            addr_valid: "addr < length (IS_Store state)" and
            inner_path_ty: "type_at_path env (storeTyping ! addr) path
                            = Some (CoreTy_Datatype dtName tyArgs)"
            by auto
          have interp_eq: "interp_writable_lvalue (Suc fuel) state tm =
              Inr (addr, path @ [LVPath_VariantProj ctorName])"
            using CoreTm_VariantProj Inr ap_eq by simp
          (* Append the variant projection step to the path *)
          have "type_at_path env (storeTyping ! addr)
                  (path @ [LVPath_VariantProj ctorName]) = Some ty"
            using type_at_path_append[OF inner_path_ty] ctor_lookup dt_eq ty_eq by simp
          with interp_eq addr_valid show ?thesis by simp
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
        have inner_sound: "sound_lvalue_result state env storeTyping (CoreTy_Array elemTy dims)
                             (interp_writable_lvalue fuel state innerTm)"
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
        proof (cases "interp_writable_lvalue fuel state innerTm")
          case (Inl err)
          then have "interp_writable_lvalue (Suc fuel) state tm = Inl err"
            using CoreTm_ArrayProj by simp
          with inner_sound Inl show ?thesis by auto
        next
          case (Inr addrPath)
          obtain addr path where ap_eq: "addrPath = (addr, path)" by (cases addrPath) auto
          from inner_sound Inr ap_eq have
            addr_valid: "addr < length (IS_Store state)" and
            inner_path_ty: "type_at_path env (storeTyping ! addr) path
                            = Some (CoreTy_Array elemTy dims)"
            by auto
          show ?thesis
          proof (cases "interp_term_list fuel state idxTms")
            case (Inl err)
            then have "interp_writable_lvalue (Suc fuel) state tm = Inl err"
              using CoreTm_ArrayProj \<open>interp_writable_lvalue fuel state innerTm = Inr addrPath\<close>
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
            have interp_eq: "interp_writable_lvalue (Suc fuel) state tm =
                Inr (addr, path @ [LVPath_ArrayProj indices])"
              using CoreTm_ArrayProj \<open>interp_writable_lvalue fuel state innerTm = Inr addrPath\<close>
                    ap_eq Inr interp_idx_eq by simp
            (* Append the array projection step to the path *)
            have "type_at_path env (storeTyping ! addr)
                    (path @ [LVPath_ArrayProj indices]) = Some ty"
              using type_at_path_append[OF inner_path_ty] ty_eq by simp
            with interp_eq addr_valid show ?thesis by simp
          qed
        qed
      (* Non-lvalue cases are contradictions since is_writable_lvalue returns False *)
      qed (use writable in \<open>simp_all\<close>)
    qed
  next
    case 4
    show ?case proof (intro impI)
      assume typing: "core_statement_type env NotGhost stmt = Some env'"
      have IH_term: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 tm0 ty0.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                core_term_type env0 NotGhost tm0 = Some ty0 \<Longrightarrow>
                sound_term_result env0 ty0 (interp_term fuel state0 tm0)"
        by (simp add: "4.prems"(1,2) Suc.IH(1))
      have IH_lvalue: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 tm0 ty0.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                is_writable_lvalue env0 tm0 \<and> core_term_type env0 NotGhost tm0 = Some ty0 \<Longrightarrow>
                sound_lvalue_result state0 env0 storeTyping0 ty0 (interp_writable_lvalue fuel state0 tm0)"
        by (simp add: "4.prems"(1,2) Suc.IH(3))
      have IH_fc: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 fnName0 argTms0 funInfo0 tyArgs0 retTy0.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                fmlookup (TE_Functions env0) fnName0 = Some funInfo0 \<Longrightarrow>
                FI_Ghost funInfo0 = NotGhost \<Longrightarrow>
                list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env0 NotGhost tm of
                      None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  argTms0 (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo0) tyArgs0)) ty)
                               (FI_TmArgs funInfo0)) \<Longrightarrow>
                retTy0 = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo0) tyArgs0)) (FI_ReturnType funInfo0) \<Longrightarrow>
                length tyArgs0 = length (FI_TyArgs funInfo0) \<Longrightarrow>
                list_all (is_well_kinded env0) tyArgs0 \<Longrightarrow>
                list_all (is_runtime_type env0) tyArgs0 \<Longrightarrow>
                \<forall>i < length argTms0.
                  (snd (snd (FI_TmArgs funInfo0 ! i)) = Ref \<longrightarrow>
                   is_writable_lvalue env0 (argTms0 ! i)) \<Longrightarrow>
                sound_function_call_result env0 storeTyping0 retTy0 (interp_function_call fuel state0 fnName0 argTms0)"
        using Suc.IH(6) by simp
      show "sound_statement_result env env' storeTyping (interp_statement (Suc fuel) state stmt)"
      proof (cases stmt)
        case (CoreStmt_VarDecl declGhost varName varOrRef varTy initTm)
        then show ?thesis proof (cases varOrRef)
          case Var
          then show ?thesis proof (cases declGhost)
            case NotGhost
            \<comment> \<open>NotGhost Var VarDecl: evaluates initTm (via interp_function_call
                if it's a CoreTm_FunctionCall, else via interp_term), then
                alloc_store + fmupd for the new local. The rhs may be an
                impure function call (typechecked via core_impure_call_type)
                or a plain term (typechecked via core_term_type). \<close>
            from typing CoreStmt_VarDecl Var NotGhost have init_ty_disj:
              "core_impure_call_type env NotGhost initTm = Some varTy
               \<or> core_term_type env NotGhost initTm = Some varTy"
              by (auto split: if_splits)
            from typing CoreStmt_VarDecl Var NotGhost have env'_eq:
              "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                            TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                            TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
              by (auto split: if_splits)

            \<comment> \<open>Normalize the disjunction via the shared helper. \<close>
            note fn_call_facts_or_pure = fn_call_facts_from_disjunct[OF init_ty_disj]

            show ?thesis
            proof (cases "\<exists>fnName tyArgs argTms. initTm = CoreTm_FunctionCall fnName tyArgs argTms")
              case True
              \<comment> \<open>Function-call initTm: use IH_fc and alloc_store newState. \<close>
              then obtain fnName tyArgs argTms where initTm_eq:
                "initTm = CoreTm_FunctionCall fnName tyArgs argTms" by auto
              from fn_call_facts_or_pure initTm_eq obtain funInfo fnName' tyArgs' argTms' where
                initTm_eq': "initTm = CoreTm_FunctionCall fnName' tyArgs' argTms'" and
                fn_lookup: "fmlookup (TE_Functions env) fnName' = Some funInfo" and
                len_tyargs: "length tyArgs' = length (FI_TyArgs funInfo)" and
                tyargs_wk: "list_all (is_well_kinded env) tyArgs'" and
                tyargs_rt: "list_all (is_runtime_type env) tyArgs'" and
                fn_not_ghost: "FI_Ghost funInfo = NotGhost" and
                len_tmargs: "length argTms' = length (FI_TmArgs funInfo)" and
                args_check: "list_all2 (\<lambda>tm expectedTy.
                               case core_term_type env NotGhost tm of
                                 None \<Rightarrow> False
                               | Some actualTy \<Rightarrow> actualTy = expectedTy)
                             argTms'
                             (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs')) ty)
                                  (FI_TmArgs funInfo))" and
                fn_ty_eq: "varTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs'))
                                               (FI_ReturnType funInfo)" and
                ref_lvalues: "\<forall>i < length argTms'.
                                snd (snd (FI_TmArgs funInfo ! i)) = Ref
                                  \<longrightarrow> is_writable_lvalue env (argTms' ! i)"
                by blast
              from initTm_eq initTm_eq' have name_eqs:
                "fnName' = fnName" "tyArgs' = tyArgs" "argTms' = argTms"
                by auto
              note fn_lookup = fn_lookup[unfolded name_eqs]
              note len_tyargs = len_tyargs[unfolded name_eqs]
              note tyargs_wk = tyargs_wk[unfolded name_eqs]
              note tyargs_rt = tyargs_rt[unfolded name_eqs]
              note len_tmargs = len_tmargs[unfolded name_eqs]
              note args_check = args_check[unfolded name_eqs]
              note fn_ty_eq = fn_ty_eq[unfolded name_eqs]
              note ref_lvalues = ref_lvalues[unfolded name_eqs]
              from IH_fc[OF "4.prems"(1,2) fn_lookup fn_not_ghost args_check fn_ty_eq
                            len_tyargs tyargs_wk tyargs_rt ref_lvalues]
              have fc_sound: "sound_function_call_result env storeTyping varTy
                  (interp_function_call fuel state fnName argTms)" .
              show ?thesis
              proof (cases "interp_function_call fuel state fnName argTms")
                case (Inl err)
                with fc_sound have err_sound: "sound_error_result err" by simp
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Var varTy initTm) = Inl err"
                  using Inl initTm_eq by simp
                with err_sound CoreStmt_VarDecl Var NotGhost show ?thesis by simp
              next
                case (Inr fcResult)
                obtain newState initialVal where fcResult_eq: "fcResult = (newState, initialVal)"
                  by (cases fcResult) auto
                from fc_sound Inr fcResult_eq obtain storeTyping1 where
                  new_sme: "state_matches_env newState env storeTyping1" and
                  ext1: "storeTyping_extends storeTyping storeTyping1" and
                  val_typed: "value_has_type env initialVal varTy"
                  by auto
                \<comment> \<open>Now alloc_store newState and fmupd the new local. \<close>
                obtain state' addr where alloc_eq:
                  "(state', addr) = alloc_store newState initialVal"
                  by (cases "alloc_store newState initialVal") auto
                let ?state'' = "state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state'),
                                         IS_Refs := fmdrop varName (IS_Refs state'),
                                         IS_ConstLocals := fminus (IS_ConstLocals state') {|varName|} \<rparr>"
                have interp_eq: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Var varTy initTm) = Inr (Continue ?state'')"
                  using Inr fcResult_eq alloc_eq initTm_eq
                  by (simp add: case_prod_beta)
                \<comment> \<open>Extend storeTyping1 by [varTy] to get the new storeTyping. \<close>
                from state_matches_env_add_nonconst_local[OF new_sme val_typed
                    alloc_eq refl env'_eq]
                have new_sme_ext: "state_matches_env ?state'' env' (storeTyping1 @ [varTy])" .
                have ext2: "storeTyping_extends storeTyping1 (storeTyping1 @ [varTy])"
                  using storeTyping_extends_append .
                have ext_total: "storeTyping_extends storeTyping (storeTyping1 @ [varTy])"
                  using storeTyping_extends_trans[OF ext1 ext2] .
                from new_sme_ext ext_total interp_eq CoreStmt_VarDecl Var NotGhost
                show ?thesis by auto
              qed
            next
              case False
              \<comment> \<open>Non-function-call initTm: use IH_term, alloc_store state. \<close>
              hence not_fc: "\<And>fnName tyArgs argTms.
                  initTm \<noteq> CoreTm_FunctionCall fnName tyArgs argTms" by auto
              from fn_call_facts_or_pure not_fc have init_ty:
                "core_term_type env NotGhost initTm = Some varTy" by blast
              from IH_term[OF "4.prems"(1,2) init_ty]
              have init_sound: "sound_term_result env varTy (interp_term fuel state initTm)" .
              show ?thesis
              proof (cases "interp_term fuel state initTm")
                case (Inl err)
                with init_sound have err_sound: "sound_error_result err" by simp
                from Inl not_fc have interp_err:
                  "interp_statement (Suc fuel) state
                      (CoreStmt_VarDecl NotGhost varName Var varTy initTm) = Inl err"
                  by (cases initTm) auto
                with err_sound CoreStmt_VarDecl Var NotGhost show ?thesis by simp
              next
                case (Inr initialVal)
                from init_sound Inr have val_typed: "value_has_type env initialVal varTy" by simp
                obtain state' addr where alloc_eq: "(state', addr) = alloc_store state initialVal"
                  by (cases "alloc_store state initialVal") auto
                let ?state'' = "state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state'),
                                         IS_Refs := fmdrop varName (IS_Refs state'),
                                         IS_ConstLocals := fminus (IS_ConstLocals state') {|varName|} \<rparr>"
                have interp_eq: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Var varTy initTm) =
                    Inr (Continue ?state'')"
                  using Inr alloc_eq not_fc
                  by (cases initTm) (auto simp: case_prod_beta split: prod.splits)
                have new_sme: "state_matches_env ?state'' env' (storeTyping @ [varTy])"
                  using state_matches_env_add_nonconst_local[OF "4.prems"(1) val_typed
                      alloc_eq refl env'_eq] .
                have ext: "storeTyping_extends storeTyping (storeTyping @ [varTy])"
                  using storeTyping_extends_append .
                from new_sme ext interp_eq CoreStmt_VarDecl Var NotGhost
                show ?thesis by auto
              qed
            qed
          next
            case Ghost
            \<comment> \<open>Ghost Var VarDecl: interpreter drops the variable from IS_Locals/IS_Refs\<close>
            (* Extract facts from typechecking *)
            from typing CoreStmt_VarDecl Var Ghost have
              env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := finsert varName (TE_GhostLocals env),
                                     TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
              by (auto split: if_splits)
            (* The interpreter drops varName from IS_Locals, IS_Refs, IS_ConstLocals *)
            let ?state' = "state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
                                   IS_Refs := fmdrop varName (IS_Refs state),
                                   IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"
            have interp_eq: "interp_statement (Suc fuel) state
                (CoreStmt_VarDecl Ghost varName Var varTy initTm) = Inr (Continue ?state')"
              by simp
            (* Prove state_matches_env for the modified state and extended env.
               varName is ghost in env', so it must be absent from IS_Locals/IS_Refs
               (which fmdrop ensures). All other variables are unchanged. *)
            from "4.prems"(1) have
              old_sme: "state_matches_env state env storeTyping" .
            have env'_fields: "TE_DataCtors env' = TE_DataCtors env"
                              "TE_Datatypes env' = TE_Datatypes env"
                              "TE_TypeVars env' = TE_TypeVars env"
                              "TE_GhostDatatypes env' = TE_GhostDatatypes env"
                              "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
              using env'_eq by simp_all
            have vht_eq: "\<And>v t. value_has_type env' v t = value_has_type env v t"
              using value_has_type_cong_env[OF env'_fields] .
            have tap_eq: "\<And>t p. type_at_path env t p = type_at_path env' t p"
              using type_at_path_cong_env[OF env'_fields(1)] .
            have "state_matches_env ?state' env' storeTyping"
              unfolding state_matches_env_def
            proof (intro conjI)
              (* local_vars_exist: non-ghost locals in env' must be in ?state'.
                 varName is ghost in env' so excluded. Others are in env (non-ghost)
                 so in state, and fmdrop doesn't affect them. *)
              show "local_vars_exist_in_state ?state' env' storeTyping"
                unfolding local_vars_exist_in_state_def
              proof (intro allI impI, elim conjE)
                fix name ty
                assume lk: "fmlookup (TE_LocalVars env') name = Some ty"
                  and ng: "name |\<notin>| TE_GhostLocals env'"
                from ng env'_eq have "name \<noteq> varName" by auto
                with lk env'_eq have lk_old: "fmlookup (TE_LocalVars env) name = Some ty" by simp
                from ng env'_eq \<open>name \<noteq> varName\<close> have ng_old: "name |\<notin>| TE_GhostLocals env" by auto
                from old_sme lk_old ng_old
                have "local_var_in_state_with_type state env storeTyping name ty"
                  unfolding state_matches_env_def local_vars_exist_in_state_def by blast
                with \<open>name \<noteq> varName\<close> tap_eq show "local_var_in_state_with_type ?state' env' storeTyping name ty"
                  unfolding local_var_in_state_with_type_def
                  by (auto split: option.splits)
              qed
            next
              (* global_vars_exist: globals unchanged (TE_GlobalVars and TE_GhostGlobals same).
                 IS_Globals is unchanged (?state' only modifies IS_Locals/IS_Refs). *)
              show "global_vars_exist_in_state ?state' env'"
              proof -
                from old_sme have old_gv: "global_vars_exist_in_state state env"
                  unfolding state_matches_env_def by simp
                have gv_eq: "TE_GlobalVars env' = TE_GlobalVars env" using env'_eq by simp
                have gg_eq: "TE_GhostGlobals env' = TE_GhostGlobals env" using env'_eq by simp
                show ?thesis unfolding global_vars_exist_in_state_def
                proof (intro allI impI, elim conjE)
                  fix name ty
                  assume lk: "fmlookup (TE_GlobalVars env') name = Some ty"
                    and ng: "name |\<notin>| TE_GhostGlobals env'"
                  from lk gv_eq have "fmlookup (TE_GlobalVars env) name = Some ty" by simp
                  moreover from ng gg_eq have "name |\<notin>| TE_GhostGlobals env" by simp
                  ultimately have "global_var_in_state_with_type state env name ty"
                    using old_gv unfolding global_vars_exist_in_state_def by blast
                  thus "global_var_in_state_with_type ?state' env' name ty"
                    using vht_eq unfolding global_var_in_state_with_type_def
                    by (auto split: option.splits)
                qed
              qed
            next
              (* no_extra_local_vars: if not in TE_LocalVars or ghost, not in IS_Locals/IS_Refs.
                 fmdrop removes varName. For others, same as before. *)
              show "no_extra_local_vars ?state' env'"
                unfolding no_extra_local_vars_def
              proof (intro allI impI)
                fix name
                assume ante: "fmlookup (TE_LocalVars env') name = None \<or> name |\<in>| TE_GhostLocals env'"
                show "fmlookup (IS_Locals ?state') name = None \<and>
                      fmlookup (IS_Refs ?state') name = None"
                proof (cases "name = varName")
                  case True
                  then show ?thesis by simp
                next
                  case False
                  from ante False env'_eq
                  have "fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env" by auto
                  with old_sme have "fmlookup (IS_Locals state) name = None \<and>
                      fmlookup (IS_Refs state) name = None"
                    unfolding state_matches_env_def no_extra_local_vars_def by blast
                  with False show ?thesis by simp
                qed
              qed
            next
              show "no_extra_global_vars ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def no_extra_global_vars_def by simp
            next
              show "funs_exist_in_state ?state' env'"
                unfolding funs_exist_in_state_def
              proof (intro allI impI, elim conjE)
                fix name info
                assume lk: "fmlookup (TE_Functions env') name = Some info"
                  and ng: "FI_Ghost info = NotGhost"
                from old_sme have old_fes: "funs_exist_in_state state env"
                  unfolding state_matches_env_def by simp
                have funs_eq: "TE_Functions env' = TE_Functions env" using env'_eq by simp
                from lk funs_eq have lk': "fmlookup (TE_Functions env) name = Some info" by simp
                from old_fes lk' ng obtain interpFun where
                  if_lk: "fmlookup (IS_Functions state) name = Some interpFun" and
                  matches: "fun_info_matches_interp_fun env info interpFun"
                  unfolding funs_exist_in_state_def by (auto split: option.splits)
                have if_lk': "fmlookup (IS_Functions ?state') name = Some interpFun"
                  using if_lk by simp
                have fcong: "fun_info_matches_interp_fun env' info interpFun =
                              fun_info_matches_interp_fun env info interpFun"
                  by (rule fun_info_matches_interp_fun_cong_env)
                     (use env'_eq in simp_all)
                have "fun_info_matches_interp_fun env' info interpFun"
                  using matches fcong by simp
                with if_lk' show "case fmlookup (IS_Functions ?state') name of
                                    None \<Rightarrow> False
                                  | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env' info interpFun"
                  by simp
              qed
            next
              show "no_extra_funs ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def no_extra_funs_def by simp
            next
              (* non_consts_in_locals_or_refs: non-ghost non-const locals must be in
                 IS_Locals or IS_Refs. varName is ghost so excluded. Others: same as before. *)
              show "non_consts_in_locals_or_refs ?state' env'"
                unfolding non_consts_in_locals_or_refs_def
              proof (intro allI impI, elim conjE)
                fix name
                assume lk: "fmlookup (TE_LocalVars env') name \<noteq> None"
                  and ng: "name |\<notin>| TE_GhostLocals env'"
                  and nc: "name |\<notin>| TE_ConstLocals env'"
                from ng env'_eq have "name \<noteq> varName" by auto
                with lk env'_eq have "fmlookup (TE_LocalVars env) name \<noteq> None" by simp
                moreover from ng env'_eq \<open>name \<noteq> varName\<close> have "name |\<notin>| TE_GhostLocals env" by auto
                moreover from nc env'_eq \<open>name \<noteq> varName\<close> have "name |\<notin>| TE_ConstLocals env" by auto
                ultimately have "fmlookup (IS_Locals state) name \<noteq> None \<or>
                    fmlookup (IS_Refs state) name \<noteq> None"
                  using old_sme unfolding state_matches_env_def non_consts_in_locals_or_refs_def
                  by blast
                with \<open>name \<noteq> varName\<close> show "fmlookup (IS_Locals ?state') name \<noteq> None \<or>
                    fmlookup (IS_Refs ?state') name \<noteq> None"
                  by simp
              qed
            next
              show "const_locals_match ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def const_locals_match_def by auto
            next
              show "store_well_typed ?state' env' storeTyping"
                using old_sme vht_eq
                unfolding state_matches_env_def store_well_typed_def by simp
            qed
            with CoreStmt_VarDecl Var Ghost show ?thesis
              using interp_eq storeTyping_extends_refl by auto
          qed
        next
          case Ref
          \<comment> \<open>Ref VarDecl: three branches.
              - Ghost: interpreter drops varName from IS_Locals/IS_Refs/IS_ConstLocals.
              - NotGhost + base read-only (in IS_ConstLocals or IS_Globals): copy path,
                use IH_term to get the value, alloc_store, add to IS_ConstLocals.
              - NotGhost + base writable: alias path, use IH_lvalue to get (addr, path),
                update IS_Refs.
              The typechecker decides const-vs-non-const at compile time, but we have to
              show the interpreter's runtime branch matches the static decision. \<close>
          show ?thesis proof (cases declGhost)
            case Ghost
            from typing CoreStmt_VarDecl Ref Ghost have
              env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := finsert varName (TE_GhostLocals env),
                                     TE_ConstLocals := (if is_writable_lvalue env initTm
                                                       then fminus (TE_ConstLocals env) {|varName|}
                                                       else finsert varName (TE_ConstLocals env)) \<rparr>"
              by (auto split: if_splits)
            \<comment> \<open>The interpreter drops varName from IS_Locals, IS_Refs, IS_ConstLocals. \<close>
            let ?state' = "state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
                                   IS_Refs := fmdrop varName (IS_Refs state),
                                   IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"
            have interp_eq: "interp_statement (Suc fuel) state
                (CoreStmt_VarDecl Ghost varName Ref varTy initTm) = Inr (Continue ?state')"
              by simp
            from "4.prems"(1) have
              old_sme: "state_matches_env state env storeTyping" .
            have env'_fields: "TE_DataCtors env' = TE_DataCtors env"
                              "TE_Datatypes env' = TE_Datatypes env"
                              "TE_TypeVars env' = TE_TypeVars env"
                              "TE_GhostDatatypes env' = TE_GhostDatatypes env"
                              "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
              using env'_eq by simp_all
            have vht_eq: "\<And>v t. value_has_type env' v t = value_has_type env v t"
              using value_has_type_cong_env[OF env'_fields] .
            have tap_eq: "\<And>t p. type_at_path env t p = type_at_path env' t p"
              using type_at_path_cong_env[OF env'_fields(1)] .
            have "state_matches_env ?state' env' storeTyping"
              unfolding state_matches_env_def
            proof (intro conjI)
              show "local_vars_exist_in_state ?state' env' storeTyping"
                unfolding local_vars_exist_in_state_def
              proof (intro allI impI, elim conjE)
                fix name ty
                assume lk: "fmlookup (TE_LocalVars env') name = Some ty"
                  and ng: "name |\<notin>| TE_GhostLocals env'"
                from ng env'_eq have "name \<noteq> varName" by auto
                with lk env'_eq have lk_old: "fmlookup (TE_LocalVars env) name = Some ty" by simp
                from ng env'_eq \<open>name \<noteq> varName\<close> have ng_old: "name |\<notin>| TE_GhostLocals env" by auto
                from old_sme lk_old ng_old
                have "local_var_in_state_with_type state env storeTyping name ty"
                  unfolding state_matches_env_def local_vars_exist_in_state_def by blast
                with \<open>name \<noteq> varName\<close> tap_eq show "local_var_in_state_with_type ?state' env' storeTyping name ty"
                  unfolding local_var_in_state_with_type_def
                  by (auto split: option.splits)
              qed
            next
              show "global_vars_exist_in_state ?state' env'"
              proof -
                from old_sme have old_gv: "global_vars_exist_in_state state env"
                  unfolding state_matches_env_def by simp
                have gv_eq: "TE_GlobalVars env' = TE_GlobalVars env" using env'_eq by simp
                have gg_eq: "TE_GhostGlobals env' = TE_GhostGlobals env" using env'_eq by simp
                show ?thesis unfolding global_vars_exist_in_state_def
                proof (intro allI impI, elim conjE)
                  fix name ty
                  assume lk: "fmlookup (TE_GlobalVars env') name = Some ty"
                    and ng: "name |\<notin>| TE_GhostGlobals env'"
                  from lk gv_eq have "fmlookup (TE_GlobalVars env) name = Some ty" by simp
                  moreover from ng gg_eq have "name |\<notin>| TE_GhostGlobals env" by simp
                  ultimately have "global_var_in_state_with_type state env name ty"
                    using old_gv unfolding global_vars_exist_in_state_def by blast
                  thus "global_var_in_state_with_type ?state' env' name ty"
                    using vht_eq unfolding global_var_in_state_with_type_def
                    by (auto split: option.splits)
                qed
              qed
            next
              show "no_extra_local_vars ?state' env'"
                unfolding no_extra_local_vars_def
              proof (intro allI impI)
                fix name
                assume ante: "fmlookup (TE_LocalVars env') name = None \<or> name |\<in>| TE_GhostLocals env'"
                show "fmlookup (IS_Locals ?state') name = None \<and>
                      fmlookup (IS_Refs ?state') name = None"
                proof (cases "name = varName")
                  case True
                  then show ?thesis by simp
                next
                  case False
                  from ante False env'_eq
                  have "fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env" by auto
                  with old_sme have "fmlookup (IS_Locals state) name = None \<and>
                      fmlookup (IS_Refs state) name = None"
                    unfolding state_matches_env_def no_extra_local_vars_def by blast
                  with False show ?thesis by simp
                qed
              qed
            next
              show "no_extra_global_vars ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def no_extra_global_vars_def by simp
            next
              show "funs_exist_in_state ?state' env'"
                unfolding funs_exist_in_state_def
              proof (intro allI impI, elim conjE)
                fix name info
                assume lk: "fmlookup (TE_Functions env') name = Some info"
                  and ng: "FI_Ghost info = NotGhost"
                from old_sme have old_fes: "funs_exist_in_state state env"
                  unfolding state_matches_env_def by simp
                have funs_eq: "TE_Functions env' = TE_Functions env" using env'_eq by simp
                from lk funs_eq have lk': "fmlookup (TE_Functions env) name = Some info" by simp
                from old_fes lk' ng obtain interpFun where
                  if_lk: "fmlookup (IS_Functions state) name = Some interpFun" and
                  matches: "fun_info_matches_interp_fun env info interpFun"
                  unfolding funs_exist_in_state_def by (auto split: option.splits)
                have if_lk': "fmlookup (IS_Functions ?state') name = Some interpFun"
                  using if_lk by simp
                have fcong: "fun_info_matches_interp_fun env' info interpFun =
                              fun_info_matches_interp_fun env info interpFun"
                  by (rule fun_info_matches_interp_fun_cong_env)
                     (use env'_eq in simp_all)
                have "fun_info_matches_interp_fun env' info interpFun"
                  using matches fcong by simp
                with if_lk' show "case fmlookup (IS_Functions ?state') name of
                                    None \<Rightarrow> False
                                  | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env' info interpFun"
                  by simp
              qed
            next
              show "no_extra_funs ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def no_extra_funs_def by simp
            next
              show "non_consts_in_locals_or_refs ?state' env'"
                unfolding non_consts_in_locals_or_refs_def
              proof (intro allI impI, elim conjE)
                fix name
                assume lk: "fmlookup (TE_LocalVars env') name \<noteq> None"
                  and ng: "name |\<notin>| TE_GhostLocals env'"
                  and nc: "name |\<notin>| TE_ConstLocals env'"
                from ng env'_eq have "name \<noteq> varName" by auto
                with lk env'_eq have "fmlookup (TE_LocalVars env) name \<noteq> None" by simp
                moreover from ng env'_eq \<open>name \<noteq> varName\<close> have "name |\<notin>| TE_GhostLocals env" by auto
                moreover from nc env'_eq \<open>name \<noteq> varName\<close>
                have "name |\<notin>| TE_ConstLocals env" by (auto split: if_splits)
                ultimately have "fmlookup (IS_Locals state) name \<noteq> None \<or>
                    fmlookup (IS_Refs state) name \<noteq> None"
                  using old_sme unfolding state_matches_env_def non_consts_in_locals_or_refs_def
                  by blast
                with \<open>name \<noteq> varName\<close> show "fmlookup (IS_Locals ?state') name \<noteq> None \<or>
                    fmlookup (IS_Refs ?state') name \<noteq> None"
                  by simp
              qed
            next
              show "const_locals_match ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def const_locals_match_def
                by (auto split: if_splits)
            next
              show "store_well_typed ?state' env' storeTyping"
                using old_sme vht_eq
                unfolding state_matches_env_def store_well_typed_def by simp
            qed
            with CoreStmt_VarDecl Ref Ghost show ?thesis
              using interp_eq storeTyping_extends_refl by auto
          next
            case NotGhost
            from "4.prems"(1) have old_sme: "state_matches_env state env storeTyping" .
            \<comment> \<open>Extract typechecker facts. \<close>
            from typing CoreStmt_VarDecl Ref NotGhost have
              wk: "is_well_kinded env varTy" and
              rt: "is_runtime_type env varTy" and
              init_lvalue: "is_lvalue initTm" and
              init_ty: "core_term_type env NotGhost initTm = Some varTy" and
              env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                                     TE_ConstLocals := (if is_writable_lvalue env initTm
                                                       then fminus (TE_ConstLocals env) {|varName|}
                                                       else finsert varName (TE_ConstLocals env)) \<rparr>"
              by (auto split: if_splits)

            \<comment> \<open>The interpreter dispatches on lvalue_base_name initTm. is_lvalue ensures
                this is Some baseName. \<close>
            from init_lvalue obtain baseName where
              base_eq: "lvalue_base_name initTm = Some baseName"
              unfolding is_lvalue_def by (cases "lvalue_base_name initTm") auto

            \<comment> \<open>is_writable_lvalue reduces to tyenv_var_writable on the base. \<close>
            from init_lvalue base_eq have
              wl_iff: "is_writable_lvalue env initTm = tyenv_var_writable env baseName"
              by (induction initTm) (auto simp: is_lvalue_def)
            \<comment> \<open>From core_term_type env NotGhost initTm = Some varTy, derive that the
                lvalue base is non-ghost. We generalise the type in the induction. \<close>
            have base_not_ghost_aux:
              "\<And>ty. core_term_type env NotGhost tm = Some ty
                    \<Longrightarrow> lvalue_base_name tm = Some baseName
                    \<Longrightarrow> \<not> tyenv_var_ghost env baseName" for tm
              by (induction tm) (auto split: option.splits if_splits)
            from base_not_ghost_aux[OF init_ty base_eq] have base_not_ghost:
              "\<not> tyenv_var_ghost env baseName" .
            from old_sme have
              cn_match: "IS_ConstLocals state = fminus (TE_ConstLocals env) (TE_GhostLocals env)"
              unfolding state_matches_env_def const_locals_match_def by simp

            \<comment> \<open>The runtime predicate matches the static is_writable_lvalue predicate.
                Locals shadow globals, so the runtime check is on IS_Locals/IS_Refs. \<close>
            have static_writable_iff_runtime:
              "is_writable_lvalue env initTm
               \<longleftrightarrow> baseName |\<notin>| IS_ConstLocals state
                   \<and> (fmlookup (IS_Locals state) baseName \<noteq> None
                      \<or> fmlookup (IS_Refs state) baseName \<noteq> None)"
            proof
              assume writable: "is_writable_lvalue env initTm"
              with wl_iff have tvw: "tyenv_var_writable env baseName" by simp
              from tvw have
                in_locals: "fmlookup (TE_LocalVars env) baseName \<noteq> None" and
                not_const: "baseName |\<notin>| TE_ConstLocals env"
                unfolding tyenv_var_writable_def by simp_all
              from in_locals base_not_ghost have not_ghost: "baseName |\<notin>| TE_GhostLocals env"
                unfolding tyenv_var_ghost_def by auto
              from not_const cn_match have not_iconst: "baseName |\<notin>| IS_ConstLocals state"
                by auto
              from old_sme in_locals not_ghost not_const
              have in_state: "fmlookup (IS_Locals state) baseName \<noteq> None
                              \<or> fmlookup (IS_Refs state) baseName \<noteq> None"
                unfolding state_matches_env_def non_consts_in_locals_or_refs_def by blast
              show "baseName |\<notin>| IS_ConstLocals state
                    \<and> (fmlookup (IS_Locals state) baseName \<noteq> None
                       \<or> fmlookup (IS_Refs state) baseName \<noteq> None)"
                using not_iconst in_state by simp
            next
              assume hyp: "baseName |\<notin>| IS_ConstLocals state
                           \<and> (fmlookup (IS_Locals state) baseName \<noteq> None
                              \<or> fmlookup (IS_Refs state) baseName \<noteq> None)"
              hence not_iconst: "baseName |\<notin>| IS_ConstLocals state"
                and in_state: "fmlookup (IS_Locals state) baseName \<noteq> None
                               \<or> fmlookup (IS_Refs state) baseName \<noteq> None" by simp_all
              \<comment> \<open>By no_extra_local_vars contrapositive: baseName in IS_Locals or IS_Refs
                  \<Longrightarrow> baseName \<in> TE_LocalVars (and \<notin> TE_GhostLocals). \<close>
              have in_locals: "fmlookup (TE_LocalVars env) baseName \<noteq> None"
              proof (rule ccontr)
                assume neg: "\<not> fmlookup (TE_LocalVars env) baseName \<noteq> None"
                hence "fmlookup (TE_LocalVars env) baseName = None
                       \<or> baseName |\<in>| TE_GhostLocals env" by simp
                with old_sme have "fmlookup (IS_Locals state) baseName = None
                                   \<and> fmlookup (IS_Refs state) baseName = None"
                  unfolding state_matches_env_def no_extra_local_vars_def by blast
                with in_state show False by simp
              qed
              from in_locals base_not_ghost have not_ghost: "baseName |\<notin>| TE_GhostLocals env"
                unfolding tyenv_var_ghost_def by auto
              from not_iconst cn_match not_ghost have not_const: "baseName |\<notin>| TE_ConstLocals env"
                by auto
              from in_locals not_const have "tyenv_var_writable env baseName"
                unfolding tyenv_var_writable_def by simp
              with wl_iff show "is_writable_lvalue env initTm" by simp
            qed

            show ?thesis
            proof (cases "is_writable_lvalue env initTm")
              case writable: True
              \<comment> \<open>Alias path: use IH_lvalue. The interpreter falls into the alias branch
                  since base is writable, so by static_writable_iff_runtime, base is not
                  in IS_ConstLocals and is in IS_Locals or IS_Refs. \<close>
              from writable static_writable_iff_runtime have
                base_not_const: "baseName |\<notin>| IS_ConstLocals state" and
                base_in_state: "fmlookup (IS_Locals state) baseName \<noteq> None
                                \<or> fmlookup (IS_Refs state) baseName \<noteq> None" by simp_all
              from IH_lvalue[OF "4.prems"(1,2) conjI[OF writable init_ty]]
              have lv_sound: "sound_lvalue_result state env storeTyping varTy
                  (interp_writable_lvalue fuel state initTm)" .
              show ?thesis
              proof (cases "interp_writable_lvalue fuel state initTm")
                case (Inl err)
                with lv_sound have err_sound: "sound_error_result err" by simp
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Ref varTy initTm) = Inl err"
                  using Inl base_eq base_not_const base_in_state by auto
                with err_sound CoreStmt_VarDecl Ref NotGhost show ?thesis by simp
              next
                case (Inr addrPath)
                obtain addr path where ap_eq: "addrPath = (addr, path)"
                  by (cases addrPath) auto
                from lv_sound Inr ap_eq have
                  addr_valid: "addr < length (IS_Store state)" and
                  path_ty: "type_at_path env (storeTyping ! addr) path = Some varTy"
                  by auto
                let ?state' = "state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
                                       IS_Refs := fmupd varName (addr, path) (IS_Refs state),
                                       IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"
                have interp_eq: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Ref varTy initTm) = Inr (Continue ?state')"
                  using Inr ap_eq base_eq base_not_const base_in_state by auto
                \<comment> \<open>var_fresh and var_not_ghost preconditions for state_matches_env_add_ref. \<close>
                from "4.prems"(2) have wf: "tyenv_well_formed env" .
                from old_sme have nc_invariant: "non_consts_in_locals_or_refs state env"
                  unfolding state_matches_env_def by simp
                \<comment> \<open>We need varName \<notin> TE_LocalVars and varName \<notin> TE_GhostLocals. These come
                    from tyenv well-formedness applied to env'? No — env' adds varName to
                    TE_LocalVars, so we need that varName is fresh in env. Hmm — actually,
                    the typechecker doesn't enforce freshness; shadowing is permitted.
                    state_matches_env_add_ref's var_fresh precondition is too strong.

                    Workaround: use state_matches_env directly without going through the
                    helper, or relax the helper to not require var_fresh. \<close>
                \<comment> \<open>Easier: prove state_matches_env directly, similar to the Ghost case but
                    with the new addr/path entry in IS_Refs. \<close>
                have env'_writable_eq:
                  "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                                TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
                  using env'_eq writable by simp
                have env'_fields: "TE_DataCtors env' = TE_DataCtors env"
                                  "TE_Datatypes env' = TE_Datatypes env"
                                  "TE_TypeVars env' = TE_TypeVars env"
                                  "TE_GhostDatatypes env' = TE_GhostDatatypes env"
                                  "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
                  using env'_writable_eq by simp_all
                have vht_eq: "\<And>v t. value_has_type env' v t = value_has_type env v t"
                  using value_has_type_cong_env[OF env'_fields] .
                have tap_eq: "\<And>t p. type_at_path env t p = type_at_path env' t p"
                  using type_at_path_cong_env[OF env'_fields(1)] .
                have new_sme: "state_matches_env ?state' env' storeTyping"
                  unfolding state_matches_env_def
                proof (intro conjI)
                  show "local_vars_exist_in_state ?state' env' storeTyping"
                    unfolding local_vars_exist_in_state_def
                  proof (intro allI impI, elim conjE)
                    fix name ty
                    assume lk: "fmlookup (TE_LocalVars env') name = Some ty"
                      and ng: "name |\<notin>| TE_GhostLocals env'"
                    show "local_var_in_state_with_type ?state' env' storeTyping name ty"
                    proof (cases "name = varName")
                      case True
                      from lk env'_writable_eq True have ty_eq: "ty = varTy" by simp
                      have lk_locals: "fmlookup (IS_Locals ?state') varName = None" by simp
                      have lk_refs: "fmlookup (IS_Refs ?state') varName = Some (addr, path)" by simp
                      have path_ty': "type_at_path env' (storeTyping ! addr) path = Some varTy"
                        using path_ty tap_eq by simp
                      show ?thesis
                        using True ty_eq lk_locals lk_refs addr_valid path_ty'
                        unfolding local_var_in_state_with_type_def by simp
                    next
                      case False
                      from lk env'_writable_eq False have lk_old: "fmlookup (TE_LocalVars env) name = Some ty" by simp
                      from ng env'_writable_eq False have ng_old: "name |\<notin>| TE_GhostLocals env" by auto
                      from old_sme lk_old ng_old
                      have old: "local_var_in_state_with_type state env storeTyping name ty"
                        unfolding state_matches_env_def local_vars_exist_in_state_def by blast
                      from False have lk_lo: "fmlookup (IS_Locals ?state') name = fmlookup (IS_Locals state) name"
                        by simp
                      from False have lk_re: "fmlookup (IS_Refs ?state') name = fmlookup (IS_Refs state) name"
                        by simp
                      show ?thesis
                        using old lk_lo lk_re tap_eq
                        unfolding local_var_in_state_with_type_def
                        by (auto split: option.splits)
                    qed
                  qed
                next
                  show "global_vars_exist_in_state ?state' env'"
                  proof -
                    from old_sme have old_gv: "global_vars_exist_in_state state env"
                      unfolding state_matches_env_def by simp
                    have gv_eq: "TE_GlobalVars env' = TE_GlobalVars env" using env'_writable_eq by simp
                    have gg_eq: "TE_GhostGlobals env' = TE_GhostGlobals env" using env'_writable_eq by simp
                    show ?thesis unfolding global_vars_exist_in_state_def
                    proof (intro allI impI, elim conjE)
                      fix name ty
                      assume "fmlookup (TE_GlobalVars env') name = Some ty"
                        and "name |\<notin>| TE_GhostGlobals env'"
                      hence "fmlookup (TE_GlobalVars env) name = Some ty"
                        and "name |\<notin>| TE_GhostGlobals env"
                        using gv_eq gg_eq by simp_all
                      hence "global_var_in_state_with_type state env name ty"
                        using old_gv unfolding global_vars_exist_in_state_def by blast
                      thus "global_var_in_state_with_type ?state' env' name ty"
                        using vht_eq unfolding global_var_in_state_with_type_def
                        by (auto split: option.splits)
                    qed
                  qed
                next
                  show "no_extra_local_vars ?state' env'"
                    unfolding no_extra_local_vars_def
                  proof (intro allI impI)
                    fix name
                    assume ante: "fmlookup (TE_LocalVars env') name = None \<or> name |\<in>| TE_GhostLocals env'"
                    show "fmlookup (IS_Locals ?state') name = None \<and>
                          fmlookup (IS_Refs ?state') name = None"
                    proof (cases "name = varName")
                      case True
                      from env'_writable_eq have "fmlookup (TE_LocalVars env') varName = Some varTy" by simp
                      with ante True have "varName |\<in>| TE_GhostLocals env'" by simp
                      hence False using env'_writable_eq by auto
                      thus ?thesis ..
                    next
                      case False
                      from ante env'_writable_eq False
                      have "fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env" by auto
                      with old_sme have "fmlookup (IS_Locals state) name = None \<and>
                          fmlookup (IS_Refs state) name = None"
                        unfolding state_matches_env_def no_extra_local_vars_def by blast
                      with False show ?thesis by simp
                    qed
                  qed
                next
                  show "no_extra_global_vars ?state' env'"
                    using old_sme env'_writable_eq
                    unfolding state_matches_env_def no_extra_global_vars_def by simp
                next
                  show "funs_exist_in_state ?state' env'"
                    unfolding funs_exist_in_state_def
                  proof (intro allI impI, elim conjE)
                    fix name info
                    assume lk: "fmlookup (TE_Functions env') name = Some info"
                      and ng: "FI_Ghost info = NotGhost"
                    from old_sme have old_fes: "funs_exist_in_state state env"
                      unfolding state_matches_env_def by simp
                    have funs_eq: "TE_Functions env' = TE_Functions env" using env'_writable_eq by simp
                    from lk funs_eq have lk': "fmlookup (TE_Functions env) name = Some info" by simp
                    from old_fes lk' ng obtain interpFun where
                      if_lk: "fmlookup (IS_Functions state) name = Some interpFun" and
                      matches: "fun_info_matches_interp_fun env info interpFun"
                      unfolding funs_exist_in_state_def by (auto split: option.splits)
                    have if_lk': "fmlookup (IS_Functions ?state') name = Some interpFun"
                      using if_lk by simp
                    have fcong: "fun_info_matches_interp_fun env' info interpFun =
                                  fun_info_matches_interp_fun env info interpFun"
                      by (rule fun_info_matches_interp_fun_cong_env)
                         (use env'_writable_eq in simp_all)
                    have "fun_info_matches_interp_fun env' info interpFun"
                      using matches fcong by simp
                    with if_lk' show "case fmlookup (IS_Functions ?state') name of
                                        None \<Rightarrow> False
                                      | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env' info interpFun"
                      by simp
                  qed
                next
                  show "no_extra_funs ?state' env'"
                    using old_sme env'_writable_eq
                    unfolding state_matches_env_def no_extra_funs_def by simp
                next
                  show "non_consts_in_locals_or_refs ?state' env'"
                    unfolding non_consts_in_locals_or_refs_def
                  proof (intro allI impI, elim conjE)
                    fix name
                    assume lk: "fmlookup (TE_LocalVars env') name \<noteq> None"
                      and ng: "name |\<notin>| TE_GhostLocals env'"
                      and nc: "name |\<notin>| TE_ConstLocals env'"
                    show "fmlookup (IS_Locals ?state') name \<noteq> None \<or>
                          fmlookup (IS_Refs ?state') name \<noteq> None"
                    proof (cases "name = varName")
                      case True
                      then show ?thesis by simp
                    next
                      case False
                      from lk env'_writable_eq False have "fmlookup (TE_LocalVars env) name \<noteq> None" by simp
                      moreover from ng env'_writable_eq False have "name |\<notin>| TE_GhostLocals env" by auto
                      moreover from nc env'_writable_eq False have "name |\<notin>| TE_ConstLocals env" by auto
                      ultimately have "fmlookup (IS_Locals state) name \<noteq> None \<or>
                          fmlookup (IS_Refs state) name \<noteq> None"
                        using old_sme
                        unfolding state_matches_env_def non_consts_in_locals_or_refs_def by blast
                      with False show ?thesis by simp
                    qed
                  qed
                next
                  show "const_locals_match ?state' env'"
                    using old_sme env'_writable_eq
                    unfolding state_matches_env_def const_locals_match_def by auto
                next
                  show "store_well_typed ?state' env' storeTyping"
                    using old_sme vht_eq
                    unfolding state_matches_env_def store_well_typed_def by simp
                qed
                from new_sme interp_eq CoreStmt_VarDecl Ref NotGhost
                show ?thesis using storeTyping_extends_refl by auto
              qed
            next
              case readonly: False
              \<comment> \<open>Copy path: use IH_term to get the value, alloc_store, add to IS_ConstLocals. \<close>
              from readonly static_writable_iff_runtime have
                runtime_readonly: "baseName |\<in>| IS_ConstLocals state
                                   \<or> (fmlookup (IS_Locals state) baseName = None
                                      \<and> fmlookup (IS_Refs state) baseName = None)" by auto
              from IH_term[OF "4.prems"(1,2) init_ty]
              have init_sound: "sound_term_result env varTy (interp_term fuel state initTm)" .
              show ?thesis
              proof (cases "interp_term fuel state initTm")
                case (Inl err)
                with init_sound have err_sound: "sound_error_result err" by simp
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Ref varTy initTm) = Inl err"
                  using Inl base_eq runtime_readonly by simp
                with err_sound CoreStmt_VarDecl Ref NotGhost show ?thesis by simp
              next
                case (Inr initVal)
                from init_sound Inr have val_typed: "value_has_type env initVal varTy" by simp
                obtain state' addr where alloc_eq: "(state', addr) = alloc_store state initVal"
                  by (cases "alloc_store state initVal") auto
                let ?state'' = "state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state'),
                                         IS_Refs := fmdrop varName (IS_Refs state'),
                                         IS_ConstLocals := finsert varName (IS_ConstLocals state') \<rparr>"
                have interp_eq: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Ref varTy initTm) = Inr (Continue ?state'')"
                  using Inr alloc_eq base_eq runtime_readonly
                  by (simp add: case_prod_beta)
                from env'_eq readonly have env'_const_eq:
                  "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                                TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>"
                  by simp
                have new_sme: "state_matches_env ?state'' env' (storeTyping @ [varTy])"
                  using state_matches_env_add_const_local[OF "4.prems"(1) val_typed alloc_eq refl env'_const_eq] .
                have ext: "storeTyping_extends storeTyping (storeTyping @ [varTy])"
                  using storeTyping_extends_append .
                from new_sme ext interp_eq CoreStmt_VarDecl Ref NotGhost
                show ?thesis by auto
              qed
            qed
          qed
        qed
      next
        case (CoreStmt_Assign assignGhost lhsTm rhsTm)
        then show ?thesis proof (cases assignGhost)
          case Ghost
          \<comment> \<open>Ghost Assign: interpreter returns Continue state, env unchanged\<close>
          from typing CoreStmt_Assign Ghost have "env' = env"
            by (auto split: if_splits option.splits)
          with Ghost CoreStmt_Assign "4.prems"(1) show ?thesis
            using storeTyping_extends_refl by auto
        next
          case NotGhost
          \<comment> \<open>NotGhost Assign: evaluates lhs lvalue and rhs term, updates store.
              For now we handle only the non-function-call rhs case.\<close>
          from typing CoreStmt_Assign NotGhost obtain lhsTy where
            lhs_writable: "is_writable_lvalue env lhsTm" and
            lhs_ty: "core_term_type env NotGhost lhsTm = Some lhsTy" and
            rhs_ty_disj: "core_impure_call_type env NotGhost rhsTm = Some lhsTy
                          \<or> core_term_type env NotGhost rhsTm = Some lhsTy" and
            env'_eq: "env' = env"
            by (auto split: if_splits option.splits)
          from IH_lvalue[OF "4.prems"(1,2) conjI[OF lhs_writable lhs_ty]]
          have lhs_sound: "sound_lvalue_result state env storeTyping lhsTy
              (interp_writable_lvalue fuel state lhsTm)" .
          \<comment> \<open>Normalize the disjunction via the shared helper. \<close>
          note fn_call_facts_or_pure = fn_call_facts_from_disjunct[OF rhs_ty_disj]

          show ?thesis
          proof (cases "interp_writable_lvalue fuel state lhsTm")
            case (Inl err)
            with lhs_sound have "sound_error_result err" by simp
            with Inl CoreStmt_Assign NotGhost show ?thesis by simp
          next
            case (Inr addrPath)
            obtain addr path where ap_eq: "addrPath = (addr, path)"
              by (cases addrPath) auto
            from lhs_sound Inr ap_eq have
              addr_valid: "addr < length (IS_Store state)" and
              path_ty: "type_at_path env (storeTyping ! addr) path = Some lhsTy"
              by auto
            \<comment> \<open>Handle the function-call rhs separately from other term rhs.\<close>
            show ?thesis
            proof (cases "\<exists>fnName tyArgs argTms. rhsTm = CoreTm_FunctionCall fnName tyArgs argTms")
              case True
              \<comment> \<open>Function call rhs: use interp_function_call_sound (IH_fc).\<close>
              then obtain fnName tyArgs argTms where rhsTm_eq:
                "rhsTm = CoreTm_FunctionCall fnName tyArgs argTms" by auto
              \<comment> \<open>Extract function-call facts from fn_call_facts_or_pure (either branch
                  of the impure/pure disjunction). \<close>
              from fn_call_facts_or_pure rhsTm_eq obtain funInfo fnName' tyArgs' argTms' where
                rhsTm_eq': "rhsTm = CoreTm_FunctionCall fnName' tyArgs' argTms'" and
                fn_lookup: "fmlookup (TE_Functions env) fnName' = Some funInfo" and
                len_tyargs: "length tyArgs' = length (FI_TyArgs funInfo)" and
                tyargs_wk: "list_all (is_well_kinded env) tyArgs'" and
                tyargs_rt: "list_all (is_runtime_type env) tyArgs'" and
                fn_not_ghost: "FI_Ghost funInfo = NotGhost" and
                len_tmargs: "length argTms' = length (FI_TmArgs funInfo)" and
                args_check: "list_all2 (\<lambda>tm expectedTy.
                               case core_term_type env NotGhost tm of
                                 None \<Rightarrow> False
                               | Some actualTy \<Rightarrow> actualTy = expectedTy)
                             argTms'
                             (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs')) ty)
                                  (FI_TmArgs funInfo))" and
                fn_ty_eq: "lhsTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs'))
                                               (FI_ReturnType funInfo)" and
                ref_lvalues: "\<forall>i < length argTms'.
                                snd (snd (FI_TmArgs funInfo ! i)) = Ref
                                  \<longrightarrow> is_writable_lvalue env (argTms' ! i)"
                by blast
              from rhsTm_eq rhsTm_eq' have name_eqs:
                "fnName' = fnName" "tyArgs' = tyArgs" "argTms' = argTms"
                by auto
              note fn_lookup = fn_lookup[unfolded name_eqs]
              note len_tyargs = len_tyargs[unfolded name_eqs]
              note tyargs_wk = tyargs_wk[unfolded name_eqs]
              note tyargs_rt = tyargs_rt[unfolded name_eqs]
              note len_tmargs = len_tmargs[unfolded name_eqs]
              note args_check = args_check[unfolded name_eqs]
              note fn_ty_eq = fn_ty_eq[unfolded name_eqs]
              note ref_lvalues = ref_lvalues[unfolded name_eqs]
              from IH_fc[OF "4.prems"(1,2) fn_lookup fn_not_ghost args_check fn_ty_eq
                            len_tyargs tyargs_wk tyargs_rt ref_lvalues]
              have fc_sound: "sound_function_call_result env storeTyping lhsTy
                  (interp_function_call fuel state fnName argTms)" .
              show ?thesis
              proof (cases "interp_function_call fuel state fnName argTms")
                case (Inl err)
                with fc_sound have err_sound: "sound_error_result err" by simp
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_Assign NotGhost lhsTm rhsTm) = Inl err"
                  using Inl \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close> ap_eq rhsTm_eq
                  by simp
                with err_sound CoreStmt_Assign NotGhost show ?thesis by simp
              next
                case (Inr fcResult)
                obtain newState rhsVal where fcResult_eq: "fcResult = (newState, rhsVal)"
                  by (cases fcResult) auto
                from fc_sound Inr fcResult_eq obtain storeTyping1 where
                  new_sme: "state_matches_env newState env storeTyping1" and
                  ext1: "storeTyping_extends storeTyping storeTyping1" and
                  rhs_typed: "value_has_type env rhsVal lhsTy"
                  by auto
                \<comment> \<open>Since storeTyping_extends, the original addr's type is preserved.\<close>
                from ext1 obtain suffix where st1_eq: "storeTyping1 = storeTyping @ suffix"
                  unfolding storeTyping_extends_def by auto
                from new_sme
                have st1_len: "length storeTyping1 = length (IS_Store newState)"
                  unfolding state_matches_env_def store_well_typed_def by simp
                from "4.prems"(1)
                have st_len: "length storeTyping = length (IS_Store state)"
                  unfolding state_matches_env_def store_well_typed_def by simp
                from addr_valid st_len have addr_lt_st: "addr < length storeTyping" by simp
                have st1_at_addr: "storeTyping1 ! addr = storeTyping ! addr"
                  using st1_eq addr_lt_st by (simp add: nth_append)
                from addr_lt_st st1_eq have addr_lt_st1: "addr < length storeTyping1" by simp
                from addr_lt_st1 st1_len
                have addr_valid_new: "addr < length (IS_Store newState)" by simp
                from path_ty st1_at_addr
                have path_ty_new: "type_at_path env (storeTyping1 ! addr) path = Some lhsTy" by simp
                \<comment> \<open>Get the old slot value (in newState) typed at storeTyping1 ! addr.\<close>
                from new_sme addr_valid_new
                have old_slot_typed: "value_has_type env (IS_Store newState ! addr)
                                        (storeTyping1 ! addr)"
                  unfolding state_matches_env_def store_well_typed_def by simp
                show ?thesis
                proof (cases "update_value_at_path (IS_Store newState ! addr) path rhsVal")
                  case (Inl err)
                  from update_value_at_path_error_is_runtime[OF old_slot_typed path_ty_new Inl]
                  have err_eq: "err = RuntimeError" .
                  have interp_err: "interp_statement (Suc fuel) state
                      (CoreStmt_Assign NotGhost lhsTm rhsTm) = Inl RuntimeError"
                    using Inl Inr fcResult_eq
                          \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close>
                          ap_eq rhsTm_eq err_eq by simp
                  with CoreStmt_Assign NotGhost show ?thesis by simp
                next
                  case (Inr newVal)
                  from update_value_at_path_preserves_type[OF old_slot_typed Inr path_ty_new rhs_typed]
                  have new_slot_typed: "value_has_type env newVal (storeTyping1 ! addr)" .
                  \<comment> \<open>Build the final state.\<close>
                  let ?finalState = "newState \<lparr> IS_Store := (IS_Store newState)[addr := newVal] \<rparr>"
                  have interp_eq: "interp_statement (Suc fuel) state
                      (CoreStmt_Assign NotGhost lhsTm rhsTm) = Inr (Continue ?finalState)"
                    using Inr \<open>interp_function_call fuel state fnName argTms = Inr fcResult\<close>
                          fcResult_eq
                          \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close>
                          ap_eq rhsTm_eq by simp
                  from state_matches_env_update_store[OF new_sme addr_valid_new
                      new_slot_typed refl]
                  have final_sme: "state_matches_env ?finalState env storeTyping1" .
                  from final_sme ext1 interp_eq env'_eq CoreStmt_Assign NotGhost
                  show ?thesis by auto
                qed
              qed
            next
              case False
              \<comment> \<open>Non-function-call rhs: use IH_term.\<close>
              from False have not_fc: "\<And>fnName tyArgs argTms.
                  rhsTm \<noteq> CoreTm_FunctionCall fnName tyArgs argTms" by auto
              from fn_call_facts_or_pure not_fc have rhs_ty:
                "core_term_type env NotGhost rhsTm = Some lhsTy" by blast
              from IH_term[OF "4.prems"(1,2) rhs_ty]
              have rhs_sound: "sound_term_result env lhsTy (interp_term fuel state rhsTm)" .
              show ?thesis
              proof (cases "interp_term fuel state rhsTm")
                case (Inl err)
                with rhs_sound have err_sound: "sound_error_result err" by simp
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_Assign NotGhost lhsTm rhsTm) = Inl err"
                  using Inl \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close> ap_eq not_fc
                  by (cases rhsTm) auto
                with err_sound CoreStmt_Assign NotGhost show ?thesis by simp
              next
                case (Inr rhsVal)
                from rhs_sound Inr have rhs_typed: "value_has_type env rhsVal lhsTy" by simp
                \<comment> \<open>Get the old slot value typed at storeTyping ! addr.\<close>
                from "4.prems"(1) addr_valid
                have old_slot_typed: "value_has_type env (IS_Store state ! addr) (storeTyping ! addr)"
                  unfolding state_matches_env_def store_well_typed_def by simp
                show ?thesis
                proof (cases "update_value_at_path (IS_Store state ! addr) path rhsVal")
                  case (Inl err)
                  \<comment> \<open>update_value_at_path failed — must be a sound error.
                      By update_value_at_path_error_is_runtime.\<close>
                  from update_value_at_path_error_is_runtime[OF old_slot_typed path_ty Inl]
                  have err_eq: "err = RuntimeError" .
                  have interp_err: "interp_statement (Suc fuel) state
                      (CoreStmt_Assign NotGhost lhsTm rhsTm) = Inl RuntimeError"
                    using Inl Inr \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close>
                          ap_eq err_eq not_fc
                    by (cases rhsTm) auto
                  with CoreStmt_Assign NotGhost show ?thesis by simp
                next
                  case (Inr newVal)
                  \<comment> \<open>update_value_at_path succeeded with newVal of the slot's type.\<close>
                  from update_value_at_path_preserves_type[OF old_slot_typed Inr path_ty rhs_typed]
                  have new_slot_typed: "value_has_type env newVal (storeTyping ! addr)" .
                  \<comment> \<open>Build the new state.\<close>
                  let ?state' = "state \<lparr> IS_Store := (IS_Store state)[addr := newVal] \<rparr>"
                  have interp_eq: "interp_statement (Suc fuel) state
                      (CoreStmt_Assign NotGhost lhsTm rhsTm) = Inr (Continue ?state')"
                    using Inr \<open>interp_term fuel state rhsTm = Inr rhsVal\<close>
                      \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close> ap_eq not_fc
                    by (cases rhsTm) auto
                  \<comment> \<open>Apply state_matches_env_update_store to get new state matches env.\<close>
                  from state_matches_env_update_store[OF "4.prems"(1) addr_valid
                      new_slot_typed refl]
                  have new_sme: "state_matches_env ?state' env storeTyping" .
                  have ext: "storeTyping_extends storeTyping storeTyping"
                    using storeTyping_extends_refl .
                  from new_sme ext interp_eq env'_eq CoreStmt_Assign NotGhost
                  show ?thesis by auto
                qed
              qed
            qed
          qed
        qed
      next
        case (CoreStmt_Fix _ _) with typing show ?thesis sorry
      next
        case (CoreStmt_Obtain _ _ _) with typing show ?thesis sorry
      next
        case (CoreStmt_Use _) with typing show ?thesis sorry
      next
        case (CoreStmt_Swap swapGhost lhsTm rhsTm)
        then show ?thesis proof (cases swapGhost)
          case Ghost
          \<comment> \<open>Ghost Swap: interpreter returns Continue state, env unchanged\<close>
          from typing CoreStmt_Swap Ghost have "env' = env"
            by (auto split: if_splits option.splits)
          with Ghost CoreStmt_Swap "4.prems"(1) show ?thesis
            using storeTyping_extends_refl by auto
        next
          case NotGhost
          \<comment> \<open>NotGhost Swap: evaluates both lvalues and swaps the values.\<close>
          from typing CoreStmt_Swap NotGhost obtain lhsTy where
            lhs_writable: "is_writable_lvalue env lhsTm" and
            rhs_writable: "is_writable_lvalue env rhsTm" and
            lhs_ty: "core_term_type env NotGhost lhsTm = Some lhsTy" and
            rhs_ty: "core_term_type env NotGhost rhsTm = Some lhsTy" and
            env'_eq: "env' = env"
            by (auto split: if_splits option.splits)
          from IH_lvalue[OF "4.prems"(1,2) conjI[OF lhs_writable lhs_ty]]
          have lhs_sound: "sound_lvalue_result state env storeTyping lhsTy
              (interp_writable_lvalue fuel state lhsTm)" .
          from IH_lvalue[OF "4.prems"(1,2) conjI[OF rhs_writable rhs_ty]]
          have rhs_sound: "sound_lvalue_result state env storeTyping lhsTy
              (interp_writable_lvalue fuel state rhsTm)" .
          show ?thesis
          proof (cases "interp_writable_lvalue fuel state lhsTm")
            case (Inl err)
            with lhs_sound have "sound_error_result err" by simp
            with Inl CoreStmt_Swap NotGhost show ?thesis by simp
          next
            case Inr_lhs: (Inr lhsAddrPath)
            obtain addr1 path1 where ap1_eq: "lhsAddrPath = (addr1, path1)"
              by (cases lhsAddrPath) auto
            from lhs_sound Inr_lhs ap1_eq have
              addr1_valid: "addr1 < length (IS_Store state)" and
              path1_ty: "type_at_path env (storeTyping ! addr1) path1 = Some lhsTy"
              by auto
            show ?thesis
            proof (cases "interp_writable_lvalue fuel state rhsTm")
              case (Inl err)
              with rhs_sound have "sound_error_result err" by simp
              with Inl Inr_lhs ap1_eq CoreStmt_Swap NotGhost show ?thesis by simp
            next
              case Inr_rhs: (Inr rhsAddrPath)
              obtain addr2 path2 where ap2_eq: "rhsAddrPath = (addr2, path2)"
                by (cases rhsAddrPath) auto
              from rhs_sound Inr_rhs ap2_eq have
                addr2_valid: "addr2 < length (IS_Store state)" and
                path2_ty: "type_at_path env (storeTyping ! addr2) path2 = Some lhsTy"
                by auto
              \<comment> \<open>Get the original slot values typed at their storeTyping entries.\<close>
              from "4.prems"(1) addr1_valid
              have slot1_typed: "value_has_type env (IS_Store state ! addr1) (storeTyping ! addr1)"
                unfolding state_matches_env_def store_well_typed_def by simp
              from "4.prems"(1) addr2_valid
              have slot2_typed: "value_has_type env (IS_Store state ! addr2) (storeTyping ! addr2)"
                unfolding state_matches_env_def store_well_typed_def by simp
              \<comment> \<open>Case split on get_value_at_path results for both slots.\<close>
              show ?thesis
              proof (cases "get_value_at_path (IS_Store state ! addr1) path1")
                case (Inl err1)
                from get_value_at_path_error_is_runtime[OF slot1_typed path1_ty Inl]
                have err1_eq: "err1 = RuntimeError" .
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inl RuntimeError"
                  using Inr_lhs ap1_eq Inr_rhs ap2_eq Inl err1_eq by simp
                with CoreStmt_Swap NotGhost show ?thesis by simp
              next
                case Inr_get1: (Inr val1)
                from get_value_at_path_type[OF slot1_typed Inr_get1] obtain pathTy1 where
                  pathTy1_eq: "type_at_path env (storeTyping ! addr1) path1 = Some pathTy1" and
                  val1_typed: "value_has_type env val1 pathTy1"
                  by auto
                with path1_ty have val1_typed_lhsTy: "value_has_type env val1 lhsTy" by simp
                show ?thesis
                proof (cases "get_value_at_path (IS_Store state ! addr2) path2")
                  case (Inl err2)
                  from get_value_at_path_error_is_runtime[OF slot2_typed path2_ty Inl]
                  have err2_eq: "err2 = RuntimeError" .
                  have interp_err: "interp_statement (Suc fuel) state
                      (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inl RuntimeError"
                    using Inr_lhs ap1_eq Inr_rhs ap2_eq Inr_get1 Inl err2_eq by simp
                  with CoreStmt_Swap NotGhost show ?thesis by simp
                next
                  case Inr_get2: (Inr val2)
                  from get_value_at_path_type[OF slot2_typed Inr_get2] obtain pathTy2 where
                    pathTy2_eq: "type_at_path env (storeTyping ! addr2) path2 = Some pathTy2" and
                    val2_typed: "value_has_type env val2 pathTy2"
                    by auto
                  with path2_ty have val2_typed_lhsTy: "value_has_type env val2 lhsTy" by simp
                  \<comment> \<open>First update: put val2 into slot1 at path1.\<close>
                  show ?thesis
                  proof (cases "update_value_at_path (IS_Store state ! addr1) path1 val2")
                    case (Inl err)
                    from update_value_at_path_error_is_runtime[OF slot1_typed path1_ty Inl]
                    have "err = RuntimeError" .
                    then have interp_err: "interp_statement (Suc fuel) state
                        (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inl RuntimeError"
                      using Inr_lhs ap1_eq Inr_rhs ap2_eq Inr_get1 Inr_get2 Inl by simp
                    with CoreStmt_Swap NotGhost show ?thesis by simp
                  next
                    case Inr_upd1: (Inr new_val1)
                    from update_value_at_path_preserves_type[OF slot1_typed Inr_upd1 path1_ty val2_typed_lhsTy]
                    have new_val1_typed: "value_has_type env new_val1 (storeTyping ! addr1)" .
                    \<comment> \<open>Build intermediate store1 where slot addr1 has new_val1.\<close>
                    let ?store1 = "(IS_Store state)[addr1 := new_val1]"
                    let ?state1 = "state \<lparr> IS_Store := ?store1 \<rparr>"
                    from state_matches_env_update_store[OF "4.prems"(1) addr1_valid
                        new_val1_typed refl]
                    have state1_sme: "state_matches_env ?state1 env storeTyping" .
                    \<comment> \<open>Second update: put val1 into slot2 at path2 in the intermediate store.\<close>
                    have store1_len: "length ?store1 = length (IS_Store state)" by simp
                    from addr2_valid store1_len have addr2_valid1: "addr2 < length ?store1" by simp
                    from state1_sme addr2_valid1
                    have slot2_store1_typed:
                        "value_has_type env (?store1 ! addr2) (storeTyping ! addr2)"
                      unfolding state_matches_env_def store_well_typed_def by simp
                    show ?thesis
                    proof (cases "update_value_at_path (?store1 ! addr2) path2 val1")
                      case (Inl err)
                      from update_value_at_path_error_is_runtime[OF slot2_store1_typed path2_ty Inl]
                      have "err = RuntimeError" .
                      then have interp_err: "interp_statement (Suc fuel) state
                          (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inl RuntimeError"
                        using Inr_lhs ap1_eq Inr_rhs ap2_eq Inr_get1 Inr_get2 Inr_upd1 Inl
                        by (simp add: Let_def)
                      with CoreStmt_Swap NotGhost show ?thesis by simp
                    next
                      case Inr_upd2: (Inr new_val2)
                      from update_value_at_path_preserves_type[OF slot2_store1_typed Inr_upd2 path2_ty val1_typed_lhsTy]
                      have new_val2_typed: "value_has_type env new_val2 (storeTyping ! addr2)" .
                      \<comment> \<open>Build the final state as an update of the intermediate state.\<close>
                      let ?state2 = "?state1 \<lparr> IS_Store := (IS_Store ?state1)[addr2 := new_val2] \<rparr>"
                      have addr2_valid_state1: "addr2 < length (IS_Store ?state1)"
                        using addr2_valid1 by simp
                      from state_matches_env_update_store[OF state1_sme addr2_valid_state1
                          new_val2_typed refl]
                      have state2_sme: "state_matches_env ?state2 env storeTyping" .
                      have interp_eq: "interp_statement (Suc fuel) state
                          (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inr (Continue ?state2)"
                        using Inr_lhs ap1_eq Inr_rhs ap2_eq Inr_get1 Inr_get2 Inr_upd1 Inr_upd2
                        by (simp add: Let_def)
                      have ext: "storeTyping_extends storeTyping storeTyping"
                        using storeTyping_extends_refl .
                      from state2_sme ext interp_eq env'_eq CoreStmt_Swap NotGhost
                      show ?thesis by auto
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      next
        case (CoreStmt_Return tm)
        \<comment> \<open>Return: evaluate the term; if successful, return the value.\<close>
        from typing CoreStmt_Return have
          tm_ty: "core_term_type env NotGhost tm = Some (TE_ReturnType env)" and
          env'_eq: "env' = env"
          by (auto split: if_splits)
        from IH_term[OF "4.prems"(1,2) tm_ty]
        have tm_sound: "sound_term_result env (TE_ReturnType env) (interp_term fuel state tm)" .
        show ?thesis proof (cases "interp_term fuel state tm")
          case (Inl err)
          with tm_sound have "sound_error_result err" by simp
          with Inl CoreStmt_Return show ?thesis by simp
        next
          case (Inr val)
          with tm_sound have vht: "value_has_type env val (TE_ReturnType env)" by simp
          have interp_eq: "interp_statement (Suc fuel) state (CoreStmt_Return tm)
                          = Inr (Return state val)"
            using Inr by simp
          \<comment> \<open>Use env itself as env_mid (reflexivity of tyenv_fixed_eq).\<close>
          have "sound_statement_result env env' storeTyping (Inr (Return state val))"
            unfolding env'_eq using vht "4.prems"(1) "4.prems"(2)
            by (auto intro!: exI[of _ env] exI[of _ storeTyping] tyenv_fixed_eq_refl
                              storeTyping_extends_refl)
          with CoreStmt_Return interp_eq show ?thesis by simp
        qed
      next
        case (CoreStmt_Assert condTm proofBody)
        \<comment> \<open>Assert is a runtime no-op: Inr (Continue state), and env' = env.\<close>
        from typing CoreStmt_Assert have env'_eq: "env' = env"
          by (auto split: if_splits option.splits)
        have interp_eq: "interp_statement (Suc fuel) state (CoreStmt_Assert condTm proofBody)
                        = Inr (Continue state)"
          by simp
        from "4.prems"(1) env'_eq have "state_matches_env state env' storeTyping" by simp
        with CoreStmt_Assert interp_eq show ?thesis using storeTyping_extends_refl by auto
      next
        case (CoreStmt_Assume tm)
        \<comment> \<open>Assume is a runtime no-op: Inr (Continue state), and env' = env.\<close>
        from typing CoreStmt_Assume have env'_eq: "env' = env"
          by (auto split: if_splits)
        have interp_eq: "interp_statement (Suc fuel) state (CoreStmt_Assume tm)
                        = Inr (Continue state)"
          by simp
        from "4.prems"(1) env'_eq have "state_matches_env state env' storeTyping" by simp
        with CoreStmt_Assume interp_eq show ?thesis using storeTyping_extends_refl by auto
      next
        case (CoreStmt_While _ _ _ _ _) with typing show ?thesis sorry
      next
        case (CoreStmt_Match _ _ _) with typing show ?thesis sorry
      next
        case (CoreStmt_ShowHide showOrHide name)
        \<comment> \<open>ShowHide is a runtime no-op: Inr (Continue state), and env' = env.\<close>
        from typing CoreStmt_ShowHide have env'_eq: "env' = env" by simp
        have interp_eq: "interp_statement (Suc fuel) state (CoreStmt_ShowHide showOrHide name)
                        = Inr (Continue state)"
          by simp
        from "4.prems"(1) env'_eq have "state_matches_env state env' storeTyping" by simp
        with CoreStmt_ShowHide interp_eq show ?thesis using storeTyping_extends_refl by auto
      qed
    qed
  next
    case 5
    show ?case proof (intro impI)
      assume typing: "core_statement_list_type env NotGhost stmts = Some env'"
      have IH_stmt: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmt0 env0'.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                core_statement_type env0 NotGhost stmt0 = Some env0' \<Longrightarrow>
                sound_statement_result env0 env0' storeTyping0 (interp_statement fuel state0 stmt0)"
        by (simp add: "5.prems"(1,2) Suc.IH(4))
      have IH_stmts: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmts0 env0'.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                core_statement_list_type env0 NotGhost stmts0 = Some env0' \<Longrightarrow>
                sound_statement_result env0 env0' storeTyping0 (interp_statement_list fuel state0 stmts0)"
        by (simp add: "5.prems"(1,2) Suc.IH(5))
      show "sound_statement_result env env' storeTyping (interp_statement_list (Suc fuel) state stmts)"
      proof (cases stmts)
        case Nil
        with typing have "env' = env" by simp
        with "5.prems"(1) show ?thesis using Nil storeTyping_extends_refl by auto
      next
        case (Cons stmt0 stmts0)
        from typing Cons obtain env_mid where
          stmt_ty: "core_statement_type env NotGhost stmt0 = Some env_mid" and
          rest_ty: "core_statement_list_type env_mid NotGhost stmts0 = Some env'"
          by (auto split: option.splits)
        from IH_stmt[OF "5.prems"(1,2) stmt_ty]
        have stmt_sound: "sound_statement_result env env_mid storeTyping
                            (interp_statement fuel state stmt0)" .
        show ?thesis proof (cases "interp_statement fuel state stmt0")
          case (Inl err)
          with stmt_sound have "sound_error_result err" by simp
          with Inl Cons show ?thesis by simp
        next
          case (Inr result)
          then show ?thesis proof (cases result)
            case (Continue state')
            with Inr stmt_sound obtain storeTyping_mid where
              sme: "state_matches_env state' env_mid storeTyping_mid" and
              ext1: "storeTyping_extends storeTyping storeTyping_mid"
              by auto
            from core_statement_type_preserves_well_formed[OF stmt_ty "5.prems"(2)]
            have wf_mid: "tyenv_well_formed env_mid" .
            from IH_stmts[OF sme wf_mid rest_ty]
            have rest_sound: "sound_statement_result env_mid env' storeTyping_mid
                                (interp_statement_list fuel state' stmts0)" .
            from Inr Continue
            have interp_stmt_eq: "interp_statement fuel state stmt0 = Inr (Continue state')"
              by simp
            show ?thesis proof (cases "interp_statement_list fuel state' stmts0")
              case (Inl err)
              from rest_sound Inl have "sound_error_result err" by simp
              then show ?thesis using Cons interp_stmt_eq Inl by simp
            next
              case (Inr result2)
              then show ?thesis proof (cases result2)
                case (Continue state'')
                from rest_sound Inr Continue
                obtain storeTyping'' where
                  sme'': "state_matches_env state'' env' storeTyping''" and
                  ext2: "storeTyping_extends storeTyping_mid storeTyping''"
                  by auto
                from storeTyping_extends_trans[OF ext1 ext2]
                have "storeTyping_extends storeTyping storeTyping''" .
                with sme'' show ?thesis using Cons interp_stmt_eq Inr Continue by auto
              next
                case (Return state'' retVal2)
                \<comment> \<open>The rest of the list returned. We get env_mid2 between env_mid and env'.
                   We need env_mid2 between env and env'. Use monotonicity of the first stmt.\<close>
                from rest_sound Inr Return
                obtain env_mid2 storeTyping2 where
                  vht: "value_has_type env_mid retVal2 (TE_ReturnType env_mid)" and
                  sub1: "tyenv_fixed_eq env_mid env_mid2" and
                  sub2: "tyenv_fixed_eq env_mid2 env'" and
                  wf_env_mid2: "tyenv_well_formed env_mid2" and
                  sme2: "state_matches_env state'' env_mid2 storeTyping2" and
                  ext2: "storeTyping_extends storeTyping_mid storeTyping2"
                  by auto
                from storeTyping_extends_trans[OF ext1 ext2]
                have ext_full: "storeTyping_extends storeTyping storeTyping2" .
                from core_statement_type_fixed_eq[OF stmt_ty]
                have sub_env_envmid: "tyenv_fixed_eq env env_mid" .
                from tyenv_fixed_eq_trans[OF this sub1]
                have sub_env_mid2: "tyenv_fixed_eq env env_mid2" .
                \<comment> \<open>Transfer value_has_type from env_mid to env\<close>
                from sub_env_envmid
                have "TE_DataCtors env = TE_DataCtors env_mid"
                  "TE_Datatypes env = TE_Datatypes env_mid"
                  "TE_TypeVars env = TE_TypeVars env_mid"
                  "TE_GhostDatatypes env = TE_GhostDatatypes env_mid"
                  "TE_RuntimeTypeVars env = TE_RuntimeTypeVars env_mid"
                  "TE_ReturnType env = TE_ReturnType env_mid"
                  unfolding tyenv_fixed_eq_def by simp_all
                hence vht_env: "value_has_type env retVal2 (TE_ReturnType env)"
                  using vht value_has_type_cong_env by metis
                from \<open>interp_statement_list fuel state' stmts0 = Inr result2\<close> Return
                have interp_rest_eq: "interp_statement_list fuel state' stmts0 = Inr (Return state'' retVal2)"
                  by simp
                from vht_env sub_env_mid2 sub2 wf_env_mid2 sme2 ext_full
                show ?thesis
                  using Cons interp_stmt_eq interp_rest_eq by auto
              qed
            qed
          next
            case (Return state' retVal)
            \<comment> \<open>The first statement returned. We get env_mid2 between env and env_mid.
               We need env_mid2 between env and env'. Use monotonicity of the rest.\<close>
            with Inr stmt_sound obtain env_mid2 storeTyping2 where
              vht: "value_has_type env retVal (TE_ReturnType env)" and
              sub1: "tyenv_fixed_eq env env_mid2" and
              sub2: "tyenv_fixed_eq env_mid2 env_mid" and
              wf_env_mid2: "tyenv_well_formed env_mid2" and
              sme2: "state_matches_env state' env_mid2 storeTyping2" and
              ext: "storeTyping_extends storeTyping storeTyping2"
              by auto
            from core_statement_list_type_fixed_eq[OF rest_ty]
            have "tyenv_fixed_eq env_mid env'" .
            from tyenv_fixed_eq_trans[OF sub2 this]
            have "tyenv_fixed_eq env_mid2 env'" .
            with vht sub1 wf_env_mid2 sme2 ext
            show ?thesis using Inr Return Cons by auto
          qed
        qed
      qed
    qed
  next
    case 6

    show ?case
    proof -

      \<comment> \<open>The state's function table has an InterpFun for fnName that matches the
          env's FunInfo. This follows from state_matches_env via funs_exist_in_state,
          and from the function being non-ghost. \<close>
      have fes: "funs_exist_in_state state env"
        unfolding state_matches_env_def
        using "6.prems"(9) state_matches_env_def by auto
      obtain f where
        if_lookup: "fmlookup (IS_Functions state) fnName = Some f" and
        fi_match: "fun_info_matches_interp_fun env funInfo f"
        unfolding funs_exist_in_state_def
        by (metis "6.prems"(1,2) case_optionE fes funs_exist_in_state_def)

      \<comment> \<open>Basic shape of the InterpFun matches the FunInfo. From fun_info_matches_interp_fun.\<close>
      from fi_match have len_args: "length (IF_Args f) = length (FI_TmArgs funInfo)"
        unfolding fun_info_matches_interp_fun_def by simp
      from fi_match have var_ref_match:
        "list_all2 (\<lambda>(name1, _, vor1) (name2, vor2). name1 = name2 \<and> vor1 = vor2)
                   (FI_TmArgs funInfo) (IF_Args f)"
        unfolding fun_info_matches_interp_fun_def by simp

      \<comment> \<open>Names from the interpreter's interp_function_call definition. We name them
          with let so that we can refer to them in helper-lemma applications below. \<close>
      let ?refResults = "map (interp_writable_lvalue fuel state) argTms"
      let ?valResults = "map (interp_term fuel state) argTms"
      let ?argTuples = "zip (IF_Args f) (zip ?refResults ?valResults)"
      let ?clearedState = "state \<lparr> IS_Locals := fmempty,
                                    IS_Refs := fmempty,
                                    IS_ConstLocals := {||} \<rparr>"

      \<comment> \<open>Length of argTms equals number of formal parameters and number of IF_Args. \<close>
      have len_argTms: "length argTms = length (FI_TmArgs funInfo)"
        using "6.prems"(3) by (simp add: list_all2_lengthD)
      have len_argTms_args: "length argTms = length (IF_Args f)"
        using len_argTms len_args by simp

      \<comment> \<open>The type substitution that specializes the callee's type arguments to the
          caller's concrete type arguments. \<close>
      let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"

      \<comment> \<open>The body environment as it appears at the call site, before substitution:
          the formal parameters, callee's own type variables, callee's return type. \<close>
      define bodyEnv0 where "bodyEnv0 = body_env_for env funInfo"

      \<comment> \<open>The body environment after substituting the callee's type arguments. This is
          the env in which we expect the body to evaluate at this call site:
          locals have caller-instantiated types, TE_TypeVars / TE_RuntimeTypeVars
          drop the now-bound callee type variables and pick up the caller's, and
          TE_ReturnType becomes apply_subst ?tySubst (FI_ReturnType funInfo) = retTy. \<close>
      define bodyEnv where "bodyEnv = apply_subst_to_callee_env ?tySubst env bodyEnv0"

      \<comment> \<open>The substituted return type equals retTy by 6.prems(4). \<close>
      have bodyEnv_TE_ReturnType: "TE_ReturnType bodyEnv = retTy"
        unfolding bodyEnv_def bodyEnv0_def
        using "6.prems"(4) by (simp add: body_env_for_def)

      show "sound_function_call_result env storeTyping retTy
              (interp_function_call (Suc fuel) state fnName argTms)"
      proof (cases "IF_Body f")
        case Inl_body: (Inl bodyStmts)
        \<comment> \<open>Core-body case.\<close>

        \<comment> \<open>Body-welltyped premise from fi_match. We get a witness env' for the result
            of typechecking; we don't actually care what it is. \<close>
        have body_typed_unsubst_ex:
          "\<exists>env'. core_statement_list_type (body_env_for env funInfo) NotGhost bodyStmts
                    = Some env'"
          using fi_match Inl_body
          unfolding fun_info_matches_interp_fun_def
          by (auto split: sum.splits)
        then obtain bodyEnv' where
          body_typed_unsubst: "core_statement_list_type (body_env_for env funInfo)
                                 NotGhost bodyStmts = Some bodyEnv'"
          by blast

        \<comment> \<open>Establish the preconditions of core_statement_list_type_subst_callee_env. \<close>
        have wf_bodyEnv0: "tyenv_well_formed bodyEnv0"
          unfolding bodyEnv0_def
          using body_env_for_well_formed[OF "6.prems"(10) "6.prems"(1) "6.prems"(2)] .

        \<comment> \<open>FI_TyArgs are distinct (from tyenv_fun_tyvars_distinct). Combined with
            len_tyargs from "6.prems"(5), this lets us compute the substitution's range. \<close>
        have distinct_tyArgs: "distinct (FI_TyArgs funInfo)"
          using "6.prems"(10) "6.prems"(1)
          unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def
          by blast

        have subst_range_eq: "fmran' ?tySubst = set tyArgs"
          using fmran'_fmap_of_list_zip[OF "6.prems"(5)[symmetric] distinct_tyArgs] .

        have subst_range_wk: "\<forall>ty' \<in> fmran' ?tySubst. is_well_kinded env ty'"
          using subst_range_eq "6.prems"(6) by (auto simp: list_all_iff)

        have subst_range_rt: "\<forall>ty' \<in> fmran' ?tySubst. is_runtime_type env ty'"
          using subst_range_eq "6.prems"(7) by (auto simp: list_all_iff)

        \<comment> \<open>callee_env_subst_ok ?tySubst env bodyEnv0:
            - global-field agreement: bodyEnv0 = body_env_for env funInfo inherits these
              fields from env, so they trivially agree.
            - tyvar conditions: bodyEnv0's TE_TypeVars are fset_of_list (FI_TyArgs funInfo),
              and ?tySubst's domain is exactly the same set, so every tyvar in
              bodyEnv0 maps to a value in tyArgs (which we already know is well-kinded
              in env). \<close>
        have ok: "callee_env_subst_ok ?tySubst env bodyEnv0"
          unfolding callee_env_subst_ok_def
        proof (intro conjI)
          show "TE_GlobalVars env = TE_GlobalVars bodyEnv0"
            and "TE_GhostGlobals env = TE_GhostGlobals bodyEnv0"
            and "TE_Functions env = TE_Functions bodyEnv0"
            and "TE_Datatypes env = TE_Datatypes bodyEnv0"
            and "TE_DataCtors env = TE_DataCtors bodyEnv0"
            and "TE_DataCtorsByType env = TE_DataCtorsByType bodyEnv0"
            and "TE_GhostDatatypes env = TE_GhostDatatypes bodyEnv0"
            by (simp_all add: bodyEnv0_def body_env_for_def)
        next
          show "\<forall>n. n |\<in>| TE_TypeVars bodyEnv0 \<longrightarrow>
                  (case fmlookup ?tySubst n of
                    Some ty' \<Rightarrow> is_well_kinded env ty'
                  | None \<Rightarrow> n |\<in>| TE_TypeVars env)"
          proof (intro allI impI)
            fix n assume "n |\<in>| TE_TypeVars bodyEnv0"
            hence n_in: "n \<in> set (FI_TyArgs funInfo)"
              by (simp add: bodyEnv0_def body_env_for_def fset_of_list.rep_eq)
            have dom_eq: "fset (fmdom ?tySubst) = set (FI_TyArgs funInfo)"
              using fmdom_fmap_of_list_zip[OF "6.prems"(5)[symmetric]] .
            from n_in dom_eq have "n |\<in>| fmdom ?tySubst"
              by simp
            then obtain ty' where lk: "fmlookup ?tySubst n = Some ty'"
              by (metis fmlookup_dom_iff)
            with subst_range_wk have "is_well_kinded env ty'"
              by (auto intro: fmran'I)
            with lk show "case fmlookup ?tySubst n of
                            Some ty' \<Rightarrow> is_well_kinded env ty'
                          | None \<Rightarrow> n |\<in>| TE_TypeVars env"
              by simp
          qed
        qed

        \<comment> \<open>callee_env_subst_runtime_ok holds because the substitution range is runtime
            in env (which it always is in this case, since the call is non-ghost). \<close>
        have ok_rt: "callee_env_subst_runtime_ok ?tySubst env bodyEnv0"
          unfolding callee_env_subst_runtime_ok_def
        proof (intro allI impI)
          fix n assume "n |\<in>| TE_RuntimeTypeVars bodyEnv0"
          hence n_in: "n \<in> set (FI_TyArgs funInfo)"
            by (simp add: bodyEnv0_def body_env_for_def fset_of_list.rep_eq)
          have dom_eq: "fset (fmdom ?tySubst) = set (FI_TyArgs funInfo)"
            using fmdom_fmap_of_list_zip[OF "6.prems"(5)[symmetric]] .
          from n_in dom_eq have "n |\<in>| fmdom ?tySubst" by simp
          then obtain ty' where lk: "fmlookup ?tySubst n = Some ty'"
            by (meson fmlookup_dom_iff)
          with subst_range_rt have "is_runtime_type env ty'"
            by (auto intro: fmran'I)
          with lk show "case fmlookup ?tySubst n of
                          Some ty' \<Rightarrow> is_runtime_type env ty'
                        | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
            by simp
        qed

        \<comment> \<open>HELPER 1: discharge body_typed via core_statement_list_type_subst_callee_env.
            The lemma substitutes both syntax and env, so the typechecked body here
            is the substituted body. The interpreter actually runs the unsubstituted
            body; the erasure lemma (TODO) bridges that gap. \<close>
        define bodyEnv'' where
          "bodyEnv'' = apply_subst_to_callee_env ?tySubst env bodyEnv'"
        define bodyStmts' where
          "bodyStmts' = apply_subst_to_stmt_list ?tySubst bodyStmts"
        have body_typed:
          "core_statement_list_type bodyEnv NotGhost bodyStmts' = Some bodyEnv''"
          unfolding bodyEnv_def bodyEnv''_def bodyStmts'_def
          using core_statement_list_type_subst_callee_env
                  [OF body_typed_unsubst[unfolded bodyEnv0_def[symmetric]]
                      wf_bodyEnv0 ok subst_range_wk]
                subst_range_rt ok_rt by blast

        \<comment> \<open>HELPER 2 (arg processing soundness). The fold over process_one_arg either
            errors (in which case the result is a sound error) or produces a
            preCallState matching bodyEnv under some bodyStoreTyping that extends
            storeTyping. Rough shape:

              state_matches_env state env storeTyping
              \<Longrightarrow> length argTms = length (FI_TmArgs funInfo)
              \<Longrightarrow> name/var-ref agreement (var_ref_match)
              \<Longrightarrow> args list_all2 typing ("6.prems"(3))
              \<Longrightarrow> sound_arg_processing_result env bodyEnv storeTyping
                    (fold process_one_arg ?argTuples (Inr ?clearedState))

            where sound_arg_processing_result is something like:
              Inl err   \<longrightarrow> sound_error_result err
              Inr state \<longrightarrow> \<exists>bodyStoreTyping.
                  state_matches_env state bodyEnv bodyStoreTyping
                \<and> storeTyping_extends storeTyping bodyStoreTyping

            Whether to phrase it as a custom predicate or inline it is a detail
            we'll resolve when we write the helper. \<close>

        \<comment> \<open>HELPER 3: bodyEnv well-formed via apply_subst_to_callee_env_well_formed.
            We need is_well_kinded / is_runtime_type of the substituted return type
            in env. The unsubstituted FI_ReturnType is well-kinded and runtime in
            env's-with-FI_TyArgs-as-TE_TypeVars (from tyenv_fun_types_well_kinded
            and tyenv_fun_ghost_constraint), and tyArgs are well-kinded and runtime
            in env, so apply_subst_specializes_well_kinded / _runtime conclude. \<close>
        have fi_ret_wk_inner:
          "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                          (FI_ReturnType funInfo)"
          using "6.prems"(10) "6.prems"(1)
          unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def
          by blast
        have fi_ret_rt_inner:
          "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                   TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                           (FI_ReturnType funInfo)"
          using "6.prems"(10) "6.prems"(1) "6.prems"(2)
          unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def
          by auto

        have ret_wk: "is_well_kinded env (apply_subst ?tySubst (TE_ReturnType bodyEnv0))"
          using apply_subst_specializes_well_kinded[OF fi_ret_wk_inner "6.prems"(6)
                                                       "6.prems"(5)[symmetric]]
          by (simp add: bodyEnv0_def body_env_for_def)

        have ret_rt: "TE_FunctionGhost bodyEnv0 = NotGhost \<Longrightarrow>
                       is_runtime_type env (apply_subst ?tySubst (TE_ReturnType bodyEnv0))"
          using apply_subst_specializes_runtime[OF fi_ret_rt_inner "6.prems"(7)
                                                    "6.prems"(5)[symmetric]]
          by (simp add: bodyEnv0_def body_env_for_def)

        have wf_bodyEnv: "tyenv_well_formed bodyEnv"
          unfolding bodyEnv_def
          using apply_subst_to_callee_env_well_formed[OF wf_bodyEnv0 "6.prems"(10) ok ok_rt ret_wk ret_rt] .

        \<comment> \<open>HELPER 2 (arg processing soundness): invoke fold_process_one_arg_sound
            to conclude that the arg fold is a sound arg processing result.
            The writable-lvalue witness for Ref positions is supplied by the
            caller (either via core_impure_call_type_fn_facts for impure
            calls, or vacuously for pure calls where all args are Var). \<close>
        have argTms_lvalues:
          "\<forall>i < length argTms.
             (snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
              is_writable_lvalue env (argTms ! i))"
          using "6.prems"(8) .
        have argTms_typed:
          "list_all2 (\<lambda>tm expectedTy. core_term_type env NotGhost tm = Some expectedTy)
             argTms (map (\<lambda>(_, ty, _). apply_subst ?tySubst ty) (FI_TmArgs funInfo))"
          using "6.prems"(3) by (auto simp: list_all2_iff split: option.splits)

        \<comment> \<open>Bind the term- and writable-lvalue-soundness IHs locally so they can be
            applied per argTm. \<close>
        have IH_term: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 tm0 ty0.
              state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
              tyenv_well_formed env0 \<Longrightarrow>
              core_term_type env0 NotGhost tm0 = Some ty0 \<Longrightarrow>
              sound_term_result env0 ty0 (interp_term fuel state0 tm0)"
          using Suc.IH(1) by simp
        have IH_lvalue: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 tm0 ty0.
              state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
              tyenv_well_formed env0 \<Longrightarrow>
              is_writable_lvalue env0 tm0 \<Longrightarrow>
              core_term_type env0 NotGhost tm0 = Some ty0 \<Longrightarrow>
              sound_lvalue_result state0 env0 storeTyping0 ty0
                (interp_writable_lvalue fuel state0 tm0)"
          using Suc.IH(3) by simp

        \<comment> \<open>Per-position soundness of interp_term on each argTm at its expected type. \<close>
        have vals_sound:
          "\<forall>i < length (FI_TmArgs funInfo).
             sound_term_result env
               (apply_subst ?tySubst (fst (snd (FI_TmArgs funInfo ! i))))
               (map (interp_term fuel state) argTms ! i)"
        proof (intro allI impI)
          fix i assume i_lt: "i < length (FI_TmArgs funInfo)"
          with len_argTms have i_lt_tms: "i < length argTms" by simp
          from argTms_typed i_lt_tms i_lt
          have tm_typed: "core_term_type env NotGhost (argTms ! i)
                            = Some (apply_subst ?tySubst (fst (snd (FI_TmArgs funInfo ! i))))"
            by (auto simp: list_all2_conv_all_nth split_def)
          from IH_term[OF "6.prems"(9) "6.prems"(10) tm_typed]
          have "sound_term_result env
                  (apply_subst ?tySubst (fst (snd (FI_TmArgs funInfo ! i))))
                  (interp_term fuel state (argTms ! i))" .
          thus "sound_term_result env
                  (apply_subst ?tySubst (fst (snd (FI_TmArgs funInfo ! i))))
                  (map (interp_term fuel state) argTms ! i)"
            using i_lt_tms by simp
        qed

        \<comment> \<open>Per-position soundness of interp_writable_lvalue on each Ref-parameter argTm. \<close>
        have lvals_sound:
          "\<forall>i < length (FI_TmArgs funInfo).
             snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
               sound_lvalue_result state env storeTyping
                 (apply_subst ?tySubst (fst (snd (FI_TmArgs funInfo ! i))))
                 (map (interp_writable_lvalue fuel state) argTms ! i)"
        proof (intro allI impI)
          fix i
          assume i_lt: "i < length (FI_TmArgs funInfo)"
          assume is_ref: "snd (snd (FI_TmArgs funInfo ! i)) = Ref"
          with len_argTms i_lt have i_lt_tms: "i < length argTms" by simp
          from argTms_lvalues i_lt_tms is_ref
          have is_wl: "is_writable_lvalue env (argTms ! i)" by simp
          from argTms_typed i_lt_tms i_lt
          have tm_typed: "core_term_type env NotGhost (argTms ! i)
                            = Some (apply_subst ?tySubst (fst (snd (FI_TmArgs funInfo ! i))))"
            by (auto simp: list_all2_conv_all_nth split_def)
          from IH_lvalue[OF "6.prems"(9) "6.prems"(10) is_wl tm_typed]
          have "sound_lvalue_result state env storeTyping
                  (apply_subst ?tySubst (fst (snd (FI_TmArgs funInfo ! i))))
                  (interp_writable_lvalue fuel state (argTms ! i))" .
          thus "sound_lvalue_result state env storeTyping
                  (apply_subst ?tySubst (fst (snd (FI_TmArgs funInfo ! i))))
                  (map (interp_writable_lvalue fuel state) argTms ! i)"
            using i_lt_tms by simp
        qed

        have arg_proc_sound:
          "sound_arg_processing_result env funInfo ?tySubst storeTyping
             (fold process_one_arg ?argTuples (Inr ?clearedState))"
          using fold_process_one_arg_sound[OF "6.prems"(9,10,1,2) fi_match
                                              vals_sound lvals_sound len_argTms] .

        show ?thesis
        proof (cases "fold process_one_arg ?argTuples (Inr ?clearedState)")
          case Inl_fold: (Inl err)
          \<comment> \<open>Arg processing errored. Helper 2 gives us sound_error_result. \<close>
          from arg_proc_sound Inl_fold have err_sound: "sound_error_result err"
            by (simp add: sound_arg_processing_result_def)
          have interp_eq:
            "interp_function_call (Suc fuel) state fnName argTms = Inl err"
            using if_lookup len_argTms_args Inl_body Inl_fold
            by (simp add: Let_def)
          show ?thesis using err_sound interp_eq by simp
        next
          case Inr_fold: (Inr preCallState)
          \<comment> \<open>Arg processing succeeded. Helper 2 gives us a store typing for
              the cleared+populated state that matches bodyEnv. \<close>
          from arg_proc_sound Inr_fold have arg_proc_ok:
            "\<exists>bodyStoreTyping.
              state_matches_env preCallState bodyEnv bodyStoreTyping
            \<and> storeTyping_extends storeTyping bodyStoreTyping"
            unfolding sound_arg_processing_result_def bodyEnv_def bodyEnv0_def by simp
          then obtain bodyStoreTyping where
            sme_pre: "state_matches_env preCallState bodyEnv bodyStoreTyping" and
            ext_pre: "storeTyping_extends storeTyping bodyStoreTyping"
            by blast

          \<comment> \<open>Apply the statement-list IH to the body. \<close>
          have IH_stmts: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmts0 env0'.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                core_statement_list_type env0 NotGhost stmts0 = Some env0' \<Longrightarrow>
                sound_statement_result env0 env0' storeTyping0
                  (interp_statement_list fuel state0 stmts0)"
            using Suc.IH(5) by simp
          from IH_stmts[OF sme_pre wf_bodyEnv body_typed]
          have body_sound_subst:
            "sound_statement_result bodyEnv bodyEnv'' bodyStoreTyping
               (interp_statement_list fuel preCallState bodyStmts')" .

          \<comment> \<open>HELPER 5 (erasure). The interpreter's result on the substituted body
              equals its result on the original body, because the syntactic
              substitution only affects types embedded in the syntax which the
              interpreter ignores at runtime. Proved in CoreInterpErasure.thy. \<close>
          have erase_eq:
            "interp_statement_list fuel preCallState bodyStmts'
               = interp_statement_list fuel preCallState bodyStmts"
            using interp_erasure(5)[of bodyStmts fuel]
                  body_typed_unsubst
            unfolding bodyStmts'_def by blast
          have body_sound: "sound_statement_result bodyEnv bodyEnv'' bodyStoreTyping
                              (interp_statement_list fuel preCallState bodyStmts)"
            using body_sound_subst erase_eq by simp

          show ?thesis
          proof (cases "interp_statement_list fuel preCallState bodyStmts")
            case Inl_body_res: (Inl err)
            \<comment> \<open>Body errored. body_sound gives sound_error_result. \<close>
            with body_sound have err_sound: "sound_error_result err" by simp
            have interp_eq:
              "interp_function_call (Suc fuel) state fnName argTms = Inl err"
              using if_lookup len_argTms_args Inl_body Inr_fold Inl_body_res
              by (simp add: Let_def)
            show ?thesis using err_sound interp_eq by simp
          next
            case Inr_body_res: (Inr res)
            then show ?thesis proof (cases res)
              case (Continue postState)
              \<comment> \<open>Body fell off the end without returning. The interpreter then
                  produces RuntimeError, which is a sound error. \<close>
              have interp_eq:
                "interp_function_call (Suc fuel) state fnName argTms = Inl RuntimeError"
                using if_lookup len_argTms_args Inl_body Inr_fold Inr_body_res Continue
                by (simp add: Let_def)
              show ?thesis using interp_eq by simp
            next
              case (Return postCallState retVal)
              \<comment> \<open>Body returned. Extract the return-case fields. \<close>
              from body_sound Inr_body_res Return
              have body_sound_ret:
                "sound_statement_result bodyEnv bodyEnv'' bodyStoreTyping
                   (Inr (Return postCallState retVal))"
                by simp
              from body_sound_ret
              have vht_body_ret: "value_has_type bodyEnv retVal (TE_ReturnType bodyEnv)"
                and body_ret_exists:
                  "\<exists>env_mid storeTyping'. tyenv_fixed_eq bodyEnv env_mid
                    \<and> tyenv_fixed_eq env_mid bodyEnv''
                    \<and> tyenv_well_formed env_mid
                    \<and> state_matches_env postCallState env_mid storeTyping'
                    \<and> storeTyping_extends bodyStoreTyping storeTyping'"
                by simp_all
              from body_ret_exists obtain env_mid postStoreTyping where
                fxeq1: "tyenv_fixed_eq bodyEnv env_mid" and
                fxeq2: "tyenv_fixed_eq env_mid bodyEnv''" and
                wf_env_mid: "tyenv_well_formed env_mid" and
                sme_post: "state_matches_env postCallState env_mid postStoreTyping" and
                ext_post: "storeTyping_extends bodyStoreTyping postStoreTyping"
                by blast
              from vht_body_ret fxeq1
              have vht_mid: "value_has_type env_mid retVal (TE_ReturnType env_mid)"
                unfolding tyenv_fixed_eq_def using value_has_type_cong_env by metis

              \<comment> \<open>Transfer value_has_type from env_mid to bodyEnv via the fixed-eq, and
                  observe TE_ReturnType bodyEnv = retTy. \<close>
              have vht_retTy_bodyEnv: "value_has_type bodyEnv retVal retTy"
              proof -
                from fxeq1 have ret_eq: "TE_ReturnType env_mid = TE_ReturnType bodyEnv"
                  unfolding tyenv_fixed_eq_def by simp
                from fxeq1 have field_eq:
                  "TE_DataCtors env_mid = TE_DataCtors bodyEnv"
                  "TE_Datatypes env_mid = TE_Datatypes bodyEnv"
                  "TE_TypeVars env_mid = TE_TypeVars bodyEnv"
                  "TE_GhostDatatypes env_mid = TE_GhostDatatypes bodyEnv"
                  "TE_RuntimeTypeVars env_mid = TE_RuntimeTypeVars bodyEnv"
                  unfolding tyenv_fixed_eq_def by simp_all
                from vht_mid ret_eq bodyEnv_TE_ReturnType
                have "value_has_type env_mid retVal retTy" by simp
                thus ?thesis using field_eq value_has_type_cong_env by metis
              qed

              \<comment> \<open>Transfer value_has_type from bodyEnv to env. The value_has_type
                  predicate depends only on TE_DataCtors, TE_Datatypes, TE_TypeVars,
                  TE_GhostDatatypes, TE_RuntimeTypeVars; bodyEnv inherits the first
                  four from env (via body_env_for) and we explicitly set TE_TypeVars /
                  TE_RuntimeTypeVars := those of env in the substituted env. \<close>
              have vht_retTy_env: "value_has_type env retVal retTy"
              proof -
                have field_eq:
                  "TE_DataCtors bodyEnv = TE_DataCtors env"
                  "TE_Datatypes bodyEnv = TE_Datatypes env"
                  "TE_TypeVars bodyEnv = TE_TypeVars env"
                  "TE_GhostDatatypes bodyEnv = TE_GhostDatatypes env"
                  "TE_RuntimeTypeVars bodyEnv = TE_RuntimeTypeVars env"
                  by (simp_all add: bodyEnv_def bodyEnv0_def body_env_for_def
                                    apply_subst_to_callee_env_def)
                from vht_retTy_bodyEnv field_eq show ?thesis
                  using value_has_type_cong_env by metis
              qed

              \<comment> \<open>HELPER 4 (restore_scope soundness). Apply the standalone
                  restore_scope_sound lemma with finalStoreTyping = storeTyping. \<close>

              \<comment> \<open>Chain storeTyping extensions to get storeTyping \<le> postStoreTyping. \<close>
              have ext_full: "storeTyping_extends storeTyping postStoreTyping"
                using storeTyping_extends_trans[OF ext_pre ext_post] .

              \<comment> \<open>Globals/functions preservation from state through the whole call. The
                  clearedState step is a direct record update that only touches
                  locals/refs/const-names. The fold step and the body step go through
                  the interpreter-preservation corollaries. \<close>
              let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                             IS_ConstLocals := {||} \<rparr>"
              have cleared_gf:
                "IS_Globals ?clearedState = IS_Globals state"
                "IS_Functions ?clearedState = IS_Functions state"
                by simp_all
              from fold_process_one_arg_preserves_globals_funs[OF Inr_fold]
              have pre_gf:
                "IS_Globals preCallState = IS_Globals ?clearedState"
                "IS_Functions preCallState = IS_Functions ?clearedState"
                by simp_all
              from Inr_body_res Return
              have body_eq: "interp_statement_list fuel preCallState bodyStmts
                              = Inr (Return postCallState retVal)"
                by simp
              have post_g_pre: "IS_Globals postCallState = IS_Globals preCallState"
                using interp_statement_list_return_preserves_globals[OF body_eq] .
              have post_f_pre: "IS_Functions postCallState = IS_Functions preCallState"
                using interp_statement_list_return_preserves_functions[OF body_eq] .
              have post_globals_eq: "IS_Globals postCallState = IS_Globals state"
                using post_g_pre pre_gf cleared_gf by simp
              have post_functions_eq: "IS_Functions postCallState = IS_Functions state"
                using post_f_pre pre_gf cleared_gf by simp

              \<comment> \<open>Datatype-field equality between env and env_mid. bodyEnv inherits
                  DataCtors / Datatypes / GhostDatatypes from env via body_env_for,
                  and fxeq1 transfers them to env_mid. \<close>
              have body_dt_eq:
                "TE_DataCtors bodyEnv = TE_DataCtors env"
                "TE_Datatypes bodyEnv = TE_Datatypes env"
                "TE_GhostDatatypes bodyEnv = TE_GhostDatatypes env"
                by (simp_all add: bodyEnv_def bodyEnv0_def body_env_for_def
                                  apply_subst_to_callee_env_def)
              from fxeq1 have fx_dt_eq:
                "TE_DataCtors bodyEnv = TE_DataCtors env_mid"
                "TE_Datatypes bodyEnv = TE_Datatypes env_mid"
                "TE_GhostDatatypes bodyEnv = TE_GhostDatatypes env_mid"
                unfolding tyenv_fixed_eq_def by simp_all
              have env_env_mid_dt:
                "TE_DataCtors env = TE_DataCtors env_mid"
                "TE_Datatypes env = TE_Datatypes env_mid"
                "TE_GhostDatatypes env = TE_GhostDatatypes env_mid"
                using body_dt_eq fx_dt_eq by simp_all

              have sme_final: "state_matches_env (restore_scope state postCallState)
                                env storeTyping"
                using restore_scope_sound[OF "6.prems"(9) sme_post ext_full
                                             post_globals_eq post_functions_eq
                                             env_env_mid_dt(1) env_env_mid_dt(2)
                                             env_env_mid_dt(3)
                                             "6.prems"(10) wf_env_mid] .
              have ext_final: "storeTyping_extends storeTyping storeTyping"
                using storeTyping_extends_refl .
              let ?finalStoreTyping = storeTyping

              \<comment> \<open>Plumb the final state and the return value through interp_function_call's
                  case structure. \<close>
              have interp_eq:
                "interp_function_call (Suc fuel) state fnName argTms
                   = Inr (restore_scope state postCallState, retVal)"
                using if_lookup len_argTms_args Inl_body Inr_fold Inr_body_res Return
                by (simp add: Let_def)
              show ?thesis
                using interp_eq sme_final ext_final vht_retTy_env by auto
            qed
          qed
        qed

      next
        case (Inr externFun)
        \<comment> \<open>Extern-function case. Deferred — depends on extern_fun_contract being
            given a real definition. \<close>
        show ?thesis
          sorry
      qed
    qed
  }
qed


end

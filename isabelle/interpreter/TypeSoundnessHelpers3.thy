theory TypeSoundnessHelpers3
  imports TypeSoundnessHelpers2
begin

(*-----------------------------------------------------------------------------*)
(* Type soundness for terms *)
(*-----------------------------------------------------------------------------*)

(* Type soundness for Cast *)
lemma type_soundness_cast:
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Cast target_ty operand) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_Cast target_ty operand))"
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
  have operand_sound: "sound_term_result state env operand_ty (interp_term fuel state operand)"
    by simp

  (* Case split on operand result *)
  show ?thesis
  proof (cases "interp_term fuel state operand")
    case (Inr operand_val)
    (* Operand succeeded - extract type information *)
    from operand_sound Inr operand_is_int
    have operand_typed: "value_has_type env operand_val operand_ty"
      by (simp add: is_integer_type_apply_subst)

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
                        sound_term_result state env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Unop unop operand) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_Unop unop operand))"
proof (cases unop)
  case CoreUnop_Negate
  (* Extract facts from typing *)
  from typing CoreUnop_Negate have
    operand_typing: "core_term_type env NotGhost operand = Some ty"
    and signed_numeric: "is_signed_numeric_type ty"
    by (auto split: option.splits if_splits)

  (* Apply IH to operand *)
  from IH[OF operand_typing]
  have operand_sound: "sound_term_result state env ty (interp_term fuel state operand)"
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
    from operand_sound Inr signed_numeric
    have operand_typed: "value_has_type env operand_val ty"
      by (simp add: is_signed_numeric_type_apply_subst)

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
  have operand_sound: "sound_term_result state env ty (interp_term fuel state operand)"
    by simp

  (* Case split on operand result *)
  show ?thesis
  proof (cases "interp_term fuel state operand")
    case (Inl err)
    then show ?thesis using operand_sound by auto
  next
    case (Inr operand_val)
    from operand_sound Inr finite_int
    have operand_typed: "value_has_type env operand_val ty"
      by (simp add: is_finite_integer_type_apply_subst)

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
  have operand_sound: "sound_term_result state env CoreTy_Bool (interp_term fuel state operand)"
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
  shows "sound_term_result state env (CoreTy_FiniteInt sign bits) (generic_int_binop f v1 v2)"
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
  shows "sound_term_result state env CoreTy_Bool (generic_int_cmp_binop f v1 v2)"
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
  shows "sound_term_result state env CoreTy_Bool (generic_bool_binop f v1 v2)"
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
                        sound_term_result state env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Binop op lhs rhs) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_Binop op lhs rhs))"
proof -
  (* Extract facts from typing *)
  from typing obtain lhsTy rhsTy where
    lhs_typing: "core_term_type env NotGhost lhs = Some lhsTy" and
    rhs_typing: "core_term_type env NotGhost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)

  (* Apply IH to operands *)
  from IH[OF lhs_typing] have lhs_sound: "sound_term_result state env lhsTy (interp_term fuel state lhs)" .
  from IH[OF rhs_typing] have rhs_sound: "sound_term_result state env rhsTy (interp_term fuel state rhs)" .

  (* Case split on lhs evaluation *)
  show ?thesis
  proof (cases "interp_term fuel state lhs")
    case (Inl err)
    (* LHS failed - propagate error *)
    then have "interp_term (Suc fuel) state (CoreTm_Binop op lhs rhs) = Inl err" by simp
    with lhs_sound Inl show ?thesis by auto
  next
    case (Inr lhsVal)
    from lhs_sound Inr binop_operand_apply_subst(1)[OF typing lhs_typing rhs_typing]
    have lhs_typed: "value_has_type env lhsVal lhsTy" by simp

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
      from rhs_sound Inr binop_operand_apply_subst(2)[OF typing lhs_typing rhs_typing]
      have rhs_typed: "value_has_type env rhsVal rhsTy" by simp

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
                sound_term_result state' env' ty' (interp_term fuel state' tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Let var rhs body) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_Let var rhs body))"
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
  have rhs_sound: "sound_term_result state env rhsTy (interp_term fuel state rhs)" .

  show ?thesis
  proof (cases "interp_term fuel state rhs")
    case (Inl err)
    (* RHS failed - propagate error *)
    then have "interp_term (Suc fuel) state (CoreTm_Let var rhs body) = Inl err"
      by simp
    with rhs_sound Inl show ?thesis by auto
  next
    case (Inr rhsVal)
    (* RHS succeeded. rhsTy may mention runtime tyvars; rhsVal satisfies the
       substituted (ground) form. storeTyping is extended with that ground form. *)
    from rhs_sound Inr
    have rhs_typed: "value_has_type env rhsVal (apply_subst (IS_TyArgs state) rhsTy)"
      by simp

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
    have state''_env': "state_matches_env ?state'' ?env'
                          (storeTyping @ [apply_subst (IS_TyArgs state) rhsTy])"
      using state_matches_env_add_const_local[OF state_env rhs_typed alloc_eq refl refl]
      by simp

    (* The extended env is well-formed *)
    have rhs_rt: "is_runtime_type env rhsTy"
      using core_term_type_notghost_runtime[OF rhs_typing wf_env] .
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
    have body_sound: "sound_term_result ?state'' ?env' ty (interp_term fuel ?state'' body)" .

    (* sound_term_result env' = sound_term_result env, because value_has_type
       only depends on datatypes, not TE_LocalVars/TE_GlobalVars/TE_GhostLocals *)
    have env'_fields: "TE_DataCtors ?env' = TE_DataCtors env"
                       "TE_Datatypes ?env' = TE_Datatypes env"
                       "TE_TypeVars ?env' = TE_TypeVars env"
                       "TE_GhostDatatypes ?env' = TE_GhostDatatypes env"
                       "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env"
      by simp_all
    have vht_eq: "\<And>v t. value_has_type ?env' v t = value_has_type env v t"
      using value_has_type_cong_env[OF env'_fields] .
    have tyargs_eq: "IS_TyArgs ?state'' = IS_TyArgs state"
      using alloc_eq by auto
    from body_sound vht_eq tyargs_eq
    have "sound_term_result state env ty (interp_term fuel ?state'' body)"
      by (cases "interp_term fuel ?state'' body") auto
    with interp_eq show ?thesis by simp
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
                sound_term_result state' env' ty' (interp_term fuel state' tm')"
    and typing: "core_term_type env NotGhost (CoreTm_RecordProj tm fldName) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_RecordProj tm fldName))"
proof -
  (* Extract facts from typing *)
  from typing obtain fieldTypes where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Record fieldTypes)" and
    fld_lookup: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)

  (* Apply IH to tm *)
  from IH[OF state_env wf_env tm_typing]
  have tm_sound: "sound_term_result state env (CoreTy_Record fieldTypes) (interp_term fuel state tm)" .

  show ?thesis
  proof (cases "interp_term fuel state tm")
    case (Inl err)
    (* tm failed - propagate error *)
    then have "interp_term (Suc fuel) state (CoreTm_RecordProj tm fldName) = Inl err"
      by simp
    with tm_sound Inl show ?thesis by auto
  next
    case (Inr val)
    (* tm succeeded. The substituted field types are what value_has_type sees. *)
    let ?subFieldTypes = "map (\<lambda>(n, t). (n, apply_subst (IS_TyArgs state) t)) fieldTypes"
    from tm_sound Inr
    have val_typed: "value_has_type env val (CoreTy_Record ?subFieldTypes)" by simp

    (* Value must be CV_Record *)
    from val_typed obtain fieldValues where
      val_eq: "val = CV_Record fieldValues" and
      fields_rel: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t)
                     fieldValues ?subFieldTypes"
      by (cases val) (auto split: CoreType.splits)

    (* Lift fld_lookup through the apply_subst on field types *)
    have fld_lookup_sub:
      "map_of ?subFieldTypes fldName = Some (apply_subst (IS_TyArgs state) ty)"
      using fld_lookup by (induction fieldTypes) auto

    (* map_of fieldValues fldName succeeds with the right (substituted) type *)
    from map_of_list_all2[OF fields_rel fld_lookup_sub]
    obtain fldVal where
      fld_val_lookup: "map_of fieldValues fldName = Some fldVal" and
      fld_val_typed: "value_has_type env fldVal (apply_subst (IS_TyArgs state) ty)" by auto

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
                sound_term_result state' env' ty' (interp_term fuel state' tm')"
    and typing: "core_term_type env NotGhost (CoreTm_VariantProj tm ctorName) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_VariantProj tm ctorName))"
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
  have tm_sound: "sound_term_result state env (CoreTy_Datatype dtName tyArgs) (interp_term fuel state tm)" .

  show ?thesis
  proof (cases "interp_term fuel state tm")
    case (Inl err)
    (* tm failed - propagate error *)
    then have "interp_term (Suc fuel) state (CoreTm_VariantProj tm ctorName) = Inl err"
      by simp
    with tm_sound Inl show ?thesis by auto
  next
    case (Inr val)
    (* tm succeeded. tyArgs may mention runtime tyvars; the value is typed
       against the substituted (ground) form. *)
    let ?s = "IS_TyArgs state"
    let ?subTyArgs = "map (apply_subst ?s) tyArgs"
    from tm_sound Inr
    have val_typed: "value_has_type env val (CoreTy_Datatype dtName ?subTyArgs)"
      by simp

    (* Value must be CV_Variant *)
    from value_has_type_Name[OF val_typed] obtain actualCtor payload where
      val_eq: "val = CV_Variant actualCtor payload" by auto

    (* Extract typing facts from value_has_type for the variant *)
    from val_typed val_eq obtain dtName3 tyvars3 payloadTy3 where
      val_ctor_lookup: "fmlookup (TE_DataCtors env) actualCtor = Some (dtName3, tyvars3, payloadTy3)" and
      val_dt_eq: "dtName = dtName3" and
      val_len_eq: "length tyvars3 = length ?subTyArgs" and
      payload_typed: "value_has_type env payload
          (apply_subst (fmap_of_list (zip tyvars3 ?subTyArgs)) payloadTy3)"
      by (auto split: option.splits prod.splits)

    show ?thesis
    proof (cases "actualCtor = ctorName")
      case True
      (* Constructor names match - projection succeeds *)
      (* Both look up the same constructor, so tyvars and payloadTy agree *)
      from val_ctor_lookup ctor_lookup True dt_eq val_dt_eq
      have tyvars_eq: "tyvars3 = tyvars" and payloadTy_eq: "payloadTy3 = payloadTy"
        by auto

      (* Move the apply_subst outside via apply_subst_compose_zip. Preconditions:
         (1) length tyvars = length tyArgs (from len_eq), (2) payloadTy's tyvars
         are a subset of tyvars (from tyenv_payloads_well_kinded), (3) tyvars
         distinct (from tyenv_ctor_tyvars_distinct). *)
      from wf_env have
        payloads_wk: "tyenv_payloads_well_kinded env" and
        ctor_distinct: "tyenv_ctor_tyvars_distinct env"
        unfolding tyenv_well_formed_def by auto
      from payloads_wk ctor_lookup
      have payload_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
        unfolding tyenv_payloads_well_kinded_def by blast
      have payload_tyvars_sub: "type_tyvars payloadTy \<subseteq> set tyvars"
        using is_well_kinded_type_tyvars_subset[OF payload_wk]
        by (simp add: fset_of_list.rep_eq)
      from ctor_distinct ctor_lookup have tyvars_distinct: "distinct tyvars"
        unfolding tyenv_ctor_tyvars_distinct_def by blast

      have compose_eq:
        "apply_subst (fmap_of_list (zip tyvars ?subTyArgs)) payloadTy
           = apply_subst ?s (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
        using apply_subst_compose_zip[OF len_eq[symmetric] payload_tyvars_sub tyvars_distinct] .

      have "value_has_type env payload (apply_subst ?s ty)"
        using payload_typed tyvars_eq payloadTy_eq ty_eq compose_eq by simp

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
                sound_term_result state' env' ty' (interp_term fuel state' tm')"
    and IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results state' env' (map the types') (interp_term_list fuel state' tms')"
    and typing: "core_term_type env NotGhost (CoreTm_ArrayProj arr idxTms) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_ArrayProj arr idxTms))"
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
  have arr_sound: "sound_term_result state env (CoreTy_Array elemTy dims) (interp_term fuel state arr)" .

  (* Prepare typing info for index terms to use IH_list *)
  let ?types = "map (core_term_type env NotGhost) idxTms"
  from idxs_typed have types_all_some: "list_all (\<lambda>ty. ty \<noteq> None) ?types"
    by (simp add: list_all_length)
  from IH_list[OF state_env wf_env] types_all_some
  have idx_sound: "sound_term_results state env (map the ?types) (interp_term_list fuel state idxTms)"
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
    (* elemTy may mention runtime tyvars; the array's elements are typed
       against the substituted (ground) form. *)
    let ?subElemTy = "apply_subst (IS_TyArgs state) elemTy"
    from arr_sound Inr
    have arr_val_typed: "value_has_type env arrVal (CoreTy_Array ?subElemTy dims)"
      by simp

    (* Value must be CV_Array *)
    from value_has_type_Array[OF arr_val_typed] obtain sizes valuesMap where
      arr_val_eq: "arrVal = CV_Array sizes valuesMap" and
      elems_typed: "\<forall>idx v. fmlookup valuesMap idx = Some v
                              \<longrightarrow> value_has_type env v ?subElemTy"
      by auto

    show ?thesis
    proof (cases "interp_term_list fuel state idxTms")
      case (Inl err)
      then have "interp_term (Suc fuel) state (CoreTm_ArrayProj arr idxTms) = Inl err"
        using Inr arr_val_eq by simp
      with idx_sound Inl show ?thesis by auto
    next
      case (Inr idxVals)
      (* The substituted u64 type is just u64 itself, so the replicate stays the same. *)
      have map_the_types_sub:
        "map (apply_subst (IS_TyArgs state) \<circ> (the \<circ> core_term_type env NotGhost)) idxTms
           = replicate (length idxTms) (CoreTy_FiniteInt Unsigned IntBits_64)"
        using map_the_types
        by (simp flip: map_map)
      from idx_sound Inr map_the_types_sub
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
        have result_typed: "value_has_type env result ?subElemTy"
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
                sound_term_results state' env' (map the types') (interp_term_list fuel state' tms')"
    and typing: "core_term_type env NotGhost (CoreTm_Record flds) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_Record flds))"
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
  have list_sound: "sound_term_results state env (map the types) (interp_term_list fuel state (map snd flds))"
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
    (* vals are typed against the substituted forms of each field type. *)
    let ?s = "IS_TyArgs state"
    let ?subTys = "map (apply_subst ?s) tys"
    from list_sound Inr the_types
    have vals_typed': "list_all2 (value_has_type env) vals ?subTys"
      by (simp flip: map_map)

    have interp_eq: "interp_term (Suc fuel) state (CoreTm_Record flds) =
          Inr (CV_Record (zip (map fst flds) vals))"
      using Inr by simp

    (* Show the result has the substituted record type *)
    have len_vals: "length vals = length flds"
      using vals_typed' len_eq by (auto dest: list_all2_lengthD)

    have "list_all2 (\<lambda>(name1, fldVal) (name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
            (zip (map fst flds) vals) (zip (map fst flds) ?subTys)"
    proof (rule list_all2_all_nthI)
      show "length (zip (map fst flds) vals) = length (zip (map fst flds) ?subTys)"
        using len_vals len_eq by simp
    next
      fix i assume i_bound: "i < length (zip (map fst flds) vals)"
      hence i_flds: "i < length flds" using len_vals by simp
      from vals_typed' i_flds len_eq have "value_has_type env (vals ! i) (?subTys ! i)"
        by (auto simp: list_all2_conv_all_nth)
      thus "(case zip (map fst flds) vals ! i of
              (name1, fldVal) \<Rightarrow> \<lambda>(name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
             (zip (map fst flds) ?subTys ! i)"
        using i_flds len_vals len_eq by simp
    qed
    hence "value_has_type env (CV_Record (zip (map fst flds) vals))
                              (CoreTy_Record (zip (map fst flds) ?subTys))"
      using distinct_names len_eq by simp

    moreover have "apply_subst ?s ty = CoreTy_Record (zip (map fst flds) ?subTys)"
      using ty_eq len_eq by (simp add: zip_map2)
    ultimately show ?thesis using interp_eq by simp
  qed
qed

(* Type soundness for CoreTm_VariantCtor *)
lemma type_soundness_variant_ctor:
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_VariantCtor ctorName tyArgs payload) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payload))"
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
  have payload_sound: "sound_term_result state env payloadActualTy (interp_term fuel state payload)" .

  (* Case split on payload evaluation *)
  show ?thesis
  proof (cases "interp_term fuel state payload")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payload) = Inl err"
      by simp
    with payload_sound Inl show ?thesis by auto
  next
    case (Inr payloadVal)
    let ?s = "IS_TyArgs state"
    let ?subTyArgs = "map (apply_subst ?s) tyArgs"
    from payload_sound Inr
    have payload_typed: "value_has_type env payloadVal (apply_subst ?s payloadActualTy)"
      by simp

    have interp_eq: "interp_term (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payload) =
          Inr (CV_Variant ctorName payloadVal)"
      using Inr by simp

    (* Substituted tyArgs are well-kinded, runtime, and have the right length. *)
    have len_eq_sub: "length ?subTyArgs = length tyvars" using len_eq by simp
    have subTyArgs_wk: "list_all (is_well_kinded env) ?subTyArgs"
      using tyargs_wk
      by (induction tyArgs) (auto simp: is_well_kinded_apply_IS_TyArgs[OF state_env wf_env])
    have subTyArgs_rt: "list_all (is_runtime_type env) ?subTyArgs"
      using tyargs_rt
      by (induction tyArgs) (auto simp: is_runtime_type_apply_IS_TyArgs[OF state_env])
    have subTyArgs_ground: "list_all (\<lambda>a. type_tyvars a = {}) ?subTyArgs"
      using tyargs_rt
      by (induction tyArgs) (auto simp: is_runtime_type_apply_IS_TyArgs_ground[OF state_env])

    (* Lift payload typing into a (zip tyvars ?subTyArgs)-substitution form. *)
    from ctor_lookup wf_env have
      payloads_wk: "tyenv_payloads_well_kinded env" and
      ctor_distinct: "tyenv_ctor_tyvars_distinct env"
      unfolding tyenv_well_formed_def by auto
    from payloads_wk ctor_lookup
    have payload_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
      unfolding tyenv_payloads_well_kinded_def by blast
    have payload_tyvars_sub: "type_tyvars payloadTy \<subseteq> set tyvars"
      using is_well_kinded_type_tyvars_subset[OF payload_wk]
      by (simp add: fset_of_list.rep_eq)
    from ctor_distinct ctor_lookup have tyvars_distinct: "distinct tyvars"
      unfolding tyenv_ctor_tyvars_distinct_def by blast

    have compose_eq:
      "apply_subst (fmap_of_list (zip tyvars ?subTyArgs)) payloadTy
         = apply_subst ?s (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      using apply_subst_compose_zip[OF len_eq[symmetric] payload_tyvars_sub tyvars_distinct] .

    have payload_typed':
      "value_has_type env payloadVal
         (apply_subst (fmap_of_list (zip tyvars ?subTyArgs)) payloadTy)"
      using payload_typed payload_ty_eq compose_eq tySubst_def by simp

    (* Result has the substituted variant type. *)
    have "value_has_type env (CV_Variant ctorName payloadVal) (CoreTy_Datatype dtName ?subTyArgs)"
      using ctor_lookup len_eq_sub subTyArgs_wk subTyArgs_rt subTyArgs_ground
            dt_nonghost payload_typed'
      by (simp add: list_all_iff)

    moreover have "apply_subst ?s ty = CoreTy_Datatype dtName ?subTyArgs"
      using ty_eq by simp
    ultimately show ?thesis using interp_eq by simp
  qed
qed

(* Type soundness for CoreTm_Match *)
lemma type_soundness_match:
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Match scrut arms) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_Match scrut arms))"
proof -
  (* Extract facts from typing *)
  define scrutTyOpt where "scrutTyOpt = core_term_type env NotGhost scrut"

  from typing have typing': "(case scrutTyOpt of
      None \<Rightarrow> None
    | Some scrutTy \<Rightarrow>
        let pats = map fst arms; bodies = map snd arms
        in if arms = [] then None
           else if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
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
         else (case core_term_type env NotGhost (snd (hd arms)) of
                 None \<Rightarrow> None
               | Some resultTy \<Rightarrow>
                   if list_all (\<lambda>body. core_term_type env NotGhost body = Some resultTy)
                               (tl (map snd arms))
                   then Some resultTy else None)) = Some ty"
    by simp

  from typing'' have arms_nonempty: "arms \<noteq> []"
    by (cases arms) (simp_all add: Let_def)

  define hd_ty_opt where "hd_ty_opt = core_term_type env NotGhost (snd (hd arms))"

  from typing'' arms_nonempty
  have typing''': "(case hd_ty_opt of
      None \<Rightarrow> None
    | Some resultTy \<Rightarrow>
        if list_all (\<lambda>body. core_term_type env NotGhost body = Some resultTy)
                    (tl (map snd arms))
        then Some resultTy else None) = Some ty"
    unfolding hd_ty_opt_def Let_def by (simp split: if_splits)

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
  have scrut_sound: "sound_term_result state env scrutTy (interp_term fuel state scrut)" .

  (* Case split on scrutinee evaluation *)
  show ?thesis
  proof (cases "interp_term fuel state scrut")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_Match scrut arms) = Inl err" by simp
    with scrut_sound Inl show ?thesis by auto
  next
    case (Inr scrutVal)
    note scrut_eval = Inr

    (* find_matching_arm may fail (RuntimeError) or succeed. Both are sound. *)
    show ?thesis
    proof (cases "find_matching_arm scrutVal arms")
      case (Inl match_err)
      (* find_matching_arm only ever returns Inl RuntimeError (no match found) *)
      from find_matching_arm_error[OF Inl] have "match_err = RuntimeError" .
      then have "interp_term (Suc fuel) state (CoreTm_Match scrut arms) = Inl RuntimeError"
        using scrut_eval Inl by simp
      then show ?thesis by simp
    next
      case (Inr armBody)
      then have match_eq: "find_matching_arm scrutVal arms = Inr armBody" .

      (* armBody is the body of some arm in the list *)
      from find_matching_arm_in_set[OF match_eq]
      obtain pat where arm_in: "(pat, armBody) \<in> set arms" by auto

      (* armBody typechecks to resultTy *)
      have arm_typed: "core_term_type env NotGhost armBody = Some resultTy"
        using all_arms_typed arm_in by force

      (* IH on arm body *)
      from IH[OF arm_typed]
      have arm_sound: "sound_term_result state env resultTy (interp_term fuel state armBody)" .

      (* Compute the result *)
      have "interp_term (Suc fuel) state (CoreTm_Match scrut arms) =
            interp_term fuel state armBody"
        using scrut_eval match_eq by simp
      with arm_sound ty_eq show ?thesis by simp
    qed
  qed
qed

(* Type soundness for CoreTm_Sizeof *)
lemma type_soundness_sizeof:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term fuel state tm')"
    and typing: "core_term_type env NotGhost (CoreTm_Sizeof tm) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_Sizeof tm))"
proof -
  from typing obtain elemTy dims where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Array elemTy dims)" and
    ty_eq: "ty = sizeof_type dims"
    by (auto split: option.splits CoreType.splits if_splits)

  from IH[OF tm_typing]
  have tm_sound: "sound_term_result state env (CoreTy_Array elemTy dims) (interp_term fuel state tm)" .

  show ?thesis
  proof (cases "interp_term fuel state tm")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_Sizeof tm) = Inl err" by simp
    with tm_sound Inl show ?thesis by auto
  next
    case (Inr val)
    from tm_sound Inr
    have val_typed: "value_has_type env val
        (CoreTy_Array (apply_subst (IS_TyArgs state) elemTy) dims)"
      by simp
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
                sound_term_results state' env' (map the types') (interp_term_list fuel state' tms')"
    and typing: "core_term_type env NotGhost (CoreTm_LitArray elemTy tms) = Some ty"
  shows "sound_term_result state env ty (interp_term (Suc fuel) state (CoreTm_LitArray elemTy tms))"
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
  have list_sound: "sound_term_results state env (replicate (length tms) elemTy)
                      (interp_term_list fuel state tms)"
    using the_types by simp

  let ?s = "IS_TyArgs state"
  let ?subElemTy = "apply_subst ?s elemTy"

  (* Case split on list evaluation *)
  show ?thesis
  proof (cases "interp_term_list fuel state tms")
    case (Inl err)
    then have "interp_term (Suc fuel) state (CoreTm_LitArray elemTy tms) = Inl err" by simp
    with list_sound Inl show ?thesis by auto
  next
    case (Inr vals)
    from list_sound Inr
    have vals_typed: "list_all2 (value_has_type env) vals (replicate (length tms) ?subElemTy)"
      by simp
    hence len_vals: "length vals = length tms" by (auto dest: list_all2_lengthD)
    hence vals_elem_typed: "\<And>i. i < length vals \<Longrightarrow> value_has_type env (vals ! i) ?subElemTy"
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

    (* All values in fmap have type ?subElemTy *)
    have fm_vals_typed: "\<forall>idx val. fmlookup fm idx = Some val \<longrightarrow> value_has_type env val ?subElemTy"
    proof (intro allI impI)
      fix idx val assume lkup: "fmlookup fm idx = Some val"
      hence "map_of (zip (map (\<lambda>i. [int i]) [0..<length vals]) vals) idx = Some val"
        unfolding fm_def by (simp add: fmlookup_of_list)
      hence "(idx, val) \<in> set (zip (map (\<lambda>i. [int i]) [0..<length vals]) vals)"
        by (rule map_of_SomeD)
      hence "val \<in> set vals" by (auto simp: set_zip)
      then obtain i where "i < length vals" and "val = vals ! i"
        by (auto simp: in_set_conv_nth)
      thus "value_has_type env val ?subElemTy"
        using vals_elem_typed by simp
    qed

    from wk state_env wf_env have wk_sub: "is_well_kinded env ?subElemTy"
      using is_well_kinded_apply_IS_TyArgs by blast
    from rt state_env have rt_sub: "is_runtime_type env ?subElemTy"
      using is_runtime_type_apply_IS_TyArgs by blast
    from rt state_env have ground_sub: "type_tyvars ?subElemTy = {}"
      using is_runtime_type_apply_IS_TyArgs_ground by blast
    have "value_has_type env (CV_Array [n] fm)
            (CoreTy_Array ?subElemTy [CoreDim_Fixed (int (length tms))])"
      using wk_sub rt_sub ground_sub fm_vals_typed adwk fms smd by simp

    with interp_eq make_eq ty_eq show ?thesis
      using sound_term_result.simps(2) by auto
  qed
qed


(*-----------------------------------------------------------------------------*)
(* Type soundness for function calls *)
(*-----------------------------------------------------------------------------*)

lemma type_soundness_function_call:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo"
    and not_ghost: "FI_Ghost funInfo = NotGhost"
    and args_typed: "list_all2 (\<lambda>tm expectedTy.
         case core_term_type env NotGhost tm of
           None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
       argTms (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                   (FI_TmArgs funInfo))"
    and retTy_eq: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    and ty_len: "length tyArgs = length (FI_TyArgs funInfo)"
    and ty_wk: "list_all (is_well_kinded env) tyArgs"
    and ty_rt: "list_all (is_runtime_type env) tyArgs"
    and ref_writable: "\<forall>i < length argTms.
         (snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
          is_writable_lvalue env (argTms ! i))"
    and IH_term: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                  sound_term_result state' env' ty' (interp_term fuel state' tm')"
    and IH_lvalue: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                is_writable_lvalue env' tm' \<and> core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                  sound_lvalue_result state' env' storeTyping' ty' (interp_writable_lvalue fuel state' tm')"
    and IH_stmts: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmts0 env0'.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                core_statement_list_type env0 NotGhost stmts0 = Some env0' \<Longrightarrow>
                  sound_statement_result env0 env0' storeTyping0 (interp_statement_list fuel state0 stmts0)"
  shows "sound_function_call_result state env storeTyping retTy
           (interp_function_call (Suc fuel) state fnName tyArgs argTms)"
proof -
  \<comment> \<open>Obtain the InterpFun f for fnName via funs_exist_in_state. \<close>
  from state_env have fes: "funs_exist_in_state state env"
    unfolding state_matches_env_def by blast
  from fes fn_lookup not_ghost
  have "case fmlookup (IS_Functions state) fnName of
          Some interpFun \<Rightarrow> fun_info_matches_interp_fun env funInfo interpFun
        | None \<Rightarrow> False"
    unfolding funs_exist_in_state_def by blast
  then obtain f where
    f_lookup: "fmlookup (IS_Functions state) fnName = Some f"
    and fi_match: "fun_info_matches_interp_fun env funInfo f"
    by (cases "fmlookup (IS_Functions state) fnName") auto

  \<comment> \<open>Length match between argTms and f's args (via fi_match + args_typed). \<close>
  from fi_match have len_fi: "length (FI_TmArgs funInfo) = length (IF_Args f)"
    unfolding fun_info_matches_interp_fun_def by (auto dest: list_all2_lengthD)
  from args_typed have len_argTms_fi: "length argTms = length (FI_TmArgs funInfo)"
    by (simp add: list_all2_lengthD)
  hence len_argTms: "length argTms = length (IF_Args f)"
    using len_fi by simp

  \<comment> \<open>Length match between tyArgs and f's type args (via fi_match + ty_len). \<close>
  from fi_match have tyargs_eq: "FI_TyArgs funInfo = IF_TyArgs f"
    unfolding fun_info_matches_interp_fun_def by simp
  from ty_len tyargs_eq have len_tyArgs: "length tyArgs = length (IF_TyArgs f)"
    by simp

  \<comment> \<open>The call-site substitution: ground because IS_TyArgs state is ground (by
      ty_args_well_formed via state_env) and tyArgs are runtime in env. \<close>
  define tySubst :: "(nat, CoreType) fmap" where
    tySubst_def: "tySubst = fmap_of_list
                (zip (FI_TyArgs funInfo)
                     (map (apply_subst (IS_TyArgs state)) tyArgs))"

  \<comment> \<open>Basic structural facts about tySubst: distinctness, well-formedness, ground range. \<close>
  from wf_env fn_lookup have ty_dist: "distinct (FI_TyArgs funInfo)"
    unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
  from state_env have ta_caller: "ty_args_well_formed state env"
    unfolding state_matches_env_def by blast
  from ta_caller have caller_dom: "fmdom (IS_TyArgs state) = TE_RuntimeTypeVars env"
    and caller_range_ground: "subst_range_tyvars (IS_TyArgs state) = {}"
    and caller_range_wk_rt: "\<forall>ty \<in> fmran' (IS_TyArgs state).
                                is_well_kinded env ty \<and> is_runtime_type env ty"
    unfolding ty_args_well_formed_def by auto

  have fmdom_tySubst: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
    using tySubst_def ty_len
    by (simp add: fset_of_list.rep_eq)

  \<comment> \<open>tySubst's range is ground (composition of caller's ground IS_TyArgs over
      tyArgs whose tyvars are bounded by env's runtime tyvars). \<close>
  have tySubst_range_ground: "subst_range_tyvars tySubst = {}"
  proof -
    have "\<forall>t \<in> fmran' tySubst. type_tyvars t = {}"
    proof
      fix t assume mem: "t \<in> fmran' tySubst"
      then obtain n where lk: "fmlookup tySubst n = Some t"
        by (auto simp: fmran'_alt_def fmlookup_dom_iff)
      from lk tySubst_def
      have "map_of (zip (FI_TyArgs funInfo)
                (map (apply_subst (IS_TyArgs state)) tyArgs)) n = Some t"
        by (simp add: fmap_of_list.rep_eq)
      hence "(n, t) \<in> set (zip (FI_TyArgs funInfo)
                            (map (apply_subst (IS_TyArgs state)) tyArgs))"
        by (rule map_of_SomeD)
      then obtain j where j_lt: "j < length tyArgs"
        and t_eq: "t = apply_subst (IS_TyArgs state) (tyArgs ! j)"
        using ty_len by (auto simp: set_zip)
      from ty_rt j_lt have "is_runtime_type env (tyArgs ! j)"
        by (simp add: list_all_length)
      from is_runtime_type_tyvars_subset[OF this]
      have tyArg_tyvars: "type_tyvars (tyArgs ! j) \<subseteq> fset (TE_RuntimeTypeVars env)"
        by simp
      hence tyArg_in_dom: "type_tyvars (tyArgs ! j) \<subseteq> fset (fmdom (IS_TyArgs state))"
        using caller_dom by simp
      have "type_tyvars (apply_subst (IS_TyArgs state) (tyArgs ! j))
              \<subseteq> (type_tyvars (tyArgs ! j) - fset (fmdom (IS_TyArgs state)))
                \<union> subst_range_tyvars (IS_TyArgs state)"
        by (rule apply_subst_tyvars_result)
      also have "\<dots> = {}" using tyArg_in_dom caller_range_ground by auto
      finally show "type_tyvars t = {}" using t_eq by simp
    qed
    thus ?thesis unfolding subst_range_tyvars_def by auto
  qed

  \<comment> \<open>For each parameter, apply_subst tySubst paramTy_i is ground. \<close>
  have paramTy_apply_ground:
    "\<And>i. i < length (FI_TmArgs funInfo) \<Longrightarrow>
            type_tyvars (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i)))) = {}"
  proof -
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    let ?paramTy_i = "fst (snd (FI_TmArgs funInfo ! i))"
    have "?paramTy_i \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
      using i_bound by force
    from wf_env fn_lookup not_ghost have
      "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                        ?paramTy_i"
      unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def
      using \<open>?paramTy_i \<in> _\<close> by blast
    hence paramTy_tyvars:
      "type_tyvars ?paramTy_i \<subseteq> fset (fset_of_list (FI_TyArgs funInfo))"
      using is_runtime_type_tyvars_subset by fastforce
    hence paramTy_in_dom: "type_tyvars ?paramTy_i \<subseteq> fset (fmdom tySubst)"
      using fmdom_tySubst by simp
    have "type_tyvars (apply_subst tySubst ?paramTy_i)
            \<subseteq> (type_tyvars ?paramTy_i - fset (fmdom tySubst))
              \<union> subst_range_tyvars tySubst"
      by (rule apply_subst_tyvars_result)
    also have "\<dots> = {}" using paramTy_in_dom tySubst_range_ground by auto
    finally show "type_tyvars (apply_subst tySubst ?paramTy_i) = {}" by simp
  qed

  \<comment> \<open>Abbreviations matching the interpreter's let-bound names. \<close>
  let ?refResults = "map (interp_writable_lvalue fuel state) argTms"
  let ?valResults = "map (interp_term fuel state) argTms"
  let ?argTuples = "zip (IF_Args f) (zip ?refResults ?valResults)"
  let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                IS_ConstLocals := {||},
                                IS_TyArgs := tySubst \<rparr>"

  \<comment> \<open>The interpreter reduces to a fold + body dispatch. \<close>
  have interp_eq:
    "interp_function_call (Suc fuel) state fnName tyArgs argTms
     = (case fold process_one_arg ?argTuples (Inr ?clearedState) of
          Inl err \<Rightarrow> Inl err
        | Inr preCallState \<Rightarrow>
            (case IF_Body f of
               Inl bodyStmts \<Rightarrow>
                 (case interp_statement_list fuel preCallState bodyStmts of
                    Inr (Return postCallState retVal) \<Rightarrow>
                      Inr (restore_scope state postCallState, retVal)
                  | Inr (Continue _) \<Rightarrow> Inl RuntimeError
                  | Inl err \<Rightarrow> Inl err)
             | Inr externFun \<Rightarrow>
                 (let vals = rights ?valResults;
                      refs = rights (map (\<lambda>((_, vr), refResult).
                                            if vr = Ref then refResult else Inl TypeError)
                                        (zip (IF_Args f) ?refResults));
                      (newWorld, refUpdates, retVal) = externFun (IS_World state) vals;
                      state' = state \<lparr> IS_World := newWorld \<rparr>
                  in case apply_ref_updates state' refs refUpdates of
                       Inr finalState \<Rightarrow> Inr (finalState, retVal)
                     | Inl err \<Rightarrow> Inl err)))"
    using f_lookup len_argTms len_tyArgs tySubst_def tyargs_eq
    by (simp add: Let_def)

  \<comment> \<open>Build the per-argument soundness facts from the IH. The IH gives us
      sound_term_result / sound_lvalue_result at the type produced by
      core_term_type — i.e. apply_subst (fmap_of_list (zip (FI_TyArgs funInfo)
      tyArgs)) paramTy. This is the *outer* substitution (no IS_TyArgs pass);
      the helper fold_process_one_arg_sound takes its preconditions in
      exactly this shape and bridges to its internal tySubst via
      apply_subst_compose_zip. \<close>
  have vals_sound:
    "\<forall>i < length (FI_TmArgs funInfo).
       sound_term_result state env
         (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                      (fst (snd (FI_TmArgs funInfo ! i))))
         (?valResults ! i)"
  proof (intro allI impI)
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    with len_argTms_fi have i_argTms: "i < length argTms" by simp
    let ?paramTy_i = "fst (snd (FI_TmArgs funInfo ! i))"
    let ?expTy_i = "apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i"
    from args_typed have all_i:
      "\<forall>j < length argTms.
         case core_term_type env NotGhost (argTms ! j) of
           None \<Rightarrow> False
         | Some actualTy \<Rightarrow> actualTy
             = (map (\<lambda>(_, ty, _).
                       apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                   (FI_TmArgs funInfo)) ! j"
      by (simp add: list_all2_conv_all_nth)
    from all_i i_argTms have raw_ty_i:
      "case core_term_type env NotGhost (argTms ! i) of
         None \<Rightarrow> False
       | Some actualTy \<Rightarrow> actualTy
            = (map (\<lambda>(_, ty, _).
                     apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                  (FI_TmArgs funInfo)) ! i"
      by blast
    have map_i_eq:
      "(map (\<lambda>(_, ty, _).
               apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
            (FI_TmArgs funInfo)) ! i = ?expTy_i"
      using i_bound by (simp add: case_prod_beta)
    from raw_ty_i obtain actualTy where
      cty_i: "core_term_type env NotGhost (argTms ! i) = Some actualTy"
      and act_eq_raw: "actualTy = (map (\<lambda>(_, ty, _).
                     apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                  (FI_TmArgs funInfo)) ! i"
      by (cases "core_term_type env NotGhost (argTms ! i)") simp_all
    from act_eq_raw map_i_eq have act_eq: "actualTy = ?expTy_i" by simp
    from IH_term[OF state_env wf_env, of "argTms ! i" actualTy] cty_i
    have "sound_term_result state env actualTy (interp_term fuel state (argTms ! i))"
      by simp
    with act_eq i_argTms show
      "sound_term_result state env ?expTy_i (?valResults ! i)"
      by simp
  qed

  have lvals_sound:
    "\<forall>i < length (FI_TmArgs funInfo).
       snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
         sound_lvalue_result state env storeTyping
           (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                        (fst (snd (FI_TmArgs funInfo ! i))))
           (?refResults ! i)"
  proof (intro allI impI)
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
                and is_ref: "snd (snd (FI_TmArgs funInfo ! i)) = Ref"
    with len_argTms_fi have i_argTms: "i < length argTms" by simp
    let ?paramTy_i = "fst (snd (FI_TmArgs funInfo ! i))"
    let ?expTy_i = "apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i"
    from args_typed have all_i:
      "\<forall>j < length argTms.
         case core_term_type env NotGhost (argTms ! j) of
           None \<Rightarrow> False
         | Some actualTy \<Rightarrow> actualTy
             = (map (\<lambda>(_, ty, _).
                       apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                   (FI_TmArgs funInfo)) ! j"
      by (simp add: list_all2_conv_all_nth)
    from all_i i_argTms have raw_ty_i:
      "case core_term_type env NotGhost (argTms ! i) of
         None \<Rightarrow> False
       | Some actualTy \<Rightarrow> actualTy
            = (map (\<lambda>(_, ty, _).
                     apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                  (FI_TmArgs funInfo)) ! i"
      by blast
    have map_i_eq:
      "(map (\<lambda>(_, ty, _).
               apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
            (FI_TmArgs funInfo)) ! i = ?expTy_i"
      using i_bound by (simp add: case_prod_beta)
    from raw_ty_i obtain actualTy where
      cty_i: "core_term_type env NotGhost (argTms ! i) = Some actualTy"
      and act_eq_raw: "actualTy = (map (\<lambda>(_, ty, _).
                     apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                  (FI_TmArgs funInfo)) ! i"
      by (cases "core_term_type env NotGhost (argTms ! i)") simp_all
    from act_eq_raw map_i_eq have act_eq: "actualTy = ?expTy_i" by simp
    from ref_writable i_argTms is_ref have wlv_i:
      "is_writable_lvalue env (argTms ! i)" by simp
    from IH_lvalue[OF state_env wf_env, of "argTms ! i" actualTy] cty_i wlv_i
    have "sound_lvalue_result state env storeTyping actualTy
            (interp_writable_lvalue fuel state (argTms ! i))"
      by simp
    with act_eq i_argTms show
      "sound_lvalue_result state env storeTyping ?expTy_i (?refResults ! i)"
      by simp
  qed

  \<comment> \<open>Apply the helper to get sound arg processing result. \<close>
  note arg_sound = fold_process_one_arg_sound
                     [OF state_env wf_env fn_lookup not_ghost fi_match
                         ty_len ty_wk ty_rt vals_sound lvals_sound len_argTms_fi]
  \<comment> \<open>arg_sound :: sound_arg_processing_result env funInfo tySubst storeTyping
                   (fold process_one_arg ?argTuples (Inr ?clearedState))
      where the lemma's tySubst matches our local tySubst by tySubst_def. \<close>

  show ?thesis
  proof (cases "fold process_one_arg ?argTuples (Inr ?clearedState)")
    case (Inl err)
    \<comment> \<open>Arg processing errored. By arg_sound, err is a sound error. \<close>
    from arg_sound Inl tySubst_def have err_sound: "sound_error_result err"
      unfolding sound_arg_processing_result_def by simp
    from interp_eq Inl have
      "interp_function_call (Suc fuel) state fnName tyArgs argTms = Inl err"
      by simp
    thus ?thesis using err_sound by simp
  next
    case fold_Inr: (Inr preCallState)
    \<comment> \<open>Arg processing succeeded. Extract the body env match + storeTyping. \<close>
    from arg_sound fold_Inr tySubst_def
    have tyargs_pre: "IS_TyArgs preCallState = tySubst"
      and pre_match: "\<exists>bodyStoreTyping.
                        state_matches_env preCallState (body_env_for env funInfo) bodyStoreTyping
                      \<and> storeTyping_extends storeTyping bodyStoreTyping"
      unfolding sound_arg_processing_result_def by auto
    from pre_match obtain bodyStoreTyping where
      sme_body: "state_matches_env preCallState (body_env_for env funInfo) bodyStoreTyping"
      and ext_body: "storeTyping_extends storeTyping bodyStoreTyping"
      by blast

    \<comment> \<open>Common facts derived from sme_body. \<close>
    have wf_bodyEnv: "tyenv_well_formed (body_env_for env funInfo)"
      using body_env_for_well_formed[OF wf_env fn_lookup not_ghost] .

    show ?thesis
    proof (cases "IF_Body f")
      case body_babylon: (Inl bodyStmts)
      \<comment> \<open>Babylon body. The fi_match assumption certifies that bodyStmts
          typechecks in body_env_for env funInfo. \<close>
      from fi_match body_babylon obtain bodyEnv' where
        body_ty: "core_statement_list_type (body_env_for env funInfo) NotGhost bodyStmts
                    = Some bodyEnv'"
        unfolding fun_info_matches_interp_fun_def by auto

      \<comment> \<open>Apply IH(5) to get sound_statement_result on the body. \<close>
      from IH_stmts[OF sme_body wf_bodyEnv, of bodyStmts bodyEnv'] body_ty
      have body_sound: "sound_statement_result (body_env_for env funInfo) bodyEnv'
                          bodyStoreTyping
                          (interp_statement_list fuel preCallState bodyStmts)"
        by simp

      show ?thesis
      proof (cases "interp_statement_list fuel preCallState bodyStmts")
        case body_Inl: (Inl err)
        \<comment> \<open>Body errored. Sound by body_sound. \<close>
        from body_sound body_Inl have err_sound: "sound_error_result err" by simp
        from interp_eq fold_Inr body_babylon body_Inl
        have "interp_function_call (Suc fuel) state fnName tyArgs argTms = Inl err"
          by simp
        thus ?thesis using err_sound by simp
      next
        case body_Inr: (Inr execRes)
        show ?thesis
        proof (cases execRes)
          case (Continue contState)
          \<comment> \<open>Body reached end without Return — interpreter returns RuntimeError. \<close>
          from interp_eq fold_Inr body_babylon body_Inr Continue
          have "interp_function_call (Suc fuel) state fnName tyArgs argTms = Inl RuntimeError"
            by simp
          thus ?thesis by simp
        next
          case (Return postCallState retVal)
          \<comment> \<open>Main case. Extract env_mid + postStoreTyping + return value typing. \<close>
          from body_sound body_Inr Return
          have ret_typed_bodyEnv:
            "value_has_type (body_env_for env funInfo) retVal
               (apply_subst (IS_TyArgs postCallState)
                            (TE_ReturnType (body_env_for env funInfo)))"
            by simp
          from body_sound body_Inr Return obtain env_mid postStoreTyping where
            fxeq1: "tyenv_fixed_eq (body_env_for env funInfo) env_mid"
            and fxeq2: "tyenv_fixed_eq env_mid bodyEnv'"
            and wf_mid: "tyenv_well_formed env_mid"
            and sme_post: "state_matches_env postCallState env_mid postStoreTyping"
            and ext_post: "storeTyping_extends bodyStoreTyping postStoreTyping"
            by auto

          \<comment> \<open>Concrete form of the interpreter result. \<close>            from interp_eq fold_Inr body_babylon body_Inr Return
          have interp_result:
            "interp_function_call (Suc fuel) state fnName tyArgs argTms
               = Inr (restore_scope state postCallState, retVal)"
            by simp

          \<comment> \<open>preCallState's IS_Globals / IS_Functions = state's (cleared state preserves
              them; the fold preserves them too). \<close>
          from fold_Inr have fold_eq:
            "fold process_one_arg ?argTuples (Inr ?clearedState) = Inr preCallState" .
          from fold_process_one_arg_preserves_globals_funs[OF fold_eq]
          have pre_globals: "IS_Globals preCallState = IS_Globals state"
            and pre_functions: "IS_Functions preCallState = IS_Functions state"
            by auto

          \<comment> \<open>postCallState inherits IS_Globals / IS_Functions from preCallState
              (statement-list execution preserves them). \<close>
          from body_Inr Return have body_list_eq:
            "interp_statement_list fuel preCallState bodyStmts
               = Inr (Return postCallState retVal)"
            by simp
          have post_globals: "IS_Globals postCallState = IS_Globals state"
            using interp_statement_list_return_preserves_globals[OF body_list_eq] pre_globals
            by simp
          have post_functions: "IS_Functions postCallState = IS_Functions state"
            using interp_statement_list_return_preserves_functions[OF body_list_eq] pre_functions
            by simp

          \<comment> \<open>tyenv_fixed_eq carries the dt-relevant field equalities. We also
              need to bridge through body_env_for, whose dt fields = env's. \<close>
          from fxeq1 have dt_eq_body_mid:
            "TE_DataCtors (body_env_for env funInfo) = TE_DataCtors env_mid"
            "TE_Datatypes (body_env_for env funInfo) = TE_Datatypes env_mid"
            "TE_GhostDatatypes (body_env_for env funInfo) = TE_GhostDatatypes env_mid"
            unfolding tyenv_fixed_eq_def by simp_all
          have dt_eq_env_body:
            "TE_DataCtors env = TE_DataCtors (body_env_for env funInfo)"
            "TE_Datatypes env = TE_Datatypes (body_env_for env funInfo)"
            "TE_GhostDatatypes env = TE_GhostDatatypes (body_env_for env funInfo)"
            by (simp_all add: body_env_for_def)
          have dt_eq:
            "TE_DataCtors env = TE_DataCtors env_mid"
            "TE_Datatypes env = TE_Datatypes env_mid"
            "TE_GhostDatatypes env = TE_GhostDatatypes env_mid"
            using dt_eq_env_body dt_eq_body_mid by simp_all

          \<comment> \<open>Chain storeTyping_extends: storeTyping \<le> bodyStoreTyping \<le> postStoreTyping. \<close>
          have ext_chain: "storeTyping_extends storeTyping postStoreTyping"
            using storeTyping_extends_trans[OF ext_body ext_post] .

          \<comment> \<open>Apply restore_scope_sound to get state_matches for the restored state. \<close>
          have sme_rs: "state_matches_env (restore_scope state postCallState) env storeTyping"
            using restore_scope_sound[OF state_env sme_post ext_chain
                                          post_globals post_functions
                                          dt_eq(1) dt_eq(2) dt_eq(3)
                                          wf_env wf_mid] .

          \<comment> \<open>storeTyping_extends storeTyping storeTyping: reflexive. \<close>
          have ext_id: "storeTyping_extends storeTyping storeTyping"
            by (rule storeTyping_extends_refl)

          \<comment> \<open>(2) IS_TyArgs preserved across restore_scope. \<close>
          have tyargs_rs: "IS_TyArgs (restore_scope state postCallState) = IS_TyArgs state"
            by (simp add: restore_scope_preserves_globals_funs)

          \<comment> \<open>(3) value_has_type env retVal (apply_subst (IS_TyArgs state) retTy).
              Bridge through body_env_for and apply_subst_compose_zip. \<close>

          \<comment> \<open>IS_TyArgs postCallState = tySubst (preserved through stmt list, then from
              arg-processing). \<close>
          have tyargs_post: "IS_TyArgs postCallState = tySubst"
            using interp_statement_list_preserves_IS_TyArgs_Return[OF body_list_eq] tyargs_pre
            by simp

          \<comment> \<open>Return type of bodyEnv is the function's return type, unsubstituted. \<close>
          have ret_ty_eq: "TE_ReturnType (body_env_for env funInfo) = FI_ReturnType funInfo"
            by (simp add: body_env_for_def)

          \<comment> \<open>Combine: value_has_type (body_env_for env funInfo) retVal
                (apply_subst tySubst (FI_ReturnType funInfo)). \<close>
          from ret_typed_bodyEnv tyargs_post ret_ty_eq
          have ret_typed_body:
            "value_has_type (body_env_for env funInfo) retVal
               (apply_subst tySubst (FI_ReturnType funInfo))"
            by simp

          \<comment> \<open>Transport to env via value_has_type_cong_env_wk. ret type is ground
              (by value_has_type_ground from ret_typed_body), so well-kindedness /
              runtime are env-independent on the type. \<close>
          have ret_ground:
            "type_tyvars (apply_subst tySubst (FI_ReturnType funInfo)) = {}"
            using value_has_type_ground[OF ret_typed_body] .
          have wf_bodyEnv: "tyenv_well_formed (body_env_for env funInfo)"
            using body_env_for_well_formed[OF wf_env fn_lookup not_ghost] .
          from value_has_type_well_kinded[OF ret_typed_body wf_bodyEnv]
          have wk_body: "is_well_kinded (body_env_for env funInfo)
                            (apply_subst tySubst (FI_ReturnType funInfo))" .
          from value_has_type_runtime[OF ret_typed_body]
          have rt_body: "is_runtime_type (body_env_for env funInfo)
                            (apply_subst tySubst (FI_ReturnType funInfo))" .
          \<comment> \<open>Bridge wk/rt to env via ground-cong lemmas. \<close>
          have wk_env: "is_well_kinded env (apply_subst tySubst (FI_ReturnType funInfo))"
            using wk_body
                  is_well_kinded_ground_cong_env[OF ret_ground, of "body_env_for env funInfo" env]
            by (simp add: body_env_for_def)
          have rt_env: "is_runtime_type env (apply_subst tySubst (FI_ReturnType funInfo))"
            using rt_body
                  is_runtime_type_ground_cong_env[OF ret_ground, of "body_env_for env funInfo" env]
            by (simp add: body_env_for_def)
          \<comment> \<open>Apply value_has_type_cong_env_wk to flip env. \<close>
          have ret_typed_env:
            "value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo))"
            using value_has_type_cong_env_wk
                    [OF dt_eq_env_body(1) dt_eq_env_body(2) dt_eq_env_body(3)
                        wf_bodyEnv wf_env wk_body wk_env rt_body rt_env ret_typed_body] .

          \<comment> \<open>Reconcile apply_subst tySubst (FI_ReturnType funInfo) with
              apply_subst (IS_TyArgs state) retTy via apply_subst_compose_zip. \<close>
          from wf_env fn_lookup have ty_dist: "distinct (FI_TyArgs funInfo)"
            unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast
          \<comment> \<open>FI_ReturnType funInfo is runtime in body_env_for env funInfo (whose
              TE_RuntimeTypeVars = fset_of_list (FI_TyArgs funInfo)), so its tyvars
              are \<subseteq> set (FI_TyArgs funInfo). Use tyenv_fun_ghost_constraint. \<close>
          from wf_env fn_lookup not_ghost have ret_runtime:
            "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                             (FI_ReturnType funInfo)"
            unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def
            by (auto simp: Let_def)
          from is_runtime_type_tyvars_subset[OF ret_runtime]
          have ret_tyvars_sub:
            "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
            by (simp add: fset_of_list.rep_eq)
          have compose:
            "apply_subst tySubst (FI_ReturnType funInfo)
             = apply_subst (IS_TyArgs state)
                 (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                              (FI_ReturnType funInfo))"
            unfolding tySubst_def
            using apply_subst_compose_zip[OF ty_len[symmetric] ret_tyvars_sub ty_dist] .
          from retTy_eq compose
          have retTy_apply:
            "apply_subst (IS_TyArgs state) retTy
               = apply_subst tySubst (FI_ReturnType funInfo)"
            by simp

          \<comment> \<open>Final return-type fact. \<close>
          from ret_typed_env retTy_apply
          have ret_final:
            "value_has_type env retVal (apply_subst (IS_TyArgs state) retTy)"
            by simp

          \<comment> \<open>Assemble the three conjuncts of sound_function_call_result. \<close>
          have witness:
            "(\<exists>storeTyping'.
                state_matches_env (restore_scope state postCallState) env storeTyping'
                \<and> storeTyping_extends storeTyping storeTyping')
              \<and> IS_TyArgs (restore_scope state postCallState) = IS_TyArgs state
              \<and> value_has_type env retVal (apply_subst (IS_TyArgs state) retTy)"
            using sme_rs ext_id tyargs_rs ret_final by blast
          from witness interp_result
          show ?thesis by simp
        qed
      qed
    next
      case body_extern: (Inr externFun)
      \<comment> \<open>Extern body — discharge via extern_fun_contract. \<close>

      from fi_match body_extern have ext_contract:
        "extern_fun_contract env funInfo externFun"
        unfolding fun_info_matches_interp_fun_def by simp

      \<comment> \<open>The interpreter result for the extern branch. \<close>
      let ?vals = "rights ?valResults"
      let ?refs = "rights (map (\<lambda>((_, vr), refResult).
                                  if vr = Ref then refResult else Inl TypeError)
                              (zip (IF_Args f) ?refResults))"

      \<comment> \<open>Unfold the externFun call. \<close>
      obtain newWorld refUpdates retVal where
        ext_call: "externFun (IS_World state) ?vals = (newWorld, refUpdates, retVal)"
        by (cases "externFun (IS_World state) ?vals") auto
      let ?stateW = "state \<lparr> IS_World := newWorld \<rparr>"

      \<comment> \<open>The fold succeeded, so all valResults are Inr and all Ref-position
          refResults are Inr. \<close>
      have fold_eq: "fold process_one_arg ?argTuples (Inr ?clearedState) = Inr preCallState"
        using fold_Inr by simp
      have len_iv: "length (IF_Args f) = length ?valResults"
        using len_argTms len_fi by simp
      have len_ir: "length (IF_Args f) = length ?refResults"
        using len_argTms len_fi by simp
      from fold_process_one_arg_inr_inversion[OF fold_eq len_ir len_iv]
      have inr_chars:
        "\<forall>i < length (IF_Args f).
           (\<exists>v. ?valResults ! i = Inr v) \<and>
           (snd ((IF_Args f) ! i) = Ref \<longrightarrow> (\<exists>a p. ?refResults ! i = Inr (a, p)))" .

      \<comment> \<open>All valResults are Inr — construct the vals list. \<close>
      have all_val_inr: "\<forall>i < length argTms. \<exists>v. ?valResults ! i = Inr v"
        using inr_chars len_argTms len_fi by simp

      \<comment> \<open>rights of an all-Inr list preserves length and indexing. Discharged
          via standalone lemmas. \<close>
      have vals_len: "length ?vals = length argTms"
        using all_val_inr rights_all_inr_length by (metis length_map)
      have vals_nth: "\<And>i. i < length argTms \<Longrightarrow> Inr (?vals ! i) = ?valResults ! i"
        using all_val_inr rights_all_inr_nth by (metis len_argTms len_iv)

      \<comment> \<open>Each val has the substituted parameter type. From vals_sound (in outerSubst
          form), apply_subst_compose_zip converts to tySubst form. \<close>
      have vals_typed:
        "\<forall>i < length argTms.
           value_has_type env (?vals ! i)
              (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i))))"
      proof (intro allI impI)
        fix i assume i_lt: "i < length argTms"
        with len_argTms_fi have i_fi: "i < length (FI_TmArgs funInfo)" by simp
        let ?paramTy_i = "fst (snd (FI_TmArgs funInfo ! i))"
        from vals_sound i_fi have outer_sound:
          "sound_term_result state env
             (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i)
             (?valResults ! i)" by blast
        from all_val_inr i_lt obtain v where v_eq: "?valResults ! i = Inr v" by blast
        from vals_nth[OF i_lt] v_eq have vals_at_i: "?vals ! i = v" by auto
        from outer_sound v_eq have
          "value_has_type env v
             (apply_subst (IS_TyArgs state)
                (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i))"
          by simp
        moreover have paramTy_subset: "type_tyvars ?paramTy_i \<subseteq> set (FI_TyArgs funInfo)"
        proof -
          have "?paramTy_i \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
            using i_fi by force
          from wf_env fn_lookup not_ghost have
            "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                              ?paramTy_i"
            unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def
            using \<open>?paramTy_i \<in> _\<close> by blast
          from is_runtime_type_tyvars_subset[OF this]
          show ?thesis by (simp add: fset_of_list.rep_eq)
        qed
        have compose:
          "apply_subst tySubst ?paramTy_i
            = apply_subst (IS_TyArgs state)
                (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i)"
          unfolding tySubst_def
          using apply_subst_compose_zip[OF ty_len[symmetric] paramTy_subset ty_dist] .
        ultimately have v_typed_tySubst:
          "value_has_type env v (apply_subst tySubst ?paramTy_i)"
          by simp
        show "value_has_type env (?vals ! i) (apply_subst tySubst ?paramTy_i)"
          using v_typed_tySubst vals_at_i by simp
      qed

      \<comment> \<open>Discharge the contract's preconditions: domain, ground/wk/rt range, and
          the list_all2 typing of vals. \<close>
      have prem_dom: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
        using fmdom_tySubst .

      \<comment> \<open>tySubst's range is well-kinded + runtime in env (apply_subst preserves them
          since IS_TyArgs state's range is wk/rt in env). The result is also ground
          by tySubst_range_ground. \<close>
      have prem_range:
        "\<forall>ty' \<in> fmran' tySubst.
           type_tyvars ty' = {} \<and> is_well_kinded env ty' \<and> is_runtime_type env ty'"
      proof
        fix ty' assume mem: "ty' \<in> fmran' tySubst"
        \<comment> \<open>Groundness from tySubst_range_ground. \<close>
        have ground_ty': "type_tyvars ty' = {}"
        proof -
          from mem obtain n where lk: "fmlookup tySubst n = Some ty'"
            by (auto simp: fmran'_alt_def fmlookup_dom_iff)
          have "ty' \<in> snd ` Map.graph (fmlookup tySubst)"
            using lk by (simp add: ranI snd_graph_ran)
          \<comment> \<open>Use tySubst_range_ground directly: it says all elements of fmran' are ground. \<close>
          from tySubst_range_ground have
            "\<forall>n \<in> fset (fmdom tySubst).
               case fmlookup tySubst n of
                 Some t \<Rightarrow> type_tyvars t = {}
               | None \<Rightarrow> True"
            unfolding subst_range_tyvars_def using fmran'I by fastforce
          with lk show ?thesis
            using fmdomI by fastforce
        qed
        \<comment> \<open>ty' = apply_subst (IS_TyArgs state) (tyArgs ! j) for some j. \<close>
        from mem obtain n where lk: "fmlookup tySubst n = Some ty'"
          by (auto simp: fmran'_alt_def fmlookup_dom_iff)
        from lk tySubst_def
        have "map_of (zip (FI_TyArgs funInfo)
                (map (apply_subst (IS_TyArgs state)) tyArgs)) n = Some ty'"
          by (simp add: fmap_of_list.rep_eq)
        hence "(n, ty') \<in> set (zip (FI_TyArgs funInfo)
                                (map (apply_subst (IS_TyArgs state)) tyArgs))"
          by (rule map_of_SomeD)
        then obtain j where j_lt: "j < length tyArgs"
          and ty'_eq: "ty' = apply_subst (IS_TyArgs state) (tyArgs ! j)"
          using ty_len by (auto simp: set_zip)
        from ty_wk j_lt have wk_j: "is_well_kinded env (tyArgs ! j)"
          by (simp add: list_all_length)
        from ty_rt j_lt have rt_j: "is_runtime_type env (tyArgs ! j)"
          by (simp add: list_all_length)
        \<comment> \<open>Apply apply_subst (IS_TyArgs state) preserves wk and rt in env. \<close>
        have wk_subst:
          "\<And>n. n |\<in>| TE_TypeVars env \<Longrightarrow>
                (case fmlookup (IS_TyArgs state) n of
                   Some t \<Rightarrow> is_well_kinded env t
                 | None \<Rightarrow> n |\<in>| TE_TypeVars env)"
        proof -
          fix n assume "n |\<in>| TE_TypeVars env"
          show "case fmlookup (IS_TyArgs state) n of
                  Some t \<Rightarrow> is_well_kinded env t
                | None \<Rightarrow> n |\<in>| TE_TypeVars env"
            using caller_range_wk_rt
            by (cases "fmlookup (IS_TyArgs state) n")
               (auto simp: \<open>n |\<in>| TE_TypeVars env\<close> fmran'I)
        qed
        have wk_apply: "is_well_kinded env (apply_subst (IS_TyArgs state) (tyArgs ! j))"
          using apply_subst_preserves_well_kinded[OF wk_j refl wk_subst] .
        have rt_subst:
          "\<And>n. n |\<in>| TE_RuntimeTypeVars env \<Longrightarrow>
                (case fmlookup (IS_TyArgs state) n of
                   Some t \<Rightarrow> is_runtime_type env t
                 | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env)"
        proof -
          fix n assume "n |\<in>| TE_RuntimeTypeVars env"
          show "case fmlookup (IS_TyArgs state) n of
                  Some t \<Rightarrow> is_runtime_type env t
                | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
            using caller_range_wk_rt
            by (cases "fmlookup (IS_TyArgs state) n")
               (auto simp: \<open>n |\<in>| TE_RuntimeTypeVars env\<close> fmran'I)
        qed
        have rt_apply: "is_runtime_type env (apply_subst (IS_TyArgs state) (tyArgs ! j))"
          using apply_subst_preserves_runtime[OF rt_j refl rt_subst] .
        show "type_tyvars ty' = {} \<and> is_well_kinded env ty' \<and> is_runtime_type env ty'"
          using ground_ty' wk_apply rt_apply ty'_eq by simp
      qed

      \<comment> \<open>vals satisfy the list_all2 typing. \<close>
      have prem_list_all2:
        "list_all2 (value_has_type env) ?vals
           (map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))"
      proof -
        have len_map: "length (map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))
                      = length ?vals"
          using vals_len len_argTms_fi by simp
        show ?thesis
          unfolding list_all2_conv_all_nth
        proof (intro conjI allI impI)
          show "length ?vals = length (map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))"
            using vals_len len_argTms_fi by simp
          fix i assume i_lt: "i < length ?vals"
          from i_lt vals_len have i_argTms: "i < length argTms" by simp
          from i_argTms len_argTms_fi have i_fi: "i < length (FI_TmArgs funInfo)" by simp
          from vals_typed i_argTms have
            "value_has_type env (?vals ! i) (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i))))"
            by blast
          moreover have
            "(map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo)) ! i
              = apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! i)))"
            using i_fi by (simp add: case_prod_beta)
          ultimately show
            "value_has_type env (?vals ! i)
              ((map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo)) ! i)"
            by simp
        qed
      qed

      \<comment> \<open>Apply the contract to get the post-conditions. \<close>
      from ext_contract have ext_inst:
        "fmdom tySubst = fset_of_list (FI_TyArgs funInfo) \<and>
         (\<forall>ty' \<in> fmran' tySubst.
              type_tyvars ty' = {} \<and> is_well_kinded env ty' \<and> is_runtime_type env ty') \<and>
         list_all2 (value_has_type env) ?vals
                   (map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))
         \<longrightarrow> (case externFun (IS_World state) ?vals of
                (newWorld, refUpdates, retVal) \<Rightarrow>
                  value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo)) \<and>
                  list_all2 (value_has_type env) refUpdates
                    (map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                         (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo))))"
        unfolding extern_fun_contract_def by meson
      from ext_inst prem_dom prem_range prem_list_all2
      have contract_implies:
        "case externFun (IS_World state) ?vals of
           (newWorld, refUpdates, retVal) \<Rightarrow>
             value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo)) \<and>
             list_all2 (value_has_type env) refUpdates
               (map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                    (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo)))"
        by meson
      from contract_implies ext_call
      have contract_post:
        "value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo))
         \<and> list_all2 (value_has_type env) refUpdates
             (map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                  (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo)))"
        by simp
      from contract_post have ret_typed_apply:
        "value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo))"
        by simp
      from contract_post have ref_updates_typed:
        "list_all2 (value_has_type env) refUpdates
           (map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo)))"
        by simp

      \<comment> \<open>Now build the ref-list information for apply_ref_updates_sound. \<close>
      \<comment> \<open>FI_TmArgs and IF_Args have matching Var/Ref positions. \<close>
      from fi_match have if_args_match:
        "list_all2 (\<lambda>(name1, _, vor1) (name2, vor2). name1 = name2 \<and> vor1 = vor2)
                   (FI_TmArgs funInfo) (IF_Args f)"
        unfolding fun_info_matches_interp_fun_def by simp
      have vor_match:
        "\<forall>i < length (IF_Args f).
             snd ((IF_Args f) ! i) = Ref \<longleftrightarrow> snd (snd (FI_TmArgs funInfo ! i)) = Ref"
      proof (intro allI impI)
        fix i assume i_lt: "i < length (IF_Args f)"
        with len_fi have i_fi: "i < length (FI_TmArgs funInfo)" by simp
        obtain n1 t1 v1 where fi_i: "FI_TmArgs funInfo ! i = (n1, t1, v1)"
          by (cases "FI_TmArgs funInfo ! i") auto
        obtain n2 v2 where if_i: "(IF_Args f) ! i = (n2, v2)"
          by (cases "(IF_Args f) ! i") auto
        from if_args_match i_lt len_fi fi_i if_i have "v1 = v2"
          by (auto simp: list_all2_conv_all_nth)
        thus "snd ((IF_Args f) ! i) = Ref \<longleftrightarrow> snd (snd (FI_TmArgs funInfo ! i)) = Ref"
          using fi_i if_i by simp
      qed

      \<comment> \<open>From fold_process_one_arg_inr_inversion: each Ref-position refResult is Inr. \<close>
      have all_ref_inr:
        "\<forall>i < length (IF_Args f). snd ((IF_Args f) ! i) = Ref
           \<longrightarrow> (\<exists>a p. ?refResults ! i = Inr (a, p))"
        using inr_chars by blast

      \<comment> \<open>Bind the idxs list name. \<close>
      define idxs :: "nat list" where
        idxs_def: "idxs = filter (\<lambda>i. snd ((IF_Args f) ! i) = Ref) [0 ..< length (IF_Args f)]"
      from rights_filter_zip_refs_chars[OF len_ir all_ref_inr]
      have refs_len: "length ?refs = length idxs"
        and refs_nth: "\<forall>j < length idxs.
                          ?refResults ! (idxs ! j) = Inr (?refs ! j)"
        unfolding idxs_def by auto

      \<comment> \<open>The Ref-filtered FI_TmArgs aligns with idxs: idxs ! j is the FI_TmArgs
          index of the j-th Ref parameter. \<close>
      have idxs_in_bound: "\<forall>j < length idxs. idxs ! j < length (IF_Args f)"
      proof (intro allI impI)
        fix j assume "j < length idxs"
        then have mem: "idxs ! j \<in> set idxs" by simp
        hence "idxs ! j \<in> set (filter (\<lambda>i. snd ((IF_Args f) ! i) = Ref) [0 ..< length (IF_Args f)])"
          unfolding idxs_def .
        hence "idxs ! j \<in> set [0 ..< length (IF_Args f)]" by auto
        thus "idxs ! j < length (IF_Args f)" by simp
      qed
      have idxs_is_ref:
        "\<forall>j < length idxs. snd ((IF_Args f) ! (idxs ! j)) = Ref"
      proof (intro allI impI)
        fix j assume "j < length idxs"
        then have mem: "idxs ! j \<in> set idxs" by simp
        hence "idxs ! j \<in> set (filter (\<lambda>i. snd ((IF_Args f) ! i) = Ref) [0 ..< length (IF_Args f)])"
          unfolding idxs_def .
        thus "snd ((IF_Args f) ! (idxs ! j)) = Ref" by simp
      qed

      \<comment> \<open>The filter on FI_TmArgs gives the same length as idxs (via vor_match).
          Strategy: both filter-lengths equal the cardinality of the Ref-positions
          among [0 ..< length FI_TmArgs funInfo] = [0 ..< length (IF_Args f)]. \<close>
      have filter_FI_len:
        "length (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo)) = length idxs"
      proof -
        \<comment> \<open>Step 1: count Ref-positions in FI_TmArgs by indexing. \<close>
        have count_FI:
          "length (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo))
            = card {i. i < length (FI_TmArgs funInfo) \<and> snd (snd (FI_TmArgs funInfo ! i)) = Ref}"
        proof -
          have "length (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo))
                = card {i. i < length (FI_TmArgs funInfo) \<and>
                            (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo ! i)}"
            by (simp add: length_filter_conv_card)
          also have "\<dots> = card {i. i < length (FI_TmArgs funInfo) \<and>
                                  snd (snd (FI_TmArgs funInfo ! i)) = Ref}"
            by (rule arg_cong[where f=card]) (auto simp: case_prod_unfold)
          finally show ?thesis .
        qed
        \<comment> \<open>Step 2: same count on idxs. \<close>
        have count_idxs:
          "length idxs = card {i. i < length (IF_Args f) \<and> snd ((IF_Args f) ! i) = Ref}"
        proof -
          have "length idxs
              = length (filter (\<lambda>i. snd ((IF_Args f) ! i) = Ref) [0 ..< length (IF_Args f)])"
            unfolding idxs_def by simp
          also have "\<dots> = card {i. i < length [0 ..< length (IF_Args f)]
                                  \<and> snd ((IF_Args f) ! ([0 ..< length (IF_Args f)] ! i)) = Ref}"
            by (rule length_filter_conv_card)
          also have "\<dots> = card {i. i < length (IF_Args f) \<and> snd ((IF_Args f) ! i) = Ref}"
            by (rule arg_cong[where f=card]) auto
          finally show ?thesis .
        qed
        \<comment> \<open>Step 3: the two index-sets are equal (via vor_match + len_fi). \<close>
        have sets_eq:
          "{i. i < length (FI_TmArgs funInfo) \<and> snd (snd (FI_TmArgs funInfo ! i)) = Ref}
            = {i. i < length (IF_Args f) \<and> snd ((IF_Args f) ! i) = Ref}"
          using len_fi vor_match by auto
        show ?thesis
          using count_FI count_idxs sets_eq by simp
      qed

      \<comment> \<open>length refUpdates = length idxs (via list_all2 from contract + filter_FI_len). \<close>
      have refUpdates_len: "length refUpdates = length idxs"
        using ref_updates_typed filter_FI_len
        by (auto dest: list_all2_lengthD)

      \<comment> \<open>For each j < length idxs, the j-th ref from ?refs has good (addr, path) data
          against storeTyping, at type apply_subst tySubst (paramTy_at_idxs_j). \<close>
      \<comment> \<open>This uses lvals_sound at index (idxs ! j), with compose_zip to convert
          outerSubst \<rightarrow> tySubst. \<close>
      have ref_typed_at_idx:
        "\<forall>j < length idxs.
            (fst (?refs ! j) < length (IS_Store state) \<and>
             type_at_path env (storeTyping ! (fst (?refs ! j))) (snd (?refs ! j))
               = Some (apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! (idxs ! j))))))"
      proof (intro allI impI)
        fix j assume j_lt: "j < length idxs"
        let ?i = "idxs ! j"
        from idxs_in_bound j_lt have i_lt_if: "?i < length (IF_Args f)" by blast
        with len_fi have i_lt_fi: "?i < length (FI_TmArgs funInfo)" by simp
        with len_argTms_fi have i_lt_argTms: "?i < length argTms" by simp
        from idxs_is_ref j_lt have if_i_ref: "snd ((IF_Args f) ! ?i) = Ref" by blast
        with vor_match i_lt_if have fi_i_ref: "snd (snd (FI_TmArgs funInfo ! ?i)) = Ref"
          by blast
        let ?paramTy_i = "fst (snd (FI_TmArgs funInfo ! ?i))"

        \<comment> \<open>lvals_sound at index ?i (outer form). \<close>
        from lvals_sound i_lt_fi fi_i_ref have
          "sound_lvalue_result state env storeTyping
             (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i)
             (?refResults ! ?i)" by blast

        \<comment> \<open>?refResults ! ?i = Inr (?refs ! j). \<close>
        from refs_nth j_lt have refResults_at: "?refResults ! ?i = Inr (?refs ! j)" by blast
        obtain a p where refs_j: "?refs ! j = (a, p)" by (cases "?refs ! j") auto

        \<comment> \<open>Combine: addr < store, type_at_path = Some (apply_subst outerSubst paramTy). \<close>
        from \<open>sound_lvalue_result _ _ _ _ _\<close> refResults_at refs_j have lval_facts:
          "a < length (IS_Store state) \<and>
           type_at_path env (storeTyping ! a) p
             = Some (apply_subst (IS_TyArgs state)
                        (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i))"
          by simp

        \<comment> \<open>compose_zip: apply_subst (IS_TyArgs state) (apply_subst outerSubst paramTy_i)
            = apply_subst tySubst paramTy_i. \<close>
        have paramTy_subset: "type_tyvars ?paramTy_i \<subseteq> set (FI_TyArgs funInfo)"
        proof -
          have "?paramTy_i \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
            using i_lt_fi by force
          from wf_env fn_lookup not_ghost have
            "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                              ?paramTy_i"
            unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def
            using \<open>?paramTy_i \<in> _\<close> by blast
          from is_runtime_type_tyvars_subset[OF this]
          show ?thesis by (simp add: fset_of_list.rep_eq)
        qed
        have compose:
          "apply_subst tySubst ?paramTy_i
            = apply_subst (IS_TyArgs state)
                (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i)"
          unfolding tySubst_def
          using apply_subst_compose_zip[OF ty_len[symmetric] paramTy_subset ty_dist] .
        show "fst (?refs ! j) < length (IS_Store state) \<and>
              type_at_path env (storeTyping ! (fst (?refs ! j))) (snd (?refs ! j))
                = Some (apply_subst tySubst ?paramTy_i)"
          using lval_facts compose refs_j by simp
      qed

      \<comment> \<open>Define tys as the contract's expected type list for refUpdates. \<close>
      define tys :: "CoreType list" where
        tys_def: "tys = map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                            (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo))"

      have tys_len: "length tys = length idxs"
        using tys_def filter_FI_len by simp

      \<comment> \<open>tys ! j = apply_subst tySubst (paramTy_at (idxs ! j)). The j-th Ref
          FI_TmArg's paramTy is the paramTy of FI_TmArgs ! (idxs ! j). \<close>
      \<comment> \<open>Step: filter P xs = map ((!) xs) (filter (\<lambda>i. P (xs!i)) [0..<length xs]). \<close>
      have filter_via_indices:
        "\<And>(P :: 'a \<Rightarrow> bool) (xs :: 'a list).
           filter P xs = map (\<lambda>i. xs ! i) (filter (\<lambda>i. P (xs ! i)) [0 ..< length xs])"
      proof -
        fix P :: "'a \<Rightarrow> bool" and xs :: "'a list"
        show "filter P xs = map (\<lambda>i. xs ! i) (filter (\<lambda>i. P (xs ! i)) [0 ..< length xs])"
        proof (induction xs rule: rev_induct)
          case Nil thus ?case by simp
        next
          case (snoc x xs)
          have len_eq: "length (xs @ [x]) = length xs + 1" by simp
          have nth_xs: "\<And>i. i < length xs \<Longrightarrow> (xs @ [x]) ! i = xs ! i"
            by (simp add: nth_append)
          have nth_x: "(xs @ [x]) ! length xs = x"
            by (simp add: nth_append)
          have upt_eq: "[0 ..< length (xs @ [x])] = [0 ..< length xs] @ [length xs]"
            using len_eq by (simp add: upt_Suc_append)
          have filter_idx_eq:
            "filter (\<lambda>i. P ((xs @ [x]) ! i)) [0 ..< length xs]
              = filter (\<lambda>i. P (xs ! i)) [0 ..< length xs]"
            using nth_xs by (intro filter_cong) auto
          show ?case
          proof (cases "P x")
            case True
            have "filter P (xs @ [x]) = filter P xs @ [x]"
              using True by simp
            also have "\<dots> = map ((!) xs) (filter (\<lambda>i. P (xs ! i)) [0 ..< length xs]) @ [x]"
              using snoc.IH by simp
            also have "\<dots> = map (\<lambda>i. (xs @ [x]) ! i)
                                (filter (\<lambda>i. P (xs ! i)) [0 ..< length xs]) @ [x]"
              using nth_xs by (auto intro: map_cong)
            also have "\<dots> = map (\<lambda>i. (xs @ [x]) ! i)
                                (filter (\<lambda>i. P ((xs @ [x]) ! i)) [0 ..< length xs])
                              @ [(xs @ [x]) ! length xs]"
              using filter_idx_eq nth_x by simp
            also have "\<dots> = map (\<lambda>i. (xs @ [x]) ! i)
                                (filter (\<lambda>i. P ((xs @ [x]) ! i))
                                        ([0 ..< length xs] @ [length xs]))"
              using True nth_x by simp
            also have "\<dots> = map (\<lambda>i. (xs @ [x]) ! i)
                                (filter (\<lambda>i. P ((xs @ [x]) ! i))
                                        [0 ..< length (xs @ [x])])"
              using upt_eq by simp
            finally show ?thesis .
          next
            case False
            have "filter P (xs @ [x]) = filter P xs"
              using False by simp
            also have "\<dots> = map ((!) xs) (filter (\<lambda>i. P (xs ! i)) [0 ..< length xs])"
              using snoc.IH .
            also have "\<dots> = map (\<lambda>i. (xs @ [x]) ! i)
                                (filter (\<lambda>i. P (xs ! i)) [0 ..< length xs])"
              using nth_xs by (auto intro: map_cong)
            also have "\<dots> = map (\<lambda>i. (xs @ [x]) ! i)
                                (filter (\<lambda>i. P ((xs @ [x]) ! i)) [0 ..< length xs])"
              using filter_idx_eq by simp
            also have "\<dots> = map (\<lambda>i. (xs @ [x]) ! i)
                                (filter (\<lambda>i. P ((xs @ [x]) ! i))
                                        ([0 ..< length xs] @ [length xs]))"
              using False nth_x by simp
            also have "\<dots> = map (\<lambda>i. (xs @ [x]) ! i)
                                (filter (\<lambda>i. P ((xs @ [x]) ! i))
                                        [0 ..< length (xs @ [x])])"
              using upt_eq by simp
            finally show ?thesis .
          qed
        qed
      qed

      \<comment> \<open>Apply: filter (Ref-only) FI_TmArgs = map (FI_TmArgs !) idxs_FI, where
          idxs_FI = filter (\<lambda>i. snd(snd(FI_TmArgs ! i)) = Ref) [0..<len]. \<close>
      have fi_filter_indexed:
        "filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo)
          = map (\<lambda>i. FI_TmArgs funInfo ! i)
                (filter (\<lambda>i. snd (snd (FI_TmArgs funInfo ! i)) = Ref)
                        [0 ..< length (FI_TmArgs funInfo)])"
        using filter_via_indices[where P = "\<lambda>(_, _, vor). vor = Ref"
                                   and xs = "FI_TmArgs funInfo"]
        by (auto simp: case_prod_unfold)

      \<comment> \<open>idxs_FI = idxs (via vor_match + len_fi). \<close>
      have idxs_FI_eq_idxs:
        "filter (\<lambda>i. snd (snd (FI_TmArgs funInfo ! i)) = Ref)
                [0 ..< length (FI_TmArgs funInfo)]
          = idxs"
      proof -
        have len_upt: "[0 ..< length (FI_TmArgs funInfo)] = [0 ..< length (IF_Args f)]"
          using len_fi by simp
        have pred_eq:
          "\<And>i. i < length (IF_Args f) \<Longrightarrow>
                snd (snd (FI_TmArgs funInfo ! i)) = Ref
                \<longleftrightarrow> snd ((IF_Args f) ! i) = Ref"
          using vor_match by blast
        have "filter (\<lambda>i. snd (snd (FI_TmArgs funInfo ! i)) = Ref)
                     [0 ..< length (FI_TmArgs funInfo)]
            = filter (\<lambda>i. snd (snd (FI_TmArgs funInfo ! i)) = Ref)
                     [0 ..< length (IF_Args f)]"
          using len_upt by simp
        also have "\<dots> = filter (\<lambda>i. snd ((IF_Args f) ! i) = Ref)
                                [0 ..< length (IF_Args f)]"
          using pred_eq by (intro filter_cong) auto
        finally show ?thesis unfolding idxs_def .
      qed

      have fi_filter_eq:
        "filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo)
          = map (\<lambda>i. FI_TmArgs funInfo ! i) idxs"
        using fi_filter_indexed idxs_FI_eq_idxs by simp

      have tys_nth:
        "\<forall>j < length idxs. tys ! j
          = apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! (idxs ! j))))"
      proof (intro allI impI)
        fix j assume j_lt: "j < length idxs"
        have "tys ! j
            = ((map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                    (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo))) ! j)"
          unfolding tys_def by simp
        also have "\<dots> = ((map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                              (map (\<lambda>i. FI_TmArgs funInfo ! i) idxs)) ! j)"
          using fi_filter_eq by simp
        also have "\<dots> = (\<lambda>(_, ty, _). apply_subst tySubst ty)
                          ((map (\<lambda>i. FI_TmArgs funInfo ! i) idxs) ! j)"
          using j_lt by simp
        also have "\<dots> = (\<lambda>(_, ty, _). apply_subst tySubst ty)
                          (FI_TmArgs funInfo ! (idxs ! j))"
          using j_lt by simp
        also have "\<dots> = apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! (idxs ! j))))"
          by (simp add: case_prod_beta)
        finally show "tys ! j
                        = apply_subst tySubst (fst (snd (FI_TmArgs funInfo ! (idxs ! j))))" .
      qed

      \<comment> \<open>refs_ok for apply_ref_updates_sound: each ?refs ! j has valid addr/path
          of type tys ! j. \<close>
      have refs_ok:
        "\<forall>j < length ?refs.
            fst (?refs ! j) < length (IS_Store state) \<and>
            type_at_path env (storeTyping ! (fst (?refs ! j))) (snd (?refs ! j))
              = Some (tys ! j)"
        using ref_typed_at_idx tys_nth refs_len by auto

      \<comment> \<open>vals_typed for apply_ref_updates_sound: each refUpdate has type tys ! j. \<close>
      have refUpdates_vals_typed:
        "\<forall>j < length refUpdates. value_has_type env (refUpdates ! j) (tys ! j)"
      proof (intro allI impI)
        fix j assume j_lt: "j < length refUpdates"
        from ref_updates_typed have len_eq:
          "length refUpdates
            = length (map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                          (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo)))"
          by (auto dest: list_all2_lengthD)
        from ref_updates_typed j_lt have
          "value_has_type env (refUpdates ! j)
             ((map (\<lambda>(_, ty, _). apply_subst tySubst ty)
                   (filter (\<lambda>(_, _, vor). vor = Ref) (FI_TmArgs funInfo))) ! j)"
          using list_all2_nthD by fastforce
        thus "value_has_type env (refUpdates ! j) (tys ! j)"
          unfolding tys_def by simp
      qed

      \<comment> \<open>state_matches_env carries over to ?stateW (which only differs in IS_World).
          All record selectors except IS_World agree between state and ?stateW.
          Strategy: replace ?stateW directly using state_matches_env_TE_ProofGoal-style
          cong... actually, just prove conjunct-by-conjunct. \<close>
      have stateW_eqs [simp]:
        "IS_Locals ?stateW = IS_Locals state"
        "IS_Refs ?stateW = IS_Refs state"
        "IS_Globals ?stateW = IS_Globals state"
        "IS_Functions ?stateW = IS_Functions state"
        "IS_Store ?stateW = IS_Store state"
        "IS_ConstLocals ?stateW = IS_ConstLocals state"
        "IS_TyArgs ?stateW = IS_TyArgs state"
        by simp_all
      \<comment> \<open>The trick: state and ?stateW have the same value under all selectors
          referenced by state_matches_env (which doesn't look at IS_World). \<close>
      have stateW_locals: "IS_Locals ?stateW = IS_Locals state" by simp
      have stateW_refs: "IS_Refs ?stateW = IS_Refs state" by simp
      have stateW_globals: "IS_Globals ?stateW = IS_Globals state" by simp
      have stateW_functions: "IS_Functions ?stateW = IS_Functions state" by simp
      have stateW_store: "IS_Store ?stateW = IS_Store state" by simp
      have stateW_consts: "IS_ConstLocals ?stateW = IS_ConstLocals state" by simp
      have stateW_tyargs: "IS_TyArgs ?stateW = IS_TyArgs state" by simp
      \<comment> \<open>Each conjunct of state_matches_env carries over via these selector equalities. \<close>
      have sme_stateW: "state_matches_env ?stateW env storeTyping"
        unfolding state_matches_env_def
      proof (intro conjI)
        show "local_vars_exist_in_state ?stateW env storeTyping"
          using state_env
          unfolding state_matches_env_def local_vars_exist_in_state_def
                    local_var_in_state_with_type_def
          using stateW_locals stateW_refs stateW_store stateW_tyargs by presburger
      next
        show "global_vars_exist_in_state ?stateW env"
          using state_env
          unfolding state_matches_env_def global_vars_exist_in_state_def
                    global_var_in_state_with_type_def
          by simp
      next
        show "no_extra_local_vars ?stateW env"
          using state_env
          unfolding state_matches_env_def no_extra_local_vars_def
          by simp
      next
        show "no_extra_global_vars ?stateW env"
          using state_env
          unfolding state_matches_env_def no_extra_global_vars_def
          by simp
      next
        show "funs_exist_in_state ?stateW env"
          using state_env
          unfolding state_matches_env_def funs_exist_in_state_def
          by simp
      next
        show "no_extra_funs ?stateW env"
          using state_env
          unfolding state_matches_env_def no_extra_funs_def
          by simp
      next
        show "const_locals_match ?stateW env"
          using state_env
          unfolding state_matches_env_def const_locals_match_def
          by simp
      next
        show "store_well_typed ?stateW env storeTyping"
          using state_env
          unfolding state_matches_env_def store_well_typed_def
          by simp
      next
        show "ty_args_well_formed ?stateW env"
          using state_env
          unfolding state_matches_env_def ty_args_well_formed_def
          by simp
      qed

      \<comment> \<open>Apply apply_ref_updates_sound to get state_matches for the final state. \<close>
      have apply_refs_sound:
        "case apply_ref_updates ?stateW ?refs refUpdates of
           Inl err \<Rightarrow> sound_error_result err
         | Inr finalState \<Rightarrow> state_matches_env finalState env storeTyping"
        using apply_ref_updates_sound[OF sme_stateW _ _ _ refUpdates_vals_typed]
              refUpdates_len refs_len tys_len refs_ok
        by simp

      \<comment> \<open>Compute the concrete interp result and discharge sound_function_call_result. \<close>
      from interp_eq fold_Inr body_extern ext_call
      have interp_result:
        "interp_function_call (Suc fuel) state fnName tyArgs argTms
           = (case apply_ref_updates ?stateW ?refs refUpdates of
                Inr finalState \<Rightarrow> Inr (finalState, retVal)
              | Inl err \<Rightarrow> Inl err)"
        by simp

      show ?thesis
      proof (cases "apply_ref_updates ?stateW ?refs refUpdates")
        case (Inl err)
        \<comment> \<open>apply_ref_updates errored — sound. \<close>
        from apply_refs_sound Inl have "sound_error_result err" by simp
        moreover from interp_result Inl have
          "interp_function_call (Suc fuel) state fnName tyArgs argTms = Inl err" by simp
        ultimately show ?thesis by simp
      next
        case (Inr finalState)
        \<comment> \<open>apply_ref_updates succeeded. The final state matches env under storeTyping. \<close>
        from apply_refs_sound Inr have sme_final:
          "state_matches_env finalState env storeTyping" by simp
        \<comment> \<open>IS_TyArgs is preserved (apply_ref_updates_preserves_globals_funs gives the
            IS_TyArgs preservation). \<close>
        from apply_ref_updates_preserves_globals_funs[OF Inr]
        have tyargs_final: "IS_TyArgs finalState = IS_TyArgs ?stateW" by simp
        have tyargs_stateW: "IS_TyArgs ?stateW = IS_TyArgs state" by simp
        \<comment> \<open>Reconcile retTy: retTy = apply_subst outerSubst (FI_ReturnType funInfo).
            The contract gave value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo)),
            and apply_subst (IS_TyArgs state) retTy = apply_subst tySubst (FI_ReturnType funInfo)
            by apply_subst_compose_zip + return-type tyvar bound. \<close>
        from wf_env fn_lookup not_ghost have ret_runtime:
          "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                   TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                           (FI_ReturnType funInfo)"
          unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def
          by (auto simp: Let_def)
        from is_runtime_type_tyvars_subset[OF ret_runtime]
        have ret_tyvars_sub:
          "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
          by (simp add: fset_of_list.rep_eq)
        have ret_compose:
          "apply_subst tySubst (FI_ReturnType funInfo)
            = apply_subst (IS_TyArgs state)
                (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo))"
          unfolding tySubst_def
          using apply_subst_compose_zip[OF ty_len[symmetric] ret_tyvars_sub ty_dist] .
        from ret_typed_apply retTy_eq ret_compose
        have ret_typed_final:
          "value_has_type env retVal (apply_subst (IS_TyArgs state) retTy)"
          by simp

        \<comment> \<open>Assemble. \<close>
        have witness:
          "(\<exists>storeTyping'.
              state_matches_env finalState env storeTyping'
              \<and> storeTyping_extends storeTyping storeTyping')
            \<and> IS_TyArgs finalState = IS_TyArgs state
            \<and> value_has_type env retVal (apply_subst (IS_TyArgs state) retTy)"
          using sme_final storeTyping_extends_refl tyargs_final tyargs_stateW ret_typed_final
            by auto
        from witness interp_result Inr
        show ?thesis by simp
      qed
    qed
  qed
qed

end

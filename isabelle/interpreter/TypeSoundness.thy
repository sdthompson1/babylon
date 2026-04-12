theory TypeSoundness
  imports TypeSoundnessHelpers
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

(* A writable lvalue is sound if its address is in the store and its path
   statically descends to the expected type through the store typing.
   This implies: if get_value_at_path succeeds, the obtained value has type ty
   (by get_value_at_path_type); if it fails, the error is RuntimeError
   (by get_value_at_path_error_is_runtime). Callers that need either fact
   should derive it from store_well_typed. *)
fun sound_lvalue_result :: "'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> CoreType
    \<Rightarrow> InterpError + (nat \<times> LValuePath list) \<Rightarrow> bool" where
  "sound_lvalue_result state env storeTyping ty (Inl err) = sound_error_result err"
| "sound_lvalue_result state env storeTyping ty (Inr (addr, path)) =
    (addr < length (IS_Store state) \<and>
     type_at_path env (storeTyping ! addr) path = Some ty)"

(* The second store typing extends the first: every address present in the
   first typing retains the same type in the second, and the second may have
   additional entries appended. This captures the fact that executing a single
   statement only ever grows the store (or leaves it the same length) — while
   a While/Match body may internally call restore_scope, that only truncates
   slots the statement itself allocated, so the net effect still extends the
   old store typing rather than removing any pre-existing entries. *)
definition storeTyping_extends :: "CoreType list \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "storeTyping_extends st1 st2 \<equiv> \<exists>suffix. st2 = st1 @ suffix"

lemma storeTyping_extends_refl: "storeTyping_extends st st"
  unfolding storeTyping_extends_def by (rule exI[of _ "[]"]) simp

lemma storeTyping_extends_trans:
  "storeTyping_extends st1 st2 \<Longrightarrow> storeTyping_extends st2 st3 \<Longrightarrow> storeTyping_extends st1 st3"
  unfolding storeTyping_extends_def by auto

lemma storeTyping_extends_append: "storeTyping_extends st (st @ suffix)"
  unfolding storeTyping_extends_def by blast

fun sound_function_call_result :: "CoreTyEnv \<Rightarrow> CoreType list \<Rightarrow> CoreType \<Rightarrow>
    InterpError + ('w InterpState \<times> CoreValue) \<Rightarrow> bool" where
  "sound_function_call_result env storeTyping retTy (Inl err) = sound_error_result err"
| "sound_function_call_result env storeTyping retTy (Inr (newState, retVal)) =
    ((\<exists>storeTyping'. state_matches_env newState env storeTyping'
                   \<and> storeTyping_extends storeTyping storeTyping')
     \<and> value_has_type env retVal retTy)"

fun sound_statement_result :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> CoreType list
    \<Rightarrow> InterpError + 'w ExecResult \<Rightarrow> bool" where
  "sound_statement_result env env' storeTyping (Inl err) = sound_error_result err"
| "sound_statement_result env env' storeTyping (Inr (Continue state')) =
    (\<exists>storeTyping'. state_matches_env state' env' storeTyping'
                  \<and> storeTyping_extends storeTyping storeTyping')"
| "sound_statement_result env env' storeTyping (Inr (Return state' retVal)) =
    (value_has_type env retVal (TE_ReturnType env) \<and>
     (\<exists>env_mid storeTyping'. tyenv_subset env env_mid \<and> tyenv_subset env_mid env' \<and>
                state_matches_env state' env_mid storeTyping'
              \<and> storeTyping_extends storeTyping storeTyping'))"


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
               TE_ConstNames := finsert var (TE_ConstNames env) \<rparr>)
        NotGhost body = Some ty"
    by (auto split: option.splits if_splits)

  let ?env' = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                     TE_ConstNames := finsert var (TE_ConstNames env) \<rparr>"

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
                              IS_ConstNames := finsert var (IS_ConstNames state') \<rparr>"

    (* The interpreter result *)
    have interp_eq: "interp_term (Suc fuel) state (CoreTm_Let var rhs body) =
          interp_term fuel ?state'' body"
      using Inr alloc_eq by (simp add: case_prod_beta split: prod.splits)

    (* var is fresh and therefore not ghost *)
    from typing have var_fresh: "tyenv_lookup_var env var = None"
      by (auto split: option.splits if_splits)
    hence var_fresh_local: "fmlookup (TE_LocalVars env) var = None"
      and var_fresh_global: "fmlookup (TE_GlobalVars env) var = None"
      unfolding tyenv_lookup_var_def by (auto split: option.splits)
    from wf_env have "TE_GhostVars env |\<subseteq>| fmdom (TE_LocalVars env) |\<union>| fmdom (TE_GlobalVars env)"
      unfolding tyenv_well_formed_def tyenv_ghost_vars_subset_def by simp
    with var_fresh_local var_fresh_global have var_not_ghost: "var |\<notin>| TE_GhostVars env"
      by (metis fin_mono fmdom_notI funion_iff)

    (* The new state matches the extended env under the extended storeTyping *)
    have state''_env': "state_matches_env ?state'' ?env' (storeTyping @ [rhsTy])"
      using state_matches_env_add_const_local[OF state_env rhs_typed alloc_eq refl refl var_not_ghost]
      by simp

    (* The extended env is well-formed *)
    from value_has_type_runtime[OF rhs_typed] have rhs_rt: "is_runtime_type env rhsTy" .
    have rhs_wk: "is_well_kinded env rhsTy"
      using core_term_type_well_kinded[OF rhs_typing wf_env] .
    have wf_env': "tyenv_well_formed ?env'"
    proof -
      let ?env_mid = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env) \<rparr>"
      have "tyenv_well_formed ?env_mid"
        using tyenv_well_formed_add_var[OF wf_env rhs_wk rhs_rt] .
      moreover have "?env' = ?env_mid \<lparr> TE_ConstNames := finsert var (TE_ConstNames env) \<rparr>"
        by simp
      ultimately show ?thesis
        using tyenv_well_formed_TE_ConstNames_irrelevant by simp
    qed

    (* Apply IH to body in extended env *)
    from IH[OF state''_env' wf_env' body_typing]
    have body_sound: "sound_term_result ?env' ty (interp_term fuel ?state'' body)" .

    (* sound_term_result env' = sound_term_result env, because value_has_type
       only depends on datatypes, not TE_LocalVars/TE_GlobalVars/TE_GhostVars *)
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
  from typing obtain dtName tyArgs dtName2 metavars payloadTy where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Datatype dtName tyArgs)" and
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, metavars, payloadTy)" and
    dt_eq: "dtName = dtName2" and
    len_eq: "length tyArgs = length metavars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip metavars tyArgs)) payloadTy"
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
    those_ok: "those (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits)

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
      by simp

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
  from typing obtain dtName metavars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, metavars, payloadTy)" and
    len_eq: "length tyArgs = length metavars" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyargs_rt: "list_all (is_runtime_type env) tyArgs" and
    dt_nonghost: "dtName |\<notin>| TE_GhostDatatypes env"
    by (auto simp: Let_def split: option.splits prod.splits if_splits)

  define tySubst where "tySubst = fmap_of_list (zip metavars tyArgs)"
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
         argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo));
       retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)
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
          not_ghost: "varName |\<notin>| TE_GhostVars env" and
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
                unfolding state_matches_env_def local_vars_exist_in_state_def by blast
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
                unfolding state_matches_env_def global_vars_exist_in_state_def by blast
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
            (* It's in IS_Refs, so it must be a local *)
            from "1.prems"(1) not_ghost None Some addrPath_eq
            have local_lookup: "fmlookup (TE_LocalVars env) varName \<noteq> None"
            proof -
              (* If global, no_extra_global says it's in IS_Globals only when non-ghost.
                 But globals are in IS_Globals, not IS_Refs. We need the local var. *)
              from "1.prems"(1) have
                "local_vars_exist_in_state state env storeTyping"
                unfolding state_matches_env_def by simp
              (* We know it's in IS_Refs. For now, we derive the local_var fact. *)
              sorry
            qed
            then obtain localTy' where local_eq: "fmlookup (TE_LocalVars env) varName = Some localTy'"
              by auto
            from "1.prems"(1) local_eq not_ghost
            have local_in_state: "local_var_in_state_with_type state env storeTyping varName localTy'"
              unfolding state_matches_env_def local_vars_exist_in_state_def by blast
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
            unfolding state_matches_env_def local_vars_exist_in_state_def by blast
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
        \<comment> \<open>Extract typing facts\<close>
        from typing CoreTm_FunctionCall obtain funInfo where
          fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
          len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
          tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
          all_var: "list_all (\<lambda>(_, vor). vor = Var) (FI_TmArgs funInfo)" and
          not_impure: "\<not> FI_Impure funInfo" and
          len_tmargs: "length tmArgs = length (FI_TmArgs funInfo)" and
          ghost_ok: "list_all (is_runtime_type env) tyArgs" and
          ghost_ok2: "FI_Ghost funInfo \<noteq> Ghost"
          by (auto simp: Let_def split: option.splits if_splits)
        let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
        let ?expectedArgTypes = "map (\<lambda>(ty, _). apply_subst ?tySubst ty) (FI_TmArgs funInfo)"
        from typing CoreTm_FunctionCall fn_lookup len_tyargs tyargs_wk all_var not_impure
             len_tmargs ghost_ok ghost_ok2 have
          args_check: "list_all2 (\<lambda>tm expectedTy.
              case core_term_type env NotGhost tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
            tmArgs ?expectedArgTypes" and
          ty_eq: "ty = apply_subst ?tySubst (FI_ReturnType funInfo)"
          by (auto simp: Let_def split: if_splits)
        \<comment> \<open>Use interp_function_call_sound IH\<close>
        have IH_fc: "\<And>env' (state' :: 'w InterpState) storeTyping' fnName' argTms' funInfo' tyArgs' retTy'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                fmlookup (TE_Functions env') fnName' = Some funInfo' \<Longrightarrow>
                FI_Ghost funInfo' = NotGhost \<Longrightarrow>
                list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env' NotGhost tm of
                      None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  argTms' (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo') tyArgs')) ty)
                               (FI_TmArgs funInfo')) \<Longrightarrow>
                retTy' = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo') tyArgs')) (FI_ReturnType funInfo') \<Longrightarrow>
                sound_function_call_result env' storeTyping' retTy' (interp_function_call fuel state' fnName' argTms')"
          using Suc.IH(6) by simp
        have fn_not_ghost: "FI_Ghost funInfo = NotGhost"
          using ghost_ok2 by (cases "FI_Ghost funInfo") auto
        have fc_sound: "sound_function_call_result env storeTyping ty
                          (interp_function_call fuel state fnName tmArgs)"
          using IH_fc[OF "1.prems"(1,2) fn_lookup fn_not_ghost args_check ty_eq] by simp
        \<comment> \<open>The interpreter checks is_pure_fun then calls interp_function_call\<close>
        have pure: "is_pure_fun state fnName"
        proof -
          have "FI_Ghost funInfo = NotGhost" using ghost_ok2 by (cases "FI_Ghost funInfo") auto
          from "1.prems"(1) fn_lookup this obtain interpFun where
            if_lookup: "fmlookup (IS_Functions state) fnName = Some interpFun" and
            fi_match: "fun_info_matches_interp_fun funInfo interpFun"
            unfolding state_matches_env_def funs_exist_in_state_def
            using case_optionE by blast
          from fi_match have len_eq: "length (FI_TmArgs funInfo) = length (IF_Args interpFun)"
            and vor_match: "list_all2 (\<lambda>(_, vor1) (_, vor2). vor1 = vor2) (FI_TmArgs funInfo) (IF_Args interpFun)"
            unfolding fun_info_matches_interp_fun_def by auto
          have "\<not> list_ex (\<lambda>(_, vr). vr = Ref) (IF_Args interpFun)"
          proof -
            have "\<And>i. i < length (IF_Args interpFun) \<Longrightarrow> snd (IF_Args interpFun ! i) = Var"
            proof -
              fix i assume i_bound: "i < length (IF_Args interpFun)"
              from vor_match i_bound len_eq
              have "snd (FI_TmArgs funInfo ! i) = snd (IF_Args interpFun ! i)"
                by (auto simp: list_all2_conv_all_nth split: prod.splits)
                   (metis prod.exhaust_sel)
              moreover have "snd (FI_TmArgs funInfo ! i) = Var"
              proof -
                obtain a b where ab: "FI_TmArgs funInfo ! i = (a, b)"
                  by (cases "FI_TmArgs funInfo ! i")
                from all_var i_bound len_eq ab have "b = Var"
                  by (auto simp: list_all_length)
                thus ?thesis using ab by simp
              qed
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
          not_ghost: "varName |\<notin>| TE_GhostVars env" and
          ty_eq: "ty = varTy"
          by (auto split: option.splits if_splits)
        (* Variable is writable, so it must be a non-const local *)
        from writable CoreTm_Var have writable_var: "tyenv_var_writable env varName" by simp
        hence local_lookup: "fmlookup (TE_LocalVars env) varName \<noteq> None"
          and not_const: "varName |\<notin>| TE_ConstNames env"
          unfolding tyenv_var_writable_def by auto
        (* Variable is in IS_Locals or IS_Refs *)
        from "3.prems"(1) local_lookup not_ghost not_const
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
          unfolding state_matches_env_def local_vars_exist_in_state_def by blast
        from "3.prems"(1) not_const have not_const_state: "varName |\<notin>| IS_ConstNames state"
          unfolding state_matches_env_def const_names_match_def by simp
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
        from typing CoreTm_VariantProj obtain dtName tyArgs dtName2 metavars payloadTy where
          inner_typing: "core_term_type env NotGhost innerTm = Some (CoreTy_Datatype dtName tyArgs)" and
          ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, metavars, payloadTy)" and
          dt_eq: "dtName = dtName2" and
          len_eq: "length tyArgs = length metavars" and
          ty_eq: "ty = apply_subst (fmap_of_list (zip metavars tyArgs)) payloadTy"
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
                  argTms0 (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo0) tyArgs0)) ty)
                               (FI_TmArgs funInfo0)) \<Longrightarrow>
                retTy0 = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo0) tyArgs0)) (FI_ReturnType funInfo0) \<Longrightarrow>
                sound_function_call_result env0 storeTyping0 retTy0 (interp_function_call fuel state0 fnName0 argTms0)"
        using Suc.IH(6) by simp
      show "sound_statement_result env env' storeTyping (interp_statement (Suc fuel) state stmt)"
      proof (cases stmt)
        case (CoreStmt_VarDecl declGhost varName varOrRef varTy initTm)
        then show ?thesis proof (cases varOrRef)
          case Var
          then show ?thesis proof (cases declGhost)
            case NotGhost
            \<comment> \<open>NotGhost Var VarDecl: evaluates initTm, allocates store\<close>
            with typing CoreStmt_VarDecl Var have
              init_ty: "core_term_type env NotGhost initTm = Some varTy"
              by (auto split: if_splits)
            from IH_term[OF "4.prems"(1,2) init_ty]
            have init_sound: "sound_term_result env varTy (interp_term fuel state initTm)" .
            show ?thesis proof (cases "interp_term fuel state initTm")
              case (Inl err)
              with init_sound have "sound_error_result err" by simp
              with Inl CoreStmt_VarDecl Var NotGhost show ?thesis by simp
            next
              case (Inr initialVal)
              \<comment> \<open>Need to show state_matches_env after alloc and fmupd\<close>
              from init_sound Inr have val_typed: "value_has_type env initialVal varTy" by simp
              (* Extract env' shape from typechecking *)
              from typing CoreStmt_VarDecl Var NotGhost have
                fresh: "tyenv_lookup_var env varName = None" and
                env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                       TE_ConstNames := TE_ConstNames env \<rparr>"
                by (auto split: option.splits if_splits)
              from fresh have fresh_local: "fmlookup (TE_LocalVars env) varName = None"
                and fresh_global: "fmlookup (TE_GlobalVars env) varName = None"
                unfolding tyenv_lookup_var_def by (auto split: option.splits)
              (* varName is not ghost (it's fresh, and ghost vars are a subset of var names) *)
              from "4.prems"(2) have "TE_GhostVars env |\<subseteq>| fmdom (TE_LocalVars env) |\<union>| fmdom (TE_GlobalVars env)"
                unfolding tyenv_well_formed_def tyenv_ghost_vars_subset_def by simp
              with fresh_local fresh_global have var_not_ghost: "varName |\<notin>| TE_GhostVars env"
                by (metis fin_mono fmdom_notI funion_iff)
              (* Decompose the interpreter result *)
              obtain state' addr where alloc_eq: "(state', addr) = alloc_store state initialVal"
                by (cases "alloc_store state initialVal") auto
              let ?state'' = "state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state') \<rparr>"
              have interp_eq: "interp_statement (Suc fuel) state
                  (CoreStmt_VarDecl NotGhost varName Var varTy initTm) =
                  Inr (Continue ?state'')"
                using Inr alloc_eq by (simp add: case_prod_beta split: prod.splits)
              (* Apply state_matches_env_add_nonconst_local *)
              have new_sme: "state_matches_env ?state'' env' (storeTyping @ [varTy])"
                using state_matches_env_add_nonconst_local[OF "4.prems"(1) val_typed
                    alloc_eq refl env'_eq var_not_ghost] .
              have ext: "storeTyping_extends storeTyping (storeTyping @ [varTy])"
                using storeTyping_extends_append .
              from new_sme ext interp_eq CoreStmt_VarDecl Var NotGhost
              show ?thesis by auto
            qed
          next
            case Ghost
            \<comment> \<open>Ghost Var VarDecl: interpreter is a no-op\<close>
            (* Extract facts from typechecking *)
            from typing CoreStmt_VarDecl Var Ghost have
              fresh: "tyenv_lookup_var env varName = None" and
              env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostVars := finsert varName (TE_GhostVars env),
                                     TE_ConstNames := TE_ConstNames env \<rparr>"
              by (auto split: option.splits if_splits)
            from fresh have fresh_local: "fmlookup (TE_LocalVars env) varName = None"
              and fresh_global: "fmlookup (TE_GlobalVars env) varName = None"
              unfolding tyenv_lookup_var_def by (auto split: option.splits)
            (* The interpreter returns state unchanged *)
            have interp_eq: "interp_statement (Suc fuel) state
                (CoreStmt_VarDecl Ghost varName Var varTy initTm) = Inr (Continue state)"
              by simp
            (* From state_matches_env state env storeTyping, extract components *)
            from "4.prems"(1) have
              old_local_vars: "local_vars_exist_in_state state env storeTyping" and
              old_global_vars: "global_vars_exist_in_state state env" and
              old_no_extra_local: "no_extra_local_vars state env" and
              old_no_extra_global: "no_extra_global_vars state env" and
              old_funs: "funs_exist_in_state state env" and
              old_no_extra_funs: "no_extra_funs state env" and
              old_non_consts: "non_consts_in_locals_or_refs state env" and
              old_const_names: "const_names_match state env" and
              old_store_wt: "store_well_typed state env storeTyping"
              by (simp_all add: state_matches_env_def)
            (* varName is not in the interpreter state (locals/refs) *)
            from old_no_extra_local fresh_local have var_absent_local:
              "fmlookup (IS_Locals state) varName = None"
              "fmlookup (IS_Refs state) varName = None"
              by (simp_all add: no_extra_local_vars_def)
            (* value_has_type is the same in env and env' *)
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
            (* 1. local_vars_exist_in_state: ghost vars are excluded, others unchanged *)
            have "local_vars_exist_in_state state env' storeTyping"
              unfolding local_vars_exist_in_state_def
            proof (intro allI impI, elim conjE)
              fix name ty
              assume lk: "fmlookup (TE_LocalVars env') name = Some ty"
                and ng: "name |\<notin>| TE_GhostVars env'"
              from lk ng have lk_old: "fmlookup (TE_LocalVars env) name = Some ty"
                and ng_old: "name |\<notin>| TE_GhostVars env"
                using env'_eq by (auto split: if_splits)
              from old_local_vars lk_old ng_old
              have old_twt: "local_var_in_state_with_type state env storeTyping name ty"
                unfolding local_vars_exist_in_state_def by blast
              thus "local_var_in_state_with_type state env' storeTyping name ty"
                unfolding local_var_in_state_with_type_def
                using old_twt tap_eq
                by (auto split: option.splits)
            qed
            (* 2. global_vars_exist_in_state: unchanged *)
            moreover have "global_vars_exist_in_state state env'"
              using old_global_vars vht_eq env'_eq
              unfolding global_vars_exist_in_state_def global_var_in_state_with_type_def
              by (auto split: option.splits)
            (* 3. no_extra_local_vars: varName is ghost so allowed; others from old *)
            moreover have "no_extra_local_vars state env'"
              unfolding no_extra_local_vars_def
            proof (intro allI impI, elim disjE)
              fix name
              assume "fmlookup (TE_LocalVars env') name = None"
              hence "fmlookup (TE_LocalVars env) name = None"
                using env'_eq by (auto split: if_splits)
              with old_no_extra_local show "fmlookup (IS_Locals state) name = None \<and>
                  fmlookup (IS_Refs state) name = None"
                by (simp add: no_extra_local_vars_def)
            next
              fix name
              assume ghost_in_env': "name |\<in>| TE_GhostVars env'"
              show "fmlookup (IS_Locals state) name = None \<and>
                  fmlookup (IS_Refs state) name = None"
              proof (cases "name = varName")
                case True
                with var_absent_local show ?thesis by simp
              next
                case False
                with ghost_in_env' env'_eq have "name |\<in>| TE_GhostVars env" by simp
                with old_no_extra_local show ?thesis by (simp add: no_extra_local_vars_def)
              qed
            qed
            (* 4. no_extra_global_vars: unchanged *)
            moreover have "no_extra_global_vars state env'"
              using old_no_extra_global env'_eq
              unfolding no_extra_global_vars_def by simp
            (* 5. funs_exist_in_state: unchanged *)
            moreover have "funs_exist_in_state state env'"
              using old_funs env'_eq unfolding funs_exist_in_state_def
              by (simp add: fun_info_matches_interp_fun_def)
            (* 6. no_extra_funs: unchanged *)
            moreover have "no_extra_funs state env'"
              using old_no_extra_funs env'_eq unfolding no_extra_funs_def by simp
            (* 7. non_consts_in_locals_or_refs: ghost vars are excluded *)
            moreover have "non_consts_in_locals_or_refs state env'"
              unfolding non_consts_in_locals_or_refs_def
            proof (intro allI impI, elim conjE)
              fix name
              assume "fmlookup (TE_LocalVars env') name \<noteq> None"
                and "name |\<notin>| TE_GhostVars env'"
                and "name |\<notin>| TE_ConstNames env'"
              hence "fmlookup (TE_LocalVars env) name \<noteq> None"
                and "name |\<notin>| TE_GhostVars env"
                and "name |\<notin>| TE_ConstNames env"
                using env'_eq by (auto split: if_splits)
              with old_non_consts show "fmlookup (IS_Locals state) name \<noteq> None \<or>
                  fmlookup (IS_Refs state) name \<noteq> None"
                by (simp add: non_consts_in_locals_or_refs_def)
            qed
            (* 8. const_names_match: TE_ConstNames unchanged *)
            moreover have "const_names_match state env'"
              using old_const_names env'_eq by (simp add: const_names_match_def)
            (* 9. store_well_typed: store and storeTyping unchanged, env change preserves value_has_type *)
            moreover have "store_well_typed state env' storeTyping"
              using old_store_wt vht_eq
              unfolding store_well_typed_def by simp
            ultimately have "state_matches_env state env' storeTyping"
              by (simp add: state_matches_env_def)
            with CoreStmt_VarDecl Var Ghost show ?thesis
              using storeTyping_extends_refl by auto
          qed
        next
          case Ref
          \<comment> \<open>Ref VarDecl: typechecking is undefined\<close>
          with typing CoreStmt_VarDecl show ?thesis sorry
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
            rhs_ty: "core_term_type env NotGhost rhsTm = Some lhsTy" and
            env'_eq: "env' = env"
            by (auto split: if_splits option.splits)
          from IH_lvalue[OF "4.prems"(1,2) conjI[OF lhs_writable lhs_ty]]
          have lhs_sound: "sound_lvalue_result state env storeTyping lhsTy
              (interp_writable_lvalue fuel state lhsTm)" .
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
              \<comment> \<open>Extract typing facts about the function call.\<close>
              from rhs_ty rhsTm_eq obtain funInfo where
                fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
                len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
                tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
                tyargs_rt: "list_all (is_runtime_type env) tyArgs" and
                not_ghost_fn: "FI_Ghost funInfo \<noteq> Ghost" and
                all_var: "list_all (\<lambda>(_, vor). vor = Var) (FI_TmArgs funInfo)" and
                not_impure: "\<not> FI_Impure funInfo" and
                len_tmargs: "length argTms = length (FI_TmArgs funInfo)"
                by (auto simp: Let_def split: option.splits if_splits)
              let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
              let ?expectedArgTypes = "map (\<lambda>(ty, _). apply_subst ?tySubst ty) (FI_TmArgs funInfo)"
              from rhs_ty rhsTm_eq fn_lookup len_tyargs tyargs_wk all_var not_impure
                   len_tmargs tyargs_rt not_ghost_fn have
                args_check: "list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env NotGhost tm of None \<Rightarrow> False
                    | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  argTms ?expectedArgTypes" and
                fn_ty_eq: "lhsTy = apply_subst ?tySubst (FI_ReturnType funInfo)"
                by (auto simp: Let_def split: if_splits)
              \<comment> \<open>Apply IH_fc to get sound_function_call_result.\<close>
              have fn_not_ghost: "FI_Ghost funInfo = NotGhost"
                using not_ghost_fn by (cases "FI_Ghost funInfo") auto
              from IH_fc[OF "4.prems"(1,2) fn_lookup fn_not_ghost args_check fn_ty_eq]
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
          \<comment> \<open>Use env itself as env_mid (reflexivity of tyenv_subset).\<close>
          have "sound_statement_result env env' storeTyping (Inr (Return state val))"
            unfolding env'_eq using vht "4.prems"(1)
            by (auto intro!: exI[of _ env] exI[of _ storeTyping] tyenv_subset_refl
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
                  sub1: "tyenv_subset env_mid env_mid2" and
                  sub2: "tyenv_subset env_mid2 env'" and
                  sme2: "state_matches_env state'' env_mid2 storeTyping2" and
                  ext2: "storeTyping_extends storeTyping_mid storeTyping2"
                  by auto
                from storeTyping_extends_trans[OF ext1 ext2]
                have ext_full: "storeTyping_extends storeTyping storeTyping2" .
                from core_statement_type_monotone[OF stmt_ty]
                have sub_env_envmid: "tyenv_subset env env_mid" .
                from tyenv_subset_trans[OF this sub1]
                have sub_env_mid2: "tyenv_subset env env_mid2" .
                \<comment> \<open>Transfer value_has_type from env_mid to env\<close>
                from sub_env_envmid
                have "TE_DataCtors env = TE_DataCtors env_mid"
                  "TE_Datatypes env = TE_Datatypes env_mid"
                  "TE_TypeVars env = TE_TypeVars env_mid"
                  "TE_GhostDatatypes env = TE_GhostDatatypes env_mid"
                  "TE_RuntimeTypeVars env = TE_RuntimeTypeVars env_mid"
                  "TE_ReturnType env = TE_ReturnType env_mid"
                  unfolding tyenv_subset_def by simp_all
                hence vht_env: "value_has_type env retVal2 (TE_ReturnType env)"
                  using vht value_has_type_cong_env by metis
                from \<open>interp_statement_list fuel state' stmts0 = Inr result2\<close> Return
                have interp_rest_eq: "interp_statement_list fuel state' stmts0 = Inr (Return state'' retVal2)"
                  by simp
                from vht_env sub_env_mid2 sub2 sme2 ext_full
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
              sub1: "tyenv_subset env env_mid2" and
              sub2: "tyenv_subset env_mid2 env_mid" and
              sme2: "state_matches_env state' env_mid2 storeTyping2" and
              ext: "storeTyping_extends storeTyping storeTyping2"
              by auto
            from core_statement_list_type_monotone[OF rest_ty]
            have "tyenv_subset env_mid env'" .
            from tyenv_subset_trans[OF sub2 this]
            have "tyenv_subset env_mid2 env'" .
            with vht sub1 sme2 ext
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
        using "6.prems"(5) state_matches_env_def by auto
      obtain f where
        if_lookup: "fmlookup (IS_Functions state) fnName = Some f" and
        fi_match: "fun_info_matches_interp_fun funInfo f"
        unfolding funs_exist_in_state_def
        by (metis "6.prems"(1,2) case_optionE fes funs_exist_in_state_def)

      \<comment> \<open>Basic shape of the InterpFun matches the FunInfo. From fun_info_matches_interp_fun.\<close>
      from fi_match have len_args: "length (IF_Args f) = length (FI_TmArgs funInfo)"
        unfolding fun_info_matches_interp_fun_def by simp
      from fi_match have var_ref_match:
        "list_all2 (\<lambda>(_, vor1) (_, vor2). vor1 = vor2) (FI_TmArgs funInfo) (IF_Args f)"
        unfolding fun_info_matches_interp_fun_def by simp

      show "sound_function_call_result env storeTyping retTy
              (interp_function_call (Suc fuel) state fnName argTms)"
      proof (cases "IF_Body f")
        case (Inl bodyStmts)
        \<comment> \<open>Core-body case.\<close>

        (* The body statement-list is well-typed, in some environment where:

          - FE_TermVars contains all global constants that were defined when the function
            was defined, as well as the formal arguments. 
          - TE_GhostVars is set appropriately. All term args are considered non-ghost;
            any globals inherit their ghost-ness from the parent environment.
          - TE_ConstNames is set appropriately.
          - TE_TypeVars must be the function's own type variable set. All are runtime.
          - TE_ReturnType must be the function's return type.
          - TE_FunctionGhost is NotGhost.
          - TE_Functions, TE_Datatypes, TE_DataCtors, etc, should inherit from our
            environment, or be a subset (as some types that exist now might not have
            existed when the function was defined).

        *)
            

        show ?thesis
          sorry

      next
        case (Inr externFun)
        \<comment> \<open>Extern-function case. Deferred for now.\<close>
        show ?thesis
          sorry
      qed
    qed
  }
qed


end

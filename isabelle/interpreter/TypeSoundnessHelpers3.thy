theory TypeSoundnessHelpers3
  imports TypeSoundnessHelpers2 "../core/TypeSubstTerm"
begin

(*-----------------------------------------------------------------------------*)
(* Type soundness for terms *)
(*-----------------------------------------------------------------------------*)

(* Applying a subst to the operand type of a valid CoreTm_Unop is a no-op
   (in either typing mode). *)
lemma unop_operand_apply_subst_any:
  assumes "core_term_type env ghost (CoreTm_Unop unop operand) = Some ty"
      and "core_term_type env ghost operand = Some operandTy"
  shows "apply_subst subst operandTy = operandTy"
proof -
  from assms have "operandTy = CoreTy_Bool \<or> is_signed_numeric_type operandTy \<or>
                   is_finite_integer_type operandTy"
    by (cases unop) (auto split: option.splits if_splits)
  then show ?thesis
    using is_signed_numeric_type_apply_subst is_finite_integer_type_apply_subst by auto
qed

(* Applying a subst to the operand types of a valid CoreTm_Binop is a no-op,
   except for equality and inequality, which in Ghost mode compare values of
   any type. *)
lemma binop_operand_apply_subst_ne:
  assumes typing: "core_term_type env ghost (CoreTm_Binop op lhs rhs) = Some ty"
      and lhs_typing: "core_term_type env ghost lhs = Some lhsTy"
      and rhs_typing: "core_term_type env ghost rhs = Some rhsTy"
      and ne: "\<not> is_eq_neq_binop op"
  shows "apply_subst subst lhsTy = lhsTy"
    and "apply_subst subst rhsTy = rhsTy"
proof -
  have fin_num: "is_finite_integer_type t \<Longrightarrow> is_numeric_type t" for t
    by (cases t) auto
  have int_num: "is_integer_type t \<Longrightarrow> is_numeric_type t" for t
    by (cases t) auto
  from typing lhs_typing rhs_typing ne
  have "(lhsTy = CoreTy_Bool \<or> is_numeric_type lhsTy)
        \<and> (rhsTy = CoreTy_Bool \<or> is_numeric_type rhsTy)"
    by (auto split: if_splits dest: fin_num int_num)
  then show "apply_subst subst lhsTy = lhsTy" and "apply_subst subst rhsTy = rhsTy"
    using is_numeric_type_apply_subst by auto
qed

(* Value-level soundness of cast_value: a successful cast of a value well-typed
   at the (substituted) source type yields a value well-typed at the
   (substituted) target type, provided the static cast condition (cast_ok)
   holds. Integer case: the value is a CV_FiniteInt or a CV_Int, and the target
   is a finite-int type (where cast_value checks the range) or int. Array
   case: the value is unchanged, the element type is shared, and the runtime
   size check is exactly the sizes_match_dims conjunct of value_has_type at
   the target. *)
lemma cast_value_sound:
  assumes cast: "cast_value tgtTy v = Inr v'"
      and co: "cast_ok env srcTy tgtTy"
      and v_typed: "value_has_type env v (apply_subst subst srcTy)"
  shows "value_has_type env v' (apply_subst subst tgtTy)"
using co proof (cases rule: cast_ok_cases)
  case Int
  have "is_integer_type (apply_subst subst srcTy)"
    using Int(1) by (simp add: is_integer_type_apply_subst)
  then consider (Fin) sign bits i where "v = CV_FiniteInt sign bits i"
              | (MInt) i where "v = CV_Int i"
    using v_typed by (cases v; cases "apply_subst subst srcTy"; simp)
  then show ?thesis
  proof cases
    case (Fin sign bits i)
    from cast Fin Int(2) show ?thesis by (cases tgtTy) (auto split: if_splits)
  next
    case (MInt i)
    from cast MInt Int(2) show ?thesis by (cases tgtTy) (auto split: if_splits)
  qed
next
  case (Array elemTy dims dims')
  have src_subst: "apply_subst subst srcTy = CoreTy_Array (apply_subst subst elemTy) dims"
    using Array(1) by simp
  from value_has_type_Array[OF v_typed[unfolded src_subst]]
  obtain sizes elems where v_eq: "v = CV_Array sizes elems" by blast
  from cast Array(2) v_eq have
    v'_eq: "v' = CV_Array sizes elems" and
    smd: "sizes_match_dims sizes dims'"
    by (auto split: if_splits)
  have dims'_wk: "array_dims_well_kinded dims'"
    using Array(2,4) by simp
  show ?thesis
    using v_typed src_subst v_eq v'_eq smd dims'_wk Array(2) by simp
qed

(* A failed cast_value on a well-typed value is a RuntimeError, never a
   TypeError: an integer value (a CV_FiniteInt or a CV_Int) meets an integer
   target, where the only failure is overflow at a finite-int target; and an
   array value meets an array target, where the only failure is the size
   check. *)
lemma cast_value_error_is_runtime:
  assumes cast: "cast_value tgtTy v = Inl err"
      and co: "cast_ok env srcTy tgtTy"
      and v_typed: "value_has_type env v (apply_subst subst srcTy)"
  shows "err = RuntimeError"
using co proof (cases rule: cast_ok_cases)
  case Int
  have "is_integer_type (apply_subst subst srcTy)"
    using Int(1) by (simp add: is_integer_type_apply_subst)
  then consider (Fin) sign bits i where "v = CV_FiniteInt sign bits i"
              | (MInt) i where "v = CV_Int i"
    using v_typed by (cases v; cases "apply_subst subst srcTy"; simp)
  then show ?thesis
  proof cases
    case (Fin sign bits i)
    from cast Fin Int(2) show ?thesis by (cases tgtTy) (auto split: if_splits)
  next
    case (MInt i)
    from cast MInt Int(2) show ?thesis by (cases tgtTy) (auto split: if_splits)
  qed
next
  case (Array elemTy dims dims')
  have src_subst: "apply_subst subst srcTy = CoreTy_Array (apply_subst subst elemTy) dims"
    using Array(1) by simp
  from value_has_type_Array[OF v_typed[unfolded src_subst]]
  obtain sizes elems where v_eq: "v = CV_Array sizes elems" by blast
  from cast Array(2) v_eq show ?thesis by (auto split: if_splits)
qed

(* Type soundness for Cast *)
lemma type_soundness_cast:
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env Ghost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term d fuel state tm')"
    and typing: "core_term_type env Ghost (CoreTm_Cast target_ty operand) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_Cast target_ty operand))"
proof -
  (* Extract facts from typing *)
  from typing obtain operand_ty where
    operand_typing: "core_term_type env Ghost operand = Some operand_ty"
    and co: "cast_ok env operand_ty target_ty"
    and ty_eq: "ty = target_ty"
    by (auto split: option.splits if_splits)

  (* Apply IH to operand *)
  from IH[OF operand_typing]
  have operand_sound: "sound_term_result state env operand_ty (interp_term d fuel state operand)"
    by simp

  (* Case split on operand result *)
  show ?thesis
  proof (cases "interp_term d fuel state operand")
    case (Inr operand_val)
    (* Operand succeeded - it is well-typed at the substituted operand type *)
    from operand_sound Inr
    have operand_typed: "value_has_type env operand_val (apply_subst (IS_TyArgs state) operand_ty)"
      by simp
    have interp_eq: "interp_term d (Suc fuel) state (CoreTm_Cast target_ty operand)
                       = cast_value target_ty operand_val"
      using Inr by simp
    (* Case split on whether the cast succeeds *)
    show ?thesis
    proof (cases "cast_value target_ty operand_val")
      case (Inl err)
      have "err = RuntimeError"
        by (rule cast_value_error_is_runtime[OF Inl co operand_typed])
      thus ?thesis using interp_eq Inl by simp
    next
      case (Inr castVal)
      have "value_has_type env castVal (apply_subst (IS_TyArgs state) target_ty)"
        by (rule cast_value_sound[OF Inr co operand_typed])
      thus ?thesis using interp_eq Inr ty_eq by simp
    qed
  next
    case (Inl err)
    then show ?thesis using operand_sound by auto
  qed
qed

(* Soundness of eval_unop, phrased purely over values: applying a unary
   operator to a well-typed operand value either succeeds with a value of the
   result type, or fails with a sound error (never TypeError). The state is
   arbitrary: a unop's result type is always Bool or a numeric type, on
   which the state's IS_TyArgs substitution is a no-op. Shared by
   type_soundness_unop below and ConstFoldCorrect's eval_unop_sound_values. *)
lemma eval_unop_sound:
  assumes typing: "core_term_type env ghost (CoreTm_Unop unop operand) = Some ty"
    and operand_typing: "core_term_type env ghost operand = Some operandTy"
    and operand_typed: "value_has_type env operandVal operandTy"
  shows "sound_term_result (state :: 'w InterpState) env ty (eval_unop unop operandVal)"
proof (cases unop)
  case CoreUnop_Negate
  (* Extract facts from typing *)
  from typing operand_typing CoreUnop_Negate have
    ty_eq: "operandTy = ty"
    and signed_numeric: "is_signed_numeric_type ty"
    by (auto split: option.splits if_splits)
  from operand_typed ty_eq have operand_ty_typed: "value_has_type env operandVal ty" by simp

  (* Since ty is signed_numeric, it is CoreTy_FiniteInt Signed bits for some
     bits, or int, or real *)
  from signed_numeric consider
      (Fin) bits where "ty = CoreTy_FiniteInt Signed bits"
    | (MInt) "ty = CoreTy_MathInt"
    | (MReal) "ty = CoreTy_MathReal"
    using is_signed_numeric_type.elims(2) by blast
  then show ?thesis
  proof cases
    case (Fin bits)
    note ty_def = Fin

    (* So the value must be CV_FiniteInt Signed bits i *)
    from operand_ty_typed ty_def obtain i where
      operand_val_def: "operandVal = CV_FiniteInt Signed bits i"
      using value_has_type_FiniteInt by blast

    (* Now evaluate the negation *)
    show ?thesis
    proof (cases "int_fits Signed bits (-i)")
      case True
      (* Negation succeeds *)
      have "eval_unop unop operandVal = Inr (CV_FiniteInt Signed bits (-i))"
        using operand_val_def True CoreUnop_Negate by simp
      with ty_def True show ?thesis by simp
    next
      case False
      (* Negation overflows - RuntimeError *)
      have "eval_unop unop operandVal = Inl RuntimeError"
        using operand_val_def False CoreUnop_Negate by simp
      then show ?thesis by simp
    qed
  next
    case MInt
    (* Negation of an int always succeeds *)
    from operand_ty_typed MInt obtain i where "operandVal = CV_Int i"
      using value_has_type_MathInt by blast
    then have "eval_unop unop operandVal = Inr (CV_Int (-i))"
      using CoreUnop_Negate by simp
    with MInt show ?thesis by simp
  next
    case MReal
    (* Negation of a real always succeeds *)
    from operand_ty_typed MReal obtain r where "operandVal = CV_Real r"
      using value_has_type_MathReal by blast
    then have "eval_unop unop operandVal = Inr (CV_Real (-r))"
      using CoreUnop_Negate by simp
    with MReal show ?thesis by simp
  qed
next
  case CoreUnop_Complement
  (* Extract facts from typing *)
  from typing operand_typing CoreUnop_Complement have
    ty_eq: "operandTy = ty"
    and finite_int: "is_finite_integer_type ty"
    by (auto split: option.splits if_splits)
  from operand_typed ty_eq have operand_ty_typed: "value_has_type env operandVal ty" by simp

  (* is_finite_integer_type ty => ty = CoreTy_FiniteInt sign bits *)
  from finite_int obtain sign bits where
    ty_def: "ty = CoreTy_FiniteInt sign bits"
    by (cases ty) auto

  (* So the value must be CV_FiniteInt sign bits i *)
  from operand_ty_typed ty_def obtain i where
    operand_val_def: "operandVal = CV_FiniteInt sign bits i"
    and i_fits: "int_fits sign bits i"
    using value_has_type_FiniteInt by blast

  (* Complement always succeeds *)
  have "eval_unop unop operandVal = Inr (CV_FiniteInt sign bits (int_complement sign bits i))"
    using operand_val_def CoreUnop_Complement by simp
  with ty_def int_complement_fits[OF i_fits] show ?thesis by simp
next
  case CoreUnop_Not
  (* Extract facts from typing *)
  from typing operand_typing CoreUnop_Not have
    operandTy_bool: "operandTy = CoreTy_Bool"
    and ty_eq: "ty = CoreTy_Bool"
    by (auto split: option.splits if_splits)

  (* Value must be CV_Bool b *)
  from operand_typed operandTy_bool obtain b where
    operand_val_def: "operandVal = CV_Bool b"
    using value_has_type_Bool by blast

  (* Not always succeeds *)
  have "eval_unop unop operandVal = Inr (CV_Bool (\<not>b))"
    using operand_val_def CoreUnop_Not by simp
  with ty_eq show ?thesis by simp
qed

(* Type soundness for unary operators *)
lemma type_soundness_unop:
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env Ghost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term d fuel state tm')"
    and typing: "core_term_type env Ghost (CoreTm_Unop unop operand) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_Unop unop operand))"
proof -
  (* The operand typechecks *)
  from typing obtain operandTy where
    operand_typing: "core_term_type env Ghost operand = Some operandTy"
    by (auto split: option.splits)

  (* Apply IH to operand *)
  from IH[OF operand_typing]
  have operand_sound: "sound_term_result state env operandTy (interp_term d fuel state operand)" .

  show ?thesis
  proof (cases "interp_term d fuel state operand")
    case (Inl err)
    (* Operand failed - propagate the sound error *)
    then show ?thesis using operand_sound by auto
  next
    case (Inr operandVal)
    (* Operand succeeded; its type is subst-invariant, so the value has
       operandTy itself *)
    from operand_sound Inr unop_operand_apply_subst_any[OF typing operand_typing]
    have operand_typed: "value_has_type env operandVal operandTy" by simp

    (* Defer to eval_unop soundness *)
    have "interp_term d (Suc fuel) state (CoreTm_Unop unop operand) = eval_unop unop operandVal"
      using Inr by simp
    with eval_unop_sound[OF typing operand_typing operand_typed]
    show ?thesis by simp
  qed
qed

(* Helper: generic_finite_int_binop preserves types when operation fits *)
lemma generic_finite_int_binop_sound:
  assumes "value_has_type env v1 (CoreTy_FiniteInt sign bits)"
      and "value_has_type env v2 (CoreTy_FiniteInt sign bits)"
  shows "sound_term_result state env (CoreTy_FiniteInt sign bits) (generic_finite_int_binop f v1 v2)"
proof -
  from assms obtain i1 i2 where
    v1_def: "v1 = CV_FiniteInt sign bits i1" and i1_fits: "int_fits sign bits i1" and
    v2_def: "v2 = CV_FiniteInt sign bits i2" and i2_fits: "int_fits sign bits i2"
    using value_has_type_FiniteInt by blast
  show ?thesis
  proof (cases "int_fits sign bits (f i1 i2)")
    case True
    then have "generic_finite_int_binop f v1 v2 = Inr (CV_FiniteInt sign bits (f i1 i2))"
      using v1_def v2_def by simp
    then show ?thesis using True by simp
  next
    case False
    then have "generic_finite_int_binop f v1 v2 = Inl RuntimeError"
      using v1_def v2_def by simp
    then show ?thesis by simp
  qed
qed

(* Helper: generic_finite_int_cmp_binop produces bool *)
lemma generic_finite_int_cmp_binop_sound:
  assumes "value_has_type env v1 (CoreTy_FiniteInt sign bits)"
      and "value_has_type env v2 (CoreTy_FiniteInt sign bits)"
  shows "sound_term_result state env CoreTy_Bool (generic_finite_int_cmp_binop f v1 v2)"
proof -
  from assms obtain i1 i2 where
    v1_def: "v1 = CV_FiniteInt sign bits i1" and
    v2_def: "v2 = CV_FiniteInt sign bits i2"
    using value_has_type_FiniteInt by blast
  have "generic_finite_int_cmp_binop f v1 v2 = Inr (CV_Bool (f i1 i2))"
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

(* Soundness of eval_binop when the operands have type int or real. Every
   operator that is typed at int or real succeeds, except division and modulo
   by zero. *)
lemma eval_binop_sound_math:
  assumes typing: "core_term_type env ghost (CoreTm_Binop op lhs rhs) = Some ty"
    and lhs_typing: "core_term_type env ghost lhs = Some lhsTy"
    and rhs_typing: "core_term_type env ghost rhs = Some rhsTy"
    and lhs_typed: "value_has_type env lhsVal lhsTy"
    and rhs_typed: "value_has_type env rhsVal rhsTy"
    and math: "lhsTy = CoreTy_MathInt \<or> lhsTy = CoreTy_MathReal"
  shows "sound_term_result (state :: 'w InterpState) env ty (eval_binop op lhsVal rhsVal)"
proof -
  (* Every operator typed at int or real takes two operands of the same type *)
  from typing lhs_typing rhs_typing math have types_eq: "rhsTy = lhsTy"
    by (auto split: if_splits)
  from math show ?thesis
  proof
    assume lhs_mi: "lhsTy = CoreTy_MathInt"
    with types_eq have rhs_mi: "rhsTy = CoreTy_MathInt" by simp
    from lhs_typed lhs_mi obtain i1 where lhs_val: "lhsVal = CV_Int i1"
      using value_has_type_MathInt by blast
    from rhs_typed rhs_mi obtain i2 where rhs_val: "rhsVal = CV_Int i2"
      using value_has_type_MathInt by blast
    from typing lhs_typing rhs_typing lhs_mi rhs_mi lhs_val rhs_val show ?thesis
      by (cases op) (auto split: if_splits)
  next
    assume lhs_mr: "lhsTy = CoreTy_MathReal"
    with types_eq have rhs_mr: "rhsTy = CoreTy_MathReal" by simp
    from lhs_typed lhs_mr obtain r1 where lhs_val: "lhsVal = CV_Real r1"
      using value_has_type_MathReal by blast
    from rhs_typed rhs_mr obtain r2 where rhs_val: "rhsVal = CV_Real r2"
      using value_has_type_MathReal by blast
    from typing lhs_typing rhs_typing lhs_mr rhs_mr lhs_val rhs_val show ?thesis
      by (cases op) (auto split: if_splits)
  qed
qed

(* Soundness of eval_binop when the operands do not have type int or real. *)
lemma eval_binop_sound_finite:
  assumes typing: "core_term_type env ghost (CoreTm_Binop op lhs rhs) = Some ty"
    and lhs_typing: "core_term_type env ghost lhs = Some lhsTy"
    and rhs_typing: "core_term_type env ghost rhs = Some rhsTy"
    and lhs_typed: "value_has_type env lhsVal lhsTy"
    and rhs_typed: "value_has_type env rhsVal rhsTy"
    and lhsTy_rt: "lhsTy \<noteq> CoreTy_MathInt \<and> lhsTy \<noteq> CoreTy_MathReal"
  shows "sound_term_result (state :: 'w InterpState) env ty (eval_binop op lhsVal rhsVal)"
proof -

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
                          then if lhsTy = rhsTy \<and> (ghost = Ghost \<or> lhsTy = CoreTy_Bool \<or> is_numeric_type lhsTy)
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
    from lhs_int rhs_int obtain i1 i2 where
      lhs_fin: "lhsVal = CV_FiniteInt sign bits i1" and
      rhs_fin: "rhsVal = CV_FiniteInt sign bits i2"
      using value_has_type_FiniteInt by blast

    show ?thesis
    proof (cases op)
      case CoreBinop_Add
      have "eval_binop op lhsVal rhsVal = generic_finite_int_binop (\<lambda>x y. x + y) lhsVal rhsVal"
        using CoreBinop_Add lhs_fin rhs_fin by simp
      with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
      show ?thesis by simp
    next
      case CoreBinop_Subtract
      have "eval_binop op lhsVal rhsVal = generic_finite_int_binop (\<lambda>x y. x - y) lhsVal rhsVal"
        using CoreBinop_Subtract lhs_fin rhs_fin by simp
      with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
      show ?thesis by simp
    next
      case CoreBinop_Multiply
      have "eval_binop op lhsVal rhsVal = generic_finite_int_binop (\<lambda>x y. x * y) lhsVal rhsVal"
        using CoreBinop_Multiply lhs_fin rhs_fin by simp
      with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
      show ?thesis by simp
    next
      case CoreBinop_Divide
      show ?thesis
      proof (cases "is_zero rhsVal")
        case True
        then have "eval_binop op lhsVal rhsVal = Inl RuntimeError"
          using CoreBinop_Divide by simp
        then show ?thesis by simp
      next
        case False
        then have "eval_binop op lhsVal rhsVal = generic_finite_int_binop tdiv lhsVal rhsVal"
          using CoreBinop_Divide lhs_fin rhs_fin by simp
        with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
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
      from lhs_int rhs_int obtain i1 i2 where
        lhs_fin: "lhsVal = CV_FiniteInt sign bits i1" and
        rhs_fin: "rhsVal = CV_FiniteInt sign bits i2"
        using value_has_type_FiniteInt by blast

      from True have op_eq: "op = CoreBinop_Modulo" by (cases op) auto
      show ?thesis
      proof (cases "is_zero rhsVal")
        case True
        then have "eval_binop op lhsVal rhsVal = Inl RuntimeError"
          using op_eq by simp
        then show ?thesis by simp
      next
        case False
        then have "eval_binop op lhsVal rhsVal = generic_finite_int_binop tmod lhsVal rhsVal"
          using op_eq lhs_fin rhs_fin by simp
        with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
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
          have "eval_binop op lhsVal rhsVal = generic_finite_int_binop (\<lambda>x y. and x y) lhsVal rhsVal"
            using CoreBinop_BitAnd by simp
          with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
          show ?thesis by simp
        next
          case CoreBinop_BitOr
          have "eval_binop op lhsVal rhsVal = generic_finite_int_binop (\<lambda>x y. or x y) lhsVal rhsVal"
            using CoreBinop_BitOr by simp
          with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
          show ?thesis by simp
        next
          case CoreBinop_BitXor
          have "eval_binop op lhsVal rhsVal = generic_finite_int_binop (\<lambda>x y. xor x y) lhsVal rhsVal"
            using CoreBinop_BitXor by simp
          with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
          show ?thesis by simp
        next
          case CoreBinop_ShiftLeft
          show ?thesis
          proof (cases "is_valid_shift lhsVal rhsVal")
            case False
            then have "eval_binop op lhsVal rhsVal = Inl RuntimeError"
              using CoreBinop_ShiftLeft by simp
            then show ?thesis by simp
          next
            case True
            then have "eval_binop op lhsVal rhsVal = generic_finite_int_binop (\<lambda>x y. push_bit (nat y) x) lhsVal rhsVal"
              using CoreBinop_ShiftLeft by simp
            with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
            show ?thesis by simp
          qed
        next
          case CoreBinop_ShiftRight
          show ?thesis
          proof (cases "is_valid_shift lhsVal rhsVal")
            case False
            then have "eval_binop op lhsVal rhsVal = Inl RuntimeError"
              using CoreBinop_ShiftRight by simp
            then show ?thesis by simp
          next
            case True
            then have "eval_binop op lhsVal rhsVal = generic_finite_int_binop (\<lambda>x y. drop_bit (nat y) x) lhsVal rhsVal"
              using CoreBinop_ShiftRight by simp
            with ty_eq lhsTy_def generic_finite_int_binop_sound[OF lhs_int rhs_int]
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
          from lhs_int rhs_int obtain i1 i2 where
            lhs_fin: "lhsVal = CV_FiniteInt sign bits i1" and
            rhs_fin: "rhsVal = CV_FiniteInt sign bits i2"
            using value_has_type_FiniteInt by blast

          show ?thesis
          proof (cases op)
            case CoreBinop_Less
            have "eval_binop op lhsVal rhsVal = generic_finite_int_cmp_binop (\<lambda>x y. x < y) lhsVal rhsVal"
              using CoreBinop_Less lhs_fin rhs_fin by simp
            with ty_eq generic_finite_int_cmp_binop_sound[OF lhs_int rhs_int]
            show ?thesis by simp
          next
            case CoreBinop_LessEqual
            have "eval_binop op lhsVal rhsVal = generic_finite_int_cmp_binop (\<lambda>x y. x \<le> y) lhsVal rhsVal"
              using CoreBinop_LessEqual lhs_fin rhs_fin by simp
            with ty_eq generic_finite_int_cmp_binop_sound[OF lhs_int rhs_int]
            show ?thesis by simp
          next
            case CoreBinop_Greater
            have "eval_binop op lhsVal rhsVal = generic_finite_int_cmp_binop (\<lambda>x y. x > y) lhsVal rhsVal"
              using CoreBinop_Greater lhs_fin rhs_fin by simp
            with ty_eq generic_finite_int_cmp_binop_sound[OF lhs_int rhs_int]
            show ?thesis by simp
          next
            case CoreBinop_GreaterEqual
            have "eval_binop op lhsVal rhsVal = generic_finite_int_cmp_binop (\<lambda>x y. x \<ge> y) lhsVal rhsVal"
              using CoreBinop_GreaterEqual lhs_fin rhs_fin by simp
            with ty_eq generic_finite_int_cmp_binop_sound[OF lhs_int rhs_int]
            show ?thesis by simp
          qed (use True in auto)
        next
          case False
          note not_ordering = False
          show ?thesis
          proof (cases "is_eq_neq_binop op")
            case True
            (* Equality/inequality: any two values compare, giving a bool *)
            from typing' not_arith not_modulo not_bitwise_shift not_ordering True have
              ty_eq: "ty = CoreTy_Bool"
              by (auto split: if_splits)
            from True have op_cases: "op = CoreBinop_Equal \<or> op = CoreBinop_NotEqual"
              by (cases op) auto
            from op_cases show ?thesis using ty_eq by auto
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
              with ty_eq generic_bool_binop_sound[OF lhs_bool_typed rhs_bool_typed]
              show ?thesis by simp
            next
              case CoreBinop_Or
              have "eval_binop op lhsVal rhsVal = generic_bool_binop (\<lambda>x y. x \<or> y) lhsVal rhsVal"
                using CoreBinop_Or by simp
              with ty_eq generic_bool_binop_sound[OF lhs_bool_typed rhs_bool_typed]
              show ?thesis by simp
            next
              case CoreBinop_Implies
              have "eval_binop op lhsVal rhsVal = generic_bool_binop (\<lambda>x y. x \<longrightarrow> y) lhsVal rhsVal"
                using CoreBinop_Implies by simp
              with ty_eq generic_bool_binop_sound[OF lhs_bool_typed rhs_bool_typed]
              show ?thesis by simp
            qed (use logical in auto)
          qed
        qed
      qed
    qed
  qed
qed

(* Soundness of eval_binop, phrased purely over values: applying a binary
   operator to well-typed operand values either succeeds with a value of the
   result type, or fails with a sound error (never TypeError). The state is
   arbitrary: a binop's result type is always Bool or a numeric type, on
   which the state's IS_TyArgs substitution is a no-op. Shared by
   type_soundness_binop below and ConstFoldCorrect's eval_binop_sound_values.

   Equality and inequality compare values of any type and always give a
   boolean, so for them nothing is needed about the operand values. *)
lemma eval_binop_sound:
  assumes typing: "core_term_type env ghost (CoreTm_Binop op lhs rhs) = Some ty"
    and lhs_typing: "core_term_type env ghost lhs = Some lhsTy"
    and rhs_typing: "core_term_type env ghost rhs = Some rhsTy"
    and lhs_typed: "\<not> is_eq_neq_binop op \<Longrightarrow> value_has_type env lhsVal lhsTy"
    and rhs_typed: "\<not> is_eq_neq_binop op \<Longrightarrow> value_has_type env rhsVal rhsTy"
  shows "sound_term_result (state :: 'w InterpState) env ty (eval_binop op lhsVal rhsVal)"
proof (cases "is_eq_neq_binop op")
  case True
  then have op_cases: "op = CoreBinop_Equal \<or> op = CoreBinop_NotEqual"
    by (cases op) auto
  from typing lhs_typing rhs_typing True have ty_eq: "ty = CoreTy_Bool"
    by (cases op) (auto split: if_splits)
  from op_cases show ?thesis using ty_eq by auto
next
  case False
  note lhs_typed' = lhs_typed[OF False]
  note rhs_typed' = rhs_typed[OF False]
  show ?thesis
  proof (cases "lhsTy = CoreTy_MathInt \<or> lhsTy = CoreTy_MathReal")
    case True
    show ?thesis
      by (rule eval_binop_sound_math[OF typing lhs_typing rhs_typing lhs_typed' rhs_typed' True])
  next
    case False
    then have not_math: "lhsTy \<noteq> CoreTy_MathInt \<and> lhsTy \<noteq> CoreTy_MathReal" by simp
    show ?thesis
      by (rule eval_binop_sound_finite[OF typing lhs_typing rhs_typing lhs_typed' rhs_typed' not_math])
  qed
qed

(* Facts about short-circuit evaluation of logical binops *)
lemma short_circuit_bool:
  "short_circuit op v = Some v' \<Longrightarrow> \<exists>b. v' = CV_Bool b"
  by (auto elim!: short_circuit.elims split: if_splits)

lemma short_circuit_type_bool:
  assumes "short_circuit op v = Some v'"
    and "core_term_type env ghost (CoreTm_Binop op lhs rhs) = Some ty"
  shows "ty = CoreTy_Bool"
  using assms by (auto elim!: short_circuit.elims split: option.splits prod.splits if_splits)

(* Type soundness for binary operators *)
lemma type_soundness_binop:
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env Ghost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term d fuel state tm')"
    and typing: "core_term_type env Ghost (CoreTm_Binop op lhs rhs) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_Binop op lhs rhs))"
proof -
  (* Extract facts from typing *)
  from typing obtain lhsTy rhsTy where
    lhs_typing: "core_term_type env Ghost lhs = Some lhsTy" and
    rhs_typing: "core_term_type env Ghost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)

  (* Apply IH to operands *)
  from IH[OF lhs_typing] have lhs_sound: "sound_term_result state env lhsTy (interp_term d fuel state lhs)" .
  from IH[OF rhs_typing] have rhs_sound: "sound_term_result state env rhsTy (interp_term d fuel state rhs)" .

  (* Case split on lhs evaluation *)
  show ?thesis
  proof (cases "interp_term d fuel state lhs")
    case (Inl err)
    (* LHS failed - propagate error *)
    then have "interp_term d (Suc fuel) state (CoreTm_Binop op lhs rhs) = Inl err" by simp
    with lhs_sound Inl show ?thesis by auto
  next
    case (Inr lhsVal)
    note lhs_eval = Inr
    (* Unless the operator is an equality, the operand type is subst-invariant,
       so the value has lhsTy itself *)
    have lhs_typed: "value_has_type env lhsVal lhsTy" if ne: "\<not> is_eq_neq_binop op"
      using lhs_sound lhs_eval
            binop_operand_apply_subst_ne(1)[OF typing lhs_typing rhs_typing ne]
      by simp

    (* Case split on short-circuit evaluation *)
    show ?thesis
    proof (cases "short_circuit op lhsVal")
      case (Some result)
      (* Short-circuit: result determined by lhs alone; it is a bool of type Bool *)
      from short_circuit_bool[OF Some] obtain b where result_eq: "result = CV_Bool b" by blast
      have ty_bool: "ty = CoreTy_Bool" using short_circuit_type_bool[OF Some typing] .
      have "interp_term d (Suc fuel) state (CoreTm_Binop op lhs rhs) = Inr result"
        using Inr Some by simp
      then show ?thesis using result_eq ty_bool by simp
    next
      case None

      (* Case split on rhs evaluation *)
      show ?thesis
      proof (cases "interp_term d fuel state rhs")
        case (Inl err)
        (* RHS failed - propagate error *)
        then have "interp_term d (Suc fuel) state (CoreTm_Binop op lhs rhs) = Inl err"
          using lhs_eval None by simp
        with rhs_sound Inl show ?thesis by auto
      next
        case (Inr rhsVal)
        have rhs_typed: "value_has_type env rhsVal rhsTy" if ne: "\<not> is_eq_neq_binop op"
          using rhs_sound Inr
                binop_operand_apply_subst_ne(2)[OF typing lhs_typing rhs_typing ne]
          by simp

        (* Both operands succeeded - defer to eval_binop soundness *)
        have "interp_term d (Suc fuel) state (CoreTm_Binop op lhs rhs) = eval_binop op lhsVal rhsVal"
          using lhs_eval Inr None by simp
        moreover have "sound_term_result state env ty (eval_binop op lhsVal rhsVal)"
          by (rule eval_binop_sound[OF typing lhs_typing rhs_typing])
             (simp_all add: lhs_typed rhs_typed)
        ultimately show ?thesis by simp
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
                core_term_type env' Ghost tm' = Some ty' \<Longrightarrow>
                sound_term_result state' env' ty' (interp_term d fuel state' tm')"
    and typing: "core_term_type env Ghost (CoreTm_Let var rhs body) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_Let var rhs body))"
proof -
  (* Extract facts from typing. In Ghost mode the typing rule records the new
     variable in TE_GhostLocals. *)
  from typing obtain rhsTy where
    rhs_typing: "core_term_type env Ghost rhs = Some rhsTy" and
    body_typing: "core_term_type
        (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
               TE_GhostLocals := finsert var (TE_GhostLocals env),
               TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
        Ghost body = Some ty"
    by (auto simp: Let_def split: option.splits if_splits)

  let ?env' = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                     TE_GhostLocals := finsert var (TE_GhostLocals env),
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  (* The same environment without the TE_GhostLocals update, which neither
     state_matches_env nor tyenv_well_formed reads. *)
  let ?env2 = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"

  (* Apply IH to rhs *)
  from IH[OF state_env wf_env rhs_typing]
  have rhs_sound: "sound_term_result state env rhsTy (interp_term d fuel state rhs)" .

  show ?thesis
  proof (cases "interp_term d fuel state rhs")
    case (Inl err)
    (* RHS failed - propagate error *)
    then have "interp_term d (Suc fuel) state (CoreTm_Let var rhs body) = Inl err"
      by simp
    with rhs_sound Inl show ?thesis by auto
  next
    case (Inr rhsVal)
    (* RHS succeeded. rhsTy may mention tyvars; rhsVal satisfies the
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
    have interp_eq: "interp_term d (Suc fuel) state (CoreTm_Let var rhs body) =
          interp_term d fuel ?state'' body"
      using Inr alloc_eq by (simp add: case_prod_beta split: prod.splits)

    (* The new state matches the extended env under the extended storeTyping *)
    have state''_env2: "state_matches_env ?state'' ?env2
                          (storeTyping @ [apply_subst (IS_TyArgs state) rhsTy])"
      using state_matches_env_add_const_local[OF state_env rhs_typed alloc_eq refl refl]
      by simp
    have sme_env'_env2: "state_matches_env ?state'' ?env' st
                           = state_matches_env ?state'' ?env2 st" for st
      by (rule state_matches_env_cong_env) simp_all
    have state''_env': "state_matches_env ?state'' ?env'
                          (storeTyping @ [apply_subst (IS_TyArgs state) rhsTy])"
      using state''_env2 sme_env'_env2 by simp

    (* The extended env is well-formed *)
    have rhs_wk: "is_well_kinded env rhsTy"
      using core_term_type_well_kinded[OF rhs_typing wf_env] .
    have wf_env': "tyenv_well_formed ?env'"
      by (rule tyenv_well_formed_declare_ghost[OF wf_env rhs_wk])

    (* Apply IH to body in extended env *)
    from IH[OF state''_env' wf_env' body_typing]
    have body_sound: "sound_term_result ?state'' ?env' ty (interp_term d fuel ?state'' body)" .

    (* sound_term_result env' = sound_term_result env, because value_has_type
       only depends on datatypes, not TE_LocalVars/TE_GlobalVars/TE_GhostLocals *)
    have env'_fields: "TE_DataCtors ?env' = TE_DataCtors env"
                       "TE_Datatypes ?env' = TE_Datatypes env"
      by simp_all
    have vht_eq: "\<And>v t. value_has_type ?env' v t = value_has_type env v t"
      using value_has_type_ground_cong_env[OF env'_fields] .
    have tyargs_eq: "IS_TyArgs ?state'' = IS_TyArgs state"
      using alloc_eq by auto
    from body_sound vht_eq tyargs_eq
    have "sound_term_result state env ty (interp_term d fuel ?state'' body)"
      by (cases "interp_term d fuel ?state'' body") auto
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
                core_term_type env' Ghost tm' = Some ty' \<Longrightarrow>
                sound_term_result state' env' ty' (interp_term d fuel state' tm')"
    and typing: "core_term_type env Ghost (CoreTm_RecordProj tm fldName) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_RecordProj tm fldName))"
proof -
  (* Extract facts from typing *)
  from typing obtain fieldTypes where
    tm_typing: "core_term_type env Ghost tm = Some (CoreTy_Record fieldTypes)" and
    fld_lookup: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)

  (* Apply IH to tm *)
  from IH[OF state_env wf_env tm_typing]
  have tm_sound: "sound_term_result state env (CoreTy_Record fieldTypes) (interp_term d fuel state tm)" .

  show ?thesis
  proof (cases "interp_term d fuel state tm")
    case (Inl err)
    (* tm failed - propagate error *)
    then have "interp_term d (Suc fuel) state (CoreTm_RecordProj tm fldName) = Inl err"
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
    have interp_eq: "interp_term d (Suc fuel) state (CoreTm_RecordProj tm fldName) = Inr fldVal"
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
                core_term_type env' Ghost tm' = Some ty' \<Longrightarrow>
                sound_term_result state' env' ty' (interp_term d fuel state' tm')"
    and typing: "core_term_type env Ghost (CoreTm_VariantProj tm ctorName) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_VariantProj tm ctorName))"
proof -
  (* Extract facts from typing *)
  from typing obtain dtName tyArgs dtName2 tyvars payloadTy where
    tm_typing: "core_term_type env Ghost tm = Some (CoreTy_Datatype dtName tyArgs)" and
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, tyvars, payloadTy)" and
    dt_eq: "dtName = dtName2" and
    len_eq: "length tyArgs = length tyvars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    by (auto split: option.splits CoreType.splits prod.splits if_splits)

  (* Apply IH to tm *)
  from IH[OF state_env wf_env tm_typing]
  have tm_sound: "sound_term_result state env (CoreTy_Datatype dtName tyArgs) (interp_term d fuel state tm)" .

  show ?thesis
  proof (cases "interp_term d fuel state tm")
    case (Inl err)
    (* tm failed - propagate error *)
    then have "interp_term d (Suc fuel) state (CoreTm_VariantProj tm ctorName) = Inl err"
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
      have abs_empty: "TE_AbstractTypes env = {||}"
        using state_env unfolding state_matches_env_def by simp
      from payloads_wk ctor_lookup abs_empty
      have payload_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
        unfolding tyenv_payloads_well_kinded_def by simp
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

      moreover have "interp_term d (Suc fuel) state (CoreTm_VariantProj tm ctorName) = Inr payload"
        using Inr val_eq True by simp

      ultimately show ?thesis by simp
    next
      case False
      (* Constructor names don't match - RuntimeError *)
      have "interp_term d (Suc fuel) state (CoreTm_VariantProj tm ctorName) = Inl RuntimeError"
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
                core_term_type env' Ghost tm' = Some ty' \<Longrightarrow>
                sound_term_result state' env' ty' (interp_term d fuel state' tm')"
    and IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' Ghost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results state' env' (map the types') (interp_term_list d fuel state' tms')"
    and typing: "core_term_type env Ghost (CoreTm_ArrayProj arr idxTms) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_ArrayProj arr idxTms))"
proof -
  (* Extract facts from typing *)
  from typing obtain elemTy dims where
    arr_typing: "core_term_type env Ghost arr = Some (CoreTy_Array elemTy dims)" and
    len_eq: "length idxTms = length dims" and
    idxs_typed: "list_all (\<lambda>tm. core_term_type env Ghost tm
                    = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)

  (* Apply IH to arr *)
  from IH_term[OF state_env wf_env arr_typing]
  have arr_sound: "sound_term_result state env (CoreTy_Array elemTy dims) (interp_term d fuel state arr)" .

  (* Prepare typing info for index terms to use IH_list *)
  let ?types = "map (core_term_type env Ghost) idxTms"
  from idxs_typed have types_all_some: "list_all (\<lambda>ty. ty \<noteq> None) ?types"
    by (simp add: list_all_length)
  from IH_list[OF state_env wf_env] types_all_some
  have idx_sound: "sound_term_results state env (map the ?types) (interp_term_list d fuel state idxTms)"
    by simp

  (* The expected types are all u64 *)
  from idxs_typed have map_the_types: "map the ?types =
      replicate (length idxTms) (CoreTy_FiniteInt Unsigned IntBits_64)"
    by (induction idxTms) (auto simp: list_all_iff)

  show ?thesis
  proof (cases "interp_term d fuel state arr")
    case (Inl err)
    then have "interp_term d (Suc fuel) state (CoreTm_ArrayProj arr idxTms) = Inl err"
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
    proof (cases "interp_term_list d fuel state idxTms")
      case (Inl err)
      then have "interp_term d (Suc fuel) state (CoreTm_ArrayProj arr idxTms) = Inl err"
        using Inr arr_val_eq by simp
      with idx_sound Inl show ?thesis by auto
    next
      case (Inr idxVals)
      (* The substituted u64 type is just u64 itself, so the replicate stays the same. *)
      have map_the_types_sub:
        "map (apply_subst (IS_TyArgs state) \<circ> (the \<circ> core_term_type env Ghost)) idxTms
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
        then have "interp_term d (Suc fuel) state (CoreTm_ArrayProj arr idxTms) = Inl RuntimeError"
          using \<open>interp_term d fuel state arr = Inr arrVal\<close> arr_val_eq Inr interp_idx_eq
          by simp
        then show ?thesis by simp
      next
        case (Some result)
        have result_typed: "value_has_type env result ?subElemTy"
          using elems_typed Some by simp
        have "interp_term d (Suc fuel) state (CoreTm_ArrayProj arr idxTms) = Inr result"
          using \<open>interp_term d fuel state arr = Inr arrVal\<close> arr_val_eq Inr interp_idx_eq Some
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
                map (core_term_type env' Ghost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results state' env' (map the types') (interp_term_list d fuel state' tms')"
    and typing: "core_term_type env Ghost (CoreTm_Record flds) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_Record flds))"
proof -
  (* Extract facts from typing *)
  from typing obtain tys where
    distinct_names: "distinct (map fst flds)" and
    those_ok: "those (map (\<lambda>(name, tm). core_term_type env Ghost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits if_splits)

  (* Derive that each field term is typed *)
  from those_ok have la2: "list_all2 (\<lambda>x y. x = Some y)
      (map (\<lambda>(name, tm). core_term_type env Ghost tm) flds) tys"
    by (simp add: those_eq_Some)
  hence len_eq: "length tys = length flds" by (auto dest: list_all2_lengthD)

  (* Connect with interp_term_list's precondition *)
  define types where "types = map (core_term_type env Ghost) (map snd flds)"
  have types_map: "types = map (\<lambda>(name, tm). core_term_type env Ghost tm) flds"
    unfolding types_def by (induction flds) auto
  have types_eq: "map (core_term_type env Ghost) (map snd flds) = types"
    unfolding types_def by simp
  have all_typed: "list_all (\<lambda>ty. ty \<noteq> None) types"
  proof -
    from la2 have "\<forall>i < length flds.
        (map (\<lambda>(name, tm). core_term_type env Ghost tm) flds) ! i = Some (tys ! i)"
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
      "(map (\<lambda>(name, tm). core_term_type env Ghost tm) flds) ! i = Some (tys ! i)"
      by (auto simp: list_all2_conv_all_nth)
    thus "map the types ! i = tys ! i"
      using types_map i_bound by auto
  qed

  (* Apply the list IH *)
  from IH_list[OF state_env wf_env, of "map snd flds" types]
  have list_sound: "sound_term_results state env (map the types) (interp_term_list d fuel state (map snd flds))"
    using types_eq all_typed by simp

  (* Case split on list evaluation *)
  show ?thesis
  proof (cases "interp_term_list d fuel state (map snd flds)")
    case (Inl err)
    then have "interp_term d (Suc fuel) state (CoreTm_Record flds) = Inl err"
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

    have interp_eq: "interp_term d (Suc fuel) state (CoreTm_Record flds) =
          Inr (CV_Record (zip (map fst flds) vals))"
      using Inr by simp

    (* Show the result has the substituted record type *)
    have len_vals: "length vals = length flds"
      using vals_typed' len_eq by (auto dest: list_all2_lengthD)

    have len_names: "length (map fst flds) = length vals"
      using len_vals by simp
    have "value_has_type env (CV_Record (zip (map fst flds) vals))
            (CoreTy_Record (zip (map fst flds) ?subTys))"
      by (rule cv_record_typed[OF vals_typed' distinct_names len_names])

    moreover have "apply_subst ?s ty = CoreTy_Record (zip (map fst flds) ?subTys)"
      using ty_eq len_eq by (simp add: zip_map2)
    ultimately show ?thesis using interp_eq by simp
  qed
qed

(* Type soundness for CoreTm_VariantCtor *)
lemma type_soundness_variant_ctor:
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env Ghost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term d fuel state tm')"
    and typing: "core_term_type env Ghost (CoreTm_VariantCtor ctorName tyArgs payload) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payload))"
proof -
  (* Extract facts from typing *)
  from typing obtain dtName tyvars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyargs_cp: "list_all is_complete_type tyArgs"
    by (auto simp: Let_def split: option.splits prod.splits if_splits)

  have abs_empty: "TE_AbstractTypes env = {||}"
    using state_env state_matches_env_def by auto

  define tySubst where "tySubst = fmap_of_list (zip tyvars tyArgs)"
  define payloadTyOpt where "payloadTyOpt = core_term_type env Ghost payload"

  from typing ctor_lookup len_eq tyargs_wk tyargs_cp
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

  have payload_typing: "core_term_type env Ghost payload = Some payloadActualTy"
    using payloadTyOpt_eq payloadTyOpt_def by simp

  (* IH on payload *)
  from IH[OF payload_typing]
  have payload_sound: "sound_term_result state env payloadActualTy (interp_term d fuel state payload)" .

  (* Case split on payload evaluation *)
  show ?thesis
  proof (cases "interp_term d fuel state payload")
    case (Inl err)
    then have "interp_term d (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payload) = Inl err"
      by simp
    with payload_sound Inl show ?thesis by auto
  next
    case (Inr payloadVal)
    let ?s = "IS_TyArgs state"
    let ?subTyArgs = "map (apply_subst ?s) tyArgs"
    from payload_sound Inr
    have payload_typed: "value_has_type env payloadVal (apply_subst ?s payloadActualTy)"
      by simp

    have interp_eq: "interp_term d (Suc fuel) state (CoreTm_VariantCtor ctorName tyArgs payload) =
          Inr (CV_Variant ctorName payloadVal)"
      using Inr by simp

    (* Substituted tyArgs are well-kinded, ground, and have the right length. *)
    have len_eq_sub: "length ?subTyArgs = length tyvars" using len_eq by simp
    have subTyArgs_wk: "list_all (is_well_kinded env) ?subTyArgs"
      using tyargs_wk
      by (induction tyArgs) (auto simp: is_well_kinded_apply_IS_TyArgs[OF state_env])
    have subTyArgs_ground: "list_all (\<lambda>a. type_tyvars a = {}) ?subTyArgs"
      using tyargs_wk
      by (induction tyArgs) (auto simp: is_well_kinded_apply_IS_TyArgs_ground[OF state_env])

    (* Lift payload typing into a (zip tyvars ?subTyArgs)-substitution form. *)
    from ctor_lookup wf_env have
      payloads_wk: "tyenv_payloads_well_kinded env" and
      ctor_distinct: "tyenv_ctor_tyvars_distinct env"
      unfolding tyenv_well_formed_def by auto
    from payloads_wk ctor_lookup
    have payload_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
      unfolding tyenv_payloads_well_kinded_def abs_empty by simp
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
      using ctor_lookup len_eq_sub subTyArgs_wk subTyArgs_ground payload_typed'
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
    and IH: "\<And>tm' ty'. core_term_type env Ghost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term d fuel state tm')"
    and typing: "core_term_type env Ghost (CoreTm_Match scrut arms) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_Match scrut arms))"
proof -
  (* Extract facts from typing *)
  define scrutTyOpt where "scrutTyOpt = core_term_type env Ghost scrut"

  from typing have typing': "(case scrutTyOpt of
      None \<Rightarrow> None
    | Some scrutTy \<Rightarrow>
        let pats = map fst arms; bodies = map snd arms
        in if arms = [] then None
           else if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
           else (case core_term_type env Ghost (snd (hd arms)) of
                   None \<Rightarrow> None
                 | Some resultTy \<Rightarrow>
                     if list_all (\<lambda>body. core_term_type env Ghost body = Some resultTy) (tl bodies)
                     then Some resultTy else None)) = Some ty"
    unfolding scrutTyOpt_def by simp

  from typing' obtain scrutTy where
    scrutTyOpt_eq: "scrutTyOpt = Some scrutTy"
    by (cases scrutTyOpt) auto

  have scrut_typing: "core_term_type env Ghost scrut = Some scrutTy"
    using scrutTyOpt_eq scrutTyOpt_def by simp

  from typing' scrutTyOpt_eq have typing'':
    "(let pats = map fst arms; bodies = map snd arms
      in if arms = [] then None
         else if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
         else (case core_term_type env Ghost (snd (hd arms)) of
                 None \<Rightarrow> None
               | Some resultTy \<Rightarrow>
                   if list_all (\<lambda>body. core_term_type env Ghost body = Some resultTy)
                               (tl (map snd arms))
                   then Some resultTy else None)) = Some ty"
    by simp

  from typing'' have arms_nonempty: "arms \<noteq> []"
    by (cases arms) (simp_all add: Let_def)

  define hd_ty_opt where "hd_ty_opt = core_term_type env Ghost (snd (hd arms))"

  from typing'' arms_nonempty
  have typing''': "(case hd_ty_opt of
      None \<Rightarrow> None
    | Some resultTy \<Rightarrow>
        if list_all (\<lambda>body. core_term_type env Ghost body = Some resultTy)
                    (tl (map snd arms))
        then Some resultTy else None) = Some ty"
    unfolding hd_ty_opt_def Let_def by (simp split: if_splits)

  from typing''' obtain resultTy where
    hd_ty_opt_eq: "hd_ty_opt = Some resultTy" and
    ty_eq: "ty = resultTy"
    by (cases hd_ty_opt) (auto split: if_splits)

  have hd_typing: "core_term_type env Ghost (snd (hd arms)) = Some resultTy"
    using hd_ty_opt_eq hd_ty_opt_def by simp

  from typing''' hd_ty_opt_eq ty_eq have
    tl_typing: "list_all (\<lambda>body. core_term_type env Ghost body = Some resultTy) (tl (map snd arms))"
    by (simp split: if_splits)

  (* IH on scrutinee *)
  from IH[OF scrut_typing]
  have scrut_sound: "sound_term_result state env scrutTy (interp_term d fuel state scrut)" .

  (* Case split on scrutinee evaluation *)
  show ?thesis
  proof (cases "interp_term d fuel state scrut")
    case (Inl err)
    then have "interp_term d (Suc fuel) state (CoreTm_Match scrut arms) = Inl err" by simp
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
      then have "interp_term d (Suc fuel) state (CoreTm_Match scrut arms) = Inl RuntimeError"
        using scrut_eval Inl by simp
      then show ?thesis by simp
    next
      case (Inr armBody)
      then have match_eq: "find_matching_arm scrutVal arms = Inr armBody" .

      (* armBody is the body of some arm in the list *)
      from find_matching_arm_in_arms[OF match_eq]
      obtain pat where arm_in: "(pat, armBody) \<in> set arms" by auto

      (* armBody typechecks to resultTy *)
      have arm_typed: "core_term_type env Ghost armBody = Some resultTy"
        by (rule match_arm_body_typed[OF arms_nonempty hd_typing tl_typing arm_in])

      (* IH on arm body *)
      from IH[OF arm_typed]
      have arm_sound: "sound_term_result state env resultTy (interp_term d fuel state armBody)" .

      (* Compute the result *)
      have "interp_term d (Suc fuel) state (CoreTm_Match scrut arms) =
            interp_term d fuel state armBody"
        using scrut_eval match_eq by simp
      with arm_sound ty_eq show ?thesis by simp
    qed
  qed
qed

(* Type soundness for CoreTm_Sizeof *)
lemma type_soundness_sizeof:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. core_term_type env Ghost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term d fuel state tm')"
    and typing: "core_term_type env Ghost (CoreTm_Sizeof tm) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_Sizeof tm))"
proof -
  from typing obtain elemTy dims where
    tm_typing: "core_term_type env Ghost tm = Some (CoreTy_Array elemTy dims)" and
    ty_eq: "ty = sizeof_type dims"
    by (auto split: option.splits CoreType.splits if_splits)

  from IH[OF tm_typing]
  have tm_sound: "sound_term_result state env (CoreTy_Array elemTy dims) (interp_term d fuel state tm)" .

  show ?thesis
  proof (cases "interp_term d fuel state tm")
    case (Inl err)
    then have "interp_term d (Suc fuel) state (CoreTm_Sizeof tm) = Inl err" by simp
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
    have interp_eq: "interp_term d (Suc fuel) state (CoreTm_Sizeof tm) =
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
                map (core_term_type env' Ghost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results state' env' (map the types') (interp_term_list d fuel state' tms')"
    and typing: "core_term_type env Ghost (CoreTm_LitArray elemTy tms) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_LitArray elemTy tms))"
proof -
  (* Extract facts from typing *)
  from typing have
    wk: "is_well_kinded env elemTy" and
    all_typed: "list_all (\<lambda>tm. core_term_type env Ghost tm = Some elemTy) tms" and
    len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)

  (* Set up list IH precondition *)
  define types where "types = map (core_term_type env Ghost) tms"
  have types_eq: "map (core_term_type env Ghost) tms = types"
    by (simp add: types_def)
  have all_some: "list_all (\<lambda>ty. ty \<noteq> None) types"
    using all_typed by (auto simp: types_def list_all_iff)
  have the_types: "map the types = replicate (length tms) elemTy"
    using all_typed by (auto simp: types_def list_all_iff intro!: nth_equalityI)

  (* Apply list IH *)
  from IH_list[OF state_env wf_env, of tms types] types_eq all_some
  have list_sound: "sound_term_results state env (replicate (length tms) elemTy)
                      (interp_term_list d fuel state tms)"
    using the_types by simp

  let ?s = "IS_TyArgs state"
  let ?subElemTy = "apply_subst ?s elemTy"

  (* Case split on list evaluation *)
  show ?thesis
  proof (cases "interp_term_list d fuel state tms")
    case (Inl err)
    then have "interp_term d (Suc fuel) state (CoreTm_LitArray elemTy tms) = Inl err" by simp
    with list_sound Inl show ?thesis by auto
  next
    case (Inr vals)
    from list_sound Inr
    have vals_typed: "list_all2 (value_has_type env) vals (replicate (length tms) ?subElemTy)"
      by simp
    hence len_vals: "length vals = length tms" by (auto dest: list_all2_lengthD)
    hence vals_elem_typed: "\<And>i. i < length vals \<Longrightarrow> value_has_type env (vals ! i) ?subElemTy"
      using vals_typed by (auto simp: list_all2_conv_all_nth)

    have interp_eq: "interp_term d (Suc fuel) state (CoreTm_LitArray elemTy tms) =
          Inr (make_1d_array vals)"
      using Inr by simp

    (* Show make_1d_array vals has the right type, via the shared lemma *)
    have wk_sub: "is_well_kinded env ?subElemTy"
      using is_well_kinded_apply_IS_TyArgs[OF state_env wk] .
    have ground_sub: "type_tyvars ?subElemTy = {}"
      using is_well_kinded_apply_IS_TyArgs_ground[OF state_env wk] .
    have len_ok': "int_in_range (int_range Unsigned IntBits_64) (int (length vals))"
      using len_ok len_vals by simp

    have "value_has_type env (make_1d_array vals)
            (CoreTy_Array ?subElemTy [CoreDim_Fixed (int (length vals))])"
      using make_1d_array_typed[OF wk_sub ground_sub vals_elem_typed len_ok'] .
    hence "value_has_type env (make_1d_array vals)
            (CoreTy_Array ?subElemTy [CoreDim_Fixed (int (length tms))])"
      using len_vals by simp

    with interp_eq ty_eq show ?thesis
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
    and args_typed: "list_all2 (\<lambda>tm expectedTy.
         core_term_type env Ghost tm = Some expectedTy)
       argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                   (FI_TmArgs funInfo))"
    and retTy_eq: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    and ty_len: "length tyArgs = length (FI_TyArgs funInfo)"
    and ty_wk: "list_all (is_well_kinded env) tyArgs"
    and ref_writable: "\<forall>i < length argTms.
         (fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
          is_writable_lvalue env (argTms ! i))"
    and IH_term: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' Ghost tm' = Some ty' \<Longrightarrow>
                  sound_term_result state' env' ty' (interp_term d fuel state' tm')"
    and IH_lvalue: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                is_writable_lvalue env' tm' \<and> core_term_type env' Ghost tm' = Some ty' \<Longrightarrow>
                  sound_lvalue_result state' env' storeTyping' ty' (interp_writable_lvalue d fuel state' tm')"
    and IH_stmts: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 ghost0 stmts0 env0'.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                TE_ProofGoal env0 = None \<Longrightarrow>
                core_statement_list_type env0 ghost0 stmts0 = Some env0' \<Longrightarrow>
                  sound_statement_result env0 env0' storeTyping0 (interp_statement_list d fuel state0 stmts0)"
  shows "sound_function_call_result state env storeTyping retTy
           (interp_function_call d (Suc fuel) state fnName tyArgs argTms)"
proof -
  \<comment> \<open>Obtain the InterpFun f for fnName via funs_exist_in_state. \<close>
  from state_env have fes: "funs_exist_in_state state env"
    unfolding state_matches_env_def by blast
  from fes fn_lookup
  have "case fmlookup (IS_Functions state) fnName of
          Some interpFun \<Rightarrow> fun_info_matches_interp_fun env funInfo interpFun
        | None \<Rightarrow> False"
    unfolding funs_exist_in_state_def by blast
  then obtain f where
    f_lookup: "fmlookup (IS_Functions state) fnName = Some f"
    and fi_match: "fun_info_matches_interp_fun env funInfo f"
    by (cases "fmlookup (IS_Functions state) fnName") auto

  have abs_empty: "TE_AbstractTypes env = {||}"
    using state_env unfolding state_matches_env_def by blast

  \<comment> \<open>Length match between argTms and f's args (via fi_match + args_typed). \<close>
  from fi_match have len_fi: "length (FI_TmArgs funInfo) = length (IF_Args f)"
    unfolding fun_info_matches_interp_fun_def by (auto dest: list_all2_lengthD)
  \<comment> \<open>Parameter names (from f's IF_Args) are distinct. The body env is built over them. \<close>
  from fi_match have dist_names: "distinct (map fst (IF_Args f))"
    unfolding fun_info_matches_interp_fun_def by simp
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
  define tySubst :: "(string, CoreType) fmap" where
    tySubst_def: "tySubst = fmap_of_list
                (zip (FI_TyArgs funInfo)
                     (map (apply_subst (IS_TyArgs state)) tyArgs))"

  \<comment> \<open>Basic structural facts about tySubst: distinctness, well-formedness, ground range. \<close>
  from wf_env fn_lookup have ty_dist: "distinct (FI_TyArgs funInfo)"
    unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast

  have fmdom_tySubst: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
    using tySubst_def ty_len
    by (simp add: fset_of_list.rep_eq)

  \<comment> \<open>Each entry of tySubst's range is ground and well-kinded in env: it is
      apply_subst (IS_TyArgs state) of a type argument that is well-kinded in env. \<close>
  have tySubst_range:
    "\<forall>t \<in> fmran' tySubst. type_tyvars t = {} \<and> is_well_kinded env t"
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
    from ty_wk j_lt have wk_j: "is_well_kinded env (tyArgs ! j)"
      by (simp add: list_all_length)
    show "type_tyvars t = {} \<and> is_well_kinded env t"
      using is_well_kinded_apply_IS_TyArgs_ground[OF state_env wk_j]
            is_well_kinded_apply_IS_TyArgs[OF state_env wk_j] t_eq
      by simp
  qed

  \<comment> \<open>The parameter types and the return type mention only the function's own
      type variables. \<close>
  have paramTy_subset:
    "\<And>i. i < length (FI_TmArgs funInfo) \<Longrightarrow>
            type_tyvars (fst (FI_TmArgs funInfo ! i)) \<subseteq> set (FI_TyArgs funInfo)"
  proof -
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    have "fst (FI_TmArgs funInfo ! i) \<in> fst ` set (FI_TmArgs funInfo)"
      using i_bound by force
    with fun_info_types_tyvars_subset(1)[OF wf_env abs_empty fn_lookup]
    show "type_tyvars (fst (FI_TmArgs funInfo ! i)) \<subseteq> set (FI_TyArgs funInfo)" by blast
  qed
  have ret_tyvars_sub: "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    using fun_info_types_tyvars_subset(2)[OF wf_env abs_empty fn_lookup] .

  \<comment> \<open>Abbreviations matching the interpreter's let-bound names. \<close>
  let ?refResults = "map (interp_writable_lvalue d fuel state) argTms"
  let ?valResults = "map (interp_term d fuel state) argTms"
  let ?argTuples = "zip (IF_Args f) (zip ?refResults ?valResults)"
  let ?clearedState = "state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty,
                                IS_ConstLocals := {||},
                                IS_TyArgs := tySubst \<rparr>"

  \<comment> \<open>The interpreter reduces to a fold + body dispatch. \<close>
  have interp_eq:
    "interp_function_call d (Suc fuel) state fnName tyArgs argTms
     = (case fold process_one_arg ?argTuples (Inr ?clearedState) of
          Inl err \<Rightarrow> Inl err
        | Inr preCallState \<Rightarrow>
            (case IF_Body f of
               Inl bodyStmts \<Rightarrow>
                 (case interp_statement_list d fuel preCallState bodyStmts of
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
                      (fst (FI_TmArgs funInfo ! i)))
         (?valResults ! i)"
  proof (intro allI impI)
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
    with len_argTms_fi have i_argTms: "i < length argTms" by simp
    let ?paramTy_i = "fst (FI_TmArgs funInfo ! i)"
    let ?expTy_i = "apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i"
    from args_typed have all_i:
      "\<forall>j < length argTms.
         case core_term_type env Ghost (argTms ! j) of
           None \<Rightarrow> False
         | Some actualTy \<Rightarrow> actualTy
             = (map (\<lambda>(ty, _).
                       apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                   (FI_TmArgs funInfo)) ! j"
      by (simp add: list_all2_conv_all_nth)
    from all_i i_argTms have raw_ty_i:
      "case core_term_type env Ghost (argTms ! i) of
         None \<Rightarrow> False
       | Some actualTy \<Rightarrow> actualTy
            = (map (\<lambda>(ty, _).
                     apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                  (FI_TmArgs funInfo)) ! i"
      by blast
    have map_i_eq:
      "(map (\<lambda>(ty, _).
               apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
            (FI_TmArgs funInfo)) ! i = ?expTy_i"
      using i_bound by (simp add: case_prod_beta)
    from raw_ty_i obtain actualTy where
      cty_i: "core_term_type env Ghost (argTms ! i) = Some actualTy"
      and act_eq_raw: "actualTy = (map (\<lambda>(ty, _).
                     apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                  (FI_TmArgs funInfo)) ! i"
      by (cases "core_term_type env Ghost (argTms ! i)") simp_all
    from act_eq_raw map_i_eq have act_eq: "actualTy = ?expTy_i" by simp
    from IH_term[OF state_env wf_env, of "argTms ! i" actualTy] cty_i
    have "sound_term_result state env actualTy (interp_term d fuel state (argTms ! i))"
      by simp
    with act_eq i_argTms show
      "sound_term_result state env ?expTy_i (?valResults ! i)"
      by simp
  qed

  have lvals_sound:
    "\<forall>i < length (FI_TmArgs funInfo).
       fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
         sound_lvalue_result state env storeTyping
           (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                        (fst (FI_TmArgs funInfo ! i)))
           (?refResults ! i)"
  proof (intro allI impI)
    fix i assume i_bound: "i < length (FI_TmArgs funInfo)"
                and is_ref: "fst (snd (FI_TmArgs funInfo ! i)) = Ref"
    with len_argTms_fi have i_argTms: "i < length argTms" by simp
    let ?paramTy_i = "fst (FI_TmArgs funInfo ! i)"
    let ?expTy_i = "apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i"
    from args_typed have all_i:
      "\<forall>j < length argTms.
         case core_term_type env Ghost (argTms ! j) of
           None \<Rightarrow> False
         | Some actualTy \<Rightarrow> actualTy
             = (map (\<lambda>(ty, _).
                       apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                   (FI_TmArgs funInfo)) ! j"
      by (simp add: list_all2_conv_all_nth)
    from all_i i_argTms have raw_ty_i:
      "case core_term_type env Ghost (argTms ! i) of
         None \<Rightarrow> False
       | Some actualTy \<Rightarrow> actualTy
            = (map (\<lambda>(ty, _).
                     apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                  (FI_TmArgs funInfo)) ! i"
      by blast
    have map_i_eq:
      "(map (\<lambda>(ty, _).
               apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
            (FI_TmArgs funInfo)) ! i = ?expTy_i"
      using i_bound by (simp add: case_prod_beta)
    from raw_ty_i obtain actualTy where
      cty_i: "core_term_type env Ghost (argTms ! i) = Some actualTy"
      and act_eq_raw: "actualTy = (map (\<lambda>(ty, _).
                     apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                  (FI_TmArgs funInfo)) ! i"
      by (cases "core_term_type env Ghost (argTms ! i)") simp_all
    from act_eq_raw map_i_eq have act_eq: "actualTy = ?expTy_i" by simp
    from ref_writable i_argTms is_ref have wlv_i:
      "is_writable_lvalue env (argTms ! i)" by simp
    from IH_lvalue[OF state_env wf_env, of "argTms ! i" actualTy] cty_i wlv_i
    have "sound_lvalue_result state env storeTyping actualTy
            (interp_writable_lvalue d fuel state (argTms ! i))"
      by simp
    with act_eq i_argTms show
      "sound_lvalue_result state env storeTyping ?expTy_i (?refResults ! i)"
      by simp
  qed

  \<comment> \<open>Apply the helper to get sound arg processing result. \<close>
  note arg_sound = fold_process_one_arg_sound
                     [OF state_env wf_env fn_lookup fi_match
                         ty_len ty_wk vals_sound lvals_sound len_argTms_fi]
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
      "interp_function_call d (Suc fuel) state fnName tyArgs argTms = Inl err"
      by simp
    thus ?thesis using err_sound by simp
  next
    case fold_Inr: (Inr preCallState)
    \<comment> \<open>Arg processing succeeded. Extract the body env match + storeTyping. \<close>
    from arg_sound fold_Inr tySubst_def
    have tyargs_pre: "IS_TyArgs preCallState = tySubst"
      and pre_match: "\<exists>bodyStoreTyping.
                        state_matches_env preCallState (body_env_for env (map fst (IF_Args f)) funInfo) bodyStoreTyping
                      \<and> storeTyping_extends storeTyping bodyStoreTyping"
      unfolding sound_arg_processing_result_def by auto
    from pre_match obtain bodyStoreTyping where
      sme_body: "state_matches_env preCallState (body_env_for env (map fst (IF_Args f)) funInfo) bodyStoreTyping"
      and ext_body: "storeTyping_extends storeTyping bodyStoreTyping"
      by blast

    \<comment> \<open>Common facts derived from sme_body. \<close>
    have len_names: "length (map fst (IF_Args f)) = length (FI_TmArgs funInfo)"
      using len_fi by simp
    have wf_bodyEnv: "tyenv_well_formed (body_env_for env (map fst (IF_Args f)) funInfo)"
      using body_env_for_well_formed[OF wf_env fn_lookup abs_empty len_names] .

    show ?thesis
    proof (cases "IF_Body f")
      case body_babylon: (Inl bodyStmts)
      \<comment> \<open>Babylon body. The fi_match assumption certifies that bodyStmts
          typechecks in body_env_for env (map fst (IF_Args f)) funInfo, in the
          mode given by FI_Ghost funInfo. \<close>
      from fi_match body_babylon obtain bodyEnv' where
        body_ty: "core_statement_list_type (body_env_for env (map fst (IF_Args f)) funInfo)
                    (FI_Ghost funInfo) bodyStmts
                    = Some bodyEnv'"
        unfolding fun_info_matches_interp_fun_def by auto

      \<comment> \<open>Apply IH(5), at the function's own mode, to get sound_statement_result
          on the body. A function body is typechecked with no proof goal. \<close>
      have no_goal_body:
        "TE_ProofGoal (body_env_for env (map fst (IF_Args f)) funInfo) = None"
        by (simp add: body_env_for_def)
      from IH_stmts[OF sme_body wf_bodyEnv no_goal_body body_ty]
      have body_sound: "sound_statement_result (body_env_for env (map fst (IF_Args f)) funInfo) bodyEnv'
                          bodyStoreTyping
                          (interp_statement_list d fuel preCallState bodyStmts)"
        by simp

      show ?thesis
      proof (cases "interp_statement_list d fuel preCallState bodyStmts")
        case body_Inl: (Inl err)
        \<comment> \<open>Body errored. Sound by body_sound. \<close>
        from body_sound body_Inl have err_sound: "sound_error_result err" by simp
        from interp_eq fold_Inr body_babylon body_Inl
        have "interp_function_call d (Suc fuel) state fnName tyArgs argTms = Inl err"
          by simp
        thus ?thesis using err_sound by simp
      next
        case body_Inr: (Inr execRes)
        show ?thesis
        proof (cases execRes)
          case (Continue contState)
          \<comment> \<open>Body reached end without Return — interpreter returns RuntimeError. \<close>
          from interp_eq fold_Inr body_babylon body_Inr Continue
          have "interp_function_call d (Suc fuel) state fnName tyArgs argTms = Inl RuntimeError"
            by simp
          thus ?thesis by simp
        next
          case (Return postCallState retVal)
          \<comment> \<open>Main case. Extract env_mid + postStoreTyping + return value typing. \<close>
          from body_sound body_Inr Return
          have ret_typed_bodyEnv:
            "value_has_type (body_env_for env (map fst (IF_Args f)) funInfo) retVal
               (apply_subst (IS_TyArgs postCallState)
                            (TE_ReturnType (body_env_for env (map fst (IF_Args f)) funInfo)))"
            by simp
          from body_sound body_Inr Return obtain env_mid postStoreTyping where
            fxeq1: "tyenv_fixed_eq (body_env_for env (map fst (IF_Args f)) funInfo) env_mid"
            and fxeq2: "tyenv_fixed_eq env_mid bodyEnv'"
            and wf_mid: "tyenv_well_formed env_mid"
            and sme_post: "state_matches_env postCallState env_mid postStoreTyping"
            and ext_post: "storeTyping_extends bodyStoreTyping postStoreTyping"
            by auto

          \<comment> \<open>Concrete form of the interpreter result. \<close>            from interp_eq fold_Inr body_babylon body_Inr Return
          have interp_result:
            "interp_function_call d (Suc fuel) state fnName tyArgs argTms
               = Inr (restore_scope state postCallState, retVal)"
            by simp

          \<comment> \<open>preCallState's IS_Globals / IS_Functions = state's (cleared state preserves
              them; the fold preserves them too). \<close>
          from fold_Inr have fold_eq:
            "fold process_one_arg ?argTuples (Inr ?clearedState) = Inr preCallState" .
          from fold_process_one_arg_preserves_globals_funs[OF fold_eq]
          have pre_globals: "IS_Globals preCallState = IS_Globals state"
            and pre_functions: "IS_Functions preCallState = IS_Functions state"
            and pre_ctors_by_type: "IS_DataCtorsByType preCallState = IS_DataCtorsByType state"
            by auto

          \<comment> \<open>postCallState inherits IS_Globals / IS_Functions from preCallState
              (statement-list execution preserves them). \<close>
          from body_Inr Return have body_list_eq:
            "interp_statement_list d fuel preCallState bodyStmts
               = Inr (Return postCallState retVal)"
            by simp
          from interp_statement_list_static[OF body_list_eq]
          have static_post: "static_parts_eq preCallState postCallState" by simp
          have post_globals: "IS_Globals postCallState = IS_Globals state"
            using static_parts_eqD(1)[OF static_post] pre_globals
            by simp
          have post_functions: "IS_Functions postCallState = IS_Functions state"
            using static_parts_eqD(2)[OF static_post] pre_functions
            by simp
          have post_ctors_by_type: "IS_DataCtorsByType postCallState = IS_DataCtorsByType state"
            using static_parts_eqD(4)[OF static_post] pre_ctors_by_type
            by simp

          \<comment> \<open>tyenv_fixed_eq carries the dt-relevant field equalities. We also
              need to bridge through body_env_for, whose dt fields = env's. \<close>
          from fxeq1 have dt_eq_body_mid:
            "TE_DataCtors (body_env_for env (map fst (IF_Args f)) funInfo) = TE_DataCtors env_mid"
            "TE_Datatypes (body_env_for env (map fst (IF_Args f)) funInfo) = TE_Datatypes env_mid"
            "TE_GhostDatatypes (body_env_for env (map fst (IF_Args f)) funInfo) = TE_GhostDatatypes env_mid"
            unfolding tyenv_fixed_eq_def by simp_all
          have dt_eq_env_body:
            "TE_DataCtors env = TE_DataCtors (body_env_for env (map fst (IF_Args f)) funInfo)"
            "TE_Datatypes env = TE_Datatypes (body_env_for env (map fst (IF_Args f)) funInfo)"
            "TE_GhostDatatypes env = TE_GhostDatatypes (body_env_for env (map fst (IF_Args f)) funInfo)"
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
                                          post_globals post_functions post_ctors_by_type
                                          dt_eq(1) dt_eq(2)] .

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
            using static_parts_eqD(3)[OF static_post] tyargs_pre
            by simp

          \<comment> \<open>Return type of bodyEnv is the function's return type, unsubstituted. \<close>
          have ret_ty_eq: "TE_ReturnType (body_env_for env (map fst (IF_Args f)) funInfo) = FI_ReturnType funInfo"
            by (simp add: body_env_for_def)

          \<comment> \<open>Combine: value_has_type (body_env_for env (map fst (IF_Args f)) funInfo) retVal
                (apply_subst tySubst (FI_ReturnType funInfo)). \<close>
          from ret_typed_bodyEnv tyargs_post ret_ty_eq
          have ret_typed_body:
            "value_has_type (body_env_for env (map fst (IF_Args f)) funInfo) retVal
               (apply_subst tySubst (FI_ReturnType funInfo))"
            by simp

          \<comment> \<open>Transport to env: value_has_type reads only the datatype fields, which
              body_env_for inherits from env. \<close>
          have ret_typed_env:
            "value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo))"
            using ret_typed_body
                  value_has_type_ground_cong_env[OF dt_eq_env_body(1) dt_eq_env_body(2)]
            by simp

          \<comment> \<open>Reconcile apply_subst tySubst (FI_ReturnType funInfo) with
              apply_subst (IS_TyArgs state) retTy via apply_subst_compose_zip. \<close>
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
              (apply_subst tySubst (fst (FI_TmArgs funInfo ! i)))"
      proof (intro allI impI)
        fix i assume i_lt: "i < length argTms"
        with len_argTms_fi have i_fi: "i < length (FI_TmArgs funInfo)" by simp
        let ?paramTy_i = "fst (FI_TmArgs funInfo ! i)"
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
        moreover have compose:
          "apply_subst tySubst ?paramTy_i
            = apply_subst (IS_TyArgs state)
                (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i)"
          unfolding tySubst_def
          using apply_subst_compose_zip[OF ty_len[symmetric] paramTy_subset[OF i_fi] ty_dist] .
        ultimately have v_typed_tySubst:
          "value_has_type env v (apply_subst tySubst ?paramTy_i)"
          by simp
        show "value_has_type env (?vals ! i) (apply_subst tySubst ?paramTy_i)"
          using v_typed_tySubst vals_at_i by simp
      qed

      \<comment> \<open>Discharge the contract's preconditions: domain, ground and well-kinded
          range, and the list_all2 typing of vals. \<close>
      have prem_dom: "fmdom tySubst = fset_of_list (FI_TyArgs funInfo)"
        using fmdom_tySubst .

      have prem_range:
        "\<forall>ty' \<in> fmran' tySubst.
           type_tyvars ty' = {} \<and> is_well_kinded env ty'"
        using tySubst_range .

      \<comment> \<open>vals satisfy the list_all2 typing. \<close>
      have prem_list_all2:
        "list_all2 (value_has_type env) ?vals
           (map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))"
      proof -
        have len_map: "length (map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))
                      = length ?vals"
          using vals_len len_argTms_fi by simp
        show ?thesis
          unfolding list_all2_conv_all_nth
        proof (intro conjI allI impI)
          show "length ?vals = length (map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))"
            using vals_len len_argTms_fi by simp
          fix i assume i_lt: "i < length ?vals"
          from i_lt vals_len have i_argTms: "i < length argTms" by simp
          from i_argTms len_argTms_fi have i_fi: "i < length (FI_TmArgs funInfo)" by simp
          from vals_typed i_argTms have
            "value_has_type env (?vals ! i) (apply_subst tySubst (fst (FI_TmArgs funInfo ! i)))"
            by blast
          moreover have
            "(map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo)) ! i
              = apply_subst tySubst (fst (FI_TmArgs funInfo ! i))"
            using i_fi by (simp add: case_prod_beta)
          ultimately show
            "value_has_type env (?vals ! i)
              ((map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo)) ! i)"
            by simp
        qed
      qed

      \<comment> \<open>Apply the contract to get the post-conditions. \<close>
      from ext_contract have ext_inst:
        "fmdom tySubst = fset_of_list (FI_TyArgs funInfo) \<and>
         (\<forall>ty' \<in> fmran' tySubst.
              type_tyvars ty' = {} \<and> is_well_kinded env ty') \<and>
         list_all2 (value_has_type env) ?vals
                   (map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))
         \<longrightarrow> (case externFun (IS_World state) ?vals of
                (newWorld, refUpdates, retVal) \<Rightarrow>
                  value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo)) \<and>
                  list_all2 (value_has_type env) refUpdates
                    (map (\<lambda>(ty, _). apply_subst tySubst ty)
                         (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo))))"
        unfolding extern_fun_contract_def by meson
      from ext_inst prem_dom prem_range prem_list_all2
      have contract_implies:
        "case externFun (IS_World state) ?vals of
           (newWorld, refUpdates, retVal) \<Rightarrow>
             value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo)) \<and>
             list_all2 (value_has_type env) refUpdates
               (map (\<lambda>(ty, _). apply_subst tySubst ty)
                    (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo)))"
        by meson
      from contract_implies ext_call
      have contract_post:
        "value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo))
         \<and> list_all2 (value_has_type env) refUpdates
             (map (\<lambda>(ty, _). apply_subst tySubst ty)
                  (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo)))"
        by simp
      from contract_post have ret_typed_apply:
        "value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo))"
        by simp
      from contract_post have ref_updates_typed:
        "list_all2 (value_has_type env) refUpdates
           (map (\<lambda>(ty, _). apply_subst tySubst ty)
                (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo)))"
        by simp

      \<comment> \<open>Now build the ref-list information for apply_ref_updates_sound. \<close>
      \<comment> \<open>FI_TmArgs and IF_Args have matching Var/Ref positions. \<close>
      from fi_match have if_args_match:
        "list_all2 (\<lambda>(_, vor1, _) (_, vor2). vor1 = vor2)
                   (FI_TmArgs funInfo) (IF_Args f)"
        unfolding fun_info_matches_interp_fun_def by simp
      have vor_match:
        "\<forall>i < length (IF_Args f).
             snd ((IF_Args f) ! i) = Ref \<longleftrightarrow> fst (snd (FI_TmArgs funInfo ! i)) = Ref"
      proof (intro allI impI)
        fix i assume i_lt: "i < length (IF_Args f)"
        with len_fi have i_fi: "i < length (FI_TmArgs funInfo)" by simp
        obtain t1 v1 g1 where fi_i: "FI_TmArgs funInfo ! i = (t1, v1, g1)"
          by (cases "FI_TmArgs funInfo ! i") auto
        obtain n2 v2 where if_i: "(IF_Args f) ! i = (n2, v2)"
          by (cases "(IF_Args f) ! i") auto
        from if_args_match i_lt len_fi fi_i if_i have "v1 = v2"
          by (auto simp: list_all2_conv_all_nth)
        thus "snd ((IF_Args f) ! i) = Ref \<longleftrightarrow> fst (snd (FI_TmArgs funInfo ! i)) = Ref"
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
        "length (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo)) = length idxs"
      proof -
        \<comment> \<open>Step 1: count Ref-positions in FI_TmArgs by indexing. \<close>
        have count_FI:
          "length (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo))
            = card {i. i < length (FI_TmArgs funInfo) \<and> fst (snd (FI_TmArgs funInfo ! i)) = Ref}"
        proof -
          have "length (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo))
                = card {i. i < length (FI_TmArgs funInfo) \<and>
                            (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo ! i)}"
            by (simp add: length_filter_conv_card)
          also have "\<dots> = card {i. i < length (FI_TmArgs funInfo) \<and>
                                  fst (snd (FI_TmArgs funInfo ! i)) = Ref}"
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
          "{i. i < length (FI_TmArgs funInfo) \<and> fst (snd (FI_TmArgs funInfo ! i)) = Ref}
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
               = Some (apply_subst tySubst (fst (FI_TmArgs funInfo ! (idxs ! j)))))"
      proof (intro allI impI)
        fix j assume j_lt: "j < length idxs"
        let ?i = "idxs ! j"
        from idxs_in_bound j_lt have i_lt_if: "?i < length (IF_Args f)" by blast
        with len_fi have i_lt_fi: "?i < length (FI_TmArgs funInfo)" by simp
        with len_argTms_fi have i_lt_argTms: "?i < length argTms" by simp
        from idxs_is_ref j_lt have if_i_ref: "snd ((IF_Args f) ! ?i) = Ref" by blast
        with vor_match i_lt_if have fi_i_ref: "fst (snd (FI_TmArgs funInfo ! ?i)) = Ref"
          by blast
        let ?paramTy_i = "fst (FI_TmArgs funInfo ! ?i)"

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
        have compose:
          "apply_subst tySubst ?paramTy_i
            = apply_subst (IS_TyArgs state)
                (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ?paramTy_i)"
          unfolding tySubst_def
          using apply_subst_compose_zip[OF ty_len[symmetric] paramTy_subset[OF i_lt_fi] ty_dist] .
        show "fst (?refs ! j) < length (IS_Store state) \<and>
              type_at_path env (storeTyping ! (fst (?refs ! j))) (snd (?refs ! j))
                = Some (apply_subst tySubst ?paramTy_i)"
          using lval_facts compose refs_j by simp
      qed

      \<comment> \<open>Define tys as the contract's expected type list for refUpdates. \<close>
      define tys :: "CoreType list" where
        tys_def: "tys = map (\<lambda>(ty, _). apply_subst tySubst ty)
                            (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo))"

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
        "filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo)
          = map (\<lambda>i. FI_TmArgs funInfo ! i)
                (filter (\<lambda>i. fst (snd (FI_TmArgs funInfo ! i)) = Ref)
                        [0 ..< length (FI_TmArgs funInfo)])"
        using filter_via_indices[where P = "\<lambda>(_, vor, _). vor = Ref"
                                   and xs = "FI_TmArgs funInfo"]
        by (auto simp: case_prod_unfold)

      \<comment> \<open>idxs_FI = idxs (via vor_match + len_fi). \<close>
      have idxs_FI_eq_idxs:
        "filter (\<lambda>i. fst (snd (FI_TmArgs funInfo ! i)) = Ref)
                [0 ..< length (FI_TmArgs funInfo)]
          = idxs"
      proof -
        have len_upt: "[0 ..< length (FI_TmArgs funInfo)] = [0 ..< length (IF_Args f)]"
          using len_fi by simp
        have pred_eq:
          "\<And>i. i < length (IF_Args f) \<Longrightarrow>
                fst (snd (FI_TmArgs funInfo ! i)) = Ref
                \<longleftrightarrow> snd ((IF_Args f) ! i) = Ref"
          using vor_match by blast
        have "filter (\<lambda>i. fst (snd (FI_TmArgs funInfo ! i)) = Ref)
                     [0 ..< length (FI_TmArgs funInfo)]
            = filter (\<lambda>i. fst (snd (FI_TmArgs funInfo ! i)) = Ref)
                     [0 ..< length (IF_Args f)]"
          using len_upt by simp
        also have "\<dots> = filter (\<lambda>i. snd ((IF_Args f) ! i) = Ref)
                                [0 ..< length (IF_Args f)]"
          using pred_eq by (intro filter_cong) auto
        finally show ?thesis unfolding idxs_def .
      qed

      have fi_filter_eq:
        "filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo)
          = map (\<lambda>i. FI_TmArgs funInfo ! i) idxs"
        using fi_filter_indexed idxs_FI_eq_idxs by simp

      have tys_nth:
        "\<forall>j < length idxs. tys ! j
          = apply_subst tySubst (fst (FI_TmArgs funInfo ! (idxs ! j)))"
      proof (intro allI impI)
        fix j assume j_lt: "j < length idxs"
        have "tys ! j
            = ((map (\<lambda>(ty, _). apply_subst tySubst ty)
                    (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo))) ! j)"
          unfolding tys_def by simp
        also have "\<dots> = ((map (\<lambda>(ty, _). apply_subst tySubst ty)
                              (map (\<lambda>i. FI_TmArgs funInfo ! i) idxs)) ! j)"
          using fi_filter_eq by simp
        also have "\<dots> = (\<lambda>(ty, _). apply_subst tySubst ty)
                          ((map (\<lambda>i. FI_TmArgs funInfo ! i) idxs) ! j)"
          using j_lt by simp
        also have "\<dots> = (\<lambda>(ty, _). apply_subst tySubst ty)
                          (FI_TmArgs funInfo ! (idxs ! j))"
          using j_lt by simp
        also have "\<dots> = apply_subst tySubst (fst (FI_TmArgs funInfo ! (idxs ! j)))"
          by (simp add: case_prod_beta)
        finally show "tys ! j
                        = apply_subst tySubst (fst (FI_TmArgs funInfo ! (idxs ! j)))" .
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
            = length (map (\<lambda>(ty, _). apply_subst tySubst ty)
                          (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo)))"
          by (auto dest: list_all2_lengthD)
        from ref_updates_typed j_lt have
          "value_has_type env (refUpdates ! j)
             ((map (\<lambda>(ty, _). apply_subst tySubst ty)
                   (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo))) ! j)"
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
      \<comment> \<open>state_matches_env does not read IS_World. \<close>
      have sme_stateW: "state_matches_env ?stateW env storeTyping"
        using state_env by simp

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
        "interp_function_call d (Suc fuel) state fnName tyArgs argTms
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
          "interp_function_call d (Suc fuel) state fnName tyArgs argTms = Inl err" by simp
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

(* ========================================================================== *)
(* Soundness of default_value                                                  *)
(* ========================================================================== *)

(* Helper: every value produced by replicating one element across all indices
   of a multi-dimensional array has the element's type. The fmap is built by
   zipping the all_indices list with replicate (length idxs) ev. *)
lemma default_array_fmap_typed:
  fixes ev :: CoreValue
  assumes "value_has_type env ev elemTy"
  shows "\<forall>idx val.
          fmlookup (fmap_of_list (map (\<lambda>i. (i, ev)) (all_indices sizes))) idx = Some val
            \<longrightarrow> value_has_type env val elemTy"
proof (intro allI impI)
  fix idx val
  assume lk: "fmlookup (fmap_of_list (map (\<lambda>i. (i, ev)) (all_indices sizes))) idx = Some val"
  hence "map_of (map (\<lambda>i. (i, ev)) (all_indices sizes)) idx = Some val"
    by (simp add: fmlookup_of_list)
  hence "(idx, val) \<in> set (map (\<lambda>i. (i, ev)) (all_indices sizes))"
    by (rule map_of_SomeD)
  hence "val = ev" by auto
  with assms show "value_has_type env val elemTy" by simp
qed

(* Helper: the fmap built by tagging all_indices with ev has domain exactly
   the all_indices fset. *)
lemma default_array_fmap_dom:
  "fmdom (fmap_of_list (map (\<lambda>i. (i, ev)) (all_indices sizes)))
     = fset_of_list (all_indices sizes)"
  by (simp add: comp_def)

(* Helper: fixed_dim_sizes on an all-Fixed list extracts the sizes and has
   the right length. *)
lemma fixed_dim_sizes_length:
  "list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims
     \<Longrightarrow> length (fixed_dim_sizes dims) = length dims"
  by (induction dims rule: fixed_dim_sizes.induct) auto

lemma fixed_dim_sizes_match_dims:
  "list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims
     \<Longrightarrow> sizes_match_dims (fixed_dim_sizes dims) dims"
  by (induction dims rule: fixed_dim_sizes.induct) auto

lemma fixed_dim_sizes_valid:
  assumes "array_dims_well_kinded dims"
      and "list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims"
  shows "sizes_valid (fixed_dim_sizes dims)"
proof -
  from assms have all_fixed: "list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims" by simp
  from assms(1) have all_in_range: "list_all dim_in_range dims"
    unfolding array_dims_well_kinded_def by simp
  show ?thesis
    using all_fixed all_in_range
  proof (induction dims rule: fixed_dim_sizes.induct)
    case 1 then show ?case by (simp add: sizes_valid_def)
  next
    case (2 n ds)
    from "2.prems"(2) have n_in: "dim_in_range (CoreDim_Fixed n)" by simp
    from "2.prems"(2) have rest_in: "list_all dim_in_range ds" by simp
    from "2.prems"(1) have rest_fixed: "list_all (\<lambda>d. dim_category d = DimCat_Fixed) ds" by simp
    from "2.IH"[OF rest_fixed rest_in] have rec: "sizes_valid (fixed_dim_sizes ds)" .
    from n_in have "int_in_range (int_range Unsigned IntBits_64) n" by simp
    hence "n \<ge> 0 \<and> n \<le> snd (int_range Unsigned IntBits_64)"
      by (cases "int_range Unsigned IntBits_64") simp
    with rec show ?case by (simp add: sizes_valid_def)
  qed auto
qed

(* Allocatable / Unknown branch: sizes_match_dims with replicate-zero sizes
   holds because every dim is non-Fixed (dims_uniform from array_dims_well_kinded
   ensures uniformity, so if one is non-Fixed they all are). *)
lemma sizes_match_dims_replicate_zero:
  assumes "array_dims_well_kinded dims"
      and "\<not> list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims"
  shows "sizes_match_dims (replicate (length dims) 0) dims"
proof -
  from assms(1) have uniform: "dims_uniform dims"
    and nonempty: "dims \<noteq> []"
    unfolding array_dims_well_kinded_def by simp_all
  from assms(2) obtain d where d_in: "d \<in> set dims"
                            and d_notFixed: "dim_category d \<noteq> DimCat_Fixed"
    by (auto simp: list_all_iff)
  \<comment> \<open>All dims share the same category. \<close>
  have all_same_pairwise: "\<forall>d1 \<in> set dims. \<forall>d2 \<in> set dims. dim_category d1 = dim_category d2"
    using uniform
  proof (induction dims rule: dims_uniform.induct)
    case 1 then show ?case by simp
  next
    case (2 d') then show ?case by simp
  next
    case (3 d1 d2 ds)
    from "3.prems" have cat_eq: "dim_category d1 = dim_category d2"
      and rest_uniform: "dims_uniform (d2 # ds)" by simp_all
    from "3.IH"[OF rest_uniform]
    have rest_pairwise: "\<forall>x \<in> set (d2 # ds). \<forall>y \<in> set (d2 # ds). dim_category x = dim_category y" .
    show ?case
    proof (intro ballI)
      fix x y
      assume x_in: "x \<in> set (d1 # d2 # ds)" and y_in: "y \<in> set (d1 # d2 # ds)"
      have d2_cat: "\<And>z. z \<in> set (d2 # ds) \<Longrightarrow> dim_category z = dim_category d2"
        using rest_pairwise by auto
      have d1_cat: "dim_category d1 = dim_category d2" using cat_eq .
      have x_cat: "dim_category x = dim_category d2"
      proof (cases "x = d1")
        case True with d1_cat show ?thesis by simp
      next
        case False with x_in have "x \<in> set (d2 # ds)" by simp
        thus ?thesis by (rule d2_cat)
      qed
      have y_cat: "dim_category y = dim_category d2"
      proof (cases "y = d1")
        case True with d1_cat show ?thesis by simp
      next
        case False with y_in have "y \<in> set (d2 # ds)" by simp
        thus ?thesis by (rule d2_cat)
      qed
      from x_cat y_cat show "dim_category x = dim_category y" by simp
    qed
  qed
  have all_same_cat: "\<forall>d' \<in> set dims. dim_category d' = dim_category d"
    using all_same_pairwise d_in by blast
  with d_notFixed have all_non_fixed: "\<forall>d' \<in> set dims. dim_category d' \<noteq> DimCat_Fixed"
    by auto
  show ?thesis
    using all_non_fixed
  proof (induction dims)
    case Nil then show ?case by simp
  next
    case (Cons d' rest)
    from Cons.prems have d'_non_fixed: "dim_category d' \<noteq> DimCat_Fixed" by simp
    from Cons.prems have rest_non_fixed: "\<forall>d'' \<in> set rest. dim_category d'' \<noteq> DimCat_Fixed" by simp
    from Cons.IH[OF rest_non_fixed]
    have rec: "sizes_match_dims (replicate (length rest) 0) rest" .
    show ?case
    proof (cases d')
      case CoreDim_Unknown
      with rec show ?thesis by simp
    next
      case CoreDim_Allocatable
      with rec show ?thesis by simp
    next
      case (CoreDim_Fixed n)
      with d'_non_fixed show ?thesis by simp
    qed
  qed
qed

(* Allocatable/Unknown branch: with sizes = replicate (length dims) 0, the
   index set is empty (some dim is 0), so fmempty matches. *)
lemma all_indices_replicate_zero_empty:
  assumes "dims \<noteq> []"
  shows "all_indices (replicate (length dims) 0) = []"
proof -
  from assms obtain d ds where dims_eq: "dims = d # ds" by (cases dims) auto
  hence rep_eq: "replicate (length dims) 0 = 0 # replicate (length ds) 0" by simp
  have "all_indices (0 # replicate (length ds) 0) = []"
    by (simp add: Let_def)
  with rep_eq show ?thesis by metis
qed

lemma fmap_matches_sizes_empty_replicate:
  assumes "dims \<noteq> []"
  shows "fmap_matches_sizes (replicate (length dims) 0) fmempty"
proof -
  have sv: "sizes_valid (replicate (length dims) 0)"
    by (simp add: sizes_valid_def list_all_iff)
  have empty: "all_indices (replicate (length dims) 0) = []"
    using all_indices_replicate_zero_empty[OF assms] .
  show ?thesis by (simp add: fmap_matches_sizes_def sv empty)
qed

(* Main soundness theorem for default_value.

   Statement: under state_matches_env and tyenv_well_formed, evaluating
   default_value on a well-kinded, ground type yields either a
   sound error or a CoreValue whose type matches.

   Proved by mutual induction following default_value_default_value_list.induct.
*)
lemma default_value_sound:
  shows default_value_sound_main:
          "state_matches_env (state :: 'w InterpState) env storeTyping \<Longrightarrow>
           tyenv_well_formed env \<Longrightarrow>
           is_well_kinded env ty \<Longrightarrow>
           type_tyvars ty = {} \<Longrightarrow>
           (case default_value fuel state ty of
              Inl err \<Rightarrow> sound_error_result err
            | Inr val \<Rightarrow> value_has_type env val ty)"
    and default_value_list_sound_main:
          "state_matches_env (state :: 'w InterpState) env storeTyping \<Longrightarrow>
           tyenv_well_formed env \<Longrightarrow>
           list_all (is_well_kinded env) tys \<Longrightarrow>
           list_all (\<lambda>ty. type_tyvars ty = {}) tys \<Longrightarrow>
           (case default_value_list fuel state tys of
              Inl err \<Rightarrow> sound_error_result err
            | Inr vals \<Rightarrow> list_all2 (value_has_type env) vals tys)"
proof (induction rule: default_value_default_value_list.induct)
  case (1 uu uv) then show ?case by simp
next
  \<comment> \<open>Bool: trivial. \<close>
  case (2 uw ux)
  then show ?case by simp
next
  \<comment> \<open>FiniteInt: zero fits. \<close>
  case (3 uy uz sign bits)
  have "int_fits sign bits 0"
    by (cases sign; cases bits; simp)
  then show ?case by simp
next
  \<comment> \<open>Record: recurse on field types via default_value_list. \<close>
  case (4 fuel state flds)
  from "4.prems"(3) have
    distinct_names: "distinct (map fst flds)" and
    flds_wk: "list_all (is_well_kinded env) (map snd flds)"
    by simp_all
  from "4.prems"(4) have flds_ground: "list_all (\<lambda>ty. type_tyvars ty = {}) (map snd flds)"
    by (auto simp: list_all_iff case_prod_beta)
  from "4.IH"[OF "4.prems"(1,2) flds_wk flds_ground]
  have IH_list: "case default_value_list fuel state (map snd flds) of
                   Inl err \<Rightarrow> sound_error_result err
                 | Inr vals \<Rightarrow> list_all2 (value_has_type env) vals (map snd flds)" .
  show ?case
  proof (cases "default_value_list fuel state (map snd flds)")
    case (Inl err)
    with IH_list show ?thesis by simp
  next
    case (Inr vals)
    with IH_list have vals_typed:
      "list_all2 (value_has_type env) vals (map snd flds)" by simp
    have len_eq: "length vals = length flds"
      using vals_typed by (auto dest: list_all2_lengthD)
    let ?fieldVals = "zip (map fst flds) vals"
    have len_pairs: "length ?fieldVals = length flds" using len_eq by simp
    have fst_eq: "map fst ?fieldVals = map fst flds"
      using len_eq by simp
    have rec_typed: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t)
                       ?fieldVals flds"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length ?fieldVals = length flds" using len_pairs .
    next
      fix i assume i_lt: "i < length ?fieldVals"
      hence i_lt': "i < length flds" using len_pairs by simp
      from vals_typed i_lt' len_eq
      have "value_has_type env (vals ! i) (map snd flds ! i)"
        by (simp add: list_all2_conv_all_nth)
      hence v_typed: "value_has_type env (vals ! i) (snd (flds ! i))"
        using i_lt' by simp
      have "?fieldVals ! i = (fst (flds ! i), vals ! i)"
        using i_lt' len_eq by simp
      then show "(case ?fieldVals ! i of (n1, v) \<Rightarrow>
                   \<lambda>(n2, t). n1 = n2 \<and> value_has_type env v t) (flds ! i)"
        using v_typed by (cases "flds ! i"; simp)
    qed
    have "value_has_type env (CV_Record ?fieldVals) (CoreTy_Record flds)"
      using distinct_names rec_typed by simp
    with Inr show ?thesis by simp
  qed
next
  \<comment> \<open>Datatype: look up the first ctor in IS_DataCtorsByType and its payload in
      IS_DataCtors, recurse on the payload. \<close>
  case (5 fuel state dtName tyArgs)
  from "5.prems"(3) obtain numTyArgs where
    dt_lookup: "fmlookup (TE_Datatypes env) dtName = Some numTyArgs" and
    len_args: "length tyArgs = numTyArgs" and
    args_wk: "list_all (is_well_kinded env) tyArgs"
    by (auto split: option.splits)
  from "5.prems"(4) have args_ground: "\<forall>arg \<in> set tyArgs. type_tyvars arg = {}" by auto

  \<comment> \<open>tyenv_datatypes_nonempty + tyenv_first_ctor_consistent give us the first ctor. \<close>
  from "5.prems"(2) have wf: "tyenv_well_formed env" .
  from wf have dt_ne: "tyenv_datatypes_nonempty env"
    unfolding tyenv_well_formed_def by simp
  from tyenv_datatypes_nonempty_first_ctor[OF dt_ne fmdomI[OF dt_lookup]]
  obtain ctorName otherCtors where
    ctors_lookup: "fmlookup (TE_DataCtorsByType env) dtName = Some (ctorName # otherCtors)"
    by blast
  from tyenv_first_ctor_consistent[OF wf ctors_lookup] obtain tyvars payload where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payload)"
    by blast

  \<comment> \<open>tables_match gives us the state's lookups. \<close>
  from "5.prems"(1) have tm: "tables_match state env"
    unfolding state_matches_env_def by simp
  \<comment> \<open>The matched env has no unresolved abstract types, so the payload-well-kinded
      and payload-runtime env shapes collapse to the ctor's own tyvars. \<close>
  from "5.prems"(1) have abs_empty: "TE_AbstractTypes env = {||}"
    unfolding state_matches_env_def by blast
  have bt_lookup: "fmlookup (IS_DataCtorsByType state) dtName = Some (ctorName # otherCtors)"
    using tm ctors_lookup unfolding tables_match_def by simp
  have dc_lookup: "fmlookup (IS_DataCtors state) ctorName = Some (dtName, tyvars, payload)"
    using tm ctor_lookup unfolding tables_match_def by simp

  \<comment> \<open>tyenv_ctors_consistent gives length tyvars = numTyArgs = length tyArgs. \<close>
  from wf have ctors_cons: "tyenv_ctors_consistent env"
    unfolding tyenv_well_formed_def by simp
  from ctors_cons ctor_lookup dt_lookup
  have len_tyvars: "length tyvars = length tyArgs"
    using len_args unfolding tyenv_ctors_consistent_def by force

  \<comment> \<open>tyenv_payloads_well_kinded: payload is well-kinded in env-with-tyvars. \<close>
  from wf have pwk: "tyenv_payloads_well_kinded env"
    unfolding tyenv_well_formed_def by simp
  from pwk ctor_lookup
  have payload_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payload"
    unfolding tyenv_payloads_well_kinded_def by (simp add: abs_empty)

  \<comment> \<open>Substituted payload is well-kinded in env. \<close>
  let ?subst = "fmap_of_list (zip tyvars tyArgs)"
  let ?substPayload = "apply_subst ?subst payload"
  have substPayload_wk: "is_well_kinded env ?substPayload"
    using abs_empty apply_subst_specializes_well_kinded args_wk len_tyvars payload_wk
    by auto

  \<comment> \<open>Groundness of the substituted payload: payload's free tyvars are within
      set tyvars (so dom subst covers them), and the subst's range is ground
      because tyArgs are. \<close>
  have payload_tyvars: "type_tyvars payload \<subseteq> fset (fset_of_list tyvars)"
    using is_well_kinded_type_tyvars_subset[OF payload_wk] by simp
  have subst_dom: "fmdom ?subst = fset_of_list tyvars"
    using len_tyvars by simp
  have subst_range_ground: "subst_range_tyvars ?subst = {}"
  proof -
    have "\<And>ty'. ty' \<in> fmran' ?subst \<Longrightarrow> type_tyvars ty' = {}"
    proof -
      fix ty' assume "ty' \<in> fmran' ?subst"
      then obtain n where "fmlookup ?subst n = Some ty'" by (auto simp: fmran'_alt_def)
      hence "(n, ty') \<in> set (zip tyvars tyArgs)"
        by (meson fmap_of_list_SomeD)
      hence "ty' \<in> set tyArgs" using set_zip_rightD by metis
      with args_ground show "type_tyvars ty' = {}" by simp
    qed
    thus ?thesis unfolding subst_range_tyvars_def by simp
  qed
  have substPayload_ground: "type_tyvars ?substPayload = {}"
  proof -
    have "type_tyvars ?substPayload \<subseteq>
            (type_tyvars payload - fset (fmdom ?subst)) \<union> subst_range_tyvars ?subst"
      by (rule apply_subst_tyvars_result)
    also have "... \<subseteq> {}"
      using payload_tyvars subst_dom subst_range_ground by auto
    finally show ?thesis by simp
  qed

  \<comment> \<open>Apply the IH to the substituted payload type. The IH requires the ctor
      list and the triple to be presented as nested equations, one per
      case/pair destructuring in default_value. \<close>
  obtain ctors where ctors_def: "ctors = ctorName # otherCtors" by simp
  obtain triple where triple_def: "triple = (dtName, tyvars, payload)" by simp
  obtain rest where rest_def: "rest = (tyvars, payload)" by simp
  have bt_lookup': "fmlookup (IS_DataCtorsByType state) dtName = Some ctors"
    using bt_lookup ctors_def by simp
  have dc_lookup': "fmlookup (IS_DataCtors state) ctorName = Some triple"
    using dc_lookup triple_def by simp
  have pair1: "(dtName, rest) = triple" using triple_def rest_def by simp
  have pair2: "(tyvars, payload) = rest" using rest_def by simp
  have IH_payload: "case default_value fuel state ?substPayload of
                      Inl err \<Rightarrow> sound_error_result err
                    | Inr v \<Rightarrow> value_has_type env v ?substPayload"
    using "5.IH" "5.prems"(1) bt_lookup' ctors_def dc_lookup' len_tyvars local.wf pair1 rest_def
      substPayload_ground substPayload_wk by auto

  show ?case
  proof (cases "default_value fuel state ?substPayload")
    case (Inl err)
    with IH_payload bt_lookup dc_lookup len_tyvars show ?thesis by (simp add: Let_def)
  next
    case (Inr v)
    with IH_payload have v_typed: "value_has_type env v ?substPayload" by simp
    \<comment> \<open>Build value_has_type for the variant. \<close>
    have ty_args_ground: "list_all (\<lambda>a. type_tyvars a = {}) tyArgs"
      using args_ground by (simp add: list_all_iff)
    have value_typed:
      "value_has_type env (CV_Variant ctorName v) (CoreTy_Datatype dtName tyArgs)"
      using ctor_lookup len_tyvars args_wk ty_args_ground v_typed
      by (simp split: option.splits)
    from bt_lookup dc_lookup len_tyvars Inr value_typed
    show ?thesis by (simp add: Let_def)
  qed
next
  \<comment> \<open>Array: two branches (all-Fixed, else). \<close>
  case (6 fuel state elemTy dims)
  from "6.prems"(3) have
    elem_wk: "is_well_kinded env elemTy" and
    dims_wk: "array_dims_well_kinded dims"
    by simp_all
  from "6.prems"(4) have elem_ground: "type_tyvars elemTy = {}" by simp
  from dims_wk have dims_nonempty: "dims \<noteq> []"
    unfolding array_dims_well_kinded_def by simp

  show ?case
  proof (cases "list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims")
    case True
    let ?sizes = "fixed_dim_sizes dims"
    from "6.IH"(1)[OF True refl "6.prems"(1,2) elem_wk elem_ground]
    have IH_elem: "case default_value fuel state elemTy of
                     Inl err \<Rightarrow> sound_error_result err
                   | Inr ev \<Rightarrow> value_has_type env ev elemTy" .
    show ?thesis
    proof (cases "default_value fuel state elemTy")
      case (Inl err)
      with IH_elem True show ?thesis by (simp add: Let_def)
    next
      case (Inr ev)
      with IH_elem have ev_typed: "value_has_type env ev elemTy" by simp
      let ?fm = "fmap_of_list (map (\<lambda>i. (i, ev)) (all_indices ?sizes))"
      have fms: "fmap_matches_sizes ?sizes ?fm"
        unfolding fmap_matches_sizes_def
        using fixed_dim_sizes_valid[OF dims_wk True] default_array_fmap_dom by simp
      have smd: "sizes_match_dims ?sizes dims"
        using fixed_dim_sizes_match_dims[OF True] .
      have fm_vals_typed:
        "\<forall>idx val. fmlookup ?fm idx = Some val \<longrightarrow> value_has_type env val elemTy"
        by (rule default_array_fmap_typed[OF ev_typed])
      have value_typed:
        "value_has_type env (CV_Array ?sizes ?fm) (CoreTy_Array elemTy dims)"
        using elem_wk elem_ground fm_vals_typed dims_wk fms smd
        by simp
      from True Inr value_typed
      show ?thesis by (simp add: Let_def)
    qed
  next
    case False
    let ?sizes = "replicate (length dims) (0::int)"
    have fms: "fmap_matches_sizes ?sizes fmempty"
      using fmap_matches_sizes_empty_replicate[OF dims_nonempty] .
    have smd: "sizes_match_dims ?sizes dims"
      using sizes_match_dims_replicate_zero[OF dims_wk False] .
    have value_typed:
      "value_has_type env (CV_Array ?sizes fmempty) (CoreTy_Array elemTy dims)"
      using elem_wk elem_ground dims_wk fms smd by simp
    from False value_typed
    show ?thesis by simp
  qed
next
  \<comment> \<open>MathInt: the default is zero. \<close>
  case (7 va vb)
  then show ?case by simp
next
  \<comment> \<open>MathReal: the default is zero. \<close>
  case (8 vc vd)
  then show ?case by simp
next
  \<comment> \<open>Var: not ground, contradicts prems. \<close>
  case (9 ve vf vg)
  then show ?case by simp
next
  \<comment> \<open>default_value_list 0: out of fuel. \<close>
  case (10 vh vi)
  then show ?case by simp
next
  \<comment> \<open>default_value_list (Suc _) []: trivial. \<close>
  case (11 vj vk)
  then show ?case by simp
next
  \<comment> \<open>default_value_list cons. \<close>
  case (12 fuel state ty tys)
  from "12.prems"(3) have ty_wk: "is_well_kinded env ty"
    and tys_wk: "list_all (is_well_kinded env) tys" by simp_all
  from "12.prems"(4) have ty_ground: "type_tyvars ty = {}"
    and tys_ground: "list_all (\<lambda>t. type_tyvars t = {}) tys" by simp_all
  from "12.IH"(1)[OF "12.prems"(1,2) ty_wk ty_ground]
  have IH_head: "case default_value fuel state ty of
                   Inl err \<Rightarrow> sound_error_result err
                 | Inr v \<Rightarrow> value_has_type env v ty" .
  show ?case
  proof (cases "default_value fuel state ty")
    case (Inl err)
    with IH_head show ?thesis by simp
  next
    case (Inr v)
    with IH_head have v_typed: "value_has_type env v ty" by simp
    from "12.IH"(2)[OF Inr "12.prems"(1,2) tys_wk tys_ground]
    have IH_tail: "case default_value_list fuel state tys of
                     Inl err \<Rightarrow> sound_error_result err
                   | Inr vs \<Rightarrow> list_all2 (value_has_type env) vs tys" by simp
    show ?thesis
    proof (cases "default_value_list fuel state tys")
      case Inl2: (Inl err)
      with IH_tail Inr show ?thesis by simp
    next
      case Inr2: (Inr vs)
      with IH_tail have vs_typed: "list_all2 (value_has_type env) vs tys" by simp
      from Inr Inr2 v_typed vs_typed
      show ?thesis by simp
    qed
  qed
qed


(* Wrapper used at the top-level cases tm branch of type_soundness. *)
lemma type_soundness_default:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and typing: "core_term_type env Ghost (CoreTm_Default ty) = Some ty'"
  shows "sound_term_result state env ty' (interp_term d (Suc fuel) state (CoreTm_Default ty))"
proof -
  from typing have
    wk: "is_well_kinded env ty" and
    ty_eq: "ty' = ty"
    by (auto split: if_splits)
  let ?gty = "apply_subst (IS_TyArgs state) ty"
  have gty_wk: "is_well_kinded env ?gty"
    using is_well_kinded_apply_IS_TyArgs[OF state_env wk] .
  have gty_ground: "type_tyvars ?gty = {}"
    using is_well_kinded_apply_IS_TyArgs_ground[OF state_env wk] .
  have interp_eq:
    "interp_term d (Suc fuel) state (CoreTm_Default ty) = default_value fuel state ?gty"
    by simp
  from default_value_sound_main[OF state_env wf_env gty_wk gty_ground]
  have sound: "case default_value fuel state ?gty of
                 Inl err \<Rightarrow> sound_error_result err
               | Inr val \<Rightarrow> value_has_type env val ?gty" .
  show ?thesis
  proof (cases "default_value fuel state ?gty")
    case (Inl err)
    with sound interp_eq ty_eq show ?thesis by simp
  next
    case (Inr val)
    with sound interp_eq ty_eq
    have "value_has_type env val ?gty" by simp
    with Inr interp_eq ty_eq show ?thesis by simp
  qed
qed


(* ========================================================================== *)
(* Allocated *)
(* ========================================================================== *)

(* any_allocated succeeds whenever every component check succeeded. *)
lemma any_allocated_Inr:
  assumes "\<forall>r \<in> set rs. \<exists>b. r = Inr b"
  shows "\<exists>b. any_allocated rs = Inr b"
using assms proof (induction rs)
  case Nil show ?case by (rule exI[of _ False]) simp
next
  case (Cons r rs)
  from Cons.prems obtain b where r_eq: "r = Inr b" by auto
  from Cons obtain b' where rest_eq: "any_allocated rs = Inr b'" by auto
  show ?case using r_eq rest_eq by simp
qed

(* is_allocated never fails on a well-typed value, provided the constructor
   table is the one the value was typed against. Groundness is not needed:
   is_allocated only fails on a type variable or an unknown constructor, and
   value_has_type already rules out both. *)
lemma is_allocated_sound:
  assumes "value_has_type env val ty"
      and "ctors = TE_DataCtors env"
  shows "\<exists>b. is_allocated ctors val ty = Inr b"
using assms proof (induction val arbitrary: ty)
  case (CV_Bool b) show ?case by (rule exI[of _ False]) simp
next
  case (CV_FiniteInt sign bits i) show ?case by (rule exI[of _ False]) simp
next
  case (CV_Int i) show ?case by (rule exI[of _ False]) simp
next
  case (CV_Real r) show ?case by (rule exI[of _ False]) simp
next
  case (CV_Record fieldValues)
  from CV_Record.prems(1) obtain fieldTypes where
    ty_eq: "ty = CoreTy_Record fieldTypes" and
    all2: "list_all2 (\<lambda>(name1, fldVal) (name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
             fieldValues fieldTypes"
    by (cases ty) auto
  have IH: "\<And>v t. v \<in> snd ` set fieldValues \<Longrightarrow> value_has_type env v t \<Longrightarrow>
              \<exists>b. is_allocated ctors v t = Inr b"
    using CV_Record.IH CV_Record.prems(2) by auto
  have each: "\<forall>r \<in> set (map (\<lambda>p. is_allocated ctors (snd (fst p)) (snd (snd p)))
                              (zip fieldValues fieldTypes)). \<exists>b. r = Inr b"
  proof
    fix r assume "r \<in> set (map (\<lambda>p. is_allocated ctors (snd (fst p)) (snd (snd p)))
                              (zip fieldValues fieldTypes))"
    then obtain p where p_in: "p \<in> set (zip fieldValues fieldTypes)" and
      r_eq: "r = is_allocated ctors (snd (fst p)) (snd (snd p))" by auto
    from p_in obtain i where
      fv_i: "fieldValues ! i = fst p" and ft_i: "fieldTypes ! i = snd p" and
      i_lt: "i < length fieldValues"
      by (auto simp: in_set_zip)
    from list_all2_nthD[OF all2 i_lt] fv_i ft_i
    have typed: "value_has_type env (snd (fst p)) (snd (snd p))"
      by (auto simp: case_prod_beta)
    from p_in have "fst p \<in> set fieldValues" by (metis set_zip_leftD prod.collapse)
    hence "snd (fst p) \<in> snd ` set fieldValues" by simp
    from IH[OF this typed] r_eq show "\<exists>b. r = Inr b" by simp
  qed
  show ?case using ty_eq any_allocated_Inr[OF each] by simp
next
  case (CV_Variant ctor payload)
  from CV_Variant.prems(1) obtain dtName argTypes tyvars payloadTy where
    ty_eq: "ty = CoreTy_Datatype dtName argTypes" and
    lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyvars = length argTypes" and
    payload_typed: "value_has_type env payload
                      (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
    by (cases ty) (auto split: option.splits prod.splits)
  from CV_Variant.IH[OF payload_typed CV_Variant.prems(2)]
  show ?case using ty_eq lookup CV_Variant.prems(2) len_eq by simp
next
  case (CV_Array sizes valuesMap)
  from CV_Array.prems(1) obtain elemTy dims where
    ty_eq: "ty = CoreTy_Array elemTy dims" and
    elems_typed: "\<forall>idx v. fmlookup valuesMap idx = Some v \<longrightarrow> value_has_type env v elemTy" and
    fms: "fmap_matches_sizes sizes valuesMap"
    by (cases ty) auto
  have IH: "\<And>v t. v \<in> fmran' valuesMap \<Longrightarrow> value_has_type env v t \<Longrightarrow>
              \<exists>b. is_allocated ctors v t = Inr b"
    using CV_Array.IH CV_Array.prems(2) by auto
  show ?case
  proof (cases "list_ex (\<lambda>d. d = CoreDim_Allocatable) dims")
    case True
    with ty_eq show ?thesis by simp
  next
    case False
    let ?check = "\<lambda>idx. case fmlookup valuesMap idx of
                          Some v \<Rightarrow> is_allocated ctors v elemTy
                        | None \<Rightarrow> Inl TypeError"
    have each: "\<forall>r \<in> set (map ?check (all_indices sizes)). \<exists>b. r = Inr b"
    proof
      fix r assume "r \<in> set (map ?check (all_indices sizes))"
      then obtain idx where idx_in: "idx \<in> set (all_indices sizes)" and
        r_eq: "r = ?check idx" by auto
      from idx_in fms have "idx |\<in>| fmdom valuesMap"
        by (simp add: fmap_matches_sizes_def fset_of_list_elem)
      then obtain v where lk: "fmlookup valuesMap idx = Some v"
        by (cases "fmlookup valuesMap idx") (auto dest: fmdom_notI)
      from elems_typed lk have typed: "value_has_type env v elemTy" by blast
      from lk have "v \<in> fmran' valuesMap" by (rule fmran'I)
      from IH[OF this typed] r_eq lk show "\<exists>b. r = Inr b" by simp
    qed
    show ?thesis using ty_eq False any_allocated_Inr[OF each] by simp
  qed
qed

(* Wrapper used at the top-level cases tm branch of type_soundness. The
   annotation is the operand's type in env, so the operand's value has the
   IS_TyArgs-resolved annotation type, which is exactly the type the
   interpreter hands to is_allocated. *)
lemma type_soundness_allocated:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and IH: "\<And>tm' ty'. core_term_type env Ghost tm' = Some ty' \<Longrightarrow>
                        sound_term_result state env ty' (interp_term d fuel state tm')"
    and typing: "core_term_type env Ghost (CoreTm_Allocated annTy tm) = Some ty"
  shows "sound_term_result state env ty (interp_term d (Suc fuel) state (CoreTm_Allocated annTy tm))"
proof -
  from typing have
    tm_typing: "core_term_type env Ghost tm = Some annTy" and
    ty_eq: "ty = CoreTy_Bool"
    by (auto split: option.splits if_splits)
  from IH[OF tm_typing]
  have tm_sound: "sound_term_result state env annTy (interp_term d fuel state tm)" .
  from state_env have dc: "IS_DataCtors state = TE_DataCtors env"
    unfolding state_matches_env_def tables_match_def by simp
  show ?thesis
  proof (cases "interp_term d fuel state tm")
    case (Inl err)
    then have "interp_term d (Suc fuel) state (CoreTm_Allocated annTy tm) = Inl err" by simp
    with tm_sound Inl show ?thesis by simp
  next
    case (Inr val)
    with tm_sound have val_typed:
      "value_has_type env val (apply_subst (IS_TyArgs state) annTy)" by simp
    from is_allocated_sound[OF val_typed dc] obtain b where
      alloc: "is_allocated (IS_DataCtors state) val (apply_subst (IS_TyArgs state) annTy) = Inr b"
      by blast
    have "interp_term d (Suc fuel) state (CoreTm_Allocated annTy tm) = Inr (CV_Bool b)"
      using Inr alloc by simp
    with ty_eq show ?thesis by simp
  qed
qed


(* Soundness of apply_cast_opt: the optional cast applied to an impure call's
   return value (CoreStmt_AssignCall / CoreStmt_VarDeclCall). If the call
   return value is well-typed at the (substituted) return type, and the typecheck
   accepted the cast (cast_result_type ... = Some resTy), then a successful cast
   yields a value well-typed at the (substituted) result type. A corollary of
   cast_value_sound. *)
lemma apply_cast_opt_sound:
  assumes cast: "apply_cast_opt castOpt retVal = Inr castVal"
      and rt_ct: "cast_result_type env ghost retTy castOpt = Some resTy"
      and retVal_typed: "value_has_type env retVal (apply_subst subst retTy)"
  shows "value_has_type env castVal (apply_subst subst resTy)"
proof (cases castOpt)
  case None
  with rt_ct have "resTy = retTy" by (simp add: cast_result_type_def)
  moreover from None cast have "castVal = retVal" by simp
  ultimately show ?thesis using retVal_typed by simp
next
  case (Some t)
  from Some rt_ct have co: "cast_ok env retTy t" and resTy_eq: "resTy = t"
    by (auto simp: cast_result_type_def split: if_splits)
  from cast Some have cv: "cast_value t retVal = Inr castVal" by simp
  from cast_value_sound[OF cv co retVal_typed] show ?thesis
    using resTy_eq by simp
qed

(* A failed apply_cast_opt on a well-typed call return value is a
   RuntimeError, never a TypeError: a corollary of
   cast_value_error_is_runtime. *)
lemma apply_cast_opt_error_is_runtime:
  assumes cast: "apply_cast_opt castOpt retVal = Inl err"
      and rt_ct: "cast_result_type env ghost retTy castOpt = Some resTy"
      and retVal_typed: "value_has_type env retVal (apply_subst subst retTy)"
  shows "err = RuntimeError"
proof (cases castOpt)
  case None
  with cast show ?thesis by simp
next
  case (Some t)
  from Some rt_ct have co: "cast_ok env retTy t" and resTy_eq: "resTy = t"
    by (auto simp: cast_result_type_def split: if_splits)
  from cast Some have cv: "cast_value t retVal = Inl err" by simp
  from cast_value_error_is_runtime[OF cv co retVal_typed] show ?thesis .
qed


(*-----------------------------------------------------------------------------*)
(* Quantifier and Obtain *)
(*-----------------------------------------------------------------------------*)

lemma sound_error_result_iff:
  "sound_error_result err \<longleftrightarrow> err \<noteq> TypeError"
  by (cases err) auto

(* In a state that matches env, the values of a type are the values that have
   the type in env. *)
lemma values_of_type_iff:
  assumes "state_matches_env state env storeTyping"
  shows "v \<in> values_of_type state ty \<longleftrightarrow> value_has_type env v ty"
proof -
  from assms have dt: "IS_Datatypes state = TE_Datatypes env"
    and dc: "IS_DataCtors state = TE_DataCtors env"
    unfolding state_matches_env_def tables_match_def by simp_all
  show ?thesis
  proof
    assume "v \<in> values_of_type state ty"
    then obtain env0 where
      dt0: "TE_Datatypes env0 = IS_Datatypes state" and
      dc0: "TE_DataCtors env0 = IS_DataCtors state" and
      vht: "value_has_type env0 v ty"
      unfolding values_of_type_def by blast
    have "value_has_type env0 v ty = value_has_type env v ty"
      by (rule value_has_type_ground_cong_env) (simp_all add: dt0 dc0 dt dc)
    with vht show "value_has_type env v ty" by simp
  next
    assume "value_has_type env v ty"
    then show "v \<in> values_of_type state ty"
      unfolding values_of_type_def using dt dc by (auto intro!: exI[of _ env])
  qed
qed

(* converged f is one of the results f m, or InsufficientFuel. *)
lemma converged_cases:
  "(\<exists>m. converged f = f m) \<or> converged f = Inl InsufficientFuel"
  by (auto simp: converged_def)

(* If no instance is a TypeError, and every instance that has a value is a
   boolean, then a quantifier over the instances is a boolean or a sound error. *)
lemma eval_quantifier_sound:
  assumes "\<forall>v \<in> vals. r v \<noteq> Inl TypeError \<and> (\<forall>w. r v = Inr w \<longrightarrow> (\<exists>b. w = CV_Bool b))"
  shows "eval_quantifier quant vals r \<noteq> Inl TypeError
         \<and> (\<forall>w. eval_quantifier quant vals r = Inr w \<longrightarrow> (\<exists>b. w = CV_Bool b))"
proof -
  have "instances_error vals r \<noteq> Some TypeError"
    using assms unfolding instances_error_def by auto
  then show ?thesis
    unfolding eval_quantifier_def by (auto split: option.splits)
qed

(* Under the same hypothesis, the witness that an Obtain picks is one of the
   values, unless there is a sound error. *)
lemma choose_witness_sound:
  assumes "\<forall>v \<in> vals. r v \<noteq> Inl TypeError \<and> (\<forall>w. r v = Inr w \<longrightarrow> (\<exists>b. w = CV_Bool b))"
  shows "choose_witness vals r \<noteq> Inl TypeError
         \<and> (\<forall>w. choose_witness vals r = Inr w \<longrightarrow> w \<in> vals)"
proof -
  have nt: "instances_error vals r \<noteq> Some TypeError"
    using assms unfolding instances_error_def by auto
  have wit: "(\<exists>v \<in> vals. r v = Inr (CV_Bool True))
              \<longrightarrow> (SOME v. v \<in> vals \<and> r v = Inr (CV_Bool True)) \<in> vals"
  proof
    assume "\<exists>v \<in> vals. r v = Inr (CV_Bool True)"
    then have "\<exists>v. v \<in> vals \<and> r v = Inr (CV_Bool True)" by blast
    from someI_ex[OF this] show "(SOME v. v \<in> vals \<and> r v = Inr (CV_Bool True)) \<in> vals"
      by simp
  qed
  show ?thesis
    unfolding choose_witness_def using nt wit by (auto split: option.splits if_splits)
qed

(* Binding a quantified variable to a value of its type gives a state that
   matches the environment in which the quantifier's body is typed, and that
   environment is well-formed. *)
lemma bind_const_local_sound:
  fixes state :: "'w InterpState"
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and wk: "is_well_kinded env varTy"
    and v_typed: "value_has_type env v (apply_subst (IS_TyArgs state) varTy)"
  shows "state_matches_env (bind_const_local var v state)
           (env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                  TE_GhostLocals := finsert var (TE_GhostLocals env),
                  TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
           (storeTyping @ [apply_subst (IS_TyArgs state) varTy])"
    and "tyenv_well_formed
           (env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                  TE_GhostLocals := finsert var (TE_GhostLocals env),
                  TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                     TE_GhostLocals := finsert var (TE_GhostLocals env),
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  (* The same environment without the TE_GhostLocals update, which
     state_matches_env does not read. *)
  let ?env2 = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"

  obtain state' addr where alloc_eq: "(state', addr) = alloc_store state v"
    by (cases "alloc_store state v") auto
  from alloc_eq have st'_eq: "state' = state \<lparr> IS_Store := IS_Store state @ [v] \<rparr>"
    and addr_eq: "addr = length (IS_Store state)"
    by (simp_all add: Let_def)
  let ?state'' = "state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                           IS_Refs := fmdrop var (IS_Refs state'),
                           IS_ConstLocals := finsert var (IS_ConstLocals state') \<rparr>"
  have bind_eq: "bind_const_local var v state = ?state''"
    by (rule InterpState.equality; simp add: st'_eq addr_eq Let_def)
  have sme2: "state_matches_env ?state'' ?env2
                (storeTyping @ [apply_subst (IS_TyArgs state) varTy])"
    by (rule state_matches_env_add_const_local[OF state_env v_typed alloc_eq refl refl])
  have sme_eq: "state_matches_env ?state'' ?env' st = state_matches_env ?state'' ?env2 st" for st
    by (rule state_matches_env_cong_env) simp_all
  show "state_matches_env (bind_const_local var v state) ?env'
          (storeTyping @ [apply_subst (IS_TyArgs state) varTy])"
    unfolding bind_eq using sme2 sme_eq by simp

  show "tyenv_well_formed ?env'"
    by (rule tyenv_well_formed_declare_ghost[OF wf_env wk])
qed

(* Type soundness for a quantifier at a positive depth. The body is run at the
   depth below, at every value of the bound variable's type, so depth_IH covers
   every instance. *)
lemma type_soundness_quantifier:
  fixes state :: "'w InterpState"
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and depth_IH: "\<And>fuel' env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' Ghost tm' = Some ty' \<Longrightarrow>
                sound_term_result state' env' ty' (interp_term d fuel' state' tm')"
    and typing: "core_term_type env Ghost (CoreTm_Quantifier quant var varTy body) = Some ty"
  shows "sound_term_result state env ty
           (interp_term (Suc d) (Suc fuel) state (CoreTm_Quantifier quant var varTy body))"
proof -
  let ?env' = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                     TE_GhostLocals := finsert var (TE_GhostLocals env),
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  from typing have wk: "is_well_kinded env varTy"
    and body_typing: "core_term_type ?env' Ghost body = Some CoreTy_Bool"
    and ty_eq: "ty = CoreTy_Bool"
    by (auto simp: Let_def split: if_splits option.splits CoreType.splits)
  let ?gty = "apply_subst (IS_TyArgs state) varTy"
  let ?vals = "values_of_type state ?gty"
  let ?r = "\<lambda>v. converged (\<lambda>m. interp_term d m (bind_const_local var v state) body)"

  have interp_eq:
    "interp_term (Suc d) (Suc fuel) state (CoreTm_Quantifier quant var varTy body)
       = eval_quantifier quant ?vals ?r"
    by (simp del: bind_const_local.simps)

  \<comment> \<open>Each instance is not a TypeError, and is a boolean if it has a value. \<close>
  have inst: "\<forall>v \<in> ?vals. ?r v \<noteq> Inl TypeError \<and> (\<forall>w. ?r v = Inr w \<longrightarrow> (\<exists>b. w = CV_Bool b))"
  proof (intro ballI)
    fix v assume v_in: "v \<in> ?vals"
    then have v_typed: "value_has_type env v ?gty"
      using values_of_type_iff[OF state_env] by simp
    let ?st = "bind_const_local var v state"
    have sme: "state_matches_env ?st ?env' (storeTyping @ [?gty])"
      by (rule bind_const_local_sound(1)[OF state_env wf_env wk v_typed])
    have wf': "tyenv_well_formed ?env'"
      by (rule bind_const_local_sound(2)[OF state_env wf_env wk v_typed])
    have each: "sound_term_result ?st ?env' CoreTy_Bool (interp_term d m ?st body)" for m
      by (rule depth_IH[OF sme wf' body_typing])
    from converged_cases[of "\<lambda>m. interp_term d m ?st body"]
    show "?r v \<noteq> Inl TypeError \<and> (\<forall>w. ?r v = Inr w \<longrightarrow> (\<exists>b. w = CV_Bool b))"
    proof
      assume "\<exists>m. converged (\<lambda>m. interp_term d m ?st body) = interp_term d m ?st body"
      then obtain m where c: "converged (\<lambda>m. interp_term d m ?st body) = interp_term d m ?st body"
        by blast
      from each[of m] show ?thesis
        unfolding c
        by (cases "interp_term d m ?st body")
           (auto simp del: bind_const_local.simps
                 simp: sound_error_result_iff dest: value_has_type_Bool)
    next
      assume "converged (\<lambda>m. interp_term d m ?st body) = Inl InsufficientFuel"
      then show ?thesis by (simp del: bind_const_local.simps)
    qed
  qed

  from eval_quantifier_sound[OF inst, of quant]
  show ?thesis
    unfolding interp_eq ty_eq
    by (cases "eval_quantifier quant ?vals ?r")
       (auto simp del: bind_const_local.simps simp: sound_error_result_iff)
qed

(* Type soundness for Obtain at a positive depth. The condition is run at the
   depth below, at every value of the variable's type, and the witness is then
   bound as for a variable declaration. *)
lemma type_soundness_obtain:
  fixes state :: "'w InterpState"
  assumes state_env: "state_matches_env state env storeTyping"
    and wf_env: "tyenv_well_formed env"
    and depth_IH: "\<And>fuel' env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' Ghost tm' = Some ty' \<Longrightarrow>
                sound_term_result state' env' ty' (interp_term d fuel' state' tm')"
    and typing: "core_statement_type env ghost (CoreStmt_Obtain var varTy condTm) = Some env'"
  shows "sound_statement_result env env' storeTyping
           (interp_statement (Suc d) (Suc fuel) state (CoreStmt_Obtain var varTy condTm))"
proof -
  let ?envO = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                     TE_GhostLocals := finsert var (TE_GhostLocals env),
                     TE_ConstLocals := fminus (TE_ConstLocals env) {|var|} \<rparr>"
  (* The same environment without the TE_GhostLocals update, which
     state_matches_env does not read. *)
  let ?envO2 = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                      TE_ConstLocals := fminus (TE_ConstLocals env) {|var|} \<rparr>"
  from typing have wk: "is_well_kinded env varTy"
    and cond_typing: "core_term_type ?envO Ghost condTm = Some CoreTy_Bool"
    and env'_eq: "env' = ?envO"
    by (auto simp: Let_def split: if_splits)
  let ?gty = "apply_subst (IS_TyArgs state) varTy"
  let ?vals = "values_of_type state ?gty"
  let ?r = "\<lambda>v. converged (\<lambda>m. interp_term d m (bind_mutable_local var v state) condTm)"

  have interp_eq:
    "interp_statement (Suc d) (Suc fuel) state (CoreStmt_Obtain var varTy condTm)
       = (case choose_witness ?vals ?r of
            Inr witness \<Rightarrow> Inr (Continue (bind_mutable_local var witness state))
          | Inl err \<Rightarrow> Inl err)"
    by (simp del: bind_mutable_local.simps)

  \<comment> \<open>Binding the variable to a value of its type gives a state that matches
      the environment after the Obtain. \<close>
  have bound: "state_matches_env (bind_mutable_local var v state) ?envO (storeTyping @ [?gty])"
    if v_typed: "value_has_type env v ?gty" for v
  proof -
    obtain state' addr where alloc_eq: "(state', addr) = alloc_store state v"
      by (cases "alloc_store state v") auto
    from alloc_eq have st'_eq: "state' = state \<lparr> IS_Store := IS_Store state @ [v] \<rparr>"
      and addr_eq: "addr = length (IS_Store state)"
      by (simp_all add: Let_def)
    let ?state'' = "state' \<lparr> IS_Locals := fmupd var addr (IS_Locals state'),
                             IS_Refs := fmdrop var (IS_Refs state'),
                             IS_ConstLocals := fminus (IS_ConstLocals state') {|var|} \<rparr>"
    have bind_eq: "bind_mutable_local var v state = ?state''"
      by (rule InterpState.equality; simp add: st'_eq addr_eq Let_def)
    have sme2: "state_matches_env ?state'' ?envO2 (storeTyping @ [?gty])"
      by (rule state_matches_env_add_nonconst_local[OF state_env v_typed alloc_eq refl refl])
    have sme_eq: "state_matches_env ?state'' ?envO st = state_matches_env ?state'' ?envO2 st"
      for st
      by (rule state_matches_env_cong_env) simp_all
    show ?thesis
      unfolding bind_eq using sme2 sme_eq by simp
  qed
  have wf': "tyenv_well_formed ?envO"
    by (rule tyenv_well_formed_declare_ghost[OF wf_env wk])

  \<comment> \<open>Each instance is not a TypeError, and is a boolean if it has a value. \<close>
  have inst: "\<forall>v \<in> ?vals. ?r v \<noteq> Inl TypeError \<and> (\<forall>w. ?r v = Inr w \<longrightarrow> (\<exists>b. w = CV_Bool b))"
  proof (intro ballI)
    fix v assume v_in: "v \<in> ?vals"
    then have v_typed: "value_has_type env v ?gty"
      using values_of_type_iff[OF state_env] by simp
    let ?st = "bind_mutable_local var v state"
    have each: "sound_term_result ?st ?envO CoreTy_Bool (interp_term d m ?st condTm)" for m
      by (rule depth_IH[OF bound[OF v_typed] wf' cond_typing])
    from converged_cases[of "\<lambda>m. interp_term d m ?st condTm"]
    show "?r v \<noteq> Inl TypeError \<and> (\<forall>w. ?r v = Inr w \<longrightarrow> (\<exists>b. w = CV_Bool b))"
    proof
      assume "\<exists>m. converged (\<lambda>m. interp_term d m ?st condTm) = interp_term d m ?st condTm"
      then obtain m where
        c: "converged (\<lambda>m. interp_term d m ?st condTm) = interp_term d m ?st condTm"
        by blast
      from each[of m] show ?thesis
        unfolding c
        by (cases "interp_term d m ?st condTm")
           (auto simp del: bind_mutable_local.simps
                 simp: sound_error_result_iff dest: value_has_type_Bool)
    next
      assume "converged (\<lambda>m. interp_term d m ?st condTm) = Inl InsufficientFuel"
      then show ?thesis by (simp del: bind_mutable_local.simps)
    qed
  qed
  note cw = choose_witness_sound[OF inst]

  show ?thesis
  proof (cases "choose_witness ?vals ?r")
    case (Inl err)
    with cw have "err \<noteq> TypeError" by auto
    then show ?thesis
      unfolding interp_eq Inl by (simp add: sound_error_result_iff)
  next
    case (Inr w)
    with cw have "w \<in> ?vals" by auto
    then have w_typed: "value_has_type env w ?gty"
      using values_of_type_iff[OF state_env] by simp
    have "state_matches_env (bind_mutable_local var w state) env' (storeTyping @ [?gty])"
      unfolding env'_eq by (rule bound[OF w_typed])
    moreover have "storeTyping_extends storeTyping (storeTyping @ [?gty])"
      by (rule storeTyping_extends_append)
    ultimately show ?thesis
      unfolding interp_eq Inr by (auto simp del: bind_mutable_local.simps)
  qed
qed

end

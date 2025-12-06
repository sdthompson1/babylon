theory TypeSoundness
  imports "ValueTyping"
begin

(*-----------------------------------------------------------------------------*)
(* Definition of soundness for interpreter results *)
(*-----------------------------------------------------------------------------*)

(* Type soundness means that evaluating a well-typed term will always either:
    - Succeed with a value of the correct type
    - Fail with a RuntimeError
    - Run out of fuel
   It will never:
    - Succeed with a value that doesn't match the type of the term
    - Fail with a TypeError
*)

definition is_sound_result :: "BabTyEnv \<Rightarrow> BabType \<Rightarrow> BabValue BabInterpResult \<Rightarrow> bool" where
  "is_sound_result env ty result \<equiv>
    (case result of
       BIR_Success val \<Rightarrow> value_has_type env val ty
     | BIR_TypeError \<Rightarrow> False
     | BIR_RuntimeError \<Rightarrow> True
     | BIR_InsufficientFuel \<Rightarrow> True)"

lemma is_sound_result_Success [simp]:
  "is_sound_result env ty (BIR_Success val) = value_has_type env val ty"
  unfolding is_sound_result_def by simp

lemma is_sound_result_TypeError [simp]:
  "\<not> is_sound_result env ty BIR_TypeError"
  unfolding is_sound_result_def by simp

lemma is_sound_result_RuntimeError [simp]:
  "is_sound_result env ty BIR_RuntimeError"
  unfolding is_sound_result_def by simp

lemma is_sound_result_InsufficientFuel [simp]:
  "is_sound_result env ty BIR_InsufficientFuel"
  unfolding is_sound_result_def by simp


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
    and IH: "\<And>tm' ty'. bab_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        is_sound_result env ty' (interp_bab_term fuel state tm')"
    and typing: "bab_term_type env NotGhost (BabTm_Cast loc target_ty operand) = Some ty"
  shows "is_sound_result env ty (interp_bab_term (Suc fuel) state (BabTm_Cast loc target_ty operand))"
proof -
  (* Extract facts from typing *)
  from typing obtain operand_ty where
    operand_typing: "bab_term_type env NotGhost operand = Some operand_ty"
    and operand_is_int: "is_integer_type operand_ty"
    and target_is_int: "is_integer_type target_ty"
    and ty_eq: "ty = target_ty"
    by (auto split: option.splits if_splits)

  (* Apply IH to operand *)
  from IH[OF operand_typing]
  have operand_sound: "is_sound_result env operand_ty (interp_bab_term fuel state operand)"
    by simp

  (* Case split on operand result *)
  show ?thesis
  proof (cases "interp_bab_term fuel state operand")
    case (BIR_Success operand_val)
    (* Operand succeeded - extract type information *)
    from operand_sound BIR_Success
    have operand_typed: "value_has_type env operand_val operand_ty"
      by simp

    (* Since operand has an integer type, value must be BV_FiniteInt or BV_MathInt *)
    from operand_typed operand_is_int
    consider (FiniteInt) src_sign src_bits i where "operand_val = BV_FiniteInt src_sign src_bits i"
           | (MathInt) i where "operand_val = BV_MathInt i"
      using value_has_integer_type_cases by blast
    then show ?thesis
    proof cases
      case (FiniteInt src_sign src_bits i)
      (* Target type must be a finite integer type (from is_integer_type + runtime type check) *)
      from target_is_int obtain loc' tgt_sign tgt_bits where
        target_ty_def: "target_ty = BabTy_FiniteInt loc' tgt_sign tgt_bits"
        using BIR_Success FiniteInt is_integer_type.elims(2) operand_typing typing by fastforce

      (* Case split on whether cast succeeds *)
      show ?thesis
      proof (cases "int_fits tgt_sign tgt_bits i")
        case True
        (* Cast succeeds - value has correct type *)
        from BIR_Success FiniteInt target_ty_def True
        have "interp_bab_term (Suc fuel) state (BabTm_Cast loc target_ty operand) =
              BIR_Success (BV_FiniteInt tgt_sign tgt_bits i)"
          by auto
        with ty_eq target_ty_def True show ?thesis by auto
      next
        case False
        (* Cast fails with RuntimeError *)
        from BIR_Success FiniteInt target_ty_def False
        have "interp_bab_term (Suc fuel) state (BabTm_Cast loc target_ty operand) = BIR_RuntimeError"
          by auto
        thus ?thesis by simp
      qed
    next
      case (MathInt i)
      (* MathInt is not a runtime type, so this contradicts bab_term_type_runtime_invariant *)
      from operand_typed MathInt obtain loc' where "operand_ty = BabTy_MathInt loc'"
        by (cases operand_ty; auto)
      then have "\<not> is_runtime_type operand_ty"
        by simp
      thus ?thesis
        using bab_term_type_runtime_invariant operand_typing wf_env by auto
    qed
  next
    case BIR_TypeError
    (* Operand returned TypeError - contradicts soundness of operand *)
    from operand_sound BIR_TypeError show ?thesis by simp
  next
    case BIR_RuntimeError
    from BIR_RuntimeError show ?thesis by simp
  next
    case BIR_InsufficientFuel
    from BIR_InsufficientFuel show ?thesis by simp
  qed
qed

(* Type soundness for if-then-else *)
lemma type_soundness_if:
  assumes state_env: "state_matches_env state env"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. bab_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        is_sound_result env ty' (interp_bab_term fuel state tm')"
    and typing: "bab_term_type env NotGhost (BabTm_If loc cond thenTm elseTm) = Some ty"
  shows "is_sound_result env ty (interp_bab_term (Suc fuel) state (BabTm_If loc cond thenTm elseTm))"
proof -
  (* Extract facts from typing - the typechecker only succeeds if all these hold *)
  obtain cond_ty where cond_typing: "bab_term_type env NotGhost cond = Some cond_ty"
    using typing by (auto split: option.splits)
  obtain bloc where cond_is_bool: "cond_ty = BabTy_Bool bloc"
    using typing cond_typing by (auto split: BabType.splits)
  obtain then_ty else_ty where
    then_typing: "bab_term_type env NotGhost thenTm = Some then_ty"
    and else_typing: "bab_term_type env NotGhost elseTm = Some else_ty"
    using typing cond_typing cond_is_bool by (auto split: option.splits)
  have types_match: "types_equal then_ty else_ty"
    using typing cond_typing cond_is_bool then_typing else_typing by (auto split: if_splits)
  have ty_eq: "ty = then_ty"
    using typing cond_typing cond_is_bool then_typing else_typing types_match by auto

  (* Apply IH to subterms *)
  from IH[OF cond_typing] have cond_sound:
    "is_sound_result env cond_ty (interp_bab_term fuel state cond)" .
  from IH[OF then_typing] have then_sound:
    "is_sound_result env then_ty (interp_bab_term fuel state thenTm)" .
  from IH[OF else_typing] have else_sound:
    "is_sound_result env else_ty (interp_bab_term fuel state elseTm)" .

  (* Case split on condition result *)
  show ?thesis
  proof (cases "interp_bab_term fuel state cond")
    case (BIR_Success cond_val)
    from cond_sound BIR_Success have cond_typed: "value_has_type env cond_val cond_ty"
      by simp

    (* Condition must be a bool *)
    from cond_is_bool cond_typed obtain b where cond_val_def: "cond_val = BV_Bool b"
      using value_has_type_Bool by blast

    (* Case split on boolean value *)
    show ?thesis
    proof (cases b)
      case True
      (* Condition is true, evaluate then branch *)
      from BIR_Success cond_val_def True
      have interp_eq: "interp_bab_term (Suc fuel) state (BabTm_If loc cond thenTm elseTm) =
                       interp_bab_term fuel state thenTm"
        by auto
      from then_sound ty_eq interp_eq show ?thesis by simp
    next
      case False
      (* Condition is false, evaluate else branch *)
      from BIR_Success cond_val_def False
      have interp_eq: "interp_bab_term (Suc fuel) state (BabTm_If loc cond thenTm elseTm) =
                       interp_bab_term fuel state elseTm"
        by auto

      (* Need to show result has type then_ty, but else branch has type else_ty *)
      show ?thesis
      proof (cases "interp_bab_term fuel state elseTm")
        case (BIR_Success val)
        from else_sound BIR_Success have val_has_else_ty: "value_has_type env val else_ty"
          by simp

        (* Use types_equal to convert from else_ty to then_ty *)
        from types_match have else_ty_eq_then_ty: "types_equal else_ty then_ty"
          using types_equal_symmetric by metis

        (* else_ty is well-kinded because bab_term_type produces well-kinded types *)
        from else_typing wf_env have else_ty_wk: "is_well_kinded env else_ty"
          by (rule bab_term_type_well_kinded)

        (* Apply value_has_type_types_equal *)
        from val_has_else_ty else_ty_eq_then_ty wf_env else_ty_wk
        have "value_has_type env val then_ty"
          by (rule value_has_type_types_equal)
        with ty_eq interp_eq BIR_Success show ?thesis by simp
      next
        case BIR_TypeError
        from else_sound BIR_TypeError show ?thesis by simp
      next
        case BIR_RuntimeError
        from interp_eq BIR_RuntimeError show ?thesis by simp
      next
        case BIR_InsufficientFuel
        from interp_eq BIR_InsufficientFuel show ?thesis by simp
      qed
    qed
  next
    case BIR_TypeError
    from cond_sound BIR_TypeError show ?thesis by simp
  next
    case BIR_RuntimeError
    from BIR_RuntimeError show ?thesis by simp
  next
    case BIR_InsufficientFuel
    from BIR_InsufficientFuel show ?thesis by simp
  qed
qed

(* Type soundness for unary operators *)
lemma type_soundness_unop:
  assumes state_env: "state_matches_env state env"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. bab_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        is_sound_result env ty' (interp_bab_term fuel state tm')"
    and typing: "bab_term_type env NotGhost (BabTm_Unop loc unop operand) = Some ty"
  shows "is_sound_result env ty (interp_bab_term (Suc fuel) state (BabTm_Unop loc unop operand))"
proof (cases unop)
  case BabUnop_Negate
  (* Negate: operand must be signed integer, result has same type *)
  from BabUnop_Negate typing obtain operand_ty where
    operand_typing: "bab_term_type env NotGhost operand = Some operand_ty"
    and is_int: "is_integer_type operand_ty"
    and ty_eq: "ty = operand_ty"
    by (auto simp: signed_integer_type_is_integer_type split: option.splits if_splits)

  from IH[OF operand_typing] have operand_sound:
    "is_sound_result env operand_ty (interp_bab_term fuel state operand)" .

  show ?thesis
  proof (cases "interp_bab_term fuel state operand")
    case (BIR_Success operand_val)
    from operand_sound BIR_Success have operand_typed: "value_has_type env operand_val operand_ty"
      by simp

    (* Since operand has an integer type, value must be BV_FiniteInt or BV_MathInt *)
    from operand_typed is_int
    consider (FiniteInt) sign bits i where "operand_val = BV_FiniteInt sign bits i"
           | (MathInt) i where "operand_val = BV_MathInt i"
      using value_has_integer_type_cases by blast
    then show ?thesis
    proof cases
      case (FiniteInt sign bits i)
      (* Since operand_ty is an integer type and value has that type, extract type info *)
      from operand_typed FiniteInt obtain loc' sign' bits' where operand_ty_def:
        "operand_ty = BabTy_FiniteInt loc' sign' bits'"
        and sign_eq: "sign = sign'" and bits_eq: "bits = bits'"
        and fits: "int_fits sign bits i"
        by (cases operand_ty; auto)

      show ?thesis
      proof (cases "int_fits sign bits (-i)")
        case True
        (* Negation succeeds *)
        from BabUnop_Negate BIR_Success FiniteInt True
        have "interp_bab_term (Suc fuel) state (BabTm_Unop loc unop operand) =
              BIR_Success (BV_FiniteInt sign bits (-i))"
          by auto
        with ty_eq operand_ty_def sign_eq bits_eq True show ?thesis by auto
      next
        case False
        (* Negation overflows - RuntimeError *)
        from BabUnop_Negate BIR_Success FiniteInt False
        have "interp_bab_term (Suc fuel) state (BabTm_Unop loc unop operand) = BIR_RuntimeError"
          by auto
        thus ?thesis by simp
      qed
    next
      case (MathInt i)
      (* MathInt is not a runtime type - contradiction *)
      from operand_typed MathInt obtain loc' where "operand_ty = BabTy_MathInt loc'"
        by (cases operand_ty; auto)
      then have "\<not> is_runtime_type operand_ty"
        by simp
      thus ?thesis
        using bab_term_type_runtime_invariant operand_typing wf_env by auto
    qed
  next
    case BIR_TypeError
    from operand_sound BIR_TypeError show ?thesis by simp
  next
    case BIR_RuntimeError
    from BabUnop_Negate BIR_RuntimeError show ?thesis by simp
  next
    case BIR_InsufficientFuel
    from BabUnop_Negate BIR_InsufficientFuel show ?thesis by simp
  qed
next
  case BabUnop_Complement
  (* Complement: operand must be finite integer, result has same type *)
  from BabUnop_Complement typing obtain operand_ty where
    operand_typing: "bab_term_type env NotGhost operand = Some operand_ty"
    and is_int: "is_integer_type operand_ty"
    and ty_eq: "ty = operand_ty"
    by (auto simp: finite_integer_type_is_integer_type split: option.splits if_splits)

  from IH[OF operand_typing] have operand_sound:
    "is_sound_result env operand_ty (interp_bab_term fuel state operand)" .

  show ?thesis
  proof (cases "interp_bab_term fuel state operand")
    case (BIR_Success operand_val)
    from operand_sound BIR_Success have operand_typed: "value_has_type env operand_val operand_ty"
      by simp

    (* Since operand has an integer type, value must be BV_FiniteInt or BV_MathInt *)
    from operand_typed is_int
    consider (FiniteInt) sign bits i where "operand_val = BV_FiniteInt sign bits i"
           | (MathInt) i where "operand_val = BV_MathInt i"
      using value_has_integer_type_cases by blast
    then show ?thesis
    proof cases
      case (FiniteInt sign bits i)
      from operand_typed FiniteInt obtain loc' sign' bits' where operand_ty_def:
        "operand_ty = BabTy_FiniteInt loc' sign' bits'"
        and sign_eq: "sign = sign'" and bits_eq: "bits = bits'"
        and fits: "int_fits sign bits i"
        by (cases operand_ty; auto)

      (* Complement always succeeds and fits *)
      from BabUnop_Complement BIR_Success FiniteInt
      have interp_eq: "interp_bab_term (Suc fuel) state (BabTm_Unop loc unop operand) =
            BIR_Success (BV_FiniteInt sign bits (int_complement sign bits i))"
        by auto

      have comp_fits: "int_fits sign bits (int_complement sign bits i)"
        using fits by (rule int_complement_fits)

      from interp_eq ty_eq operand_ty_def sign_eq bits_eq comp_fits
      show ?thesis by auto
    next
      case (MathInt i)
      (* MathInt is not a runtime type - contradiction *)
      from operand_typed MathInt obtain loc' where "operand_ty = BabTy_MathInt loc'"
        by (cases operand_ty; auto)
      then have "\<not> is_runtime_type operand_ty"
        by simp
      thus ?thesis
        using bab_term_type_runtime_invariant operand_typing wf_env by auto
    qed
  next
    case BIR_TypeError
    from operand_sound BIR_TypeError show ?thesis by simp
  next
    case BIR_RuntimeError
    from BabUnop_Complement BIR_RuntimeError show ?thesis by simp
  next
    case BIR_InsufficientFuel
    from BabUnop_Complement BIR_InsufficientFuel show ?thesis by simp
  qed
next
  case BabUnop_Not
  (* Not: operand must be bool, result is bool *)
  from BabUnop_Not typing obtain operand_ty bloc where
    operand_typing: "bab_term_type env NotGhost operand = Some operand_ty"
    and operand_is_bool: "operand_ty = BabTy_Bool bloc"
    and ty_eq: "ty = operand_ty"
    by (auto split: option.splits BabType.splits)

  from IH[OF operand_typing] have operand_sound:
    "is_sound_result env operand_ty (interp_bab_term fuel state operand)" .

  show ?thesis
  proof (cases "interp_bab_term fuel state operand")
    case (BIR_Success operand_val)
    from operand_sound BIR_Success have operand_typed: "value_has_type env operand_val operand_ty"
      by simp

    from operand_is_bool operand_typed obtain b where operand_val_def: "operand_val = BV_Bool b"
      using value_has_type_Bool by blast

    from BabUnop_Not BIR_Success operand_val_def
    have "interp_bab_term (Suc fuel) state (BabTm_Unop loc unop operand) = BIR_Success (BV_Bool (\<not>b))"
      by auto
    with ty_eq operand_is_bool show ?thesis by auto
  next
    case BIR_TypeError
    from operand_sound BIR_TypeError show ?thesis by simp
  next
    case BIR_RuntimeError
    from BabUnop_Not BIR_RuntimeError show ?thesis by simp
  next
    case BIR_InsufficientFuel
    from BabUnop_Not BIR_InsufficientFuel show ?thesis by simp
  qed
qed


(* Soundness of exec_function_call - assumed for now, to be proved later
   together with interp_bab_term soundness via mutual induction *)
lemma exec_function_call_sound:
  assumes state_env: "state_matches_env state env"
    and wf_env: "tyenv_well_formed env"
    and typing: "bab_term_type env NotGhost (BabTm_Call loc fnTm argTms) = Some ty"
  shows "case exec_function_call fuel state (BabTm_Call loc fnTm argTms) of
           BIR_Success (_, Some retVal) \<Rightarrow> value_has_type env retVal ty
         | BIR_Success (_, None) \<Rightarrow> False  \<comment> \<open>Should have return value since ty exists\<close>
         | BIR_TypeError \<Rightarrow> False
         | BIR_RuntimeError \<Rightarrow> True
         | BIR_InsufficientFuel \<Rightarrow> True"
  sorry

(* Type soundness for function calls *)
lemma type_soundness_call:
  assumes state_env: "state_matches_env state env"
    and wf_env: "tyenv_well_formed env"
    and IH: "\<And>tm' ty'. bab_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        is_sound_result env ty' (interp_bab_term fuel state tm')"
    and typing: "bab_term_type env NotGhost (BabTm_Call loc fnTm argTms) = Some ty"
  shows "is_sound_result env ty (interp_bab_term (Suc fuel) state (BabTm_Call loc fnTm argTms))"
proof -
  (* Extract function name and type args from fnTm *)
  from typing obtain fnLoc fnName tyArgs where
    fnTm_eq: "fnTm = BabTm_Name fnLoc fnName tyArgs"
    by (cases fnTm) (auto split: option.splits)

  (* Get function declaration from type environment *)
  from typing fnTm_eq obtain funDecl where
    fn_lookup_env: "fmlookup (TE_Functions env) fnName = Some funDecl"
    by (auto split: option.splits)

  (* Function lookup in state equals function lookup in env *)
  have fn_lookup_state: "fmlookup (BS_Functions state) fnName = Some funDecl"
    using function_lookup_eq[OF state_env] fn_lookup_env by simp

  (* Extract conditions from typing *)
  from typing fnTm_eq fn_lookup_env have
    not_impure: "\<not> DF_Impure funDecl" and
    no_ref_args: "\<not> list_ex (\<lambda>(_, vr, _). vr = Ref) (DF_TmArgs funDecl)"
    by (auto split: option.splits if_splits)

  (* Show is_pure_fun_term state fnTm *)
  have is_pure: "is_pure_fun_term state fnTm"
    using fnTm_eq fn_lookup_state no_ref_args not_impure
    by simp

  (* The interpreter calls exec_function_call when is_pure_fun_term holds *)
  have interp_eq: "interp_bab_term (Suc fuel) state (BabTm_Call loc fnTm argTms) =
    (case exec_function_call fuel state (BabTm_Call loc fnTm argTms) of
       BIR_Success (_, Some retVal) \<Rightarrow> BIR_Success retVal
     | BIR_Success (_, None) \<Rightarrow> BIR_TypeError
     | err \<Rightarrow> convert_error err)"
    using is_pure by simp

  (* Use exec_function_call_sound *)
  from exec_function_call_sound[OF state_env wf_env typing]
  have call_sound: "case exec_function_call fuel state (BabTm_Call loc fnTm argTms) of
           BIR_Success (_, Some retVal) \<Rightarrow> value_has_type env retVal ty
         | BIR_Success (_, None) \<Rightarrow> False
         | BIR_TypeError \<Rightarrow> False
         | BIR_RuntimeError \<Rightarrow> True
         | BIR_InsufficientFuel \<Rightarrow> True" .

  (* Case split on the result of exec_function_call *)
  show ?thesis
  proof (cases "exec_function_call fuel state (BabTm_Call loc fnTm argTms)")
    case (BIR_Success result)
    obtain newState maybeRetVal where result_eq: "result = (newState, maybeRetVal)"
      by (cases result) auto
    show ?thesis
    proof (cases maybeRetVal)
      case None
      (* This case contradicts call_sound *)
      from call_sound BIR_Success result_eq None have False by simp
      thus ?thesis by simp
    next
      case (Some retVal)
      from call_sound BIR_Success result_eq Some have "value_has_type env retVal ty"
        by simp
      with interp_eq BIR_Success result_eq Some show ?thesis
        by simp
    qed
  next
    case BIR_TypeError
    (* This case contradicts call_sound *)
    from call_sound BIR_TypeError have False by simp
    thus ?thesis by simp
  next
    case BIR_RuntimeError
    from interp_eq BIR_RuntimeError show ?thesis by simp
  next
    case BIR_InsufficientFuel
    from interp_eq BIR_InsufficientFuel show ?thesis by simp
  qed
qed


(*-----------------------------------------------------------------------------*)
(* Main type soundness theorem *)
(*-----------------------------------------------------------------------------*)

theorem type_soundness:
  fixes fuel :: nat
    and state :: "'w BabState"
    and env :: BabTyEnv
  assumes state_env: "state_matches_env state env"
      and wf_env: "tyenv_well_formed env"
  shows
    "\<forall>tm ty.
       bab_term_type env NotGhost tm = Some ty \<longrightarrow>
       is_sound_result env ty (interp_bab_term fuel state tm)"
using assms
proof (induction fuel arbitrary: state env)
  case 0
  (* Base case: fuel = 0 means BIR_InsufficientFuel *)
  then show ?case by auto
next
  case (Suc fuel)
  (* Inductive case: we have IH for fuel, proving for (Suc fuel) *)
  show ?case
  proof (intro allI impI)
    fix tm ty
    assume typing: "bab_term_type env NotGhost tm = Some ty"

    (* IH in a more convenient form *)
    have IH: "\<And>tm' ty'. bab_term_type env NotGhost tm' = Some ty' \<Longrightarrow>
                        is_sound_result env ty' (interp_bab_term fuel state tm')"
      using Suc.IH Suc.prems by blast

    (* Case split on the structure of tm *)
    show "is_sound_result env ty (interp_bab_term (Suc fuel) state tm)"
    proof (cases tm)
      case (BabTm_Literal loc lit)
      (* Case: term is a literal *)
      then show ?thesis
      proof (cases lit)
        case (BabLit_Bool b)
        (* Bool literal case *)
        from BabTm_Literal BabLit_Bool typing show ?thesis
          by (auto split: BabType.splits)
      next
        case (BabLit_Int i)
        (* Int literal case *)
        from BabTm_Literal BabLit_Int typing show ?thesis
          by (auto split: if_splits BabType.splits Signedness.splits IntBits.splits)
      next
        case (BabLit_String s)
        (* String literal - TODO *)
        from BabTm_Literal BabLit_String typing show ?thesis
          sorry
      next
        case (BabLit_Array tms)
        (* Array literal - TODO *)
        from BabTm_Literal BabLit_Array typing show ?thesis
          sorry
      qed
    next
      case (BabTm_Cast loc target_ty operand)
      (* Cast case - use helper lemma *)
      from type_soundness_cast[OF Suc.prems(1) Suc.prems(2) IH] BabTm_Cast typing
      show ?thesis by simp
    next
      case (BabTm_Unop loc unop operand)
      (* Unary operator case - use helper lemma *)
      from type_soundness_unop[OF Suc.prems(1) Suc.prems(2) IH] BabTm_Unop typing
      show ?thesis by simp
    next
      case (BabTm_Binop loc tm1 ops)
      (* Binary operator case - TODO *)
      from BabTm_Binop typing show ?thesis
        sorry
    next
      case (BabTm_If loc cond thenTm elseTm)
      (* If-then-else case - use helper lemma *)
      from type_soundness_if[OF Suc.prems(1) Suc.prems(2) IH] BabTm_If typing
      show ?thesis by simp
    next
      case (BabTm_Let loc name bindTm bodyTm)
      (* Let binding case - TODO *)
      from BabTm_Let typing show ?thesis
        sorry
    next
      case (BabTm_Quantifier loc quant tyVars vars body)
      (* Quantifier case - TODO: bab_term_type not implemented for quantifiers yet *)
      from BabTm_Quantifier typing show ?thesis
        sorry
    next
      case (BabTm_Name loc name tyArgs)
      (* Variable/constant reference *)
      from BabTm_Name typing have ty_lookup:
        "fmlookup (TE_TermVars env) name = Some ty \<and> tyArgs = [] \<and> name |\<notin>| TE_GhostVars env
         \<or> (\<exists>dtName numTyArgs. fmlookup (TE_DataCtors env) name = Some (dtName, numTyArgs, None) \<and>
              length tyArgs = numTyArgs \<and> ty = BabTy_Name loc dtName tyArgs)"
        by (auto split: option.splits if_splits prod.splits)
      show ?thesis
      proof (cases "fmlookup (TE_TermVars env) name")
        case (Some varTy)
        with ty_lookup have ty_eq: "ty = varTy"
          by (smt (verit, ccfv_threshold) BabTm_Name bab_term_type.simps(3) option.distinct(1)
              option.inject option.simps(5) typing)
        from Suc.prems have vars_wt: "vars_have_correct_types state env"
          unfolding state_matches_env_def by simp
        from vars_wt Some have var_typed: "term_var_in_state_with_type state env name varTy"
          unfolding vars_have_correct_types_def by blast
        then have var_typed':
          "(case fmlookup (BS_Locals state) name of
              Some addr \<Rightarrow> addr < length (BS_Store state) \<and> value_has_type env (BS_Store state ! addr) varTy
            | None \<Rightarrow>
              (case fmlookup (BS_RefVars state) name of
                Some (addr, path) \<Rightarrow> addr < length (BS_Store state) \<and>
                                     (case get_value_at_path (BS_Store state ! addr) path of
                                        BIR_Success v \<Rightarrow> value_has_type env v varTy
                                      | _ \<Rightarrow> False)
              | None \<Rightarrow>
                (case fmlookup (BS_Constants state) name of
                  Some v \<Rightarrow> value_has_type env v varTy
                | None \<Rightarrow> False)))"
          unfolding term_var_in_state_with_type by simp
        with BabTm_Name ty_eq show ?thesis
          by (auto split: option.splits BabInterpResult.splits simp: is_sound_result_def)
      next
        case None
        (* Data constructor case - name is a nullary data constructor *)
        from ty_lookup None obtain dtName numTyArgs where
          ctor_lookup: "fmlookup (TE_DataCtors env) name = Some (dtName, numTyArgs, None)" and
          len_eq: "length tyArgs = numTyArgs" and
          ty_eq: "ty = BabTy_Name loc dtName tyArgs"
          by auto
        from Suc.prems(1) ctor_lookup have name_in_nullary: "name |\<in>| BS_NullaryCtors state"
          by (rule nullary_ctor_in_state)
        (* name is not in locals, refvars, or constants *)
        from Suc.prems(1) None have not_local: "fmlookup (BS_Locals state) name = None"
          and not_ref: "fmlookup (BS_RefVars state) name = None"
          and not_const: "fmlookup (BS_Constants state) name = None"
          by (auto intro: not_in_env_not_in_state)
        (* So the interpreter returns BV_Variant name None *)
        from BabTm_Name not_local not_ref not_const name_in_nullary
        have interp_result: "interp_bab_term (Suc fuel) state (BabTm_Name loc name tyArgs) =
                            BIR_Success (BV_Variant name None)"
          by simp
        (* Now show the result has the right type *)
        from ctor_lookup have val_typed: "value_has_type env (BV_Variant name None) (BabTy_Name loc dtName tyArgs)"
          by simp
        with interp_result ty_eq show ?thesis
          by (simp add: BabTm_Name)
      qed
    next
      case (BabTm_Call loc fnTm argTms)
      (* Function call - use helper lemma *)
      from type_soundness_call[OF Suc.prems(1) Suc.prems(2) IH] BabTm_Call typing
      show ?thesis by simp
    next
      case (BabTm_Tuple loc tms)
      (* Tuple construction - TODO *)
      from BabTm_Tuple typing show ?thesis
        sorry
    next
      case (BabTm_Record loc fields)
      (* Record construction - TODO *)
      from BabTm_Record typing show ?thesis
        sorry
    next
      case (BabTm_RecordUpdate loc baseTm updates)
      (* Record update - TODO *)
      from BabTm_RecordUpdate typing show ?thesis
        sorry
    next
      case (BabTm_TupleProj loc tm idx)
      (* Tuple projection - TODO *)
      from BabTm_TupleProj typing show ?thesis
        sorry
    next
      case (BabTm_RecordProj loc tm field)
      (* Record projection - TODO *)
      from BabTm_RecordProj typing show ?thesis
        sorry
    next
      case (BabTm_ArrayProj loc arrTm indices)
      (* Array projection - TODO *)
      from BabTm_ArrayProj typing show ?thesis
        sorry
    next
      case (BabTm_Match loc scrutTm arms)
      (* Match expression - TODO *)
      from BabTm_Match typing show ?thesis
        sorry
    next
      case (BabTm_Sizeof loc tm)
      (* Sizeof expression - TODO *)
      from BabTm_Sizeof typing show ?thesis
        sorry
    next
      case (BabTm_Allocated loc tm)
      (* Allocated returns None in NotGhost mode, so typing assumption is false *)
      from BabTm_Allocated typing show ?thesis by simp
    next
      case (BabTm_Old loc tm)
      (* Old - interpreter returns TypeError, but typechecker is still TODO *)
      from BabTm_Old show ?thesis sorry
    qed
  qed
qed


end

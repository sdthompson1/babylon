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
    "undefined (interp_lvalue fuel state tm)"  (* TODO: state properly *)
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
    then show ?case sorry  (* requires proper definition *)
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
        case (CoreTm_Binop x71 x72 x73)
        then show ?thesis sorry
      next
        case (CoreTm_Let x81 x82 x83)
        then show ?thesis sorry
      next
        case (CoreTm_Quantifier x91 x92 x93 x94)
        then show ?thesis sorry
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
        then show ?thesis sorry
      next
        case (CoreTm_VariantProj x141 x142)
        then show ?thesis sorry
      next
        case (CoreTm_ArrayProj x151 x152)
        then show ?thesis sorry
      next
        case (CoreTm_Match x161 x162)
        then show ?thesis sorry
      next
        case (CoreTm_Sizeof x17)
        then show ?thesis sorry
      next
        case (CoreTm_Allocated x18)
        then show ?thesis sorry
      next
        case (CoreTm_Old x19)
        then show ?thesis sorry
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
    case 3
    then show ?case sorry
  next
    case 4
    then show ?case sorry
  next
    case 5
    then show ?case sorry
  }
qed

  

end

theory TypePreservation
  imports "BabInterp" "../type_system/BabTypecheck"
begin

(*-----------------------------------------------------------------------------*)
(* Definition: Type judgement for BabValues against fully resolved types *)
(*-----------------------------------------------------------------------------*)

(* Check if a value has a given type. The type must be fully resolved (no typedefs allowed). *)
fun value_has_type :: "BabTyEnv \<Rightarrow> BabValue \<Rightarrow> BabType \<Rightarrow> bool" where
  "value_has_type _ (BV_Bool _) (BabTy_Bool _) = True"
| "value_has_type _ (BV_FiniteInt sign bits val) (BabTy_FiniteInt _ sign' bits') \<longleftrightarrow>
    (sign = sign') \<and> (bits = bits') \<and> int_fits sign bits val"
(* TODO: We need to check datatypes have the correct arg types, not just the correct
   data constructor name! *)
| "value_has_type env (BV_Variant ctor_name args) (BabTy_Name _ ty_name tyargs) \<longleftrightarrow>
    (case fmlookup (TE_Datatypes env) ty_name of
      Some decl \<Rightarrow>
        list_ex (\<lambda>(loc, cname, payload). cname = ctor_name) (DD_Ctors decl)
    | None \<Rightarrow> False)"
(* TODO: Other cases *)
| "value_has_type _ _ _ = False"


(*-----------------------------------------------------------------------------*)
(* Helper lemmas for extracting value structure from types *)
(*-----------------------------------------------------------------------------*)

lemma value_has_type_Bool:
  assumes "value_has_type env val (BabTy_Bool loc)"
  shows "\<exists>b. val = BV_Bool b"
  using assms by (cases val; auto)

lemma value_has_type_FiniteInt:
  assumes "value_has_type env val (BabTy_FiniteInt loc sign bits)"
  shows "\<exists>v. val = BV_FiniteInt sign bits v \<and> int_fits sign bits v"
  using assms by (cases val; auto)


(*-----------------------------------------------------------------------------*)
(* value_has_type is preserved under type equality *)
(*-----------------------------------------------------------------------------*)

lemma value_has_type_types_equal:
  assumes "value_has_type env val ty1"
    and "types_equal ty1 ty2"
  shows "value_has_type env val ty2"
  using assms
proof (induction ty1 ty2 arbitrary: val rule: types_equal.induct)
  case (1 ty1 ty2)

  have has_type: "value_has_type env val ty1" using 1 by simp
  have types_equal: "types_equal ty1 ty2" using 1 by simp

  show "value_has_type env val ty2"
  proof (cases ty1)
    case (BabTy_Bool loc1)
    then obtain b where "val = BV_Bool b" using has_type
      by (cases val; auto)
    moreover obtain loc2 where "ty2 = BabTy_Bool loc2" using types_equal BabTy_Bool
      by (cases ty2; auto)
    ultimately show ?thesis 
      by simp
  next
    case (BabTy_FiniteInt loc1 s1 b1)
    then obtain sign bits i where "val = BV_FiniteInt sign bits i"
      and sign_eq: "sign = s1" and bits_eq: "bits = b1" and fits: "int_fits sign bits i"
      using has_type by (cases val; auto)
    moreover obtain loc2 s2 b2 where "ty2 = BabTy_FiniteInt loc2 s2 b2"
      and "s2 = s1" and "b2 = b1"
      using types_equal BabTy_FiniteInt by (cases ty2; auto)
    ultimately show ?thesis
      by simp
  next
    case (BabTy_MathInt loc1)
    then have "False" using has_type by (cases val; auto)
    then show ?thesis by simp
  next
    case (BabTy_MathReal loc1)
    then have "False" using has_type by (cases val; auto)
    then show ?thesis by simp
  next
    case (BabTy_Tuple loc1 tys1)
    with 1 show ?thesis
      sorry (* TODO: Need to handle tuple case with list_all *)
  next
    case (BabTy_Record loc1 flds1)
    with 1 show ?thesis
      sorry (* TODO: Need to handle record case with list_all *)
  next
    case (BabTy_Array loc1 elem1 dims1)
    with 1 show ?thesis
      sorry (* TODO: Need to handle array case recursively *)
  next
    case (BabTy_Name loc1 n1 tyargs1)
    obtain loc2 n2 tyargs2 where ty2_def: "ty2 = BabTy_Name loc2 n2 tyargs2"
      using types_equal BabTy_Name by (cases ty2; auto)
    with types_equal BabTy_Name have name_eq: "n1 = n2"
      by auto
    from has_type BabTy_Name ty2_def name_eq show ?thesis
      sorry
  qed
qed


(*-----------------------------------------------------------------------------*)
(* Predicate that says that a BabTyEnv (type environment) and BabState (interpreter state)
   are consistent with each other *)
(*-----------------------------------------------------------------------------*)

(* TODO: Do we need to include the condition that typedefs in the env are fully
   expanded? *)

(* Variables in TE_TermVars have corresponding well-typed values in the state *)
definition vars_well_typed :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "vars_well_typed state env \<equiv>
    \<forall>name ty. fmlookup (TE_TermVars env) name = Some ty \<longrightarrow>
      (case fmlookup (BS_Locals state) name of
        Some addr \<Rightarrow> addr < length (BS_Store state) \<and>
                     value_has_type env (BS_Store state ! addr) ty
      | None \<Rightarrow>
        (case fmlookup (BS_Constants state) name of
          Some val \<Rightarrow> value_has_type env val ty
        | None \<Rightarrow> False))"

(* Ref variables point to well-typed values at their paths *)
definition refs_well_typed :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "refs_well_typed state env \<equiv>
    \<forall>name addr path. fmlookup (BS_RefVars state) name = Some (addr, path) \<longrightarrow>
      addr < length (BS_Store state) \<and>
      (\<exists>ty. fmlookup (TE_TermVars env) name = Some ty \<and>
            (case get_value_at_path (BS_Store state ! addr) path of
              BIR_Success val \<Rightarrow> value_has_type env val ty
            | _ \<Rightarrow> False))"

(* Declarations in state match those in environment *)
definition decls_match :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "decls_match state env \<equiv>
    BS_Functions state = TE_Functions env \<and>
    BS_Datatypes state = TE_Datatypes env"

(* Type variables in state match those in environment *)
definition type_vars_match :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "type_vars_match state env \<equiv> fmdom (BS_LocalTypes state) = TE_TypeVars env"

(* Overall well-formedness: state matches environment *)
definition state_matches_env :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "state_matches_env state env \<equiv>
    vars_well_typed state env \<and>
    refs_well_typed state env \<and>
    decls_match state env \<and>
    type_vars_match state env"


(*-----------------------------------------------------------------------------*)
(* Helper lemmas for type preservation *)
(*-----------------------------------------------------------------------------*)

(* Property of int_complement *)
lemma int_complement_fits:
  assumes "int_fits sign bits i"
  shows "int_fits sign bits (int_complement sign bits i)"
  using assms by (cases sign; cases bits; auto)

(* Type Preservation for Cast *)
lemma type_preservation_cast:
  assumes state_env: "state_matches_env state env"
    and IH: "\<forall>tm ty val.
              bab_term_type env NotGhost tm = Some ty \<and>
              interp_bab_term fuel state tm = BIR_Success val
              \<longrightarrow> value_has_type env val ty"
    and typing: "bab_term_type env NotGhost (BabTm_Cast loc target_ty operand) = Some ty"
    and interp: "interp_bab_term (Suc fuel) state (BabTm_Cast loc target_ty operand) = BIR_Success val"
  shows "value_has_type env val ty"
proof -
  (* Extract facts from typing *)
  from typing obtain operand_ty where
    operand_typing: "bab_term_type env NotGhost operand = Some operand_ty"
    and operand_is_int: "is_integer_type operand_ty"
    and target_is_int: "is_integer_type target_ty"
    and ty_eq: "ty = target_ty"
    by (auto split: option.splits if_splits)

  (* Interpreter must have evaluated operand successfully *)
  from interp obtain operand_val where
    operand_interp: "interp_bab_term fuel state operand = BIR_Success operand_val"
    by (auto split: BabInterpResult.splits)

  (* Apply IH to operand *)
  from IH[rule_format] state_env operand_typing operand_interp
  have operand_typed: "value_has_type env operand_val operand_ty"
    by auto

  (* Operand must be a finite integer *)
  from interp operand_interp obtain src_sign src_bits i where
    operand_val_def: "operand_val = BV_FiniteInt src_sign src_bits i"
    by (auto split: BabInterpResult.splits BabValue.splits)

  (* Target type must be a finite integer type *)
  (* We know from typing that target_ty is an integer type.
     In NotGhost mode, it can't be BabTy_MathInt (would fail is_runtime_type check),
     so it must be BabTy_FiniteInt. *)
  from target_is_int obtain loc' tgt_sign tgt_bits where
    target_ty_def: "target_ty = BabTy_FiniteInt loc' tgt_sign tgt_bits"
    using bab_term_type_runtime_invariant[of env "BabTm_Cast loc target_ty operand" ty]
    by (metis is_integer_type.elims(2) is_runtime_type.simps(1) ty_eq typing)

  (* The value must fit in the target type for interpreter to succeed *)
  from interp operand_interp operand_val_def target_ty_def
  have fits: "int_fits tgt_sign tgt_bits i"
    by (auto split: if_splits)

  (* The result value is the integer with target type *)
  from interp operand_interp operand_val_def target_ty_def fits
  have val_def: "val = BV_FiniteInt tgt_sign tgt_bits i"
    by auto

  (* Show value_has_type *)
  from val_def target_ty_def ty_eq fits have "value_has_type env val ty"
    by auto
  thus ?thesis
    by simp
qed

(* Type Preservation for if-then-else *)
lemma type_preservation_if:
  assumes state_env: "state_matches_env state env"
    and IH: "\<forall>tm ty val.
              bab_term_type env NotGhost tm = Some ty \<and>
              interp_bab_term fuel state tm = BIR_Success val
              \<longrightarrow> value_has_type env val ty"
    and typing: "bab_term_type env NotGhost (BabTm_If loc cond thenTm elseTm) = Some ty"
    and interp: "interp_bab_term (Suc fuel) state (BabTm_If loc cond thenTm elseTm) = BIR_Success val"
  shows "value_has_type env val ty"
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

  (* Interpreter evaluates condition *)
  from interp obtain cond_val where
    cond_interp: "interp_bab_term fuel state cond = BIR_Success cond_val"
    by (auto split: BabInterpResult.splits)

  (* Apply IH to condition *)
  from IH[rule_format] state_env cond_typing cond_interp
  have cond_typed: "value_has_type env cond_val cond_ty"
    by auto

  (* Condition must be a bool *)
  from cond_is_bool obtain loc' where cond_ty_bool: "cond_ty = BabTy_Bool loc'"
    by auto
  with cond_typed obtain b where cond_val_def: "cond_val = BV_Bool b"
    using value_has_type_Bool by blast

  (* Case split on boolean value *)
  from interp cond_interp cond_val_def show ?thesis
  proof (cases b)
    case True
    (* Condition is true, evaluate then branch *)
    from interp cond_interp cond_val_def True
    have then_interp: "interp_bab_term fuel state thenTm = BIR_Success val"
      by auto

    (* Apply IH to then branch *)
    from IH[rule_format] state_env then_typing then_interp ty_eq
    show ?thesis by auto
  next
    case False
    (* Condition is false, evaluate else branch *)
    from interp cond_interp cond_val_def False
    have else_interp: "interp_bab_term fuel state elseTm = BIR_Success val"
      by auto

    (* Apply IH to else branch to get val has type else_ty *)
    from IH[rule_format] state_env else_typing else_interp
    have val_has_else_ty: "value_has_type env val else_ty"
      by auto

    (* Use types_equal to convert from else_ty to then_ty *)
    (* types_match says: types_equal fuel (TE_Typedefs env) then_ty else_ty *)
    (* By symmetry: types_equal fuel (TE_Typedefs env) else_ty then_ty *)
    from types_match have "types_equal else_ty then_ty"
      using types_equal_symmetric by metis

    (* Apply value_has_type_types_equal *)
    from val_has_else_ty this have "value_has_type env val then_ty"
      by (rule value_has_type_types_equal)
    with ty_eq show ?thesis
      by simp
  qed
qed

(* Type Preservation for unary operators *)
lemma type_preservation_unop:
  assumes state_env: "state_matches_env state env"
    and IH: "\<forall>tm ty val.
              bab_term_type env NotGhost tm = Some ty \<and>
              interp_bab_term fuel state tm = BIR_Success val
              \<longrightarrow> value_has_type env val ty"
    and typing: "bab_term_type env NotGhost (BabTm_Unop loc unop operand) = Some ty"
    and interp: "interp_bab_term (Suc fuel) state (BabTm_Unop loc unop operand) = BIR_Success val"
  shows "value_has_type env val ty"
proof (cases unop)
  case BabUnop_Negate
  (* Negate: operand must be integer, result has same type *)
  from BabUnop_Negate typing interp show ?thesis
  proof (cases "bab_term_type env NotGhost operand")
    case (Some operand_ty)
    (* Typechecking succeeded for operand *)
    from BabUnop_Negate typing Some have operand_typing:
      "bab_term_type env NotGhost operand = Some operand_ty"
      and is_int: "is_integer_type operand_ty"
      and ty_eq: "ty = operand_ty"
      by (auto split: if_splits)

    from BabUnop_Negate interp show ?thesis
    proof (cases "interp_bab_term fuel state operand")
      case (BIR_Success operand_val)
      (* Interpreter succeeded for operand *)

      (* Apply induction hypothesis to operand *)
      from IH[rule_format] state_env operand_typing BIR_Success
      have operand_typed: "value_has_type env operand_val operand_ty"
        by auto

      from BabUnop_Negate interp BIR_Success show ?thesis
      proof (cases operand_val)
        case (BV_FiniteInt sign bits i)
        (* Operand evaluated to a finite integer *)
        (* From value_has_type, we know the types match *)
        from operand_typed BV_FiniteInt have
          "value_has_type env (BV_FiniteInt sign bits i) operand_ty"
          by simp

        (* Since operand_ty is an integer type, it must be BabTy_FiniteInt *)
        from is_int obtain loc' sign' bits' where operand_ty_def:
          "operand_ty = BabTy_FiniteInt loc' sign' bits'"
          by (metis is_integer_type.elims(2) operand_typed value_has_type.simps(37))

        (* From value_has_type_FiniteInt, signs and bits must match *)
        from operand_typed BV_FiniteInt operand_ty_def
        obtain v where "BV_FiniteInt sign bits i = BV_FiniteInt sign' bits' v"
          and fits: "int_fits sign' bits' v"
          using value_has_type_FiniteInt by blast
        then have sign_eq: "sign = sign'" and bits_eq: "bits = bits'" and "i = v"
          by auto
        with fits have fits': "int_fits sign bits i"
          by simp

        (* The interpreter checks if -i fits, and succeeds with it if so *)
        from BabUnop_Negate interp BIR_Success BV_FiniteInt
        have val_eq: "int_fits sign bits (-i) \<Longrightarrow> val = BV_FiniteInt sign bits (-i)"
          by (auto split: if_splits)

        (* Since interp succeeded with BIR_Success, the result must fit *)
        have result_fits: "int_fits sign bits (-i)"
          using BabUnop_Negate BIR_Success BV_FiniteInt interp 
          by (cases "int_fits sign bits (-i)"; auto)

        from val_eq result_fits have "val = BV_FiniteInt sign bits (-i)"
          by auto

        with ty_eq operand_ty_def sign_eq bits_eq result_fits
        show ?thesis
          by auto
      qed auto
    qed auto
  qed auto
next
  case BabUnop_Complement
  (* Complement: operand must be integer, result has same type *)
  from BabUnop_Complement typing interp show ?thesis
  proof (cases "bab_term_type env NotGhost operand")
    case (Some operand_ty)
    from BabUnop_Complement typing Some have operand_typing:
      "bab_term_type env NotGhost operand = Some operand_ty"
      and is_int: "is_integer_type operand_ty"
      and ty_eq: "ty = operand_ty"
      by (auto split: if_splits)

    from BabUnop_Complement interp show ?thesis
    proof (cases "interp_bab_term fuel state operand")
      case (BIR_Success operand_val)

      (* Apply induction hypothesis *)
      from IH[rule_format] state_env operand_typing BIR_Success
      have operand_typed: "value_has_type env operand_val operand_ty"
        by auto

      from BabUnop_Complement interp BIR_Success show ?thesis
      proof (cases operand_val)
        case (BV_FiniteInt sign bits i)
        (* From value_has_type, we know the types match *)
        from operand_typed BV_FiniteInt have
          "value_has_type env (BV_FiniteInt sign bits i) operand_ty"
          by simp

        (* Since operand_ty is an integer type, it must be BabTy_FiniteInt *)
        then obtain loc' sign' bits' where operand_ty_def:
          "operand_ty = BabTy_FiniteInt loc' sign' bits'"
          using is_int
          using value_has_type.elims(2) by blast

        (* From value_has_type definition, signs and bits match *)
        from operand_typed BV_FiniteInt operand_ty_def
        have sign_eq: "sign = sign'" and bits_eq: "bits = bits'"
             and fits: "int_fits sign bits i"
          by auto

        from BabUnop_Complement interp BIR_Success BV_FiniteInt
        have "val = BV_FiniteInt sign bits (int_complement sign bits i)"
          by auto

        (* int_complement always produces a value that fits, by construction *)
        moreover have "int_fits sign bits (int_complement sign bits i)"
          using fits by (rule int_complement_fits)

        ultimately show ?thesis
          using ty_eq operand_ty_def sign_eq bits_eq
          by auto
      qed auto
    qed auto
  qed auto
next
  case BabUnop_Not
  (* Not: operand must be bool, result is bool *)
  from BabUnop_Not typing interp show ?thesis
  proof (cases "bab_term_type env NotGhost operand")
    case (Some operand_ty)
    have operand_typing: "bab_term_type env NotGhost operand = Some operand_ty"
      by (simp add: Some)
    (* For BabUnop_Not, operand_ty must be BabTy_Bool and ty = operand_ty *)
    from BabUnop_Not typing Some obtain bloc where
      operand_is_bool: "operand_ty = BabTy_Bool bloc" and
      ty_eq: "ty = operand_ty"
      by (auto split: BabType.splits)

    from BabUnop_Not interp show ?thesis
    proof (cases "interp_bab_term fuel state operand")
      case (BIR_Success operand_val)

      (* Apply induction hypothesis *)
      from IH[rule_format] state_env operand_typing BIR_Success
      have operand_typed: "value_has_type env operand_val operand_ty"
        by auto

      from BabUnop_Not interp BIR_Success show ?thesis
      proof (cases operand_val)
        case (BV_Bool b)
        from BabUnop_Not interp BIR_Success BV_Bool
        have "val = BV_Bool (\<not>b)"
          by auto

        with ty_eq operand_is_bool show ?thesis
          by auto
      qed auto
    qed auto
  qed auto
qed


(*-----------------------------------------------------------------------------*)
(* Main type preservation theorem *)
(*-----------------------------------------------------------------------------*)

(* For now this is just proved for (a subset of cases of) interp_bab_term; 
   TODO: expand as needed *)

theorem type_preservation:
  fixes fuel :: nat
    and state :: "'w BabState"
    and env :: BabTyEnv
  assumes state_env: "state_matches_env state env"
  shows
    (* 1. interp_bab_term preserves types *)
    "\<forall>tm ty val.
       bab_term_type env NotGhost tm = Some ty \<and>
       interp_bab_term fuel state tm = BIR_Success val
       \<longrightarrow> value_has_type env val ty"
using assms
proof (induction fuel arbitrary: state env)
  case 0
  (* Base case: fuel = 0 means interp_bab_term fails *)
  then show ?case by auto
next
  case (Suc fuel)
  (* Inductive case: we have IH for fuel, proving for (Suc fuel) *)
  (* IH: "\<forall>tm ty val. bab_term_type env NotGhost tm = Some ty \<and>
                           interp_bab_term fuel state tm = BIR_Success val
                           \<longrightarrow> value_has_type env val ty" *)
  show ?case
  proof (intro allI impI)
    fix tm ty val
    assume assms: "bab_term_type env NotGhost tm = Some ty \<and>
                   interp_bab_term (Suc fuel) state tm = BIR_Success val"
    then have typing: "bab_term_type env NotGhost tm = Some ty"
          and interp: "interp_bab_term (Suc fuel) state tm = BIR_Success val"
      by auto

    (* Case split on the structure of tm *)
    show "value_has_type env val ty"
    proof (cases tm)
      case (BabTm_Literal loc lit)
      (* Case: term is a literal *)
      then show ?thesis
      proof (cases lit)
        case (BabLit_Bool b)
        (* Bool literal case *)
        from BabTm_Literal BabLit_Bool typing interp show ?thesis
          by (auto split: BabType.splits)
      next
        case (BabLit_Int i)
        (* Int literal case *)
        from BabTm_Literal BabLit_Int typing interp show ?thesis
          by (auto split: if_splits BabType.splits Signedness.splits IntBits.splits)
      next
        case (BabLit_String s)
        (* String literal - TODO *)
        from BabTm_Literal BabLit_String typing interp show ?thesis
          sorry
      next
        case (BabLit_Array tms)
        (* Array literal - TODO: needs term list property *)
        from BabTm_Literal BabLit_Array typing interp show ?thesis
          sorry
      qed
    next
      case (BabTm_Cast loc target_ty operand)
      (* Cast case *)
      show ?thesis
        using BabTm_Cast Suc.IH Suc.prems interp type_preservation_cast typing by blast
    next
      case (BabTm_Unop loc unop operand)
      (* Unary operator case *)
      show ?thesis
        using BabTm_Unop Suc.IH Suc.prems interp type_preservation_unop typing by blast 
    next
      case (BabTm_Binop loc tm1 ops)
      (* Binary operator case - TODO: needs binop property *)
      from BabTm_Binop typing interp show ?thesis
        sorry
    next
      case (BabTm_If loc cond thenTm elseTm)
      (* If-then-else case *)
      show ?thesis
        using BabTm_If Suc.IH Suc.prems interp type_preservation_if typing by blast
    next
      case (BabTm_Let loc name bindTm bodyTm)
      (* Let binding case - TODO *)
      from BabTm_Let typing interp show ?thesis
        sorry
    next
      case (BabTm_Quantifier loc quant tyVars vars body)
      (* Quantifier case - TODO *)
      from BabTm_Quantifier typing interp show ?thesis
        sorry
    next
      case (BabTm_Name loc name tyArgs)
      (* Variable/constant reference - TODO *)
      from BabTm_Name typing interp show ?thesis
        sorry
    next
      case (BabTm_Call loc fnTm argTms)
      (* Function call - TODO: needs function call property *)
      from BabTm_Call typing interp show ?thesis
        sorry
    next
      case (BabTm_Tuple loc tms)
      (* Tuple construction - TODO *)
      from BabTm_Tuple typing interp show ?thesis
        sorry
    next
      case (BabTm_Record loc fields)
      (* Record construction - TODO *)
      from BabTm_Record typing interp show ?thesis
        sorry
    next
      case (BabTm_RecordUpdate loc baseTm updates)
      (* Record update - TODO *)
      from BabTm_RecordUpdate typing interp show ?thesis
        sorry
    next
      case (BabTm_TupleProj loc tm idx)
      (* Tuple projection - TODO *)
      from BabTm_TupleProj typing interp show ?thesis
        sorry
    next
      case (BabTm_RecordProj loc tm field)
      (* Record projection - TODO *)
      from BabTm_RecordProj typing interp show ?thesis
        sorry
    next
      case (BabTm_ArrayProj loc arrTm indices)
      (* Array projection - TODO *)
      from BabTm_ArrayProj typing interp show ?thesis
        sorry
    next
      case (BabTm_Match loc scrutTm arms)
      (* Match expression - TODO: needs match property *)
      from BabTm_Match typing interp show ?thesis
        sorry
    next
      case (BabTm_Sizeof loc tm)
      (* Sizeof expression - TODO *)
      from BabTm_Sizeof typing interp show ?thesis
        sorry
    next
      case (BabTm_Allocated loc tm)
        (* TODO *)
      show ?thesis sorry
    next
      case (BabTm_Old loc tm)
        (* TODO *)
      show ?thesis sorry
    qed
  qed
qed


end

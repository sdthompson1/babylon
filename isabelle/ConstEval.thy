theory ConstEval
  imports BabInterp
begin

(* Compile-time constant evaluation for array size expressions and similar.
   This is used by the elaborator to convert BabDim_Fixed terms to BabDim_FixedInt. *)

(* TODO: We can probably remove most of this and just call bab_interp_term instead.
   After all, the correctness theorem below states that const_eval is basically the same
   as bab_interp_term called in a suitable state - so we might as well just call bab_interp_term
   directly! *)

datatype ConstEvalError =
  CEErr_NotConstant Location       (* Expression fundamentally cannot be a compile-time constant *)
| CEErr_NotSupported Location      (* Expression could theoretically be const but we don't support it *)
| CEErr_EvalFailed Location        (* Evaluation failed (div by zero, name not found, type error, etc.) *)

(* Evaluate a compile-time constant expression.

   Arguments:
   - consts: Map from constant names to their values. The caller should remove any
     names that are shadowed by local variables in the current scope.
   - tm: The term to evaluate (should already be elaborated/type-checked)

   Returns either an error or a BabValue.
*)
fun const_eval :: "(string, BabValue) fmap \<Rightarrow> BabTerm \<Rightarrow> ConstEvalError + BabValue"
  and const_eval_binop :: "BabValue \<Rightarrow> (BabBinop \<times> BabTerm) list \<Rightarrow> (string, BabValue) fmap \<Rightarrow> Location \<Rightarrow> ConstEvalError + BabValue"
where
  (* Bool literal *)
  "const_eval consts (BabTm_Literal _ (BabLit_Bool b)) = Inr (BV_Bool b)"

  (* Int literal *)
| "const_eval consts (BabTm_Literal loc (BabLit_Int i)) =
    (case infer_literal_type i of
      Some (sign, bits) \<Rightarrow> Inr (BV_FiniteInt sign bits i)
    | None \<Rightarrow> Inl (CEErr_EvalFailed loc))"

  (* String and array literals not supported *)
| "const_eval consts (BabTm_Literal loc (BabLit_String _)) = Inl (CEErr_NotSupported loc)"
| "const_eval consts (BabTm_Literal loc (BabLit_Array _)) = Inl (CEErr_NotSupported loc)"

  (* Name lookup - only in constants map *)
| "const_eval consts (BabTm_Name loc name _) =
    (case fmlookup consts name of
      Some v \<Rightarrow> Inr v
    | None \<Rightarrow> Inl (CEErr_EvalFailed loc))"

  (* Cast *)
| "const_eval consts (BabTm_Cast loc targetTy operand) =
    (case const_eval consts operand of
      Inl err \<Rightarrow> Inl err
    | Inr (BV_FiniteInt _ _ i) \<Rightarrow>
        (case targetTy of
          BabTy_FiniteInt _ tgt_sign tgt_bits \<Rightarrow>
            if int_fits tgt_sign tgt_bits i
            then Inr (BV_FiniteInt tgt_sign tgt_bits i)
            else Inl (CEErr_EvalFailed loc)
        | _ \<Rightarrow> Inl (CEErr_EvalFailed loc))
    | Inr _ \<Rightarrow> Inl (CEErr_EvalFailed loc))"

  (* If-then-else *)
| "const_eval consts (BabTm_If loc cond thenTm elseTm) =
    (case const_eval consts cond of
      Inl err \<Rightarrow> Inl err
    | Inr (BV_Bool True) \<Rightarrow> const_eval consts thenTm
    | Inr (BV_Bool False) \<Rightarrow> const_eval consts elseTm
    | Inr _ \<Rightarrow> Inl (CEErr_EvalFailed loc))"

  (* Unary operators *)
| "const_eval consts (BabTm_Unop loc BabUnop_Negate operand) =
    (case const_eval consts operand of
      Inr (BV_FiniteInt sign bits i) \<Rightarrow>
        (let result = -i in
         if int_fits sign bits result then Inr (BV_FiniteInt sign bits result)
         else Inl (CEErr_EvalFailed loc))
    | Inr _ \<Rightarrow> Inl (CEErr_EvalFailed loc)
    | Inl err \<Rightarrow> Inl err)"

| "const_eval consts (BabTm_Unop loc BabUnop_Complement operand) =
    (case const_eval consts operand of
      Inr (BV_FiniteInt sign bits i) \<Rightarrow>
        Inr (BV_FiniteInt sign bits (int_complement sign bits i))
    | Inr _ \<Rightarrow> Inl (CEErr_EvalFailed loc)
    | Inl err \<Rightarrow> Inl err)"

| "const_eval consts (BabTm_Unop loc BabUnop_Not operand) =
    (case const_eval consts operand of
      Inr (BV_Bool b) \<Rightarrow> Inr (BV_Bool (\<not>b))
    | Inr _ \<Rightarrow> Inl (CEErr_EvalFailed loc)
    | Inl err \<Rightarrow> Inl err)"

  (* Binary operators *)
| "const_eval consts (BabTm_Binop loc tm1 ops) =
    (case const_eval consts tm1 of
      Inr v1 \<Rightarrow> const_eval_binop v1 ops consts loc
    | Inl err \<Rightarrow> Inl err)"

  (* Tuple projection *)
| "const_eval consts (BabTm_TupleProj loc tm idx) =
    (case const_eval consts tm of
      Inr (BV_Tuple vals) \<Rightarrow>
        if idx < length vals then Inr (vals ! idx)
        else Inl (CEErr_EvalFailed loc)
    | Inr _ \<Rightarrow> Inl (CEErr_EvalFailed loc)
    | Inl err \<Rightarrow> Inl err)"

  (* Record projection *)
| "const_eval consts (BabTm_RecordProj loc tm fieldName) =
    (case const_eval consts tm of
      Inr (BV_Record flds) \<Rightarrow>
        (case map_of flds fieldName of
          Some v \<Rightarrow> Inr v
        | None \<Rightarrow> Inl (CEErr_EvalFailed loc))
    | Inr _ \<Rightarrow> Inl (CEErr_EvalFailed loc)
    | Inl err \<Rightarrow> Inl err)"

  (* Things that are fundamentally not compile-time constants *)
| "const_eval consts (BabTm_Quantifier loc _ _ _ _) = Inl (CEErr_NotConstant loc)"
| "const_eval consts (BabTm_Call loc _ _) = Inl (CEErr_NotConstant loc)"
| "const_eval consts (BabTm_Allocated loc _) = Inl (CEErr_NotConstant loc)"
| "const_eval consts (BabTm_Old loc _) = Inl (CEErr_NotConstant loc)"

  (* Things we could support but don't *)
| "const_eval consts (BabTm_Let loc _ _ _) = Inl (CEErr_NotSupported loc)"
| "const_eval consts (BabTm_Tuple loc _) = Inl (CEErr_NotSupported loc)"
| "const_eval consts (BabTm_Record loc _) = Inl (CEErr_NotSupported loc)"
| "const_eval consts (BabTm_RecordUpdate loc _ _) = Inl (CEErr_NotSupported loc)"
| "const_eval consts (BabTm_ArrayProj loc _ _) = Inl (CEErr_NotSupported loc)"
| "const_eval consts (BabTm_Match loc _ _) = Inl (CEErr_NotSupported loc)"
| "const_eval consts (BabTm_Sizeof loc _) = Inl (CEErr_NotSupported loc)"

  (* Binary operator chain evaluation *)
| "const_eval_binop v1 [] _ _ = Inr v1"
| "const_eval_binop v1 ((op, tm2) # rest) consts loc =
    (case const_eval consts tm2 of
      Inr v2 \<Rightarrow>
        (case eval_binop op v1 v2 of
          BIR_Success result \<Rightarrow> const_eval_binop result rest consts loc
        | _ \<Rightarrow> Inl (CEErr_EvalFailed loc))
    | Inl err \<Rightarrow> Inl err)"

(* Helper to evaluate an expression and extract a u64 integer (for array sizes) *)
fun const_eval_to_u64 :: "(string, BabValue) fmap \<Rightarrow> BabTerm \<Rightarrow> ConstEvalError + int" where
  "const_eval_to_u64 consts tm =
    (case const_eval consts tm of
      Inr (BV_FiniteInt Unsigned IntBits_64 n) \<Rightarrow> Inr n
    | Inr _ \<Rightarrow> Inl (CEErr_EvalFailed (bab_term_location tm))
    | Inl err \<Rightarrow> Inl err)"


(* ========== Correctness theorem ========== *)

(* A state is suitable for const evaluation if it has no locals/refs and
   constants match the provided map *)
definition const_eval_state :: "(string, BabValue) fmap \<Rightarrow> 'w BabState \<Rightarrow> bool" where
  "const_eval_state consts state \<equiv>
     BS_Constants state = consts \<and>
     BS_Locals state = fmempty \<and>
     BS_RefVars state = fmempty"

(* Main correctness theorem using the induction principle generated for const_eval.

   This shows that if const_eval and/or const_eval_binop succeed, then the interpreter
   (in an appropriate state) would also have succeeded obtaining the same value (or run
   out of fuel). In other words, const_eval is "sound", but not necessarily "complete" 
   (i.e. there exist runtime-only expressions that cannot be evaluated at compile time).

   A subtle point: We don't rule out that the constant evaluator might succeed on an
   expression that actually diverges at runtime (i.e. runs out of fuel in the interpreter
   for every fuel value). But this is not a realistic possibility because the constant
   evaluator doesn't support any construct (such as function calls or while-loops) that
   might cause divergence.
*)
theorem const_eval_interp_correspondence:
  assumes "const_eval_state constants state"
  shows "\<forall>fuel v. const_eval constants tm = Inr v \<longrightarrow>
            (interp_bab_term fuel state tm = BIR_Success v \<or>
             interp_bab_term fuel state tm = BIR_InsufficientFuel)"
    and "\<forall>fuel v. const_eval_binop v1 ops constants loc = Inr v \<longrightarrow>
            (interp_bab_binop fuel state v1 ops = BIR_Success v \<or>
             interp_bab_binop fuel state v1 ops = BIR_InsufficientFuel)"
  using assms
proof (induction rule: const_eval_const_eval_binop.induct)
  (* Bool literal *)
  case (1 constants loc b)
  then show ?case
    by (metis const_eval.simps(1) interp_bab_term.simps(1,2) not0_implies_Suc
        sum.inject(2))
next
  (* Int literal *)
  case (2 constants loc i)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_Literal loc (BabLit_Int i)) = Inr v"
    show "interp_bab_term fuel state (BabTm_Literal loc (BabLit_Int i)) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_Literal loc (BabLit_Int i)) = BIR_InsufficientFuel"
      using ce by (cases fuel; auto split: option.splits if_splits)
  qed
next
  (* String literal - returns NotSupported error *)
  case (3 constants loc uv)
  then show ?case by simp
next
  (* Array literal - returns NotSupported error *)
  case (4 constants loc uw)
  then show ?case by simp
next
  (* Name lookup *)
  case (5 constants loc name ux)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_Name loc name ux) = Inr v"
    show "interp_bab_term fuel state (BabTm_Name loc name ux) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_Name loc name ux) = BIR_InsufficientFuel"
      using ce "5.prems" by (cases fuel; auto simp: const_eval_state_def split: option.splits)
  qed
next
  (* Cast *)
  case (6 constants loc targetTy operand)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_Cast loc targetTy operand) = Inr v"
    show "interp_bab_term fuel state (BabTm_Cast loc targetTy operand) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_Cast loc targetTy operand) = BIR_InsufficientFuel"
    proof (cases fuel)
      case 0 then show ?thesis by simp
    next
      case (Suc n)
      from ce obtain src_sign src_bits i tgt_loc tgt_sign tgt_bits where
        ce_op: "const_eval constants operand = Inr (BV_FiniteInt src_sign src_bits i)" and
        tgt: "targetTy = BabTy_FiniteInt tgt_loc tgt_sign tgt_bits" and
        fits: "int_fits tgt_sign tgt_bits i" and
        v_eq: "v = BV_FiniteInt tgt_sign tgt_bits i"
        by (auto split: sum.splits BabValue.splits BabType.splits if_splits)
      from "6.IH"[OF "6.prems"] ce_op
      have ih: "interp_bab_term n state operand = BIR_Success (BV_FiniteInt src_sign src_bits i) \<or>
                interp_bab_term n state operand = BIR_InsufficientFuel" by auto
      then show ?thesis
      proof
        assume "interp_bab_term n state operand = BIR_Success (BV_FiniteInt src_sign src_bits i)"
        then show ?thesis using Suc tgt fits v_eq by simp
      next
        assume "interp_bab_term n state operand = BIR_InsufficientFuel"
        then show ?thesis using Suc by simp
      qed
    qed
  qed
next
  (* If-then-else *)
  case (7 constants loc cond thenTm elseTm)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_If loc cond thenTm elseTm) = Inr v"
    show "interp_bab_term fuel state (BabTm_If loc cond thenTm elseTm) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_If loc cond thenTm elseTm) = BIR_InsufficientFuel"
    proof (cases fuel)
      case 0 then show ?thesis by simp
    next
      case (Suc n)
      from ce obtain b where
        ce_cond: "const_eval constants cond = Inr (BV_Bool b)" and
        ce_branch: "if b then const_eval constants thenTm = Inr v
                    else const_eval constants elseTm = Inr v"
        by (auto split: sum.splits BabValue.splits bool.splits)
      from "7.IH"(1)[OF "7.prems"] ce_cond
      have ih_cond: "interp_bab_term n state cond = BIR_Success (BV_Bool b) \<or>
                     interp_bab_term n state cond = BIR_InsufficientFuel" by auto
      show ?thesis
      proof (cases b)
        case True
        with ce_branch have ce_then: "const_eval constants thenTm = Inr v" by simp
        from "7.IH"(2) True ce_cond "7.prems" ce_then
        have ih_then: "interp_bab_term n state thenTm = BIR_Success v \<or>
                       interp_bab_term n state thenTm = BIR_InsufficientFuel" by auto
        from ih_cond show ?thesis
        proof
          assume "interp_bab_term n state cond = BIR_Success (BV_Bool b)"
          with ih_then Suc True show ?thesis by auto
        next
          assume "interp_bab_term n state cond = BIR_InsufficientFuel"
          then show ?thesis using Suc by simp
        qed
      next
        case False
        with ce_branch have ce_else: "const_eval constants elseTm = Inr v" by simp
        from "7.IH"(3) False ce_cond "7.prems" ce_else
        have ih_else: "interp_bab_term n state elseTm = BIR_Success v \<or>
                       interp_bab_term n state elseTm = BIR_InsufficientFuel" by auto
        from ih_cond show ?thesis
        proof
          assume "interp_bab_term n state cond = BIR_Success (BV_Bool b)"
          with ih_else Suc False show ?thesis by auto
        next
          assume "interp_bab_term n state cond = BIR_InsufficientFuel"
          then show ?thesis using Suc by simp
        qed
      qed
    qed
  qed
next
  (* Unop Negate *)
  case (8 constants loc operand)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_Unop loc BabUnop_Negate operand) = Inr v"
    show "interp_bab_term fuel state (BabTm_Unop loc BabUnop_Negate operand) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_Unop loc BabUnop_Negate operand) = BIR_InsufficientFuel"
    proof (cases fuel)
      case 0 then show ?thesis by simp
    next
      case (Suc n)
      from ce obtain sign bits i where
        ce_op: "const_eval constants operand = Inr (BV_FiniteInt sign bits i)" and
        fits: "int_fits sign bits (-i)" and
        v_eq: "v = BV_FiniteInt sign bits (-i)"
        by (auto split: sum.splits BabValue.splits if_splits simp: Let_def)
      from "8.IH"[OF "8.prems"] ce_op
      have ih: "interp_bab_term n state operand = BIR_Success (BV_FiniteInt sign bits i) \<or>
                interp_bab_term n state operand = BIR_InsufficientFuel" by auto
      then show ?thesis
      proof
        assume "interp_bab_term n state operand = BIR_Success (BV_FiniteInt sign bits i)"
        then show ?thesis using Suc fits v_eq by (simp add: Let_def)
      next
        assume "interp_bab_term n state operand = BIR_InsufficientFuel"
        then show ?thesis using Suc by simp
      qed
    qed
  qed
next
  (* Unop Complement *)
  case (9 constants loc operand)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_Unop loc BabUnop_Complement operand) = Inr v"
    show "interp_bab_term fuel state (BabTm_Unop loc BabUnop_Complement operand) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_Unop loc BabUnop_Complement operand) = BIR_InsufficientFuel"
    proof (cases fuel)
      case 0 then show ?thesis by simp
    next
      case (Suc n)
      from ce obtain sign bits i where
        ce_op: "const_eval constants operand = Inr (BV_FiniteInt sign bits i)" and
        v_eq: "v = BV_FiniteInt sign bits (int_complement sign bits i)"
        by (auto split: sum.splits BabValue.splits)
      from "9.IH"[OF "9.prems"] ce_op
      have ih: "interp_bab_term n state operand = BIR_Success (BV_FiniteInt sign bits i) \<or>
                interp_bab_term n state operand = BIR_InsufficientFuel" by auto
      then show ?thesis
      proof
        assume "interp_bab_term n state operand = BIR_Success (BV_FiniteInt sign bits i)"
        then show ?thesis using Suc v_eq by simp
      next
        assume "interp_bab_term n state operand = BIR_InsufficientFuel"
        then show ?thesis using Suc by simp
      qed
    qed
  qed
next
  (* Unop Not *)
  case (10 constants loc operand)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_Unop loc BabUnop_Not operand) = Inr v"
    show "interp_bab_term fuel state (BabTm_Unop loc BabUnop_Not operand) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_Unop loc BabUnop_Not operand) = BIR_InsufficientFuel"
    proof (cases fuel)
      case 0 then show ?thesis by simp
    next
      case (Suc n)
      from ce obtain b where
        ce_op: "const_eval constants operand = Inr (BV_Bool b)" and
        v_eq: "v = BV_Bool (\<not>b)"
        by (auto split: sum.splits BabValue.splits)
      from "10.IH"[OF "10.prems"] ce_op
      have ih: "interp_bab_term n state operand = BIR_Success (BV_Bool b) \<or>
                interp_bab_term n state operand = BIR_InsufficientFuel" by auto
      then show ?thesis
      proof
        assume "interp_bab_term n state operand = BIR_Success (BV_Bool b)"
        then show ?thesis using Suc v_eq by simp
      next
        assume "interp_bab_term n state operand = BIR_InsufficientFuel"
        then show ?thesis using Suc by simp
      qed
    qed
  qed
next
  (* Binop *)
  case (11 constants loc tm1 ops)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_Binop loc tm1 ops) = Inr v"
    show "interp_bab_term fuel state (BabTm_Binop loc tm1 ops) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_Binop loc tm1 ops) = BIR_InsufficientFuel"
    proof (cases fuel)
      case 0 then show ?thesis by simp
    next
      case (Suc n)
      from ce obtain v1' where
        ce_tm1: "const_eval constants tm1 = Inr v1'" and
        ce_ops: "const_eval_binop v1' ops constants loc = Inr v"
        by (auto split: sum.splits)
      from "11.IH"(1)[OF "11.prems"] ce_tm1
      have ih_tm1: "interp_bab_term n state tm1 = BIR_Success v1' \<or>
                    interp_bab_term n state tm1 = BIR_InsufficientFuel" by auto
      from "11.IH"(2)[OF ce_tm1 "11.prems"] ce_ops
      have ih_ops: "interp_bab_binop n state v1' ops = BIR_Success v \<or>
                    interp_bab_binop n state v1' ops = BIR_InsufficientFuel" by auto
      from ih_tm1 show ?thesis
      proof
        assume "interp_bab_term n state tm1 = BIR_Success v1'"
        with ih_ops Suc show ?thesis by auto
      next
        assume "interp_bab_term n state tm1 = BIR_InsufficientFuel"
        then show ?thesis using Suc by simp
      qed
    qed
  qed
next
  (* TupleProj *)
  case (12 constants loc tm idx)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_TupleProj loc tm idx) = Inr v"
    show "interp_bab_term fuel state (BabTm_TupleProj loc tm idx) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_TupleProj loc tm idx) = BIR_InsufficientFuel"
    proof (cases fuel)
      case 0 then show ?thesis by simp
    next
      case (Suc n)
      from ce obtain vals where
        ce_tm: "const_eval constants tm = Inr (BV_Tuple vals)" and
        idx_ok: "idx < length vals" and
        v_eq: "v = vals ! idx"
        by (auto split: sum.splits BabValue.splits if_splits)
      from "12.IH"[OF "12.prems"] ce_tm
      have ih: "interp_bab_term n state tm = BIR_Success (BV_Tuple vals) \<or>
                interp_bab_term n state tm = BIR_InsufficientFuel" by auto
      then show ?thesis
      proof
        assume "interp_bab_term n state tm = BIR_Success (BV_Tuple vals)"
        then show ?thesis using Suc idx_ok v_eq by simp
      next
        assume "interp_bab_term n state tm = BIR_InsufficientFuel"
        then show ?thesis using Suc by simp
      qed
    qed
  qed
next
  (* RecordProj *)
  case (13 constants loc tm fieldName)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval constants (BabTm_RecordProj loc tm fieldName) = Inr v"
    show "interp_bab_term fuel state (BabTm_RecordProj loc tm fieldName) = BIR_Success v \<or>
          interp_bab_term fuel state (BabTm_RecordProj loc tm fieldName) = BIR_InsufficientFuel"
    proof (cases fuel)
      case 0 then show ?thesis by simp
    next
      case (Suc n)
      from ce obtain flds where
        ce_tm: "const_eval constants tm = Inr (BV_Record flds)" and
        lookup: "map_of flds fieldName = Some v"
        by (auto split: sum.splits BabValue.splits option.splits)
      from "13.IH"[OF "13.prems"] ce_tm
      have ih: "interp_bab_term n state tm = BIR_Success (BV_Record flds) \<or>
                interp_bab_term n state tm = BIR_InsufficientFuel" by auto
      then show ?thesis
      proof
        assume "interp_bab_term n state tm = BIR_Success (BV_Record flds)"
        then show ?thesis using Suc lookup by simp
      next
        assume "interp_bab_term n state tm = BIR_InsufficientFuel"
        then show ?thesis using Suc by simp
      qed
    qed
  qed
next
  (* Quantifier - returns NotConstant error *)
  case (14 constants loc uy uz va vb)
  then show ?case by simp
next
  (* Call - returns NotConstant error *)
  case (15 constants loc vc vd)
  then show ?case by simp
next
  (* Allocated - returns NotConstant error *)
  case (16 constants loc ve)
  then show ?case by simp
next
  (* Old - returns NotConstant error *)
  case (17 constants loc vf)
  then show ?case by simp
next
  (* Let - returns NotSupported error *)
  case (18 constants loc vg vh vi)
  then show ?case by simp
next
  (* Tuple - returns NotSupported error *)
  case (19 constants loc vj)
  then show ?case by simp
next
  (* Record - returns NotSupported error *)
  case (20 constants loc vk)
  then show ?case by simp
next
  (* RecordUpdate - returns NotSupported error *)
  case (21 constants loc vl vm)
  then show ?case by simp
next
  (* ArrayProj - returns NotSupported error *)
  case (22 constants loc vn vo)
  then show ?case by simp
next
  (* Match - returns NotSupported error *)
  case (23 constants loc vp vq)
  then show ?case by simp
next
  (* Sizeof - returns NotSupported error *)
  case (24 constants loc vr)
  then show ?case by simp
next
  (* Binop chain - empty list *)
  case (25 v1 vs vt)
  then show ?case
    by (metis const_eval_binop.simps(1) interp_bab_binop.simps(1,2) nat.exhaust_sel
        sum.inject(2))
next
  (* Binop chain - cons *)
  case (26 v1 op tm2 rest constants loc)
  show ?case
  proof (intro allI impI)
    fix fuel v
    assume ce: "const_eval_binop v1 ((op, tm2) # rest) constants loc = Inr v"
    show "interp_bab_binop fuel state v1 ((op, tm2) # rest) = BIR_Success v \<or>
          interp_bab_binop fuel state v1 ((op, tm2) # rest) = BIR_InsufficientFuel"
    proof (cases fuel)
      case 0 then show ?thesis by simp
    next
      case (Suc n)
      from ce obtain v2 intermediate where
        ce_tm2: "const_eval constants tm2 = Inr v2" and
        eval_op: "eval_binop op v1 v2 = BIR_Success intermediate" and
        ce_rest: "const_eval_binop intermediate rest constants loc = Inr v"
        by (auto split: sum.splits BabInterpResult.splits)
      from "26.IH"(1)[OF "26.prems"] ce_tm2
      have ih_tm2: "interp_bab_term n state tm2 = BIR_Success v2 \<or>
                    interp_bab_term n state tm2 = BIR_InsufficientFuel" by auto
      from "26.IH"(2) ce_tm2 refl eval_op "26.prems" ce_rest
      have ih_rest: "interp_bab_binop n state intermediate rest = BIR_Success v \<or>
                     interp_bab_binop n state intermediate rest = BIR_InsufficientFuel" by auto
      from ih_tm2 show ?thesis
      proof
        assume tm2_succ: "interp_bab_term n state tm2 = BIR_Success v2"
        from ih_rest show ?thesis
        proof
          assume "interp_bab_binop n state intermediate rest = BIR_Success v"
          then show ?thesis using Suc tm2_succ eval_op by simp
        next
          assume "interp_bab_binop n state intermediate rest = BIR_InsufficientFuel"
          then show ?thesis using Suc tm2_succ eval_op by simp
        qed
      next
        assume "interp_bab_term n state tm2 = BIR_InsufficientFuel"
        then show ?thesis using Suc by simp
      qed
    qed
  qed
qed

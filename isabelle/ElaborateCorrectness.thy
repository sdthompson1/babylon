theory ElaborateCorrectness 
  imports BabElaborate BabTypecheck
begin

theorem elaborate_type_correct:
  assumes "elab_term fuel typedefs ghost tm = Inr (newTm, ty)"
  shows "bab_term_type env ghost newTm = Some ty"
using assms
proof (induction fuel arbitrary: env ghost tm newTm ty)
  case NoFuel: 0
  then show ?case by simp
next
  case Fuel: (Suc fuel)
  then show ?case 
  proof (cases tm)
    case (BabTm_Literal loc lit)
    then show ?thesis
    proof (cases lit)
      case (BabLit_Bool b)
      thus ?thesis using BabTm_Literal Fuel.prems by auto
    next
      case (BabLit_Int i)
      thus ?thesis using BabTm_Literal Fuel.prems by (cases "get_type_for_int i"; auto)
    next
      case (BabLit_String str)
      then show ?thesis sorry
    next
      case (BabLit_Array arr)
      then show ?thesis sorry
    qed

  next
    case (BabTm_Name x21 x22 x23)
    then show ?thesis sorry

  next
    case (BabTm_Cast loc targetTy operand)
    (* Extract info from elaborator success *)
    from Fuel.prems BabTm_Cast obtain newOperand operandTy resolvedTargetTy where
      elab_operand: "elab_term fuel typedefs ghost operand = Inr (newOperand, operandTy)"
      and resolve_ok: "resolve_typedefs fuel typedefs targetTy = Some resolvedTargetTy"
      and operand_is_int: "is_integer_type operandTy"
      and target_is_int: "is_integer_type resolvedTargetTy"
      and runtime_ok: "ghost = NotGhost \<longrightarrow> is_runtime_type resolvedTargetTy"
      and result_tm: "newTm = BabTm_Cast loc resolvedTargetTy newOperand"
      and result_ty: "ty = resolvedTargetTy"
      by (auto split: sum.splits option.splits if_splits)
    (* By IH, the elaborated operand typechecks *)
    have ih: "bab_term_type env ghost newOperand = Some operandTy"
      using Fuel.IH elab_operand by blast
    (* Now show the cast typechecks *)
    show ?thesis
      using ih operand_is_int target_is_int runtime_ok result_tm result_ty
      by auto

  next
    case (BabTm_If x41 x42 x43 x44)
    then show ?thesis sorry

  next
    case (BabTm_Unop loc op operand)
    (* Extract info from elaborator success *)
    from Fuel.prems BabTm_Unop obtain newOperand operandTy where
      elab_operand: "elab_term fuel typedefs ghost operand = Inr (newOperand, operandTy)"
      and result_tm: "newTm = BabTm_Unop loc op newOperand"
      and result_ty: "ty = operandTy"
      and type_ok: "(op = BabUnop_Negate \<longrightarrow> is_signed_integer_type operandTy)
                  \<and> (op = BabUnop_Complement \<longrightarrow> is_finite_integer_type operandTy)
                  \<and> (op = BabUnop_Not \<longrightarrow> (\<exists>bloc. operandTy = BabTy_Bool bloc))"
      by (auto split: sum.splits BabUnop.splits if_splits BabType.splits)
    (* By IH, the elaborated operand typechecks *)
    have ih: "bab_term_type env ghost newOperand = Some operandTy"
      using Fuel.IH elab_operand by blast
    (* Now show the unop typechecks *)
    show ?thesis
      using ih type_ok result_tm result_ty
      by (auto split: BabUnop.splits BabType.splits)

  next
    case (BabTm_Binop x61 x62 x63)
    then show ?thesis sorry
  next
    case (BabTm_Let x71 x72 x73 x74)
    then show ?thesis sorry
  next
    case (BabTm_Quantifier x81 x82 x83 x84 x85)
    then show ?thesis sorry
  next
    case (BabTm_Call x91 x92 x93)
    then show ?thesis sorry
  next
    case (BabTm_Tuple x101 x102)
    then show ?thesis sorry
  next
    case (BabTm_Record x111 x112)
    then show ?thesis sorry
  next
    case (BabTm_RecordUpdate x121 x122 x123)
    then show ?thesis sorry
  next
    case (BabTm_TupleProj x131 x132 x133)
    then show ?thesis sorry
  next
    case (BabTm_RecordProj x141 x142 x143)
    then show ?thesis sorry
  next
    case (BabTm_ArrayProj x151 x152 x153)
    then show ?thesis sorry
  next
    case (BabTm_Match x161 x162 x163)
    then show ?thesis sorry
  next
    case (BabTm_Sizeof x171 x172)
    then show ?thesis sorry
  next
    case (BabTm_Allocated x181 x182)
    then show ?thesis sorry
  next
    case (BabTm_Old x191 x192)
    then show ?thesis sorry
  qed
qed


end

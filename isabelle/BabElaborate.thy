theory BabElaborate
  imports IntRange ResolveTypedefs TypeEnv
begin

(* This "elaborates" a Babylon program by adding implicit casts, filling in missing type
   annotations, etc, until the program is well-typed according to BabTypecheck.thy
   (or an error is found).
*)

datatype TypeError =
  TyErr_OutOfFuel Location
  | TyErr_IntLiteralOutOfRange Location
  | TyErr_InvalidCast Location
  | TyErr_NegateRequiresSigned Location
  | TyErr_ComplementRequiresFiniteInt Location
  | TyErr_NotRequiresBool Location

type_synonym Typedefs = "(string, DeclTypedef) fmap"

(* Note: the type returned by elab_term is fully resolved (does not contain typedefs) *)
fun elab_term :: "nat \<Rightarrow> Typedefs \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> TypeError list + (BabTerm \<times> BabType)"
  where

  (* Out of fuel case *)
  "elab_term 0 _ _ tm = Inl [TyErr_OutOfFuel (bab_term_location tm)]"

  (* Main case - valid fuel *)
| "elab_term (Suc fuel) typedefs ghost tm =
    (case tm of
      BabTm_Literal loc lit \<Rightarrow>
        (case lit of
          BabLit_Bool b \<Rightarrow> Inr (tm, BabTy_Bool loc)
        | BabLit_Int i \<Rightarrow>
            (case get_type_for_int i of
              Some (sign, bits) \<Rightarrow> Inr (tm, BabTy_FiniteInt loc sign bits)
            | None \<Rightarrow> Inl [TyErr_IntLiteralOutOfRange loc])
        | _ \<Rightarrow> undefined)  \<comment>\<open>TODO: other literals\<close>

    | BabTm_Cast loc targetTy operand \<Rightarrow>
        (case elab_term fuel typedefs ghost operand of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newOperand, operandTy) \<Rightarrow>
            (case resolve_typedefs fuel typedefs targetTy of 
              None \<Rightarrow> Inl [TyErr_OutOfFuel (bab_type_location targetTy)]
            | Some resolvedTargetTy \<Rightarrow>
                if is_integer_type operandTy
                \<and> is_integer_type resolvedTargetTy
                \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type resolvedTargetTy) then
                    Inr (BabTm_Cast loc resolvedTargetTy newOperand, resolvedTargetTy)
                else
                    Inl [TyErr_InvalidCast loc]))

    | BabTm_Unop loc op operand \<Rightarrow>
        (case elab_term fuel typedefs ghost operand of
          Inl errs \<Rightarrow> Inl errs
        | Inr (newOperand, operandTy) \<Rightarrow>
            (case op of
              BabUnop_Negate \<Rightarrow>
                if is_signed_integer_type operandTy then
                  Inr (BabTm_Unop loc op newOperand, operandTy)
                else
                  Inl [TyErr_NegateRequiresSigned loc]
            | BabUnop_Complement \<Rightarrow>
                if is_finite_integer_type operandTy then
                  Inr (BabTm_Unop loc op newOperand, operandTy)
                else
                  Inl [TyErr_ComplementRequiresFiniteInt loc]
            | BabUnop_Not \<Rightarrow>
                (case operandTy of
                  BabTy_Bool _ \<Rightarrow> Inr (BabTm_Unop loc op newOperand, operandTy)
                | _ \<Rightarrow> Inl [TyErr_NotRequiresBool loc])))

    | _ \<Rightarrow> undefined)"  (* TODO: other cases *)

end

theory BabTypecheck
  imports TypeEnv IntRange
begin

(* This file defines type-correctness for an "elaborated" Babylon program, i.e. one in
   which all typedefs have been expanded out, any necessary type inference has been 
   performed, implicit casts have been inserted, etc. *)

fun bab_term_type :: "BabTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabTerm \<Rightarrow> BabType option"
  where
  (* Bool literals *)
  "bab_term_type _ _ (BabTm_Literal loc (BabLit_Bool _)) = Some (BabTy_Bool loc)"

  (* Int literals *)
| "bab_term_type _ _ (BabTm_Literal loc (BabLit_Int i)) = 
    (case get_type_for_int i of
      Some (sign, bits) \<Rightarrow> Some (BabTy_FiniteInt loc sign bits)
    | None \<Rightarrow> None)"

  (* TODO: String and array literals *)

  (* Cast *)
| "bab_term_type env mode (BabTm_Cast loc target_ty operand) =
    (case bab_term_type env mode operand of
      None \<Rightarrow> None
    | Some operand_ty \<Rightarrow>
        if is_integer_type operand_ty
        \<and> is_integer_type target_ty
        \<and> (mode = NotGhost \<longrightarrow> is_runtime_type target_ty) then
          Some target_ty
        else
          None)"

  (* Unary operators - negate, complement, logical-not *)
| "bab_term_type env mode (BabTm_Unop loc op operand) =
    (case bab_term_type env mode operand of
      Some operand_ty \<Rightarrow>
        (case op of
          BabUnop_Negate \<Rightarrow>
            (if is_signed_integer_type operand_ty then Some operand_ty else None)
        | BabUnop_Complement \<Rightarrow>
            (if is_finite_integer_type operand_ty then Some operand_ty else None)
        | BabUnop_Not \<Rightarrow>
            (case operand_ty of BabTy_Bool _ \<Rightarrow> Some operand_ty | _ \<Rightarrow> None))
    | None \<Rightarrow> None)"

  (* If-then-else: condition must be bool, branches must have same type *)
| "bab_term_type env mode (BabTm_If loc cond thenTm elseTm) =
    (case (bab_term_type env mode cond,
           bab_term_type env mode thenTm,
           bab_term_type env mode elseTm) of
      (Some (BabTy_Bool _), Some then_ty, Some else_ty) \<Rightarrow>
        (if types_equal then_ty else_ty then Some then_ty else None)
    | _ \<Rightarrow> None)"

(* TODO: Other cases *)
| "bab_term_type env mode _ = undefined"


(* Runtime type invariant: If typechecking succeeds in NotGhost mode,
   the resulting type must be runtime-compatible (no MathInt/MathReal) *)
lemma bab_term_type_runtime_invariant:
  assumes "bab_term_type env NotGhost tm = Some ty"
  shows "is_runtime_type ty"
using assms
proof (induction env NotGhost tm arbitrary: ty rule: bab_term_type.induct)
  case (1 uu loc uw)
  (* BabTm_Literal loc (BabLit_Bool _) -> BabTy_Bool loc *)
  then show ?case by auto
next
  case (2 ux loc i)
  (* BabTm_Literal loc (BabLit_Int i) -> BabTy_FiniteInt *)
  from "2.prems" show ?case
    by (auto split: option.splits)
next
  case (3 env loc target_ty operand)
  (* BabTm_Cast: guard requires is_runtime_type target_ty when mode = NotGhost *)
  from "3.prems" show ?case
    by (auto split: option.splits if_splits)
next
  case (4 env loc op operand)
  (* BabTm_Unop: returns operand_ty which by IH is runtime type *)
  from "4.prems" obtain operand_ty where
    operand_typed: "bab_term_type env NotGhost operand = Some operand_ty"
    by (auto split: option.splits)
  hence "is_runtime_type operand_ty"
    by (simp add: "4.hyps")
  thus ?case
    using "4.prems" operand_typed
    by (auto split: option.splits if_splits BabType.splits BabUnop.splits)
next
  case (5 env loc cond thenTm elseTm)
  (* BabTm_If: returns then_ty which by IH is runtime type *)
  obtain cond_ty where cond_typed: "bab_term_type env NotGhost cond = Some cond_ty"
    using "5.prems" by (auto split: option.splits)
  obtain cond_loc where cond_bool: "cond_ty = BabTy_Bool cond_loc"
    using "5.prems" cond_typed by (auto split: option.splits BabType.splits)
  obtain then_ty where then_typed: "bab_term_type env NotGhost thenTm = Some then_ty"
    using "5.prems" cond_typed cond_bool by (auto split: option.splits)
  obtain else_ty where else_typed: "bab_term_type env NotGhost elseTm = Some else_ty"
    using "5.prems" cond_typed cond_bool then_typed by (auto split: option.splits)
  have result: "ty = then_ty"
    using "5.prems" cond_typed cond_bool then_typed else_typed by (auto split: if_splits)
  from then_typed have "is_runtime_type then_ty"
    using "5.hyps"(2) cond_typed cond_bool by simp
  thus ?case
    using result by simp
next
  case ("6_1" env v vb)
  then show ?case sorry
next
  case ("6_2" env v vb)
  then show ?case sorry
next
  case ("6_3" env v va vb)
  then show ?case sorry
next
  case ("6_4" env v va vb)
  then show ?case sorry
next
  case ("6_5" env v va vb vc)
  then show ?case sorry
next
  case ("6_6" env v va vb vc vd)
  then show ?case sorry
next
  case ("6_7" env v va vb)
  then show ?case sorry
next
  case ("6_8" env v va)
  then show ?case sorry
next
  case ("6_9" env v va)
  then show ?case sorry
next
  case ("6_10" env v va vb)
  then show ?case sorry
next
  case ("6_11" env v va vb)
  then show ?case sorry
next
  case ("6_12" env v va vb)
  then show ?case sorry
next
  case ("6_13" env v va vb)
  then show ?case sorry
next
  case ("6_14" env v va vb)
  then show ?case sorry
next
  case ("6_15" env v va)
  then show ?case sorry
next
  case ("6_16" env v va)
  then show ?case sorry
next
  case ("6_17" env v va)
  then show ?case sorry
qed

end

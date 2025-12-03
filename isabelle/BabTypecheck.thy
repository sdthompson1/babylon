theory BabTypecheck
  imports TypeEnvWellFormed
begin

(* This file defines type-correctness for an "elaborated" Babylon program, i.e. one in
   which all typedefs have been expanded out, any necessary type inference has been
   performed, implicit casts have been inserted, etc. *)


(* Now for typechecking of terms. This either returns None if the term is ill-typed,
   or Some (with the term's type) if it is well-typed. *)

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

  (* Names: variables, constants, or nullary data constructors *)
| "bab_term_type env mode (BabTm_Name loc name tyArgs) =
    (case fmlookup (TE_TermVars env) name of
      Some ty \<Rightarrow>
        \<comment> \<open>Found in term variables: type args must be empty, check ghost compatibility\<close>
        (if tyArgs = [] \<and> (mode = NotGhost \<longrightarrow> name |\<notin>| TE_GhostVars env)
         then Some ty else None)
    | None \<Rightarrow>
        \<comment> \<open>Not a term variable: check if it's a nullary data constructor\<close>
        (case fmlookup (TE_DataCtors env) name of
          Some (dtName, numTyArgs, payload) \<Rightarrow>
            \<comment> \<open>Must be nullary (no payload), have correct number of type args,
                and type args must be runtime types if mode is NotGhost\<close>
            (if payload = None \<and> length tyArgs = numTyArgs
                \<and> (list_all (is_well_kinded env) tyArgs)
                \<and> (mode = NotGhost \<longrightarrow> list_all is_runtime_type tyArgs)
             then Some (BabTy_Name loc dtName tyArgs)
             else None)
        | None \<Rightarrow> None))"

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
      and "tyenv_well_formed env"
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
  case (3 env loc name tyArgs)
  (* BabTm_Name: returns either a type from TE_TermVars or a BabTy_Name for a data ctor *)
  from "3.prems" show ?case
  proof (cases "fmlookup (TE_TermVars env) name")
    case None
    (* Data constructor case: type args must be runtime types *)
    with "3.prems" show ?thesis
      by (auto split: option.splits if_splits prod.splits)
  next
    case (Some varTy)
    (* Variable case: use tyenv_well_formed to show varTy is runtime type *)
    from "3.prems"(1) Some have "tyArgs = []" and not_ghost: "name |\<notin>| TE_GhostVars env" and "ty = varTy"
      by (auto split: if_splits)
    from "3.prems"(2) Some not_ghost have "is_runtime_type varTy"
      unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
    with \<open>ty = varTy\<close> show ?thesis by simp
  qed
next
  case (4 env loc target_ty operand)
  (* BabTm_Cast: guard requires is_runtime_type target_ty when mode = NotGhost *)
  from "4.prems" show ?case
    by (auto split: option.splits if_splits)
next
  case (5 env loc op operand)
  (* BabTm_Unop: returns operand_ty which by IH is runtime type *)
  from "5.prems"(1) obtain operand_ty where
    operand_typed: "bab_term_type env NotGhost operand = Some operand_ty"
    by (auto split: option.splits)
  hence "is_runtime_type operand_ty"
    using "5.hyps" "5.prems"(2) by simp
  thus ?case
    using "5.prems"(1) operand_typed
    by (auto split: option.splits if_splits BabType.splits BabUnop.splits)
next
  case (6 env loc cond thenTm elseTm)
  (* BabTm_If: returns then_ty which by IH is runtime type *)
  obtain cond_ty where cond_typed: "bab_term_type env NotGhost cond = Some cond_ty"
    using "6.prems"(1) by (auto split: option.splits)
  obtain cond_loc where cond_bool: "cond_ty = BabTy_Bool cond_loc"
    using "6.prems"(1) cond_typed by (auto split: option.splits BabType.splits)
  obtain then_ty where then_typed: "bab_term_type env NotGhost thenTm = Some then_ty"
    using "6.prems"(1) cond_typed cond_bool by (auto split: option.splits)
  obtain else_ty where else_typed: "bab_term_type env NotGhost elseTm = Some else_ty"
    using "6.prems"(1) cond_typed cond_bool then_typed by (auto split: option.splits)
  have result: "ty = then_ty"
    using "6.prems"(1) cond_typed cond_bool then_typed else_typed by (auto split: if_splits)
  from then_typed have "is_runtime_type then_ty"
    using "6.hyps"(2) cond_typed cond_bool "6.prems"(2) by simp
  thus ?case
    using result by simp
next
  case ("7_1" env v vb)
  then show ?case sorry
next
  case ("7_2" env v vb)
  then show ?case sorry
next
  case ("7_3" env v va vb)
  then show ?case sorry
next
  case ("7_4" env v va vb)
  then show ?case sorry
next
  case ("7_5" env v va vb vc)
  then show ?case sorry
next
  case ("7_6" env v va vb)
  then show ?case sorry
next
  case ("7_7" env v va)
  then show ?case sorry
next
  case ("7_8" env v va)
  then show ?case sorry
next
  case ("7_9" env v va vb)
  then show ?case sorry
next
  case ("7_10" env v va vb)
  then show ?case sorry
next
  case ("7_11" env v va vb)
  then show ?case sorry
next
  case ("7_12" env v va vb)
  then show ?case sorry
next
  case ("7_13" env v va vb)
  then show ?case sorry
next
  case ("7_14" env v va)
  then show ?case sorry
next
  case ("7_15" env v va)
  then show ?case sorry
next
  case ("7_16" env v va)
  then show ?case sorry
qed


(* If typechecking succeeds, the returned type is well-kinded *)
lemma bab_term_type_well_kinded:
  assumes "bab_term_type env mode tm = Some ty"
      and "tyenv_well_formed env"
  shows "is_well_kinded env ty"
using assms
proof (induction env mode tm arbitrary: ty rule: bab_term_type.induct)
  case (1 uu uv loc uw)
  (* BabTm_Literal loc (BabLit_Bool _) -> BabTy_Bool loc *)
  then show ?case by auto
next
  case (2 ux uy loc i)
  (* BabTm_Literal loc (BabLit_Int i) -> BabTy_FiniteInt *)
  from "2.prems" show ?case
    by (auto split: option.splits)
next
  case (3 env mode loc name tyArgs)
  (* BabTm_Name: returns either a type from TE_TermVars or a BabTy_Name for a data ctor *)
  from "3.prems" show ?case
  proof (cases "fmlookup (TE_TermVars env) name")
    case None
    (* Data constructor case: need to show BabTy_Name dtName tyArgs is well-kinded *)
    from "3.prems"(1) None obtain dtName numTyArgs where
      ctor_lookup: "fmlookup (TE_DataCtors env) name = Some (dtName, numTyArgs, None)"
      and len_eq: "length tyArgs = numTyArgs"
      and tyargs_wk: "list_all (is_well_kinded env) tyArgs"
      and ty_eq: "ty = BabTy_Name loc dtName tyArgs"
      by (auto split: option.splits if_splits prod.splits)
    from "3.prems"(2) ctor_lookup obtain dt where
      dt_lookup: "fmlookup (TE_Datatypes env) dtName = Some dt"
      and args_len: "length (DD_TyArgs dt) = numTyArgs"
      and not_tyvar: "dtName |\<notin>| TE_TypeVars env"
      unfolding tyenv_well_formed_def tyenv_ctors_consistent_def by blast
    have "is_well_kinded env (BabTy_Name loc dtName tyArgs)"
      using dt_lookup args_len len_eq not_tyvar tyargs_wk
      by auto
    with ty_eq show ?thesis by simp
  next
    case (Some varTy)
    (* Variable case: use tyenv_well_formed *)
    from "3.prems"(1) Some have "ty = varTy"
      by (auto split: if_splits)
    from "3.prems"(2) Some have "is_well_kinded env varTy"
      unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
    with \<open>ty = varTy\<close> show ?thesis by simp
  qed
next
  case (4 env mode loc target_ty operand)
  (* BabTm_Cast: returns target_ty, which is an integer type *)
  from "4.prems" show ?case
    by (auto split: option.splits if_splits intro: is_integer_type_well_kinded)
next
  case (5 env mode loc op operand)
  (* BabTm_Unop: returns operand_ty which is either an integer type or bool *)
  from "5.prems"(1) obtain operand_ty where
    operand_typed: "bab_term_type env mode operand = Some operand_ty"
    by (auto split: option.splits)
  from "5.prems"(1) operand_typed show ?case
    by (auto split: option.splits if_splits BabType.splits BabUnop.splits
             intro: is_integer_type_well_kinded)
next
  case (6 env mode loc cond thenTm elseTm)
  (* BabTm_If: returns then_ty which by IH is well-kinded *)
  obtain cond_ty where cond_typed: "bab_term_type env mode cond = Some cond_ty"
    using "6.prems"(1) by (auto split: option.splits)
  obtain cond_loc where cond_bool: "cond_ty = BabTy_Bool cond_loc"
    using "6.prems"(1) cond_typed by (auto split: option.splits BabType.splits)
  obtain then_ty where then_typed: "bab_term_type env mode thenTm = Some then_ty"
    using "6.prems"(1) cond_typed cond_bool by (auto split: option.splits)
  obtain else_ty where else_typed: "bab_term_type env mode elseTm = Some else_ty"
    using "6.prems"(1) cond_typed cond_bool then_typed by (auto split: option.splits)
  have result: "ty = then_ty"
    using "6.prems"(1) cond_typed cond_bool then_typed else_typed by (auto split: if_splits)
  from then_typed have "is_well_kinded env then_ty"
    using "6.IH"(2) cond_typed cond_bool "6.prems"(2) by simp
  thus ?case
    using result by simp
next
  case ("7_1" env v vb)
  then show ?case sorry
next
  case ("7_2" env v vb)
  then show ?case sorry
next
  case ("7_3" env v va vb)
  then show ?case sorry
next
  case ("7_4" env v va vb)
  then show ?case sorry
next
  case ("7_5" env v va vb vc)
  then show ?case sorry
next
  case ("7_6" env v va vb)
  then show ?case sorry
next
  case ("7_7" env v va)
  then show ?case sorry
next
  case ("7_8" env v va)
  then show ?case sorry
next
  case ("7_9" env v va vb)
  then show ?case sorry
next
  case ("7_10" env v va vb)
  then show ?case sorry
next
  case ("7_11" env v va vb)
  then show ?case sorry
next
  case ("7_12" env v va vb)
  then show ?case sorry
next
  case ("7_13" env v va vb)
  then show ?case sorry
next
  case ("7_14" env v va)
  then show ?case sorry
next
  case ("7_15" env v va)
  then show ?case sorry
next
  case ("7_16" env v va)
  then show ?case sorry
qed

end

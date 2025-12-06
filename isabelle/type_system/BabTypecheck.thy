theory BabTypecheck
  imports TypeEnvWellFormed
begin

(* This defines type-correctness for fully elaborated terms. *)

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
            \<comment> \<open>Must be nullary (no payload), have correct number of well-kinded type args,
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

  (* Allocated: only valid in Ghost mode, parameter can be any type, result is bool *)
| "bab_term_type env mode (BabTm_Allocated loc tm) =
    (if mode = Ghost then
      (case bab_term_type env mode tm of
        Some _ \<Rightarrow> Some (BabTy_Bool loc)
      | None \<Rightarrow> None)
     else None)"

  (* Function call (pure functions only) *)
| "bab_term_type env mode (BabTm_Call loc callTm argTms) =
    (case callTm of
      BabTm_Name _ fnName tyArgs \<Rightarrow>
        (case fmlookup (TE_Functions env) fnName of
          None \<Rightarrow> None
        | Some funDecl \<Rightarrow>
            \<comment> \<open>Must be a pure function (not impure, no ref args)\<close>
            if DF_Impure funDecl \<or> list_ex (\<lambda>(_, vr, _). vr = Ref) (DF_TmArgs funDecl) then None
            \<comment> \<open>In NotGhost mode, the function must not be ghost\<close>
            else if mode = NotGhost \<and> DF_Ghost funDecl = Ghost then None
            \<comment> \<open>Type args count must match\<close>
            else if length tyArgs \<noteq> length (DF_TyArgs funDecl) then None
            \<comment> \<open>Type args must be well-kinded\<close>
            else if \<not> list_all (is_well_kinded env) tyArgs then None
            \<comment> \<open>In NotGhost mode, type args must be runtime types\<close>
            else if mode = NotGhost \<and> \<not> list_all is_runtime_type tyArgs then None
            \<comment> \<open>Term args count must match\<close>
            else if length argTms \<noteq> length (DF_TmArgs funDecl) then None
            \<comment> \<open>Must have a return type\<close>
            else (case DF_ReturnType funDecl of
              None \<Rightarrow> None
            | Some retTy \<Rightarrow>
                let tySubst = fmap_of_list (zip (DF_TyArgs funDecl) tyArgs);
                    expectedArgTys = map (\<lambda>(_, _, ty). substitute_bab_type tySubst ty) (DF_TmArgs funDecl);
                    actualArgTys = map (bab_term_type env mode) argTms
                in if list_all2 (\<lambda>actual expected.
                      case actual of None \<Rightarrow> False
                      | Some actualTy \<Rightarrow> types_equal actualTy expected) actualArgTys expectedArgTys
                   then Some (substitute_bab_type tySubst retTy)
                   else None))
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
  case (7 env loc tm)
  (* BabTm_Allocated: returns None in NotGhost mode, so this case is vacuously true *)
  from "7.prems"(1) show ?case by simp
next
  case (8 env loc callTm argTms)
  (* BabTm_Call: result type is substitute_bab_type tySubst retTy *)
  (* Extract function name and type args from callTm *)
  from "8.prems"(1) obtain fnLoc fnName tyArgs where
    callTm_eq: "callTm = BabTm_Name fnLoc fnName tyArgs"
    by (cases callTm) (auto split: option.splits)
  from "8.prems"(1) callTm_eq obtain funDecl where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funDecl"
    by (auto split: option.splits)
  from "8.prems"(1) callTm_eq fn_lookup have
    fn_not_ghost: "DF_Ghost funDecl \<noteq> Ghost" and
    tyargs_runtime: "list_all is_runtime_type tyArgs"
    by (auto split: option.splits if_splits)
  from fn_not_ghost have fn_is_notghost: "DF_Ghost funDecl = NotGhost"
    by (cases "DF_Ghost funDecl") auto
  from "8.prems"(1) callTm_eq fn_lookup obtain retTy where
    ret_some: "DF_ReturnType funDecl = Some retTy" and
    ty_eq: "ty = substitute_bab_type (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs)) retTy"
    by (auto split: option.splits if_splits simp: Let_def)
  (* From tyenv_well_formed, the function's return type is runtime (since fn is NotGhost) *)
  from "8.prems"(2) fn_lookup fn_is_notghost ret_some have retTy_runtime: "is_runtime_type retTy"
    unfolding tyenv_well_formed_def tyenv_functions_well_formed_def
    by (auto simp: Let_def split: option.splits)
  (* The substituted types are all runtime *)
  have subst_runtime: "\<forall>ty' \<in> fmran' (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs)). is_runtime_type ty'"
  proof
    fix ty' assume "ty' \<in> fmran' (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs))"
    then obtain name where "fmlookup (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs)) name = Some ty'"
      by (auto simp: fmran'I)
    then have "(name, ty') \<in> set (zip (DF_TyArgs funDecl) tyArgs)"
      by (metis fmap_of_list.rep_eq map_of_SomeD)
    then have "ty' \<in> set tyArgs"
      by (meson set_zip_rightD)
    with tyargs_runtime show "is_runtime_type ty'"
      by (simp add: list_all_iff)
  qed
  (* Apply is_runtime_type_substitute_bab_type *)
  from retTy_runtime subst_runtime have "is_runtime_type (substitute_bab_type (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs)) retTy)"
    by (rule is_runtime_type_substitute_bab_type)
  with ty_eq show ?case by simp
next
  case ("9_1" env v vb)
  then show ?case sorry
next
  case ("9_2" env v vb)
  then show ?case sorry
next
  case ("9_3" env v va vb)
  then show ?case sorry
next
  case ("9_4" env v va vb)
  then show ?case sorry
next
  case ("9_5" env v va vb vc)
  then show ?case sorry
next
  case ("9_6" env v va vb)
  then show ?case sorry
next
  case ("9_7" env v va)
  then show ?case sorry
next
  case ("9_8" env v va)
  then show ?case sorry
next
  case ("9_9" env v va vb)
  then show ?case sorry
next
  case ("9_10" env v va vb)
  then show ?case sorry
next
  case ("9_11" env v va vb)
  then show ?case sorry
next
  case ("9_12" env v va vb)
  then show ?case sorry
next
  case ("9_13" env v va vb)
  then show ?case sorry
next
  case ("9_14" env v va)
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
    from "3.prems"(2) ctor_lookup obtain tyVars where
      dt_lookup: "fmlookup (TE_Datatypes env) dtName = Some tyVars"
      and tyVars_len: "length tyVars = numTyArgs"
      and not_tyvar: "dtName |\<notin>| TE_TypeVars env"
      using tyenv_ctors_consistent_def tyenv_well_formed_def by blast
    have "is_well_kinded env (BabTy_Name loc dtName tyArgs)"
      using dt_lookup tyVars_len len_eq not_tyvar tyargs_wk
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
  case (7 env mode loc tm)
  (* BabTm_Allocated: returns BabTy_Bool which is always well-kinded *)
  from "7.prems"(1) show ?case by (auto split: if_splits option.splits)
next
  case (8 env mode loc callTm argTms)
  (* BabTm_Call: result type is substitute_bab_type tySubst retTy *)
  (* Extract function name and type args from callTm *)
  from "8.prems"(1) obtain fnLoc fnName tyArgs where
    callTm_eq: "callTm = BabTm_Name fnLoc fnName tyArgs"
    by (cases callTm) (auto split: option.splits)
  from "8.prems"(1) callTm_eq obtain funDecl where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funDecl"
    by (auto split: option.splits)
  from "8.prems"(1) callTm_eq fn_lookup have
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyargs_len: "length tyArgs = length (DF_TyArgs funDecl)"
    by (auto split: option.splits if_splits)
  from "8.prems"(1) callTm_eq fn_lookup obtain retTy where
    ret_some: "DF_ReturnType funDecl = Some retTy" and
    ty_eq: "ty = substitute_bab_type (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs)) retTy"
    by (auto split: option.splits if_splits simp: Let_def)
  (* From tyenv_well_formed, the function's return type is well-kinded in extended env *)
  let ?extEnv = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list (DF_TyArgs funDecl) \<rparr>"
  from "8.prems"(2) fn_lookup ret_some have retTy_wk_ext: "is_well_kinded ?extEnv retTy"
    unfolding tyenv_well_formed_def tyenv_functions_well_formed_def env_with_tyvars_def
    by (auto simp: Let_def split: option.splits)
  (* The extra type variables (DF_TyArgs funDecl) don't shadow datatype names in a well-formed env *)
  from "8.prems"(2) fn_lookup have extra_disjoint: "fset_of_list (DF_TyArgs funDecl) |\<inter>| fmdom (TE_Datatypes env) = {||}"
    unfolding tyenv_well_formed_def tyenv_functions_well_formed_def
    by (auto simp: Let_def)
  (* The substitution domain covers the extra type variables *)
  have extra_subset: "fset_of_list (DF_TyArgs funDecl) |\<subseteq>| fmdom (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs))"
    using tyargs_len by (auto simp: fset_of_list_elem set_zip_leftD)
  (* The substitution maps to well-kinded types *)
  have subst_wk: "subst_types_well_kinded env (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs))"
    using tyargs_wk by (rule subst_types_well_kinded_from_zip)
  (* Apply is_well_kinded_substitute_across_ext *)
  from is_well_kinded_substitute_across_ext[OF retTy_wk_ext extra_disjoint extra_subset subst_wk]
  have "is_well_kinded env (substitute_bab_type (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs)) retTy)"
    by simp
  with ty_eq show ?case by simp
next
  case ("9_1" env v vb)
  then show ?case sorry
next
  case ("9_2" env v vb)
  then show ?case sorry
next
  case ("9_3" env v va vb)
  then show ?case sorry
next
  case ("9_4" env v va vb)
  then show ?case sorry
next
  case ("9_5" env v va vb vc)
  then show ?case sorry
next
  case ("9_6" env v va vb)
  then show ?case sorry
next
  case ("9_7" env v va)
  then show ?case sorry
next
  case ("9_8" env v va)
  then show ?case sorry
next
  case ("9_9" env v va vb)
  then show ?case sorry
next
  case ("9_10" env v va vb)
  then show ?case sorry
next
  case ("9_11" env v va vb)
  then show ?case sorry
next
  case ("9_12" env v va vb)
  then show ?case sorry
next
  case ("9_13" env v va vb)
  then show ?case sorry
next
  case ("9_14" env v va)
  then show ?case sorry
qed


end

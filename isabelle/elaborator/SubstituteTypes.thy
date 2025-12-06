theory SubstituteTypes
  imports "../type_system/BabTypecheck" "Unify"
begin

(* Substitute type metavariables (BabTy_Meta) in a term. *)
(* This is only intended to be used on fully elaborated terms (e.g. BabDim_Fixed is not
   accounted for). *)
fun apply_subst_to_term :: "MetaSubst \<Rightarrow> BabTerm \<Rightarrow> BabTerm" where
  "apply_subst_to_term subst (BabTm_Literal loc lit) = BabTm_Literal loc lit"
| "apply_subst_to_term subst (BabTm_Name loc name tyargs) =
    BabTm_Name loc name (map (apply_subst subst) tyargs)"
| "apply_subst_to_term subst (BabTm_Cast loc ty tm) =
    BabTm_Cast loc (apply_subst subst ty) (apply_subst_to_term subst tm)"
| "apply_subst_to_term subst (BabTm_If loc cond t e) =
    BabTm_If loc (apply_subst_to_term subst cond)
                 (apply_subst_to_term subst t)
                 (apply_subst_to_term subst e)"
| "apply_subst_to_term subst (BabTm_Unop loc op tm) =
    BabTm_Unop loc op (apply_subst_to_term subst tm)"
| "apply_subst_to_term subst (BabTm_Binop loc tm ops) =
    BabTm_Binop loc (apply_subst_to_term subst tm)
                    (map (\<lambda>(op, tm). (op, apply_subst_to_term subst tm)) ops)"
| "apply_subst_to_term subst (BabTm_Let loc name rhs body) =
    BabTm_Let loc name (apply_subst_to_term subst rhs)
                       (apply_subst_to_term subst body)"
| "apply_subst_to_term subst (BabTm_Quantifier loc q var ty body) =
    BabTm_Quantifier loc q var (apply_subst subst ty)
                               (apply_subst_to_term subst body)"
| "apply_subst_to_term subst (BabTm_Call loc fn args) =
    BabTm_Call loc (apply_subst_to_term subst fn)
                   (map (apply_subst_to_term subst) args)"
| "apply_subst_to_term subst (BabTm_Tuple loc tms) =
    BabTm_Tuple loc (map (apply_subst_to_term subst) tms)"
| "apply_subst_to_term subst (BabTm_Record loc flds) =
    BabTm_Record loc (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds)"
| "apply_subst_to_term subst (BabTm_RecordUpdate loc tm flds) =
    BabTm_RecordUpdate loc (apply_subst_to_term subst tm)
                           (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds)"
| "apply_subst_to_term subst (BabTm_TupleProj loc tm n) =
    BabTm_TupleProj loc (apply_subst_to_term subst tm) n"
| "apply_subst_to_term subst (BabTm_RecordProj loc tm fld) =
    BabTm_RecordProj loc (apply_subst_to_term subst tm) fld"
| "apply_subst_to_term subst (BabTm_ArrayProj loc tm idxs) =
    BabTm_ArrayProj loc (apply_subst_to_term subst tm)
                        (map (apply_subst_to_term subst) idxs)"
| "apply_subst_to_term subst (BabTm_Match loc tm cases) =
    BabTm_Match loc (apply_subst_to_term subst tm)
                    (map (\<lambda>(pat, tm). (pat, apply_subst_to_term subst tm)) cases)"
| "apply_subst_to_term subst (BabTm_Sizeof loc tm) =
    BabTm_Sizeof loc (apply_subst_to_term subst tm)"
| "apply_subst_to_term subst (BabTm_Allocated loc tm) =
    BabTm_Allocated loc (apply_subst_to_term subst tm)"
| "apply_subst_to_term subst (BabTm_Old loc tm) =
    BabTm_Old loc (apply_subst_to_term subst tm)"


(* Helper lemmas: type predicates are preserved by apply_subst for non-meta types *)

lemma is_integer_type_apply_subst:
  "is_integer_type ty \<Longrightarrow> is_integer_type (apply_subst subst ty)"
  by (cases ty) auto

lemma is_signed_integer_type_apply_subst:
  "is_signed_integer_type ty \<Longrightarrow> is_signed_integer_type (apply_subst subst ty)"
  by (cases ty) auto

lemma is_finite_integer_type_apply_subst:
  "is_finite_integer_type ty \<Longrightarrow> is_finite_integer_type (apply_subst subst ty)"
  by (cases ty) auto

(* See also: compose_subst_preserves_well_kinded in Unify3.thy *)
lemma is_well_kinded_apply_subst:
  assumes "is_well_kinded env ty"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
  shows "is_well_kinded env (apply_subst subst ty)"
using assms proof (induction ty rule: measure_induct_rule[where f=bab_type_size])
  case (less ty)
  show ?case
  proof (cases ty)
    case (BabTy_Meta n)
    then show ?thesis using "less.prems"(2)
      by (auto simp: fmran'I split: option.splits)
  next
    case (BabTy_Name loc name tyargs)
    show ?thesis
    proof (cases "name |\<in>| TE_TypeVars env")
      case True
      with "less.prems"(1) BabTy_Name have "tyargs = []" by simp
      with True BabTy_Name show ?thesis by simp
    next
      case False
      with "less.prems"(1) BabTy_Name obtain tyVars where
        dt_lookup: "fmlookup (TE_Datatypes env) name = Some tyVars" and
        len_eq: "length tyargs = length tyVars" and
        args_wk: "list_all (is_well_kinded env) tyargs"
        by (auto split: option.splits)
      have "\<forall>arg \<in> set tyargs. is_well_kinded env (apply_subst subst arg)"
      proof
        fix arg assume "arg \<in> set tyargs"
        hence "bab_type_size arg < bab_type_size ty"
          using BabTy_Name bab_type_smaller_than_list by fastforce
        moreover have "is_well_kinded env arg"
          using args_wk \<open>arg \<in> set tyargs\<close> by (simp add: list_all_iff)
        ultimately show "is_well_kinded env (apply_subst subst arg)"
          using "less.IH" "less.prems"(2) by blast
      qed
      hence "list_all (is_well_kinded env) (map (apply_subst subst) tyargs)"
        by (simp add: list_all_iff)
      with False dt_lookup len_eq BabTy_Name show ?thesis by simp
    qed
  next
    case (BabTy_Bool loc)
    then show ?thesis by simp
  next
    case (BabTy_FiniteInt loc sign bits)
    then show ?thesis by simp
  next
    case (BabTy_MathInt loc)
    then show ?thesis by simp
  next
    case (BabTy_MathReal loc)
    then show ?thesis by simp
  next
    case (BabTy_Tuple loc tys)
    have "\<forall>t \<in> set tys. is_well_kinded env (apply_subst subst t)"
    proof
      fix t assume "t \<in> set tys"
      hence "bab_type_size t < bab_type_size ty"
        using BabTy_Tuple bab_type_smaller_than_list by fastforce
      moreover have "is_well_kinded env t"
        using "less.prems"(1) BabTy_Tuple \<open>t \<in> set tys\<close> by (simp add: list_all_iff)
      ultimately show "is_well_kinded env (apply_subst subst t)"
        using "less.IH" "less.prems"(2) by blast
    qed
    then show ?thesis using BabTy_Tuple by (simp add: list_all_iff)
  next
    case (BabTy_Record loc flds)
    have "\<forall>f \<in> set flds. is_well_kinded env (apply_subst subst (snd f))"
    proof
      fix f assume "f \<in> set flds"
      hence "bab_type_size (snd f) < bab_type_size ty"
        using BabTy_Record bab_type_smaller_than_fieldlist[of "fst f" "snd f" flds] by simp
      moreover have "is_well_kinded env (snd f)"
        using "less.prems"(1) BabTy_Record \<open>f \<in> set flds\<close> by (auto simp: list_all_iff)
      ultimately show "is_well_kinded env (apply_subst subst (snd f))"
        using "less.IH" "less.prems"(2) by blast
    qed
    then show ?thesis using BabTy_Record by (auto simp: list_all_iff)
  next
    case (BabTy_Array loc elem dims)
    have "bab_type_size elem < bab_type_size ty"
      using BabTy_Array by simp
    moreover have "is_well_kinded env elem"
      using "less.prems"(1) BabTy_Array by simp
    ultimately have "is_well_kinded env (apply_subst subst elem)"
      using "less.IH" "less.prems"(2) by blast
    moreover have "array_dims_well_kinded dims"
      using "less.prems"(1) BabTy_Array by simp
    ultimately show ?thesis using BabTy_Array by simp
  qed
qed

(* See also: compose_subst_preserves_runtime in Unify3.thy *)
lemma is_runtime_type_apply_subst:
  assumes "is_runtime_type ty"
      and "\<forall>ty' \<in> fmran' subst. is_runtime_type ty'"
  shows "is_runtime_type (apply_subst subst ty)"
using assms proof (induction ty rule: is_runtime_type.induct)
  (* BabTy_Meta case *)
  case ("7_3" n)
  then show ?case
    by (auto simp: fmran'I split: option.splits)
next
  (* BabTy_Name case *)
  case (3 uw ux tyArgs)
  then show ?case by (simp add: list_all_iff)
next
  (* Tuple case *)
  case (4 uy tys)
  then show ?case by (simp add: list_all_iff)
next
  (* Record case *)
  case (5 uz flds)
  then show ?case by (auto simp add: list_all_iff)
next
  (* Array case *)
  case (6 va ty vb)
  then show ?case by simp
qed (simp_all)

lemma types_equal_apply_subst_both:
  "types_equal ty1 ty2 \<Longrightarrow> types_equal (apply_subst subst ty1) (apply_subst subst ty2)"
  using types_equal_apply_subst by blast


(* If a term has type ty, then apply_subst_to_term subst tm has type (apply_subst subst ty).
   We assume the environment is well-formed (types are ground) and that the substitution
   produces well-kinded and (in NotGhost mode) runtime types. *)
lemma apply_subst_to_term_preserves_typing:
  assumes "bab_term_type env mode tm = Some ty"
      and "tyenv_well_formed env"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and "mode = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ty')"
  shows "bab_term_type env mode (apply_subst_to_term subst tm) = Some (apply_subst subst ty)"
using assms proof (induction env mode tm arbitrary: ty rule: bab_term_type.induct)
  (* Case 1: Bool literal *)
  case (1 uu uv loc uw)
  then show ?case by auto
next
  (* Case 2: Int literal *)
  case (2 ux uy loc i)
  then show ?case by (auto split: option.splits)
next
  (* Case 3: BabTm_Name *)
  case (3 env mode loc name tyArgs)
  (* apply_subst_to_term only substitutes in tyArgs, env is unchanged *)
  from "3.prems" show ?case
  proof (cases "fmlookup (TE_TermVars env) name")
    case None
    (* Data constructor case *)
    with "3.prems" show ?thesis
      by (auto split: option.splits if_splits prod.splits
               simp: list_all_iff is_runtime_type_apply_subst is_well_kinded_apply_subst)
  next
    case (Some varTy)
    (* Variable case: use tyenv_well_formed to show varTy is ground *)
    from "3.prems"(2) Some have "is_ground varTy"
      unfolding tyenv_well_formed_def tyenv_vars_ground_def by blast
    hence "apply_subst subst varTy = varTy"
      by (rule apply_subst_ground)
    with "3.prems"(1) Some show ?thesis
      by (auto split: if_splits)
  qed
next
  (* Case 4: Cast *)
  case (4 env mode loc target_ty operand)
  from 4(2) obtain operand_ty where
    operand_typed: "bab_term_type env mode operand = Some operand_ty" and
    is_int_operand: "is_integer_type operand_ty" and
    is_int_target: "is_integer_type target_ty" and
    runtime_ok: "mode = NotGhost \<longrightarrow> is_runtime_type target_ty" and
    ty_eq: "ty = target_ty"
    by (auto split: option.splits if_splits)
  from 4(1)[OF operand_typed "4.prems"(2) "4.prems"(3) "4.prems"(4)]
  have ih: "bab_term_type env mode (apply_subst_to_term subst operand) = Some (apply_subst subst operand_ty)" .
  have "is_integer_type (apply_subst subst operand_ty)"
    using is_int_operand is_integer_type_apply_subst by blast
  moreover have "is_integer_type (apply_subst subst target_ty)"
    using is_int_target is_integer_type_apply_subst by blast
  moreover have "mode = NotGhost \<longrightarrow> is_runtime_type (apply_subst subst target_ty)"
    using runtime_ok "4.prems"(4) is_runtime_type_apply_subst by blast
  ultimately show ?case using ih ty_eq by simp
next
  (* Case 5: Unop *)
  case (5 env mode loc op operand)
  from 5(2) obtain operand_ty where
    operand_typed: "bab_term_type env mode operand = Some operand_ty" and
    ty_eq: "ty = operand_ty"
    by (auto split: option.splits if_splits BabUnop.splits BabType.splits)
  from 5(1)[OF operand_typed "5.prems"(2) "5.prems"(3) "5.prems"(4)]
  have ih: "bab_term_type env mode (apply_subst_to_term subst operand) = Some (apply_subst subst operand_ty)" .
  show ?case
  proof (cases op)
    case BabUnop_Negate
    with 5(2) operand_typed ty_eq have "is_signed_integer_type operand_ty"
      by (auto split: option.splits if_splits)
    hence "is_signed_integer_type (apply_subst subst operand_ty)"
      using is_signed_integer_type_apply_subst by blast
    then show ?thesis using ih ty_eq BabUnop_Negate by simp
  next
    case BabUnop_Complement
    with 5(2) operand_typed ty_eq have "is_finite_integer_type operand_ty"
      by (auto split: option.splits if_splits)
    hence "is_finite_integer_type (apply_subst subst operand_ty)"
      using is_finite_integer_type_apply_subst by blast
    then show ?thesis using ih ty_eq BabUnop_Complement by simp
  next
    case BabUnop_Not
    with 5(2) operand_typed ty_eq obtain bloc where "operand_ty = BabTy_Bool bloc"
      by (auto split: option.splits if_splits BabType.splits)
    then show ?thesis using ih ty_eq BabUnop_Not by simp
  qed
next
  (* Case 6: If-then-else *)
  case (6 env mode loc cond thenTm elseTm)
  from 6(4) obtain cond_ty then_ty else_ty where
    cond_typed: "bab_term_type env mode cond = Some cond_ty" and
    then_typed: "bab_term_type env mode thenTm = Some then_ty" and
    else_typed: "bab_term_type env mode elseTm = Some else_ty"
    by (auto split: option.splits if_splits BabType.splits)
  from 6(4) cond_typed then_typed else_typed obtain cond_loc where
    cond_bool: "cond_ty = BabTy_Bool cond_loc" and
    branches_eq: "types_equal then_ty else_ty" and
    ty_eq: "ty = then_ty"
    by (auto split: option.splits if_splits BabType.splits simp del: types_equal.simps)
  from 6(1)[OF cond_typed "6.prems"(2) "6.prems"(3) "6.prems"(4)]
  have ih_cond: "bab_term_type env mode (apply_subst_to_term subst cond) = Some (apply_subst subst cond_ty)" .
  from 6(2)[OF then_typed "6.prems"(2) "6.prems"(3) "6.prems"(4)]
  have ih_then: "bab_term_type env mode (apply_subst_to_term subst thenTm) = Some (apply_subst subst then_ty)" .
  from 6(3)[OF else_typed "6.prems"(2) "6.prems"(3) "6.prems"(4)]
  have ih_else: "bab_term_type env mode (apply_subst_to_term subst elseTm) = Some (apply_subst subst else_ty)" .
  have "types_equal (apply_subst subst then_ty) (apply_subst subst else_ty)"
    using branches_eq types_equal_apply_subst_both by blast
  then show ?case using ih_cond ih_then ih_else ty_eq cond_bool by simp
next
  (* Case 7: BabTm_Allocated *)
  case (7 env mode loc tm)
  from "7.prems"(1) have mode_ghost: "mode = Ghost"
    by (auto split: if_splits)
  from "7.prems"(1) mode_ghost obtain inner_ty where
    inner_typed: "bab_term_type env mode tm = Some inner_ty" and
    ty_eq: "ty = BabTy_Bool loc"
    by (auto split: if_splits option.splits)
  from 7(1)[OF mode_ghost inner_typed "7.prems"(2) "7.prems"(3) "7.prems"(4)]
  have ih: "bab_term_type env mode (apply_subst_to_term subst tm) = Some (apply_subst subst inner_ty)" .
  show ?case using ih mode_ghost ty_eq by simp
next
  (* Case 8: BabTm_Call *)
  case (8 env mode loc callTm argTms)
  (* The typing assumption tells us callTm must be a BabTm_Name *)
  from "8.prems"(1) obtain fnLoc fnName tyArgs where
    callTm_eq: "callTm = BabTm_Name fnLoc fnName tyArgs"
    by (cases callTm) (auto split: option.splits)
  from "8.prems"(1) callTm_eq obtain funDecl where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funDecl"
    by (auto split: option.splits)
  from "8.prems"(1) callTm_eq fn_lookup have
    not_impure: "\<not> DF_Impure funDecl" and
    no_refs: "\<not> list_ex (\<lambda>(_, vr, _). vr = Ref) (DF_TmArgs funDecl)" and
    tyargs_len: "length tyArgs = length (DF_TyArgs funDecl)" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyargs_rt: "mode = NotGhost \<longrightarrow> list_all is_runtime_type tyArgs" and
    args_len: "length argTms = length (DF_TmArgs funDecl)"
    by (auto split: option.splits if_splits)
  from "8.prems"(1) callTm_eq fn_lookup not_impure no_refs tyargs_len tyargs_wk tyargs_rt args_len
  obtain retTy where
    ret_some: "DF_ReturnType funDecl = Some retTy" and
    args_typecheck: "list_all2 (\<lambda>actual expected.
        case actual of None \<Rightarrow> False
        | Some actualTy \<Rightarrow> types_equal actualTy expected)
        (map (bab_term_type env mode) argTms)
        (map (\<lambda>(_, _, ty). substitute_bab_type (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs)) ty)
             (DF_TmArgs funDecl))" and
    ty_eq: "ty = substitute_bab_type (fmap_of_list (zip (DF_TyArgs funDecl) tyArgs)) retTy"
    by (auto split: option.splits if_splits simp: Let_def)

  (* After substitution, the callTm becomes BabTm_Name fnLoc fnName (map (apply_subst subst) tyArgs) *)
  have subst_callTm: "apply_subst_to_term subst callTm = BabTm_Name fnLoc fnName (map (apply_subst subst) tyArgs)"
    using callTm_eq by simp

  (* The substituted type args are still well-kinded *)
  have subst_tyargs_wk: "list_all (is_well_kinded env) (map (apply_subst subst) tyArgs)"
    using tyargs_wk "8.prems"(3) is_well_kinded_apply_subst by (simp add: list_all_iff)

  (* The substituted type args are still runtime types in NotGhost mode *)
  have subst_tyargs_rt: "mode = NotGhost \<longrightarrow> list_all is_runtime_type (map (apply_subst subst) tyArgs)"
    using tyargs_rt "8.prems"(4) is_runtime_type_apply_subst by (simp add: list_all_iff)

  (* Length of substituted type args is preserved *)
  have subst_tyargs_len: "length (map (apply_subst subst) tyArgs) = length (DF_TyArgs funDecl)"
    using tyargs_len by simp

  (* Length of substituted arg terms is preserved *)
  have subst_args_len: "length (map (apply_subst_to_term subst) argTms) = length (DF_TmArgs funDecl)"
    using args_len by simp

  (* For each argument, by IH, the substituted term has the substituted type *)
  (* We need to show the substituted args typecheck against the substituted expected types *)

  (* The key insight: substitute_bab_type (fmap_of_list (zip tyVars (map (apply_subst subst) tyArgs))) ty
     = apply_subst subst (substitute_bab_type (fmap_of_list (zip tyVars tyArgs)) ty)
     This requires a lemma about composing substitutions. For now, we use sorry. *)

  show ?case sorry
next
  case ("9_1" env mode v vb)
  then show ?case sorry
next
  case ("9_2" env mode v vb)
  then show ?case sorry
next
  case ("9_3" env mode v va vb)
  then show ?case sorry
next
  case ("9_4" env mode v va vb)
  then show ?case sorry
next
  case ("9_5" env mode v va vb vc)
  then show ?case sorry
next
  case ("9_6" env mode v va vb)
  then show ?case sorry
next
  case ("9_7" env mode v va)
  then show ?case sorry
next
  case ("9_8" env mode v va)
  then show ?case sorry
next
  case ("9_9" env mode v va vb)
  then show ?case sorry
next
  case ("9_10" env mode v va vb)
  then show ?case sorry
next
  case ("9_11" env mode v va vb)
  then show ?case sorry
next
  case ("9_12" env mode v va vb)
  then show ?case sorry
next
  case ("9_13" env mode v va)
  then show ?case sorry
next
  case ("9_14" env mode v va)
  then show ?case sorry
qed


(* Key lemma: substitute_bab_type commutes with apply_subst (metavariable substitution).
   This says that applying a metavariable substitution after a type variable substitution
   is the same as first applying the metavariable substitution to the type arguments,
   then doing the type variable substitution.

   substitute_bab_type (fmap_of_list (zip tyVars (map (apply_subst metaSubst) tyArgs))) ty
   = apply_subst metaSubst (substitute_bab_type (fmap_of_list (zip tyVars tyArgs)) ty)

   This requires that ty is ground (contains no metavariables), because:
   - substitute_bab_type does not touch BabTy_Meta nodes
   - apply_subst does substitute BabTy_Meta nodes
   So if ty contains metavariables, the RHS would substitute them but the LHS would not. *)
lemma substitute_bab_type_apply_subst_commute:
  assumes "is_ground ty"
  shows "substitute_bab_type (fmap_of_list (zip tyVars (map (apply_subst metaSubst) tyArgs))) ty
         = apply_subst metaSubst (substitute_bab_type (fmap_of_list (zip tyVars tyArgs)) ty)"
  using assms sorry


end

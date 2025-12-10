theory SubstituteTypesInTerm
  imports "../core/CoreTypecheck"
begin

(* Substitute type metavariables (CoreTy_Meta) in a term. *)

fun apply_subst_to_term :: "MetaSubst \<Rightarrow> CoreTerm \<Rightarrow> CoreTerm" where
  "apply_subst_to_term subst (CoreTm_LitBool b) = CoreTm_LitBool b"
| "apply_subst_to_term subst (CoreTm_LitInt i) = CoreTm_LitInt i"
| "apply_subst_to_term subst (CoreTm_LitArray tms) =
    CoreTm_LitArray (map (apply_subst_to_term subst) tms)"
| "apply_subst_to_term subst (CoreTm_Var name) = CoreTm_Var name"
| "apply_subst_to_term subst (CoreTm_Cast ty tm) =
    CoreTm_Cast (apply_subst subst ty) (apply_subst_to_term subst tm)"
| "apply_subst_to_term subst (CoreTm_Unop op tm) =
    CoreTm_Unop op (apply_subst_to_term subst tm)"
| "apply_subst_to_term subst (CoreTm_Binop op tm1 tm2) =
    CoreTm_Binop op (apply_subst_to_term subst tm1) (apply_subst_to_term subst tm2)"
| "apply_subst_to_term subst (CoreTm_Let name rhs body) =
    CoreTm_Let name (apply_subst_to_term subst rhs) (apply_subst_to_term subst body)"
| "apply_subst_to_term subst (CoreTm_Quantifier q var ty body) =
    CoreTm_Quantifier q var (apply_subst subst ty) (apply_subst_to_term subst body)"
| "apply_subst_to_term subst (CoreTm_FunctionCall fnName tyArgs args) =
    CoreTm_FunctionCall fnName (map (apply_subst subst) tyArgs)
                               (map (apply_subst_to_term subst) args)"
| "apply_subst_to_term subst (CoreTm_VariantCtor ctorName tyArgs arg) =
    CoreTm_VariantCtor ctorName (map (apply_subst subst) tyArgs)
                                (apply_subst_to_term subst arg)"
| "apply_subst_to_term subst (CoreTm_Record flds) =
    CoreTm_Record (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds)"
| "apply_subst_to_term subst (CoreTm_RecordProj tm fldName) =
    CoreTm_RecordProj (apply_subst_to_term subst tm) fldName"
| "apply_subst_to_term subst (CoreTm_ArrayProj tm idxs) =
    CoreTm_ArrayProj (apply_subst_to_term subst tm)
                     (map (apply_subst_to_term subst) idxs)"
| "apply_subst_to_term subst (CoreTm_VariantProj tm ctorName) =
    CoreTm_VariantProj (apply_subst_to_term subst tm) ctorName"
| "apply_subst_to_term subst (CoreTm_Match tm cases) =
    CoreTm_Match (apply_subst_to_term subst tm)
                 (map (\<lambda>(pat, tm). (pat, apply_subst_to_term subst tm)) cases)"
| "apply_subst_to_term subst (CoreTm_Sizeof tm) =
    CoreTm_Sizeof (apply_subst_to_term subst tm)"
| "apply_subst_to_term subst (CoreTm_Allocated tm) =
    CoreTm_Allocated (apply_subst_to_term subst tm)"
| "apply_subst_to_term subst (CoreTm_Old tm) =
    CoreTm_Old (apply_subst_to_term subst tm)"


(* Helper for proving map over lists *)
lemma map_apply_subst_to_term_empty:
  "(\<And>t. t \<in> set tms \<Longrightarrow> apply_subst_to_term fmempty t = t) \<Longrightarrow>
   map (apply_subst_to_term fmempty) tms = tms"
  by (induction tms) auto


(* Empty substitution leaves term unchanged *)
lemma apply_subst_to_term_empty [simp]:
  "apply_subst_to_term fmempty tm = tm"
proof (induction tm)
  case (CoreTm_LitArray tms)
  thus ?case using map_apply_subst_to_term_empty by simp
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  thus ?case using map_apply_subst_to_term_empty by simp
next
  case (CoreTm_VariantCtor ctorName tyArgs arg)
  thus ?case by simp
next
  case (CoreTm_Record flds)
  have "map (\<lambda>(name, tm). (name, apply_subst_to_term fmempty tm)) flds = flds"
  proof -
    have "\<forall>(n, t) \<in> set flds. apply_subst_to_term fmempty t = t"
      using CoreTm_Record.IH by auto
    thus ?thesis by (induction flds) auto
  qed
  thus ?case by simp
next
  case (CoreTm_ArrayProj tm idxs)
  thus ?case using map_apply_subst_to_term_empty by simp
next
  case (CoreTm_Match tm cases)
  have "map (\<lambda>(pat, tm). (pat, apply_subst_to_term fmempty tm)) cases = cases"
  proof -
    have "\<forall>(p, t) \<in> set cases. apply_subst_to_term fmempty t = t"
      using CoreTm_Match.IH by auto
    thus ?thesis by (induction cases) auto
  qed
  thus ?case using CoreTm_Match.IH by simp
qed simp_all


(* Composing substitutions: applying s2 after s1 is the same as applying (compose_subst s2 s1) *)
lemma apply_subst_to_term_compose:
  "apply_subst_to_term s2 (apply_subst_to_term s1 tm) =
   apply_subst_to_term (compose_subst s2 s1) tm"
proof (induction tm)
  case (CoreTm_Cast ty tm)
  thus ?case by (simp add: compose_subst_correct[symmetric])
next
  case (CoreTm_Quantifier q var ty body)
  thus ?case by (simp add: compose_subst_correct[symmetric])
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  have "map (apply_subst s2) (map (apply_subst s1) tyArgs) =
        map (apply_subst (compose_subst s2 s1)) tyArgs"
    by (simp add: compose_subst_correct[symmetric])
  moreover have "map (apply_subst_to_term s2) (map (apply_subst_to_term s1) args) =
                 map (apply_subst_to_term (compose_subst s2 s1)) args"
    using CoreTm_FunctionCall by (induction args) auto
  ultimately show ?case by simp
next
  case (CoreTm_VariantCtor ctorName tyArgs arg)
  have "map (apply_subst s2) (map (apply_subst s1) tyArgs) =
        map (apply_subst (compose_subst s2 s1)) tyArgs"
    by (simp add: compose_subst_correct[symmetric])
  thus ?case using CoreTm_VariantCtor by simp
next
  case (CoreTm_Record flds)
  have "map (\<lambda>(name, tm). (name, apply_subst_to_term s2 tm))
            (map (\<lambda>(name, tm). (name, apply_subst_to_term s1 tm)) flds) =
        map (\<lambda>(name, tm). (name, apply_subst_to_term (compose_subst s2 s1) tm)) flds"
  proof -
    have "\<forall>(n, t) \<in> set flds.
          apply_subst_to_term s2 (apply_subst_to_term s1 t) =
          apply_subst_to_term (compose_subst s2 s1) t"
      using CoreTm_Record.IH by auto
    thus ?thesis by (induction flds) auto
  qed
  thus ?case by simp
next
  case (CoreTm_Match tm cases)
  have "map (\<lambda>(pat, tm). (pat, apply_subst_to_term s2 tm))
            (map (\<lambda>(pat, tm). (pat, apply_subst_to_term s1 tm)) cases) =
        map (\<lambda>(pat, tm). (pat, apply_subst_to_term (compose_subst s2 s1) tm)) cases"
  proof -
    have "\<forall>(p, t) \<in> set cases.
          apply_subst_to_term s2 (apply_subst_to_term s1 t) =
          apply_subst_to_term (compose_subst s2 s1) t"
      using CoreTm_Match.IH by auto
    thus ?thesis by (induction cases) auto
  qed
  thus ?case using CoreTm_Match.IH by simp
qed simp_all


(* If a term has type ty, then apply_subst_to_term subst tm has type (apply_subst subst ty).
   We assume the environment is well-formed, and that the substitution produces well-kinded 
   and (in NotGhost mode) runtime types. *)
lemma apply_subst_to_term_preserves_typing:
  assumes "core_term_type env mode tm = Some ty"
      and "tyenv_well_formed env"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and "mode = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ty')"
  shows "core_term_type env mode (apply_subst_to_term subst tm) = Some (apply_subst subst ty)"
using assms proof (induction tm arbitrary: ty mode)
  case (CoreTm_LitBool b)
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray tms)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_Var name)
  from CoreTm_Var.prems(1) obtain varTy where
    lookup: "fmlookup (TE_TermVars env) name = Some varTy" and
    ty_eq: "ty = varTy"
    by (auto split: option.splits if_splits)
  (* The variable's type is ground (from tyenv_well_formed) *)
  have "tyenv_vars_ground env"
    using CoreTm_Var.prems(2) tyenv_well_formed_def by blast
  hence "is_ground varTy"
    using lookup tyenv_vars_ground_def by blast
  hence "apply_subst subst varTy = varTy"
    by (rule apply_subst_ground)
  thus ?case using CoreTm_Var.prems(1) lookup ty_eq by auto
next
  case (CoreTm_Cast targetTy operand)
  from CoreTm_Cast.prems(1) obtain operandTy where
    operand_typed: "core_term_type env mode operand = Some operandTy" and
    is_int_operand: "is_integer_type operandTy" and
    is_int_target: "is_integer_type targetTy" and
    runtime_ok: "mode = NotGhost \<longrightarrow> is_runtime_type targetTy" and
    ty_eq: "ty = targetTy"
    by (auto split: option.splits if_splits)
  from CoreTm_Cast.IH[OF operand_typed CoreTm_Cast.prems(2) CoreTm_Cast.prems(3) CoreTm_Cast.prems(4)]
  have ih: "core_term_type env mode (apply_subst_to_term subst operand) = Some (apply_subst subst operandTy)" .
  have "is_integer_type (apply_subst subst operandTy)"
    using is_int_operand is_integer_type_apply_subst by blast
  moreover have "is_integer_type (apply_subst subst targetTy)"
    using is_int_target is_integer_type_apply_subst by blast
  moreover have "mode = NotGhost \<longrightarrow> is_runtime_type (apply_subst subst targetTy)"
    using runtime_ok CoreTm_Cast.prems(4) apply_subst_preserves_runtime by blast
  ultimately show ?case using ih ty_eq by simp
next
  case (CoreTm_Unop op operand)
  from CoreTm_Unop.prems(1) obtain operandTy where
    operand_typed: "core_term_type env mode operand = Some operandTy" and
    ty_eq: "ty = operandTy"
    by (auto split: option.splits if_splits CoreUnop.splits CoreType.splits)
  from CoreTm_Unop.IH[OF operand_typed CoreTm_Unop.prems(2) CoreTm_Unop.prems(3) CoreTm_Unop.prems(4)]
  have ih: "core_term_type env mode (apply_subst_to_term subst operand) = Some (apply_subst subst operandTy)" .
  show ?case
  proof (cases op)
    case CoreUnop_Negate
    with CoreTm_Unop.prems(1) operand_typed ty_eq have "is_signed_integer_type operandTy"
      by (auto split: option.splits if_splits)
    hence "is_signed_integer_type (apply_subst subst operandTy)"
      using is_signed_integer_type_apply_subst by blast
    then show ?thesis using ih ty_eq CoreUnop_Negate by simp
  next
    case CoreUnop_Complement
    with CoreTm_Unop.prems(1) operand_typed ty_eq have "is_finite_integer_type operandTy"
      by (auto split: option.splits if_splits)
    hence "is_finite_integer_type (apply_subst subst operandTy)"
      using is_finite_integer_type_apply_subst by blast
    then show ?thesis using ih ty_eq CoreUnop_Complement by simp
  next
    case CoreUnop_Not
    with CoreTm_Unop.prems(1) operand_typed ty_eq have "operandTy = CoreTy_Bool"
      using CoreUnop.simps(9) by fastforce
    then show ?thesis using ih ty_eq CoreUnop_Not by simp
  qed
next
  case (CoreTm_Binop op tm1 tm2)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_Let name rhs body)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_Quantifier q var varTy body)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_VariantCtor ctorName tyArgs arg)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_Record flds)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_RecordProj tm fldName)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_ArrayProj tm idxs)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_VariantProj tm ctorName)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_Match tm cases)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_Sizeof tm)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
next
  case (CoreTm_Allocated tm)
  show ?case
  proof (cases mode)
    case NotGhost
    then show ?thesis using CoreTm_Allocated.prems(1) by simp
  next
    case Ghost
    from CoreTm_Allocated.prems(1) Ghost obtain innerTy where
      inner_typed: "core_term_type env Ghost tm = Some innerTy" and
      ty_eq: "ty = CoreTy_Bool"
      by (auto split: option.splits)
    from CoreTm_Allocated.IH[OF inner_typed CoreTm_Allocated.prems(2) CoreTm_Allocated.prems(3)]
    have ih: "core_term_type env Ghost (apply_subst_to_term subst tm) = Some (apply_subst subst innerTy)"
      using Ghost by simp
    show ?thesis using ih Ghost ty_eq by simp
  qed
next
  case (CoreTm_Old tm)
  (* Not yet implemented in core_term_type *)
  then show ?case sorry
qed

end

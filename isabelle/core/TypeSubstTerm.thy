theory TypeSubstTerm
  imports TypeSubst CoreFreeVars CoreTypecheck
begin

(* ========================================================================== *)
(* Type substitution on terms *)
(* ========================================================================== *)

fun apply_subst_to_term :: "TypeSubst \<Rightarrow> CoreTerm \<Rightarrow> CoreTerm" where
  "apply_subst_to_term subst (CoreTm_LitBool b) = CoreTm_LitBool b"
| "apply_subst_to_term subst (CoreTm_LitInt i) = CoreTm_LitInt i"
| "apply_subst_to_term subst (CoreTm_LitArray elemTy tms) =
    CoreTm_LitArray (apply_subst subst elemTy) (map (apply_subst_to_term subst) tms)"
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
| "apply_subst_to_term subst (CoreTm_Default ty) =
    CoreTm_Default (apply_subst subst ty)"


(* Helper for proving map over lists *)
lemma map_apply_subst_to_term_empty:
  "(\<And>t. t \<in> set tms \<Longrightarrow> apply_subst_to_term fmempty t = t) \<Longrightarrow>
   map (apply_subst_to_term fmempty) tms = tms"
  by (induction tms) auto


(* Empty substitution leaves term unchanged *)
lemma apply_subst_to_term_empty [simp]:
  "apply_subst_to_term fmempty tm = tm"
proof (induction tm)
  case (CoreTm_LitArray elemTy tms)
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
qed (simp_all add: compose_subst_correct)


(* lvalue-ness only depends on the top-level term shape, which substitution preserves. *)
lemma lvalue_base_name_apply_subst_to_term:
  "lvalue_base_name (apply_subst_to_term subst tm) = lvalue_base_name tm"
  by (induction tm) auto

lemma is_lvalue_apply_subst_to_term [simp]:
  "is_lvalue (apply_subst_to_term subst tm) = is_lvalue tm"
  by (simp add: is_lvalue_def lvalue_base_name_apply_subst_to_term)

(* is_writable_lvalue recurses through RecordProj / VariantProj / ArrayProj to the
   base CoreTm_Var. apply_subst_to_term preserves these forms, so writability is
   preserved. *)
lemma is_writable_lvalue_apply_subst_to_term [simp]:
  "is_writable_lvalue env (apply_subst_to_term subst tm) = is_writable_lvalue env tm"
  by (induction tm) auto


(* Type substitution does not change free term variables,
   since it only substitutes type variables. *)
lemma apply_subst_to_term_free_vars:
  "core_term_free_vars (apply_subst_to_term subst tm) = core_term_free_vars tm"
proof (induction tm)
  case (CoreTm_LitArray elemTy tms)
  then show ?case by (induction tms) auto
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  then show ?case by (induction args) auto
next
  case (CoreTm_Record flds)
  have eq: "\<And>n t. (n, t) \<in> set flds \<Longrightarrow>
    core_term_free_vars (apply_subst_to_term subst t) = core_term_free_vars t"
    using CoreTm_Record.IH by auto
  have map_eq:
    "map (core_term_free_vars \<circ> snd \<circ> (\<lambda>(n, t). (n, apply_subst_to_term subst t))) flds
     = map (core_term_free_vars \<circ> snd) flds"
    using eq by (intro map_cong) auto
  show ?case by (simp add: map_eq)
next
  case (CoreTm_ArrayProj tm idxs)
  then show ?case by (induction idxs) auto
next
  case (CoreTm_Match tm cases)
  have eq: "\<And>p t. (p, t) \<in> set cases \<Longrightarrow>
    core_term_free_vars (apply_subst_to_term subst t) = core_term_free_vars t"
    using CoreTm_Match.IH by auto
  have map_eq:
    "map (core_term_free_vars \<circ> snd \<circ> (\<lambda>(p, t). (p, apply_subst_to_term subst t))) cases
     = map (core_term_free_vars \<circ> snd) cases"
    using eq by (intro map_cong) auto
  show ?case using CoreTm_Match.IH(1) by (simp add: map_eq)
qed simp_all


(* Free type variables after substituting a term come from: free tyvars of the
   original term not in dom(subst), or tyvars in the range of subst. Mirrors
   apply_subst_tyvars_result (TypeSubst.thy) at each embedded type annotation. *)
lemma apply_subst_to_term_free_tyvars:
  "core_term_free_tyvars (apply_subst_to_term subst tm) \<subseteq>
   (core_term_free_tyvars tm - fset (fmdom subst)) \<union> subst_range_tyvars subst"
proof (induction tm)
  case (CoreTm_LitArray elemTy tms)
  have ty: "type_tyvars (apply_subst subst elemTy) \<subseteq>
            (type_tyvars elemTy - fset (fmdom subst)) \<union> subst_range_tyvars subst"
    by (rule apply_subst_tyvars_result)
  from CoreTm_LitArray show ?case using ty by (induction tms) auto
next
  case (CoreTm_Cast targetTy tm)
  have ty: "type_tyvars (apply_subst subst targetTy) \<subseteq>
            (type_tyvars targetTy - fset (fmdom subst)) \<union> subst_range_tyvars subst"
    by (rule apply_subst_tyvars_result)
  from CoreTm_Cast show ?case using ty by auto
next
  case (CoreTm_Quantifier q var varTy body)
  have ty: "type_tyvars (apply_subst subst varTy) \<subseteq>
            (type_tyvars varTy - fset (fmdom subst)) \<union> subst_range_tyvars subst"
    by (rule apply_subst_tyvars_result)
  from CoreTm_Quantifier show ?case using ty by auto
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  have tyargs: "\<Union>(type_tyvars ` set (map (apply_subst subst) tyArgs)) \<subseteq>
                (\<Union>(type_tyvars ` set tyArgs) - fset (fmdom subst)) \<union> subst_range_tyvars subst"
    using apply_subst_tyvars_result by fastforce
  from CoreTm_FunctionCall show ?case using tyargs by (induction args) auto
next
  case (CoreTm_VariantCtor ctorName tyArgs arg)
  have tyargs: "\<Union>(type_tyvars ` set (map (apply_subst subst) tyArgs)) \<subseteq>
                (\<Union>(type_tyvars ` set tyArgs) - fset (fmdom subst)) \<union> subst_range_tyvars subst"
    using apply_subst_tyvars_result by fastforce
  from CoreTm_VariantCtor show ?case using tyargs by auto
next
  case (CoreTm_Record flds)
  have IH: "\<And>n t. (n, t) \<in> set flds \<Longrightarrow>
    core_term_free_tyvars (apply_subst_to_term subst t) \<subseteq>
    (core_term_free_tyvars t - fset (fmdom subst)) \<union> subst_range_tyvars subst"
    using CoreTm_Record.IH by auto
  show ?case
  proof
    fix x assume "x \<in> core_term_free_tyvars (apply_subst_to_term subst (CoreTm_Record flds))"
    then obtain n t where mem: "(n, t) \<in> set flds"
      and x_in: "x \<in> core_term_free_tyvars (apply_subst_to_term subst t)"
      by auto
    from IH[OF mem] x_in have
      "x \<in> (core_term_free_tyvars t - fset (fmdom subst)) \<union> subst_range_tyvars subst" by blast
    moreover have "core_term_free_tyvars t \<subseteq> core_term_free_tyvars (CoreTm_Record flds)"
      using mem by force
    ultimately show "x \<in> (core_term_free_tyvars (CoreTm_Record flds) - fset (fmdom subst))
                          \<union> subst_range_tyvars subst" by auto
  qed
next
  case (CoreTm_ArrayProj arr idxs)
  from CoreTm_ArrayProj show ?case by (induction idxs) auto
next
  case (CoreTm_Match scrut arms)
  have IH2: "\<And>p t. (p, t) \<in> set arms \<Longrightarrow>
    core_term_free_tyvars (apply_subst_to_term subst t) \<subseteq>
    (core_term_free_tyvars t - fset (fmdom subst)) \<union> subst_range_tyvars subst"
    using CoreTm_Match.IH by auto
  show ?case
  proof
    fix x assume "x \<in> core_term_free_tyvars (apply_subst_to_term subst (CoreTm_Match scrut arms))"
    then consider (scrut) "x \<in> core_term_free_tyvars (apply_subst_to_term subst scrut)"
      | (arm) p t where "(p, t) \<in> set arms" "x \<in> core_term_free_tyvars (apply_subst_to_term subst t)"
      by auto
    thus "x \<in> (core_term_free_tyvars (CoreTm_Match scrut arms) - fset (fmdom subst))
               \<union> subst_range_tyvars subst"
    proof cases
      case scrut
      with CoreTm_Match.IH(1) show ?thesis by auto
    next
      case (arm p t)
      from IH2[OF arm(1)] arm(2) have
        "x \<in> (core_term_free_tyvars t - fset (fmdom subst)) \<union> subst_range_tyvars subst" by blast
      moreover have "core_term_free_tyvars t \<subseteq> core_term_free_tyvars (CoreTm_Match scrut arms)"
        using arm(1) by force
      ultimately show ?thesis by auto
    qed
  qed
next
  case (CoreTm_Default ty)
  show ?case using apply_subst_tyvars_result by simp
qed auto

(* Corollary: a ground substitution (empty range tyvars) whose domain covers an
   interval removes those interval tyvars from a term. *)
corollary apply_subst_to_term_free_tyvars_ground:
  assumes "subst_range_tyvars subst = {}"
  shows "core_term_free_tyvars (apply_subst_to_term subst tm) \<subseteq>
         core_term_free_tyvars tm - fset (fmdom subst)"
  using apply_subst_to_term_free_tyvars[of subst tm] assms by auto


(* Integer/numeric/etc. types are all closed under substitution (they only match
   on concrete, type-variable-free type constructors). *)
lemma is_integer_type_apply_subst:
  "is_integer_type ty \<Longrightarrow> apply_subst subst ty = ty"
  by (cases ty) auto

lemma is_numeric_type_apply_subst:
  "is_numeric_type ty \<Longrightarrow> apply_subst subst ty = ty"
  by (cases ty) auto

lemma is_signed_numeric_type_apply_subst:
  "is_signed_numeric_type ty \<Longrightarrow> apply_subst subst ty = ty"
  by (cases ty rule: is_signed_numeric_type.cases) auto

lemma is_finite_integer_type_apply_subst:
  "is_finite_integer_type ty \<Longrightarrow> apply_subst subst ty = ty"
  by (cases ty) auto

(* Applying a subst to the types of valid CoreTm_Binop operands is a no-op. *)
(* (Follows from binop_operand_type_bool_or_numeric.) *)
lemma binop_operand_apply_subst:
  assumes "core_term_type env NotGhost (CoreTm_Binop op lhs rhs) = Some ty"
      and "core_term_type env NotGhost lhs = Some lhsTy"
      and "core_term_type env NotGhost rhs = Some rhsTy"
  shows "apply_subst subst lhsTy = lhsTy"
    and "apply_subst subst rhsTy = rhsTy"
  using binop_operand_type_bool_or_numeric[OF assms] is_numeric_type_apply_subst
  by auto

(* Valid decreases-types are fully concrete (Bool, integers, or records of
   valid decreases-types), so substitution is a no-op. *)
lemma is_valid_decreases_type_apply_subst:
  "is_valid_decreases_type ty \<Longrightarrow> apply_subst subst ty = ty"
proof (induction ty rule: is_valid_decreases_type.induct)
  case (4 flds)
  then have "\<And>n ty. (n, ty) \<in> set flds \<Longrightarrow> apply_subst subst ty = ty"
    by (auto simp: list_all_iff)
  hence "map (\<lambda>(n, ty). (n, apply_subst subst ty)) flds = flds"
    by (induction flds) auto
  thus ?case by simp
qed auto

(* sizeof_type produces only closed types (u64 or a record of u64s), so
   substitution leaves them alone. *)
lemma map_apply_subst_zip_replicate_u64:
  "map (\<lambda>(name, ty). (name, apply_subst subst ty)) (zip names (replicate n u64_type))
     = zip names (replicate n u64_type)"
proof (induction names arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons name names)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc m)
    with Cons.IH show ?thesis by (simp add: u64_type_def)
  qed
qed

lemma apply_subst_sizeof_type [simp]:
  "apply_subst subst (sizeof_type dims) = sizeof_type dims"
proof -
  have rec_case:
    "\<And>n names. apply_subst subst (CoreTy_Record (zip names (replicate n u64_type)))
              = CoreTy_Record (zip names (replicate n u64_type))"
    by (simp add: map_apply_subst_zip_replicate_u64)
  show ?thesis
  proof (cases dims)
    case Nil
    then show ?thesis by (simp add: u64_type_def)
  next
    case (Cons d ds)
    show ?thesis
    proof (cases ds)
      case Nil
      with Cons show ?thesis by (simp add: u64_type_def)
    next
      case (Cons d2 rest)
      with \<open>dims = d # ds\<close> rec_case
      show ?thesis
        using sizeof_type.simps(3) by presburger
    qed
  qed
qed


end

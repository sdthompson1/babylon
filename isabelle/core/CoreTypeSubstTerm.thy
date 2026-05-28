theory CoreTypeSubstTerm
  imports CoreTypecheck CoreStmtTypecheck
begin

(* Syntactic type-variable substitution on terms.

   This file defines apply_subst_to_term (the workhorse the elaborator runs
   to clear metavariables) and basic algebraic facts about it: it is the
   identity for the empty substitution, composes with compose_subst, leaves
   lvalue-ness and free variables alone, and is the identity on the closed
   types used by Cast / Binop / Sizeof.

   See also CoreTypeSubst.thy for a type-preservation theorem about 
   apply_subst_to_term. 
*)

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

(* If a pattern is compatible with a type, it is compatible with that type
   after substitution. (The reverse is not true if ty is a CoreTy_Var.) *)
lemma pattern_compatible_apply_subst:
  assumes "tyenv_well_formed env"
      and "pattern_compatible env p ty"
  shows "pattern_compatible env p (apply_subst subst ty)"
  using assms
proof (induction p ty rule: pattern_compatible.induct[case_names Wildcard Bool Int Variant Record, consumes 0])
  case (Wildcard env uu)
  then show ?case by simp
next
  case (Bool env uv ty)
  then show ?case by (cases ty) auto
next
  case (Int env uw ty)
  then show ?case by (cases ty) auto
next
  case (Variant env ctorName payloadPat ty)
  from Variant.prems show ?case
  proof (cases ty)
    case (CoreTy_Datatype tyName tyArgs)
    with Variant.prems obtain dtName tyvars payloadTy where
      ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
      dt_eq: "tyName = dtName" and
      len_eq: "length tyArgs = length tyvars" and
      pc_payload: "pattern_compatible env payloadPat
                     (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      by (auto split: option.splits prod.splits)
    \<comment> \<open>The data-ctor's payload is well-kinded in an env whose tyvars are
        exactly ctor's tyvars, hence its free vars are a subset. \<close>
    have payload_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
      using Variant.prems(1) ctor_lookup
      unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
    have tyvars_distinct: "distinct tyvars"
      using Variant.prems(1) ctor_lookup
      unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast
    have payload_tyvars: "type_tyvars payloadTy \<subseteq> set tyvars"
      using is_well_kinded_type_tyvars_subset[OF payload_wk]
      by (simp add: fset_of_list.rep_eq)
    \<comment> \<open>Substitution composition: apply_subst subst commutes with the inner
        tyvar-to-tyArgs subst, since payload free vars stay within tyvars. \<close>
    have compose:
      "apply_subst (fmap_of_list (zip tyvars (map (apply_subst subst) tyArgs))) payloadTy
         = apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      using apply_subst_compose_zip[OF len_eq[symmetric] payload_tyvars tyvars_distinct, of subst] .
    \<comment> \<open>IH on payloadPat. \<close>
    have ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
      using CoreTy_Datatype dt_eq by simp
    have payload_subst:
      "pattern_compatible env payloadPat
         (apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy))"
      using Variant.IH[OF ctor_lookup refl refl ty_eq Variant.prems(1) pc_payload] .
    show ?thesis
      using ctor_lookup CoreTy_Datatype dt_eq len_eq payload_subst compose by simp
  qed (use Variant.prems in \<open>auto split: option.splits prod.splits\<close>)
next
  case (Record env pflds ty)
  from Record.prems show ?case
  proof (cases ty)
    case (CoreTy_Record fldTys)
    with Record.prems have
      flds_ok: "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty)
                          pflds fldTys"
      by auto
    \<comment> \<open>The substituted record type has the same field names, with each field's
        type substituted. \<close>
    let ?subst_fldTys = "map (\<lambda>(name, fty). (name, apply_subst subst fty)) fldTys"
    have subst_ty_eq: "apply_subst subst ty = CoreTy_Record ?subst_fldTys"
      using CoreTy_Record by simp
    have lens_eq: "length pflds = length fldTys"
      using flds_ok by (simp add: list_all2_lengthD)
    \<comment> \<open>For each index i, the IH gives subst-compatibility of the i-th pattern
        with the substituted i-th field type. \<close>
    have flds_ok':
      "list_all2 (\<lambda>(pn, p) (fn, fty'). pn = fn \<and> pattern_compatible env p fty')
                 pflds ?subst_fldTys"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length pflds = length ?subst_fldTys" using lens_eq by simp
    next
      fix i assume i_lt: "i < length pflds"
      let ?pf = "pflds ! i"
      let ?ft = "fldTys ! i"
      obtain pn p where pf_eq: "?pf = (pn, p)" by (cases ?pf)
      obtain fn fty where ft_eq: "?ft = (fn, fty)" by (cases ?ft)
      have pf_in: "?pf \<in> set pflds" using i_lt by simp
      have ft_in: "?ft \<in> set fldTys" using i_lt lens_eq by simp
      from flds_ok i_lt have
        names_eq: "pn = fn" and
        pc_p: "pattern_compatible env p fty"
        using pf_eq ft_eq lens_eq by (auto simp: list_all2_conv_all_nth)
      have ih_pc: "pattern_compatible env p (apply_subst subst fty)"
        using Record.IH[OF CoreTy_Record pf_in ft_in pf_eq[symmetric] Record.prems(1) pc_p] .
      have subst_nth: "?subst_fldTys ! i = (fn, apply_subst subst fty)"
        using i_lt lens_eq ft_eq by simp
      show "(case pflds ! i of (pn, p) \<Rightarrow>
              \<lambda>(fn, fty'). pn = fn \<and> pattern_compatible env p fty')
            (?subst_fldTys ! i)"
        using pf_eq subst_nth names_eq ih_pc by simp
    qed
    show ?thesis
      using subst_ty_eq flds_ok' by simp
  qed (use Record.prems in \<open>auto split: CoreType.splits\<close>)
qed


(* Type substitution does not change term-level free variables,
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

(* Corollary of binop_operand_type_bool_or_numeric: each operand type is ground
   (CoreTy_Bool or numeric), so apply_subst is a no-op on it. *)
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


(* General fmap helpers about fmap_of_list and zip. *)

lemma fmdom_fmap_of_list_zip:
  "length xs = length ys \<Longrightarrow> fset (fmdom (fmap_of_list (zip xs ys))) = set xs"
  by (induction xs ys rule: list_induct2) auto

lemma fmran'_fmupd_notin:
  "k |\<notin>| fmdom m \<Longrightarrow> fmran' (fmupd k v m) = insert v (fmran' m)"
proof (intro set_eqI iffI)
  fix x
  assume notin: "k |\<notin>| fmdom m"
  { assume "x \<in> fmran' (fmupd k v m)"
    then obtain a where "fmlookup (fmupd k v m) a = Some x"
      by (auto simp: fmran'_def)
    then have "x = v \<or> x \<in> fmran' m"
      by (cases "k = a") (auto simp: fmran'_def)
    thus "x \<in> insert v (fmran' m)" by auto
  }
  { assume "x \<in> insert v (fmran' m)"
    then have "x = v \<or> x \<in> fmran' m" by auto
    then show "x \<in> fmran' (fmupd k v m)"
    proof
      assume "x = v"
      thus ?thesis by (auto simp: fmran'_def)
    next
      assume "x \<in> fmran' m"
      then obtain a where lookup: "fmlookup m a = Some x"
        by (auto simp: fmran'_def)
      hence "a \<noteq> k" using notin by (auto dest: fmdomI)
      hence "fmlookup (fmupd k v m) a = Some x" using lookup by simp
      thus ?thesis
        by (simp add: fmran'I)
    qed
  }
qed

(* The range of fmap_of_list (zip xs ys) is exactly set ys when xs has distinct
   keys and the lengths match. Used downstream for substitution-range conditions
   over zip-built substitutions. *)
lemma fmran'_fmap_of_list_zip:
  "length xs = length ys \<Longrightarrow> distinct xs \<Longrightarrow> fmran' (fmap_of_list (zip xs ys)) = set ys"
proof (induction xs ys rule: list_induct2)
  case Nil
  then show ?case by (simp add: fmran'_def)
next
  case (Cons x xs y ys)
  from Cons.prems have x_notin: "x \<notin> set xs" and distinct_xs: "distinct xs" by simp_all
  from x_notin have x_notin_dom: "x |\<notin>| fmdom (fmap_of_list (zip xs ys))"
    using fmdom_fmap_of_list_zip[OF Cons.hyps] by simp
  have "fmran' (fmap_of_list (zip (x # xs) (y # ys))) =
        fmran' (fmupd x y (fmap_of_list (zip xs ys)))"
    by simp
  also have "... = insert y (fmran' (fmap_of_list (zip xs ys)))"
    using x_notin_dom by (rule fmran'_fmupd_notin)
  also have "... = insert y (set ys)"
    using Cons.IH distinct_xs by simp
  finally show ?case by simp
qed


end

theory CoreTypeSubst
  imports CoreTypecheck CoreStmtTypecheck
begin

(* Substitute type variables (CoreTy_Var) in terms and environments.

   This file contains the substitution machinery used by:
   - The elaborator: produces terms with metavariables (type variables used
     as unifiable placeholders) that get progressively resolved by unification,
     then substituted away. apply_subst_to_term is the workhorse for that, and
     apply_subst_to_term_preserves_typing is the lemma ElabTermCorrect uses to
     show that the elaborator's substitutions don't break typing.
   - The function-call soundness proof (TypeSoundness.thy case 6): substitutes
     the callee's type variables to caller-instantiated types, in the *type
     environment* used to typecheck the callee body. The body's source syntax
     is left alone; we re-run the typechecker on the same source in a different
     env. apply_subst_to_callee_env builds that env, and the
     core_*_type_subst_callee_env lemmas establish that typing is preserved.

   Naming follows the pattern apply_subst_to_<thing>: apply_subst_to_term for
   the function, apply_subst_to_term_preserves_typing for the typing-preservation
   lemma about it. *)


(* ========================================================================== *)
(* Substitution on terms                                                       *)
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

(* pattern_compatible only inspects the top-level shape of the scrutinee type
   (and for Datatype, just the type name). Substitution preserves all of these
   top-level shapes, so if the predicate holds on ty it also holds on
   apply_subst subst ty. (The reverse is not true if ty is a CoreTy_Var.) *)
lemma pattern_compatible_apply_subst:
  "pattern_compatible env p ty \<Longrightarrow> pattern_compatible env p (apply_subst subst ty)"
  by (cases p; cases ty) (auto split: option.splits prod.splits)


(* apply_subst_to_term_preserves_typing is now stated and proved in the
   "Term typing under callee-env substitution" section below, since it depends
   on apply_subst_to_callee_env and core_term_type_subst_callee_env. *)

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
  show ?case by (auto simp: eq)
next
  case (CoreTm_ArrayProj tm idxs)
  then show ?case by (induction idxs) auto
next
  case (CoreTm_Match tm cases)
  have eq: "\<And>p t. (p, t) \<in> set cases \<Longrightarrow>
    core_term_free_vars (apply_subst_to_term subst t) = core_term_free_vars t"
    using CoreTm_Match.IH by auto
  show ?case using CoreTm_Match.IH(1) by (auto simp: eq)
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


(* ========================================================================== *)
(* Substitution on statements                                                  *)
(* ========================================================================== *)

fun apply_subst_to_stmt :: "TypeSubst \<Rightarrow> CoreStatement \<Rightarrow> CoreStatement"
and apply_subst_to_stmt_list :: "TypeSubst \<Rightarrow> CoreStatement list \<Rightarrow> CoreStatement list" where
  "apply_subst_to_stmt subst (CoreStmt_VarDecl g name vr ty tm) =
    CoreStmt_VarDecl g name vr (apply_subst subst ty) (apply_subst_to_term subst tm)"
| "apply_subst_to_stmt subst (CoreStmt_Fix name ty) =
    CoreStmt_Fix name (apply_subst subst ty)"
| "apply_subst_to_stmt subst (CoreStmt_Obtain name ty tm) =
    CoreStmt_Obtain name (apply_subst subst ty) (apply_subst_to_term subst tm)"
| "apply_subst_to_stmt subst (CoreStmt_Use tm) =
    CoreStmt_Use (apply_subst_to_term subst tm)"
| "apply_subst_to_stmt subst (CoreStmt_Assign g lhs rhs) =
    CoreStmt_Assign g (apply_subst_to_term subst lhs) (apply_subst_to_term subst rhs)"
| "apply_subst_to_stmt subst (CoreStmt_Swap g lhs rhs) =
    CoreStmt_Swap g (apply_subst_to_term subst lhs) (apply_subst_to_term subst rhs)"
| "apply_subst_to_stmt subst (CoreStmt_Return tm) =
    CoreStmt_Return (apply_subst_to_term subst tm)"
| "apply_subst_to_stmt subst (CoreStmt_Assert tm proof_stmts) =
    CoreStmt_Assert (apply_subst_to_term subst tm) (apply_subst_to_stmt_list subst proof_stmts)"
| "apply_subst_to_stmt subst (CoreStmt_Assume tm) =
    CoreStmt_Assume (apply_subst_to_term subst tm)"
| "apply_subst_to_stmt subst (CoreStmt_While g cond invs decr body) =
    CoreStmt_While g
      (apply_subst_to_term subst cond)
      (map (apply_subst_to_term subst) invs)
      (apply_subst_to_term subst decr)
      (apply_subst_to_stmt_list subst body)"
| "apply_subst_to_stmt subst (CoreStmt_Match g scrut arms) =
    CoreStmt_Match g
      (apply_subst_to_term subst scrut)
      (map (\<lambda>(pat, body). (pat, apply_subst_to_stmt_list subst body)) arms)"
| "apply_subst_to_stmt subst (CoreStmt_ShowHide sh name) =
    CoreStmt_ShowHide sh name"
| "apply_subst_to_stmt_list subst [] = []"
| "apply_subst_to_stmt_list subst (s # rest) =
    apply_subst_to_stmt subst s # apply_subst_to_stmt_list subst rest"


(* ========================================================================== *)
(* Substitution on callee environments                                         *)
(* ========================================================================== *)

(* At a function call site, the callee body was originally typechecked in an
   environment with the callee's own type variables (FI_TyArgs) in scope. To
   re-typecheck the body in the caller's context we must:
   - Replace the callee's type variables with the caller's (which act as the
     binders for any unresolved type variables in the substitution's range).
   - Substitute through TE_LocalVars (parameter types), so the formal
     parameters get caller-instantiated types.
   - Substitute through TE_ReturnType, so the return-type check inside Return
     statements sees the caller-instantiated return type.
   The other env fields (globals, datatypes, ctors, functions, ghost-locals,
   const-names, function-ghost flag) are unchanged: they were inherited from
   the caller's env via body_env_for in the first place. *)
definition apply_subst_to_callee_env ::
    "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "apply_subst_to_callee_env subst callerEnv calleeEnv =
    calleeEnv \<lparr>
      TE_LocalVars := fmmap (apply_subst subst) (TE_LocalVars calleeEnv),
      TE_TypeVars := TE_TypeVars callerEnv,
      TE_RuntimeTypeVars := TE_RuntimeTypeVars callerEnv,
      TE_ReturnType := apply_subst subst (TE_ReturnType calleeEnv)
    \<rparr>"

(* Field projections - these come up everywhere downstream. *)
lemma apply_subst_to_callee_env_TE_LocalVars [simp]:
  "TE_LocalVars (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = fmmap (apply_subst subst) (TE_LocalVars calleeEnv)"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_GlobalVars [simp]:
  "TE_GlobalVars (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_GlobalVars calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_GhostLocals [simp]:
  "TE_GhostLocals (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_GhostLocals calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_GhostGlobals [simp]:
  "TE_GhostGlobals (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_GhostGlobals calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_ConstLocals [simp]:
  "TE_ConstLocals (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_ConstLocals calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_TypeVars [simp]:
  "TE_TypeVars (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_TypeVars callerEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_RuntimeTypeVars [simp]:
  "TE_RuntimeTypeVars (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_RuntimeTypeVars callerEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_ReturnType [simp]:
  "TE_ReturnType (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = apply_subst subst (TE_ReturnType calleeEnv)"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_FunctionGhost [simp]:
  "TE_FunctionGhost (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_FunctionGhost calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_Functions [simp]:
  "TE_Functions (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_Functions calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_Datatypes [simp]:
  "TE_Datatypes (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_Datatypes calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_DataCtors [simp]:
  "TE_DataCtors (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_DataCtors calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_DataCtorsByType [simp]:
  "TE_DataCtorsByType (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_DataCtorsByType calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

lemma apply_subst_to_callee_env_TE_GhostDatatypes [simp]:
  "TE_GhostDatatypes (apply_subst_to_callee_env subst callerEnv calleeEnv)
     = TE_GhostDatatypes calleeEnv"
  by (simp add: apply_subst_to_callee_env_def)

(* pattern_compatible only inspects the top-level type constructor, which
   apply_subst preserves. TE_DataCtors is also inherited from calleeEnv. *)
lemma pattern_compatible_apply_subst_callee_env:
  "pattern_compatible calleeEnv p ty
     \<Longrightarrow> pattern_compatible (apply_subst_to_callee_env subst callerEnv calleeEnv) p
                            (apply_subst subst ty)"
  by (cases p; cases ty) (auto split: option.splits prod.splits)

(* Substituting types in TE_LocalVars preserves the *keys*, so writability is
   preserved (it only looks at TE_LocalVars's domain and TE_ConstLocals). *)
lemma tyenv_var_writable_apply_subst_to_callee_env [simp]:
  "tyenv_var_writable (apply_subst_to_callee_env subst callerEnv calleeEnv) name
     = tyenv_var_writable calleeEnv name"
  by (simp add: tyenv_var_writable_def apply_subst_to_callee_env_def)

(* Ghost-ness of a variable is determined by TE_LocalVars's domain (not types),
   TE_GhostLocals, and TE_GhostGlobals. All preserved under substitution. *)
lemma tyenv_var_ghost_apply_subst_to_callee_env [simp]:
  "tyenv_var_ghost (apply_subst_to_callee_env subst callerEnv calleeEnv) name
     = tyenv_var_ghost calleeEnv name"
  unfolding tyenv_var_ghost_def
  by (cases "fmlookup (TE_LocalVars calleeEnv) name") simp_all

(* Variable lookup: for locals, the type gets substituted; for globals, the type
   is unchanged (and globally closed in a well-formed env, see the Var case). *)
lemma tyenv_lookup_var_apply_subst_to_callee_env:
  "tyenv_lookup_var (apply_subst_to_callee_env subst callerEnv calleeEnv) name
     = (case fmlookup (TE_LocalVars calleeEnv) name of
          Some ty \<Rightarrow> Some (apply_subst subst ty)
        | None \<Rightarrow> fmlookup (TE_GlobalVars calleeEnv) name)"
  unfolding tyenv_lookup_var_def apply_subst_to_callee_env_def
  by (cases "fmlookup (TE_LocalVars calleeEnv) name") simp_all

lemma is_writable_lvalue_apply_subst_to_callee_env [simp]:
  "is_writable_lvalue (apply_subst_to_callee_env subst callerEnv calleeEnv) tm
     = is_writable_lvalue calleeEnv tm"
  by (induction tm) auto


(* Conditions on a substitution and the caller/callee env relationship that are
   *always* needed for the typing-preservation lemmas: caller and callee agree on
   the global-ish fields, and the substitution maps every callee type variable
   either to a well-kinded type in callerEnv or back to a callerEnv type variable.
   Used by core_term_type_subst_callee_env and friends. *)
definition callee_env_subst_ok ::
    "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "callee_env_subst_ok subst callerEnv calleeEnv \<equiv>
    \<comment> \<open>Caller and callee agree on the global-ish fields. (In our case 6 use
        these are inherited from callerEnv via body_env_for.) \<close>
    TE_GlobalVars callerEnv = TE_GlobalVars calleeEnv \<and>
    TE_GhostGlobals callerEnv = TE_GhostGlobals calleeEnv \<and>
    TE_Functions callerEnv = TE_Functions calleeEnv \<and>
    TE_Datatypes callerEnv = TE_Datatypes calleeEnv \<and>
    TE_DataCtors callerEnv = TE_DataCtors calleeEnv \<and>
    TE_DataCtorsByType callerEnv = TE_DataCtorsByType calleeEnv \<and>
    TE_GhostDatatypes callerEnv = TE_GhostDatatypes calleeEnv \<and>
    \<comment> \<open>Every callee type variable is either mapped to a well-kinded type in callerEnv
        or remains in callerEnv's TE_TypeVars. \<close>
    (\<forall>n. n |\<in>| TE_TypeVars calleeEnv \<longrightarrow>
         (case fmlookup subst n of
            Some ty' \<Rightarrow> is_well_kinded callerEnv ty'
          | None \<Rightarrow> n |\<in>| TE_TypeVars callerEnv))"

(* The runtime-tyvar condition is split out separately because it is only needed
   in NotGhost mode. Most consumers will pass it conditionally:
   `mode = NotGhost \<Longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv`. *)
definition callee_env_subst_runtime_ok ::
    "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "callee_env_subst_runtime_ok subst callerEnv calleeEnv \<equiv>
    \<forall>n. n |\<in>| TE_RuntimeTypeVars calleeEnv \<longrightarrow>
         (case fmlookup subst n of
            Some ty' \<Rightarrow> is_runtime_type callerEnv ty'
          | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars callerEnv)"


(* Lifting facts: under callee_env_subst_ok, apply_subst preserves well-kindedness
   from calleeEnv to ?be, and runtime-ness similarly. These are direct corollaries
   of apply_subst_preserves_well_kinded / apply_subst_preserves_runtime, but stated
   in terms of ?be so they fit into the well-formedness proof below. *)
lemma apply_subst_preserves_well_kinded_callee:
  assumes "is_well_kinded calleeEnv ty"
      and "callee_env_subst_ok subst callerEnv calleeEnv"
  shows "is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv)
                        (apply_subst subst ty)"
proof (rule apply_subst_preserves_well_kinded[OF assms(1)])
  show "TE_Datatypes (apply_subst_to_callee_env subst callerEnv calleeEnv)
          = TE_Datatypes calleeEnv"
    by simp
next
  fix n assume "n |\<in>| TE_TypeVars calleeEnv"
  with assms(2) show
    "case fmlookup subst n of
        Some ty' \<Rightarrow> is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv) ty'
      | None \<Rightarrow> n |\<in>| TE_TypeVars (apply_subst_to_callee_env subst callerEnv calleeEnv)"
    unfolding callee_env_subst_ok_def
    by (auto split: option.splits intro: is_well_kinded_cong_env[THEN iffD1])
qed

lemma apply_subst_preserves_runtime_callee:
  assumes "is_runtime_type calleeEnv ty"
      and "callee_env_subst_ok subst callerEnv calleeEnv"
      and "callee_env_subst_runtime_ok subst callerEnv calleeEnv"
  shows "is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                         (apply_subst subst ty)"
proof (rule apply_subst_preserves_runtime[OF assms(1)])
  show "TE_GhostDatatypes (apply_subst_to_callee_env subst callerEnv calleeEnv)
          = TE_GhostDatatypes calleeEnv"
    by simp
next
  \<comment> \<open>is_runtime_type only depends on TE_GhostDatatypes and TE_RuntimeTypeVars; on
      ?be both agree with callerEnv (the former by callee_env_subst_ok, the
      latter by definition), so runtime-ness in callerEnv transfers to ?be. \<close>
  have rt_cong: "\<And>ty'. is_runtime_type callerEnv ty'
                       = is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ty'"
    using assms(2)
    by (intro is_runtime_type_cong_env)
       (simp_all add: callee_env_subst_ok_def)
  fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars calleeEnv"
  show
    "case fmlookup subst n of
        Some ty' \<Rightarrow> is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ty'
      | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars (apply_subst_to_callee_env subst callerEnv calleeEnv)"
  proof (cases "fmlookup subst n")
    case None
    with assms(3) n_in have "n |\<in>| TE_RuntimeTypeVars callerEnv"
      unfolding callee_env_subst_runtime_ok_def by auto
    thus ?thesis using None by simp
  next
    case (Some ty')
    with assms(3) n_in have "is_runtime_type callerEnv ty'"
      unfolding callee_env_subst_runtime_ok_def by auto
    with rt_cong have "is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ty'"
      by simp
    thus ?thesis using Some by simp
  qed
qed


(* Well-formedness of the callee env after substitution. This is the lemma case 6
   of the type soundness theorem uses to discharge wf_bodyEnv: given that the
   pre-substitution body env (e.g. body_env_for callerEnv funInfo) is well-formed
   and the substitution conditions hold, the substituted env is also well-formed. *)
lemma apply_subst_to_callee_env_well_formed:
  assumes wf_callee: "tyenv_well_formed calleeEnv"
      and wf_caller: "tyenv_well_formed callerEnv"
      and ok: "callee_env_subst_ok subst callerEnv calleeEnv"
      and ok_rt: "callee_env_subst_runtime_ok subst callerEnv calleeEnv"
      and ret_wk: "is_well_kinded callerEnv (apply_subst subst (TE_ReturnType calleeEnv))"
      and ret_rt: "TE_FunctionGhost calleeEnv = NotGhost \<Longrightarrow>
                   is_runtime_type callerEnv (apply_subst subst (TE_ReturnType calleeEnv))"
  shows "tyenv_well_formed (apply_subst_to_callee_env subst callerEnv calleeEnv)"
proof -
  let ?be = "apply_subst_to_callee_env subst callerEnv calleeEnv"

  \<comment> \<open>Field-agreement facts pulled out for repeated use. \<close>
  from ok have
    gv_eq: "TE_GlobalVars callerEnv = TE_GlobalVars calleeEnv" and
    gg_eq: "TE_GhostGlobals callerEnv = TE_GhostGlobals calleeEnv" and
    fns_eq: "TE_Functions callerEnv = TE_Functions calleeEnv" and
    dt_eq: "TE_Datatypes callerEnv = TE_Datatypes calleeEnv" and
    dc_eq: "TE_DataCtors callerEnv = TE_DataCtors calleeEnv" and
    dcbt_eq: "TE_DataCtorsByType callerEnv = TE_DataCtorsByType calleeEnv" and
    gd_eq: "TE_GhostDatatypes callerEnv = TE_GhostDatatypes calleeEnv"
    unfolding callee_env_subst_ok_def by auto

  \<comment> \<open>Congruences relating ?be to callerEnv on cleared envs (for the global
      conjuncts of vars_well_kinded and vars_runtime). \<close>
  have wk_cleared_caller_eq:
    "\<And>ty. is_well_kinded (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty
        = is_well_kinded (callerEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
    by (rule is_well_kinded_cong_env) (simp_all add: dt_eq)
  have rt_cleared_caller_eq:
    "\<And>ty. is_runtime_type (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty
        = is_runtime_type (callerEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
    by (rule is_runtime_type_cong_env) (simp_all add: gd_eq)

  \<comment> \<open>Congruences for the inner-override conjuncts (payloads, fun types, etc.). \<close>
  have wk_scope_eq:
    "\<And>tvs t. is_well_kinded (?be \<lparr> TE_TypeVars := tvs \<rparr>) t
            = is_well_kinded (calleeEnv \<lparr> TE_TypeVars := tvs \<rparr>) t"
    by (rule is_well_kinded_cong_env) (simp_all add: apply_subst_to_callee_env_def)
  have rt_scope_eq:
    "\<And>tvs rtvs t.
       is_runtime_type (?be \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t
       = is_runtime_type (calleeEnv \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) t"
    by (rule is_runtime_type_cong_env) (simp_all add: apply_subst_to_callee_env_def)

  \<comment> \<open>Extract conjuncts of well-formedness from both envs. \<close>
  from wf_callee have
    callee_vars_wk: "tyenv_vars_well_kinded calleeEnv" and
    callee_vars_rt: "tyenv_vars_runtime calleeEnv" and
    callee_ghost_subset: "tyenv_ghost_vars_subset calleeEnv" and
    callee_ctors_cons: "tyenv_ctors_consistent calleeEnv" and
    callee_payloads_wk: "tyenv_payloads_well_kinded calleeEnv" and
    callee_ctor_tyvars_distinct: "tyenv_ctor_tyvars_distinct calleeEnv" and
    callee_ctors_by_type: "tyenv_ctors_by_type_consistent calleeEnv" and
    callee_fun_types_wk: "tyenv_fun_types_well_kinded calleeEnv" and
    callee_fun_tyvars_distinct: "tyenv_fun_tyvars_distinct calleeEnv" and
    callee_fun_param_names_distinct: "tyenv_fun_param_names_distinct calleeEnv" and
    callee_fun_ghost: "tyenv_fun_ghost_constraint calleeEnv" and
    callee_nonghost_payloads: "tyenv_nonghost_payloads_runtime calleeEnv" and
    callee_ghost_dt_subset: "tyenv_ghost_datatypes_subset calleeEnv" and
    callee_rt_subset: "tyenv_runtime_tyvars_subset calleeEnv"
    unfolding tyenv_well_formed_def by auto

  from wf_caller have
    caller_vars_wk: "tyenv_vars_well_kinded callerEnv" and
    caller_rt_subset: "tyenv_runtime_tyvars_subset callerEnv"
    unfolding tyenv_well_formed_def by auto

  \<comment> \<open>(1) tyenv_vars_well_kinded ?be \<close>
  have c1: "tyenv_vars_well_kinded ?be"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix name ty
    assume "fmlookup (TE_LocalVars ?be) name = Some ty"
    then obtain origTy where
      orig_lk: "fmlookup (TE_LocalVars calleeEnv) name = Some origTy" and
      ty_eq: "ty = apply_subst subst origTy"
      by (auto split: option.splits)
    from callee_vars_wk orig_lk have "is_well_kinded calleeEnv origTy"
      unfolding tyenv_vars_well_kinded_def by blast
    from apply_subst_preserves_well_kinded_callee[OF this ok]
    show "is_well_kinded ?be ty" using ty_eq by simp
  next
    fix name ty
    assume gv: "fmlookup (TE_GlobalVars ?be) name = Some ty"
    \<comment> \<open>?be inherits TE_GlobalVars from calleeEnv, which agrees with callerEnv. \<close>
    hence "fmlookup (TE_GlobalVars callerEnv) name = Some ty"
      using gv_eq by simp
    with caller_vars_wk
    have "is_well_kinded (callerEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      unfolding tyenv_vars_well_kinded_def by blast
    thus "is_well_kinded (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      using wk_cleared_caller_eq by simp
  qed

  \<comment> \<open>(2) tyenv_vars_runtime ?be \<close>
  from wf_caller have caller_vars_rt: "tyenv_vars_runtime callerEnv"
    unfolding tyenv_well_formed_def by auto
  have c2: "tyenv_vars_runtime ?be"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix name ty
    assume A: "fmlookup (TE_LocalVars ?be) name = Some ty
               \<and> name |\<notin>| TE_GhostLocals ?be"
    from A have lv: "fmlookup (TE_LocalVars ?be) name = Some ty"
      and ng: "name |\<notin>| TE_GhostLocals ?be" by simp_all
    from lv obtain origTy where
      orig_lk: "fmlookup (TE_LocalVars calleeEnv) name = Some origTy" and
      ty_eq: "ty = apply_subst subst origTy"
      by (auto split: option.splits)
    from ng have ng_callee: "name |\<notin>| TE_GhostLocals calleeEnv" by simp
    from callee_vars_rt orig_lk ng_callee
    have "is_runtime_type calleeEnv origTy"
      unfolding tyenv_vars_runtime_def by blast
    from apply_subst_preserves_runtime_callee[OF this ok ok_rt]
    show "is_runtime_type ?be ty" using ty_eq by simp
  next
    fix name ty
    assume A: "fmlookup (TE_GlobalVars ?be) name = Some ty
               \<and> name |\<notin>| TE_GhostGlobals ?be"
    from A have gv: "fmlookup (TE_GlobalVars ?be) name = Some ty"
      and ng: "name |\<notin>| TE_GhostGlobals ?be" by simp_all
    from gv have gv_caller: "fmlookup (TE_GlobalVars callerEnv) name = Some ty"
      using gv_eq by simp
    from ng have ng_caller: "name |\<notin>| TE_GhostGlobals callerEnv"
      using gg_eq by simp
    from caller_vars_rt gv_caller ng_caller
    have "is_runtime_type (callerEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      unfolding tyenv_vars_runtime_def by blast
    thus "is_runtime_type (?be \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      using rt_cleared_caller_eq by simp
  qed

  \<comment> \<open>(3) tyenv_ghost_vars_subset ?be: TE_GhostLocals subset of TE_LocalVars dom (preserved
       under fmmap), TE_GhostGlobals subset of TE_GlobalVars (inherited). \<close>
  have c3: "tyenv_ghost_vars_subset ?be"
    using callee_ghost_subset
    unfolding tyenv_ghost_vars_subset_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(4) tyenv_return_type_well_kinded ?be: TE_ReturnType ?be = apply_subst subst (TE_ReturnType calleeEnv);
       given as a premise. But the predicate checks well-kindedness in ?be, not callerEnv.
       Use congruence to bridge. \<close>
  have wk_be_caller_eq:
    "\<And>ty. is_well_kinded ?be ty = is_well_kinded callerEnv ty"
    by (rule is_well_kinded_cong_env) (simp_all add: dt_eq[symmetric])
  have c4: "tyenv_return_type_well_kinded ?be"
    unfolding tyenv_return_type_well_kinded_def
    using ret_wk wk_be_caller_eq by simp

  \<comment> \<open>(5) tyenv_ctors_consistent ?be: TE_DataCtors and TE_Datatypes inherited from calleeEnv. \<close>
  have c5: "tyenv_ctors_consistent ?be"
    using callee_ctors_cons unfolding tyenv_ctors_consistent_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(6) tyenv_payloads_well_kinded ?be: inner override on TE_TypeVars; TE_DataCtors,
       TE_Datatypes inherited. \<close>
  have c6: "tyenv_payloads_well_kinded ?be"
    unfolding tyenv_payloads_well_kinded_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
    hence ctor_lk: "fmlookup (TE_DataCtors calleeEnv) ctorName = Some (dtName, tyVars, payload)"
      by (simp add: apply_subst_to_callee_env_def)
    with callee_payloads_wk
    have "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload"
      unfolding tyenv_payloads_well_kinded_def by blast
    thus "is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list tyVars \<rparr>) payload"
      using wk_scope_eq by simp
  qed

  \<comment> \<open>(7) tyenv_ctor_tyvars_distinct ?be: TE_DataCtors inherited. \<close>
  have c7: "tyenv_ctor_tyvars_distinct ?be"
    using callee_ctor_tyvars_distinct unfolding tyenv_ctor_tyvars_distinct_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(8) tyenv_ctors_by_type_consistent ?be: TE_DataCtorsByType, TE_DataCtors inherited. \<close>
  have c8: "tyenv_ctors_by_type_consistent ?be"
    using callee_ctors_by_type unfolding tyenv_ctors_by_type_consistent_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(9) tyenv_fun_types_well_kinded ?be: inner override; TE_Functions, TE_Datatypes inherited. \<close>
  have c9: "tyenv_fun_types_well_kinded ?be"
    unfolding tyenv_fun_types_well_kinded_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?be) funName = Some info"
    hence info_lk: "fmlookup (TE_Functions calleeEnv) funName = Some info"
      by (simp add: apply_subst_to_callee_env_def)
    with callee_fun_types_wk have
      args_wk: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
                  is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty"
      and ret_wk_inner: "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                                  (FI_ReturnType info)"
      unfolding tyenv_fun_types_well_kinded_def by auto
    show "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
              is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
          is_well_kinded (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info) \<rparr>) (FI_ReturnType info)"
      using args_wk ret_wk_inner wk_scope_eq by simp
  qed

  \<comment> \<open>(10) tyenv_fun_tyvars_distinct ?be: TE_Functions inherited. \<close>
  have c10: "tyenv_fun_tyvars_distinct ?be"
    using callee_fun_tyvars_distinct unfolding tyenv_fun_tyvars_distinct_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(11) tyenv_fun_param_names_distinct ?be: TE_Functions inherited. \<close>
  have c11: "tyenv_fun_param_names_distinct ?be"
    using callee_fun_param_names_distinct unfolding tyenv_fun_param_names_distinct_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(12) tyenv_fun_ghost_constraint ?be: inner override; TE_Functions inherited. \<close>
  have c12: "tyenv_fun_ghost_constraint ?be"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI, elim conjE)
    fix funName info
    assume info_lk_be: "fmlookup (TE_Functions ?be) funName = Some info"
       and ng_info: "FI_Ghost info = NotGhost"
    from info_lk_be have info_lk: "fmlookup (TE_Functions calleeEnv) funName = Some info"
      by (simp add: apply_subst_to_callee_env_def)
    from callee_fun_ghost info_lk ng_info have
      "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
            is_runtime_type (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                          TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
       is_runtime_type (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                     TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                       (FI_ReturnType info)"
      unfolding tyenv_fun_ghost_constraint_def Let_def by auto
    thus "(\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs info).
              is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                      TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>) ty) \<and>
           is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs info),
                                   TE_RuntimeTypeVars := fset_of_list (FI_TyArgs info) \<rparr>)
                           (FI_ReturnType info)"
      using rt_scope_eq by simp
  qed

  \<comment> \<open>(13) tyenv_nonghost_payloads_runtime ?be: inner override; TE_DataCtors,
        TE_GhostDatatypes inherited. \<close>
  have c13: "tyenv_nonghost_payloads_runtime ?be"
    unfolding tyenv_nonghost_payloads_runtime_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume ctor_lk_be: "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
       and ng_dt: "dtName |\<notin>| TE_GhostDatatypes ?be"
    from ctor_lk_be have ctor_lk: "fmlookup (TE_DataCtors calleeEnv) ctorName = Some (dtName, tyVars, payload)"
      by (simp add: apply_subst_to_callee_env_def)
    from ng_dt have ng_dt_callee: "dtName |\<notin>| TE_GhostDatatypes calleeEnv"
      by (simp add: apply_subst_to_callee_env_def)
    from callee_nonghost_payloads ctor_lk ng_dt_callee
    have "is_runtime_type (calleeEnv \<lparr> TE_TypeVars := fset_of_list tyVars,
                                        TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload"
      unfolding tyenv_nonghost_payloads_runtime_def by blast
    thus "is_runtime_type (?be \<lparr> TE_TypeVars := fset_of_list tyVars,
                                  TE_RuntimeTypeVars := fset_of_list tyVars \<rparr>) payload"
      using rt_scope_eq by simp
  qed

  \<comment> \<open>(14) tyenv_ghost_datatypes_subset ?be: TE_GhostDatatypes, TE_Datatypes inherited. \<close>
  have c14: "tyenv_ghost_datatypes_subset ?be"
    using callee_ghost_dt_subset unfolding tyenv_ghost_datatypes_subset_def
    by (simp add: apply_subst_to_callee_env_def)

  \<comment> \<open>(15) tyenv_runtime_tyvars_subset ?be: TE_RuntimeTypeVars and TE_TypeVars
       both come from callerEnv, so this reduces to the caller's subset clause. \<close>
  have c15: "tyenv_runtime_tyvars_subset ?be"
    using caller_rt_subset unfolding tyenv_runtime_tyvars_subset_def by simp

  from c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15
  show ?thesis unfolding tyenv_well_formed_def by simp
qed


(* ========================================================================== *)
(* Shared setup for FunctionCall substitution proofs                           *)
(* ========================================================================== *)

(* The "preamble" facts that both pure-call and impure-call substitution proofs
   need once they've looked up a function. Given a successful lookup plus the
   ambient subst-ok hypotheses, this bundles the facts about the substituted
   type arguments (well-kindedness, runtime-ness in NotGhost mode, length), the
   distinctness of the function's type parameters, the containment of FI_TmArgs
   / FI_ReturnType type variables in FI_TyArgs, and the substitution-composition
   equation for the return type. Both callers destructure this with obtain. *)
lemma function_call_subst_setup:
  assumes fn_lookup: "fmlookup (TE_Functions calleeEnv) fnName = Some funInfo"
      and len_tyArgs: "length tyArgs = length (FI_TyArgs funInfo)"
      and tyArgs_wk: "list_all (is_well_kinded calleeEnv) tyArgs"
      and ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type calleeEnv) tyArgs"
      and wf: "tyenv_well_formed calleeEnv"
      and ok: "callee_env_subst_ok subst callerEnv calleeEnv"
      and subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded callerEnv ty'"
      and ok_rt: "ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv"
  shows "fmlookup (TE_Functions (apply_subst_to_callee_env subst callerEnv calleeEnv)) fnName
           = Some funInfo"
    and "list_all (is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv))
                  (map (apply_subst subst) tyArgs)"
    and "ghost = NotGhost \<longrightarrow>
         list_all (is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv))
                  (map (apply_subst subst) tyArgs)"
    and "length (map (apply_subst subst) tyArgs) = length (FI_TyArgs funInfo)"
    and "distinct (FI_TyArgs funInfo)"
    and "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
           type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
    and "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    and "apply_subst subst (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                         (FI_ReturnType funInfo))
           = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst subst) tyArgs)))
                         (FI_ReturnType funInfo)"
proof -
  show "fmlookup (TE_Functions (apply_subst_to_callee_env subst callerEnv calleeEnv)) fnName
          = Some funInfo"
    using fn_lookup by simp

  show "list_all (is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv))
                 (map (apply_subst subst) tyArgs)"
    using tyArgs_wk
    by (induction tyArgs)
       (auto intro: apply_subst_preserves_well_kinded_callee[OF _ ok])

  show "ghost = NotGhost \<longrightarrow>
        list_all (is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv))
                 (map (apply_subst subst) tyArgs)"
  proof
    assume ng: "ghost = NotGhost"
    with ng_tyArgs have rt: "list_all (is_runtime_type calleeEnv) tyArgs" by simp
    from ng ok_rt have ok_rt': "callee_env_subst_runtime_ok subst callerEnv calleeEnv" by simp
    show "list_all (is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv))
                   (map (apply_subst subst) tyArgs)"
      using rt
      by (induction tyArgs)
         (auto intro: apply_subst_preserves_runtime_callee[OF _ ok ok_rt'])
  qed

  show "length (map (apply_subst subst) tyArgs) = length (FI_TyArgs funInfo)"
    using len_tyArgs by simp

  show tyArgs_distinct: "distinct (FI_TyArgs funInfo)"
    using wf fn_lookup
    unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def by blast

  have fi_args_wk:
    "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
       is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t"
    using wf fn_lookup
    unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fi_ret_wk:
    "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) (FI_ReturnType funInfo)"
    using wf fn_lookup
    unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast

  show fi_args_tyvars:
    "\<forall>t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
  proof
    fix t assume "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
    with fi_args_wk
    have "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t"
      by blast
    from is_well_kinded_type_tyvars_subset[OF this]
    show "type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
      by (simp add: fset_of_list.rep_eq)
  qed

  show fi_ret_tyvars: "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
    using is_well_kinded_type_tyvars_subset[OF fi_ret_wk]
    by (simp add: fset_of_list.rep_eq)

  show "apply_subst subst (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                        (FI_ReturnType funInfo))
          = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst subst) tyArgs)))
                        (FI_ReturnType funInfo)"
    using apply_subst_compose_zip[OF len_tyArgs[symmetric] fi_ret_tyvars tyArgs_distinct, of subst]
    by simp
qed


(* ========================================================================== *)
(* Term typing under callee-env substitution                                   *)
(* ========================================================================== *)

(* If a term typechecks in calleeEnv, then it typechecks (with substituted result
   type) in the substituted callee env. The term itself is not substituted; only
   the env changes. This is what case 6 of type soundness needs to re-typecheck a
   function body's terms in the caller's context.

   Conditions:
   - calleeEnv is well-formed (so variable lookups land on well-kinded types, etc.)
   - callee_env_subst_ok: caller and callee envs agree on the global-ish fields,
     and the substitution covers callee type variables with caller-typed values
   - The substitution's range is well-kinded in callerEnv (needed for any embedded
     types like Cast targets, Quantifier binders, function tyArgs, etc., to remain
     well-kinded after substitution)
   - In NotGhost mode, the substitution's range is also runtime in callerEnv
     (needed for the runtime-type checks at non-ghost positions). *)
lemma core_term_type_subst_callee_env:
  assumes "core_term_type calleeEnv ghost tm = Some ty"
      and "tyenv_well_formed calleeEnv"
      and "callee_env_subst_ok subst callerEnv calleeEnv"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded callerEnv ty'"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
      and "ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv"
  shows "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                        (apply_subst_to_term subst tm)
           = Some (apply_subst subst ty)"
using assms proof (induction tm arbitrary: ty ghost calleeEnv)
  case (CoreTm_LitBool b)
  \<comment> \<open>LitBool always has type Bool, which is closed under substitution. \<close>
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  \<comment> \<open>LitInt has a finite-int type, which is closed under substitution. \<close>
  then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray elemTy tms)
  \<comment> \<open>LitArray: each element must typecheck to elemTy. After substitution, each
      element typechecks to (apply_subst subst elemTy), and the result type is
      Array (apply_subst subst elemTy) [Fixed (length tms)]. \<close>
  from CoreTm_LitArray.prems(1) have
    elemTy_wk: "is_well_kinded calleeEnv elemTy" and
    elemTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type calleeEnv elemTy" and
    tms_typed: "list_all (\<lambda>tm. core_term_type calleeEnv ghost tm = Some elemTy) tms" and
    len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)

  have elemTy_wk_subst: "is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv)
                                        (apply_subst subst elemTy)"
    using apply_subst_preserves_well_kinded_callee[OF elemTy_wk CoreTm_LitArray.prems(3)] .
  have elemTy_rt_subst:
    "ghost = NotGhost \<longrightarrow>
       is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                       (apply_subst subst elemTy)"
  proof
    assume ng: "ghost = NotGhost"
    with elemTy_rt have rt: "is_runtime_type calleeEnv elemTy" by simp
    from ng CoreTm_LitArray.prems(6) have ok_rt: "callee_env_subst_runtime_ok subst callerEnv calleeEnv"
      by simp
    from apply_subst_preserves_runtime_callee[OF rt CoreTm_LitArray.prems(3) ok_rt]
    show "is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                          (apply_subst subst elemTy)" .
  qed

  \<comment> \<open>Each element typechecks to (apply_subst subst elemTy) after substitution. \<close>
  have tms_subst:
    "list_all (\<lambda>tm. core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost tm
                      = Some (apply_subst subst elemTy))
              (map (apply_subst_to_term subst) tms)"
  proof (unfold list_all_iff, intro ballI)
    fix tm' assume "tm' \<in> set (map (apply_subst_to_term subst) tms)"
    then obtain tm where tm_in: "tm \<in> set tms" and tm'_eq: "tm' = apply_subst_to_term subst tm"
      by auto
    from tms_typed tm_in have tm_typed: "core_term_type calleeEnv ghost tm = Some elemTy"
      by (simp add: list_all_iff)
    from CoreTm_LitArray.IH[OF tm_in tm_typed CoreTm_LitArray.prems(2,3,4,5,6)]
    show "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost tm'
            = Some (apply_subst subst elemTy)"
      using tm'_eq by simp
  qed

  have len_eq: "length (map (apply_subst_to_term subst) tms) = length tms" by simp

  show ?case
    using elemTy_wk_subst elemTy_rt_subst tms_subst len_eq len_ok ty_eq by simp
next
  case (CoreTm_Var name)
  \<comment> \<open>Var: looks up the variable in locals (substituted types) or globals (closed
      types). apply_subst_to_term is the identity on Var (no type substitution).
      For local vars, the substituted type is apply_subst subst (original type);
      for global vars, globals are closed so apply_subst subst ty = ty. \<close>
  from CoreTm_Var.prems(1) obtain lookupTy where
    lookup: "tyenv_lookup_var calleeEnv name = Some lookupTy" and
    not_ghost_ok: "ghost = NotGhost \<longrightarrow> \<not> tyenv_var_ghost calleeEnv name" and
    ty_eq: "ty = lookupTy"
    by (auto split: option.splits if_splits)
  show ?case
  proof (cases "fmlookup (TE_LocalVars calleeEnv) name")
    case (Some localTy)
    with lookup have ty_local: "lookupTy = localTy"
      by (simp add: tyenv_lookup_var_def)
    from Some ty_local have
      lookup_subst: "tyenv_lookup_var (apply_subst_to_callee_env subst callerEnv calleeEnv) name
                       = Some (apply_subst subst localTy)"
      by (simp add: tyenv_lookup_var_apply_subst_to_callee_env)
    show ?thesis
      using lookup_subst ty_eq ty_local not_ghost_ok by simp
  next
    case None
    with lookup have gv: "fmlookup (TE_GlobalVars calleeEnv) name = Some lookupTy"
      by (simp add: tyenv_lookup_var_def)
    \<comment> \<open>Global's type is closed (well-formed env), so apply_subst is identity. \<close>
    from gv CoreTm_Var.prems(2) have wk_cleared:
      "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) lookupTy"
      unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
    have tyvars_empty: "type_tyvars lookupTy = {}"
      using is_well_kinded_type_tyvars_subset[OF wk_cleared] by simp
    have ty_closed: "apply_subst subst lookupTy = lookupTy"
      using tyvars_empty by (simp add: apply_subst_disjoint_id)
    from None have
      lookup_subst: "tyenv_lookup_var (apply_subst_to_callee_env subst callerEnv calleeEnv) name
                       = fmlookup (TE_GlobalVars calleeEnv) name"
      by (simp add: tyenv_lookup_var_apply_subst_to_callee_env)
    show ?thesis
      using lookup_subst gv ty_eq ty_closed not_ghost_ok by simp
  qed
next
  case (CoreTm_Cast targetTy operand)
  \<comment> \<open>Cast: operand has some integer type; result is targetTy (also integer).
      Substitution leaves integer types unchanged, so after substitution the
      operand's type is still an integer (the same one), the target is still
      an integer (and unchanged). \<close>
  from CoreTm_Cast.prems(1) obtain operandTy where
    op_typed: "core_term_type calleeEnv ghost operand = Some operandTy" and
    op_int: "is_integer_type operandTy" and
    tgt_int: "is_integer_type targetTy" and
    tgt_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type calleeEnv targetTy" and
    ty_eq: "ty = targetTy"
    by (auto split: option.splits if_splits)
  from CoreTm_Cast.IH[OF op_typed CoreTm_Cast.prems(2,3,4,5,6)]
  have op_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst operand)
       = Some (apply_subst subst operandTy)" .
  have op_ty_eq: "apply_subst subst operandTy = operandTy"
    using op_int is_integer_type_apply_subst by simp
  have tgt_ty_eq: "apply_subst subst targetTy = targetTy"
    using tgt_int is_integer_type_apply_subst by simp
  \<comment> \<open>The substituted targetTy, for the runtime check, stays runtime since it's
      closed (integer types have no type variables). \<close>
  have tgt_rt_subst:
    "ghost = NotGhost \<longrightarrow>
       is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                       (apply_subst subst targetTy)"
  proof
    assume ng: "ghost = NotGhost"
    with tgt_rt have rt: "is_runtime_type calleeEnv targetTy" by simp
    from ng CoreTm_Cast.prems(6) have ok_rt: "callee_env_subst_runtime_ok subst callerEnv calleeEnv"
      by simp
    from apply_subst_preserves_runtime_callee[OF rt CoreTm_Cast.prems(3) ok_rt]
    show "is_runtime_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                          (apply_subst subst targetTy)" .
  qed
  show ?case
    using op_subst op_int op_ty_eq tgt_int tgt_ty_eq tgt_rt_subst ty_eq
    by auto
next
  case (CoreTm_Unop op operand)
  \<comment> \<open>Unop: operand has some type, result depends on the operator. For Negate the
      operand is signed numeric, for Complement finite integer, for Not boolean.
      All of these are closed types; substitution leaves them unchanged. \<close>
  from CoreTm_Unop.prems(1) obtain operandTy where
    op_typed: "core_term_type calleeEnv ghost operand = Some operandTy"
    by (auto split: option.splits)
  from CoreTm_Unop.IH[OF op_typed CoreTm_Unop.prems(2,3,4,5,6)]
  have op_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst operand)
       = Some (apply_subst subst operandTy)" .
  show ?case
  proof (cases op)
    case CoreUnop_Negate
    with CoreTm_Unop.prems(1) op_typed have
      op_sn: "is_signed_numeric_type operandTy" and
      ty_eq: "ty = operandTy"
      by (auto split: if_splits)
    have "apply_subst subst operandTy = operandTy"
      using op_sn is_signed_numeric_type_apply_subst by simp
    with op_subst op_sn ty_eq CoreUnop_Negate show ?thesis by simp
  next
    case CoreUnop_Complement
    with CoreTm_Unop.prems(1) op_typed have
      op_fi: "is_finite_integer_type operandTy" and
      ty_eq: "ty = operandTy"
      by (auto split: if_splits)
    have "apply_subst subst operandTy = operandTy"
      using op_fi is_finite_integer_type_apply_subst by simp
    with op_subst op_fi ty_eq CoreUnop_Complement show ?thesis by simp
  next
    case CoreUnop_Not
    with CoreTm_Unop.prems(1) op_typed have
      op_bool: "operandTy = CoreTy_Bool" and
      ty_eq: "ty = CoreTy_Bool"
      by (auto split: if_splits)
    with op_subst CoreUnop_Not show ?thesis by simp
  qed
next
  case (CoreTm_Binop op lhs rhs)
  \<comment> \<open>Binop: lhs and rhs have the same type. Split by operator category. For
      arithmetic/modulo/bitwise/shift/ordering/logical, the type is a closed
      concrete type so substitution is the identity. For eq/neq the result type
      is always Bool; the operand type may be arbitrary in Ghost mode, but both
      operands still have the same (substituted) type after substitution. \<close>
  from CoreTm_Binop.prems(1) obtain lhsTy rhsTy where
    lhs_typed: "core_term_type calleeEnv ghost lhs = Some lhsTy" and
    rhs_typed: "core_term_type calleeEnv ghost rhs = Some rhsTy"
    by (auto split: option.splits)
  from CoreTm_Binop.IH(1)[OF lhs_typed CoreTm_Binop.prems(2,3,4,5,6)]
  have lhs_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst lhs)
       = Some (apply_subst subst lhsTy)" .
  from CoreTm_Binop.IH(2)[OF rhs_typed CoreTm_Binop.prems(2,3,4,5,6)]
  have rhs_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst rhs)
       = Some (apply_subst subst rhsTy)" .
  from CoreTm_Binop.prems(1) lhs_typed rhs_typed have tys_eq: "lhsTy = rhsTy"
    by (auto split: if_splits)

  from binop_category_exhaustive[of op] consider
    "is_arithmetic_binop op" | "is_modulo_binop op" | "is_bitwise_binop op"
    | "is_shift_binop op" | "is_ordering_binop op" | "is_eq_neq_binop op"
    | "is_logical_binop op"
    by blast
  thus ?case
  proof cases
    case 1  \<comment> \<open>arithmetic: requires numeric, result is operand type\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      num: "is_numeric_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using num is_numeric_type_apply_subst by simp
    show ?thesis
      using 1 lhs_subst rhs_subst tys_eq ty_eq ty_closed num
      by (auto dest: binop_categories_disjoint)
  next
    case 2  \<comment> \<open>modulo: requires integer\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      int: "is_integer_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using int is_integer_type_apply_subst by simp
    show ?thesis
      using 2 lhs_subst rhs_subst tys_eq ty_eq ty_closed int
      by (auto dest: binop_categories_disjoint)
  next
    case 3  \<comment> \<open>bitwise: requires finite integer\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      fi: "is_finite_integer_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using fi is_finite_integer_type_apply_subst by simp
    show ?thesis
      using 3 lhs_subst rhs_subst tys_eq ty_eq ty_closed fi
      by (auto dest: binop_categories_disjoint)
  next
    case 4  \<comment> \<open>shift: requires finite integer\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      fi: "is_finite_integer_type lhsTy" and ty_eq: "ty = lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using fi is_finite_integer_type_apply_subst by simp
    show ?thesis
      using 4 lhs_subst rhs_subst tys_eq ty_eq ty_closed fi
      by (auto dest: binop_categories_disjoint)
  next
    case 5  \<comment> \<open>ordering: requires numeric, result is Bool\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      num: "is_numeric_type lhsTy" and ty_eq: "ty = CoreTy_Bool"
      by (auto dest: binop_categories_disjoint split: if_splits)
    have ty_closed: "apply_subst subst lhsTy = lhsTy"
      using num is_numeric_type_apply_subst by simp
    show ?thesis
      using 5 lhs_subst rhs_subst tys_eq ty_eq ty_closed num
      by (auto dest: binop_categories_disjoint)
  next
    case 6  \<comment> \<open>eq/neq: any same-type operands (in Ghost) or bool/numeric, result Bool\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      ty_eq: "ty = CoreTy_Bool" and
      typing_ok: "ghost = Ghost \<or> lhsTy = CoreTy_Bool \<or> is_numeric_type lhsTy"
      by (auto dest: binop_categories_disjoint split: if_splits)
    show ?thesis
      using 6 lhs_subst rhs_subst tys_eq ty_eq typing_ok
            is_numeric_type_apply_subst
      by (auto dest: binop_categories_disjoint split: if_splits)
  next
    case 7  \<comment> \<open>logical: requires Bool\<close>
    with CoreTm_Binop.prems(1) lhs_typed rhs_typed have
      bool_eq: "lhsTy = CoreTy_Bool" and ty_eq: "ty = CoreTy_Bool"
      by (auto dest: binop_categories_disjoint split: if_splits)
    show ?thesis
      using 7 lhs_subst rhs_subst tys_eq ty_eq bool_eq
      by (auto dest: binop_categories_disjoint)
  qed
next
  case (CoreTm_Let var rhs body)
  \<comment> \<open>Let: rhs gets typechecked in calleeEnv; body in the env extended with
      (var, rhsTy). We apply the rhs IH against calleeEnv, then the body IH
      against the extended env. The substituted extended env equals the env
      extension of the substituted env. \<close>
  from CoreTm_Let.prems(1) obtain rhsTy where
    rhs_typed: "core_term_type calleeEnv ghost rhs = Some rhsTy" and
    body_typed: "core_term_type
                   (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                                TE_GhostLocals := (if ghost = Ghost
                                                  then finsert var (TE_GhostLocals calleeEnv)
                                                  else fminus (TE_GhostLocals calleeEnv) {|var|}),
                                TE_ConstLocals := finsert var (TE_ConstLocals calleeEnv) \<rparr>)
                   ghost body = Some ty"
    by (auto split: option.splits simp: Let_def)

  let ?env_ext = "calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                              TE_GhostLocals := (if ghost = Ghost
                                                then finsert var (TE_GhostLocals calleeEnv)
                                                else fminus (TE_GhostLocals calleeEnv) {|var|}),
                              TE_ConstLocals := finsert var (TE_ConstLocals calleeEnv) \<rparr>"

  \<comment> \<open>RHS IH gives the substituted rhs has the substituted rhsTy. \<close>
  from CoreTm_Let.IH(1)[OF rhs_typed CoreTm_Let.prems(2,3,4,5,6)]
  have rhs_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst rhs)
       = Some (apply_subst subst rhsTy)" .

  \<comment> \<open>The new local's type is well-kinded (and runtime if ghost = NotGhost) by
      core_term_type's wellformedness preservation. \<close>
  have rhsTy_wk: "is_well_kinded calleeEnv rhsTy"
    using core_term_type_well_kinded[OF rhs_typed CoreTm_Let.prems(2)] .
  have rhsTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type calleeEnv rhsTy"
  proof
    assume ng: "ghost = NotGhost"
    with rhs_typed have "core_term_type calleeEnv NotGhost rhs = Some rhsTy" by simp
    from core_term_type_notghost_runtime[OF this CoreTm_Let.prems(2)]
    show "is_runtime_type calleeEnv rhsTy" .
  qed

  have wf_ext: "tyenv_well_formed ?env_ext"
  proof (cases ghost)
    case NotGhost
    from rhsTy_rt NotGhost have rt: "is_runtime_type calleeEnv rhsTy" by simp
    from tyenv_well_formed_add_var[OF CoreTm_Let.prems(2) rhsTy_wk rt]
    have wf':
      "tyenv_well_formed
         (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                      TE_GhostLocals := fminus (TE_GhostLocals calleeEnv) {|var|} \<rparr>)" .
    from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf',
            of "finsert var (TE_ConstLocals calleeEnv)"]
    have "tyenv_well_formed
            (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                         TE_GhostLocals := fminus (TE_GhostLocals calleeEnv) {|var|} \<rparr>
                       \<lparr> TE_ConstLocals := finsert var (TE_ConstLocals calleeEnv) \<rparr>)" .
    with NotGhost show ?thesis by simp
  next
    case Ghost
    from tyenv_well_formed_add_ghost_var[OF CoreTm_Let.prems(2) rhsTy_wk]
    have wf':
      "tyenv_well_formed
         (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                      TE_GhostLocals := finsert var (TE_GhostLocals calleeEnv) \<rparr>)" .
    from tyenv_well_formed_TE_ConstLocals_irrelevant[OF wf',
            of "finsert var (TE_ConstLocals calleeEnv)"]
    have "tyenv_well_formed
            (calleeEnv \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars calleeEnv),
                         TE_GhostLocals := finsert var (TE_GhostLocals calleeEnv) \<rparr>
                       \<lparr> TE_ConstLocals := finsert var (TE_ConstLocals calleeEnv) \<rparr>)" .
    with Ghost show ?thesis by simp
  qed

  \<comment> \<open>callee_env_subst_ok ?env_ext: same as for calleeEnv since we only changed
      TE_LocalVars / TE_GhostLocals / TE_ConstLocals, none of which appear in
      callee_env_subst_ok. \<close>
  have ok_ext: "callee_env_subst_ok subst callerEnv ?env_ext"
    using CoreTm_Let.prems(3)
    unfolding callee_env_subst_ok_def by simp

  have ok_rt_ext: "ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv ?env_ext"
    using CoreTm_Let.prems(6)
    unfolding callee_env_subst_runtime_ok_def by simp

  from CoreTm_Let.IH(2)[OF body_typed wf_ext ok_ext CoreTm_Let.prems(4) CoreTm_Let.prems(5) ok_rt_ext]
  have body_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv ?env_ext) ghost
                    (apply_subst_to_term subst body)
       = Some (apply_subst subst ty)" .

  \<comment> \<open>The substituted extended env equals the extended substituted env. \<close>
  have ext_subst_eq:
    "apply_subst_to_callee_env subst callerEnv ?env_ext
       = (apply_subst_to_callee_env subst callerEnv calleeEnv) \<lparr>
            TE_LocalVars := fmupd var (apply_subst subst rhsTy)
                              (TE_LocalVars (apply_subst_to_callee_env subst callerEnv calleeEnv)),
            TE_GhostLocals := (if ghost = Ghost
                              then finsert var (TE_GhostLocals (apply_subst_to_callee_env subst callerEnv calleeEnv))
                              else fminus (TE_GhostLocals (apply_subst_to_callee_env subst callerEnv calleeEnv))
                                          {|var|}),
            TE_ConstLocals := finsert var (TE_ConstLocals (apply_subst_to_callee_env subst callerEnv calleeEnv)) \<rparr>"
    unfolding apply_subst_to_callee_env_def by (simp add: fmmap_fmupd)

  show ?case
    using rhs_subst body_subst ext_subst_eq by (simp add: Let_def)
next
  case (CoreTm_Quantifier quant var varTy body)
  \<comment> \<open>Quantifier: ghost-only. Body typechecks in env extended with (var, varTy)
      where varTy is well-kinded. Result is Bool. \<close>
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Quantifier.prems(1) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Quantifier.prems(1) have
      varTy_wk: "is_well_kinded calleeEnv varTy" and
      body_typed: "core_term_type
                     (calleeEnv \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars calleeEnv),
                                  TE_GhostLocals := finsert var (TE_GhostLocals calleeEnv) \<rparr>)
                     Ghost body = Some CoreTy_Bool" and
      ty_eq: "ty = CoreTy_Bool"
      by (auto split: option.splits CoreType.splits if_splits)

    let ?env_ext = "calleeEnv \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars calleeEnv),
                                TE_GhostLocals := finsert var (TE_GhostLocals calleeEnv) \<rparr>"

    \<comment> \<open>well-formedness of ?env_ext via tyenv_well_formed_add_ghost_var \<close>
    from tyenv_well_formed_add_ghost_var[OF CoreTm_Quantifier.prems(2) varTy_wk]
    have wf_ext: "tyenv_well_formed ?env_ext" .

    \<comment> \<open>callee_env_subst_ok ?env_ext: only TE_LocalVars / TE_GhostLocals changed,
        which callee_env_subst_ok doesn't reference. \<close>
    have ok_ext: "callee_env_subst_ok subst callerEnv ?env_ext"
      using CoreTm_Quantifier.prems(3)
      unfolding callee_env_subst_ok_def by simp

    \<comment> \<open>Substituted varTy is well-kinded in the substituted env. \<close>
    have varTy_wk_subst:
      "is_well_kinded (apply_subst_to_callee_env subst callerEnv calleeEnv)
                      (apply_subst subst varTy)"
      using apply_subst_preserves_well_kinded_callee[OF varTy_wk CoreTm_Quantifier.prems(3)] .

    \<comment> \<open>Body IH (in Ghost mode, so both runtime preconditions are vacuous). \<close>
    have body_rt_premise:
      "Ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
      by simp
    have body_rt_ok_premise:
      "Ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv ?env_ext"
      by simp
    from CoreTm_Quantifier.IH[OF body_typed wf_ext ok_ext CoreTm_Quantifier.prems(4)
                                  body_rt_premise body_rt_ok_premise]
    have body_subst:
      "core_term_type (apply_subst_to_callee_env subst callerEnv ?env_ext) Ghost
                      (apply_subst_to_term subst body)
         = Some (apply_subst subst CoreTy_Bool)" .

    \<comment> \<open>The substituted ?env_ext equals the substituted env extended with
        (var, apply_subst subst varTy). \<close>
    have ext_subst_eq:
      "apply_subst_to_callee_env subst callerEnv ?env_ext
         = (apply_subst_to_callee_env subst callerEnv calleeEnv) \<lparr>
              TE_LocalVars := fmupd var (apply_subst subst varTy)
                                (TE_LocalVars (apply_subst_to_callee_env subst callerEnv calleeEnv)),
              TE_GhostLocals := finsert var (TE_GhostLocals (apply_subst_to_callee_env subst callerEnv calleeEnv)) \<rparr>"
      unfolding apply_subst_to_callee_env_def by (simp add: fmmap_fmupd)

    show ?thesis
      using body_subst varTy_wk_subst ext_subst_eq Ghost ty_eq by simp
  qed
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  \<comment> \<open>FunctionCall: the typechecker builds an inner substitution mapping the
      callee's type parameters (FI_TyArgs) to the call-site type arguments (tyArgs),
      and applies it to the callee's argument and return types. After our outer
      substitution, the tyArgs become substituted; the inner substitution then
      uses the substituted tyArgs. Substitution composition (apply_subst_compose_zip)
      lets us conclude that the result type matches. \<close>
  from CoreTm_FunctionCall.prems(1) obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions calleeEnv) fnName = Some funInfo" and
    len_tyArgs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyArgs_wk: "list_all (is_well_kinded calleeEnv) tyArgs" and
    not_ghost_cond: "\<not> (ghost = NotGhost
                       \<and> (\<not> list_all (is_runtime_type calleeEnv) tyArgs
                          \<or> FI_Ghost funInfo = Ghost))" and
    all_var: "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)" and
    not_impure: "\<not> FI_Impure funInfo" and
    len_tmArgs: "length tmArgs = length (FI_TmArgs funInfo)" and
    args_check: "list_all2 (\<lambda>tm expectedTy.
                    case core_term_type calleeEnv ghost tm of
                      None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  tmArgs (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                              (FI_TmArgs funInfo))" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: option.splits if_splits)
  have ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type calleeEnv) tyArgs"
    using not_ghost_cond by blast
  have ng_fn: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    using not_ghost_cond by blast

  let ?be = "apply_subst_to_callee_env subst callerEnv calleeEnv"
  let ?subst_tyArgs = "map (apply_subst subst) tyArgs"
  let ?innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?subst_innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) ?subst_tyArgs)"

  \<comment> \<open>Bundled setup facts from the shared helper. \<close>
  note call_setup = function_call_subst_setup[OF fn_lookup len_tyArgs tyArgs_wk ng_tyArgs
                                                 CoreTm_FunctionCall.prems(2,3,4,6)]
  note fn_lookup_subst   = call_setup(1)
  note tyArgs_wk_subst   = call_setup(2)
  note tyArgs_rt_subst   = call_setup(3)
  note len_tyArgs_subst  = call_setup(4)
  note tyArgs_distinct   = call_setup(5)
  note fi_args_tyvars    = call_setup(6)
  note fi_ret_tyvars     = call_setup(7)
  note ret_compose       = call_setup(8)

  have len_tmArgs_eq: "length tmArgs = length (FI_TmArgs funInfo)" using len_tmArgs .

  \<comment> \<open>Each tmArg's IH lifts to the substituted version. The expected type after
      substitution is apply_subst subst (apply_subst ?innerSubst (FI_TmArgs[i].type)),
      which by composition equals apply_subst ?subst_innerSubst (FI_TmArgs[i].type). \<close>
  have args_check_subst:
    "list_all2 (\<lambda>tm expectedTy.
                  case core_term_type ?be ghost tm of
                    None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
              (map (apply_subst_to_term subst) tmArgs)
              (map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty) (FI_TmArgs funInfo))"
  proof -
    \<comment> \<open>The original list_all2 says, for each tmArg, the term typechecks to the
        expected substituted-arg-type. The IH on each tmArg gives us the substituted
        version, which has the substituted-substituted type. Composition equates
        that to the substituted-with-composed-tyArgs type. \<close>
    have len_eq:
      "length tmArgs = length (map (\<lambda>(_, ty, _). apply_subst ?innerSubst ty) (FI_TmArgs funInfo))"
      using len_tmArgs by simp
    show ?thesis
    proof (rule list_all2_all_nthI)
      show "length (map (apply_subst_to_term subst) tmArgs)
              = length (map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty) (FI_TmArgs funInfo))"
        using len_tmArgs by simp
    next
      fix i assume i_bound: "i < length (map (apply_subst_to_term subst) tmArgs)"
      hence i_bound': "i < length tmArgs" by simp
      hence i_bound_args: "i < length (FI_TmArgs funInfo)" using len_tmArgs by simp
      \<comment> \<open>From args_check, the i-th tmArg typechecks to the i-th expected (inner-sub'd) type. \<close>
      from args_check have args_nth_raw:
        "case core_term_type calleeEnv ghost (tmArgs ! i) of
           None \<Rightarrow> False
         | Some actualTy \<Rightarrow>
             actualTy = map (\<lambda>(_, ty, _). apply_subst ?innerSubst ty) (FI_TmArgs funInfo) ! i"
        using i_bound' len_tmArgs
        by (simp add: list_all2_conv_all_nth)
      have args_nth:
        "case core_term_type calleeEnv ghost (tmArgs ! i) of
           None \<Rightarrow> False
         | Some actualTy \<Rightarrow> actualTy = (case FI_TmArgs funInfo ! i of
              (_, ty, _) \<Rightarrow> apply_subst ?innerSubst ty)"
        using args_nth_raw i_bound_args
        by (metis nth_map)
      then obtain actualTy where
        actual_typed: "core_term_type calleeEnv ghost (tmArgs ! i) = Some actualTy" and
        actual_eq: "actualTy = (case FI_TmArgs funInfo ! i of
                                (_, ty, _) \<Rightarrow> apply_subst ?innerSubst ty)"
        by (auto split: option.splits)
      \<comment> \<open>Apply the IH to this tmArg. \<close>
      have tmArg_in: "tmArgs ! i \<in> set tmArgs" using i_bound' by simp
      from CoreTm_FunctionCall.IH[OF tmArg_in actual_typed
                                     CoreTm_FunctionCall.prems(2,3,4,5,6)]
      have ih_result:
        "core_term_type ?be ghost (apply_subst_to_term subst (tmArgs ! i))
           = Some (apply_subst subst actualTy)" .
      \<comment> \<open>The substituted actual type equals the substituted-with-composed
          version of the i-th FI_TmArgs type. \<close>
      obtain n ti vor where fi_arg_eq: "FI_TmArgs funInfo ! i = (n, ti, vor)"
        by (cases "FI_TmArgs funInfo ! i") auto
      from actual_eq fi_arg_eq have actual_eq2: "actualTy = apply_subst ?innerSubst ti" by simp
      \<comment> \<open>ti's type variables are in FI_TyArgs (from fi_args_tyvars). \<close>
      have ti_in: "ti \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
        using i_bound_args fi_arg_eq
        by (force simp: image_iff in_set_conv_nth)
      with fi_args_tyvars have ti_tyvars: "type_tyvars ti \<subseteq> set (FI_TyArgs funInfo)" by blast
      have actual_compose:
        "apply_subst subst actualTy = apply_subst ?subst_innerSubst ti"
        unfolding actual_eq2
        using apply_subst_compose_zip[OF len_tyArgs[symmetric] ti_tyvars tyArgs_distinct, of subst]
        by simp
      from ih_result actual_compose have ih_result':
        "core_term_type ?be ghost (apply_subst_to_term subst (tmArgs ! i))
           = Some (apply_subst ?subst_innerSubst ti)" by simp
      show "case core_term_type ?be ghost (map (apply_subst_to_term subst) tmArgs ! i) of
              None \<Rightarrow> False
            | Some actualTy \<Rightarrow> actualTy = map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty)
                                              (FI_TmArgs funInfo) ! i"
        using ih_result' i_bound' i_bound_args fi_arg_eq
        by simp
    qed
  qed

  show ?case
    using fn_lookup_subst len_tyArgs_subst tyArgs_wk_subst tyArgs_rt_subst ng_fn
          all_var not_impure len_tmArgs_eq args_check_subst ty_eq ret_compose
    by (auto simp: Let_def)
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  \<comment> \<open>VariantCtor: looks up the constructor; tyArgs are well-kinded; in NotGhost
      tyArgs are runtime and the datatype is non-ghost; payload typechecks to
      apply_subst (zip tyvars tyArgs) payloadTy; result is Datatype dtName tyArgs.

      After substitution: tyArgs become substituted tyArgs (well-kinded/runtime
      via apply_subst_preserves_*_callee), payload's IH lifts, the inner
      substitution composes via apply_subst_compose_zip. \<close>
  from CoreTm_VariantCtor.prems(1) obtain dtName tyvars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors calleeEnv) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    tyArgs_wk: "list_all (is_well_kinded calleeEnv) tyArgs" and
    ng_constraint: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type calleeEnv) tyArgs
                                          \<and> dtName |\<notin>| TE_GhostDatatypes calleeEnv" and
    payload_typed: "core_term_type calleeEnv ghost payload
                      = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)" and
    ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
    by (auto split: option.splits if_splits prod.splits)

  let ?be = "apply_subst_to_callee_env subst callerEnv calleeEnv"
  let ?subst_tyArgs = "map (apply_subst subst) tyArgs"

  \<comment> \<open>Constructor lookup unchanged in substituted env. \<close>
  have ctor_lookup_subst:
    "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyvars, payloadTy)"
    using ctor_lookup by simp

  \<comment> \<open>Substituted tyArgs are well-kinded in ?be. \<close>
  have tyArgs_wk_subst: "list_all (is_well_kinded ?be) ?subst_tyArgs"
    using tyArgs_wk
    by (induction tyArgs)
       (auto intro: apply_subst_preserves_well_kinded_callee[OF _ CoreTm_VariantCtor.prems(3)])

  \<comment> \<open>Substituted tyArgs are runtime in ?be (when ghost = NotGhost). \<close>
  have tyArgs_rt_subst:
    "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?be) ?subst_tyArgs"
  proof
    assume ng: "ghost = NotGhost"
    with ng_constraint have rt: "list_all (is_runtime_type calleeEnv) tyArgs" by simp
    from ng CoreTm_VariantCtor.prems(6) have ok_rt:
      "callee_env_subst_runtime_ok subst callerEnv calleeEnv" by simp
    show "list_all (is_runtime_type ?be) ?subst_tyArgs"
      using rt
      by (induction tyArgs)
         (auto intro: apply_subst_preserves_runtime_callee[OF _ CoreTm_VariantCtor.prems(3) ok_rt])
  qed

  \<comment> \<open>The datatype is non-ghost (when ghost = NotGhost); ?be inherits TE_GhostDatatypes
      from calleeEnv so the same. \<close>
  have ng_dt_subst:
    "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes ?be"
    using ng_constraint by simp

  \<comment> \<open>Payload IH gives the substituted payload typechecks to substituted result. \<close>
  from CoreTm_VariantCtor.IH[OF payload_typed CoreTm_VariantCtor.prems(2,3,4,5,6)]
  have payload_subst:
    "core_term_type ?be ghost (apply_subst_to_term subst payload)
       = Some (apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy))" .

  \<comment> \<open>tyvars are distinct (from tyenv_ctor_tyvars_distinct). \<close>
  have tyvars_distinct: "distinct tyvars"
    using CoreTm_VariantCtor.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast

  \<comment> \<open>payloadTy's type variables are within set tyvars. \<close>
  have payload_wk: "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
    using CoreTm_VariantCtor.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  have payload_tyvars: "type_tyvars payloadTy \<subseteq> set tyvars"
    using is_well_kinded_type_tyvars_subset[OF payload_wk]
    by (simp add: fset_of_list.rep_eq)

  \<comment> \<open>Substitution composition for the payload. \<close>
  have payload_compose:
    "apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)
       = apply_subst (fmap_of_list (zip tyvars ?subst_tyArgs)) payloadTy"
    using apply_subst_compose_zip[OF len_eq[symmetric] payload_tyvars tyvars_distinct, of subst]
    by simp

  have payload_subst_compose:
    "core_term_type ?be ghost (apply_subst_to_term subst payload)
       = Some (apply_subst (fmap_of_list (zip tyvars ?subst_tyArgs)) payloadTy)"
    using payload_subst payload_compose by simp

  have len_eq_subst: "length ?subst_tyArgs = length tyvars" using len_eq by simp

  show ?case
    using ctor_lookup_subst tyArgs_wk_subst tyArgs_rt_subst ng_dt_subst
          payload_subst_compose len_eq_subst ty_eq by simp
next
  case (CoreTm_Record flds)
  \<comment> \<open>Record: each field typechecks; result is a Record type of the field types.
      After substitution, each field's result type is substituted. \<close>
  from CoreTm_Record.prems(1) obtain fieldTys where
    distinct_names: "distinct (map fst flds)" and
    flds_typed: "those (map (\<lambda>(name, tm). core_term_type calleeEnv ghost tm) flds)
                   = Some fieldTys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) fieldTys)"
    by (auto split: option.splits if_splits)

  \<comment> \<open>The IH for CoreTm_Record is per-field: for any pair (n, t) in flds and any
      type ty', if t typechecks to ty', then the substituted t typechecks to the
      substituted ty'. We extract a uniform IH and then induct on flds. \<close>
  have field_IH:
    "\<And>fld ty'. fld \<in> set flds \<Longrightarrow>
       core_term_type calleeEnv ghost (snd fld) = Some ty' \<Longrightarrow>
       core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                      (apply_subst_to_term subst (snd fld))
         = Some (apply_subst subst ty')"
    using CoreTm_Record.IH CoreTm_Record.prems(2,3,4,5,6)
    by (auto simp: snds.simps)

  have len_tys: "length fieldTys = length flds"
    using flds_typed by (induction flds arbitrary: fieldTys) (auto split: option.splits)

  have fields_subst:
    "those (map (\<lambda>(name, tm). core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                                              ghost tm)
                (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds))
       = Some (map (apply_subst subst) fieldTys)"
  using flds_typed field_IH
  proof (induction flds arbitrary: fieldTys)
    case Nil
    then show ?case by simp
  next
    case (Cons fld flds')
    obtain name tm where fld_eq: "fld = (name, tm)" by (cases fld)
    from Cons.prems(1) fld_eq obtain hty rest where
      hd_typed: "core_term_type calleeEnv ghost tm = Some hty" and
      rest_typed: "those (map (\<lambda>(n, t). core_term_type calleeEnv ghost t) flds') = Some rest" and
      fieldTys_eq: "fieldTys = hty # rest"
      by (auto split: option.splits)
    from Cons.prems(2)[of fld hty] fld_eq hd_typed
    have hd_subst:
      "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                      (apply_subst_to_term subst tm)
         = Some (apply_subst subst hty)"
      by simp
    have rest_IH:
      "\<And>fld' ty''. fld' \<in> set flds' \<Longrightarrow>
         core_term_type calleeEnv ghost (snd fld') = Some ty'' \<Longrightarrow>
         core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                        (apply_subst_to_term subst (snd fld'))
           = Some (apply_subst subst ty'')"
      using Cons.prems(2) by auto
    from Cons.IH[OF rest_typed rest_IH]
    have rest_subst:
      "those (map (\<lambda>(name, tm). core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv)
                                                ghost tm)
                  (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds'))
         = Some (map (apply_subst subst) rest)" .
    show ?case
      using hd_subst rest_subst fld_eq fieldTys_eq by simp
  qed

  have zip_eq:
    "zip (map fst (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds))
         (map (apply_subst subst) fieldTys)
     = map (\<lambda>(n, t). (n, apply_subst subst t)) (zip (map fst flds) fieldTys)"
    using len_tys by (induction flds fieldTys rule: list_induct2') auto

  have distinct_names_subst:
    "distinct (map fst (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds))"
    using distinct_names by (simp add: comp_def case_prod_beta)
  show ?case
    using fields_subst ty_eq zip_eq distinct_names_subst by simp
next
  case (CoreTm_RecordProj tm fldName)
  \<comment> \<open>RecordProj: inner term has type CoreTy_Record fieldTypes; result is
      the field's type. After substitution, the inner is a Record of substituted
      fields; looking up the field in the substituted list gives the substituted
      type. \<close>
  from CoreTm_RecordProj.prems(1) obtain fieldTypes where
    inner_typed: "core_term_type calleeEnv ghost tm = Some (CoreTy_Record fieldTypes)" and
    fld_lookup: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)
  from CoreTm_RecordProj.IH[OF inner_typed CoreTm_RecordProj.prems(2,3,4,5,6)]
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst tm)
       = Some (CoreTy_Record (map (\<lambda>(n, t). (n, apply_subst subst t)) fieldTypes))"
    by simp
  have fld_lookup_subst:
    "map_of (map (\<lambda>(n, t). (n, apply_subst subst t)) fieldTypes) fldName
       = Some (apply_subst subst ty)"
    using fld_lookup by (induction fieldTypes) auto
  show ?case
    using inner_subst fld_lookup_subst by simp
next
  case (CoreTm_ArrayProj arr idxTms)
  \<comment> \<open>ArrayProj: inner is Array elemTy dims; idxTms are u64; result is elemTy.
      After substitution, inner is Array (substituted elemTy) dims; result is
      substituted elemTy. \<close>
  from CoreTm_ArrayProj.prems(1) obtain elemTy dims where
    inner_typed: "core_term_type calleeEnv ghost arr = Some (CoreTy_Array elemTy dims)" and
    len_ok: "length idxTms = length dims" and
    idxs_typed: "list_all (\<lambda>tm. core_term_type calleeEnv ghost tm
                          = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_ArrayProj.IH(1)[OF inner_typed CoreTm_ArrayProj.prems(2,3,4,5,6)]
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst arr)
       = Some (CoreTy_Array (apply_subst subst elemTy) dims)"
    by simp
  \<comment> \<open>Each index term still typechecks to u64 after substitution (u64 is closed). \<close>
  have idxs_subst:
    "list_all (\<lambda>tm. core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost tm
                      = Some (CoreTy_FiniteInt Unsigned IntBits_64))
              (map (apply_subst_to_term subst) idxTms)"
  proof (unfold list_all_iff, intro ballI)
    fix tm' assume "tm' \<in> set (map (apply_subst_to_term subst) idxTms)"
    then obtain tm where tm_in: "tm \<in> set idxTms" and tm'_eq: "tm' = apply_subst_to_term subst tm"
      by auto
    from idxs_typed tm_in have
      tm_typed: "core_term_type calleeEnv ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      by (simp add: list_all_iff)
    from CoreTm_ArrayProj.IH(2)[OF tm_in tm_typed CoreTm_ArrayProj.prems(2,3,4,5,6)]
    show "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost tm'
            = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
      using tm'_eq by simp
  qed
  show ?case
    using inner_subst idxs_subst len_ok ty_eq by simp
next
  case (CoreTm_VariantProj tm ctorName)
  \<comment> \<open>VariantProj: inner term has type Datatype dtName tyArgs; looks up the
      constructor in TE_DataCtors (inherited from calleeEnv); result is the
      substituted payload type (substituting tyvars := tyArgs).

      After outer substitution: inner becomes Datatype dtName (map substitution
      tyArgs). The DataCtors lookup is unchanged (env field inherited). The
      result of the *outer* substitution on the original result type equals the
      inner substitution on the *substituted* tyArgs: this is substitution
      composition / commutativity. \<close>
  from CoreTm_VariantProj.prems(1) obtain dtName tyArgs tyvars payloadTy where
    inner_typed: "core_term_type calleeEnv ghost tm = Some (CoreTy_Datatype dtName tyArgs)" and
    ctor_lookup: "fmlookup (TE_DataCtors calleeEnv) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    by (auto split: option.splits CoreType.splits if_splits prod.splits)
  from CoreTm_VariantProj.IH[OF inner_typed CoreTm_VariantProj.prems(2,3,4,5,6)]
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst tm)
       = Some (CoreTy_Datatype dtName (map (apply_subst subst) tyArgs))"
    by simp
  have ctor_lookup_subst:
    "fmlookup (TE_DataCtors (apply_subst_to_callee_env subst callerEnv calleeEnv)) ctorName
       = Some (dtName, tyvars, payloadTy)"
    using ctor_lookup by simp
  have len_eq_subst: "length (map (apply_subst subst) tyArgs) = length tyvars"
    using len_eq by simp

  \<comment> \<open>tyvars are distinct (from tyenv_ctor_tyvars_distinct, a wf clause). \<close>
  have tyvars_distinct: "distinct tyvars"
    using CoreTm_VariantProj.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast

  \<comment> \<open>payloadTy's type variables are within set tyvars (from tyenv_payloads_well_kinded
      via is_well_kinded_type_tyvars_subset). \<close>
  have payload_wk: "is_well_kinded (calleeEnv \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
    using CoreTm_VariantProj.prems(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  have payload_tyvars: "type_tyvars payloadTy \<subseteq> set tyvars"
    using is_well_kinded_type_tyvars_subset[OF payload_wk]
    by (simp add: fset_of_list.rep_eq)

  \<comment> \<open>Substitution composition: pushing the outer subst through the inner zip
      substitution gives the same result as composing them. \<close>
  have ty_subst_eq:
    "apply_subst subst ty
       = apply_subst (fmap_of_list (zip tyvars (map (apply_subst subst) tyArgs))) payloadTy"
    unfolding ty_eq
    using apply_subst_compose_zip[OF len_eq[symmetric] payload_tyvars tyvars_distinct, of subst]
    by simp

  show ?case
    using inner_subst ctor_lookup_subst len_eq_subst ty_subst_eq by simp
next
  case (CoreTm_Match scrut arms)
  \<comment> \<open>Match: scrutinee typechecks; pattern compatibility / regularity hold;
      all arm bodies have the same type. After substitution, the scrutinee's
      type is substituted, the patterns are unchanged (substitution doesn't touch
      them), and each arm body's IH gives the substituted body type. \<close>
  from CoreTm_Match.prems(1) obtain scrutTy where
    scrut_typed: "core_term_type calleeEnv ghost scrut = Some scrutTy" and
    arms_nonempty: "arms \<noteq> []" and
    pats_compat: "list_all (\<lambda>p. pattern_compatible calleeEnv p scrutTy) (map fst arms)" and
    pats_regular: "patterns_regular (map fst arms)" and
    hd_typed: "core_term_type calleeEnv ghost (snd (hd arms)) = Some ty" and
    rest_typed: "list_all (\<lambda>body. core_term_type calleeEnv ghost body = Some ty)
                          (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)

  let ?be = "apply_subst_to_callee_env subst callerEnv calleeEnv"
  let ?subst_arms = "map (\<lambda>(pat, body). (pat, apply_subst_to_term subst body)) arms"

  \<comment> \<open>Scrutinee IH. \<close>
  from CoreTm_Match.IH(1)[OF scrut_typed CoreTm_Match.prems(2,3,4,5,6)]
  have scrut_subst:
    "core_term_type ?be ghost (apply_subst_to_term subst scrut)
       = Some (apply_subst subst scrutTy)" .

  \<comment> \<open>Per-arm IH from the structural induction. The IH gives, for each (pat, body)
      pair in arms, the body's typing-substitution result. \<close>
  have arm_IH:
    "\<And>arm ty'. arm \<in> set arms \<Longrightarrow>
       core_term_type calleeEnv ghost (snd arm) = Some ty' \<Longrightarrow>
       core_term_type ?be ghost (apply_subst_to_term subst (snd arm))
         = Some (apply_subst subst ty')"
    using CoreTm_Match.IH(2) CoreTm_Match.prems(2,3,4,5,6)
    by (auto simp: snds.simps)

  \<comment> \<open>The patterns of arms are unchanged after substitution; we only substitute the bodies. \<close>
  have pats_eq: "map fst ?subst_arms = map fst arms"
    by (induction arms) auto

  \<comment> \<open>Pattern compatibility and regularity both transfer to the substituted
      env / type. \<close>
  have pats_compat_subst:
    "list_all (\<lambda>p. pattern_compatible ?be p (apply_subst subst scrutTy)) (map fst ?subst_arms)"
    using pats_compat pats_eq
    by (induction arms)
       (auto intro: pattern_compatible_apply_subst_callee_env)
  have pats_regular_subst: "patterns_regular (map fst ?subst_arms)"
    using pats_regular pats_eq by metis

  \<comment> \<open>Head body IH. \<close>
  have hd_in: "hd arms \<in> set arms" using arms_nonempty by auto
  from arm_IH[OF hd_in hd_typed]
  have hd_subst:
    "core_term_type ?be ghost (apply_subst_to_term subst (snd (hd arms)))
       = Some (apply_subst subst ty)" .

  \<comment> \<open>Head of the substituted arms equals the substituted head of arms. \<close>
  have hd_subst_arms_eq:
    "snd (hd ?subst_arms) = apply_subst_to_term subst (snd (hd arms))"
    using arms_nonempty by (cases arms) auto

  \<comment> \<open>Tail bodies: each typechecks to apply_subst subst ty after substitution. \<close>
  have tl_subst:
    "list_all (\<lambda>body. core_term_type ?be ghost body = Some (apply_subst subst ty))
              (tl (map snd ?subst_arms))"
  proof -
    \<comment> \<open>tl (map snd ?subst_arms) = map (apply_subst_to_term subst) (tl (map snd arms)) \<close>
    have tl_eq: "tl (map snd ?subst_arms)
                   = map (apply_subst_to_term subst) (tl (map snd arms))"
      using arms_nonempty by (cases arms) auto
    show ?thesis
      unfolding tl_eq
    proof (unfold list_all_iff, intro ballI)
      fix b' assume "b' \<in> set (map (apply_subst_to_term subst) (tl (map snd arms)))"
      then obtain b where
        b_in: "b \<in> set (tl (map snd arms))" and
        b'_eq: "b' = apply_subst_to_term subst b"
        by auto
      from b_in have b_typed: "core_term_type calleeEnv ghost b = Some ty"
        using rest_typed by (simp add: list_all_iff)
      \<comment> \<open>b is the body of some arm in arms. \<close>
      from b_in arms_nonempty obtain arm where
        arm_in: "arm \<in> set arms" and arm_body: "snd arm = b"
        by (cases arms) auto
      from arm_IH[OF arm_in] b_typed arm_body
      have "core_term_type ?be ghost (apply_subst_to_term subst b)
              = Some (apply_subst subst ty)"
        by simp
      thus "core_term_type ?be ghost b' = Some (apply_subst subst ty)"
        using b'_eq by simp
    qed
  qed

  have arms_nonempty_subst: "?subst_arms \<noteq> []"
    using arms_nonempty by (cases arms) auto

  show ?case
    using scrut_subst arms_nonempty_subst pats_compat_subst pats_regular_subst
          hd_subst hd_subst_arms_eq tl_subst
    by (auto simp: Let_def)
next
  case (CoreTm_Sizeof tm)
  \<comment> \<open>Sizeof requires the inner term to have an Array type and returns sizeof_type
      of its dims. apply_subst preserves the dims of an Array, and sizeof_type
      produces a closed type. is_lvalue is a syntactic property preserved by
      apply_subst_to_term. \<close>
  from CoreTm_Sizeof.prems(1) obtain elemTy dims where
    inner: "core_term_type calleeEnv ghost tm = Some (CoreTy_Array elemTy dims)" and
    cond_ok: "\<not> (list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue tm \<and> ghost = NotGhost)" and
    ty_eq: "ty = sizeof_type dims"
    by (auto split: CoreType.splits option.splits if_splits)
  from CoreTm_Sizeof.IH[OF inner CoreTm_Sizeof.prems(2,3,4,5,6)]
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                    (apply_subst_to_term subst tm)
       = Some (CoreTy_Array (apply_subst subst elemTy) dims)" by simp
  have lvalue_eq: "is_lvalue (apply_subst_to_term subst tm) = is_lvalue tm" by simp
  show ?case using inner_subst cond_ok ty_eq lvalue_eq by simp
next
  case (CoreTm_Allocated tm)
  \<comment> \<open>Allocated is ghost-only and always returns Bool. The NotGhost equation reduces
      to None, so we must be in Ghost. The inner term must typecheck to something. \<close>
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Allocated.prems(1) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Allocated.prems(1) obtain innerTy where
      inner: "core_term_type calleeEnv Ghost tm = Some innerTy" and
      ty_eq: "ty = CoreTy_Bool"
      by (auto split: option.splits)
    from CoreTm_Allocated.IH[OF inner CoreTm_Allocated.prems(2,3,4)]
         CoreTm_Allocated.prems(5) CoreTm_Allocated.prems(6)
    have "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) Ghost
                          (apply_subst_to_term subst tm)
            = Some (apply_subst subst innerTy)" by simp
    with Ghost ty_eq show ?thesis by simp
  qed
next
  case (CoreTm_Old tm)
  \<comment> \<open>Old is a ghost-only pass-through. The NotGhost equation reduces to None,
      so the precondition forces ghost = Ghost. The IH on tm closes the case. \<close>
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Old.prems(1) show ?thesis by simp
  next
    case Ghost
    with CoreTm_Old.prems(1) have inner: "core_term_type calleeEnv Ghost tm = Some ty" by simp
    from CoreTm_Old.IH[OF inner CoreTm_Old.prems(2,3,4)]
         CoreTm_Old.prems(5) CoreTm_Old.prems(6)
    have "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) Ghost
                          (apply_subst_to_term subst tm)
            = Some (apply_subst subst ty)" by simp
    with Ghost show ?thesis by simp
  qed
qed


(* If a term has type ty, then apply_subst_to_term subst tm has type
   (apply_subst subst ty), under the following conditions:

   - The environment is well-formed.
   - The substitution range is well-kinded in env (and runtime in NotGhost mode), so
     that types introduced by the substitution remain well-kinded.
   - The substitution does not affect any local variable's type and does not
     affect the return type. Without this, the lemma is false: for
     `CoreTm_Var name` whose env type is `T`, the result type is the env's `T`
     unchanged, not `apply_subst subst T`. Globals are closed (by the well-kinded
     clause of tyenv_well_formed) so are unaffected by any substitution and need
     no precondition.

     Elaborator clients can typically discharge this from their freshness
     invariant: fresh type variables in the substitution's domain don't appear in any
     pre-existing local-var type or return type.

   This lemma is a corollary of core_term_type_subst_callee_env: under these
   conditions, apply_subst_to_callee_env subst env env = env. *)
lemma apply_subst_to_term_preserves_typing:
  assumes typed: "core_term_type env mode tm = Some ty"
      and wf: "tyenv_well_formed env"
      and subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and subst_rt: "mode = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type env ty')"
      and locals_unaffected:
        "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty'
                      \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType env) = TE_ReturnType env"
  shows "core_term_type env mode (apply_subst_to_term subst tm) = Some (apply_subst subst ty)"
proof -
  \<comment> \<open>fmmap is the identity on TE_LocalVars (each entry's type is unchanged
      under the substitution). \<close>
  have locals_id: "fmmap (apply_subst subst) (TE_LocalVars env) = TE_LocalVars env"
    by (meson fmap.map_ident_strong fmran'E locals_unaffected)

  \<comment> \<open>(i) The substituted callee env equals env. \<close>
  have env_subst_id: "apply_subst_to_callee_env subst env env = env"
    unfolding apply_subst_to_callee_env_def
    by (simp add: locals_id ret_unaffected)

  \<comment> \<open>(ii) callee_env_subst_ok holds. The global field equalities are reflexive.
      For the TE_TypeVars condition: any tyvar in scope, if it's mapped by the
      substitution, the result is well-kinded in env (from subst_wk). If it's
      not mapped, it remains in scope. \<close>
  have ok: "callee_env_subst_ok subst env env"
    unfolding callee_env_subst_ok_def
  proof (intro conjI)
    show "TE_GlobalVars env = TE_GlobalVars env"
      "TE_GhostGlobals env = TE_GhostGlobals env"
      "TE_Functions env = TE_Functions env"
      "TE_Datatypes env = TE_Datatypes env"
      "TE_DataCtors env = TE_DataCtors env"
      "TE_DataCtorsByType env = TE_DataCtorsByType env"
      "TE_GhostDatatypes env = TE_GhostDatatypes env"
      by simp_all
  next
    show "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow>
              (case fmlookup subst n of
                 Some ty' \<Rightarrow> is_well_kinded env ty'
               | None \<Rightarrow> n |\<in>| TE_TypeVars env)"
      using subst_wk by (auto split: option.splits intro: fmran'I)
  qed

  \<comment> \<open>(iii) callee_env_subst_runtime_ok holds in NotGhost mode. \<close>
  have ok_rt: "mode = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst env env"
  proof
    assume ng: "mode = NotGhost"
    with subst_rt have rt: "\<forall>ty' \<in> fmran' subst. is_runtime_type env ty'" by simp
    show "callee_env_subst_runtime_ok subst env env"
      unfolding callee_env_subst_runtime_ok_def
      using rt by (auto split: option.splits intro: fmran'I)
  qed

  from core_term_type_subst_callee_env[OF typed wf ok subst_wk subst_rt ok_rt]
  show ?thesis using env_subst_id by simp
qed


(* Companion to function_call_subst_setup: for a single FI_TmArgs entry, the
   "typecheck then compose" step. Given that an argument typechecks to
   `apply_subst innerSubst ti`, the substituted argument typechecks under the
   substituted env to `apply_subst subst_innerSubst ti`. Lives here (after
   core_term_type_subst_callee_env) because it depends on that lemma. *)
lemma fun_arg_subst_typecheck:
  assumes typed: "core_term_type calleeEnv ghost tm
                    = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti)"
      and ti_tyvars: "type_tyvars ti \<subseteq> set (FI_TyArgs funInfo)"
      and tyArgs_distinct: "distinct (FI_TyArgs funInfo)"
      and len_tyArgs: "length tyArgs = length (FI_TyArgs funInfo)"
      and wf: "tyenv_well_formed calleeEnv"
      and ok: "callee_env_subst_ok subst callerEnv calleeEnv"
      and subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded callerEnv ty'"
      and subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
      and ok_rt: "ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv"
  shows "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                        (apply_subst_to_term subst tm)
           = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst subst) tyArgs))) ti)"
proof -
  from core_term_type_subst_callee_env[OF typed wf ok subst_wk subst_rt ok_rt]
  have "core_term_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                       (apply_subst_to_term subst tm)
          = Some (apply_subst subst
                    (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti))" .
  moreover have
    "apply_subst subst (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ti)
       = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst subst) tyArgs))) ti"
    using apply_subst_compose_zip[OF len_tyArgs[symmetric] ti_tyvars tyArgs_distinct, of subst]
    by simp
  ultimately show ?thesis by simp
qed


(* ========================================================================== *)
(* Impure call typing under callee-env substitution                            *)
(* ========================================================================== *)

(* Mirror of core_term_type_subst_callee_env for core_impure_call_type.
   Only the CoreTm_FunctionCall case is non-trivial; every other term shape
   makes core_impure_call_type return None, so the hypothesis is unsatisfiable.

   The proof closely mirrors the FunctionCall case of core_term_type_subst_callee_env,
   except that:
     - argument list_all2 discriminates on Var vs Ref;
     - for Var args we use the inner term lemma (via
       core_term_type_subst_callee_env);
     - for Ref args the term is a writable lvalue, which is a syntactic property
       preserved by substitution, and the inner core_term_type check is handled
       the same way. *)
lemma core_impure_call_type_subst_callee_env:
  assumes "core_impure_call_type calleeEnv ghost tm = Some ty"
      and "tyenv_well_formed calleeEnv"
      and "callee_env_subst_ok subst callerEnv calleeEnv"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded callerEnv ty'"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
      and "ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv"
  shows "core_impure_call_type (apply_subst_to_callee_env subst callerEnv calleeEnv) ghost
                               (apply_subst_to_term subst tm)
           = Some (apply_subst subst ty)"
proof -
  \<comment> \<open>tm must be a function-call term; otherwise core_impure_call_type is None. \<close>
  from assms(1) obtain fnName tyArgs tmArgs where
    tm_eq: "tm = CoreTm_FunctionCall fnName tyArgs tmArgs"
    unfolding core_impure_call_type_def
    by (cases tm) (auto split: option.splits if_splits)

  \<comment> \<open>Read all the successful-path conditions off the unfolded definition. We
      do this in two stages: (a) the top-level if-ladder, which simp can drive
      without inspecting the inner case on Var/Ref; (b) the list_all2 body,
      which we extract as an opaque fact (cong-friendly simp avoids rewriting
      the Var/Ref branches). \<close>
  from assms(1) tm_eq have impure_unfolded:
    "(case fmlookup (TE_Functions calleeEnv) fnName of
        None \<Rightarrow> None
      | Some funInfo \<Rightarrow>
          if length tyArgs \<noteq> length (FI_TyArgs funInfo) then None
          else if \<not> list_all (is_well_kinded calleeEnv) tyArgs then None
          else if ghost = NotGhost
                  \<and> (\<not> list_all (is_runtime_type calleeEnv) tyArgs
                     \<or> FI_Ghost funInfo = Ghost) then None
          else if length tmArgs \<noteq> length (FI_TmArgs funInfo) then None
          else
            let tySubst = fmap_of_list (zip (FI_TyArgs funInfo) tyArgs);
                expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo);
                varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)
            in if list_all2 (\<lambda>(tm, vor) expectedTy.
                     case vor of
                       Var \<Rightarrow>
                         (case core_term_type calleeEnv ghost tm of
                            None \<Rightarrow> False
                          | Some actualTy \<Rightarrow> actualTy = expectedTy)
                     | Ref \<Rightarrow>
                         is_writable_lvalue calleeEnv tm
                         \<and> core_term_type calleeEnv ghost tm = Some expectedTy)
                   (zip tmArgs varOrRefs) expectedArgTypes
               then Some (apply_subst tySubst (FI_ReturnType funInfo))
               else None) = Some ty"
    unfolding core_impure_call_type_def by simp

  from impure_unfolded obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions calleeEnv) fnName = Some funInfo"
    by (cases "fmlookup (TE_Functions calleeEnv) fnName") auto

  from impure_unfolded fn_lookup have body_eq:
    "(if length tyArgs \<noteq> length (FI_TyArgs funInfo) then None
      else if \<not> list_all (is_well_kinded calleeEnv) tyArgs then None
      else if ghost = NotGhost
              \<and> (\<not> list_all (is_runtime_type calleeEnv) tyArgs
                 \<or> FI_Ghost funInfo = Ghost) then None
      else if length tmArgs \<noteq> length (FI_TmArgs funInfo) then None
      else
        let tySubst = fmap_of_list (zip (FI_TyArgs funInfo) tyArgs);
            expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo);
            varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)
        in if list_all2 (\<lambda>(tm, vor) expectedTy.
                 case vor of
                   Var \<Rightarrow>
                     (case core_term_type calleeEnv ghost tm of
                        None \<Rightarrow> False
                      | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 | Ref \<Rightarrow>
                     is_writable_lvalue calleeEnv tm
                     \<and> core_term_type calleeEnv ghost tm = Some expectedTy)
               (zip tmArgs varOrRefs) expectedArgTypes
           then Some (apply_subst tySubst (FI_ReturnType funInfo))
           else None) = Some ty"
    by simp

  from body_eq have len_tyArgs: "length tyArgs = length (FI_TyArgs funInfo)"
    by (metis option.distinct(1))
  from body_eq len_tyArgs have tyArgs_wk: "list_all (is_well_kinded calleeEnv) tyArgs"
    by (metis option.distinct(1))
  from body_eq len_tyArgs tyArgs_wk have not_ghost_cond:
    "\<not> (ghost = NotGhost
        \<and> (\<not> list_all (is_runtime_type calleeEnv) tyArgs
           \<or> FI_Ghost funInfo = Ghost))"
    by (metis option.distinct(1))
  from body_eq len_tyArgs tyArgs_wk not_ghost_cond have len_tmArgs:
    "length tmArgs = length (FI_TmArgs funInfo)"
    by (metis option.distinct(1))
  from body_eq len_tyArgs tyArgs_wk not_ghost_cond len_tmArgs
  have after_ifs:
    "(let tySubst = fmap_of_list (zip (FI_TyArgs funInfo) tyArgs);
          expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo);
          varOrRefs = map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)
      in if list_all2 (\<lambda>(tm, vor) expectedTy.
               case vor of
                 Var \<Rightarrow>
                   (case core_term_type calleeEnv ghost tm of
                      None \<Rightarrow> False
                    | Some actualTy \<Rightarrow> actualTy = expectedTy)
               | Ref \<Rightarrow>
                   is_writable_lvalue calleeEnv tm
                   \<and> core_term_type calleeEnv ghost tm = Some expectedTy)
             (zip tmArgs varOrRefs) expectedArgTypes
         then Some (apply_subst tySubst (FI_ReturnType funInfo))
         else None) = Some ty"
    by argo
  from after_ifs have args_check:
    "list_all2 (\<lambda>(tm, vor) expectedTy.
                  case vor of
                    Var \<Rightarrow>
                      (case core_term_type calleeEnv ghost tm of
                         None \<Rightarrow> False
                       | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  | Ref \<Rightarrow>
                      is_writable_lvalue calleeEnv tm
                      \<and> core_term_type calleeEnv ghost tm = Some expectedTy)
               (zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)))
               (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                    (FI_TmArgs funInfo))"
    by (simp add: Let_def split: if_splits)
  from after_ifs have ty_eq:
    "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    by (simp add: Let_def split: if_splits)
  have ng_tyArgs: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type calleeEnv) tyArgs"
    using not_ghost_cond by blast
  have ng_fn: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    using not_ghost_cond by blast

  let ?be = "apply_subst_to_callee_env subst callerEnv calleeEnv"
  let ?subst_tyArgs = "map (apply_subst subst) tyArgs"
  let ?innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?subst_innerSubst = "fmap_of_list (zip (FI_TyArgs funInfo) ?subst_tyArgs)"

  note call_setup = function_call_subst_setup[OF fn_lookup len_tyArgs tyArgs_wk ng_tyArgs assms(2,3,4,6)]
  note fn_lookup_subst   = call_setup(1)
  note tyArgs_wk_subst   = call_setup(2)
  note tyArgs_rt_subst   = call_setup(3)
  note len_tyArgs_subst  = call_setup(4)
  note tyArgs_distinct   = call_setup(5)
  note fi_args_tyvars    = call_setup(6)
  note fi_ret_tyvars     = call_setup(7)
  note ret_compose       = call_setup(8)

  have len_tmArgs_eq: "length tmArgs = length (FI_TmArgs funInfo)" using len_tmArgs .

  \<comment> \<open>For each argument index, the argument typechecks under the substituted
      environment, respecting its Var/Ref mode. \<close>
  have args_check_subst:
    "list_all2 (\<lambda>(tm, vor) expectedTy.
                  (case vor of
                     Var \<Rightarrow>
                       (case core_term_type ?be ghost tm of
                          None \<Rightarrow> False
                        | Some actualTy \<Rightarrow> actualTy = expectedTy)
                   | Ref \<Rightarrow>
                       is_writable_lvalue ?be tm
                       \<and> core_term_type ?be ghost tm = Some expectedTy))
              (zip (map (apply_subst_to_term subst) tmArgs)
                   (map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)))
              (map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty) (FI_TmArgs funInfo))"
  proof (rule list_all2_all_nthI)
    show "length (zip (map (apply_subst_to_term subst) tmArgs)
                      (map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)))
            = length (map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty) (FI_TmArgs funInfo))"
      using len_tmArgs by simp
  next
    fix i
    assume i_bound: "i < length (zip (map (apply_subst_to_term subst) tmArgs)
                                     (map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)))"
    hence i_bound': "i < length tmArgs" using len_tmArgs by simp
    hence i_bound_args: "i < length (FI_TmArgs funInfo)" using len_tmArgs by simp

    obtain n ti vor where fi_arg_eq: "FI_TmArgs funInfo ! i = (n, ti, vor)"
      by (cases "FI_TmArgs funInfo ! i") auto
    have ti_in: "ti \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
      using i_bound_args fi_arg_eq
      by (force simp: image_iff in_set_conv_nth)
    with fi_args_tyvars have ti_tyvars: "type_tyvars ti \<subseteq> set (FI_TyArgs funInfo)" by blast

    have subst_expected_nth:
      "(map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty) (FI_TmArgs funInfo)) ! i
          = apply_subst ?subst_innerSubst ti"
      using fi_arg_eq i_bound_args by simp

    have zip_nth_orig:
      "zip tmArgs (map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)) ! i
         = (tmArgs ! i, vor)"
      using i_bound' i_bound_args len_tmArgs fi_arg_eq by simp
    have expected_nth:
      "(map (\<lambda>(_, ty, _). apply_subst ?innerSubst ty) (FI_TmArgs funInfo)) ! i
          = apply_subst ?innerSubst ti"
      using fi_arg_eq i_bound_args by simp

    \<comment> \<open>Pull out the i-th entry of args_check as a fully instantiated fact. \<close>
    have nth_check:
      "(case vor of
          Var \<Rightarrow>
            (case core_term_type calleeEnv ghost (tmArgs ! i) of
               None \<Rightarrow> False
             | Some actualTy \<Rightarrow> actualTy = apply_subst ?innerSubst ti)
        | Ref \<Rightarrow>
            is_writable_lvalue calleeEnv (tmArgs ! i)
            \<and> core_term_type calleeEnv ghost (tmArgs ! i) = Some (apply_subst ?innerSubst ti))"
      using list_all2_nthD2[OF args_check, of i] i_bound' len_tmArgs
            zip_nth_orig expected_nth
      by simp

    have zip_nth:
      "zip (map (apply_subst_to_term subst) tmArgs)
           (map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)) ! i
         = (apply_subst_to_term subst (tmArgs ! i), vor)"
      using i_bound' i_bound_args len_tmArgs fi_arg_eq by simp

    have arg_check_subst_i:
      "(case vor of
          Var \<Rightarrow>
            (case core_term_type ?be ghost (apply_subst_to_term subst (tmArgs ! i)) of
               None \<Rightarrow> False
             | Some actualTy \<Rightarrow> actualTy = apply_subst ?subst_innerSubst ti)
        | Ref \<Rightarrow>
            is_writable_lvalue ?be (apply_subst_to_term subst (tmArgs ! i))
            \<and> core_term_type ?be ghost (apply_subst_to_term subst (tmArgs ! i))
                = Some (apply_subst ?subst_innerSubst ti))"
    proof (cases vor)
      case Var
      from nth_check Var have
        typed: "core_term_type calleeEnv ghost (tmArgs ! i) = Some (apply_subst ?innerSubst ti)"
        by (auto split: option.splits)
      from fun_arg_subst_typecheck[OF typed ti_tyvars tyArgs_distinct len_tyArgs assms(2,3,4,5,6)]
      have "core_term_type ?be ghost (apply_subst_to_term subst (tmArgs ! i))
              = Some (apply_subst ?subst_innerSubst ti)" .
      with Var show ?thesis by simp
    next
      case Ref
      from nth_check Ref have
        writable: "is_writable_lvalue calleeEnv (tmArgs ! i)" and
        typed: "core_term_type calleeEnv ghost (tmArgs ! i) = Some (apply_subst ?innerSubst ti)"
        by auto
      from fun_arg_subst_typecheck[OF typed ti_tyvars tyArgs_distinct len_tyArgs assms(2,3,4,5,6)]
      have "core_term_type ?be ghost (apply_subst_to_term subst (tmArgs ! i))
              = Some (apply_subst ?subst_innerSubst ti)" .
      moreover from writable
      have "is_writable_lvalue ?be (apply_subst_to_term subst (tmArgs ! i))" by simp
      ultimately show ?thesis using Ref by simp
    qed

    show "(\<lambda>(tm, vor) expectedTy.
             case vor of
               Var \<Rightarrow>
                 (case core_term_type ?be ghost tm of
                    None \<Rightarrow> False
                  | Some actualTy \<Rightarrow> actualTy = expectedTy)
             | Ref \<Rightarrow>
                 is_writable_lvalue ?be tm
                 \<and> core_term_type ?be ghost tm = Some expectedTy)
            (zip (map (apply_subst_to_term subst) tmArgs)
                 (map (\<lambda>(_, _, vor). vor) (FI_TmArgs funInfo)) ! i)
            ((map (\<lambda>(_, ty, _). apply_subst ?subst_innerSubst ty) (FI_TmArgs funInfo)) ! i)"
      using arg_check_subst_i zip_nth subst_expected_nth by simp
  qed

  show ?thesis
    unfolding tm_eq apply_subst_to_term.simps core_impure_call_type_def
    using fn_lookup_subst len_tyArgs_subst tyArgs_wk_subst tyArgs_rt_subst ng_fn
          len_tmArgs_eq args_check_subst ty_eq ret_compose
    by (auto simp: Let_def)
qed


(* ========================================================================== *)
(* Statement typing under callee-env substitution                              *)
(* ========================================================================== *)

(* The statement-level analogue, for both individual statements and statement
   lists. This is what case 6 uses to discharge body_typed_ex: given that the
   body typechecks in body_env_for callerEnv funInfo, conclude that it
   typechecks in the substituted env.

   Mutual induction is required because Assert (and While/Match if/when their
   typechecking is implemented) recurses into nested statement lists.

   Several statement forms (Fix, Obtain, Use, While, Match, VarDecl Ref) have
   `undefined` typechecking and are TODO. Those cases are sorry'd here; they
   cannot be proved as long as their typechecker bodies are `undefined`. *)
lemma core_statement_type_and_list_subst_callee_env:
  "\<lbrakk> core_statement_type calleeEnv mode stmt = Some calleeEnv';
     tyenv_well_formed calleeEnv;
     callee_env_subst_ok subst callerEnv calleeEnv;
     \<forall>ty' \<in> fmran' subst. is_well_kinded callerEnv ty';
     mode = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty');
     mode = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv \<rbrakk>
   \<Longrightarrow> core_statement_type
         (apply_subst_to_callee_env subst callerEnv calleeEnv) mode
         (apply_subst_to_stmt subst stmt)
       = Some (apply_subst_to_callee_env subst callerEnv calleeEnv')"
  "\<lbrakk> core_statement_list_type calleeEnv mode stmts = Some calleeEnv';
     tyenv_well_formed calleeEnv;
     callee_env_subst_ok subst callerEnv calleeEnv;
     \<forall>ty' \<in> fmran' subst. is_well_kinded callerEnv ty';
     mode = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty');
     mode = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv calleeEnv \<rbrakk>
   \<Longrightarrow> core_statement_list_type
         (apply_subst_to_callee_env subst callerEnv calleeEnv) mode
         (apply_subst_to_stmt_list subst stmts)
       = Some (apply_subst_to_callee_env subst callerEnv calleeEnv')"
proof (induction stmt and stmts
       arbitrary: calleeEnv' callerEnv subst
              and calleeEnv' callerEnv subst
       rule: core_statement_type_core_statement_list_type.induct)
  case (1 env mode declGhost varName varTy initTm)
  \<comment> \<open>VarDecl Var: declares a new local variable. The result env extends TE_LocalVars
      with (varName, varTy). After substitution, the new local's type is
      apply_subst subst varTy. The substituted result env equals the substituted
      version of the original result env (since both add the same substituted entry
      and the env's other fields are inherited). \<close>
  from "1.prems"(1) have
    ghost_ok: "mode = Ghost \<longrightarrow> declGhost = Ghost" and
    varTy_wk: "is_well_kinded env varTy" and
    varTy_rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    init_typed: "core_impure_call_type env declGhost initTm = Some varTy
                 \<or> core_term_type env declGhost initTm = Some varTy" and
    env'_eq: "calleeEnv' = env \<lparr>
        TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
        TE_GhostLocals := (if declGhost = Ghost then finsert varName (TE_GhostLocals env)
                           else fminus (TE_GhostLocals env) {|varName|}),
        TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
    by (auto split: if_splits)

  \<comment> \<open>Substituted varTy is well-kinded in ?be. \<close>
  let ?be = "apply_subst_to_callee_env subst callerEnv env"
  have varTy_wk_subst: "is_well_kinded ?be (apply_subst subst varTy)"
    using apply_subst_preserves_well_kinded_callee[OF varTy_wk "1.prems"(3)] .

  \<comment> \<open>Runtime version (gated on declGhost = NotGhost). When declGhost = NotGhost,
      mode = NotGhost too (by ghost_ok), so the substitution range is runtime. \<close>
  have varTy_rt_subst:
    "declGhost = NotGhost \<longrightarrow> is_runtime_type ?be (apply_subst subst varTy)"
  proof
    assume dg: "declGhost = NotGhost"
    with ghost_ok have mode_ng: "mode = NotGhost" by (cases mode) auto
    from dg varTy_rt have rt: "is_runtime_type env varTy" by simp
    from mode_ng "1.prems"(6) have ok_rt: "callee_env_subst_runtime_ok subst callerEnv env" by simp
    from apply_subst_preserves_runtime_callee[OF rt "1.prems"(3) ok_rt]
    show "is_runtime_type ?be (apply_subst subst varTy)" .
  qed

  \<comment> \<open>The runtime substitution-range conditions for the inner term lemma. \<close>
  have rt_for_declGhost:
    "declGhost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
    using ghost_ok "1.prems"(5) by (cases mode) auto
  have rt_ok_for_declGhost:
    "declGhost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv env"
    using ghost_ok "1.prems"(6) by (cases mode) auto

  \<comment> \<open>Term lemma (or its impure-call variant) applied to initTm. The substituted
      term replaces embedded types. Branch on which of the two alternatives held. \<close>
  have init_subst:
    "core_impure_call_type ?be declGhost (apply_subst_to_term subst initTm)
       = Some (apply_subst subst varTy)
     \<or> core_term_type ?be declGhost (apply_subst_to_term subst initTm)
       = Some (apply_subst subst varTy)"
    using init_typed
  proof
    assume "core_impure_call_type env declGhost initTm = Some varTy"
    from core_impure_call_type_subst_callee_env[OF this "1.prems"(2,3,4) rt_for_declGhost rt_ok_for_declGhost]
    show ?thesis by simp
  next
    assume "core_term_type env declGhost initTm = Some varTy"
    from core_term_type_subst_callee_env[OF this "1.prems"(2,3,4) rt_for_declGhost rt_ok_for_declGhost]
    show ?thesis by simp
  qed

  \<comment> \<open>Putting it together: the substituted result env equals the substituted version
      of the original result env. The TE_GhostLocals and TE_ConstLocals updates are
      preserved by substitution since they only depend on names. \<close>
  have result_env_eq:
    "?be \<lparr> TE_LocalVars := fmupd varName (apply_subst subst varTy) (TE_LocalVars ?be),
           TE_GhostLocals := (if declGhost = Ghost then finsert varName (TE_GhostLocals ?be)
                              else fminus (TE_GhostLocals ?be) {|varName|}),
           TE_ConstLocals := fminus (TE_ConstLocals ?be) {|varName|} \<rparr>
       = apply_subst_to_callee_env subst callerEnv calleeEnv'"
    unfolding env'_eq apply_subst_to_callee_env_def by (simp add: fmmap_fmupd)

  show ?case
    using ghost_ok varTy_wk_subst varTy_rt_subst init_subst result_env_eq
    by simp
next
  case (2 env mode declGhost varName varTy initTm)
  \<comment> \<open>VarDecl Ref: declares a new local ref. The result env extends TE_LocalVars
      with (varName, varTy), and adds varName to TE_ConstLocals iff initTm is not
      a writable lvalue (i.e. its base is read-only). Substitution preserves
      is_lvalue, is_writable_lvalue, and the result env shape, mirroring case 1. \<close>
  from "2.prems"(1) have
    ghost_ok: "mode = Ghost \<longrightarrow> declGhost = Ghost" and
    varTy_wk: "is_well_kinded env varTy" and
    varTy_rt: "declGhost = NotGhost \<longrightarrow> is_runtime_type env varTy" and
    init_lvalue: "is_lvalue initTm" and
    init_typed: "core_term_type env declGhost initTm = Some varTy" and
    env'_eq: "calleeEnv' = env \<lparr>
        TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
        TE_GhostLocals := (if declGhost = Ghost then finsert varName (TE_GhostLocals env)
                           else fminus (TE_GhostLocals env) {|varName|}),
        TE_ConstLocals := (if is_writable_lvalue env initTm
                          then fminus (TE_ConstLocals env) {|varName|}
                          else finsert varName (TE_ConstLocals env)) \<rparr>"
    by (auto split: if_splits)

  let ?be = "apply_subst_to_callee_env subst callerEnv env"
  have varTy_wk_subst: "is_well_kinded ?be (apply_subst subst varTy)"
    using apply_subst_preserves_well_kinded_callee[OF varTy_wk "2.prems"(3)] .

  have varTy_rt_subst:
    "declGhost = NotGhost \<longrightarrow> is_runtime_type ?be (apply_subst subst varTy)"
  proof
    assume dg: "declGhost = NotGhost"
    with ghost_ok have mode_ng: "mode = NotGhost" by (cases mode) auto
    from dg varTy_rt have rt: "is_runtime_type env varTy" by simp
    from mode_ng "2.prems"(6) have ok_rt: "callee_env_subst_runtime_ok subst callerEnv env" by simp
    from apply_subst_preserves_runtime_callee[OF rt "2.prems"(3) ok_rt]
    show "is_runtime_type ?be (apply_subst subst varTy)" .
  qed

  have rt_for_declGhost:
    "declGhost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
    using ghost_ok "2.prems"(5) by (cases mode) auto
  have rt_ok_for_declGhost:
    "declGhost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv env"
    using ghost_ok "2.prems"(6) by (cases mode) auto

  \<comment> \<open>Substitution preserves is_lvalue and is_writable_lvalue. \<close>
  have init_lvalue_subst: "is_lvalue (apply_subst_to_term subst initTm)"
    using init_lvalue by simp
  have wl_eq: "is_writable_lvalue ?be (apply_subst_to_term subst initTm)
                = is_writable_lvalue env initTm"
    by simp

  \<comment> \<open>The pure-term lemma applied to initTm. \<close>
  from core_term_type_subst_callee_env[OF init_typed "2.prems"(2,3,4) rt_for_declGhost rt_ok_for_declGhost]
  have init_subst:
    "core_term_type ?be declGhost (apply_subst_to_term subst initTm)
       = Some (apply_subst subst varTy)" by simp

  \<comment> \<open>The substituted result env equals the substituted version of the original
      result env. TE_GhostLocals and TE_ConstLocals updates depend only on names. \<close>
  have result_env_eq:
    "?be \<lparr> TE_LocalVars := fmupd varName (apply_subst subst varTy) (TE_LocalVars ?be),
           TE_GhostLocals := (if declGhost = Ghost then finsert varName (TE_GhostLocals ?be)
                              else fminus (TE_GhostLocals ?be) {|varName|}),
           TE_ConstLocals := (if is_writable_lvalue env initTm
                             then fminus (TE_ConstLocals ?be) {|varName|}
                             else finsert varName (TE_ConstLocals ?be)) \<rparr>
       = apply_subst_to_callee_env subst callerEnv calleeEnv'"
    unfolding env'_eq apply_subst_to_callee_env_def by (simp add: fmmap_fmupd)

  show ?case
    using ghost_ok varTy_wk_subst varTy_rt_subst init_lvalue_subst init_subst result_env_eq wl_eq
    by simp
next
  case (3 env mode assignGhost lhsTm rhsTm)
  \<comment> \<open>Assign: lhs is a writable lvalue, rhs has the same type as lhs, result env
      unchanged. After substitution, lhs gets a substituted type and rhs has the
      same. is_writable_lvalue is a syntactic property of the term so it survives
      substitution unchanged. \<close>
  from "3.prems"(1) obtain lhsTy where
    ghost_ok: "mode = Ghost \<longrightarrow> assignGhost = Ghost" and
    lhs_writable: "is_writable_lvalue env lhsTm" and
    lhs_typed: "core_term_type env assignGhost lhsTm = Some lhsTy" and
    rhs_typed: "core_impure_call_type env assignGhost rhsTm = Some lhsTy
                \<or> core_term_type env assignGhost rhsTm = Some lhsTy" and
    env'_eq: "calleeEnv' = env"
    by (auto split: if_splits option.splits)
  \<comment> \<open>The runtime-substitution-range condition: for the term lemma to apply in
      assignGhost mode, we need to know the substitution range is runtime in
      callerEnv whenever assignGhost = NotGhost. We have it for the outer mode;
      assignGhost can only be NotGhost when mode = NotGhost. \<close>
  have rt_for_assignGhost:
    "assignGhost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
    using ghost_ok "3.prems"(5) by (cases mode) auto
  have rt_ok_for_assignGhost:
    "assignGhost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv env"
    using ghost_ok "3.prems"(6) by (cases mode) auto
  from core_term_type_subst_callee_env[OF lhs_typed "3.prems"(2,3,4) rt_for_assignGhost rt_ok_for_assignGhost]
  have lhs_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv env) assignGhost
                    (apply_subst_to_term subst lhsTm)
       = Some (apply_subst subst lhsTy)" .
  have rhs_subst:
    "core_impure_call_type (apply_subst_to_callee_env subst callerEnv env) assignGhost
                           (apply_subst_to_term subst rhsTm)
       = Some (apply_subst subst lhsTy)
     \<or> core_term_type (apply_subst_to_callee_env subst callerEnv env) assignGhost
                     (apply_subst_to_term subst rhsTm)
       = Some (apply_subst subst lhsTy)"
    using rhs_typed
  proof
    assume "core_impure_call_type env assignGhost rhsTm = Some lhsTy"
    from core_impure_call_type_subst_callee_env[OF this "3.prems"(2,3,4) rt_for_assignGhost rt_ok_for_assignGhost]
    show ?thesis by simp
  next
    assume "core_term_type env assignGhost rhsTm = Some lhsTy"
    from core_term_type_subst_callee_env[OF this "3.prems"(2,3,4) rt_for_assignGhost rt_ok_for_assignGhost]
    show ?thesis by simp
  qed
  have lhs_writable_subst:
    "is_writable_lvalue (apply_subst_to_callee_env subst callerEnv env)
                        (apply_subst_to_term subst lhsTm)"
    using lhs_writable by simp
  show ?case
    using lhs_subst rhs_subst lhs_writable_subst ghost_ok env'_eq
    by (auto split: option.splits)
next
  case (4 env mode tm)
  \<comment> \<open>Return: inner term must typecheck to TE_ReturnType env in the function's
      ghost mode. The result env equals env (= the substituted version), so
      the conclusion's substituted result env is just the substituted input env. \<close>
  from "4.prems"(1) have
    inner_typed: "core_term_type env mode tm = Some (TE_ReturnType env)" and
    mode_eq: "mode = TE_FunctionGhost env" and
    env'_eq: "calleeEnv' = env"
    by (auto split: if_splits)
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv env) mode
                    (apply_subst_to_term subst tm)
       = Some (apply_subst subst (TE_ReturnType env))"
    by (rule core_term_type_subst_callee_env
             [OF inner_typed "4.prems"(2) "4.prems"(3) "4.prems"(4) "4.prems"(5) "4.prems"(6)])
  show ?case
    using inner_subst mode_eq env'_eq by simp
next
  case (5 env mode swapGhost lhsTm rhsTm)
  \<comment> \<open>Swap: both sides are writable lvalues of the same type; result env unchanged.
      Same pattern as Assign with two lvalues. \<close>
  from "5.prems"(1) obtain lhsTy where
    ghost_ok: "mode = Ghost \<longrightarrow> swapGhost = Ghost" and
    lhs_writable: "is_writable_lvalue env lhsTm" and
    rhs_writable: "is_writable_lvalue env rhsTm" and
    lhs_typed: "core_term_type env swapGhost lhsTm = Some lhsTy" and
    rhs_typed: "core_term_type env swapGhost rhsTm = Some lhsTy" and
    env'_eq: "calleeEnv' = env"
    by (auto split: if_splits option.splits)
  have rt_for_swapGhost:
    "swapGhost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
    using ghost_ok "5.prems"(5) by (cases mode) auto
  have rt_ok_for_swapGhost:
    "swapGhost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv env"
    using ghost_ok "5.prems"(6) by (cases mode) auto
  from core_term_type_subst_callee_env[OF lhs_typed "5.prems"(2,3,4) rt_for_swapGhost rt_ok_for_swapGhost]
  have lhs_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv env) swapGhost
                    (apply_subst_to_term subst lhsTm)
       = Some (apply_subst subst lhsTy)" .
  from core_term_type_subst_callee_env[OF rhs_typed "5.prems"(2,3,4) rt_for_swapGhost rt_ok_for_swapGhost]
  have rhs_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv env) swapGhost
                    (apply_subst_to_term subst rhsTm)
       = Some (apply_subst subst lhsTy)" .
  have lhs_writable_subst:
    "is_writable_lvalue (apply_subst_to_callee_env subst callerEnv env)
                        (apply_subst_to_term subst lhsTm)"
    using lhs_writable by simp
  have rhs_writable_subst:
    "is_writable_lvalue (apply_subst_to_callee_env subst callerEnv env)
                        (apply_subst_to_term subst rhsTm)"
    using rhs_writable by simp
  show ?case
    using lhs_subst rhs_subst lhs_writable_subst rhs_writable_subst ghost_ok env'_eq
    by (auto split: option.splits)
next
  case (6 env mode condTm proofBody)
  \<comment> \<open>Assert: condition must be Bool in Ghost mode; proof body typechecks in Ghost
      context with no constraint on the resulting env. The IH for Assert is
      conditional on the condition typechecking; we extract it and apply it. \<close>
  from "6.prems"(1) obtain proofEnv where
    cond_typed: "core_term_type env Ghost condTm = Some CoreTy_Bool" and
    proof_typed: "core_statement_list_type env Ghost proofBody = Some proofEnv" and
    env'_eq: "calleeEnv' = env"
    by (auto split: if_splits option.splits)

  \<comment> \<open>Term lemma applied to the condition. The condition is checked in Ghost mode
      so the runtime preconditions are vacuous. \<close>
  have ghost_rt: "Ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
    by simp
  have ghost_rt_ok: "Ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv env"
    by simp
  from core_term_type_subst_callee_env[OF cond_typed "6.prems"(2,3,4) ghost_rt ghost_rt_ok]
  have cond_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv env) Ghost
                    (apply_subst_to_term subst condTm)
       = Some CoreTy_Bool"
    by simp

  \<comment> \<open>The Assert IH is conditional on cond_typed. Discharge that and use it. \<close>
  from "6.IH"[OF cond_typed proof_typed "6.prems"(2,3,4) ghost_rt ghost_rt_ok]
  have proof_subst:
    "core_statement_list_type
       (apply_subst_to_callee_env subst callerEnv env) Ghost
       (apply_subst_to_stmt_list subst proofBody)
     = Some (apply_subst_to_callee_env subst callerEnv proofEnv)"
    by simp

  show ?case
    using cond_subst proof_subst env'_eq by simp
next
  case (7 env mode tm)
  \<comment> \<open>Assume: inner term must typecheck to Bool in Ghost mode; result env unchanged.
      Inner is checked in Ghost so the runtime-substitution-range condition is
      not needed. \<close>
  from "7.prems"(1) have
    inner_typed: "core_term_type env Ghost tm = Some CoreTy_Bool" and
    env'_eq: "calleeEnv' = env"
    by (auto split: if_splits)
  have ghost_rt: "Ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
    by simp
  have ghost_rt_ok: "Ghost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv env"
    by simp
  from core_term_type_subst_callee_env[OF inner_typed "7.prems"(2,3,4) ghost_rt ghost_rt_ok]
  have inner_subst:
    "core_term_type (apply_subst_to_callee_env subst callerEnv env) Ghost
                    (apply_subst_to_term subst tm)
       = Some CoreTy_Bool"
    by simp
  show ?case using inner_subst env'_eq by auto
next
  case (8 env mode va vb)
  \<comment> \<open>ShowHide is a no-op: typechecks to Some env in any env. The result env
      equals the input env, so substituting both gives the same answer. \<close>
  then show ?case by simp
next
  case (9 env mode matchGhost scrut arms)
  \<comment> \<open>Match: scrutinee must typecheck, each pattern must be compatible with the
      scrutinee type, the patterns must be regular, and each arm body must
      typecheck as a statement list. The result env is env itself. After
      substitution, the scrutinee gets a substituted type and each arm body is
      substituted individually; pattern checks survive substitution. \<close>
  from "9.prems"(1) obtain scrutTy where
    ghost_ok: "mode = Ghost \<longrightarrow> matchGhost = Ghost" and
    scrut_typed: "core_term_type env matchGhost scrut = Some scrutTy" and
    pats_compat: "list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)" and
    pats_regular: "patterns_regular (map fst arms)" and
    bodies_typed: "list_all (\<lambda>body. core_statement_list_type env matchGhost body \<noteq> None)
                            (map snd arms)" and
    env'_eq: "calleeEnv' = env"
    by (auto simp: Let_def split: if_splits option.splits)

  \<comment> \<open>The runtime-substitution-range conditions for the inner term lemma, when
      matchGhost = NotGhost. \<close>
  have rt_for_matchGhost:
    "matchGhost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type callerEnv ty')"
    using ghost_ok "9.prems"(5) by (cases mode) auto
  have rt_ok_for_matchGhost:
    "matchGhost = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv env"
    using ghost_ok "9.prems"(6) by (cases mode) auto

  let ?be = "apply_subst_to_callee_env subst callerEnv env"
  let ?subst_arms = "map (\<lambda>(pat, body). (pat, apply_subst_to_stmt_list subst body)) arms"

  \<comment> \<open>Scrutinee typing transfers under substitution. \<close>
  from core_term_type_subst_callee_env
         [OF scrut_typed "9.prems"(2,3,4) rt_for_matchGhost rt_ok_for_matchGhost]
  have scrut_subst:
    "core_term_type ?be matchGhost (apply_subst_to_term subst scrut)
       = Some (apply_subst subst scrutTy)" .

  \<comment> \<open>Patterns are unchanged under apply_subst_to_stmt. \<close>
  have pats_eq: "map fst ?subst_arms = map fst arms"
    by (induction arms) auto

  \<comment> \<open>Pattern compatibility transfers to the substituted env / type. \<close>
  have pats_compat_subst:
    "list_all (\<lambda>p. pattern_compatible ?be p (apply_subst subst scrutTy)) (map fst ?subst_arms)"
    using pats_compat pats_eq
    by (induction arms)
       (auto intro: pattern_compatible_apply_subst_callee_env)

  have pats_regular_subst: "patterns_regular (map fst ?subst_arms)"
    using pats_regular pats_eq by metis

  \<comment> \<open>Each arm body's statement-list-typing transfers under substitution. The IH
      for Match gives us this for any arm body z in set (map snd arms). \<close>
  have bodies_typed_subst:
    "list_all (\<lambda>body. core_statement_list_type ?be matchGhost body \<noteq> None)
              (map snd ?subst_arms)"
    unfolding list_all_iff
  proof
    fix body' assume body'_in: "body' \<in> set (map snd ?subst_arms)"
    then obtain pat body where
      arm_in: "(pat, body) \<in> set arms" and
      body'_eq: "body' = apply_subst_to_stmt_list subst body"
      by auto
    from arm_in have body_in_snd: "body \<in> set (map snd arms)" by force
    from bodies_typed body_in_snd obtain armEnv where
      body_typed: "core_statement_list_type env matchGhost body = Some armEnv"
      by (auto simp: list_all_iff)
    have pats_compat_nn: "\<not> \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) (map fst arms)"
      using pats_compat by simp
    have pats_regular_nn: "\<not> \<not> patterns_regular (map fst arms)"
      using pats_regular by simp
    from "9.IH"[OF ghost_ok scrut_typed refl refl pats_compat_nn pats_regular_nn
                   body_in_snd body_typed "9.prems"(2,3,4)
                   rt_for_matchGhost rt_ok_for_matchGhost]
    have "core_statement_list_type ?be matchGhost (apply_subst_to_stmt_list subst body)
            = Some (apply_subst_to_callee_env subst callerEnv armEnv)"
      by simp
    thus "core_statement_list_type ?be matchGhost body' \<noteq> None"
      using body'_eq by simp
  qed

  \<comment> \<open>The substituted match statement typechecks, and its result env equals the
      substituted input env. \<close>
  show ?case
    using ghost_ok scrut_subst pats_compat_subst pats_regular_subst bodies_typed_subst env'_eq
    by (simp add: Let_def)
next
  case (10 uw ux uy uz)
  \<comment> \<open>TODO: Fix - typechecking is undefined; cannot prove until implemented \<close>
  then show ?case sorry
next
  case (11 va vb vc vd ve)
  \<comment> \<open>TODO: Obtain - typechecking is undefined; cannot prove until implemented \<close>
  then show ?case sorry
next
  case (12 vf vg vh)
  \<comment> \<open>TODO: Use - typechecking is undefined; cannot prove until implemented \<close>
  then show ?case sorry
next
  case (13 vi vj vk vl vm vn vo)
  \<comment> \<open>TODO: While - typechecking is undefined; cannot prove until implemented \<close>
  then show ?case sorry
next
  case (14 env vp)
  \<comment> \<open>Nil statement list typechecks to Some env in any env. The result env equals
      the input env, so substituting both gives the same answer. \<close>
  then show ?case by simp
next
  case (15 env mode stmt stmts)
  \<comment> \<open>List Cons: typecheck the head statement, then the tail list. The strengthened
      lemma conclusion says the substituted result env equals the substituted middle
      env, which is exactly the input env we need for the tail's IH application. \<close>
  from "15.prems"(1) obtain envMid where
    head_typed: "core_statement_type env mode stmt = Some envMid" and
    tail_typed: "core_statement_list_type envMid mode stmts = Some calleeEnv'"
    by (auto split: option.splits)

  \<comment> \<open>Statement IH gives the head's substituted typing. \<close>
  from "15.IH"(1)[OF head_typed "15.prems"(2,3,4,5,6)]
  have head_subst:
    "core_statement_type
       (apply_subst_to_callee_env subst callerEnv env) mode
       (apply_subst_to_stmt subst stmt)
     = Some (apply_subst_to_callee_env subst callerEnv envMid)" .

  \<comment> \<open>For the tail IH we need: well-formedness of envMid, and callee_env_subst_ok
      between callerEnv and envMid. Statement typechecking preserves wellformedness;
      and tyenv_fixed_eq between env and envMid means the global-ish fields agree,
      which lets us transfer callee_env_subst_ok across. \<close>
  from core_statement_type_preserves_well_formed[OF head_typed "15.prems"(2)]
  have wf_mid: "tyenv_well_formed envMid" .

  from core_statement_type_fixed_eq[OF head_typed]
  have fxeq: "tyenv_fixed_eq env envMid" .

  have field_eq:
    "TE_GlobalVars envMid = TE_GlobalVars env"
    "TE_GhostGlobals envMid = TE_GhostGlobals env"
    "TE_Functions envMid = TE_Functions env"
    "TE_Datatypes envMid = TE_Datatypes env"
    "TE_DataCtors envMid = TE_DataCtors env"
    "TE_DataCtorsByType envMid = TE_DataCtorsByType env"
    "TE_GhostDatatypes envMid = TE_GhostDatatypes env"
    "TE_TypeVars envMid = TE_TypeVars env"
    "TE_RuntimeTypeVars envMid = TE_RuntimeTypeVars env"
    using fxeq unfolding tyenv_fixed_eq_def by simp_all

  have ok_mid: "callee_env_subst_ok subst callerEnv envMid"
    using "15.prems"(3) field_eq
    unfolding callee_env_subst_ok_def by simp

  have ok_rt_mid: "mode = NotGhost \<longrightarrow> callee_env_subst_runtime_ok subst callerEnv envMid"
    using "15.prems"(6) field_eq
    unfolding callee_env_subst_runtime_ok_def by simp

  \<comment> \<open>Apply the list IH to the tail. \<close>
  from "15.IH"(2)[OF head_typed tail_typed wf_mid ok_mid "15.prems"(4,5) ok_rt_mid]
  have tail_subst:
    "core_statement_list_type
       (apply_subst_to_callee_env subst callerEnv envMid) mode
       (apply_subst_to_stmt_list subst stmts)
     = Some (apply_subst_to_callee_env subst callerEnv calleeEnv')" .

  show ?case using head_subst tail_subst by simp
qed

lemmas core_statement_type_subst_callee_env =
  core_statement_type_and_list_subst_callee_env(1)
lemmas core_statement_list_type_subst_callee_env =
  core_statement_type_and_list_subst_callee_env(2)


end

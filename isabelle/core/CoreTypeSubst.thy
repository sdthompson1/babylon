theory CoreTypeSubst
  imports CoreTypecheck CoreStmtTypecheck
begin

(* Substitute type metavariables (CoreTy_Meta) in a term, statement, or environment.

   This file contains the substitution machinery used by the function-call soundness
   proof (TypeSoundness.thy case 6) and by any future metatheoretic work that needs
   to push type substitutions through well-typed syntax.

   The two central results (not yet proved in full here) are:

   - apply_subst_to_stmt_list_preserves_typing: if a statement list typechecks in
     some environment, then the substituted list typechecks in the substituted
     environment. (This is "Lemma 1" in the soundness plan.)

   - The interpreter erasure lemma lives in a separate file
     (InterpTypeErasure.thy) and is "Lemma 2". It says that running the interpreter
     on the substituted statement list gives the same result as running it on the
     original list, under well-typedness.

   Naming follows the pattern already established by apply_subst_to_term:
   apply_subst_to_<thing> for the substitution function,
   apply_subst_to_<thing>_preserves_typing for the typing-preservation lemma. *)


(* ========================================================================== *)
(* Substitution on terms                                                       *)
(* ========================================================================== *)

fun apply_subst_to_term :: "MetaSubst \<Rightarrow> CoreTerm \<Rightarrow> CoreTerm" where
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


(* CorePattern does not currently carry any CoreType, so substitution on patterns
   is the identity. Defined here for symmetry and so future pattern forms can
   plug in without reshaping callers. *)
fun apply_subst_to_pat :: "MetaSubst \<Rightarrow> CorePattern \<Rightarrow> CorePattern" where
  "apply_subst_to_pat subst p = p"


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

(* pattern_compatible and patterns_exhaustive only inspect the top-level shape of the
   scrutinee type (and for Datatype, just the type name). Substitution preserves all
   of these top-level shapes, so if the predicate holds on ty it also holds on
   apply_subst subst ty. (The reverse is not true if ty is a CoreTy_Meta.) *)
lemma pattern_compatible_apply_subst:
  "pattern_compatible env p ty \<Longrightarrow> pattern_compatible env p (apply_subst subst ty)"
  by (cases p; cases ty) (auto split: option.splits prod.splits)

lemma patterns_exhaustive_apply_subst:
  "patterns_exhaustive env ty pats \<Longrightarrow> patterns_exhaustive env (apply_subst subst ty) pats"
  by (cases ty) (auto split: if_splits)


(* If a term has type ty, then apply_subst_to_term subst tm has type (apply_subst subst ty).
   We assume the environment is well-formed, and that the substitution produces well-kinded
   and (in NotGhost mode) runtime types. *)
lemma apply_subst_to_term_preserves_typing:
  assumes "core_term_type env mode tm = Some ty"
      and "tyenv_well_formed env"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and "mode = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type env ty')"
  shows "core_term_type env mode (apply_subst_to_term subst tm) = Some (apply_subst subst ty)"
  sorry

(* Type substitution does not change term-level free variables,
   since it only substitutes type metavariables. *)
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


(* ========================================================================== *)
(* Substitution on statements                                                  *)
(* ========================================================================== *)

fun apply_subst_to_stmt :: "MetaSubst \<Rightarrow> CoreStatement \<Rightarrow> CoreStatement"
and apply_subst_to_stmt_list :: "MetaSubst \<Rightarrow> CoreStatement list \<Rightarrow> CoreStatement list" where
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
      (map (\<lambda>(pat, body). (apply_subst_to_pat subst pat, apply_subst_to_stmt_list subst body)) arms)"
| "apply_subst_to_stmt subst (CoreStmt_ShowHide sh name) =
    CoreStmt_ShowHide sh name"
| "apply_subst_to_stmt_list subst [] = []"
| "apply_subst_to_stmt_list subst (s # rest) =
    apply_subst_to_stmt subst s # apply_subst_to_stmt_list subst rest"


(* Statement-level and statement-list-level typing preservation under type substitution.
   Proved together by mutual induction on the apply_subst_to_stmt / apply_subst_to_stmt_list
   definition, since While, Match and Assert contain nested statement lists. *)
lemma apply_subst_to_stmt_and_list_preserves_typing:
  "\<lbrakk> core_statement_type env ghost stmt = Some env';
     tyenv_well_formed env;
     \<forall>ty' \<in> fmran' subst. is_well_kinded env ty';
     ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type env ty') \<rbrakk>
   \<Longrightarrow> core_statement_type env ghost (apply_subst_to_stmt subst stmt) = Some env'"
  "\<lbrakk> core_statement_list_type env ghost stmts = Some env';
     tyenv_well_formed env;
     \<forall>ty' \<in> fmran' subst. is_well_kinded env ty';
     ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type env ty') \<rbrakk>
   \<Longrightarrow> core_statement_list_type env ghost (apply_subst_to_stmt_list subst stmts) = Some env'"
proof (induction stmt and stmts
       arbitrary: env env' ghost and env env' ghost
       rule: apply_subst_to_stmt_apply_subst_to_stmt_list.induct)
  case (1 subst declGhost varName varOrRef varTy initTm)
  then show ?case sorry
next
  case (2 subst name ty)
  \<comment> \<open>CoreStmt_Fix: typechecking undefined\<close>
  then show ?case sorry
next
  case (3 subst name ty tm)
  \<comment> \<open>CoreStmt_Obtain: typechecking undefined\<close>
  then show ?case sorry
next
  case (4 subst tm)
  \<comment> \<open>CoreStmt_Use: typechecking undefined\<close>
  then show ?case sorry
next
  case (5 subst g lhs rhs)
  then show ?case sorry
next
  case (6 subst g lhs rhs)
  then show ?case sorry
next
  case (7 subst tm)
  then show ?case sorry
next
  case (8 subst tm proof_stmts)
  then show ?case sorry
next
  case (9 subst tm)
  \<comment> \<open>CoreStmt_Assume: inner term typechecks in Ghost to Bool; substitution preserves that\<close>
  from "9.prems"(1) have
    tm_typed: "core_term_type env Ghost tm = Some CoreTy_Bool" and
    env_eq: "env' = env"
    by (auto split: if_splits)
  from apply_subst_to_term_preserves_typing[OF tm_typed "9.prems"(2) "9.prems"(3)]
  have "core_term_type env Ghost (apply_subst_to_term subst tm) = Some (apply_subst subst CoreTy_Bool)"
    by simp
  hence "core_term_type env Ghost (apply_subst_to_term subst tm) = Some CoreTy_Bool" by simp
  thus ?case using env_eq by simp
next
  case (10 subst g cond invs decr body)
  \<comment> \<open>CoreStmt_While: typechecking undefined\<close>
  then show ?case sorry
next
  case (11 subst g scrut arms)
  \<comment> \<open>CoreStmt_Match: typechecking undefined\<close>
  then show ?case sorry
next
  case (12 subst sh name)
  \<comment> \<open>CoreStmt_ShowHide: no-op; returns Some env unchanged\<close>
  then show ?case by simp
next
  case (13 subst)
  \<comment> \<open>Nil statement list\<close>
  then show ?case by simp
next
  case (14 subst s rest)
  then show ?case sorry
qed

(* Convenience aliases matching the original names. *)
lemmas apply_subst_to_stmt_preserves_typing =
  apply_subst_to_stmt_and_list_preserves_typing(1)
lemmas apply_subst_to_stmt_list_preserves_typing =
  apply_subst_to_stmt_and_list_preserves_typing(2)


(* ========================================================================== *)
(* Substitution on environments                                                *)
(* ========================================================================== *)

(* Apply a substitution to every type stored in an environment.
   The substitution touches:
     - TE_LocalVars, TE_GlobalVars: variable types (though in a well-formed env these
                    are ground, so in practice this is a no-op at use sites)
     - TE_ReturnType
   It does NOT touch:
     - TE_TypeVars / TE_RuntimeTypeVars (these are binder sets, not types)
     - TE_Datatypes, TE_DataCtors, TE_DataCtorsByType (these are outer-scope
                    definitions, fixed before the substitution applies)
     - TE_Functions (function signatures are also outer-scope and fixed). *)
definition apply_subst_to_env :: "MetaSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "apply_subst_to_env subst env =
    env \<lparr> TE_LocalVars := fmmap (apply_subst subst) (TE_LocalVars env),
          TE_GlobalVars := fmmap (apply_subst subst) (TE_GlobalVars env),
          TE_ReturnType := apply_subst subst (TE_ReturnType env) \<rparr>"

end

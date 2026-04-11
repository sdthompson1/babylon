theory InterpTypeErasure
  imports CoreInterp StateMatchesEnv "../core/CoreTypeSubst"
begin

(* ========================================================================== *)
(* Interpreter erasure under type substitution                                *)
(* ========================================================================== *)

(* This file contains "Lemma 2" of the soundness plan: the interpreter is
   invariant under type substitution on its syntactic arguments, provided the
   syntax is well-typed.

   Informally: running interp_statement_list on the substituted body gives the
   same result as running it on the original body. This is the erasure property
   that allows the function-call soundness proof (TypeSoundness.thy case 6) to
   apply the statement-list IH to the substituted body and then transport the
   result back to the original body that the interpreter actually runs.

   The proof obligation at each interpreter branch is discharged by one of four
   observations:
     (i)   typechecking forces the embedded type to be ground at that position
           (e.g. the target of CoreTm_Cast must be CoreTy_FiniteInt, ruling
           out rigid metavars that substitution might alter);
     (ii)  the interpreter does not actually read the embedded type (e.g.
           CoreTm_LitArray's elemTy is not inspected once we know the term
           list typechecks);
     (iii) the syntactic position is not a type (e.g. array dimensions are
           integer literals);
     (iv)  the branch is unreachable at runtime (e.g. CoreTm_Quantifier is
           ghost-only, CoreTm_Allocated is ghost-only, CoreStmt_Fix/Obtain/Use
           are ghost-only).

   The proof is a single mutual induction on fuel that mirrors the interpreter's
   own 6-way mutual recursion.

   Preconditions. The substitution \<sigma> must have runtime-typed range (so that
   values typed at pre-substitution types remain well-typed after substitution)
   and the syntactic argument must be well-typed in an env whose TE_TypeVars
   is a superset of fmdom \<sigma>. The state_matches_env premise threads the state's
   store typing through the argument. *)


(* Erasure for individual interpreter entry points. Stated separately here
   but proved together by mutual induction. *)

lemma interp_term_subst_erase:
  assumes "state_matches_env state env storeTyping"
      and "tyenv_well_formed env"
      and "core_term_type env NotGhost tm = Some ty"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and "\<forall>ty' \<in> fmran' subst. is_runtime_type env ty'"
  shows "interp_term fuel state (apply_subst_to_term subst tm)
         = interp_term fuel state tm"
  sorry

lemma interp_term_list_subst_erase:
  assumes "state_matches_env state env storeTyping"
      and "tyenv_well_formed env"
      and "list_all (\<lambda>tm. \<exists>ty. core_term_type env NotGhost tm = Some ty) tms"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and "\<forall>ty' \<in> fmran' subst. is_runtime_type env ty'"
  shows "interp_term_list fuel state (map (apply_subst_to_term subst) tms)
         = interp_term_list fuel state tms"
  sorry

lemma interp_writable_lvalue_subst_erase:
  assumes "state_matches_env state env storeTyping"
      and "tyenv_well_formed env"
      and "is_writable_lvalue env tm"
      and "core_term_type env NotGhost tm = Some ty"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and "\<forall>ty' \<in> fmran' subst. is_runtime_type env ty'"
  shows "interp_writable_lvalue fuel state (apply_subst_to_term subst tm)
         = interp_writable_lvalue fuel state tm"
  sorry

lemma interp_statement_subst_erase:
  assumes "state_matches_env state env storeTyping"
      and "tyenv_well_formed env"
      and "core_statement_type env NotGhost stmt = Some env'"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and "\<forall>ty' \<in> fmran' subst. is_runtime_type env ty'"
  shows "interp_statement fuel state (apply_subst_to_stmt subst stmt)
         = interp_statement fuel state stmt"
  sorry

(* Lemma 2 proper: the statement-list form is what function-call soundness
   consumes. *)
lemma interp_statement_list_subst_erase:
  assumes "state_matches_env state env storeTyping"
      and "tyenv_well_formed env"
      and "core_statement_list_type env NotGhost stmts = Some env'"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and "\<forall>ty' \<in> fmran' subst. is_runtime_type env ty'"
  shows "interp_statement_list fuel state (apply_subst_to_stmt_list subst stmts)
         = interp_statement_list fuel state stmts"
  sorry

lemma interp_function_call_subst_erase:
  assumes "state_matches_env state env storeTyping"
      and "tyenv_well_formed env"
      and "fmlookup (TE_Functions env) fnName = Some funInfo"
      and "list_all (\<lambda>tm. \<exists>ty. core_term_type env NotGhost tm = Some ty) argTms"
      and "\<forall>ty' \<in> fmran' subst. is_well_kinded env ty'"
      and "\<forall>ty' \<in> fmran' subst. is_runtime_type env ty'"
  shows "interp_function_call fuel state fnName (map (apply_subst_to_term subst) argTms)
         = interp_function_call fuel state fnName argTms"
  sorry

end

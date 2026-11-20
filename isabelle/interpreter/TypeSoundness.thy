theory TypeSoundness
  imports TypeSoundnessHelpers4
begin

(*-----------------------------------------------------------------------------*)
(* Main interpreter type soundness theorem. *)
(*-----------------------------------------------------------------------------*)

(* Given a well-formed type environment, a machine state consistent with
   that environment, and well-typed input, the interpreter either runs out of
   fuel, fails with a RuntimeError, or produces a result consistent with the
   typechecking (e.g., in interp_term, it produces a value of the correct type).
   It does not fail with a TypeError.

   The machine's IS_Ghost flag must be set correctly:
    - For terms, it must equal the typechecking mode used.
    - For statements, the two can differ, but NotGhost execution cannot enter a Ghost function
      (i.e. if IS_Ghost = NotGhost then TE_FunctionGhost must also be NotGhost).
    - For function calls, see full theorem statement below.

   For statements, TE_ProofGoal env must be None, i.e. the interpreter cannot execute
   proof bodies.

   For the definitions of sound_term_result, sound_statement_result, etc., see
   the top of TypeSoundnessHelpers1.thy.
*)

theorem type_soundness:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
  shows interp_term_sound:
    "core_term_type env ghost tm = Some ty \<and> IS_Ghost state = ghost \<longrightarrow>
      sound_term_result state env ty (interp_term d fuel state tm)"
  and interp_term_list_sound:
    "map (core_term_type env ghost) tms = types \<and>
    list_all (\<lambda>ty. ty \<noteq> None) types \<and> IS_Ghost state = ghost \<longrightarrow>
      sound_term_results state env (map the types) (interp_term_list d fuel state tms)"
  and interp_writable_lvalue_sound:
    "is_writable_lvalue env tm \<and> core_term_type env ghost tm = Some ty
       \<and> IS_Ghost state = ghost \<longrightarrow>
      sound_lvalue_result state env storeTyping ty (interp_writable_lvalue d fuel state tm)"
  and interp_statement_sound:
    "core_statement_type env ghost stmt = Some env' \<and> TE_ProofGoal env = None
       \<and> (IS_Ghost state = NotGhost \<longrightarrow> TE_FunctionGhost env = NotGhost) \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement d fuel state stmt)"
  and interp_statement_list_sound:
    "core_statement_list_type env ghost stmts = Some env' \<and> TE_ProofGoal env = None
       \<and> (IS_Ghost state = NotGhost \<longrightarrow> TE_FunctionGhost env = NotGhost) \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement_list d fuel state stmts)"
  and interp_function_call_sound:
    "\<lbrakk> fmlookup (TE_Functions env) fnName = Some funInfo;
       list_all2 (\<lambda>tm (ty, _, g).
           core_term_type env (param_mode ghost g) tm
             = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty))
         argTms (FI_TmArgs funInfo);
       IS_Ghost state = ghost;
       ghost = NotGhost \<longrightarrow> FI_Ghost funInfo = NotGhost;
       retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo);
       length tyArgs = length (FI_TyArgs funInfo);
       list_all (is_well_kinded env) tyArgs;
       \<forall>i < length argTms.
         (fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
          is_writable_lvalue env (argTms ! i))
     \<rbrakk> \<Longrightarrow> sound_function_call_result state env storeTyping retTy (interp_function_call d fuel state fnName tyArgs argTms)"
proof -
  have dIH:
    "\<forall>d' < d. \<forall>fuel' env' (state' :: 'w InterpState) storeTyping' tm' ty'.
        state_matches_env state' env' storeTyping' \<longrightarrow>
        tyenv_well_formed env' \<longrightarrow>
        core_term_type env' (IS_Ghost state') tm' = Some ty' \<longrightarrow>
        sound_term_result state' env' ty' (interp_term d' fuel' state' tm')"
    by (intro allI impI) (rule interp_term_sound_all_depths)
  note at_d = type_soundness_at_depth[OF dIH state_env wf_env]
  show "core_term_type env ghost tm = Some ty \<and> IS_Ghost state = ghost \<longrightarrow>
      sound_term_result state env ty (interp_term d fuel state tm)"
    using at_d(1) by blast
  show "map (core_term_type env ghost) tms = types \<and>
    list_all (\<lambda>ty. ty \<noteq> None) types \<and> IS_Ghost state = ghost \<longrightarrow>
      sound_term_results state env (map the types) (interp_term_list d fuel state tms)"
    using at_d(2) by blast
  show "is_writable_lvalue env tm \<and> core_term_type env ghost tm = Some ty
       \<and> IS_Ghost state = ghost \<longrightarrow>
      sound_lvalue_result state env storeTyping ty (interp_writable_lvalue d fuel state tm)"
    using at_d(3) by blast
  show "core_statement_type env ghost stmt = Some env' \<and> TE_ProofGoal env = None
       \<and> (IS_Ghost state = NotGhost \<longrightarrow> TE_FunctionGhost env = NotGhost) \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement d fuel state stmt)"
    by (rule at_d(4))
  show "core_statement_list_type env ghost stmts = Some env' \<and> TE_ProofGoal env = None
       \<and> (IS_Ghost state = NotGhost \<longrightarrow> TE_FunctionGhost env = NotGhost) \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement_list d fuel state stmts)"
    by (rule at_d(5))
  show "\<lbrakk> fmlookup (TE_Functions env) fnName = Some funInfo;
       list_all2 (\<lambda>tm (ty, _, g).
           core_term_type env (param_mode ghost g) tm
             = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty))
         argTms (FI_TmArgs funInfo);
       IS_Ghost state = ghost;
       ghost = NotGhost \<longrightarrow> FI_Ghost funInfo = NotGhost;
       retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo);
       length tyArgs = length (FI_TyArgs funInfo);
       list_all (is_well_kinded env) tyArgs;
       \<forall>i < length argTms.
         (fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
          is_writable_lvalue env (argTms ! i))
     \<rbrakk> \<Longrightarrow> sound_function_call_result state env storeTyping retTy (interp_function_call d fuel state fnName tyArgs argTms)"
  proof -
    assume fn: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and args: "list_all2 (\<lambda>tm (ty, _, g).
           core_term_type env (param_mode ghost g) tm
             = Some (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty))
         argTms (FI_TmArgs funInfo)"
      and mode: "IS_Ghost state = ghost"
      and callee: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo = NotGhost"
      and ret: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
      and len: "length tyArgs = length (FI_TyArgs funInfo)"
      and wk: "list_all (is_well_kinded env) tyArgs"
      and refs: "\<forall>i < length argTms.
         (fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
          is_writable_lvalue env (argTms ! i))"
    show "sound_function_call_result state env storeTyping retTy
            (interp_function_call d fuel state fnName tyArgs argTms)"
      by (rule at_d(6)[OF fn args[folded mode] callee[folded mode] ret len wk refs])
  qed
qed


end

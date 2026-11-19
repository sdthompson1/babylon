theory TypeSoundness
  imports TypeSoundnessHelpers4
begin

(*-----------------------------------------------------------------------------*)
(* Main interpreter type soundness theorem. *)
(*-----------------------------------------------------------------------------*)

(* Given a well-formed type environment, a machine state consistent with
   that environment, and well-typed input (in either Ghost or NotGhost mode),
   the interpreter either runs out of fuel, fails with a RuntimeError, or
   produces a result consistent with the typechecking (e.g., in interp_term,
   it produces a value of the correct type). It does not fail with a TypeError.

   The mode of the state (IS_Ghost) has to fit the typing:
    - a term, a list of terms or an lvalue is evaluated in a state whose mode
      is the mode in which it is typed;
    - a statement (typed in any mode) is run in a state that is in NotGhost
      mode only if the enclosing function is not ghost (TE_FunctionGhost env).
      The two modes need not be equal: a function that is not ghost runs in
      Ghost mode when ghost code calls it. (The interpreter raises the mode
      itself for the terms of a statement that has a ghost flag.)
    - a function call is made in a state of mode `ghost`, each argument being
      typed in the mode of its parameter (param_mode ghost g), and the function
      called is not ghost if `ghost` is NotGhost.
   Without these the theorem is false: a term typed in Ghost mode may call a
   ghost function, and the interpreter gives a TypeError if that happens in a
   state in NotGhost mode.

   For statements, the theorem only holds if TE_ProofGoal env = None; the
   interpreter cannot execute proof bodies.

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

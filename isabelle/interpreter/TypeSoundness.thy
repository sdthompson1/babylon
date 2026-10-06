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

   For statements, the theorem only holds if TE_ProofGoal env = None; the
   interpreter cannot execute proof bodies.

   For the definitions of sound_term_result, sound_statement_result, etc., see
   the top of TypeSoundnessHelpers1.thy.
*)

theorem type_soundness:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
  shows interp_term_sound:
    "core_term_type env ghost tm = Some ty \<longrightarrow>
      sound_term_result state env ty (interp_term d fuel state tm)"
  and interp_term_list_sound:
    "map (core_term_type env ghost) tms = types \<and>
    list_all (\<lambda>ty. ty \<noteq> None) types \<longrightarrow>
      sound_term_results state env (map the types) (interp_term_list d fuel state tms)"
  and interp_writable_lvalue_sound:
    "is_writable_lvalue env tm \<and> core_term_type env ghost tm = Some ty \<longrightarrow>
      sound_lvalue_result state env storeTyping ty (interp_writable_lvalue d fuel state tm)"
  and interp_statement_sound:
    "core_statement_type env ghost stmt = Some env' \<and> TE_ProofGoal env = None \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement d fuel state stmt)"
  and interp_statement_list_sound:
    "core_statement_list_type env ghost stmts = Some env' \<and> TE_ProofGoal env = None \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement_list d fuel state stmts)"
  and interp_function_call_sound:
    "\<lbrakk> fmlookup (TE_Functions env) fnName = Some funInfo;
       list_all2 (\<lambda>tm expectedTy.
           core_term_type env ghost tm = Some expectedTy)
         argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo));
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
        core_term_type env' Ghost tm' = Some ty' \<longrightarrow>
        sound_term_result state' env' ty' (interp_term d' fuel' state' tm')"
    by (intro allI impI) (rule interp_term_sound_all_depths)
  note at_d = type_soundness_at_depth[OF dIH state_env wf_env]
  show "core_term_type env ghost tm = Some ty \<longrightarrow>
      sound_term_result state env ty (interp_term d fuel state tm)"
  proof (intro impI)
    assume t: "core_term_type env ghost tm = Some ty"
    show "sound_term_result state env ty (interp_term d fuel state tm)"
      by (rule at_d(1)[rule_format, OF core_term_type_NotGhost_imp_Ghost[OF t]])
  qed
  show "map (core_term_type env ghost) tms = types \<and>
    list_all (\<lambda>ty. ty \<noteq> None) types \<longrightarrow>
      sound_term_results state env (map the types) (interp_term_list d fuel state tms)"
  proof (intro impI, elim conjE)
    assume m: "map (core_term_type env ghost) tms = types"
      and a: "list_all (\<lambda>ty. ty \<noteq> None) types"
    have eq: "core_term_type env Ghost t = core_term_type env ghost t" if "t \<in> set tms" for t
    proof -
      from m a that have "core_term_type env ghost t \<noteq> None"
        by (auto simp: list_all_iff)
      then obtain ty0 where s: "core_term_type env ghost t = Some ty0" by auto
      from core_term_type_NotGhost_imp_Ghost[OF s] s show ?thesis by simp
    qed
    have "map (core_term_type env Ghost) tms = map (core_term_type env ghost) tms"
      by (rule map_cong[OF refl]) (rule eq)
    with m have g: "map (core_term_type env Ghost) tms = types" by simp
    show "sound_term_results state env (map the types) (interp_term_list d fuel state tms)"
      by (rule at_d(2)[rule_format, OF conjI[OF g a]])
  qed
  show "is_writable_lvalue env tm \<and> core_term_type env ghost tm = Some ty \<longrightarrow>
      sound_lvalue_result state env storeTyping ty (interp_writable_lvalue d fuel state tm)"
  proof (intro impI, elim conjE)
    assume w: "is_writable_lvalue env tm"
      and t: "core_term_type env ghost tm = Some ty"
    show "sound_lvalue_result state env storeTyping ty (interp_writable_lvalue d fuel state tm)"
      by (rule at_d(3)[rule_format, OF conjI[OF w core_term_type_NotGhost_imp_Ghost[OF t]]])
  qed
  show "core_statement_type env ghost stmt = Some env' \<and> TE_ProofGoal env = None \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement d fuel state stmt)"
    by (rule at_d(4))
  show "core_statement_list_type env ghost stmts = Some env' \<and> TE_ProofGoal env = None \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement_list d fuel state stmts)"
    by (rule at_d(5))
  show "\<lbrakk> fmlookup (TE_Functions env) fnName = Some funInfo;
       list_all2 (\<lambda>tm expectedTy.
           core_term_type env ghost tm = Some expectedTy)
         argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo));
       retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo);
       length tyArgs = length (FI_TyArgs funInfo);
       list_all (is_well_kinded env) tyArgs;
       \<forall>i < length argTms.
         (fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
          is_writable_lvalue env (argTms ! i))
     \<rbrakk> \<Longrightarrow> sound_function_call_result state env storeTyping retTy (interp_function_call d fuel state fnName tyArgs argTms)"
  proof -
    assume fn: "fmlookup (TE_Functions env) fnName = Some funInfo"
      and args: "list_all2 (\<lambda>tm expectedTy.
           core_term_type env ghost tm = Some expectedTy)
         argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))"
      and ret: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
      and len: "length tyArgs = length (FI_TyArgs funInfo)"
      and wk: "list_all (is_well_kinded env) tyArgs"
      and refs: "\<forall>i < length argTms.
         (fst (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
          is_writable_lvalue env (argTms ! i))"
    have g_args: "list_all2 (\<lambda>tm expectedTy.
           core_term_type env Ghost tm = Some expectedTy)
         argTms (map (\<lambda>(ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo))"
    proof (rule list_all2_mono[OF args])
      fix tm0 ety
      assume "core_term_type env ghost tm0 = Some ety"
      then show "core_term_type env Ghost tm0 = Some ety" by (rule core_term_type_NotGhost_imp_Ghost)
    qed
    show "sound_function_call_result state env storeTyping retTy
            (interp_function_call d fuel state fnName tyArgs argTms)"
      by (rule at_d(6)[OF fn g_args ret len wk refs])
  qed
qed


end

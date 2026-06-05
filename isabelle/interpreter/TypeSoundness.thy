theory TypeSoundness
  imports TypeSoundnessHelpers3
begin

(*-----------------------------------------------------------------------------*)
(* Main interpreter type soundness theorem. *)
(*-----------------------------------------------------------------------------*)

(* Given a well-formed type environment, and a machine state consistent with
   that environment, the interpreter either runs out of fuel, fails with a
   RuntimeError, or produces a result consistent with the typechecking
   (e.g., in interp_term, it produces a value of the correct type).
   It does not fail with a TypeError.
*)

theorem type_soundness:
  assumes state_env: "state_matches_env (state :: 'w InterpState) env storeTyping"
    and wf_env: "tyenv_well_formed env"
  shows interp_term_sound:
    "core_term_type env NotGhost tm = Some ty \<longrightarrow>
      sound_term_result state env ty (interp_term fuel state tm)"
  and interp_term_list_sound:
    "map (core_term_type env NotGhost) tms = types \<and>
    list_all (\<lambda>ty. ty \<noteq> None) types \<longrightarrow>
      sound_term_results state env (map the types) (interp_term_list fuel state tms)"
  and interp_writable_lvalue_sound:
    "is_writable_lvalue env tm \<and> core_term_type env NotGhost tm = Some ty \<longrightarrow>
      sound_lvalue_result state env storeTyping ty (interp_writable_lvalue fuel state tm)"
  and interp_statement_sound:
    "core_statement_type env NotGhost stmt = Some env' \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement fuel state stmt)"
  and interp_statement_list_sound:
    "core_statement_list_type env NotGhost stmts = Some env' \<longrightarrow>
      sound_statement_result env env' storeTyping (interp_statement_list fuel state stmts)"
  and interp_function_call_sound:
    "\<lbrakk> fmlookup (TE_Functions env) fnName = Some funInfo;
       FI_Ghost funInfo = NotGhost;
       list_all2 (\<lambda>tm expectedTy.
           case core_term_type env NotGhost tm of
             None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
         argTms (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                     (FI_TmArgs funInfo));
       retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo);
       length tyArgs = length (FI_TyArgs funInfo);
       list_all (is_well_kinded env) tyArgs;
       list_all (is_runtime_type env) tyArgs;
       \<forall>i < length argTms.
         (snd (snd (FI_TmArgs funInfo ! i)) = Ref \<longrightarrow>
          is_writable_lvalue env (argTms ! i))
     \<rbrakk> \<Longrightarrow> sound_function_call_result state env storeTyping retTy (interp_function_call fuel state fnName tyArgs argTms)"
using assms
proof (induction fuel arbitrary: state env storeTyping tm ty tms types fnName argTms stmt env' stmts funInfo tyArgs retTy)
  case 0
  {
    case 1
    then show ?case by simp
  next
    case 2
    then show ?case by simp
  next
    case 3
    then show ?case by simp
  next
    case 4
    then show ?case by simp
  next
    case 5
    then show ?case by simp
  next
    case 6
    then show ?case by simp
  }
next
  case (Suc fuel)
  {
    (* interp_term_sound *)
    case 1
    show ?case proof (intro impI)

      (* Given a well-typed term *)
      assume typing: "core_term_type env NotGhost tm = Some ty"

      (* From IH, we know interp_term works properly for fuel;
         we need to prove it for (Suc fuel) *)
      have IH: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                  state_matches_env state' env' storeTyping' \<Longrightarrow>
                  tyenv_well_formed env' \<Longrightarrow>
                  core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                    sound_term_result state' env' ty' (interp_term fuel state' tm')"
        by (simp add: "1.prems"(1,2) Suc.IH(1))

      show "sound_term_result state env ty (interp_term (Suc fuel) state tm)"
      proof (cases tm)
        (* Literal bool - evaluates to CV_Bool *)
        case (CoreTm_LitBool b)
        then show ?thesis using typing by auto
      next
        (* Literal int - evaluates to CV_FiniteInt if well-typed *)
        case (CoreTm_LitInt i)
        then show ?thesis using typing by auto
      next
        case (CoreTm_LitArray elemTy elemTms)
        have IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results state' env' (map the types') (interp_term_list fuel state' tms')"
          by (simp add: Suc.IH(2) "1.prems"(1,2))
        from CoreTm_LitArray show ?thesis
          using type_soundness_lit_array[OF "1.prems"(1,2) IH_list] typing
          by simp
  
      next
        (* Variable/constant lookup *)
        case (CoreTm_Var varName)
        (* From typing, the variable exists in the type env *)
        from typing CoreTm_Var obtain varTy where
          var_lookup: "tyenv_lookup_var env varName = Some varTy" and
          not_ghost: "\<not> tyenv_var_ghost env varName" and
          ty_eq: "ty = varTy"
          by (auto split: option.splits if_splits)
        show ?thesis proof (cases "fmlookup (IS_Locals state) varName")
          case None
          then show ?thesis proof (cases "fmlookup (IS_Refs state) varName")
            case None2: None
            (* Variable must be in Globals. It must be a global in the type env. *)
            (* If it were a local, then non_consts or no_extra would place it in IS_Locals/IS_Refs *)
            show ?thesis
            proof (cases "fmlookup (TE_LocalVars env) varName")
              case (Some localTy)
              (* Local var not in IS_Locals or IS_Refs: contradicts non_consts/no_extra *)
              from var_lookup Some have "varTy = localTy"
                unfolding tyenv_lookup_var_def by simp
              (* If const local, it should still be in IS_Locals or IS_Refs via local_vars_exist *)
              from "1.prems"(1) Some not_ghost
              have "local_var_in_state_with_type state env storeTyping varName localTy"
                unfolding state_matches_env_def local_vars_exist_in_state_def
                by (simp add: tyenv_var_ghost_def)
              with None None2 show ?thesis
                unfolding local_var_in_state_with_type_def
                by (auto split: option.splits)
            next
              case None3: None
              (* Global variable *)
              from var_lookup None3 have global_lookup: "fmlookup (TE_GlobalVars env) varName = Some varTy"
                unfolding tyenv_lookup_var_def by simp
              from "1.prems"(1) global_lookup not_ghost
              have "global_var_in_state_with_type state env varName varTy"
                unfolding state_matches_env_def global_vars_exist_in_state_def
                by (simp add: None3 tyenv_var_ghost_def)
              then obtain val where
                const_lookup: "fmlookup (IS_Globals state) varName = Some val"
                and val_typed: "value_has_type env val varTy"
                unfolding global_var_in_state_with_type_def
                by (auto split: option.splits)
              have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName) = Inr val"
                using CoreTm_Var None None2 const_lookup by simp
              (* varTy is ground (value_has_type only holds for ground types), so
                 apply_subst is a no-op. *)
              have "apply_subst (IS_TyArgs state) varTy = varTy"
                using value_has_type_ground[OF val_typed] apply_subst_disjoint_id by auto
              then show ?thesis using val_typed CoreTm_Var ty_eq interp_result by simp
            qed
          next
            case (Some addrPath)
            (* Variable is a ref - need to dereference *)
            obtain addr path where addrPath_eq: "addrPath = (addr, path)"
              by (cases addrPath) auto
            (* Must be a local var *)
            from var_lookup obtain localTy where
              local_or_global: "fmlookup (TE_LocalVars env) varName = Some localTy \<or>
                fmlookup (TE_GlobalVars env) varName = Some localTy"
              and ty_local: "varTy = localTy"
              unfolding tyenv_lookup_var_def by (auto split: option.splits)
            (* It's in IS_Refs, so it must be a non-ghost local.
               Proof by contrapositive of no_extra_local_vars: if varName were not in
               TE_LocalVars (or were ghost), then it would not be in IS_Refs. *)
            from "1.prems"(1) have nel: "no_extra_local_vars state env"
              unfolding state_matches_env_def by simp
            from Some have refs_some: "fmlookup (IS_Refs state) varName \<noteq> None" by simp
            have local_lookup: "fmlookup (TE_LocalVars env) varName \<noteq> None"
            proof (rule ccontr)
              assume "\<not> fmlookup (TE_LocalVars env) varName \<noteq> None"
              hence "fmlookup (TE_LocalVars env) varName = None" by simp
              with nel have "fmlookup (IS_Refs state) varName = None"
                unfolding no_extra_local_vars_def by blast
              with refs_some show False by simp
            qed
            then obtain localTy' where local_eq: "fmlookup (TE_LocalVars env) varName = Some localTy'"
              by auto
            from "1.prems"(1) local_eq not_ghost
            have local_in_state: "local_var_in_state_with_type state env storeTyping varName localTy'"
              unfolding state_matches_env_def local_vars_exist_in_state_def
              by (metis no_extra_local_vars_def refs_some)
            from var_lookup local_eq have ty_eq': "varTy = localTy'"
              unfolding tyenv_lookup_var_def by simp
            from local_in_state None Some addrPath_eq have
              addr_valid: "addr < length (IS_Store state)" and
              path_ty: "type_at_path env (storeTyping ! addr) path
                          = Some (apply_subst (IS_TyArgs state) localTy')"
              unfolding local_var_in_state_with_type_def
              by (auto split: option.splits)
            from state_env addr_valid
            have slot_typed: "value_has_type env (IS_Store state ! addr) (storeTyping ! addr)"
              unfolding state_matches_env_def store_well_typed_def
              using "1.prems"(1) state_matches_env_def store_well_typed_def by blast
            show ?thesis
            proof (cases "get_value_at_path (IS_Store state ! addr) path")
              case (Inl err)
              \<comment> \<open>Dangling ref: by get_value_at_path_error_is_runtime, must be RuntimeError.\<close>
              from get_value_at_path_error_is_runtime[OF slot_typed path_ty Inl]
              have err_eq: "err = RuntimeError" .
              have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName) = Inl RuntimeError"
                using CoreTm_Var None Some addrPath_eq Inl err_eq by simp
              then show ?thesis using CoreTm_Var by simp
            next
              case (Inr v)
              \<comment> \<open>Live ref: by get_value_at_path_type, value has the (substituted) ref type.\<close>
              from get_value_at_path_type[OF slot_typed Inr] obtain pathTy where
                pathTy_eq: "type_at_path env (storeTyping ! addr) path = Some pathTy"
                and v_typed: "value_has_type env v pathTy"
                by auto
              from pathTy_eq path_ty
              have "value_has_type env v (apply_subst (IS_TyArgs state) localTy')"
                using v_typed by simp
              have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName) = Inr v"
                using CoreTm_Var None Some addrPath_eq Inr by simp
              then show ?thesis
                using \<open>value_has_type env v (apply_subst (IS_TyArgs state) localTy')\<close>
                      CoreTm_Var ty_eq ty_eq' by simp
            qed
          qed
        next
          case (Some addr)
          then have interp_result: "interp_term (Suc fuel) state (CoreTm_Var varName)
                                      = Inr (IS_Store state ! addr)"
            using CoreTm_Var by simp
          (* Must be a local var *)
          from var_lookup obtain localTy where
            local_eq: "fmlookup (TE_LocalVars env) varName = Some localTy"
            and local_ty: "varTy = localTy"
            unfolding tyenv_lookup_var_def
          proof (cases "fmlookup (TE_LocalVars env) varName")
            case lSome: (Some lt)
            then show ?thesis using that var_lookup unfolding tyenv_lookup_var_def by simp
          next
            case lNone: None
            (* If global, no_extra_global_vars says it's not in IS_Locals when ghost,
               and global_vars_exist says it's in IS_Globals. But we know it's in IS_Locals.
               From no_extra_local_vars: varName not in TE_LocalVars \<Longrightarrow> not in IS_Locals.
               Contradiction. *)
            from "1.prems"(1) lNone have "fmlookup (IS_Locals state) varName = None"
              unfolding state_matches_env_def no_extra_local_vars_def by simp
            with Some show ?thesis by simp
          qed
          from "1.prems"(1) local_eq not_ghost
          have local_in_state: "local_var_in_state_with_type state env storeTyping varName localTy"
            unfolding state_matches_env_def local_vars_exist_in_state_def
            by (simp add: tyenv_var_ghost_def)
          from local_in_state Some have addr_valid: "addr < length (IS_Store state)"
            and st_eq: "storeTyping ! addr = apply_subst (IS_TyArgs state) localTy"
            unfolding local_var_in_state_with_type_def by auto
          from "1.prems"(1) addr_valid
          have "value_has_type env (IS_Store state ! addr) (storeTyping ! addr)"
            unfolding state_matches_env_def store_well_typed_def by simp
          with st_eq
          have "value_has_type env (IS_Store state ! addr) (apply_subst (IS_TyArgs state) localTy)"
            by simp
          then show ?thesis
            using CoreTm_Var interp_result ty_eq local_ty by auto
        qed

      next
        (* Cast - use helper lemma *)
        case (CoreTm_Cast targetTy operandTm)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_cast typing by blast 

      next
        (* Unary operator - use helper lemma *)
        case (CoreTm_Unop op operandTm)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_unop typing by blast

      next
        (* Binary operator - use helper lemma *)
        case (CoreTm_Binop op lhsTm rhsTm)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_binop typing by blast
      next
        (* Let-binding - use helper lemma *)
        case (CoreTm_Let var rhsTm bodyTm)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_let typing by blast
      next
        case (CoreTm_Quantifier x91 x92 x93 x94)
        then show ?thesis using typing by simp
      next
        case (CoreTm_FunctionCall fnName tyArgs tmArgs)
        \<comment> \<open>Extract typing facts. We need all_var and not_impure below (for
            the purity proof), which are only produced on the pure path, so
            destructure core_term_type directly rather than via the shared
            helper. \<close>
        from typing CoreTm_FunctionCall obtain funInfo where
          fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
          len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
          tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
          all_var: "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)" and
          not_impure: "\<not> FI_Impure funInfo" and
          len_tmargs: "length tmArgs = length (FI_TmArgs funInfo)" and
          tyargs_rt: "list_all (is_runtime_type env) tyArgs" and
          ghost_ok2: "FI_Ghost funInfo \<noteq> Ghost"
          by (auto simp: Let_def split: option.splits if_splits)
        let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
        let ?expectedArgTypes = "map (\<lambda>(_, ty, _). apply_subst ?tySubst ty) (FI_TmArgs funInfo)"
        from typing CoreTm_FunctionCall fn_lookup len_tyargs tyargs_wk all_var not_impure
             len_tmargs tyargs_rt ghost_ok2 have
          args_check: "list_all2 (\<lambda>tm expectedTy.
              case core_term_type env NotGhost tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
            tmArgs ?expectedArgTypes" and
          ty_eq: "ty = apply_subst ?tySubst (FI_ReturnType funInfo)"
          by (auto simp: Let_def split: if_splits)
        have fn_not_ghost: "FI_Ghost funInfo = NotGhost"
          using ghost_ok2 by (cases "FI_Ghost funInfo") auto
        \<comment> \<open>Vacuous lvalue obligation: all args are Var. \<close>
        have ref_lvalues: "\<forall>i < length tmArgs.
                            snd (snd (FI_TmArgs funInfo ! i)) = Ref
                              \<longrightarrow> is_writable_lvalue env (tmArgs ! i)"
        proof (intro allI impI)
          fix i assume i_lt: "i < length tmArgs"
            and is_ref: "snd (snd (FI_TmArgs funInfo ! i)) = Ref"
          with len_tmargs have i_lt_fi: "i < length (FI_TmArgs funInfo)" by simp
          obtain n ti vor where fi_arg: "FI_TmArgs funInfo ! i = (n, ti, vor)"
            by (cases "FI_TmArgs funInfo ! i") auto
          from is_ref fi_arg have vor_eq: "vor = Ref" by simp
          from all_var i_lt_fi fi_arg
          have "(\<lambda>(_, _, vor). vor = Var) (n, ti, vor)"
            by (metis list_all_length)
          hence "vor = Var" by simp
          with vor_eq have False by simp
          thus "is_writable_lvalue env (tmArgs ! i)" by simp
        qed
        \<comment> \<open>Use interp_function_call_sound IH\<close>
        have IH_fc: "\<And>env' (state' :: 'w InterpState) storeTyping' fnName' argTms' funInfo' tyArgs' retTy'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                fmlookup (TE_Functions env') fnName' = Some funInfo' \<Longrightarrow>
                FI_Ghost funInfo' = NotGhost \<Longrightarrow>
                list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env' NotGhost tm of
                      None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  argTms' (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo') tyArgs')) ty)
                               (FI_TmArgs funInfo')) \<Longrightarrow>
                retTy' = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo') tyArgs')) (FI_ReturnType funInfo') \<Longrightarrow>
                length tyArgs' = length (FI_TyArgs funInfo') \<Longrightarrow>
                list_all (is_well_kinded env') tyArgs' \<Longrightarrow>
                list_all (is_runtime_type env') tyArgs' \<Longrightarrow>
                \<forall>i < length argTms'.
                  (snd (snd (FI_TmArgs funInfo' ! i)) = Ref \<longrightarrow>
                   is_writable_lvalue env' (argTms' ! i)) \<Longrightarrow>
                sound_function_call_result state' env' storeTyping' retTy' (interp_function_call fuel state' fnName' tyArgs' argTms')"
          using Suc.IH(6) by simp
        have fc_sound: "sound_function_call_result state env storeTyping ty
                          (interp_function_call fuel state fnName tyArgs tmArgs)"
          using IH_fc[OF "1.prems"(1,2) fn_lookup fn_not_ghost args_check ty_eq
                          len_tyargs tyargs_wk tyargs_rt ref_lvalues]
          by simp
        \<comment> \<open>The interpreter checks is_pure_fun then calls interp_function_call\<close>
        have pure: "is_pure_fun state fnName"
        proof -
          have "FI_Ghost funInfo = NotGhost" using ghost_ok2 by (cases "FI_Ghost funInfo") auto
          from "1.prems"(1) fn_lookup this obtain interpFun where
            if_lookup: "fmlookup (IS_Functions state) fnName = Some interpFun" and
            fi_match: "fun_info_matches_interp_fun env funInfo interpFun"
            unfolding state_matches_env_def funs_exist_in_state_def
            using case_optionE by blast
          from fi_match have vor_match: "list_all2 (\<lambda>(name1, _, vor1) (name2, vor2). name1 = name2 \<and> vor1 = vor2)
                                      (FI_TmArgs funInfo) (IF_Args interpFun)"
            unfolding fun_info_matches_interp_fun_def by auto
          from vor_match have len_eq: "length (FI_TmArgs funInfo) = length (IF_Args interpFun)"
            by (rule list_all2_lengthD)
          have "\<not> list_ex (\<lambda>(_, vr). vr = Ref) (IF_Args interpFun)"
          proof -
            have "\<And>i. i < length (IF_Args interpFun) \<Longrightarrow> snd (IF_Args interpFun ! i) = Var"
            proof -
              fix i assume i_bound: "i < length (IF_Args interpFun)"
              obtain n a b where nab: "FI_TmArgs funInfo ! i = (n, a, b)"
                by (cases "FI_TmArgs funInfo ! i") auto
              from vor_match i_bound len_eq nab
              have "b = snd (IF_Args interpFun ! i)"
                using list_all2_nthD by fastforce
              moreover have "b = Var"
                using all_var i_bound len_eq nab by (auto simp: list_all_length)
              ultimately show "snd (IF_Args interpFun ! i) = Var" by simp
            qed
            thus ?thesis
              by (fastforce simp: list_ex_iff in_set_conv_nth split: prod.splits)
          qed
          moreover from fi_match not_impure have "\<not> IF_Impure interpFun"
            unfolding fun_info_matches_interp_fun_def by simp
          ultimately show ?thesis using if_lookup by simp
        qed
        show ?thesis
        proof (cases "interp_function_call fuel state fnName tyArgs tmArgs")
          case (Inl err)
          from fc_sound Inl have "sound_error_result err" by simp
          moreover have "interp_term (Suc fuel) state tm = Inl err"
            using CoreTm_FunctionCall Inl pure by simp
          ultimately show ?thesis by simp
        next
          case (Inr result)
          obtain newState retVal where result_eq: "result = (newState, retVal)"
            by (cases result) auto
          from fc_sound Inr result_eq
          have "value_has_type env retVal (apply_subst (IS_TyArgs state) ty)" by simp
          moreover have "interp_term (Suc fuel) state tm = Inr retVal"
            using CoreTm_FunctionCall Inr result_eq pure by simp
          ultimately show ?thesis by simp
        qed
      next
        case (CoreTm_VariantCtor x111 x112 x113)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_variant_ctor typing by blast
      next
        case (CoreTm_Record x12)
        have IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results state' env' (map the types') (interp_term_list fuel state' tms')"
          by (simp add: Suc.IH(2) "1.prems"(1,2))
        from CoreTm_Record show ?thesis
          using type_soundness_record[OF "1.prems"(1,2) IH_list] typing
          by fastforce
      next
        case (CoreTm_RecordProj x131 x132)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_record_proj typing by blast
      next
        case (CoreTm_VariantProj x141 x142)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_variant_proj typing by blast
      next
        case (CoreTm_ArrayProj x151 x152)
        have IH_term: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_term_result state' env' ty' (interp_term fuel state' tm')"
          by (simp add: Suc.IH(1) "1.prems"(1,2))
        have IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results state' env' (map the types') (interp_term_list fuel state' tms')"
          by (simp add: Suc.IH(2) "1.prems"(1,2))
        from CoreTm_ArrayProj show ?thesis
          using type_soundness_array_proj[OF "1.prems"(1,2) IH_term IH_list] typing
          by fastforce
      next
        case (CoreTm_Match x161 x162)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_match typing by blast
      next
        case (CoreTm_Sizeof x17)
        then show ?thesis
          using "1.prems"(1,2) Suc.IH(1) type_soundness_sizeof typing by blast
      next
        case (CoreTm_Allocated x18)
        then show ?thesis using typing by simp
      next
        case (CoreTm_Old x19)
        then show ?thesis using typing by simp
      next
        case (CoreTm_Default x20)
        then show ?thesis
          using "1.prems"(1,2) type_soundness_default typing by blast
      qed
    qed
  next
    (* interp_term_list_sound *)
    case 2
    show ?case proof (intro impI, elim conjE)
      assume types_eq: "map (core_term_type env NotGhost) tms = types"
         and all_typed: "list_all (\<lambda>ty. ty \<noteq> None) types"
      show "sound_term_results state env (map the types) (interp_term_list (Suc fuel) state tms)"
      proof (cases tms)
        case Nil
        then have "interp_term_list (Suc fuel) state tms = Inr []" by simp
        moreover from Nil types_eq have "map the types = []" by simp
        ultimately show ?thesis by simp
      next
        case (Cons tm tms')
        (* Get typing for head and tail *)
        from types_eq Cons obtain types' where
          types_cons: "types = core_term_type env NotGhost tm # types'"
          and types'_eq: "map (core_term_type env NotGhost) tms' = types'"
          by auto
        from all_typed types_cons have
          tm_typed_opt: "core_term_type env NotGhost tm \<noteq> None"
          and all_typed': "list_all (\<lambda>ty. ty \<noteq> None) types'"
          by auto
        from tm_typed_opt obtain tm_ty where
          tm_typing: "core_term_type env NotGhost tm = Some tm_ty"
          by auto

        (* Use IH for the head term *)
        have head_sound: "sound_term_result state env tm_ty (interp_term fuel state tm)"
          using tm_typing
          using "2.prems"(1,2) Suc.IH(1) by auto

        (* Use IH for the tail list *)
        have tail_sound: "sound_term_results state env (map the types') (interp_term_list fuel state tms')"
          using "2.prems"(1,2) Suc.IH(2) all_typed' types'_eq by auto

        (* Case split on head evaluation *)
        show ?thesis
        proof (cases "interp_term fuel state tm")
          case (Inl err)
          (* Head failed - propagate error *)
          from head_sound Inl have "sound_error_result err" by simp
          moreover have "interp_term_list (Suc fuel) state tms = Inl err"
            using Cons Inl by simp
          ultimately show ?thesis by simp
        next
          case (Inr val)
          (* Head succeeded *)
          from head_sound Inr
          have val_typed: "value_has_type env val (apply_subst (IS_TyArgs state) tm_ty)" by simp
          (* Case split on tail evaluation *)
          show ?thesis
          proof (cases "interp_term_list fuel state tms'")
            case (Inl err)
            (* Tail failed - propagate error *)
            from tail_sound Inl have "sound_error_result err" by simp
            moreover have "interp_term_list (Suc fuel) state tms = Inl err"
              using Cons Inr Inl by simp
            ultimately show ?thesis by simp
          next
            case (Inr vals)
            (* Both succeeded *)
            from tail_sound Inr
            have vals_typed: "list_all2 (value_has_type env) vals
                                (map (apply_subst (IS_TyArgs state)) (map the types'))" by simp
            have result: "interp_term_list (Suc fuel) state tms = Inr (val # vals)"
              using Cons \<open>interp_term fuel state tm = Inr val\<close> Inr by simp
            have "map the types = tm_ty # map the types'"
              using types_cons tm_typing by simp
            with val_typed vals_typed result show ?thesis by simp
          qed
        qed
      qed
    qed
  next
    (* interp_writable_lvalue_sound *)
    case 3
    show ?case proof (intro impI, elim conjE)
      assume writable: "is_writable_lvalue env tm"
        and typing: "core_term_type env NotGhost tm = Some ty"

      have IH_lvalue: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                is_writable_lvalue env' tm' \<and> core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                sound_lvalue_result state' env' storeTyping' ty' (interp_writable_lvalue fuel state' tm')"
        by (simp add: Suc.IH(3) "3.prems"(1,2))

      have IH_list: "\<And>env' (state' :: 'w InterpState) storeTyping' tms' types'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                map (core_term_type env' NotGhost) tms' = types' \<and>
                list_all (\<lambda>ty. ty \<noteq> None) types' \<Longrightarrow>
                sound_term_results state' env' (map the types') (interp_term_list fuel state' tms')"
        by (simp add: Suc.IH(2) "3.prems"(1,2))

      show "sound_lvalue_result state env storeTyping ty (interp_writable_lvalue (Suc fuel) state tm)"
      proof (cases tm)
        (* CoreTm_Var: base case for lvalues *)
        case (CoreTm_Var varName)
        from typing CoreTm_Var obtain varTy where
          var_lookup: "tyenv_lookup_var env varName = Some varTy" and
          not_ghost: "\<not> tyenv_var_ghost env varName" and
          ty_eq: "ty = varTy"
          by (auto split: option.splits if_splits)
        (* Variable is writable, so it must be a non-const local *)
        from writable CoreTm_Var have writable_var: "tyenv_var_writable env varName" by simp
        hence local_lookup: "fmlookup (TE_LocalVars env) varName \<noteq> None"
          and not_const: "varName |\<notin>| TE_ConstLocals env"
          unfolding tyenv_var_writable_def by auto
        (* Since it's a local, not_ghost means not in TE_GhostLocals *)
        from not_ghost local_lookup have not_ghost_local: "varName |\<notin>| TE_GhostLocals env"
          unfolding tyenv_var_ghost_def by (auto split: option.splits)
        (* Variable is in IS_Locals or IS_Refs *)
        from "3.prems"(1) local_lookup not_ghost_local not_const
        have in_locals_or_refs:
          "fmlookup (IS_Locals state) varName \<noteq> None \<or>
           fmlookup (IS_Refs state) varName \<noteq> None"
          unfolding state_matches_env_def non_consts_in_locals_or_refs_def
          using local_vars_exist_in_state_implies_non_consts_in_locals_or_refs
            non_consts_in_locals_or_refs_def by blast
        (* Variable has correct type in state as a local *)
        from local_lookup obtain localTy where
          local_lookup_eq: "fmlookup (TE_LocalVars env) varName = Some localTy" by auto
        from var_lookup local_lookup_eq have ty_local: "localTy = varTy"
          unfolding tyenv_lookup_var_def by simp
        have var_in_state: "local_var_in_state_with_type state env storeTyping varName ty"
          using "3.prems"(1) local_lookup_eq not_ghost ty_eq ty_local
          unfolding state_matches_env_def local_vars_exist_in_state_def
          by (simp add: not_ghost_local)
        from "3.prems"(1) not_const have not_const_state: "varName |\<notin>| IS_ConstLocals state"
          unfolding state_matches_env_def const_locals_match_def by simp
        show ?thesis
        proof (cases "fmlookup (IS_Locals state) varName")
          case (Some addr)
          then have interp_eq: "interp_writable_lvalue (Suc fuel) state tm = Inr (addr, [])"
            using CoreTm_Var not_const_state by simp
          from var_in_state Some have
            addr_valid: "addr < length (IS_Store state)" and
            st_eq: "storeTyping ! addr = apply_subst (IS_TyArgs state) ty"
            unfolding local_var_in_state_with_type_def by auto
          from st_eq have "type_at_path env (storeTyping ! addr) []
                              = Some (apply_subst (IS_TyArgs state) ty)" by simp
          with interp_eq addr_valid show ?thesis by simp
        next
          case None
          (* Must be in IS_Refs *)
          from in_locals_or_refs None have "fmlookup (IS_Refs state) varName \<noteq> None" by simp
          then obtain addrPath where refs_lookup: "fmlookup (IS_Refs state) varName = Some addrPath"
            by auto
          obtain addr path where addrPath_eq: "addrPath = (addr, path)"
            by (cases addrPath) auto
          then have interp_eq: "interp_writable_lvalue (Suc fuel) state tm = Inr (addr, path)"
            using CoreTm_Var None refs_lookup not_const_state by simp
          from var_in_state None refs_lookup addrPath_eq have
            addr_valid: "addr < length (IS_Store state)" and
            path_ty: "type_at_path env (storeTyping ! addr) path
                         = Some (apply_subst (IS_TyArgs state) ty)"
            unfolding local_var_in_state_with_type_def
            by (auto split: option.splits)
          with interp_eq show ?thesis by simp
        qed
      next
        (* CoreTm_RecordProj: extend path with record field *)
        case (CoreTm_RecordProj innerTm fldName)
        from typing CoreTm_RecordProj obtain fieldTypes where
          inner_typing: "core_term_type env NotGhost innerTm = Some (CoreTy_Record fieldTypes)" and
          fld_lookup: "map_of fieldTypes fldName = Some ty"
          by (auto split: option.splits CoreType.splits)
        from writable CoreTm_RecordProj have inner_writable: "is_writable_lvalue env innerTm"
          by simp
        from IH_lvalue[OF "3.prems"(1,2)] inner_writable inner_typing
        have inner_sound: "sound_lvalue_result state env storeTyping (CoreTy_Record fieldTypes)
                             (interp_writable_lvalue fuel state innerTm)"
          by simp
        show ?thesis
        proof (cases "interp_writable_lvalue fuel state innerTm")
          case (Inl err)
          then have "interp_writable_lvalue (Suc fuel) state tm = Inl err"
            using CoreTm_RecordProj by simp
          with inner_sound Inl show ?thesis by auto
        next
          case (Inr addrPath)
          obtain addr path where ap_eq: "addrPath = (addr, path)" by (cases addrPath) auto
          let ?s = "IS_TyArgs state"
          let ?subFieldTypes = "map (\<lambda>(name, ty). (name, apply_subst ?s ty)) fieldTypes"
          from inner_sound Inr ap_eq have
            addr_valid: "addr < length (IS_Store state)" and
            inner_path_ty: "type_at_path env (storeTyping ! addr) path
                              = Some (CoreTy_Record ?subFieldTypes)"
            by auto
          have interp_eq: "interp_writable_lvalue (Suc fuel) state tm =
              Inr (addr, path @ [LVPath_RecordProj fldName])"
            using CoreTm_RecordProj Inr ap_eq by simp
          (* fld_lookup lifted through the substitution on field types. *)
          have fld_lookup_sub:
            "map_of ?subFieldTypes fldName = Some (apply_subst ?s ty)"
            using fld_lookup by (induction fieldTypes) auto
          (* type_at_path extends: appending a RecordProj step descends into fieldTypes *)
          have "type_at_path env (storeTyping ! addr)
                  (path @ [LVPath_RecordProj fldName]) = Some (apply_subst ?s ty)"
            using type_at_path_append[OF inner_path_ty] fld_lookup_sub by simp
          with interp_eq addr_valid show ?thesis by simp
        qed
      next
        (* CoreTm_VariantProj: extend path with variant projection *)
        case (CoreTm_VariantProj innerTm ctorName)
        from typing CoreTm_VariantProj obtain dtName tyArgs dtName2 tyvars payloadTy where
          inner_typing: "core_term_type env NotGhost innerTm = Some (CoreTy_Datatype dtName tyArgs)" and
          ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, tyvars, payloadTy)" and
          dt_eq: "dtName = dtName2" and
          len_eq: "length tyArgs = length tyvars" and
          ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
          by (auto split: option.splits CoreType.splits prod.splits if_splits)
        from writable CoreTm_VariantProj have inner_writable: "is_writable_lvalue env innerTm"
          by simp
        from IH_lvalue[OF "3.prems"(1,2)] inner_writable inner_typing
        have inner_sound: "sound_lvalue_result state env storeTyping (CoreTy_Datatype dtName tyArgs)
                             (interp_writable_lvalue fuel state innerTm)"
          by simp
        show ?thesis
        proof (cases "interp_writable_lvalue fuel state innerTm")
          case (Inl err)
          then have "interp_writable_lvalue (Suc fuel) state tm = Inl err"
            using CoreTm_VariantProj by simp
          with inner_sound Inl show ?thesis by auto
        next
          case (Inr addrPath)
          obtain addr path where ap_eq: "addrPath = (addr, path)" by (cases addrPath) auto
          let ?s = "IS_TyArgs state"
          let ?subTyArgs = "map (apply_subst ?s) tyArgs"
          from inner_sound Inr ap_eq have
            addr_valid: "addr < length (IS_Store state)" and
            inner_path_ty: "type_at_path env (storeTyping ! addr) path
                            = Some (CoreTy_Datatype dtName ?subTyArgs)"
            by auto
          have interp_eq: "interp_writable_lvalue (Suc fuel) state tm =
              Inr (addr, path @ [LVPath_VariantProj ctorName])"
            using CoreTm_VariantProj Inr ap_eq by simp
          (* Lift apply_subst outside via apply_subst_compose_zip. *)
          have payloads_wk: "tyenv_payloads_well_kinded env"
            using wf_env tyenv_well_formed_def "3.prems"(2) by simp
          have ctor_distinct: "tyenv_ctor_tyvars_distinct env"
            using wf_env tyenv_well_formed_def "3.prems"(2) by simp
          from payloads_wk ctor_lookup
          have payload_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
            unfolding tyenv_payloads_well_kinded_def by blast
          have payload_tyvars_sub: "type_tyvars payloadTy \<subseteq> set tyvars"
            using is_well_kinded_type_tyvars_subset[OF payload_wk]
            by (simp add: fset_of_list.rep_eq)
          from ctor_distinct ctor_lookup have tyvars_distinct: "distinct tyvars"
            unfolding tyenv_ctor_tyvars_distinct_def by blast
          have compose_eq:
            "apply_subst (fmap_of_list (zip tyvars ?subTyArgs)) payloadTy
               = apply_subst ?s (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
            using apply_subst_compose_zip[OF len_eq[symmetric] payload_tyvars_sub tyvars_distinct] .
          (* Append the variant projection step to the path *)
          have "type_at_path env (storeTyping ! addr)
                  (path @ [LVPath_VariantProj ctorName]) = Some (apply_subst ?s ty)"
            using type_at_path_append[OF inner_path_ty] ctor_lookup dt_eq ty_eq compose_eq
            by simp
          with interp_eq addr_valid show ?thesis by simp
        qed
      next
        (* CoreTm_ArrayProj: extend path with array index *)
        case (CoreTm_ArrayProj innerTm idxTms)
        from typing CoreTm_ArrayProj obtain elemTy dims where
          inner_typing: "core_term_type env NotGhost innerTm = Some (CoreTy_Array elemTy dims)" and
          len_eq: "length idxTms = length dims" and
          idxs_typed: "list_all (\<lambda>tm. core_term_type env NotGhost tm
                          = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
          ty_eq: "ty = elemTy"
          by (auto split: option.splits CoreType.splits if_splits)
        from writable CoreTm_ArrayProj have inner_writable: "is_writable_lvalue env innerTm"
          by simp
        from IH_lvalue[OF "3.prems"(1,2)] inner_writable inner_typing
        have inner_sound: "sound_lvalue_result state env storeTyping (CoreTy_Array elemTy dims)
                             (interp_writable_lvalue fuel state innerTm)"
          by simp
        (* Index terms *)
        let ?types = "map (core_term_type env NotGhost) idxTms"
        from idxs_typed have types_all_some: "list_all (\<lambda>ty. ty \<noteq> None) ?types"
          by (simp add: list_all_length)
        from IH_list[OF "3.prems"(1,2)] types_all_some
        have idx_sound: "sound_term_results state env (map the ?types) (interp_term_list fuel state idxTms)"
          by simp
        from idxs_typed have map_the_types: "map the ?types =
            replicate (length idxTms) (CoreTy_FiniteInt Unsigned IntBits_64)"
          by (induction idxTms) (auto simp: list_all_iff)
        show ?thesis
        proof (cases "interp_writable_lvalue fuel state innerTm")
          case (Inl err)
          then have "interp_writable_lvalue (Suc fuel) state tm = Inl err"
            using CoreTm_ArrayProj by simp
          with inner_sound Inl show ?thesis by auto
        next
          case (Inr addrPath)
          obtain addr path where ap_eq: "addrPath = (addr, path)" by (cases addrPath) auto
          let ?s = "IS_TyArgs state"
          from inner_sound Inr ap_eq have
            addr_valid: "addr < length (IS_Store state)" and
            inner_path_ty: "type_at_path env (storeTyping ! addr) path
                            = Some (CoreTy_Array (apply_subst ?s elemTy) dims)"
            by auto
          show ?thesis
          proof (cases "interp_term_list fuel state idxTms")
            case (Inl err)
            then have "interp_writable_lvalue (Suc fuel) state tm = Inl err"
              using CoreTm_ArrayProj \<open>interp_writable_lvalue fuel state innerTm = Inr addrPath\<close>
                    ap_eq by simp
            with idx_sound Inl show ?thesis by auto
          next
            case (Inr idxVals)
            (* u64 is ground so map (apply_subst _) (replicate _ u64) = replicate _ u64. *)
            have map_the_types_sub:
              "map (apply_subst ?s \<circ> (the \<circ> core_term_type env NotGhost)) idxTms
                 = replicate (length idxTms) (CoreTy_FiniteInt Unsigned IntBits_64)"
              using map_the_types by (simp flip: map_map)
            from idx_sound Inr map_the_types_sub
            have idxVals_typed: "list_all2 (value_has_type env) idxVals
                (replicate (length idxTms) (CoreTy_FiniteInt Unsigned IntBits_64))"
              by simp
            from interpret_index_vals_u64[OF idxVals_typed]
            obtain indices where interp_idx_eq: "interpret_index_vals idxVals = Inr indices" by auto
            have interp_eq: "interp_writable_lvalue (Suc fuel) state tm =
                Inr (addr, path @ [LVPath_ArrayProj indices])"
              using CoreTm_ArrayProj \<open>interp_writable_lvalue fuel state innerTm = Inr addrPath\<close>
                    ap_eq Inr interp_idx_eq by simp
            (* Append the array projection step to the path *)
            have "type_at_path env (storeTyping ! addr)
                    (path @ [LVPath_ArrayProj indices]) = Some (apply_subst ?s ty)"
              using type_at_path_append[OF inner_path_ty] ty_eq by simp
            with interp_eq addr_valid show ?thesis by simp
          qed
        qed
      (* Non-lvalue cases are contradictions since is_writable_lvalue returns False *)
      qed (use writable in \<open>simp_all\<close>)
    qed
  next
    case 4
    show ?case proof (intro impI)
      assume typing: "core_statement_type env NotGhost stmt = Some env'"
      have IH_term: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 tm0 ty0.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                core_term_type env0 NotGhost tm0 = Some ty0 \<Longrightarrow>
                sound_term_result state0 env0 ty0 (interp_term fuel state0 tm0)"
        by (simp add: "4.prems"(1,2) Suc.IH(1))
      have IH_lvalue: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 tm0 ty0.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                is_writable_lvalue env0 tm0 \<and> core_term_type env0 NotGhost tm0 = Some ty0 \<Longrightarrow>
                sound_lvalue_result state0 env0 storeTyping0 ty0 (interp_writable_lvalue fuel state0 tm0)"
        by (simp add: "4.prems"(1,2) Suc.IH(3))
      have IH_fc: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 fnName0 argTms0 funInfo0 tyArgs0 retTy0.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                fmlookup (TE_Functions env0) fnName0 = Some funInfo0 \<Longrightarrow>
                FI_Ghost funInfo0 = NotGhost \<Longrightarrow>
                list_all2 (\<lambda>tm expectedTy.
                    case core_term_type env0 NotGhost tm of
                      None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                  argTms0 (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo0) tyArgs0)) ty)
                               (FI_TmArgs funInfo0)) \<Longrightarrow>
                retTy0 = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo0) tyArgs0)) (FI_ReturnType funInfo0) \<Longrightarrow>
                length tyArgs0 = length (FI_TyArgs funInfo0) \<Longrightarrow>
                list_all (is_well_kinded env0) tyArgs0 \<Longrightarrow>
                list_all (is_runtime_type env0) tyArgs0 \<Longrightarrow>
                \<forall>i < length argTms0.
                  (snd (snd (FI_TmArgs funInfo0 ! i)) = Ref \<longrightarrow>
                   is_writable_lvalue env0 (argTms0 ! i)) \<Longrightarrow>
                sound_function_call_result state0 env0 storeTyping0 retTy0 (interp_function_call fuel state0 fnName0 tyArgs0 argTms0)"
        using Suc.IH(6) by simp
      show "sound_statement_result env env' storeTyping (interp_statement (Suc fuel) state stmt)"
      proof (cases stmt)
        case (CoreStmt_VarDecl declGhost varName varOrRef varTy initTm)
        then show ?thesis proof (cases varOrRef)
          case Var
          then show ?thesis proof (cases declGhost)
            case NotGhost
            \<comment> \<open>NotGhost Var VarDecl: the initializer is an ordinary (pure) term;
                evaluate it via interp_term, then alloc_store + fmupd the new
                local. (Impure-call initializers use CoreStmt_VarDeclCall.) \<close>
            from typing CoreStmt_VarDecl Var NotGhost have init_ty:
              "core_term_type env NotGhost initTm = Some varTy"
              by (auto split: if_splits)
            from typing CoreStmt_VarDecl Var NotGhost have env'_eq:
              "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                            TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                            TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
              by (auto split: if_splits)
            from IH_term[OF "4.prems"(1,2) init_ty]
            have init_sound: "sound_term_result state env varTy (interp_term fuel state initTm)" .
            show ?thesis
            proof (cases "interp_term fuel state initTm")
              case (Inl err)
              with init_sound have err_sound: "sound_error_result err" by simp
              from Inl have interp_err:
                "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Var varTy initTm) = Inl err"
                by simp
              with err_sound CoreStmt_VarDecl Var NotGhost show ?thesis by simp
            next
              case (Inr initialVal)
              from init_sound Inr
              have val_typed: "value_has_type env initialVal
                                 (apply_subst (IS_TyArgs state) varTy)" by simp
              obtain state' addr where alloc_eq: "(state', addr) = alloc_store state initialVal"
                by (cases "alloc_store state initialVal") auto
              let ?state'' = "state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state'),
                                       IS_Refs := fmdrop varName (IS_Refs state'),
                                       IS_ConstLocals := fminus (IS_ConstLocals state') {|varName|} \<rparr>"
              have interp_eq: "interp_statement (Suc fuel) state
                  (CoreStmt_VarDecl NotGhost varName Var varTy initTm) =
                  Inr (Continue ?state'')"
                using Inr alloc_eq by (simp add: case_prod_beta)
              let ?subVarTy = "apply_subst (IS_TyArgs state) varTy"
              have new_sme: "state_matches_env ?state'' env' (storeTyping @ [?subVarTy])"
                using state_matches_env_add_nonconst_local[OF "4.prems"(1) val_typed
                    alloc_eq refl env'_eq] .
              have ext: "storeTyping_extends storeTyping (storeTyping @ [?subVarTy])"
                using storeTyping_extends_append .
              from new_sme ext interp_eq CoreStmt_VarDecl Var NotGhost
              show ?thesis by auto
            qed
          next
            case Ghost
            \<comment> \<open>Ghost Var VarDecl: interpreter drops the variable from IS_Locals/IS_Refs\<close>
            (* Extract facts from typechecking *)
            from typing CoreStmt_VarDecl Var Ghost have
              env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := finsert varName (TE_GhostLocals env),
                                     TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
              by (auto split: if_splits)
            (* The interpreter drops varName from IS_Locals, IS_Refs, IS_ConstLocals *)
            let ?state' = "state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
                                   IS_Refs := fmdrop varName (IS_Refs state),
                                   IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"
            have interp_eq: "interp_statement (Suc fuel) state
                (CoreStmt_VarDecl Ghost varName Var varTy initTm) = Inr (Continue ?state')"
              by simp
            (* Prove state_matches_env for the modified state and extended env.
               varName is ghost in env', so it must be absent from IS_Locals/IS_Refs
               (which fmdrop ensures). All other variables are unchanged. *)
            from "4.prems"(1) have
              old_sme: "state_matches_env state env storeTyping" .
            have "state_matches_env ?state' env' storeTyping"
              using state_matches_env_add_ghost_local[OF old_sme env'_eq refl] .
            with CoreStmt_VarDecl Var Ghost show ?thesis
              using interp_eq storeTyping_extends_refl by auto
          qed
        next
          case Ref
          \<comment> \<open>Ref VarDecl: three branches.
              - Ghost: interpreter drops varName from IS_Locals/IS_Refs/IS_ConstLocals.
              - NotGhost + base read-only (in IS_ConstLocals or IS_Globals): copy path,
                use IH_term to get the value, alloc_store, add to IS_ConstLocals.
              - NotGhost + base writable: alias path, use IH_lvalue to get (addr, path),
                update IS_Refs.
              The typechecker decides const-vs-non-const at compile time, but we have to
              show the interpreter's runtime branch matches the static decision. \<close>
          show ?thesis proof (cases declGhost)
            case Ghost
            from typing CoreStmt_VarDecl Ref Ghost have
              env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := finsert varName (TE_GhostLocals env),
                                     TE_ConstLocals := (if is_writable_lvalue env initTm
                                                       then fminus (TE_ConstLocals env) {|varName|}
                                                       else finsert varName (TE_ConstLocals env)) \<rparr>"
              by (auto split: if_splits)
            \<comment> \<open>The interpreter drops varName from IS_Locals, IS_Refs, IS_ConstLocals. \<close>
            let ?state' = "state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
                                   IS_Refs := fmdrop varName (IS_Refs state),
                                   IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"
            have interp_eq: "interp_statement (Suc fuel) state
                (CoreStmt_VarDecl Ghost varName Ref varTy initTm) = Inr (Continue ?state')"
              by simp
            from "4.prems"(1) have
              old_sme: "state_matches_env state env storeTyping" .
            have tyargs_eq [simp]: "IS_TyArgs ?state' = IS_TyArgs state" by simp
            have env'_fields: "TE_DataCtors env' = TE_DataCtors env"
                              "TE_Datatypes env' = TE_Datatypes env"
                              "TE_TypeVars env' = TE_TypeVars env"
                              "TE_GhostDatatypes env' = TE_GhostDatatypes env"
                              "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
              using env'_eq by simp_all
            have vht_eq: "\<And>v t. value_has_type env' v t = value_has_type env v t"
              using value_has_type_cong_env[OF env'_fields] .
            have tap_eq: "\<And>t p. type_at_path env t p = type_at_path env' t p"
              using type_at_path_cong_env[OF env'_fields(1)] .
            have "state_matches_env ?state' env' storeTyping"
              unfolding state_matches_env_def
            proof (intro conjI)
              show "local_vars_exist_in_state ?state' env' storeTyping"
                unfolding local_vars_exist_in_state_def
              proof (intro allI impI, elim conjE)
                fix name ty
                assume lk: "fmlookup (TE_LocalVars env') name = Some ty"
                  and ng: "name |\<notin>| TE_GhostLocals env'"
                from ng env'_eq have "name \<noteq> varName" by auto
                with lk env'_eq have lk_old: "fmlookup (TE_LocalVars env) name = Some ty" by simp
                from ng env'_eq \<open>name \<noteq> varName\<close> have ng_old: "name |\<notin>| TE_GhostLocals env" by auto
                from old_sme lk_old ng_old
                have "local_var_in_state_with_type state env storeTyping name ty"
                  unfolding state_matches_env_def local_vars_exist_in_state_def by blast
                with \<open>name \<noteq> varName\<close> tap_eq show "local_var_in_state_with_type ?state' env' storeTyping name ty"
                  unfolding local_var_in_state_with_type_def Let_def
                  by (auto split: option.splits)
              qed
            next
              show "global_vars_exist_in_state ?state' env'"
              proof -
                from old_sme have old_gv: "global_vars_exist_in_state state env"
                  unfolding state_matches_env_def by simp
                have gv_eq: "TE_GlobalVars env' = TE_GlobalVars env" using env'_eq by simp
                have gg_eq: "TE_GhostGlobals env' = TE_GhostGlobals env" using env'_eq by simp
                show ?thesis unfolding global_vars_exist_in_state_def
                proof (intro allI impI, elim conjE)
                  fix name ty
                  assume lk: "fmlookup (TE_GlobalVars env') name = Some ty"
                    and ng: "name |\<notin>| TE_GhostGlobals env'"
                  from lk gv_eq have "fmlookup (TE_GlobalVars env) name = Some ty" by simp
                  moreover from ng gg_eq have "name |\<notin>| TE_GhostGlobals env" by simp
                  ultimately have "global_var_in_state_with_type state env name ty"
                    using old_gv unfolding global_vars_exist_in_state_def by blast
                  thus "global_var_in_state_with_type ?state' env' name ty"
                    using vht_eq unfolding global_var_in_state_with_type_def
                    by (auto split: option.splits)
                qed
              qed
            next
              show "no_extra_local_vars ?state' env'"
                unfolding no_extra_local_vars_def
              proof (intro allI impI)
                fix name
                assume ante: "fmlookup (TE_LocalVars env') name = None \<or> name |\<in>| TE_GhostLocals env'"
                show "fmlookup (IS_Locals ?state') name = None \<and>
                      fmlookup (IS_Refs ?state') name = None"
                proof (cases "name = varName")
                  case True
                  then show ?thesis by simp
                next
                  case False
                  from ante False env'_eq
                  have "fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env" by auto
                  with old_sme have "fmlookup (IS_Locals state) name = None \<and>
                      fmlookup (IS_Refs state) name = None"
                    unfolding state_matches_env_def no_extra_local_vars_def by blast
                  with False show ?thesis by simp
                qed
              qed
            next
              show "no_extra_global_vars ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def no_extra_global_vars_def by simp
            next
              show "funs_exist_in_state ?state' env'"
                unfolding funs_exist_in_state_def
              proof (intro allI impI, elim conjE)
                fix name info
                assume lk: "fmlookup (TE_Functions env') name = Some info"
                  and ng: "FI_Ghost info = NotGhost"
                from old_sme have old_fes: "funs_exist_in_state state env"
                  unfolding state_matches_env_def by simp
                have funs_eq: "TE_Functions env' = TE_Functions env" using env'_eq by simp
                from lk funs_eq have lk': "fmlookup (TE_Functions env) name = Some info" by simp
                from old_fes lk' ng obtain interpFun where
                  if_lk: "fmlookup (IS_Functions state) name = Some interpFun" and
                  matches: "fun_info_matches_interp_fun env info interpFun"
                  unfolding funs_exist_in_state_def by (auto split: option.splits)
                have if_lk': "fmlookup (IS_Functions ?state') name = Some interpFun"
                  using if_lk by simp
                have fcong: "fun_info_matches_interp_fun env' info interpFun =
                              fun_info_matches_interp_fun env info interpFun"
                  by (rule fun_info_matches_interp_fun_cong_env)
                     (use env'_eq in simp_all)
                have "fun_info_matches_interp_fun env' info interpFun"
                  using matches fcong by simp
                with if_lk' show "case fmlookup (IS_Functions ?state') name of
                                    None \<Rightarrow> False
                                  | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env' info interpFun"
                  by simp
              qed
            next
              show "no_extra_funs ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def no_extra_funs_def by simp
            next
              show "const_locals_match ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def const_locals_match_def
                by (auto split: if_splits)
            next
              show "store_well_typed ?state' env' storeTyping"
                using old_sme vht_eq
                unfolding state_matches_env_def store_well_typed_def by simp
            next
              have rt_eq: "\<And>ty. is_runtime_type env' ty = is_runtime_type env ty"
                by (rule is_runtime_type_cong_env) (use env'_fields in simp_all)
              have wk_eq: "\<And>ty. is_well_kinded env' ty = is_well_kinded env ty"
                by (rule is_well_kinded_cong_env) (use env'_fields in simp_all)
              show "ty_args_well_formed ?state' env'"
                using old_sme env'_fields rt_eq wk_eq
                unfolding state_matches_env_def ty_args_well_formed_def by simp
            next
              show "default_ctors_match ?state' env'"
                using old_sme env'_eq
                unfolding state_matches_env_def default_ctors_match_def by simp
            qed
            with CoreStmt_VarDecl Ref Ghost show ?thesis
              using interp_eq storeTyping_extends_refl by auto
          next
            case NotGhost
            from "4.prems"(1) have old_sme: "state_matches_env state env storeTyping" .
            \<comment> \<open>Extract typechecker facts. \<close>
            from typing CoreStmt_VarDecl Ref NotGhost have
              wk: "is_well_kinded env varTy" and
              rt: "is_runtime_type env varTy" and
              init_lvalue: "is_lvalue initTm" and
              init_ty: "core_term_type env NotGhost initTm = Some varTy" and
              env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                     TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                                     TE_ConstLocals := (if is_writable_lvalue env initTm
                                                       then fminus (TE_ConstLocals env) {|varName|}
                                                       else finsert varName (TE_ConstLocals env)) \<rparr>"
              by (auto split: if_splits)

            \<comment> \<open>The interpreter dispatches on lvalue_base_name initTm. is_lvalue ensures
                this is Some baseName. \<close>
            from init_lvalue obtain baseName where
              base_eq: "lvalue_base_name initTm = Some baseName"
              unfolding is_lvalue_def by (cases "lvalue_base_name initTm") auto

            \<comment> \<open>is_writable_lvalue reduces to tyenv_var_writable on the base. \<close>
            from init_lvalue base_eq have
              wl_iff: "is_writable_lvalue env initTm = tyenv_var_writable env baseName"
              by (induction initTm) (auto simp: is_lvalue_def)
            \<comment> \<open>From core_term_type env NotGhost initTm = Some varTy, derive that the
                lvalue base is non-ghost. We generalise the type in the induction. \<close>
            have base_not_ghost_aux:
              "\<And>ty. core_term_type env NotGhost tm = Some ty
                    \<Longrightarrow> lvalue_base_name tm = Some baseName
                    \<Longrightarrow> \<not> tyenv_var_ghost env baseName" for tm
              by (induction tm) (auto split: option.splits if_splits)
            from base_not_ghost_aux[OF init_ty base_eq] have base_not_ghost:
              "\<not> tyenv_var_ghost env baseName" .
            from old_sme have
              cn_match: "IS_ConstLocals state = fminus (TE_ConstLocals env) (TE_GhostLocals env)"
              unfolding state_matches_env_def const_locals_match_def by simp

            \<comment> \<open>The runtime predicate matches the static is_writable_lvalue predicate.
                Locals shadow globals, so the runtime check is on IS_Locals/IS_Refs. \<close>
            have static_writable_iff_runtime:
              "is_writable_lvalue env initTm
               \<longleftrightarrow> baseName |\<notin>| IS_ConstLocals state
                   \<and> (fmlookup (IS_Locals state) baseName \<noteq> None
                      \<or> fmlookup (IS_Refs state) baseName \<noteq> None)"
            proof
              assume writable: "is_writable_lvalue env initTm"
              with wl_iff have tvw: "tyenv_var_writable env baseName" by simp
              from tvw have
                in_locals: "fmlookup (TE_LocalVars env) baseName \<noteq> None" and
                not_const: "baseName |\<notin>| TE_ConstLocals env"
                unfolding tyenv_var_writable_def by simp_all
              from in_locals base_not_ghost have not_ghost: "baseName |\<notin>| TE_GhostLocals env"
                unfolding tyenv_var_ghost_def by auto
              from not_const cn_match have not_iconst: "baseName |\<notin>| IS_ConstLocals state"
                by auto
              from old_sme in_locals not_ghost not_const
              have in_state: "fmlookup (IS_Locals state) baseName \<noteq> None
                              \<or> fmlookup (IS_Refs state) baseName \<noteq> None"
                unfolding state_matches_env_def
                using local_vars_exist_in_state_implies_non_consts_in_locals_or_refs
                  non_consts_in_locals_or_refs_def by blast
              show "baseName |\<notin>| IS_ConstLocals state
                    \<and> (fmlookup (IS_Locals state) baseName \<noteq> None
                       \<or> fmlookup (IS_Refs state) baseName \<noteq> None)"
                using not_iconst in_state by simp
            next
              assume hyp: "baseName |\<notin>| IS_ConstLocals state
                           \<and> (fmlookup (IS_Locals state) baseName \<noteq> None
                              \<or> fmlookup (IS_Refs state) baseName \<noteq> None)"
              hence not_iconst: "baseName |\<notin>| IS_ConstLocals state"
                and in_state: "fmlookup (IS_Locals state) baseName \<noteq> None
                               \<or> fmlookup (IS_Refs state) baseName \<noteq> None" by simp_all
              \<comment> \<open>By no_extra_local_vars contrapositive: baseName in IS_Locals or IS_Refs
                  \<Longrightarrow> baseName \<in> TE_LocalVars (and \<notin> TE_GhostLocals). \<close>
              have in_locals: "fmlookup (TE_LocalVars env) baseName \<noteq> None"
              proof (rule ccontr)
                assume neg: "\<not> fmlookup (TE_LocalVars env) baseName \<noteq> None"
                hence "fmlookup (TE_LocalVars env) baseName = None
                       \<or> baseName |\<in>| TE_GhostLocals env" by simp
                with old_sme have "fmlookup (IS_Locals state) baseName = None
                                   \<and> fmlookup (IS_Refs state) baseName = None"
                  unfolding state_matches_env_def no_extra_local_vars_def by blast
                with in_state show False by simp
              qed
              from in_locals base_not_ghost have not_ghost: "baseName |\<notin>| TE_GhostLocals env"
                unfolding tyenv_var_ghost_def by auto
              from not_iconst cn_match not_ghost have not_const: "baseName |\<notin>| TE_ConstLocals env"
                by auto
              from in_locals not_const have "tyenv_var_writable env baseName"
                unfolding tyenv_var_writable_def by simp
              with wl_iff show "is_writable_lvalue env initTm" by simp
            qed

            show ?thesis
            proof (cases "is_writable_lvalue env initTm")
              case writable: True
              \<comment> \<open>Alias path: use IH_lvalue. The interpreter falls into the alias branch
                  since base is writable, so by static_writable_iff_runtime, base is not
                  in IS_ConstLocals and is in IS_Locals or IS_Refs. \<close>
              from writable static_writable_iff_runtime have
                base_not_const: "baseName |\<notin>| IS_ConstLocals state" and
                base_in_state: "fmlookup (IS_Locals state) baseName \<noteq> None
                                \<or> fmlookup (IS_Refs state) baseName \<noteq> None" by simp_all
              from IH_lvalue[OF "4.prems"(1,2) conjI[OF writable init_ty]]
              have lv_sound: "sound_lvalue_result state env storeTyping varTy
                  (interp_writable_lvalue fuel state initTm)" .
              show ?thesis
              proof (cases "interp_writable_lvalue fuel state initTm")
                case (Inl err)
                with lv_sound have err_sound: "sound_error_result err" by simp
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Ref varTy initTm) = Inl err"
                  using Inl base_eq base_not_const base_in_state by auto
                with err_sound CoreStmt_VarDecl Ref NotGhost show ?thesis by simp
              next
                case (Inr addrPath)
                obtain addr path where ap_eq: "addrPath = (addr, path)"
                  by (cases addrPath) auto
                from lv_sound Inr ap_eq have
                  addr_valid: "addr < length (IS_Store state)" and
                  path_ty: "type_at_path env (storeTyping ! addr) path
                              = Some (apply_subst (IS_TyArgs state) varTy)"
                  by auto
                let ?state' = "state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
                                       IS_Refs := fmupd varName (addr, path) (IS_Refs state),
                                       IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"
                have interp_eq: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Ref varTy initTm) = Inr (Continue ?state')"
                  using Inr ap_eq base_eq base_not_const base_in_state by auto
                \<comment> \<open>var_fresh and var_not_ghost preconditions for state_matches_env_add_ref. \<close>
                from "4.prems"(2) have wf: "tyenv_well_formed env" .
                from old_sme have nc_invariant: "non_consts_in_locals_or_refs state env"
                  using local_vars_exist_in_state_implies_non_consts_in_locals_or_refs state_matches_env_def
                  by blast

                \<comment> \<open>We need varName \<notin> TE_LocalVars and varName \<notin> TE_GhostLocals. These come
                    from tyenv well-formedness applied to env'? No — env' adds varName to
                    TE_LocalVars, so we need that varName is fresh in env. Hmm — actually,
                    the typechecker doesn't enforce freshness; shadowing is permitted.
                    state_matches_env_add_ref's var_fresh precondition is too strong.

                    Workaround: use state_matches_env directly without going through the
                    helper, or relax the helper to not require var_fresh. \<close>
                \<comment> \<open>Easier: prove state_matches_env directly, similar to the Ghost case but
                    with the new addr/path entry in IS_Refs. \<close>
                have env'_writable_eq:
                  "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                                TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
                  using env'_eq writable by simp
                have env'_fields: "TE_DataCtors env' = TE_DataCtors env"
                                  "TE_Datatypes env' = TE_Datatypes env"
                                  "TE_TypeVars env' = TE_TypeVars env"
                                  "TE_GhostDatatypes env' = TE_GhostDatatypes env"
                                  "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
                  using env'_writable_eq by simp_all
                have vht_eq: "\<And>v t. value_has_type env' v t = value_has_type env v t"
                  using value_has_type_cong_env[OF env'_fields] .
                have tap_eq: "\<And>t p. type_at_path env t p = type_at_path env' t p"
                  using type_at_path_cong_env[OF env'_fields(1)] .
                have new_sme: "state_matches_env ?state' env' storeTyping"
                  unfolding state_matches_env_def
                proof (intro conjI)
                  show "local_vars_exist_in_state ?state' env' storeTyping"
                    unfolding local_vars_exist_in_state_def
                  proof (intro allI impI, elim conjE)
                    fix name ty
                    assume lk: "fmlookup (TE_LocalVars env') name = Some ty"
                      and ng: "name |\<notin>| TE_GhostLocals env'"
                    show "local_var_in_state_with_type ?state' env' storeTyping name ty"
                    proof (cases "name = varName")
                      case True
                      from lk env'_writable_eq True have ty_eq: "ty = varTy" by simp
                      have lk_locals: "fmlookup (IS_Locals ?state') varName = None" by simp
                      have lk_refs: "fmlookup (IS_Refs ?state') varName = Some (addr, path)" by simp
                      have tyargs_eq: "IS_TyArgs ?state' = IS_TyArgs state" by simp
                      have path_ty': "type_at_path env' (storeTyping ! addr) path
                                        = Some (apply_subst (IS_TyArgs ?state') varTy)"
                        using path_ty tap_eq tyargs_eq by simp
                      show ?thesis
                        using True ty_eq lk_locals lk_refs addr_valid path_ty'
                        unfolding local_var_in_state_with_type_def by simp
                    next
                      case False
                      from lk env'_writable_eq False have lk_old: "fmlookup (TE_LocalVars env) name = Some ty" by simp
                      from ng env'_writable_eq False have ng_old: "name |\<notin>| TE_GhostLocals env" by auto
                      from old_sme lk_old ng_old
                      have old: "local_var_in_state_with_type state env storeTyping name ty"
                        unfolding state_matches_env_def local_vars_exist_in_state_def by blast
                      from False have lk_lo: "fmlookup (IS_Locals ?state') name = fmlookup (IS_Locals state) name"
                        by simp
                      from False have lk_re: "fmlookup (IS_Refs ?state') name = fmlookup (IS_Refs state) name"
                        by simp
                      show ?thesis
                        using old lk_lo lk_re tap_eq
                        unfolding local_var_in_state_with_type_def Let_def
                        by (auto split: option.splits)
                    qed
                  qed
                next
                  show "global_vars_exist_in_state ?state' env'"
                  proof -
                    from old_sme have old_gv: "global_vars_exist_in_state state env"
                      unfolding state_matches_env_def by simp
                    have gv_eq: "TE_GlobalVars env' = TE_GlobalVars env" using env'_writable_eq by simp
                    have gg_eq: "TE_GhostGlobals env' = TE_GhostGlobals env" using env'_writable_eq by simp
                    show ?thesis unfolding global_vars_exist_in_state_def
                    proof (intro allI impI, elim conjE)
                      fix name ty
                      assume "fmlookup (TE_GlobalVars env') name = Some ty"
                        and "name |\<notin>| TE_GhostGlobals env'"
                      hence "fmlookup (TE_GlobalVars env) name = Some ty"
                        and "name |\<notin>| TE_GhostGlobals env"
                        using gv_eq gg_eq by simp_all
                      hence "global_var_in_state_with_type state env name ty"
                        using old_gv unfolding global_vars_exist_in_state_def by blast
                      thus "global_var_in_state_with_type ?state' env' name ty"
                        using vht_eq unfolding global_var_in_state_with_type_def
                        by (auto split: option.splits)
                    qed
                  qed
                next
                  show "no_extra_local_vars ?state' env'"
                    unfolding no_extra_local_vars_def
                  proof (intro allI impI)
                    fix name
                    assume ante: "fmlookup (TE_LocalVars env') name = None \<or> name |\<in>| TE_GhostLocals env'"
                    show "fmlookup (IS_Locals ?state') name = None \<and>
                          fmlookup (IS_Refs ?state') name = None"
                    proof (cases "name = varName")
                      case True
                      from env'_writable_eq have "fmlookup (TE_LocalVars env') varName = Some varTy" by simp
                      with ante True have "varName |\<in>| TE_GhostLocals env'" by simp
                      hence False using env'_writable_eq by auto
                      thus ?thesis ..
                    next
                      case False
                      from ante env'_writable_eq False
                      have "fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env" by auto
                      with old_sme have "fmlookup (IS_Locals state) name = None \<and>
                          fmlookup (IS_Refs state) name = None"
                        unfolding state_matches_env_def no_extra_local_vars_def by blast
                      with False show ?thesis by simp
                    qed
                  qed
                next
                  show "no_extra_global_vars ?state' env'"
                    using old_sme env'_writable_eq
                    unfolding state_matches_env_def no_extra_global_vars_def by simp
                next
                  show "funs_exist_in_state ?state' env'"
                    unfolding funs_exist_in_state_def
                  proof (intro allI impI, elim conjE)
                    fix name info
                    assume lk: "fmlookup (TE_Functions env') name = Some info"
                      and ng: "FI_Ghost info = NotGhost"
                    from old_sme have old_fes: "funs_exist_in_state state env"
                      unfolding state_matches_env_def by simp
                    have funs_eq: "TE_Functions env' = TE_Functions env" using env'_writable_eq by simp
                    from lk funs_eq have lk': "fmlookup (TE_Functions env) name = Some info" by simp
                    from old_fes lk' ng obtain interpFun where
                      if_lk: "fmlookup (IS_Functions state) name = Some interpFun" and
                      matches: "fun_info_matches_interp_fun env info interpFun"
                      unfolding funs_exist_in_state_def by (auto split: option.splits)
                    have if_lk': "fmlookup (IS_Functions ?state') name = Some interpFun"
                      using if_lk by simp
                    have fcong: "fun_info_matches_interp_fun env' info interpFun =
                                  fun_info_matches_interp_fun env info interpFun"
                      by (rule fun_info_matches_interp_fun_cong_env)
                         (use env'_writable_eq in simp_all)
                    have "fun_info_matches_interp_fun env' info interpFun"
                      using matches fcong by simp
                    with if_lk' show "case fmlookup (IS_Functions ?state') name of
                                        None \<Rightarrow> False
                                      | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env' info interpFun"
                      by simp
                  qed
                next
                  show "no_extra_funs ?state' env'"
                    using old_sme env'_writable_eq
                    unfolding state_matches_env_def no_extra_funs_def by simp
                next
                  show "const_locals_match ?state' env'"
                    using old_sme env'_writable_eq
                    unfolding state_matches_env_def const_locals_match_def by auto
                next
                  show "store_well_typed ?state' env' storeTyping"
                    using old_sme vht_eq
                    unfolding state_matches_env_def store_well_typed_def by simp
                next
                  have rt_eq: "\<And>ty. is_runtime_type env' ty = is_runtime_type env ty"
                    by (rule is_runtime_type_cong_env) (use env'_fields in simp_all)
                  have wk_eq: "\<And>ty. is_well_kinded env' ty = is_well_kinded env ty"
                    by (rule is_well_kinded_cong_env) (use env'_fields in simp_all)
                  show "ty_args_well_formed ?state' env'"
                    using old_sme env'_fields rt_eq wk_eq
                    unfolding state_matches_env_def ty_args_well_formed_def by simp
                next
                  show "default_ctors_match ?state' env'"
                    using old_sme env'_writable_eq
                    unfolding state_matches_env_def default_ctors_match_def by simp
                qed
                from new_sme interp_eq CoreStmt_VarDecl Ref NotGhost
                show ?thesis using storeTyping_extends_refl by auto
              qed
            next
              case readonly: False
              \<comment> \<open>Copy path: use IH_term to get the value, alloc_store, add to IS_ConstLocals. \<close>
              from readonly static_writable_iff_runtime have
                runtime_readonly: "baseName |\<in>| IS_ConstLocals state
                                   \<or> (fmlookup (IS_Locals state) baseName = None
                                      \<and> fmlookup (IS_Refs state) baseName = None)" by auto
              from IH_term[OF "4.prems"(1,2) init_ty]
              have init_sound: "sound_term_result state env varTy (interp_term fuel state initTm)" .
              show ?thesis
              proof (cases "interp_term fuel state initTm")
                case (Inl err)
                with init_sound have err_sound: "sound_error_result err" by simp
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Ref varTy initTm) = Inl err"
                  using Inl base_eq runtime_readonly by simp
                with err_sound CoreStmt_VarDecl Ref NotGhost show ?thesis by simp
              next
                case (Inr initVal)
                from init_sound Inr
                have val_typed: "value_has_type env initVal
                                   (apply_subst (IS_TyArgs state) varTy)" by simp
                obtain state' addr where alloc_eq: "(state', addr) = alloc_store state initVal"
                  by (cases "alloc_store state initVal") auto
                let ?state'' = "state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state'),
                                         IS_Refs := fmdrop varName (IS_Refs state'),
                                         IS_ConstLocals := finsert varName (IS_ConstLocals state') \<rparr>"
                have interp_eq: "interp_statement (Suc fuel) state
                    (CoreStmt_VarDecl NotGhost varName Ref varTy initTm) = Inr (Continue ?state'')"
                  using Inr alloc_eq base_eq runtime_readonly
                  by (simp add: case_prod_beta)
                from env'_eq readonly have env'_const_eq:
                  "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                                TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>"
                  by simp
                let ?subVarTy = "apply_subst (IS_TyArgs state) varTy"
                have new_sme: "state_matches_env ?state'' env' (storeTyping @ [?subVarTy])"
                  using state_matches_env_add_const_local[OF "4.prems"(1) val_typed alloc_eq refl env'_const_eq] .
                have ext: "storeTyping_extends storeTyping (storeTyping @ [?subVarTy])"
                  using storeTyping_extends_append .
                from new_sme ext interp_eq CoreStmt_VarDecl Ref NotGhost
                show ?thesis by auto
              qed
            qed
          qed
        qed
      next
        case (CoreStmt_VarDeclCall declGhost varName varTy castOpt fnName tyArgs argTms)
        \<comment> \<open>Extract the call facts and the cast result type from typing (both ghost
            modes share these; they differ only in the env'/interpreter shape).
            varTy is the explicit declared type; the cast result must equal it. \<close>
        from typing CoreStmt_VarDeclCall obtain retTy where
          call_ty: "core_impure_call_type env declGhost fnName tyArgs argTms = Some retTy" and
          cast_ty: "cast_result_type env declGhost retTy castOpt = Some varTy"
          by (auto split: if_splits option.splits)
        show ?thesis proof (cases declGhost)
          case Ghost
          \<comment> \<open>Ghost VarDeclCall: the call is not executed; the interpreter drops
              varName from the runtime maps. Mirrors Ghost VarDecl(Var). \<close>
          from typing CoreStmt_VarDeclCall Ghost call_ty cast_ty have env'_eq:
            "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                          TE_GhostLocals := finsert varName (TE_GhostLocals env),
                          TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
            by (simp split: if_splits)
          let ?state' = "state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
                                 IS_Refs := fmdrop varName (IS_Refs state),
                                 IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"
          have interp_eq: "interp_statement (Suc fuel) state
              (CoreStmt_VarDeclCall Ghost varName varTy castOpt fnName tyArgs argTms)
                = Inr (Continue ?state')"
            by simp
          from "4.prems"(1) have old_sme: "state_matches_env state env storeTyping" .
          have "state_matches_env ?state' env' storeTyping"
            using state_matches_env_add_ghost_local[OF old_sme env'_eq refl] .
          with CoreStmt_VarDeclCall Ghost show ?thesis
            using interp_eq storeTyping_extends_refl by auto
        next
          case NotGhost
          \<comment> \<open>NotGhost VarDeclCall: run the call, apply the optional cast, then
              alloc_store + fmupd the new local. \<close>
          from typing CoreStmt_VarDeclCall NotGhost call_ty cast_ty have env'_eq:
            "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                          TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|},
                          TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
            by (simp split: if_splits)
          \<comment> \<open>Function-call facts for IH_fc. \<close>
          from core_impure_call_type_fn_facts[OF call_ty[unfolded NotGhost]] obtain funInfo where
            fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
            len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
            tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
            tyargs_rt: "NotGhost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs" and
            fn_not_ghost: "NotGhost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
            len_tmargs: "length argTms = length (FI_TmArgs funInfo)" and
            fn_ty_eq: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                           (FI_ReturnType funInfo)" and
            args_check: "list_all2 (\<lambda>tm expectedTy.
                           case core_term_type env NotGhost tm of
                             None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                         argTms
                         (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                              (FI_TmArgs funInfo))" and
            ref_lvalues: "\<forall>i < length argTms.
                            snd (snd (FI_TmArgs funInfo ! i)) = Ref
                              \<longrightarrow> is_writable_lvalue env (argTms ! i)"
            by blast
          have fn_not_ghost': "FI_Ghost funInfo = NotGhost"
            using fn_not_ghost by (cases "FI_Ghost funInfo") auto
          have tyargs_rt': "list_all (is_runtime_type env) tyArgs" using tyargs_rt by simp
          from IH_fc[OF "4.prems"(1,2) fn_lookup fn_not_ghost' args_check fn_ty_eq
                        len_tyargs tyargs_wk tyargs_rt' ref_lvalues]
          have fc_sound: "sound_function_call_result state env storeTyping retTy
              (interp_function_call fuel state fnName tyArgs argTms)" .
          show ?thesis
          proof (cases "interp_function_call fuel state fnName tyArgs argTms")
            case (Inl err)
            with fc_sound have err_sound: "sound_error_result err" by simp
            have interp_err: "interp_statement (Suc fuel) state
                (CoreStmt_VarDeclCall NotGhost varName varTy castOpt fnName tyArgs argTms) = Inl err"
              using Inl by simp
            with err_sound CoreStmt_VarDeclCall NotGhost show ?thesis by simp
          next
            case (Inr fcResult)
            obtain newState retVal where fcResult_eq: "fcResult = (newState, retVal)"
              by (cases fcResult) auto
            from fc_sound Inr fcResult_eq obtain storeTyping1 where
              new_sme: "state_matches_env newState env storeTyping1" and
              ext1: "storeTyping_extends storeTyping storeTyping1" and
              tyargs_eq: "IS_TyArgs newState = IS_TyArgs state" and
              ret_typed: "value_has_type env retVal (apply_subst (IS_TyArgs state) retTy)"
              by auto
            show ?thesis
            proof (cases "apply_cast_opt castOpt retVal")
              case (Inl err)
              have err_eq: "err = RuntimeError"
                using apply_cast_opt_error_is_runtime[OF Inl cast_ty[unfolded NotGhost] ret_typed] .
              have interp_err: "interp_statement (Suc fuel) state
                  (CoreStmt_VarDeclCall NotGhost varName varTy castOpt fnName tyArgs argTms) = Inl RuntimeError"
                using Inl Inr fcResult_eq err_eq by simp
              with CoreStmt_VarDeclCall NotGhost show ?thesis by simp
            next
              case (Inr initialVal)
              from apply_cast_opt_sound[OF Inr cast_ty[unfolded NotGhost] ret_typed[unfolded tyargs_eq[symmetric]]]
              have val_typed_new: "value_has_type env initialVal (apply_subst (IS_TyArgs newState) varTy)" .
              hence val_typed: "value_has_type env initialVal (apply_subst (IS_TyArgs state) varTy)"
                using tyargs_eq by simp
              obtain state' addr where alloc_eq:
                "(state', addr) = alloc_store newState initialVal"
                by (cases "alloc_store newState initialVal") auto
              let ?state'' = "state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state'),
                                       IS_Refs := fmdrop varName (IS_Refs state'),
                                       IS_ConstLocals := fminus (IS_ConstLocals state') {|varName|} \<rparr>"
              have interp_eq: "interp_statement (Suc fuel) state
                  (CoreStmt_VarDeclCall NotGhost varName varTy castOpt fnName tyArgs argTms)
                    = Inr (Continue ?state'')"
                using \<open>interp_function_call fuel state fnName tyArgs argTms = Inr fcResult\<close>
                      fcResult_eq Inr alloc_eq by (simp add: case_prod_beta)
              let ?subVarTy = "apply_subst (IS_TyArgs newState) varTy"
              from state_matches_env_add_nonconst_local[OF new_sme val_typed_new
                  alloc_eq refl env'_eq]
              have new_sme_ext: "state_matches_env ?state'' env' (storeTyping1 @ [?subVarTy])" .
              have ext2: "storeTyping_extends storeTyping1 (storeTyping1 @ [?subVarTy])"
                using storeTyping_extends_append .
              have ext_total: "storeTyping_extends storeTyping (storeTyping1 @ [?subVarTy])"
                using storeTyping_extends_trans[OF ext1 ext2] .
              from new_sme_ext ext_total interp_eq CoreStmt_VarDeclCall NotGhost
              show ?thesis by auto
            qed
          qed
        qed
      next
        case (CoreStmt_Assign assignGhost lhsTm rhsTm)
        then show ?thesis proof (cases assignGhost)
          case Ghost
          \<comment> \<open>Ghost Assign: interpreter returns Continue state, env unchanged\<close>
          from typing CoreStmt_Assign Ghost have "env' = env"
            by (auto split: if_splits option.splits)
          with Ghost CoreStmt_Assign "4.prems"(1) show ?thesis
            using storeTyping_extends_refl by auto
        next
          case NotGhost
          \<comment> \<open>NotGhost Assign: rhs is an ordinary (pure) term. Evaluate lhs lvalue
              and rhs term, then update the store. (Impure-call rhs's are handled
              by CoreStmt_AssignCall.)\<close>
          from typing CoreStmt_Assign NotGhost obtain lhsTy where
            lhs_writable: "is_writable_lvalue env lhsTm" and
            lhs_ty: "core_term_type env NotGhost lhsTm = Some lhsTy" and
            rhs_ty: "core_term_type env NotGhost rhsTm = Some lhsTy" and
            env'_eq: "env' = env"
            by (auto split: if_splits option.splits)
          from IH_lvalue[OF "4.prems"(1,2) conjI[OF lhs_writable lhs_ty]]
          have lhs_sound: "sound_lvalue_result state env storeTyping lhsTy
              (interp_writable_lvalue fuel state lhsTm)" .
          show ?thesis
          proof (cases "interp_writable_lvalue fuel state lhsTm")
            case (Inl err)
            with lhs_sound have "sound_error_result err" by simp
            with Inl CoreStmt_Assign NotGhost show ?thesis by simp
          next
            case (Inr addrPath)
            obtain addr path where ap_eq: "addrPath = (addr, path)"
              by (cases addrPath) auto
            from lhs_sound Inr ap_eq have
              addr_valid: "addr < length (IS_Store state)" and
              path_ty: "type_at_path env (storeTyping ! addr) path
                          = Some (apply_subst (IS_TyArgs state) lhsTy)"
              by auto
            from IH_term[OF "4.prems"(1,2) rhs_ty]
            have rhs_sound: "sound_term_result state env lhsTy (interp_term fuel state rhsTm)" .
            show ?thesis
            proof (cases "interp_term fuel state rhsTm")
              case (Inl err)
              with rhs_sound have err_sound: "sound_error_result err" by simp
              have interp_err: "interp_statement (Suc fuel) state
                  (CoreStmt_Assign NotGhost lhsTm rhsTm) = Inl err"
                using Inl \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close> ap_eq by simp
              with err_sound CoreStmt_Assign NotGhost show ?thesis by simp
            next
              case (Inr rhsVal)
              from rhs_sound Inr
              have rhs_typed: "value_has_type env rhsVal
                                 (apply_subst (IS_TyArgs state) lhsTy)" by simp
              from "4.prems"(1) addr_valid
              have old_slot_typed: "value_has_type env (IS_Store state ! addr) (storeTyping ! addr)"
                unfolding state_matches_env_def store_well_typed_def by simp
              show ?thesis
              proof (cases "update_value_at_path (IS_Store state ! addr) path rhsVal")
                case (Inl err)
                from update_value_at_path_error_is_runtime[OF old_slot_typed path_ty Inl]
                have err_eq: "err = RuntimeError" .
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_Assign NotGhost lhsTm rhsTm) = Inl RuntimeError"
                  using Inl Inr \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close>
                        ap_eq err_eq by simp
                with CoreStmt_Assign NotGhost show ?thesis by simp
              next
                case (Inr newVal)
                from update_value_at_path_preserves_type[OF old_slot_typed Inr path_ty rhs_typed]
                have new_slot_typed: "value_has_type env newVal (storeTyping ! addr)" .
                let ?state' = "state \<lparr> IS_Store := (IS_Store state)[addr := newVal] \<rparr>"
                have interp_eq: "interp_statement (Suc fuel) state
                    (CoreStmt_Assign NotGhost lhsTm rhsTm) = Inr (Continue ?state')"
                  using Inr \<open>interp_term fuel state rhsTm = Inr rhsVal\<close>
                    \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close> ap_eq by simp
                from state_matches_env_update_store[OF "4.prems"(1) addr_valid
                    new_slot_typed refl]
                have new_sme: "state_matches_env ?state' env storeTyping" .
                have ext: "storeTyping_extends storeTyping storeTyping"
                  using storeTyping_extends_refl .
                from new_sme ext interp_eq env'_eq CoreStmt_Assign NotGhost
                show ?thesis by auto
              qed
            qed
          qed
        qed
      next
        case (CoreStmt_AssignCall assignGhost lhsTm castOpt fnName tyArgs argTms)
        then show ?thesis proof (cases assignGhost)
          case Ghost
          \<comment> \<open>Ghost AssignCall: interpreter returns Continue state, env unchanged.\<close>
          from typing CoreStmt_AssignCall Ghost have "env' = env"
            by (auto split: if_splits option.splits)
          with Ghost CoreStmt_AssignCall "4.prems"(1) show ?thesis
            using storeTyping_extends_refl by auto
        next
          case NotGhost
          \<comment> \<open>NotGhost AssignCall: resolve lhs, run the call, apply the optional cast,
              update the store. The call facts come from core_impure_call_type. \<close>
          from typing CoreStmt_AssignCall NotGhost have lhs_writable: "is_writable_lvalue env lhsTm"
            by (simp split: if_splits)
          from typing CoreStmt_AssignCall NotGhost lhs_writable obtain lhsTy where
            lhs_ty: "core_term_type env NotGhost lhsTm = Some lhsTy"
            by (simp split: option.splits)
          from typing CoreStmt_AssignCall NotGhost lhs_writable lhs_ty obtain retTy where
            call_ty: "core_impure_call_type env NotGhost fnName tyArgs argTms = Some retTy"
            by (simp split: option.splits)
          from typing CoreStmt_AssignCall NotGhost lhs_writable lhs_ty call_ty have
            cast_ty: "cast_result_type env NotGhost retTy castOpt = Some lhsTy" and
            env'_eq: "env' = env"
            by (simp split: if_splits)+
          \<comment> \<open>Extract the function-call facts (shape for IH_fc / type_soundness_function_call). \<close>
          from core_impure_call_type_fn_facts[OF call_ty] obtain funInfo where
            fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
            len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
            tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
            tyargs_rt: "NotGhost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs" and
            fn_not_ghost: "NotGhost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
            len_tmargs: "length argTms = length (FI_TmArgs funInfo)" and
            fn_ty_eq: "retTy = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                           (FI_ReturnType funInfo)" and
            args_check: "list_all2 (\<lambda>tm expectedTy.
                           case core_term_type env NotGhost tm of
                             None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
                         argTms
                         (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                              (FI_TmArgs funInfo))" and
            ref_lvalues: "\<forall>i < length argTms.
                            snd (snd (FI_TmArgs funInfo ! i)) = Ref
                              \<longrightarrow> is_writable_lvalue env (argTms ! i)"
            by blast
          have fn_not_ghost': "FI_Ghost funInfo = NotGhost"
            using fn_not_ghost by (cases "FI_Ghost funInfo") auto
          have tyargs_rt': "list_all (is_runtime_type env) tyArgs" using tyargs_rt by simp
          from IH_lvalue[OF "4.prems"(1,2) conjI[OF lhs_writable lhs_ty]]
          have lhs_sound: "sound_lvalue_result state env storeTyping lhsTy
              (interp_writable_lvalue fuel state lhsTm)" .
          from IH_fc[OF "4.prems"(1,2) fn_lookup fn_not_ghost' args_check fn_ty_eq
                        len_tyargs tyargs_wk tyargs_rt' ref_lvalues]
          have fc_sound: "sound_function_call_result state env storeTyping retTy
              (interp_function_call fuel state fnName tyArgs argTms)" .
          show ?thesis
          proof (cases "interp_writable_lvalue fuel state lhsTm")
            case (Inl err)
            with lhs_sound have "sound_error_result err" by simp
            with Inl CoreStmt_AssignCall NotGhost show ?thesis by simp
          next
            case (Inr addrPath)
            obtain addr path where ap_eq: "addrPath = (addr, path)"
              by (cases addrPath) auto
            from lhs_sound Inr ap_eq have
              addr_valid: "addr < length (IS_Store state)" and
              path_ty: "type_at_path env (storeTyping ! addr) path
                          = Some (apply_subst (IS_TyArgs state) lhsTy)"
              by auto
            show ?thesis
            proof (cases "interp_function_call fuel state fnName tyArgs argTms")
              case (Inl err)
              with fc_sound have err_sound: "sound_error_result err" by simp
              have interp_err: "interp_statement (Suc fuel) state
                  (CoreStmt_AssignCall NotGhost lhsTm castOpt fnName tyArgs argTms) = Inl err"
                using Inl \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close> ap_eq by simp
              with err_sound CoreStmt_AssignCall NotGhost show ?thesis by simp
            next
              case (Inr fcResult)
              obtain newState retVal where fcResult_eq: "fcResult = (newState, retVal)"
                by (cases fcResult) auto
              from fc_sound Inr fcResult_eq obtain storeTyping1 where
                new_sme: "state_matches_env newState env storeTyping1" and
                ext1: "storeTyping_extends storeTyping storeTyping1" and
                tyargs_eq: "IS_TyArgs newState = IS_TyArgs state" and
                ret_typed: "value_has_type env retVal
                              (apply_subst (IS_TyArgs state) retTy)"
                by auto
              \<comment> \<open>storeTyping_extends preserves the original addr's type.\<close>
              from ext1 obtain suffix where st1_eq: "storeTyping1 = storeTyping @ suffix"
                unfolding storeTyping_extends_def by auto
              from new_sme
              have st1_len: "length storeTyping1 = length (IS_Store newState)"
                unfolding state_matches_env_def store_well_typed_def by simp
              from "4.prems"(1)
              have st_len: "length storeTyping = length (IS_Store state)"
                unfolding state_matches_env_def store_well_typed_def by simp
              from addr_valid st_len have addr_lt_st: "addr < length storeTyping" by simp
              have st1_at_addr: "storeTyping1 ! addr = storeTyping ! addr"
                using st1_eq addr_lt_st by (simp add: nth_append)
              from addr_lt_st st1_eq have addr_lt_st1: "addr < length storeTyping1" by simp
              from addr_lt_st1 st1_len
              have addr_valid_new: "addr < length (IS_Store newState)" by simp
              from path_ty st1_at_addr
              have path_ty_new: "type_at_path env (storeTyping1 ! addr) path
                                   = Some (apply_subst (IS_TyArgs state) lhsTy)" by simp
              from new_sme addr_valid_new
              have old_slot_typed: "value_has_type env (IS_Store newState ! addr)
                                      (storeTyping1 ! addr)"
                unfolding state_matches_env_def store_well_typed_def by simp
              \<comment> \<open>Apply the optional cast to the call's return value. \<close>
              show ?thesis
              proof (cases "apply_cast_opt castOpt retVal")
                case (Inl err)
                \<comment> \<open>A failed cast is a RuntimeError (apply_cast_opt overflow). \<close>
                have err_eq: "err = RuntimeError"
                  using apply_cast_opt_error_is_runtime[OF Inl cast_ty ret_typed] .
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_AssignCall NotGhost lhsTm castOpt fnName tyArgs argTms) = Inl RuntimeError"
                  using Inl Inr fcResult_eq
                        \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close> ap_eq err_eq by simp
                with CoreStmt_AssignCall NotGhost show ?thesis by simp
              next
                case (Inr rhsVal)
                from apply_cast_opt_sound[OF Inr cast_ty ret_typed[unfolded tyargs_eq[symmetric]]]
                have rhs_typed: "value_has_type env rhsVal (apply_subst (IS_TyArgs newState) lhsTy)" .
                hence rhs_typed': "value_has_type env rhsVal (apply_subst (IS_TyArgs state) lhsTy)"
                  using tyargs_eq by simp
                show ?thesis
                proof (cases "update_value_at_path (IS_Store newState ! addr) path rhsVal")
                  case (Inl err)
                  from update_value_at_path_error_is_runtime[OF old_slot_typed path_ty_new Inl]
                  have err_eq: "err = RuntimeError" .
                  have interp_err: "interp_statement (Suc fuel) state
                      (CoreStmt_AssignCall NotGhost lhsTm castOpt fnName tyArgs argTms) = Inl RuntimeError"
                    using Inl \<open>interp_function_call fuel state fnName tyArgs argTms = Inr fcResult\<close>
                          fcResult_eq \<open>apply_cast_opt castOpt retVal = Inr rhsVal\<close>
                          \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close>
                          ap_eq err_eq by simp
                  with CoreStmt_AssignCall NotGhost show ?thesis by simp
                next
                  case (Inr newVal)
                  from update_value_at_path_preserves_type[OF old_slot_typed Inr path_ty_new rhs_typed']
                  have new_slot_typed: "value_has_type env newVal (storeTyping1 ! addr)" .
                  let ?finalState = "newState \<lparr> IS_Store := (IS_Store newState)[addr := newVal] \<rparr>"
                  have interp_eq: "interp_statement (Suc fuel) state
                      (CoreStmt_AssignCall NotGhost lhsTm castOpt fnName tyArgs argTms)
                        = Inr (Continue ?finalState)"
                    using Inr \<open>interp_function_call fuel state fnName tyArgs argTms = Inr fcResult\<close>
                          fcResult_eq \<open>apply_cast_opt castOpt retVal = Inr rhsVal\<close>
                          \<open>interp_writable_lvalue fuel state lhsTm = Inr addrPath\<close> ap_eq by simp
                  from state_matches_env_update_store[OF new_sme addr_valid_new
                      new_slot_typed refl]
                  have final_sme: "state_matches_env ?finalState env storeTyping1" .
                  from final_sme ext1 interp_eq env'_eq CoreStmt_AssignCall NotGhost
                  show ?thesis by auto
                qed
              qed
            qed
          qed
        qed
      next
        case (CoreStmt_Fix _ _)
        \<comment> \<open>Fix only typechecks in Ghost mode; the outer case is NotGhost, so
            typing is contradictory and the case is vacuous. \<close>
        from typing CoreStmt_Fix show ?thesis
          by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
      next
        case (CoreStmt_Obtain varName varTy condTm)
        \<comment> \<open>Obtain: a runtime no-op that introduces a ghost local. Like the Ghost
            Var VarDecl case, the interpreter drops varName from the runtime
            maps and we extend env with the new ghost local. \<close>
        from typing CoreStmt_Obtain have
          env'_eq: "env' = env \<lparr> TE_LocalVars := fmupd varName varTy (TE_LocalVars env),
                                 TE_GhostLocals := finsert varName (TE_GhostLocals env),
                                 TE_ConstLocals := fminus (TE_ConstLocals env) {|varName|} \<rparr>"
          by (auto simp: Let_def split: if_splits)
        let ?state' = "state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
                               IS_Refs := fmdrop varName (IS_Refs state),
                               IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"
        have interp_eq: "interp_statement (Suc fuel) state
            (CoreStmt_Obtain varName varTy condTm) = Inr (Continue ?state')"
          by simp
        from "4.prems"(1) have
          old_sme: "state_matches_env state env storeTyping" .
        have tyargs_eq [simp]: "IS_TyArgs ?state' = IS_TyArgs state" by simp
        have env'_fields: "TE_DataCtors env' = TE_DataCtors env"
                          "TE_Datatypes env' = TE_Datatypes env"
                          "TE_TypeVars env' = TE_TypeVars env"
                          "TE_GhostDatatypes env' = TE_GhostDatatypes env"
                          "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
          using env'_eq by simp_all
        have vht_eq: "\<And>v t. value_has_type env' v t = value_has_type env v t"
          using value_has_type_cong_env[OF env'_fields] .
        have tap_eq: "\<And>t p. type_at_path env t p = type_at_path env' t p"
          using type_at_path_cong_env[OF env'_fields(1)] .
        have "state_matches_env ?state' env' storeTyping"
          unfolding state_matches_env_def
        proof (intro conjI)
          show "local_vars_exist_in_state ?state' env' storeTyping"
            unfolding local_vars_exist_in_state_def
          proof (intro allI impI, elim conjE)
            fix name ty
            assume lk: "fmlookup (TE_LocalVars env') name = Some ty"
              and ng: "name |\<notin>| TE_GhostLocals env'"
            from ng env'_eq have "name \<noteq> varName" by auto
            with lk env'_eq have lk_old: "fmlookup (TE_LocalVars env) name = Some ty" by simp
            from ng env'_eq \<open>name \<noteq> varName\<close> have ng_old: "name |\<notin>| TE_GhostLocals env" by auto
            from old_sme lk_old ng_old
            have "local_var_in_state_with_type state env storeTyping name ty"
              unfolding state_matches_env_def local_vars_exist_in_state_def by blast
            with \<open>name \<noteq> varName\<close> tap_eq show "local_var_in_state_with_type ?state' env' storeTyping name ty"
              unfolding local_var_in_state_with_type_def Let_def
              by (auto split: option.splits)
          qed
        next
          show "global_vars_exist_in_state ?state' env'"
          proof -
            from old_sme have old_gv: "global_vars_exist_in_state state env"
              unfolding state_matches_env_def by simp
            have gv_eq: "TE_GlobalVars env' = TE_GlobalVars env" using env'_eq by simp
            have gg_eq: "TE_GhostGlobals env' = TE_GhostGlobals env" using env'_eq by simp
            show ?thesis unfolding global_vars_exist_in_state_def
            proof (intro allI impI, elim conjE)
              fix name ty
              assume lk: "fmlookup (TE_GlobalVars env') name = Some ty"
                and ng: "name |\<notin>| TE_GhostGlobals env'"
              from lk gv_eq have "fmlookup (TE_GlobalVars env) name = Some ty" by simp
              moreover from ng gg_eq have "name |\<notin>| TE_GhostGlobals env" by simp
              ultimately have "global_var_in_state_with_type state env name ty"
                using old_gv unfolding global_vars_exist_in_state_def by blast
              thus "global_var_in_state_with_type ?state' env' name ty"
                using vht_eq unfolding global_var_in_state_with_type_def
                by (auto split: option.splits)
            qed
          qed
        next
          show "no_extra_local_vars ?state' env'"
            unfolding no_extra_local_vars_def
          proof (intro allI impI)
            fix name
            assume ante: "fmlookup (TE_LocalVars env') name = None \<or> name |\<in>| TE_GhostLocals env'"
            show "fmlookup (IS_Locals ?state') name = None \<and>
                  fmlookup (IS_Refs ?state') name = None"
            proof (cases "name = varName")
              case True
              then show ?thesis by simp
            next
              case False
              from ante False env'_eq
              have "fmlookup (TE_LocalVars env) name = None \<or> name |\<in>| TE_GhostLocals env" by auto
              with old_sme have "fmlookup (IS_Locals state) name = None \<and>
                  fmlookup (IS_Refs state) name = None"
                unfolding state_matches_env_def no_extra_local_vars_def by blast
              with False show ?thesis by simp
            qed
          qed
        next
          show "no_extra_global_vars ?state' env'"
            using old_sme env'_eq
            unfolding state_matches_env_def no_extra_global_vars_def by simp
        next
          show "funs_exist_in_state ?state' env'"
            unfolding funs_exist_in_state_def
          proof (intro allI impI, elim conjE)
            fix name info
            assume lk: "fmlookup (TE_Functions env') name = Some info"
              and ng: "FI_Ghost info = NotGhost"
            from old_sme have old_fes: "funs_exist_in_state state env"
              unfolding state_matches_env_def by simp
            have funs_eq: "TE_Functions env' = TE_Functions env" using env'_eq by simp
            from lk funs_eq have lk': "fmlookup (TE_Functions env) name = Some info" by simp
            from old_fes lk' ng obtain interpFun where
              if_lk: "fmlookup (IS_Functions state) name = Some interpFun" and
              matches: "fun_info_matches_interp_fun env info interpFun"
              unfolding funs_exist_in_state_def by (auto split: option.splits)
            have if_lk': "fmlookup (IS_Functions ?state') name = Some interpFun"
              using if_lk by simp
            have fcong: "fun_info_matches_interp_fun env' info interpFun =
                          fun_info_matches_interp_fun env info interpFun"
              by (rule fun_info_matches_interp_fun_cong_env)
                 (use env'_eq in simp_all)
            have "fun_info_matches_interp_fun env' info interpFun"
              using matches fcong by simp
            with if_lk' show "case fmlookup (IS_Functions ?state') name of
                                None \<Rightarrow> False
                              | Some interpFun \<Rightarrow> fun_info_matches_interp_fun env' info interpFun"
              by simp
          qed
        next
          show "no_extra_funs ?state' env'"
            using old_sme env'_eq
            unfolding state_matches_env_def no_extra_funs_def by simp
        next
          show "const_locals_match ?state' env'"
            using old_sme env'_eq
            unfolding state_matches_env_def const_locals_match_def by auto
        next
          show "store_well_typed ?state' env' storeTyping"
            using old_sme vht_eq
            unfolding state_matches_env_def store_well_typed_def by simp
        next
          have rt_eq: "\<And>ty. is_runtime_type env' ty = is_runtime_type env ty"
            by (rule is_runtime_type_cong_env) (use env'_fields in simp_all)
          have wk_eq: "\<And>ty. is_well_kinded env' ty = is_well_kinded env ty"
            by (rule is_well_kinded_cong_env) (use env'_fields in simp_all)
          show "ty_args_well_formed ?state' env'"
            using old_sme env'_fields rt_eq wk_eq
            unfolding state_matches_env_def ty_args_well_formed_def by simp
        next
          show "default_ctors_match ?state' env'"
            using old_sme env'_eq
            unfolding state_matches_env_def default_ctors_match_def by simp
        qed
        with CoreStmt_Obtain show ?thesis
          using interp_eq storeTyping_extends_refl by auto
      next
        case (CoreStmt_Use _)
        \<comment> \<open>Use only typechecks in Ghost mode; the outer case is NotGhost, so
            typing is contradictory and the case is vacuous. \<close>
        from typing CoreStmt_Use show ?thesis
          by (auto split: option.splits CoreTerm.splits Quantifier.splits if_splits)
      next
        case (CoreStmt_Swap swapGhost lhsTm rhsTm)
        then show ?thesis proof (cases swapGhost)
          case Ghost
          \<comment> \<open>Ghost Swap: interpreter returns Continue state, env unchanged\<close>
          from typing CoreStmt_Swap Ghost have "env' = env"
            by (auto split: if_splits option.splits)
          with Ghost CoreStmt_Swap "4.prems"(1) show ?thesis
            using storeTyping_extends_refl by auto
        next
          case NotGhost
          \<comment> \<open>NotGhost Swap: evaluates both lvalues and swaps the values.\<close>
          from typing CoreStmt_Swap NotGhost obtain lhsTy where
            lhs_writable: "is_writable_lvalue env lhsTm" and
            rhs_writable: "is_writable_lvalue env rhsTm" and
            lhs_ty: "core_term_type env NotGhost lhsTm = Some lhsTy" and
            rhs_ty: "core_term_type env NotGhost rhsTm = Some lhsTy" and
            env'_eq: "env' = env"
            by (auto split: if_splits option.splits)
          from IH_lvalue[OF "4.prems"(1,2) conjI[OF lhs_writable lhs_ty]]
          have lhs_sound: "sound_lvalue_result state env storeTyping lhsTy
              (interp_writable_lvalue fuel state lhsTm)" .
          from IH_lvalue[OF "4.prems"(1,2) conjI[OF rhs_writable rhs_ty]]
          have rhs_sound: "sound_lvalue_result state env storeTyping lhsTy
              (interp_writable_lvalue fuel state rhsTm)" .
          show ?thesis
          proof (cases "interp_writable_lvalue fuel state lhsTm")
            case (Inl err)
            with lhs_sound have "sound_error_result err" by simp
            with Inl CoreStmt_Swap NotGhost show ?thesis by simp
          next
            case Inr_lhs: (Inr lhsAddrPath)
            obtain addr1 path1 where ap1_eq: "lhsAddrPath = (addr1, path1)"
              by (cases lhsAddrPath) auto
            from lhs_sound Inr_lhs ap1_eq have
              addr1_valid: "addr1 < length (IS_Store state)" and
              path1_ty: "type_at_path env (storeTyping ! addr1) path1
                            = Some (apply_subst (IS_TyArgs state) lhsTy)"
              by auto
            show ?thesis
            proof (cases "interp_writable_lvalue fuel state rhsTm")
              case (Inl err)
              with rhs_sound have "sound_error_result err" by simp
              with Inl Inr_lhs ap1_eq CoreStmt_Swap NotGhost show ?thesis by simp
            next
              case Inr_rhs: (Inr rhsAddrPath)
              obtain addr2 path2 where ap2_eq: "rhsAddrPath = (addr2, path2)"
                by (cases rhsAddrPath) auto
              from rhs_sound Inr_rhs ap2_eq have
                addr2_valid: "addr2 < length (IS_Store state)" and
                path2_ty: "type_at_path env (storeTyping ! addr2) path2
                              = Some (apply_subst (IS_TyArgs state) lhsTy)"
                by auto
              \<comment> \<open>Get the original slot values typed at their storeTyping entries.\<close>
              from "4.prems"(1) addr1_valid
              have slot1_typed: "value_has_type env (IS_Store state ! addr1) (storeTyping ! addr1)"
                unfolding state_matches_env_def store_well_typed_def by simp
              from "4.prems"(1) addr2_valid
              have slot2_typed: "value_has_type env (IS_Store state ! addr2) (storeTyping ! addr2)"
                unfolding state_matches_env_def store_well_typed_def by simp
              \<comment> \<open>Case split on get_value_at_path results for both slots.\<close>
              show ?thesis
              proof (cases "get_value_at_path (IS_Store state ! addr1) path1")
                case (Inl err1)
                from get_value_at_path_error_is_runtime[OF slot1_typed path1_ty Inl]
                have err1_eq: "err1 = RuntimeError" .
                have interp_err: "interp_statement (Suc fuel) state
                    (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inl RuntimeError"
                  using Inr_lhs ap1_eq Inr_rhs ap2_eq Inl err1_eq by simp
                with CoreStmt_Swap NotGhost show ?thesis by simp
              next
                case Inr_get1: (Inr val1)
                from get_value_at_path_type[OF slot1_typed Inr_get1] obtain pathTy1 where
                  pathTy1_eq: "type_at_path env (storeTyping ! addr1) path1 = Some pathTy1" and
                  val1_typed: "value_has_type env val1 pathTy1"
                  by auto
                with path1_ty
                have val1_typed_lhsTy: "value_has_type env val1 (apply_subst (IS_TyArgs state) lhsTy)"
                  by simp
                show ?thesis
                proof (cases "get_value_at_path (IS_Store state ! addr2) path2")
                  case (Inl err2)
                  from get_value_at_path_error_is_runtime[OF slot2_typed path2_ty Inl]
                  have err2_eq: "err2 = RuntimeError" .
                  have interp_err: "interp_statement (Suc fuel) state
                      (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inl RuntimeError"
                    using Inr_lhs ap1_eq Inr_rhs ap2_eq Inr_get1 Inl err2_eq by simp
                  with CoreStmt_Swap NotGhost show ?thesis by simp
                next
                  case Inr_get2: (Inr val2)
                  from get_value_at_path_type[OF slot2_typed Inr_get2] obtain pathTy2 where
                    pathTy2_eq: "type_at_path env (storeTyping ! addr2) path2 = Some pathTy2" and
                    val2_typed: "value_has_type env val2 pathTy2"
                    by auto
                  with path2_ty
                  have val2_typed_lhsTy: "value_has_type env val2 (apply_subst (IS_TyArgs state) lhsTy)"
                    by simp
                  \<comment> \<open>First update: put val2 into slot1 at path1.\<close>
                  show ?thesis
                  proof (cases "update_value_at_path (IS_Store state ! addr1) path1 val2")
                    case (Inl err)
                    from update_value_at_path_error_is_runtime[OF slot1_typed path1_ty Inl]
                    have "err = RuntimeError" .
                    then have interp_err: "interp_statement (Suc fuel) state
                        (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inl RuntimeError"
                      using Inr_lhs ap1_eq Inr_rhs ap2_eq Inr_get1 Inr_get2 Inl by simp
                    with CoreStmt_Swap NotGhost show ?thesis by simp
                  next
                    case Inr_upd1: (Inr new_val1)
                    from update_value_at_path_preserves_type[OF slot1_typed Inr_upd1 path1_ty val2_typed_lhsTy]
                    have new_val1_typed: "value_has_type env new_val1 (storeTyping ! addr1)" .
                    \<comment> \<open>Build intermediate store1 where slot addr1 has new_val1.\<close>
                    let ?store1 = "(IS_Store state)[addr1 := new_val1]"
                    let ?state1 = "state \<lparr> IS_Store := ?store1 \<rparr>"
                    from state_matches_env_update_store[OF "4.prems"(1) addr1_valid
                        new_val1_typed refl]
                    have state1_sme: "state_matches_env ?state1 env storeTyping" .
                    \<comment> \<open>Second update: put val1 into slot2 at path2 in the intermediate store.\<close>
                    have store1_len: "length ?store1 = length (IS_Store state)" by simp
                    from addr2_valid store1_len have addr2_valid1: "addr2 < length ?store1" by simp
                    from state1_sme addr2_valid1
                    have slot2_store1_typed:
                        "value_has_type env (?store1 ! addr2) (storeTyping ! addr2)"
                      unfolding state_matches_env_def store_well_typed_def by simp
                    show ?thesis
                    proof (cases "update_value_at_path (?store1 ! addr2) path2 val1")
                      case (Inl err)
                      from update_value_at_path_error_is_runtime[OF slot2_store1_typed path2_ty Inl]
                      have "err = RuntimeError" .
                      then have interp_err: "interp_statement (Suc fuel) state
                          (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inl RuntimeError"
                        using Inr_lhs ap1_eq Inr_rhs ap2_eq Inr_get1 Inr_get2 Inr_upd1 Inl
                        by (simp add: Let_def)
                      with CoreStmt_Swap NotGhost show ?thesis by simp
                    next
                      case Inr_upd2: (Inr new_val2)
                      from update_value_at_path_preserves_type[OF slot2_store1_typed Inr_upd2 path2_ty val1_typed_lhsTy]
                      have new_val2_typed: "value_has_type env new_val2 (storeTyping ! addr2)" .
                      \<comment> \<open>Build the final state as an update of the intermediate state.\<close>
                      let ?state2 = "?state1 \<lparr> IS_Store := (IS_Store ?state1)[addr2 := new_val2] \<rparr>"
                      have addr2_valid_state1: "addr2 < length (IS_Store ?state1)"
                        using addr2_valid1 by simp
                      from state_matches_env_update_store[OF state1_sme addr2_valid_state1
                          new_val2_typed refl]
                      have state2_sme: "state_matches_env ?state2 env storeTyping" .
                      have interp_eq: "interp_statement (Suc fuel) state
                          (CoreStmt_Swap NotGhost lhsTm rhsTm) = Inr (Continue ?state2)"
                        using Inr_lhs ap1_eq Inr_rhs ap2_eq Inr_get1 Inr_get2 Inr_upd1 Inr_upd2
                        by (simp add: Let_def)
                      have ext: "storeTyping_extends storeTyping storeTyping"
                        using storeTyping_extends_refl .
                      from state2_sme ext interp_eq env'_eq CoreStmt_Swap NotGhost
                      show ?thesis by auto
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      next
        case (CoreStmt_Return tm)
        \<comment> \<open>Return: evaluate the term; if successful, return the value.\<close>
        from typing CoreStmt_Return have
          tm_ty: "core_term_type env NotGhost tm = Some (TE_ReturnType env)" and
          env'_eq: "env' = env"
          by (auto split: if_splits)
        from IH_term[OF "4.prems"(1,2) tm_ty]
        have tm_sound: "sound_term_result state env (TE_ReturnType env) (interp_term fuel state tm)" .
        show ?thesis proof (cases "interp_term fuel state tm")
          case (Inl err)
          with tm_sound have "sound_error_result err" by simp
          with Inl CoreStmt_Return show ?thesis by simp
        next
          case (Inr val)
          with tm_sound
          have vht: "value_has_type env val (apply_subst (IS_TyArgs state) (TE_ReturnType env))"
            by simp
          have interp_eq: "interp_statement (Suc fuel) state (CoreStmt_Return tm)
                          = Inr (Return state val)"
            using Inr by simp
          \<comment> \<open>Use env itself as env_mid (reflexivity of tyenv_fixed_eq).\<close>
          have "sound_statement_result env env' storeTyping (Inr (Return state val))"
            unfolding env'_eq using vht "4.prems"(1) "4.prems"(2)
            by (auto intro!: exI[of _ env] exI[of _ storeTyping] tyenv_fixed_eq_refl
                              storeTyping_extends_refl)
          with CoreStmt_Return interp_eq show ?thesis by simp
        qed
      next
        case (CoreStmt_Assert condOpt proofBody)
        \<comment> \<open>Assert is a runtime no-op: Inr (Continue state), and env' = env.\<close>
        from typing CoreStmt_Assert have env'_eq: "env' = env"
          by (auto simp: Let_def split: if_splits option.splits)
        have interp_eq: "interp_statement (Suc fuel) state (CoreStmt_Assert condOpt proofBody)
                        = Inr (Continue state)"
          by simp
        from "4.prems"(1) env'_eq have "state_matches_env state env' storeTyping" by simp
        with CoreStmt_Assert interp_eq show ?thesis using storeTyping_extends_refl by auto
      next
        case (CoreStmt_Assume tm)
        \<comment> \<open>Assume is a runtime no-op: Inr (Continue state), and env' = env.\<close>
        from typing CoreStmt_Assume have env'_eq: "env' = env"
          by (auto split: if_splits)
        have interp_eq: "interp_statement (Suc fuel) state (CoreStmt_Assume tm)
                        = Inr (Continue state)"
          by simp
        from "4.prems"(1) env'_eq have "state_matches_env state env' storeTyping" by simp
        with CoreStmt_Assume interp_eq show ?thesis using storeTyping_extends_refl by auto
      next
        case (CoreStmt_While whileGhost condTm invars decr bodyStmts)
        \<comment> \<open>While: Ghost mode is a no-op at runtime. NotGhost mode evaluates the
            condition; if True, runs the body and recurses on the loop
            (via the statement-level fuel IH) after restore_scope; if False,
            returns Continue state. The typechecker's result env equals the
            input env. \<close>
        from typing CoreStmt_While have env'_eq: "env' = env"
          by (auto split: if_splits option.splits CoreType.splits)
        show ?thesis
        proof (cases whileGhost)
          case Ghost
          have interp_eq: "interp_statement (Suc fuel) state
                            (CoreStmt_While whileGhost condTm invars decr bodyStmts)
                            = Inr (Continue state)"
            using Ghost by simp
          from "4.prems"(1) env'_eq have "state_matches_env state env' storeTyping" by simp
          with CoreStmt_While interp_eq show ?thesis
            using storeTyping_extends_refl by auto
        next
          case NotGhost
          note whileGhost_eq = NotGhost
          \<comment> \<open>The loop body typechecks in env with TE_ProofGoal reset to None
              (a loop body is not at the top level of an assert proof). \<close>
          define benv where "benv = env \<lparr> TE_ProofGoal := None \<rparr>"
          from typing CoreStmt_While NotGhost have
            cond_ty: "core_term_type env NotGhost condTm = Some CoreTy_Bool" and
            body_typed: "\<exists>bodyEnv'. core_statement_list_type benv NotGhost bodyStmts
                                    = Some bodyEnv'"
            unfolding benv_def
            by (auto split: if_splits option.splits CoreType.splits)
          \<comment> \<open>Core typing result: CoreStmt_While yields env' = env. We need the
              recursive-call premise of that exact shape. \<close>
          have while_typed: "core_statement_type env NotGhost
              (CoreStmt_While whileGhost condTm invars decr bodyStmts) = Some env"
            using typing CoreStmt_While env'_eq by simp
          from IH_term[OF "4.prems"(1,2) cond_ty]
          have cond_sound: "sound_term_result state env CoreTy_Bool (interp_term fuel state condTm)" .
          have IH_stmts: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmts0 env0'.
                  state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                  tyenv_well_formed env0 \<Longrightarrow>
                  core_statement_list_type env0 NotGhost stmts0 = Some env0' \<Longrightarrow>
                  sound_statement_result env0 env0' storeTyping0
                    (interp_statement_list fuel state0 stmts0)"
            using Suc.IH(5) by simp
          have IH_stmt: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmt0 env0'.
                  state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                  tyenv_well_formed env0 \<Longrightarrow>
                  core_statement_type env0 NotGhost stmt0 = Some env0' \<Longrightarrow>
                  sound_statement_result env0 env0' storeTyping0
                    (interp_statement fuel state0 stmt0)"
            using Suc.IH(4) by simp
          show ?thesis
          proof (cases "interp_term fuel state condTm")
            case (Inl err)
            with cond_sound have "sound_error_result err" by simp
            moreover have "interp_statement (Suc fuel) state
                (CoreStmt_While whileGhost condTm invars decr bodyStmts) = Inl err"
              using Inl NotGhost by simp
            ultimately show ?thesis using CoreStmt_While by simp
          next
            case (Inr condVal)
            note cond_eval = Inr
            from cond_sound Inr have cond_typed: "value_has_type env condVal CoreTy_Bool" by simp
            then obtain b where condVal_eq: "condVal = CV_Bool b"
              by (cases condVal) (auto split: CoreType.splits)
            show ?thesis
            proof (cases b)
              case False
              have interp_eq: "interp_statement (Suc fuel) state
                    (CoreStmt_While whileGhost condTm invars decr bodyStmts)
                    = Inr (Continue state)"
                using cond_eval condVal_eq False NotGhost by simp
              from "4.prems"(1) env'_eq have "state_matches_env state env' storeTyping" by simp
              with CoreStmt_While interp_eq show ?thesis
                using storeTyping_extends_refl by auto
            next
              case True
              from body_typed obtain bodyEnv' where
                body_ty: "core_statement_list_type benv NotGhost bodyStmts = Some bodyEnv'"
                by blast
              \<comment> \<open>state_matches_env / tyenv_well_formed transfer from env to benv
                  (benv differs only in TE_ProofGoal, which they ignore). \<close>
              have sme_benv: "state_matches_env state benv storeTyping"
                using "4.prems"(1) unfolding benv_def by simp
              have wf_benv: "tyenv_well_formed benv"
                using "4.prems"(2) unfolding benv_def
                by (simp add: tyenv_well_formed_TE_ProofGoal_irrelevant)
              from IH_stmts[OF sme_benv wf_benv body_ty]
              have "sound_statement_result benv bodyEnv' storeTyping
                  (interp_statement_list fuel state bodyStmts)" .
              \<comment> \<open>sound_statement_result ignores TE_ProofGoal of its first env, so we
                  may restate it with env in place of benv. \<close>
              hence body_sound: "sound_statement_result env bodyEnv' storeTyping
                  (interp_statement_list fuel state bodyStmts)"
                unfolding benv_def by simp
              from core_statement_list_type_preserves_well_formed[OF body_ty wf_benv]
              have wf_bodyEnv': "tyenv_well_formed bodyEnv'" .
              from core_statement_list_type_fixed_eq[OF body_ty]
              have "tyenv_fixed_eq benv bodyEnv'" .
              hence fxeq_body: "tyenv_fixed_eq env bodyEnv'"
                unfolding benv_def by simp
              show ?thesis
              proof (cases "interp_statement_list fuel state bodyStmts")
                case (Inl body_err)
                with body_sound have "sound_error_result body_err" by simp
                moreover have "interp_statement (Suc fuel) state
                    (CoreStmt_While whileGhost condTm invars decr bodyStmts) = Inl body_err"
                  using cond_eval condVal_eq True Inl NotGhost by simp
                ultimately show ?thesis using CoreStmt_While by simp
              next
                case (Inr bodyRes)
                note body_eval = Inr
                show ?thesis
                proof (cases bodyRes)
                  case (Continue state1)
                  from body_sound body_eval Continue obtain bodyStoreTyping where
                    sme_body: "state_matches_env state1 bodyEnv' bodyStoreTyping" and
                    ext_body: "storeTyping_extends storeTyping bodyStoreTyping"
                    by auto
                  from body_eval Continue
                  have body_list_eq: "interp_statement_list fuel state bodyStmts
                                      = Inr (Continue state1)" by simp
                  from interp_statement_list_preserves_globals[OF body_list_eq]
                  have globals_eq: "IS_Globals state1 = IS_Globals state" .
                  from interp_statement_list_preserves_functions[OF body_list_eq]
                  have functions_eq: "IS_Functions state1 = IS_Functions state" .
                  from interp_statement_list_preserves_IS_DefaultCtors_Continue[OF body_list_eq]
                  have default_ctors_eq: "IS_DefaultCtors state1 = IS_DefaultCtors state" .
                  from fxeq_body have dt_eq:
                    "TE_DataCtors env = TE_DataCtors bodyEnv'"
                    "TE_Datatypes env = TE_Datatypes bodyEnv'"
                    "TE_GhostDatatypes env = TE_GhostDatatypes bodyEnv'"
                    unfolding tyenv_fixed_eq_def by simp_all
                  have sme_rs: "state_matches_env (restore_scope state state1)
                                  env storeTyping"
                    using restore_scope_sound[OF "4.prems"(1) sme_body ext_body
                                                 globals_eq functions_eq default_ctors_eq
                                                 dt_eq(1) dt_eq(2) dt_eq(3)
                                                 "4.prems"(2) wf_bodyEnv'] .
                  \<comment> \<open>Recursive call: apply the fuel-level statement IH. \<close>
                  from IH_stmt[OF sme_rs "4.prems"(2) while_typed]
                  have rec_sound: "sound_statement_result env env storeTyping
                      (interp_statement fuel (restore_scope state state1)
                         (CoreStmt_While whileGhost condTm invars decr bodyStmts))"
                    using whileGhost_eq by simp
                  have interp_eq: "interp_statement (Suc fuel) state
                      (CoreStmt_While whileGhost condTm invars decr bodyStmts)
                      = interp_statement fuel (restore_scope state state1)
                         (CoreStmt_While whileGhost condTm invars decr bodyStmts)"
                    using cond_eval condVal_eq True body_eval Continue NotGhost by simp
                  from rec_sound interp_eq env'_eq CoreStmt_While show ?thesis by simp
                next
                  case (Return state1 retVal)
                  from body_sound body_eval Return have
                    ret_typed: "value_has_type env retVal
                                   (apply_subst (IS_TyArgs state1) (TE_ReturnType env))" and
                    body_return_ex: "\<exists>env_mid storeTyping'.
                        tyenv_fixed_eq env env_mid \<and> tyenv_fixed_eq env_mid bodyEnv' \<and>
                        tyenv_well_formed env_mid \<and>
                        state_matches_env state1 env_mid storeTyping' \<and>
                        storeTyping_extends storeTyping storeTyping'"
                    by auto
                  from body_return_ex obtain env_mid bodyStoreTyping where
                    fxeq1: "tyenv_fixed_eq env env_mid" and
                    fxeq2: "tyenv_fixed_eq env_mid bodyEnv'" and
                    wf_mid: "tyenv_well_formed env_mid" and
                    sme_body: "state_matches_env state1 env_mid bodyStoreTyping" and
                    ext_body: "storeTyping_extends storeTyping bodyStoreTyping"
                    by blast
                  from body_eval Return
                  have body_list_eq: "interp_statement_list fuel state bodyStmts
                                      = Inr (Return state1 retVal)" by simp
                  from interp_statement_list_return_preserves_globals[OF body_list_eq]
                  have globals_eq: "IS_Globals state1 = IS_Globals state" .
                  from interp_statement_list_return_preserves_functions[OF body_list_eq]
                  have functions_eq: "IS_Functions state1 = IS_Functions state" .
                  from interp_statement_list_preserves_IS_TyArgs_Return[OF body_list_eq]
                  have tyargs_eq: "IS_TyArgs state1 = IS_TyArgs state" .
                  from interp_statement_list_preserves_IS_DefaultCtors_Return[OF body_list_eq]
                  have default_ctors_eq: "IS_DefaultCtors state1 = IS_DefaultCtors state" .
                  from fxeq1 have dt_eq:
                    "TE_DataCtors env = TE_DataCtors env_mid"
                    "TE_Datatypes env = TE_Datatypes env_mid"
                    "TE_GhostDatatypes env = TE_GhostDatatypes env_mid"
                    unfolding tyenv_fixed_eq_def by simp_all
                  have sme_rs: "state_matches_env (restore_scope state state1)
                                  env storeTyping"
                    using restore_scope_sound[OF "4.prems"(1) sme_body ext_body
                                                 globals_eq functions_eq default_ctors_eq
                                                 dt_eq(1) dt_eq(2) dt_eq(3)
                                                 "4.prems"(2) wf_mid] .
                  have interp_eq: "interp_statement (Suc fuel) state
                      (CoreStmt_While whileGhost condTm invars decr bodyStmts)
                      = Inr (Return (restore_scope state state1) retVal)"
                    using cond_eval condVal_eq True body_eval Return NotGhost by simp
                  from ret_typed tyargs_eq
                  have ret_typed': "value_has_type env retVal
                                       (apply_subst (IS_TyArgs state) (TE_ReturnType env))"
                    by simp
                  have "sound_statement_result env env' storeTyping
                         (Inr (Return (restore_scope state state1) retVal))"
                    unfolding env'_eq
                    using ret_typed' sme_rs "4.prems"(2)
                    by (auto intro!: exI[of _ env] exI[of _ storeTyping]
                                     tyenv_fixed_eq_refl storeTyping_extends_refl)
                  with interp_eq CoreStmt_While show ?thesis by simp
                qed
              qed
            qed
          qed
        qed
      next
        case (CoreStmt_Match matchGhost scrut arms)
        \<comment> \<open>Match: in Ghost mode (at the statement level) the interpreter is a
            no-op. In NotGhost mode the interpreter evaluates the scrutinee,
            picks a matching arm body, runs it, and calls restore_scope on the
            result. The typechecker's result env equals the input env (body
            scope is discarded). \<close>
        from typing CoreStmt_Match have env'_eq: "env' = env"
          by (auto simp: Let_def split: if_splits option.splits)
        show ?thesis
        proof (cases matchGhost)
          case Ghost
          \<comment> \<open>Ghost match: interpreter returns Continue state unchanged. \<close>
          have interp_eq: "interp_statement (Suc fuel) state
                            (CoreStmt_Match matchGhost scrut arms) = Inr (Continue state)"
            using Ghost by simp
          from "4.prems"(1) env'_eq have "state_matches_env state env' storeTyping" by simp
          with CoreStmt_Match interp_eq show ?thesis
            using storeTyping_extends_refl by auto
        next
          case NotGhost
          note matchGhost_eq = NotGhost
          \<comment> \<open>Arm bodies typecheck in env with TE_ProofGoal reset to None (a match
              arm is not at the top level of an assert proof). \<close>
          define benv where "benv = env \<lparr> TE_ProofGoal := None \<rparr>"
          from typing CoreStmt_Match NotGhost obtain scrutTy where
            scrut_ty: "core_term_type env NotGhost scrut = Some scrutTy" and
            bodies_typed: "list_all (\<lambda>body.
              core_statement_list_type benv NotGhost body \<noteq> None) (map snd arms)"
            unfolding benv_def
            by (auto simp: Let_def split: if_splits option.splits)
          have sme_benv: "state_matches_env state benv storeTyping"
            using "4.prems"(1) unfolding benv_def by simp
          have wf_benv: "tyenv_well_formed benv"
            using "4.prems"(2) unfolding benv_def
            by (simp add: tyenv_well_formed_TE_ProofGoal_irrelevant)
          from IH_term[OF "4.prems"(1,2) scrut_ty]
          have scrut_sound: "sound_term_result state env scrutTy (interp_term fuel state scrut)" .
          have IH_stmts: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmts0 env0'.
                  state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                  tyenv_well_formed env0 \<Longrightarrow>
                  core_statement_list_type env0 NotGhost stmts0 = Some env0' \<Longrightarrow>
                  sound_statement_result env0 env0' storeTyping0
                    (interp_statement_list fuel state0 stmts0)"
            using Suc.IH(5) by simp
          show ?thesis
          proof (cases "interp_term fuel state scrut")
            case (Inl err)
            with scrut_sound have "sound_error_result err" by simp
            with Inl CoreStmt_Match NotGhost show ?thesis by simp
          next
            case (Inr scrutVal)
            note scrut_eval = Inr
            show ?thesis
            proof (cases "find_matching_arm scrutVal arms")
              case (Inl match_err)
              from find_matching_arm_error[OF Inl] have err_eq: "match_err = RuntimeError" .
              have interp_err: "interp_statement (Suc fuel) state
                  (CoreStmt_Match matchGhost scrut arms) = Inl RuntimeError"
                using scrut_eval Inl err_eq NotGhost by simp
              with CoreStmt_Match show ?thesis by simp
            next
              case (Inr armBody)
              note match_eq = Inr
              from find_matching_arm_in_set[OF match_eq]
              obtain pat where arm_in: "(pat, armBody) \<in> set arms" by auto
              from arm_in have body_in: "armBody \<in> set (map snd arms)" by force
              from bodies_typed body_in obtain bodyEnv' where
                body_typed: "core_statement_list_type benv NotGhost armBody = Some bodyEnv'"
                by (auto simp: list_all_iff)
              from IH_stmts[OF sme_benv wf_benv body_typed]
              have "sound_statement_result benv bodyEnv' storeTyping
                  (interp_statement_list fuel state armBody)" .
              \<comment> \<open>sound_statement_result ignores TE_ProofGoal of its first env. \<close>
              hence body_sound: "sound_statement_result env bodyEnv' storeTyping
                  (interp_statement_list fuel state armBody)"
                unfolding benv_def by simp
              from core_statement_list_type_preserves_well_formed[OF body_typed wf_benv]
              have wf_bodyEnv': "tyenv_well_formed bodyEnv'" .
              from core_statement_list_type_fixed_eq[OF body_typed]
              have "tyenv_fixed_eq benv bodyEnv'" .
              hence fxeq_body: "tyenv_fixed_eq env bodyEnv'"
                unfolding benv_def by simp
              show ?thesis
              proof (cases "interp_statement_list fuel state armBody")
                case (Inl body_err)
                with body_sound have "sound_error_result body_err" by simp
                moreover have "interp_statement (Suc fuel) state
                      (CoreStmt_Match matchGhost scrut arms) = Inl body_err"
                  using scrut_eval match_eq Inl NotGhost by simp
                ultimately show ?thesis using CoreStmt_Match by simp
              next
                case (Inr bodyRes)
                note body_eval = Inr
                show ?thesis
                proof (cases bodyRes)
                  case (Continue state1)
                  from body_sound body_eval Continue obtain bodyStoreTyping where
                    sme_body: "state_matches_env state1 bodyEnv' bodyStoreTyping" and
                    ext_body: "storeTyping_extends storeTyping bodyStoreTyping"
                    by auto
                  \<comment> \<open>Globals/functions preserved through the body. \<close>
                  from body_eval Continue
                  have body_list_eq: "interp_statement_list fuel state armBody
                                      = Inr (Continue state1)" by simp
                  from interp_statement_list_preserves_globals[OF body_list_eq]
                  have globals_eq: "IS_Globals state1 = IS_Globals state" .
                  from interp_statement_list_preserves_functions[OF body_list_eq]
                  have functions_eq: "IS_Functions state1 = IS_Functions state" .
                  from interp_statement_list_preserves_IS_DefaultCtors_Continue[OF body_list_eq]
                  have default_ctors_eq: "IS_DefaultCtors state1 = IS_DefaultCtors state" .
                  \<comment> \<open>Apply restore_scope_sound. \<close>
                  from fxeq_body have dt_eq:
                    "TE_DataCtors env = TE_DataCtors bodyEnv'"
                    "TE_Datatypes env = TE_Datatypes bodyEnv'"
                    "TE_GhostDatatypes env = TE_GhostDatatypes bodyEnv'"
                    unfolding tyenv_fixed_eq_def by simp_all
                  have sme_rs: "state_matches_env (restore_scope state state1)
                                  env storeTyping"
                    using restore_scope_sound[OF "4.prems"(1) sme_body ext_body
                                                 globals_eq functions_eq default_ctors_eq
                                                 dt_eq(1) dt_eq(2) dt_eq(3)
                                                 "4.prems"(2) wf_bodyEnv'] .
                  have interp_eq: "interp_statement (Suc fuel) state
                      (CoreStmt_Match matchGhost scrut arms)
                      = Inr (Continue (restore_scope state state1))"
                    using scrut_eval match_eq body_eval Continue NotGhost by simp
                  from sme_rs interp_eq env'_eq CoreStmt_Match
                  show ?thesis using storeTyping_extends_refl by auto
                next
                  case (Return state1 retVal)
                  from body_sound body_eval Return have
                    ret_typed: "value_has_type env retVal
                                   (apply_subst (IS_TyArgs state1) (TE_ReturnType env))" and
                    body_return_ex: "\<exists>env_mid storeTyping'.
                        tyenv_fixed_eq env env_mid \<and> tyenv_fixed_eq env_mid bodyEnv' \<and>
                        tyenv_well_formed env_mid \<and>
                        state_matches_env state1 env_mid storeTyping' \<and>
                        storeTyping_extends storeTyping storeTyping'"
                    by auto
                  from body_return_ex obtain env_mid bodyStoreTyping where
                    fxeq1: "tyenv_fixed_eq env env_mid" and
                    fxeq2: "tyenv_fixed_eq env_mid bodyEnv'" and
                    wf_mid: "tyenv_well_formed env_mid" and
                    sme_body: "state_matches_env state1 env_mid bodyStoreTyping" and
                    ext_body: "storeTyping_extends storeTyping bodyStoreTyping"
                    by blast
                  \<comment> \<open>Globals/functions preserved through the body (Return). \<close>
                  from body_eval Return
                  have body_list_eq: "interp_statement_list fuel state armBody
                                      = Inr (Return state1 retVal)" by simp
                  from interp_statement_list_return_preserves_globals[OF body_list_eq]
                  have globals_eq: "IS_Globals state1 = IS_Globals state" .
                  from interp_statement_list_return_preserves_functions[OF body_list_eq]
                  have functions_eq: "IS_Functions state1 = IS_Functions state" .
                  from interp_statement_list_preserves_IS_TyArgs_Return[OF body_list_eq]
                  have tyargs_eq: "IS_TyArgs state1 = IS_TyArgs state" .
                  from interp_statement_list_preserves_IS_DefaultCtors_Return[OF body_list_eq]
                  have default_ctors_eq: "IS_DefaultCtors state1 = IS_DefaultCtors state" .
                  \<comment> \<open>Apply restore_scope_sound with env_mid. \<close>
                  from fxeq1 have dt_eq:
                    "TE_DataCtors env = TE_DataCtors env_mid"
                    "TE_Datatypes env = TE_Datatypes env_mid"
                    "TE_GhostDatatypes env = TE_GhostDatatypes env_mid"
                    unfolding tyenv_fixed_eq_def by simp_all
                  have sme_rs: "state_matches_env (restore_scope state state1)
                                  env storeTyping"
                    using restore_scope_sound[OF "4.prems"(1) sme_body ext_body
                                                 globals_eq functions_eq default_ctors_eq
                                                 dt_eq(1) dt_eq(2) dt_eq(3)
                                                 "4.prems"(2) wf_mid] .
                  have interp_eq: "interp_statement (Suc fuel) state
                      (CoreStmt_Match matchGhost scrut arms)
                      = Inr (Return (restore_scope state state1) retVal)"
                    using scrut_eval match_eq body_eval Return NotGhost by simp
                  from ret_typed tyargs_eq
                  have ret_typed': "value_has_type env retVal
                                       (apply_subst (IS_TyArgs state) (TE_ReturnType env))"
                    by simp
                  \<comment> \<open>Build the Return-case sound_statement_result: use env itself as
                      env_mid (fxeq refl both sides) with storeTyping unchanged. \<close>
                  have "sound_statement_result env env' storeTyping
                         (Inr (Return (restore_scope state state1) retVal))"
                    unfolding env'_eq
                    using ret_typed' sme_rs "4.prems"(2)
                    by (auto intro!: exI[of _ env] exI[of _ storeTyping]
                                     tyenv_fixed_eq_refl storeTyping_extends_refl)
                  with interp_eq CoreStmt_Match show ?thesis by simp
                qed
              qed
            qed
          qed
        qed
      next
        case (CoreStmt_ShowHide showOrHide name)
        \<comment> \<open>ShowHide is a runtime no-op: Inr (Continue state), and env' = env.\<close>
        from typing CoreStmt_ShowHide have env'_eq: "env' = env" by simp
        have interp_eq: "interp_statement (Suc fuel) state (CoreStmt_ShowHide showOrHide name)
                        = Inr (Continue state)"
          by simp
        from "4.prems"(1) env'_eq have "state_matches_env state env' storeTyping" by simp
        with CoreStmt_ShowHide interp_eq show ?thesis using storeTyping_extends_refl by auto
      qed
    qed
  next
    case 5
    show ?case proof (intro impI)
      assume typing: "core_statement_list_type env NotGhost stmts = Some env'"
      have IH_stmt: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmt0 env0'.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                core_statement_type env0 NotGhost stmt0 = Some env0' \<Longrightarrow>
                sound_statement_result env0 env0' storeTyping0 (interp_statement fuel state0 stmt0)"
        by (simp add: "5.prems"(1,2) Suc.IH(4))
      have IH_stmts: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmts0 env0'.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                core_statement_list_type env0 NotGhost stmts0 = Some env0' \<Longrightarrow>
                sound_statement_result env0 env0' storeTyping0 (interp_statement_list fuel state0 stmts0)"
        by (simp add: "5.prems"(1,2) Suc.IH(5))
      show "sound_statement_result env env' storeTyping (interp_statement_list (Suc fuel) state stmts)"
      proof (cases stmts)
        case Nil
        with typing have "env' = env" by simp
        with "5.prems"(1) show ?thesis using Nil storeTyping_extends_refl by auto
      next
        case (Cons stmt0 stmts0)
        from typing Cons obtain env_mid where
          stmt_ty: "core_statement_type env NotGhost stmt0 = Some env_mid" and
          rest_ty: "core_statement_list_type env_mid NotGhost stmts0 = Some env'"
          by (auto split: option.splits)
        from IH_stmt[OF "5.prems"(1,2) stmt_ty]
        have stmt_sound: "sound_statement_result env env_mid storeTyping
                            (interp_statement fuel state stmt0)" .
        show ?thesis proof (cases "interp_statement fuel state stmt0")
          case (Inl err)
          with stmt_sound have "sound_error_result err" by simp
          with Inl Cons show ?thesis by simp
        next
          case (Inr result)
          then show ?thesis proof (cases result)
            case (Continue state')
            with Inr stmt_sound obtain storeTyping_mid where
              sme: "state_matches_env state' env_mid storeTyping_mid" and
              ext1: "storeTyping_extends storeTyping storeTyping_mid"
              by auto
            from core_statement_type_preserves_well_formed[OF stmt_ty "5.prems"(2)]
            have wf_mid: "tyenv_well_formed env_mid" .
            from IH_stmts[OF sme wf_mid rest_ty]
            have rest_sound: "sound_statement_result env_mid env' storeTyping_mid
                                (interp_statement_list fuel state' stmts0)" .
            from Inr Continue
            have interp_stmt_eq: "interp_statement fuel state stmt0 = Inr (Continue state')"
              by simp
            show ?thesis proof (cases "interp_statement_list fuel state' stmts0")
              case (Inl err)
              from rest_sound Inl have "sound_error_result err" by simp
              then show ?thesis using Cons interp_stmt_eq Inl by simp
            next
              case (Inr result2)
              then show ?thesis proof (cases result2)
                case (Continue state'')
                from rest_sound Inr Continue
                obtain storeTyping'' where
                  sme'': "state_matches_env state'' env' storeTyping''" and
                  ext2: "storeTyping_extends storeTyping_mid storeTyping''"
                  by auto
                from storeTyping_extends_trans[OF ext1 ext2]
                have "storeTyping_extends storeTyping storeTyping''" .
                with sme'' show ?thesis using Cons interp_stmt_eq Inr Continue by auto
              next
                case (Return state'' retVal2)
                \<comment> \<open>The rest of the list returned. We get env_mid2 between env_mid and env'.
                   We need env_mid2 between env and env'. Use monotonicity of the first stmt.\<close>
                from rest_sound Inr Return
                obtain env_mid2 storeTyping2 where
                  vht: "value_has_type env_mid retVal2
                          (apply_subst (IS_TyArgs state'') (TE_ReturnType env_mid))" and
                  sub1: "tyenv_fixed_eq env_mid env_mid2" and
                  sub2: "tyenv_fixed_eq env_mid2 env'" and
                  wf_env_mid2: "tyenv_well_formed env_mid2" and
                  sme2: "state_matches_env state'' env_mid2 storeTyping2" and
                  ext2: "storeTyping_extends storeTyping_mid storeTyping2"
                  by auto
                from storeTyping_extends_trans[OF ext1 ext2]
                have ext_full: "storeTyping_extends storeTyping storeTyping2" .
                from core_statement_type_fixed_eq[OF stmt_ty]
                have sub_env_envmid: "tyenv_fixed_eq env env_mid" .
                from tyenv_fixed_eq_trans[OF this sub1]
                have sub_env_mid2: "tyenv_fixed_eq env env_mid2" .
                \<comment> \<open>Transfer value_has_type from env_mid to env. TE_ReturnType agrees by
                    tyenv_fixed_eq, and the env's other read fields agree as well.\<close>
                from sub_env_envmid
                have env_fields_eq:
                  "TE_DataCtors env = TE_DataCtors env_mid"
                  "TE_Datatypes env = TE_Datatypes env_mid"
                  "TE_TypeVars env = TE_TypeVars env_mid"
                  "TE_GhostDatatypes env = TE_GhostDatatypes env_mid"
                  "TE_RuntimeTypeVars env = TE_RuntimeTypeVars env_mid"
                  "TE_ReturnType env = TE_ReturnType env_mid"
                  unfolding tyenv_fixed_eq_def by simp_all
                hence vht_env: "value_has_type env retVal2
                                  (apply_subst (IS_TyArgs state'') (TE_ReturnType env))"
                  using vht value_has_type_cong_env by metis
                from \<open>interp_statement_list fuel state' stmts0 = Inr result2\<close> Return
                have interp_rest_eq: "interp_statement_list fuel state' stmts0 = Inr (Return state'' retVal2)"
                  by simp
                from vht_env sub_env_mid2 sub2 wf_env_mid2 sme2 ext_full
                show ?thesis
                  using Cons interp_stmt_eq interp_rest_eq by auto
              qed
            qed
          next
            case (Return state' retVal)
            \<comment> \<open>The first statement returned. We get env_mid2 between env and env_mid.
               We need env_mid2 between env and env'. Use monotonicity of the rest.\<close>
            with Inr stmt_sound obtain env_mid2 storeTyping2 where
              vht: "value_has_type env retVal
                       (apply_subst (IS_TyArgs state') (TE_ReturnType env))" and
              sub1: "tyenv_fixed_eq env env_mid2" and
              sub2: "tyenv_fixed_eq env_mid2 env_mid" and
              wf_env_mid2: "tyenv_well_formed env_mid2" and
              sme2: "state_matches_env state' env_mid2 storeTyping2" and
              ext: "storeTyping_extends storeTyping storeTyping2"
              by auto
            from core_statement_list_type_fixed_eq[OF rest_ty]
            have "tyenv_fixed_eq env_mid env'" .
            from tyenv_fixed_eq_trans[OF sub2 this]
            have "tyenv_fixed_eq env_mid2 env'" .
            with vht sub1 wf_env_mid2 sme2 ext
            show ?thesis using Inr Return Cons by auto
          qed
        qed
      qed
    qed
  next
    case 6
    note fn_lookup    = "6.prems"(1)
     and not_ghost    = "6.prems"(2)
     and args_typed   = "6.prems"(3)
     and retTy_eq     = "6.prems"(4)
     and ty_len       = "6.prems"(5)
     and ty_wk        = "6.prems"(6)
     and ty_rt        = "6.prems"(7)
     and ref_writable = "6.prems"(8)
     and state_env    = "6.prems"(9)
     and wf_env       = "6.prems"(10)
    \<comment> \<open>Strip the leading state_matches_env / tyenv_well_formed assumptions
        from the term, lvalue and statement-list IHs so they match the shape
        expected by the helper lemma. \<close>
    have IH_term: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                  sound_term_result state' env' ty' (interp_term fuel state' tm')"
      using Suc.IH(1) by simp
    have IH_lvalue: "\<And>env' (state' :: 'w InterpState) storeTyping' tm' ty'.
                state_matches_env state' env' storeTyping' \<Longrightarrow>
                tyenv_well_formed env' \<Longrightarrow>
                is_writable_lvalue env' tm' \<and> core_term_type env' NotGhost tm' = Some ty' \<Longrightarrow>
                  sound_lvalue_result state' env' storeTyping' ty' (interp_writable_lvalue fuel state' tm')"
      using Suc.IH(3) by simp
    have IH_stmts: "\<And>env0 (state0 :: 'w InterpState) storeTyping0 stmts0 env0'.
                state_matches_env state0 env0 storeTyping0 \<Longrightarrow>
                tyenv_well_formed env0 \<Longrightarrow>
                core_statement_list_type env0 NotGhost stmts0 = Some env0' \<Longrightarrow>
                  sound_statement_result env0 env0' storeTyping0 (interp_statement_list fuel state0 stmts0)"
      using Suc.IH(5) by simp
    show ?case
      by (rule type_soundness_function_call
            [OF state_env wf_env fn_lookup not_ghost args_typed retTy_eq
                ty_len ty_wk ty_rt ref_writable IH_term IH_lvalue IH_stmts])
  }
qed


end

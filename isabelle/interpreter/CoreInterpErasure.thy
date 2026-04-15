theory CoreInterpErasure
  imports CoreInterp "../core/CoreTypeSubst" "../core/CoreStmtTypecheck"
begin

(* ========================================================================== *)
(* Helper: those-success implies all elements are Some                          *)
(* ========================================================================== *)

lemma those_all_some:
  assumes "those xs = Some ys"
  shows "list_all (\<lambda>t. t \<noteq> None) xs"
  using assms by (induction xs arbitrary: ys) (auto split: option.splits)


(* ========================================================================== *)
(* Main erasure theorem                                                         *)
(* ========================================================================== *)

(* Claim: running the interpreter on syntax that has had a type substitution
   applied to it gives the same result as running the interpreter on the
   original syntax, provided the original was well-typed in NotGhost mode.

   The substitution replaces CoreTy_Var nodes in any type embedded in the
   syntax. The interpreter is runtime-type-erased, so it only ever inspects
   types in one place: the target type of CoreTm_Cast. Well-typedness
   guarantees that target is an integer type, which is invariant under
   substitution. All other positions where substitution modifies syntax
   (LitArray elemTy, FunctionCall tyArgs, VariantCtor tyArgs, VarDecl ty,
   Fix/Obtain ty, Quantifier ty) are either ignored by the interpreter or
   live in ghost-only statements that never execute at runtime. *)

definition exec_result_erasure_eq
    :: "'w InterpState \<Rightarrow> CoreStatement list \<Rightarrow> CoreStatement list \<Rightarrow> nat \<Rightarrow> bool" where
  "exec_result_erasure_eq state stmts stmts' fuel \<equiv>
    interp_statement_list fuel state stmts = interp_statement_list fuel state stmts'"

lemma interp_erasure:
  fixes dummy :: "'w InterpState"
  shows
    "\<forall>(state :: 'w InterpState) env ty subst.
       core_term_type env NotGhost tm = Some ty \<longrightarrow>
         interp_term fuel state (apply_subst_to_term subst tm)
         = interp_term fuel state tm"
  and
    "\<forall>(state :: 'w InterpState) env types subst.
       map (core_term_type env NotGhost) tms = types \<and>
       list_all (\<lambda>ty. ty \<noteq> None) types \<longrightarrow>
         interp_term_list fuel state (map (apply_subst_to_term subst) tms)
         = interp_term_list fuel state tms"
  and
    "\<forall>(state :: 'w InterpState) env ty subst.
       core_term_type env NotGhost lvTm = Some ty \<longrightarrow>
         interp_writable_lvalue fuel state (apply_subst_to_term subst lvTm)
         = interp_writable_lvalue fuel state lvTm"
  and
    "\<forall>(state :: 'w InterpState) env env' subst.
       core_statement_type env NotGhost stmt = Some env' \<longrightarrow>
         interp_statement fuel state (apply_subst_to_stmt subst stmt)
         = interp_statement fuel state stmt"
  and
    "\<forall>(state :: 'w InterpState) env env' subst.
       core_statement_list_type env NotGhost stmts = Some env' \<longrightarrow>
         interp_statement_list fuel state (apply_subst_to_stmt_list subst stmts)
         = interp_statement_list fuel state stmts"
  and
    "\<forall>(state :: 'w InterpState) env subst.
       list_all (\<lambda>tm. \<exists>ty. core_term_type env NotGhost tm = Some ty) argTms \<longrightarrow>
         interp_function_call fuel state fnName (map (apply_subst_to_term subst) argTms)
         = interp_function_call fuel state fnName argTms"
proof (induction fuel arbitrary: tm tms lvTm stmt stmts fnName argTms rule: nat.induct)
  case zero
  {
    case 1 show ?case by simp
  next
    case 2 show ?case by simp
  next
    case 3 show ?case by simp
  next
    case 4 show ?case by simp
  next
    case 5 show ?case by simp
  next
    case 6 show ?case by simp
  }
next
  case (Suc fuel)
  note IH_term = Suc.IH(1)
  note IH_term_list = Suc.IH(2)
  note IH_lvalue = Suc.IH(3)
  note IH_stmt = Suc.IH(4)
  note IH_stmt_list = Suc.IH(5)
  note IH_call = Suc.IH(6)
  {
    case (1 tm) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and env ty subst
      assume typing: "core_term_type env NotGhost tm = Some ty"
      show "interp_term (Suc fuel) state (apply_subst_to_term subst tm)
            = interp_term (Suc fuel) state tm"
      proof (cases tm)
        case (CoreTm_LitBool b) then show ?thesis by simp
      next
        case (CoreTm_LitInt i) then show ?thesis by simp
      next
        case (CoreTm_LitArray elemTy tms0)
        from typing CoreTm_LitArray
        have tms_typed:
          "map (core_term_type env NotGhost) tms0 = map (core_term_type env NotGhost) tms0
           \<and> list_all (\<lambda>t. t \<noteq> None) (map (core_term_type env NotGhost) tms0)"
          by (auto simp: list_all_iff split: option.splits if_splits)
        have tms_eq: "interp_term_list fuel state (map (apply_subst_to_term subst) tms0)
                      = interp_term_list fuel state tms0"
          using IH_term_list[of tms0] tms_typed by blast
        show ?thesis using CoreTm_LitArray tms_eq by (simp split: sum.splits)
      next
        case (CoreTm_Var varName) then show ?thesis by simp
      next
        case (CoreTm_Cast targetTy sub)
        from typing CoreTm_Cast
        have sub_ty: "\<exists>subTy. core_term_type env NotGhost sub = Some subTy"
          by (auto split: option.splits if_splits)
        then obtain subTy where sub_ty_eq: "core_term_type env NotGhost sub = Some subTy" ..
        have sub_eq: "interp_term fuel state (apply_subst_to_term subst sub)
                      = interp_term fuel state sub"
          using IH_term[of sub] sub_ty_eq by blast
        \<comment> \<open>Well-typedness forces targetTy to be an integer type, which is
            invariant under substitution. \<close>
        from typing CoreTm_Cast have tgt_int: "is_integer_type targetTy"
          by (auto split: option.splits if_splits)
        have tgt_eq: "apply_subst subst targetTy = targetTy"
          using tgt_int is_integer_type_apply_subst by blast
        show ?thesis using CoreTm_Cast sub_eq tgt_eq by (simp split: sum.splits)
      next
        case (CoreTm_Unop op sub)
        from typing CoreTm_Unop obtain subTy where
          sub_ty: "core_term_type env NotGhost sub = Some subTy"
          by (auto split: option.splits)
        have sub_eq: "interp_term fuel state (apply_subst_to_term subst sub)
                      = interp_term fuel state sub"
          using IH_term[of sub] sub_ty by blast
        show ?thesis using CoreTm_Unop sub_eq by (simp split: sum.splits)
      next
        case (CoreTm_Binop op lhs rhs)
        from typing CoreTm_Binop obtain lTy rTy where
          l_ty: "core_term_type env NotGhost lhs = Some lTy" and
          r_ty: "core_term_type env NotGhost rhs = Some rTy"
          by (auto split: option.splits)
        have l_eq: "interp_term fuel state (apply_subst_to_term subst lhs)
                     = interp_term fuel state lhs"
          using IH_term[of lhs] l_ty by blast
        have r_eq: "interp_term fuel state (apply_subst_to_term subst rhs)
                     = interp_term fuel state rhs"
          using IH_term[of rhs] r_ty by blast
        show ?thesis using CoreTm_Binop l_eq r_eq by (simp split: sum.splits)
      next
        case (CoreTm_Let varName rhs body)
        \<comment> \<open>Let typechecks rhs in env and body in the extended env. We only use
            rhs's typing at the current IH call; for body we invoke IH on
            body with the extended env. \<close>
        from typing CoreTm_Let obtain rhsTy where
          rhs_ty: "core_term_type env NotGhost rhs = Some rhsTy" and
          body_ty: "core_term_type
              (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                     TE_GhostLocals := TE_GhostLocals env |-| {|varName|},
                     TE_ConstNames := finsert varName (TE_ConstNames env) \<rparr>)
              NotGhost body = Some ty"
          by (auto split: option.splits if_splits)
        have rhs_eq: "\<And>st :: 'w InterpState.
             interp_term fuel st (apply_subst_to_term subst rhs)
             = interp_term fuel st rhs"
          using IH_term[of rhs] rhs_ty by blast
        have body_eq: "\<And>st :: 'w InterpState.
             interp_term fuel st (apply_subst_to_term subst body)
             = interp_term fuel st body"
          using IH_term[of body] body_ty by blast
        show ?thesis
          using CoreTm_Let rhs_eq body_eq
          by (simp add: Let_def case_prod_beta split: sum.splits)
      next
        case (CoreTm_Quantifier q var qty body)
        \<comment> \<open>Quantifier is ghost-only; interpreter returns TypeError. \<close>
        then show ?thesis by simp
      next
        case (CoreTm_FunctionCall callName tyArgs argTms0)
        \<comment> \<open>Interpreter ignores tyArgs; the argTms list recurses into the call IH. \<close>
        from typing CoreTm_FunctionCall
        obtain fi where
          fi_lookup: "fmlookup (TE_Functions env) callName = Some fi" and
          argLen: "length argTms0 = length (FI_TmArgs fi)" and
          argTms_l2:
            "list_all2 (\<lambda>tm expectedTy.
                 (\<exists>y. core_term_type env NotGhost tm = Some y)
               \<and> (\<forall>t. core_term_type env NotGhost tm = Some t \<longrightarrow>
                       t = expectedTy))
               argTms0
               (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
                    (FI_TmArgs fi))"
          by (auto simp: Let_def split: option.splits if_splits)
        have argTms_typed:
          "list_all (\<lambda>tm. \<exists>t. core_term_type env NotGhost tm = Some t) argTms0"
          unfolding list_all_length
        proof (intro allI impI)
          fix i assume i_lt: "i < length argTms0"
          from argTms_l2 i_lt have pair_ok:
            "(\<exists>y. core_term_type env NotGhost (argTms0 ! i) = Some y)
             \<and> (\<forall>t. core_term_type env NotGhost (argTms0 ! i) = Some t \<longrightarrow>
                     t = (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tyArgs)) ty)
                                (FI_TmArgs fi)) ! i)"
            using argLen list_all2_nthD2 by fastforce
          from pair_ok show "\<exists>t. core_term_type env NotGhost (argTms0 ! i) = Some t" by blast
        qed
        have call_eq:
          "interp_function_call fuel state callName (map (apply_subst_to_term subst) argTms0)
           = interp_function_call fuel state callName argTms0"
          using IH_call argTms_typed by auto
        show ?thesis using CoreTm_FunctionCall call_eq
          by (simp split: sum.splits prod.splits)
      next
        case (CoreTm_VariantCtor ctorName tyArgs payload)
        from typing CoreTm_VariantCtor obtain pTy where
          p_ty: "core_term_type env NotGhost payload = Some pTy"
          by (auto split: option.splits if_splits)
        have p_eq: "interp_term fuel state (apply_subst_to_term subst payload)
                     = interp_term fuel state payload"
          using IH_term[of payload] p_ty by blast
        show ?thesis using CoreTm_VariantCtor p_eq by (simp split: sum.splits)
      next
        case (CoreTm_Record flds)
        \<comment> \<open>typechecker types the snd of each field. interpreter uses interp_term_list
            on (map snd flds). \<close>
        from typing CoreTm_Record obtain tys where
          those_eq: "those (map (\<lambda>(name, y). core_term_type env NotGhost y) flds) = Some tys"
          by (auto split: option.splits)
        have snd_typed:
          "list_all (\<lambda>t. t \<noteq> None) (map (core_term_type env NotGhost) (map snd flds))"
        proof -
          have eq_form: "map (\<lambda>(name, y). core_term_type env NotGhost y) flds
                         = map (core_term_type env NotGhost) (map snd flds)"
            by (induct flds) auto
          from those_all_some[OF those_eq] show ?thesis
            by (simp add: eq_form)
        qed
        have map_typed:
          "map (core_term_type env NotGhost) (map snd flds)
           = map (core_term_type env NotGhost) (map snd flds)
           \<and> list_all (\<lambda>t. t \<noteq> None) (map (core_term_type env NotGhost) (map snd flds))"
          using snd_typed by simp
        have tms_eq: "interp_term_list fuel state (map (apply_subst_to_term subst) (map snd flds))
                       = interp_term_list fuel state (map snd flds)"
          using IH_term_list[of "map snd flds"] map_typed by blast
        \<comment> \<open>Substitution commutes with snd on fields; names (fst) are preserved. \<close>
        have map_snd_subst:
          "map snd (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds)
           = map (apply_subst_to_term subst) (map snd flds)"
          by (induct flds) auto
        have names_eq:
          "map fst (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds)
           = map fst flds"
          by (induct flds) auto
        have tms_eq': "interp_term_list fuel state
                          (map snd (map (\<lambda>(name, tm). (name, apply_subst_to_term subst tm)) flds))
                        = interp_term_list fuel state (map snd flds)"
          using tms_eq by (metis map_snd_subst)
        have fst_map_eq:
          "map (fst \<circ> (\<lambda>(name, tm). (name, apply_subst_to_term subst tm))) flds = map fst flds"
          by (induct flds) auto
        show ?thesis using CoreTm_Record tms_eq' fst_map_eq
          by (simp add: comp_def case_prod_beta split: sum.splits)
      next
        case (CoreTm_RecordProj sub fldName)
        from typing CoreTm_RecordProj obtain subTy where
          sub_ty: "core_term_type env NotGhost sub = Some subTy"
          by (auto split: option.splits)
        have sub_eq: "interp_term fuel state (apply_subst_to_term subst sub)
                       = interp_term fuel state sub"
          using IH_term[of sub] sub_ty by blast
        show ?thesis using CoreTm_RecordProj sub_eq by (simp split: sum.splits)
      next
        case (CoreTm_VariantProj sub ctorName)
        from typing CoreTm_VariantProj obtain subTy where
          sub_ty: "core_term_type env NotGhost sub = Some subTy"
          by (auto split: option.splits)
        have sub_eq: "interp_term fuel state (apply_subst_to_term subst sub)
                       = interp_term fuel state sub"
          using IH_term[of sub] sub_ty by blast
        show ?thesis using CoreTm_VariantProj sub_eq by (simp split: sum.splits)
      next
        case (CoreTm_ArrayProj sub idxTms)
        from typing CoreTm_ArrayProj obtain subTy where
          sub_ty: "core_term_type env NotGhost sub = Some subTy"
          by (auto split: option.splits)
        have sub_eq: "interp_term fuel state (apply_subst_to_term subst sub)
                       = interp_term fuel state sub"
          using IH_term[of sub] sub_ty by blast
        from typing CoreTm_ArrayProj sub_ty
        have idx_typed:
          "list_all (\<lambda>t. t \<noteq> None) (map (core_term_type env NotGhost) idxTms)"
          by (auto simp: list_all_iff split: CoreType.splits if_splits)
        have idx_map_typed:
          "map (core_term_type env NotGhost) idxTms = map (core_term_type env NotGhost) idxTms
           \<and> list_all (\<lambda>t. t \<noteq> None) (map (core_term_type env NotGhost) idxTms)"
          using idx_typed by simp
        have idx_eq: "interp_term_list fuel state (map (apply_subst_to_term subst) idxTms)
                       = interp_term_list fuel state idxTms"
          using IH_term_list[of idxTms] idx_map_typed by blast
        show ?thesis using CoreTm_ArrayProj sub_eq idx_eq
          by (simp split: sum.splits CoreValue.splits)
      next
        case (CoreTm_Match scrut arms)
        from typing CoreTm_Match obtain sTy where
          s_ty: "core_term_type env NotGhost scrut = Some sTy"
          by (auto split: option.splits if_splits)
        have s_eq: "interp_term fuel state (apply_subst_to_term subst scrut)
                     = interp_term fuel state scrut"
          using IH_term[of scrut] s_ty by blast
        \<comment> \<open>Every arm body typechecks: hd via the match typing rule, rest via
            the list_all condition. \<close>
        from typing CoreTm_Match s_ty
        have arms_nonempty: "arms \<noteq> []"
          by (auto simp: Let_def split: option.splits if_splits)
        from typing CoreTm_Match s_ty arms_nonempty
        obtain firstBodyTy where
          first_ty: "core_term_type env NotGhost (snd (hd arms)) = Some firstBodyTy"
          and rest_all_ty:
          "list_all (\<lambda>body. core_term_type env NotGhost body = Some firstBodyTy)
                     (tl (map snd arms))"
          by (auto simp: Let_def split: option.splits if_splits)
        have arm_body_typed:
          "\<And>body. body \<in> snd ` set arms \<Longrightarrow>
             \<exists>t. core_term_type env NotGhost body = Some t"
        proof -
          fix body assume body_in: "body \<in> snd ` set arms"
          show "\<exists>t. core_term_type env NotGhost body = Some t"
          proof (cases "body = snd (hd arms)")
            case True with first_ty show ?thesis by blast
          next
            case False
            with body_in arms_nonempty have "body \<in> set (tl (map snd arms))"
              by (cases arms) auto
            with rest_all_ty show ?thesis
              by (auto simp: list_all_iff)
          qed
        qed
        \<comment> \<open>Pointwise equality of interp_term applied to each arm's body under
            substitution. \<close>
        have arm_interp_eq:
          "\<And>body. body \<in> snd ` set arms \<Longrightarrow>
             interp_term fuel state (apply_subst_to_term subst body)
             = interp_term fuel state body"
        proof -
          fix body assume body_in: "body \<in> snd ` set arms"
          from arm_body_typed[OF body_in] obtain t where
            body_ty: "core_term_type env NotGhost body = Some t" by blast
          show "interp_term fuel state (apply_subst_to_term subst body)
                 = interp_term fuel state body"
            using IH_term[of body] body_ty by blast
        qed
        \<comment> \<open>The arms-after-substitution have the same pattern-components, just
            substituted bodies. Hence find_matching_arm returns the substituted
            body corresponding to whichever original body it would have picked. \<close>
        have find_cong:
          "\<And>scrutVal.
             find_matching_arm scrutVal
                (map (\<lambda>(pat, armTm). (pat, apply_subst_to_term subst armTm)) arms)
             = map_sum id (apply_subst_to_term subst) (find_matching_arm scrutVal arms)"
        proof -
          fix scrutVal
          show "find_matching_arm scrutVal
                   (map (\<lambda>(pat, armTm). (pat, apply_subst_to_term subst armTm)) arms)
                 = map_sum id (apply_subst_to_term subst) (find_matching_arm scrutVal arms)"
            by (induct arms) auto
        qed
        show ?thesis
        proof (cases "interp_term fuel state scrut")
          case (Inl err)
          show ?thesis using CoreTm_Match s_eq Inl by simp
        next
          case (Inr scrutVal)
          show ?thesis
          proof (cases "find_matching_arm scrutVal arms")
            case (Inl err)
            from find_cong[of scrutVal] Inl
            have subst_err: "find_matching_arm scrutVal
                (map (\<lambda>(pat, armTm). (pat, apply_subst_to_term subst armTm)) arms)
                = Inl err" by simp
            show ?thesis
              using CoreTm_Match s_eq Inr Inl subst_err by simp
          next
            case (Inr armTm)
            \<comment> \<open>armTm is the snd of some element of arms. \<close>
            have arm_in_arms: "armTm \<in> snd ` set arms"
              using Inr by (induction arms) (auto split: if_splits)
            from find_cong[of scrutVal] Inr
            have subst_find: "find_matching_arm scrutVal
                (map (\<lambda>(pat, armTm'). (pat, apply_subst_to_term subst armTm')) arms)
                = Inr (apply_subst_to_term subst armTm)" by simp
            from arm_interp_eq[OF arm_in_arms]
            have arm_eq: "interp_term fuel state (apply_subst_to_term subst armTm)
                           = interp_term fuel state armTm" .
            show ?thesis
              using CoreTm_Match s_eq \<open>interp_term fuel state scrut = Inr scrutVal\<close>
                    Inr subst_find arm_eq by simp
          qed
        qed
      next
        case (CoreTm_Sizeof sub)
        from typing CoreTm_Sizeof obtain subTy where
          sub_ty: "core_term_type env NotGhost sub = Some subTy"
          by (auto split: option.splits if_splits)
        have sub_eq: "interp_term fuel state (apply_subst_to_term subst sub)
                       = interp_term fuel state sub"
          using IH_term[of sub] sub_ty by blast
        show ?thesis using CoreTm_Sizeof sub_eq by (simp split: sum.splits)
      next
        case (CoreTm_Allocated _) then show ?thesis by simp
      next
        case (CoreTm_Old _) then show ?thesis by simp
      qed
    qed
  next
    case (2 tms) show ?case
    proof (intro allI impI, elim conjE)
      fix state :: "'w InterpState" and env types subst
      assume types_eq: "map (core_term_type env NotGhost) tms = types"
         and all_some: "list_all (\<lambda>ty. ty \<noteq> None) types"
      show "interp_term_list (Suc fuel) state (map (apply_subst_to_term subst) tms)
            = interp_term_list (Suc fuel) state tms"
      proof (cases tms)
        case Nil
        then show ?thesis by simp
      next
        case (Cons tm1 rest)
        from types_eq Cons all_some obtain ty1 where
          tm1_ty: "core_term_type env NotGhost tm1 = Some ty1"
          by (cases "core_term_type env NotGhost tm1") auto
        have tm1_eq: "interp_term fuel state (apply_subst_to_term subst tm1)
                       = interp_term fuel state tm1"
          using IH_term[of tm1] tm1_ty by blast
        have rest_typed:
          "map (core_term_type env NotGhost) rest = map (core_term_type env NotGhost) rest
           \<and> list_all (\<lambda>ty. ty \<noteq> None) (map (core_term_type env NotGhost) rest)"
          using types_eq Cons all_some by auto
        have rest_eq: "interp_term_list fuel state (map (apply_subst_to_term subst) rest)
                        = interp_term_list fuel state rest"
          using IH_term_list[of rest] rest_typed by blast
        show ?thesis using Cons tm1_eq rest_eq
          by (simp split: sum.splits)
      qed
    qed
  next
    case (3 lvTm) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and env ty subst
      assume typing: "core_term_type env NotGhost lvTm = Some ty"
      show "interp_writable_lvalue (Suc fuel) state (apply_subst_to_term subst lvTm)
            = interp_writable_lvalue (Suc fuel) state lvTm"
      proof (cases lvTm)
        case (CoreTm_Var varName)
        then show ?thesis by simp
      next
        case (CoreTm_RecordProj sub fldName)
        from typing CoreTm_RecordProj obtain subTy where
          sub_ty: "core_term_type env NotGhost sub = Some subTy"
          by (auto split: option.splits)
        have sub_eq: "interp_writable_lvalue fuel state (apply_subst_to_term subst sub)
                      = interp_writable_lvalue fuel state sub"
          using IH_lvalue[of sub] sub_ty by blast
        show ?thesis using CoreTm_RecordProj sub_eq
          by (simp split: sum.splits)
      next
        case (CoreTm_VariantProj sub ctorName)
        from typing CoreTm_VariantProj obtain subTy where
          sub_ty: "core_term_type env NotGhost sub = Some subTy"
          by (auto split: option.splits)
        have sub_eq: "interp_writable_lvalue fuel state (apply_subst_to_term subst sub)
                      = interp_writable_lvalue fuel state sub"
          using IH_lvalue[of sub] sub_ty by blast
        show ?thesis using CoreTm_VariantProj sub_eq
          by (simp split: sum.splits)
      next
        case (CoreTm_ArrayProj sub idxTms)
        from typing CoreTm_ArrayProj obtain subTy where
          sub_ty: "core_term_type env NotGhost sub = Some subTy"
          by (auto split: option.splits)
        have sub_eq: "interp_writable_lvalue fuel state (apply_subst_to_term subst sub)
                      = interp_writable_lvalue fuel state sub"
          using IH_lvalue[of sub] sub_ty by blast
        \<comment> \<open>Also need that interp_term_list on the substituted idxTms equals the
            original. Well-typedness of the ArrayProj ensures each idx term
            typechecks (with some integer type). \<close>
        from typing CoreTm_ArrayProj sub_ty
        have idx_typed: "list_all (\<lambda>tm. \<exists>t. core_term_type env NotGhost tm = Some t) idxTms"
          by (auto simp: list_all_iff split: CoreType.splits if_splits)
        have map_typed:
          "map (core_term_type env NotGhost) idxTms = map (core_term_type env NotGhost) idxTms
           \<and> list_all (\<lambda>t. t \<noteq> None) (map (core_term_type env NotGhost) idxTms)"
          using idx_typed by (auto simp: list_all_iff)
        have idx_eq: "interp_term_list fuel state (map (apply_subst_to_term subst) idxTms)
                       = interp_term_list fuel state idxTms"
          using IH_term_list[of idxTms] map_typed by blast
        show ?thesis using CoreTm_ArrayProj sub_eq idx_eq
          by (simp split: sum.splits)
      qed (use typing in \<open>simp_all\<close>)
    qed
  next
    case (4 stmt) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and env env' subst
      assume typing: "core_statement_type env NotGhost stmt = Some env'"
      show "interp_statement (Suc fuel) state (apply_subst_to_stmt subst stmt)
            = interp_statement (Suc fuel) state stmt"
      proof (cases stmt)
        case (CoreStmt_VarDecl g varName vr ty initTm)
        show ?thesis
        proof (cases vr)
          case Var
          show ?thesis
          proof (cases g)
            case Ghost
            then show ?thesis using CoreStmt_VarDecl Var by simp
          next
            case NotGhost
            from typing CoreStmt_VarDecl Var NotGhost
            have init_ty: "core_impure_call_type env NotGhost initTm = Some ty
                           \<or> core_term_type env NotGhost initTm = Some ty"
              by (auto split: if_splits)
            \<comment> \<open>Plain-term branch: erasure follows directly from IH_term. \<close>
            have init_eq: "core_term_type env NotGhost initTm = Some ty \<Longrightarrow>
                            interp_term fuel state (apply_subst_to_term subst initTm)
                             = interp_term fuel state initTm"
              using IH_term[of initTm] by blast
            \<comment> \<open>Impure-call branch: the rhs is a CoreTm_FunctionCall, its arguments
                all typecheck (so their erasure is via IH_term_list / IH_call). \<close>
            have init_call_eq:
              "\<And>fn tys args. initTm = CoreTm_FunctionCall fn tys args \<Longrightarrow>
                 core_impure_call_type env NotGhost initTm = Some ty \<Longrightarrow>
                 interp_function_call fuel state fn (map (apply_subst_to_term subst) args)
                 = interp_function_call fuel state fn args"
            proof -
              fix fn tys args
              assume tm_eq: "initTm = CoreTm_FunctionCall fn tys args"
                and impure_ty: "core_impure_call_type env NotGhost initTm = Some ty"
              from core_impure_call_type_args_typed[OF impure_ty tm_eq]
              have args_typed:
                "list_all (\<lambda>tm. \<exists>t. core_term_type env NotGhost tm = Some t) args"
                by blast
              show "interp_function_call fuel state fn (map (apply_subst_to_term subst) args)
                    = interp_function_call fuel state fn args"
                using IH_call args_typed by auto
            qed

            from init_ty show ?thesis
            proof
              assume impure: "core_impure_call_type env NotGhost initTm = Some ty"
              show ?thesis
              proof (cases initTm)
                case (CoreTm_FunctionCall fn tys args)
                from init_call_eq[OF CoreTm_FunctionCall impure]
                have call_eq: "interp_function_call fuel state fn
                                  (map (apply_subst_to_term subst) args)
                               = interp_function_call fuel state fn args" .
                show ?thesis
                  using CoreStmt_VarDecl Var NotGhost CoreTm_FunctionCall call_eq
                  by (simp split: sum.splits prod.splits add: case_prod_beta Let_def)
              qed (use impure in \<open>simp_all add: core_impure_call_type_def\<close>)
            next
              assume pure: "core_term_type env NotGhost initTm = Some ty"
              from init_eq[OF pure] have eq_fact:
                "interp_term fuel state (apply_subst_to_term subst initTm)
                   = interp_term fuel state initTm" .
              \<comment> \<open>If initTm is a plain term (non-call), the interpreter falls through
                  to interp_term in both the original and substituted statement. If
                  it is a pure function call, the interpreter still dispatches to
                  interp_function_call (since the new impure path checks syntactic
                  shape, not purity), so we need IH_call there too. \<close>
              show ?thesis
              proof (cases initTm)
                case (CoreTm_FunctionCall fn tys args)
                from pure CoreTm_FunctionCall obtain fi where
                  fi_lookup: "fmlookup (TE_Functions env) fn = Some fi" and
                  argTms_l2:
                    "list_all2 (\<lambda>tm expectedTy.
                        (\<exists>y. core_term_type env NotGhost tm = Some y)
                        \<and> (\<forall>t. core_term_type env NotGhost tm = Some t \<longrightarrow>
                                t = expectedTy))
                      args
                      (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tys)) ty)
                           (FI_TmArgs fi))"
                  by (auto simp: Let_def split: option.splits if_splits)
                have args_typed:
                  "list_all (\<lambda>tm. \<exists>t. core_term_type env NotGhost tm = Some t) args"
                  unfolding list_all_length
                proof (intro allI impI)
                  fix i assume i_lt: "i < length args"
                  from argTms_l2 i_lt show "\<exists>t. core_term_type env NotGhost (args ! i) = Some t"
                    by (auto simp: list_all2_conv_all_nth)
                qed
                have call_eq: "interp_function_call fuel state fn
                                 (map (apply_subst_to_term subst) args)
                               = interp_function_call fuel state fn args"
                  using IH_call args_typed by auto
                show ?thesis
                  using CoreStmt_VarDecl Var NotGhost CoreTm_FunctionCall call_eq
                  by (simp split: sum.splits prod.splits add: case_prod_beta Let_def)
              qed (use CoreStmt_VarDecl Var NotGhost eq_fact in
                   \<open>simp_all split: sum.splits prod.splits add: case_prod_beta Let_def\<close>)
            qed
          qed
        next
          case Ref
          show ?thesis
          proof (cases g)
            case Ghost
            then show ?thesis using CoreStmt_VarDecl Ref by simp
          next
            case NotGhost
            from typing CoreStmt_VarDecl Ref NotGhost
            have init_lvalue: "is_lvalue initTm"
              and init_ty: "core_term_type env NotGhost initTm = Some ty"
              by (auto split: if_splits)
            \<comment> \<open>The interpreter dispatches on lvalue_base_name (invariant under
                substitution), then either interp_term (copy path) or
                interp_writable_lvalue (alias path). Both erase via the IHs. \<close>
            have base_eq: "lvalue_base_name (apply_subst_to_term subst initTm)
                            = lvalue_base_name initTm"
              by (rule lvalue_base_name_apply_subst_to_term)
            have term_eq: "interp_term fuel state (apply_subst_to_term subst initTm)
                            = interp_term fuel state initTm"
              using IH_term[of initTm] init_ty by blast
            have lv_eq: "interp_writable_lvalue fuel state (apply_subst_to_term subst initTm)
                          = interp_writable_lvalue fuel state initTm"
              using IH_lvalue[of initTm] init_ty by blast
            show ?thesis
              using CoreStmt_VarDecl Ref NotGhost base_eq term_eq lv_eq
              by (simp split: option.splits sum.splits add: case_prod_beta)
          qed
        qed
      next
        case (CoreStmt_Assign g lhs rhs)
        show ?thesis
        proof (cases g)
          case Ghost
          then show ?thesis using CoreStmt_Assign by simp
        next
          case NotGhost
          from typing CoreStmt_Assign NotGhost
          have lhs_wl: "is_writable_lvalue env lhs"
            by (auto split: if_splits option.splits)
          from typing CoreStmt_Assign NotGhost obtain lhsTy where
            lhs_ty: "core_term_type env NotGhost lhs = Some lhsTy" and
            rhs_ty: "core_impure_call_type env NotGhost rhs = Some lhsTy
                     \<or> core_term_type env NotGhost rhs = Some lhsTy"
            by (auto split: if_splits option.splits)
          have lhs_eq: "interp_writable_lvalue fuel state (apply_subst_to_term subst lhs)
                         = interp_writable_lvalue fuel state lhs"
            using IH_lvalue[of lhs] lhs_ty by blast
          \<comment> \<open>If rhs is not a function call, core_impure_call_type returns None, so
              the pure branch of rhs_ty holds and IH_term gives the erasure. \<close>
          have rhs_non_call_eq:
            "(\<nexists>fn tys args. rhs = CoreTm_FunctionCall fn tys args) \<Longrightarrow>
             interp_term fuel state (apply_subst_to_term subst rhs)
                = interp_term fuel state rhs"
          proof -
            assume no_call: "\<nexists>fn tys args. rhs = CoreTm_FunctionCall fn tys args"
            hence impure_none: "core_impure_call_type env NotGhost rhs = None"
              unfolding core_impure_call_type_def by (cases rhs) auto
            with rhs_ty have pure: "core_term_type env NotGhost rhs = Some lhsTy" by auto
            show "interp_term fuel state (apply_subst_to_term subst rhs)
                    = interp_term fuel state rhs"
              using IH_term[of rhs] pure by blast
          qed

          \<comment> \<open>When rhs is a function call, args all typecheck (via core_term_type),
              whether the disjunction gave us core_impure_call_type or core_term_type. \<close>
          have rhs_call_eq:
            "\<And>fn tys args. rhs = CoreTm_FunctionCall fn tys args \<Longrightarrow>
               interp_function_call fuel state fn (map (apply_subst_to_term subst) args)
               = interp_function_call fuel state fn args"
          proof -
            fix fn tys args assume rhs_eq_fc: "rhs = CoreTm_FunctionCall fn tys args"
            have args_typed: "list_all (\<lambda>tm. \<exists>t. core_term_type env NotGhost tm = Some t) args"
              using rhs_ty
            proof
              assume impure: "core_impure_call_type env NotGhost rhs = Some lhsTy"
              from core_impure_call_type_args_typed[OF impure rhs_eq_fc] show ?thesis by blast
            next
              assume pure: "core_term_type env NotGhost rhs = Some lhsTy"
              from pure rhs_eq_fc
              obtain fi where
                fi_lookup: "fmlookup (TE_Functions env) fn = Some fi" and
                argTms_l2:
                  "list_all2 (\<lambda>tm expectedTy.
                       (\<exists>y. core_term_type env NotGhost tm = Some y)
                     \<and> (\<forall>t. core_term_type env NotGhost tm = Some t \<longrightarrow>
                             t = expectedTy))
                     args
                     (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs fi) tys)) ty)
                          (FI_TmArgs fi))"
                by (auto simp: Let_def split: option.splits if_splits)
              show "list_all (\<lambda>tm. \<exists>t. core_term_type env NotGhost tm = Some t) args"
                unfolding list_all_length
              proof (intro allI impI)
                fix i assume i_lt: "i < length args"
                from argTms_l2 i_lt show "\<exists>t. core_term_type env NotGhost (args ! i) = Some t"
                  by (auto simp: list_all2_conv_all_nth)
              qed
            qed
            show "interp_function_call fuel state fn (map (apply_subst_to_term subst) args)
                  = interp_function_call fuel state fn args"
              using IH_call args_typed by auto
          qed
          show ?thesis
          proof (cases rhs)
            case (CoreTm_FunctionCall fn tys args)
            from rhs_call_eq[OF CoreTm_FunctionCall]
            have call_eq: "interp_function_call fuel state fn
                              (map (apply_subst_to_term subst) args)
                           = interp_function_call fuel state fn args" .
            show ?thesis
              using CoreStmt_Assign NotGhost lhs_eq call_eq CoreTm_FunctionCall
              by (simp split: sum.splits prod.splits add: Let_def)
          qed (use CoreStmt_Assign NotGhost lhs_eq rhs_non_call_eq in
               \<open>simp_all split: sum.splits prod.splits add: Let_def\<close>)
        qed
      next
        case (CoreStmt_Swap g lhs rhs)
        show ?thesis
        proof (cases g)
          case Ghost
          then show ?thesis using CoreStmt_Swap by simp
        next
          case NotGhost
          from typing CoreStmt_Swap NotGhost
          obtain lhsTy where
            lhs_ty: "core_term_type env NotGhost lhs = Some lhsTy" and
            rhs_ty: "core_term_type env NotGhost rhs = Some lhsTy"
            by (auto split: if_splits option.splits)
          have lhs_eq: "interp_writable_lvalue fuel state (apply_subst_to_term subst lhs)
                         = interp_writable_lvalue fuel state lhs"
            using IH_lvalue[of lhs] lhs_ty by blast
          have rhs_eq: "interp_writable_lvalue fuel state (apply_subst_to_term subst rhs)
                         = interp_writable_lvalue fuel state rhs"
            using IH_lvalue[of rhs] rhs_ty by blast
          show ?thesis using CoreStmt_Swap NotGhost lhs_eq rhs_eq
            by (simp split: sum.splits prod.splits add: Let_def)
        qed
      next
        case (CoreStmt_Return tm)
        from typing CoreStmt_Return
        have tm_ty: "core_term_type env NotGhost tm = Some (TE_ReturnType env)"
          by (auto split: if_splits)
        have tm_eq: "interp_term fuel state (apply_subst_to_term subst tm)
                      = interp_term fuel state tm"
          using IH_term[of tm] tm_ty by blast
        show ?thesis using CoreStmt_Return tm_eq by (simp split: sum.splits)
      next
        case (CoreStmt_Assert condTm proofBody)
        \<comment> \<open>Assert is a runtime no-op. \<close>
        then show ?thesis by simp
      next
        case (CoreStmt_Assume condTm)
        then show ?thesis by simp
      next
        case (CoreStmt_ShowHide sh name)
        then show ?thesis by simp
      next
        case (CoreStmt_Fix _ _)
        \<comment> \<open>Typechecker is undefined for Fix — deferred. \<close>
        show ?thesis sorry
      next
        case (CoreStmt_Obtain _ _ _)
        \<comment> \<open>Typechecker is undefined for Obtain — deferred. \<close>
        show ?thesis sorry
      next
        case (CoreStmt_Use _)
        \<comment> \<open>Typechecker is undefined for Use — deferred. \<close>
        show ?thesis sorry
      next
        case (CoreStmt_While _ _ _ _ _)
        \<comment> \<open>Typechecker is undefined for While — deferred. \<close>
        show ?thesis sorry
      next
        case (CoreStmt_Match _ _ _)
        \<comment> \<open>Typechecker is undefined for Match statement — deferred. \<close>
        show ?thesis sorry
      qed
    qed
  next
    case (5 stmts) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and env env' subst
      assume typing: "core_statement_list_type env NotGhost stmts = Some env'"
      show "interp_statement_list (Suc fuel) state (apply_subst_to_stmt_list subst stmts)
            = interp_statement_list (Suc fuel) state stmts"
      proof (cases stmts)
        case Nil
        then show ?thesis by simp
      next
        case (Cons stmt1 rest)
        from typing Cons obtain envMid where
          stmt1_ty: "core_statement_type env NotGhost stmt1 = Some envMid" and
          rest_ty: "core_statement_list_type envMid NotGhost rest = Some env'"
          by (auto split: option.splits)
        have stmt1_eq: "\<And>st :: 'w InterpState.
                interp_statement fuel st (apply_subst_to_stmt subst stmt1)
                = interp_statement fuel st stmt1"
          using IH_stmt[of stmt1] stmt1_ty by blast
        have rest_eq: "\<And>st :: 'w InterpState.
                interp_statement_list fuel st (apply_subst_to_stmt_list subst rest)
                = interp_statement_list fuel st rest"
          using IH_stmt_list[of rest] rest_ty by blast
        show ?thesis using Cons stmt1_eq rest_eq
          by (simp split: sum.splits ExecResult.splits)
      qed
    qed
  next
    case (6 fnName argTms) show ?case
    proof (intro allI impI)
      fix state :: "'w InterpState" and env subst
      assume all_typed: "list_all (\<lambda>tm. \<exists>ty. core_term_type env NotGhost tm = Some ty) argTms"
      \<comment> \<open>The interpreter computes refResults and valResults by mapping over
          argTms, then folds process_one_arg. apply_subst_to_term on each argTm
          preserves each of these results individually (via IH_term and
          IH_lvalue). Since the interpreter's behaviour is determined entirely
          by those lists, the results match. \<close>
      have pointwise_ref:
        "\<And>tm0. tm0 \<in> set argTms \<Longrightarrow>
           interp_writable_lvalue fuel state (apply_subst_to_term subst tm0)
           = interp_writable_lvalue fuel state tm0"
      proof -
        fix tm0 assume tm0_in: "tm0 \<in> set argTms"
        from all_typed tm0_in obtain ty0 where
          tm0_ty: "core_term_type env NotGhost tm0 = Some ty0"
          by (auto simp: list_all_iff)
        show "interp_writable_lvalue fuel state (apply_subst_to_term subst tm0)
              = interp_writable_lvalue fuel state tm0"
          using IH_lvalue[of tm0] tm0_ty by blast
      qed
      have pointwise_val:
        "\<And>tm0. tm0 \<in> set argTms \<Longrightarrow>
           interp_term fuel state (apply_subst_to_term subst tm0)
           = interp_term fuel state tm0"
      proof -
        fix tm0 assume tm0_in: "tm0 \<in> set argTms"
        from all_typed tm0_in obtain ty0 where
          tm0_ty: "core_term_type env NotGhost tm0 = Some ty0"
          by (auto simp: list_all_iff)
        show "interp_term fuel state (apply_subst_to_term subst tm0)
              = interp_term fuel state tm0"
          using IH_term[of tm0] tm0_ty by blast
      qed
      have ref_eq: "map (interp_writable_lvalue fuel state) (map (apply_subst_to_term subst) argTms)
                    = map (interp_writable_lvalue fuel state) argTms"
        using pointwise_ref by (induction argTms) auto
      have val_eq: "map (interp_term fuel state) (map (apply_subst_to_term subst) argTms)
                    = map (interp_term fuel state) argTms"
        using pointwise_val by (induction argTms) auto
      show "interp_function_call (Suc fuel) state fnName (map (apply_subst_to_term subst) argTms)
            = interp_function_call (Suc fuel) state fnName argTms"
        by (simp only: interp_function_call.simps ref_eq val_eq length_map)
    qed
  }
qed

end

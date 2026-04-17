theory ElabTermCorrectHelpers
  imports ElabTerm ElabTypeCorrect "../core/CoreTypecheck" Unify3
begin

(* Extend a type environment with a half-open range of fresh rigid type variables.
   When not in ghost context, these are also added to TE_RuntimeTypeVars, since they
   will only ever be instantiated with runtime types. In ghost context we only add
   them to TE_TypeVars, leaving their runtime status unconstrained. *)
definition extend_env_with_tyvars :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> CoreTyEnv" where
  "extend_env_with_tyvars env ghost lo hi =
     env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list [lo..<hi],
           TE_RuntimeTypeVars := (if ghost = NotGhost
                                   then TE_RuntimeTypeVars env |\<union>| fset_of_list [lo..<hi]
                                   else TE_RuntimeTypeVars env) \<rparr>"

(* Identity: when the interval is empty, the env is unchanged. *)
lemma extend_env_with_tyvars_empty [simp]:
  assumes "lo \<ge> hi"
  shows "extend_env_with_tyvars env ghost lo hi = env"
  using assms unfolding extend_env_with_tyvars_def by simp

(* Splitting a contiguous interval of fresh type variables. *)
lemma fset_of_list_upt_split:
  assumes "lo \<le> mid" and "mid \<le> hi"
  shows "fset_of_list [lo..<mid] |\<union>| fset_of_list [mid..<hi] = fset_of_list [lo..<hi]"
proof -
  have "[lo..<hi] = [lo..<mid] @ [mid..<hi]"
    using assms
    using le_Suc_ex upt_add_eq_append by blast
  thus ?thesis by simp
qed

(* Helper: extend_env_with_tyvars with a wider interval can be viewed as extending
   the narrower version further. Used to lift well-kindedness / runtime facts. *)
lemma extend_env_with_tyvars_widen_eq:
  assumes "lo' \<le> lo" and "hi \<le> hi'"
  shows "\<exists>extraTV extraRT. extend_env_with_tyvars env ghost lo' hi' =
           (extend_env_with_tyvars env ghost lo hi)
             \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraTV,
               TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraRT \<rparr>"
proof -
  let ?diff = "fset_of_list [lo'..<hi'] |-| fset_of_list [lo..<hi]"
  have contained: "fset_of_list [lo..<hi] |\<subseteq>| fset_of_list [lo'..<hi']"
    using assms by (auto simp: fset_of_list_elem)
  have union_eq: "fset_of_list [lo..<hi] |\<union>| ?diff = fset_of_list [lo'..<hi']"
    using contained by auto
  show ?thesis
  proof (cases "ghost = NotGhost")
    case True
    have "extend_env_with_tyvars env ghost lo' hi' =
            (extend_env_with_tyvars env ghost lo hi)
              \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?diff,
                TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?diff \<rparr>"
      unfolding extend_env_with_tyvars_def using True union_eq by (simp add: funion_assoc)
    thus ?thesis by blast
  next
    case False
    have "extend_env_with_tyvars env ghost lo' hi' =
            (extend_env_with_tyvars env ghost lo hi)
              \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| ?diff,
                TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| {||} \<rparr>"
      unfolding extend_env_with_tyvars_def using False union_eq by (simp add: funion_assoc)
    thus ?thesis by blast
  qed
qed

(* is_well_kinded is preserved when widening the type-variable interval *)
lemma is_well_kinded_extend_env_with_tyvars_mono:
  assumes "is_well_kinded (extend_env_with_tyvars env ghost lo hi) ty"
    and "lo' \<le> lo" and "hi \<le> hi'"
  shows "is_well_kinded (extend_env_with_tyvars env ghost lo' hi') ty"
proof -
  obtain extraTV extraRT where env_eq:
    "extend_env_with_tyvars env ghost lo' hi' =
       (extend_env_with_tyvars env ghost lo hi)
         \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraTV,
           TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraRT \<rparr>"
    using extend_env_with_tyvars_widen_eq[OF assms(2,3)] by blast
  show ?thesis
    using assms(1) is_well_kinded_extend_tyvars by (simp add: env_eq)
qed

(* is_runtime_type is preserved when widening the type-variable interval *)
lemma is_runtime_type_extend_env_with_tyvars_mono:
  assumes "is_runtime_type (extend_env_with_tyvars env ghost lo hi) ty"
    and "lo' \<le> lo" and "hi \<le> hi'"
  shows "is_runtime_type (extend_env_with_tyvars env ghost lo' hi') ty"
proof -
  obtain extraTV extraRT where env_eq:
    "extend_env_with_tyvars env ghost lo' hi' =
       (extend_env_with_tyvars env ghost lo hi)
         \<lparr> TE_TypeVars := TE_TypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraTV,
           TE_RuntimeTypeVars := TE_RuntimeTypeVars (extend_env_with_tyvars env ghost lo hi) |\<union>| extraRT \<rparr>"
    using extend_env_with_tyvars_widen_eq[OF assms(2,3)] by blast
  show ?thesis
    using assms(1) is_runtime_type_extend_runtime_tyvars by (simp add: env_eq)
qed

(* Weakening: extending the interval further preserves core_term_type.
   Both endpoints may move outward (lo' \<le> lo, hi' \<ge> hi). *)
lemma core_term_type_extend_env_with_tyvars_mono:
  assumes "core_term_type (extend_env_with_tyvars env ghost lo hi) ghost tm = Some ty"
    and "lo' \<le> lo" and "hi \<le> hi'"
  shows "core_term_type (extend_env_with_tyvars env ghost lo' hi') ghost tm = Some ty"
proof -
  let ?env_src = "extend_env_with_tyvars env ghost lo hi"
  let ?env_tgt = "extend_env_with_tyvars env ghost lo' hi'"
  let ?diff = "fset_of_list [lo'..<hi'] |-| fset_of_list [lo..<hi]"
  \<comment> \<open>[lo..<hi] is contained in [lo'..<hi'] when endpoints move outward\<close>
  have contained: "fset_of_list [lo..<hi] |\<subseteq>| fset_of_list [lo'..<hi']"
    using assms(2,3) by (auto simp: fset_of_list_elem)
  \<comment> \<open>Union of a subset with the difference is the whole\<close>
  have union_eq: "fset_of_list [lo..<hi] |\<union>| ?diff = fset_of_list [lo'..<hi']"
    using contained by auto
  \<comment> \<open>Target env = source env with extra type vars added\<close>
  have env_eq: "?env_tgt = ?env_src \<lparr> TE_TypeVars := TE_TypeVars ?env_src |\<union>| ?diff,
                                      TE_RuntimeTypeVars := TE_RuntimeTypeVars ?env_src |\<union>|
                                                            (if ghost = NotGhost then ?diff else {||}) \<rparr>"
    unfolding extend_env_with_tyvars_def
    using union_eq by (cases "ghost = NotGhost") (auto simp: funion_assoc)
  show ?thesis
    using assms(1) core_term_type_irrelevant_tyvar
    by (simp add: env_eq)
qed

(* Well-formedness is preserved under extend_env_with_tyvars. *)
lemma tyenv_well_formed_extend_env_with_tyvars:
  assumes "tyenv_well_formed env"
  shows "tyenv_well_formed (extend_env_with_tyvars env ghost lo hi)"
proof (cases "ghost = NotGhost")
  case True
  thus ?thesis
    using assms tyenv_well_formed_extend_tyvars[where extraTV="fset_of_list [lo..<hi]"
                                                    and extraRT="fset_of_list [lo..<hi]"]
    unfolding extend_env_with_tyvars_def by simp
next
  case False
  \<comment> \<open>Extending only TE_TypeVars is a special case: use extraRT = fempty\<close>
  have "tyenv_well_formed (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list [lo..<hi],
                                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| {||} \<rparr>)"
    using assms tyenv_well_formed_extend_tyvars[where extraTV="fset_of_list [lo..<hi]"
                                                    and extraRT="{||}"] by blast
  thus ?thesis using False unfolding extend_env_with_tyvars_def by simp
qed

(* Monotonicity of next_mv: elab_term / elab_term_list only advance the counter. *)
lemma elab_term_next_mv_monotone:
  "elab_term env elabEnv ghost tm next_mv = Inr (tm', ty', next_mv') \<Longrightarrow> next_mv \<le> next_mv'"
and elab_term_list_next_mv_monotone:
  "elab_term_list env elabEnv ghost tms next_mv = Inr (tms', tys', next_mv') \<Longrightarrow> next_mv \<le> next_mv'"
proof (induction env elabEnv ghost tm next_mv and env elabEnv ghost tms next_mv
       arbitrary: tm' ty' next_mv' and tms' tys' next_mv'
       rule: elab_term_elab_term_list.induct)
  case (1 env elabEnv ghost loc lit next_mv)
  \<comment> \<open>Literal: Bool/Int leave next_mv unchanged; Array allocates one meta and threads
       through elab_term_list; String is undefined (TODO)\<close>
  show ?case
  proof (cases lit)
    case (BabLit_Bool b)
    with "1.prems" show ?thesis by auto
  next
    case (BabLit_Int i)
    with "1.prems" show ?thesis by (auto split: option.splits)
  next
    case (BabLit_String s)
    with "1.prems" show ?thesis by (auto simp: Let_def split: if_splits)
  next
    case (BabLit_Array tms)
    from "1.prems" BabLit_Array have
      len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))"
      by (auto split: if_splits)
    from "1.prems" BabLit_Array len_ok obtain elabTms actualTys next_mv1 where
      elab_list: "elab_term_list env elabEnv ghost tms (next_mv + 1)
                  = Inr (elabTms, actualTys, next_mv1)"
      by (auto simp: Let_def split: sum.splits)
    have mono: "next_mv + 1 \<le> next_mv1"
      using "1.IH"[OF BabLit_Array _ refl elab_list] len_ok by simp
    from "1.prems" BabLit_Array len_ok elab_list have next_mv_eq: "next_mv' = next_mv1"
      by (auto simp: Let_def unify_and_coerce_def split: sum.splits prod.splits)
    from mono next_mv_eq show ?thesis by simp
  qed
next
  case (2 env elabEnv ghost loc name tyArgs next_mv)
  \<comment> \<open>BabTm_Name: variable path has next_mv unchanged; constructor path uses resolve_type_args\<close>
  from "2.prems" show ?case
    by (auto simp: resolve_type_args_def Let_def
             split: option.splits if_splits sum.splits prod.splits)
next
  case (3 env elabEnv ghost loc targetTy operand next_mv)
  from "3.prems" show ?case
    by (auto simp: Let_def split: sum.splits if_splits option.splits dest!: "3.IH")
next
  case (4 env elabEnv ghost loc condTm thenTm elseTm next_mv)
  \<comment> \<open>BabTm_If: threads through cond, then, else\<close>
  from "4.prems" obtain newCond condTy next_mv1 where
    elab_cond: "elab_term env elabEnv ghost condTm next_mv = Inr (newCond, condTy, next_mv1)"
    by (auto split: sum.splits)
  from "4.prems" elab_cond obtain newThen thenTy next_mv2 where
    elab_then: "elab_term env elabEnv ghost thenTm next_mv1 = Inr (newThen, thenTy, next_mv2)"
    by (auto split: sum.splits)
  from "4.prems" elab_cond elab_then obtain newElse elseTy next_mv3 where
    elab_else: "elab_term env elabEnv ghost elseTm next_mv2 = Inr (newElse, elseTy, next_mv3)"
    by (auto split: sum.splits)
  have m1: "next_mv \<le> next_mv1"
    using "4.IH"(1) elab_cond by simp
  have m2: "next_mv1 \<le> next_mv2"
    using "4.IH"(2) elab_cond elab_then by simp
  have m3: "next_mv2 \<le> next_mv3"
    using "4.IH"(3) elab_cond elab_then elab_else by simp
  from "4.prems" elab_cond elab_then elab_else have "next_mv' = next_mv3"
    by (auto simp: Let_def split: option.splits if_splits)
  with m1 m2 m3 show ?case by simp
next
  case (5 env elabEnv ghost loc op operand next_mv)
  \<comment> \<open>BabTm_Unop: forwards operand's next_mv\<close>
  from "5.prems" show ?case
    by (auto simp: Let_def split: sum.splits option.splits BabUnop.splits if_splits dest!: "5.IH")
next
  case (6 env elabEnv ghost loc lhs operands next_mv)
  \<comment> \<open>BabTm_Binop: threads through lhs, rhs list\<close>
  from "6.prems" obtain newLhs lhsTy next_mv1 where
    elab_lhs: "elab_term env elabEnv ghost lhs next_mv = Inr (newLhs, lhsTy, next_mv1)"
    by (auto split: sum.splits)
  from "6.prems" elab_lhs obtain rhsTms rhsTys next_mv2 where
    elab_rhs: "elab_term_list env elabEnv ghost (map snd operands) next_mv1 = Inr (rhsTms, rhsTys, next_mv2)"
    by (auto split: sum.splits)
  have m1: "next_mv \<le> next_mv1"
    using "6.IH"(1) elab_lhs by simp
  have m2: "next_mv1 \<le> next_mv2"
    using "6.IH"(2) elab_lhs elab_rhs by simp
  from "6.prems" elab_lhs elab_rhs have "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)
  with m1 m2 show ?case by simp
next
  case (7 env elabEnv ghost loc varName rhs body next_mv)
  \<comment> \<open>BabTm_Let: threads through rhs and body\<close>
  from "7.prems" obtain rhsTm rhsTy next_mv1 where
    elab_rhs: "elab_term env elabEnv ghost rhs next_mv = Inr (rhsTm, rhsTy, next_mv1)"
    by (auto split: sum.splits)
  from "7.prems" elab_rhs have rhs_resolved:
    "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)"
    by (auto split: if_splits)
  let ?env_body = "env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                          TE_GhostLocals := (if ghost = Ghost then finsert varName (TE_GhostLocals env)
                                               else fminus (TE_GhostLocals env) {|varName|}),
                          TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>"
  from "7.prems" elab_rhs rhs_resolved obtain bodyTm bodyTy next_mv2 where
    elab_body: "elab_term ?env_body elabEnv ghost body next_mv1 = Inr (bodyTm, bodyTy, next_mv2)"
    by (auto simp: Let_def split: sum.splits)
  have m1: "next_mv \<le> next_mv1"
    using "7.IH"(1) elab_rhs by simp
  have m2: "next_mv1 \<le> next_mv2"
    using "7.IH"(2) elab_rhs rhs_resolved elab_body by (simp add: Let_def)
  from "7.prems" elab_rhs rhs_resolved elab_body have "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)
  with m1 m2 show ?case by simp
next
  case (8 env elabEnv ghost loc quant name varTy tm next_mv)
  \<comment> \<open>BabTm_Quantifier: forwards body's next_mv\<close>
  from "8.prems" show ?case
    using "8.IH" by (auto simp: Let_def split: sum.splits if_splits option.splits)
next
  case (9 env elabEnv ghost loc callee args next_mv)
  \<comment> \<open>BabTm_Call: threads through resolve_callee, elab_term_list, build_call_result\<close>
  from "9.prems" obtain calleeName expArgTypes calleeInfo next_mv1 where
    resolve_eq: "resolve_callee env elabEnv ghost callee next_mv
                 = Inr (calleeName, expArgTypes, calleeInfo, next_mv1)"
    by (auto simp: build_call_result_def Let_def split: sum.splits CalleeInfo.splits prod.splits)
  \<comment> \<open>resolve_callee is monotone\<close>
  have resolve_mono: "next_mv \<le> next_mv1"
  proof (cases callee)
    case (BabTm_Name fnLoc fnName' tyArgs')
    from resolve_eq BabTm_Name show ?thesis
      by (auto simp: resolve_callee_def resolve_callee_function_def resolve_callee_data_ctor_def
                     resolve_type_args_def Let_def
               split: option.splits if_splits sum.splits)
  qed (use resolve_eq in \<open>simp_all add: resolve_callee_def\<close>)
  from "9.prems" resolve_eq have len_args: "length args = length expArgTypes"
    by (auto simp: build_call_result_def Let_def split: if_splits sum.splits CalleeInfo.splits prod.splits)
  from "9.prems" resolve_eq len_args obtain elabArgTms actualTypes next_mv2 where
    elab_args: "elab_term_list env elabEnv ghost args next_mv1 = Inr (elabArgTms, actualTypes, next_mv2)"
    by (auto simp: build_call_result_def Let_def split: sum.splits CalleeInfo.splits prod.splits)
  have m2: "next_mv1 \<le> next_mv2"
    using "9.IH" resolve_eq len_args elab_args
    by (auto simp: resolve_callee_def build_call_result_def Let_def
             split: sum.splits BabTerm.splits option.splits CalleeInfo.splits prod.splits)
  from "9.prems" resolve_eq len_args elab_args have "next_mv' = next_mv2"
    by (auto simp: build_call_result_def Let_def unify_and_coerce_def
             split: sum.splits CalleeInfo.splits prod.splits)
  with resolve_mono m2 show ?case by simp
next
  case (10 env elabEnv ghost loc tms next_mv)
  \<comment> \<open>BabTm_Tuple: forwards elab_term_list's next_mv\<close>
  from "10.prems" show ?case
    by (auto simp: Let_def split: sum.splits dest!: "10.IH")
next
  case (11 env elabEnv ghost loc flds next_mv)
  \<comment> \<open>BabTm_Record: forwards elab_term_list's next_mv\<close>
  from "11.prems" show ?case
    by (auto simp: Let_def split: sum.splits option.splits dest!: "11.IH")
next
  case (12 env elabEnv ghost loc tm flds next_mv)
  \<comment> \<open>BabTm_RecordUpdate: threads through parent and update list next_mv\<close>
  from "12.prems"(1) have no_dup: "first_duplicate_name fst flds = None"
    by (auto split: option.splits)
  from "12.prems"(1) no_dup obtain parentTm parentTy next_mv1 where
    elab_parent: "elab_term env elabEnv ghost tm next_mv = Inr (parentTm, parentTy, next_mv1)"
    by (auto split: sum.splits option.splits)
  have mono1: "next_mv \<le> next_mv1"
    using "12.IH"(1)[OF no_dup] elab_parent by simp
  from "12.prems"(1) elab_parent obtain parentFields where
    parent_rec: "parentTy = CoreTy_Record parentFields"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits option.splits CoreType.splits if_splits prod.splits)
  from "12.prems"(1) no_dup elab_parent parent_rec have
    fields_exist: "check_update_fields_exist flds parentFields = None"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  from "12.prems"(1) no_dup elab_parent parent_rec fields_exist
  obtain newUpdateTms actualTypes next_mv2 where
    elab_updates: "elab_term_list env elabEnv ghost (map snd flds) next_mv1
                   = Inr (newUpdateTms, actualTypes, next_mv2)"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  have pair1: "(parentTm, parentTy, next_mv1) = (parentTm, parentTy, next_mv1)" by simp
  have pair2: "(parentTy, next_mv1) = (parentTy, next_mv1)" by simp
  have mono2: "next_mv1 \<le> next_mv2"
    using "12.IH"(2)[OF no_dup elab_parent pair1 pair2 parent_rec fields_exist]
          elab_updates by simp
  from "12.prems"(1) elab_parent parent_rec elab_updates have "next_mv' = next_mv2"
    by (auto simp: Let_def unify_and_coerce_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  with mono1 mono2 show ?case by simp
next
  case (13 env elabEnv ghost loc tm idx next_mv)
  \<comment> \<open>BabTm_TupleProj: forwards sub-term's next_mv\<close>
  from "13.prems" show ?case
    by (auto simp del: nat_to_string.simps split: sum.splits CoreType.splits option.splits dest!: "13.IH")
next
  case (14 env elabEnv ghost loc tm fldName next_mv)
  \<comment> \<open>BabTm_RecordProj: forwards sub-term's next_mv\<close>
  from "14.prems" show ?case
    by (auto split: sum.splits CoreType.splits option.splits dest!: "14.IH")
next
  case (15 env elabEnv ghost loc tm idxs next_mv)
  \<comment> \<open>BabTm_ArrayProj: threads through array term and index list\<close>
  from "15.prems"(1) obtain newArr arrTy next_mv1 where
    elab_arr: "elab_term env elabEnv ghost tm next_mv = Inr (newArr, arrTy, next_mv1)"
    by (auto split: sum.splits)
  have mono1: "next_mv \<le> next_mv1"
    using "15.IH"(1) elab_arr by simp
  from "15.prems"(1) elab_arr obtain elemTy dims where
    arr_ty: "arrTy = CoreTy_Array elemTy dims"
    by (auto simp: unify_and_coerce_def
             split: sum.splits CoreType.splits if_splits)
  from "15.prems"(1) elab_arr arr_ty have len_eq: "length idxs = length dims"
    by (auto simp: unify_and_coerce_def split: sum.splits if_splits)
  hence len_neq_false: "\<not> (length idxs \<noteq> length dims)" by simp
  from "15.prems"(1) elab_arr arr_ty len_eq
  obtain elabIdxTms actualTypes next_mv2 where
    elab_idxs: "elab_term_list env elabEnv ghost idxs next_mv1
                = Inr (elabIdxTms, actualTypes, next_mv2)"
    by (auto simp: unify_and_coerce_def split: sum.splits)
  have pair1: "(newArr, arrTy, next_mv1) = (newArr, arrTy, next_mv1)" by simp
  have pair2: "(arrTy, next_mv1) = (arrTy, next_mv1)" by simp
  have mono2: "next_mv1 \<le> next_mv2"
    using "15.IH"(2)[OF elab_arr pair1 pair2 arr_ty len_neq_false] elab_idxs by simp
  from "15.prems"(1) elab_arr arr_ty len_eq elab_idxs have "next_mv' = next_mv2"
    by (auto simp: unify_and_coerce_def split: sum.splits)
  with mono1 mono2 show ?case by simp
next
  case "16"  \<comment> \<open>BabTm_Match: undefined\<close>
  from "16.prems" show ?case sorry
next
  case (17 env elabEnv ghost loc tm next_mv)
  \<comment> \<open>BabTm_Sizeof: forwards sub-term's next_mv\<close>
  from "17.prems" show ?case
    using "17.IH" by (auto split: sum.splits CoreType.splits if_splits)
next
  case (18 env elabEnv ghost loc tm next_mv)
  \<comment> \<open>BabTm_Allocated: forwards sub-term's next_mv\<close>
  from "18.prems" show ?case
    using "18.IH" by (auto split: sum.splits if_splits)
next
  case (19 env elabEnv ghost loc tm next_mv)
  \<comment> \<open>BabTm_Old: forwards sub-term's next_mv\<close>
  from "19.prems" show ?case
    using "19.IH" by (auto split: sum.splits if_splits)
next
  case "20" \<comment> \<open>elab_term_list: Nil\<close>
  from "20.prems" show ?case by simp
next
  case (21 env elabEnv ghost tm tms next_mv)
  \<comment> \<open>elab_term_list: Cons\<close>
  from "21.prems" obtain tm'' ty'' next_mv1 tms'' tys'' next_mv2 where
    elab_head: "elab_term env elabEnv ghost tm next_mv = Inr (tm'', ty'', next_mv1)" and
    elab_tail: "elab_term_list env elabEnv ghost tms next_mv1 = Inr (tms'', tys'', next_mv2)"
    by (auto split: sum.splits)
  have m1: "next_mv \<le> next_mv1"
    using "21.IH"(1) elab_head by simp
  have m2: "next_mv1 \<le> next_mv2"
    using "21.IH"(3) elab_head elab_tail by simp
  from "21.prems" elab_head elab_tail have "next_mv' = next_mv2"
    by (auto split: sum.splits)
  with m1 m2 show ?case by simp
qed

(* Length of elab_term_list output matches input *)
lemma elab_term_list_length:
  "elab_term_list env elabEnv ghost tms next_mv = Inr (tms', tys', next_mv')
   \<Longrightarrow> length tms' = length tms \<and> length tys' = length tms"
proof (induction tms arbitrary: tms' tys' next_mv next_mv')
  case Nil
  then show ?case by simp
next
  case (Cons tm tms)
  then show ?case by (auto split: sum.splits)
qed

(* Correctness of resolve_type_args:
   If it succeeds, the returned type arguments have the right length,
   are well-kinded in the extended env, and are runtime types in NotGhost mode. *)
lemma resolve_type_args_correct:
  assumes "resolve_type_args env elabEnv ghost loc name tyvars tyArgs next_mv
           = Inr (newTyArgs, next_mv')"
      and "tyenv_well_formed env"
      and "typedefs_well_formed env (EE_Typedefs elabEnv)"
  shows "next_mv \<le> next_mv'
       \<and> length newTyArgs = length tyvars
       \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs
       \<and> (ghost = NotGhost \<longrightarrow>
            list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs)"
proof -
  let ?numTyParams = "length tyvars"
  show ?thesis
  proof (cases "tyArgs = [] \<and> ?numTyParams > 0")
    case True
    \<comment> \<open>Type args were omitted - metavariables generated\<close>
    let ?genTyArgs = "map CoreTy_Var [next_mv..<next_mv + ?numTyParams]"
    from assms(1) True
    have results: "newTyArgs = ?genTyArgs"
                  "next_mv' = next_mv + ?numTyParams"
      by (auto simp: resolve_type_args_def Let_def)
    have len_ok: "length ?genTyArgs = ?numTyParams" by simp
    have mono: "next_mv \<le> next_mv'" using results by simp
    let ?env_ext = "extend_env_with_tyvars env ghost next_mv next_mv'"
    have all_in_tv: "\<forall>n \<in> set [next_mv..<next_mv + ?numTyParams]. n |\<in>| TE_TypeVars ?env_ext"
      using results by (auto simp: extend_env_with_tyvars_def fset_of_list_elem)
    have wk_ok: "list_all (is_well_kinded ?env_ext) ?genTyArgs"
      using list_all_tyvar_is_well_kinded[OF all_in_tv] .
    have all_in_rtv: "ghost = NotGhost \<Longrightarrow>
                       \<forall>n \<in> set [next_mv..<next_mv + ?numTyParams]. n |\<in>| TE_RuntimeTypeVars ?env_ext"
      using results by (auto simp: extend_env_with_tyvars_def fset_of_list_elem)
    have runtime_ok: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env_ext) ?genTyArgs"
      using all_in_rtv list_all_tyvar_is_runtime by blast
    show ?thesis
      using results len_ok wk_ok runtime_ok mono by auto
  next
    case False
    show ?thesis
    proof (cases "?numTyParams = length tyArgs")
      case True
      from assms(1) False True
      obtain elabTyArgs where
        elab_tyargs: "elab_type_list env elabEnv ghost tyArgs = Inr elabTyArgs"
        by (cases "elab_type_list env elabEnv ghost tyArgs")
           (auto simp: resolve_type_args_def Let_def split: if_splits)
      from assms(1) False True elab_tyargs
      have results: "newTyArgs = elabTyArgs"
                    "next_mv' = next_mv"
        by (auto simp: resolve_type_args_def Let_def)
      have len_ok: "length elabTyArgs = ?numTyParams"
        using elab_tyargs True elab_type_list_length by fastforce
      have mono: "next_mv \<le> next_mv'" using results by simp
      have env_eq: "extend_env_with_tyvars env ghost next_mv next_mv' = env"
        using results by simp
      have wk_ok: "list_all (is_well_kinded env) elabTyArgs"
        using elab_tyargs assms(2,3) elab_type_is_well_kinded(2) by auto
      have runtime_ok: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) elabTyArgs"
        using elab_tyargs assms(2,3) elab_type_notghost_is_runtime(2) by (cases ghost; auto)
      show ?thesis
        using results len_ok wk_ok runtime_ok mono env_eq by auto
    next
      case False2: False
      from assms(1) False False2
      have "False" by (auto simp: resolve_type_args_def Let_def split: sum.splits if_splits)
      thus ?thesis ..
    qed
  qed
qed


(* ============================================================================== *)
(* Function call and datatype construction correctness *)
(* ============================================================================== *)

(* Validity predicate for a function callee: the function exists, is pure,
   satisfies ghost constraints, type args are well-kinded/runtime,
   and expArgTypes + retType are consistent with the function declaration. *)
definition callee_info_valid_function ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> string \<Rightarrow> CoreType list \<Rightarrow> CoreType \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "callee_info_valid_function env ghost fnName tyArgs retType expArgTypes =
    (\<exists>funInfo.
       fmlookup (TE_Functions env) fnName = Some funInfo
     \<and> (ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost)
     \<and> \<not> FI_Impure funInfo
     \<and> list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)
     \<and> length tyArgs = length (FI_TyArgs funInfo)
     \<and> list_all (is_well_kinded env) tyArgs
     \<and> (ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs)
     \<and> expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                         (FI_TmArgs funInfo)
     \<and> retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                              (FI_ReturnType funInfo))"

(* Validity predicate for a data constructor callee: the constructor exists,
   satisfies ghost constraints, type args are well-kinded/runtime,
   and expArgTypes are consistent with the payload type and arity. *)
definition callee_info_valid_data_ctor ::
  "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> string \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> CoreType list \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "callee_info_valid_data_ctor env ghost ctorName dtName arity tyArgs expArgTypes =
    (\<exists>tyvars payloadTy.
       fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)
     \<and> (ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes env)
     \<and> length tyArgs = length tyvars
     \<and> list_all (is_well_kinded env) tyArgs
     \<and> (ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) tyArgs)
     \<and> (arity = 0 \<longrightarrow> payloadTy = CoreTy_Record [])
     \<and> (arity \<ge> 2 \<longrightarrow> (\<exists>fieldTys. payloadTy = CoreTy_Record (zip (tuple_field_names arity) fieldTys)
                                 \<and> length fieldTys = arity))
     \<and> (let subst = fmap_of_list (zip tyvars tyArgs) in
          expArgTypes = (if arity = 0 then []
                         else if arity = 1 then [apply_subst subst payloadTy]
                         else case payloadTy of
                                CoreTy_Record flds \<Rightarrow>
                                  map (\<lambda>(_, ty). apply_subst subst ty) flds
                              | _ \<Rightarrow> [])))"

(* Combined validity predicate: dispatches to the appropriate sub-predicate. *)
definition callee_info_valid :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CalleeInfo \<Rightarrow> CoreType list \<Rightarrow> bool" where
  "callee_info_valid env ghost ci expArgTypes =
    (case ci of
      CI_Function fnName tyArgs retType \<Rightarrow>
        callee_info_valid_function env ghost fnName tyArgs retType expArgTypes
    | CI_DataCtor ctorName dtName arity tyArgs \<Rightarrow>
        callee_info_valid_data_ctor env ghost ctorName dtName arity tyArgs expArgTypes)"

(* callee_info_valid is monotone in the type-variable interval. *)
lemma callee_info_valid_mono:
  assumes "callee_info_valid (extend_env_with_tyvars env ghost lo hi) ghost ci expArgTypes"
      and "lo' \<le> lo" and "hi \<le> hi'"
  shows "callee_info_valid (extend_env_with_tyvars env ghost lo' hi') ghost ci expArgTypes"
proof (cases ci)
  case (CI_Function fnName tyArgs retType)
  let ?env1 = "extend_env_with_tyvars env ghost lo hi"
  let ?env2 = "extend_env_with_tyvars env ghost lo' hi'"
  from assms(1) CI_Function obtain funInfo where props:
    "fmlookup (TE_Functions ?env1) fnName = Some funInfo"
    "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    "\<not> FI_Impure funInfo"
    "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)"
    "length tyArgs = length (FI_TyArgs funInfo)"
    "list_all (is_well_kinded ?env1) tyArgs"
    "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env1) tyArgs"
    "expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                       (FI_TmArgs funInfo)"
    "retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                            (FI_ReturnType funInfo)"
    unfolding callee_info_valid_def callee_info_valid_function_def by auto
  have fn_eq: "fmlookup (TE_Functions ?env2) fnName = Some funInfo"
    using props(1) by (simp add: extend_env_with_tyvars_def)
  have wk: "list_all (is_well_kinded ?env2) tyArgs"
    using props(6) by (auto simp: list_all_iff
            intro: is_well_kinded_extend_env_with_tyvars_mono[OF _ assms(2,3)])
  have rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env2) tyArgs"
    using props(7) by (auto simp: list_all_iff
            intro: is_runtime_type_extend_env_with_tyvars_mono[OF _ assms(2,3)])
  show ?thesis using CI_Function fn_eq props(2,3,4,5,8,9) wk rt
    unfolding callee_info_valid_def callee_info_valid_function_def by auto
next
  case (CI_DataCtor ctorName dtName arity tyArgs)
  let ?env1 = "extend_env_with_tyvars env ghost lo hi"
  let ?env2 = "extend_env_with_tyvars env ghost lo' hi'"
  from assms(1) CI_DataCtor obtain tyvars payloadTy where props:
    "fmlookup (TE_DataCtors ?env1) ctorName = Some (dtName, tyvars, payloadTy)"
    "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes ?env1"
    "length tyArgs = length tyvars"
    "list_all (is_well_kinded ?env1) tyArgs"
    "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env1) tyArgs"
    "arity = 0 \<longrightarrow> payloadTy = CoreTy_Record []"
    "arity \<ge> 2 \<longrightarrow> (\<exists>fieldTys. payloadTy = CoreTy_Record (zip (tuple_field_names arity) fieldTys)
                              \<and> length fieldTys = arity)"
    "let subst = fmap_of_list (zip tyvars tyArgs) in
       expArgTypes = (if arity = 0 then []
                      else if arity = 1 then [apply_subst subst payloadTy]
                      else case payloadTy of
                             CoreTy_Record flds \<Rightarrow> map (\<lambda>(_, ty). apply_subst subst ty) flds
                           | _ \<Rightarrow> [])"
    unfolding callee_info_valid_def callee_info_valid_data_ctor_def by auto
  have dc_eq: "fmlookup (TE_DataCtors ?env2) ctorName = Some (dtName, tyvars, payloadTy)"
    using props(1) by (simp add: extend_env_with_tyvars_def)
  have ghost_eq: "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes ?env2"
    using props(2) by (simp add: extend_env_with_tyvars_def)
  have wk: "list_all (is_well_kinded ?env2) tyArgs"
    using props(4) by (auto simp: list_all_iff
            intro: is_well_kinded_extend_env_with_tyvars_mono[OF _ assms(2,3)])
  have rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env2) tyArgs"
    using props(5) by (auto simp: list_all_iff
            intro: is_runtime_type_extend_env_with_tyvars_mono[OF _ assms(2,3)])
  show ?thesis using CI_DataCtor dc_eq ghost_eq props(3,6,7,8) wk rt
    unfolding callee_info_valid_def callee_info_valid_data_ctor_def by auto
qed

(* Correctness of resolve_callee_function:
   If it succeeds, callee_info_valid_function holds in the extended env. *)
lemma resolve_callee_function_correct:
  assumes "resolve_callee_function env elabEnv ghost loc name tyArgs next_mv
           = Inr (calleeName, expArgTypes, calleeInfo, next_mv')"
      and "tyenv_well_formed env"
      and "typedefs_well_formed env (EE_Typedefs elabEnv)"
  shows "\<exists>newTyArgs retType.
     calleeName = name
   \<and> calleeInfo = CI_Function name newTyArgs retType
   \<and> next_mv \<le> next_mv'
   \<and> callee_info_valid_function (extend_env_with_tyvars env ghost next_mv next_mv')
                                ghost name newTyArgs retType expArgTypes
   \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes
   \<and> (ghost = NotGhost \<longrightarrow>
        list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes)"
proof -
  from assms(1) obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) name = Some funInfo"
    by (auto simp: resolve_callee_function_def resolve_type_args_def Let_def
             split: option.splits if_splits sum.splits)
  from assms(1) fn_lookup have not_void: "name |\<notin>| EE_VoidFunctions elabEnv"
    by (auto simp: resolve_callee_function_def split: if_splits sum.splits)
  from assms(1) fn_lookup not_void have not_impure: "\<not> FI_Impure funInfo"
    by (auto simp: resolve_callee_function_def split: if_splits sum.splits)
  from assms(1) fn_lookup not_void not_impure have
    all_var: "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)"
    by (auto simp: resolve_callee_function_def split: if_splits sum.splits)
  from assms(1) fn_lookup not_void not_impure all_var have
    ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    by (auto simp: resolve_callee_function_def split: if_splits sum.splits)

  from assms(1) fn_lookup not_void not_impure all_var ghost_ok
  obtain newTyArgs next_mv1 where
    name_eq: "calleeName = name" and
    resolve_eq: "resolve_type_args env elabEnv ghost loc name (FI_TyArgs funInfo) tyArgs next_mv
                 = Inr (newTyArgs, next_mv1)" and
    next_mv_eq: "next_mv' = next_mv1" and
    expArg_eq: "expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)
                                  (FI_TmArgs funInfo)" and
    ci_eq: "calleeInfo = CI_Function name newTyArgs
              (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) (FI_ReturnType funInfo))"
    by (auto simp: resolve_callee_function_def Let_def split: sum.splits)

  have rta: "next_mv \<le> next_mv'
           \<and> length newTyArgs = length (FI_TyArgs funInfo)
           \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs
           \<and> (ghost = NotGhost \<longrightarrow>
                list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs)"
    using resolve_type_args_correct[OF resolve_eq assms(2,3)] next_mv_eq by simp

  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  have fn_lookup': "fmlookup (TE_Functions ?env') name = Some funInfo"
    using fn_lookup by (simp add: extend_env_with_tyvars_def)

  have civ: "callee_info_valid_function ?env' ghost name newTyArgs
               (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) (FI_ReturnType funInfo))
               expArgTypes"
    unfolding callee_info_valid_function_def
    using fn_lookup' ghost_ok not_impure all_var rta expArg_eq by auto

  \<comment> \<open>expArgTypes well-kinded: each is apply_subst of a function param type\<close>
  have wf': "tyenv_well_formed ?env'"
    using assms(2) tyenv_well_formed_extend_env_with_tyvars by blast
  have tyargs_wk: "list_all (is_well_kinded ?env') newTyArgs" using rta by simp
  have "tyenv_fun_types_well_kinded ?env'"
    using wf' tyenv_well_formed_def by blast
  hence fi_args_wk_inner: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
            is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) ty"
    using fn_lookup' tyenv_fun_types_well_kinded_def by blast
  have len_tyargs: "length newTyArgs = length (FI_TyArgs funInfo)" using rta by simp
  have expArgTypes_wk: "list_all (is_well_kinded ?env') expArgTypes"
  proof -
    have "list_all (\<lambda>(_, ty, _). is_well_kinded ?env' (apply_subst
            (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)) (FI_TmArgs funInfo)"
    proof (unfold list_all_iff, intro ballI, clarify)
      fix n t v assume "(n, t, v) \<in> set (FI_TmArgs funInfo)"
      hence "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)" by (force simp: rev_image_eqI)
      with fi_args_wk_inner
      have "is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t" by blast
      thus "is_well_kinded ?env' (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) t)"
        using apply_subst_specializes_well_kinded[OF _ tyargs_wk len_tyargs[symmetric]] by simp
    qed
    thus ?thesis using expArg_eq by (auto simp: list_all_iff)
  qed

  \<comment> \<open>expArgTypes runtime\<close>
  have "tyenv_fun_ghost_constraint ?env'"
    using wf' tyenv_well_formed_def by blast
  hence fi_args_rt_inner: "FI_Ghost funInfo = NotGhost \<Longrightarrow>
          \<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
            is_runtime_type (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                      TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) ty"
    using fn_lookup' tyenv_fun_ghost_constraint_def by (simp add: Let_def)
  have expArgTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') expArgTypes"
  proof
    assume ng: "ghost = NotGhost"
    hence fg_ng: "FI_Ghost funInfo = NotGhost" using GhostOrNot.exhaust ghost_ok by auto
    have tyargs_rt: "list_all (is_runtime_type ?env') newTyArgs" using rta ng by simp
    have "list_all (\<lambda>(_, ty, _). is_runtime_type ?env' (apply_subst
            (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)) (FI_TmArgs funInfo)"
    proof (unfold list_all_iff, intro ballI, clarify)
      fix n t v assume "(n, t, v) \<in> set (FI_TmArgs funInfo)"
      hence "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)" by (force simp: rev_image_eqI)
      with fi_args_rt_inner[OF fg_ng]
      have "is_runtime_type (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                       TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t" by blast
      thus "is_runtime_type ?env' (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) t)"
        using apply_subst_specializes_runtime[OF _ tyargs_rt len_tyargs[symmetric]] by simp
    qed
    thus "list_all (is_runtime_type ?env') expArgTypes"
      using expArg_eq by (auto simp: list_all_iff)
  qed

  show ?thesis
    using name_eq ci_eq rta civ expArgTypes_wk expArgTypes_rt by blast
qed

(* Correctness of resolve_callee_data_ctor:
   If it succeeds, callee_info_valid_data_ctor holds in the extended env. *)
lemma resolve_callee_data_ctor_correct:
  assumes "resolve_callee_data_ctor env elabEnv ghost loc name arity tyArgs next_mv
           = Inr (calleeName, expArgTypes, calleeInfo, next_mv')"
      and "tyenv_well_formed env"
      and "elabenv_well_formed env elabEnv"
      and "fmlookup (EE_DataCtorArity elabEnv) name = Some arity"
  shows "\<exists>dtName newTyArgs.
     calleeName = name
   \<and> calleeInfo = CI_DataCtor name dtName arity newTyArgs
   \<and> next_mv \<le> next_mv'
   \<and> callee_info_valid_data_ctor (extend_env_with_tyvars env ghost next_mv next_mv')
                                 ghost name dtName arity newTyArgs expArgTypes
   \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes
   \<and> (ghost = NotGhost \<longrightarrow>
        list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes)"
proof -
  from assms(1) obtain dtName tyvars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) name = Some (dtName, tyvars, payloadTy)"
    by (auto simp: resolve_callee_data_ctor_def resolve_type_args_def Let_def
             split: option.splits if_splits sum.splits prod.splits)
  from assms(1) ctor_lookup have
    ghost_ok: "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes env"
    by (auto simp: resolve_callee_data_ctor_def split: if_splits sum.splits prod.splits)

  from assms(1) ctor_lookup ghost_ok
  obtain newTyArgs next_mv1 where
    name_eq: "calleeName = name" and
    resolve_eq: "resolve_type_args env elabEnv ghost loc name tyvars tyArgs next_mv
                 = Inr (newTyArgs, next_mv1)" and
    next_mv_eq: "next_mv' = next_mv1" and
    ci_eq: "calleeInfo = CI_DataCtor name dtName arity newTyArgs" and
    expArg_eq: "expArgTypes = (let subst = fmap_of_list (zip tyvars newTyArgs) in
                  if arity = 0 then []
                  else if arity = 1 then [apply_subst subst payloadTy]
                  else case payloadTy of
                         CoreTy_Record flds \<Rightarrow> map (\<lambda>(_, ty). apply_subst subst ty) flds
                       | _ \<Rightarrow> [])"
    by (auto simp: resolve_callee_data_ctor_def Let_def split: sum.splits prod.splits)

  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using assms(3) unfolding elabenv_well_formed_def by simp
  have rta: "next_mv \<le> next_mv'
           \<and> length newTyArgs = length tyvars
           \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs
           \<and> (ghost = NotGhost \<longrightarrow>
                list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs)"
    using resolve_type_args_correct[OF resolve_eq assms(2) td_wf] next_mv_eq by simp

  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  have ctor_lookup': "fmlookup (TE_DataCtors ?env') name = Some (dtName, tyvars, payloadTy)"
    using ctor_lookup by (simp add: extend_env_with_tyvars_def)
  have ghost_ok': "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes ?env'"
    using ghost_ok by (simp add: extend_env_with_tyvars_def)

  \<comment> \<open>From elabenv_well_formed: arity 0 implies payloadTy = CoreTy_Record []\<close>
  have arity_consistent: "data_ctor_arity_consistent env name arity"
    using assms(3,4) unfolding elabenv_well_formed_def by auto
  have arity_zero_payload: "arity = 0 \<longrightarrow> payloadTy = CoreTy_Record []"
    using arity_consistent ctor_lookup unfolding data_ctor_arity_consistent_def by auto

  have arity_ge2_payload: "arity \<ge> 2 \<longrightarrow> (\<exists>fieldTys. payloadTy = CoreTy_Record (zip (tuple_field_names arity) fieldTys)
                                                    \<and> length fieldTys = arity)"
    using arity_consistent ctor_lookup unfolding data_ctor_arity_consistent_def by auto

  have civ: "callee_info_valid_data_ctor ?env' ghost name dtName arity newTyArgs expArgTypes"
    unfolding callee_info_valid_data_ctor_def
    using ctor_lookup' ghost_ok' rta expArg_eq arity_zero_payload arity_ge2_payload by auto

  \<comment> \<open>expArgTypes well-kinded\<close>
  have wf': "tyenv_well_formed ?env'"
    using assms(2) tyenv_well_formed_extend_env_with_tyvars by blast
  have tyargs_wk: "list_all (is_well_kinded ?env') newTyArgs" using rta by simp
  have len_tyargs: "length newTyArgs = length tyvars" using rta by simp
  have "tyenv_payloads_well_kinded ?env'"
    using wf' tyenv_well_formed_def by blast
  hence payload_wk: "is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
    using ctor_lookup' tyenv_payloads_well_kinded_def by blast
  have "tyenv_ctor_tyvars_distinct env"
    using assms(2) tyenv_well_formed_def by blast
  hence tyvars_distinct: "distinct tyvars"
    using ctor_lookup tyenv_ctor_tyvars_distinct_def by blast
  let ?subst = "fmap_of_list (zip tyvars newTyArgs)"
  have payload_subst_wk: "is_well_kinded ?env' (apply_subst ?subst payloadTy)"
    using apply_subst_specializes_well_kinded[OF payload_wk tyargs_wk len_tyargs[symmetric]] .
  have expArgTypes_wk: "list_all (is_well_kinded ?env') expArgTypes"
  proof (cases "arity = 0")
    case True thus ?thesis using expArg_eq by (simp add: Let_def)
  next
    case False
    show ?thesis
    proof (cases "arity = 1")
      case True thus ?thesis using expArg_eq payload_subst_wk by (simp add: Let_def)
    next
      case False2: False
      \<comment> \<open>arity >= 2: expArgTypes are substituted record field types\<close>
      show ?thesis
      proof (cases payloadTy)
        case (CoreTy_Record flds)
        have "\<forall>(_, ty) \<in> set flds.
                is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) ty"
          using payload_wk CoreTy_Record by (auto simp: list_all_iff)
        hence "\<forall>(_, ty) \<in> set flds. is_well_kinded ?env' (apply_subst ?subst ty)"
          using apply_subst_specializes_well_kinded[OF _ tyargs_wk len_tyargs[symmetric]]
          by (auto simp: list_all_iff)
        thus ?thesis using expArg_eq False False2 CoreTy_Record
          by (auto simp: Let_def list_all_iff)
      qed (use expArg_eq False False2 in \<open>simp_all add: Let_def\<close>)
    qed
  qed

  \<comment> \<open>expArgTypes runtime\<close>
  have expArgTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') expArgTypes"
  proof
    assume ng: "ghost = NotGhost"
    have tyargs_rt: "list_all (is_runtime_type ?env') newTyArgs" using rta ng by simp
    have "tyenv_nonghost_payloads_runtime ?env'"
      using wf' tyenv_well_formed_def by blast
    hence payload_rt_inner: "dtName |\<notin>| TE_GhostDatatypes ?env' \<Longrightarrow>
            is_runtime_type (?env' \<lparr> TE_TypeVars := fset_of_list tyvars,
                                      TE_RuntimeTypeVars := fset_of_list tyvars \<rparr>) payloadTy"
      using ctor_lookup' tyenv_nonghost_payloads_runtime_def by blast
    have dt_not_ghost: "dtName |\<notin>| TE_GhostDatatypes ?env'" using ghost_ok' ng by simp
    have payload_subst_rt: "is_runtime_type ?env' (apply_subst ?subst payloadTy)"
      using apply_subst_specializes_runtime[OF payload_rt_inner[OF dt_not_ghost]
              tyargs_rt len_tyargs[symmetric]] .
    show "list_all (is_runtime_type ?env') expArgTypes"
    proof (cases "arity = 0")
      case True thus ?thesis using expArg_eq by (simp add: Let_def)
    next
      case False
      show ?thesis
      proof (cases "arity = 1")
        case True thus ?thesis using expArg_eq payload_subst_rt by (simp add: Let_def)
      next
        case False2: False
        show ?thesis
        proof (cases payloadTy)
          case (CoreTy_Record flds)
          have "\<forall>(_, ty) \<in> set flds.
                  is_runtime_type (?env' \<lparr> TE_TypeVars := fset_of_list tyvars,
                                            TE_RuntimeTypeVars := fset_of_list tyvars \<rparr>) ty"
            using payload_rt_inner[OF dt_not_ghost] CoreTy_Record by (auto simp: list_all_iff)
          hence "\<forall>(_, ty) \<in> set flds. is_runtime_type ?env' (apply_subst ?subst ty)"
            using apply_subst_specializes_runtime[OF _ tyargs_rt len_tyargs[symmetric]]
            by (auto simp: list_all_iff)
          thus ?thesis using expArg_eq False False2 CoreTy_Record
            by (auto simp: Let_def list_all_iff)
        qed (use expArg_eq False False2 in \<open>simp_all add: Let_def\<close>)
      qed
    qed
  qed

  show ?thesis
    using name_eq ci_eq rta civ expArgTypes_wk expArgTypes_rt by blast
qed

(* Combined resolve_callee correctness: monotonicity + callee_info_valid in the extended env. *)
lemma resolve_callee_correct:
  assumes "resolve_callee env elabEnv ghost callee next_mv
           = Inr (calleeName, expArgTypes, calleeInfo, next_mv')"
      and "tyenv_well_formed env"
      and "elabenv_well_formed env elabEnv"
  shows "next_mv \<le> next_mv'
       \<and> callee_info_valid (extend_env_with_tyvars env ghost next_mv next_mv') ghost calleeInfo expArgTypes
       \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes
       \<and> (ghost = NotGhost \<longrightarrow>
            list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes)"
proof (cases callee)
  case (BabTm_Name loc name tyArgs)
  show ?thesis
  proof (cases "fmlookup (EE_DataCtorArity elabEnv) name")
    case (Some arity)
    \<comment> \<open>Data constructor path\<close>
    from assms(1) BabTm_Name Some have
      resolve_dc: "resolve_callee_data_ctor env elabEnv ghost loc name arity tyArgs next_mv
                   = Inr (calleeName, expArgTypes, calleeInfo, next_mv')"
      by (simp add: resolve_callee_def)
    from resolve_callee_data_ctor_correct[OF resolve_dc assms(2,3) Some]
    obtain dtName newTyArgs where props:
      "calleeName = name"
      "calleeInfo = CI_DataCtor name dtName arity newTyArgs"
      "next_mv \<le> next_mv'"
      "callee_info_valid_data_ctor (extend_env_with_tyvars env ghost next_mv next_mv')
                                   ghost name dtName arity newTyArgs expArgTypes"
      "list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes"
      "ghost = NotGhost \<longrightarrow>
         list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes"
      by blast
    have civ: "callee_info_valid (extend_env_with_tyvars env ghost next_mv next_mv') ghost calleeInfo expArgTypes"
      using props by (simp add: callee_info_valid_def)
    show ?thesis using props civ by simp
  next
    case None
    \<comment> \<open>Function path\<close>
    from assms(1) BabTm_Name None have
      resolve_fn: "resolve_callee_function env elabEnv ghost loc name tyArgs next_mv
                   = Inr (calleeName, expArgTypes, calleeInfo, next_mv')"
      by (simp add: resolve_callee_def)
    have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
      using assms(3) unfolding elabenv_well_formed_def by simp
    from resolve_callee_function_correct[OF resolve_fn assms(2) td_wf]
    obtain newTyArgs retType where props:
      "calleeName = name"
      "calleeInfo = CI_Function name newTyArgs retType"
      "next_mv \<le> next_mv'"
      "callee_info_valid_function (extend_env_with_tyvars env ghost next_mv next_mv')
                                  ghost name newTyArgs retType expArgTypes"
      "list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes"
      "ghost = NotGhost \<longrightarrow>
         list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) expArgTypes"
      by blast
    have civ: "callee_info_valid (extend_env_with_tyvars env ghost next_mv next_mv') ghost calleeInfo expArgTypes"
      using props by (simp add: callee_info_valid_def)
    show ?thesis using props civ by simp
  qed
qed (use assms(1) in \<open>simp_all add: resolve_callee_def\<close>)


(* Correctness of build_call_result:
   Given that calleeInfo is valid in env', the coerced args typecheck in env',
   and the substitution is well-kinded/runtime, the result term typechecks in env'.
   env' must be an extension of env that only adds type variables. *)
lemma build_call_result_correct:
  assumes build_eq: "build_call_result env ghost loc calleeInfo finalSubst finalArgTms
                     = (resultTm, resultTy)"
      and civ: "callee_info_valid env' ghost calleeInfo expArgTypes"
      and wf': "tyenv_well_formed env'"
      and wf: "tyenv_well_formed env"
      and coerce: "list_all2 (\<lambda>tm expTy. core_term_type env' ghost tm = Some (apply_subst finalSubst expTy))
                             finalArgTms expArgTypes"
      and subst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded env' ty"
      and subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type env' ty)"
      and subst_flex: "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> n |\<notin>| TE_TypeVars env"
      and locals_eq: "TE_LocalVars env' = TE_LocalVars env"
      and ret_eq: "TE_ReturnType env' = TE_ReturnType env"
  shows "core_term_type env' ghost resultTm = Some resultTy"
proof (cases calleeInfo)
  case (CI_Function fnName tyArgs retType)
  \<comment> \<open>Extract build_call_result outputs\<close>
  let ?finalTyArgs = "map (apply_subst finalSubst) tyArgs"
  from build_eq CI_Function have
    resultTm_eq: "resultTm = CoreTm_FunctionCall fnName ?finalTyArgs finalArgTms" and
    resultTy_eq: "resultTy = apply_subst finalSubst retType"
    by (auto simp: build_call_result_def Let_def)

  \<comment> \<open>Extract function info from callee_info_valid\<close>
  from civ CI_Function obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env') fnName = Some funInfo" and
    ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    not_impure: "\<not> FI_Impure funInfo" and
    all_var: "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)" and
    len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyargs_wk: "list_all (is_well_kinded env') tyArgs" and
    tyargs_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env') tyArgs" and
    expArgTypes_eq: "expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                                       (FI_TmArgs funInfo)" and
    retType_eq: "retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                        (FI_ReturnType funInfo)"
    unfolding callee_info_valid_def callee_info_valid_function_def by auto

  \<comment> \<open>Final type args well-kinded and runtime\<close>
  have finalTyArgs_wk: "list_all (is_well_kinded env') ?finalTyArgs"
    using tyargs_wk subst_wk by (auto simp: list_all_iff fmran'I
            intro: apply_subst_preserves_well_kinded split: option.splits)
  have finalTyArgs_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env') ?finalTyArgs"
    using tyargs_rt subst_rt by (auto simp: list_all_iff fmran'I
            intro: apply_subst_preserves_runtime split: option.splits)
  have len_finalTyArgs: "length ?finalTyArgs = length (FI_TyArgs funInfo)"
    using len_tyargs by simp

  \<comment> \<open>Coerced args match Core's expected types (double substitution)\<close>
  have "tyenv_fun_types_well_kinded env'"
    using wf' tyenv_well_formed_def by blast
  hence fi_args_wk_inner: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
            is_well_kinded (env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) ty"
    using fn_lookup tyenv_fun_types_well_kinded_def by blast
  have fi_args_tyvars: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). type_tyvars ty \<subseteq> set (FI_TyArgs funInfo)"
  proof
    fix ty assume "ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
    with fi_args_wk_inner
    have wk: "is_well_kinded (env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) ty" by blast
    have "type_tyvars ty \<subseteq> fset (TE_TypeVars (env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>))"
      using is_well_kinded_type_tyvars_subset[OF wk] .
    thus "type_tyvars ty \<subseteq> set (FI_TyArgs funInfo)"
      by (simp add: fset_of_list.rep_eq)
  qed
  have "tyenv_fun_tyvars_distinct env'"
    using wf' tyenv_well_formed_def by blast
  hence fi_tyargs_distinct: "distinct (FI_TyArgs funInfo)"
    using fn_lookup tyenv_fun_tyvars_distinct_def by blast

  let ?coreTySubst = "fmap_of_list (zip (FI_TyArgs funInfo) ?finalTyArgs)"
  let ?coreExpArgTypes = "map (\<lambda>(_, ty, _). apply_subst ?coreTySubst ty) (FI_TmArgs funInfo)"
  let ?argTys = "map (fst \<circ> snd) (FI_TmArgs funInfo)"

  have fi_args_tyvars': "\<forall>t \<in> set ?argTys. type_tyvars t \<subseteq> set (FI_TyArgs funInfo)"
    using fi_args_tyvars by auto
  have coreExpArgTypes_eq: "?coreExpArgTypes = map (apply_subst
      (fmap_of_list (zip (FI_TyArgs funInfo) (map (apply_subst finalSubst) tyArgs)))) ?argTys"
    by (induction "FI_TmArgs funInfo") auto
  have expArgTypes_fst: "expArgTypes = map (apply_subst
      (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))) ?argTys"
    using expArgTypes_eq by (induction "FI_TmArgs funInfo") auto
  have core_exp_eq: "?coreExpArgTypes = map (apply_subst finalSubst) expArgTypes"
    using len_tyargs fi_args_tyvars' fi_tyargs_distinct coreExpArgTypes_eq expArgTypes_fst
    by (metis map_apply_subst_compose_zip)

  have args_match: "list_all2 (\<lambda>tm expectedTy.
           case core_term_type env' ghost tm of
             None \<Rightarrow> False
           | Some actualTy \<Rightarrow> actualTy = expectedTy)
         finalArgTms ?coreExpArgTypes"
    using coerce core_exp_eq by (simp add: list_all2_conv_all_nth)

  have len_finalArgTms: "length finalArgTms = length (FI_TmArgs funInfo)"
    using coerce expArgTypes_eq by (simp add: list_all2_lengthD)

  \<comment> \<open>Return type after double substitution\<close>
  have fi_ret_tyvars: "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
  proof -
    have "tyenv_fun_types_well_kinded env'"
      using wf' tyenv_well_formed_def by blast
    hence wk: "is_well_kinded (env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                              (FI_ReturnType funInfo)"
      using fn_lookup tyenv_fun_types_well_kinded_def by blast
    have "type_tyvars (FI_ReturnType funInfo) \<subseteq>
          fset (TE_TypeVars (env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>))"
      using is_well_kinded_type_tyvars_subset[OF wk] .
    thus ?thesis by (simp add: fset_of_list.rep_eq)
  qed
  have ret_eq2: "resultTy = apply_subst ?coreTySubst (FI_ReturnType funInfo)"
    using resultTy_eq retType_eq len_tyargs fi_ret_tyvars fi_tyargs_distinct
    by (simp add: apply_subst_compose_zip)

  show ?thesis
    using resultTm_eq fn_lookup ghost_ok not_impure all_var
          len_finalTyArgs finalTyArgs_wk finalTyArgs_rt
          len_finalArgTms args_match ret_eq2
    by (simp add: Let_def)
next
  case (CI_DataCtor ctorName dtName arity tyArgs)
  let ?finalTyArgs = "map (apply_subst finalSubst) tyArgs"
  let ?payload = "if arity = 0 then CoreTm_Record []
                  else if arity = 1 then hd finalArgTms
                  else CoreTm_Record (zip (tuple_field_names arity) finalArgTms)"

  \<comment> \<open>Extract build_call_result outputs\<close>
  from build_eq CI_DataCtor have
    resultTm_eq: "resultTm = CoreTm_VariantCtor ctorName ?finalTyArgs ?payload" and
    resultTy_eq: "resultTy = CoreTy_Datatype dtName ?finalTyArgs"
    by (auto simp: build_call_result_def Let_def split: if_splits)

  \<comment> \<open>Extract data ctor info from callee_info_valid\<close>
  from civ CI_DataCtor obtain tyvars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env') ctorName = Some (dtName, tyvars, payloadTy)" and
    ghost_ok: "ghost = NotGhost \<longrightarrow> dtName |\<notin>| TE_GhostDatatypes env'" and
    len_tyargs: "length tyArgs = length tyvars" and
    tyargs_wk: "list_all (is_well_kinded env') tyArgs" and
    tyargs_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env') tyArgs" and
    arity_zero_payload: "arity = 0 \<longrightarrow> payloadTy = CoreTy_Record []" and
    arity_ge2_payload: "arity \<ge> 2 \<longrightarrow> (\<exists>fieldTys. payloadTy = CoreTy_Record (zip (tuple_field_names arity) fieldTys)
                                                \<and> length fieldTys = arity)" and
    expArg_eq: "let subst = fmap_of_list (zip tyvars tyArgs) in
                  expArgTypes = (if arity = 0 then []
                                 else if arity = 1 then [apply_subst subst payloadTy]
                                 else case payloadTy of
                                        CoreTy_Record flds \<Rightarrow>
                                          map (\<lambda>(_, ty). apply_subst subst ty) flds
                                      | _ \<Rightarrow> [])"
    unfolding callee_info_valid_def callee_info_valid_data_ctor_def by auto

  \<comment> \<open>Final type args well-kinded and runtime\<close>
  have finalTyArgs_wk: "list_all (is_well_kinded env') ?finalTyArgs"
    using tyargs_wk subst_wk by (auto simp: list_all_iff fmran'I
            intro: apply_subst_preserves_well_kinded split: option.splits)
  have finalTyArgs_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env') ?finalTyArgs"
    using tyargs_rt subst_rt by (auto simp: list_all_iff fmran'I
            intro: apply_subst_preserves_runtime split: option.splits)
  have len_finalTyArgs: "length ?finalTyArgs = length tyvars"
    using len_tyargs by simp

  \<comment> \<open>Distinct tyvars\<close>
  have "tyenv_ctor_tyvars_distinct env'"
    using wf' tyenv_well_formed_def by blast
  hence tyvars_distinct: "distinct tyvars"
    using ctor_lookup tyenv_ctor_tyvars_distinct_def by blast

  \<comment> \<open>Payload type well-kinded (for the double-substitution argument)\<close>
  have "tyenv_payloads_well_kinded env'"
    using wf' tyenv_well_formed_def by blast
  hence payload_wk: "is_well_kinded (env' \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
    using ctor_lookup tyenv_payloads_well_kinded_def by blast
  have payload_tyvars: "type_tyvars payloadTy \<subseteq> set tyvars"
  proof -
    have "type_tyvars payloadTy \<subseteq> fset (TE_TypeVars (env' \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>))"
      using is_well_kinded_type_tyvars_subset[OF payload_wk] .
    thus ?thesis by (simp add: fset_of_list.rep_eq)
  qed

  \<comment> \<open>Core type substitution = fmap_of_list (zip tyvars finalTyArgs)\<close>
  let ?coreTySubst = "fmap_of_list (zip tyvars ?finalTyArgs)"
  let ?origSubst = "fmap_of_list (zip tyvars tyArgs)"

  \<comment> \<open>Double substitution: apply_subst finalSubst (apply_subst origSubst payloadTy)
     = apply_subst coreTySubst payloadTy\<close>
  have payload_double_subst:
    "apply_subst finalSubst (apply_subst ?origSubst payloadTy) = apply_subst ?coreTySubst payloadTy"
    using len_tyargs payload_tyvars tyvars_distinct
    by (simp add: apply_subst_compose_zip)

  \<comment> \<open>Show payload typechecks with the expected type\<close>
  have payload_typed: "core_term_type env' ghost ?payload = Some (apply_subst ?coreTySubst payloadTy)"
  proof (cases "arity = 0")
    case True
    hence "payloadTy = CoreTy_Record []" using arity_zero_payload by simp
    thus ?thesis using True by simp
  next
    case False
    show ?thesis
    proof (cases "arity = 1")
      case True
      \<comment> \<open>Single argument: payload = hd finalArgTms\<close>
      from expArg_eq True have exp_eq: "expArgTypes = [apply_subst ?origSubst payloadTy]"
        by (simp add: Let_def)
      from coerce exp_eq have "core_term_type env' ghost (hd finalArgTms)
                                = Some (apply_subst finalSubst (apply_subst ?origSubst payloadTy))"
        using list.rel_cases by fastforce
      thus ?thesis using False True payload_double_subst by simp
    next
      case False2: False
      \<comment> \<open>Multiple arguments: payload = CoreTm_Record (zip (tuple_field_names arity) finalArgTms)\<close>
      from False False2 have "arity \<ge> 2" by arith
      with arity_ge2_payload obtain fieldTys where
        payload_rec: "payloadTy = CoreTy_Record (zip (tuple_field_names arity) fieldTys)" and
        len_fieldTys: "length fieldTys = arity"
        by auto
      let ?flds = "zip (tuple_field_names arity) fieldTys"
      from expArg_eq False False2 payload_rec
      have exp_eq: "expArgTypes = map (\<lambda>(_, ty). apply_subst ?origSubst ty) ?flds"
        by (simp add: Let_def)

      \<comment> \<open>Each coerced arg types to the double-substituted field type\<close>
      have fld_tyvars: "\<forall>(_, ty) \<in> set ?flds. type_tyvars ty \<subseteq> set tyvars"
        using payload_tyvars payload_rec by fastforce
      have fld_double_subst: "\<forall>(_, ty) \<in> set ?flds.
              apply_subst finalSubst (apply_subst ?origSubst ty) = apply_subst ?coreTySubst ty"
        using len_tyargs tyvars_distinct fld_tyvars
        by (auto simp: apply_subst_compose_zip)
      have len_expArgTypes: "length expArgTypes = length ?flds"
        using exp_eq by simp
      have len_finalArgTms: "length finalArgTms = length expArgTypes"
        using coerce by (simp add: list_all2_lengthD)

      \<comment> \<open>Each finalArgTm types to the corresponding core field type\<close>
      have args_typed: "\<forall>i < length ?flds.
              core_term_type env' ghost (finalArgTms ! i)
              = Some (apply_subst ?coreTySubst (snd (?flds ! i)))"
      proof (intro allI impI)
        fix i assume i_lt: "i < length ?flds"
        have "core_term_type env' ghost (finalArgTms ! i)
              = Some (apply_subst finalSubst (expArgTypes ! i))"
          using coerce i_lt len_expArgTypes by (auto simp: list_all2_conv_all_nth)
        also have "expArgTypes ! i = apply_subst ?origSubst (snd (?flds ! i))"
          using exp_eq i_lt by auto
        also have "apply_subst finalSubst (apply_subst ?origSubst (snd (?flds ! i)))
                   = apply_subst ?coreTySubst (snd (?flds ! i))"
        proof -
          have "?flds ! i \<in> set ?flds" using i_lt nth_mem by blast
          with fld_double_subst show ?thesis by (cases "?flds ! i") auto
        qed
        finally show "core_term_type env' ghost (finalArgTms ! i)
                      = Some (apply_subst ?coreTySubst (snd (?flds ! i)))" .
      qed

      \<comment> \<open>tuple_field_names are distinct\<close>
      have distinct_names: "distinct (tuple_field_names arity)"
        using distinct_tuple_field_names .

      \<comment> \<open>The substituted payload type\<close>
      have subst_rec: "apply_subst ?coreTySubst payloadTy
                       = CoreTy_Record (map (\<lambda>(n, ty). (n, apply_subst ?coreTySubst ty)) ?flds)"
        using payload_rec by (induction ?flds) auto

      \<comment> \<open>CoreTm_Record typing\<close>
      have payload_eq: "?payload = CoreTm_Record (zip (tuple_field_names arity) finalArgTms)"
        using False False2 by simp

      \<comment> \<open>field names are tuple_field_names arity, which are distinct\<close>
      have fst_flds: "map fst ?flds = tuple_field_names arity"
        using len_fieldTys by simp

      \<comment> \<open>The snd of each field = fieldTys ! i\<close>
      have snd_flds: "map snd ?flds = fieldTys"
        using len_fieldTys by (simp add: tuple_field_names_def)

      \<comment> \<open>lengths match\<close>
      have len_flds: "length ?flds = arity"
        using len_fieldTys by simp
      have len_args_arity: "length finalArgTms = arity"
        using len_finalArgTms len_expArgTypes len_flds by simp

      \<comment> \<open>Each arg has a definite type (simplified)\<close>
      have each_typed: "\<forall>i < arity. core_term_type env' ghost (finalArgTms ! i)
                        = Some (apply_subst ?coreTySubst (fieldTys ! i))"
      proof (intro allI impI)
        fix i assume i_lt: "i < arity"
        hence i_lt': "i < length ?flds" using len_flds by simp
        from args_typed i_lt' have "core_term_type env' ghost (finalArgTms ! i)
              = Some (apply_subst ?coreTySubst (snd (?flds ! i)))" by simp
        moreover have "snd (?flds ! i) = fieldTys ! i"
          using i_lt len_fieldTys by (simp add: tuple_field_names_def)
        ultimately show "core_term_type env' ghost (finalArgTms ! i)
                         = Some (apply_subst ?coreTySubst (fieldTys ! i))" by simp
      qed

      \<comment> \<open>Build the those result\<close>
      have len_names: "length (tuple_field_names arity) = arity"
        by (simp add: tuple_field_names_def)
      have those_input: "map (\<lambda>(name, tm). core_term_type env' ghost tm)
                             (zip (tuple_field_names arity) finalArgTms)
                         = map (\<lambda>i. Some (apply_subst ?coreTySubst (fieldTys ! i))) [0..<arity]"
      proof (rule nth_equalityI)
        show "length (map (\<lambda>(name, tm). core_term_type env' ghost tm)
                          (zip (tuple_field_names arity) finalArgTms))
              = length (map (\<lambda>i. Some (apply_subst ?coreTySubst (fieldTys ! i))) [0..<arity])"
          using len_args_arity len_names by simp
      next
        fix i assume "i < length (map (\<lambda>(name, tm). core_term_type env' ghost tm)
                                      (zip (tuple_field_names arity) finalArgTms))"
        hence i_lt: "i < arity" using len_args_arity len_names by simp
        show "map (\<lambda>(name, tm). core_term_type env' ghost tm)
                  (zip (tuple_field_names arity) finalArgTms) ! i
              = map (\<lambda>i. Some (apply_subst ?coreTySubst (fieldTys ! i))) [0..<arity] ! i"
          using each_typed i_lt len_args_arity len_names
          by simp
      qed
      have those_ok: "those (map (\<lambda>(name, tm). core_term_type env' ghost tm)
                                 (zip (tuple_field_names arity) finalArgTms))
                      = Some (map (\<lambda>i. apply_subst ?coreTySubst (fieldTys ! i)) [0..<arity])"
        unfolding those_input those_eq_Some
        by (auto simp: list_all2_conv_all_nth)

      have result_tys: "map (\<lambda>i. apply_subst ?coreTySubst (fieldTys ! i)) [0..<arity]
                        = map (apply_subst ?coreTySubst) fieldTys"
        using len_fieldTys by (intro nth_equalityI) auto

      have zip_map_eq: "zip (tuple_field_names arity) (map (apply_subst ?coreTySubst) fieldTys)
                        = map2 (\<lambda>n ty. (n, apply_subst ?coreTySubst ty)) (tuple_field_names arity) fieldTys"
        by (rule nth_equalityI) (auto simp: len_fieldTys tuple_field_names_def)

      show ?thesis using payload_rec subst_rec payload_eq distinct_names
            fst_flds len_args_arity those_ok result_tys zip_map_eq
        by (simp add: Let_def tuple_field_names_def)
    qed
  qed

  show ?thesis
    using resultTm_eq resultTy_eq ctor_lookup len_finalTyArgs finalTyArgs_wk finalTyArgs_rt
          ghost_ok payload_typed
    by (simp add: Let_def)
qed


(* ============================================================================== *)
(* Correctness of type unification/coercion *)
(* ============================================================================== *)

(* Correctness of unify_type_lists (Phase 1):
   If it succeeds, the substitution is well-kinded and runtime-preserving,
   finalSubst extends accSubst (via composition with some theta),
   and for each pair of types, either they unify or both are finite integers. *)
lemma unify_type_lists_correct:
  assumes "unify_type_lists is_flex mk_err idx actualTys expectedTys accSubst = Inr finalSubst"
      and "tyenv_well_formed env"
      and "length actualTys = length expectedTys"
      and "list_all (is_well_kinded env) actualTys"
      and "list_all (is_well_kinded env) expectedTys"
      and "\<forall>ty \<in> fmran' accSubst. is_well_kinded env ty"
      and "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) actualTys"
      and "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) expectedTys"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' accSubst. is_runtime_type env ty)"
      and acc_dom_flex: "\<forall>n. n |\<in>| fmdom accSubst \<longrightarrow> is_flex n"
  shows "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type env ty))
       \<and> (\<exists>theta. finalSubst = compose_subst theta accSubst)
       \<and> list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
              \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
         actualTys expectedTys
       \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> is_flex n)"
  using assms
proof (induction is_flex mk_err idx actualTys expectedTys accSubst
       arbitrary: finalSubst
       rule: unify_type_lists.induct)
  case (1 is_flex mk_err idx accSubst)
  from "1.prems"(1) have finalSubst_eq: "finalSubst = accSubst" by simp
  moreover have "accSubst = compose_subst fmempty accSubst" by simp
  moreover from "1.prems"(10) finalSubst_eq have
    "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> is_flex n" by simp
  ultimately show ?case using "1.prems"(6,9) by blast
next
  case (2 is_flex mk_err idx actualTy actualTys expectedTy expectedTys accSubst)
  let ?actualTy' = "apply_subst accSubst actualTy"
  let ?expectedTy' = "apply_subst accSubst expectedTy"

  from "2.prems"(3) have len_tl: "length actualTys = length expectedTys" by simp
  from "2.prems"(4) have actualTy_wk: "is_well_kinded env actualTy"
    and actualTys_wk: "list_all (is_well_kinded env) actualTys" by simp_all
  from "2.prems"(5) have expectedTy_wk: "is_well_kinded env expectedTy"
    and expectedTys_wk: "list_all (is_well_kinded env) expectedTys" by simp_all
  from "2.prems"(7) have actualTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env actualTy"
    and actualTys_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) actualTys" by simp_all
  from "2.prems"(8) have expectedTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env expectedTy"
    and expectedTys_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) expectedTys" by simp_all

  show ?case
  proof (cases "unify is_flex ?actualTy' ?expectedTy'")
    case (Some newSubst)
    let ?composedSubst = "compose_subst newSubst accSubst"

    from "2.prems"(1) Some have
      recurse: "unify_type_lists is_flex mk_err (idx + 1) actualTys expectedTys ?composedSubst = Inr finalSubst"
      by (simp add: Let_def)

    \<comment> \<open>Simple case: src = tgt = env, so kind/runtime preservation reduces to
        checking that each bound meta in accSubst yields a well-kinded/runtime type.\<close>
    have wk_case: "\<And>t. is_well_kinded env t \<Longrightarrow> is_well_kinded env (apply_subst accSubst t)"
    proof -
      fix t assume t_wk: "is_well_kinded env t"
      show "is_well_kinded env (apply_subst accSubst t)"
      proof (rule apply_subst_preserves_well_kinded[OF t_wk])
        show "TE_Datatypes env = TE_Datatypes env" by simp
      next
        fix n assume n_in: "n |\<in>| TE_TypeVars env"
        show "case fmlookup accSubst n of
                Some ty' \<Rightarrow> is_well_kinded env ty'
              | None \<Rightarrow> n |\<in>| TE_TypeVars env"
          using n_in "2.prems"(6) by (auto simp: fmran'I split: option.splits)
      qed
    qed
    have rt_case: "\<And>t. ghost = NotGhost \<Longrightarrow> is_runtime_type env t \<Longrightarrow>
                       is_runtime_type env (apply_subst accSubst t)"
    proof -
      fix t assume ng: "ghost = NotGhost" and t_rt: "is_runtime_type env t"
      show "is_runtime_type env (apply_subst accSubst t)"
      proof (rule apply_subst_preserves_runtime[OF t_rt])
        show "TE_GhostDatatypes env = TE_GhostDatatypes env" by simp
      next
        fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars env"
        show "case fmlookup accSubst n of
                Some ty' \<Rightarrow> is_runtime_type env ty'
              | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
          using n_in "2.prems"(9) ng by (auto simp: fmran'I split: option.splits)
      qed
    qed
    have actualTy'_wk: "is_well_kinded env ?actualTy'"
      using actualTy_wk wk_case by blast
    have expectedTy'_wk: "is_well_kinded env ?expectedTy'"
      using expectedTy_wk wk_case by blast
    have actualTy'_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env ?actualTy'"
      using actualTy_rt rt_case by blast
    have expectedTy'_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env ?expectedTy'"
      using expectedTy_rt rt_case by blast

    have newSubst_wk: "\<forall>ty \<in> fmran' newSubst. is_well_kinded env ty"
      using Some actualTy'_wk expectedTy'_wk unify_preserves_well_kinded by blast
    have newSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' newSubst. is_runtime_type env ty)"
      using Some actualTy'_rt expectedTy'_rt unify_preserves_runtime by blast

    have composed_wk: "\<forall>ty \<in> fmran' ?composedSubst. is_well_kinded env ty"
      using newSubst_wk "2.prems"(6) compose_subst_preserves_well_kinded by blast
    have composed_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' ?composedSubst. is_runtime_type env ty)"
      using newSubst_rt "2.prems"(9) compose_subst_preserves_runtime by blast

    have newSubst_dom_flex: "\<forall>n. n |\<in>| fmdom newSubst \<longrightarrow> is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have composed_dom_flex: "\<forall>n. n |\<in>| fmdom ?composedSubst \<longrightarrow> is_flex n"
      using newSubst_dom_flex "2.prems"(10)
      by (auto simp: compose_subst_def)

    have ih: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
            \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type env ty))
            \<and> (\<exists>theta. finalSubst = compose_subst theta ?composedSubst)
            \<and> list_all2 (\<lambda>actualTy expectedTy.
                apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
                \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                   \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
              actualTys expectedTys
            \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> is_flex n)"
      using "2.IH"(2) Some len_tl actualTys_rt actualTys_wk "2.prems"(2) composed_rt composed_wk
        expectedTys_rt expectedTys_wk recurse composed_dom_flex by simp

    \<comment> \<open>From unify_sound, after applying newSubst the types are equal\<close>
    from unify_sound[OF Some]
    have "apply_subst newSubst ?actualTy' = apply_subst newSubst ?expectedTy'" .
    hence head_eq: "apply_subst ?composedSubst actualTy = apply_subst ?composedSubst expectedTy"
      by (simp add: compose_subst_correct)

    \<comment> \<open>From IH, finalSubst = compose_subst theta composedSubst for some theta\<close>
    from ih obtain theta where finalSubst_eq: "finalSubst = compose_subst theta ?composedSubst"
      by blast
    \<comment> \<open>So finalSubst = compose_subst theta (compose_subst newSubst accSubst)
         = compose_subst (compose_subst theta newSubst) accSubst\<close>
    have finalSubst_ext: "finalSubst = compose_subst (compose_subst theta newSubst) accSubst"
      using finalSubst_eq by (simp add: compose_subst_assoc)
    hence extends_acc: "\<exists>theta'. finalSubst = compose_subst theta' accSubst" by blast

    \<comment> \<open>Use compose_subst_correct: apply_subst finalSubst t = apply_subst theta (apply_subst composedSubst t)\<close>
    have "apply_subst finalSubst actualTy = apply_subst theta (apply_subst ?composedSubst actualTy)"
      using finalSubst_eq by (simp add: compose_subst_correct)
    also have "... = apply_subst theta (apply_subst ?composedSubst expectedTy)"
      using head_eq by simp
    also have "... = apply_subst finalSubst expectedTy"
      using finalSubst_eq by (simp add: compose_subst_correct)
    finally have head_unified: "apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy" .

    show ?thesis using ih extends_acc head_unified by auto
  next
    case None
    from "2.prems"(1) None have
      is_int: "is_finite_integer_type ?actualTy' \<and> is_finite_integer_type ?expectedTy'"
      and recurse: "unify_type_lists is_flex mk_err (idx + 1) actualTys expectedTys accSubst = Inr finalSubst"
      by (simp_all add: Let_def split: if_splits)

    have ih: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
            \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type env ty))
            \<and> (\<exists>theta. finalSubst = compose_subst theta accSubst)
            \<and> list_all2 (\<lambda>actualTy expectedTy.
                apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
                \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                   \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
              actualTys expectedTys
            \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> is_flex n)"
      using "2.IH"(1) None is_int len_tl recurse "2.prems"(2) actualTys_wk expectedTys_wk
                       "2.prems"(6) actualTys_rt expectedTys_rt "2.prems"(9) "2.prems"(10)
      by simp

    \<comment> \<open>From IH, finalSubst = compose_subst theta accSubst for some theta\<close>
    from ih obtain theta where finalSubst_eq: "finalSubst = compose_subst theta accSubst"
      by blast

    \<comment> \<open>Finite integer types have no type variables, so applying any substitution is identity\<close>
    have actualTy'_no_tyvars: "type_tyvars ?actualTy' = {}"
      using is_int finite_integer_type_is_integer_type integer_type_no_tyvars by blast
    have expectedTy'_no_tyvars: "type_tyvars ?expectedTy' = {}"
      using is_int finite_integer_type_is_integer_type integer_type_no_tyvars by blast

    \<comment> \<open>apply_subst finalSubst actualTy = apply_subst theta (apply_subst accSubst actualTy)
       = apply_subst theta ?actualTy'. Since ?actualTy' has no type variables, this equals ?actualTy'.\<close>
    have "apply_subst finalSubst actualTy = apply_subst theta ?actualTy'"
      using finalSubst_eq by (simp add: compose_subst_correct)
    also have "... = ?actualTy'"
      using actualTy'_no_tyvars apply_subst_disjoint_id by simp
    finally have actual_eq: "apply_subst finalSubst actualTy = ?actualTy'" .
    hence actual_finite: "is_finite_integer_type (apply_subst finalSubst actualTy)"
      using is_int by simp

    have "apply_subst finalSubst expectedTy = apply_subst theta ?expectedTy'"
      using finalSubst_eq by (simp add: compose_subst_correct)
    also have "... = ?expectedTy'"
      using expectedTy'_no_tyvars apply_subst_disjoint_id by simp
    finally have expected_eq: "apply_subst finalSubst expectedTy = ?expectedTy'" .
    hence expected_finite: "is_finite_integer_type (apply_subst finalSubst expectedTy)"
      using is_int by simp

    show ?thesis using ih actual_finite expected_finite by simp
  qed
next
  case ("3_1" uu uv uw v va uz)
  then show ?case by simp
next
  case ("3_2" uu uv uw v va uz)
  then show ?case by simp
qed

(* Correctness of apply_call_coercions (Phase 2):
   If input terms have the actual types, and the type unification property holds
   (types equal after substitution or both finite integers), then output terms
   have the expected types after substitution. *)
lemma apply_call_coercions_correct:
  assumes "list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) tms actualTys"
      and "list_all2 (\<lambda>actualTy expectedTy.
             apply_subst subst actualTy = apply_subst subst expectedTy
             \<or> (is_finite_integer_type (apply_subst subst actualTy)
                \<and> is_finite_integer_type (apply_subst subst expectedTy)))
           actualTys expectedTys"
      and "tyenv_well_formed env"
      and "\<forall>ty \<in> fmran' subst. is_well_kinded env ty"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' subst. is_runtime_type env ty)"
      and "length tms = length actualTys"
      and "length actualTys = length expectedTys"
      and locals_unaffected:
        "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty'
                      \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType env) = TE_ReturnType env"
  shows "list_all2 (\<lambda>tm expectedTy.
           core_term_type env ghost tm = Some (apply_subst subst expectedTy))
         (apply_call_coercions subst tms actualTys expectedTys) expectedTys"
  using assms
proof (induction subst tms actualTys expectedTys rule: apply_call_coercions.induct)
  case (1 subst)
  then show ?case by simp
next
  case (2 subst tm tms actualTy actualTys expectedTy expectedTys)
  let ?tm' = "apply_subst_to_term subst tm"
  let ?actualTy' = "apply_subst subst actualTy"
  let ?expectedTy' = "apply_subst subst expectedTy"

  from "2.prems"(1) have
    head_typed: "core_term_type env ghost tm = Some actualTy" and
    tail_typed: "list_all2 (\<lambda>tm ty. core_term_type env ghost tm = Some ty) tms actualTys"
    by simp_all
  from "2.prems"(2) have
    head_prop: "?actualTy' = ?expectedTy' \<or> (is_finite_integer_type ?actualTy' \<and> is_finite_integer_type ?expectedTy')" and
    tail_prop: "list_all2 (\<lambda>actualTy expectedTy.
                  apply_subst subst actualTy = apply_subst subst expectedTy
                  \<or> (is_finite_integer_type (apply_subst subst actualTy)
                     \<and> is_finite_integer_type (apply_subst subst expectedTy)))
                actualTys expectedTys"
    by simp_all
  from "2.prems"(6,7) have
    len_tms: "length tms = length actualTys" and
    len_tys: "length actualTys = length expectedTys"
    by simp_all

  \<comment> \<open>IH for tail\<close>
  have ih: "list_all2 (\<lambda>tm expectedTy.
              core_term_type env ghost tm = Some (apply_subst subst expectedTy))
            (apply_call_coercions subst tms actualTys expectedTys) expectedTys"
    using "2.IH" tail_typed tail_prop "2.prems"(3,4,5,8,9) len_tms len_tys
          locals_unaffected ret_unaffected
    by simp

  \<comment> \<open>For the head: apply_subst_to_term preserves typing (with substituted type)\<close>
  have head_tm'_typed: "core_term_type env ghost ?tm' = Some ?actualTy'"
    by (simp add: "2.prems"(4,5,8,9) apply_subst_to_term_preserves_typing assms(3)
        head_typed)

  \<comment> \<open>Show the head element has the expected type\<close>
  have head_result: "core_term_type env ghost
                       (if ?actualTy' = ?expectedTy' then ?tm' else CoreTm_Cast ?expectedTy' ?tm')
                     = Some ?expectedTy'"
  proof (cases "?actualTy' = ?expectedTy'")
    case True
    then show ?thesis using head_tm'_typed by simp
  next
    case False
    \<comment> \<open>Types differ, so both must be finite integer types\<close>
    from head_prop False have
      actual_finite: "is_finite_integer_type ?actualTy'" and
      expected_finite: "is_finite_integer_type ?expectedTy'"
      by simp_all
    \<comment> \<open>Cast typechecks: operand has integer type, target has integer type, both runtime if NotGhost\<close>
    have actual_int: "is_integer_type ?actualTy'"
      using actual_finite finite_integer_type_is_integer_type by blast
    have expected_int: "is_integer_type ?expectedTy'"
      using expected_finite finite_integer_type_is_integer_type by blast
    have expected_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env ?expectedTy'"
      using expected_finite by (cases ?expectedTy') auto
    show ?thesis using head_tm'_typed actual_int expected_int expected_rt False
      by (auto split: option.splits)
  qed

  show ?case using head_result ih by (simp add: Let_def)
next
  case ("3_1" subst v va vb)
  then show ?case by simp
next
  case ("3_2" subst v va vb)
  then show ?case by simp
next
  case ("3_3" subst v va vb)
  then show ?case by simp
next
  case ("3_4" subst v va vb)
  then show ?case by simp
next
  case ("3_5" subst v va)
  then show ?case by simp
next
  case ("3_6" subst v va)
  then show ?case by simp
qed

(* Correctness of coerce_to_common_int_type:
   If coercion succeeds, both output terms have the common type. *)
lemma coerce_to_common_int_type_correct:
  assumes "coerce_to_common_int_type tm1 ty1 tm2 ty2 = Some (newTm1, newTm2, commonTy)"
      and "core_term_type env ghost tm1 = Some ty1"
      and "core_term_type env ghost tm2 = Some ty2"
      and "tyenv_well_formed env"
  shows "core_term_type env ghost newTm1 = Some commonTy
       \<and> core_term_type env ghost newTm2 = Some commonTy"
proof (cases ty1)
  case (CoreTy_FiniteInt sign1 bits1)
  then show ?thesis
  proof (cases ty2)
    case (CoreTy_FiniteInt sign2 bits2)
    from assms(1) CoreTy_FiniteInt \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close>
    obtain commonSign commonBits where
      combine: "combine_int_types sign1 bits1 sign2 bits2 = Some (commonSign, commonBits)"
      and commonTy_eq: "commonTy = CoreTy_FiniteInt commonSign commonBits"
      and newTm1_eq: "newTm1 = (if sign1 = commonSign \<and> bits1 = commonBits then tm1
                                else CoreTm_Cast (CoreTy_FiniteInt commonSign commonBits) tm1)"
      and newTm2_eq: "newTm2 = (if sign2 = commonSign \<and> bits2 = commonBits then tm2
                                else CoreTm_Cast (CoreTy_FiniteInt commonSign commonBits) tm2)"
      by (auto simp: Let_def split: option.splits)

    have ty1_int: "is_integer_type ty1" using \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> by simp
    have ty2_int: "is_integer_type ty2" using CoreTy_FiniteInt by simp
    have commonTy_int: "is_integer_type commonTy" using commonTy_eq by simp
    have commonTy_rt: "is_runtime_type env commonTy" using commonTy_eq by simp

    have newTm1_typed: "core_term_type env ghost newTm1 = Some commonTy"
    proof (cases "sign1 = commonSign \<and> bits1 = commonBits")
      case True
      hence "newTm1 = tm1" and "ty1 = commonTy"
        using newTm1_eq \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> commonTy_eq by auto
      thus ?thesis using assms(2) by simp
    next
      case False
      hence "newTm1 = CoreTm_Cast commonTy tm1" using newTm1_eq commonTy_eq by simp
      thus ?thesis using assms(2) ty1_int commonTy_int commonTy_rt by auto
    qed

    have newTm2_typed: "core_term_type env ghost newTm2 = Some commonTy"
    proof (cases "sign2 = commonSign \<and> bits2 = commonBits")
      case True
      hence "newTm2 = tm2" and "ty2 = commonTy"
        using newTm2_eq CoreTy_FiniteInt commonTy_eq by auto
      thus ?thesis using assms(3) by simp
    next
      case False
      hence "newTm2 = CoreTm_Cast commonTy tm2" using newTm2_eq commonTy_eq by simp
      thus ?thesis using assms(3) ty2_int commonTy_int commonTy_rt by auto
    qed

    show ?thesis using newTm1_typed newTm2_typed by simp
  next
    case other: (CoreTy_Bool)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: CoreTy_MathInt
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: CoreTy_MathReal
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: (CoreTy_Datatype x1 x2)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: (CoreTy_Record x)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: (CoreTy_Array x1 x2)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  next
    case other: (CoreTy_Var x)
    with assms(1) \<open>ty1 = CoreTy_FiniteInt sign1 bits1\<close> show ?thesis by simp
  qed
next
  case other: CoreTy_Bool
  with assms(1) show ?thesis by simp
next
  case other: CoreTy_MathInt
  with assms(1) show ?thesis by simp
next
  case other: CoreTy_MathReal
  with assms(1) show ?thesis by simp
next
  case other: (CoreTy_Datatype x1 x2)
  with assms(1) show ?thesis by simp
next
  case other: (CoreTy_Record x)
  with assms(1) show ?thesis by simp
next
  case other: (CoreTy_Array x1 x2)
  with assms(1) show ?thesis by simp
next
  case other: (CoreTy_Var x)
  with assms(1) show ?thesis by simp
qed


end

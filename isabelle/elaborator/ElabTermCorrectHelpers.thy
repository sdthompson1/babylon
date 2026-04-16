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
  "elab_term env typedefs ghost tm next_mv = Inr (tm', ty', next_mv') \<Longrightarrow> next_mv \<le> next_mv'"
and elab_term_list_next_mv_monotone:
  "elab_term_list env typedefs ghost tms next_mv = Inr (tms', tys', next_mv') \<Longrightarrow> next_mv \<le> next_mv'"
proof (induction env typedefs ghost tm next_mv and env typedefs ghost tms next_mv
       arbitrary: tm' ty' next_mv' and tms' tys' next_mv'
       rule: elab_term_elab_term_list.induct)
  case (1 env typedefs ghost loc lit next_mv)
  \<comment> \<open>Literal: Bool/Int leave next_mv unchanged; String/Array are undefined (TODO)\<close>
  show ?case
  proof (cases lit)
    case (BabLit_Bool b)
    with "1.prems" show ?thesis by auto
  next
    case (BabLit_Int i)
    with "1.prems" show ?thesis by (auto split: option.splits)
  next
    case (BabLit_String s)
    with "1.prems" show ?thesis sorry
  next
    case (BabLit_Array xs)
    with "1.prems" show ?thesis sorry
  qed
next
  case (2 env typedefs ghost loc name tyArgs next_mv)
  \<comment> \<open>BabTm_Name: undefined (TODO)\<close>
  from "2.prems" show ?case sorry
next
  case (3 env typedefs ghost loc targetTy operand next_mv)
  from "3.prems" show ?case
    by (auto simp: Let_def split: sum.splits if_splits option.splits dest!: "3.IH")
next
  case (4 env typedefs ghost loc condTm thenTm elseTm next_mv)
  \<comment> \<open>BabTm_If: threads through cond, then, else\<close>
  from "4.prems" obtain newCond condTy next_mv1 where
    elab_cond: "elab_term env typedefs ghost condTm next_mv = Inr (newCond, condTy, next_mv1)"
    by (auto split: sum.splits)
  from "4.prems" elab_cond obtain newThen thenTy next_mv2 where
    elab_then: "elab_term env typedefs ghost thenTm next_mv1 = Inr (newThen, thenTy, next_mv2)"
    by (auto split: sum.splits)
  from "4.prems" elab_cond elab_then obtain newElse elseTy next_mv3 where
    elab_else: "elab_term env typedefs ghost elseTm next_mv2 = Inr (newElse, elseTy, next_mv3)"
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
  case (5 env typedefs ghost loc op operand next_mv)
  \<comment> \<open>BabTm_Unop: forwards operand's next_mv\<close>
  from "5.prems" show ?case
    by (auto simp: Let_def split: sum.splits option.splits BabUnop.splits if_splits dest!: "5.IH")
next
  case (6 env typedefs ghost loc lhs operands next_mv)
  \<comment> \<open>BabTm_Binop: threads through lhs, rhs list\<close>
  from "6.prems" obtain newLhs lhsTy next_mv1 where
    elab_lhs: "elab_term env typedefs ghost lhs next_mv = Inr (newLhs, lhsTy, next_mv1)"
    by (auto split: sum.splits)
  from "6.prems" elab_lhs obtain rhsTms rhsTys next_mv2 where
    elab_rhs: "elab_term_list env typedefs ghost (map snd operands) next_mv1 = Inr (rhsTms, rhsTys, next_mv2)"
    by (auto split: sum.splits)
  have m1: "next_mv \<le> next_mv1"
    using "6.IH"(1) elab_lhs by simp
  have m2: "next_mv1 \<le> next_mv2"
    using "6.IH"(2) elab_lhs elab_rhs by simp
  from "6.prems" elab_lhs elab_rhs have "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)
  with m1 m2 show ?case by simp
next
  case (7 env typedefs ghost loc varName rhs body next_mv)
  \<comment> \<open>BabTm_Let: threads through rhs and body\<close>
  from "7.prems" obtain rhsTm rhsTy next_mv1 where
    elab_rhs: "elab_term env typedefs ghost rhs next_mv = Inr (rhsTm, rhsTy, next_mv1)"
    by (auto split: sum.splits)
  from "7.prems" elab_rhs have rhs_resolved:
    "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)"
    by (auto split: if_splits)
  let ?env_body = "env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                          TE_GhostLocals := (if ghost = Ghost then finsert varName (TE_GhostLocals env)
                                               else fminus (TE_GhostLocals env) {|varName|}),
                          TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>"
  from "7.prems" elab_rhs rhs_resolved obtain bodyTm bodyTy next_mv2 where
    elab_body: "elab_term ?env_body typedefs ghost body next_mv1 = Inr (bodyTm, bodyTy, next_mv2)"
    by (auto simp: Let_def split: sum.splits)
  have m1: "next_mv \<le> next_mv1"
    using "7.IH"(1) elab_rhs by simp
  have m2: "next_mv1 \<le> next_mv2"
    using "7.IH"(2) elab_rhs rhs_resolved elab_body by (simp add: Let_def)
  from "7.prems" elab_rhs rhs_resolved elab_body have "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)
  with m1 m2 show ?case by simp
next
  case (8 env typedefs ghost loc quant name varTy tm next_mv)
  \<comment> \<open>BabTm_Quantifier: forwards body's next_mv\<close>
  from "8.prems" show ?case
    using "8.IH" by (auto simp: Let_def split: sum.splits if_splits option.splits)
next
  case (9 env typedefs ghost loc callee args next_mv)
  \<comment> \<open>BabTm_Call: threads through determine_fun_call_type, elab_term_list\<close>
  from "9.prems" obtain fnName tyArgs expArgTypes retType next_mv1 where
    det_call: "determine_fun_call_type env typedefs ghost callee next_mv
               = Inr (fnName, tyArgs, expArgTypes, retType, next_mv1)"
    by (auto split: sum.splits)
  \<comment> \<open>determine_fun_call_type is monotone: either generates fresh metas (next_mv1 = next_mv + n)
     or keeps next_mv unchanged.\<close>
  have det_mono: "next_mv \<le> next_mv1"
  proof (cases callee)
    case (BabTm_Name fnLoc fnName' tyArgs')
    from det_call BabTm_Name show ?thesis
      by (auto simp: Let_def split: option.splits if_splits sum.splits)
  qed (use det_call in simp_all)
  from "9.prems" det_call have len_args: "length args = length expArgTypes"
    by (auto split: if_splits)
  from "9.prems" det_call len_args obtain elabArgTms actualTypes next_mv2 where
    elab_args: "elab_term_list env typedefs ghost args next_mv1 = Inr (elabArgTms, actualTypes, next_mv2)"
    by (auto split: sum.splits)
  have m2: "next_mv1 \<le> next_mv2"
    using "9.IH" det_call len_args elab_args by simp
  from "9.prems" det_call len_args elab_args have "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)
  with det_mono m2 show ?case by simp
next
  case (10 env typedefs ghost loc tms next_mv)
  \<comment> \<open>BabTm_Tuple: forwards elab_term_list's next_mv\<close>
  from "10.prems" show ?case
    by (auto simp: Let_def split: sum.splits dest!: "10.IH")
next
  case (11 env typedefs ghost loc flds next_mv)
  \<comment> \<open>BabTm_Record: forwards elab_term_list's next_mv\<close>
  from "11.prems" show ?case
    by (auto simp: Let_def split: sum.splits option.splits dest!: "11.IH")
next
  case (12 env typedefs ghost loc tm flds next_mv)
  \<comment> \<open>BabTm_RecordUpdate: threads through parent and update list next_mv\<close>
  from "12.prems"(1) have no_dup: "first_duplicate_name fst flds = None"
    by (auto split: option.splits)
  from "12.prems"(1) no_dup obtain parentTm parentTy next_mv1 where
    elab_parent: "elab_term env typedefs ghost tm next_mv = Inr (parentTm, parentTy, next_mv1)"
    by (auto split: sum.splits option.splits)
  have mono1: "next_mv \<le> next_mv1"
    using "12.IH"(1)[OF no_dup] elab_parent by simp
  from "12.prems"(1) elab_parent obtain parentFields where
    parent_rec: "parentTy = CoreTy_Record parentFields"
    by (auto simp: Let_def unify_update_args_def build_updated_record_def
             split: sum.splits option.splits CoreType.splits if_splits prod.splits)
  from "12.prems"(1) no_dup elab_parent parent_rec have
    fields_exist: "check_update_fields_exist flds parentFields = None"
    by (auto simp: Let_def unify_update_args_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  from "12.prems"(1) no_dup elab_parent parent_rec fields_exist
  obtain newUpdateTms actualTypes next_mv2 where
    elab_updates: "elab_term_list env typedefs ghost (map snd flds) next_mv1
                   = Inr (newUpdateTms, actualTypes, next_mv2)"
    by (auto simp: Let_def unify_update_args_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  have pair1: "(parentTm, parentTy, next_mv1) = (parentTm, parentTy, next_mv1)" by simp
  have pair2: "(parentTy, next_mv1) = (parentTy, next_mv1)" by simp
  have mono2: "next_mv1 \<le> next_mv2"
    using "12.IH"(2)[OF no_dup elab_parent pair1 pair2 parent_rec fields_exist]
          elab_updates by simp
  from "12.prems"(1) elab_parent parent_rec elab_updates have "next_mv' = next_mv2"
    by (auto simp: Let_def unify_update_args_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  with mono1 mono2 show ?case by simp
next
  case (13 env typedefs ghost loc tm idx next_mv)
  \<comment> \<open>BabTm_TupleProj: forwards sub-term's next_mv\<close>
  from "13.prems" show ?case
    by (auto simp del: nat_to_string.simps split: sum.splits CoreType.splits option.splits dest!: "13.IH")
next
  case (14 env typedefs ghost loc tm fldName next_mv)
  \<comment> \<open>BabTm_RecordProj: forwards sub-term's next_mv\<close>
  from "14.prems" show ?case
    by (auto split: sum.splits CoreType.splits option.splits dest!: "14.IH")
next
  case "15"  \<comment> \<open>BabTm_ArrayProj: undefined\<close>
  from "15.prems" show ?case sorry
next
  case "16"  \<comment> \<open>BabTm_Match: undefined\<close>
  from "16.prems" show ?case sorry
next
  case (17 env typedefs ghost loc tm next_mv)
  \<comment> \<open>BabTm_Sizeof: forwards sub-term's next_mv\<close>
  from "17.prems" show ?case
    using "17.IH" by (auto split: sum.splits CoreType.splits if_splits)
next
  case (18 env typedefs ghost loc tm next_mv)
  \<comment> \<open>BabTm_Allocated: forwards sub-term's next_mv\<close>
  from "18.prems" show ?case
    using "18.IH" by (auto split: sum.splits if_splits)
next
  case (19 env typedefs ghost loc tm next_mv)
  \<comment> \<open>BabTm_Old: forwards sub-term's next_mv\<close>
  from "19.prems" show ?case
    using "19.IH" by (auto split: sum.splits if_splits)
next
  case "20" \<comment> \<open>elab_term_list: Nil\<close>
  from "20.prems" show ?case by simp
next
  case (21 env typedefs ghost tm tms next_mv)
  \<comment> \<open>elab_term_list: Cons\<close>
  from "21.prems" obtain tm'' ty'' next_mv1 tms'' tys'' next_mv2 where
    elab_head: "elab_term env typedefs ghost tm next_mv = Inr (tm'', ty'', next_mv1)" and
    elab_tail: "elab_term_list env typedefs ghost tms next_mv1 = Inr (tms'', tys'', next_mv2)"
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
  "elab_term_list env typedefs ghost tms next_mv = Inr (tms', tys', next_mv')
   \<Longrightarrow> length tms' = length tms \<and> length tys' = length tms"
proof (induction tms arbitrary: tms' tys' next_mv next_mv')
  case Nil
  then show ?case by simp
next
  case (Cons tm tms)
  then show ?case by (auto split: sum.splits)
qed

(* Correctness of determine_fun_call_type:
   If it succeeds, the returned information is consistent with the function declaration.
   The returned type arguments are well-kinded in the extended env (since the
   meta-generation branch adds fresh metas in [next_mv..<next_mv']). *)
lemma determine_fun_call_type_correct:
  assumes "determine_fun_call_type env typedefs ghost callTm next_mv
           = Inr (fnName, newTyArgs, expArgTypes, retType, next_mv')"
      and "tyenv_well_formed env"
      and "typedefs_well_formed env typedefs"
  shows "next_mv \<le> next_mv'
       \<and> (\<exists>funInfo.
           fmlookup (TE_Functions env) fnName = Some funInfo
         \<and> (ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost)
         \<and> \<not> FI_Impure funInfo
         \<and> list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)
         \<and> length newTyArgs = length (FI_TyArgs funInfo)
         \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs
         \<and> (ghost = NotGhost \<longrightarrow>
              list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv')) newTyArgs)
         \<and> expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs)) ty)
                             (FI_TmArgs funInfo)
         \<and> retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) newTyArgs))
                                  (FI_ReturnType funInfo))"
proof (cases callTm)
  case (BabTm_Name fnLoc fnName' tyArgs)
  from assms(1) BabTm_Name obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName' = Some funInfo"
    by (auto split: option.splits if_splits)
  from assms(1) BabTm_Name fn_lookup have
    not_impure: "\<not> FI_Impure funInfo"
    by (auto split: if_splits sum.splits)
  from assms(1) BabTm_Name fn_lookup not_impure have
    all_var: "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)"
    by (auto split: if_splits sum.splits)
  from assms(1) BabTm_Name fn_lookup not_impure all_var have
    ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    by (auto split: if_splits sum.splits)
  from assms(1) BabTm_Name fn_lookup not_impure all_var ghost_ok have
    fnName_eq: "fnName = fnName'"
    by (auto simp: Let_def split: if_splits sum.splits)

  let ?numTyParams = "length (FI_TyArgs funInfo)"

  show ?thesis
  proof (cases "tyArgs = [] \<and> ?numTyParams > 0")
    case True
    \<comment> \<open>Type args were omitted - metavariables generated\<close>
    let ?genTyArgs = "map CoreTy_Var [next_mv..<next_mv + ?numTyParams]"
    from assms(1) BabTm_Name fn_lookup not_impure all_var ghost_ok True
    have results: "newTyArgs = ?genTyArgs"
                  "next_mv' = next_mv + ?numTyParams"
                  "expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) ?genTyArgs)) ty)
                                     (FI_TmArgs funInfo)"
                  "retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) ?genTyArgs))
                                         (FI_ReturnType funInfo)"
      by (auto simp: Let_def)
    have len_ok: "length ?genTyArgs = ?numTyParams" by simp
    have mono: "next_mv \<le> next_mv'" using results by simp
    let ?env_ext = "extend_env_with_tyvars env ghost next_mv next_mv'"
    \<comment> \<open>The fresh metas are all in TE_TypeVars of the extended env\<close>
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
      using fn_lookup ghost_ok not_impure all_var fnName_eq results len_ok wk_ok runtime_ok mono
      by auto
  next
    case False
    show ?thesis
    proof (cases "?numTyParams = length tyArgs")
      case True
      from assms(1) BabTm_Name fn_lookup not_impure all_var ghost_ok False True
      obtain elabTyArgs where
        elab_tyargs: "elab_type_list env typedefs ghost tyArgs = Inr elabTyArgs"
        by (cases "elab_type_list env typedefs ghost tyArgs")
           (auto simp: Let_def split: if_splits)
      from assms(1) BabTm_Name fn_lookup not_impure all_var ghost_ok False True elab_tyargs
      have results: "newTyArgs = elabTyArgs"
                    "next_mv' = next_mv"
                    "expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) elabTyArgs)) ty)
                                       (FI_TmArgs funInfo)"
                    "retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) elabTyArgs))
                                           (FI_ReturnType funInfo)"
        by (auto simp: Let_def)
      have len_ok: "length elabTyArgs = ?numTyParams"
        using elab_tyargs True elab_type_list_length by fastforce
      have mono: "next_mv \<le> next_mv'" using results by simp
      \<comment> \<open>Interval is empty so the extended env equals env\<close>
      have env_eq: "extend_env_with_tyvars env ghost next_mv next_mv' = env"
        using results by simp
      have wk_ok: "list_all (is_well_kinded env) elabTyArgs"
        using elab_tyargs assms(2,3) elab_type_is_well_kinded(2) by auto
      have runtime_ok: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type env) elabTyArgs"
        using elab_tyargs assms(2,3) elab_type_notghost_is_runtime(2) by (cases ghost; auto)
      show ?thesis
        using fn_lookup ghost_ok not_impure all_var fnName_eq results len_ok wk_ok runtime_ok mono env_eq
        by auto
    next
      case False2: False
      from assms(1) BabTm_Name fn_lookup not_impure all_var ghost_ok False False2
      have "False" by (auto simp: Let_def split: sum.splits if_splits)
      thus ?thesis ..
    qed
  qed
qed (use assms(1) in simp_all)


(* Correctness of unify_call_types (Phase 1):
   If it succeeds, the substitution is well-kinded and runtime-preserving,
   finalSubst extends accSubst (via composition with some theta),
   and for each pair of types, either they unify or both are finite integers. *)
lemma unify_call_types_correct:
  assumes "unify_call_types is_flex loc fnName argIdx actualTys expectedTys accSubst = Inr finalSubst"
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
proof (induction is_flex loc fnName argIdx actualTys expectedTys accSubst
       arbitrary: finalSubst
       rule: unify_call_types.induct)
  case (1 is_flex loc fnName argIdx accSubst)
  from "1.prems"(1) have finalSubst_eq: "finalSubst = accSubst" by simp
  moreover have "accSubst = compose_subst fmempty accSubst" by simp
  moreover from "1.prems"(10) finalSubst_eq have
    "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> is_flex n" by simp
  ultimately show ?case using "1.prems"(6,9) by blast
next
  case (2 is_flex loc fnName argIdx actualTy actualTys expectedTy expectedTys accSubst)
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
      recurse: "unify_call_types is_flex loc fnName (argIdx + 1) actualTys expectedTys ?composedSubst = Inr finalSubst"
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
      and recurse: "unify_call_types is_flex loc fnName (argIdx + 1) actualTys expectedTys accSubst = Inr finalSubst"
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
   If input terms have the actual types, and the unify_call_types property holds
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

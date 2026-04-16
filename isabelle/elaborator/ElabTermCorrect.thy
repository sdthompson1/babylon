theory ElabTermCorrect
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
    ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost"
    by (auto split: if_splits sum.splits)
  from assms(1) BabTm_Name fn_lookup ghost_ok have
    fnName_eq: "fnName = fnName'"
    by (auto simp: Let_def split: if_splits sum.splits)

  let ?numTyParams = "length (FI_TyArgs funInfo)"

  show ?thesis
  proof (cases "tyArgs = [] \<and> ?numTyParams > 0")
    case True
    \<comment> \<open>Type args were omitted - metavariables generated\<close>
    let ?genTyArgs = "map CoreTy_Var [next_mv..<next_mv + ?numTyParams]"
    from assms(1) BabTm_Name fn_lookup ghost_ok True
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
      using fn_lookup ghost_ok fnName_eq results len_ok wk_ok runtime_ok mono
      by auto
  next
    case False
    show ?thesis
    proof (cases "?numTyParams = length tyArgs")
      case True
      from assms(1) BabTm_Name fn_lookup ghost_ok False True
      obtain elabTyArgs where
        elab_tyargs: "elab_type_list env typedefs ghost tyArgs = Inr elabTyArgs"
        by (cases "elab_type_list env typedefs ghost tyArgs")
           (auto simp: Let_def split: if_splits)
      from assms(1) BabTm_Name fn_lookup ghost_ok False True elab_tyargs
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
        using fn_lookup ghost_ok fnName_eq results len_ok wk_ok runtime_ok mono env_eq
        by auto
    next
      case False2: False
      from assms(1) BabTm_Name fn_lookup ghost_ok False False2
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


(* ========================================================================== *)
(* Correctness of binary operator helpers *)
(* ========================================================================== *)

(* Correctness of check_and_coerce_binop: if the helper succeeds, the result is a
   CoreTm_Binop where both operands typecheck to a common type satisfying type_pred,
   and the common type is FiniteInt (when coercion was needed) or equal to the input types.
   The assumption that type_pred holds for all FiniteInt types is needed because
   coercion produces FiniteInt output. *)
lemma check_and_coerce_binop_correct:
  assumes "check_and_coerce_binop type_pred resultTyOverride errMsg cop
             lhsTm lhsTy rhsTm rhsTy loc babOp = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "core_term_type env ghost rhsTm = Some rhsTy"
    and "tyenv_well_formed env"
    and "\<And>s b. type_pred (CoreTy_FiniteInt s b)"
  shows "\<exists>opL opR commonTy.
    resultTm = CoreTm_Binop cop opL opR
    \<and> core_term_type env ghost opL = Some commonTy
    \<and> core_term_type env ghost opR = Some commonTy
    \<and> type_pred commonTy
    \<and> resultTy = (case resultTyOverride of None \<Rightarrow> commonTy | Some ty \<Rightarrow> ty)"
proof (cases "lhsTy = rhsTy")
  case True
  from assms(1) True have pred: "type_pred lhsTy"
    by (auto simp: check_and_coerce_binop_def Let_def split: if_splits)
  from assms(1) True pred have
    tm_eq: "resultTm = CoreTm_Binop cop lhsTm rhsTm" and
    ty_eq: "resultTy = (case resultTyOverride of None \<Rightarrow> lhsTy | Some ty \<Rightarrow> ty)"
    by (auto simp: check_and_coerce_binop_def Let_def)
  from pred tm_eq ty_eq assms(2,3) True show ?thesis
    by (intro exI[of _ lhsTm] exI[of _ rhsTm] exI[of _ lhsTy]) auto
next
  case False
  from assms(1) False have preds: "type_pred lhsTy" "type_pred rhsTy"
    by (auto simp: check_and_coerce_binop_def Let_def split: if_splits)
  from assms(1) False preds obtain newLhs newRhs commonTy where
    coerce: "coerce_to_common_int_type lhsTm lhsTy rhsTm rhsTy = Some (newLhs, newRhs, commonTy)" and
    tm_eq: "resultTm = CoreTm_Binop cop newLhs newRhs" and
    ty_eq: "resultTy = (case resultTyOverride of None \<Rightarrow> commonTy | Some ty \<Rightarrow> ty)"
    by (auto simp: check_and_coerce_binop_def Let_def split: option.splits)
  from coerce_to_common_int_type_correct[OF coerce assms(2,3,4)]
  have typed: "core_term_type env ghost newLhs = Some commonTy"
              "core_term_type env ghost newRhs = Some commonTy" by auto
  from coerce obtain s b where "commonTy = CoreTy_FiniteInt s b"
    by (cases lhsTy; cases rhsTy) (auto split: option.splits simp: Let_def)
  hence "type_pred commonTy" using assms(5) by simp
  with typed tm_eq ty_eq show ?thesis
    by (intro exI[of _ newLhs] exI[of _ newRhs] exI[of _ commonTy]) auto
qed

(* Helper: extract components from a successful build_comparison_chain in the let-binding case *)
lemma build_comparison_chain_let_elim:
  assumes "(case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy varTm rhsTy of
              Inl errs \<Rightarrow> Inl errs
            | Inr (cmpTm, _) \<Rightarrow>
                (case build_comparison_chain is_flex loc ghost ctr' varTm rhsTy rest of
                  Inl errs \<Rightarrow> Inl errs
                | Inr restTm \<Rightarrow>
                    Inr (CoreTm_Let varName rhs
                          (CoreTm_Binop CoreBinop_And cmpTm restTm)))) = Inr resultTm"
  obtains cmpTm cmpTy restTm where
    "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy varTm rhsTy = Inr (cmpTm, cmpTy)"
    "build_comparison_chain is_flex loc ghost ctr' varTm rhsTy rest = Inr restTm"
    "resultTm = CoreTm_Let varName rhs (CoreTm_Binop CoreBinop_And cmpTm restTm)"
  using assms by (auto split: sum.splits prod.splits)

(* Helper: range of fmap_of_list where all values are the same *)
lemma fmran'_fmap_of_list_const:
  "\<forall>ty' \<in> fmran' (fmap_of_list (map (\<lambda>n. (n, v)) ns)). ty' = v"
proof (induct ns)
  case Nil thus ?case by (simp add: fmran'_def fmlookup_of_list)
next
  case (Cons n ns)
  thus ?case by (auto simp: fmran'_def fmlookup_of_list)
qed

(* The range of const_subst_for contains only the default type *)
lemma const_subst_for_range:
  "\<forall>ty' \<in> fmran' (const_subst_for is_flex ty defaultTy). ty' = defaultTy"
  unfolding const_subst_for_def by (rule fmran'_fmap_of_list_const)

(* Helper: lookup in a constant-valued fmap_of_list *)
lemma fmlookup_fmap_of_list_const:
  "n \<in> set ns \<Longrightarrow> fmlookup (fmap_of_list (map (\<lambda>n. (n, v)) ns)) n = Some v"
  by (induct ns) (auto simp: fmlookup_of_list)

(* const_subst_for maps every flexible metavariable in the type *)
lemma const_subst_for_domain:
  "n \<in> type_tyvars ty \<Longrightarrow> is_flex n \<Longrightarrow>
   fmlookup (const_subst_for is_flex ty defaultTy) n = Some defaultTy"
  unfolding const_subst_for_def
  using fmlookup_fmap_of_list_const[of n "filter is_flex (type_tyvars_list ty)" defaultTy]
  by (simp add: set_type_tyvars_list)

(* Correctness of resolve_binop_metas: if the input terms typecheck at their types,
   the resolved terms typecheck at the resolved types. *)
lemma resolve_binop_metas_correct:
  assumes resolved: "resolve_binop_metas is_flex babOp lhsTm lhsTy rhsTm rhsTy = (lhsTm', lhsTy', rhsTm', rhsTy')"
    and lhs_typed: "core_term_type env ghost lhsTm = Some lhsTy"
    and rhs_typed: "core_term_type env ghost rhsTm = Some rhsTy"
    and wf: "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost lhsTm' = Some lhsTy'
       \<and> core_term_type env ghost rhsTm' = Some rhsTy'"
proof (cases "unify is_flex lhsTy rhsTy")
  case None
  \<comment> \<open>Unification failed: pass through unchanged\<close>
  from resolved None have "lhsTm' = lhsTm" "lhsTy' = lhsTy" "rhsTm' = rhsTm" "rhsTy' = rhsTy"
    by simp_all
  thus ?thesis using lhs_typed rhs_typed by simp
next
  case (Some unifSubst)
  let ?unifiedTy = "apply_subst unifSubst lhsTy"
  have sound: "apply_subst unifSubst lhsTy = apply_subst unifSubst rhsTy"
    using unify_sound[OF Some] .

  \<comment> \<open>Substitution range is well-kinded and runtime\<close>
  have lhs_wk: "is_well_kinded env lhsTy"
    using core_term_type_well_kinded[OF lhs_typed wf] .
  have rhs_wk: "is_well_kinded env rhsTy"
    using core_term_type_well_kinded[OF rhs_typed wf] .
  have unif_range_wk: "\<forall>ty' \<in> fmran' unifSubst. is_well_kinded env ty'"
    using unify_preserves_well_kinded[OF Some lhs_wk rhs_wk] .
  have unif_range_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' unifSubst. is_runtime_type env ty')"
  proof
    assume ng: "ghost = NotGhost"
    have "is_runtime_type env lhsTy"
      using core_term_type_notghost_runtime lhs_typed wf ng by auto
    moreover have "is_runtime_type env rhsTy"
      using core_term_type_notghost_runtime wf ng rhs_typed by auto
    ultimately show "\<forall>ty' \<in> fmran' unifSubst. is_runtime_type env ty'"
      using unify_preserves_runtime[OF Some] by auto
  qed

  \<comment> \<open>Helper: applying unifSubst preserves well-kindedness / runtime (src = tgt = env)\<close>
  have unif_apply_wk: "\<And>t. is_well_kinded env t \<Longrightarrow> is_well_kinded env (apply_subst unifSubst t)"
  proof -
    fix t assume t_wk: "is_well_kinded env t"
    show "is_well_kinded env (apply_subst unifSubst t)"
    proof (rule apply_subst_preserves_well_kinded[OF t_wk])
      show "TE_Datatypes env = TE_Datatypes env" by simp
    next
      fix n assume n_in: "n |\<in>| TE_TypeVars env"
      show "case fmlookup unifSubst n of
              Some ty' \<Rightarrow> is_well_kinded env ty'
            | None \<Rightarrow> n |\<in>| TE_TypeVars env"
        using n_in unif_range_wk by (auto simp: fmran'I split: option.splits)
    qed
  qed
  have unif_apply_rt: "\<And>t. ghost = NotGhost \<Longrightarrow> is_runtime_type env t \<Longrightarrow>
                           is_runtime_type env (apply_subst unifSubst t)"
  proof -
    fix t assume ng: "ghost = NotGhost" and t_rt: "is_runtime_type env t"
    show "is_runtime_type env (apply_subst unifSubst t)"
    proof (rule apply_subst_preserves_runtime[OF t_rt])
      show "TE_GhostDatatypes env = TE_GhostDatatypes env" by simp
    next
      fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars env"
      show "case fmlookup unifSubst n of
              Some ty' \<Rightarrow> is_runtime_type env ty'
            | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
        using n_in unif_range_rt ng by (auto simp: fmran'I split: option.splits)
    qed
  qed

  \<comment> \<open>The unifier only binds flex metavars. Combined with the caller's
      rigidity assumptions on locals and the return type, the substitution
      leaves them unchanged. \<close>
  have unif_dom_flex: "\<forall>n. n |\<in>| fmdom unifSubst \<longrightarrow> is_flex n"
    using unify_unify_list_dom_flex(1)[OF Some] .

  have locals_unaffected:
    "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty' \<Longrightarrow> apply_subst unifSubst ty' = ty'"
  proof -
    fix name ty' assume lk: "fmlookup (TE_LocalVars env) name = Some ty'"
    have "type_tyvars ty' \<inter> fset (fmdom unifSubst) = {}"
    proof -
      { fix n assume n_mv: "n \<in> type_tyvars ty'" and n_dom: "n \<in> fset (fmdom unifSubst)"
        from n_dom have "n |\<in>| fmdom unifSubst" by simp
        with unif_dom_flex have "is_flex n" by blast
        moreover from locals_rigid lk n_mv have "\<not> is_flex n" by blast
        ultimately have False by simp
      }
      thus ?thesis by auto
    qed
    thus "apply_subst unifSubst ty' = ty'"
      by (rule apply_subst_disjoint_id)
  qed
  have ret_unaffected: "apply_subst unifSubst (TE_ReturnType env) = TE_ReturnType env"
  proof -
    have "type_tyvars (TE_ReturnType env) \<inter> fset (fmdom unifSubst) = {}"
    proof -
      { fix n assume n_mv: "n \<in> type_tyvars (TE_ReturnType env)"
                 and n_dom: "n \<in> fset (fmdom unifSubst)"
        from n_dom have "n |\<in>| fmdom unifSubst" by simp
        with unif_dom_flex have "is_flex n" by blast
        moreover from ret_rigid n_mv have "\<not> is_flex n" by blast
        ultimately have False by simp
      }
      thus ?thesis by auto
    qed
    thus ?thesis by (rule apply_subst_disjoint_id)
  qed

  \<comment> \<open>Both terms typecheck after applying unifSubst\<close>
  have lhs_unif: "core_term_type env ghost (apply_subst_to_term unifSubst lhsTm) = Some ?unifiedTy"
    using apply_subst_to_term_preserves_typing
            [OF lhs_typed wf unif_range_wk unif_range_rt locals_unaffected ret_unaffected]
    by simp
  have rhs_unif: "core_term_type env ghost (apply_subst_to_term unifSubst rhsTm) = Some ?unifiedTy"
    using apply_subst_to_term_preserves_typing
            [OF rhs_typed wf unif_range_wk unif_range_rt locals_unaffected ret_unaffected]
          sound
    by simp

  show ?thesis
  proof (cases "list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list ?unifiedTy)")
    case True
    \<comment> \<open>Resolved: directly use unified type\<close>
    from resolved Some True have
      eqs: "lhsTm' = apply_subst_to_term unifSubst lhsTm"
           "lhsTy' = ?unifiedTy"
           "rhsTm' = apply_subst_to_term unifSubst rhsTm"
           "rhsTy' = ?unifiedTy"
      by (auto simp: Let_def)
    show ?thesis using lhs_unif rhs_unif eqs by simp
  next
    case not_resolved: False
    \<comment> \<open>Not resolved: fill remaining flexible metas with default type\<close>
    let ?defaultTy = "default_type_for_binop babOp"
    let ?fillSubst = "const_subst_for is_flex ?unifiedTy ?defaultTy"
    let ?fullSubst = "compose_subst ?fillSubst unifSubst"
    from resolved Some not_resolved have
      eqs: "lhsTm' = apply_subst_to_term ?fullSubst lhsTm"
           "lhsTy' = apply_subst ?fillSubst ?unifiedTy"
           "rhsTm' = apply_subst_to_term ?fullSubst rhsTm"
           "rhsTy' = apply_subst ?fillSubst ?unifiedTy"
      by (auto simp: Let_def)

    \<comment> \<open>The default type is well-kinded and runtime\<close>
    have default_wk: "is_well_kinded env ?defaultTy"
      by (auto simp: default_type_for_binop_def split: option.splits)
    have default_rt: "is_runtime_type env ?defaultTy"
      by (auto simp: default_type_for_binop_def split: option.splits)

    \<comment> \<open>The fill substitution range is well-kinded and runtime\<close>
    have fill_range_wk: "\<forall>ty' \<in> fmran' ?fillSubst. is_well_kinded env ty'"
      using const_subst_for_range[of is_flex ?unifiedTy ?defaultTy] default_wk by metis
    have fill_range_rt: "\<forall>ty' \<in> fmran' ?fillSubst. is_runtime_type env ty'"
      using const_subst_for_range[of is_flex ?unifiedTy ?defaultTy] default_rt by metis

    \<comment> \<open>Full substitution range is well-kinded and runtime\<close>
    have full_range_wk: "\<forall>ty' \<in> fmran' ?fullSubst. is_well_kinded env ty'"
      using compose_subst_preserves_well_kinded fill_range_wk unif_range_wk by blast
    have full_range_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' ?fullSubst. is_runtime_type env ty')"
    proof
      assume ng: "ghost = NotGhost"
      from unif_range_rt ng have "\<forall>ty' \<in> fmran' unifSubst. is_runtime_type env ty'" by simp
      from compose_subst_preserves_runtime[OF fill_range_rt this]
      show "\<forall>ty' \<in> fmran' ?fullSubst. is_runtime_type env ty'"
        using Some compose_subst_preserves_runtime core_term_type_well_kinded_and_runtime fill_range_rt
          lhs_typed local.wf ng rhs_typed unify_preserves_runtime by presburger
    qed

    \<comment> \<open>?fullSubst's domain is contained in flex metavars: it's the union of
        unifSubst's domain (from unify_dom_flex) and ?fillSubst's domain
        (filtered to flex by const_subst_for's definition). \<close>
    have fill_dom_flex: "\<forall>n. n |\<in>| fmdom ?fillSubst \<longrightarrow> is_flex n"
      unfolding const_subst_for_def
      by auto
    have full_dom_flex: "\<forall>n. n |\<in>| fmdom ?fullSubst \<longrightarrow> is_flex n"
      using unif_dom_flex fill_dom_flex
      by (auto simp: compose_subst_def)

    have locals_unaffected_full:
      "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty' \<Longrightarrow> apply_subst ?fullSubst ty' = ty'"
    proof -
      fix name ty' assume lk: "fmlookup (TE_LocalVars env) name = Some ty'"
      have "type_tyvars ty' \<inter> fset (fmdom ?fullSubst) = {}"
      proof -
        { fix n assume n_mv: "n \<in> type_tyvars ty'"
                    and n_dom: "n \<in> fset (fmdom ?fullSubst)"
          from n_dom have "n |\<in>| fmdom ?fullSubst" by simp
          with full_dom_flex have "is_flex n" by blast
          moreover from locals_rigid lk n_mv have "\<not> is_flex n" by blast
          ultimately have False by simp
        }
        thus ?thesis by auto
      qed
      thus "apply_subst ?fullSubst ty' = ty'"
        by (rule apply_subst_disjoint_id)
    qed
    have ret_unaffected_full: "apply_subst ?fullSubst (TE_ReturnType env) = TE_ReturnType env"
    proof -
      have "type_tyvars (TE_ReturnType env) \<inter> fset (fmdom ?fullSubst) = {}"
      proof -
        { fix n assume n_mv: "n \<in> type_tyvars (TE_ReturnType env)"
                    and n_dom: "n \<in> fset (fmdom ?fullSubst)"
          from n_dom have "n |\<in>| fmdom ?fullSubst" by simp
          with full_dom_flex have "is_flex n" by blast
          moreover from ret_rigid n_mv have "\<not> is_flex n" by blast
          ultimately have False by simp
        }
        thus ?thesis by auto
      qed
      thus ?thesis by (rule apply_subst_disjoint_id)
    qed

    \<comment> \<open>Applying fullSubst preserves typing\<close>
    have lhs_full: "core_term_type env ghost (apply_subst_to_term ?fullSubst lhsTm) =
                    Some (apply_subst ?fullSubst lhsTy)"
      using apply_subst_to_term_preserves_typing
              [OF lhs_typed wf full_range_wk full_range_rt
                  locals_unaffected_full ret_unaffected_full]
      by simp
    have rhs_full: "core_term_type env ghost (apply_subst_to_term ?fullSubst rhsTm) =
                    Some (apply_subst ?fullSubst rhsTy)"
      using apply_subst_to_term_preserves_typing
              [OF rhs_typed wf full_range_wk full_range_rt
                  locals_unaffected_full ret_unaffected_full]
      by simp

    \<comment> \<open>apply_subst ?fullSubst lhsTy = apply_subst ?fillSubst ?unifiedTy via compose_subst_correct\<close>
    have lhs_eq: "apply_subst ?fullSubst lhsTy = apply_subst ?fillSubst ?unifiedTy"
      by (simp add: compose_subst_correct)
    have rhs_eq: "apply_subst ?fullSubst rhsTy = apply_subst ?fillSubst ?unifiedTy"
      using sound by (simp add: compose_subst_correct)

    show ?thesis using lhs_full rhs_full lhs_eq rhs_eq eqs by simp
  qed
qed

(* Correctness of elab_single_binop: if elaboration succeeds, the result typechecks. *)
lemma elab_single_binop_correct:
  assumes "elab_single_binop is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "core_term_type env ghost rhsTm = Some rhsTy"
    and "tyenv_well_formed env"
    and "binop_to_core babOp = Some cop"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
proof -
  obtain lhsTm' lhsTy' rhsTm' rhsTy' where
    resolved: "resolve_binop_metas is_flex babOp lhsTm lhsTy rhsTm rhsTy = (lhsTm', lhsTy', rhsTm', rhsTy')"
    by (cases "resolve_binop_metas is_flex babOp lhsTm lhsTy rhsTm rhsTy") auto
  have lhs': "core_term_type env ghost lhsTm' = Some lhsTy'"
    and rhs': "core_term_type env ghost rhsTm' = Some rhsTy'"
    using resolve_binop_metas_correct[OF resolved assms(2,3,4) locals_rigid ret_rigid] by auto

  have cop: "binop_to_core babOp = Some cop" using assms(5) .

  \<comment> \<open>Case-split on the binop category using exhaustiveness\<close>
  consider (arith) "is_arithmetic_binop cop"
    | (modulo) "\<not> is_arithmetic_binop cop" "is_modulo_binop cop"
    | (bitwise) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "is_bitwise_binop cop"
    | (shift) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
              "is_shift_binop cop"
    | (ordering) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
                 "\<not> is_shift_binop cop" "is_ordering_binop cop"
    | (eq_neq) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
               "\<not> is_shift_binop cop" "\<not> is_ordering_binop cop" "is_eq_neq_binop cop"
    | (logical) "\<not> is_arithmetic_binop cop" "\<not> is_modulo_binop cop" "\<not> is_bitwise_binop cop"
                "\<not> is_shift_binop cop" "\<not> is_ordering_binop cop" "\<not> is_eq_neq_binop cop"
                "is_logical_binop cop"
    using binop_category_exhaustive[of cop] by blast
  then show ?thesis
  proof cases
    \<comment> \<open>Arithmetic: both numeric, same type or coerced to common type\<close>
    case arith
    from assms(1) resolved cop arith have
      "check_and_coerce_binop is_numeric_type None TyErr_BinopRequiresNumeric cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_numeric_type commonTy" and ty_eq: "resultTy = commonTy"
      by auto
    with arith show ?thesis by auto
  next
    \<comment> \<open>Modulo: both integer, same type or coerced\<close>
    case modulo
    from assms(1) resolved cop modulo have
      "check_and_coerce_binop is_integer_type None TyErr_BinopRequiresInteger cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_integer_type commonTy" and ty_eq: "resultTy = commonTy"
      by auto
    with modulo show ?thesis by auto
  next
    \<comment> \<open>Bitwise: both finite integer, same type or coerced\<close>
    case bitwise
    from assms(1) resolved cop bitwise have
      "check_and_coerce_binop is_finite_integer_type None TyErr_BinopRequiresFiniteInteger cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_finite_integer_type commonTy" and ty_eq: "resultTy = commonTy"
      by auto
    with bitwise show ?thesis by auto
  next
    \<comment> \<open>Shift: both finite integer, cast RHS to LHS type\<close>
    case shift
    from assms(1) resolved cop shift have
      fin_lhs: "is_finite_integer_type lhsTy'" and fin_rhs: "is_finite_integer_type rhsTy'" and
      tm_eq: "resultTm = CoreTm_Binop cop lhsTm' (if lhsTy' = rhsTy' then rhsTm' else CoreTm_Cast lhsTy' rhsTm')" and
      ty_eq: "resultTy = lhsTy'"
      by (auto simp: Let_def split: if_splits)
    have cast_typed: "core_term_type env ghost (if lhsTy' = rhsTy' then rhsTm' else CoreTm_Cast lhsTy' rhsTm') = Some lhsTy'"
    proof (cases "lhsTy' = rhsTy'")
      case True
      then show ?thesis using rhs' by simp
    next
      case False
      have "is_integer_type rhsTy'" using fin_rhs finite_integer_type_is_integer_type by simp
      moreover have "is_integer_type lhsTy'" using fin_lhs finite_integer_type_is_integer_type by simp
      moreover have "is_runtime_type env lhsTy'" using fin_lhs by (cases lhsTy') auto
      ultimately show ?thesis using rhs' False by auto
    qed
    with lhs' fin_lhs shift tm_eq ty_eq show ?thesis by auto
  next
    \<comment> \<open>Ordering: both numeric, result is Bool\<close>
    case ordering
    from assms(1) resolved cop ordering have
      "check_and_coerce_binop is_numeric_type (Some CoreTy_Bool) TyErr_BinopRequiresNumeric cop
         lhsTm' lhsTy' rhsTm' rhsTy' loc babOp = Inr (resultTm, resultTy)"
      by (simp add: Let_def)
    from check_and_coerce_binop_correct[OF this lhs' rhs' assms(4)]
    obtain opL opR commonTy where
      tm_eq: "resultTm = CoreTm_Binop cop opL opR" and
      opL_ty: "core_term_type env ghost opL = Some commonTy" and
      opR_ty: "core_term_type env ghost opR = Some commonTy" and
      pred: "is_numeric_type commonTy" and ty_eq: "resultTy = CoreTy_Bool"
      by auto
    with ordering show ?thesis by auto
  next
    \<comment> \<open>Equality/inequality\<close>
    case eq_neq
    show ?thesis
    proof (cases "lhsTy' = rhsTy'")
      case True
      with assms(1) resolved cop eq_neq have
        cond: "ghost = Ghost \<or> lhsTy' = CoreTy_Bool \<or> is_numeric_type lhsTy'" and
        tm_eq: "resultTm = CoreTm_Binop cop lhsTm' rhsTm'" and ty_eq: "resultTy = CoreTy_Bool"
        by (auto simp: Let_def split: if_splits)
      with lhs' rhs' eq_neq True show ?thesis by auto
    next
      case False
      with assms(1) resolved cop eq_neq obtain newLhs newRhs commonTy where
        coerce: "coerce_to_common_int_type lhsTm' lhsTy' rhsTm' rhsTy' = Some (newLhs, newRhs, commonTy)"
        and tm_eq: "resultTm = CoreTm_Binop cop newLhs newRhs" and ty_eq: "resultTy = CoreTy_Bool"
        by (auto simp: Let_def split: option.splits if_splits)
      from coerce_to_common_int_type_correct[OF coerce lhs' rhs' assms(4)]
      have typed: "core_term_type env ghost newLhs = Some commonTy"
                  "core_term_type env ghost newRhs = Some commonTy" by auto
      from coerce have "is_finite_integer_type commonTy"
        by (cases lhsTy'; cases rhsTy') (auto split: option.splits simp: Let_def)
      hence "is_numeric_type commonTy" by (cases commonTy) auto
      with typed eq_neq tm_eq ty_eq show ?thesis by auto
    qed
  next
    \<comment> \<open>Logical: both Bool\<close>
    case logical
    from assms(1) resolved cop logical have
      "lhsTy' = CoreTy_Bool" "rhsTy' = CoreTy_Bool"
      "resultTm = CoreTm_Binop cop lhsTm' rhsTm'" "resultTy = CoreTy_Bool"
      by (auto simp: Let_def split: if_splits)
    with lhs' rhs' logical show ?thesis by auto
  qed
qed

(* Correctness of elab_binop_with_special *)
lemma elab_binop_with_special_correct:
  assumes "elab_binop_with_special is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "core_term_type env ghost rhsTm = Some rhsTy"
    and "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
proof (cases "babOp = BabBinop_ImpliedBy \<or> babOp = BabBinop_Iff")
  case True
  then show ?thesis
  proof
    assume "babOp = BabBinop_ImpliedBy"
    \<comment> \<open>ImpliedBy: swaps operands and calls elab_single_binop with Implies\<close>
    with assms(1) have
      "elab_single_binop is_flex loc ghost BabBinop_Implies rhsTm rhsTy lhsTm lhsTy = Inr (resultTm, resultTy)"
      by simp
    thus ?thesis using elab_single_binop_correct[OF _ assms(3,2,4) _ locals_rigid ret_rigid]
      using binop_to_core.simps(19) by blast
  next
    assume iff: "babOp = BabBinop_Iff"
    \<comment> \<open>Iff: resolves metas then checks both Bool\<close>
    obtain lhsTm' lhsTy' rhsTm' rhsTy' where
      resolved: "resolve_binop_metas is_flex BabBinop_Iff lhsTm lhsTy rhsTm rhsTy = (lhsTm', lhsTy', rhsTm', rhsTy')"
      by (cases "resolve_binop_metas is_flex BabBinop_Iff lhsTm lhsTy rhsTm rhsTy") auto
    have lhs': "core_term_type env ghost lhsTm' = Some lhsTy'"
      and rhs': "core_term_type env ghost rhsTm' = Some rhsTy'"
      using resolve_binop_metas_correct[OF resolved assms(2,3,4) locals_rigid ret_rigid] by auto
    from assms(1) iff resolved have
      "lhsTy' = CoreTy_Bool" "rhsTy' = CoreTy_Bool"
      "resultTm = CoreTm_Binop CoreBinop_Equal lhsTm' rhsTm'" "resultTy = CoreTy_Bool"
      by (auto simp: Let_def split: if_splits)
    with lhs' rhs' show ?thesis by auto
  qed
next
  case False
  \<comment> \<open>All other cases: elab_binop_with_special delegates to elab_single_binop\<close>
  hence eq: "elab_binop_with_special is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy
       = elab_single_binop is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy"
    by (cases babOp) simp_all
  from False obtain cop where "binop_to_core babOp = Some cop"
    by (cases babOp) auto
  with assms(1) eq show ?thesis
    using elab_single_binop_correct assms(2,3,4) locals_rigid ret_rigid by auto
qed

(* For comparison operators (those with a comparison_direction), elab_binop_with_special
   always returns CoreTy_Bool as the result type when it succeeds. *)
lemma elab_binop_with_special_comparison_bool:
  assumes "elab_binop_with_special is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    and "comparison_direction babOp \<noteq> None"
  shows "resultTy = CoreTy_Bool"
proof -
  \<comment> \<open>comparison_direction is only Some for <, <=, >, >=, ==, !=\<close>
  from assms(2) have "babOp \<in> {BabBinop_Less, BabBinop_LessEqual, BabBinop_Greater,
    BabBinop_GreaterEqual, BabBinop_Equal, BabBinop_NotEqual}"
    by (cases babOp) auto
  \<comment> \<open>None of these are ImpliedBy or Iff, so elab_binop_with_special calls elab_single_binop\<close>
  hence eq: "elab_single_binop is_flex loc ghost babOp lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
    using assms(1) by auto
  \<comment> \<open>For each of these 6 ops, elab_single_binop returns CoreTy_Bool on success\<close>
  from \<open>babOp \<in> _\<close> eq show "resultTy = CoreTy_Bool"
    by (cases babOp; simp add: check_and_coerce_binop_def Let_def
                      split: prod.splits option.splits if_splits)
qed

(* If check_comparison_chain_directions succeeds, all ops are comparisons *)
lemma check_comparison_chain_directions_all_comparison:
  assumes "check_comparison_chain_directions ops dir"
    and "(op, tm, ty) \<in> set ops"
  shows "comparison_direction op \<noteq> None"
  using assms by (induction ops arbitrary: dir) (auto split: option.splits if_splits)

(* Correctness of fold_binop_left *)
lemma fold_binop_left_correct:
  assumes "fold_binop_left is_flex loc ghost accTm accTy ops = Inr (resultTm, resultTy)"
    and "core_term_type env ghost accTm = Some accTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
using assms proof (induction ops arbitrary: accTm accTy)
  case Nil
  then show ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto
  from Cons.prems(1) triple_eq obtain midTm midTy where
    step: "elab_binop_with_special is_flex loc ghost op accTm accTy rhsTm rhsTy = Inr (midTm, midTy)" and
    rest: "fold_binop_left is_flex loc ghost midTm midTy rest = Inr (resultTm, resultTy)"
    by (auto split: sum.splits)
  have mid_typed: "core_term_type env ghost midTm = Some midTy"
    using elab_binop_with_special_correct[OF step Cons.prems(2) _ Cons.prems(4)
                                               Cons.prems(5) Cons.prems(6)]
      Cons.prems(3) triple_eq by simp
  show ?case using Cons.IH[OF rest mid_typed] Cons.prems(3,4,5,6) triple_eq by simp
qed

(* Correctness of fold_implies_right *)
lemma fold_implies_right_correct:
  assumes "fold_implies_right is_flex loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
using assms proof (induction ops arbitrary: lhsTm lhsTy resultTm resultTy)
  case Nil
  then show ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto
  have rhs_typed: "core_term_type env ghost rhsTm = Some rhsTy"
    using Cons.prems(3) triple_eq by simp
  show ?case
  proof (cases rest)
    case Nil
    \<comment> \<open>Single element: just call elab_binop_with_special\<close>
    from Cons.prems(1) triple_eq Nil have
      "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy = Inr (resultTm, resultTy)"
      by simp
    thus ?thesis
      using elab_binop_with_special_correct Cons.prems(2) rhs_typed Cons.prems(4)
            Cons.prems(5) Cons.prems(6) by blast
  next
    case (Cons triple2 rest2)
    \<comment> \<open>Multiple elements: recurse on right side, then combine\<close>
    from Cons.prems(1) triple_eq \<open>rest = triple2 # rest2\<close> obtain rightTm rightTy where
      recurse: "fold_implies_right is_flex loc ghost rhsTm rhsTy rest = Inr (rightTm, rightTy)" and
      combine: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rightTm rightTy = Inr (resultTm, resultTy)"
      by (auto split: sum.splits)
    have rest_all: "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) rest"
      using Cons.prems(3) triple_eq by simp
    have right_typed: "core_term_type env ghost rightTm = Some rightTy"
      using Cons.IH[OF recurse rhs_typed rest_all Cons.prems(4) Cons.prems(5) Cons.prems(6)] .
    show ?thesis
      using elab_binop_with_special_correct[OF combine Cons.prems(2) right_typed
                          Cons.prems(4) Cons.prems(5) Cons.prems(6)] .
  qed
qed

(* Helper: ''chain@@'' @ nat_to_string n starts with ''chain@@'' *)
lemma chain_var_prefix: "take 7 (''chain@@'' @ nat_to_string n) = ''chain@@''"
  by simp

(* Helper: the empty string does not start with ''chain@@'' *)
lemma empty_not_chain_prefix: "take 7 '''' \<noteq> ''chain@@''"
  by simp

(* Helper: if has_unexpected_chain_var returns False, then the only chain@@-prefixed
   free variable (if any) is the allowed one. *)
lemma not_has_unexpected_chain_var:
  assumes "\<not> has_unexpected_chain_var tm allowed"
    and "v \<in> core_term_free_vars tm"
    and "take 7 v = ''chain@@''"
  shows "v = allowed"
  using assms by (auto simp: has_unexpected_chain_var_def)

(* If build_comparison_chain returns Inr, then chain@@ variables (with index >= chainCtr)
   are not free in lhsTm, and chain@@ variables are not free in the op terms.
   This follows from the has_unexpected_chain_var runtime checks.
   We prove a combined statement to avoid issues with multi-conclusion induction. *)
lemma build_comparison_chain_inputs_fresh_combined:
  assumes "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy ops = Inr resultTm"
  shows "(\<forall>n \<ge> chainCtr. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm)
       \<and> (\<forall>opx \<in> set ops. \<forall>n. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars (fst (snd opx)))"
  using assms
proof (induction ops arbitrary: chainCtr lhsTm lhsTy resultTm)
  case Nil
  \<comment> \<open>build_comparison_chain returns Inl [] for empty ops, contradicting Inr\<close>
  thus ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto

  \<comment> \<open>Extract the check results from the Inr return\<close>
  let ?lhsAllowed = "if chainCtr = 0 then '''' else ''chain@@'' @ nat_to_string (chainCtr - 1)"

  \<comment> \<open>The Cons equation starts with a check; if it fails we get Inl, contradicting Inr.\<close>
  have checks_passed: "\<not> (has_unexpected_chain_var lhsTm ?lhsAllowed
                          \<or> has_unexpected_chain_var rhsTm '''')"
  proof (rule notI)
    assume "has_unexpected_chain_var lhsTm ?lhsAllowed
            \<or> has_unexpected_chain_var rhsTm ''''"
    hence "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (triple # rest)
           = Inl [TyErr_InternalError_UnexpectedChainVar loc]"
      using triple_eq by (simp add: Let_def)
    with Cons.prems show False by simp
  qed
  hence check_lhs: "\<not> has_unexpected_chain_var lhsTm ?lhsAllowed"
    and check_rhs: "\<not> has_unexpected_chain_var rhsTm ''''"
    by auto

  \<comment> \<open>Part 1: chain@@n not free in lhsTm for n \<ge> chainCtr\<close>
  have lhs_result: "\<forall>n \<ge> chainCtr. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm"
  proof (intro allI impI notI)
    fix n assume n_ge: "n \<ge> chainCtr"
    assume in_fv: "''chain@@'' @ nat_to_string n \<in> core_term_free_vars lhsTm"
    have eq_allowed: "''chain@@'' @ nat_to_string n = ?lhsAllowed"
      using not_has_unexpected_chain_var[OF check_lhs in_fv chain_var_prefix] .
    show False
    proof (cases "chainCtr = 0")
      case True
      from True eq_allowed have "''chain@@'' @ nat_to_string n = ''''" by simp
      thus False by simp
    next
      case False
      from False eq_allowed
      have "''chain@@'' @ nat_to_string n = ''chain@@'' @ nat_to_string (chainCtr - 1)" by simp
      hence "nat_to_string n = nat_to_string (chainCtr - 1)" by simp
      hence "n = chainCtr - 1" using nat_to_string_injective by blast
      with n_ge False show False by arith
    qed
  qed

  \<comment> \<open>Part 2a: chain@@n not free in rhsTm (the first op term)\<close>
  have rhs_result: "\<forall>n. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars rhsTm"
  proof (intro allI notI)
    fix n assume in_fv: "''chain@@'' @ nat_to_string n \<in> core_term_free_vars rhsTm"
    have "''chain@@'' @ nat_to_string n = ''''"
      using not_has_unexpected_chain_var[OF check_rhs in_fv chain_var_prefix] .
    thus False by simp
  qed

  \<comment> \<open>Part 2b: chain@@n not free in ops in rest (from IH via recursive call)\<close>
  have rest_result: "\<forall>opx \<in> set rest. \<forall>n. ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars (fst (snd opx))"
  proof (cases rest)
    case Nil thus ?thesis by simp
  next
    case (Cons triple2 rest2)
    \<comment> \<open>rest is non-empty, so there is a recursive call that returns Inr\<close>
    obtain resolvedLhs resolvedLhsTy resolvedRhs resolvedRhsTy where
      resolved: "resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy =
                 (resolvedLhs, resolvedLhsTy, resolvedRhs, resolvedRhsTy)"
      by (cases "resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy") auto
    \<comment> \<open>Simplify the function with checks eliminated\<close>
    from checks_passed triple_eq
    have bcc_simplified:
      "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (triple # rest) =
       (case rest of
         [] \<Rightarrow> (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy of
                  Inl errs \<Rightarrow> Inl errs | Inr (cmpTm, _) \<Rightarrow> Inr cmpTm)
       | _ \<Rightarrow>
         let (_, _, resolvedRhs', resolvedRhsTy') = resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy
         in if is_simple_term resolvedRhs' then
              (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy resolvedRhs' resolvedRhsTy' of
                Inl errs \<Rightarrow> Inl errs
              | Inr (cmpTm, _) \<Rightarrow>
                  (case build_comparison_chain is_flex loc ghost chainCtr resolvedRhs' resolvedRhsTy' rest of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr restTm \<Rightarrow> Inr (CoreTm_Binop CoreBinop_And cmpTm restTm)))
            else if \<not> list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list resolvedRhsTy')
                 then Inl [TyErr_CannotInferType loc]
            else let varName = ''chain@@'' @ nat_to_string chainCtr;
                     varTm = CoreTm_Var varName
                 in (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy varTm resolvedRhsTy' of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr (cmpTm, _) \<Rightarrow>
                        (case build_comparison_chain is_flex loc ghost (chainCtr + 1) varTm resolvedRhsTy' rest of
                          Inl errs \<Rightarrow> Inl errs
                        | Inr restTm \<Rightarrow>
                            Inr (CoreTm_Let varName resolvedRhs'
                                  (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"
      by (simp add: Let_def)

    show ?thesis
    proof (cases "is_simple_term resolvedRhs")
      case True
      \<comment> \<open>Simple term: recursive call with same chainCtr\<close>
      from Cons.prems bcc_simplified Cons resolved True
      obtain restTm where
        recurse: "build_comparison_chain is_flex loc ghost chainCtr resolvedRhs resolvedRhsTy rest = Inr restTm"
        by (auto simp: Let_def split: sum.splits prod.splits list.splits)
      from Cons.IH[OF recurse] show ?thesis by (simp add: prod.case_eq_if)
    next
      case not_simple: False
      \<comment> \<open>Hide nat_to_string chainCtr behind a definition to prevent linarith looping\<close>
      define varName where "varName = ''chain@@'' @ nat_to_string chainCtr"
      let ?varTm = "CoreTm_Var varName"

      \<comment> \<open>Derive a simplified equation for the complex case\<close>
      from bcc_simplified Cons resolved not_simple
      have bcc_complex:
        "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (triple # rest) =
         (if \<not> list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list resolvedRhsTy)
          then Inl [TyErr_CannotInferType loc]
          else (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy ?varTm resolvedRhsTy of
                  Inl errs \<Rightarrow> Inl errs
                | Inr (cmpTm, _) \<Rightarrow>
                    (case build_comparison_chain is_flex loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr restTm \<Rightarrow>
                        Inr (CoreTm_Let varName resolvedRhs
                              (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"
        unfolding varName_def[symmetric]
        by (simp add: Let_def split: list.splits prod.splits)

      show ?thesis
      proof (cases "list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list resolvedRhsTy)")
        case False
        \<comment> \<open>Not resolved: returns Inl, contradicting Inr\<close>
        from Cons.prems bcc_complex False
        have False by simp
        thus ?thesis ..
      next
        case True
        \<comment> \<open>Complex term: recursive call with chainCtr + 1\<close>
        from Cons.prems bcc_complex True
        obtain restTm where
          recurse: "build_comparison_chain is_flex loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest = Inr restTm"
          by (auto split: sum.splits prod.splits)
        from Cons.IH[OF recurse] show ?thesis by (simp add: prod.case_eq_if)
      qed
    qed
  qed

  \<comment> \<open>Combine parts\<close>
  from lhs_result rhs_result rest_result
  show ?case using triple_eq by (auto simp: prod.case_eq_if)
qed

(* Split the combined lemma into the two conclusions used elsewhere *)
lemma build_comparison_chain_inputs_fresh:
  assumes "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy ops = Inr resultTm"
  shows "\<And>n. n \<ge> chainCtr \<Longrightarrow> ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm"
    and "\<And>op tm ty n. (op, tm, ty) \<in> set ops \<Longrightarrow>
           ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars tm"
proof -
  note combined = build_comparison_chain_inputs_fresh_combined[OF assms]
  { fix n assume "n \<ge> chainCtr"
    with combined show "''chain@@'' @ nat_to_string n \<notin> core_term_free_vars lhsTm" by blast }
  { fix op tm ty n assume "(op, tm, ty) \<in> set ops"
    hence "(op, tm, ty) \<in> set ops" .
    with combined have "''chain@@'' @ nat_to_string n \<notin> core_term_free_vars (fst (snd (op, tm, ty)))"
      by blast
    thus "''chain@@'' @ nat_to_string n \<notin> core_term_free_vars tm" by simp }
qed

(* Correctness of build_comparison_chain. *)
lemma build_comparison_chain_correct:
  assumes "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy ops = Inr resultTm"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
    and "check_comparison_chain_directions ops dir"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some CoreTy_Bool"
  using assms
proof (induction ops arbitrary: chainCtr lhsTm lhsTy resultTm env dir)
  case Nil
  then show ?case by simp
next
  case (Cons triple rest)
  obtain op rhsTm rhsTy where triple_eq: "triple = (op, rhsTm, rhsTy)"
    by (cases triple) auto
  have rhs_typed: "core_term_type env ghost rhsTm = Some rhsTy"
    using Cons.prems(3) triple_eq by simp

  \<comment> \<open>Get the chain direction info for op\<close>
  have op_cmp: "comparison_direction op \<noteq> None"
    using check_comparison_chain_directions_all_comparison[OF Cons.prems(5)]
          triple_eq by (meson list.set_intros(1) prod_cases3)

  \<comment> \<open>Get resolved operands\<close>
  obtain resolvedLhs resolvedLhsTy resolvedRhs resolvedRhsTy where
    resolved: "resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy =
               (resolvedLhs, resolvedLhsTy, resolvedRhs, resolvedRhsTy)"
    by (cases "resolve_binop_metas is_flex op lhsTm lhsTy rhsTm rhsTy") auto

  have resolvedRhs_typed: "core_term_type env ghost resolvedRhs = Some resolvedRhsTy"
    using Cons.prems(2,4,6,7) resolve_binop_metas_correct resolved rhs_typed by blast

  \<comment> \<open>Propagate chain direction check to rest\<close>
  have rest_dirs: "check_comparison_chain_directions rest
      (if comparison_direction op = Some ChainNeutral then dir else the (comparison_direction op))"
    using Cons.prems(5) triple_eq by (auto split: option.splits if_splits)

  \<comment> \<open>The has_unexpected_chain_var checks must have passed (otherwise we'd get Inl)\<close>
  let ?lhsAllowed = "if chainCtr = 0 then '''' else ''chain@@'' @ nat_to_string (chainCtr - 1)"
  have checks_passed: "\<not> (has_unexpected_chain_var lhsTm ?lhsAllowed
                          \<or> has_unexpected_chain_var rhsTm '''')"
  proof (rule notI)
    assume "has_unexpected_chain_var lhsTm ?lhsAllowed
            \<or> has_unexpected_chain_var rhsTm ''''"
    hence "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (triple # rest)
           = Inl [TyErr_InternalError_UnexpectedChainVar loc]"
      using triple_eq by (simp add: Let_def)
    with Cons.prems(1) show False by simp
  qed

  show ?case
  proof (cases rest)
    case Nil
    \<comment> \<open>Last comparison: just elaborate normally\<close>
    from Cons.prems(1) triple_eq Nil checks_passed
    obtain cmpTm cmpTy where
      elab: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy rhsTm rhsTy = Inr (cmpTm, cmpTy)"
      and result: "resultTm = cmpTm"
      by (auto simp: Let_def split: sum.splits prod.splits)
    have "core_term_type env ghost cmpTm = Some cmpTy"
      using Cons.prems(2,4,6,7) elab elab_binop_with_special_correct rhs_typed by auto
    moreover have "cmpTy = CoreTy_Bool"
      using elab_binop_with_special_comparison_bool[OF elab op_cmp] .
    ultimately show ?thesis using result by simp
  next
    case rest_cons: (Cons triple2 rest2)
    \<comment> \<open>More comparisons follow\<close>

    \<comment> \<open>Common facts for both subcases\<close>
    have rest_all: "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) rest"
      using Cons.prems(3) triple_eq by simp

    show ?thesis
    proof (cases "is_simple_term resolvedRhs")
      case True
      \<comment> \<open>Simple term: duplicate directly\<close>
      from Cons.prems(1) triple_eq rest_cons resolved True checks_passed
      obtain cmpTm cmpTy restTm where
        elab: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy resolvedRhs resolvedRhsTy
               = Inr (cmpTm, cmpTy)" and
        recurse: "build_comparison_chain is_flex loc ghost chainCtr resolvedRhs resolvedRhsTy rest
                  = Inr restTm" and
        result: "resultTm = CoreTm_Binop CoreBinop_And cmpTm restTm"
        by (auto simp: Let_def split: sum.splits prod.splits)
      have cmpTy_bool: "cmpTy = CoreTy_Bool"
        using elab_binop_with_special_comparison_bool[OF elab op_cmp] .
      have cmp_typed: "core_term_type env ghost cmpTm = Some CoreTy_Bool"
        using Cons.prems(2,4,6,7) cmpTy_bool elab elab_binop_with_special_correct resolvedRhs_typed
        by blast
      have rest_typed: "core_term_type env ghost restTm = Some CoreTy_Bool"
        using Cons.IH[OF recurse resolvedRhs_typed rest_all Cons.prems(4) rest_dirs
                         Cons.prems(6) Cons.prems(7)] .
      show ?thesis using cmp_typed rest_typed result by simp
    next
      case not_simple: False
      \<comment> \<open>Complex term: let-binding case\<close>
      let ?varName = "''chain@@'' @ nat_to_string chainCtr"
      let ?varTm = "CoreTm_Var ?varName"

      \<comment> \<open>The resolved check must pass (otherwise we'd get Inl).\<close>
      from Cons.prems(1) triple_eq rest_cons resolved not_simple checks_passed
      have ground: "list_all (\<lambda>n. \<not> is_flex n) (type_tyvars_list resolvedRhsTy)"
        by (auto simp: Let_def split: if_splits sum.splits prod.splits)

      \<comment> \<open>Extract the elab and recursive call results via the helper lemma.\<close>
      from Cons.prems(1) triple_eq rest_cons resolved not_simple ground
      obtain cmpTm cmpTy restTm where
        elab: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy ?varTm resolvedRhsTy
               = Inr (cmpTm, cmpTy)" and
        recurse: "build_comparison_chain is_flex loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest
                  = Inr restTm" and
        result: "resultTm = CoreTm_Let ?varName resolvedRhs
                              (CoreTm_Binop CoreBinop_And cmpTm restTm)"
      proof -
        have "build_comparison_chain is_flex loc ghost chainCtr lhsTm lhsTy (Cons triple rest)
          = (let varName = ''chain@@'' @ nat_to_string chainCtr;
              varTm = CoreTm_Var varName
          in (case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy varTm resolvedRhsTy of
            Inl errs \<Rightarrow> Inl errs
          | Inr (cmpTm, _) \<Rightarrow>
              (case build_comparison_chain is_flex loc ghost (chainCtr + 1) varTm resolvedRhsTy rest of
                Inl errs \<Rightarrow> Inl errs
              | Inr restTm \<Rightarrow>
                  Inr (CoreTm_Let varName resolvedRhs
                        (CoreTm_Binop CoreBinop_And cmpTm restTm)))))"
          using rest_cons triple_eq resolved not_simple ground checks_passed
          by (simp only: build_comparison_chain.simps prod.case Let_def list.case
                         if_False if_True if_not_P[OF not_simple]
                         not_True_eq_False not_False_eq_True ground)

        hence "(case elab_binop_with_special is_flex loc ghost op lhsTm lhsTy ?varTm resolvedRhsTy of
                Inl errs \<Rightarrow> Inl errs
              | Inr (cmpTm, _) \<Rightarrow>
                  (case build_comparison_chain is_flex loc ghost (chainCtr + 1) ?varTm resolvedRhsTy rest of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr restTm \<Rightarrow>
                      Inr (CoreTm_Let ?varName resolvedRhs
                            (CoreTm_Binop CoreBinop_And cmpTm restTm)))) = Inr resultTm"
          by (metis Cons.prems(1))

        thus ?thesis using build_comparison_chain_let_elim that by blast
      qed

      \<comment> \<open>Hide nat_to_string chainCtr behind a definition to prevent linarith looping\<close>
      define vn where "vn = ''chain@@'' @ nat_to_string chainCtr"
      have vn_eq: "?varName = vn" by (simp add: vn_def)

      \<comment> \<open>Rewrite elab, recurse, result to use vn\<close>
      note elab' = elab[unfolded vn_eq[symmetric]]
      note recurse' = recurse[unfolded vn_eq[symmetric]]
      note result' = result[unfolded vn_eq[symmetric]]

      \<comment> \<open>Derive chain@@ freshness from build_comparison_chain_inputs_fresh\<close>
      have lhs_fresh: "vn \<notin> core_term_free_vars lhsTm"
        using build_comparison_chain_inputs_fresh(1)[OF Cons.prems(1)] vn_def by blast
      have rest_fresh: "\<And>op tm ty n. (op, tm, ty) \<in> set rest \<Longrightarrow>
             ''chain@@'' @ nat_to_string n \<notin> core_term_free_vars tm"
        using build_comparison_chain_inputs_fresh(2)[OF Cons.prems(1)]
              triple_eq by (meson list.set_intros(2))

      \<comment> \<open>Build the extended environment\<close>
      define gv' where "gv' = (if ghost = Ghost then finsert vn (TE_GhostLocals env)
                               else fminus (TE_GhostLocals env) {|vn|})"
      define env' where "env' = env \<lparr> TE_LocalVars := fmupd vn resolvedRhsTy (TE_LocalVars env),
                                       TE_GhostLocals := gv',
                                       TE_ConstLocals := finsert vn (TE_ConstLocals env) \<rparr>"

      \<comment> \<open>env' is well-formed\<close>
      have wk: "is_well_kinded env resolvedRhsTy"
        using core_term_type_well_kinded[OF resolvedRhs_typed Cons.prems(4)] .
      define env_no_cn where "env_no_cn = env \<lparr> TE_LocalVars := fmupd vn resolvedRhsTy (TE_LocalVars env),
                                                  TE_GhostLocals := gv' \<rparr>"
      have wf_no_cn: "tyenv_well_formed env_no_cn"
      proof (cases ghost)
        case Ghost
        show ?thesis using tyenv_well_formed_add_ghost_var[OF Cons.prems(4) wk] Ghost
          by (simp add: env_no_cn_def gv'_def)
      next
        case NotGhost
        have rt: "is_runtime_type env resolvedRhsTy"
          using core_term_type_notghost_runtime[OF _ Cons.prems(4)] resolvedRhs_typed NotGhost by simp
        thus ?thesis using tyenv_well_formed_add_var[OF Cons.prems(4) wk rt] NotGhost
          by (simp add: env_no_cn_def gv'_def)
      qed
      have env'_eq_cn: "env' = env_no_cn \<lparr> TE_ConstLocals := finsert vn (TE_ConstLocals env) \<rparr>"
        by (simp add: env'_def env_no_cn_def)
      have env'_wf: "tyenv_well_formed env'"
        using wf_no_cn tyenv_well_formed_TE_ConstLocals_irrelevant env'_eq_cn by simp

      \<comment> \<open>The variable typechecks in env'\<close>
      have var_typed: "core_term_type env' ghost (CoreTm_Var vn) = Some resolvedRhsTy"
        by (cases ghost)
           (simp_all add: env'_def gv'_def tyenv_lookup_var_def tyenv_var_ghost_def)

      \<comment> \<open>lhsTm typechecks in env' by weakening (vn not free in lhsTm)\<close>
      have gv'_agree: "\<forall>y. y \<noteq> vn \<longrightarrow> (y |\<in>| gv' \<longleftrightarrow> y |\<in>| TE_GhostLocals env)"
        by (auto simp: gv'_def)
      have lhs_typed': "core_term_type env' ghost lhsTm = Some lhsTy"
        using core_term_type_irrelevant_var[OF lhs_fresh Cons.prems(2) gv'_agree]
              core_term_type_TE_ConstLocals_irrelevant
        by (simp add: env'_def env_no_cn_def)

      \<comment> \<open>env' has the same TE_TypeVars / TE_ReturnType as env (only locals,
          ghost-locals, and const-names changed). The rigidity conditions lift:
          old locals are still rigid (from Cons.prems(6)), and the newly added
          local resolvedRhsTy has no flex metavars (from ground). \<close>
      have env'_locals_rigid:
        "\<forall>name ty' n. fmlookup (TE_LocalVars env') name = Some ty'
                        \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
      proof (intro allI impI)
        fix name ty' n
        assume lk: "fmlookup (TE_LocalVars env') name = Some ty'"
        assume n_mv: "n \<in> type_tyvars ty'"
        show "\<not> is_flex n"
        proof (cases "name = vn")
          case True
          with lk have "ty' = resolvedRhsTy"
            by (simp add: env'_def)
          with n_mv ground show ?thesis
            by (auto simp: set_type_tyvars_list[symmetric] list_all_iff)
        next
          case False
          with lk have "fmlookup (TE_LocalVars env) name = Some ty'"
            by (simp add: env'_def)
          with Cons.prems(6) n_mv show ?thesis by blast
        qed
      qed
      have env'_ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env') \<longrightarrow> \<not> is_flex n"
        using Cons.prems(7) by (simp add: env'_def)

      \<comment> \<open>cmpTm typechecks in env'\<close>
      have cmpTy_bool: "cmpTy = CoreTy_Bool"
        using elab_binop_with_special_comparison_bool[OF elab op_cmp] .
      have elab_vn: "elab_binop_with_special is_flex loc ghost op lhsTm lhsTy (CoreTm_Var vn) resolvedRhsTy
                     = Inr (cmpTm, cmpTy)"
        using elab using vn_eq by auto
      have cmp_typed: "core_term_type env' ghost cmpTm = Some CoreTy_Bool"
        using elab_binop_with_special_correct[OF elab_vn lhs_typed' var_typed env'_wf
                                                  env'_locals_rigid env'_ret_rigid]
              cmpTy_bool by simp

      \<comment> \<open>The ops in rest typecheck in env' by weakening\<close>
      have rest_all': "list_all (\<lambda>(op, tm, ty). core_term_type env' ghost tm = Some ty) rest"
        unfolding list_all_iff
      proof (intro ballI, clarify)
        fix xop xtm xty assume in_rest: "(xop, xtm, xty) \<in> set rest"
        have xtm_typed: "core_term_type env ghost xtm = Some xty"
          using rest_all in_rest by (auto simp: list_all_iff)
        have xtm_fresh: "vn \<notin> core_term_free_vars xtm"
          using rest_fresh in_rest vn_def by blast
        show "core_term_type env' ghost xtm = Some xty"
          using core_term_type_irrelevant_var[OF xtm_fresh xtm_typed gv'_agree]
                core_term_type_TE_ConstLocals_irrelevant
          by (simp add: env'_def env_no_cn_def)
      qed

      \<comment> \<open>restTm typechecks in env' by the inductive hypothesis\<close>
      have recurse_vn: "build_comparison_chain is_flex loc ghost (chainCtr + 1)
                          (CoreTm_Var vn) resolvedRhsTy rest = Inr restTm"
        using recurse using vn_eq by auto
      have rest_typed: "core_term_type env' ghost restTm = Some CoreTy_Bool"
        using Cons.IH[OF recurse_vn var_typed rest_all' env'_wf rest_dirs
                         env'_locals_rigid env'_ret_rigid] .

      \<comment> \<open>The body (And cmpTm restTm) typechecks in env'\<close>
      have body_typed: "core_term_type env' ghost (CoreTm_Binop CoreBinop_And cmpTm restTm)
                        = Some CoreTy_Bool"
        using cmp_typed rest_typed by simp

      \<comment> \<open>The whole let-expression typechecks\<close>
      have result_vn: "resultTm = CoreTm_Let vn resolvedRhs
                                    (CoreTm_Binop CoreBinop_And cmpTm restTm)"
        using result vn_def by simp
      have "core_term_type env ghost (CoreTm_Let vn resolvedRhs
              (CoreTm_Binop CoreBinop_And cmpTm restTm)) = Some CoreTy_Bool"
        using resolvedRhs_typed ground body_typed
        by (simp add: env'_def gv'_def Let_def)
      thus ?thesis using result_vn by simp
    qed
  qed
qed

(* Correctness of process_binop_chain *)
lemma process_binop_chain_correct:
  assumes "process_binop_chain is_flex loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
    and "core_term_type env ghost lhsTm = Some lhsTy"
    and "list_all (\<lambda>(op, tm, ty). core_term_type env ghost tm = Some ty) ops"
    and "tyenv_well_formed env"
    and locals_rigid: "\<forall>name ty' n. fmlookup (TE_LocalVars env) name = Some ty'
                         \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> is_flex n"
    and ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType env) \<longrightarrow> \<not> is_flex n"
  shows "core_term_type env ghost resultTm = Some resultTy"
proof (cases ops)
  case Nil
  with assms(1) show ?thesis using assms(2) by simp
next
  case (Cons triple rest)
  let ?firstOp = "fst (hd ops)"
  show ?thesis
  proof (cases "?firstOp = BabBinop_Implies \<or> ?firstOp = BabBinop_ImpliedBy")
    case True
    \<comment> \<open>Implies chain: right-associates (check_implies_chain must pass, else we'd get Inl)\<close>
    with assms(1) Cons have "fold_implies_right is_flex loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
      by (auto simp: Let_def split: if_splits)
    thus ?thesis using fold_implies_right_correct assms(2,3,4) locals_rigid ret_rigid by blast
  next
    case not_implies: False
    show ?thesis
    proof (cases "is_comparison_bab_binop ?firstOp \<and> length ops > 1")
      case True
      \<comment> \<open>Comparison chain\<close>
      from assms(1) Cons not_implies True
      have dirs: "check_comparison_chain_directions ops ChainNeutral"
        by (auto simp: Let_def split: sum.splits if_splits)
      from assms(1) Cons not_implies True
      obtain chainTm where
        chain_ok: "build_comparison_chain is_flex loc ghost 0 lhsTm lhsTy ops = Inr chainTm"
        and result: "resultTm = chainTm" and rty: "resultTy = CoreTy_Bool"
        by (auto simp: Let_def split: sum.splits if_splits)
      have "core_term_type env ghost chainTm = Some CoreTy_Bool"
        using build_comparison_chain_correct[OF chain_ok assms(2,3,4) dirs locals_rigid ret_rigid] .
      thus ?thesis using result rty by simp
    next
      case False
      \<comment> \<open>Left-associate\<close>
      with assms(1) Cons not_implies have
        "fold_binop_left is_flex loc ghost lhsTm lhsTy ops = Inr (resultTm, resultTy)"
        by (auto simp: Let_def split: if_splits)
      thus ?thesis using fold_binop_left_correct assms(2,3,4) locals_rigid ret_rigid by blast
    qed
  qed
qed


(* ========================================================================== *)
(* Record update helper lemmas *)
(* ========================================================================== *)

(* A substitution whose domain is disjoint from TE_TypeVars env
   is the identity on all local variable types and the return type.
   This pattern recurs in If, Quantifier, Call, RecordUpdate, etc. *)
lemma flex_subst_identity_on_env:
  assumes dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> n |\<notin>| TE_TypeVars env"
      and wf: "tyenv_well_formed env"
      and locals_eq: "TE_LocalVars env' = TE_LocalVars env"
      and ret_eq: "TE_ReturnType env' = TE_ReturnType env"
  shows "(\<forall>vname vty. fmlookup (TE_LocalVars env') vname = Some vty
                       \<longrightarrow> apply_subst subst vty = vty)
       \<and> apply_subst subst (TE_ReturnType env') = TE_ReturnType env'"
proof (intro conjI allI impI)
  fix vname vty
  assume lk: "fmlookup (TE_LocalVars env') vname = Some vty"
  with locals_eq have lk_env: "fmlookup (TE_LocalVars env) vname = Some vty" by simp
  from wf have "tyenv_vars_well_kinded env" unfolding tyenv_well_formed_def by simp
  with lk_env have "is_well_kinded env vty" unfolding tyenv_vars_well_kinded_def by blast
  hence "type_tyvars vty \<subseteq> fset (TE_TypeVars env)"
    using is_well_kinded_type_tyvars_subset by blast
  hence "type_tyvars vty \<inter> fset (fmdom subst) = {}" using dom_flex by auto
  thus "apply_subst subst vty = vty" by (rule apply_subst_disjoint_id)
next
  from wf have "tyenv_return_type_well_kinded env" unfolding tyenv_well_formed_def by simp
  hence "is_well_kinded env (TE_ReturnType env)" unfolding tyenv_return_type_well_kinded_def .
  hence "type_tyvars (TE_ReturnType env) \<subseteq> fset (TE_TypeVars env)"
    using is_well_kinded_type_tyvars_subset by blast
  hence "type_tyvars (TE_ReturnType env) \<inter> fset (fmdom subst) = {}" using dom_flex by auto
  hence "apply_subst subst (TE_ReturnType env) = TE_ReturnType env"
    by (rule apply_subst_disjoint_id)
  thus "apply_subst subst (TE_ReturnType env') = TE_ReturnType env'" using ret_eq by simp
qed


lemma check_update_fields_exist_sound:
  "check_update_fields_exist flds parentFields = None \<Longrightarrow>
   \<forall>(name, _) \<in> set flds. map_of parentFields name \<noteq> None"
  by (induction flds) (auto split: if_splits)

(* Correctness of unify_update_types (Phase 1 of record update):
   Analogous to unify_call_types_correct but keyed by field name.
   If unification succeeds, the finalSubst is well-kinded, runtime, flex-domain,
   extends accSubst, and each update field's actual type either unifies with or is
   coercible to the expected type from the parent. *)

lemma build_record_update_map_fst:
  "map fst (build_record_update parentTm iterFields updates) = map fst iterFields"
  by (induction parentTm iterFields updates rule: build_record_update.induct)
     (auto split: option.splits)

lemma build_record_update_length:
  "length (build_record_update parentTm iterFields updates) = length iterFields"
  using build_record_update_map_fst by (metis length_map)

lemma apply_update_coercions_map_fst:
  "length namedTms = length namedActualTys \<Longrightarrow>
   length namedActualTys = length namedExpectedTys \<Longrightarrow>
   map fst (apply_update_coercions subst namedTms namedActualTys namedExpectedTys)
   = map fst namedTms"
proof (induction subst namedTms namedActualTys namedExpectedTys
       rule: apply_update_coercions.induct)
  case (2 subst name tm rest nameA actualTy actualRest nameE expectedTy expectedRest)
  then show ?case by (simp add: Let_def)
qed simp_all

lemma unify_update_types_correct:
  assumes "unify_update_types is_flex loc updates parentFields accSubst = Inr finalSubst"
      and "tyenv_well_formed env"
      and "\<forall>(name, ty) \<in> set updates. is_well_kinded env ty"
      and "\<forall>(name, ty) \<in> set parentFields. is_well_kinded env ty"
      and "\<forall>ty \<in> fmran' accSubst. is_well_kinded env ty"
      and "ghost = NotGhost \<longrightarrow> (\<forall>(name, ty) \<in> set updates. is_runtime_type env ty)"
      and "ghost = NotGhost \<longrightarrow> (\<forall>(name, ty) \<in> set parentFields. is_runtime_type env ty)"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' accSubst. is_runtime_type env ty)"
      and acc_dom_flex: "\<forall>n. n |\<in>| fmdom accSubst \<longrightarrow> is_flex n"
      and "\<forall>(name, _) \<in> set updates. map_of parentFields name \<noteq> None"
  shows "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type env ty))
       \<and> (\<exists>theta. finalSubst = compose_subst theta accSubst)
       \<and> list_all (\<lambda>(name, actualTy).
           case map_of parentFields name of
             Some expectedTy \<Rightarrow>
               apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
               \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                  \<and> is_finite_integer_type (apply_subst finalSubst expectedTy))
           | None \<Rightarrow> True)
         updates
       \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> is_flex n)"
  using assms
proof (induction is_flex loc updates parentFields accSubst
       arbitrary: finalSubst
       rule: unify_update_types.induct)
  case (1 is_flex loc parentFields accSubst)
  from "1.prems"(1) have "finalSubst = accSubst" by simp
  moreover have "accSubst = compose_subst fmempty accSubst" by simp
  ultimately show ?case
    using "1.prems"(5,8,9) list_all_simps(2) by blast 
next
  case (2 is_flex loc name actualTy rest parentFields accSubst)
  let ?actualTy' = "apply_subst accSubst actualTy"

  from "2.prems"(10) have name_found: "map_of parentFields name \<noteq> None" by simp
  then obtain expectedTy where
    lookup: "map_of parentFields name = Some expectedTy" by blast
  let ?expectedTy' = "apply_subst accSubst expectedTy"

  from "2.prems"(3) have actualTy_wk: "is_well_kinded env actualTy"
    and rest_wk: "\<forall>(n, ty) \<in> set rest. is_well_kinded env ty" by simp_all
  from "2.prems"(6) have actualTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env actualTy"
    and rest_rt: "ghost = NotGhost \<longrightarrow> (\<forall>(n, ty) \<in> set rest. is_runtime_type env ty)" by simp_all
  from "2.prems"(10) have rest_found: "\<forall>(n, _) \<in> set rest. map_of parentFields n \<noteq> None"
    by simp

  \<comment> \<open>expectedTy is well-kinded and runtime because it's in parentFields\<close>
  have expectedTy_wk: "is_well_kinded env expectedTy"
    using "2.prems"(4) lookup by (auto dest: map_of_SomeD)
  have expectedTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env expectedTy"
    using "2.prems"(7) lookup by (auto dest: map_of_SomeD)

  \<comment> \<open>Well-kindedness / runtime under accSubst\<close>
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
        using n_in "2.prems"(5) by (auto simp: fmran'I split: option.splits)
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
        using n_in "2.prems"(8) ng by (auto simp: fmran'I split: option.splits)
    qed
  qed
  have actualTy'_wk: "is_well_kinded env ?actualTy'" using actualTy_wk wk_case by blast
  have expectedTy'_wk: "is_well_kinded env ?expectedTy'" using expectedTy_wk wk_case by blast
  have actualTy'_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env ?actualTy'"
    using actualTy_rt rt_case by blast
  have expectedTy'_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env ?expectedTy'"
    using expectedTy_rt rt_case by blast

  show ?case
  proof (cases "unify is_flex ?actualTy' ?expectedTy'")
    case (Some newSubst)
    let ?composedSubst = "compose_subst newSubst accSubst"

    from "2.prems"(1) lookup Some have
      recurse: "unify_update_types is_flex loc rest parentFields ?composedSubst = Inr finalSubst"
      by (simp add: Let_def)

    have newSubst_wk: "\<forall>ty \<in> fmran' newSubst. is_well_kinded env ty"
      using Some actualTy'_wk expectedTy'_wk unify_preserves_well_kinded by blast
    have newSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' newSubst. is_runtime_type env ty)"
      using Some actualTy'_rt expectedTy'_rt unify_preserves_runtime by blast

    have composed_wk: "\<forall>ty \<in> fmran' ?composedSubst. is_well_kinded env ty"
      using newSubst_wk "2.prems"(5) compose_subst_preserves_well_kinded by blast
    have composed_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' ?composedSubst. is_runtime_type env ty)"
      using newSubst_rt "2.prems"(8) compose_subst_preserves_runtime by blast

    have newSubst_dom_flex: "\<forall>n. n |\<in>| fmdom newSubst \<longrightarrow> is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have composed_dom_flex: "\<forall>n. n |\<in>| fmdom ?composedSubst \<longrightarrow> is_flex n"
      using newSubst_dom_flex "2.prems"(9) by (auto simp: compose_subst_def)

    have ih: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
            \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type env ty))
            \<and> (\<exists>theta. finalSubst = compose_subst theta ?composedSubst)
            \<and> list_all (\<lambda>(name, actualTy).
                case map_of parentFields name of
                  Some expectedTy \<Rightarrow>
                    apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
                    \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                       \<and> is_finite_integer_type (apply_subst finalSubst expectedTy))
                | None \<Rightarrow> True) rest
            \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> is_flex n)"
      using "2.IH"(2)[OF lookup refl refl Some] recurse "2.prems"(2) rest_wk "2.prems"(4) composed_wk
            rest_rt "2.prems"(7) composed_rt composed_dom_flex rest_found by simp

    \<comment> \<open>From unify_sound, after applying newSubst the types are equal\<close>
    from unify_sound[OF Some]
    have "apply_subst newSubst ?actualTy' = apply_subst newSubst ?expectedTy'" .
    hence head_eq: "apply_subst ?composedSubst actualTy = apply_subst ?composedSubst expectedTy"
      by (simp add: compose_subst_correct)

    from ih obtain theta where finalSubst_eq: "finalSubst = compose_subst theta ?composedSubst"
      by blast
    have finalSubst_ext: "finalSubst = compose_subst (compose_subst theta newSubst) accSubst"
      using finalSubst_eq by (simp add: compose_subst_assoc)
    hence extends_acc: "\<exists>theta'. finalSubst = compose_subst theta' accSubst" by blast

    have "apply_subst finalSubst actualTy = apply_subst theta (apply_subst ?composedSubst actualTy)"
      using finalSubst_eq by (simp add: compose_subst_correct)
    also have "... = apply_subst theta (apply_subst ?composedSubst expectedTy)"
      using head_eq by simp
    also have "... = apply_subst finalSubst expectedTy"
      using finalSubst_eq by (simp add: compose_subst_correct)
    finally have head_unified: "apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy" .

    show ?thesis using ih extends_acc head_unified lookup by auto
  next
    case None
    from "2.prems"(1) lookup None have
      is_int: "is_finite_integer_type ?actualTy' \<and> is_finite_integer_type ?expectedTy'"
      and recurse: "unify_update_types is_flex loc rest parentFields accSubst = Inr finalSubst"
      by (simp_all add: Let_def split: if_splits)

    have ih: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded env ty)
            \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type env ty))
            \<and> (\<exists>theta. finalSubst = compose_subst theta accSubst)
            \<and> list_all (\<lambda>(name, actualTy).
                case map_of parentFields name of
                  Some expectedTy \<Rightarrow>
                    apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
                    \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                       \<and> is_finite_integer_type (apply_subst finalSubst expectedTy))
                | None \<Rightarrow> True) rest
            \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> is_flex n)"
      using "2.IH"(1)[OF lookup refl refl None is_int] recurse "2.prems"(2) rest_wk "2.prems"(4,5)
            rest_rt "2.prems"(7,8,9) rest_found by simp

    from ih obtain theta where finalSubst_eq: "finalSubst = compose_subst theta accSubst"
      by blast

    \<comment> \<open>Finite integer types have no type variables, so subst is identity on them\<close>
    have actualTy'_no_tyvars: "type_tyvars ?actualTy' = {}"
      using is_int finite_integer_type_is_integer_type integer_type_no_tyvars by blast
    have expectedTy'_no_tyvars: "type_tyvars ?expectedTy' = {}"
      using is_int finite_integer_type_is_integer_type integer_type_no_tyvars by blast

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

    show ?thesis using ih actual_finite expected_finite lookup by auto
  qed
qed

(* Correctness of apply_update_coercions (Phase 2 of record update):
   If input terms have the actual types, and the unification property holds
   (types equal after substitution or both finite integers), then output terms
   have the expected types after substitution. *)
lemma apply_update_coercions_correct:
  assumes "list_all2 (\<lambda>(_, tm) (_, ty). core_term_type env ghost tm = Some ty)
             namedTms namedActualTys"
      and "list_all2 (\<lambda>(name, actualTy) (_, expectedTy).
             apply_subst subst actualTy = apply_subst subst expectedTy
             \<or> (is_finite_integer_type (apply_subst subst actualTy)
                \<and> is_finite_integer_type (apply_subst subst expectedTy)))
           namedActualTys namedExpectedTys"
      and "tyenv_well_formed env"
      and "\<forall>ty \<in> fmran' subst. is_well_kinded env ty"
      and "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' subst. is_runtime_type env ty)"
      and "length namedTms = length namedActualTys"
      and "length namedActualTys = length namedExpectedTys"
      and locals_unaffected:
        "\<And>name ty'. fmlookup (TE_LocalVars env) name = Some ty'
                      \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType env) = TE_ReturnType env"
  shows "list_all2 (\<lambda>(name, tm) (_, expectedTy).
           core_term_type env ghost tm = Some (apply_subst subst expectedTy))
         (apply_update_coercions subst namedTms namedActualTys namedExpectedTys)
         namedExpectedTys"
  using assms
proof (induction subst namedTms namedActualTys namedExpectedTys
       rule: apply_update_coercions.induct)
  case (1 subst)
  then show ?case by simp
next
  case (2 subst name tm rest nameA actualTy actualRest nameE expectedTy expectedRest)
  let ?tm' = "apply_subst_to_term subst tm"
  let ?actualTy' = "apply_subst subst actualTy"
  let ?expectedTy' = "apply_subst subst expectedTy"

  from "2.prems"(1) have
    head_typed: "core_term_type env ghost tm = Some actualTy" and
    tail_typed: "list_all2 (\<lambda>(_, tm) (_, ty). core_term_type env ghost tm = Some ty)
                  rest actualRest"
    by simp_all
  from "2.prems"(2) have
    head_prop: "?actualTy' = ?expectedTy' \<or>
      (is_finite_integer_type ?actualTy' \<and> is_finite_integer_type ?expectedTy')" and
    tail_prop: "list_all2 (\<lambda>(name, actualTy) (_, expectedTy).
                  apply_subst subst actualTy = apply_subst subst expectedTy
                  \<or> (is_finite_integer_type (apply_subst subst actualTy)
                     \<and> is_finite_integer_type (apply_subst subst expectedTy)))
                actualRest expectedRest"
    by simp_all
  from "2.prems"(6,7) have
    len_tms: "length rest = length actualRest" and
    len_tys: "length actualRest = length expectedRest"
    by simp_all

  \<comment> \<open>IH for tail\<close>
  have ih: "list_all2 (\<lambda>(name, tm) (_, expectedTy).
              core_term_type env ghost tm = Some (apply_subst subst expectedTy))
            (apply_update_coercions subst rest actualRest expectedRest) expectedRest"
    using "2.IH" tail_typed tail_prop "2.prems"(3,4,5,8,9) len_tms len_tys by simp

  \<comment> \<open>For the head: apply_subst_to_term preserves typing\<close>
  have head_tm'_typed: "core_term_type env ghost ?tm' = Some ?actualTy'"
    using apply_subst_to_term_preserves_typing[OF head_typed "2.prems"(3,4,5,8,9)] .

  \<comment> \<open>Show the head element has the expected type\<close>
  have head_result: "core_term_type env ghost
                       (if ?actualTy' = ?expectedTy' then ?tm' else CoreTm_Cast ?expectedTy' ?tm')
                     = Some ?expectedTy'"
  proof (cases "?actualTy' = ?expectedTy'")
    case True
    then show ?thesis using head_tm'_typed by simp
  next
    case False
    from head_prop False have
      actual_finite: "is_finite_integer_type ?actualTy'" and
      expected_finite: "is_finite_integer_type ?expectedTy'"
      by simp_all
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

(* Correctness of build_record_update:
   For each field in parentFields, the result term is either a projection from the
   parent (for unchanged fields) or the corresponding update term. In either case,
   it typechecks to the field's type. *)
lemma build_record_update_correct_aux:
  assumes parent_typed: "core_term_type env ghost parentTm = Some (CoreTy_Record allFields)"
      and updates_typed: "\<forall>(name, tm) \<in> set updates.
             \<exists>ty. map_of allFields name = Some ty
                \<and> core_term_type env ghost tm = Some ty"
      and iterFields_subset: "\<forall>(name, ty) \<in> set iterFields. map_of allFields name = Some ty"
  shows "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type env ghost tm = Some ty)
           (build_record_update parentTm iterFields updates) iterFields"
  using iterFields_subset updates_typed parent_typed
proof (induction parentTm iterFields updates rule: build_record_update.induct)
  case (1 parent updates)
  then show ?case by simp
next
  case (2 parent name ty rest updates)
  have name_in: "map_of allFields name = Some ty"
    using "2.prems"(1) by simp
  have rest_subset: "\<forall>(n, t) \<in> set rest. map_of allFields n = Some t"
    using "2.prems"(1) by simp

  show ?case
  proof (cases "map_of updates name")
    case (Some newTm)
    from Some have in_updates: "(name, newTm) \<in> set updates" by (rule map_of_SomeD)
    from "2.prems"(2) in_updates
    have "\<exists>ty'. map_of allFields name = Some ty'
                \<and> core_term_type env ghost newTm = Some ty'"
      by auto
    with name_in have head_typed: "core_term_type env ghost newTm = Some ty" by simp
    have "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type env ghost tm = Some ty)
                     (build_record_update parent rest updates) rest"
      using "2.IH"(2)[OF Some] rest_subset "2.prems"(2,3) by simp
    with head_typed show ?thesis using Some by simp
  next
    case None
    have proj_typed: "core_term_type env ghost (CoreTm_RecordProj parent name) = Some ty"
      using "2.prems"(3) name_in by simp
    have "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type env ghost tm = Some ty)
                     (build_record_update parent rest updates) rest"
      using "2.IH"(1)[OF None] rest_subset "2.prems"(2,3) by simp
    with proj_typed show ?thesis using None by simp
  qed
qed

lemma build_record_update_correct:
  assumes "core_term_type env ghost parentTm = Some (CoreTy_Record parentFields)"
      and "\<forall>(name, tm) \<in> set updates.
             \<exists>ty. map_of parentFields name = Some ty
                \<and> core_term_type env ghost tm = Some ty"
      and "distinct (map fst parentFields)"
  shows "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type env ghost tm = Some ty)
           (build_record_update parentTm parentFields updates) parentFields"
proof -
  have "\<forall>(name, ty) \<in> set parentFields. map_of parentFields name = Some ty"
    using assms(3) by simp
  thus ?thesis using build_record_update_correct_aux[OF assms(1) assms(2)] by simp
qed


(* Helper lemma for BabTm_Call case of elab_term_correct.
   Given that the arg terms are already well-typed in env',
   and the elaboration of the Call succeeds, the result typechecks. *)
lemma elab_term_correct_call:
  assumes
    elab_eq: "elab_term env typedefs ghost (BabTm_Call loc callee args) next_mv
              = Inr (newTm, ty, next_mv')"
    and wf: "tyenv_well_formed env"
    and td_wf: "typedefs_well_formed env typedefs"
    and fresh: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
    \<comment> \<open>Sub-elaboration results\<close>
    and det_call: "determine_fun_call_type env typedefs ghost callee next_mv
                   = Inr (fnName, tyArgs, expArgTypes, retType, next_mv1)"
    and elab_args: "elab_term_list env typedefs ghost args next_mv1
                    = Inr (elabArgTms, actualTypes, next_mv2)"
    \<comment> \<open>IH result lifted to the full extended env\<close>
    and ih_args: "list_all2 (\<lambda>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost tm = Some ty)
                  elabArgTms actualTypes"
  shows "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost newTm = Some ty"
proof -
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"

  from elab_eq det_call have len_args: "length args = length expArgTypes"
    by (auto split: if_splits)
  from elab_eq det_call len_args elab_args obtain finalArgTms finalSubst where
    unify_args: "unify_call_args ?is_flex loc fnName 0 elabArgTms actualTypes expArgTypes fmempty
                 = Inr (finalArgTms, finalSubst)"
    by (auto simp: Let_def split: sum.splits)
  from elab_eq det_call len_args elab_args unify_args have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)
  from elab_eq det_call len_args elab_args unify_args have
    result_eq: "newTm = CoreTm_FunctionCall fnName (map (apply_subst finalSubst) tyArgs) finalArgTms"
               "ty = apply_subst finalSubst retType"
    by (auto simp: Let_def)

  \<comment> \<open>Get function info from determine_fun_call_type_correct\<close>
  have det_correct: "next_mv \<le> next_mv1
       \<and> (\<exists>funInfo.
           fmlookup (TE_Functions env) fnName = Some funInfo
         \<and> (ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost)
         \<and> length tyArgs = length (FI_TyArgs funInfo)
         \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv1)) tyArgs
         \<and> (ghost = NotGhost \<longrightarrow>
              list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv1)) tyArgs)
         \<and> expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                             (FI_TmArgs funInfo)
         \<and> retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                  (FI_ReturnType funInfo))"
    using determine_fun_call_type_correct[OF det_call wf td_wf] .
  from det_correct have mono_1: "next_mv \<le> next_mv1" by blast
  have mono_2: "next_mv1 \<le> next_mv2"
    using elab_term_list_next_mv_monotone[OF elab_args] .
  from det_correct obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyargs_wk_ext: "list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv1)) tyArgs" and
    tyargs_rt_ext: "ghost = NotGhost \<longrightarrow>
                    list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv1)) tyArgs" and
    expArgTypes_eq: "expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                                       (FI_TmArgs funInfo)" and
    retType_eq: "retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                       (FI_ReturnType funInfo)"
    by blast

  \<comment> \<open>Extract unify_call_types result from unify_call_args\<close>
  obtain unifySubst where
    unify_types: "unify_call_types ?is_flex loc fnName 0 actualTypes expArgTypes fmempty = Inr unifySubst" and
    finalArgTms_eq: "finalArgTms = apply_call_coercions unifySubst elabArgTms actualTypes expArgTypes" and
    finalSubst_eq: "finalSubst = unifySubst"
  proof -
    from unify_args show ?thesis
      by (auto simp: unify_call_args_def split: sum.splits intro: that)
  qed

  have len_elabArgTms: "length elabArgTms = length actualTypes"
    using ih_args by (simp add: list_all2_lengthD)
  have len_actualTypes: "length actualTypes = length expArgTypes"
    using len_args elab_args by (simp add: elab_term_list_length)

  have wf': "tyenv_well_formed ?env'"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>Well-kindedness and runtime for actualTypes and expArgTypes in ?env'\<close>
  have actualTypes_wk: "list_all (is_well_kinded ?env') actualTypes"
  proof (simp add: list_all_length, intro allI impI)
    fix i assume "i < length actualTypes"
    with ih_args have "core_term_type ?env' ghost (elabArgTms ! i) = Some (actualTypes ! i)"
      by (simp add: list_all2_conv_all_nth)
    thus "is_well_kinded ?env' (actualTypes ! i)"
      using wf' core_term_type_well_kinded by blast
  qed
  have actualTypes_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') actualTypes"
    using ih_args wf' core_term_type_notghost_runtime
    by (auto simp: list_all2_conv_all_nth list_all_length)

  have tyargs_wk: "list_all (is_well_kinded ?env') tyArgs"
    using tyargs_wk_ext is_well_kinded_extend_env_with_tyvars_mono[where lo=next_mv and hi=next_mv1
                                                                        and lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by (fastforce simp: list_all_iff)
  have tyargs_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') tyArgs"
    using tyargs_rt_ext is_runtime_type_extend_env_with_tyvars_mono[where lo=next_mv and hi=next_mv1
                                                                         and lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by (fastforce simp: list_all_iff)

  have fn_lookup': "fmlookup (TE_Functions ?env') fnName = Some funInfo"
    using fn_lookup by (simp add: extend_env_with_tyvars_def)
  have "tyenv_fun_types_well_kinded ?env'"
    using wf' tyenv_well_formed_def by blast
  hence fi_args_wk_inner: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo).
            is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) ty"
    using fn_lookup' tyenv_fun_types_well_kinded_def by blast

  have expArgTypes_wk: "list_all (is_well_kinded ?env') expArgTypes"
  proof -
    have "list_all (\<lambda>(_, ty, _). is_well_kinded ?env' (apply_subst
            (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)) (FI_TmArgs funInfo)"
    proof (unfold list_all_iff, intro ballI, clarify)
      fix n t v assume tv_in: "(n, t, v) \<in> set (FI_TmArgs funInfo)"
      hence t_in: "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)" by (force simp: rev_image_eqI)
      from t_in fi_args_wk_inner
      have t_wk: "is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t" by blast
      show "is_well_kinded ?env' (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) t)"
        using apply_subst_specializes_well_kinded[OF t_wk tyargs_wk len_tyargs[symmetric]] .
    qed
    thus ?thesis using expArgTypes_eq by (auto simp: list_all_iff)
  qed

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
    have tyargs_rt': "list_all (is_runtime_type ?env') tyArgs" using tyargs_rt ng by simp
    have "list_all (\<lambda>(_, ty, _). is_runtime_type ?env' (apply_subst
            (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)) (FI_TmArgs funInfo)"
    proof (unfold list_all_iff, intro ballI, clarify)
      fix n t v assume tv_in: "(n, t, v) \<in> set (FI_TmArgs funInfo)"
      hence t_in: "t \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)" by (force simp: rev_image_eqI)
      from t_in fi_args_rt_inner[OF fg_ng]
      have t_rt: "is_runtime_type (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                             TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) t" by blast
      show "is_runtime_type ?env' (apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) t)"
        using apply_subst_specializes_runtime[OF t_rt tyargs_rt' len_tyargs[symmetric]] .
    qed
    thus "list_all (is_runtime_type ?env') expArgTypes"
      using expArgTypes_eq by (auto simp: list_all_iff)
  qed

  \<comment> \<open>Apply unify_call_types_correct in the extended env ?env'\<close>
  have empty_dom_flex: "\<forall>n. n |\<in>| fmdom (fmempty :: (nat, CoreType) fmap) \<longrightarrow> ?is_flex n"
    by simp
  have unify_correct: "(\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty))
       \<and> (\<exists>theta. finalSubst = compose_subst theta fmempty)
       \<and> list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
              \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
         actualTypes expArgTypes
       \<and> (\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n)"
    using unify_call_types_correct[OF unify_types wf' len_actualTypes
            actualTypes_wk expArgTypes_wk _ actualTypes_rt expArgTypes_rt _ empty_dom_flex]
          finalSubst_eq by fastforce

  from unify_correct have
    finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty" and
    finalSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty)" and
    types_unified: "list_all2 (\<lambda>actualTy expectedTy.
           apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
           \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
              \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
         actualTypes expArgTypes" and
    finalSubst_dom_flex: "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n"
    by blast+

  have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
    unfolding extend_env_with_tyvars_def by simp
  have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
    unfolding extend_env_with_tyvars_def by simp
  from flex_subst_identity_on_env[OF finalSubst_dom_flex wf env'_locals env'_ret]
  have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                                      \<Longrightarrow> apply_subst finalSubst ty' = ty'"
    and ret_unaffected: "apply_subst finalSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
    by blast+

  have coerce_correct: "list_all2 (\<lambda>tm expectedTy.
           core_term_type ?env' ghost tm = Some (apply_subst finalSubst expectedTy))
         finalArgTms expArgTypes"
    using apply_call_coercions_correct[OF ih_args types_unified wf'
            finalSubst_wk finalSubst_rt len_elabArgTms len_actualTypes
            locals_unaffected ret_unaffected]
          finalArgTms_eq finalSubst_eq by simp

  let ?finalTyArgs = "map (apply_subst finalSubst) tyArgs"

  have finalTyArgs_wk: "list_all (is_well_kinded ?env') ?finalTyArgs"
  proof (unfold list_all_iff, intro ballI, simp only: set_map)
    fix ty assume "ty \<in> apply_subst finalSubst ` set tyArgs"
    then obtain ty0 where ty0_in: "ty0 \<in> set tyArgs" and ty_eq: "ty = apply_subst finalSubst ty0" by auto
    from ty0_in tyargs_wk have ty0_wk: "is_well_kinded ?env' ty0" by (simp add: list_all_iff)
    have "is_well_kinded ?env' (apply_subst finalSubst ty0)"
    proof (rule apply_subst_preserves_well_kinded[OF ty0_wk])
      show "TE_Datatypes ?env' = TE_Datatypes ?env'" by simp
    next
      fix n assume n_in: "n |\<in>| TE_TypeVars ?env'"
      show "case fmlookup finalSubst n of
              Some ty' \<Rightarrow> is_well_kinded ?env' ty'
            | None \<Rightarrow> n |\<in>| TE_TypeVars ?env'"
        using n_in finalSubst_wk by (auto simp: fmran'I split: option.splits)
    qed
    thus "is_well_kinded ?env' ty" using ty_eq by simp
  qed

  have finalTyArgs_rt: "ghost = NotGhost \<longrightarrow> list_all (is_runtime_type ?env') ?finalTyArgs"
  proof
    assume ng: "ghost = NotGhost"
    show "list_all (is_runtime_type ?env') ?finalTyArgs"
    proof (unfold list_all_iff, intro ballI, simp only: set_map)
      fix ty assume "ty \<in> apply_subst finalSubst ` set tyArgs"
      then obtain ty0 where ty0_in: "ty0 \<in> set tyArgs" and ty_eq: "ty = apply_subst finalSubst ty0" by auto
      from ty0_in tyargs_rt ng have ty0_rt: "is_runtime_type ?env' ty0" by (simp add: list_all_iff)
      have "is_runtime_type ?env' (apply_subst finalSubst ty0)"
      proof (rule apply_subst_preserves_runtime[OF ty0_rt])
        show "TE_GhostDatatypes ?env' = TE_GhostDatatypes ?env'" by simp
      next
        fix n assume n_in: "n |\<in>| TE_RuntimeTypeVars ?env'"
        show "case fmlookup finalSubst n of
                Some ty' \<Rightarrow> is_runtime_type ?env' ty'
              | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars ?env'"
          using n_in finalSubst_rt ng by (auto simp: fmran'I split: option.splits)
      qed
      thus "is_runtime_type ?env' ty" using ty_eq by simp
    qed
  qed

  have len_finalTyArgs: "length ?finalTyArgs = length (FI_TyArgs funInfo)"
    using len_tyargs by simp

  let ?coreTySubst = "fmap_of_list (zip (FI_TyArgs funInfo) ?finalTyArgs)"
  let ?coreExpArgTypes = "map (\<lambda>(_, ty, _). apply_subst ?coreTySubst ty) (FI_TmArgs funInfo)"

  have fi_args_tyvars: "\<forall>ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo). type_tyvars ty \<subseteq> set (FI_TyArgs funInfo)"
  proof
    fix ty assume ty_in: "ty \<in> (fst \<circ> snd) ` set (FI_TmArgs funInfo)"
    from ty_in fi_args_wk_inner
    have ty_wk: "is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>) ty"
      by blast
    have "type_tyvars ty \<subseteq> fset (TE_TypeVars (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>))"
      using is_well_kinded_type_tyvars_subset[OF ty_wk] .
    thus "type_tyvars ty \<subseteq> set (FI_TyArgs funInfo)" by (simp add: fset_of_list.rep_eq)
  qed

  have "tyenv_fun_tyvars_distinct env"
    using wf tyenv_well_formed_def by blast
  hence fi_tyargs_distinct: "distinct (FI_TyArgs funInfo)"
    using fn_lookup tyenv_fun_tyvars_distinct_def by blast

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
           case core_term_type ?env' ghost tm of
             None \<Rightarrow> False
           | Some actualTy \<Rightarrow> actualTy = expectedTy)
         finalArgTms ?coreExpArgTypes"
  proof -
    have "list_all2 (\<lambda>tm expectedTy.
             core_term_type ?env' ghost tm = Some expectedTy)
           finalArgTms (map (apply_subst finalSubst) expArgTypes)"
      using coerce_correct by (simp add: list_all2_conv_all_nth)
    thus ?thesis
      using core_exp_eq by (simp add: list_all2_conv_all_nth)
  qed

  have len_finalArgTms: "length finalArgTms = length (FI_TmArgs funInfo)"
    using coerce_correct expArgTypes_eq by (simp add: list_all2_lengthD)

  have fi_ret_tyvars: "type_tyvars (FI_ReturnType funInfo) \<subseteq> set (FI_TyArgs funInfo)"
  proof -
    have "tyenv_fun_types_well_kinded ?env'"
      using wf' tyenv_well_formed_def by blast
    hence ret_wk: "is_well_kinded (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                                  (FI_ReturnType funInfo)"
      using fn_lookup' tyenv_fun_types_well_kinded_def by blast
    have "type_tyvars (FI_ReturnType funInfo) \<subseteq>
          fset (TE_TypeVars (?env' \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>))"
      using is_well_kinded_type_tyvars_subset[OF ret_wk] .
    thus ?thesis by (simp add: fset_of_list.rep_eq)
  qed
  have ret_eq: "ty = apply_subst ?coreTySubst (FI_ReturnType funInfo)"
    using result_eq retType_eq len_tyargs fi_ret_tyvars fi_tyargs_distinct
    by (simp add: apply_subst_compose_zip)

  show ?thesis
    using result_eq fn_lookup ghost_ok len_finalTyArgs finalTyArgs_wk finalTyArgs_rt
          len_finalArgTms args_match ret_eq
    sorry \<comment> \<open>TODO: need to show function is pure (all Var args, not impure);
             requires elaborator to check FI_Impure and Var/Ref status\<close>
qed

(* Helper lemma for BabTm_RecordUpdate case of elab_term_correct.
   Given that the parent and update sub-terms are already well-typed in env',
   and the elaboration of the RecordUpdate succeeds, the result typechecks. *)
lemma elab_term_correct_record_update:
  assumes
    elab_eq: "elab_term env typedefs ghost (BabTm_RecordUpdate loc tm flds) next_mv
              = Inr (newTm, ty, next_mv')"
    and wf: "tyenv_well_formed env"
    and fresh: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv"
    \<comment> \<open>Sub-elaboration results\<close>
    and elab_parent: "elab_term env typedefs ghost tm next_mv = Inr (parentTm, parentTy, next_mv1)"
    and elab_updates: "elab_term_list env typedefs ghost (map snd flds) next_mv1
                       = Inr (newUpdateTms, actualTypes, next_mv2)"
    \<comment> \<open>IH results lifted to the full extended env\<close>
    and ih_parent: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost parentTm
                    = Some parentTy"
    and ih_updates: "list_all2 (\<lambda>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost tm = Some ty)
                     newUpdateTms actualTypes"
  shows "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost newTm = Some ty"
proof -
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"

  \<comment> \<open>Extract elaboration sub-results from elab_eq\<close>
  from elab_eq have no_dup: "first_duplicate_name fst flds = None"
    by (auto split: option.splits)
  from elab_eq no_dup elab_parent obtain parentFields where
    parent_rec: "parentTy = CoreTy_Record parentFields"
    by (auto simp: Let_def unify_update_args_def build_updated_record_def
             split: sum.splits CoreType.splits option.splits if_splits prod.splits)
  from elab_eq no_dup elab_parent parent_rec have
    fields_exist: "check_update_fields_exist flds parentFields = None"
    by (auto simp: Let_def unify_update_args_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  from elab_eq no_dup elab_parent parent_rec fields_exist elab_updates
  obtain coercedUpdates finalSubst where
    unify_result: "unify_update_args ?is_flex loc (map fst flds) newUpdateTms actualTypes parentFields
                   = Inr (coercedUpdates, finalSubst)"
    by (auto simp: Let_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  from elab_eq no_dup elab_parent parent_rec fields_exist elab_updates unify_result
  have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: Let_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  from elab_eq no_dup elab_parent parent_rec fields_exist elab_updates unify_result
  have result_eq:
    "newTm = fst (build_updated_record finalSubst parentTm parentFields coercedUpdates)"
    "ty = snd (build_updated_record finalSubst parentTm parentFields coercedUpdates)"
    by (auto simp: Let_def split: prod.splits)

  \<comment> \<open>Specialize IH results to parentFields\<close>
  have ih_parent': "core_term_type ?env' ghost parentTm = Some (CoreTy_Record parentFields)"
    using ih_parent parent_rec by simp

  have wf': "tyenv_well_formed ?env'"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>Lengths\<close>
  have len_updates: "length newUpdateTms = length actualTypes"
    using ih_updates by (simp add: list_all2_lengthD)
  have len_flds: "length newUpdateTms = length flds"
    using elab_updates elab_term_list_length by fastforce
  have len_flds_actual: "length flds = length actualTypes"
    using len_flds len_updates by simp

  \<comment> \<open>Well-kindedness and runtime for actualTypes in ?env'\<close>
  have actualTypes_wk: "\<forall>(name, ty) \<in> set (zip (map fst flds) actualTypes). is_well_kinded ?env' ty"
  proof (clarsimp)
    fix name ty assume "(name, ty) \<in> set (zip (map fst flds) actualTypes)"
    then obtain i where i_lt: "i < length actualTypes" and ty_eq: "ty = actualTypes ! i"
      using len_flds by (auto simp: set_zip in_set_conv_nth)
    from ih_updates have "core_term_type ?env' ghost (newUpdateTms ! i) = Some ty"
      using i_lt len_updates ty_eq by (simp add: list_all2_conv_all_nth)
    thus "is_well_kinded ?env' ty"
      using core_term_type_well_kinded wf' by blast
  qed

  have actualTypes_rt: "ghost = NotGhost \<longrightarrow>
      (\<forall>(name, ty) \<in> set (zip (map fst flds) actualTypes). is_runtime_type ?env' ty)"
  proof (intro impI)
    assume ng: "ghost = NotGhost"
    show "\<forall>(name, ty) \<in> set (zip (map fst flds) actualTypes). is_runtime_type ?env' ty"
    proof (clarsimp)
      fix name ty assume in_zip: "(name, ty) \<in> set (zip (map fst flds) actualTypes)"
      then obtain i where i_lt: "i < length actualTypes" and ty_eq: "ty = actualTypes ! i"
        using len_flds by (auto simp: set_zip in_set_conv_nth)
      from ih_updates have "core_term_type ?env' ghost (newUpdateTms ! i) = Some ty"
        using i_lt len_updates ty_eq by (simp add: list_all2_conv_all_nth)
      thus "is_runtime_type ?env' ty"
        using core_term_type_notghost_runtime ng wf' by auto
    qed
  qed

  \<comment> \<open>Well-kindedness and runtime for parentFields in ?env'\<close>
  have parent_ty_wk: "is_well_kinded ?env' (CoreTy_Record parentFields)"
    using core_term_type_well_kinded[OF ih_parent' wf'] .
  hence parentFields_wk: "\<forall>(name, ty) \<in> set parentFields. is_well_kinded ?env' ty"
    by (auto simp: list_all_iff)

  have parentFields_rt: "ghost = NotGhost \<longrightarrow>
      (\<forall>(name, ty) \<in> set parentFields. is_runtime_type ?env' ty)"
  proof (intro impI)
    assume ng: "ghost = NotGhost"
    have "is_runtime_type ?env' (CoreTy_Record parentFields)"
      using core_term_type_notghost_runtime[OF _ wf'] ih_parent' ng by blast
    thus "\<forall>(n, t) \<in> set parentFields. is_runtime_type ?env' t"
      by (auto simp: list_all_iff)
  qed

  \<comment> \<open>Extract unify_update_types result from unify_update_args\<close>
  obtain unifySubst where
    unify_types: "unify_update_types ?is_flex loc (zip (map fst flds) actualTypes) parentFields fmempty
                  = Inr unifySubst" and
    coercedUpdates_eq: "coercedUpdates = apply_update_coercions unifySubst
        (zip (map fst flds) newUpdateTms) (zip (map fst flds) actualTypes)
        (zip (map fst flds) (map (\<lambda>n. case map_of parentFields n of Some ty \<Rightarrow> ty) (map fst flds)))" and
    finalSubst_eq: "finalSubst = unifySubst"
  proof -
    from unify_result show ?thesis
      by (auto simp: unify_update_args_def Let_def split: sum.splits intro: that)
  qed

  \<comment> \<open>All update field names exist in parentFields\<close>
  have flds_found: "\<forall>(name, _) \<in> set flds. map_of parentFields name \<noteq> None"
    using check_update_fields_exist_sound[OF fields_exist] .
  have updates_found: "\<forall>(name, _) \<in> set (zip (map fst flds) actualTypes).
                         map_of parentFields name \<noteq> None"
  proof (clarsimp simp: set_zip)
    fix i assume i_lt1: "i < length flds" and i_lt2: "i < length actualTypes"
    have "(flds ! i) \<in> set flds" using i_lt1 by simp
    with flds_found have "map_of parentFields (fst (flds ! i)) \<noteq> None"
      by (cases "flds ! i") auto
    thus "\<exists>y. map_of parentFields (fst (flds ! i)) = Some y"
      by auto
  qed

  \<comment> \<open>Apply unify_update_types_correct\<close>
  have empty_wk: "\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_well_kinded ?env' ty"
    by (simp add: fmran'_def)
  have empty_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' (fmempty :: TypeSubst). is_runtime_type ?env' ty)"
    by (simp add: fmran'_def)
  have empty_dom: "\<forall>n. n |\<in>| fmdom (fmempty :: TypeSubst) \<longrightarrow> ?is_flex n" by simp

  have unify_correct: "(\<forall>ty \<in> fmran' unifySubst. is_well_kinded ?env' ty)
       \<and> (ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' unifySubst. is_runtime_type ?env' ty))
       \<and> list_all (\<lambda>(name, actualTy).
           case map_of parentFields name of
             Some expectedTy \<Rightarrow>
               apply_subst unifySubst actualTy = apply_subst unifySubst expectedTy
               \<or> (is_finite_integer_type (apply_subst unifySubst actualTy)
                  \<and> is_finite_integer_type (apply_subst unifySubst expectedTy))
           | None \<Rightarrow> True)
         (zip (map fst flds) actualTypes)
       \<and> (\<forall>n. n |\<in>| fmdom unifySubst \<longrightarrow> ?is_flex n)"
    using unify_update_types_correct[OF unify_types
            wf' actualTypes_wk parentFields_wk empty_wk actualTypes_rt parentFields_rt
            empty_rt empty_dom updates_found] by blast

  have finalSubst_wk: "\<forall>ty \<in> fmran' finalSubst. is_well_kinded ?env' ty"
    using unify_correct finalSubst_eq by simp
  have finalSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' finalSubst. is_runtime_type ?env' ty)"
    using unify_correct finalSubst_eq by simp
  have finalSubst_dom_flex: "\<forall>n. n |\<in>| fmdom finalSubst \<longrightarrow> ?is_flex n"
    using unify_correct finalSubst_eq by simp

  \<comment> \<open>Subst doesn't affect locals or return type\<close>
  have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
    unfolding extend_env_with_tyvars_def by simp
  have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
    unfolding extend_env_with_tyvars_def by simp
  from flex_subst_identity_on_env[OF finalSubst_dom_flex wf env'_locals env'_ret]
  have locals_unaffected: "\<And>vname vty. fmlookup (TE_LocalVars ?env') vname = Some vty
                                       \<Longrightarrow> apply_subst finalSubst vty = vty"
    and ret_unaffected: "apply_subst finalSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
    by blast+

  \<comment> \<open>Parent term after substitution\<close>
  let ?finalParentTm = "apply_subst_to_term finalSubst parentTm"
  let ?finalParentFields = "map (\<lambda>(n, ty). (n, apply_subst finalSubst ty)) parentFields"

  have finalParent_typed: "core_term_type ?env' ghost ?finalParentTm
                           = Some (CoreTy_Record ?finalParentFields)"
  proof -
    have "core_term_type ?env' ghost ?finalParentTm
          = Some (apply_subst finalSubst (CoreTy_Record parentFields))"
      using apply_subst_to_term_preserves_typing
              [OF ih_parent' wf' finalSubst_wk finalSubst_rt locals_unaffected ret_unaffected] .
    also have "apply_subst finalSubst (CoreTy_Record parentFields)
              = CoreTy_Record ?finalParentFields"
      by simp
    finally show ?thesis .
  qed

  \<comment> \<open>Distinctness of parent field names\<close>
  have distinct_parent: "distinct (map fst parentFields)"
    using parent_ty_wk by simp
  have fst_final_eq: "map fst ?finalParentFields = map fst parentFields"
    by (induction parentFields) auto
  have distinct_final: "distinct (map fst ?finalParentFields)"
    using distinct_parent fst_final_eq by metis

  \<comment> \<open>Convert list_all unification property to list_all2\<close>
  let ?namedTms = "zip (map fst flds) newUpdateTms"
  let ?namedActualTys = "zip (map fst flds) actualTypes"
  let ?namedExpectedTys = "zip (map fst flds) (map (\<lambda>n. case map_of parentFields n of Some ty \<Rightarrow> ty) (map fst flds))"

  have ih_named_tms: "list_all2 (\<lambda>(_, tm) (_, ty). core_term_type ?env' ghost tm = Some ty)
                        ?namedTms ?namedActualTys"
    using ih_updates len_updates len_flds
    by (auto simp: list_all2_conv_all_nth)

  have unify_list_all: "list_all (\<lambda>(name, actualTy).
           case map_of parentFields name of
             Some expectedTy \<Rightarrow>
               apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
               \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                  \<and> is_finite_integer_type (apply_subst finalSubst expectedTy))
           | None \<Rightarrow> True)
         (zip (map fst flds) actualTypes)"
    using unify_correct finalSubst_eq by blast

  have types_unified: "list_all2 (\<lambda>(name, actualTy) (_, expectedTy).
             apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
             \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
           ?namedActualTys ?namedExpectedTys"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length ?namedActualTys = length ?namedExpectedTys"
      using len_flds_actual by simp
  next
    fix i assume i_lt: "i < length ?namedActualTys"
    hence i_flds: "i < length flds" using len_flds_actual by simp
    have nth_actual: "?namedActualTys ! i = (map fst flds ! i, actualTypes ! i)"
      using i_flds len_flds_actual by simp
    have nth_expected: "?namedExpectedTys ! i =
      (map fst flds ! i, (case map_of parentFields (map fst flds ! i) of Some ty \<Rightarrow> ty))"
      using i_flds by simp
    from unify_list_all have
      "\<And>j. j < length (zip (map fst flds) actualTypes) \<Longrightarrow>
        (case (zip (map fst flds) actualTypes) ! j of (name, actualTy) \<Rightarrow>
           (case map_of parentFields name of
             Some expectedTy \<Rightarrow>
               apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
               \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                  \<and> is_finite_integer_type (apply_subst finalSubst expectedTy))
           | None \<Rightarrow> True))"
      by (simp add: list_all_length)
    from this[of i] have case_split: "case map_of parentFields (map fst flds ! i) of
             Some expectedTy \<Rightarrow>
               apply_subst finalSubst (actualTypes ! i) = apply_subst finalSubst expectedTy
               \<or> (is_finite_integer_type (apply_subst finalSubst (actualTypes ! i))
                  \<and> is_finite_integer_type (apply_subst finalSubst expectedTy))
           | None \<Rightarrow> True"
      using i_flds len_flds_actual by simp
    from flds_found i_flds have "map_of parentFields (fst (flds ! i)) \<noteq> None"
      by (metis (mono_tags, lifting) case_prod_beta in_set_conv_nth)
    then obtain ety where ety: "map_of parentFields (map fst flds ! i) = Some ety"
      using i_flds by auto
    from case_split ety have
      "apply_subst finalSubst (actualTypes ! i) = apply_subst finalSubst ety
       \<or> (is_finite_integer_type (apply_subst finalSubst (actualTypes ! i))
          \<and> is_finite_integer_type (apply_subst finalSubst ety))"
      by simp
    thus "(case ?namedActualTys ! i of (name, actualTy) \<Rightarrow> \<lambda>(_, expectedTy).
             apply_subst finalSubst actualTy = apply_subst finalSubst expectedTy
             \<or> (is_finite_integer_type (apply_subst finalSubst actualTy)
                \<and> is_finite_integer_type (apply_subst finalSubst expectedTy)))
          (?namedExpectedTys ! i)"
      using nth_actual nth_expected ety by simp
  qed

  have len_namedTms: "length ?namedTms = length ?namedActualTys" using len_updates by simp
  have len_namedTys: "length ?namedActualTys = length ?namedExpectedTys"
    using len_flds_actual by simp

  \<comment> \<open>Apply apply_update_coercions_correct\<close>
  have coerced_typed: "list_all2 (\<lambda>(name, tm) (_, expectedTy).
           core_term_type ?env' ghost tm = Some (apply_subst finalSubst expectedTy))
         coercedUpdates ?namedExpectedTys"
    using apply_update_coercions_correct[OF ih_named_tms types_unified wf'
            finalSubst_wk finalSubst_rt len_namedTms len_namedTys
            locals_unaffected ret_unaffected]
          coercedUpdates_eq finalSubst_eq by simp

  \<comment> \<open>map_of on finalParentFields gives apply_subst finalSubst of the original\<close>
  have map_of_final: "\<And>n ty. map_of parentFields n = Some ty \<Longrightarrow>
                              map_of ?finalParentFields n = Some (apply_subst finalSubst ty)"
    using distinct_parent by (induction parentFields) (auto split: if_splits)

  \<comment> \<open>Each coerced update term has the right type for build_record_update_correct\<close>
  have coerced_updates_for_build: "\<forall>(name, tm) \<in> set coercedUpdates.
         \<exists>ty. map_of ?finalParentFields name = Some ty
            \<and> core_term_type ?env' ghost tm = Some ty"
  proof (clarsimp)
    fix name tm assume in_set: "(name, tm) \<in> set coercedUpdates"
    from coerced_typed have len_coerced: "length coercedUpdates = length ?namedExpectedTys"
      by (simp add: list_all2_lengthD)
    from in_set obtain j where j_lt: "j < length coercedUpdates"
      and j_eq: "coercedUpdates ! j = (name, tm)"
      by (auto simp: in_set_conv_nth)
    from coerced_typed j_lt have
      "(case coercedUpdates ! j of (name, tm) \<Rightarrow> \<lambda>(_, expectedTy).
         core_term_type ?env' ghost tm = Some (apply_subst finalSubst expectedTy))
       (?namedExpectedTys ! j)"
      by (meson list_all2_nthD)
    with j_eq have "core_term_type ?env' ghost tm =
      Some (apply_subst finalSubst (snd (?namedExpectedTys ! j)))"
      by (auto split: prod.splits)
    moreover have "snd (?namedExpectedTys ! j) =
      (case map_of parentFields (map fst flds ! j) of Some ty \<Rightarrow> ty)"
      using j_lt len_coerced len_flds_actual by simp
    moreover have "name = map fst flds ! j"
    proof -
      have "map fst coercedUpdates = map fst ?namedTms"
        using apply_update_coercions_map_fst[of ?namedTms ?namedActualTys ?namedExpectedTys]
              len_updates len_flds_actual coercedUpdates_eq finalSubst_eq by simp
      hence "fst (coercedUpdates ! j) = fst (?namedTms ! j)"
        using j_lt by (simp add: map_equality_iff)
      with j_eq show ?thesis using j_lt len_coerced len_flds_actual len_updates by simp
    qed
    moreover have "map_of parentFields (fst (flds ! j)) \<noteq> None"
    proof -
      have "(flds ! j) \<in> set flds" using j_lt len_coerced len_flds_actual by simp
      with flds_found show ?thesis by (cases "flds ! j") auto
    qed
    then obtain ety where "map_of parentFields (map fst flds ! j) = Some ety"
      using j_lt len_coerced len_flds_actual by auto
    ultimately have "core_term_type ?env' ghost tm = Some (apply_subst finalSubst ety)"
      by simp
    moreover have "map_of ?finalParentFields name = Some (apply_subst finalSubst ety)"
      using map_of_final \<open>map_of parentFields (map fst flds ! j) = Some ety\<close>
            \<open>name = map fst flds ! j\<close> by simp
    ultimately show "\<exists>ty. map_of ?finalParentFields name = Some ty
                        \<and> core_term_type ?env' ghost tm = Some ty"
      by blast
  qed

  \<comment> \<open>Apply build_record_update_correct\<close>
  let ?resultFlds = "build_record_update ?finalParentTm ?finalParentFields coercedUpdates"

  have result_typed: "list_all2 (\<lambda>(name, tm) (_, ty). core_term_type ?env' ghost tm = Some ty)
           ?resultFlds ?finalParentFields"
    using build_record_update_correct[OF finalParent_typed coerced_updates_for_build distinct_final] .

  \<comment> \<open>Field names of resultFlds match finalParentFields\<close>
  have fst_result: "map fst ?resultFlds = map fst ?finalParentFields"
    using build_record_update_map_fst fst_final_eq by simp
  have distinct_result: "distinct (map fst ?resultFlds)"
    using distinct_final fst_result by simp
  have len_result: "length ?resultFlds = length ?finalParentFields"
    using build_record_update_length by simp

  \<comment> \<open>Build the 'those' fact from result_typed\<close>
  have those_ok: "those (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds)
                  = Some (map snd ?finalParentFields)"
  proof -
    have "list_all2 (\<lambda>x y. x = Some y)
            (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds)
            (map snd ?finalParentFields)"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds)
            = length (map snd ?finalParentFields)"
        using len_result by simp
    next
      fix i assume i_lt: "i < length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds)"
      hence i_flds: "i < length ?finalParentFields" using len_result by simp
      from result_typed have "(case ?resultFlds ! i of (name, tm) \<Rightarrow> \<lambda>(_, ty).
              core_term_type ?env' ghost tm = Some ty)
            (?finalParentFields ! i)"
        using i_flds
        by (meson list_all2_nthD2)
      thus "map (\<lambda>(name, tm). core_term_type ?env' ghost tm) ?resultFlds ! i
            = Some (map snd ?finalParentFields ! i)"
        using i_flds len_result by (auto split: prod.splits)
    qed
    thus ?thesis by (simp add: those_eq_Some)
  qed

  \<comment> \<open>The zip of names and types reconstructs finalParentFields\<close>
  have zip_reconstruct: "zip (map fst ?resultFlds) (map snd ?finalParentFields) = ?finalParentFields"
    using fst_result
    by (metis zip_map_fst_snd)

  \<comment> \<open>core_term_type of the CoreTm_Record\<close>
  have "core_term_type ?env' ghost (CoreTm_Record ?resultFlds) = Some (CoreTy_Record ?finalParentFields)"
    using distinct_result those_ok zip_reconstruct by simp

  thus ?thesis using result_eq
    by (simp add: build_updated_record_def Let_def)
qed


(* ========================================================================== *)
(* Main correctness theorem *)
(* ========================================================================== *)

(* Correctness theorem for elab_term and elab_term_list.
   If elaboration succeeds, the resulting term(s) are well-typed in env extended
   with the fresh metavariables introduced during elaboration (the interval
   [next_mv ..< next_mv']).

   The freshness precondition (fourth assumption) says that next_mv is strictly
   greater than every type variable already in env. This ensures that the fresh
   metas the elaborator generates don't collide with existing ones. *)
theorem elab_term_correct:
  "elab_term env typedefs ghost tm next_mv = Inr (newTm, ty, next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   typedefs_well_formed env typedefs \<Longrightarrow>
   (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv) \<Longrightarrow>
   core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost newTm = Some ty"
and elab_term_list_correct:
  "elab_term_list env typedefs ghost tms next_mv = Inr (newTms, tys, next_mv') \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   typedefs_well_formed env typedefs \<Longrightarrow>
   (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv) \<Longrightarrow>
   list_all2 (\<lambda>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv next_mv') ghost tm = Some ty) newTms tys"
proof (induction env typedefs ghost tm next_mv and env typedefs ghost tms next_mv
       arbitrary: newTm ty next_mv' and newTms tys next_mv'
       rule: elab_term_elab_term_list.induct)
  \<comment> \<open>Case: BabTm_Literal\<close>
  case (1 env typedefs ghost loc lit next_mv)
  show ?case
  proof (cases lit)
    case (BabLit_Bool b)
    with "1.prems"(1) have "newTm = CoreTm_LitBool b" and "ty = CoreTy_Bool"
      by auto
    thus ?thesis by simp
  next
    case (BabLit_Int i)
    with "1.prems"(1) obtain sign bits where
      get_type: "get_type_for_int i = Some (sign, bits)" and
      newTm_eq: "newTm = CoreTm_LitInt i" and
      ty_eq: "ty = CoreTy_FiniteInt sign bits"
      by (auto split: option.splits)
    thus ?thesis using get_type by simp
  next
    (* TODO *)
    case (BabLit_String x3)
    then show ?thesis sorry
  next
    (* TODO *)
    case (BabLit_Array x4)
    then show ?thesis sorry
  qed
next
  \<comment> \<open>Case: BabTm_Name (undefined)\<close>
  case (2 env typedefs ghost loc name tyArgs next_mv)
  then show ?case sorry

next
  \<comment> \<open>Case: BabTm_Cast\<close>
  case (3 env typedefs ghost loc targetTy operand next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract intermediate results\<close>
  from "3.prems"(1) obtain newTargetTy where
    elab_target: "elab_type env typedefs ghost targetTy = Inr newTargetTy"
    by (auto split: sum.splits)
  from "3.prems"(1) elab_target obtain newOperand operandTy next_mv'' where
    elab_operand: "elab_term env typedefs ghost operand next_mv = Inr (newOperand, operandTy, next_mv'')"
    by (auto split: sum.splits)
  \<comment> \<open>Cast forwards the operand's next_mv, so next_mv' = next_mv''\<close>
  from "3.prems"(1) elab_target elab_operand have next_mv_eq: "next_mv' = next_mv''"
    by (auto split: if_splits option.splits)
  from "3.prems"(1) elab_target elab_operand have
    target_is_int: "is_integer_type newTargetTy"
    by (auto split: if_splits)

  \<comment> \<open>IH: operand has its type in the extended env\<close>
  have ih: "core_term_type ?env' ghost newOperand = Some operandTy"
    by (simp add: "3.IH" "3.prems"(2,3,4) elab_operand elab_target next_mv_eq)

  \<comment> \<open>Target type is well-kinded / runtime in the original env and so also in ?env'\<close>
  have target_wk_env: "is_well_kinded env newTargetTy"
    using elab_target "3.prems"(2,3) elab_type_is_well_kinded by simp
  have target_rt_env: "ghost = NotGhost \<longrightarrow> is_runtime_type env newTargetTy"
    using elab_target "3.prems"(2,3) elab_type_notghost_is_runtime by (cases ghost) auto
  have target_wk: "is_well_kinded ?env' newTargetTy"
    using target_wk_env is_well_kinded_extend_tyvars
    unfolding extend_env_with_tyvars_def
    by (simp add: is_integer_type_well_kinded target_is_int)
  have target_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' newTargetTy"
    using target_rt_env is_runtime_type_extend_runtime_tyvars
    unfolding extend_env_with_tyvars_def by auto

  have wf': "tyenv_well_formed ?env'"
    using "3.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast

  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"

  show ?case
  proof (cases "unify ?is_flex operandTy newTargetTy")
    case (Some subst)
    \<comment> \<open>Unification succeeded: cast is eliminated via the unifier's substitution\<close>
    from "3.prems"(1) elab_target elab_operand target_is_int Some have
      result: "newTm = apply_subst_to_term subst newOperand" "ty = newTargetTy"
      by (auto split: if_splits)

    \<comment> \<open>operandTy is well-kinded in ?env'\<close>
    have operand_wk: "is_well_kinded ?env' operandTy"
      using core_term_type_well_kinded[OF ih wf'] .
    have operand_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' operandTy"
      using core_term_type_notghost_runtime ih wf' by auto

    \<comment> \<open>The unifier's substitution range is well-kinded and runtime in ?env'\<close>
    have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?env' ty'"
      using unify_preserves_well_kinded[OF Some operand_wk target_wk] .
    have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?env' ty')"
    proof
      assume ng: "ghost = NotGhost"
      show "\<forall>ty' \<in> fmran' subst. is_runtime_type ?env' ty'"
        using unify_preserves_runtime[OF Some] operand_rt target_rt ng by blast
    qed

    \<comment> \<open>The unifier only binds flex metas; locals and return type are unaffected. \<close>
    have unif_dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from flex_subst_identity_on_env[OF unif_dom_flex "3.prems"(2) env'_locals env'_ret]
    have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                                        \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType ?env') = TE_ReturnType ?env'"
      by blast+

    have subst_applied:
      "core_term_type ?env' ghost (apply_subst_to_term subst newOperand)
         = Some (apply_subst subst operandTy)"
      using apply_subst_to_term_preserves_typing
              [OF ih wf' subst_wk subst_rt locals_unaffected ret_unaffected] .
    also have "apply_subst subst operandTy = apply_subst subst newTargetTy"
      using unify_sound[OF Some] .
    also have "apply_subst subst newTargetTy = newTargetTy"
      using target_is_int is_integer_type_apply_subst by simp
    finally show ?thesis using result by simp

  next
    case None
    \<comment> \<open>Unification failed: fall through to the integer-cast branch\<close>
    from "3.prems"(1) elab_target elab_operand target_is_int None have
      result: "newTm = CoreTm_Cast newTargetTy newOperand" "ty = newTargetTy"
      and operand_is_int: "is_integer_type operandTy"
      by (auto split: if_splits)
    show ?thesis using result ih operand_is_int target_is_int target_rt by auto
  qed

next
  \<comment> \<open>Case: BabTm_If - elaborates to CoreTm_Match with True/False patterns\<close>
  case (4 env typedefs ghost loc condTm thenTm elseTm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"

  \<comment> \<open>Extract intermediate elaboration results\<close>
  from "4.prems"(1) obtain newCond condTy next_mv1 where
    elab_cond: "elab_term env typedefs ghost condTm next_mv = Inr (newCond, condTy, next_mv1)"
    by (auto split: sum.splits)
  from "4.prems"(1) elab_cond obtain newThen thenTy next_mv2 where
    elab_then: "elab_term env typedefs ghost thenTm next_mv1 = Inr (newThen, thenTy, next_mv2)"
    by (auto split: sum.splits)
  from "4.prems"(1) elab_cond elab_then obtain newElse elseTy next_mv3 where
    elab_else: "elab_term env typedefs ghost elseTm next_mv2 = Inr (newElse, elseTy, next_mv3)"
    by (auto split: sum.splits)

  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"

  \<comment> \<open>Elaboration only succeeds if the condition unifies with Bool. \<close>
  from "4.prems"(1) elab_cond elab_then elab_else obtain condSubst where
    cond_unify: "unify ?is_flex condTy CoreTy_Bool = Some condSubst"
    by (auto simp: Let_def split: sum.splits option.splits)

  define finalCond where
    "finalCond = apply_subst_to_term condSubst newCond"

  \<comment> \<open>If forwards elseTm's next_mv so outer next_mv' = next_mv3\<close>
  from "4.prems"(1) elab_cond elab_then elab_else cond_unify have next_mv_eq: "next_mv' = next_mv3"
    by (auto simp: Let_def split: option.splits if_splits)

  \<comment> \<open>Monotonicity: next_mv \<le> next_mv1 \<le> next_mv2 \<le> next_mv3\<close>
  have mono_12: "next_mv \<le> next_mv1"
    using elab_term_next_mv_monotone[OF elab_cond] .
  have mono_23: "next_mv1 \<le> next_mv2"
    using elab_term_next_mv_monotone[OF elab_then] .
  have mono_34: "next_mv2 \<le> next_mv3"
    using elab_term_next_mv_monotone[OF elab_else] .

  \<comment> \<open>Freshness preconditions for each sub-call\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv1"
    using "4.prems"(4) mono_12 by fastforce
  have fresh_2: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv2"
    using "4.prems"(4) mono_12 mono_23 by fastforce

  \<comment> \<open>IH: elaborated subterms have their claimed types in their respective sub-envs\<close>
  have ih_cond_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost newCond = Some condTy"
    using "4.IH"(1) elab_cond "4.prems"(2,3,4) by simp
  have ih_then_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost newThen = Some thenTy"
    using "4.IH"(2) elab_cond elab_then "4.prems"(2,3) fresh_1 by simp
  have ih_else_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv2 next_mv3) ghost newElse = Some elseTy"
    using "4.IH"(3) elab_cond elab_then elab_else "4.prems"(2,3) fresh_2 by simp

  \<comment> \<open>Lift all IHs into the outer extended env\<close>
  have ih_cond: "core_term_type ?env' ghost newCond = Some condTy"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_cond_sub, where lo'=next_mv and hi'=next_mv']
          mono_12 mono_23 mono_34 next_mv_eq by simp
  have ih_then: "core_term_type ?env' ghost newThen = Some thenTy"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_then_sub, where lo'=next_mv and hi'=next_mv']
          mono_12 mono_23 mono_34 next_mv_eq by simp
  have ih_else: "core_term_type ?env' ghost newElse = Some elseTy"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_else_sub, where lo'=next_mv and hi'=next_mv']
          mono_12 mono_23 mono_34 next_mv_eq by simp

  have wf': "tyenv_well_formed ?env'"
    using "4.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>A generic helper: any substitution whose domain is disjoint from
      TE_TypeVars env leaves locals and the return type unchanged. \<close>
  have unif_id_on_env:
    "\<And>s ty'. \<forall>n. n |\<in>| fmdom (s :: (nat, CoreType) fmap) \<longrightarrow> ?is_flex n
              \<Longrightarrow> type_tyvars ty' \<subseteq> fset (TE_TypeVars env)
              \<Longrightarrow> apply_subst s ty' = ty'"
  proof -
    fix s :: "(nat, CoreType) fmap" and ty'
    assume dom_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> ?is_flex n"
    assume mvs: "type_tyvars ty' \<subseteq> fset (TE_TypeVars env)"
    have "type_tyvars ty' \<inter> fset (fmdom s) = {}"
      using mvs dom_flex by auto
    thus "apply_subst s ty' = ty'" by (rule apply_subst_disjoint_id)
  qed
  have locals_unaffected_for:
    "\<And>s name ty'. \<forall>n. n |\<in>| fmdom (s :: (nat, CoreType) fmap) \<longrightarrow> ?is_flex n
                 \<Longrightarrow> fmlookup (TE_LocalVars ?env') name = Some ty'
                 \<Longrightarrow> apply_subst s ty' = ty'"
  proof -
    fix s :: "(nat, CoreType) fmap" and name ty'
    assume dom_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> ?is_flex n"
    assume lk: "fmlookup (TE_LocalVars ?env') name = Some ty'"
    have "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    with lk have lk_env: "fmlookup (TE_LocalVars env) name = Some ty'" by simp
    from "4.prems"(2) have "tyenv_vars_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    with lk_env have "is_well_kinded env ty'"
      unfolding tyenv_vars_well_kinded_def by blast
    from is_well_kinded_type_tyvars_subset[OF this]
    have "type_tyvars ty' \<subseteq> fset (TE_TypeVars env)" .
    thus "apply_subst s ty' = ty'"
      using unif_id_on_env[OF dom_flex] by blast
  qed
  have ret_unaffected_for:
    "\<And>s. \<forall>n. n |\<in>| fmdom (s :: (nat, CoreType) fmap) \<longrightarrow> ?is_flex n
         \<Longrightarrow> apply_subst s (TE_ReturnType ?env') = TE_ReturnType ?env'"
  proof -
    fix s :: "(nat, CoreType) fmap"
    assume dom_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> ?is_flex n"
    have ret_eq: "TE_ReturnType ?env' = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from "4.prems"(2) have "tyenv_return_type_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    hence "is_well_kinded env (TE_ReturnType env)"
      unfolding tyenv_return_type_well_kinded_def .
    from is_well_kinded_type_tyvars_subset[OF this]
    have "type_tyvars (TE_ReturnType env) \<subseteq> fset (TE_TypeVars env)" .
    hence "apply_subst s (TE_ReturnType env) = TE_ReturnType env"
      using unif_id_on_env[OF dom_flex] by blast
    thus "apply_subst s (TE_ReturnType ?env') = TE_ReturnType ?env'"
      using ret_eq by simp
  qed

  \<comment> \<open>condSubst range is well-kinded / runtime in ?env'. \<close>
  have cond_wk: "is_well_kinded ?env' condTy"
    using core_term_type_well_kinded[OF ih_cond wf'] .
  have cond_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' condTy"
    using core_term_type_notghost_runtime ih_cond wf' by auto
  have bool_wk: "is_well_kinded ?env' CoreTy_Bool" by simp
  have bool_rt: "is_runtime_type ?env' CoreTy_Bool" by simp
  have condSubst_wk: "\<forall>ty' \<in> fmran' condSubst. is_well_kinded ?env' ty'"
    using unify_preserves_well_kinded[OF cond_unify cond_wk bool_wk] .
  have condSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' condSubst. is_runtime_type ?env' ty')"
  proof
    assume ng: "ghost = NotGhost"
    show "\<forall>ty' \<in> fmran' condSubst. is_runtime_type ?env' ty'"
      using unify_preserves_runtime[OF cond_unify] cond_rt bool_rt ng by blast
  qed
  have condSubst_dom_flex: "\<forall>n. n |\<in>| fmdom condSubst \<longrightarrow> ?is_flex n"
    using unify_unify_list_dom_flex(1)[OF cond_unify] .
  have condSubst_locals: "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                                     \<Longrightarrow> apply_subst condSubst ty' = ty'"
    using locals_unaffected_for[OF condSubst_dom_flex] .
  have condSubst_ret: "apply_subst condSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
    using ret_unaffected_for[OF condSubst_dom_flex] .

  \<comment> \<open>Final condition has type Bool in ?env'. \<close>
  have finalCond_typed: "core_term_type ?env' ghost finalCond = Some CoreTy_Bool"
  proof -
    have "core_term_type ?env' ghost (apply_subst_to_term condSubst newCond)
            = Some (apply_subst condSubst condTy)"
      using apply_subst_to_term_preserves_typing
              [OF ih_cond wf' condSubst_wk condSubst_rt condSubst_locals condSubst_ret] .
    also have "apply_subst condSubst condTy = apply_subst condSubst CoreTy_Bool"
      using unify_sound[OF cond_unify] .
    also have "apply_subst condSubst CoreTy_Bool = CoreTy_Bool" by simp
    finally show ?thesis unfolding finalCond_def .
  qed

  \<comment> \<open>Now handle the two cases: unification succeeds or integer coercion\<close>
  show ?case
  proof (cases "unify ?is_flex thenTy elseTy")
    case (Some branchSubst)
    \<comment> \<open>Unification succeeded\<close>
    let ?resultTy = "apply_subst branchSubst thenTy"
    let ?newThen' = "apply_subst_to_term branchSubst newThen"
    let ?newElse' = "apply_subst_to_term branchSubst newElse"
    let ?matchArms = "[(CorePat_Bool True, ?newThen'), (CorePat_Bool False, ?newElse')]"

    from "4.prems"(1) elab_cond elab_then elab_else cond_unify Some have
      result_eq: "newTm = CoreTm_Match finalCond ?matchArms" "ty = ?resultTy"
      by (auto simp: finalCond_def Let_def split: option.splits)

    \<comment> \<open>From unify_sound: applying branchSubst unifies the types\<close>
    from unify_sound[OF Some] have unified: "apply_subst branchSubst thenTy = apply_subst branchSubst elseTy" .

    \<comment> \<open>branchSubst range is well-kinded / runtime in ?env'. \<close>
    have then_wk: "is_well_kinded ?env' thenTy"
      using core_term_type_well_kinded[OF ih_then wf'] .
    have else_wk: "is_well_kinded ?env' elseTy"
      using core_term_type_well_kinded[OF ih_else wf'] .
    have branchSubst_wk: "\<forall>ty \<in> fmran' branchSubst. is_well_kinded ?env' ty"
      using unify_preserves_well_kinded[OF Some then_wk else_wk] .
    have branchSubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty \<in> fmran' branchSubst. is_runtime_type ?env' ty)"
    proof
      assume ng: "ghost = NotGhost"
      have "is_runtime_type ?env' thenTy"
        using core_term_type_notghost_runtime ih_then wf' ng by auto
      moreover have "is_runtime_type ?env' elseTy"
        using core_term_type_notghost_runtime ih_else wf' ng by auto
      ultimately show "\<forall>ty \<in> fmran' branchSubst. is_runtime_type ?env' ty"
        using unify_preserves_runtime[OF Some] by blast
    qed
    have branchSubst_dom_flex: "\<forall>n. n |\<in>| fmdom branchSubst \<longrightarrow> ?is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have branchSubst_locals:
      "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                    \<Longrightarrow> apply_subst branchSubst ty' = ty'"
      using locals_unaffected_for[OF branchSubst_dom_flex] .
    have branchSubst_ret: "apply_subst branchSubst (TE_ReturnType ?env') = TE_ReturnType ?env'"
      using ret_unaffected_for[OF branchSubst_dom_flex] .

    have then'_typed: "core_term_type ?env' ghost ?newThen' = Some ?resultTy"
      using apply_subst_to_term_preserves_typing
              [OF ih_then wf' branchSubst_wk branchSubst_rt branchSubst_locals branchSubst_ret] .
    have else'_typed: "core_term_type ?env' ghost ?newElse' = Some ?resultTy"
      using apply_subst_to_term_preserves_typing
              [OF ih_else wf' branchSubst_wk branchSubst_rt branchSubst_locals branchSubst_ret]
            unified by simp

    \<comment> \<open>The match typechecks\<close>
    have "core_term_type ?env' ghost (CoreTm_Match finalCond ?matchArms) = Some ?resultTy"
    proof -
      have "?matchArms \<noteq> []" by simp
      have pats_compat: "list_all (\<lambda>p. pattern_compatible ?env' p CoreTy_Bool) (map fst ?matchArms)"
        by simp
      have pats_regular: "patterns_regular (map fst ?matchArms)"
        by (simp add: patterns_regular_def)
      have pats_exhaustive: "patterns_exhaustive ?env' CoreTy_Bool (map fst ?matchArms)"
        by simp
      have bodies_typed: "list_all (\<lambda>body. core_term_type ?env' ghost body = Some ?resultTy) (map snd ?matchArms)"
        using then'_typed else'_typed by simp
      show ?thesis
        using finalCond_typed \<open>?matchArms \<noteq> []\<close> pats_compat pats_regular pats_exhaustive bodies_typed
        by (simp add: then'_typed)
    qed
    thus ?thesis using result_eq by simp

  next
    case None
    \<comment> \<open>Unification failed - try integer coercion\<close>
    from "4.prems"(1) elab_cond elab_then elab_else cond_unify None
    obtain coercedThen coercedElse commonTy where
      coerce: "coerce_to_common_int_type newThen thenTy newElse elseTy = Some (coercedThen, coercedElse, commonTy)"
      by (auto simp: finalCond_def Let_def split: option.splits)

    let ?matchArms = "[(CorePat_Bool True, coercedThen), (CorePat_Bool False, coercedElse)]"

    from "4.prems"(1) elab_cond elab_then elab_else cond_unify None coerce have
      result_eq: "newTm = CoreTm_Match finalCond ?matchArms" "ty = commonTy"
      by (auto simp: finalCond_def Let_def split: option.splits)

    \<comment> \<open>From coerce_to_common_int_type_correct: coerced terms have common type\<close>
    have coerced_typed: "core_term_type ?env' ghost coercedThen = Some commonTy
                       \<and> core_term_type ?env' ghost coercedElse = Some commonTy"
      using coerce_to_common_int_type_correct[OF coerce ih_then ih_else wf'] .
    hence coerced_then_typed: "core_term_type ?env' ghost coercedThen = Some commonTy"
      and coerced_else_typed: "core_term_type ?env' ghost coercedElse = Some commonTy"
      by simp_all

    \<comment> \<open>The match typechecks\<close>
    have "core_term_type ?env' ghost (CoreTm_Match finalCond ?matchArms) = Some commonTy"
    proof -
      have "?matchArms \<noteq> []" by simp
      have pats_compat: "list_all (\<lambda>p. pattern_compatible ?env' p CoreTy_Bool) (map fst ?matchArms)"
        by simp
      have pats_regular: "patterns_regular (map fst ?matchArms)"
        by (simp add: patterns_regular_def)
      have pats_exhaustive: "patterns_exhaustive ?env' CoreTy_Bool (map fst ?matchArms)"
        by simp
      have bodies_typed: "list_all (\<lambda>body. core_term_type ?env' ghost body = Some commonTy) (map snd ?matchArms)"
        using coerced_then_typed coerced_else_typed by simp
      show ?thesis
        using finalCond_typed \<open>?matchArms \<noteq> []\<close> pats_compat pats_regular pats_exhaustive bodies_typed
        by (simp add: coerced_then_typed)
    qed
    thus ?thesis using result_eq by simp
  qed

next
  \<comment> \<open>Case: BabTm_Unop\<close>
  case (5 env typedefs ghost loc op operand next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract intermediate results\<close>
  from "5.prems"(1) obtain newOperand operandTy next_mv'' where
    elab_operand: "elab_term env typedefs ghost operand next_mv = Inr (newOperand, operandTy, next_mv'')"
    by (auto split: sum.splits)
  \<comment> \<open>Unop forwards the operand's next_mv\<close>
  from "5.prems"(1) elab_operand have next_mv_eq: "next_mv' = next_mv''"
    by (auto simp: Let_def split: option.splits BabUnop.splits if_splits)

  have wf': "tyenv_well_formed ?env'"
    using "5.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>IH: operand has its type in the extended env\<close>
  have ih: "core_term_type ?env' ghost newOperand = Some operandTy"
    using "5.IH"[OF elab_operand "5.prems"(2,3,4)] next_mv_eq by simp

  let ?cop = "unop_to_core op"
  let ?defaultTy = "default_type_for_unop ?cop"
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"

  show ?case
  proof (cases "unify ?is_flex operandTy ?defaultTy")
    case (Some subst)
    \<comment> \<open>Unification succeeded: operand is either already the default type or a
        flex metavariable. The substitution resolves it to defaultTy. \<close>
    let ?newOperand2 = "apply_subst_to_term subst newOperand"
    from "5.prems"(1) elab_operand Some have
      result: "newTm = CoreTm_Unop ?cop ?newOperand2" "ty = ?defaultTy"
      by (auto simp: Let_def)

    \<comment> \<open>operandTy is well-kinded / runtime in ?env'\<close>
    have operand_wk: "is_well_kinded ?env' operandTy"
      using core_term_type_well_kinded[OF ih wf'] .
    have operand_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' operandTy"
      using core_term_type_notghost_runtime ih wf' by auto
    have default_wk: "is_well_kinded ?env' ?defaultTy"
      by (rule default_type_for_unop_is_well_kinded)
    have default_rt: "is_runtime_type ?env' ?defaultTy"
      by (rule default_type_for_unop_is_runtime)

    \<comment> \<open>subst range is well-kinded / runtime in ?env'\<close>
    have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?env' ty'"
      using unify_preserves_well_kinded[OF Some operand_wk default_wk] .
    have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?env' ty')"
    proof
      assume ng: "ghost = NotGhost"
      show "\<forall>ty' \<in> fmran' subst. is_runtime_type ?env' ty'"
        using unify_preserves_runtime[OF Some] operand_rt default_rt ng by blast
    qed

    \<comment> \<open>subst has flex domain, so locals and return type are unaffected. \<close>
    have subst_dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have env'_locals: "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    have env'_ret: "TE_ReturnType ?env' = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from flex_subst_identity_on_env[OF subst_dom_flex "5.prems"(2) env'_locals env'_ret]
    have locals_unaffected: "\<And>name ty'. fmlookup (TE_LocalVars ?env') name = Some ty'
                                        \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType ?env') = TE_ReturnType ?env'"
      by blast+

    \<comment> \<open>After substitution, newOperand has type defaultTy in ?env'\<close>
    have operand2_typed: "core_term_type ?env' ghost ?newOperand2 = Some ?defaultTy"
    proof -
      have "core_term_type ?env' ghost ?newOperand2 = Some (apply_subst subst operandTy)"
        using apply_subst_to_term_preserves_typing
                [OF ih wf' subst_wk subst_rt locals_unaffected ret_unaffected] .
      also have "apply_subst subst operandTy = apply_subst subst ?defaultTy"
        using unify_sound[OF Some] .
      also have "apply_subst subst ?defaultTy = ?defaultTy"
        by (cases ?cop) simp_all
      finally show ?thesis .
    qed

    \<comment> \<open>The default type satisfies the operator's requirement\<close>
    have op_ok: "(case ?cop of
        CoreUnop_Negate \<Rightarrow> is_signed_numeric_type ?defaultTy
      | CoreUnop_Complement \<Rightarrow> is_finite_integer_type ?defaultTy
      | CoreUnop_Not \<Rightarrow> ?defaultTy = CoreTy_Bool)"
      by (cases op) simp_all

    show ?thesis using result operand2_typed op_ok by (cases ?cop) auto

  next
    case None
    \<comment> \<open>Unification failed: operand is a concrete type different from defaultTy.
        Case-split on the operator and the operand type. \<close>
    show ?thesis
    proof (cases op)
      case BabUnop_Negate
      \<comment> \<open>Negate: must be signed numeric (not defaultTy = i32).\<close>
      from "5.prems"(1) elab_operand None BabUnop_Negate have
        signed: "is_signed_numeric_type operandTy"
        and result: "newTm = CoreTm_Unop CoreUnop_Negate newOperand" "ty = operandTy"
        by (auto simp: Let_def split: if_splits)
      show ?thesis using result ih signed by simp
    next
      case BabUnop_Complement
      \<comment> \<open>Complement: must be a finite integer type (not defaultTy = i32).\<close>
      from "5.prems"(1) elab_operand None BabUnop_Complement have
        finite: "is_finite_integer_type operandTy"
        and result: "newTm = CoreTm_Unop CoreUnop_Complement newOperand" "ty = operandTy"
        by (auto simp: Let_def split: if_splits)
      show ?thesis using result ih finite by simp
    next
      case BabUnop_Not
      \<comment> \<open>Not: elaborator errors since unify against Bool failed. \<close>
      from "5.prems"(1) elab_operand None BabUnop_Not show ?thesis
        by (auto simp: Let_def)
    qed
  qed

next
  \<comment> \<open>Case: BabTm_Binop\<close>
  case (6 env typedefs ghost loc lhs operands next_mv)
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract elaboration of LHS\<close>
  from "6.prems"(1) obtain newLhs lhsTy next_mv1 where
    elab_lhs: "elab_term env typedefs ghost lhs next_mv = Inr (newLhs, lhsTy, next_mv1)"
    by (auto split: sum.splits)
  \<comment> \<open>Extract elaboration of RHS terms\<close>
  from "6.prems"(1) elab_lhs obtain rhsTms rhsTys next_mv2 where
    elab_rhs_list: "elab_term_list env typedefs ghost (map snd operands) next_mv1
                    = Inr (rhsTms, rhsTys, next_mv2)"
    by (auto split: sum.splits)
  \<comment> \<open>Build the operator list\<close>
  let ?opTriples = "zip (map fst operands) (zip rhsTms rhsTys)"
  let ?opList = "map (\<lambda>(op, tm_ty). (op, fst tm_ty, snd tm_ty)) ?opTriples"
  \<comment> \<open>Extract process_binop_chain success\<close>
  from "6.prems"(1) elab_lhs elab_rhs_list obtain resultTm resultTy where
    process_result: "process_binop_chain ?is_flex loc ghost newLhs lhsTy ?opList = Inr (resultTm, resultTy)"
    and result_eq: "newTm = resultTm" "ty = resultTy"
    by (auto simp: Let_def split: sum.splits)
  \<comment> \<open>Binop forwards elab_term_list's next_mv\<close>
  from "6.prems"(1) elab_lhs elab_rhs_list process_result have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)
  have mono_1: "next_mv \<le> next_mv1"
    using elab_term_next_mv_monotone[OF elab_lhs] .
  have mono_2: "next_mv1 \<le> next_mv2"
    using elab_term_list_next_mv_monotone[OF elab_rhs_list] .
  have wf': "tyenv_well_formed ?env'"
    using "6.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
  \<comment> \<open>IH on LHS: newLhs has type lhsTy in the extended env\<close>
  have lhs_typing_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost newLhs = Some lhsTy"
    using "6.IH"(1)[OF elab_lhs "6.prems"(2,3,4)] .
  have lhs_typing: "core_term_type ?env' ghost newLhs = Some lhsTy"
    using core_term_type_extend_env_with_tyvars_mono[OF lhs_typing_sub, where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp
  \<comment> \<open>Freshness carries forward through the lhs sub-call\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv1"
    using "6.prems"(4) mono_1 by fastforce
  \<comment> \<open>IH on RHS list: each rhsTm has its corresponding type in the extended env\<close>
  have rhs_typing_sub: "list_all2 (\<lambda>tm ty. core_term_type
                                      (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty)
                                    rhsTms rhsTys"
    using "6.IH"(2) "6.prems"(2,3) elab_lhs elab_rhs_list fresh_1 by simp
  have rhs_typing: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty) rhsTms rhsTys"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty \<Longrightarrow>
                  core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono mono_1 mono_2 next_mv_eq by blast
    thus ?thesis using rhs_typing_sub by (auto elim!: list_all2_mono)
  qed
  \<comment> \<open>Convert list_all2 on rhsTms/rhsTys to list_all on opList\<close>
  have rhs_len: "length rhsTms = length rhsTys"
    using rhs_typing by (auto dest: list_all2_lengthD)
  have ops_typed: "list_all (\<lambda>(op, tm, ty). core_term_type ?env' ghost tm = Some ty) ?opList"
  proof (unfold list_all_iff, intro ballI, clarify)
    fix op tm tyR
    assume in_set: "(op, tm, tyR) \<in> set ?opList"
    from in_set obtain tmTy where
      tmTy_in: "(op, tmTy) \<in> set (zip (map fst operands) (zip rhsTms rhsTys))" and
      tmTy_eq: "tm = fst tmTy" "tyR = snd tmTy"
      by auto
    from tmTy_in have "tmTy \<in> set (zip rhsTms rhsTys)"
      using set_zip_rightD by metis
    then obtain i where i_bound: "i < length rhsTms" and "i < length rhsTys"
      and tm_eq: "tm = rhsTms ! i" and ty_eq: "tyR = rhsTys ! i"
      using tmTy_eq rhs_len by (auto simp: set_zip in_set_conv_nth)
    thus "core_term_type ?env' ghost tm = Some tyR"
      using rhs_typing by (auto dest: list_all2_nthD)
  qed
  \<comment> \<open>Locals and return type of ?env' come from env (unchanged by the
      extension) and are well-kinded in env, so their type variables lie in
      TE_TypeVars env. The Binop case's is_flex is (\<lambda>n. n |\<notin>| TE_TypeVars env),
      so none of those type variables are flex. \<close>
  have env'_locals_rigid:
    "\<forall>name ty' n. fmlookup (TE_LocalVars ?env') name = Some ty'
                    \<longrightarrow> n \<in> type_tyvars ty' \<longrightarrow> \<not> ?is_flex n"
  proof (intro allI impI)
    fix name ty' n
    assume lk: "fmlookup (TE_LocalVars ?env') name = Some ty'"
    assume n_mv: "n \<in> type_tyvars ty'"
    have "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    with lk have lk_env: "fmlookup (TE_LocalVars env) name = Some ty'" by simp
    from "6.prems"(2) have "tyenv_vars_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    with lk_env have "is_well_kinded env ty'"
      unfolding tyenv_vars_well_kinded_def by blast
    from is_well_kinded_type_tyvars_subset[OF this] n_mv
    have "n \<in> fset (TE_TypeVars env)" by blast
    thus "\<not> ?is_flex n" by simp
  qed
  have env'_ret_rigid: "\<forall>n. n \<in> type_tyvars (TE_ReturnType ?env') \<longrightarrow> \<not> ?is_flex n"
  proof (intro allI impI)
    fix n assume n_mv: "n \<in> type_tyvars (TE_ReturnType ?env')"
    have "TE_ReturnType ?env' = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    with n_mv have n_mv': "n \<in> type_tyvars (TE_ReturnType env)" by simp
    from "6.prems"(2) have "tyenv_return_type_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    hence "is_well_kinded env (TE_ReturnType env)"
      unfolding tyenv_return_type_well_kinded_def .
    from is_well_kinded_type_tyvars_subset[OF this] n_mv'
    have "n \<in> fset (TE_TypeVars env)" by blast
    thus "\<not> ?is_flex n" by simp
  qed

  \<comment> \<open>Apply process_binop_chain_correct\<close>
  have "core_term_type ?env' ghost resultTm = Some resultTy"
    using process_binop_chain_correct
            [OF process_result lhs_typing ops_typed wf' env'_locals_rigid env'_ret_rigid] .
  thus ?case using result_eq by simp

next
  \<comment> \<open>Case: BabTm_Let\<close>
  case (7 env typedefs ghost loc varName rhs body next_mv)
  let ?env_ext = "extend_env_with_tyvars env ghost next_mv next_mv'"

  \<comment> \<open>Extract rhs elaboration and the resolved-type check\<close>
  from "7.prems"(1) obtain rhsTm rhsTy next_mv1 where
    elab_rhs: "elab_term env typedefs ghost rhs next_mv = Inr (rhsTm, rhsTy, next_mv1)"
    by (auto split: sum.splits)
  from "7.prems"(1) elab_rhs have rhs_resolved:
    "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list rhsTy)"
    by (auto split: if_splits)

  \<comment> \<open>Build the let-body env (as used in both elab_term and core_term_type)\<close>
  let ?body_env = "env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                         TE_GhostLocals := (if ghost = Ghost
                                             then finsert varName (TE_GhostLocals env)
                                             else fminus (TE_GhostLocals env) {|varName|}),
                         TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>"

  from "7.prems"(1) elab_rhs rhs_resolved obtain bodyTm bodyTy next_mv2 where
    elab_body: "elab_term ?body_env typedefs ghost body next_mv1 = Inr (bodyTm, bodyTy, next_mv2)" and
    result_eq: "newTm = CoreTm_Let varName rhsTm bodyTm" "ty = bodyTy"
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>Let forwards body's next_mv\<close>
  from "7.prems"(1) elab_rhs rhs_resolved elab_body have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>Monotonicity\<close>
  have mono_1: "next_mv \<le> next_mv1"
    using elab_term_next_mv_monotone[OF elab_rhs] .
  have mono_2: "next_mv1 \<le> next_mv2"
    using elab_term_next_mv_monotone[OF elab_body] .

  \<comment> \<open>IH on rhs: rhsTm has type rhsTy in extend_env_with_tyvars env ghost next_mv next_mv1\<close>
  have rhs_typing_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost rhsTm = Some rhsTy"
    using "7.IH"(1)[OF elab_rhs "7.prems"(2,3,4)] .
  \<comment> \<open>Lift to ?env_ext\<close>
  have rhs_typing: "core_term_type ?env_ext ghost rhsTm = Some rhsTy"
    using core_term_type_extend_env_with_tyvars_mono[OF rhs_typing_sub, where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp

  \<comment> \<open>Well-kindedness of rhsTy in env: follows directly from rhs_resolved via is_well_kinded_transfer.\<close>
  have rhs_wk_env: "is_well_kinded env rhsTy"
  proof -
    have wf_sub: "tyenv_well_formed (extend_env_with_tyvars env ghost next_mv next_mv1)"
      using "7.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
    have rhs_wk_sub: "is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv1) rhsTy"
      using core_term_type_well_kinded[OF "7.IH"(1)[OF elab_rhs "7.prems"(2,3,4)] wf_sub] .
    have tyvars_in_env: "type_tyvars rhsTy \<subseteq> fset (TE_TypeVars env)"
      using rhs_resolved
      by (auto simp: set_type_tyvars_list[symmetric] list_all_iff fset_of_list_elem)
    show ?thesis
      using is_well_kinded_transfer[OF rhs_wk_sub tyvars_in_env]
      by (simp add: extend_env_with_tyvars_def)
  qed

  \<comment> \<open>In non-ghost context, rhsTy is also runtime in env.
     rhs_resolved pins rhsTy's type variables into env.TE_TypeVars, and freshness (prems(4))
     says those are all strictly below next_mv, so they're disjoint from the fresh
     range [next_mv..<next_mv1]. Hence any type variable in rhsTy that's runtime in the
     sub-extended env is also runtime in the original env.\<close>
  have rhs_rt_env: "ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy"
  proof
    assume ng: "ghost = NotGhost"
    have wf_sub: "tyenv_well_formed (extend_env_with_tyvars env ghost next_mv next_mv1)"
      using "7.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
    have rhs_rt_sub: "is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv1) rhsTy"
      using core_term_type_notghost_runtime ng rhs_typing_sub wf_sub by auto
    \<comment> \<open>Every type variable in rhsTy is in env.TE_TypeVars (from rhs_resolved)\<close>
    have tyvars_in_env_tv: "\<forall>n \<in> type_tyvars rhsTy. n |\<in>| TE_TypeVars env"
      using rhs_resolved by (auto simp: set_type_tyvars_list[symmetric] list_all_iff)
    \<comment> \<open>And every such type variable is < next_mv (by freshness)\<close>
    have tyvars_lt: "\<forall>n \<in> type_tyvars rhsTy. n < next_mv"
      using tyvars_in_env_tv "7.prems"(4) by blast
    \<comment> \<open>In the sub-extended env, TE_RuntimeTypeVars = env.TE_RuntimeTypeVars \<union> [next_mv..<next_mv1].
       Combined with tyvars_lt, any type variable in rhsTy that's runtime in the sub-extended env
       is also in env.TE_RuntimeTypeVars.\<close>
    have tyvars_in_env_rtv: "type_tyvars rhsTy \<subseteq> fset (TE_RuntimeTypeVars env)"
    proof
      fix n assume n_in: "n \<in> type_tyvars rhsTy"
      \<comment> \<open>From rhs_rt_sub we know n is in the sub-extended env's RT set\<close>
      have rhs_tyvars_rt: "type_tyvars rhsTy \<subseteq>
                          fset (TE_RuntimeTypeVars (extend_env_with_tyvars env ghost next_mv next_mv1))"
        using is_runtime_type_tyvars_subset[OF rhs_rt_sub] .
      from rhs_tyvars_rt n_in
      have "n |\<in>| TE_RuntimeTypeVars (extend_env_with_tyvars env ghost next_mv next_mv1)"
        by (auto simp: fset_of_list_elem)
      hence n_in_ext_rtv: "n |\<in>| TE_RuntimeTypeVars env |\<union>| fset_of_list [next_mv..<next_mv1]"
        using ng unfolding extend_env_with_tyvars_def by simp
      from tyvars_lt n_in have "n < next_mv" by blast
      hence "n \<notin> set [next_mv..<next_mv1]" by simp
      hence "n |\<notin>| fset_of_list [next_mv..<next_mv1]" by (simp add: fset_of_list_elem)
      with n_in_ext_rtv have "n |\<in>| TE_RuntimeTypeVars env" by blast
      thus "n \<in> fset (TE_RuntimeTypeVars env)" by (simp add: fset_of_list_elem)
    qed
    show "is_runtime_type env rhsTy"
      using is_runtime_type_transfer[OF rhs_rt_sub tyvars_in_env_rtv]
      unfolding extend_env_with_tyvars_def by simp
  qed

  have wf_body_env: "tyenv_well_formed ?body_env"
  proof (cases "ghost = Ghost")
    case True
    thus ?thesis
      using "7.prems"(2) rhs_wk_env tyenv_well_formed_add_ghost_var
      by (simp add: tyenv_well_formed_TE_ConstLocals_irrelevant)
  next
    case False
    hence ng: "ghost = NotGhost" by (cases ghost) simp_all
    with rhs_rt_env have rhs_rt: "is_runtime_type env rhsTy" by simp
    have wf_no_cn: "tyenv_well_formed (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
                                              TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>)"
      using tyenv_well_formed_add_var[OF "7.prems"(2) rhs_wk_env rhs_rt] .
    have env_rewrite: "?body_env =
      (env \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars env),
              TE_GhostLocals := fminus (TE_GhostLocals env) {|varName|} \<rparr>)
      \<lparr> TE_ConstLocals := finsert varName (TE_ConstLocals env) \<rparr>"
      using ng by simp
    show ?thesis
      using wf_no_cn tyenv_well_formed_TE_ConstLocals_irrelevant env_rewrite by simp
  qed

  have td_wf_body: "typedefs_well_formed ?body_env typedefs"
  proof -
    have wk_eq: "\<And>t. is_well_kinded ?body_env t = is_well_kinded env t"
      using is_well_kinded_cong_env[of ?body_env env] by simp
    show ?thesis
      using "7.prems"(3) unfolding typedefs_well_formed_def wk_eq by auto
  qed

  \<comment> \<open>Freshness carries through to next_mv1; ?body_env has same TE_TypeVars as env\<close>
  have fresh_body: "\<forall>n. n |\<in>| TE_TypeVars ?body_env \<longrightarrow> n < next_mv1"
    using "7.prems"(4) mono_1 by fastforce

  \<comment> \<open>IH on body: bodyTm has type bodyTy in extend_env_with_tyvars ?body_env ghost next_mv1 next_mv2\<close>
  have body_typing_sub: "core_term_type (extend_env_with_tyvars ?body_env ghost next_mv1 next_mv2) ghost bodyTm = Some bodyTy"
    using "7.IH"(2) elab_body elab_rhs rhs_resolved td_wf_body wf_body_env fresh_body by simp

  \<comment> \<open>Show extend_env_with_tyvars ?body_env ghost next_mv1 next_mv2 equals the Let-extended ?env_ext\<close>
  let ?core_body_env = "?env_ext \<lparr> TE_LocalVars := fmupd varName rhsTy (TE_LocalVars ?env_ext),
                                    TE_GhostLocals := (if ghost = Ghost
                                                        then finsert varName (TE_GhostLocals ?env_ext)
                                                        else fminus (TE_GhostLocals ?env_ext) {|varName|}),
                                    TE_ConstLocals := finsert varName (TE_ConstLocals ?env_ext) \<rparr>"

  have env_widen_body: "core_term_type (extend_env_with_tyvars ?body_env ghost next_mv next_mv') ghost bodyTm = Some bodyTy"
    using core_term_type_extend_env_with_tyvars_mono[OF body_typing_sub,
              where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp

  have env_eq: "extend_env_with_tyvars ?body_env ghost next_mv next_mv' = ?core_body_env"
    unfolding extend_env_with_tyvars_def by simp

  have body_typing: "core_term_type ?core_body_env ghost bodyTm = Some bodyTy"
    using env_widen_body env_eq by simp

  \<comment> \<open>Final: core_term_type of CoreTm_Let unfolds to the check on rhs and body in ?core_body_env\<close>
  show ?case
    using result_eq rhs_typing body_typing
    by (simp add: Let_def)
next
  \<comment> \<open>Case: BabTm_Quantifier\<close>
  case (8 env typedefs ghost loc quant name varTy tm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"

  \<comment> \<open>Ghost only\<close>
  from "8.prems"(1) have ghost_eq: "ghost = Ghost"
    by (auto split: if_splits)

  \<comment> \<open>Elaborate the type annotation\<close>
  from "8.prems"(1) ghost_eq obtain coreVarTy where
    elab_ty: "elab_type env typedefs ghost varTy = Inr coreVarTy"
    by (auto split: sum.splits)

  \<comment> \<open>Body env\<close>
  let ?body_env = "env \<lparr> TE_LocalVars := fmupd name coreVarTy (TE_LocalVars env),
                         TE_GhostLocals := finsert name (TE_GhostLocals env) \<rparr>"

  \<comment> \<open>Elaborate the body\<close>
  from "8.prems"(1) ghost_eq elab_ty obtain bodyTm bodyTy next_mv_body where
    elab_body: "elab_term ?body_env typedefs ghost tm next_mv = Inr (bodyTm, bodyTy, next_mv_body)"
    by (auto simp: Let_def split: sum.splits option.splits)

  \<comment> \<open>Unify body type with Bool\<close>
  from "8.prems"(1) ghost_eq elab_ty elab_body obtain bodySubst where
    body_unify: "unify ?is_flex bodyTy CoreTy_Bool = Some bodySubst"
    by (auto simp: Let_def split: sum.splits option.splits)

  \<comment> \<open>Extract the final results\<close>
  define finalBody where "finalBody = apply_subst_to_term bodySubst bodyTm"
  define finalVarTy where "finalVarTy = apply_subst bodySubst coreVarTy"

  from "8.prems"(1) ghost_eq elab_ty elab_body body_unify have
    newTm_eq: "newTm = CoreTm_Quantifier quant name finalVarTy finalBody" and
    ty_eq: "ty = CoreTy_Bool" and
    next_mv_eq: "next_mv' = next_mv_body"
    by (auto simp: Let_def finalBody_def finalVarTy_def)

  \<comment> \<open>varTy is well-kinded in env\<close>
  have varTy_wk: "is_well_kinded env coreVarTy"
    using elab_ty "8.prems"(2,3) elab_type_is_well_kinded by simp

  \<comment> \<open>body_env is well-formed\<close>
  have wf_body_env: "tyenv_well_formed ?body_env"
    using tyenv_well_formed_add_ghost_var[OF "8.prems"(2) varTy_wk] .

  \<comment> \<open>typedefs are well-formed w.r.t. body_env\<close>
  have td_wf_body: "typedefs_well_formed ?body_env typedefs"
  proof -
    have wk_eq: "\<And>t. is_well_kinded ?body_env t = is_well_kinded env t"
      using is_well_kinded_cong_env[of ?body_env env] by simp
    show ?thesis
      using "8.prems"(3) unfolding typedefs_well_formed_def wk_eq by auto
  qed

  \<comment> \<open>Freshness for the body call\<close>
  have fresh_body: "\<forall>n. n |\<in>| TE_TypeVars ?body_env \<longrightarrow> n < next_mv"
    using "8.prems"(4) by simp

  \<comment> \<open>IH on body\<close>
  have ih_body_sub: "core_term_type (extend_env_with_tyvars ?body_env ghost next_mv next_mv_body) ghost bodyTm = Some bodyTy"
    using "8.IH" ghost_eq elab_ty elab_body wf_body_env td_wf_body fresh_body
    by (simp add: Let_def)

  \<comment> \<open>Widen to outer env — next_mv_body = next_mv' so this is trivial\<close>
  have ih_body: "core_term_type (extend_env_with_tyvars ?body_env ghost next_mv next_mv') ghost bodyTm = Some bodyTy"
    using ih_body_sub next_mv_eq by simp

  \<comment> \<open>The extended env for the body in core terms\<close>
  let ?env'_body = "?env' \<lparr> TE_LocalVars := fmupd name coreVarTy (TE_LocalVars ?env'),
                            TE_GhostLocals := finsert name (TE_GhostLocals ?env') \<rparr>"

  have env_eq: "extend_env_with_tyvars ?body_env ghost next_mv next_mv' = ?env'_body"
    unfolding extend_env_with_tyvars_def by simp

  have ih_body': "core_term_type ?env'_body ghost bodyTm = Some bodyTy"
    using ih_body env_eq by simp

  \<comment> \<open>?env' and ?env'_body are well-formed\<close>
  have wf': "tyenv_well_formed ?env'"
    using "8.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast

  have varTy_wk': "is_well_kinded ?env' coreVarTy"
    using varTy_wk is_well_kinded_cong_env[of ?env' env]
    by (metis extend_env_with_tyvars_empty is_well_kinded_extend_env_with_tyvars_mono
        nat_le_linear)

  have wf_body': "tyenv_well_formed ?env'_body"
    using tyenv_well_formed_add_ghost_var[OF wf' varTy_wk'] .

  \<comment> \<open>bodySubst properties\<close>
  have bodySubst_dom_flex: "\<forall>n. n |\<in>| fmdom bodySubst \<longrightarrow> ?is_flex n"
    using unify_unify_list_dom_flex(1)[OF body_unify] .

  have body_wk: "is_well_kinded ?env'_body bodyTy"
    using core_term_type_well_kinded[OF ih_body' wf_body'] .
  have bool_wk: "is_well_kinded ?env'_body CoreTy_Bool" by simp

  have bodySubst_wk: "\<forall>ty' \<in> fmran' bodySubst. is_well_kinded ?env'_body ty'"
    using unify_preserves_well_kinded[OF body_unify body_wk bool_wk] .

  \<comment> \<open>Since ghost = Ghost, runtime conditions are vacuous\<close>
  have bodySubst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' bodySubst. is_runtime_type ?env'_body ty')"
    using ghost_eq by simp

  \<comment> \<open>Generic helper: subst with flex domain is identity on types whose tyvars are in TE_TypeVars env\<close>
  have unif_id_on_env:
    "\<And>s ty'. \<forall>n. n |\<in>| fmdom (s :: (nat, CoreType) fmap) \<longrightarrow> ?is_flex n
              \<Longrightarrow> type_tyvars ty' \<subseteq> fset (TE_TypeVars env)
              \<Longrightarrow> apply_subst s ty' = ty'"
  proof -
    fix s :: "(nat, CoreType) fmap" and ty'
    assume dom_flex: "\<forall>n. n |\<in>| fmdom s \<longrightarrow> ?is_flex n"
    assume mvs: "type_tyvars ty' \<subseteq> fset (TE_TypeVars env)"
    have "type_tyvars ty' \<inter> fset (fmdom s) = {}"
      using mvs dom_flex by auto
    thus "apply_subst s ty' = ty'" by (rule apply_subst_disjoint_id)
  qed

  \<comment> \<open>Locals in ?env'_body: subst doesn't affect them (their tyvars are in TE_TypeVars env)\<close>
  have bodySubst_locals: "\<And>vname vty. fmlookup (TE_LocalVars ?env'_body) vname = Some vty
                                     \<Longrightarrow> apply_subst bodySubst vty = vty"
  proof -
    fix vname vty
    assume lk: "fmlookup (TE_LocalVars ?env'_body) vname = Some vty"
    have lv_eq: "TE_LocalVars ?env'_body = fmupd name coreVarTy (TE_LocalVars ?env')"
      by simp
    have lv_env_eq: "TE_LocalVars ?env' = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    from "8.prems"(2) have vwk: "tyenv_vars_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    show "apply_subst bodySubst vty = vty"
    proof (cases "vname = name")
      case True
      with lk lv_eq have "vty = coreVarTy" by simp
      have "type_tyvars coreVarTy \<subseteq> fset (TE_TypeVars env)"
        using is_well_kinded_type_tyvars_subset[OF varTy_wk] .
      thus ?thesis using \<open>vty = coreVarTy\<close> unif_id_on_env[OF bodySubst_dom_flex] by simp
    next
      case False
      with lk lv_eq lv_env_eq have lk_env: "fmlookup (TE_LocalVars env) vname = Some vty"
        by simp
      from vwk lk_env have "is_well_kinded env vty"
        unfolding tyenv_vars_well_kinded_def by blast
      from is_well_kinded_type_tyvars_subset[OF this]
      have "type_tyvars vty \<subseteq> fset (TE_TypeVars env)" .
      thus ?thesis using unif_id_on_env[OF bodySubst_dom_flex] by simp
    qed
  qed

  have bodySubst_ret: "apply_subst bodySubst (TE_ReturnType ?env'_body) = TE_ReturnType ?env'_body"
  proof -
    have ret_eq: "TE_ReturnType ?env'_body = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from "8.prems"(2) have "tyenv_return_type_well_kinded env"
      unfolding tyenv_well_formed_def by simp
    hence "is_well_kinded env (TE_ReturnType env)"
      unfolding tyenv_return_type_well_kinded_def .
    have "type_tyvars (TE_ReturnType env) \<subseteq> fset (TE_TypeVars env)"
      by (simp add: \<open>is_well_kinded env (TE_ReturnType env)\<close>
          is_well_kinded_type_tyvars_subset)
    thus ?thesis using ret_eq unif_id_on_env[OF bodySubst_dom_flex] by simp
  qed

  \<comment> \<open>Body substitution preserves typing\<close>
  have finalBody_typed: "core_term_type ?env'_body ghost finalBody = Some CoreTy_Bool"
  proof -
    have "core_term_type ?env'_body ghost (apply_subst_to_term bodySubst bodyTm)
            = Some (apply_subst bodySubst bodyTy)"
      using apply_subst_to_term_preserves_typing
              [OF ih_body' wf_body' bodySubst_wk bodySubst_rt bodySubst_locals bodySubst_ret] .
    also have "apply_subst bodySubst bodyTy = apply_subst bodySubst CoreTy_Bool"
      using unify_sound[OF body_unify] .
    also have "apply_subst bodySubst CoreTy_Bool = CoreTy_Bool" by simp
    finally show ?thesis unfolding finalBody_def .
  qed

  \<comment> \<open>bodySubst is identity on coreVarTy (its tyvars are in TE_TypeVars env)\<close>
  have varTy_unchanged: "finalVarTy = coreVarTy"
    unfolding finalVarTy_def
    using unif_id_on_env[OF bodySubst_dom_flex is_well_kinded_type_tyvars_subset[OF varTy_wk]] .

  have finalVarTy_wk: "is_well_kinded ?env' finalVarTy"
    using varTy_unchanged varTy_wk' by simp

  show ?case
    using newTm_eq ty_eq ghost_eq finalVarTy_wk finalBody_typed varTy_unchanged
    by (simp add: Let_def)

next
  \<comment> \<open>Case: BabTm_Call\<close>
  case (9 env typedefs ghost loc callee args next_mv)
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract intermediate results from elaboration\<close>
  from "9.prems"(1) obtain fnName tyArgs expArgTypes retType next_mv1 where
    det_call: "determine_fun_call_type env typedefs ghost callee next_mv
               = Inr (fnName, tyArgs, expArgTypes, retType, next_mv1)"
    by (auto split: sum.splits)
  from "9.prems"(1) det_call have len_args: "length args = length expArgTypes"
    by (auto split: if_splits)
  from "9.prems"(1) det_call len_args obtain elabArgTms actualTypes next_mv2 where
    elab_args: "elab_term_list env typedefs ghost args next_mv1 = Inr (elabArgTms, actualTypes, next_mv2)"
    by (auto split: sum.splits)
  from "9.prems"(1) det_call len_args elab_args obtain finalArgTms finalSubst where
    unify_args: "unify_call_args ?is_flex loc fnName 0 elabArgTms actualTypes expArgTypes fmempty
                 = Inr (finalArgTms, finalSubst)"
    by (auto simp: Let_def split: sum.splits)
  \<comment> \<open>BabTm_Call forwards elab_term_list's next_mv, so next_mv' = next_mv2\<close>
  from "9.prems"(1) det_call len_args elab_args unify_args have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: Let_def split: sum.splits)
  from "9.prems"(1) det_call len_args elab_args unify_args have
    result_eq: "newTm = CoreTm_FunctionCall fnName (map (apply_subst finalSubst) tyArgs) finalArgTms"
               "ty = apply_subst finalSubst retType"
    by (auto simp: Let_def)

  \<comment> \<open>Get function info from determine_fun_call_type_correct\<close>
  have det_correct: "next_mv \<le> next_mv1
       \<and> (\<exists>funInfo.
           fmlookup (TE_Functions env) fnName = Some funInfo
         \<and> (ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost)
         \<and> length tyArgs = length (FI_TyArgs funInfo)
         \<and> list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv1)) tyArgs
         \<and> (ghost = NotGhost \<longrightarrow>
              list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv1)) tyArgs)
         \<and> expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                             (FI_TmArgs funInfo)
         \<and> retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                  (FI_ReturnType funInfo))"
    using determine_fun_call_type_correct[OF det_call "9.prems"(2,3)] .
  from det_correct have mono_1: "next_mv \<le> next_mv1" by blast
  from det_correct obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    ghost_ok: "ghost = NotGhost \<longrightarrow> FI_Ghost funInfo \<noteq> Ghost" and
    len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyargs_wk_ext: "list_all (is_well_kinded (extend_env_with_tyvars env ghost next_mv next_mv1)) tyArgs" and
    tyargs_rt_ext: "ghost = NotGhost \<longrightarrow>
                    list_all (is_runtime_type (extend_env_with_tyvars env ghost next_mv next_mv1)) tyArgs" and
    expArgTypes_eq: "expArgTypes = map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                                       (FI_TmArgs funInfo)" and
    retType_eq: "retType = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))
                                       (FI_ReturnType funInfo)"
    by blast

  \<comment> \<open>Freshness carries through det_call\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv1"
    using "9.prems"(4) mono_1 by fastforce
  \<comment> \<open>From IH on elab_term_list: elaborated args have their types in a sub-extended env\<close>
  have ih_args_sub: "list_all2 (\<lambda>tm ty. core_term_type
                                  (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty)
                               elabArgTms actualTypes"
    using "9.IH" "9.prems"(2,3) det_call elab_args len_args fresh_1 by simp
  have mono_2: "next_mv1 \<le> next_mv2"
    using elab_term_list_next_mv_monotone[OF elab_args] .
  \<comment> \<open>Lift ih_args_sub to the outer extended env\<close>
  have ih_args: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty)
                           elabArgTms actualTypes"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty \<Longrightarrow>
                  core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono[where lo=next_mv1 and hi=next_mv2
                                                        and lo'=next_mv and hi'=next_mv']
            mono_1 mono_2 next_mv_eq by simp
    thus ?thesis using ih_args_sub by (auto elim!: list_all2_mono)
  qed

  (* Use the helper lemma to complete the proof *)
  show ?case
    using elab_term_correct_call[OF "9.prems"(1,2,3,4) det_call elab_args ih_args] .

next
  \<comment> \<open>Case: BabTm_Tuple\<close>
  case (10 env typedefs ghost loc tms next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?names = "tuple_field_names (length tms)"
  \<comment> \<open>Extract elaboration results\<close>
  from "10.prems"(1) obtain newTms tys where
    elab_list: "elab_term_list env typedefs ghost tms next_mv
                = Inr (newTms, tys, next_mv')" and
    newTm_eq: "newTm = CoreTm_Record (zip ?names newTms)" and
    ty_eq: "ty = CoreTy_Record (zip ?names tys)"
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>IH on the element list\<close>
  have ih: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty) newTms tys"
    using "10.IH"[OF elab_list "10.prems"(2,3,4)] .

  have len_eq: "length newTms = length tys"
    using ih by (simp add: list_all2_lengthD)
  have len_list: "length newTms = length tms"
    using elab_term_list_length[OF elab_list] by simp
  have len_tys: "length tys = length tms"
    using len_eq len_list by simp
  have len_names: "length ?names = length tms" by simp

  \<comment> \<open>Each field of zip names newTms typechecks to the matching type\<close>
  have each_field: "\<And>i. i < length tms \<Longrightarrow>
        core_term_type ?env' ghost (snd ((zip ?names newTms) ! i)) = Some (tys ! i)"
  proof -
    fix i assume i_lt: "i < length tms"
    have snd_eq: "snd ((zip ?names newTms) ! i) = newTms ! i"
      using i_lt len_list len_names by simp
    from ih have "core_term_type ?env' ghost (newTms ! i) = Some (tys ! i)"
      using i_lt len_list len_tys
      by (simp add: list_all2_conv_all_nth)
    with snd_eq show "core_term_type ?env' ghost (snd ((zip ?names newTms) ! i)) = Some (tys ! i)"
      by simp
  qed

  \<comment> \<open>those succeeds on the zipped list\<close>
  have those_ok: "those (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))
                  = Some tys"
  proof -
    have len_zip: "length (zip ?names newTms) = length tms"
      using len_list len_names by simp
    have la2: "list_all2 (\<lambda>x y. x = Some y)
                 (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms)) tys"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))
            = length tys"
        using len_zip len_tys by simp
    next
      fix i assume i_lt: "i < length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))"
      from i_lt len_zip have i_tms: "i < length tms" by simp
      obtain n t where nt_eq: "(zip ?names newTms) ! i = (n, t)" by (cases "(zip ?names newTms) ! i")
      from nt_eq have snd_eq: "snd ((zip ?names newTms) ! i) = t" by simp
      from each_field[OF i_tms] snd_eq have t_ty: "core_term_type ?env' ghost t = Some (tys ! i)"
        by simp
      from nt_eq t_ty i_lt len_zip
      show "map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms) ! i
            = Some (tys ! i)"
        by simp
    qed
    thus ?thesis by (simp add: those_eq_Some)
  qed

  \<comment> \<open>Distinctness: tuple_field_names is distinct, and equals map fst (zip ...) when lengths match\<close>
  have fst_zip_eq: "map fst (zip ?names newTms) = ?names"
    using len_list len_names by simp
  have distinct_zipped: "distinct (map fst (zip ?names newTms))"
    using fst_zip_eq distinct_tuple_field_names by simp

  show ?case
    using newTm_eq ty_eq those_ok distinct_zipped fst_zip_eq
    by simp
next
  \<comment> \<open>Case: BabTm_Record\<close>
  case (11 env typedefs ghost loc flds next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?names = "map fst flds"
  \<comment> \<open>Extract elaboration results\<close>
  from "11.prems"(1) have no_dup: "first_duplicate_name fst flds = None"
    by (auto split: option.splits)
  hence distinct_names: "distinct ?names"
    by (rule first_duplicate_name_None_implies_distinct)
  from "11.prems"(1) no_dup obtain newTms tys where
    elab_list: "elab_term_list env typedefs ghost (map snd flds) next_mv
                = Inr (newTms, tys, next_mv')" and
    newTm_eq: "newTm = CoreTm_Record (zip ?names newTms)" and
    ty_eq: "ty = CoreTy_Record (zip ?names tys)"
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>IH on the field term list\<close>
  have ih: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty) newTms tys"
    using "11.IH"[OF no_dup elab_list "11.prems"(2,3,4)] .

  \<comment> \<open>Fields line up with tys after zipping\<close>
  have len_eq: "length newTms = length tys"
    using ih by (simp add: list_all2_lengthD)
  have len_names: "length ?names = length flds" by simp
  have len_list: "length newTms = length flds"
    using elab_term_list_length[OF elab_list] by simp
  have len_tys: "length tys = length flds"
    using len_eq len_list by simp

  \<comment> \<open>Each field of zip names newTms typechecks to the matching type\<close>
  have each_field: "\<And>i. i < length flds \<Longrightarrow>
        core_term_type ?env' ghost (snd ((zip ?names newTms) ! i)) = Some (tys ! i)"
  proof -
    fix i assume i_lt: "i < length flds"
    have snd_eq: "snd ((zip ?names newTms) ! i) = newTms ! i"
      using i_lt len_list by (simp add: len_names)
    from ih have "core_term_type ?env' ghost (newTms ! i) = Some (tys ! i)"
      using i_lt len_list len_tys
      by (simp add: list_all2_conv_all_nth)
    with snd_eq show "core_term_type ?env' ghost (snd ((zip ?names newTms) ! i)) = Some (tys ! i)"
      by simp
  qed

  \<comment> \<open>Hence `those` succeeds, via list_all2 + those_eq_Some\<close>
  have those_ok: "those (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))
                  = Some tys"
  proof -
    have len_zip: "length (zip ?names newTms) = length flds"
      using len_list len_names by simp
    have la2: "list_all2 (\<lambda>x y. x = Some y)
                 (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms)) tys"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))
            = length tys"
        using len_zip len_tys by simp
    next
      fix i assume i_lt: "i < length (map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms))"
      from i_lt len_zip have i_flds: "i < length flds" by simp
      obtain n t where nt_eq: "(zip ?names newTms) ! i = (n, t)" by (cases "(zip ?names newTms) ! i")
      from nt_eq have snd_eq: "snd ((zip ?names newTms) ! i) = t" by simp
      from each_field[OF i_flds] snd_eq have t_ty: "core_term_type ?env' ghost t = Some (tys ! i)"
        by simp
      from nt_eq t_ty i_lt len_zip
      show "map (\<lambda>(name, tm). core_term_type ?env' ghost tm) (zip ?names newTms) ! i
            = Some (tys ! i)"
        by simp
    qed
    thus ?thesis by (simp add: those_eq_Some)
  qed

  \<comment> \<open>Distinctness of the zipped names\<close>
  have distinct_zipped: "distinct (map fst (zip ?names newTms))"
    using distinct_names len_list len_names by simp

  \<comment> \<open>Zipped name list equals the original names, so the resulting record type matches\<close>
  have fst_zip_eq: "map fst (zip ?names newTms) = ?names"
    using len_list len_names by simp

  \<comment> \<open>Put it all together\<close>
  show ?case
    using newTm_eq ty_eq those_ok distinct_zipped fst_zip_eq
    by simp

next
  \<comment> \<open>Case: BabTm_RecordUpdate\<close>
  case (12 env typedefs ghost loc tm flds next_mv)
  let ?is_flex = "(\<lambda>n. n |\<notin>| TE_TypeVars env)"
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"

  \<comment> \<open>Extract elaboration results\<close>
  from "12.prems"(1) have no_dup: "first_duplicate_name fst flds = None"
    by (auto split: option.splits)
  from "12.prems"(1) no_dup obtain parentTm parentTy next_mv1 where
    elab_parent: "elab_term env typedefs ghost tm next_mv = Inr (parentTm, parentTy, next_mv1)"
    by (auto split: sum.splits)
  from "12.prems"(1) no_dup elab_parent obtain parentFields where
    parent_rec: "parentTy = CoreTy_Record parentFields"
    by (auto simp: Let_def unify_update_args_def build_updated_record_def
             split: sum.splits CoreType.splits option.splits if_splits prod.splits)
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
  from "12.prems"(1) no_dup elab_parent parent_rec fields_exist elab_updates
  obtain coercedUpdates finalSubst where
    unify_result: "unify_update_args ?is_flex loc (map fst flds) newUpdateTms actualTypes parentFields
                   = Inr (coercedUpdates, finalSubst)"
    by (auto simp: Let_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  from "12.prems"(1) no_dup elab_parent parent_rec fields_exist elab_updates unify_result
  have next_mv_eq: "next_mv' = next_mv2"
    by (auto simp: Let_def build_updated_record_def
             split: sum.splits option.splits if_splits prod.splits)
  from "12.prems"(1) no_dup elab_parent parent_rec fields_exist elab_updates unify_result
  have result_eq:
    "newTm = fst (build_updated_record finalSubst parentTm parentFields coercedUpdates)"
    "ty = snd (build_updated_record finalSubst parentTm parentFields coercedUpdates)"
    by (auto simp: Let_def split: prod.splits)

  \<comment> \<open>Monotonicity\<close>
  have mono_1: "next_mv \<le> next_mv1"
    using "12.IH"(1)[OF no_dup] elab_parent elab_term_next_mv_monotone by simp
  have pair1: "(parentTm, parentTy, next_mv1) = (parentTm, parentTy, next_mv1)" by simp
  have pair2: "(parentTy, next_mv1) = (parentTy, next_mv1)" by simp
  have mono_2: "next_mv1 \<le> next_mv2"
    using "12.IH"(2)[OF no_dup elab_parent pair1 pair2 parent_rec fields_exist] elab_updates 
      elab_term_list_next_mv_monotone by simp

  \<comment> \<open>IH on parent: parentTm has type parentTy in sub-extended env\<close>
  have ih_parent_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost parentTm
                       = Some (CoreTy_Record parentFields)"
    using "12.IH"(1)[OF no_dup elab_parent] parent_rec "12.prems"(2,3,4) by simp
  have ih_parent: "core_term_type ?env' ghost parentTm = Some (CoreTy_Record parentFields)"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_parent_sub, where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp

  \<comment> \<open>Freshness for elab_term_list\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv1"
    using "12.prems"(4) mono_1 by fastforce

  \<comment> \<open>IH on update terms\<close>
  have ih_updates_sub: "list_all2 (\<lambda>tm ty. core_term_type
                          (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty)
                        newUpdateTms actualTypes"
    using "12.IH"(2)[OF no_dup elab_parent pair1 pair2 parent_rec fields_exist elab_updates]
          "12.prems"(2,3) fresh_1 by simp
  have ih_updates: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty)
                    newUpdateTms actualTypes"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv2) ghost tm = Some ty \<Longrightarrow>
                  core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono[where lo=next_mv1 and hi=next_mv2
                                                        and lo'=next_mv and hi'=next_mv']
            mono_1 mono_2 next_mv_eq by simp
    thus ?thesis using ih_updates_sub by (auto elim!: list_all2_mono)
  qed

  have wf': "tyenv_well_formed ?env'"
    using "12.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast

  \<comment> \<open>Lengths\<close>
  have len_updates: "length newUpdateTms = length actualTypes"
    using ih_updates by (simp add: list_all2_lengthD)
  have len_flds: "length newUpdateTms = length flds"
    using elab_updates elab_term_list_length by fastforce

  \<comment> \<open>Well-kindedness and runtime for actualTypes in ?env'\<close>
  have actualTypes_wk: "\<forall>(name, ty) \<in> set (zip (map fst flds) actualTypes). is_well_kinded ?env' ty"
  proof (clarsimp)
    fix name ty assume "(name, ty) \<in> set (zip (map fst flds) actualTypes)"
    then obtain i where i_lt: "i < length actualTypes" and ty_eq: "ty = actualTypes ! i"
      using len_flds by (auto simp: set_zip in_set_conv_nth)
    from ih_updates have "core_term_type ?env' ghost (newUpdateTms ! i) = Some ty"
      using i_lt len_updates ty_eq by (simp add: list_all2_conv_all_nth)
    thus "is_well_kinded ?env' ty"
      using core_term_type_well_kinded wf' by blast
  qed

  (* Use the helper lemma to complete the proof *)
  show ?case
    using elab_term_correct_record_update "12.prems"(1,2,4) elab_parent elab_updates 
      ih_parent ih_updates parent_rec by blast

next
  \<comment> \<open>Case: BabTm_TupleProj\<close>
  case (13 env typedefs ghost loc tm idx next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract elaboration results\<close>
  from "13.prems"(1) obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env typedefs ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)"
    by (auto split: sum.splits)
  from "13.prems"(1) elab_sub obtain fieldTypes where
    sub_ty_eq: "subTy = CoreTy_Record fieldTypes"
    by (auto simp del: nat_to_string.simps split: CoreType.splits option.splits)
  from "13.prems"(1) elab_sub sub_ty_eq obtain fldTy where
    fld_lookup: "map_of fieldTypes (nat_to_string idx) = Some fldTy" and
    newTm_eq: "newTm = CoreTm_RecordProj newSubTm (nat_to_string idx)" and
    ty_eq: "ty = fldTy" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto simp del: nat_to_string.simps split: option.splits)

  \<comment> \<open>IH on the sub-term\<close>
  have ih: "core_term_type ?env' ghost newSubTm = Some (CoreTy_Record fieldTypes)"
    using "13.IH" elab_sub sub_ty_eq next_mv_eq "13.prems"(2,3,4)
    by (simp del: nat_to_string.simps)

  \<comment> \<open>Put it together\<close>
  show ?case
    using newTm_eq ty_eq ih fld_lookup by (simp del: nat_to_string.simps)
next
  \<comment> \<open>Case: BabTm_RecordProj\<close>
  case (14 env typedefs ghost loc tm fldName next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract elaboration results\<close>
  from "14.prems"(1) obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env typedefs ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)"
    by (auto split: sum.splits)
  from "14.prems"(1) elab_sub obtain fieldTypes where
    sub_ty_eq: "subTy = CoreTy_Record fieldTypes"
    by (auto split: CoreType.splits option.splits)
  from "14.prems"(1) elab_sub sub_ty_eq obtain fldTy where
    fld_lookup: "map_of fieldTypes fldName = Some fldTy" and
    newTm_eq: "newTm = CoreTm_RecordProj newSubTm fldName" and
    ty_eq: "ty = fldTy" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto split: option.splits)

  \<comment> \<open>IH on the sub-term\<close>
  have ih: "core_term_type ?env' ghost newSubTm = Some (CoreTy_Record fieldTypes)"
    using "14.IH" elab_sub sub_ty_eq next_mv_eq "14.prems"(2,3,4) by simp

  \<comment> \<open>Put it together\<close>
  show ?case
    using newTm_eq ty_eq ih fld_lookup by simp
next
  \<comment> \<open>Case: BabTm_ArrayProj (undefined)\<close>
  case (15 env typedefs ghost loc tm idxs next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_Match (undefined)\<close>
  case (16 env typedefs ghost loc scrut arms next_mv)
  then show ?case sorry
next
  \<comment> \<open>Case: BabTm_Sizeof\<close>
  case (17 env typedefs ghost loc tm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  \<comment> \<open>Extract elaboration results\<close>
  from "17.prems"(1) obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env typedefs ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)"
    by (auto split: sum.splits)
  from "17.prems"(1) elab_sub obtain elemTy dims where
    sub_ty_eq: "subTy = CoreTy_Array elemTy dims"
    by (auto split: CoreType.splits option.splits if_splits)
  from "17.prems"(1) elab_sub sub_ty_eq have
    guard: "\<not> (list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue newSubTm \<and> ghost = NotGhost)" and
    newTm_eq: "newTm = CoreTm_Sizeof newSubTm" and
    ty_eq: "ty = sizeof_type dims" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto split: if_splits)

  \<comment> \<open>IH on the sub-term\<close>
  have ih: "core_term_type ?env' ghost newSubTm = Some (CoreTy_Array elemTy dims)"
    using "17.IH" elab_sub sub_ty_eq next_mv_eq "17.prems"(2,3,4) by simp

  \<comment> \<open>Put it together\<close>
  show ?case
    using newTm_eq ty_eq ih guard by simp
next
  \<comment> \<open>Case: BabTm_Allocated\<close>
  case (18 env typedefs ghost loc tm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  from "18.prems"(1) have ghost_eq: "ghost = Ghost"
    by (auto split: if_splits)
  from "18.prems"(1) ghost_eq obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env typedefs ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)" and
    newTm_eq: "newTm = CoreTm_Allocated newSubTm" and
    ty_eq: "ty = CoreTy_Bool" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto split: sum.splits)
  have ih: "core_term_type ?env' ghost newSubTm = Some subTy"
    using "18.IH" ghost_eq elab_sub next_mv_eq "18.prems"(2,3,4) by simp
  show ?case
    using newTm_eq ty_eq ghost_eq ih by simp
next
  \<comment> \<open>Case: BabTm_Old\<close>
  case (19 env typedefs ghost loc tm next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  from "19.prems"(1) have ghost_eq: "ghost = Ghost"
    by (auto split: if_splits)
  from "19.prems"(1) ghost_eq obtain newSubTm subTy next_mv_sub where
    elab_sub: "elab_term env typedefs ghost tm next_mv = Inr (newSubTm, subTy, next_mv_sub)" and
    newTm_eq: "newTm = CoreTm_Old newSubTm" and
    ty_eq: "ty = subTy" and
    next_mv_eq: "next_mv' = next_mv_sub"
    by (auto split: sum.splits)
  have ih: "core_term_type ?env' ghost newSubTm = Some subTy"
    using "19.IH" ghost_eq elab_sub next_mv_eq "19.prems"(2,3,4) by simp
  show ?case
    using newTm_eq ty_eq ghost_eq ih by simp
next
  \<comment> \<open>Case: elab_term_list empty\<close>
  case (20 env typedefs ghost next_mv)
  from "20.prems"(1) have "newTms = []" and "tys = []" by simp_all
  thus ?case by simp
next
  \<comment> \<open>Case: elab_term_list cons\<close>
  case (21 env typedefs ghost tm tms next_mv)
  let ?env' = "extend_env_with_tyvars env ghost next_mv next_mv'"
  from "21.prems"(1) obtain tm' ty' next_mv1 tms' tys' next_mv'' where
    elab_head: "elab_term env typedefs ghost tm next_mv = Inr (tm', ty', next_mv1)" and
    elab_tail: "elab_term_list env typedefs ghost tms next_mv1 = Inr (tms', tys', next_mv'')" and
    results: "newTms = tm' # tms'" "tys = ty' # tys'"
    by (auto split: sum.splits)
  \<comment> \<open>Cons forwards elab_term_list's next_mv, so next_mv' = next_mv''\<close>
  from "21.prems"(1) elab_head elab_tail results have next_mv_eq: "next_mv' = next_mv''"
    by (auto split: sum.splits)
  have mono_1: "next_mv \<le> next_mv1"
    using elab_term_next_mv_monotone[OF elab_head] .
  have mono_2: "next_mv1 \<le> next_mv''"
    using elab_term_list_next_mv_monotone[OF elab_tail] .
  \<comment> \<open>Freshness carries through the head sub-call\<close>
  have fresh_1: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> n < next_mv1"
    using "21.prems"(4) mono_1 by fastforce
  \<comment> \<open>IH for head, lifted to ?env'\<close>
  have ih_head_sub: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv1) ghost tm' = Some ty'"
    using "21.IH"(1) elab_head "21.prems"(2,3,4) by simp
  have ih_head: "core_term_type ?env' ghost tm' = Some ty'"
    using core_term_type_extend_env_with_tyvars_mono[OF ih_head_sub, where lo'=next_mv and hi'=next_mv']
          mono_1 mono_2 next_mv_eq by simp
  \<comment> \<open>IH for tail, lifted to ?env'\<close>
  have ih_tail_sub: "list_all2 (\<lambda>tm ty. core_term_type
                                  (extend_env_with_tyvars env ghost next_mv1 next_mv'') ghost tm = Some ty)
                               tms' tys'"
    using "21.IH"(3) elab_head elab_tail "21.prems"(2,3) fresh_1 by simp
  have ih_tail: "list_all2 (\<lambda>tm ty. core_term_type ?env' ghost tm = Some ty) tms' tys'"
  proof -
    have "\<And>tm ty. core_term_type (extend_env_with_tyvars env ghost next_mv1 next_mv'') ghost tm = Some ty \<Longrightarrow>
                  core_term_type ?env' ghost tm = Some ty"
      using core_term_type_extend_env_with_tyvars_mono[where lo=next_mv1 and hi=next_mv''
                                                        and lo'=next_mv and hi'=next_mv']
            mono_1 mono_2 next_mv_eq by simp
    thus ?thesis using ih_tail_sub by (auto elim!: list_all2_mono)
  qed
  show ?case using ih_head ih_tail results by simp
qed

end

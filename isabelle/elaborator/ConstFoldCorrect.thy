theory ConstFoldCorrect
  imports ConstFold "../core/CoreModuleTypecheck" "../interpreter/TypeSoundnessHelpers3"
begin

(* This theory proves two important (families of) results:

   1) eval_const_type_preservation, fold_const_type_preservation: If a well-typed
      (NotGhost) term with ground embedded types evaluates (against a map of well-typed
      values) to a value, then that value has the same type as the original term.

   2) eval_const_interp_agree, fold_const_interp_agree, fold_const_is_core_evaluation:
      These basically say that eval_const and fold_const are equivalent to running the
      normal Core interpreter (interp_term) in a suitable InterpState.

   Note: eval_const type preservation is proved directly by induction. We can't directly
   use the interpreter's type_soundness theorem (because that only applies to "fully
   ground" states, with no unresolved type variables, but eval_const is used during
   separate compilation where there might be unresolved abstract types). However, we
   can re-use some of the interpreter's helper lemmas, e.g. eval_binop_sound.
*)


(* ========================================================================== *)
(* Small helpers                                                              *)
(* ========================================================================== *)

(* Unpacking Option.those. *)
lemma those_some_nth:
  assumes "those xs = Some ys"
  shows "length ys = length xs \<and> (\<forall>i < length xs. xs ! i = Some (ys ! i))"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems obtain y ys' where
    x_eq: "x = Some y" and rest: "those xs = Some ys'" and ys_eq: "ys = y # ys'"
    by (auto split: option.splits)
  from Cons.IH[OF rest] show ?case
    by (auto simp: x_eq ys_eq nth_Cons split: nat.splits)
qed


(* ========================================================================== *)
(* Type preservation for the shared operator helpers *)
(* ========================================================================== *)

(* Unary operators. Follows from the interpreter's eval_unop_sound,
   instantiated at an arbitrary (unit) InterpState: its IS_TyArgs
   substitution is a no-op on the unop's result type. *)
lemma eval_unop_sound_values:
  assumes typing: "core_term_type env NotGhost (CoreTm_Unop op operand) = Some ty"
      and op_typing: "core_term_type env NotGhost operand = Some operandTy"
      and vt: "value_has_type env opVal operandTy"
      and ev: "eval_unop op opVal = Inr v"
  shows "value_has_type env v ty"
proof -
  have "sound_term_result (undefined :: unit InterpState) env ty (eval_unop op opVal)"
    by (rule eval_unop_sound[OF typing op_typing vt])
  with ev show ?thesis
    using unop_type_apply_subst(2)[OF typing op_typing] by simp
qed

(* Binary operators. Follows from the interpreter's eval_binop_sound in the
   same way. *)
lemma eval_binop_sound_values:
  assumes typing: "core_term_type env NotGhost (CoreTm_Binop op lhs rhs) = Some ty"
      and lhs_typing: "core_term_type env NotGhost lhs = Some lhsTy"
      and rhs_typing: "core_term_type env NotGhost rhs = Some rhsTy"
      and lhs_typed: "value_has_type env lhsVal lhsTy"
      and rhs_typed: "value_has_type env rhsVal rhsTy"
      and ev: "eval_binop op lhsVal rhsVal = Inr v"
  shows "value_has_type env v ty"
proof -
  have "sound_term_result (undefined :: unit InterpState) env ty (eval_binop op lhsVal rhsVal)"
    by (rule eval_binop_sound[OF typing lhs_typing rhs_typing lhs_typed rhs_typed])
  with ev show ?thesis
    using binop_result_apply_subst[OF typing lhs_typing rhs_typing] by simp
qed


(* ========================================================================== *)
(* Soundness of eval_const_list, given per-member soundness                   *)
(* ========================================================================== *)

lemma eval_const_list_sound_aux:
  assumes IH: "\<And>tm v' t. tm \<in> set tms \<Longrightarrow>
                 core_term_type env NotGhost tm = Some t \<Longrightarrow>
                 term_types_ground tm \<Longrightarrow>
                 eval_const vals tm = Inr v' \<Longrightarrow> value_has_type env v' t"
      and typings: "list_all2 (\<lambda>tm t. core_term_type env NotGhost tm = Some t
                                       \<and> term_types_ground tm) tms tys"
      and ev: "eval_const_list vals tms = Inr vs"
  shows "list_all2 (value_has_type env) vs tys"
  using IH typings ev
proof (induction tms arbitrary: tys vs)
  case Nil
  then show ?case by simp
next
  case (Cons tm tms')
  from Cons.prems(2) obtain t1 tys' where
    tys_eq: "tys = t1 # tys'" and
    hd_ok: "core_term_type env NotGhost tm = Some t1 \<and> term_types_ground tm" and
    tl_ok: "list_all2 (\<lambda>tm t. core_term_type env NotGhost tm = Some t
                               \<and> term_types_ground tm) tms' tys'"
    by (auto simp: list_all2_Cons1)
  from Cons.prems(3) obtain v1 vs' where
    ev_hd: "eval_const vals tm = Inr v1" and
    ev_tl: "eval_const_list vals tms' = Inr vs'" and
    vs_eq: "vs = v1 # vs'"
    by (auto split: sum.splits)
  have hd_typed: "value_has_type env v1 t1"
    using Cons.prems(1) hd_ok ev_hd by auto
  have tl_typed: "list_all2 (value_has_type env) vs' tys'"
    by (rule Cons.IH[OF _ tl_ok ev_tl]) (use Cons.prems(1) in auto)
  show ?case using hd_typed tl_typed tys_eq vs_eq by simp
qed


(* ========================================================================== *)
(* The main type preservation induction *)
(* ========================================================================== *)

(* Generalized over the Let-extended value map: every entry of `vals` types
   against the variable lookup in env. The premises quantify over the map
   because CoreTm_Let extends both the environment and the map in step. *)
theorem eval_const_type_preservation_gen:
  assumes "core_term_type env NotGhost tm = Some ty"
      and "term_types_ground tm"
      and "\<And>name v'. fmlookup vals name = Some v' \<Longrightarrow>
             \<exists>vty. tyenv_lookup_var env name = Some vty \<and> value_has_type env v' vty"
      and "eval_const vals tm = Inr v"
  shows "value_has_type env v ty"
  using assms
proof (induction tm arbitrary: env ty vals v)
  case (CoreTm_LitBool b)
  then show ?case by auto
next
  case (CoreTm_LitInt i)
  from CoreTm_LitInt.prems(1) obtain sign bits where
    gt: "get_type_for_int i = Some (sign, bits)" and
    ty_eq: "ty = CoreTy_FiniteInt sign bits"
    by (auto split: option.splits prod.splits)
  from CoreTm_LitInt.prems(4) gt have v_eq: "v = CV_FiniteInt sign bits i"
    by auto
  have "int_fits sign bits i"
    using gt by (auto split: if_splits)
  then show ?case using ty_eq v_eq by simp
next
  case (CoreTm_LitArray elemTy tms)
  from CoreTm_LitArray.prems(1) have
    wk: "is_well_kinded env elemTy" and
    rt: "is_runtime_type env elemTy" and
    all_typed: "list_all (\<lambda>tm. core_term_type env NotGhost tm = Some elemTy) tms" and
    len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)
  from CoreTm_LitArray.prems(2) have
    elem_ground: "type_tyvars elemTy = {}" and
    tms_ground: "list_all term_types_ground tms"
    by simp_all
  from CoreTm_LitArray.prems(4) obtain vs where
    ev_list: "eval_const_list vals tms = Inr vs" and
    v_eq: "v = make_1d_array vs"
    by (auto split: sum.splits)

  \<comment> \<open>Element soundness via the list helper.\<close>
  have typings: "list_all2 (\<lambda>tm t. core_term_type env NotGhost tm = Some t
                                    \<and> term_types_ground tm)
                   tms (replicate (length tms) elemTy)"
    using all_typed tms_ground
    by (auto simp: list_all2_conv_all_nth list_all_length)
  have memIH: "\<And>tm v' t. tm \<in> set tms \<Longrightarrow>
                 core_term_type env NotGhost tm = Some t \<Longrightarrow>
                 term_types_ground tm \<Longrightarrow>
                 eval_const vals tm = Inr v' \<Longrightarrow> value_has_type env v' t"
    using CoreTm_LitArray.IH CoreTm_LitArray.prems(3) by blast
  have vs_typed: "list_all2 (value_has_type env) vs (replicate (length tms) elemTy)"
    by (rule eval_const_list_sound_aux[OF memIH typings ev_list])
  have len_vals: "length vs = length tms"
    using vs_typed by (auto dest: list_all2_lengthD)
  have vs_elem_typed: "\<And>i. i < length vs \<Longrightarrow> value_has_type env (vs ! i) elemTy"
    using vs_typed len_vals by (auto simp: list_all2_conv_all_nth)

  \<comment> \<open>make_1d_array vs has the array type, via the shared lemma.\<close>
  have len_ok': "int_in_range (int_range Unsigned IntBits_64) (int (length vs))"
    using len_ok len_vals by simp
  have "value_has_type env (make_1d_array vs)
          (CoreTy_Array elemTy [CoreDim_Fixed (int (length vs))])"
    using make_1d_array_typed[OF wk rt elem_ground vs_elem_typed len_ok'] .
  then show ?case using v_eq ty_eq len_vals by simp
next
  case (CoreTm_Var name)
  from CoreTm_Var.prems(1) have lk: "tyenv_lookup_var env name = Some ty"
    by (auto split: option.splits if_splits)
  from CoreTm_Var.prems(4) have vlk: "fmlookup vals name = Some v"
    by (auto split: option.splits)
  from CoreTm_Var.prems(3)[OF vlk] obtain vty where
    "tyenv_lookup_var env name = Some vty" and "value_has_type env v vty" by blast
  with lk show ?case by simp
next
  case (CoreTm_Cast targetTy operand)
  from CoreTm_Cast.prems(1) have ty_eq: "ty = targetTy"
    by (auto split: option.splits if_splits)
  from CoreTm_Cast.prems(4) obtain i sign bits where
    tgt: "targetTy = CoreTy_FiniteInt sign bits" and
    fits: "int_fits sign bits i" and
    v_eq: "v = CV_FiniteInt sign bits i"
    by (auto split: sum.splits CoreValue.splits CoreType.splits if_splits)
  show ?case using ty_eq tgt fits v_eq by simp
next
  case (CoreTm_Unop op operand)
  from CoreTm_Unop.prems(1) obtain operandTy where
    op_typing: "core_term_type env NotGhost operand = Some operandTy"
    by (auto split: option.splits)
  from CoreTm_Unop.prems(4) obtain opVal where
    ev_op: "eval_const vals operand = Inr opVal" and
    ev_unop: "eval_unop op opVal = Inr v"
    by (auto split: sum.splits)
  have opVal_typed: "value_has_type env opVal operandTy"
    using CoreTm_Unop.IH[OF op_typing _ CoreTm_Unop.prems(3) ev_op]
          CoreTm_Unop.prems(2) by simp
  show ?case
    by (rule eval_unop_sound_values[OF CoreTm_Unop.prems(1) op_typing opVal_typed ev_unop])
next
  case (CoreTm_Binop op lhs rhs)
  from CoreTm_Binop.prems(1) obtain lhsTy rhsTy where
    lhs_typing: "core_term_type env NotGhost lhs = Some lhsTy" and
    rhs_typing: "core_term_type env NotGhost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)
  from CoreTm_Binop.prems(4) obtain lhsVal rhsVal where
    ev_lhs: "eval_const vals lhs = Inr lhsVal" and
    ev_rhs: "eval_const vals rhs = Inr rhsVal" and
    ev_op: "eval_binop op lhsVal rhsVal = Inr v"
    by (auto split: sum.splits)
  from CoreTm_Binop.prems(2) have
    g_lhs: "term_types_ground lhs" and g_rhs: "term_types_ground rhs" by simp_all
  have lhs_typed: "value_has_type env lhsVal lhsTy"
    using CoreTm_Binop.IH(1)[OF lhs_typing g_lhs CoreTm_Binop.prems(3) ev_lhs] .
  have rhs_typed: "value_has_type env rhsVal rhsTy"
    using CoreTm_Binop.IH(2)[OF rhs_typing g_rhs CoreTm_Binop.prems(3) ev_rhs] .
  show ?case
    by (rule eval_binop_sound_values[OF CoreTm_Binop.prems(1) lhs_typing rhs_typing
          lhs_typed rhs_typed ev_op])
next
  case (CoreTm_Let var rhs body)
  from CoreTm_Let.prems(1) obtain rhsTy where
    rhs_typing: "core_term_type env NotGhost rhs = Some rhsTy" and
    body_typing: "core_term_type
       (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
              TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
              TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
       NotGhost body = Some ty"
    by (auto simp: Let_def split: option.splits)
  define env' where
    "env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                  TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
                  TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  have body_typing': "core_term_type env' NotGhost body = Some ty"
    using body_typing by (simp add: env'_def)
  from CoreTm_Let.prems(2) have
    g_rhs: "term_types_ground rhs" and g_body: "term_types_ground body" by simp_all
  from CoreTm_Let.prems(4) obtain rhsVal where
    ev_rhs: "eval_const vals rhs = Inr rhsVal" and
    ev_body: "eval_const (fmupd var rhsVal vals) body = Inr v"
    by (auto split: sum.splits)
  have rhs_typed: "value_has_type env rhsVal rhsTy"
    using CoreTm_Let.IH(1)[OF rhs_typing g_rhs CoreTm_Let.prems(3) ev_rhs] .
  \<comment> \<open>value_has_type is insensitive to the scope-field changes of env'.\<close>
  have cong: "\<And>v' t. value_has_type env' v' t = value_has_type env v' t"
    by (rule value_has_type_cong_env) (simp_all add: env'_def)
  have vals_ok': "\<And>name v'. fmlookup (fmupd var rhsVal vals) name = Some v' \<Longrightarrow>
        \<exists>vty. tyenv_lookup_var env' name = Some vty \<and> value_has_type env' v' vty"
  proof -
    fix name v'
    assume lk: "fmlookup (fmupd var rhsVal vals) name = Some v'"
    show "\<exists>vty. tyenv_lookup_var env' name = Some vty \<and> value_has_type env' v' vty"
    proof (cases "name = var")
      case True
      with lk have v'_eq: "v' = rhsVal" by simp
      have "tyenv_lookup_var env' var = Some rhsTy"
        by (simp add: env'_def tyenv_lookup_var_def)
      with True v'_eq rhs_typed cong show ?thesis by auto
    next
      case False
      with lk have lk0: "fmlookup vals name = Some v'" by simp
      from CoreTm_Let.prems(3)[OF lk0] obtain vty where
        lk_env: "tyenv_lookup_var env name = Some vty" and
        vt: "value_has_type env v' vty" by blast
      have "tyenv_lookup_var env' name = tyenv_lookup_var env name"
        using False by (simp add: env'_def tyenv_lookup_var_def split: option.split)
      with lk_env vt cong show ?thesis by auto
    qed
  qed
  have "value_has_type env' v ty"
    using CoreTm_Let.IH(2)[OF body_typing' g_body vals_ok' ev_body] .
  then show ?case using cong by simp
next
  case (CoreTm_Quantifier q var varTy body)
  then show ?case by simp
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  then show ?case by simp
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  from CoreTm_VariantCtor.prems(1) obtain dtName tyvars payloadTy where
    lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    args_wk: "list_all (is_well_kinded env) tyArgs" and
    args_rt: "list_all (is_runtime_type env) tyArgs" and
    not_ghost: "dtName |\<notin>| TE_GhostDatatypes env" and
    payload_typing: "core_term_type env NotGhost payload
                       = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)" and
    ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
    by (auto simp: Let_def split: option.splits if_splits)
  from CoreTm_VariantCtor.prems(2) have
    args_ground: "list_all (\<lambda>t. type_tyvars t = {}) tyArgs" and
    g_payload: "term_types_ground payload"
    by simp_all
  from CoreTm_VariantCtor.prems(4) obtain pv where
    ev_payload: "eval_const vals payload = Inr pv" and
    v_eq: "v = CV_Variant ctorName pv"
    by (auto split: sum.splits)
  have pv_typed: "value_has_type env pv
                    (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
    using CoreTm_VariantCtor.IH[OF payload_typing g_payload
            CoreTm_VariantCtor.prems(3) ev_payload] .
  show ?case
    unfolding v_eq ty_eq
    using lookup len_eq args_wk args_rt args_ground not_ghost pv_typed
    by simp
next
  case (CoreTm_Record flds)
  from CoreTm_Record.prems(1) obtain tys where
    dn: "distinct (map fst flds)" and
    those_eq: "those (map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: if_splits option.splits)
  from CoreTm_Record.prems(4) obtain vs where
    ev_list: "eval_const_list vals (map snd flds) = Inr vs" and
    v_eq: "v = CV_Record (zip (map fst flds) vs)"
    by (auto split: sum.splits)
  have len_tys: "length tys = length flds"
    using those_some_nth[OF those_eq] by simp
  have nth_typed: "\<And>i. i < length flds \<Longrightarrow>
        core_term_type env NotGhost (snd (flds ! i)) = Some (tys ! i)"
  proof -
    fix i assume i_lt: "i < length flds"
    have "(map (\<lambda>(name, tm). core_term_type env NotGhost tm) flds) ! i = Some (tys ! i)"
      using those_some_nth[OF those_eq] i_lt by simp
    thus "core_term_type env NotGhost (snd (flds ! i)) = Some (tys ! i)"
      using i_lt by (simp add: split_def)
  qed
  have typings: "list_all2 (\<lambda>tm t. core_term_type env NotGhost tm = Some t
                                    \<and> term_types_ground tm) (map snd flds) tys"
    unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length (map snd flds) = length tys" using len_tys by simp
  next
    fix i assume "i < length (map snd flds)"
    hence i_lt: "i < length flds" by simp
    show "core_term_type env NotGhost (map snd flds ! i) = Some (tys ! i)"
      using nth_typed[OF i_lt] i_lt by simp
  next
    fix i assume "i < length (map snd flds)"
    hence i_lt: "i < length flds" by simp
    show "term_types_ground (map snd flds ! i)"
      using CoreTm_Record.prems(2) i_lt by (auto simp: list_all_length)
  qed
  have memIH: "\<And>tm v' t. tm \<in> set (map snd flds) \<Longrightarrow>
                 core_term_type env NotGhost tm = Some t \<Longrightarrow>
                 term_types_ground tm \<Longrightarrow>
                 eval_const vals tm = Inr v' \<Longrightarrow> value_has_type env v' t"
  proof -
    fix tm v' t
    assume "tm \<in> set (map snd flds)"
    then obtain nm where mem: "(nm, tm) \<in> set flds" by auto
    assume "core_term_type env NotGhost tm = Some t"
       and "term_types_ground tm"
       and "eval_const vals tm = Inr v'"
    with CoreTm_Record.IH[OF mem] CoreTm_Record.prems(3)
    show "value_has_type env v' t" by fastforce
  qed
  have vs_typed: "list_all2 (value_has_type env) vs tys"
    by (rule eval_const_list_sound_aux[OF memIH typings ev_list])
  have len_vs: "length vs = length tys"
    using vs_typed by (auto dest: list_all2_lengthD)
  have len_names: "length (map fst flds) = length vs"
    using len_vs len_tys by simp
  show ?case
    unfolding v_eq ty_eq
    by (rule cv_record_typed[OF vs_typed dn len_names])
next
  case (CoreTm_RecordProj tm fldName)
  from CoreTm_RecordProj.prems(1) obtain fieldTypes where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Record fieldTypes)" and
    mo_ty: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)
  from CoreTm_RecordProj.prems(4) obtain nameValPairs where
    ev_tm: "eval_const vals tm = Inr (CV_Record nameValPairs)" and
    mo_v: "map_of nameValPairs fldName = Some v"
    by (auto split: sum.splits CoreValue.splits option.splits)
  have rec_typed: "value_has_type env (CV_Record nameValPairs) (CoreTy_Record fieldTypes)"
    using CoreTm_RecordProj.IH[OF tm_typing _ CoreTm_RecordProj.prems(3) ev_tm]
          CoreTm_RecordProj.prems(2) by simp
  hence all2: "list_all2 (\<lambda>(n1, fldVal) (n2, fldTy). n1 = n2 \<and>
                            value_has_type env fldVal fldTy)
                 nameValPairs fieldTypes"
    by simp
  from map_of_list_all2[OF all2 mo_ty] obtain v' where
    "map_of nameValPairs fldName = Some v'" and "value_has_type env v' ty" by blast
  with mo_v show ?case by simp
next
  case (CoreTm_VariantProj tm expectedCtor)
  from CoreTm_VariantProj.prems(1) obtain dtName tyArgs dtName2 tyvars payloadTy where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Datatype dtName tyArgs)" and
    ctor_lk: "fmlookup (TE_DataCtors env) expectedCtor = Some (dtName2, tyvars, payloadTy)" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_VariantProj.prems(4) obtain actualCtor payload where
    ev_tm: "eval_const vals tm = Inr (CV_Variant actualCtor payload)" and
    ctor_eq: "actualCtor = expectedCtor" and
    v_eq: "v = payload"
    by (auto split: sum.splits CoreValue.splits if_splits)
  have scrut_typed: "value_has_type env (CV_Variant actualCtor payload)
                       (CoreTy_Datatype dtName tyArgs)"
    using CoreTm_VariantProj.IH[OF tm_typing _ CoreTm_VariantProj.prems(3) ev_tm]
          CoreTm_VariantProj.prems(2) by simp
  \<comment> \<open>The value's clause for the (same) constructor gives the payload typing.\<close>
  have "value_has_type env payload
          (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
    using scrut_typed ctor_eq ctor_lk
    by (auto split: option.splits)
  then show ?case using v_eq ty_eq by simp
next
  case (CoreTm_ArrayProj arr idxTms)
  from CoreTm_ArrayProj.prems(1) obtain elemTy dims where
    arr_typing: "core_term_type env NotGhost arr = Some (CoreTy_Array elemTy dims)" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_ArrayProj.prems(4) obtain sizes elementMap indexVals indices where
    ev_arr: "eval_const vals arr = Inr (CV_Array sizes elementMap)" and
    ev_idx: "eval_const_list vals idxTms = Inr indexVals" and
    idx_ok: "interpret_index_vals indexVals = Inr indices" and
    elem_lk: "fmlookup elementMap indices = Some v"
    by (auto split: sum.splits CoreValue.splits option.splits)
  have arr_typed: "value_has_type env (CV_Array sizes elementMap)
                     (CoreTy_Array elemTy dims)"
    using CoreTm_ArrayProj.IH(1)[OF arr_typing _ CoreTm_ArrayProj.prems(3) ev_arr]
          CoreTm_ArrayProj.prems(2) by simp
  hence "\<forall>idx val. fmlookup elementMap idx = Some val \<longrightarrow> value_has_type env val elemTy"
    by simp
  then show ?case using elem_lk ty_eq by blast
next
  case (CoreTm_Match scrut arms)
  from CoreTm_Match.prems(1) obtain scrutTy where
    scrut_typing: "core_term_type env NotGhost scrut = Some scrutTy" and
    nonempty: "arms \<noteq> []" and
    hd_typing: "core_term_type env NotGhost (snd (hd arms)) = Some ty" and
    tl_typed: "list_all (\<lambda>body. core_term_type env NotGhost body = Some ty)
                 (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)
  from CoreTm_Match.prems(4) obtain scrutVal armTm where
    ev_scrut: "eval_const vals scrut = Inr scrutVal" and
    fma: "find_matching_arm scrutVal arms = Inr armTm" and
    ev_arm: "eval_const vals armTm = Inr v"
    by (auto split: sum.splits)
  from find_matching_arm_in_arms[OF fma] obtain pat where
    mem: "(pat, armTm) \<in> set arms" by auto
  have arm_typing: "core_term_type env NotGhost armTm = Some ty"
    by (rule match_arm_body_typed[OF nonempty hd_typing tl_typed mem])
  have arm_ground: "term_types_ground armTm"
    using CoreTm_Match.prems(2) mem by (auto simp: list_all_iff)
  have arm_snd: "armTm \<in> snd ` set arms" using mem by force
  show ?case
    using CoreTm_Match.IH(2) CoreTm_Match.prems(3) arm_snd arm_ground arm_typing
      ev_arm by fastforce
next
  case (CoreTm_Sizeof tm)
  from CoreTm_Sizeof.prems(1) obtain elemTy dims where
    tm_typing: "core_term_type env NotGhost tm = Some (CoreTy_Array elemTy dims)" and
    ty_eq: "ty = sizeof_type dims"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_Sizeof.prems(4) obtain sizes vm where
    ev_tm: "eval_const vals tm = Inr (CV_Array sizes vm)" and
    v_eq: "v = array_size_to_value sizes"
    by (auto split: sum.splits CoreValue.splits)
  have arr_typed: "value_has_type env (CV_Array sizes vm) (CoreTy_Array elemTy dims)"
    using CoreTm_Sizeof.IH[OF tm_typing _ CoreTm_Sizeof.prems(3) ev_tm]
          CoreTm_Sizeof.prems(2) by simp
  hence fms: "fmap_matches_sizes sizes vm" and smd: "sizes_match_dims sizes dims"
    by simp_all
  have sv: "sizes_valid sizes"
    using fms by (simp add: fmap_matches_sizes_def)
  show ?case
    unfolding v_eq ty_eq
    by (rule array_size_to_value_has_sizeof_type[OF sv smd])
next
  case (CoreTm_Allocated tm)
  then show ?case by simp
next
  case (CoreTm_Old tm)
  then show ?case by simp
next
  case (CoreTm_Default defTy)
  then show ?case by simp
qed


(* ========================================================================== *)
(* Top-level corollary: eval_const_type_preservation *)
(* ========================================================================== *)

(* If eval_const succeeds, its result has exactly the type predicted by the typechecker.
   The premises are all ones that can be supplied by the elaborator when it is evaluating
   a global constant. *)
theorem eval_const_type_preservation:
  assumes typing: "core_term_type env NotGhost tm = Some ty"
      and locals: "TE_LocalVars env = fmempty"
      and gvals: "module_globals_well_typed env globalVals"
      and ground: "term_types_ground tm"
      and ev: "eval_const globalVals tm = Inr v"
  shows "value_has_type env v ty"
proof (rule eval_const_type_preservation_gen[OF typing ground _ ev])
  fix name v'
  assume lk: "fmlookup globalVals name = Some v'"
  from gvals lk obtain vty where
    decl: "fmlookup (TE_GlobalVars env) name = Some vty" and
    vt: "value_has_type env v' vty"
    unfolding module_globals_well_typed_def by blast
  have "tyenv_lookup_var env name = Some vty"
    using decl locals by (simp add: tyenv_lookup_var_def)
  with vt show "\<exists>vty. tyenv_lookup_var env name = Some vty \<and> value_has_type env v' vty"
    by blast
qed

(* Two well-typed value maps combine to a well-typed map (fmadd resolves
   each name to one side or the other; no domain disjointness is needed). *)
lemma module_globals_well_typed_fmadd:
  assumes a: "module_globals_well_typed env a"
      and b: "module_globals_well_typed env b"
  shows "module_globals_well_typed env (a ++\<^sub>f b)"
  unfolding module_globals_well_typed_def
proof (intro allI impI)
  fix name v assume "fmlookup (a ++\<^sub>f b) name = Some v"
  then have "fmlookup b name = Some v \<or> fmlookup a name = Some v"
    by (auto split: if_splits)
  then show "\<exists>declTy. fmlookup (TE_GlobalVars env) name = Some declTy \<and>
               value_has_type env v declTy"
    using a b unfolding module_globals_well_typed_def by blast
qed

(* Soundness of the elaborator's entry point: a successful fold yields a
   value of the initializer's type. The groundness and evaluation facts are
   what fold_const's own checks guarantee. *)
theorem fold_const_type_preservation:
  assumes fc: "fold_const globalVals loc tm = Inr v"
      and typing: "core_term_type env NotGhost tm = Some ty"
      and locals: "TE_LocalVars env = fmempty"
      and gvals: "module_globals_well_typed env globalVals"
  shows "value_has_type env v ty"
proof -
  from fc have ground: "term_types_ground tm"
         and ev: "eval_const globalVals tm = Inr v"
    unfolding fold_const_def by (auto simp: Let_def split: if_splits sum.splits)
  show ?thesis by (rule eval_const_type_preservation[OF typing locals gvals ground ev])
qed


(* ========================================================================== *)
(* Agreement with the interpreter                                             *)
(* ========================================================================== *)

(* State/value-map agreement predicate. Every value in the value-map must
   also exist in the InterpState, either as a local or a global, and the value
   in the InterpState's store must agree.

   At the top-level, the value map will only contain globals, but during evaluation
   of Let terms it might also include locals (which is why locals have to be included). *)
definition vals_agree :: "'w InterpState \<Rightarrow> (string, CoreValue) fmap \<Rightarrow> bool" where
  "vals_agree st vals = (\<forall>name v. fmlookup vals name = Some v \<longrightarrow>
     (case fmlookup (IS_Locals st) name of
        Some addr \<Rightarrow> addr < length (IS_Store st) \<and> IS_Store st ! addr = v
      | None \<Rightarrow>
        (case fmlookup (IS_Refs st) name of
           Some (addr, path) \<Rightarrow> addr < length (IS_Store st)
                                \<and> get_value_at_path (IS_Store st ! addr) path = Inr v
         | None \<Rightarrow> fmlookup (IS_Globals st) name = Some v)))"

(* A tracked name evaluates to its value under the interpreter. *)
lemma vals_agree_lookup:
  assumes ag: "vals_agree st vals"
      and lk: "fmlookup vals name = Some v"
  shows "interp_term (Suc f) (st :: 'w InterpState) (CoreTm_Var name) = Inr v"
proof -
  from ag lk have "(case fmlookup (IS_Locals st) name of
      Some addr \<Rightarrow> addr < length (IS_Store st) \<and> IS_Store st ! addr = v
    | None \<Rightarrow>
      (case fmlookup (IS_Refs st) name of
         Some (addr, path) \<Rightarrow> addr < length (IS_Store st)
                              \<and> get_value_at_path (IS_Store st ! addr) path = Inr v
       | None \<Rightarrow> fmlookup (IS_Globals st) name = Some v))"
    unfolding vals_agree_def by blast
  thus ?thesis by (auto split: option.splits)
qed

(* vals_agree is preserved by the state extension interp_term performs for CoreTm_Let. *)
lemma vals_agree_extend:
  assumes ag: "vals_agree st vals"
      and store': "IS_Store st' = IS_Store st @ [rhsVal]"
      and locals': "IS_Locals st' = fmupd var (length (IS_Store st)) (IS_Locals st)"
      and refs': "IS_Refs st' = fmdrop var (IS_Refs st)"
      and globals': "IS_Globals st' = IS_Globals st"
  shows "vals_agree st' (fmupd var rhsVal vals)"
  unfolding vals_agree_def
proof (intro allI impI)
  fix name v assume lk: "fmlookup (fmupd var rhsVal vals) name = Some v"
  show "(case fmlookup (IS_Locals st') name of
        Some addr \<Rightarrow> addr < length (IS_Store st') \<and> IS_Store st' ! addr = v
      | None \<Rightarrow>
        (case fmlookup (IS_Refs st') name of
           Some (addr, path) \<Rightarrow> addr < length (IS_Store st')
                                \<and> get_value_at_path (IS_Store st' ! addr) path = Inr v
         | None \<Rightarrow> fmlookup (IS_Globals st') name = Some v))"
  proof (cases "name = var")
    case True
    with lk have v_eq: "v = rhsVal" by simp
    show ?thesis using True v_eq by (simp add: locals' store')
  next
    case False
    with lk have lk0: "fmlookup vals name = Some v" by simp
    from ag lk0 have base: "(case fmlookup (IS_Locals st) name of
        Some addr \<Rightarrow> addr < length (IS_Store st) \<and> IS_Store st ! addr = v
      | None \<Rightarrow>
        (case fmlookup (IS_Refs st) name of
           Some (addr, path) \<Rightarrow> addr < length (IS_Store st)
                                \<and> get_value_at_path (IS_Store st ! addr) path = Inr v
         | None \<Rightarrow> fmlookup (IS_Globals st) name = Some v))"
      unfolding vals_agree_def by blast
    show ?thesis using base False
      by (auto simp: locals' refs' globals' store' nth_append split: option.splits)
  qed
qed

(* Fuel plumbing helpers.
   Each lemma turns per-subterm agreement (at ANY sufficiently large fuel)
   into agreement for a term whose interp clause spends one Suc and then
   evaluates the subterm(s) at the decremented fuel. The `step` premise is
   the per-clause computation, discharged by simp at each use site. *)

lemma agree_leafI:
  fixes st :: "'w InterpState"
  assumes "\<And>f. interp_term (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term f st tm = eval_const vals tm"
proof -
  have "\<forall>f\<ge>Suc 0. interp_term f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc 0 \<le> f"
    then obtain f' where "f = Suc f'" using Suc_le_D by auto
    thus "interp_term f st tm = eval_const vals tm" using assms by blast
  qed
  thus ?thesis by blast
qed

lemma agree_lift1:
  fixes st :: "'w InterpState" and st1 :: "'w InterpState"
  assumes sub: "\<exists>N. \<forall>f\<ge>N. interp_term f st1 t1 = eval_const vals1 t1"
      and step: "\<And>f. interp_term f st1 t1 = eval_const vals1 t1 \<Longrightarrow>
                   interp_term (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term f st tm = eval_const vals tm"
proof -
  obtain N where N: "\<forall>f\<ge>N. interp_term f st1 t1 = eval_const vals1 t1"
    using sub by blast
  have "\<forall>f\<ge>Suc N. interp_term f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc N \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge: "N \<le> f'"
      using Suc_le_D by auto
    have "interp_term (Suc f') st tm = eval_const vals tm"
      by (rule step) (use N ge in blast)
    thus "interp_term f st tm = eval_const vals tm" by (simp add: f_eq)
  qed
  thus ?thesis by blast
qed

lemma agree_lift2:
  fixes st :: "'w InterpState" and st1 :: "'w InterpState" and st2 :: "'w InterpState"
  assumes sub1: "\<exists>N. \<forall>f\<ge>N. interp_term f st1 t1 = eval_const vals1 t1"
      and sub2: "\<exists>N. \<forall>f\<ge>N. interp_term f st2 t2 = eval_const vals2 t2"
      and step: "\<And>f. interp_term f st1 t1 = eval_const vals1 t1 \<Longrightarrow>
                   interp_term f st2 t2 = eval_const vals2 t2 \<Longrightarrow>
                   interp_term (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term f st tm = eval_const vals tm"
proof -
  obtain N1 where N1: "\<forall>f\<ge>N1. interp_term f st1 t1 = eval_const vals1 t1"
    using sub1 by blast
  obtain N2 where N2: "\<forall>f\<ge>N2. interp_term f st2 t2 = eval_const vals2 t2"
    using sub2 by blast
  have "\<forall>f\<ge>Suc (max N1 N2). interp_term f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc (max N1 N2) \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge1: "N1 \<le> f'" and ge2: "N2 \<le> f'"
      using Suc_le_D by force
    have "interp_term (Suc f') st tm = eval_const vals tm"
      by (rule step) (use N1 ge1 N2 ge2 in blast)+
    thus "interp_term f st tm = eval_const vals tm" by (simp add: f_eq)
  qed
  thus ?thesis by blast
qed

lemma agree_lift_list:
  fixes st :: "'w InterpState" and st1 :: "'w InterpState"
  assumes sub: "\<exists>N. \<forall>f\<ge>N. interp_term_list f st1 tms = eval_const_list vals1 tms"
      and step: "\<And>f. interp_term_list f st1 tms = eval_const_list vals1 tms \<Longrightarrow>
                   interp_term (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term f st tm = eval_const vals tm"
proof -
  obtain N where N: "\<forall>f\<ge>N. interp_term_list f st1 tms = eval_const_list vals1 tms"
    using sub by blast
  have "\<forall>f\<ge>Suc N. interp_term f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc N \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge: "N \<le> f'"
      using Suc_le_D by auto
    have "interp_term (Suc f') st tm = eval_const vals tm"
      by (rule step) (use N ge in blast)
    thus "interp_term f st tm = eval_const vals tm" by (simp add: f_eq)
  qed
  thus ?thesis by blast
qed

lemma agree_lift_tm_list:
  fixes st :: "'w InterpState" and st1 :: "'w InterpState" and st2 :: "'w InterpState"
  assumes sub1: "\<exists>N. \<forall>f\<ge>N. interp_term f st1 t1 = eval_const vals1 t1"
      and sub2: "\<exists>N. \<forall>f\<ge>N. interp_term_list f st2 tms = eval_const_list vals2 tms"
      and step: "\<And>f. interp_term f st1 t1 = eval_const vals1 t1 \<Longrightarrow>
                   interp_term_list f st2 tms = eval_const_list vals2 tms \<Longrightarrow>
                   interp_term (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term f st tm = eval_const vals tm"
proof -
  obtain N1 where N1: "\<forall>f\<ge>N1. interp_term f st1 t1 = eval_const vals1 t1"
    using sub1 by blast
  obtain N2 where N2: "\<forall>f\<ge>N2. interp_term_list f st2 tms = eval_const_list vals2 tms"
    using sub2 by blast
  have "\<forall>f\<ge>Suc (max N1 N2). interp_term f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc (max N1 N2) \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge1: "N1 \<le> f'" and ge2: "N2 \<le> f'"
      using Suc_le_D by force
    have "interp_term (Suc f') st tm = eval_const vals tm"
      by (rule step) (use N1 ge1 N2 ge2 in blast)+
    thus "interp_term f st tm = eval_const vals tm" by (simp add: f_eq)
  qed
  thus ?thesis by blast
qed

(* List-level agreement from member-level agreement (same state and map
   throughout: interp_term_list does not thread state changes). *)
lemma agree_list:
  fixes st :: "'w InterpState"
  assumes "\<And>t. t \<in> set tms \<Longrightarrow> \<exists>N. \<forall>f\<ge>N. interp_term f st t = eval_const vals t"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term_list f st tms = eval_const_list vals tms"
  using assms
proof (induction tms)
  case Nil
  have "\<forall>f\<ge>Suc 0. interp_term_list f st [] = eval_const_list vals ([] :: CoreTerm list)"
  proof (intro allI impI)
    fix f assume "Suc 0 \<le> f"
    then obtain f' where "f = Suc f'" using Suc_le_D by auto
    thus "interp_term_list f st [] = eval_const_list vals ([] :: CoreTerm list)"
      by simp
  qed
  thus ?case by blast
next
  case (Cons t ts)
  obtain N1 where N1: "\<forall>f\<ge>N1. interp_term f st t = eval_const vals t"
    using Cons.prems[of t] by auto
  have tl_agree: "\<exists>N. \<forall>f\<ge>N. interp_term_list f st ts = eval_const_list vals ts"
  proof (rule Cons.IH)
    fix ta assume "ta \<in> set ts"
    thus "\<exists>N. \<forall>f\<ge>N. interp_term f st ta = eval_const vals ta"
      using Cons.prems[of ta] by simp
  qed
  then obtain N2 where N2: "\<forall>f\<ge>N2. interp_term_list f st ts = eval_const_list vals ts"
    by blast
  have "\<forall>f\<ge>Suc (max N1 N2). interp_term_list f st (t # ts) = eval_const_list vals (t # ts)"
  proof (intro allI impI)
    fix f assume "Suc (max N1 N2) \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge1: "N1 \<le> f'" and ge2: "N2 \<le> f'"
      using Suc_le_D by force
    have h: "interp_term f' st t = eval_const vals t" using N1 ge1 by blast
    have tl: "interp_term_list f' st ts = eval_const_list vals ts" using N2 ge2 by blast
    show "interp_term_list f st (t # ts) = eval_const_list vals (t # ts)"
      by (simp add: f_eq h tl split: sum.split)
  qed
  thus ?case by blast
qed


(* ========================================================================== *)
(* The main agreement induction                                               *)
(* ========================================================================== *)

(* Generalized over the Let-extended value map and state. Structural
   induction; every case is: obtain agreement for the subterms (IH), then
   the clause-level computation is literally the same case expression on
   both sides (shared helpers), discharged by simp. *)
theorem eval_const_interp_agree_gen:
  fixes st :: "'w InterpState"
  assumes "is_constant_term tm"
      and "core_term_free_vars tm |\<subseteq>| fmdom vals"
      and "vals_agree st vals"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term f st tm = eval_const vals tm"
  using assms
proof (induction tm arbitrary: vals st)
  case (CoreTm_LitBool b)
  show ?case by (rule agree_leafI) simp
next
  case (CoreTm_LitInt i)
  show ?case by (rule agree_leafI) simp
next
  case (CoreTm_LitArray elemTy tms)
  have members: "\<And>t. t \<in> set tms \<Longrightarrow>
                   \<exists>N. \<forall>f\<ge>N. interp_term f st t = eval_const vals t"
  proof -
    fix t assume mem: "t \<in> set tms"
    have c: "is_constant_term t"
      using CoreTm_LitArray.prems(1) mem by (auto simp: list_all_iff)
    have fv: "core_term_free_vars t |\<subseteq>| fmdom vals"
      using CoreTm_LitArray.prems(2) mem
      by (fastforce simp: fsubset_iff fmember_ffUnion_fimage_fset_of_list_iff)
    show "\<exists>N. \<forall>f\<ge>N. interp_term f st t = eval_const vals t"
      using CoreTm_LitArray.IH mem c fv CoreTm_LitArray.prems(3) by blast
  qed
  show ?case
  proof (rule agree_lift_list[OF agree_list[OF members]])
    fix f assume h: "interp_term_list f st tms = eval_const_list vals tms"
    show "interp_term (Suc f) st (CoreTm_LitArray elemTy tms)
            = eval_const vals (CoreTm_LitArray elemTy tms)"
      by (simp add: h)
  qed
next
  case (CoreTm_Var name)
  have "name |\<in>| fmdom vals"
    using CoreTm_Var.prems(2) by (auto simp: fsubset_iff)
  then obtain v where lk: "fmlookup vals name = Some v"
    by (metis fmdomE)
  show ?case
  proof (rule agree_leafI)
    fix f
    have "interp_term (Suc f) st (CoreTm_Var name) = Inr v"
      by (rule vals_agree_lookup[OF CoreTm_Var.prems(3) lk])
    thus "interp_term (Suc f) st (CoreTm_Var name) = eval_const vals (CoreTm_Var name)"
      by (simp add: lk)
  qed
next
  case (CoreTm_Cast targetTy operand)
  have c: "is_constant_term operand" using CoreTm_Cast.prems(1) by simp
  have fv: "core_term_free_vars operand |\<subseteq>| fmdom vals"
    using CoreTm_Cast.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term f st operand = eval_const vals operand"
    by (rule CoreTm_Cast.IH[OF c fv CoreTm_Cast.prems(3)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term f st operand = eval_const vals operand"
    show "interp_term (Suc f) st (CoreTm_Cast targetTy operand)
            = eval_const vals (CoreTm_Cast targetTy operand)"
      by (simp add: h)
  qed
next
  case (CoreTm_Unop op operand)
  have c: "is_constant_term operand" using CoreTm_Unop.prems(1) by simp
  have fv: "core_term_free_vars operand |\<subseteq>| fmdom vals"
    using CoreTm_Unop.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term f st operand = eval_const vals operand"
    by (rule CoreTm_Unop.IH[OF c fv CoreTm_Unop.prems(3)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term f st operand = eval_const vals operand"
    show "interp_term (Suc f) st (CoreTm_Unop op operand)
            = eval_const vals (CoreTm_Unop op operand)"
      by (simp add: h)
  qed
next
  case (CoreTm_Binop op lhs rhs)
  have c1: "is_constant_term lhs" and c2: "is_constant_term rhs"
    using CoreTm_Binop.prems(1) by simp_all
  have fv1: "core_term_free_vars lhs |\<subseteq>| fmdom vals"
   and fv2: "core_term_free_vars rhs |\<subseteq>| fmdom vals"
    using CoreTm_Binop.prems(2) by (auto simp: fsubset_iff)
  have sub1: "\<exists>N. \<forall>f\<ge>N. interp_term f st lhs = eval_const vals lhs"
    by (rule CoreTm_Binop.IH(1)[OF c1 fv1 CoreTm_Binop.prems(3)])
  have sub2: "\<exists>N. \<forall>f\<ge>N. interp_term f st rhs = eval_const vals rhs"
    by (rule CoreTm_Binop.IH(2)[OF c2 fv2 CoreTm_Binop.prems(3)])
  show ?case
  proof (rule agree_lift2[OF sub1 sub2])
    fix f assume h1: "interp_term f st lhs = eval_const vals lhs"
             and h2: "interp_term f st rhs = eval_const vals rhs"
    show "interp_term (Suc f) st (CoreTm_Binop op lhs rhs)
            = eval_const vals (CoreTm_Binop op lhs rhs)"
      by (simp add: h1 h2 split: sum.split)
  qed
next
  case (CoreTm_Let var rhs body)
  have c_rhs: "is_constant_term rhs" and c_body: "is_constant_term body"
    using CoreTm_Let.prems(1) by simp_all
  have fv_rhs: "core_term_free_vars rhs |\<subseteq>| fmdom vals"
    using CoreTm_Let.prems(2) by (auto simp: fsubset_iff)
  have sub_rhs: "\<exists>N. \<forall>f\<ge>N. interp_term f st rhs = eval_const vals rhs"
    by (rule CoreTm_Let.IH(1)[OF c_rhs fv_rhs CoreTm_Let.prems(3)])
  show ?case
  proof (cases "eval_const vals rhs")
    case (Inl err)
    show ?thesis
    proof (rule agree_lift1[OF sub_rhs])
      fix f assume h: "interp_term f st rhs = eval_const vals rhs"
      show "interp_term (Suc f) st (CoreTm_Let var rhs body)
              = eval_const vals (CoreTm_Let var rhs body)"
        by (simp add: h Inl)
    qed
  next
    case (Inr rhsVal)
    define vals' where "vals' = fmupd var rhsVal vals"
    define st'' where
      "st'' = st \<lparr> IS_Store := IS_Store st @ [rhsVal],
                   IS_Locals := fmupd var (length (IS_Store st)) (IS_Locals st),
                   IS_Refs := fmdrop var (IS_Refs st),
                   IS_ConstLocals := finsert var (IS_ConstLocals st) \<rparr>"
    have ag': "vals_agree st'' vals'"
      unfolding vals'_def
      by (rule vals_agree_extend[OF CoreTm_Let.prems(3)]) (simp_all add: st''_def)
    have fv_body: "core_term_free_vars body |\<subseteq>| fmdom vals'"
      using CoreTm_Let.prems(2) by (auto simp: vals'_def fsubset_iff)
    have sub_body: "\<exists>N. \<forall>f\<ge>N. interp_term f st'' body = eval_const vals' body"
      by (rule CoreTm_Let.IH(2)[OF c_body fv_body ag'])
    show ?thesis
    proof (rule agree_lift2[OF sub_rhs sub_body])
      fix f assume h1: "interp_term f st rhs = eval_const vals rhs"
               and h2: "interp_term f st'' body = eval_const vals' body"
      have "interp_term (Suc f) st (CoreTm_Let var rhs body) = interp_term f st'' body"
        by (simp add: h1 Inr st''_def Let_def)
      also have "... = eval_const vals' body" by (rule h2)
      finally show "interp_term (Suc f) st (CoreTm_Let var rhs body)
                      = eval_const vals (CoreTm_Let var rhs body)"
        by (simp add: Inr vals'_def)
    qed
  qed
next
  case (CoreTm_Quantifier q var varTy body)
  then show ?case by simp
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  then show ?case by simp
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  have c: "is_constant_term payload" using CoreTm_VariantCtor.prems(1) by simp
  have fv: "core_term_free_vars payload |\<subseteq>| fmdom vals"
    using CoreTm_VariantCtor.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term f st payload = eval_const vals payload"
    by (rule CoreTm_VariantCtor.IH[OF c fv CoreTm_VariantCtor.prems(3)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term f st payload = eval_const vals payload"
    show "interp_term (Suc f) st (CoreTm_VariantCtor ctorName tyArgs payload)
            = eval_const vals (CoreTm_VariantCtor ctorName tyArgs payload)"
      by (simp add: h)
  qed
next
  case (CoreTm_Record flds)
  have members: "\<And>t. t \<in> set (map snd flds) \<Longrightarrow>
                   \<exists>N. \<forall>f\<ge>N. interp_term f st t = eval_const vals t"
  proof -
    fix t assume "t \<in> set (map snd flds)"
    then obtain nm where mem: "(nm, t) \<in> set flds" by auto
    have c: "is_constant_term t"
      using CoreTm_Record.prems(1) mem by (fastforce simp: list_all_iff)
    have fv: "core_term_free_vars t |\<subseteq>| fmdom vals"
      using CoreTm_Record.prems(2) mem
      by (fastforce simp: fsubset_iff fmember_ffUnion_fimage_fset_of_list_iff)
    show "\<exists>N. \<forall>f\<ge>N. interp_term f st t = eval_const vals t"
      using CoreTm_Record.IH mem c fv CoreTm_Record.prems(3) by fastforce
  qed
  show ?case
  proof (rule agree_lift_list[OF agree_list[OF members]])
    fix f assume h: "interp_term_list f st (map snd flds)
                       = eval_const_list vals (map snd flds)"
    show "interp_term (Suc f) st (CoreTm_Record flds)
            = eval_const vals (CoreTm_Record flds)"
      by (simp add: h)
  qed
next
  case (CoreTm_RecordProj tm fldName)
  have c: "is_constant_term tm" using CoreTm_RecordProj.prems(1) by simp
  have fv: "core_term_free_vars tm |\<subseteq>| fmdom vals"
    using CoreTm_RecordProj.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term f st tm = eval_const vals tm"
    by (rule CoreTm_RecordProj.IH[OF c fv CoreTm_RecordProj.prems(3)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term f st tm = eval_const vals tm"
    show "interp_term (Suc f) st (CoreTm_RecordProj tm fldName)
            = eval_const vals (CoreTm_RecordProj tm fldName)"
      by (simp add: h)
  qed
next
  case (CoreTm_VariantProj tm expectedCtor)
  have c: "is_constant_term tm" using CoreTm_VariantProj.prems(1) by simp
  have fv: "core_term_free_vars tm |\<subseteq>| fmdom vals"
    using CoreTm_VariantProj.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term f st tm = eval_const vals tm"
    by (rule CoreTm_VariantProj.IH[OF c fv CoreTm_VariantProj.prems(3)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term f st tm = eval_const vals tm"
    show "interp_term (Suc f) st (CoreTm_VariantProj tm expectedCtor)
            = eval_const vals (CoreTm_VariantProj tm expectedCtor)"
      by (simp add: h)
  qed
next
  case (CoreTm_ArrayProj arr idxTms)
  have c_arr: "is_constant_term arr"
    using CoreTm_ArrayProj.prems(1) by simp
  have fv_arr: "core_term_free_vars arr |\<subseteq>| fmdom vals"
    using CoreTm_ArrayProj.prems(2) by (auto simp: fsubset_iff)
  have sub_arr: "\<exists>N. \<forall>f\<ge>N. interp_term f st arr = eval_const vals arr"
    by (rule CoreTm_ArrayProj.IH(1)[OF c_arr fv_arr CoreTm_ArrayProj.prems(3)])
  have members: "\<And>t. t \<in> set idxTms \<Longrightarrow>
                   \<exists>N. \<forall>f\<ge>N. interp_term f st t = eval_const vals t"
  proof -
    fix t assume mem: "t \<in> set idxTms"
    have c: "is_constant_term t"
      using CoreTm_ArrayProj.prems(1) mem by (auto simp: list_all_iff)
    have fv: "core_term_free_vars t |\<subseteq>| fmdom vals"
      using CoreTm_ArrayProj.prems(2) mem
      by (fastforce simp: fsubset_iff fmember_ffUnion_fimage_fset_of_list_iff)
    show "\<exists>N. \<forall>f\<ge>N. interp_term f st t = eval_const vals t"
      using CoreTm_ArrayProj.IH(2) mem c fv CoreTm_ArrayProj.prems(3) by blast
  qed
  show ?case
  proof (rule agree_lift_tm_list[OF sub_arr agree_list[OF members]])
    fix f assume h1: "interp_term f st arr = eval_const vals arr"
             and h2: "interp_term_list f st idxTms = eval_const_list vals idxTms"
    show "interp_term (Suc f) st (CoreTm_ArrayProj arr idxTms)
            = eval_const vals (CoreTm_ArrayProj arr idxTms)"
      by (simp add: h1 h2 split: sum.split CoreValue.split)
  qed
next
  case (CoreTm_Match scrut arms)
  have c_scrut: "is_constant_term scrut"
    using CoreTm_Match.prems(1) by simp
  have fv_scrut: "core_term_free_vars scrut |\<subseteq>| fmdom vals"
    using CoreTm_Match.prems(2) by (auto simp: fsubset_iff)
  have sub_scrut: "\<exists>N. \<forall>f\<ge>N. interp_term f st scrut = eval_const vals scrut"
    by (rule CoreTm_Match.IH(1)[OF c_scrut fv_scrut CoreTm_Match.prems(3)])
  show ?case
  proof (cases "eval_const vals scrut")
    case (Inl err)
    show ?thesis
    proof (rule agree_lift1[OF sub_scrut])
      fix f assume h: "interp_term f st scrut = eval_const vals scrut"
      show "interp_term (Suc f) st (CoreTm_Match scrut arms)
              = eval_const vals (CoreTm_Match scrut arms)"
        by (simp add: h Inl)
    qed
  next
    case (Inr scrutVal)
    show ?thesis
    proof (cases "find_matching_arm scrutVal arms")
      case (Inl err)
      show ?thesis
      proof (rule agree_lift1[OF sub_scrut])
        fix f assume h: "interp_term f st scrut = eval_const vals scrut"
        show "interp_term (Suc f) st (CoreTm_Match scrut arms)
                = eval_const vals (CoreTm_Match scrut arms)"
          by (simp add: h Inr Inl)
      qed
    next
      case (Inr armTm)
      note fma = Inr
      from find_matching_arm_in_arms[OF fma] obtain pat where
        mem: "(pat, armTm) \<in> set arms" by auto
      have c_arm: "is_constant_term armTm"
        using CoreTm_Match.prems(1) mem by (fastforce simp: list_all_iff)
      have fv_arm: "core_term_free_vars armTm |\<subseteq>| fmdom vals"
        using CoreTm_Match.prems(2) mem
        by (fastforce simp: fsubset_iff fmember_ffUnion_fimage_fset_of_list_iff)
      have sub_arm: "\<exists>N. \<forall>f\<ge>N. interp_term f st armTm = eval_const vals armTm"
        using CoreTm_Match.IH(2) mem c_arm fv_arm CoreTm_Match.prems(3) by fastforce
      show ?thesis
      proof (rule agree_lift2[OF sub_scrut sub_arm])
        fix f assume h1: "interp_term f st scrut = eval_const vals scrut"
                 and h2: "interp_term f st armTm = eval_const vals armTm"
        show "interp_term (Suc f) st (CoreTm_Match scrut arms)
                = eval_const vals (CoreTm_Match scrut arms)"
          by (simp add: h1 h2 \<open>eval_const vals scrut = Inr scrutVal\<close> fma)
      qed
    qed
  qed
next
  case (CoreTm_Sizeof tm)
  have c: "is_constant_term tm" using CoreTm_Sizeof.prems(1) by simp
  have fv: "core_term_free_vars tm |\<subseteq>| fmdom vals"
    using CoreTm_Sizeof.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term f st tm = eval_const vals tm"
    by (rule CoreTm_Sizeof.IH[OF c fv CoreTm_Sizeof.prems(3)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term f st tm = eval_const vals tm"
    show "interp_term (Suc f) st (CoreTm_Sizeof tm)
            = eval_const vals (CoreTm_Sizeof tm)"
      by (simp add: h)
  qed
next
  case (CoreTm_Allocated tm)
  show ?case by (rule agree_leafI) simp
next
  case (CoreTm_Old tm)
  show ?case by (rule agree_leafI) simp
next
  case (CoreTm_Default defTy)
  then show ?case by simp
qed


(* ========================================================================== *)
(* Main results for eval_const/interp_term agreement *)
(* ========================================================================== *)

(* Compile-time evaluation equals runtime interpretation (for SOME fuel)
   at any state that agrees with the constants' value map. *)
theorem eval_const_interp_agree:
  fixes st :: "'w InterpState"
  assumes "is_constant_term tm"
      and "core_term_free_vars tm |\<subseteq>| fmdom globalVals"
      and "vals_agree st globalVals"
  shows "\<exists>fuel. interp_term fuel st tm = eval_const globalVals tm"
proof -
  obtain N where "\<forall>f\<ge>N. interp_term f st tm = eval_const globalVals tm"
    using eval_const_interp_agree_gen[OF assms] by blast
  thus ?thesis by (meson order_refl)
qed

(* Similar result for fold_const (the elaborator's wrapper over eval_const). *)
corollary fold_const_interp_agree:
  fixes st :: "'w InterpState"
  assumes const: "is_constant_term tm"
      and fold_ok: "fold_const globalVals loc tm = Inr v"
      and ag: "vals_agree st globalVals"
  shows "\<exists>fuel. interp_term fuel st tm = Inr v"
proof -
  from fold_ok have
    miss: "core_term_free_vars tm |-| fmdom globalVals = {||}" and
    ev: "eval_const globalVals tm = Inr v"
    unfolding fold_const_def by (auto simp: Let_def split: if_splits sum.splits)
  have fv: "core_term_free_vars tm |\<subseteq>| fmdom globalVals"
    using miss by (metis fempty_iff fminus_iff fsubsetI)
  show ?thesis
    using eval_const_interp_agree[OF const fv ag] ev by simp
qed

(* A canonical witness for vals_agree: globals hold exactly the constants' value map,
   and all other fields are empty. The world type is fixed to `unit`. *)
definition const_eval_state :: "(string, CoreValue) fmap \<Rightarrow> unit InterpState" where
  "const_eval_state vals =
     \<lparr> IS_Globals = vals,
       IS_Locals = fmempty,
       IS_Refs = fmempty,
       IS_Store = [],
       IS_ConstLocals = {||},
       IS_TyArgs = fmempty,
       IS_DefaultCtors = fmempty,
       IS_Functions = fmempty,
       IS_World = () \<rparr>"

lemma const_eval_state_agrees: "vals_agree (const_eval_state vals) vals"
  by (simp add: vals_agree_def const_eval_state_def)

(* A successful fold_const is the same (on compile-time constant terms) as a call to
   the term interpreter, in a specific InterpState.

   This theorem could be used to justify a claim (e.g. in a language specification
   document) that the elaborator evaluates constants at compile time using the ordinary
   dynamic semantics of the Core language (in the particular InterpState given by
   const_eval_state). *)
corollary fold_const_is_core_evaluation:
  assumes const: "is_constant_term tm"
      and fold_ok: "fold_const globalVals loc tm = Inr v"
  shows "\<exists>fuel. interp_term fuel (const_eval_state globalVals) tm = Inr v"
  by (rule fold_const_interp_agree[OF const fold_ok const_eval_state_agrees])

end

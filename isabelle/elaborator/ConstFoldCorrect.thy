theory ConstFoldCorrect
  imports ConstFold "../core/CoreModuleTypecheck" "../interpreter/TypeSoundnessHelpers3"
          "../util/ListExtras"
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
    by (rule eval_binop_sound[OF typing lhs_typing rhs_typing])
       (rule lhs_typed, rule rhs_typed)
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
    using make_1d_array_typed[OF wk elem_ground vs_elem_typed len_ok'] .
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
  from CoreTm_Cast.prems(1) obtain operandTy where
    op_typing: "core_term_type env NotGhost operand = Some operandTy" and
    co: "cast_ok env operandTy targetTy" and
    ty_eq: "ty = targetTy"
    by (auto split: option.splits if_splits)
  from CoreTm_Cast.prems(4) obtain opVal where
    ev_op: "eval_const vals operand = Inr opVal" and
    cast: "cast_value targetTy opVal = Inr v"
    by (auto split: sum.splits)
  have op_ground: "term_types_ground operand"
    using CoreTm_Cast.prems(2) by simp
  have op_typed: "value_has_type env opVal operandTy"
    using CoreTm_Cast.IH[OF op_typing op_ground CoreTm_Cast.prems(3) ev_op] .
  \<comment> \<open>The value-level cast lemma, with the empty substitution.\<close>
  have "value_has_type env v (apply_subst fmempty targetTy)"
    using cast_value_sound[where subst = fmempty, OF cast co] op_typed by simp
  thus ?case using ty_eq by simp
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
  from CoreTm_Binop.prems(4) obtain lhsVal where
    ev_lhs: "eval_const vals lhs = Inr lhsVal"
    by (auto split: sum.splits)
  from CoreTm_Binop.prems(2) have
    g_lhs: "term_types_ground lhs" and g_rhs: "term_types_ground rhs" by simp_all
  have lhs_typed: "value_has_type env lhsVal lhsTy"
    using CoreTm_Binop.IH(1)[OF lhs_typing g_lhs CoreTm_Binop.prems(3) ev_lhs] .
  show ?case
  proof (cases "short_circuit op lhsVal")
    case (Some result)
    (* Short-circuit: the result is a bool, and the binop's type is Bool *)
    have v_eq: "v = result"
      using CoreTm_Binop.prems(4) ev_lhs Some by simp
    obtain b where result_eq: "result = CV_Bool b"
      using short_circuit_bool[OF Some] by blast
    have ty_eq: "ty = CoreTy_Bool"
      using short_circuit_type_bool[OF Some CoreTm_Binop.prems(1)] .
    show ?thesis using v_eq result_eq ty_eq by simp
  next
    case None
    from CoreTm_Binop.prems(4) ev_lhs None obtain rhsVal where
      ev_rhs: "eval_const vals rhs = Inr rhsVal" and
      ev_op: "eval_binop op lhsVal rhsVal = Inr v"
      by (auto split: sum.splits)
    have rhs_typed: "value_has_type env rhsVal rhsTy"
      using CoreTm_Binop.IH(2)[OF rhs_typing g_rhs CoreTm_Binop.prems(3) ev_rhs] .
    show ?thesis
      by (rule eval_binop_sound_values[OF CoreTm_Binop.prems(1) lhs_typing rhs_typing
            lhs_typed rhs_typed ev_op])
  qed
next
  case (CoreTm_Let var rhs body)
  from CoreTm_Let.prems(1) obtain rhsTy where
    rhs_typing: "core_term_type env NotGhost rhs = Some rhsTy" and
    body_typing: "core_term_type
       (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
              TE_GhostLocals := fminus (TE_GhostLocals env) {|var|},
              TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
       NotGhost body = Some ty"
    by (auto simp: Let_def split: option.splits if_splits)
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
    using lookup len_eq args_wk args_ground pv_typed
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
  from CoreTm_ArrayProj.prems(4) obtain al sizes elementMap indexVals indices where
    ev_arr: "eval_const vals arr = Inr (CV_Array al sizes elementMap)" and
    ev_idx: "eval_const_list vals idxTms = Inr indexVals" and
    idx_ok: "interpret_index_vals indexVals = Inr indices" and
    elem_lk: "fmlookup elementMap indices = Some v"
    by (auto split: sum.splits CoreValue.splits option.splits)
  have arr_typed: "value_has_type env (CV_Array al sizes elementMap)
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
  from CoreTm_Sizeof.prems(4) obtain al sizes vm where
    ev_tm: "eval_const vals tm = Inr (CV_Array al sizes vm)" and
    v_eq: "v = array_size_to_value sizes"
    by (auto split: sum.splits CoreValue.splits)
  have arr_typed: "value_has_type env (CV_Array al sizes vm) (CoreTy_Array elemTy dims)"
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
  case (CoreTm_Allocated ty tm)
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
(* Values with no allocated part                                              *)
(* ========================================================================== *)

(* The interpreter gives RuntimeError when a value in a value position is
   allocated (value_position in CoreInterp.thy); eval_const makes no such check.
   So the two can agree only where no checked value is allocated. This section
   shows that a constant term yields no allocated value if the values of the
   constants it reads are not allocated.

   "Not allocated" (is_allocated) is not itself preserved by eval_const. An array
   that is not allocated may hold an allocated element at an index outside its
   sizes (is_allocated looks only at the indices within the sizes), and an array
   projection would return that element. A well-typed array has no such element
   (fmap_matches_sizes). Rather than carry the types of all intermediate values
   through the inductions, we use a stronger property that is preserved with no
   typing assumption at all: deep_unallocated says that no part of the value is
   allocated, looking at every entry of every element map. On a well-typed value
   the two properties are the same (deep_unallocated_not_allocated and
   value_has_type_deep_unallocated). *)

function deep_unallocated :: "(string \<Rightarrow> CoreAllocLevel \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> CoreValue \<Rightarrow> bool" where
  "deep_unallocated extAlloc (CV_Bool _) = True"
| "deep_unallocated extAlloc (CV_FiniteInt _ _ _) = True"
| "deep_unallocated extAlloc (CV_Int _) = True"
| "deep_unallocated extAlloc (CV_Real _) = True"
| "deep_unallocated extAlloc (CV_Record fieldValues) =
    list_all (\<lambda>fld. deep_unallocated extAlloc (snd fld)) fieldValues"
| "deep_unallocated extAlloc (CV_Variant ctor payload) = deep_unallocated extAlloc payload"
| "deep_unallocated extAlloc (CV_Array allocatable sizes valuesMap) =
    (\<not> (allocatable \<and> list_all (\<lambda>s. s \<noteq> 0) sizes) \<and>
     (\<forall>idx v. fmlookup valuesMap idx = Some v \<longrightarrow> deep_unallocated extAlloc v))"
| "deep_unallocated extAlloc (CV_Extern n l k) = (\<not> is_allocated extAlloc (CV_Extern n l k))"
  by pat_completeness auto

termination deep_unallocated
proof (relation "measure (\<lambda>(extAlloc, val). size val)", goal_cases)
  case 1
  show ?case by simp
next
  case (2 extAlloc fieldValues fld)
  hence "(fst fld, snd fld) \<in> set fieldValues" by simp
  hence "size (snd fld) < size (CV_Record fieldValues)" by (rule size_record_field)
  thus ?case by simp
next
  case (3 extAlloc ctor payload)
  show ?case by simp
next
  case (4 extAlloc allocatable sizes valuesMap idx v)
  hence "size v < size (CV_Array allocatable sizes valuesMap)" by (rule size_array_lookup)
  thus ?case by simp
qed

lemma deep_unallocated_not_allocated:
  "deep_unallocated extAlloc v \<Longrightarrow> \<not> is_allocated extAlloc v"
proof (induction extAlloc v rule: deep_unallocated.induct)
  case (5 extAlloc fieldValues)
  then show ?case by (auto simp: list_all_iff list_ex_iff)
next
  case (7 extAlloc allocatable sizes valuesMap)
  then show ?case by (auto simp: list_ex_iff split: option.splits)
qed simp_all

lemma all_indices_zero_size:
  "0 \<in> set sizes \<Longrightarrow> all_indices sizes = []"
  by (induction sizes) (auto simp: Let_def)

lemma value_has_type_deep_unallocated:
  assumes "value_has_type env v ty" and "\<not> is_allocated extAlloc v"
  shows "deep_unallocated extAlloc v"
  using assms
proof (induction extAlloc v arbitrary: ty rule: deep_unallocated.induct)
  case (5 extAlloc fieldValues)
  from "5.prems"(1) obtain fieldTypes where
    all2: "list_all2 (\<lambda>(name1, fldVal) (name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
             fieldValues fieldTypes"
    by (auto split: CoreType.splits)
  have "\<And>fld. fld \<in> set fieldValues \<Longrightarrow> deep_unallocated extAlloc (snd fld)"
  proof -
    fix fld assume mem: "fld \<in> set fieldValues"
    then obtain i where i: "i < length fieldValues" "fieldValues ! i = fld"
      by (auto simp: in_set_conv_nth)
    from list_all2_nthD[OF all2 i(1)] i(2)
    have "value_has_type env (snd fld) (snd (fieldTypes ! i))"
      by (cases fld; cases "fieldTypes ! i") auto
    moreover from "5.prems"(2) mem have "\<not> is_allocated extAlloc (snd fld)"
      by (auto simp: list_ex_iff)
    ultimately show "deep_unallocated extAlloc (snd fld)"
      using "5.IH"[OF mem] by blast
  qed
  then show ?case by (simp add: list_all_iff)
next
  case (6 extAlloc ctor payload)
  from "6.prems"(1) obtain pty where "value_has_type env payload pty"
    by (auto split: CoreType.splits option.splits)
  with "6.IH" "6.prems"(2) show ?case by simp
next
  case (7 extAlloc allocatable sizes valuesMap)
  from "7.prems"(1) obtain elemTy dims where
    elems: "\<forall>idx val. fmlookup valuesMap idx = Some val \<longrightarrow> value_has_type env val elemTy" and
    fms: "fmap_matches_sizes sizes valuesMap"
    by (auto split: CoreType.splits)
  from fms have dom: "fmdom valuesMap = fset_of_list (all_indices sizes)"
    by (simp add: fmap_matches_sizes_def)
  have in_sizes: "\<And>idx val. fmlookup valuesMap idx = Some val \<Longrightarrow> idx \<in> set (all_indices sizes)"
  proof -
    fix idx val assume "fmlookup valuesMap idx = Some val"
    hence "idx |\<in>| fmdom valuesMap" by (rule fmdomI)
    with dom show "idx \<in> set (all_indices sizes)" by (simp add: fset_of_list_elem)
  qed
  show ?case
  proof (cases allocatable)
    case True
    with "7.prems"(2) have "\<not> list_all (\<lambda>s. s \<noteq> 0) sizes" by simp
    hence "0 \<in> set sizes" by (auto simp: list_all_iff)
    hence "all_indices sizes = []" by (rule all_indices_zero_size)
    with in_sizes have "\<And>idx val. fmlookup valuesMap idx = Some val \<Longrightarrow> False" by fastforce
    with True \<open>\<not> list_all (\<lambda>s. s \<noteq> 0) sizes\<close> show ?thesis by auto
  next
    case False
    have "\<And>idx val. fmlookup valuesMap idx = Some val \<Longrightarrow> deep_unallocated extAlloc val"
    proof -
      fix idx val assume lk: "fmlookup valuesMap idx = Some val"
      from "7.prems"(2) False in_sizes[OF lk] lk have "\<not> is_allocated extAlloc val"
        by (auto simp: list_ex_iff)
      with "7.IH"[OF lk] elems lk show "deep_unallocated extAlloc val" by blast
    qed
    with False show ?thesis by auto
  qed
qed simp_all

(* Preservation by the helpers that eval_const shares with the interpreter. *)

lemma make_1d_array_deep_unallocated:
  assumes "\<And>v. v \<in> set vs \<Longrightarrow> deep_unallocated extAlloc v"
  shows "deep_unallocated extAlloc (make_1d_array vs)"
proof -
  have "\<And>idx v. fmlookup (fmap_of_list (zip (map (\<lambda>i. [int i]) [0..<length vs]) vs)) idx = Some v
          \<Longrightarrow> v \<in> set vs"
    by (auto simp: fmlookup_of_list dest!: map_of_SomeD set_zip_rightD)
  with assms show ?thesis by auto
qed

lemma cast_value_deep_unallocated:
  assumes "cast_value ty v = Inr v'" and "deep_unallocated extAlloc v"
  shows "deep_unallocated extAlloc v'"
  using assms
  by (cases "(ty, v)" rule: cast_value.cases) (auto split: if_splits)

lemma generic_finite_int_binop_deep_unallocated:
  "generic_finite_int_binop f a b = Inr r \<Longrightarrow> deep_unallocated extAlloc r"
  by (cases "(f, a, b)" rule: generic_finite_int_binop.cases) (auto simp: Let_def split: if_splits)

lemma generic_finite_int_cmp_binop_deep_unallocated:
  "generic_finite_int_cmp_binop f a b = Inr r \<Longrightarrow> deep_unallocated extAlloc r"
  by (cases "(f, a, b)" rule: generic_finite_int_cmp_binop.cases) (auto split: if_splits)

lemma generic_integer_binop_deep_unallocated:
  "generic_integer_binop f a b = Inr r \<Longrightarrow> deep_unallocated extAlloc r"
  by (cases a; cases b)
     (auto simp: Let_def split: if_splits
           dest: generic_finite_int_binop_deep_unallocated[where extAlloc = extAlloc])

lemma generic_numeric_binop_deep_unallocated:
  "generic_numeric_binop fi fr a b = Inr r \<Longrightarrow> deep_unallocated extAlloc r"
  by (cases a; cases b)
     (auto simp: Let_def split: if_splits
           dest: generic_integer_binop_deep_unallocated[where extAlloc = extAlloc])

lemma generic_numeric_cmp_binop_deep_unallocated:
  "generic_numeric_cmp_binop fi fr a b = Inr r \<Longrightarrow> deep_unallocated extAlloc r"
  by (cases a; cases b)
     (auto simp: Let_def split: if_splits
           dest: generic_finite_int_cmp_binop_deep_unallocated[where extAlloc = extAlloc])

lemma generic_bool_binop_deep_unallocated:
  "generic_bool_binop f a b = Inr r \<Longrightarrow> deep_unallocated extAlloc r"
  by (cases "(f, a, b)" rule: generic_bool_binop.cases) auto

lemma eval_binop_deep_unallocated:
  "eval_binop op a b = Inr r \<Longrightarrow> deep_unallocated extAlloc r"
  by (cases op)
     (auto split: if_splits sum.splits
           dest: generic_finite_int_binop_deep_unallocated[where extAlloc = extAlloc]
                 generic_integer_binop_deep_unallocated[where extAlloc = extAlloc]
                 generic_numeric_binop_deep_unallocated[where extAlloc = extAlloc]
                 generic_numeric_cmp_binop_deep_unallocated[where extAlloc = extAlloc]
                 generic_bool_binop_deep_unallocated[where extAlloc = extAlloc])

lemma eval_unop_deep_unallocated:
  "eval_unop op a = Inr r \<Longrightarrow> deep_unallocated extAlloc r"
  by (cases op) (auto split: CoreValue.splits if_splits)

lemma short_circuit_deep_unallocated:
  "short_circuit op a = Some r \<Longrightarrow> deep_unallocated extAlloc r"
  by (auto elim!: short_circuit.elims split: if_splits)

lemma array_size_to_value_deep_unallocated:
  "deep_unallocated extAlloc (array_size_to_value sizes)"
  by (cases sizes rule: array_size_to_value.cases)
     (auto simp: list_all_iff dest!: set_zip_rightD)

(* eval_const preserves it, whatever the term. *)
lemma eval_const_deep_unallocated_aux:
  shows "(\<forall>name v'. fmlookup vals name = Some v' \<longrightarrow> deep_unallocated extAlloc v')
           \<longrightarrow> (\<forall>v. eval_const vals tm = Inr v \<longrightarrow> deep_unallocated extAlloc v)"
    and "(\<forall>name v'. fmlookup vals name = Some v' \<longrightarrow> deep_unallocated extAlloc v')
           \<longrightarrow> (\<forall>vs. eval_const_list vals tms = Inr vs
                  \<longrightarrow> (\<forall>v \<in> set vs. deep_unallocated extAlloc v))"
proof (induction vals tm and vals tms rule: eval_const_eval_const_list.induct)
  case (3 vals uu tms)
  then show ?case
    by (auto split: sum.splits simp del: make_1d_array.simps
             intro!: make_1d_array_deep_unallocated)
next
  case (4 vals varName)
  then show ?case by (auto split: option.splits)
next
  case (5 vals targetTy tm)
  then show ?case
    by (auto split: sum.splits dest: cast_value_deep_unallocated[where extAlloc = extAlloc])
next
  case (6 vals op tm)
  then show ?case
    by (auto split: sum.splits dest: eval_unop_deep_unallocated[where extAlloc = extAlloc])
next
  case (7 vals op lhsTm rhsTm)
  \<comment> \<open>The result of an operator is a scalar, whatever the operands are.\<close>
  show ?case
  proof (intro impI allI)
    fix v
    assume ev: "eval_const vals (CoreTm_Binop op lhsTm rhsTm) = Inr v"
    from ev obtain lhsVal where lhs: "eval_const vals lhsTm = Inr lhsVal"
      by (auto split: sum.splits)
    show "deep_unallocated extAlloc v"
    proof (cases "short_circuit op lhsVal")
      case (Some result)
      with ev lhs have "v = result" by simp
      with Some show ?thesis by (simp add: short_circuit_deep_unallocated)
    next
      case None
      with ev lhs obtain rhsVal where "eval_binop op lhsVal rhsVal = Inr v"
        by (auto split: sum.splits)
      thus ?thesis by (rule eval_binop_deep_unallocated)
    qed
  qed
next
  case (8 vals varName rhsTm bodyTm)
  show ?case
  proof (intro impI allI)
    fix v
    assume ua: "\<forall>name v'. fmlookup vals name = Some v' \<longrightarrow> deep_unallocated extAlloc v'"
       and ev: "eval_const vals (CoreTm_Let varName rhsTm bodyTm) = Inr v"
    from ev obtain rhsVal where
      rhs: "eval_const vals rhsTm = Inr rhsVal" and
      body: "eval_const (fmupd varName rhsVal vals) bodyTm = Inr v"
      by (auto split: sum.splits)
    from "8.IH"(1) ua rhs have "deep_unallocated extAlloc rhsVal" by blast
    with ua have "\<forall>name v'. fmlookup (fmupd varName rhsVal vals) name = Some v'
                    \<longrightarrow> deep_unallocated extAlloc v'" by auto
    with "8.IH"(2)[OF rhs] body show "deep_unallocated extAlloc v" by blast
  qed
next
  case (10 vals ctorName uw payloadTm)
  then show ?case by (auto split: sum.splits)
next
  case (11 vals nameTermPairs)
  then show ?case
    by (auto split: sum.splits simp: list_all_iff dest!: set_zip_rightD)
next
  case (12 vals tm fldName)
  then show ?case
    by (auto split: sum.splits CoreValue.splits option.splits simp: list_all_iff
             dest!: map_of_SomeD)
       (metis snd_conv)
next
  case (13 vals tm expectedCtorName)
  then show ?case by (auto split: sum.splits CoreValue.splits if_splits)
next
  case (14 vals arrayTm idxTms)
  \<comment> \<open>Every entry of the element map has no allocated part, whether or not its
      index is within the sizes of the array.\<close>
  show ?case
  proof (intro impI allI)
    fix v
    assume ua: "\<forall>name v'. fmlookup vals name = Some v' \<longrightarrow> deep_unallocated extAlloc v'"
       and ev: "eval_const vals (CoreTm_ArrayProj arrayTm idxTms) = Inr v"
    from ev obtain al sizes elementMap indices where
      arr: "eval_const vals arrayTm = Inr (CV_Array al sizes elementMap)" and
      lk: "fmlookup elementMap indices = Some v"
      by (auto split: sum.splits CoreValue.splits option.splits)
    from "14.IH"(1) ua arr
    have "deep_unallocated extAlloc (CV_Array al sizes elementMap)" by blast
    with lk show "deep_unallocated extAlloc v" by simp
  qed
next
  case (15 vals scrutTm arms)
  show ?case
  proof (intro impI allI)
    fix v
    assume ua: "\<forall>name v'. fmlookup vals name = Some v' \<longrightarrow> deep_unallocated extAlloc v'"
       and ev: "eval_const vals (CoreTm_Match scrutTm arms) = Inr v"
    from ev obtain scrutVal armTm where
      scrut: "eval_const vals scrutTm = Inr scrutVal" and
      fma: "find_matching_arm scrutVal arms = Inr armTm" and
      arm: "eval_const vals armTm = Inr v"
      by (auto split: sum.splits)
    from "15.IH"(2) scrut fma ua arm show "deep_unallocated extAlloc v" by blast
  qed
next
  case (16 vals tm)
  then show ?case
    by (auto split: sum.splits CoreValue.splits intro: array_size_to_value_deep_unallocated)
next
  case (21 vals tm tms)
  show ?case
  proof (intro impI allI ballI)
    fix vs v
    assume ua: "\<forall>name v'. fmlookup vals name = Some v' \<longrightarrow> deep_unallocated extAlloc v'"
       and ev: "eval_const_list vals (tm # tms) = Inr vs"
       and mem: "v \<in> set vs"
    from ev obtain v1 vs' where
      hd: "eval_const vals tm = Inr v1" and
      tl: "eval_const_list vals tms = Inr vs'" and
      vs: "vs = v1 # vs'"
      by (auto split: sum.splits)
    from "21.IH"(1) ua hd have d1: "deep_unallocated extAlloc v1" by blast
    from "21.IH"(2) hd ua tl have d2: "\<forall>v\<in>set vs'. deep_unallocated extAlloc v" by blast
    from mem vs d1 d2 show "deep_unallocated extAlloc v" by auto
  qed
qed (auto split: option.splits)

lemma eval_const_deep_unallocated:
  assumes "\<forall>name c. fmlookup vals name = Some c \<longrightarrow> deep_unallocated extAlloc c"
      and "eval_const vals tm = Inr v"
  shows "deep_unallocated extAlloc v"
  using eval_const_deep_unallocated_aux(1) assms by blast

lemma eval_const_list_deep_unallocated:
  assumes "\<forall>name c. fmlookup vals name = Some c \<longrightarrow> deep_unallocated extAlloc c"
      and "eval_const_list vals tms = Inr vs"
      and "v \<in> set vs"
  shows "deep_unallocated extAlloc v"
  using eval_const_deep_unallocated_aux(2) assms by blast

(* The same in terms of is_allocated: if every value of the map is well typed
   and not allocated, then the result of eval_const is not allocated. The oracle
   is arbitrary, and the term need not be typed. (There is no is_constant_term
   premise either: on any other term eval_const gives no value.) *)
theorem eval_const_not_allocated:
  assumes typed: "\<And>name c. fmlookup vals name = Some c \<Longrightarrow> \<exists>cty. value_has_type env c cty"
      and unalloc: "\<And>name c. fmlookup vals name = Some c \<Longrightarrow> \<not> is_allocated extAlloc c"
      and ev: "eval_const vals tm = Inr v"
  shows "\<not> is_allocated extAlloc v"
proof -
  have "\<forall>name c. fmlookup vals name = Some c \<longrightarrow> deep_unallocated extAlloc c"
  proof (intro allI impI)
    fix name c assume lk: "fmlookup vals name = Some c"
    from typed[OF lk] obtain cty where "value_has_type env c cty" ..
    thus "deep_unallocated extAlloc c"
      using unalloc[OF lk] by (rule value_has_type_deep_unallocated)
  qed
  from eval_const_deep_unallocated[OF this ev] show ?thesis
    by (rule deep_unallocated_not_allocated)
qed

(* Consequently the value_position check (R1) of the interpreter does nothing to
   a result of eval_const. *)
lemma value_position_eval_const:
  fixes st :: "'w InterpState"
  assumes "\<forall>name c. fmlookup vals name = Some c
             \<longrightarrow> deep_unallocated (IS_ExternAlloc st) c"
  shows "value_position st (eval_const vals tm) = eval_const vals tm"
proof (cases "eval_const vals tm")
  case (Inl err)
  then show ?thesis by simp
next
  case (Inr v)
  have "\<not> is_allocated (IS_ExternAlloc st) v"
    by (rule deep_unallocated_not_allocated[OF eval_const_deep_unallocated[OF assms Inr]])
  with Inr show ?thesis by (simp add: value_position_def)
qed

lemma value_position_list_eval_const_list:
  fixes st :: "'w InterpState"
  assumes "\<forall>name c. fmlookup vals name = Some c
             \<longrightarrow> deep_unallocated (IS_ExternAlloc st) c"
  shows "value_position_list st (eval_const_list vals tms) = eval_const_list vals tms"
proof (cases "eval_const_list vals tms")
  case (Inl err)
  then show ?thesis by simp
next
  case (Inr vs)
  have "\<And>v. v \<in> set vs \<Longrightarrow> \<not> is_allocated (IS_ExternAlloc st) v"
    by (rule deep_unallocated_not_allocated[OF eval_const_list_deep_unallocated[OF assms Inr]])
  with Inr show ?thesis by (simp add: value_position_list_def list_ex_iff)
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
  shows "interp_term d (Suc f) (st :: 'w InterpState) (CoreTm_Var name) = Inr v"
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

(* Every value in the map is well-typed (assuming the state itself is well-typed, i.e.
   satisfies state_matches_env). *)
lemma vals_agree_value_typed:
  fixes st :: "'w InterpState"
  assumes sme: "state_matches_env st env storeTyping"
      and ag: "vals_agree st vals"
      and lk: "fmlookup vals name = Some v"
  shows "\<exists>ty. value_has_type env v ty"
proof -
  from ag lk have base: "(case fmlookup (IS_Locals st) name of
      Some addr \<Rightarrow> addr < length (IS_Store st) \<and> IS_Store st ! addr = v
    | None \<Rightarrow>
      (case fmlookup (IS_Refs st) name of
         Some (addr, path) \<Rightarrow> addr < length (IS_Store st)
                              \<and> get_value_at_path (IS_Store st ! addr) path = Inr v
       | None \<Rightarrow> fmlookup (IS_Globals st) name = Some v))"
    unfolding vals_agree_def by blast
  from sme have swt: "store_well_typed st env storeTyping"
    and lve: "local_vars_exist_in_state st env storeTyping"
    and gve: "global_vars_exist_in_state st env"
    and nel: "no_extra_local_vars st env"
    and neg: "no_extra_global_vars st env"
    unfolding state_matches_env_def by simp_all
  have slot: "\<And>addr. addr < length (IS_Store st)
                \<Longrightarrow> value_has_type env (IS_Store st ! addr) (storeTyping ! addr)"
    using swt unfolding store_well_typed_def by blast
  show ?thesis
  proof (cases "fmlookup (IS_Locals st) name")
    case (Some addr)
    with base have "addr < length (IS_Store st)" and "IS_Store st ! addr = v" by simp_all
    with slot[of addr] show ?thesis by blast
  next
    case None
    show ?thesis
    proof (cases "fmlookup (IS_Refs st) name")
      case (Some ap)
      obtain addr path where ap: "ap = (addr, path)" by (cases ap)
      from base None Some ap have valid: "addr < length (IS_Store st)"
        and gv: "get_value_at_path (IS_Store st ! addr) path = Inr v" by simp_all
      from nel Some obtain lty where lty: "fmlookup (TE_LocalVars env) name = Some lty"
        unfolding no_extra_local_vars_def
        by (cases "fmlookup (TE_LocalVars env) name") auto
      from lve lty have "local_var_in_state_with_type st env storeTyping name lty"
        unfolding local_vars_exist_in_state_def by blast
      with None Some ap
      have pt: "type_at_path env (storeTyping ! addr) path
                  = Some (apply_subst (IS_TyArgs st) lty)"
        unfolding local_var_in_state_with_type_def by (simp add: Let_def)
      from get_value_at_path_type[OF slot[OF valid] pt gv] show ?thesis by blast
    next
      case None2: None
      from base None None2 have g: "fmlookup (IS_Globals st) name = Some v" by simp
      from neg g obtain gty where gty: "fmlookup (TE_GlobalVars env) name = Some gty"
        unfolding no_extra_global_vars_def
        by (cases "fmlookup (TE_GlobalVars env) name") auto
      from gve gty have "global_var_in_state_with_type st env name gty"
        unfolding global_vars_exist_in_state_def by blast
      with g show ?thesis unfolding global_var_in_state_with_type_def by auto
    qed
  qed
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
   the per-clause computation, discharged by simp at each use site.
   The depth `d` is the same throughout: none of these clauses spends depth. *)

lemma agree_leafI:
  fixes st :: "'w InterpState"
  assumes "\<And>f. interp_term d (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term d f st tm = eval_const vals tm"
proof -
  have "\<forall>f\<ge>Suc 0. interp_term d f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc 0 \<le> f"
    then obtain f' where "f = Suc f'" using Suc_le_D by auto
    thus "interp_term d f st tm = eval_const vals tm" using assms by blast
  qed
  thus ?thesis by blast
qed

lemma agree_lift1:
  fixes st :: "'w InterpState" and st1 :: "'w InterpState"
  assumes sub: "\<exists>N. \<forall>f\<ge>N. interp_term d f st1 t1 = eval_const vals1 t1"
      and step: "\<And>f. interp_term d f st1 t1 = eval_const vals1 t1 \<Longrightarrow>
                   interp_term d (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term d f st tm = eval_const vals tm"
proof -
  obtain N where N: "\<forall>f\<ge>N. interp_term d f st1 t1 = eval_const vals1 t1"
    using sub by blast
  have "\<forall>f\<ge>Suc N. interp_term d f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc N \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge: "N \<le> f'"
      using Suc_le_D by auto
    have "interp_term d (Suc f') st tm = eval_const vals tm"
      by (rule step) (use N ge in blast)
    thus "interp_term d f st tm = eval_const vals tm" by (simp add: f_eq)
  qed
  thus ?thesis by blast
qed

lemma agree_lift2:
  fixes st :: "'w InterpState" and st1 :: "'w InterpState" and st2 :: "'w InterpState"
  assumes sub1: "\<exists>N. \<forall>f\<ge>N. interp_term d f st1 t1 = eval_const vals1 t1"
      and sub2: "\<exists>N. \<forall>f\<ge>N. interp_term d f st2 t2 = eval_const vals2 t2"
      and step: "\<And>f. interp_term d f st1 t1 = eval_const vals1 t1 \<Longrightarrow>
                   interp_term d f st2 t2 = eval_const vals2 t2 \<Longrightarrow>
                   interp_term d (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term d f st tm = eval_const vals tm"
proof -
  obtain N1 where N1: "\<forall>f\<ge>N1. interp_term d f st1 t1 = eval_const vals1 t1"
    using sub1 by blast
  obtain N2 where N2: "\<forall>f\<ge>N2. interp_term d f st2 t2 = eval_const vals2 t2"
    using sub2 by blast
  have "\<forall>f\<ge>Suc (max N1 N2). interp_term d f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc (max N1 N2) \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge1: "N1 \<le> f'" and ge2: "N2 \<le> f'"
      using Suc_le_D by force
    have "interp_term d (Suc f') st tm = eval_const vals tm"
      by (rule step) (use N1 ge1 N2 ge2 in blast)+
    thus "interp_term d f st tm = eval_const vals tm" by (simp add: f_eq)
  qed
  thus ?thesis by blast
qed

lemma agree_lift_list:
  fixes st :: "'w InterpState" and st1 :: "'w InterpState"
  assumes sub: "\<exists>N. \<forall>f\<ge>N. interp_term_list d f st1 tms = eval_const_list vals1 tms"
      and step: "\<And>f. interp_term_list d f st1 tms = eval_const_list vals1 tms \<Longrightarrow>
                   interp_term d (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term d f st tm = eval_const vals tm"
proof -
  obtain N where N: "\<forall>f\<ge>N. interp_term_list d f st1 tms = eval_const_list vals1 tms"
    using sub by blast
  have "\<forall>f\<ge>Suc N. interp_term d f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc N \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge: "N \<le> f'"
      using Suc_le_D by auto
    have "interp_term d (Suc f') st tm = eval_const vals tm"
      by (rule step) (use N ge in blast)
    thus "interp_term d f st tm = eval_const vals tm" by (simp add: f_eq)
  qed
  thus ?thesis by blast
qed

lemma agree_lift_tm_list:
  fixes st :: "'w InterpState" and st1 :: "'w InterpState" and st2 :: "'w InterpState"
  assumes sub1: "\<exists>N. \<forall>f\<ge>N. interp_term d f st1 t1 = eval_const vals1 t1"
      and sub2: "\<exists>N. \<forall>f\<ge>N. interp_term_list d f st2 tms = eval_const_list vals2 tms"
      and step: "\<And>f. interp_term d f st1 t1 = eval_const vals1 t1 \<Longrightarrow>
                   interp_term_list d f st2 tms = eval_const_list vals2 tms \<Longrightarrow>
                   interp_term d (Suc f) st tm = eval_const vals tm"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term d f st tm = eval_const vals tm"
proof -
  obtain N1 where N1: "\<forall>f\<ge>N1. interp_term d f st1 t1 = eval_const vals1 t1"
    using sub1 by blast
  obtain N2 where N2: "\<forall>f\<ge>N2. interp_term_list d f st2 tms = eval_const_list vals2 tms"
    using sub2 by blast
  have "\<forall>f\<ge>Suc (max N1 N2). interp_term d f st tm = eval_const vals tm"
  proof (intro allI impI)
    fix f assume "Suc (max N1 N2) \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge1: "N1 \<le> f'" and ge2: "N2 \<le> f'"
      using Suc_le_D by force
    have "interp_term d (Suc f') st tm = eval_const vals tm"
      by (rule step) (use N1 ge1 N2 ge2 in blast)+
    thus "interp_term d f st tm = eval_const vals tm" by (simp add: f_eq)
  qed
  thus ?thesis by blast
qed

(* List-level agreement from member-level agreement (same state and map
   throughout: interp_term_list does not thread state changes). *)
lemma agree_list:
  fixes st :: "'w InterpState"
  assumes "\<And>t. t \<in> set tms \<Longrightarrow> \<exists>N. \<forall>f\<ge>N. interp_term d f st t = eval_const vals t"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term_list d f st tms = eval_const_list vals tms"
  using assms
proof (induction tms)
  case Nil
  have "\<forall>f\<ge>Suc 0. interp_term_list d f st [] = eval_const_list vals ([] :: CoreTerm list)"
  proof (intro allI impI)
    fix f assume "Suc 0 \<le> f"
    then obtain f' where "f = Suc f'" using Suc_le_D by auto
    thus "interp_term_list d f st [] = eval_const_list vals ([] :: CoreTerm list)"
      by simp
  qed
  thus ?case by blast
next
  case (Cons t ts)
  obtain N1 where N1: "\<forall>f\<ge>N1. interp_term d f st t = eval_const vals t"
    using Cons.prems[of t] by auto
  have tl_agree: "\<exists>N. \<forall>f\<ge>N. interp_term_list d f st ts = eval_const_list vals ts"
  proof (rule Cons.IH)
    fix ta assume "ta \<in> set ts"
    thus "\<exists>N. \<forall>f\<ge>N. interp_term d f st ta = eval_const vals ta"
      using Cons.prems[of ta] by simp
  qed
  then obtain N2 where N2: "\<forall>f\<ge>N2. interp_term_list d f st ts = eval_const_list vals ts"
    by blast
  have "\<forall>f\<ge>Suc (max N1 N2). interp_term_list d f st (t # ts) = eval_const_list vals (t # ts)"
  proof (intro allI impI)
    fix f assume "Suc (max N1 N2) \<le> f"
    then obtain f' where f_eq: "f = Suc f'" and ge1: "N1 \<le> f'" and ge2: "N2 \<le> f'"
      using Suc_le_D by force
    have h: "interp_term d f' st t = eval_const vals t" using N1 ge1 by blast
    have tl: "interp_term_list d f' st ts = eval_const_list vals ts" using N2 ge2 by blast
    show "interp_term_list d f st (t # ts) = eval_const_list vals (t # ts)"
      by (simp add: f_eq h tl split: sum.split)
  qed
  thus ?case by blast
qed


(* ========================================================================== *)
(* The main agreement induction                                               *)
(* ========================================================================== *)

(* Generalized over the Let-extended value map and state. Structural
   induction; every case is: obtain agreement for the subterms (IH), then
   the clause-level computation is the same case expression on both sides
   (shared helpers), discharged by simp. The interpreter's value_position
   checks disappear by value_position_eval_const: no value of the map has an
   allocated part (the fourth premise), so no subterm yields an allocated value.
   That premise is kept through CoreTm_Let by eval_const_deep_unallocated,
   because nothing checks the right-hand side of a let.

   The premise makes the check vacuous whatever the mode of the state, so
   IS_Ghost is not mentioned. (In ghost mode there is no check at all.)

   The depth `d` is arbitrary, because a constant term has no quantifier. *)
theorem eval_const_interp_agree_gen:
  fixes st :: "'w InterpState"
  assumes "is_constant_term tm"
      and "core_term_free_vars tm |\<subseteq>| fmdom vals"
      and "vals_agree st vals"
      and "\<forall>name c. fmlookup vals name = Some c
             \<longrightarrow> deep_unallocated (IS_ExternAlloc st) c"
  shows "\<exists>N. \<forall>f\<ge>N. interp_term d f st tm = eval_const vals tm"
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
                   \<exists>N. \<forall>f\<ge>N. interp_term d f st t = eval_const vals t"
  proof -
    fix t assume mem: "t \<in> set tms"
    have c: "is_constant_term t"
      using CoreTm_LitArray.prems(1) mem by (auto simp: list_all_iff)
    have fv: "core_term_free_vars t |\<subseteq>| fmdom vals"
      using CoreTm_LitArray.prems(2) mem
      by (fastforce simp: fsubset_iff fmember_ffUnion_fimage_fset_of_list_iff)
    show "\<exists>N. \<forall>f\<ge>N. interp_term d f st t = eval_const vals t"
      using CoreTm_LitArray.IH mem c fv CoreTm_LitArray.prems(3,4) by blast
  qed
  show ?case
  proof (rule agree_lift_list[OF agree_list[OF members]])
    fix f assume h: "interp_term_list d f st tms = eval_const_list vals tms"
    show "interp_term d (Suc f) st (CoreTm_LitArray elemTy tms)
            = eval_const vals (CoreTm_LitArray elemTy tms)"
      by (simp add: h value_position_list_eval_const_list[OF CoreTm_LitArray.prems(4)])
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
    have "interp_term d (Suc f) st (CoreTm_Var name) = Inr v"
      by (rule vals_agree_lookup[OF CoreTm_Var.prems(3) lk])
    thus "interp_term d (Suc f) st (CoreTm_Var name) = eval_const vals (CoreTm_Var name)"
      by (simp add: lk)
  qed
next
  case (CoreTm_Cast targetTy operand)
  have c: "is_constant_term operand" using CoreTm_Cast.prems(1) by simp
  have fv: "core_term_free_vars operand |\<subseteq>| fmdom vals"
    using CoreTm_Cast.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term d f st operand = eval_const vals operand"
    by (rule CoreTm_Cast.IH[OF c fv CoreTm_Cast.prems(3,4)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term d f st operand = eval_const vals operand"
    show "interp_term d (Suc f) st (CoreTm_Cast targetTy operand)
            = eval_const vals (CoreTm_Cast targetTy operand)"
      by (simp add: h Let_def value_position_eval_const[OF CoreTm_Cast.prems(4)])
  qed
next
  case (CoreTm_Unop op operand)
  have c: "is_constant_term operand" using CoreTm_Unop.prems(1) by simp
  have fv: "core_term_free_vars operand |\<subseteq>| fmdom vals"
    using CoreTm_Unop.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term d f st operand = eval_const vals operand"
    by (rule CoreTm_Unop.IH[OF c fv CoreTm_Unop.prems(3,4)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term d f st operand = eval_const vals operand"
    show "interp_term d (Suc f) st (CoreTm_Unop op operand)
            = eval_const vals (CoreTm_Unop op operand)"
      by (simp add: h value_position_eval_const[OF CoreTm_Unop.prems(4)])
  qed
next
  case (CoreTm_Binop op lhs rhs)
  have c1: "is_constant_term lhs" and c2: "is_constant_term rhs"
    using CoreTm_Binop.prems(1) by simp_all
  have fv1: "core_term_free_vars lhs |\<subseteq>| fmdom vals"
   and fv2: "core_term_free_vars rhs |\<subseteq>| fmdom vals"
    using CoreTm_Binop.prems(2) by (auto simp: fsubset_iff)
  have sub1: "\<exists>N. \<forall>f\<ge>N. interp_term d f st lhs = eval_const vals lhs"
    by (rule CoreTm_Binop.IH(1)[OF c1 fv1 CoreTm_Binop.prems(3,4)])
  have sub2: "\<exists>N. \<forall>f\<ge>N. interp_term d f st rhs = eval_const vals rhs"
    by (rule CoreTm_Binop.IH(2)[OF c2 fv2 CoreTm_Binop.prems(3,4)])
  show ?case
  proof (rule agree_lift2[OF sub1 sub2])
    fix f assume h1: "interp_term d f st lhs = eval_const vals lhs"
             and h2: "interp_term d f st rhs = eval_const vals rhs"
    show "interp_term d (Suc f) st (CoreTm_Binop op lhs rhs)
            = eval_const vals (CoreTm_Binop op lhs rhs)"
      by (simp add: h1 h2 value_position_eval_const[OF CoreTm_Binop.prems(4)]
               split: sum.split option.split)
  qed
next
  case (CoreTm_Let var rhs body)
  have c_rhs: "is_constant_term rhs" and c_body: "is_constant_term body"
    using CoreTm_Let.prems(1) by simp_all
  have fv_rhs: "core_term_free_vars rhs |\<subseteq>| fmdom vals"
    using CoreTm_Let.prems(2) by (auto simp: fsubset_iff)
  have sub_rhs: "\<exists>N. \<forall>f\<ge>N. interp_term d f st rhs = eval_const vals rhs"
    by (rule CoreTm_Let.IH(1)[OF c_rhs fv_rhs CoreTm_Let.prems(3,4)])
  show ?case
  proof (cases "eval_const vals rhs")
    case (Inl err)
    show ?thesis
    proof (rule agree_lift1[OF sub_rhs])
      fix f assume h: "interp_term d f st rhs = eval_const vals rhs"
      show "interp_term d (Suc f) st (CoreTm_Let var rhs body)
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
    \<comment> \<open>The right-hand side is in a place position, so the interpreter did not check
        its value. It has no allocated part all the same, so the extended map
        still satisfies the premise.\<close>
    have "deep_unallocated (IS_ExternAlloc st) rhsVal"
      by (rule eval_const_deep_unallocated[OF CoreTm_Let.prems(4) Inr])
    with CoreTm_Let.prems(4)
    have ua': "\<forall>name c. fmlookup vals' name = Some c
                 \<longrightarrow> deep_unallocated (IS_ExternAlloc st) c"
      by (auto simp: vals'_def)
    have ua'': "\<forall>name c. fmlookup vals' name = Some c
                  \<longrightarrow> deep_unallocated (IS_ExternAlloc st'') c"
      using ua' by (simp add: st''_def)
    have sub_body: "\<exists>N. \<forall>f\<ge>N. interp_term d f st'' body = eval_const vals' body"
      by (rule CoreTm_Let.IH(2)[OF c_body fv_body ag' ua''])
    show ?thesis
    proof (rule agree_lift2[OF sub_rhs sub_body])
      fix f assume h1: "interp_term d f st rhs = eval_const vals rhs"
               and h2: "interp_term d f st'' body = eval_const vals' body"
      have "interp_term d (Suc f) st (CoreTm_Let var rhs body)
              = value_position st (interp_term d f st'' body)"
        by (simp add: h1 Inr st''_def Let_def)
      also have "... = eval_const vals' body"
        by (simp add: h2 value_position_eval_const[OF ua'])
      finally show "interp_term d (Suc f) st (CoreTm_Let var rhs body)
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
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term d f st payload = eval_const vals payload"
    by (rule CoreTm_VariantCtor.IH[OF c fv CoreTm_VariantCtor.prems(3,4)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term d f st payload = eval_const vals payload"
    show "interp_term d (Suc f) st (CoreTm_VariantCtor ctorName tyArgs payload)
            = eval_const vals (CoreTm_VariantCtor ctorName tyArgs payload)"
      by (simp add: h value_position_eval_const[OF CoreTm_VariantCtor.prems(4)])
  qed
next
  case (CoreTm_Record flds)
  have members: "\<And>t. t \<in> set (map snd flds) \<Longrightarrow>
                   \<exists>N. \<forall>f\<ge>N. interp_term d f st t = eval_const vals t"
  proof -
    fix t assume "t \<in> set (map snd flds)"
    then obtain nm where mem: "(nm, t) \<in> set flds" by auto
    have c: "is_constant_term t"
      using CoreTm_Record.prems(1) mem by (fastforce simp: list_all_iff)
    have fv: "core_term_free_vars t |\<subseteq>| fmdom vals"
      using CoreTm_Record.prems(2) mem
      by (fastforce simp: fsubset_iff fmember_ffUnion_fimage_fset_of_list_iff)
    show "\<exists>N. \<forall>f\<ge>N. interp_term d f st t = eval_const vals t"
      using CoreTm_Record.IH mem c fv CoreTm_Record.prems(3,4) by fastforce
  qed
  show ?case
  proof (rule agree_lift_list[OF agree_list[OF members]])
    fix f assume h: "interp_term_list d f st (map snd flds)
                       = eval_const_list vals (map snd flds)"
    show "interp_term d (Suc f) st (CoreTm_Record flds)
            = eval_const vals (CoreTm_Record flds)"
      by (simp add: h value_position_list_eval_const_list[OF CoreTm_Record.prems(4)])
  qed
next
  case (CoreTm_RecordProj tm fldName)
  have c: "is_constant_term tm" using CoreTm_RecordProj.prems(1) by simp
  have fv: "core_term_free_vars tm |\<subseteq>| fmdom vals"
    using CoreTm_RecordProj.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term d f st tm = eval_const vals tm"
    by (rule CoreTm_RecordProj.IH[OF c fv CoreTm_RecordProj.prems(3,4)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term d f st tm = eval_const vals tm"
    show "interp_term d (Suc f) st (CoreTm_RecordProj tm fldName)
            = eval_const vals (CoreTm_RecordProj tm fldName)"
      by (simp add: h)
  qed
next
  case (CoreTm_VariantProj tm expectedCtor)
  have c: "is_constant_term tm" using CoreTm_VariantProj.prems(1) by simp
  have fv: "core_term_free_vars tm |\<subseteq>| fmdom vals"
    using CoreTm_VariantProj.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term d f st tm = eval_const vals tm"
    by (rule CoreTm_VariantProj.IH[OF c fv CoreTm_VariantProj.prems(3,4)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term d f st tm = eval_const vals tm"
    show "interp_term d (Suc f) st (CoreTm_VariantProj tm expectedCtor)
            = eval_const vals (CoreTm_VariantProj tm expectedCtor)"
      by (simp add: h)
  qed
next
  case (CoreTm_ArrayProj arr idxTms)
  have c_arr: "is_constant_term arr"
    using CoreTm_ArrayProj.prems(1) by simp
  have fv_arr: "core_term_free_vars arr |\<subseteq>| fmdom vals"
    using CoreTm_ArrayProj.prems(2) by (auto simp: fsubset_iff)
  have sub_arr: "\<exists>N. \<forall>f\<ge>N. interp_term d f st arr = eval_const vals arr"
    by (rule CoreTm_ArrayProj.IH(1)[OF c_arr fv_arr CoreTm_ArrayProj.prems(3,4)])
  have members: "\<And>t. t \<in> set idxTms \<Longrightarrow>
                   \<exists>N. \<forall>f\<ge>N. interp_term d f st t = eval_const vals t"
  proof -
    fix t assume mem: "t \<in> set idxTms"
    have c: "is_constant_term t"
      using CoreTm_ArrayProj.prems(1) mem by (auto simp: list_all_iff)
    have fv: "core_term_free_vars t |\<subseteq>| fmdom vals"
      using CoreTm_ArrayProj.prems(2) mem
      by (fastforce simp: fsubset_iff fmember_ffUnion_fimage_fset_of_list_iff)
    show "\<exists>N. \<forall>f\<ge>N. interp_term d f st t = eval_const vals t"
      using CoreTm_ArrayProj.IH(2) mem c fv CoreTm_ArrayProj.prems(3,4) by blast
  qed
  show ?case
  proof (rule agree_lift_tm_list[OF sub_arr agree_list[OF members]])
    fix f assume h1: "interp_term d f st arr = eval_const vals arr"
             and h2: "interp_term_list d f st idxTms = eval_const_list vals idxTms"
    show "interp_term d (Suc f) st (CoreTm_ArrayProj arr idxTms)
            = eval_const vals (CoreTm_ArrayProj arr idxTms)"
      by (simp add: h1 h2 value_position_list_eval_const_list[OF CoreTm_ArrayProj.prems(4)]
               split: sum.split CoreValue.split)
  qed
next
  case (CoreTm_Match scrut arms)
  have c_scrut: "is_constant_term scrut"
    using CoreTm_Match.prems(1) by simp
  have fv_scrut: "core_term_free_vars scrut |\<subseteq>| fmdom vals"
    using CoreTm_Match.prems(2) by (auto simp: fsubset_iff)
  have sub_scrut: "\<exists>N. \<forall>f\<ge>N. interp_term d f st scrut = eval_const vals scrut"
    by (rule CoreTm_Match.IH(1)[OF c_scrut fv_scrut CoreTm_Match.prems(3,4)])
  show ?case
  proof (cases "eval_const vals scrut")
    case (Inl err)
    show ?thesis
    proof (rule agree_lift1[OF sub_scrut])
      fix f assume h: "interp_term d f st scrut = eval_const vals scrut"
      show "interp_term d (Suc f) st (CoreTm_Match scrut arms)
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
        fix f assume h: "interp_term d f st scrut = eval_const vals scrut"
        show "interp_term d (Suc f) st (CoreTm_Match scrut arms)
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
      have sub_arm: "\<exists>N. \<forall>f\<ge>N. interp_term d f st armTm = eval_const vals armTm"
        using CoreTm_Match.IH(2) mem c_arm fv_arm CoreTm_Match.prems(3,4) by fastforce
      show ?thesis
      proof (rule agree_lift2[OF sub_scrut sub_arm])
        fix f assume h1: "interp_term d f st scrut = eval_const vals scrut"
                 and h2: "interp_term d f st armTm = eval_const vals armTm"
        show "interp_term d (Suc f) st (CoreTm_Match scrut arms)
                = eval_const vals (CoreTm_Match scrut arms)"
          by (simp add: h1 h2 \<open>eval_const vals scrut = Inr scrutVal\<close> fma
                   value_position_eval_const[OF CoreTm_Match.prems(4)])
      qed
    qed
  qed
next
  case (CoreTm_Sizeof tm)
  have c: "is_constant_term tm" using CoreTm_Sizeof.prems(1) by simp
  have fv: "core_term_free_vars tm |\<subseteq>| fmdom vals"
    using CoreTm_Sizeof.prems(2) by simp
  have sub: "\<exists>N. \<forall>f\<ge>N. interp_term d f st tm = eval_const vals tm"
    by (rule CoreTm_Sizeof.IH[OF c fv CoreTm_Sizeof.prems(3,4)])
  show ?case
  proof (rule agree_lift1[OF sub])
    fix f assume h: "interp_term d f st tm = eval_const vals tm"
    show "interp_term d (Suc f) st (CoreTm_Sizeof tm)
            = eval_const vals (CoreTm_Sizeof tm)"
      by (simp add: h)
  qed
next
  case (CoreTm_Allocated ty tm)
  then show ?case by simp
next
  case (CoreTm_Default defTy)
  then show ?case by simp
qed


(* ========================================================================== *)
(* Main results for eval_const/interp_term agreement *)
(* ========================================================================== *)

(* Compile-time constant evaluation equals runtime interpretation (for SOME fuel, at
   any depth) at any well-typed state that agrees with the constants' value map,
   provided that no constant is allocated (hypothesis `unalloc` below).

   We do not prove that the global constants of an elaborated module are never allocated
   (this is future work), but clearly this should be the case: constant elaboration can be
   thought of as filling in bytes in a "data section" of the program, before execution
   even begins, and therefore it cannot allocate anything on the heap. *)
theorem eval_const_interp_agree:
  fixes st :: "'w InterpState"
  assumes const: "is_constant_term tm"
      and fv: "core_term_free_vars tm |\<subseteq>| fmdom globalVals"
      and ag: "vals_agree st globalVals"
      and sme: "state_matches_env st env storeTyping"
      and unalloc: "\<And>name c. fmlookup globalVals name = Some c
                      \<Longrightarrow> \<not> is_allocated (IS_ExternAlloc st) c"
  shows "\<exists>fuel. interp_term d fuel st tm = eval_const globalVals tm"
proof -
  have ua: "\<forall>name c. fmlookup globalVals name = Some c
              \<longrightarrow> deep_unallocated (IS_ExternAlloc st) c"
  proof (intro allI impI)
    fix name c assume lk: "fmlookup globalVals name = Some c"
    from vals_agree_value_typed[OF sme ag lk] obtain cty where "value_has_type env c cty" ..
    thus "deep_unallocated (IS_ExternAlloc st) c"
      using unalloc[OF lk] by (rule value_has_type_deep_unallocated)
  qed
  obtain N where "\<forall>f\<ge>N. interp_term d f st tm = eval_const globalVals tm"
    using eval_const_interp_agree_gen[where d = d, OF const fv ag ua] by blast
  thus ?thesis by (meson order_refl)
qed

(* Similar result for fold_const (the elaborator's wrapper over eval_const). *)
corollary fold_const_interp_agree:
  fixes st :: "'w InterpState"
  assumes const: "is_constant_term tm"
      and fold_ok: "fold_const globalVals loc tm = Inr v"
      and ag: "vals_agree st globalVals"
      and sme: "state_matches_env st env storeTyping"
      and unalloc: "\<And>name c. fmlookup globalVals name = Some c
                      \<Longrightarrow> \<not> is_allocated (IS_ExternAlloc st) c"
  shows "\<exists>fuel. interp_term d fuel st tm = Inr v"
proof -
  from fold_ok have
    miss: "core_term_free_vars tm |-| fmdom globalVals = {||}" and
    ev: "eval_const globalVals tm = Inr v"
    unfolding fold_const_def by (auto simp: Let_def split: if_splits sum.splits)
  have fv: "core_term_free_vars tm |\<subseteq>| fmdom globalVals"
    using miss by (metis fempty_iff fminus_iff fsubsetI)
  show ?thesis
    using eval_const_interp_agree[where d = d, OF const fv ag sme unalloc] ev by simp
qed

(* A canonical witness for vals_agree: globals hold exactly the constants' value map,
   and all other fields are empty. The world type is fixed to `unit`. The state is in
   executable mode, and its oracle says that no extern value is allocated. *)
definition const_eval_state :: "(string, CoreValue) fmap \<Rightarrow> unit InterpState" where
  "const_eval_state vals =
     \<lparr> IS_Globals = vals,
       IS_Locals = fmempty,
       IS_Refs = fmempty,
       IS_Store = [],
       IS_ConstLocals = {||},
       IS_TyArgs = fmempty,
       IS_Ghost = NotGhost,
       IS_Datatypes = fmempty,
       IS_DataCtors = fmempty,
       IS_DataCtorsByType = fmempty,
       IS_Functions = fmempty,
       IS_World = (),
       IS_ExternAlloc = (\<lambda>_ _ _. False) \<rparr>"

lemma const_eval_state_agrees: "vals_agree (const_eval_state vals) vals"
  by (simp add: vals_agree_def const_eval_state_def)

(* A successful fold_const is the same (on compile-time constant terms) as a call to
   the term interpreter, in a specific InterpState, provided that the constants' values
   are well typed and none of them is allocated.

   const_eval_state has no functions and no datatype tables, so it does not match a type
   environment in general (state_matches_env); the typing of the constants' values is
   therefore asked for directly, as module_globals_well_typed. "Not allocated" is
   judged with the oracle of const_eval_state.

   This theorem could be used to justify a claim (e.g. in a language specification
   document) that the elaborator evaluates constants at compile time using the ordinary
   dynamic semantics of the Core language (in the particular InterpState given by
   const_eval_state). *)
corollary fold_const_is_core_evaluation:
  assumes const: "is_constant_term tm"
      and fold_ok: "fold_const globalVals loc tm = Inr v"
      and gvals: "module_globals_well_typed env globalVals"
      and unalloc: "\<And>name c. fmlookup globalVals name = Some c
                      \<Longrightarrow> \<not> is_allocated (\<lambda>_ _ _. False) c"
  shows "\<exists>fuel. interp_term d fuel (const_eval_state globalVals) tm = Inr v"
proof -
  from fold_ok have
    miss: "core_term_free_vars tm |-| fmdom globalVals = {||}" and
    ev: "eval_const globalVals tm = Inr v"
    unfolding fold_const_def by (auto simp: Let_def split: if_splits sum.splits)
  have fv: "core_term_free_vars tm |\<subseteq>| fmdom globalVals"
    using miss by (metis fempty_iff fminus_iff fsubsetI)
  have orc: "IS_ExternAlloc (const_eval_state globalVals) = (\<lambda>_ _ _. False)"
    by (simp add: const_eval_state_def)
  have ua: "\<forall>name c. fmlookup globalVals name = Some c
              \<longrightarrow> deep_unallocated (IS_ExternAlloc (const_eval_state globalVals)) c"
    unfolding orc
  proof (intro allI impI)
    fix name c assume lk: "fmlookup globalVals name = Some c"
    from gvals lk obtain cty where "value_has_type env c cty"
      unfolding module_globals_well_typed_def by blast
    thus "deep_unallocated (\<lambda>_ _ _. False) c"
      using unalloc[OF lk] by (rule value_has_type_deep_unallocated)
  qed
  obtain N where
    "\<forall>f\<ge>N. interp_term d f (const_eval_state globalVals) tm = eval_const globalVals tm"
    using eval_const_interp_agree_gen[where d = d, OF const fv const_eval_state_agrees ua]
    by blast
  with ev show ?thesis by (metis order_refl)
qed

end

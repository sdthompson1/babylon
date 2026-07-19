theory CoreValueTransfer
  imports CoreValue TypeSubstModuleEnv TyEnvExtension
begin

(* Transfer lemmas for value_has_type across environment changes: extension
   along the declaration axes (linking's weakening direction) and type
   substitution through the environment's constructor tables (linking's
   normalization direction).

   The key observation throughout is that a well-typed value's types are
   ground (value_has_type_ground), and every kind/runtime check that
   value_has_type makes is on a type whose groundness the same clause
   asserts. So value_has_type only really reads TE_Datatypes, TE_DataCtors
   and TE_GhostDatatypes, and it is stable under any change that preserves
   the entries those reads can hit. *)


(* ========================================================================== *)
(* Ground monotonicity of the kind and runtime checks                         *)
(* ========================================================================== *)

(* For a ground type, well-kindedness transfers to any env whose datatype
   table preserves the old entries (TE_TypeVars is never consulted). *)
lemma is_well_kinded_ground_mono:
  assumes dt: "\<And>d n. fmlookup (TE_Datatypes env) d = Some n
                 \<Longrightarrow> fmlookup (TE_Datatypes env') d = Some n"
      and ground: "type_tyvars ty = {}"
      and wk: "is_well_kinded env ty"
  shows "is_well_kinded env' ty"
using ground wk proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  from CoreTy_Datatype.prems(2) obtain numTyVars where
    lk: "fmlookup (TE_Datatypes env) name = Some numTyVars" and
    len: "length argTypes = numTyVars" and
    args: "list_all (is_well_kinded env) argTypes"
    by (auto split: option.splits)
  from CoreTy_Datatype.prems(1) have args_ground: "\<forall>t \<in> set argTypes. type_tyvars t = {}"
    by auto
  have args': "list_all (is_well_kinded env') argTypes"
    using CoreTy_Datatype.IH args args_ground unfolding list_all_iff by blast
  show ?case using dt[OF lk] len args' by simp
next
  case (CoreTy_Record flds)
  have each: "\<And>a b. (a, b) \<in> set flds \<Longrightarrow> is_well_kinded env' b"
  proof -
    fix a b assume mem: "(a, b) \<in> set flds"
    from mem CoreTy_Record.prems(2) have wkb: "is_well_kinded env b"
      by (auto simp: list_all_iff)
    from mem CoreTy_Record.prems(1) have gb: "type_tyvars b = {}"
      by (auto simp: case_prod_beta)
    show "is_well_kinded env' b"
      using CoreTy_Record.IH gb mem wkb by auto
  qed
  thus ?case using CoreTy_Record.prems(2) by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  then show ?case by auto
next
  case (CoreTy_Var n)
  then show ?case by simp
qed simp_all

(* For a ground, well-kinded type, runtime-ness transfers to any env whose
   datatype table preserves the old entries and whose ghost markers are
   unchanged on the old datatype domain (TE_RuntimeTypeVars is never
   consulted). Well-kindedness pins every datatype name in the type into the
   old domain, where the ghost marker is unchanged. *)
lemma is_runtime_type_ground_mono:
  assumes dt: "\<And>d n. fmlookup (TE_Datatypes env) d = Some n
                 \<Longrightarrow> fmlookup (TE_Datatypes env') d = Some n"
      and gd: "\<And>d. d |\<in>| fmdom (TE_Datatypes env)
                 \<Longrightarrow> (d |\<in>| TE_GhostDatatypes env' \<longleftrightarrow> d |\<in>| TE_GhostDatatypes env)"
      and ground: "type_tyvars ty = {}"
      and wk: "is_well_kinded env ty"
      and rt: "is_runtime_type env ty"
  shows "is_runtime_type env' ty"
using ground wk rt proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  from CoreTy_Datatype.prems(2) obtain numTyVars where
    lk: "fmlookup (TE_Datatypes env) name = Some numTyVars" and
    args_wk: "list_all (is_well_kinded env) argTypes"
    by (auto split: option.splits)
  from CoreTy_Datatype.prems(3) have
    ng: "name |\<notin>| TE_GhostDatatypes env" and
    args_rt: "list_all (is_runtime_type env) argTypes"
    by auto
  from CoreTy_Datatype.prems(1) have args_ground: "\<forall>t \<in> set argTypes. type_tyvars t = {}"
    by auto
  have dom: "name |\<in>| fmdom (TE_Datatypes env)"
    using lk by (simp add: fmdomI)
  have ng': "name |\<notin>| TE_GhostDatatypes env'"
    using gd[OF dom] ng by blast
  have args_rt': "list_all (is_runtime_type env') argTypes"
    using CoreTy_Datatype.IH args_ground args_wk args_rt
    unfolding list_all_iff by blast
  show ?case using ng' args_rt' by simp
next
  case (CoreTy_Record flds)
  have each: "\<And>a b. (a, b) \<in> set flds \<Longrightarrow> is_runtime_type env' b"
  proof -
    fix a b assume mem: "(a, b) \<in> set flds"
    from mem CoreTy_Record.prems(2) have wkb: "is_well_kinded env b"
      by (auto simp: list_all_iff)
    from mem CoreTy_Record.prems(3) have rtb: "is_runtime_type env b"
      by (auto simp: list_all_iff)
    from mem CoreTy_Record.prems(1) have gb: "type_tyvars b = {}"
      by (auto simp: case_prod_beta)
    show "is_runtime_type env' b"
      using CoreTy_Record.IH gb mem rtb wkb by force
  qed
  thus ?case by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  then show ?case by auto
next
  case (CoreTy_Var n)
  then show ?case by simp
qed simp_all


(* ========================================================================== *)
(* value_has_type under environment extension                                 *)
(* ========================================================================== *)

(* value_has_type transfers to any env that preserves the datatype-table
   entries and the ghost markers on the old datatype domain. This is the
   value-side analogue of core_term_type_tyenv_extends, but with weaker
   premises: the tyvar and scope fields may change arbitrarily, because a
   value's types are ground. tyenv_ctors_consistent env pins the variant
   datatype names into the old datatype domain for the ghost-marker
   transfer. *)
lemma value_has_type_env_mono:
  assumes dc: "\<And>c e. fmlookup (TE_DataCtors env) c = Some e
                 \<Longrightarrow> fmlookup (TE_DataCtors env') c = Some e"
      and dt: "\<And>d n. fmlookup (TE_Datatypes env) d = Some n
                 \<Longrightarrow> fmlookup (TE_Datatypes env') d = Some n"
      and gd: "\<And>d. d |\<in>| fmdom (TE_Datatypes env)
                 \<Longrightarrow> (d |\<in>| TE_GhostDatatypes env' \<longleftrightarrow> d |\<in>| TE_GhostDatatypes env)"
      and cons: "tyenv_ctors_consistent env"
      and vht: "value_has_type env val ty"
  shows "value_has_type env' val ty"
using vht proof (induction val arbitrary: ty)
  case (CV_Bool b)
  then show ?case by (cases ty) auto
next
  case (CV_FiniteInt sign bits i)
  then show ?case by (cases ty) auto
next
  case (CV_Record fieldValues)
  have fieldIH: "\<And>v t. v \<in> snd ` set fieldValues \<Longrightarrow>
                   value_has_type env v t \<Longrightarrow> value_has_type env' v t"
    using CV_Record.IH by auto
  show ?case
  proof (cases ty)
    case (CoreTy_Record fieldTypes)
    from CV_Record.prems CoreTy_Record have
      fv_tys: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t)
                 fieldValues fieldTypes" and
      dn: "distinct (map fst fieldTypes)"
      by simp_all
    have len_eq: "length fieldValues = length fieldTypes"
      using fv_tys by (simp add: list_all2_lengthD)
    have target: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env' v t)
                    fieldValues fieldTypes"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length fieldValues = length fieldTypes" using len_eq .
    next
      fix i assume i_lt: "i < length fieldValues"
      from fv_tys i_lt have pair_ok:
        "fst (fieldValues ! i) = fst (fieldTypes ! i) \<and>
         value_has_type env (snd (fieldValues ! i)) (snd (fieldTypes ! i))"
        unfolding list_all2_conv_all_nth by (auto simp: split_def)
      have v_in: "snd (fieldValues ! i) \<in> snd ` set fieldValues"
        using i_lt by (auto intro!: nth_mem imageI)
      have vht': "value_has_type env' (snd (fieldValues ! i)) (snd (fieldTypes ! i))"
        using fieldIH[OF v_in] pair_ok by blast
      show "(case fieldValues ! i of (n1, v) \<Rightarrow>
             \<lambda>(n2, t). n1 = n2 \<and> value_has_type env' v t) (fieldTypes ! i)"
        using pair_ok vht' by (simp add: split_def)
    qed
    show ?thesis using CoreTy_Record target dn by simp
  qed (use CV_Record.prems in auto)
next
  case (CV_Variant ctor payload)
  show ?case
  proof (cases ty)
    case (CoreTy_Datatype dty1 argTypes)
    from CV_Variant.prems CoreTy_Datatype obtain dty2 tyvars payloadTy where
      lookup: "fmlookup (TE_DataCtors env) ctor = Some (dty2, tyvars, payloadTy)" and
      dty_eq: "dty1 = dty2" and
      len_eq: "length tyvars = length argTypes" and
      args_wk: "list_all (is_well_kinded env) argTypes" and
      args_rt: "list_all (is_runtime_type env) argTypes" and
      args_ground: "list_all (\<lambda>a. type_tyvars a = {}) argTypes" and
      not_ghost: "dty1 |\<notin>| TE_GhostDatatypes env" and
      payload_vht: "value_has_type env payload
                      (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
      by (auto split: option.splits)
    have lookup': "fmlookup (TE_DataCtors env') ctor = Some (dty2, tyvars, payloadTy)"
      using dc[OF lookup] .
    have args_wk': "list_all (is_well_kinded env') argTypes"
      using args_wk args_ground is_well_kinded_ground_mono[OF dt]
      unfolding list_all_iff by blast
    have args_rt': "list_all (is_runtime_type env') argTypes"
      using args_wk args_rt args_ground is_runtime_type_ground_mono[OF dt gd]
      unfolding list_all_iff by blast
    have dt_dom: "dty2 |\<in>| fmdom (TE_Datatypes env)"
      using cons lookup unfolding tyenv_ctors_consistent_def
      by (blast intro: fmdomI)
    have not_ghost': "dty1 |\<notin>| TE_GhostDatatypes env'"
      using gd[OF dt_dom] not_ghost dty_eq by blast
    have payload': "value_has_type env' payload
                      (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
      using CV_Variant.IH payload_vht by blast
    show ?thesis
      using CoreTy_Datatype lookup' dty_eq len_eq args_wk' args_rt' args_ground
            not_ghost' payload'
      by simp
  qed (use CV_Variant.prems in auto)
next
  case (CV_Array sizes valuesMap)
  show ?case
  proof (cases ty)
    case (CoreTy_Array elemTy dims)
    from CV_Array.prems CoreTy_Array have
      elem_wk: "is_well_kinded env elemTy" and
      elem_rt: "is_runtime_type env elemTy" and
      elem_ground: "type_tyvars elemTy = {}" and
      elems_vht: "\<forall>idx val. fmlookup valuesMap idx = Some val
                             \<longrightarrow> value_has_type env val elemTy" and
      dims_wk: "array_dims_well_kinded dims" and
      matches: "fmap_matches_sizes sizes valuesMap" and
      sizes_ok: "sizes_match_dims sizes dims"
      by simp_all
    have elem_wk': "is_well_kinded env' elemTy"
      using is_well_kinded_ground_mono[OF dt elem_ground elem_wk] .
    have elem_rt': "is_runtime_type env' elemTy"
      using is_runtime_type_ground_mono[OF dt gd elem_ground elem_wk elem_rt] .
    have elems_vht': "\<forall>idx val. fmlookup valuesMap idx = Some val
                                 \<longrightarrow> value_has_type env' val elemTy"
    proof (intro allI impI)
      fix idx val
      assume lk: "fmlookup valuesMap idx = Some val"
      with elems_vht have vht_v: "value_has_type env val elemTy" by blast
      from CV_Array.IH[of val elemTy] vht_v lk
      show "value_has_type env' val elemTy"
        by (auto simp: fmran'I)
    qed
    show ?thesis
      using CoreTy_Array elem_wk' elem_rt' elem_ground elems_vht'
            dims_wk matches sizes_ok
      by simp
  qed (use CV_Array.prems in auto)
qed

(* Corollary in terms of tyenv_extends: the extension's lookup-preservation
   and ghost-marker clauses are exactly the premises of the mono lemma. *)
lemma value_has_type_tyenv_extends:
  assumes ext: "tyenv_extends env env'"
      and cons: "tyenv_ctors_consistent env"
      and vht: "value_has_type env val ty"
  shows "value_has_type env' val ty"
proof (rule value_has_type_env_mono[OF _ _ _ cons vht])
  fix c e assume "fmlookup (TE_DataCtors env) c = Some e"
  thus "fmlookup (TE_DataCtors env') c = Some e"
    using ext unfolding tyenv_extends_def by blast
next
  fix d n assume "fmlookup (TE_Datatypes env) d = Some n"
  thus "fmlookup (TE_Datatypes env') d = Some n"
    using ext unfolding tyenv_extends_def by blast
next
  fix d assume "d |\<in>| fmdom (TE_Datatypes env)"
  thus "d |\<in>| TE_GhostDatatypes env' \<longleftrightarrow> d |\<in>| TE_GhostDatatypes env"
    using ext unfolding tyenv_extends_def by blast
qed


(* ========================================================================== *)
(* value_has_type under type substitution through the environment             *)
(* ========================================================================== *)

(* The generic form: env' is any env whose constructor table is env's with
   the substitution applied to the payload types, and whose datatype table
   and ghost markers are unchanged. The value is untouched (values contain no
   types), and its type moves by apply_subst - though since a well-typed
   value's type is ground, the substitution on the type side is a no-op
   (see value_has_type_apply_subst_ground below).

   Capture-avoidance (cap) and binder distinctness (dist) make the
   constructor-payload instantiation commute with the substitution
   (subst_names_avoid_compose). *)
lemma value_has_type_apply_subst_generic:
  assumes dc': "TE_DataCtors env' = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
      and dt': "TE_Datatypes env' = TE_Datatypes env"
      and gd': "TE_GhostDatatypes env' = TE_GhostDatatypes env"
      and cap: "\<And>ctorName dtName tyVars payloadTy.
                  fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payloadTy)
                  \<Longrightarrow> subst_names subst |\<inter>| fset_of_list tyVars = {||}"
      and dist: "\<And>ctorName dtName tyVars payloadTy.
                   fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payloadTy)
                   \<Longrightarrow> distinct tyVars"
      and vht: "value_has_type env val ty"
  shows "value_has_type env' val (apply_subst subst ty)"
using vht proof (induction val arbitrary: ty)
  case (CV_Bool b)
  then show ?case by (cases ty) auto
next
  case (CV_FiniteInt sign bits i)
  then show ?case by (cases ty) auto
next
  case (CV_Record fieldValues)
  have fieldIH: "\<And>v t. v \<in> snd ` set fieldValues \<Longrightarrow>
                   value_has_type env v t \<Longrightarrow> value_has_type env' v (apply_subst subst t)"
    using CV_Record.IH by auto
  show ?case
  proof (cases ty)
    case (CoreTy_Record fieldTypes)
    from CV_Record.prems CoreTy_Record have
      fv_tys: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t)
                 fieldValues fieldTypes" and
      dn: "distinct (map fst fieldTypes)"
      by simp_all
    have len_eq: "length fieldValues = length fieldTypes"
      using fv_tys by (simp add: list_all2_lengthD)
    let ?fieldTypes' = "map (\<lambda>(name, t). (name, apply_subst subst t)) fieldTypes"
    have fst_eq: "map fst ?fieldTypes' = map fst fieldTypes"
      by (induction fieldTypes) auto
    have len_eq': "length fieldValues = length ?fieldTypes'"
      using len_eq by simp
    have target: "list_all2 (\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env' v t)
                    fieldValues ?fieldTypes'"
      unfolding list_all2_conv_all_nth
    proof (intro conjI allI impI)
      show "length fieldValues = length ?fieldTypes'" using len_eq' .
    next
      fix i assume i_lt: "i < length fieldValues"
      from fv_tys i_lt have pair_ok:
        "fst (fieldValues ! i) = fst (fieldTypes ! i) \<and>
         value_has_type env (snd (fieldValues ! i)) (snd (fieldTypes ! i))"
        unfolding list_all2_conv_all_nth by (auto simp: split_def)
      have v_in: "snd (fieldValues ! i) \<in> snd ` set fieldValues"
        using i_lt by (auto intro!: nth_mem imageI)
      have vht': "value_has_type env' (snd (fieldValues ! i))
                    (apply_subst subst (snd (fieldTypes ! i)))"
        using fieldIH[OF v_in] pair_ok by blast
      have nth_eq: "?fieldTypes' ! i = (fst (fieldTypes ! i),
                                        apply_subst subst (snd (fieldTypes ! i)))"
        using i_lt len_eq by (simp add: split_def)
      show "(case fieldValues ! i of (n1, v) \<Rightarrow>
             \<lambda>(n2, t). n1 = n2 \<and> value_has_type env' v t) (?fieldTypes' ! i)"
        using pair_ok vht' nth_eq by (simp add: split_def)
    qed
    have ty'_eq: "apply_subst subst ty = CoreTy_Record ?fieldTypes'"
      using CoreTy_Record by simp
    show ?thesis
      unfolding ty'_eq using target dn fst_eq
      by (metis (no_types, lifting) CoreType.simps(67) value_has_type.simps(3))
  qed (use CV_Record.prems in auto)
next
  case (CV_Variant ctor payload)
  show ?case
  proof (cases ty)
    case (CoreTy_Datatype dty1 argTypes)
    from CV_Variant.prems CoreTy_Datatype obtain dty2 tyvars payloadTy where
      lookup: "fmlookup (TE_DataCtors env) ctor = Some (dty2, tyvars, payloadTy)" and
      dty_eq: "dty1 = dty2" and
      len_eq: "length tyvars = length argTypes" and
      args_wk: "list_all (is_well_kinded env) argTypes" and
      args_rt: "list_all (is_runtime_type env) argTypes" and
      args_ground: "list_all (\<lambda>a. type_tyvars a = {}) argTypes" and
      not_ghost: "dty1 |\<notin>| TE_GhostDatatypes env" and
      payload_vht: "value_has_type env payload
                      (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
      by (auto split: option.splits)
    \<comment> \<open>Ground argument types are fixed by the substitution.\<close>
    have args_id_each: "\<And>a. a \<in> set argTypes \<Longrightarrow> apply_subst subst a = a"
    proof -
      fix a assume "a \<in> set argTypes"
      hence "type_tyvars a = {}" using args_ground by (simp add: list_all_iff)
      thus "apply_subst subst a = a"
        using apply_subst_disjoint_id by simp
    qed
    have args_id: "map (apply_subst subst) argTypes = argTypes"
      using args_id_each by (simp add: map_idI)
    have ty'_eq: "apply_subst subst ty = CoreTy_Datatype dty1 argTypes"
      using CoreTy_Datatype args_id by simp
    \<comment> \<open>The substituted constructor entry.\<close>
    have lookup': "fmlookup (TE_DataCtors env') ctor
                     = Some (dty2, tyvars, apply_subst subst payloadTy)"
      using lookup unfolding dc' by simp
    \<comment> \<open>Kind/runtime checks: ground congruence over the unchanged fields.\<close>
    have args_wk': "list_all (is_well_kinded env') argTypes"
      using args_wk args_ground is_well_kinded_ground_cong_env[OF _ dt']
      unfolding list_all_iff by blast
    have args_rt': "list_all (is_runtime_type env') argTypes"
      using args_rt args_ground is_runtime_type_ground_cong_env[OF _ gd']
      unfolding list_all_iff by blast
    have not_ghost': "dty1 |\<notin>| TE_GhostDatatypes env'"
      using not_ghost gd' by simp
    \<comment> \<open>Payload: the IH moves the value across, and capture-avoidance commutes
        the instantiation with the substitution.\<close>
    have payload_IH: "value_has_type env' payload
                        (apply_subst subst
                           (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy))"
      using CV_Variant.IH payload_vht by blast
    have commute: "apply_subst (fmap_of_list (zip tyvars (map (apply_subst subst) argTypes)))
                     (apply_subst subst payloadTy)
                     = apply_subst subst
                         (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
      by (rule subst_names_avoid_compose[OF len_eq cap[OF lookup] dist[OF lookup]])
    have payload': "value_has_type env' payload
                      (apply_subst (fmap_of_list (zip tyvars argTypes))
                         (apply_subst subst payloadTy))"
      using payload_IH commute args_id by simp
    show ?thesis
      unfolding ty'_eq
      using lookup' dty_eq len_eq args_wk' args_rt' args_ground not_ghost' payload'
      by simp
  qed (use CV_Variant.prems in auto)
next
  case (CV_Array sizes valuesMap)
  show ?case
  proof (cases ty)
    case (CoreTy_Array elemTy dims)
    from CV_Array.prems CoreTy_Array have
      elem_wk: "is_well_kinded env elemTy" and
      elem_rt: "is_runtime_type env elemTy" and
      elem_ground: "type_tyvars elemTy = {}" and
      elems_vht: "\<forall>idx val. fmlookup valuesMap idx = Some val
                             \<longrightarrow> value_has_type env val elemTy" and
      dims_wk: "array_dims_well_kinded dims" and
      matches: "fmap_matches_sizes sizes valuesMap" and
      sizes_ok: "sizes_match_dims sizes dims"
      by simp_all
    have elem_id: "apply_subst subst elemTy = elemTy"
      using apply_subst_disjoint_id elem_ground by simp
    have ty'_eq: "apply_subst subst ty = CoreTy_Array elemTy dims"
      using CoreTy_Array elem_id by simp
    have elem_wk': "is_well_kinded env' elemTy"
      using elem_wk is_well_kinded_ground_cong_env[OF elem_ground dt'] by blast
    have elem_rt': "is_runtime_type env' elemTy"
      using elem_rt is_runtime_type_ground_cong_env[OF elem_ground gd'] by blast
    have elems_vht': "\<forall>idx val. fmlookup valuesMap idx = Some val
                                 \<longrightarrow> value_has_type env' val elemTy"
    proof (intro allI impI)
      fix idx val
      assume lk: "fmlookup valuesMap idx = Some val"
      with elems_vht have vht_v: "value_has_type env val elemTy" by blast
      from CV_Array.IH[of val elemTy] vht_v lk
      have "value_has_type env' val (apply_subst subst elemTy)"
        by (auto simp: fmran'I)
      thus "value_has_type env' val elemTy" using elem_id by simp
    qed
    show ?thesis
      unfolding ty'_eq
      using elem_wk' elem_rt' elem_ground elems_vht' dims_wk matches sizes_ok
      by simp
  qed (use CV_Array.prems in auto)
qed

(* The type side of the substitution is in fact a no-op: a well-typed value's
   type is ground. *)
lemma value_has_type_apply_subst_ground:
  assumes "value_has_type env val ty"
  shows "apply_subst subst ty = ty"
proof (rule apply_subst_disjoint_id)
  show "type_tyvars ty \<inter> fset (fmdom subst) = {}"
    using value_has_type_ground[OF assms] by simp
qed

(* Instantiation for apply_subst_to_tyenv. tyenv_well_formed supplies the
   binder distinctness; capture-avoidance must be supplied by the caller
   (from the module invariant's capture_avoiding, or the elaborator's
   corresponding check). *)
lemma value_has_type_apply_subst_to_tyenv:
  assumes vht: "value_has_type env val ty"
      and wf: "tyenv_well_formed env"
      and cap: "\<And>ctorName dtName tyVars payloadTy.
                  fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payloadTy)
                  \<Longrightarrow> subst_names subst |\<inter>| fset_of_list tyVars = {||}"
  shows "value_has_type (apply_subst_to_tyenv subst env) val (apply_subst subst ty)"
proof (rule value_has_type_apply_subst_generic[OF _ _ _ cap _ vht])
  show "TE_DataCtors (apply_subst_to_tyenv subst env)
          = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
    by (simp add: apply_subst_to_tyenv_def)
  show "TE_Datatypes (apply_subst_to_tyenv subst env) = TE_Datatypes env"
    by (simp add: apply_subst_to_tyenv_def)
  show "TE_GhostDatatypes (apply_subst_to_tyenv subst env) = TE_GhostDatatypes env"
    by (simp add: apply_subst_to_tyenv_def)
next
  fix ctorName dtName tyVars payloadTy
  assume "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payloadTy)"
  thus "distinct tyVars"
    using wf unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast
qed

(* Instantiation for apply_subst_to_module_env: the value-side analogue of
   core_term_type_subst_module_env. module_env_subst_ok's constructor
   capture-avoidance clause supplies cap; tyenv_well_formed supplies the
   binder distinctness. (No runtime_ok side condition: a value's types are
   ground, so runtime-ness never consults the substituted tyvars.) *)
lemma value_has_type_subst_module_env:
  assumes vht: "value_has_type env val ty"
      and wf: "tyenv_well_formed env"
      and ok: "module_env_subst_ok subst targetEnv env"
  shows "value_has_type (apply_subst_to_module_env subst targetEnv env) val
                        (apply_subst subst ty)"
proof (rule value_has_type_apply_subst_generic[OF _ _ _ _ _ vht])
  show "TE_DataCtors (apply_subst_to_module_env subst targetEnv env)
          = fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)"
    by (simp add: apply_subst_to_module_env_def)
  show "TE_Datatypes (apply_subst_to_module_env subst targetEnv env) = TE_Datatypes env"
    by (simp add: apply_subst_to_module_env_def)
  show "TE_GhostDatatypes (apply_subst_to_module_env subst targetEnv env)
          = TE_GhostDatatypes env"
    by (simp add: apply_subst_to_module_env_def)
next
  fix ctorName dtName tyVars payloadTy
  assume lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payloadTy)"
  show "subst_names subst |\<inter>| fset_of_list tyVars = {||}"
    using ok lk unfolding module_env_subst_ok_def by blast
  show "distinct tyVars"
    using wf lk unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by blast
qed

end

theory CoreValue
  imports "../core/CoreTyEnv" "../core/CoreKindcheck" "../core/MetaSubst"
          "../core/CoreTyEnvWellFormed"
begin

(* This file defines CoreValue and provides some helpers e.g. type calculations. *)


(* ========================================================================== *)
(* CoreValue definition *)
(* ========================================================================== *)

(* Evaluated values *)
(* This only covers runtime values - MathInt/MathReal not included *)
datatype CoreValue =
  CV_Bool bool
  | CV_FiniteInt Signedness IntBits int
  | CV_Record "(string \<times> CoreValue) list"
  | CV_Variant string CoreValue
  | CV_Array "int list" "(int list, CoreValue) fmap"  (* size list, array index \<rightarrow> value *)
  (* TODO: extern or abstract types? *)


(* ========================================================================== *)
(* Array dimension helpers *)
(* ========================================================================== *)

(* Generate all indices for an array with given sizes.
   E.g. all_indices [2, 3] = [[0,0], [0,1], [0,2], [1,0], [1,1], [1,2]] *)
fun all_indices :: "int list \<Rightarrow> int list list" where
  "all_indices [] = [[]]"
| "all_indices (n # ns) =
    (let rest = all_indices ns
     in concat (map (\<lambda>i. map (\<lambda>idx. i # idx) rest) (map int [0..<nat n])))"

(* Check that sizes are all non-negative and fit in u64 *)
definition sizes_valid :: "int list \<Rightarrow> bool" where
  "sizes_valid sizes \<equiv> list_all (\<lambda>s. s \<ge> 0 \<and> s \<le> snd (int_range Unsigned IntBits_64)) sizes"

(* Check that the fmap's keys are exactly the expected set of indices for the given sizes *)
definition fmap_matches_sizes :: "int list \<Rightarrow> (int list, 'a) fmap \<Rightarrow> bool" where
  "fmap_matches_sizes sizes fm \<equiv>
    sizes_valid sizes \<and> fmdom fm = fset_of_list (all_indices sizes)"

(* Check that sizes are consistent with dimension specs (for Fixed dimensions) *)
fun sizes_match_dims :: "int list \<Rightarrow> CoreDimension list \<Rightarrow> bool" where
  "sizes_match_dims [] [] = True"
| "sizes_match_dims (s # ss) (CoreDim_Fixed n # ds) = (s = n \<and> sizes_match_dims ss ds)"
| "sizes_match_dims (s # ss) (_ # ds) = sizes_match_dims ss ds"
| "sizes_match_dims _ _ = False"  (* mismatched lengths *)


(* ========================================================================== *)
(* Type judgement for CoreValues *)
(* ========================================================================== *)

(* Note: we cannot always know the type of a CoreValue uniquely, for example,
   the value "Nothing" could be Nothing<i32>, Nothing<bool>, etc. However, we 
   can provide a typing relation which tells you whether a given value has a
   given (ground) type, as follows. *)

function value_has_type :: "CoreTyEnv \<Rightarrow> CoreValue \<Rightarrow> CoreType \<Rightarrow> bool" where
  "value_has_type env (CV_Bool _) ty = (ty = CoreTy_Bool)"
| "value_has_type env (CV_FiniteInt sign bits i) ty =
    (ty = CoreTy_FiniteInt sign bits \<and> int_fits sign bits i)"
| "value_has_type env (CV_Record fieldValues) ty =
    (case ty of
      CoreTy_Record fieldTypes \<Rightarrow>
        list_all2 (\<lambda>(name1, fldVal) (name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
          fieldValues fieldTypes
    | _ \<Rightarrow> False)"
| "value_has_type env (CV_Variant ctor payload) ty =
    (case ty of
      CoreTy_Name dty1 argTypes \<Rightarrow>
        (case fmlookup (TE_DataCtors env) ctor of
          Some (dty2, metavars, payloadTy) \<Rightarrow>
            (dty1 = dty2 \<and>
            length metavars = length argTypes \<and>
            list_all (is_well_kinded env) argTypes \<and>
            list_all is_runtime_type argTypes \<and>
            value_has_type env payload
                (apply_subst (fmap_of_list (zip metavars argTypes)) payloadTy))
        | None \<Rightarrow> False)
    | _ \<Rightarrow> False)"
| "value_has_type env (CV_Array sizes valuesMap) ty =
    (case ty of
      CoreTy_Array elemTy dims \<Rightarrow>
        is_well_kinded env elemTy \<and>
        is_runtime_type elemTy \<and>
        (\<forall>idx val. fmlookup valuesMap idx = Some val \<longrightarrow> value_has_type env val elemTy) \<and>
        array_dims_well_kinded dims \<and>
        fmap_matches_sizes sizes valuesMap \<and>
        sizes_match_dims sizes dims
    | _ => False)"

  by pat_completeness auto


(* ========================================================================== *)
(* Termination proof *)
(* ========================================================================== *)

(* Values in an array are smaller than the array containing them *)
lemma size_array_lookup:
  assumes "fmlookup vals idx = Some v"
  shows "size v < size (CV_Array sizes vals)"
proof -
  from assms have mem: "(idx, v) |\<in>| fset_of_fmap vals"
    by transfer auto
  hence mem': "(idx, v) \<in> fset (fset_of_fmap vals)"
    by simp
  let ?f = "\<lambda>x. Suc (case x of (a, x) \<Rightarrow> size x)"
  have "?f (idx, v) \<le> (\<Sum>x\<in>fset (fset_of_fmap vals). ?f x)"
    by (rule member_le_sum[OF mem']) auto
  hence "Suc (size v) \<le> (\<Sum>x\<in>fset (fset_of_fmap vals). Suc (case x of (a, x) \<Rightarrow> size x))"
    by simp
  thus ?thesis
    by simp
qed

(* Record field values are smaller than the record *)
lemma size_record_field:
  assumes "(name, v) \<in> set flds"
  shows "size v < size (CV_Record flds)"
proof -
  from assms have "size v < Suc (size_list (size_prod (\<lambda>_. 0) size) flds)"
    by (induction flds) auto
  thus ?thesis by simp
qed

termination value_has_type
proof (relation "measure (\<lambda>(env, val, ty). size val)")
  show "wf (measure (\<lambda>(env, val, ty). size val))" by simp
next
  (* Record case: z \<in> set fieldValues, (x, y) = z, so y is a field value *)
  fix env :: CoreTyEnv
  fix fieldValues :: "(string \<times> CoreValue) list"
  fix ty :: CoreType
  fix x6 yb xa xb
  fix z :: "string \<times> CoreValue"
  fix x :: string
  fix y :: CoreValue
  assume "z \<in> set fieldValues" and "(x, y) = z"
  then have "(x, y) \<in> set fieldValues" by simp
  then show "((env, y, xb), env, CV_Record fieldValues, ty)
             \<in> measure (\<lambda>(env, val, ty). size val)"
    using size_record_field by auto
next
  (* Variant case: payload is direct subterm *)
  fix env :: CoreTyEnv
  fix ctor :: string
  fix payload :: CoreValue
  fix ty :: CoreType
  fix x11 :: string
  fix x12 :: "CoreType list"
  fix x2 x y
  fix xa :: "nat list"
  fix ya :: CoreType
  show "((env, payload, apply_subst (fmap_of_list (zip xa x12)) ya),
         env, CV_Variant ctor payload, ty) \<in> measure (\<lambda>(env, val, ty). size val)"
    by simp
next
  (* Array case *)
  fix env :: CoreTyEnv
  fix sizes :: "int list"
  fix valuesMap :: "(int list, CoreValue) fmap"
  fix ty :: CoreType 
  fix x71 x72 x
  fix xa :: CoreValue
  assume "fmlookup valuesMap x = Some xa"
  then show "((env, xa, x71), env, CV_Array sizes valuesMap, ty)
             \<in> measure (\<lambda>(env, val, ty). size val)"
    using size_array_lookup by auto
qed


(* ========================================================================== *)
(* Value types are well-kinded and runtime *)
(* ========================================================================== *)

lemma value_has_type_well_kinded:
  assumes "value_has_type env val ty"
      and "tyenv_well_formed env"
  shows "is_well_kinded env ty"
using assms proof (induction val arbitrary: ty)
  case (CV_Bool b)
  then show ?case by simp
next
  case (CV_FiniteInt sign bits i)
  then show ?case by simp
next
  case (CV_Record fieldValues)
  then obtain fieldTypes where
    ty_eq: "ty = CoreTy_Record fieldTypes" and
    all2: "list_all2 (\<lambda>(name1, fldVal) (name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
             fieldValues fieldTypes"
    by (cases ty) auto
  have "list_all (is_well_kinded env) (map snd fieldTypes)"
    unfolding list_all_iff
  proof
    fix fldTy
    assume "fldTy \<in> set (map snd fieldTypes)"
    then obtain name2 where name2_in: "(name2, fldTy) \<in> set fieldTypes" by auto
    from all2 have len_eq: "length fieldValues = length fieldTypes"
      by (rule list_all2_lengthD)
    from name2_in obtain i where
      i_bound: "i < length fieldTypes" and
      idx_eq: "fieldTypes ! i = (name2, fldTy)"
      by (metis in_set_conv_nth)
    with len_eq have i_bound': "i < length fieldValues" by simp
    define fldVal where "fldVal = snd (fieldValues ! i)"
    define name1 where "name1 = fst (fieldValues ! i)"
    have fv_idx: "fieldValues ! i = (name1, fldVal)"
      by (simp add: name1_def fldVal_def)
    from all2 i_bound have "(\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t)
                             (fieldValues ! i) (fieldTypes ! i)"
      by (simp add: list_all2_nthD2)
    with fv_idx idx_eq have typed: "value_has_type env fldVal fldTy" by simp
    from i_bound' fv_idx have in_fv: "(name1, fldVal) \<in> set fieldValues"
      by (metis nth_mem)
    from in_fv have "fldVal \<in> snd ` set fieldValues" by force
    then show "is_well_kinded env fldTy"
      using CV_Record.IH assms(2) typed by fastforce
  qed
  then show ?case using ty_eq by simp
next
  case (CV_Variant ctor payload)
  then obtain dtName argTypes metavars payloadTy where
    ty_eq: "ty = CoreTy_Name dtName argTypes" and
    lookup: "fmlookup (TE_DataCtors env) ctor = Some (dtName, metavars, payloadTy)" and
    len_eq: "length metavars = length argTypes" and
    args_wk: "list_all (is_well_kinded env) argTypes"
    by (cases ty) (auto split: option.splits prod.splits)
  (* From tyenv_well_formed, we know ctors are consistent with datatypes *)
  from CV_Variant.prems(2) have "tyenv_ctors_consistent env"
    unfolding tyenv_well_formed_def by simp
  then have dt_lookup: "fmlookup (TE_Datatypes env) dtName = Some (length metavars)"
    using lookup unfolding tyenv_ctors_consistent_def by blast
  (* dtName is in TE_Datatypes, so it's not a type variable (by disjointness) *)
  from CV_Variant.prems(2) have "tyenv_tyvars_datatypes_disjoint env"
    unfolding tyenv_well_formed_def by simp
  then have "dtName |\<notin>| TE_TypeVars env"
    by (meson disjoint_iff_fnot_equal dt_lookup fmdomI
        tyenv_tyvars_datatypes_disjoint_def)
  show ?case
    using ty_eq dt_lookup len_eq args_wk \<open>dtName |\<notin>| TE_TypeVars env\<close> by simp
next
  case (CV_Array sizes valuesMap)
  then obtain elemTy dims where
    ty_eq: "ty = CoreTy_Array elemTy dims" and
    elem_wk: "is_well_kinded env elemTy" and
    dims_wk: "array_dims_well_kinded dims"
    by (cases ty) auto
  show ?case
    using ty_eq elem_wk dims_wk by simp
qed

lemma value_has_type_runtime:
  assumes "value_has_type env val ty"
  shows "is_runtime_type ty"
using assms proof (induction val arbitrary: ty)
  case (CV_Bool b)
  then show ?case by simp
next
  case (CV_FiniteInt sign bits i)
  then show ?case by simp
next
  case (CV_Record fieldValues)
  then obtain fieldTypes where
    ty_eq: "ty = CoreTy_Record fieldTypes" and
    all2: "list_all2 (\<lambda>(name1, fldVal) (name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy)
             fieldValues fieldTypes"
    by (cases ty) auto
  have "list_all is_runtime_type (map snd fieldTypes)"
    unfolding list_all_iff
  proof
    fix fldTy
    assume "fldTy \<in> set (map snd fieldTypes)"
    then obtain name2 where name2_in: "(name2, fldTy) \<in> set fieldTypes" by auto
    from all2 have len_eq: "length fieldValues = length fieldTypes"
      by (rule list_all2_lengthD)
    from name2_in obtain i where
      i_bound: "i < length fieldTypes" and
      idx_eq: "fieldTypes ! i = (name2, fldTy)"
      by (metis in_set_conv_nth)
    with len_eq have i_bound': "i < length fieldValues" by simp
    define fldVal where "fldVal = snd (fieldValues ! i)"
    define name1 where "name1 = fst (fieldValues ! i)"
    have fv_idx: "fieldValues ! i = (name1, fldVal)"
      by (simp add: name1_def fldVal_def)
    from all2 i_bound have "(\<lambda>(n1, v) (n2, t). n1 = n2 \<and> value_has_type env v t)
                             (fieldValues ! i) (fieldTypes ! i)"
      by (simp add: list_all2_nthD2)
    with fv_idx idx_eq have typed: "value_has_type env fldVal fldTy" by simp
    from i_bound' fv_idx have in_fv: "(name1, fldVal) \<in> set fieldValues"
      by (metis nth_mem)
    then show "is_runtime_type fldTy"
      using CV_Record.IH typed by fastforce
  qed
  then show ?case using ty_eq by simp
next
  case (CV_Variant ctor payload)
  then obtain dtName argTypes where
    ty_eq: "ty = CoreTy_Name dtName argTypes" and
    args_rt: "list_all is_runtime_type argTypes"
    by (cases ty) (auto split: option.splits prod.splits)
  show ?case
    using ty_eq args_rt by simp
next
  case (CV_Array sizes valuesMap)
  then obtain elemTy dims where
    ty_eq: "ty = CoreTy_Array elemTy dims" and
    elem_rt: "is_runtime_type elemTy"
    by (cases ty) auto
  show ?case
    using ty_eq elem_rt by simp
qed


(* ========================================================================== *)
(* Helper lemmas for extracting value structure from types *)
(* ========================================================================== *)

lemma value_has_type_Bool:
  assumes "value_has_type env val CoreTy_Bool"
  shows "\<exists>b. val = CV_Bool b"
  using assms by (cases val; auto)

lemma value_has_type_FiniteInt:
  assumes "value_has_type env val (CoreTy_FiniteInt sign bits)"
  shows "\<exists>i. val = CV_FiniteInt sign bits i \<and> int_fits sign bits i"
  using assms by (cases val; auto)

end
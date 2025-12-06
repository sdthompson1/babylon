theory ValueTyping
  imports "BabInterp" "../type_system/BabTypecheck"
begin

(*-----------------------------------------------------------------------------*)
(* Definition: Type judgement for BabValues against fully resolved types *)
(*-----------------------------------------------------------------------------*)

(* Check if a value has a given type. The type must be kind-correct.
   Structured by case on value first, then type, for better simp rules. *)
function value_has_type :: "BabTyEnv \<Rightarrow> BabValue \<Rightarrow> BabType \<Rightarrow> bool" where
  "value_has_type env (BV_Bool _) ty = (case ty of BabTy_Bool _ \<Rightarrow> True | _ \<Rightarrow> False)"
| "value_has_type env (BV_FiniteInt sign bits i) ty =
    (case ty of
      BabTy_FiniteInt _ sign' bits' \<Rightarrow> sign = sign' \<and> bits = bits' \<and> int_fits sign bits i
    | _ \<Rightarrow> False)"
| "value_has_type env (BV_MathInt _) ty = (case ty of BabTy_MathInt _ \<Rightarrow> True | _ \<Rightarrow> False)"
| "value_has_type env (BV_Tuple vals) ty =
    (case ty of
      BabTy_Tuple _ tys \<Rightarrow>
        length vals = length tys \<and>
        list_all (\<lambda>(v, t). value_has_type env v t) (zip vals tys)
    | _ \<Rightarrow> False)"
| "value_has_type env (BV_Record fldVals) ty =
    (case ty of
      BabTy_Record _ fldTys \<Rightarrow>
        length fldVals = length fldTys \<and>
        list_all (\<lambda>((nameV, v), (nameT, t)). nameV = nameT \<and> value_has_type env v t)
                 (zip fldVals fldTys)
    | _ \<Rightarrow> False)"
| "value_has_type env (BV_Array dims vals) ty =
    (case ty of
      BabTy_Array _ elemTy expectedDims \<Rightarrow>
        length dims = length expectedDims \<and>
        (\<forall>idx v. fmlookup vals idx = Some v \<longrightarrow> value_has_type env v elemTy)
    | _ \<Rightarrow> False)"
| "value_has_type env (BV_Variant ctor_name maybePayload) ty =
    (case ty of
      BabTy_Name _ ty_name tyargs \<Rightarrow>
        (case fmlookup (TE_DataCtors env) ctor_name of
          Some (dtName, numTyArgs, maybePayloadTy) \<Rightarrow>
            dtName = ty_name \<and>
            (case (maybePayload, maybePayloadTy) of
              (None, None) \<Rightarrow> True
            | (Some payloadVal, Some payloadTy) \<Rightarrow>
                (case fmlookup (TE_Datatypes env) dtName of
                  Some tyVars \<Rightarrow>
                    let subst = fmap_of_list (zip tyVars tyargs);
                        substitutedTy = substitute_bab_type subst payloadTy
                    in value_has_type env payloadVal substitutedTy
                | None \<Rightarrow> False)
            | _ \<Rightarrow> False)
        | None \<Rightarrow> False)
    | _ \<Rightarrow> False)"
| "value_has_type env (BV_Abstract _) ty = False"
  by pat_completeness auto


(*-----------------------------------------------------------------------------*)
(* Termination proof *)
(*-----------------------------------------------------------------------------*)

lemma size_list_elem:
  assumes "x \<in> set xs"
  shows "size x < Suc (size_list size xs)"
  using assms by (induction xs) auto

lemma size_tuple_elem:
  assumes "v \<in> set vals"
  shows "size v < size (BV_Tuple vals)"
  using size_list_elem[OF assms] by simp

lemma size_record_elem_aux:
  assumes "(name, v) \<in> set flds"
  shows "size v < Suc (size_list (size_prod (\<lambda>x. 0) size) flds)"
  using assms by (induction flds) auto

lemma size_record_elem:
  assumes "v \<in> set (map snd flds)"
  shows "size v < size (BV_Record flds)"
proof -
  from assms obtain name where "(name, v) \<in> set flds" by auto
  then have "size v < Suc (size_list (size_prod (\<lambda>x. 0) size) flds)"
    by (rule size_record_elem_aux)
  then show ?thesis by simp
qed

termination value_has_type
proof (relation "measure (\<lambda>(env, val, ty). size val)")
  show "wf (measure (\<lambda>(env, val, ty). size val))" by simp
next
  (* Tuple case *)
  fix env :: BabTyEnv
  fix vals :: "BabValue list"
  fix ty x61 x62 z x y
  assume "ty = BabTy_Tuple x61 x62" and "z \<in> set (zip vals x62)" and "(x, y) = z"
  then have "x \<in> set vals" by (metis set_zip_leftD)
  then show "((env, x, y), env, BV_Tuple vals, ty) \<in> measure (\<lambda>(env, val, ty). size val)"
    using size_tuple_elem by auto
next
  (* Record case *)
  fix env :: BabTyEnv
  fix fldVals :: "(string \<times> BabValue) list"
  fix ty x71 x72 z x y xa ya xb xc
  assume "ty = BabTy_Record x71 x72" and "z \<in> set (zip fldVals x72)"
     and "(x, y) = z" and "(xa, ya) = x"
  then have "(xa, ya) \<in> set fldVals" by (metis set_zip_leftD)
  then have "ya \<in> set (map snd fldVals)" by force
  then show "((env, ya, xc), env, BV_Record fldVals, ty) \<in> measure (\<lambda>(env, val, ty). size val)"
    using size_record_elem by auto
next
  (* Array case *)
  fix env :: BabTyEnv
  fix dims 
  fix vals :: "(int list, BabValue) fmap"
  fix ty x81 x82 x83 x xa
  assume "ty = BabTy_Array x81 x82 x83" and "fmlookup vals x = Some xa"
  then show "((env, xa, x82), env, BV_Array dims vals, ty) \<in> measure (\<lambda>(env, val, ty). size val)"
    using size_fmap_lookup by auto
next
  (* Variant case *)
  fix env :: BabTyEnv
  fix ctor_name maybePayload ty x11 x12 x13 x2 x y xa
  fix ya :: "BabType option"
  fix xaa yb
  fix x2a :: BabValue
  fix x2b x2c xb xc
  assume "ty = BabTy_Name x11 x12 x13"
     and "(xaa, yb) = (maybePayload, ya)" and "xaa = Some x2a"
  then have "maybePayload = Some x2a" by simp
  then show "((env, x2a, xc), env, BV_Variant ctor_name maybePayload, ty)
             \<in> measure (\<lambda>(env, val, ty). size val)"
    by simp
qed


(*-----------------------------------------------------------------------------*)
(* Helper lemmas for extracting value structure from types *)
(*-----------------------------------------------------------------------------*)

lemma value_has_type_Bool:
  assumes "value_has_type env val (BabTy_Bool loc)"
  shows "\<exists>b. val = BV_Bool b"
  using assms by (cases val; auto)

lemma value_has_type_FiniteInt:
  assumes "value_has_type env val (BabTy_FiniteInt loc sign bits)"
  shows "\<exists>v. val = BV_FiniteInt sign bits v \<and> int_fits sign bits v"
  using assms by (cases val; auto)

(* If a value has an integer type, it must be BV_FiniteInt or BV_MathInt *)
lemma value_has_integer_type_cases:
  assumes "value_has_type env val ty"
      and "is_integer_type ty"
  obtains (FiniteInt) sign bits i where "val = BV_FiniteInt sign bits i"
        | (MathInt) i where "val = BV_MathInt i"
  using assms by (cases ty; cases val; auto)


(*-----------------------------------------------------------------------------*)
(* value_has_type is preserved under type equality *)
(*-----------------------------------------------------------------------------*)

(* If val has type ty1, then it also has any equal type, presuming that the env
   was well-formed and ty1 was well-kinded *)
lemma value_has_type_types_equal:
  assumes "value_has_type env val ty1"
    and "types_equal ty1 ty2"
    and "tyenv_well_formed env"
    and "is_well_kinded env ty1"
  shows "value_has_type env val ty2"
  using assms
proof (induction val arbitrary: ty1 ty2 rule: measure_induct_rule[where f=size])
  case (less val)

  have has_type: "value_has_type env val ty1" using less.prems by simp
  have types_eq: "types_equal ty1 ty2" using less.prems by simp
  have wf_env: "tyenv_well_formed env" using less.prems by simp
  have ty1_wk: "is_well_kinded env ty1" using less.prems by simp

  show "value_has_type env val ty2"
  proof (cases ty1)
    case (BabTy_Bool loc1)
    then obtain b where "val = BV_Bool b" using has_type
      by (cases val; auto)
    moreover obtain loc2 where "ty2 = BabTy_Bool loc2" using types_eq BabTy_Bool
      by (cases ty2; auto)
    ultimately show ?thesis
      by simp
  next
    case (BabTy_FiniteInt loc1 s1 b1)
    then obtain sign bits i where "val = BV_FiniteInt sign bits i"
      and sign_eq: "sign = s1" and bits_eq: "bits = b1" and fits: "int_fits sign bits i"
      using has_type by (cases val; auto)
    moreover obtain loc2 s2 b2 where "ty2 = BabTy_FiniteInt loc2 s2 b2"
      and "s2 = s1" and "b2 = b1"
      using types_eq BabTy_FiniteInt by (cases ty2; auto)
    ultimately show ?thesis
      by simp
  next
    case (BabTy_MathInt loc1)
    then obtain i where "val = BV_MathInt i" using has_type
      by (cases val; auto)
    moreover obtain loc2 where "ty2 = BabTy_MathInt loc2" using types_eq BabTy_MathInt
      by (cases ty2; auto)
    ultimately show ?thesis
      by simp
  next
    case (BabTy_MathReal loc1)
    then have "False" using has_type by (cases val; auto)
    then show ?thesis by simp
  next
    case (BabTy_Tuple loc1 tys1)
    (* Get that val is a tuple with matching length *)
    obtain vals where val_tuple: "val = BV_Tuple vals"
      using has_type BabTy_Tuple by (cases val) auto
    from has_type BabTy_Tuple val_tuple have
      len_eq1: "length vals = length tys1" and
      vals_typed: "list_all (\<lambda>(v, ty). value_has_type env v ty) (zip vals tys1)"
      by auto

    (* ty2 must also be a tuple with types_equal element types *)
    obtain loc2 tys2 where ty2_def: "ty2 = BabTy_Tuple loc2 tys2"
      using types_eq BabTy_Tuple by (cases ty2; auto)
    from types_eq BabTy_Tuple ty2_def have types_eq': "types_equal (BabTy_Tuple loc1 tys1) (BabTy_Tuple loc2 tys2)"
      by simp
    from types_eq'[unfolded types_equal_Tuple] have
      len_eq_tys: "length tys1 = length tys2" by simp
    hence tys_eq: "list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip tys1 tys2)"
      using \<open>length tys1 = length tys2 \<and> list_all (\<lambda>(x, y). types_equal x y) (zip tys1 tys2)\<close>
      by auto      
    hence len_eq2: "length vals = length tys2"
      using len_eq1 by (simp add: len_eq_tys) 

    (* Each element value has the corresponding ty2 type *)
    have vals_typed2: "list_all (\<lambda>(v, ty). value_has_type env v ty) (zip vals tys2)"
    proof -
      have "\<forall>i < length vals. value_has_type env (vals ! i) (tys2 ! i)"
      proof (intro allI impI)
        fix i assume i_bound: "i < length vals"
        (* vals ! i has type tys1 ! i *)
        from vals_typed i_bound len_eq1 have "value_has_type env (vals ! i) (tys1 ! i)"
          by (simp add: list_all_length)
        (* tys1 ! i types_equal tys2 ! i *)
        moreover from tys_eq i_bound len_eq1 len_eq_tys have "types_equal (tys1 ! i) (tys2 ! i)"
          by (simp add: list_all_length)
        (* tys1 ! i is well-kinded *)
        moreover from ty1_wk BabTy_Tuple i_bound len_eq1 have "is_well_kinded env (tys1 ! i)"
          by (simp add: list_all_length)
        (* vals ! i is smaller than val *)
        moreover from val_tuple i_bound have "size (vals ! i) < size val"
          using size_tuple_elem[of "vals ! i" vals] by simp
        ultimately show "value_has_type env (vals ! i) (tys2 ! i)"
          using less.IH wf_env by blast
      qed
      thus ?thesis
        using len_eq2 by (simp add: list_all_length)
    qed

    from val_tuple ty2_def len_eq2 vals_typed2 show ?thesis
      by simp
  next
    case (BabTy_Record loc1 flds1)
    (* Get that val is a record with matching fields *)
    from has_type BabTy_Record obtain fldVals where
      val_record: "val = BV_Record fldVals" and
      len_eq1: "length fldVals = length flds1" and
      flds_typed: "list_all (\<lambda>((nameV, v), (nameT, ty)). nameV = nameT \<and> value_has_type env v ty)
                            (zip fldVals flds1)"
      by (cases val; auto)

    (* ty2 must also be a record with types_equal field types *)
    obtain loc2 flds2 where ty2_def: "ty2 = BabTy_Record loc2 flds2"
      using types_eq BabTy_Record by (cases ty2; auto)
    from types_eq BabTy_Record ty2_def have types_eq': "types_equal (BabTy_Record loc1 flds1) (BabTy_Record loc2 flds2)"
      by simp
    from types_eq'[unfolded types_equal_Record] have
      len_eq_flds: "length flds1 = length flds2" by simp
    from types_eq'[unfolded types_equal_Record] have
      flds_eq: "list_all (\<lambda>(f1, f2). fst f1 = fst f2 \<and> types_equal (snd f1) (snd f2)) (zip flds1 flds2)"
      by simp
    hence len_eq2: "length fldVals = length flds2"
      using len_eq1
      by (simp add: len_eq_flds)

    (* Each field value has the corresponding ty2 type *)
    have flds_typed2: "list_all (\<lambda>((nameV, v), (nameT, ty)). nameV = nameT \<and> value_has_type env v ty)
                                (zip fldVals flds2)"
    proof -
      have "\<forall>i < length fldVals.
              fst (fldVals ! i) = fst (flds2 ! i) \<and>
              value_has_type env (snd (fldVals ! i)) (snd (flds2 ! i))"
      proof (intro allI impI)
        fix i assume i_bound: "i < length fldVals"
        (* Field names match and value has type from flds1 *)
        obtain nameV v where fldVals_i: "fldVals ! i = (nameV, v)"
          by (cases "fldVals ! i") auto
        obtain nameT t where flds1_i: "flds1 ! i = (nameT, t)"
          by (cases "flds1 ! i") auto
        from flds_typed i_bound len_eq1 fldVals_i flds1_i have
          "nameV = nameT" and "value_has_type env v t"
          by (auto simp: list_all_length)
        hence name_eq1: "fst (fldVals ! i) = fst (flds1 ! i)"
          and val_typed1: "value_has_type env (snd (fldVals ! i)) (snd (flds1 ! i))"
          using fldVals_i flds1_i by auto
        (* Field names match between flds1 and flds2, and types are equal *)
        from flds_eq i_bound len_eq1 len_eq_flds have
          name_eq2: "fst (flds1 ! i) = fst (flds2 ! i)" and
          ty_eq: "types_equal (snd (flds1 ! i)) (snd (flds2 ! i))"
          by (auto simp: list_all_length split: prod.splits)
        (* snd (flds1 ! i) is well-kinded *)
        from ty1_wk BabTy_Record i_bound len_eq1 have "is_well_kinded env (snd (flds1 ! i))"
          by (auto simp: list_all_length comp_def)
        (* snd (fldVals ! i) is smaller than val *)
        moreover from val_record i_bound have "size (snd (fldVals ! i)) < size val"
          using size_record_elem[of "snd (fldVals ! i)" fldVals] by simp
        ultimately have "value_has_type env (snd (fldVals ! i)) (snd (flds2 ! i))"
          using val_typed1 ty_eq less.IH wf_env by blast
        with name_eq1 name_eq2 show "fst (fldVals ! i) = fst (flds2 ! i) \<and>
              value_has_type env (snd (fldVals ! i)) (snd (flds2 ! i))"
          by simp
      qed
      thus ?thesis
        using len_eq2 by (auto simp: list_all_length split: prod.splits)
    qed

    from val_record ty2_def len_eq2 flds_typed2 show ?thesis
      by simp
  next
    case (BabTy_Array loc1 elem1 dims1)
    (* Get that val is an array *)
    from has_type BabTy_Array obtain dims vals where
      val_array: "val = BV_Array dims vals" and
      len_eq1: "length dims = length dims1" and
      vals_typed: "\<forall>idx v. fmlookup vals idx = Some v \<longrightarrow> value_has_type env v elem1"
      by (cases val; auto)

    (* ty2 must also be an array with types_equal element type *)
    obtain loc2 elem2 dims2 where ty2_def: "ty2 = BabTy_Array loc2 elem2 dims2"
      using types_eq BabTy_Array by (cases ty2; auto)
    from types_eq BabTy_Array ty2_def have
      elem_eq: "types_equal elem1 elem2" and
      dims_eq: "length dims1 = length dims2"
      by auto
    hence len_eq2: "length dims = length dims2"
      using len_eq1 by simp

    (* elem1 is well-kinded *)
    from ty1_wk BabTy_Array have elem1_wk: "is_well_kinded env elem1"
      by simp

    (* All array values have the elem2 type *)
    have vals_typed2: "\<forall>idx v. fmlookup vals idx = Some v \<longrightarrow> value_has_type env v elem2"
    proof (intro allI impI)
      fix idx v assume lookup: "fmlookup vals idx = Some v"
      from vals_typed lookup have v_typed1: "value_has_type env v elem1"
        by blast
      (* v is smaller than val *)
      from lookup val_array have "size v < size val"
        using size_fmap_lookup by simp
      with v_typed1 elem_eq elem1_wk wf_env show "value_has_type env v elem2"
        using less.IH by blast
    qed

    from val_array ty2_def len_eq2 vals_typed2 show ?thesis
      by simp
  next
    case (BabTy_Name loc1 n1 tyargs1)
    obtain loc2 n2 tyargs2 where ty2_def: "ty2 = BabTy_Name loc2 n2 tyargs2"
      using types_eq BabTy_Name by (cases ty2; auto)
    with types_eq BabTy_Name have name_eq: "n1 = n2"
      by auto
    from types_eq BabTy_Name ty2_def have tyargs_eq:
      "length tyargs1 = length tyargs2"
      "list_all (\<lambda>(t1, t2). types_equal t1 t2) (zip tyargs1 tyargs2)"
      using types_equal_Name by auto

    from has_type BabTy_Name obtain ctor_name maybePayload where
      val_variant: "val = BV_Variant ctor_name maybePayload"
      by (cases val; auto)

    show ?thesis
    proof (cases "fmlookup (TE_DataCtors env) ctor_name")
      case None
      with has_type BabTy_Name val_variant show ?thesis by simp
    next
      case (Some ctor_info)
      obtain dtName numTyArgs maybePayloadTy where
        ctor_info_eq: "ctor_info = (dtName, numTyArgs, maybePayloadTy)"
        by (cases ctor_info) auto

      from has_type BabTy_Name val_variant Some ctor_info_eq
      have dtName_eq: "dtName = n1"
        by simp

      show ?thesis
      proof (cases maybePayload)
        case None
        (* No payload in value *)
        with has_type BabTy_Name val_variant Some ctor_info_eq ty2_def name_eq dtName_eq
        show ?thesis by (cases maybePayloadTy; simp)
      next
        case (Some payloadVal)
        (* Value has payload *)
        show ?thesis
        proof (cases maybePayloadTy)
          case None
          (* Mismatch: value has payload but type doesn't - impossible given has_type *)
          from has_type BabTy_Name val_variant
               \<open>fmlookup (TE_DataCtors env) ctor_name = Some ctor_info\<close> ctor_info_eq
               \<open>maybePayload = Some payloadVal\<close> None
          have False by simp
          thus ?thesis by simp
        next
          case (Some payloadTy)
          (* Both have payload - need to show value_has_type for substituted type *)

          from has_type BabTy_Name val_variant \<open>fmlookup (TE_DataCtors env) ctor_name = Some ctor_info\<close>
               ctor_info_eq \<open>maybePayload = Some payloadVal\<close> Some
          obtain tyVars where
            tyVars_lookup: "fmlookup (TE_Datatypes env) dtName = Some tyVars" and
            payload_has_type: "value_has_type env payloadVal
              (substitute_bab_type (fmap_of_list (zip tyVars tyargs1)) payloadTy)"
            by (auto split: option.splits)

          (* Build the substitutions *)
          let ?subst1 = "fmap_of_list (zip tyVars tyargs1)"
          let ?subst2 = "fmap_of_list (zip tyVars tyargs2)"

          (* Get not_tyvar from tyenv_ctors_consistent *)
          from wf_env have ctors_consistent: "tyenv_ctors_consistent env"
            unfolding tyenv_well_formed_def by simp
          from ctors_consistent \<open>fmlookup (TE_DataCtors env) ctor_name = Some ctor_info\<close> ctor_info_eq
          obtain tyVars' where "fmlookup (TE_Datatypes env) dtName = Some tyVars'"
            and "length tyVars' = numTyArgs"
            and not_tyvar: "dtName |\<notin>| TE_TypeVars env"
            unfolding tyenv_ctors_consistent_def by blast
          with tyVars_lookup have len_tyVars_numTyArgs: "length tyVars = numTyArgs"
            by simp

          (* Get distinct tyVars from tyenv_datatypes_distinct *)
          from wf_env have datatypes_distinct: "tyenv_datatypes_distinct env"
            unfolding tyenv_well_formed_def by simp
          from datatypes_distinct tyVars_lookup have tyVars_distinct: "distinct tyVars"
            unfolding tyenv_datatypes_distinct_def by blast

          (* Get length tyVars = length tyargs1 from ty1 being well-kinded *)
          (* ty1 = BabTy_Name loc1 n1 tyargs1, dtName = n1, and n1 is not a type variable *)
          (* is_well_kinded for BabTy_Name checks: fmlookup TE_Datatypes n1 = Some tyVars
             and length tyargs1 = length tyVars *)
          from ty1_wk BabTy_Name dtName_eq not_tyvar tyVars_lookup
          have len1: "length tyVars = length tyargs1"
            by auto
          have len2: "length tyVars = length tyargs2"
            using len1 tyargs_eq by simp

          (* The two substitutions are types_equal-compatible *)
          have substs_eq: "substs_types_equal ?subst1 ?subst2"
            using zip_substs_types_equal[OF len1 len2 tyargs_eq(2) tyVars_distinct] .

          (* Therefore the substituted types are types_equal *)
          have substituted_types_eq: "types_equal
            (substitute_bab_type ?subst1 payloadTy)
            (substitute_bab_type ?subst2 payloadTy)"
            using substitute_bab_type_preserves_types_equal[OF substs_eq] .

          (* payloadVal is strictly smaller than val *)
          have payload_smaller: "size payloadVal < size val"
            using val_variant \<open>maybePayload = Some payloadVal\<close> by simp

          (* We need to show the substituted payload type is well-kinded for the IH *)
          (* First, get that payloadTy is well-kinded from tyenv_payloads_well_kinded *)
          from wf_env have payloads_wk: "tyenv_payloads_well_kinded env"
            unfolding tyenv_well_formed_def by simp
          from payloads_wk \<open>fmlookup (TE_DataCtors env) ctor_name = Some ctor_info\<close>
               ctor_info_eq Some
          have payloadTy_wk: "is_well_kinded env payloadTy"
            unfolding tyenv_payloads_well_kinded_def by blast

          (* Get that tyargs1 are all well-kinded from ty1_wk *)
          from ty1_wk BabTy_Name dtName_eq not_tyvar tyVars_lookup
          have tyargs1_wk: "list_all (is_well_kinded env) tyargs1"
            by auto

          (* The substitution maps to well-kinded types *)
          from tyargs1_wk have subst1_wk: "subst_types_well_kinded env ?subst1"
            by (rule subst_types_well_kinded_from_zip)

          (* Therefore the substituted payload type is well-kinded *)
          have subst1_payload_wk: "is_well_kinded env (substitute_bab_type ?subst1 payloadTy)"
            using substitute_bab_type_well_kinded[OF payloadTy_wk subst1_wk] .

          (* Now we can use the IH! *)
          have payload_has_type2: "value_has_type env payloadVal
            (substitute_bab_type ?subst2 payloadTy)"
            using less.IH[OF payload_smaller payload_has_type substituted_types_eq wf_env subst1_payload_wk] .

          with ty2_def name_eq dtName_eq val_variant
               \<open>fmlookup (TE_DataCtors env) ctor_name = Some ctor_info\<close> ctor_info_eq
               \<open>maybePayload = Some payloadVal\<close> Some tyVars_lookup
          show ?thesis by simp
        qed
      qed
    qed
  next
    case (BabTy_Meta n)
    thus ?thesis using has_type types_eq by (cases ty2; auto)
  qed
qed


(*-----------------------------------------------------------------------------*)
(* Consistency of BabTyEnv with BabState *)
(*-----------------------------------------------------------------------------*)

(* This predicate says that "name" is defined as a term variable in the state
   (as either a local, reference, or constant)
   and that its current value (in the state) matches the given type. *)
definition term_var_in_state_with_type:
  "term_var_in_state_with_type state env name ty =
    (case fmlookup (BS_Locals state) name of
        Some addr \<Rightarrow> addr < length (BS_Store state) \<and>
                     value_has_type env (BS_Store state ! addr) ty
      | None \<Rightarrow>
        (case fmlookup (BS_RefVars state) name of
          Some (addr, path) \<Rightarrow> addr < length (BS_Store state) \<and>
                               (case get_value_at_path (BS_Store state ! addr) path of
                                  BIR_Success v \<Rightarrow> value_has_type env v ty
                                | _ \<Rightarrow> False)
        | None \<Rightarrow>
            (case fmlookup (BS_Constants state) name of
              Some val \<Rightarrow> value_has_type env val ty
            | None \<Rightarrow> False)))"

(* If a variable is in TE_TermVars, then it exists in the state with the correct type *)
definition vars_have_correct_types :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "vars_have_correct_types state env \<equiv>
    \<forall>name ty. fmlookup (TE_TermVars env) name = Some ty \<longrightarrow>
      term_var_in_state_with_type state env name ty"

(* If a variable is not in TE_TermVars, then it does not exist in the state *)
definition no_extra_vars :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "no_extra_vars state env \<equiv>
    \<forall>name. fmlookup (TE_TermVars env) name = None \<longrightarrow>
      fmlookup (BS_Locals state) name = None \<and>
      fmlookup (BS_RefVars state) name = None \<and>
      fmlookup (BS_Constants state) name = None"

(* Data constructor names in state match those in type environment *)
definition ctors_match :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "ctors_match state env \<equiv>
    BS_NullaryCtors state = ffilter (\<lambda>name.
      case fmlookup (TE_DataCtors env) name of
        Some (_, _, None) \<Rightarrow> True
      | _ \<Rightarrow> False) (fmdom (TE_DataCtors env)) \<and>
    BS_UnaryCtors state = ffilter (\<lambda>name.
      case fmlookup (TE_DataCtors env) name of
        Some (_, _, Some _) \<Rightarrow> True
      | _ \<Rightarrow> False) (fmdom (TE_DataCtors env))"

(* Function declarations in state match those in type environment *)
definition functions_match :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "functions_match state env \<equiv> BS_Functions state = TE_Functions env"

(* Overall definition: state matches environment *)
definition state_matches_env :: "'w BabState \<Rightarrow> BabTyEnv \<Rightarrow> bool" where
  "state_matches_env state env \<equiv>
    vars_have_correct_types state env \<and>
    no_extra_vars state env \<and>
    ctors_match state env \<and>
    functions_match state env"


(*-----------------------------------------------------------------------------*)
(* Helper lemmas for state/environment consistency *)
(*-----------------------------------------------------------------------------*)

(* If a name is not in TE_TermVars, then it's not in BS_Locals, BS_RefVars, or BS_Constants *)
lemma not_in_env_not_in_state:
  assumes "state_matches_env state env"
      and "fmlookup (TE_TermVars env) name = None"
  shows "fmlookup (BS_Locals state) name = None"
    and "fmlookup (BS_RefVars state) name = None"
    and "fmlookup (BS_Constants state) name = None"
  using assms unfolding state_matches_env_def no_extra_vars_def by auto

(* Function lookup in state equals function lookup in env *)
lemma function_lookup_eq:
  assumes "state_matches_env state env"
  shows "fmlookup (BS_Functions state) fnName = fmlookup (TE_Functions env) fnName"
  using assms unfolding state_matches_env_def functions_match_def by simp

(* If a name is a nullary constructor in the type environment, it's in BS_NullaryCtors *)
lemma nullary_ctor_in_state:
  assumes "state_matches_env state env"
      and "fmlookup (TE_DataCtors env) name = Some (dtName, numTyArgs, None)"
  shows "name |\<in>| BS_NullaryCtors state"
proof -
  from assms(1) have "ctors_match state env"
    unfolding state_matches_env_def by simp
  hence "BS_NullaryCtors state = ffilter (\<lambda>n.
      case fmlookup (TE_DataCtors env) n of
        Some (_, _, None) \<Rightarrow> True
      | _ \<Rightarrow> False) (fmdom (TE_DataCtors env))"
    unfolding ctors_match_def by simp
  moreover from assms(2) have "name |\<in>| fmdom (TE_DataCtors env)"
    by (simp add: fmdomI)
  moreover from assms(2) have "(case fmlookup (TE_DataCtors env) name of
        Some (_, _, None) \<Rightarrow> True | _ \<Rightarrow> False)"
    by simp
  ultimately show ?thesis by auto
qed

end

theory RepVal
  imports SizeExpr "../minic/MiniCMemoryLemmas" "../interpreter/CoreInterp"
begin

(* ========================================================================== *)
(* The representation relation (minic/DESIGN.md, section 4)                   *)
(* ========================================================================== *)

(* rep_val env enc hmap mem ty v bs: the bytes bs are the type_size ty bytes
   of the Core value v at the closed type ty, with heap blocks in the MiniC
   memory mem. hmap gives the pointer of each extern handle (hmap 0 = MP_Null
   and injectivity are hypotheses of the theorems that need them, not of
   the relation). The sizes are measured at the pointer size of the encoding
   and the zero assignment (the types are closed).

   The clauses follow section 4 of the design, in a "slice" formulation:
   each component of an aggregate is represented by the slice of bs at its
   offset, and the length of bs is the size of the type. This makes the
   projection lemmas (section "Paths") compositions of slices and the
   update lemmas splices.

   The byte size bound (|ty| < 2^64) is not a clause of the relation: the
   static checker (SizeBound.thy) establishes it for the types a run
   instantiates, and only the descriptor clause needs bounds of its own
   (the element count and the data size fit a uint64_t, so that the index
   arithmetic of the generated code is defined), which the extern
   hypothesis delivers for arrays an extern allocates. *)


section \<open>Scalars\<close>

(* The sizes of closed types at the encoding's pointer size. *)
abbreviation gsz :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> CoreType \<Rightarrow> nat" where
  "gsz env enc ty \<equiv> type_size env (enc_ptr_size enc) (\<lambda>_. 0) ty"

(* The C scalar type of a scalar Core type: bool is uint8_t, integers are
   themselves, extern types are void pointers. *)
fun scalar_ty :: "CoreType \<Rightarrow> CTy option" where
  "scalar_ty CoreTy_Bool = Some CTy_U8"
| "scalar_ty (CoreTy_FiniteInt s b) = Some (CTy_Int s b)"
| "scalar_ty (CoreTy_Extern _ _) = Some CTy_VoidPtr"
| "scalar_ty _ = None"

(* The MiniC value of a scalar Core value. *)
fun scalar_val :: "(nat \<Rightarrow> MPtr) \<Rightarrow> CoreValue \<Rightarrow> MVal option" where
  "scalar_val hmap (CV_Bool b) = Some (MV_U8 (if b then 1 else 0))"
| "scalar_val hmap (CV_FiniteInt s b i) = Some (MV_Int s b i)"
| "scalar_val hmap (CV_Extern _ _ h) = Some (MV_Ptr (hmap h))"
| "scalar_val hmap _ = None"

lemma scalar_ty_width:
  "scalar_ty ty = Some cty \<Longrightarrow> ty_width enc cty = gsz env enc ty"
  by (cases ty) auto

(* The induction hypothesis of a value induction for a record field. *)
lemma snds_pair: "v \<in> Basic_BNFs.snds (n, v)"
  by (simp add: prod_set_defs)

(* The size lemmas of CoreValue.thy in the form the termination goals take
   after simplification. *)
lemmas size_record_field' = size_record_field[simplified]
lemmas size_array_lookup' = size_array_lookup[simplified]


section \<open>Descriptors\<close>

(* The dimension k of a descriptor is a uint64_t at desc_dim_offset P k. *)
definition desc_dims_ok :: "MEncoding \<Rightarrow> int list \<Rightarrow> MByte list \<Rightarrow> bool" where
  "desc_dims_ok enc sizes bs =
    (\<forall>k < length sizes. slice (desc_dim_offset (enc_ptr_size enc) k) 8 bs = encode_val enc (MV_U64 (sizes ! k)))"

(* An array with an allocatable dimension owns its data: the data is a whole
   heap block (which free_array frees). An incomplete array (CoreDim_Unknown
   dimensions) may be a view of a region inside a block (a cast of a fixed
   array). *)
definition allocatable_dims :: "CoreDimension list \<Rightarrow> bool" where
  "allocatable_dims dims = list_ex (\<lambda>d. d = CoreDim_Allocatable) dims"

(* The data of a descriptor with elements: n readable bytes at p, a whole
   block if owned. *)
definition data_region_ok :: "MMem \<Rightarrow> bool \<Rightarrow> MPtr \<Rightarrow> nat \<Rightarrow> MByte list \<Rightarrow> bool" where
  "data_region_ok mem owned p n data =
    (mem_read mem p n = Some data
     \<and> (owned \<longrightarrow> (\<exists>blk. p = MP_Addr blk 0 \<and> fmlookup (MM_Blocks mem) blk = Some data)))"

(* The data pointer of a descriptor without elements: null, or a valid
   pointer (the start of a block, if owned: Array.c may return a non-null
   pointer for an empty allocation, which free_array must be able to free). *)
definition empty_data_ok :: "MMem \<Rightarrow> bool \<Rightarrow> MPtr \<Rightarrow> bool" where
  "empty_data_ok mem owned p =
    (p = MP_Null \<or> (ptr_range_ok mem p 0 \<and> (owned \<longrightarrow> (\<exists>blk. p = MP_Addr blk 0))))"


section \<open>The relation\<close>

function rep_val :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (nat \<Rightarrow> MPtr) \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> CoreValue \<Rightarrow> MByte list \<Rightarrow> bool" where
  "rep_val env enc hmap mem ty (CV_Bool b) bs =
    (ty = CoreTy_Bool \<and> bs = encode_val enc (MV_U8 (if b then 1 else 0)))"
| "rep_val env enc hmap mem ty (CV_FiniteInt s b i) bs =
    (ty = CoreTy_FiniteInt s b \<and> int_fits s b i \<and> bs = encode_val enc (MV_Int s b i))"
| "rep_val env enc hmap mem ty (CV_Record fvs) bs =
    (case ty of
       CoreTy_Record ftys \<Rightarrow>
         distinct (map fst ftys)
         \<and> length bs = gsz env enc (CoreTy_Record ftys)
         \<and> list_all2 (\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
               rep_val env enc hmap mem fty v
                 (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs))
             fvs ftys
     | _ \<Rightarrow> False)"
| "rep_val env enc hmap mem ty (CV_Variant ctor payload) bs =
    (case ty of
       CoreTy_Datatype dt args \<Rightarrow>
         (case fmlookup (TE_DataCtors env) ctor of
            Some (dt2, tyvars, payloadTy) \<Rightarrow>
              dt = dt2 \<and> length tyvars = length args \<and> ctor \<in> set (dt_ctors env dt)
              \<and> length bs = gsz env enc (CoreTy_Datatype dt args)
              \<and> take (tag_size env dt) bs
                  = encode_val enc (MV_Int Unsigned (tag_bits env dt) (int (ctor_tag env dt ctor)))
              \<and> rep_val env enc hmap mem (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) payload
                  (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs)
          | None \<Rightarrow> False)
     | _ \<Rightarrow> False)"
| "rep_val env enc hmap mem ty (CV_Array sizes elems) bs =
    (case ty of
       CoreTy_Array elemTy dims \<Rightarrow>
         sizes_match_dims sizes dims
         \<and> fmdom elems = fset_of_list (all_indices sizes)
         \<and> (if dims_all_fixed dims then
              length bs = gsz env enc elemTy * sizes_count sizes
              \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                   rep_val env enc hmap mem elemTy v
                     (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) bs))
            else
              sizes_valid sizes
              \<and> sizes_count sizes < u64_max
              \<and> gsz env enc elemTy * sizes_count sizes < u64_max
              \<and> length bs = desc_size (enc_ptr_size enc) (length dims)
              \<and> desc_dims_ok enc sizes bs
              \<and> (\<exists>p. take (enc_ptr_size enc) bs = encode_ptr enc p
                   \<and> (if sizes_count sizes = 0 then empty_data_ok mem (allocatable_dims dims) p
                      else (\<exists>data. data_region_ok mem (allocatable_dims dims) p
                                      (gsz env enc elemTy * sizes_count sizes) data
                              \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                                   rep_val env enc hmap mem elemTy v
                                     (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))))))
     | _ \<Rightarrow> False)"
| "rep_val env enc hmap mem ty (CV_Int _) bs = False"
| "rep_val env enc hmap mem ty (CV_Real _) bs = False"
| "rep_val env enc hmap mem ty (CV_Extern n l h) bs = (ty = CoreTy_Extern n l \<and> bs = encode_ptr enc (hmap h))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(env, enc, hmap, mem, ty, v, bs). size v)")
     (auto dest!: set_zip_leftD intro: size_record_field' size_array_lookup')

(* The value forms a type admits. *)
lemma rep_val_Bool_iff:
  "rep_val env enc hmap mem CoreTy_Bool v bs \<longleftrightarrow> (\<exists>b. v = CV_Bool b \<and> bs = encode_val enc (MV_U8 (if b then 1 else 0)))"
  by (cases v) simp_all

lemma rep_val_FiniteInt_iff:
  "rep_val env enc hmap mem (CoreTy_FiniteInt s b) v bs
   \<longleftrightarrow> (\<exists>i. v = CV_FiniteInt s b i \<and> int_fits s b i \<and> bs = encode_val enc (MV_Int s b i))"
  by (cases v) auto

lemma rep_val_Extern_iff:
  "rep_val env enc hmap mem (CoreTy_Extern n l) v bs \<longleftrightarrow> (\<exists>h. v = CV_Extern n l h \<and> bs = encode_ptr enc (hmap h))"
  by (cases v) auto

(* The record clause, taken apart. *)
lemma rep_val_Record_E:
  assumes "rep_val env enc hmap mem ty (CV_Record fvs) bs"
  obtains ftys where "ty = CoreTy_Record ftys" and "distinct (map fst ftys)"
    and "length bs = gsz env enc (CoreTy_Record ftys)"
    and "list_all2 (\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
           rep_val env enc hmap mem fty v
             (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)) fvs ftys"
  using assms by (cases ty) auto

lemma rep_val_Variant_E:
  assumes "rep_val env enc hmap mem ty (CV_Variant ctor payload) bs"
  obtains dt args tyvars payloadTy where "ty = CoreTy_Datatype dt args"
    and "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
    and "length tyvars = length args" and "ctor \<in> set (dt_ctors env dt)"
    and "length bs = gsz env enc (CoreTy_Datatype dt args)"
    and "take (tag_size env dt) bs = encode_val enc (MV_Int Unsigned (tag_bits env dt) (int (ctor_tag env dt ctor)))"
    and "rep_val env enc hmap mem (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) payload
           (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs)"
  using assms by (cases ty) (auto split: option.splits)

lemma rep_val_Array_E:
  assumes "rep_val env enc hmap mem ty (CV_Array sizes elems) bs"
  obtains elemTy dims where "ty = CoreTy_Array elemTy dims"
    and "sizes_match_dims sizes dims" and "fmdom elems = fset_of_list (all_indices sizes)"
  using assms by (cases ty) auto

(* The fixed-array clause. *)
lemma rep_val_FixedArray_E:
  assumes "rep_val env enc hmap mem (CoreTy_Array elemTy dims) (CV_Array sizes elems) bs"
    and "dims_all_fixed dims"
  shows "sizes = dims_sizes dims"
    and "fmdom elems = fset_of_list (all_indices sizes)"
    and "length bs = gsz env enc elemTy * sizes_count sizes"
    and "\<And>idx v. fmlookup elems idx = Some v \<Longrightarrow>
           rep_val env enc hmap mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) bs)"
proof -
  show "sizes = dims_sizes dims"
  proof -
    have "sizes_match_dims sizes dims" using assms(1) by simp
    with assms(2) show ?thesis
    proof (induction sizes dims rule: sizes_match_dims.induct)
      case (2 s ss n ds)
      then show ?case by (simp add: dims_all_fixed_def dims_sizes_def)
    qed (auto simp: dims_all_fixed_def dims_sizes_def)
  qed
qed (use assms in simp_all)

(* The descriptor clause. *)
lemma rep_val_Desc_E:
  assumes "rep_val env enc hmap mem (CoreTy_Array elemTy dims) (CV_Array sizes elems) bs"
    and "\<not> dims_all_fixed dims"
  obtains p where "sizes_match_dims sizes dims" and "fmdom elems = fset_of_list (all_indices sizes)"
    and "sizes_valid sizes" and "sizes_count sizes < u64_max"
    and "gsz env enc elemTy * sizes_count sizes < u64_max"
    and "length bs = desc_size (enc_ptr_size enc) (length dims)"
    and "desc_dims_ok enc sizes bs"
    and "take (enc_ptr_size enc) bs = encode_ptr enc p"
    and "sizes_count sizes = 0 \<Longrightarrow> empty_data_ok mem (allocatable_dims dims) p"
    and "sizes_count sizes \<noteq> 0 \<Longrightarrow> \<exists>data. data_region_ok mem (allocatable_dims dims) p
                                      (gsz env enc elemTy * sizes_count sizes) data
                              \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                                   rep_val env enc hmap mem elemTy v
                                     (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))"
proof -
  note R = assms(1)[simplified assms(2) if_False rep_val.simps CoreType.case]
  from R have ex: "\<exists>p. take (enc_ptr_size enc) bs = encode_ptr enc p
                   \<and> (if sizes_count sizes = 0 then empty_data_ok mem (allocatable_dims dims) p
                      else (\<exists>data. data_region_ok mem (allocatable_dims dims) p
                                      (gsz env enc elemTy * sizes_count sizes) data
                              \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                                   rep_val env enc hmap mem elemTy v
                                     (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))))"
    by blast
  then obtain p where P: "take (enc_ptr_size enc) bs = encode_ptr enc p"
    and C: "if sizes_count sizes = 0 then empty_data_ok mem (allocatable_dims dims) p
            else (\<exists>data. data_region_ok mem (allocatable_dims dims) p (gsz env enc elemTy * sizes_count sizes) data
                    \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                         rep_val env enc hmap mem elemTy v
                           (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data)))"
    by blast
  show thesis
  proof (rule that[OF _ _ _ _ _ _ _ P])
    show "sizes_match_dims sizes dims" using R by blast
    show "fmdom elems = fset_of_list (all_indices sizes)" using R by blast
    show "sizes_valid sizes" using R by blast
    show "sizes_count sizes < u64_max" using R by blast
    show "gsz env enc elemTy * sizes_count sizes < u64_max" using R by blast
    show "length bs = desc_size (enc_ptr_size enc) (length dims)" using R by blast
    show "desc_dims_ok enc sizes bs" using R by blast
    show "sizes_count sizes = 0 \<Longrightarrow> empty_data_ok mem (allocatable_dims dims) p" using C by simp
    show "sizes_count sizes \<noteq> 0 \<Longrightarrow> \<exists>data. data_region_ok mem (allocatable_dims dims) p
                                      (gsz env enc elemTy * sizes_count sizes) data
                              \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                                   rep_val env enc hmap mem elemTy v
                                     (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))"
      using C by simp
  qed
qed


section \<open>Length\<close>

lemma sizes_match_dims_length: "sizes_match_dims sizes dims \<Longrightarrow> length sizes = length dims"
  by (induction sizes dims rule: sizes_match_dims.induct) auto

lemma rep_val_length:
  assumes "valid_encoding enc" and "rep_val env enc hmap mem ty v bs"
  shows "length bs = gsz env enc ty"
proof (cases v)
  case (CV_Bool b)
  with assms show ?thesis by (simp add: valid_encoding_length int_fits_unsigned)
next
  case (CV_FiniteInt s b i)
  with assms show ?thesis by (simp add: valid_encoding_length)
next
  case (CV_Record fvs)
  with assms(2) show ?thesis by (auto split: CoreType.splits)
next
  case (CV_Variant ctor payload)
  with assms(2) show ?thesis by (auto split: CoreType.splits option.splits)
next
  case (CV_Array sizes elems)
  with assms(2) obtain elemTy dims where ty: "ty = CoreTy_Array elemTy dims"
    and match: "sizes_match_dims sizes dims" by (auto split: CoreType.splits)
  show ?thesis
  proof (cases "dims_all_fixed dims")
    case True
    have "sizes = dims_sizes dims"
      by (rule rep_val_FixedArray_E(1)[OF assms(2)[unfolded ty CV_Array] True])
    with assms(2) CV_Array ty True show ?thesis by simp
  next
    case False
    with assms(2) CV_Array ty show ?thesis
      by (simp add: sizes_match_dims_length[OF match])
  qed
next
  case (CV_Extern n l h)
  with assms(2) show ?thesis by simp
qed (use assms(2) in simp_all)


section \<open>Scalars\<close>

(* The bytes of a scalar are the encoding of its MiniC value. *)
lemma rep_val_scalar:
  assumes "scalar_ty ty = Some cty" and "rep_val env enc hmap mem ty v bs"
  shows "\<exists>mv. scalar_val hmap v = Some mv \<and> val_has_ty mv cty \<and> bs = encode_val enc mv"
proof (cases ty)
  case CoreTy_Bool
  with assms obtain b where v: "v = CV_Bool b" and bs: "bs = encode_val enc (MV_U8 (if b then 1 else 0))"
    by (auto simp: rep_val_Bool_iff)
  have cty: "cty = CTy_U8" using assms(1) CoreTy_Bool by simp
  have "val_has_ty (MV_U8 (if b then 1 else 0)) CTy_U8" by (simp add: int_fits_unsigned)
  thus ?thesis unfolding v bs cty by (intro exI[of _ "MV_U8 (if b then 1 else 0)"]) simp
next
  case (CoreTy_FiniteInt s b)
  with assms obtain i where v: "v = CV_FiniteInt s b i" and fits: "int_fits s b i"
    and bs: "bs = encode_val enc (MV_Int s b i)"
    by (auto simp: rep_val_FiniteInt_iff)
  have cty: "cty = CTy_Int s b" using assms(1) CoreTy_FiniteInt by simp
  show ?thesis using fits unfolding v bs cty by (intro exI[of _ "MV_Int s b i"]) simp
next
  case (CoreTy_Extern n l)
  with assms obtain h where v: "v = CV_Extern n l h" and bs: "bs = encode_ptr enc (hmap h)"
    by (auto simp: rep_val_Extern_iff)
  have cty: "cty = CTy_VoidPtr" using assms(1) CoreTy_Extern by simp
  show ?thesis unfolding v bs cty by (intro exI[of _ "MV_Ptr (hmap h)"]) simp
qed (use assms(1) in simp_all)

(* ... and decode to it. *)
lemma rep_val_scalar_decode:
  assumes "valid_encoding enc" and "scalar_ty ty = Some cty" and "rep_val env enc hmap mem ty v bs"
  obtains mv where "scalar_val hmap v = Some mv" and "val_has_ty mv cty" and "bs = encode_val enc mv"
    and "decode_val enc cty bs = Some mv"
proof -
  from rep_val_scalar[OF assms(2,3)] obtain mv where
    1: "scalar_val hmap v = Some mv" and 2: "val_has_ty mv cty" and 3: "bs = encode_val enc mv" by blast
  have "decode_val enc cty bs = Some mv" unfolding 3 by (rule decode_val_encode_val[OF assms(1) 2])
  from that[OF 1 2 3 this] show thesis .
qed

(* A load from a region holding a scalar's bytes returns its MiniC value. *)
lemma rep_val_scalar_load:
  assumes "valid_encoding enc" and "scalar_ty ty = Some cty"
    and "rep_val env enc hmap mem ty v bs" and "mem_read mem p (gsz env enc ty) = Some bs"
  shows "mem_load enc mem cty p = scalar_val hmap v"
proof -
  from rep_val_scalar_decode[OF assms(1-3)] obtain mv where
    "scalar_val hmap v = Some mv" "decode_val enc cty bs = Some mv" by blast
  with assms(4) scalar_ty_width[OF assms(2), of enc env] show ?thesis
    by (simp add: mem_load_def)
qed

(* The bytes of a scalar's MiniC value represent it. *)
lemma rep_val_scalar_I:
  assumes "scalar_val hmap v = Some mv"
    and "case v of CV_Bool _ \<Rightarrow> ty = CoreTy_Bool
         | CV_FiniteInt s b i \<Rightarrow> ty = CoreTy_FiniteInt s b \<and> int_fits s b i
         | CV_Extern n l _ \<Rightarrow> ty = CoreTy_Extern n l
         | _ \<Rightarrow> False"
  shows "rep_val env enc hmap mem ty v (encode_val enc mv)"
  using assms by (cases v) auto

(* A store of a scalar's MiniC value produces bytes that represent it. *)
lemma rep_val_scalar_store:
  assumes "valid_encoding enc" and "scalar_ty ty = Some cty" and "scalar_val hmap v = Some mv"
    and "rep_val env enc hmap mem0 ty v bs0"   \<comment> \<open>any representation: fixes the type of v\<close>
    and "mem_store enc mem cty p mv = Some mem'"
  shows "mem_read mem' p (gsz env enc ty) = Some (encode_val enc mv)
         \<and> rep_val env enc hmap mem' ty v (encode_val enc mv)"
proof -
  from rep_val_scalar[OF assms(2,4)] assms(3) have hty: "val_has_ty mv cty" by auto
  from assms(5) have w: "mem_write mem p (encode_val enc mv) = Some mem'"
    by (auto simp: mem_store_def split: if_splits)
  from w obtain b off where p: "p = MP_Addr b off" by (cases p) (auto simp: mem_write_def)
  have len: "length (encode_val enc mv) = gsz env enc ty"
    using length_encode_val[OF assms(1) hty] scalar_ty_width[OF assms(2), of enc env] by simp
  have "mem_read mem' p (gsz env enc ty) = Some (encode_val enc mv)"
    using mem_read_mem_write[OF w[unfolded p]] len p by simp
  moreover have "rep_val env enc hmap mem' ty v (encode_val enc mv)"
    using assms(2,3,4) by (cases ty; cases v) auto
  ultimately show ?thesis ..
qed

(* A scalar's representation does not depend on the memory. *)
lemma rep_val_scalar_mem:
  assumes "scalar_ty ty = Some cty"
  shows "rep_val env enc hmap mem' ty v bs = rep_val env enc hmap mem ty v bs"
  using assms by (cases ty; cases v) simp_all


section \<open>Reachable heap blocks and the frame condition\<close>

(* The heap blocks that the representation of v in bs refers to: the block
   a descriptor's data pointer points into (for a descriptor with elements,
   its data block; for an empty one, the block its non-null pointer is
   valid in), and recursively the blocks of the elements. Computed from the
   bytes, since the pointers are in the bytes, not in the Core value. *)
(* The congruence rule that lets the function package see the hypothesis
   fmlookup elems idx = Some v of the union over the elements. *)
lemma UN_fmlookup_cong [fundef_cong]:
  assumes "elems = elems'" and "\<And>idx v. fmlookup elems' idx = Some v \<Longrightarrow> f idx v = g idx v"
  shows "\<Union> {f idx v | idx v. fmlookup elems idx = Some v} = \<Union> {g idx v | idx v. fmlookup elems' idx = Some v}"
  using assms by auto

function reach_blocks :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> CoreValue \<Rightarrow> MByte list \<Rightarrow> nat set" where
  "reach_blocks env enc mem ty (CV_Record fvs) bs =
    (case ty of
       CoreTy_Record ftys \<Rightarrow>
         \<Union> (set (map (\<lambda>((n1, v), (n2, fty)).
               reach_blocks env enc mem fty v
                 (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs))
             (zip fvs ftys)))
     | _ \<Rightarrow> {})"
| "reach_blocks env enc mem ty (CV_Variant ctor payload) bs =
    (case ty of
       CoreTy_Datatype dt args \<Rightarrow>
         (case fmlookup (TE_DataCtors env) ctor of
            Some (dt2, tyvars, payloadTy) \<Rightarrow>
              reach_blocks env enc mem (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) payload
                (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs)
          | None \<Rightarrow> {})
     | _ \<Rightarrow> {})"
| "reach_blocks env enc mem ty (CV_Array sizes elems) bs =
    (case ty of
       CoreTy_Array elemTy dims \<Rightarrow>
         (if dims_all_fixed dims then
            \<Union> {reach_blocks env enc mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) bs)
                | idx v. fmlookup elems idx = Some v}
          else
            (case decode_ptr enc (take (enc_ptr_size enc) bs) of
               Some (MP_Addr blk off) \<Rightarrow>
                 insert blk
                   (if sizes_count sizes = 0 then {}
                    else (case mem_read mem (MP_Addr blk off) (gsz env enc elemTy * sizes_count sizes) of
                            Some data \<Rightarrow>
                              \<Union> {reach_blocks env enc mem elemTy v
                                    (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data)
                                  | idx v. fmlookup elems idx = Some v}
                          | None \<Rightarrow> {}))
             | _ \<Rightarrow> {}))
     | _ \<Rightarrow> {})"
| "reach_blocks env enc mem ty (CV_Bool _) bs = {}"
| "reach_blocks env enc mem ty (CV_FiniteInt _ _ _) bs = {}"
| "reach_blocks env enc mem ty (CV_Int _) bs = {}"
| "reach_blocks env enc mem ty (CV_Real _) bs = {}"
| "reach_blocks env enc mem ty (CV_Extern _ _ _) bs = {}"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(env, enc, mem, ty, v, bs). size v)")
     (auto dest!: set_zip_leftD intro: size_record_field' size_array_lookup')

(* The reachable blocks of the components. *)
lemma reach_blocks_Record_fld:
  assumes "((n1, v), (n2, fty)) \<in> set (zip fvs ftys)"
  shows "reach_blocks env enc mem fty v (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)
         \<subseteq> reach_blocks env enc mem (CoreTy_Record ftys) (CV_Record fvs) bs"
proof -
  let ?f = "\<lambda>((n1, v), (n2, fty)). reach_blocks env enc mem fty v
              (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)"
  have "?f ((n1, v), (n2, fty)) \<in> set (map ?f (zip fvs ftys))"
    using assms unfolding set_map by (rule imageI)
  hence "?f ((n1, v), (n2, fty)) \<subseteq> \<Union> (set (map ?f (zip fvs ftys)))" by (rule Union_upper)
  thus ?thesis unfolding reach_blocks.simps(1) CoreType.case by simp
qed

lemma reach_blocks_Record_fld_nth:
  assumes "i < length fvs" and "i < length ftys" and "fvs ! i = (n1, v)" and "ftys ! i = (n2, fty)"
  shows "reach_blocks env enc mem fty v (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)
         \<subseteq> reach_blocks env enc mem (CoreTy_Record ftys) (CV_Record fvs) bs"
proof (rule reach_blocks_Record_fld)
  have "zip fvs ftys ! i = ((n1, v), (n2, fty))" using assms by (simp add: nth_zip)
  thus "((n1, v), (n2, fty)) \<in> set (zip fvs ftys)" using assms(1,2) by (metis nth_mem length_zip min_less_iff_conj)
qed

lemma reach_blocks_Variant_payload:
  assumes "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
  shows "reach_blocks env enc mem (CoreTy_Datatype dt args) (CV_Variant ctor payload) bs
         = reach_blocks env enc mem (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) payload
             (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs)"
  using assms by simp

lemma reach_blocks_FixedArray_elem:
  assumes "dims_all_fixed dims" and "fmlookup elems idx = Some v"
  shows "reach_blocks env enc mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) bs)
         \<subseteq> reach_blocks env enc mem (CoreTy_Array elemTy dims) (CV_Array sizes elems) bs"
  using assms by auto

lemma reach_blocks_Desc:
  assumes "valid_encoding enc" and "\<not> dims_all_fixed dims"
    and "take (enc_ptr_size enc) bs = encode_ptr enc (MP_Addr blk off)"
  shows "blk \<in> reach_blocks env enc mem (CoreTy_Array elemTy dims) (CV_Array sizes elems) bs"
proof -
  have "decode_ptr enc (take (enc_ptr_size enc) bs) = Some (MP_Addr blk off)"
    unfolding assms(3) by (rule decode_ptr_encode_ptr[OF assms(1)])
  thus ?thesis using assms(2) by simp
qed

lemma reach_blocks_Desc_elem:
  assumes "valid_encoding enc" and "\<not> dims_all_fixed dims" and "sizes_count sizes \<noteq> 0"
    and "take (enc_ptr_size enc) bs = encode_ptr enc (MP_Addr blk off)"
    and "mem_read mem (MP_Addr blk off) (gsz env enc elemTy * sizes_count sizes) = Some data"
    and "fmlookup elems idx = Some v"
  shows "reach_blocks env enc mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data)
         \<subseteq> reach_blocks env enc mem (CoreTy_Array elemTy dims) (CV_Array sizes elems) bs"
proof -
  have "decode_ptr enc (take (enc_ptr_size enc) bs) = Some (MP_Addr blk off)"
    unfolding assms(4) by (rule decode_ptr_encode_ptr[OF assms(1)])
  thus ?thesis using assms(2,3,5,6) by auto
qed

(* Two memories agree on a set of blocks. *)
definition blocks_agree :: "MMem \<Rightarrow> MMem \<Rightarrow> nat set \<Rightarrow> bool" where
  "blocks_agree mem mem' S = (\<forall>b \<in> S. fmlookup (MM_Blocks mem') b = fmlookup (MM_Blocks mem) b)"

lemma blocks_agree_subset: "blocks_agree mem mem' S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> blocks_agree mem mem' T"
  by (auto simp: blocks_agree_def)

lemma blocks_agree_read:
  "blocks_agree mem mem' S \<Longrightarrow> blk \<in> S \<Longrightarrow> mem_read mem' (MP_Addr blk off) n = mem_read mem (MP_Addr blk off) n"
  by (simp add: blocks_agree_def mem_read_def)

lemma blocks_agree_range_ok:
  "blocks_agree mem mem' S \<Longrightarrow> blk \<in> S \<Longrightarrow> ptr_range_ok mem' (MP_Addr blk off) n = ptr_range_ok mem (MP_Addr blk off) n"
  by (simp add: blocks_agree_def ptr_range_ok_def)

(* reach_blocks itself only depends on the memory through the reachable blocks. *)
lemma reach_blocks_agree:
  assumes "blocks_agree mem mem' (reach_blocks env enc mem ty v bs)"
  shows "reach_blocks env enc mem' ty v bs = reach_blocks env enc mem ty v bs"
  using assms
proof (induction v arbitrary: ty bs)
  case (CV_Record fvs)
  show ?case
  proof (cases ty)
    case (CoreTy_Record ftys)
    let ?f = "\<lambda>m. \<lambda>((n1, v), (n2, fty)). reach_blocks env enc m fty v
                 (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)"
    have "\<And>x. x \<in> set (zip fvs ftys) \<Longrightarrow> ?f mem' x = ?f mem x"
    proof -
      fix x assume x: "x \<in> set (zip fvs ftys)"
      obtain n1 v n2 fty where xe: "x = ((n1, v), (n2, fty))" by (cases x) auto
      have in_fvs: "(n1, v) \<in> set fvs" using x xe by (auto dest: set_zip_leftD)
      have sub: "reach_blocks env enc mem fty v (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)
                 \<subseteq> reach_blocks env enc mem ty (CV_Record fvs) bs"
        unfolding CoreTy_Record using x xe by (intro reach_blocks_Record_fld) simp
      show "?f mem' x = ?f mem x"
        unfolding xe using CV_Record.IH[OF in_fvs snds_pair blocks_agree_subset[OF CV_Record.prems sub]] by simp
    qed
    hence eq: "map (?f mem') (zip fvs ftys) = map (?f mem) (zip fvs ftys)" by (rule map_cong[OF refl])
    show ?thesis unfolding CoreTy_Record reach_blocks.simps(1) CoreType.case eq ..
  qed simp_all
next
  case (CV_Variant ctor payload)
  show ?case
  proof (cases ty)
    case (CoreTy_Datatype dt args)
    show ?thesis
    proof (cases "fmlookup (TE_DataCtors env) ctor")
      case None
      then show ?thesis unfolding CoreTy_Datatype by simp
    next
      case (Some x)
      then obtain dt2 tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) ctor = Some (dt2, tyvars, payloadTy)"
        by (cases x) auto
      show ?thesis unfolding CoreTy_Datatype
        using CV_Variant.IH[of "apply_subst (fmap_of_list (zip tyvars args)) payloadTy"]
              CV_Variant.prems unfolding CoreTy_Datatype by (simp add: lk)
    qed
  qed simp_all
next
  case (CV_Array sizes elems)
  show ?case
  proof (cases ty)
    case (CoreTy_Array elemTy dims)
    show ?thesis
    proof (cases "dims_all_fixed dims")
      case True
      have "\<And>idx v. fmlookup elems idx = Some v \<Longrightarrow>
              reach_blocks env enc mem' elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) bs)
              = reach_blocks env enc mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) bs)"
      proof -
        fix idx v assume lk: "fmlookup elems idx = Some v"
        have sub: "reach_blocks env enc mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) bs)
                   \<subseteq> reach_blocks env enc mem ty (CV_Array sizes elems) bs"
          unfolding CoreTy_Array using True lk by auto
        show "?thesis idx v"
          using CV_Array.IH[of v elemTy] lk blocks_agree_subset[OF CV_Array.prems sub]
          by (simp add: fmran'I)
      qed
      thus ?thesis unfolding CoreTy_Array using True by simp (blast)
    next
      case False
      show ?thesis
      proof (cases "decode_ptr enc (take (enc_ptr_size enc) bs)")
        case None
        then show ?thesis unfolding CoreTy_Array using False by simp
      next
        case (Some p)
        show ?thesis
        proof (cases p)
          case MP_Null
          then show ?thesis unfolding CoreTy_Array using False Some by simp
        next
          case (MP_Addr blk off)
          have blk_in: "blk \<in> reach_blocks env enc mem ty (CV_Array sizes elems) bs"
            unfolding CoreTy_Array using False Some MP_Addr by simp
          have rd: "mem_read mem' (MP_Addr blk off) n = mem_read mem (MP_Addr blk off) n" for n
            by (rule blocks_agree_read[OF CV_Array.prems blk_in])
          show ?thesis
          proof (cases "sizes_count sizes = 0")
            case True
            then show ?thesis unfolding CoreTy_Array using False Some MP_Addr by simp
          next
            case cnt: False
            show ?thesis
            proof (cases "mem_read mem (MP_Addr blk off) (gsz env enc elemTy * sizes_count sizes)")
              case None
              then show ?thesis unfolding CoreTy_Array using False Some MP_Addr cnt rd by simp
            next
              case (Some data)
              have "\<And>idx v. fmlookup elems idx = Some v \<Longrightarrow>
                      reach_blocks env enc mem' elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data)
                      = reach_blocks env enc mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data)"
              proof -
                fix idx v assume lk: "fmlookup elems idx = Some v"
                have sub: "reach_blocks env enc mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data)
                           \<subseteq> reach_blocks env enc mem ty (CV_Array sizes elems) bs"
                  unfolding CoreTy_Array using False \<open>decode_ptr enc (take (enc_ptr_size enc) bs) = Some p\<close> MP_Addr cnt Some lk
                  by auto
                show "?thesis idx v"
                  using CV_Array.IH[of v elemTy] lk blocks_agree_subset[OF CV_Array.prems sub]
                  by (simp add: fmran'I)
              qed
              thus ?thesis unfolding CoreTy_Array
                using False \<open>decode_ptr enc (take (enc_ptr_size enc) bs) = Some p\<close> MP_Addr cnt Some rd
                by simp blast
            qed
          qed
        qed
      qed
    qed
  qed simp_all
qed simp_all

(* The frame lemma: the representation depends on the memory only through
   the reachable blocks. *)
lemma rep_val_frame:
  assumes "valid_encoding enc"
  shows "rep_val env enc hmap mem ty v bs \<Longrightarrow> blocks_agree mem mem' (reach_blocks env enc mem ty v bs)
         \<Longrightarrow> rep_val env enc hmap mem' ty v bs"
proof (induction v arbitrary: ty bs)
  case (CV_Record fvs)
  from rep_val_Record_E[OF CV_Record.prems(1)] obtain ftys where
    ty: "ty = CoreTy_Record ftys" and dist: "distinct (map fst ftys)"
    and len: "length bs = gsz env enc (CoreTy_Record ftys)"
    and flds: "list_all2 (\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
           rep_val env enc hmap mem fty v
             (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)) fvs ftys"
    by blast
  have lens: "length fvs = length ftys" using flds by (rule list_all2_lengthD)
  let ?P = "\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
           rep_val env enc hmap mem' fty v
             (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)"
  have "list_all2 ?P fvs ftys"
  proof (rule list_all2_all_nthI[OF lens])
    fix i assume i: "i < length fvs"
    obtain n1 v where fvi: "fvs ! i = (n1, v)" by (cases "fvs ! i")
    obtain n2 fty where ftyi: "ftys ! i = (n2, fty)" by (cases "ftys ! i")
    from list_all2_nthD[OF flds i] fvi ftyi have eq: "n1 = n2"
      and r: "rep_val env enc hmap mem fty v (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)"
      by auto
    have in_fvs: "(n1, v) \<in> set fvs" using i fvi by (metis nth_mem)
    have sub: "reach_blocks env enc mem fty v (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)
               \<subseteq> reach_blocks env enc mem ty (CV_Record fvs) bs"
      unfolding ty by (rule reach_blocks_Record_fld_nth[OF i _ fvi ftyi]) (use i lens in simp)
    have "rep_val env enc hmap mem' fty v (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)"
      by (rule CV_Record.IH[OF in_fvs snds_pair r blocks_agree_subset[OF CV_Record.prems(2) sub]])
    with eq show "?P (fvs ! i) (ftys ! i)" unfolding fvi ftyi by simp
  qed
  with dist len ty show ?case by simp
next
  case (CV_Variant ctor payload)
  from rep_val_Variant_E[OF CV_Variant.prems(1)] obtain dt args tyvars payloadTy where
    ty: "ty = CoreTy_Datatype dt args"
    and lk: "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
    and rest: "length tyvars = length args" "ctor \<in> set (dt_ctors env dt)"
      "length bs = gsz env enc (CoreTy_Datatype dt args)"
      "take (tag_size env dt) bs = encode_val enc (MV_Int Unsigned (tag_bits env dt) (int (ctor_tag env dt ctor)))"
    and r: "rep_val env enc hmap mem (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) payload
           (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs)"
    by blast
  have agree: "blocks_agree mem mem' (reach_blocks env enc mem (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) payload
           (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs))"
    using CV_Variant.prems(2) unfolding ty reach_blocks_Variant_payload[OF lk] .
  from CV_Variant.IH[OF r agree] rest lk show ?case unfolding ty by simp
next
  case (CV_Array sizes elems)
  from rep_val_Array_E[OF CV_Array.prems(1)] obtain elemTy dims where
    ty: "ty = CoreTy_Array elemTy dims" by blast
  let ?esz = "gsz env enc elemTy"
  show ?case
  proof (cases "dims_all_fixed dims")
    case True
    note E = rep_val_FixedArray_E[OF CV_Array.prems(1)[unfolded ty] True]
    have "\<And>idx v. fmlookup elems idx = Some v \<Longrightarrow>
            rep_val env enc hmap mem' elemTy v (slice (elem_offset ?esz sizes idx) ?esz bs)"
    proof -
      fix idx v assume lk: "fmlookup elems idx = Some v"
      have sub: "reach_blocks env enc mem elemTy v (slice (elem_offset ?esz sizes idx) ?esz bs)
                 \<subseteq> reach_blocks env enc mem ty (CV_Array sizes elems) bs"
        unfolding ty by (rule reach_blocks_FixedArray_elem[OF True lk])
      show "rep_val env enc hmap mem' elemTy v (slice (elem_offset ?esz sizes idx) ?esz bs)"
        by (rule CV_Array.IH[OF fmran'I[OF lk] E(4)[OF lk] blocks_agree_subset[OF CV_Array.prems(2) sub]])
    qed
    with CV_Array.prems(1) True show ?thesis unfolding ty by simp
  next
    case False
    from rep_val_Desc_E[OF CV_Array.prems(1)[unfolded ty] False] obtain p where
      D: "sizes_match_dims sizes dims" "fmdom elems = fset_of_list (all_indices sizes)"
         "sizes_valid sizes" "sizes_count sizes < u64_max" "?esz * sizes_count sizes < u64_max"
         "length bs = desc_size (enc_ptr_size enc) (length dims)" "desc_dims_ok enc sizes bs"
         "take (enc_ptr_size enc) bs = encode_ptr enc p"
      and empty: "sizes_count sizes = 0 \<Longrightarrow> empty_data_ok mem (allocatable_dims dims) p"
      and nonempty: "sizes_count sizes \<noteq> 0 \<Longrightarrow> \<exists>data. data_region_ok mem (allocatable_dims dims) p (?esz * sizes_count sizes) data
                       \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                            rep_val env enc hmap mem elemTy v (slice (elem_offset ?esz sizes idx) ?esz data))"
      by blast
    show ?thesis
    proof (cases p)
      case MP_Null
      \<comment> \<open>A null pointer: no elements (data_region_ok needs a readable range), no memory dependence.\<close>
      have "sizes_count sizes = 0"
      proof (rule ccontr)
        assume "sizes_count sizes \<noteq> 0"
        from nonempty[OF this] obtain data where "mem_read mem p (?esz * sizes_count sizes) = Some data"
          by (auto simp: data_region_ok_def)
        thus False using MP_Null by (simp add: mem_read_def)
      qed
      with D MP_Null show ?thesis unfolding ty using False
        by (simp add: empty_data_ok_def) (rule exI[where x = MP_Null], simp)
    next
      case (MP_Addr blk off)
      have blk_in: "blk \<in> reach_blocks env enc mem ty (CV_Array sizes elems) bs"
        unfolding ty by (rule reach_blocks_Desc[OF assms False D(8)[unfolded MP_Addr]])
      note agree_blk = CV_Array.prems(2)[unfolded blocks_agree_def, rule_format, OF blk_in]
      show ?thesis
      proof (cases "sizes_count sizes = 0")
        case True
        from empty[OF True] have "empty_data_ok mem' (allocatable_dims dims) p"
          unfolding empty_data_ok_def MP_Addr using agree_blk by (simp add: ptr_range_ok_def)
        with D True show ?thesis unfolding ty using False by (auto simp: empty_data_ok_def)
      next
        case cnt: False
        from nonempty[OF cnt] obtain data where
          reg: "data_region_ok mem (allocatable_dims dims) p (?esz * sizes_count sizes) data"
          and elems_r: "\<And>idx v. fmlookup elems idx = Some v \<Longrightarrow>
                          rep_val env enc hmap mem elemTy v (slice (elem_offset ?esz sizes idx) ?esz data)"
          by blast
        have rd: "mem_read mem (MP_Addr blk off) (?esz * sizes_count sizes) = Some data"
          using reg unfolding data_region_ok_def MP_Addr by simp
        have reg': "data_region_ok mem' (allocatable_dims dims) p (?esz * sizes_count sizes) data"
          using reg agree_blk unfolding data_region_ok_def MP_Addr by (simp add: mem_read_def)
        have "\<And>idx v. fmlookup elems idx = Some v \<Longrightarrow>
                rep_val env enc hmap mem' elemTy v (slice (elem_offset ?esz sizes idx) ?esz data)"
        proof -
          fix idx v assume lk: "fmlookup elems idx = Some v"
          have sub: "reach_blocks env enc mem elemTy v (slice (elem_offset ?esz sizes idx) ?esz data)
                     \<subseteq> reach_blocks env enc mem ty (CV_Array sizes elems) bs"
            unfolding ty by (rule reach_blocks_Desc_elem[OF assms False cnt D(8)[unfolded MP_Addr] rd lk])
          show "rep_val env enc hmap mem' elemTy v (slice (elem_offset ?esz sizes idx) ?esz data)"
            by (rule CV_Array.IH[OF fmran'I[OF lk] elems_r[OF lk] blocks_agree_subset[OF CV_Array.prems(2) sub]])
        qed
        with D cnt reg' show ?thesis unfolding ty using False by auto
      qed
    qed
  qed
qed simp_all

(* A memory with the same blocks (e.g. after a write to an unreachable
   block) represents the same values. *)
lemma rep_val_frame_write:
  assumes "valid_encoding enc"
    and "rep_val env enc hmap mem ty v bs"
    and "mem_write mem (MP_Addr b off) new = Some mem'"
    and "b \<notin> reach_blocks env enc mem ty v bs"
  shows "rep_val env enc hmap mem' ty v bs"
proof (rule rep_val_frame[OF assms(1,2)])
  show "blocks_agree mem mem' (reach_blocks env enc mem ty v bs)"
    unfolding blocks_agree_def
  proof
    fix b' assume "b' \<in> reach_blocks env enc mem ty v bs"
    with assms(4) have "b' \<noteq> b" by auto
    thus "fmlookup (MM_Blocks mem') b' = fmlookup (MM_Blocks mem) b'" by (rule mem_write_lookup_other[OF assms(3)])
  qed
qed


section \<open>Junk bytes\<close>

(* The bytes after a variant's payload may be anything (MB_Undef included). *)
lemma rep_val_variant_junk:
  assumes "rep_val env enc hmap mem (CoreTy_Datatype dt args) (CV_Variant ctor payload) bs"
    and "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
    and "length bs' = length bs"
    and "take (tag_size env dt + gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs'
         = take (tag_size env dt + gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs"
  shows "rep_val env enc hmap mem (CoreTy_Datatype dt args) (CV_Variant ctor payload) bs'"
proof -
  let ?psz = "gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)"
  let ?t = "tag_size env dt"
  have tag: "take ?t bs' = take ?t bs"
  proof -
    have "take ?t bs' = take ?t (take (?t + ?psz) bs')" by (simp add: take_take)
    also have "\<dots> = take ?t (take (?t + ?psz) bs)" unfolding assms(4) ..
    also have "\<dots> = take ?t bs" by (simp add: take_take)
    finally show ?thesis .
  qed
  have payload: "slice ?t ?psz bs' = slice ?t ?psz bs"
  proof -
    have "slice ?t ?psz bs' = drop ?t (take (?t + ?psz) bs')" by (simp add: slice_def drop_take)
    also have "\<dots> = drop ?t (take (?t + ?psz) bs)" unfolding assms(4) ..
    also have "\<dots> = slice ?t ?psz bs" by (simp add: slice_def drop_take)
    finally show ?thesis .
  qed
  from assms(1,2) show ?thesis
    using assms(3) tag payload by (auto split: option.splits)
qed

end

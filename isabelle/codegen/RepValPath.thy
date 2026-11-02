theory RepValPath
  imports RepVal
begin

(* ========================================================================== *)
(* Paths: where the bytes of a sub-value are (minic/DESIGN.md, section 4)     *)
(* ========================================================================== *)

(* An lvalue path (LValuePath list, InterpState.thy) selects a sub-value of a
   Core value. This theory locates the bytes of that sub-value relative to
   the bytes of the whole value: at an offset within the same bytes for
   record, variant and fixed-array projections (and same-category array
   casts), or at a pointer into a heap block once the path has gone through
   an array descriptor. The projection lemma says that the bytes at the
   location represent the sub-value that get_value_at_path returns; the
   update lemmas say that replacing those bytes (a splice of the byte list,
   or a write to the heap block) represents the value that
   update_value_at_path returns. *)


section \<open>One step of a path, on the Core side\<close>

(* The sub-value one step down, and the value with that sub-value replaced;
   get_value_at_path / update_value_at_path step by step. *)
fun step_get :: "CoreValue \<Rightarrow> LValuePath \<Rightarrow> CoreValue option" where
  "step_get (CV_Record flds) (LVPath_RecordProj f) = map_of flds f"
| "step_get (CV_Variant ctor payload) (LVPath_VariantProj c) = (if ctor = c then Some payload else None)"
| "step_get (CV_Array sizes elems) (LVPath_ArrayProj idx) = fmlookup elems idx"
| "step_get (CV_Array sizes elems) (LVPath_ArrayCast dims) =
    (if sizes_match_dims sizes dims then Some (CV_Array sizes elems) else None)"
| "step_get _ _ = None"

fun step_put :: "CoreValue \<Rightarrow> LValuePath \<Rightarrow> CoreValue \<Rightarrow> CoreValue option" where
  "step_put (CV_Record flds) (LVPath_RecordProj f) w =
    (if map_of flds f = None then None else Some (CV_Record (AList.update f w flds)))"
| "step_put (CV_Variant ctor payload) (LVPath_VariantProj c) w = (if ctor = c then Some (CV_Variant ctor w) else None)"
| "step_put (CV_Array sizes elems) (LVPath_ArrayProj idx) w =
    (if fmlookup elems idx = None then None else Some (CV_Array sizes (fmupd idx w elems)))"
| "step_put (CV_Array sizes elems) (LVPath_ArrayCast dims) w =
    (if sizes_match_dims sizes dims then
       (case w of CV_Array sizes' elems' \<Rightarrow> if sizes' = sizes then Some w else None | _ \<Rightarrow> None)
     else None)"
| "step_put _ _ _ = None"

lemma get_value_at_path_Cons:
  "get_value_at_path v (s # rest) = Inr v' \<longleftrightarrow> (\<exists>v1. step_get v s = Some v1 \<and> get_value_at_path v1 rest = Inr v')"
  by (cases v; cases s) (auto split: option.splits if_splits)

lemma update_value_at_path_Cons:
  "update_value_at_path v (s # rest) v' = Inr w \<longleftrightarrow>
   (\<exists>v1 w1. step_get v s = Some v1 \<and> update_value_at_path v1 rest v' = Inr w1 \<and> step_put v s w1 = Some w)"
  by (cases v; cases s) (auto split: option.splits if_splits sum.splits CoreValue.splits)


section \<open>Locations\<close>

(* Where the bytes of a sub-value are: at an offset within the bytes of the
   enclosing value, or at a pointer into memory (after a descriptor step). *)
datatype PathLoc = PL_Here nat | PL_Mem MPtr

(* The location of a sub-sub-value: l1 is the location of the sub-value
   relative to the whole, l2 the location of the sub-sub-value relative to
   the sub-value. *)
fun loc_compose :: "PathLoc \<Rightarrow> PathLoc \<Rightarrow> PathLoc" where
  "loc_compose (PL_Here o1) (PL_Here o2) = PL_Here (o1 + o2)"
| "loc_compose (PL_Mem p) (PL_Here o2) = PL_Mem (ptr_off p o2)"
| "loc_compose _ (PL_Mem q) = PL_Mem q"

lemma loc_compose_Here_0 [simp]: "loc_compose (PL_Here 0) l = l"
  by (cases l) simp_all

lemma loc_compose_Here_0_right [simp]: "loc_compose l (PL_Here 0) = l"
  by (cases l) simp_all

(* The absolute pointer of a location, when the whole value is in memory at p. *)
fun loc_ptr :: "MPtr \<Rightarrow> PathLoc \<Rightarrow> MPtr" where
  "loc_ptr p (PL_Here off) = ptr_off p off"
| "loc_ptr p (PL_Mem q) = q"

lemma loc_ptr_compose: "loc_ptr p (loc_compose l1 l2) = loc_ptr (loc_ptr p l1) l2"
  by (cases l1; cases l2) (simp_all add: ptr_off_add)


section \<open>Decoding a descriptor\<close>

(* The dimension k of a descriptor, decoded from its bytes. *)
definition desc_dim :: "MEncoding \<Rightarrow> MByte list \<Rightarrow> nat \<Rightarrow> int option" where
  "desc_dim enc bs k =
    (case decode_val enc CTy_U64 (slice (desc_dim_offset (enc_ptr_size enc) k) 8 bs) of
       Some (MV_Int Unsigned IntBits_64 n) \<Rightarrow> Some n
     | _ \<Rightarrow> None)"

(* The sizes of a descriptor of d dimensions. *)
definition desc_sizes :: "MEncoding \<Rightarrow> nat \<Rightarrow> MByte list \<Rightarrow> int list option" where
  "desc_sizes enc d bs = those (map (desc_dim enc bs) [0..<d])"

(* The data pointer. *)
definition desc_ptr :: "MEncoding \<Rightarrow> MByte list \<Rightarrow> MPtr option" where
  "desc_ptr enc bs = decode_ptr enc (take (enc_ptr_size enc) bs)"

lemma those_map_Some: "those (map (\<lambda>k. Some (f k)) ks) = Some (map f ks)"
  by (induction ks) simp_all

lemma desc_sizes_of_dims_ok:
  assumes "valid_encoding enc" and "sizes_valid sizes" and "desc_dims_ok enc sizes bs"
  shows "desc_sizes enc (length sizes) bs = Some sizes"
proof -
  have "\<And>k. k < length sizes \<Longrightarrow> desc_dim enc bs k = Some (sizes ! k)"
  proof -
    fix k assume k: "k < length sizes"
    have fits: "val_has_ty (MV_U64 (sizes ! k)) CTy_U64"
      using assms(2) k unfolding sizes_valid_def list_all_length by simp
    have "slice (desc_dim_offset (enc_ptr_size enc) k) 8 bs = encode_val enc (MV_U64 (sizes ! k))"
      using assms(3) k unfolding desc_dims_ok_def by blast
    thus "desc_dim enc bs k = Some (sizes ! k)"
      unfolding desc_dim_def using decode_val_encode_val[OF assms(1) fits] by simp
  qed
  hence eq: "map (desc_dim enc bs) [0..<length sizes] = map (\<lambda>k. Some (sizes ! k)) [0..<length sizes]"
    by (intro map_cong) auto
  show ?thesis unfolding desc_sizes_def eq those_map_Some by (simp add: map_nth)
qed

lemma desc_ptr_of_take:
  assumes "valid_encoding enc" and "take (enc_ptr_size enc) bs = encode_ptr enc p"
  shows "desc_ptr enc bs = Some p"
  unfolding desc_ptr_def assms(2) by (rule decode_ptr_encode_ptr[OF assms(1)])


section \<open>The location of a path\<close>

(* One step: the type of the sub-value, its bytes, and its location relative
   to the bytes bs of the enclosing value of type ty. An array cast keeps
   the location when it does not change the category (fixed vs descriptor)
   and does not add ownership (the weakening T[*] to T[] is fine, the
   reverse is not a valid Core cast). The cast's dims must be well-kinded,
   as type_at_path requires. *)
fun path_step :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> MByte list \<Rightarrow> LValuePath
                  \<Rightarrow> (CoreType \<times> MByte list \<times> PathLoc) option" where
  "path_step env enc mem (CoreTy_Record ftys) bs (LVPath_RecordProj f) =
    (case map_of ftys f of
       Some fty \<Rightarrow> Some (fty, slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f) (gsz env enc fty) bs,
                         PL_Here (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f))
     | None \<Rightarrow> None)"
| "path_step env enc mem (CoreTy_Datatype dt args) bs (LVPath_VariantProj c) =
    (case fmlookup (TE_DataCtors env) c of
       Some (dt2, tyvars, payloadTy) \<Rightarrow>
         if dt = dt2 then
           Some (apply_subst (fmap_of_list (zip tyvars args)) payloadTy,
                 slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs,
                 PL_Here (tag_size env dt))
         else None
     | None \<Rightarrow> None)"
| "path_step env enc mem (CoreTy_Array elemTy dims) bs (LVPath_ArrayProj idx) =
    (if dims_all_fixed dims then
       (if index_in_bounds (dims_sizes dims) idx then
          Some (elemTy, slice (elem_offset (gsz env enc elemTy) (dims_sizes dims) idx) (gsz env enc elemTy) bs,
                PL_Here (elem_offset (gsz env enc elemTy) (dims_sizes dims) idx))
        else None)
     else
       (case desc_ptr enc bs of
          Some p \<Rightarrow>
            (case desc_sizes enc (length dims) bs of
               Some sizes \<Rightarrow>
                 if index_in_bounds sizes idx then
                   (case mem_read mem (ptr_off p (elem_offset (gsz env enc elemTy) sizes idx)) (gsz env enc elemTy) of
                      Some bs1 \<Rightarrow> Some (elemTy, bs1, PL_Mem (ptr_off p (elem_offset (gsz env enc elemTy) sizes idx)))
                    | None \<Rightarrow> None)
                 else None
             | None \<Rightarrow> None)
        | None \<Rightarrow> None))"
| "path_step env enc mem (CoreTy_Array elemTy dims) bs (LVPath_ArrayCast dims') =
    (if dims_all_fixed dims' = dims_all_fixed dims \<and> (allocatable_dims dims' \<longrightarrow> allocatable_dims dims)
        \<and> array_dims_well_kinded dims'
     then Some (CoreTy_Array elemTy dims', bs, PL_Here 0) else None)"
| "path_step _ _ _ _ _ _ = None"

fun path_loc :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> MByte list \<Rightarrow> LValuePath list
                 \<Rightarrow> (CoreType \<times> MByte list \<times> PathLoc) option" where
  "path_loc env enc mem ty bs [] = Some (ty, bs, PL_Here 0)"
| "path_loc env enc mem ty bs (s # rest) =
    (case path_step env enc mem ty bs s of
       Some (ty1, bs1, l1) \<Rightarrow>
         (case path_loc env enc mem ty1 bs1 rest of
            Some (ty', bs', l') \<Rightarrow> Some (ty', bs', loc_compose l1 l')
          | None \<Rightarrow> None)
     | None \<Rightarrow> None)"

lemma path_loc_Cons:
  "path_loc env enc mem ty bs (s # rest) = Some (ty', bs', l) \<longleftrightarrow>
   (\<exists>ty1 bs1 l1 l'. path_step env enc mem ty bs s = Some (ty1, bs1, l1)
      \<and> path_loc env enc mem ty1 bs1 rest = Some (ty', bs', l') \<and> l = loc_compose l1 l')"
  by (auto split: option.splits prod.splits)

lemma path_loc_ConsD:
  "path_loc env enc mem ty bs (s # rest) = Some (ty', bs', l) \<Longrightarrow>
   \<exists>ty1 bs1 l1 l'. path_step env enc mem ty bs s = Some (ty1, bs1, l1)
      \<and> path_loc env enc mem ty1 bs1 rest = Some (ty', bs', l') \<and> l = loc_compose l1 l'"
  by (simp only: path_loc_Cons)

(* A slice of the right length is inside the list (for a zero length, the
   offset must be known to be inside). *)
lemma slice_len_inside: "length (slice off n xs) = n \<Longrightarrow> off \<le> length xs \<Longrightarrow> off + n \<le> length xs"
  by (auto simp: min_def split: if_splits)

(* The type at the path is the one type_at_path computes. *)
lemma path_step_type:
  assumes "path_step env enc mem ty bs s = Some (ty1, bs1, l1)"
  shows "type_at_path env ty (s # rest) = type_at_path env ty1 rest"
  using assms by (cases ty; cases s) (auto split: option.splits if_splits)

lemma path_loc_type:
  assumes "path_loc env enc mem ty bs path = Some (ty', bs', l)"
  shows "type_at_path env ty path = Some ty'"
  using assms
proof (induction path arbitrary: ty bs l)
  case Nil
  then show ?case by simp
next
  case (Cons s rest)
  from path_loc_ConsD[OF Cons.prems] obtain ty1 bs1 l1 l' where
    st: "path_step env enc mem ty bs s = Some (ty1, bs1, l1)"
    and pl: "path_loc env enc mem ty1 bs1 rest = Some (ty', bs', l')"
    by blast
  show ?case unfolding path_step_type[OF st] by (rule Cons.IH[OF pl])
qed


section \<open>Retyping an array\<close>

(* A fixed array's rep_val does not depend on the dims beyond their sizes; a
   descriptor's does not depend on them beyond their number and whether the
   data is owned. *)
lemma sizes_match_dims_fixed:
  "sizes_match_dims sizes dims \<Longrightarrow> dims_all_fixed dims \<Longrightarrow> sizes = dims_sizes dims"
proof (induction sizes dims rule: sizes_match_dims.induct)
  case (2 s ss n ds)
  then show ?case by (simp add: dims_all_fixed_def dims_sizes_def)
qed (auto simp: dims_all_fixed_def dims_sizes_def)

(* Weakening: the same bytes at a type with the same category, the same
   number of dimensions, and no more ownership. *)
lemma rep_val_Array_weaken:
  assumes "rep_val env enc hmap mem (CoreTy_Array elemTy dims) (CV_Array sizes elems) bs"
    and "sizes_match_dims sizes dims'"
    and "dims_all_fixed dims' = dims_all_fixed dims"
    and "allocatable_dims dims' \<longrightarrow> allocatable_dims dims"
  shows "rep_val env enc hmap mem (CoreTy_Array elemTy dims') (CV_Array sizes elems) bs"
proof (cases "dims_all_fixed dims")
  case True
  with assms show ?thesis by simp
next
  case False
  have len: "length dims' = length dims"
    using sizes_match_dims_length[OF assms(2)] sizes_match_dims_length[of sizes dims] assms(1) by simp
  have weak: "\<And>p n data. data_region_ok mem (allocatable_dims dims) p n data \<Longrightarrow> data_region_ok mem (allocatable_dims dims') p n data"
    "\<And>p. empty_data_ok mem (allocatable_dims dims) p \<Longrightarrow> empty_data_ok mem (allocatable_dims dims') p"
    using assms(4) by (auto simp: data_region_ok_def empty_data_ok_def)
  have nf': "\<not> dims_all_fixed dims'" using assms(3) False by simp
  from rep_val_Desc_E[OF assms(1) False] obtain p where
    D: "sizes_match_dims sizes dims" "fmdom elems = fset_of_list (all_indices sizes)"
       "sizes_valid sizes" "sizes_count sizes < u64_max" "gsz env enc elemTy * sizes_count sizes < u64_max"
       "length bs = desc_size (enc_ptr_size enc) (length dims)" "desc_dims_ok enc sizes bs"
       "take (enc_ptr_size enc) bs = encode_ptr enc p"
    and empty: "sizes_count sizes = 0 \<Longrightarrow> empty_data_ok mem (allocatable_dims dims) p"
    and nonempty: "sizes_count sizes \<noteq> 0 \<Longrightarrow> \<exists>data. data_region_ok mem (allocatable_dims dims) p
                       (gsz env enc elemTy * sizes_count sizes) data
                       \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                            rep_val env enc hmap mem elemTy v
                              (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))"
    by blast
  show ?thesis
  proof (cases "sizes_count sizes = 0")
    case z: True
    from weak(2)[OF empty[OF z]] D z assms(2) nf' len show ?thesis
      unfolding rep_val.simps CoreType.case by simp blast
  next
    case nz: False
    from nonempty[OF nz] obtain data where
      "data_region_ok mem (allocatable_dims dims) p (gsz env enc elemTy * sizes_count sizes) data"
      and el: "\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                 rep_val env enc hmap mem elemTy v
                   (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data)"
      by blast
    from weak(1)[OF this(1)] D nz assms(2) nf' len el show ?thesis
      unfolding rep_val.simps CoreType.case by simp blast
  qed
qed

(* The owning direction needs the data block to be exactly the data. *)
lemma rep_val_Array_strengthen:
  assumes "rep_val env enc hmap mem (CoreTy_Array elemTy dims') (CV_Array sizes elems) bs"
    and "sizes_match_dims sizes dims"
    and "dims_all_fixed dims' = dims_all_fixed dims"
    and "\<not> dims_all_fixed dims"
    and "allocatable_dims dims \<Longrightarrow> \<not> allocatable_dims dims' \<Longrightarrow>
         (\<forall>p. take (enc_ptr_size enc) bs = encode_ptr enc p \<longrightarrow>
            (if sizes_count sizes = 0 then p = MP_Null \<or> (\<exists>blk. p = MP_Addr blk 0)
             else (\<exists>blk data. p = MP_Addr blk 0 \<and> fmlookup (MM_Blocks mem) blk = Some data
                     \<and> length data = gsz env enc elemTy * sizes_count sizes)))"
  shows "rep_val env enc hmap mem (CoreTy_Array elemTy dims) (CV_Array sizes elems) bs"
proof (cases "allocatable_dims dims \<and> \<not> allocatable_dims dims'")
  case False
  hence "allocatable_dims dims \<longrightarrow> allocatable_dims dims'" by blast
  from rep_val_Array_weaken[OF assms(1,2) assms(3)[symmetric] this] show ?thesis .
next
  case True
  note own = assms(5)[OF conjunct1[OF True] conjunct2[OF True]]
  have len: "length dims' = length dims"
    using sizes_match_dims_length[OF assms(2)] sizes_match_dims_length[of sizes dims'] assms(1) by simp
  have nf': "\<not> dims_all_fixed dims'" using assms(3,4) by simp
  from rep_val_Desc_E[OF assms(1) nf'] obtain p where
    D: "sizes_match_dims sizes dims'" "fmdom elems = fset_of_list (all_indices sizes)"
       "sizes_valid sizes" "sizes_count sizes < u64_max" "gsz env enc elemTy * sizes_count sizes < u64_max"
       "length bs = desc_size (enc_ptr_size enc) (length dims')" "desc_dims_ok enc sizes bs"
       "take (enc_ptr_size enc) bs = encode_ptr enc p"
    and empty: "sizes_count sizes = 0 \<Longrightarrow> empty_data_ok mem (allocatable_dims dims') p"
    and nonempty: "sizes_count sizes \<noteq> 0 \<Longrightarrow> \<exists>data. data_region_ok mem (allocatable_dims dims') p
                       (gsz env enc elemTy * sizes_count sizes) data
                       \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                            rep_val env enc hmap mem elemTy v
                              (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))"
    by blast
  show ?thesis
  proof (cases "sizes_count sizes = 0")
    case z: True
    have "empty_data_ok mem (allocatable_dims dims) p"
      using empty[OF z] own[rule_format, OF D(8)] z by (auto simp: empty_data_ok_def)
    with D z assms(2,4) len show ?thesis
      unfolding rep_val.simps CoreType.case by simp blast
  next
    case nz: False
    from nonempty[OF nz] obtain data where
      reg: "data_region_ok mem (allocatable_dims dims') p (gsz env enc elemTy * sizes_count sizes) data"
      and el: "\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                 rep_val env enc hmap mem elemTy v
                   (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data)"
      by blast
    from own[rule_format, OF D(8)] nz obtain blk data0 where
      p: "p = MP_Addr blk 0" and blk: "fmlookup (MM_Blocks mem) blk = Some data0"
      and lendata0: "length data0 = gsz env enc elemTy * sizes_count sizes" by auto
    have rd: "mem_read mem p (gsz env enc elemTy * sizes_count sizes) = Some data"
      using reg by (simp add: data_region_ok_def)
    have "data = data0"
      using rd unfolding p mem_read_def using blk lendata0 by simp
    hence "data_region_ok mem (allocatable_dims dims) p (gsz env enc elemTy * sizes_count sizes) data"
      using rd p blk by (auto simp: data_region_ok_def)
    with D nz assms(2,4) len el show ?thesis
      unfolding rep_val.simps CoreType.case by simp blast
  qed
qed


section \<open>The projection lemma\<close>

(* The tag is inside the datatype's bytes (unconditionally: the fuel of
   type_size is positive, so the datatype equation always has the tag). *)
lemma tag_size_le_type_size: "tag_size env dt \<le> type_size env P sz (CoreTy_Datatype dt args)"
  unfolding type_size_def dt_fuel_def by (simp add: tsz_Suc_Datatype)

(* The bytes of a fixed array element. *)
lemma index_in_bounds_count_pos:
  "index_in_bounds sizes idx \<Longrightarrow> 0 < sizes_count sizes"
  using flat_index_bounds[of sizes idx] by auto

(* One step: the sub-value's bytes represent it; its reachable blocks are
   among the whole's; a memory location's block is reachable from the
   whole; an in-place location lies inside the bytes. *)
lemma path_step_sound:
  assumes "valid_encoding enc"
    and "rep_val env enc hmap mem ty v bs"
    and "path_step env enc mem ty bs s = Some (ty1, bs1, l1)"
    and "step_get v s = Some v1"
  shows "rep_val env enc hmap mem ty1 v1 bs1
         \<and> reach_blocks env enc mem ty1 v1 bs1 \<subseteq> reach_blocks env enc mem ty v bs
         \<and> (\<forall>q. l1 = PL_Mem q \<longrightarrow> (\<exists>blk off. q = MP_Addr blk off \<and> blk \<in> reach_blocks env enc mem ty v bs))
         \<and> (\<forall>off. l1 = PL_Here off \<longrightarrow> bs1 = slice off (gsz env enc ty1) bs \<and> off + gsz env enc ty1 \<le> length bs)"
proof (cases s)
  case (LVPath_RecordProj f)
  from assms(3,4) obtain ftys fvs where ty: "ty = CoreTy_Record ftys" and v: "v = CV_Record fvs"
    unfolding LVPath_RecordProj by (cases ty; cases v) (auto split: option.splits)
  from assms(3) obtain fty where fty: "map_of ftys f = Some fty"
    and ty1: "ty1 = fty"
    and bs1: "bs1 = slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f) (gsz env enc fty) bs"
    and l1: "l1 = PL_Here (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f)"
    unfolding LVPath_RecordProj ty by (auto split: option.splits)
  from assms(4) have fv: "map_of fvs f = Some v1" unfolding LVPath_RecordProj v by simp
  from rep_val_Record_E[OF assms(2)[unfolded v]] ty obtain
    dist: "distinct (map fst ftys)" and len: "length bs = gsz env enc (CoreTy_Record ftys)"
    and flds: "list_all2 (\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
           rep_val env enc hmap mem fty v
             (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)) fvs ftys"
    by auto
  from map_of_SomeD[OF fv] obtain i where i: "i < length fvs" and fvi: "fvs ! i = (f, v1)"
    by (auto simp: in_set_conv_nth)
  have lens: "length fvs = length ftys" using flds by (rule list_all2_lengthD)
  obtain n2 fty2 where ftyi: "ftys ! i = (n2, fty2)" by (cases "ftys ! i")
  from list_all2_nthD[OF flds i] fvi ftyi have n2: "n2 = f"
    and r: "rep_val env enc hmap mem fty2 v1 (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f) (gsz env enc fty2) bs)"
    by auto
  have "map_of ftys f = Some fty2"
    using ftyi n2 i lens dist by (metis map_of_eq_Some_iff nth_mem)
  with fty have fty2: "fty2 = fty" by simp
  have rep1: "rep_val env enc hmap mem ty1 v1 bs1" using r unfolding ty1 bs1 fty2 .
  have sub: "reach_blocks env enc mem ty1 v1 bs1 \<subseteq> reach_blocks env enc mem ty v bs"
    unfolding ty1 bs1 ty v using reach_blocks_Record_fld_nth[OF i _ fvi ftyi[unfolded n2 fty2]] i lens by simp
  have inside: "field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f + gsz env enc ty1 \<le> length bs"
    unfolding ty1 len by (rule field_offset_bound[OF fty])
  show ?thesis using rep1 sub inside l1 bs1 ty1 by simp
next
  case (LVPath_VariantProj c)
  from assms(4) obtain ctor payload where v: "v = CV_Variant ctor payload"
    unfolding LVPath_VariantProj by (cases v) auto
  from assms(4) have c: "ctor = c" and v1: "v1 = payload" unfolding LVPath_VariantProj v by (auto split: if_splits)
  from rep_val_Variant_E[OF assms(2)[unfolded v]] obtain dt args tyvars payloadTy where
    ty: "ty = CoreTy_Datatype dt args"
    and lk: "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
    and "length tyvars = length args" "ctor \<in> set (dt_ctors env dt)"
      "length bs = gsz env enc (CoreTy_Datatype dt args)"
      "take (tag_size env dt) bs = encode_val enc (MV_Int Unsigned (tag_bits env dt) (int (ctor_tag env dt ctor)))"
    and r: "rep_val env enc hmap mem (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) payload
           (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs)"
    by blast
  from assms(3) have ty1: "ty1 = apply_subst (fmap_of_list (zip tyvars args)) payloadTy"
    and bs1: "bs1 = slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs"
    and l1: "l1 = PL_Here (tag_size env dt)"
    unfolding LVPath_VariantProj ty using lk c by auto
  have rep1: "rep_val env enc hmap mem ty1 v1 bs1" using r unfolding ty1 bs1 v1 .
  have sub: "reach_blocks env enc mem ty1 v1 bs1 \<subseteq> reach_blocks env enc mem ty v bs"
    unfolding ty v ty1 bs1 v1 reach_blocks_Variant_payload[OF lk] by simp
  have "tag_size env dt \<le> length bs"
    using rep_val_length[OF assms(1) assms(2)] unfolding ty by (simp add: tag_size_le_type_size)
  hence inside: "tag_size env dt + gsz env enc ty1 \<le> length bs"
    using rep_val_length[OF assms(1) rep1] unfolding bs1 ty1 by (intro slice_len_inside) simp_all
  show ?thesis using rep1 sub inside l1 bs1 ty1 by simp
next
  case (LVPath_ArrayProj idx)
  from assms(3,4) obtain elemTy dims sizes elems where ty: "ty = CoreTy_Array elemTy dims"
    and v: "v = CV_Array sizes elems"
    unfolding LVPath_ArrayProj by (cases ty; cases v) (auto split: option.splits)
  from assms(4) have lk: "fmlookup elems idx = Some v1" unfolding LVPath_ArrayProj v by simp
  let ?esz = "gsz env enc elemTy"
  show ?thesis
  proof (cases "dims_all_fixed dims")
    case True
    note E = rep_val_FixedArray_E[OF assms(2)[unfolded ty v] True]
    from assms(3) have ty1: "ty1 = elemTy"
      and bs1: "bs1 = slice (elem_offset ?esz (dims_sizes dims) idx) ?esz bs"
      and l1: "l1 = PL_Here (elem_offset ?esz (dims_sizes dims) idx)"
      and inb: "index_in_bounds (dims_sizes dims) idx"
      unfolding LVPath_ArrayProj ty using True by (auto split: if_splits)
    have rep1: "rep_val env enc hmap mem ty1 v1 bs1" using E(4)[OF lk] unfolding ty1 bs1 E(1) .
    have sub: "reach_blocks env enc mem ty1 v1 bs1 \<subseteq> reach_blocks env enc mem ty v bs"
      unfolding ty v ty1 bs1 E(1) by (rule reach_blocks_FixedArray_elem[OF True lk])
    have inside: "elem_offset ?esz (dims_sizes dims) idx + gsz env enc ty1 \<le> length bs"
      using elem_offset_bound[OF inb, of ?esz] E(3) unfolding ty1 E(1) by simp
    show ?thesis using rep1 sub inside l1 bs1 ty1 by simp
  next
    case False
    from rep_val_Desc_E[OF assms(2)[unfolded ty v] False] obtain p where
      D: "sizes_match_dims sizes dims" "fmdom elems = fset_of_list (all_indices sizes)"
         "sizes_valid sizes" "sizes_count sizes < u64_max" "?esz * sizes_count sizes < u64_max"
         "length bs = desc_size (enc_ptr_size enc) (length dims)" "desc_dims_ok enc sizes bs"
         "take (enc_ptr_size enc) bs = encode_ptr enc p"
      and empty: "sizes_count sizes = 0 \<Longrightarrow> empty_data_ok mem (allocatable_dims dims) p"
      and nonempty: "sizes_count sizes \<noteq> 0 \<Longrightarrow> \<exists>data. data_region_ok mem (allocatable_dims dims) p
                         (?esz * sizes_count sizes) data
                         \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                              rep_val env enc hmap mem elemTy v (slice (elem_offset ?esz sizes idx) ?esz data))"
      by blast
    have inb: "index_in_bounds sizes idx"
      using lk D(2) by (metis fmdomI fset_of_list_elem in_all_indices_iff)
    have cnt: "sizes_count sizes \<noteq> 0" using index_in_bounds_count_pos[OF inb] by simp
    have ptr: "desc_ptr enc bs = Some p" by (rule desc_ptr_of_take[OF assms(1) D(8)])
    have szs: "desc_sizes enc (length dims) bs = Some sizes"
      using desc_sizes_of_dims_ok[OF assms(1) D(3) D(7)] sizes_match_dims_length[OF D(1)] by simp
    from assms(3) have ty1: "ty1 = elemTy"
      and rd1: "mem_read mem (ptr_off p (elem_offset ?esz sizes idx)) ?esz = Some bs1"
      and l1: "l1 = PL_Mem (ptr_off p (elem_offset ?esz sizes idx))"
      unfolding LVPath_ArrayProj ty using False ptr szs inb by (auto split: option.splits if_splits)
    from nonempty[OF cnt] obtain data where
      reg: "data_region_ok mem (allocatable_dims dims) p (?esz * sizes_count sizes) data"
      and el: "\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                 rep_val env enc hmap mem elemTy v (slice (elem_offset ?esz sizes idx) ?esz data)"
      by blast
    have rd: "mem_read mem p (?esz * sizes_count sizes) = Some data" using reg by (simp add: data_region_ok_def)
    from mem_read_sub[OF rd elem_offset_bound[OF inb]] rd1
    have bs1: "bs1 = slice (elem_offset ?esz sizes idx) ?esz data" by simp
    have rep1: "rep_val env enc hmap mem ty1 v1 bs1" using el lk unfolding ty1 bs1 by blast
    from rd obtain blk off where p: "p = MP_Addr blk off" by (cases p) (auto simp: mem_read_def)
    have sub: "reach_blocks env enc mem ty1 v1 bs1 \<subseteq> reach_blocks env enc mem ty v bs"
      unfolding ty v ty1 bs1 by (rule reach_blocks_Desc_elem[OF assms(1) False cnt D(8)[unfolded p] rd[unfolded p] lk])
    have blk_in: "blk \<in> reach_blocks env enc mem ty v bs"
      unfolding ty v by (rule reach_blocks_Desc[OF assms(1) False D(8)[unfolded p]])
    show ?thesis using rep1 sub blk_in l1 p by simp
  qed
next
  case (LVPath_ArrayCast dims')
  from assms(3,4) obtain elemTy dims sizes elems where ty: "ty = CoreTy_Array elemTy dims"
    and v: "v = CV_Array sizes elems"
    unfolding LVPath_ArrayCast by (cases ty; cases v) (auto split: option.splits)
  from assms(4) have match: "sizes_match_dims sizes dims'" and v1: "v1 = v"
    unfolding LVPath_ArrayCast v by (auto split: if_splits)
  from assms(3) have cat: "dims_all_fixed dims' = dims_all_fixed dims"
    and alloc: "allocatable_dims dims' \<longrightarrow> allocatable_dims dims"
    and ty1: "ty1 = CoreTy_Array elemTy dims'" and bs1: "bs1 = bs" and l1: "l1 = PL_Here 0"
    unfolding LVPath_ArrayCast ty by (auto split: if_splits)
  have rep1: "rep_val env enc hmap mem ty1 v1 bs1"
    unfolding ty1 bs1 v1 v by (rule rep_val_Array_weaken[OF assms(2)[unfolded ty v] match cat alloc])
  have sub: "reach_blocks env enc mem ty1 v1 bs1 \<subseteq> reach_blocks env enc mem ty v bs"
    unfolding ty1 bs1 v1 v ty using cat by simp
  have len: "length bs = gsz env enc ty1" using rep_val_length[OF assms(1) rep1] unfolding bs1 .
  show ?thesis using rep1 sub l1 bs1 len by (simp add: slice_0)
qed

(* The parts of path_step_sound. *)
lemma path_step_rep:
  "valid_encoding enc \<Longrightarrow> rep_val env enc hmap mem ty v bs \<Longrightarrow> path_step env enc mem ty bs s = Some (ty1, bs1, l1)
   \<Longrightarrow> step_get v s = Some v1 \<Longrightarrow> rep_val env enc hmap mem ty1 v1 bs1"
  by (rule conjunct1[OF path_step_sound])

lemma path_step_reach:
  "valid_encoding enc \<Longrightarrow> rep_val env enc hmap mem ty v bs \<Longrightarrow> path_step env enc mem ty bs s = Some (ty1, bs1, l1)
   \<Longrightarrow> step_get v s = Some v1 \<Longrightarrow> reach_blocks env enc mem ty1 v1 bs1 \<subseteq> reach_blocks env enc mem ty v bs"
  by (rule conjunct1[OF conjunct2[OF path_step_sound]])

lemma path_step_Mem_reach:
  "valid_encoding enc \<Longrightarrow> rep_val env enc hmap mem ty v bs \<Longrightarrow> path_step env enc mem ty bs s = Some (ty1, bs1, PL_Mem q)
   \<Longrightarrow> step_get v s = Some v1 \<Longrightarrow> \<exists>blk off. q = MP_Addr blk off \<and> blk \<in> reach_blocks env enc mem ty v bs"
  using conjunct1[OF conjunct2[OF conjunct2[OF path_step_sound]]] by blast

lemma path_step_Here:
  "valid_encoding enc \<Longrightarrow> rep_val env enc hmap mem ty v bs \<Longrightarrow> path_step env enc mem ty bs s = Some (ty1, bs1, PL_Here off)
   \<Longrightarrow> step_get v s = Some v1 \<Longrightarrow> bs1 = slice off (gsz env enc ty1) bs \<and> off + gsz env enc ty1 \<le> length bs"
  using conjunct2[OF conjunct2[OF conjunct2[OF path_step_sound]]] by blast

(* A memory location of a step is where the step read the bytes. *)
lemma path_step_Mem_read:
  assumes "path_step env enc mem ty bs s = Some (ty1, bs1, PL_Mem p)"
  shows "mem_read mem p (gsz env enc ty1) = Some bs1"
  using assms by (cases ty; cases s) (simp_all split: option.splits if_splits prod.splits)

(* The projection lemma: the bytes at the path's location represent the
   sub-value; its reachable blocks are among the whole's; a memory location
   is in a reachable block; an in-place location is inside the bytes. *)
lemma path_loc_sound_conj:
  assumes "valid_encoding enc"
  shows "rep_val env enc hmap mem ty v bs \<Longrightarrow> path_loc env enc mem ty bs path = Some (ty', bs', l)
         \<Longrightarrow> get_value_at_path v path = Inr v'
         \<Longrightarrow> rep_val env enc hmap mem ty' v' bs'
             \<and> reach_blocks env enc mem ty' v' bs' \<subseteq> reach_blocks env enc mem ty v bs
             \<and> (\<forall>q. l = PL_Mem q \<longrightarrow> (\<exists>blk off. q = MP_Addr blk off \<and> blk \<in> reach_blocks env enc mem ty v bs))
             \<and> (\<forall>off. l = PL_Here off \<longrightarrow> bs' = slice off (gsz env enc ty') bs \<and> off + gsz env enc ty' \<le> length bs)"
proof (induction path arbitrary: ty v bs l)
  case Nil
  then have e: "ty' = ty" "bs' = bs" "l = PL_Here 0" "v' = v" by simp_all
  have "length bs = gsz env enc ty" by (rule rep_val_length[OF assms Nil.prems(1)])
  then show ?case unfolding e using Nil.prems(1) by (simp add: slice_0)
next
  case (Cons s rest)
  from path_loc_ConsD[OF Cons.prems(2)] obtain ty1 bs1 l1 l' where
    st: "path_step env enc mem ty bs s = Some (ty1, bs1, l1)"
    and pl: "path_loc env enc mem ty1 bs1 rest = Some (ty', bs', l')" and l: "l = loc_compose l1 l'"
    by blast
  from Cons.prems(3) obtain v1 where sg: "step_get v s = Some v1" and g: "get_value_at_path v1 rest = Inr v'"
    by (auto simp: get_value_at_path_Cons)
  note S1 = path_step_rep[OF assms Cons.prems(1) st sg]
  note S2 = path_step_reach[OF assms Cons.prems(1) st sg]
  note IH = Cons.IH[OF S1 pl g]
  have IH1: "rep_val env enc hmap mem ty' v' bs'" by (rule conjunct1[OF IH])
  have IH2: "reach_blocks env enc mem ty' v' bs' \<subseteq> reach_blocks env enc mem ty1 v1 bs1"
    by (rule conjunct1[OF conjunct2[OF IH]])
  have IH3: "\<And>q. l' = PL_Mem q \<Longrightarrow> \<exists>blk off. q = MP_Addr blk off \<and> blk \<in> reach_blocks env enc mem ty1 v1 bs1"
    using conjunct1[OF conjunct2[OF conjunct2[OF IH]]] by blast
  have IH4: "\<And>off. l' = PL_Here off \<Longrightarrow> bs' = slice off (gsz env enc ty') bs1 \<and> off + gsz env enc ty' \<le> length bs1"
    using conjunct2[OF conjunct2[OF conjunct2[OF IH]]] by blast
  show ?case
  proof (intro conjI)
    show "rep_val env enc hmap mem ty' v' bs'" by (rule IH1)
    show "reach_blocks env enc mem ty' v' bs' \<subseteq> reach_blocks env enc mem ty v bs" using IH2 S2 by (rule subset_trans)
  next
    show "\<forall>q. l = PL_Mem q \<longrightarrow> (\<exists>blk off. q = MP_Addr blk off \<and> blk \<in> reach_blocks env enc mem ty v bs)"
    proof (intro allI impI)
    fix q assume lq: "l = PL_Mem q"
    show "\<exists>blk off. q = MP_Addr blk off \<and> blk \<in> reach_blocks env enc mem ty v bs"
    proof (cases l')
      case (PL_Mem q')
      with lq l have "q = q'" by (cases l1) simp_all
      with IH3[OF PL_Mem] S2 show ?thesis by blast
    next
      case (PL_Here o2)
      with lq l obtain p where l1: "l1 = PL_Mem p" and q: "q = ptr_off p o2" by (cases l1) simp_all
      from path_step_Mem_reach[OF assms Cons.prems(1) st[unfolded l1] sg] obtain blk off where
        "p = MP_Addr blk off" "blk \<in> reach_blocks env enc mem ty v bs" by blast
      thus ?thesis unfolding q by simp
    qed
    qed
  next
    show "\<forall>off. l = PL_Here off \<longrightarrow> bs' = slice off (gsz env enc ty') bs \<and> off + gsz env enc ty' \<le> length bs"
    proof (intro allI impI)
    fix off assume lo: "l = PL_Here off"
    then obtain o1 o2 where l1: "l1 = PL_Here o1" and l': "l' = PL_Here o2" and off: "off = o1 + o2"
      using l by (cases l1; cases l') auto
    from path_step_Here[OF assms Cons.prems(1) st[unfolded l1] sg]
    have bs1: "bs1 = slice o1 (gsz env enc ty1) bs" and in1: "o1 + gsz env enc ty1 \<le> length bs" by auto
    from IH4[OF l'] have bs': "bs' = slice o2 (gsz env enc ty') bs1" and in2: "o2 + gsz env enc ty' \<le> length bs1" by auto
    have len1: "length bs1 = gsz env enc ty1" unfolding bs1 by (rule length_slice_le[OF in1])
    have "bs' = slice (o1 + o2) (gsz env enc ty') bs"
      unfolding bs' bs1 by (rule slice_slice) (use in2 len1 in simp)
    moreover have "o1 + o2 + gsz env enc ty' \<le> length bs" using in1 in2 len1 by simp
    ultimately show "bs' = slice off (gsz env enc ty') bs \<and> off + gsz env enc ty' \<le> length bs" by (simp add: off)
    qed
  qed
qed

lemma path_loc_rep:
  "valid_encoding enc \<Longrightarrow> rep_val env enc hmap mem ty v bs \<Longrightarrow> path_loc env enc mem ty bs path = Some (ty', bs', l)
   \<Longrightarrow> get_value_at_path v path = Inr v' \<Longrightarrow> rep_val env enc hmap mem ty' v' bs'"
  by (rule conjunct1[OF path_loc_sound_conj])

lemma path_loc_reach:
  "valid_encoding enc \<Longrightarrow> rep_val env enc hmap mem ty v bs \<Longrightarrow> path_loc env enc mem ty bs path = Some (ty', bs', l)
   \<Longrightarrow> get_value_at_path v path = Inr v' \<Longrightarrow> reach_blocks env enc mem ty' v' bs' \<subseteq> reach_blocks env enc mem ty v bs"
  by (rule conjunct1[OF conjunct2[OF path_loc_sound_conj]])

lemma path_loc_Mem_reach:
  "valid_encoding enc \<Longrightarrow> rep_val env enc hmap mem ty v bs \<Longrightarrow> path_loc env enc mem ty bs path = Some (ty', bs', PL_Mem q)
   \<Longrightarrow> get_value_at_path v path = Inr v' \<Longrightarrow> \<exists>blk off. q = MP_Addr blk off \<and> blk \<in> reach_blocks env enc mem ty v bs"
  using conjunct1[OF conjunct2[OF conjunct2[OF path_loc_sound_conj]]] by blast

lemma path_loc_Here:
  "valid_encoding enc \<Longrightarrow> rep_val env enc hmap mem ty v bs \<Longrightarrow> path_loc env enc mem ty bs path = Some (ty', bs', PL_Here off)
   \<Longrightarrow> get_value_at_path v path = Inr v' \<Longrightarrow> bs' = slice off (gsz env enc ty') bs \<and> off + gsz env enc ty' \<le> length bs"
  using conjunct2[OF conjunct2[OF conjunct2[OF path_loc_sound_conj]]] by blast

(* The bytes at a memory location, read from the memory. *)
lemma path_loc_Mem_read:
  assumes "valid_encoding enc" and "rep_val env enc hmap mem ty v bs"
    and "path_loc env enc mem ty bs path = Some (ty', bs', PL_Mem q)"
    and "get_value_at_path v path = Inr v'"
  shows "mem_read mem q (gsz env enc ty') = Some bs'"
  using assms(2-4)
proof (induction path arbitrary: ty v bs q)
  case Nil
  then show ?case by simp
next
  case (Cons s rest)
  from path_loc_ConsD[OF Cons.prems(2)] obtain ty1 bs1 l1 l' where
    st: "path_step env enc mem ty bs s = Some (ty1, bs1, l1)"
    and pl: "path_loc env enc mem ty1 bs1 rest = Some (ty', bs', l')" and l: "PL_Mem q = loc_compose l1 l'"
    by blast
  from Cons.prems(3) obtain v1 where sg: "step_get v s = Some v1" and g: "get_value_at_path v1 rest = Inr v'"
    by (auto simp: get_value_at_path_Cons)
  note S1 = path_step_rep[OF assms(1) Cons.prems(1) st sg]
  show ?case
  proof (cases l')
    case (PL_Mem q')
    with l have "q = q'" by (cases l1) simp_all
    with Cons.IH[OF S1 pl[unfolded PL_Mem] g] show ?thesis by simp
  next
    case (PL_Here o2)
    with l obtain p where l1: "l1 = PL_Mem p" and q: "q = ptr_off p o2" by (cases l1) simp_all
    from path_loc_Here[OF assms(1) S1 pl[unfolded PL_Here] g]
    have bs': "bs' = slice o2 (gsz env enc ty') bs1" and in2: "o2 + gsz env enc ty' \<le> length bs1" by auto
    have rd: "mem_read mem p (gsz env enc ty1) = Some bs1" by (rule path_step_Mem_read[OF st[unfolded l1]])
    have len1: "length bs1 = gsz env enc ty1" by (rule rep_val_length[OF assms(1) S1])
    show ?thesis unfolding q bs' using mem_read_sub[OF rd, of o2 "gsz env enc ty'"] in2 len1 by simp
  qed
qed

end

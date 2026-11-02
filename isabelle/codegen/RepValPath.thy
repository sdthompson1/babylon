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


section \<open>Updates: the Core side\<close>

(* An update that succeeds reads the old sub-value. *)
lemma update_value_at_path_get:
  "update_value_at_path v path v' = Inr w \<Longrightarrow> \<exists>vold. get_value_at_path v path = Inr vold"
proof (induction path arbitrary: v w)
  case Nil
  then show ?case by simp
next
  case (Cons s rest)
  from Cons.prems obtain v1 w1 where sg: "step_get v s = Some v1"
    and u: "update_value_at_path v1 rest v' = Inr w1" by (auto simp: update_value_at_path_Cons)
  from Cons.IH[OF u] obtain vold where "get_value_at_path v1 rest = Inr vold" by blast
  with sg show ?case by (auto simp: get_value_at_path_Cons)
qed

(* AList.update on a list with distinct keys: the entry of that key is
   replaced, the others stay in place. *)
lemma AList_update_nth:
  assumes "distinct (map fst xs)" and "k \<in> fst ` set xs"
  shows "length (AList.update k v xs) = length xs
         \<and> (\<forall>i < length xs. AList.update k v xs ! i = (if fst (xs ! i) = k then (k, v) else xs ! i))"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "fst x = k")
    case True
    hence notin: "k \<notin> fst ` set xs" using Cons.prems(1) by auto
    have "\<And>i. i < length (x # xs) \<Longrightarrow> ((k, v) # xs) ! i = (if fst ((x # xs) ! i) = k then (k, v) else (x # xs) ! i)"
    proof -
      fix i assume i: "i < length (x # xs)"
      show "((k, v) # xs) ! i = (if fst ((x # xs) ! i) = k then (k, v) else (x # xs) ! i)"
      proof (cases i)
        case (Suc n)
        with i have "xs ! n \<in> set xs" by (simp add: nth_mem)
        hence "fst (xs ! n) \<in> fst ` set xs" by simp
        hence ne: "fst (xs ! n) \<noteq> k" using notin True by blast
        show ?thesis using Suc ne by simp
      qed (simp add: True)
    qed
    thus ?thesis using True by simp
  next
    case False
    hence kin: "k \<in> fst ` set xs" using Cons.prems(2) by auto
    have dist: "distinct (map fst xs)" using Cons.prems(1) by simp
    note IH = Cons.IH[OF dist kin]
    have "\<And>i. i < length (x # xs) \<Longrightarrow>
            (x # AList.update k v xs) ! i = (if fst ((x # xs) ! i) = k then (k, v) else (x # xs) ! i)"
    proof -
      fix i assume "i < length (x # xs)"
      thus "(x # AList.update k v xs) ! i = (if fst ((x # xs) ! i) = k then (k, v) else (x # xs) ! i)"
        using IH False by (cases i) auto
    qed
    thus ?thesis using False IH by simp
  qed
qed


section \<open>Field ranges are disjoint\<close>

(* Distinct keys: equal keys at two positions means the same position. *)
lemma distinct_fst_nth_eq:
  assumes "distinct (map fst xs)" and "i < length xs" and "j < length xs" and "fst (xs ! i) = fst (xs ! j)"
  shows "i = j"
  using assms by (auto simp: distinct_conv_nth)

(* The position of a key in a list with distinct keys. *)
lemma map_of_nth_distinct:
  assumes "distinct (map fst xs)" and "i < length xs" and "map_of xs (fst (xs ! i)) = Some y"
  shows "xs ! i = (fst (xs ! i), y)"
proof -
  from map_of_SomeD[OF assms(3)] obtain j where j: "j < length xs" and xj: "xs ! j = (fst (xs ! i), y)"
    by (auto simp: in_set_conv_nth)
  have "i = j" using distinct_fst_nth_eq[OF assms(1,2) j] xj by simp
  thus ?thesis using xj by simp
qed

lemma sum_list_map_take_le: "sum_list (map f (take n xs)) \<le> (sum_list (map f xs) :: nat)"
  by (induction xs arbitrary: n) (auto simp: take_Cons split: nat.split)

lemma field_offset_disjoint:
  assumes "distinct (map fst flds)"
    and "i < length flds" and "j < length flds" and "i \<noteq> j"
  shows "field_offset env P sz flds (fst (flds ! i)) + type_size env P sz (snd (flds ! i))
           \<le> field_offset env P sz flds (fst (flds ! j))
         \<or> field_offset env P sz flds (fst (flds ! j)) + type_size env P sz (snd (flds ! j))
           \<le> field_offset env P sz flds (fst (flds ! i))"
proof -
  have off: "\<And>k. k < length flds \<Longrightarrow>
               field_offset env P sz flds (fst (flds ! k)) = sum_list (map (\<lambda>fld. type_size env P sz (snd fld)) (take k flds))"
  proof -
    fix k assume k: "k < length flds"
    have split: "flds = take k flds @ (fst (flds ! k), snd (flds ! k)) # drop (Suc k) flds"
      using k by (simp add: id_take_nth_drop)
    have notin: "fst (flds ! k) \<notin> fst ` set (take k flds)"
    proof
      assume "fst (flds ! k) \<in> fst ` set (take k flds)"
      then obtain k' where "k' < k" and "fst (flds ! k') = fst (flds ! k)"
        by (auto simp: in_set_conv_nth)
      with k assms(1) show False by (auto simp: distinct_conv_nth)
    qed
    show "field_offset env P sz flds (fst (flds ! k)) = sum_list (map (\<lambda>fld. type_size env P sz (snd fld)) (take k flds))"
      using field_offset_split[OF split notin] by simp
  qed
  have step: "\<And>a b. a < b \<Longrightarrow> b < length flds \<Longrightarrow>
                field_offset env P sz flds (fst (flds ! a)) + type_size env P sz (snd (flds ! a))
                \<le> field_offset env P sz flds (fst (flds ! b))"
  proof -
    fix a b assume ab: "a < b" and b: "b < length flds"
    let ?f = "\<lambda>fld. type_size env P sz (snd fld)"
    have "take (Suc a) flds = take a flds @ [flds ! a]" using ab b by (simp add: take_Suc_conv_app_nth)
    hence s1: "sum_list (map ?f (take (Suc a) flds)) = sum_list (map ?f (take a flds)) + ?f (flds ! a)" by simp
    have "take (Suc a) (take b flds) = take (Suc a) flds" using ab by (simp add: min_def)
    hence "sum_list (map ?f (take (Suc a) flds)) \<le> sum_list (map ?f (take b flds))"
      using sum_list_map_take_le[of ?f "Suc a" "take b flds"] by simp
    thus "field_offset env P sz flds (fst (flds ! a)) + type_size env P sz (snd (flds ! a))
          \<le> field_offset env P sz flds (fst (flds ! b))"
      using off[OF b] off[of a] ab b s1 by simp
  qed
  show ?thesis using step[of i j] step[of j i] assms(2-4) by (cases "i < j") auto
qed


section \<open>Ownership within a value\<close>

(* The reachable blocks of a record field, given the (value, type) pair of
   the zip. *)
definition fld_reach :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> (string \<times> CoreType) list \<Rightarrow> MByte list
                         \<Rightarrow> (string \<times> CoreValue) \<times> (string \<times> CoreType) \<Rightarrow> nat set" where
  "fld_reach env enc mem ftys bs x = (case x of ((n1, v), (n2, fty)) \<Rightarrow>
     reach_blocks env enc mem fty v (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs))"

(* The heap blocks reachable from v form a tree: the blocks reachable from
   distinct components are disjoint, and the data block of a descriptor is
   reachable from none of its elements. The update lemmas need this to know
   that writing into a block reached through the path leaves every other
   component's blocks untouched. Stage 6 maintains it for every cell. *)
function val_owned :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> CoreValue \<Rightarrow> MByte list \<Rightarrow> bool" where
  "val_owned env enc mem ty (CV_Record fvs) bs =
    (case ty of
       CoreTy_Record ftys \<Rightarrow>
         (\<forall>i j. i < length (zip fvs ftys) \<longrightarrow> j < length (zip fvs ftys) \<longrightarrow> i \<noteq> j \<longrightarrow>
            fld_reach env enc mem ftys bs (zip fvs ftys ! i) \<inter> fld_reach env enc mem ftys bs (zip fvs ftys ! j) = {})
         \<and> (\<forall>x \<in> set (zip fvs ftys). case x of ((n1, v), (n2, fty)) \<Rightarrow>
              val_owned env enc mem fty v
                (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs))
     | _ \<Rightarrow> True)"
| "val_owned env enc mem ty (CV_Variant ctor payload) bs =
    (case ty of
       CoreTy_Datatype dt args \<Rightarrow>
         (case fmlookup (TE_DataCtors env) ctor of
            Some (dt2, tyvars, payloadTy) \<Rightarrow>
              val_owned env enc mem (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) payload
                (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs)
          | None \<Rightarrow> True)
     | _ \<Rightarrow> True)"
| "val_owned env enc mem ty (CV_Array sizes elems) bs =
    (case ty of
       CoreTy_Array elemTy dims \<Rightarrow>
         (if dims_all_fixed dims then
            (\<forall>idx1 v1 idx2 v2. fmlookup elems idx1 = Some v1 \<longrightarrow> fmlookup elems idx2 = Some v2 \<longrightarrow> idx1 \<noteq> idx2 \<longrightarrow>
               reach_blocks env enc mem elemTy v1 (slice (elem_offset (gsz env enc elemTy) sizes idx1) (gsz env enc elemTy) bs)
               \<inter> reach_blocks env enc mem elemTy v2 (slice (elem_offset (gsz env enc elemTy) sizes idx2) (gsz env enc elemTy) bs) = {})
            \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                 val_owned env enc mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) bs))
          else
            (case decode_ptr enc (take (enc_ptr_size enc) bs) of
               Some (MP_Addr blk off) \<Rightarrow>
                 (if sizes_count sizes = 0 then True
                  else (case mem_read mem (MP_Addr blk off) (gsz env enc elemTy * sizes_count sizes) of
                          Some data \<Rightarrow>
                            (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                               blk \<notin> reach_blocks env enc mem elemTy v
                                        (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))
                            \<and> (\<forall>idx1 v1 idx2 v2. fmlookup elems idx1 = Some v1 \<longrightarrow> fmlookup elems idx2 = Some v2 \<longrightarrow> idx1 \<noteq> idx2 \<longrightarrow>
                                 reach_blocks env enc mem elemTy v1 (slice (elem_offset (gsz env enc elemTy) sizes idx1) (gsz env enc elemTy) data)
                                 \<inter> reach_blocks env enc mem elemTy v2 (slice (elem_offset (gsz env enc elemTy) sizes idx2) (gsz env enc elemTy) data) = {})
                            \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                                 val_owned env enc mem elemTy v
                                   (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))
                        | None \<Rightarrow> True))
             | _ \<Rightarrow> True))
     | _ \<Rightarrow> True)"
| "val_owned env enc mem ty (CV_Bool _) bs = True"
| "val_owned env enc mem ty (CV_FiniteInt _ _ _) bs = True"
| "val_owned env enc mem ty (CV_Int _) bs = True"
| "val_owned env enc mem ty (CV_Real _) bs = True"
| "val_owned env enc mem ty (CV_Extern _ _ _) bs = True"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(env, enc, mem, ty, v, bs). size v)")
     (auto dest!: set_zip_leftD intro: size_record_field' size_array_lookup')

(* The ownership facts of one step: the component is owned, and the blocks
   reachable from any other component are disjoint from the component's.
   For a descriptor step, additionally the data block is not reachable from
   any element. *)
lemma val_owned_step:
  assumes "valid_encoding enc"
    and "rep_val env enc hmap mem ty v bs"
    and "val_owned env enc mem ty v bs"
    and "path_step env enc mem ty bs s = Some (ty1, bs1, l1)"
    and "step_get v s = Some v1"
  shows "val_owned env enc mem ty1 v1 bs1"
  using assms
proof (cases s)
  case (LVPath_RecordProj f)
  from assms(4,5) obtain ftys fvs where ty: "ty = CoreTy_Record ftys" and v: "v = CV_Record fvs"
    unfolding LVPath_RecordProj by (cases ty; cases v) (auto split: option.splits)
  from assms(4) obtain fty where fty: "map_of ftys f = Some fty" and ty1: "ty1 = fty"
    and bs1: "bs1 = slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f) (gsz env enc fty) bs"
    unfolding LVPath_RecordProj ty by (auto split: option.splits)
  from assms(5) have fv: "map_of fvs f = Some v1" unfolding LVPath_RecordProj v by simp
  from rep_val_Record_E[OF assms(2)[unfolded v]] ty obtain
    dist: "distinct (map fst ftys)"
    and flds: "list_all2 (\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
           rep_val env enc hmap mem fty v
             (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)) fvs ftys"
    by auto
  from map_of_SomeD[OF fv] obtain i where i: "i < length fvs" and fvi: "fvs ! i = (f, v1)"
    by (auto simp: in_set_conv_nth)
  have lens: "length fvs = length ftys" using flds by (rule list_all2_lengthD)
  obtain n2 fty2 where ftyi: "ftys ! i = (n2, fty2)" by (cases "ftys ! i")
  from list_all2_nthD[OF flds i] fvi ftyi have n2: "n2 = f" by auto
  have "map_of ftys f = Some fty2" using ftyi n2 i lens dist by (metis map_of_eq_Some_iff nth_mem)
  with fty have fty2: "fty2 = fty" by simp
  have "((f, v1), (f, fty)) \<in> set (zip fvs ftys)"
    using i lens fvi ftyi[unfolded n2 fty2] by (metis nth_zip nth_mem length_zip min_less_iff_conj)
  with assms(3) show ?thesis unfolding ty v ty1 bs1 by (simp split: prod.splits)
next
  case (LVPath_VariantProj c)
  from assms(5) obtain ctor payload where v: "v = CV_Variant ctor payload"
    unfolding LVPath_VariantProj by (cases v) auto
  from assms(5) have c: "ctor = c" and v1: "v1 = payload" unfolding LVPath_VariantProj v by (auto split: if_splits)
  from assms(4) obtain dt args where ty: "ty = CoreTy_Datatype dt args"
    unfolding LVPath_VariantProj by (cases ty) auto
  from assms(4) obtain tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) c = Some (dt, tyvars, payloadTy)"
    and ty1: "ty1 = apply_subst (fmap_of_list (zip tyvars args)) payloadTy"
    and bs1: "bs1 = slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs"
    unfolding LVPath_VariantProj ty by (auto split: option.splits if_splits)
  from assms(3) show ?thesis unfolding ty v ty1 bs1 v1 c using lk by simp
next
  case (LVPath_ArrayProj idx)
  from assms(4,5) obtain elemTy dims sizes elems where ty: "ty = CoreTy_Array elemTy dims"
    and v: "v = CV_Array sizes elems"
    unfolding LVPath_ArrayProj by (cases ty; cases v) (auto split: option.splits)
  from assms(5) have lk: "fmlookup elems idx = Some v1" unfolding LVPath_ArrayProj v by simp
  let ?esz = "gsz env enc elemTy"
  show ?thesis
  proof (cases "dims_all_fixed dims")
    case True
    note E = rep_val_FixedArray_E[OF assms(2)[unfolded ty v] True]
    from assms(4) have ty1: "ty1 = elemTy"
      and bs1: "bs1 = slice (elem_offset ?esz (dims_sizes dims) idx) ?esz bs"
      unfolding LVPath_ArrayProj ty using True by (auto split: if_splits)
    from assms(3) show ?thesis unfolding ty v ty1 bs1 E(1) using True lk by simp
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
    from assms(4) have ty1: "ty1 = elemTy"
      and rd1: "mem_read mem (ptr_off p (elem_offset ?esz sizes idx)) ?esz = Some bs1"
      unfolding LVPath_ArrayProj ty using False ptr szs inb by (auto split: option.splits if_splits)
    from nonempty[OF cnt] obtain data where
      reg: "data_region_ok mem (allocatable_dims dims) p (?esz * sizes_count sizes) data" by blast
    have rd: "mem_read mem p (?esz * sizes_count sizes) = Some data" using reg by (simp add: data_region_ok_def)
    from mem_read_sub[OF rd elem_offset_bound[OF inb]] rd1
    have bs1: "bs1 = slice (elem_offset ?esz sizes idx) ?esz data" by simp
    from rd obtain blk off where p: "p = MP_Addr blk off" by (cases p) (auto simp: mem_read_def)
    have dec: "decode_ptr enc (take (enc_ptr_size enc) bs) = Some (MP_Addr blk off)"
      unfolding D(8) p by (rule decode_ptr_encode_ptr[OF assms(1)])
    from assms(3) show ?thesis unfolding ty v ty1 bs1 using False dec cnt rd[unfolded p] lk by simp
  qed
next
  case (LVPath_ArrayCast dims')
  from assms(4,5) obtain elemTy dims sizes elems where ty: "ty = CoreTy_Array elemTy dims"
    and v: "v = CV_Array sizes elems"
    unfolding LVPath_ArrayCast by (cases ty; cases v) (auto split: option.splits)
  from assms(5) have v1: "v1 = v" unfolding LVPath_ArrayCast v by (auto split: if_splits)
  from assms(4) have cat: "dims_all_fixed dims' = dims_all_fixed dims"
    and ty1: "ty1 = CoreTy_Array elemTy dims'" and bs1: "bs1 = bs"
    unfolding LVPath_ArrayCast ty by (auto split: if_splits)
  from assms(3) show ?thesis unfolding ty v ty1 bs1 v1 using cat by simp
qed


section \<open>Reassembling a value after an update\<close>

(* A record whose fields are all represented. *)
lemma rep_val_Record_I:
  assumes "distinct (map fst ftys)" and "length bs = gsz env enc (CoreTy_Record ftys)"
    and "length fvs = length ftys"
    and "\<And>i. i < length ftys \<Longrightarrow> fst (fvs ! i) = fst (ftys ! i)
           \<and> rep_val env enc hmap mem (snd (ftys ! i)) (snd (fvs ! i))
               (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys (fst (ftys ! i))) (gsz env enc (snd (ftys ! i))) bs)"
  shows "rep_val env enc hmap mem (CoreTy_Record ftys) (CV_Record fvs) bs"
proof -
  have "list_all2 (\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
           rep_val env enc hmap mem fty v
             (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)) fvs ftys"
  proof (rule list_all2_all_nthI[OF assms(3)])
    fix i assume i: "i < length fvs"
    obtain n1 v where fvi: "fvs ! i = (n1, v)" by (cases "fvs ! i")
    obtain n2 fty where ftyi: "ftys ! i = (n2, fty)" by (cases "ftys ! i")
    from assms(4)[of i] i assms(3) fvi ftyi show "(\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
           rep_val env enc hmap mem fty v
             (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)) (fvs ! i) (ftys ! i)"
      by simp
  qed
  with assms(1,2) show ?thesis by simp
qed

(* The record with field f replaced: every other field keeps its bytes
   (represented in the new memory), field f gets the new bytes. *)
lemma rep_val_Record_update:
  assumes enc: "valid_encoding enc"
    and old: "rep_val env enc hmap mem (CoreTy_Record ftys) (CV_Record fvs) bs"
    and fty: "map_of ftys f = Some fty"
    and len: "length bs'' = length bs"
    and sib: "\<And>i. i < length ftys \<Longrightarrow> fst (ftys ! i) \<noteq> f \<Longrightarrow>
                rep_val env enc hmap mem' (snd (ftys ! i)) (snd (fvs ! i))
                  (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys (fst (ftys ! i))) (gsz env enc (snd (ftys ! i))) bs'')"
    and new: "rep_val env enc hmap mem' fty w1 (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f) (gsz env enc fty) bs'')"
  shows "rep_val env enc hmap mem' (CoreTy_Record ftys) (CV_Record (AList.update f w1 fvs)) bs''"
proof -
  from rep_val_Record_E[OF old] obtain
    dist: "distinct (map fst ftys)" and lenbs: "length bs = gsz env enc (CoreTy_Record ftys)"
    and flds: "list_all2 (\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
           rep_val env enc hmap mem fty v
             (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys n2) (gsz env enc fty) bs)) fvs ftys"
    by auto
  have lens: "length fvs = length ftys" using flds by (rule list_all2_lengthD)
  have names: "\<And>i. i < length ftys \<Longrightarrow> fst (fvs ! i) = fst (ftys ! i)"
  proof -
    fix i assume i: "i < length ftys"
    from list_all2_nthD[OF flds, of i] i lens show "fst (fvs ! i) = fst (ftys ! i)"
      by (cases "fvs ! i"; cases "ftys ! i") auto
  qed
  have distv: "distinct (map fst fvs)"
    using dist names lens by (simp add: distinct_conv_nth)
  from map_of_SomeD[OF fty] obtain j where j: "j < length ftys" and ftyj: "ftys ! j = (f, fty)"
    by (auto simp: in_set_conv_nth)
  have "fst (fvs ! j) = f" using names[OF j] ftyj by simp
  hence fin: "f \<in> fst ` set fvs" using j lens by (metis nth_mem imageI)
  note U = AList_update_nth[OF distv fin, of w1]
  show ?thesis
  proof (rule rep_val_Record_I[OF dist len[unfolded lenbs]])
    show "length (AList.update f w1 fvs) = length ftys" using U lens by simp
  next
    fix i assume i: "i < length ftys"
    show "fst (AList.update f w1 fvs ! i) = fst (ftys ! i) \<and>
          rep_val env enc hmap mem' (snd (ftys ! i)) (snd (AList.update f w1 fvs ! i))
            (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys (fst (ftys ! i))) (gsz env enc (snd (ftys ! i))) bs'')"
    proof (cases "fst (ftys ! i) = f")
      case True
      have "ftys ! i = (f, fty)" using map_of_nth_distinct[OF dist i] fty True by simp
      with U i lens names True new show ?thesis by simp
    next
      case False
      with U i lens names sib[OF i False] show ?thesis by simp
    qed
  qed
qed

(* The variant with its payload replaced. *)
lemma rep_val_Variant_update:
  assumes old: "rep_val env enc hmap mem (CoreTy_Datatype dt args) (CV_Variant ctor payload) bs"
    and lk: "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
    and len: "length bs'' = length bs"
    and tag: "take (tag_size env dt) bs'' = take (tag_size env dt) bs"
    and new: "rep_val env enc hmap mem' (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) w1
                (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs'')"
  shows "rep_val env enc hmap mem' (CoreTy_Datatype dt args) (CV_Variant ctor w1) bs''"
  using old lk len tag new by (simp split: option.splits)

(* A fixed array with element idx replaced. *)
lemma rep_val_FixedArray_update:
  assumes old: "rep_val env enc hmap mem (CoreTy_Array elemTy dims) (CV_Array sizes elems) bs"
    and fixed: "dims_all_fixed dims"
    and lk: "fmlookup elems idx = Some v0"
    and len: "length bs'' = length bs"
    and sib: "\<And>idx' v. idx' \<noteq> idx \<Longrightarrow> fmlookup elems idx' = Some v \<Longrightarrow>
                rep_val env enc hmap mem' elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx') (gsz env enc elemTy) bs'')"
    and new: "rep_val env enc hmap mem' elemTy w1 (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) bs'')"
  shows "rep_val env enc hmap mem' (CoreTy_Array elemTy dims) (CV_Array sizes (fmupd idx w1 elems)) bs''"
proof -
  note E = rep_val_FixedArray_E[OF old fixed]
  have dom: "fmdom (fmupd idx w1 elems) = fset_of_list (all_indices sizes)"
    using E(2) fmdomI[OF lk] by auto
  have "\<And>idx' v. fmlookup (fmupd idx w1 elems) idx' = Some v \<Longrightarrow>
          rep_val env enc hmap mem' elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx') (gsz env enc elemTy) bs'')"
    using sib new by (auto split: if_splits)
  with old fixed dom len show ?thesis by simp
qed

(* A descriptor whose data region now holds data'. *)
lemma rep_val_Desc_update:
  assumes old: "rep_val env enc hmap mem (CoreTy_Array elemTy dims) (CV_Array sizes elems) bs"
    and nf: "\<not> dims_all_fixed dims"
    and ptr: "take (enc_ptr_size enc) bs = encode_ptr enc p"
    and lk: "fmlookup elems idx = Some v0"
    and reg: "data_region_ok mem' (allocatable_dims dims) p (gsz env enc elemTy * sizes_count sizes) data'"
    and sib: "\<And>idx' v. idx' \<noteq> idx \<Longrightarrow> fmlookup elems idx' = Some v \<Longrightarrow>
                rep_val env enc hmap mem' elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx') (gsz env enc elemTy) data')"
    and new: "rep_val env enc hmap mem' elemTy w1 (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data')"
  shows "rep_val env enc hmap mem' (CoreTy_Array elemTy dims) (CV_Array sizes (fmupd idx w1 elems)) bs"
proof -
  from rep_val_Desc_E[OF old nf] obtain p0 where
    D: "sizes_match_dims sizes dims" "fmdom elems = fset_of_list (all_indices sizes)"
       "sizes_valid sizes" "sizes_count sizes < u64_max" "gsz env enc elemTy * sizes_count sizes < u64_max"
       "length bs = desc_size (enc_ptr_size enc) (length dims)" "desc_dims_ok enc sizes bs"
       "take (enc_ptr_size enc) bs = encode_ptr enc p0"
    and empty: "sizes_count sizes = 0 \<Longrightarrow> empty_data_ok mem (allocatable_dims dims) p0"
    and nonempty: "sizes_count sizes \<noteq> 0 \<Longrightarrow> \<exists>data. data_region_ok mem (allocatable_dims dims) p0
                       (gsz env enc elemTy * sizes_count sizes) data
                       \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                            rep_val env enc hmap mem elemTy v
                              (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))"
    by blast
  have inb: "index_in_bounds sizes idx"
    using lk D(2) by (metis fmdomI fset_of_list_elem in_all_indices_iff)
  have cnt: "sizes_count sizes \<noteq> 0" using index_in_bounds_count_pos[OF inb] by simp
  have dom: "fmdom (fmupd idx w1 elems) = fset_of_list (all_indices sizes)"
    using D(2) fmdomI[OF lk] by auto
  have els: "\<forall>idx' v. fmlookup (fmupd idx w1 elems) idx' = Some v \<longrightarrow>
          rep_val env enc hmap mem' elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx') (gsz env enc elemTy) data')"
    using sib new by (auto split: if_splits)
  have ex: "\<exists>p. take (enc_ptr_size enc) bs = encode_ptr enc p
             \<and> (if sizes_count sizes = 0 then empty_data_ok mem' (allocatable_dims dims) p
                else (\<exists>data. data_region_ok mem' (allocatable_dims dims) p (gsz env enc elemTy * sizes_count sizes) data
                        \<and> (\<forall>idx' v. fmlookup (fmupd idx w1 elems) idx' = Some v \<longrightarrow>
                             rep_val env enc hmap mem' elemTy v
                               (slice (elem_offset (gsz env enc elemTy) sizes idx') (gsz env enc elemTy) data))))"
  proof (intro exI[where x = p] conjI)
    show "take (enc_ptr_size enc) bs = encode_ptr enc p" by (rule ptr)
    show "if sizes_count sizes = 0 then empty_data_ok mem' (allocatable_dims dims) p
          else (\<exists>data. data_region_ok mem' (allocatable_dims dims) p (gsz env enc elemTy * sizes_count sizes) data
                  \<and> (\<forall>idx' v. fmlookup (fmupd idx w1 elems) idx' = Some v \<longrightarrow>
                       rep_val env enc hmap mem' elemTy v
                         (slice (elem_offset (gsz env enc elemTy) sizes idx') (gsz env enc elemTy) data)))"
      unfolding if_not_P[OF cnt] by (intro exI[where x = data'] conjI reg els)
  qed
  show ?thesis
    unfolding rep_val.simps CoreType.case using nf D(1,3-7) dom ex by simp
qed


section \<open>The update lemma\<close>

(* The casts of a path that an update may go through: a cast that drops
   ownership (T[*] to T[]) is fine when the update happens inside the heap
   data (the descriptor bytes do not change), but not when the whole cast
   array is replaced (the new value would have to own its data, which a T[]
   value does not promise). *)
fun path_casts_ok :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> MByte list \<Rightarrow> LValuePath list \<Rightarrow> bool" where
  "path_casts_ok env enc mem ty bs [] = True"
| "path_casts_ok env enc mem ty bs (s # rest) =
    (case path_step env enc mem ty bs s of
       Some (ty1, bs1, l1) \<Rightarrow>
         path_casts_ok env enc mem ty1 bs1 rest
         \<and> (case (s, ty) of
              (LVPath_ArrayCast dims', CoreTy_Array elemTy dims) \<Rightarrow>
                allocatable_dims dims' = allocatable_dims dims
                \<or> (case path_loc env enc mem ty1 bs1 rest of Some (_, _, PL_Mem _) \<Rightarrow> True | _ \<Rightarrow> False)
            | _ \<Rightarrow> True)
     | None \<Rightarrow> True)"

(* How the memory and the bytes change for an update at a location: an
   in-place update splices the new bytes into the value's bytes, and may
   change the memory anywhere except in the blocks reachable from the parts
   of the value other than the old target (blocks_agree on reach(v) minus
   reach(old target) is a convenient over-approximation of that, given
   val_owned); an update at a memory location is a write of the new bytes
   there, and the value's own bytes do not change. *)
definition update_at :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> CoreValue \<Rightarrow> MByte list
                         \<Rightarrow> CoreType \<Rightarrow> CoreValue \<Rightarrow> MByte list \<Rightarrow> PathLoc \<Rightarrow> MByte list \<Rightarrow> MByte list \<Rightarrow> bool" where
  "update_at env enc mem mem' ty v bs ty' vold bs0 l bs' bs'' =
    (case l of
       PL_Here off \<Rightarrow>
         blocks_agree mem mem' (reach_blocks env enc mem ty v bs - reach_blocks env enc mem ty' vold bs0)
         \<and> bs'' = splice off bs' bs
     | PL_Mem q \<Rightarrow> (\<exists>blk ofs. q = MP_Addr blk ofs) \<and> mem_write mem q bs' = Some mem' \<and> bs'' = bs)"

(* The block a memory write changes is the only block that differs. *)
lemma mem_write_agree_other:
  assumes "mem_write mem (MP_Addr blk ofs) new = Some mem'" and "blk \<notin> S"
  shows "blocks_agree mem mem' S"
  unfolding blocks_agree_def
proof
  fix b assume "b \<in> S"
  with assms(2) have "b \<noteq> blk" by auto
  thus "fmlookup (MM_Blocks mem') b = fmlookup (MM_Blocks mem) b" by (rule mem_write_lookup_other[OF assms(1)])
qed

(* An in-place step (offset o1, component of n1 bytes) composed with the
   rest of the path: the update seen from the component, the frame for the
   other components (whose blocks are disjoint from the component's), and
   the bytes of the whole after the update. Rv, Rc and Rold are the blocks
   reachable from the whole value, from the component, and from the old
   target. *)
lemma inplace_step_bytes_conj:
  fixes Rv Rc Rold :: "nat set"
  assumes sub_c: "Rc \<subseteq> Rv" and sub_old: "Rold \<subseteq> Rc"
    and comp: "o1 + n1 \<le> length bs" and bs1: "bs1 = slice o1 n1 bs"
    and lenbs': "length bs' = n'"
    and inside: "\<And>o2. l' = PL_Here o2 \<Longrightarrow> o2 + n' \<le> n1"
    and memq: "\<And>q. l' = PL_Mem q \<Longrightarrow> \<exists>blk ofs. q = MP_Addr blk ofs \<and> blk \<in> Rc"
    and upd: "case loc_compose (PL_Here o1) l' of
                PL_Here off \<Rightarrow> blocks_agree mem mem' (Rv - Rold) \<and> bs'' = splice off bs' bs
              | PL_Mem q \<Rightarrow> (\<exists>blk ofs. q = MP_Addr blk ofs) \<and> mem_write mem q bs' = Some mem' \<and> bs'' = bs"
    and bs1'': "bs1'' = (case l' of PL_Here o2 \<Rightarrow> splice o2 bs' bs1 | PL_Mem _ \<Rightarrow> bs1)"
  shows "(case l' of
           PL_Here o2 \<Rightarrow> blocks_agree mem mem' (Rc - Rold) \<and> bs1'' = splice o2 bs' bs1
         | PL_Mem q \<Rightarrow> (\<exists>blk ofs. q = MP_Addr blk ofs) \<and> mem_write mem q bs' = Some mem' \<and> bs1'' = bs1)
         \<and> (\<forall>S. S \<subseteq> Rv \<longrightarrow> S \<inter> Rc = {} \<longrightarrow> blocks_agree mem mem' S)
         \<and> length bs'' = length bs
         \<and> slice o1 n1 bs'' = bs1''
         \<and> (\<forall>ofs n. ofs + n \<le> o1 \<or> o1 + n1 \<le> ofs \<longrightarrow> ofs + n \<le> length bs \<longrightarrow> slice ofs n bs'' = slice ofs n bs)
         \<and> take o1 bs'' = take o1 bs"
proof (cases l')
  case (PL_Here o2)
  from upd have agree: "blocks_agree mem mem' (Rv - Rold)" and bs'': "bs'' = splice (o1 + o2) bs' bs"
    unfolding PL_Here by simp_all
  have in2: "o2 + n' \<le> n1" by (rule inside[OF PL_Here])
  have rng: "o1 + o2 + length bs' \<le> length bs" using in2 comp lenbs' by simp
  have c1: "blocks_agree mem mem' (Rc - Rold)" using blocks_agree_subset[OF agree] sub_c by blast
  have c2: "\<And>S. S \<subseteq> Rv \<Longrightarrow> S \<inter> Rc = {} \<Longrightarrow> blocks_agree mem mem' S"
  proof -
    fix S assume "S \<subseteq> Rv" "S \<inter> Rc = {}"
    hence "S \<subseteq> Rv - Rold" using sub_old by blast
    thus "blocks_agree mem mem' S" by (rule blocks_agree_subset[OF agree])
  qed
  have c3: "length bs'' = length bs" unfolding bs'' by (rule length_splice[OF rng])
  have c4: "slice o1 n1 bs'' = bs1''"
    unfolding bs'' bs1'' PL_Here PathLoc.case bs1
    by (subst slice_splice_inside) (use in2 comp lenbs' in simp_all)
  have c5: "\<And>ofs n. ofs + n \<le> o1 \<or> o1 + n1 \<le> ofs \<Longrightarrow> ofs + n \<le> length bs \<Longrightarrow> slice ofs n bs'' = slice ofs n bs"
  proof -
    fix ofs n assume "ofs + n \<le> o1 \<or> o1 + n1 \<le> ofs" and "ofs + n \<le> length bs"
    hence "ofs + n \<le> o1 + o2 \<or> o1 + o2 + length bs' \<le> ofs" using in2 lenbs' by auto
    thus "slice ofs n bs'' = slice ofs n bs" unfolding bs'' by (rule slice_splice_disjoint[OF _ rng])
  qed
  have c6: "take o1 bs'' = take o1 bs" unfolding bs'' by (rule take_splice_before) (use rng in simp_all)
  show ?thesis using c1 c2 c3 c4 c5 c6 bs1'' by (simp add: PL_Here)
next
  case (PL_Mem q)
  from upd obtain blk ofs where q: "q = MP_Addr blk ofs" and wr: "mem_write mem q bs' = Some mem'" and bs'': "bs'' = bs"
    unfolding PL_Mem by auto
  from memq[OF PL_Mem] q have blk: "blk \<in> Rc" by simp
  have c2: "\<And>S. S \<subseteq> Rv \<Longrightarrow> S \<inter> Rc = {} \<Longrightarrow> blocks_agree mem mem' S"
  proof -
    fix S assume "S \<subseteq> Rv" "S \<inter> Rc = {}"
    with blk have "blk \<notin> S" by blast
    thus "blocks_agree mem mem' S" by (rule mem_write_agree_other[OF wr[unfolded q]])
  qed
  show ?thesis using c2 q wr bs1'' bs'' bs1 by (simp add: PL_Mem)
qed

lemma inplace_step_bytes:
  fixes Rv Rc Rold :: "nat set"
  assumes sub_c: "Rc \<subseteq> Rv" and sub_old: "Rold \<subseteq> Rc"
    and comp: "o1 + n1 \<le> length bs" and bs1: "bs1 = slice o1 n1 bs"
    and lenbs': "length bs' = n'"
    and inside: "\<And>o2. l' = PL_Here o2 \<Longrightarrow> o2 + n' \<le> n1"
    and memq: "\<And>q. l' = PL_Mem q \<Longrightarrow> \<exists>blk ofs. q = MP_Addr blk ofs \<and> blk \<in> Rc"
    and upd: "case loc_compose (PL_Here o1) l' of
                PL_Here off \<Rightarrow> blocks_agree mem mem' (Rv - Rold) \<and> bs'' = splice off bs' bs
              | PL_Mem q \<Rightarrow> (\<exists>blk ofs. q = MP_Addr blk ofs) \<and> mem_write mem q bs' = Some mem' \<and> bs'' = bs"
    and bs1'': "bs1'' = (case l' of PL_Here o2 \<Rightarrow> splice o2 bs' bs1 | PL_Mem _ \<Rightarrow> bs1)"
  shows "case l' of
           PL_Here o2 \<Rightarrow> blocks_agree mem mem' (Rc - Rold) \<and> bs1'' = splice o2 bs' bs1
         | PL_Mem q \<Rightarrow> (\<exists>blk ofs. q = MP_Addr blk ofs) \<and> mem_write mem q bs' = Some mem' \<and> bs1'' = bs1"
    and "\<And>S. S \<subseteq> Rv \<Longrightarrow> S \<inter> Rc = {} \<Longrightarrow> blocks_agree mem mem' S"
    and "length bs'' = length bs"
    and "slice o1 n1 bs'' = bs1''"
    and "\<And>ofs n. ofs + n \<le> o1 \<or> o1 + n1 \<le> ofs \<Longrightarrow> ofs + n \<le> length bs \<Longrightarrow> slice ofs n bs'' = slice ofs n bs"
    and "take o1 bs'' = take o1 bs"
proof -
  note C = inplace_step_bytes_conj[OF assms]
  show "case l' of
           PL_Here o2 \<Rightarrow> blocks_agree mem mem' (Rc - Rold) \<and> bs1'' = splice o2 bs' bs1
         | PL_Mem q \<Rightarrow> (\<exists>blk ofs. q = MP_Addr blk ofs) \<and> mem_write mem q bs' = Some mem' \<and> bs1'' = bs1"
    by (rule conjunct1[OF C])
  show "\<And>S. S \<subseteq> Rv \<Longrightarrow> S \<inter> Rc = {} \<Longrightarrow> blocks_agree mem mem' S"
    using conjunct1[OF conjunct2[OF C]] by blast
  show "length bs'' = length bs" by (rule conjunct1[OF conjunct2[OF conjunct2[OF C]]])
  show "slice o1 n1 bs'' = bs1''" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF C]]]])
  show "\<And>ofs n. ofs + n \<le> o1 \<or> o1 + n1 \<le> ofs \<Longrightarrow> ofs + n \<le> length bs \<Longrightarrow> slice ofs n bs'' = slice ofs n bs"
    using conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF C]]]]] by blast
  show "take o1 bs'' = take o1 bs" by (rule conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF conjunct2[OF C]]]]])
qed

(* The block of a memory location is live with an unchanged length after
   a write anywhere. *)
lemma mem_write_block_length_any:
  assumes "mem_write mem (MP_Addr b off) new = Some mem'"
    and "fmlookup (MM_Blocks mem) blk = Some data"
  shows "\<exists>data'. fmlookup (MM_Blocks mem') blk = Some data' \<and> length data' = length data"
proof (cases "blk = b")
  case True
  from mem_write_block_length[OF assms(1) assms(2)[unfolded True]] show ?thesis unfolding True by blast
next
  case False
  from mem_write_lookup_other[OF assms(1) False] assms(2) show ?thesis by simp
qed

lemma path_update_sound:
  assumes enc: "valid_encoding enc"
  shows "rep_val env enc hmap mem ty v bs \<Longrightarrow> val_owned env enc mem ty v bs
    \<Longrightarrow> path_loc env enc mem ty bs path = Some (ty', bs0, l)
    \<Longrightarrow> path_casts_ok env enc mem ty bs path
    \<Longrightarrow> get_value_at_path v path = Inr vold
    \<Longrightarrow> update_value_at_path v path v' = Inr w
    \<Longrightarrow> rep_val env enc hmap mem' ty' v' bs'
    \<Longrightarrow> update_at env enc mem mem' ty v bs ty' vold bs0 l bs' bs''
    \<Longrightarrow> rep_val env enc hmap mem' ty w bs''"
proof (induction path arbitrary: ty v bs ty' bs0 l vold w bs'')
  case Nil
  hence e: "ty' = ty" "bs0 = bs" "l = PL_Here 0" "vold = v" "w = v'" by simp_all
  have len: "length bs' = gsz env enc ty" using rep_val_length[OF enc Nil.prems(7)] e(1) by simp
  have "bs'' = splice 0 bs' bs" using Nil.prems(8) unfolding update_at_def e by simp
  also have "\<dots> = bs'" using len rep_val_length[OF enc Nil.prems(1)] by (simp add: splice_all)
  finally show ?case using Nil.prems(7) e by simp
next
  case (Cons s rest)
  from path_loc_ConsD[OF Cons.prems(3)] obtain ty1 bs1 l1 l' where
    st: "path_step env enc mem ty bs s = Some (ty1, bs1, l1)"
    and pl: "path_loc env enc mem ty1 bs1 rest = Some (ty', bs0, l')" and l: "l = loc_compose l1 l'"
    by blast
  from Cons.prems(5) obtain v1 where sg: "step_get v s = Some v1" and g: "get_value_at_path v1 rest = Inr vold"
    by (auto simp: get_value_at_path_Cons)
  from Cons.prems(6) obtain v1' w1 where sg': "step_get v s = Some v1'"
    and u: "update_value_at_path v1' rest v' = Inr w1" and sp: "step_put v s w1 = Some w"
    by (auto simp: update_value_at_path_Cons)
  have v1': "v1' = v1" using sg sg' by simp
  note u = u[unfolded v1']
  have casts1: "path_casts_ok env enc mem ty1 bs1 rest" using Cons.prems(4) st by simp
  note rep1 = path_step_rep[OF enc Cons.prems(1) st sg]
  note reach1 = path_step_reach[OF enc Cons.prems(1) st sg]
  note own1 = val_owned_step[OF enc Cons.prems(1,2) st sg]
  note reach_old = path_loc_reach[OF enc rep1 pl g]
  have len': "length bs' = gsz env enc ty'" by (rule rep_val_length[OF enc Cons.prems(7)])
  have len1: "length bs1 = gsz env enc ty1" by (rule rep_val_length[OF enc rep1])
  have inside': "\<And>o2. l' = PL_Here o2 \<Longrightarrow> o2 + gsz env enc ty' \<le> gsz env enc ty1"
    using path_loc_Here[OF enc rep1 _ g] pl len1 by metis
  have memq': "\<And>q. l' = PL_Mem q \<Longrightarrow> \<exists>blk ofs. q = MP_Addr blk ofs \<and> blk \<in> reach_blocks env enc mem ty1 v1 bs1"
    using path_loc_Mem_reach[OF enc rep1 _ g] pl by metis
  define bs1'' where "bs1'' = (case l' of PL_Here o2 \<Rightarrow> splice o2 bs' bs1 | PL_Mem _ \<Rightarrow> bs1)"
  let ?Rv = "reach_blocks env enc mem ty v bs"
  let ?Rc = "reach_blocks env enc mem ty1 v1 bs1"
  let ?Rold = "reach_blocks env enc mem ty' vold bs0"
  \<comment> \<open>The in-place steps share the byte-level reasoning of inplace_step_bytes.\<close>
  have inplace: "\<And>o1. l1 = PL_Here o1 \<Longrightarrow>
       rep_val env enc hmap mem' ty1 w1 bs1''
       \<and> (\<forall>S. S \<subseteq> ?Rv \<longrightarrow> S \<inter> ?Rc = {} \<longrightarrow> blocks_agree mem mem' S)
       \<and> length bs'' = length bs
       \<and> slice o1 (gsz env enc ty1) bs'' = bs1''
       \<and> (\<forall>ofs n. ofs + n \<le> o1 \<or> o1 + gsz env enc ty1 \<le> ofs \<longrightarrow> ofs + n \<le> length bs \<longrightarrow> slice ofs n bs'' = slice ofs n bs)
       \<and> take o1 bs'' = take o1 bs"
  proof -
    fix o1 assume l1: "l1 = PL_Here o1"
    from path_step_Here[OF enc Cons.prems(1) st[unfolded l1] sg]
    have bs1: "bs1 = slice o1 (gsz env enc ty1) bs" and comp: "o1 + gsz env enc ty1 \<le> length bs" by auto
    have upd: "case loc_compose (PL_Here o1) l' of
                PL_Here off \<Rightarrow> blocks_agree mem mem' (?Rv - ?Rold) \<and> bs'' = splice off bs' bs
              | PL_Mem q \<Rightarrow> (\<exists>blk ofs. q = MP_Addr blk ofs) \<and> mem_write mem q bs' = Some mem' \<and> bs'' = bs"
      using Cons.prems(8) unfolding update_at_def l l1 by simp
    note B = inplace_step_bytes[OF reach1 reach_old comp bs1 len' inside' memq' upd bs1''_def]
    have IH_pre: "update_at env enc mem mem' ty1 v1 bs1 ty' vold bs0 l' bs' bs1''"
      unfolding update_at_def using B(1) by (cases l') simp_all
    note IH = Cons.IH[OF rep1 own1 pl casts1 g u Cons.prems(7) IH_pre]
    show "rep_val env enc hmap mem' ty1 w1 bs1''
       \<and> (\<forall>S. S \<subseteq> ?Rv \<longrightarrow> S \<inter> ?Rc = {} \<longrightarrow> blocks_agree mem mem' S)
       \<and> length bs'' = length bs
       \<and> slice o1 (gsz env enc ty1) bs'' = bs1''
       \<and> (\<forall>ofs n. ofs + n \<le> o1 \<or> o1 + gsz env enc ty1 \<le> ofs \<longrightarrow> ofs + n \<le> length bs \<longrightarrow> slice ofs n bs'' = slice ofs n bs)
       \<and> take o1 bs'' = take o1 bs"
      using IH B(2-6) by blast
  qed
  show ?case
  proof (cases s)
    case (LVPath_RecordProj f)
    from st sg obtain ftys fvs where ty: "ty = CoreTy_Record ftys" and v: "v = CV_Record fvs"
      unfolding LVPath_RecordProj by (cases ty; cases v) (auto split: option.splits)
    from st obtain fty where fty: "map_of ftys f = Some fty" and ty1: "ty1 = fty"
      and bs1: "bs1 = slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f) (gsz env enc fty) bs"
      and l1: "l1 = PL_Here (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys f)"
      unfolding LVPath_RecordProj ty by (auto split: option.splits)
    from sg have fv: "map_of fvs f = Some v1" unfolding LVPath_RecordProj v by simp
    from sp have w: "w = CV_Record (AList.update f w1 fvs)" unfolding LVPath_RecordProj v using fv by simp
    let ?fo = "field_offset env (enc_ptr_size enc) (\<lambda>_. 0) ftys"
    note I = inplace[OF l1]
    from rep_val_Record_E[OF Cons.prems(1)[unfolded v]] ty obtain
      dist: "distinct (map fst ftys)" and lenbs: "length bs = gsz env enc (CoreTy_Record ftys)"
      and flds: "list_all2 (\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
             rep_val env enc hmap mem fty v (slice (?fo n2) (gsz env enc fty) bs)) fvs ftys"
      by auto
    have lens: "length fvs = length ftys" using flds by (rule list_all2_lengthD)
    have names: "\<And>i. i < length ftys \<Longrightarrow> fst (fvs ! i) = fst (ftys ! i)"
    proof -
      fix i assume i: "i < length ftys"
      from list_all2_nthD[OF flds, of i] i lens show "fst (fvs ! i) = fst (ftys ! i)"
        by (cases "fvs ! i"; cases "ftys ! i") auto
    qed
    from map_of_SomeD[OF fv] obtain i where i: "i < length fvs" and fvi: "fvs ! i = (f, v1)"
      by (auto simp: in_set_conv_nth)
    have "fst (ftys ! i) = f" using names[of i] i lens fvi by simp
    hence ftyi: "ftys ! i = (f, fty)" using map_of_nth_distinct[OF dist, of i] i lens fty by simp
    have Rc: "fld_reach env enc mem ftys bs (zip fvs ftys ! i) = ?Rc"
      unfolding fld_reach_def using i lens fvi ftyi ty1 bs1 by (simp add: nth_zip)
    show ?thesis unfolding w ty
    proof (rule rep_val_Record_update[OF enc Cons.prems(1)[unfolded ty v] fty])
      show "length bs'' = length bs" using I by blast
    next
      show "rep_val env enc hmap mem' fty w1 (slice (?fo f) (gsz env enc fty) bs'')"
        using I unfolding ty1 by blast
    next
      fix j assume j: "j < length ftys" and nf: "fst (ftys ! j) \<noteq> f"
      have ji: "j \<noteq> i" using nf ftyi by auto
      obtain nj gty where ftyj: "ftys ! j = (nj, gty)" by (cases "ftys ! j")
      have nj: "fst (ftys ! j) = nj" using ftyj by simp
      obtain vj where fvj: "fvs ! j = (nj, vj)" using names[OF j] nj by (cases "fvs ! j") simp
      have njf: "nj \<noteq> f" using nf nj by simp
      \<comment> \<open>Field j's bytes are unchanged.\<close>
      have moj: "map_of ftys nj = Some gty"
        unfolding map_of_eq_Some_iff[OF dist] using nth_mem[OF j] ftyj by simp
      have bnd: "?fo nj + gsz env enc gty \<le> length bs"
        using field_offset_bound[OF moj, of env "enc_ptr_size enc" "\<lambda>_. 0"] lenbs by simp
      have disj: "?fo nj + gsz env enc gty \<le> ?fo f \<or> ?fo f + gsz env enc fty \<le> ?fo nj"
        using field_offset_disjoint[OF dist j i[unfolded lens] ji, where env = env and P = "enc_ptr_size enc" and sz = "\<lambda>_. 0"]
              ftyi ftyj by simp
      have same: "slice (?fo nj) (gsz env enc gty) bs'' = slice (?fo nj) (gsz env enc gty) bs"
        using I disj bnd unfolding ty1 by blast
      \<comment> \<open>... and its blocks are untouched.\<close>
      have repj: "rep_val env enc hmap mem gty vj (slice (?fo nj) (gsz env enc gty) bs)"
        using list_all2_nthD[OF flds, of j] j lens fvj ftyj by simp
      have Rj: "fld_reach env enc mem ftys bs (zip fvs ftys ! j) = reach_blocks env enc mem gty vj (slice (?fo nj) (gsz env enc gty) bs)"
        unfolding fld_reach_def using j lens fvj ftyj by (simp add: nth_zip)
      have sub: "reach_blocks env enc mem gty vj (slice (?fo nj) (gsz env enc gty) bs) \<subseteq> ?Rv"
        unfolding ty v by (rule reach_blocks_Record_fld_nth[OF _ j fvj ftyj]) (use j lens in simp)
      have disjR0: "fld_reach env enc mem ftys bs (zip fvs ftys ! j) \<inter> fld_reach env enc mem ftys bs (zip fvs ftys ! i) = {}"
        using conjunct1[OF Cons.prems(2)[unfolded ty v val_owned.simps CoreType.case], rule_format, of j i] j i lens ji
        by simp
      have disjR: "reach_blocks env enc mem gty vj (slice (?fo nj) (gsz env enc gty) bs) \<inter> ?Rc = {}"
        using disjR0 unfolding Rj Rc .
      have "blocks_agree mem mem' (reach_blocks env enc mem gty vj (slice (?fo nj) (gsz env enc gty) bs))"
        using I sub disjR by blast
      from rep_val_frame[OF enc repj this] show
        "rep_val env enc hmap mem' (snd (ftys ! j)) (snd (fvs ! j)) (slice (?fo (fst (ftys ! j))) (gsz env enc (snd (ftys ! j))) bs'')"
        using ftyj fvj same by simp
    qed
  next
    case (LVPath_VariantProj c)
    from sg obtain ctor payload where v: "v = CV_Variant ctor payload"
      unfolding LVPath_VariantProj by (cases v) auto
    from sg have c: "ctor = c" and v1: "v1 = payload" unfolding LVPath_VariantProj v by (auto split: if_splits)
    from st obtain dt args where ty: "ty = CoreTy_Datatype dt args" unfolding LVPath_VariantProj by (cases ty) auto
    from st obtain tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) c = Some (dt, tyvars, payloadTy)"
      and ty1: "ty1 = apply_subst (fmap_of_list (zip tyvars args)) payloadTy"
      and l1: "l1 = PL_Here (tag_size env dt)"
      unfolding LVPath_VariantProj ty by (auto split: option.splits if_splits)
    from sp have w: "w = CV_Variant ctor w1" unfolding LVPath_VariantProj v using c by simp
    note I = inplace[OF l1]
    show ?thesis unfolding w ty
    proof (rule rep_val_Variant_update[OF Cons.prems(1)[unfolded ty v] lk[unfolded c[symmetric]]])
      show "length bs'' = length bs" using I by blast
      show "take (tag_size env dt) bs'' = take (tag_size env dt) bs" using I by blast
      show "rep_val env enc hmap mem' (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) w1
              (slice (tag_size env dt) (gsz env enc (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)) bs'')"
        using I unfolding ty1 by blast
    qed
  next
    case (LVPath_ArrayProj idx)
    from st sg obtain elemTy dims sizes elems where ty: "ty = CoreTy_Array elemTy dims"
      and v: "v = CV_Array sizes elems"
      unfolding LVPath_ArrayProj by (cases ty; cases v) (auto split: option.splits)
    from sg have lk: "fmlookup elems idx = Some v1" unfolding LVPath_ArrayProj v by simp
    from sp have w: "w = CV_Array sizes (fmupd idx w1 elems)" unfolding LVPath_ArrayProj v using lk by simp
    let ?esz = "gsz env enc elemTy"
    show ?thesis
    proof (cases "dims_all_fixed dims")
      case True
      note E = rep_val_FixedArray_E[OF Cons.prems(1)[unfolded ty v] True]
      from st have ty1: "ty1 = elemTy"
        and l1: "l1 = PL_Here (elem_offset ?esz (dims_sizes dims) idx)"
        and inb: "index_in_bounds (dims_sizes dims) idx"
        unfolding LVPath_ArrayProj ty using True by (auto split: if_splits)
      note I = inplace[OF l1]
      show ?thesis unfolding w ty
      proof (rule rep_val_FixedArray_update[OF Cons.prems(1)[unfolded ty v] True lk])
        show "length bs'' = length bs" using I by blast
        show "rep_val env enc hmap mem' elemTy w1 (slice (elem_offset ?esz sizes idx) ?esz bs'')"
          using I unfolding ty1 E(1) by blast
      next
        fix idx' vj assume ne: "idx' \<noteq> idx" and lkj: "fmlookup elems idx' = Some vj"
        have inb': "index_in_bounds sizes idx'" using lkj E(2) by (metis fmdomI fset_of_list_elem in_all_indices_iff)
        have bnd: "elem_offset ?esz sizes idx' + ?esz \<le> length bs"
          using elem_offset_bound[OF inb', of ?esz] E(3) by simp
        have disj: "elem_offset ?esz sizes idx' + ?esz \<le> elem_offset ?esz sizes idx
                    \<or> elem_offset ?esz sizes idx + ?esz \<le> elem_offset ?esz sizes idx'"
          using elem_offset_disjoint[OF inb' inb[unfolded E(1)[symmetric]] ne] .
        have same: "slice (elem_offset ?esz sizes idx') ?esz bs'' = slice (elem_offset ?esz sizes idx') ?esz bs"
          using I disj bnd unfolding ty1 E(1) by blast
        have repj: "rep_val env enc hmap mem elemTy vj (slice (elem_offset ?esz sizes idx') ?esz bs)" by (rule E(4)[OF lkj])
        have sub: "reach_blocks env enc mem elemTy vj (slice (elem_offset ?esz sizes idx') ?esz bs) \<subseteq> ?Rv"
          unfolding ty v by (rule reach_blocks_FixedArray_elem[OF True lkj])
        have bs1: "bs1 = slice (elem_offset ?esz sizes idx) ?esz bs"
          using conjunct1[OF path_step_Here[OF enc Cons.prems(1) st[unfolded l1] sg]] unfolding ty1 E(1) .
        have disjR: "reach_blocks env enc mem elemTy vj (slice (elem_offset ?esz sizes idx') ?esz bs) \<inter> ?Rc = {}"
          using conjunct1[OF Cons.prems(2)[unfolded ty v val_owned.simps CoreType.case if_P[OF True]], rule_format, of idx' vj idx v1]
                lkj lk ne unfolding ty1 bs1 by simp
        have "blocks_agree mem mem' (reach_blocks env enc mem elemTy vj (slice (elem_offset ?esz sizes idx') ?esz bs))"
          using I sub disjR by blast
        from rep_val_frame[OF enc repj this] show
          "rep_val env enc hmap mem' elemTy vj (slice (elem_offset ?esz sizes idx') ?esz bs'')"
          using same by simp
      qed
    next
      case False
      \<comment> \<open>The descriptor step: the component lives in the data block.\<close>
      from rep_val_Desc_E[OF Cons.prems(1)[unfolded ty v] False] obtain pd where
        D: "sizes_match_dims sizes dims" "fmdom elems = fset_of_list (all_indices sizes)"
           "sizes_valid sizes" "sizes_count sizes < u64_max" "?esz * sizes_count sizes < u64_max"
           "length bs = desc_size (enc_ptr_size enc) (length dims)" "desc_dims_ok enc sizes bs"
           "take (enc_ptr_size enc) bs = encode_ptr enc pd"
        and empty: "sizes_count sizes = 0 \<Longrightarrow> empty_data_ok mem (allocatable_dims dims) pd"
        and nonempty: "sizes_count sizes \<noteq> 0 \<Longrightarrow> \<exists>data. data_region_ok mem (allocatable_dims dims) pd
                           (?esz * sizes_count sizes) data
                           \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                                rep_val env enc hmap mem elemTy v (slice (elem_offset ?esz sizes idx) ?esz data))"
        by blast
      have inb: "index_in_bounds sizes idx" using lk D(2) by (metis fmdomI fset_of_list_elem in_all_indices_iff)
      have cnt: "sizes_count sizes \<noteq> 0" using index_in_bounds_count_pos[OF inb] by simp
      have ptr: "desc_ptr enc bs = Some pd" by (rule desc_ptr_of_take[OF enc D(8)])
      have szs: "desc_sizes enc (length dims) bs = Some sizes"
        using desc_sizes_of_dims_ok[OF enc D(3) D(7)] sizes_match_dims_length[OF D(1)] by simp
      let ?eo = "elem_offset ?esz sizes idx"
      let ?n = "?esz * sizes_count sizes"
      from st have ty1: "ty1 = elemTy"
        and rd1: "mem_read mem (ptr_off pd ?eo) ?esz = Some bs1"
        and l1: "l1 = PL_Mem (ptr_off pd ?eo)"
        unfolding LVPath_ArrayProj ty using False ptr szs inb by (auto split: option.splits if_splits)
      from nonempty[OF cnt] obtain data where
        reg: "data_region_ok mem (allocatable_dims dims) pd ?n data"
        and els: "\<And>idx v. fmlookup elems idx = Some v \<Longrightarrow> rep_val env enc hmap mem elemTy v (slice (elem_offset ?esz sizes idx) ?esz data)"
        by blast
      have rd: "mem_read mem pd ?n = Some data" using reg by (simp add: data_region_ok_def)
      from rd obtain blk od where pd: "pd = MP_Addr blk od" by (cases pd) (auto simp: mem_read_def)
      have lendata: "length data = ?n" using mem_read_Some_block[OF rd] by (auto simp: length_slice_le)
      have bs1: "bs1 = slice ?eo ?esz data" using mem_read_sub[OF rd elem_offset_bound[OF inb]] rd1 by simp
      have dec: "decode_ptr enc (take (enc_ptr_size enc) bs) = Some (MP_Addr blk od)"
        unfolding D(8) pd by (rule decode_ptr_encode_ptr[OF enc])
      \<comment> \<open>The ownership facts of the descriptor.\<close>
      have own: "(\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow> blk \<notin> reach_blocks env enc mem elemTy v (slice (elem_offset ?esz sizes idx) ?esz data))
                 \<and> (\<forall>idx1 v1 idx2 v2. fmlookup elems idx1 = Some v1 \<longrightarrow> fmlookup elems idx2 = Some v2 \<longrightarrow> idx1 \<noteq> idx2 \<longrightarrow>
                      reach_blocks env enc mem elemTy v1 (slice (elem_offset ?esz sizes idx1) ?esz data)
                      \<inter> reach_blocks env enc mem elemTy v2 (slice (elem_offset ?esz sizes idx2) ?esz data) = {})"
        using Cons.prems(2) unfolding ty v val_owned.simps CoreType.case using False dec cnt rd[unfolded pd] by simp
      have blk_notc: "blk \<notin> ?Rc" using own lk unfolding ty1 bs1 by blast
      have eo_bnd: "?eo + ?esz \<le> ?n" by (rule elem_offset_bound[OF inb])
      \<comment> \<open>After the update: the data region holds data', the descriptor bytes are unchanged.\<close>
      have "\<exists>data'. bs'' = bs \<and> data_region_ok mem' (allocatable_dims dims) pd ?n data'
             \<and> rep_val env enc hmap mem' elemTy w1 (slice ?eo ?esz data')
             \<and> (\<forall>idx' v. idx' \<noteq> idx \<longrightarrow> fmlookup elems idx' = Some v \<longrightarrow>
                  slice (elem_offset ?esz sizes idx') ?esz data' = slice (elem_offset ?esz sizes idx') ?esz data
                  \<and> blocks_agree mem mem' (reach_blocks env enc mem elemTy v (slice (elem_offset ?esz sizes idx') ?esz data)))"
      proof (cases l')
        case (PL_Here o2)
        with l l1 have lm: "l = PL_Mem (ptr_off pd (?eo + o2))" by (simp add: ptr_off_add)
        from Cons.prems(8) have wr: "mem_write mem (ptr_off pd (?eo + o2)) bs' = Some mem'" and bs'': "bs'' = bs"
          unfolding update_at_def lm by auto
        have in2: "o2 + gsz env enc ty' \<le> ?esz" using inside'[OF PL_Here] unfolding ty1 .
        have rng: "?eo + o2 + length bs' \<le> ?n" using in2 eo_bnd len' by simp
        \<comment> \<open>The component's update, seen from the component: in place, the data block untouched.\<close>
        have agree_c: "blocks_agree mem mem' (?Rc - ?Rold)"
          by (rule mem_write_agree_other[OF wr[unfolded pd ptr_off.simps]]) (use blk_notc in blast)
        have IH_pre: "update_at env enc mem mem' ty1 v1 bs1 ty' vold bs0 l' bs' bs1''"
          unfolding update_at_def PL_Here bs1''_def using agree_c by simp
        note IH = Cons.IH[OF rep1 own1 pl casts1 g u Cons.prems(7) IH_pre]
        have data': "mem_read mem' pd ?n = Some (splice (?eo + o2) bs' data)"
          by (rule mem_read_after_write_sub[OF rd rng wr])
        have reg': "data_region_ok mem' (allocatable_dims dims) pd ?n (splice (?eo + o2) bs' data)"
        proof (cases "allocatable_dims dims")
          case True
          with reg obtain blk' where pd0: "pd = MP_Addr blk' 0" and blk': "fmlookup (MM_Blocks mem) blk' = Some data"
            by (auto simp: data_region_ok_def)
          from mem_write_block_length[OF wr[unfolded pd0 ptr_off.simps] blk'] obtain d' where
            "fmlookup (MM_Blocks mem') blk' = Some d'" "d' = splice (0 + (?eo + o2)) bs' data" by blast
          thus ?thesis using data' pd0 by (simp add: data_region_ok_def)
        next
          case False
          thus ?thesis using data' by (simp add: data_region_ok_def)
        qed
        have newc: "rep_val env enc hmap mem' elemTy w1 (slice ?eo ?esz (splice (?eo + o2) bs' data))"
          using IH unfolding ty1 bs1''_def PL_Here PathLoc.case bs1
          by (subst slice_splice_inside) (use in2 eo_bnd lendata len' in simp_all)
        have sibs: "\<And>idx' v. idx' \<noteq> idx \<Longrightarrow> fmlookup elems idx' = Some v \<Longrightarrow>
                  slice (elem_offset ?esz sizes idx') ?esz (splice (?eo + o2) bs' data) = slice (elem_offset ?esz sizes idx') ?esz data
                  \<and> blocks_agree mem mem' (reach_blocks env enc mem elemTy v (slice (elem_offset ?esz sizes idx') ?esz data))"
        proof -
          fix idx' vj assume ne: "idx' \<noteq> idx" and lkj: "fmlookup elems idx' = Some vj"
          have inb': "index_in_bounds sizes idx'" using lkj D(2) by (metis fmdomI fset_of_list_elem in_all_indices_iff)
          have disj: "elem_offset ?esz sizes idx' + ?esz \<le> ?eo \<or> ?eo + ?esz \<le> elem_offset ?esz sizes idx'"
            using elem_offset_disjoint[OF inb' inb ne] .
          have "slice (elem_offset ?esz sizes idx') ?esz (splice (?eo + o2) bs' data) = slice (elem_offset ?esz sizes idx') ?esz data"
            using disj in2 len' by (intro slice_splice_disjoint) (use rng lendata in auto)
          moreover have "blocks_agree mem mem' (reach_blocks env enc mem elemTy vj (slice (elem_offset ?esz sizes idx') ?esz data))"
            by (rule mem_write_agree_other[OF wr[unfolded pd ptr_off.simps]]) (use own lkj in blast)
          ultimately show "slice (elem_offset ?esz sizes idx') ?esz (splice (?eo + o2) bs' data) = slice (elem_offset ?esz sizes idx') ?esz data
                  \<and> blocks_agree mem mem' (reach_blocks env enc mem elemTy vj (slice (elem_offset ?esz sizes idx') ?esz data))" ..
        qed
        show ?thesis using bs'' reg' newc sibs by blast
      next
        case (PL_Mem q)
        with l l1 have lm: "l = PL_Mem q" by simp
        from Cons.prems(8) obtain qb qo where q: "q = MP_Addr qb qo"
          and wr: "mem_write mem q bs' = Some mem'" and bs'': "bs'' = bs"
          unfolding update_at_def lm by auto
        from memq'[OF PL_Mem] q have qb: "qb \<in> ?Rc" by simp
        have qb_blk: "qb \<noteq> blk" using qb blk_notc by auto
        have IH_pre: "update_at env enc mem mem' ty1 v1 bs1 ty' vold bs0 l' bs' bs1''"
          unfolding update_at_def PL_Mem bs1''_def using q wr by simp
        note IH = Cons.IH[OF rep1 own1 pl casts1 g u Cons.prems(7) IH_pre]
        have data': "mem_read mem' pd ?n = Some data"
          using mem_read_write_other_block[OF wr[unfolded q] qb_blk[symmetric]] rd unfolding pd by simp
        have reg': "data_region_ok mem' (allocatable_dims dims) pd ?n data"
          using reg data' mem_write_lookup_other[OF wr[unfolded q] qb_blk[symmetric]] unfolding pd by (auto simp: data_region_ok_def)
        have newc: "rep_val env enc hmap mem' elemTy w1 (slice ?eo ?esz data)"
          using IH unfolding ty1 bs1''_def PL_Mem PathLoc.case bs1 .
        have sibs: "\<And>idx' v. idx' \<noteq> idx \<Longrightarrow> fmlookup elems idx' = Some v \<Longrightarrow>
                  slice (elem_offset ?esz sizes idx') ?esz data = slice (elem_offset ?esz sizes idx') ?esz data
                  \<and> blocks_agree mem mem' (reach_blocks env enc mem elemTy v (slice (elem_offset ?esz sizes idx') ?esz data))"
        proof -
          fix idx' vj assume ne: "idx' \<noteq> idx" and lkj: "fmlookup elems idx' = Some vj"
          have "qb \<notin> reach_blocks env enc mem elemTy vj (slice (elem_offset ?esz sizes idx') ?esz data)"
            using own lkj lk ne qb unfolding ty1 bs1 by blast
          thus "slice (elem_offset ?esz sizes idx') ?esz data = slice (elem_offset ?esz sizes idx') ?esz data
                  \<and> blocks_agree mem mem' (reach_blocks env enc mem elemTy vj (slice (elem_offset ?esz sizes idx') ?esz data))"
            using mem_write_agree_other[OF wr[unfolded q]] by blast
        qed
        show ?thesis using bs'' reg' newc sibs by blast
      qed
      then obtain data' where bs'': "bs'' = bs" and reg': "data_region_ok mem' (allocatable_dims dims) pd ?n data'"
        and newc: "rep_val env enc hmap mem' elemTy w1 (slice ?eo ?esz data')"
        and sibs: "\<And>idx' v. idx' \<noteq> idx \<Longrightarrow> fmlookup elems idx' = Some v \<Longrightarrow>
                  slice (elem_offset ?esz sizes idx') ?esz data' = slice (elem_offset ?esz sizes idx') ?esz data
                  \<and> blocks_agree mem mem' (reach_blocks env enc mem elemTy v (slice (elem_offset ?esz sizes idx') ?esz data))"
        by blast
      show ?thesis unfolding w ty bs''
      proof (rule rep_val_Desc_update[OF Cons.prems(1)[unfolded ty v] False D(8) lk reg' _ newc])
        fix idx' vj assume ne: "idx' \<noteq> idx" and lkj: "fmlookup elems idx' = Some vj"
        from sibs[OF ne lkj] rep_val_frame[OF enc els[OF lkj]] show
          "rep_val env enc hmap mem' elemTy vj (slice (elem_offset ?esz sizes idx') ?esz data')" by simp
      qed
    qed
  next
    case (LVPath_ArrayCast dims')
    from st sg obtain elemTy dims sizes elems where ty: "ty = CoreTy_Array elemTy dims"
      and v: "v = CV_Array sizes elems"
      unfolding LVPath_ArrayCast by (cases ty; cases v) (auto split: option.splits)
    from sg have match: "sizes_match_dims sizes dims'" and v1: "v1 = v"
      unfolding LVPath_ArrayCast v by (auto split: if_splits)
    from st have cat: "dims_all_fixed dims' = dims_all_fixed dims"
      and alloc: "allocatable_dims dims' \<longrightarrow> allocatable_dims dims"
      and ty1: "ty1 = CoreTy_Array elemTy dims'" and bs1: "bs1 = bs" and l1: "l1 = PL_Here 0"
      unfolding LVPath_ArrayCast ty by (auto split: if_splits)
    from sp obtain elems' where w1: "w1 = CV_Array sizes elems'" and w: "w = w1"
      unfolding LVPath_ArrayCast v using match by (auto split: CoreValue.splits if_splits)
    note I = inplace[OF l1]
    have lenbs: "length bs = gsz env enc ty1" using len1 unfolding bs1 .
    have I1: "rep_val env enc hmap mem' ty1 w1 bs1''" by (rule conjunct1[OF I])
    have I3: "length bs'' = length bs" by (rule conjunct1[OF conjunct2[OF conjunct2[OF I]]])
    have I4: "slice 0 (gsz env enc ty1) bs'' = bs1''" by (rule conjunct1[OF conjunct2[OF conjunct2[OF conjunct2[OF I]]]])
    have "bs1'' = bs''" using I4 I3 lenbs by (simp add: slice_0)
    hence repw: "rep_val env enc hmap mem' ty1 w1 bs''" using I1 by simp
    have match0: "sizes_match_dims sizes dims" using Cons.prems(1) unfolding ty v by simp
    have casts: "allocatable_dims dims' = allocatable_dims dims
                 \<or> (case path_loc env enc mem ty1 bs1 rest of Some (_, _, PL_Mem _) \<Rightarrow> True | _ \<Rightarrow> False)"
      using Cons.prems(4) st unfolding LVPath_ArrayCast ty by simp
    show ?thesis
    proof (cases "allocatable_dims dims \<and> \<not> allocatable_dims dims'")
      case False
      hence "allocatable_dims dims \<longrightarrow> allocatable_dims dims'" by blast
      from rep_val_Array_weaken[OF repw[unfolded ty1 w1] match0 cat[symmetric] this] show ?thesis unfolding w w1 ty .
    next
      case True
      \<comment> \<open>The cast drops ownership: the update must have gone into the heap data.\<close>
      have memloc: "case path_loc env enc mem ty1 bs1 rest of Some (_, _, PL_Mem _) \<Rightarrow> True | _ \<Rightarrow> False"
        using casts True by blast
      obtain q where l': "l' = PL_Mem q"
      proof (cases l')
        case (PL_Here o2)
        with memloc show ?thesis unfolding pl by simp
      next
        case (PL_Mem q)
        show ?thesis by (rule that[OF PL_Mem])
      qed
      with l l1 have lm: "l = PL_Mem q" by simp
      from Cons.prems(8) obtain qb qo where q: "q = MP_Addr qb qo"
        and wr: "mem_write mem q bs' = Some mem'" and bs'': "bs'' = bs"
        unfolding update_at_def lm by auto
      have nf: "\<not> dims_all_fixed dims"
        using True by (auto simp: allocatable_dims_def dims_all_fixed_def list_ex_iff list_all_iff
                            intro!: bexI[where x = CoreDim_Allocatable])
      from rep_val_Desc_E[OF Cons.prems(1)[unfolded ty v] nf] obtain pd where
        "sizes_match_dims sizes dims" "fmdom elems = fset_of_list (all_indices sizes)"
        "sizes_valid sizes" "sizes_count sizes < u64_max" "gsz env enc elemTy * sizes_count sizes < u64_max"
        "length bs = desc_size (enc_ptr_size enc) (length dims)" "desc_dims_ok enc sizes bs"
        and D8: "take (enc_ptr_size enc) bs = encode_ptr enc pd"
        and empty: "sizes_count sizes = 0 \<Longrightarrow> empty_data_ok mem (allocatable_dims dims) pd"
        and nonempty: "sizes_count sizes \<noteq> 0 \<Longrightarrow> \<exists>data. data_region_ok mem (allocatable_dims dims) pd
                           (gsz env enc elemTy * sizes_count sizes) data
                           \<and> (\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                                rep_val env enc hmap mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data))"
        by blast
      show ?thesis unfolding w w1 ty bs''
      proof (rule rep_val_Array_strengthen[OF repw[unfolded ty1 w1 bs''] match0 cat nf])
        assume "allocatable_dims dims" "\<not> allocatable_dims dims'"
        show "\<forall>p. take (enc_ptr_size enc) bs = encode_ptr enc p \<longrightarrow>
            (if sizes_count sizes = 0 then p = MP_Null \<or> (\<exists>blk. p = MP_Addr blk 0)
             else (\<exists>blk data. p = MP_Addr blk 0 \<and> fmlookup (MM_Blocks mem') blk = Some data
                     \<and> length data = gsz env enc elemTy * sizes_count sizes))"
        proof (intro allI impI)
          fix p assume h: "take (enc_ptr_size enc) bs = encode_ptr enc p"
          have eq: "encode_ptr enc p = encode_ptr enc pd" by (rule trans[OF h[symmetric] D8])
          have "Some p = decode_ptr enc (encode_ptr enc pd)"
            using decode_ptr_encode_ptr[OF enc, of p] unfolding eq by (rule sym)
          hence p: "p = pd" unfolding decode_ptr_encode_ptr[OF enc] by simp
          show "if sizes_count sizes = 0 then p = MP_Null \<or> (\<exists>blk. p = MP_Addr blk 0)
                else (\<exists>blk data. p = MP_Addr blk 0 \<and> fmlookup (MM_Blocks mem') blk = Some data
                        \<and> length data = gsz env enc elemTy * sizes_count sizes)"
          proof (cases "sizes_count sizes = 0")
            case z: True
            from empty[OF z] \<open>allocatable_dims dims\<close> show ?thesis unfolding p using z by (auto simp: empty_data_ok_def)
          next
            case nz: False
            from nonempty[OF nz] obtain data where
              reg: "data_region_ok mem (allocatable_dims dims) pd (gsz env enc elemTy * sizes_count sizes) data"
              and "\<forall>idx v. fmlookup elems idx = Some v \<longrightarrow>
                     rep_val env enc hmap mem elemTy v (slice (elem_offset (gsz env enc elemTy) sizes idx) (gsz env enc elemTy) data)"
              by blast
            have rd: "mem_read mem pd (gsz env enc elemTy * sizes_count sizes) = Some data"
              using reg by (simp add: data_region_ok_def)
            obtain blk where pd0: "pd = MP_Addr blk 0" and blk: "fmlookup (MM_Blocks mem) blk = Some data"
              using reg \<open>allocatable_dims dims\<close> unfolding data_region_ok_def by blast
            have lendata: "length data = gsz env enc elemTy * sizes_count sizes"
              using mem_read_Some_block[OF rd] by (auto simp: length_slice_le)
            from mem_write_block_length_any[OF wr[unfolded q] blk] obtain data' where
              "fmlookup (MM_Blocks mem') blk = Some data'" "length data' = length data" by blast
            thus ?thesis unfolding p pd0 using nz lendata by auto
          qed
        qed
      qed
    qed
  qed
qed

end

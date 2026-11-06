theory RepValDefault
  imports RepVal DatatypeAcyclic "../core/CoreTyEnvWellFormed"
begin

(* ========================================================================== *)
(* Default values are all-zero bytes (minic/DESIGN.md, risk 9)                 *)
(* ========================================================================== *)

(* default_value (CoreInterp.thy) is represented, at every type, by all-zero
   bytes: false, 0, null, the first constructor (tag 0) with a zero payload,
   a fixed array of zero elements, an empty descriptor (null, sizes 0). *)


section \<open>Hypotheses on the datatype tables\<close>

(* What the default-value lemma needs of the tables: constructor payloads
   are well-kinded in their type variables (so that type_size of a
   substituted payload is type_size of the payload at the argument sizes),
   the type variables are distinct, TE_DataCtorsByType agrees with
   TE_DataCtors, and there are no abstract types (the module is normalized).
   tyenv_well_formed of a normalized module gives all of it. *)
definition dt_tables_ok :: "CoreTyEnv \<Rightarrow> bool" where
  "dt_tables_ok env =
    (tyenv_payloads_well_kinded env \<and> tyenv_ctor_tyvars_distinct env
     \<and> tyenv_ctors_by_type_consistent env \<and> TE_AbstractTypes env = {||})"

lemma dt_tables_ok_of_wf:
  "tyenv_well_formed env \<Longrightarrow> TE_AbstractTypes env = {||} \<Longrightarrow> dt_tables_ok env"
  by (simp add: dt_tables_ok_def tyenv_well_formed_def)

(* A type without the mathematical types (which have no representation). *)
fun math_free :: "CoreType \<Rightarrow> bool" where
  "math_free CoreTy_MathInt = False"
| "math_free CoreTy_MathReal = False"
| "math_free (CoreTy_Record flds) = list_all (math_free \<circ> snd) flds"
| "math_free (CoreTy_Array elemTy dims) = math_free elemTy"
| "math_free (CoreTy_Datatype dt args) = list_all math_free args"
| "math_free _ = True"

(* The constructor payloads are math-free (after ghost erasure every
   remaining datatype is a runtime one). *)
definition tables_math_free :: "CoreTyEnv \<Rightarrow> bool" where
  "tables_math_free env =
    (\<forall>ctor dt tyvars payloadTy. fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)
       \<longrightarrow> math_free payloadTy)"

lemma math_free_subst:
  assumes "math_free ty" and "\<And>v t. fmlookup subst v = Some t \<Longrightarrow> math_free t"
  shows "math_free (apply_subst subst ty)"
  using assms
proof (induction ty)
  case (CoreTy_Var v)
  then show ?case by (cases "fmlookup subst v") auto
qed (auto simp: list_all_iff)

lemma math_free_subst_zip:
  assumes "math_free ty" and "list_all math_free args"
  shows "math_free (apply_subst (fmap_of_list (zip tyvars args)) ty)"
proof (rule math_free_subst[OF assms(1)])
  fix v t assume "fmlookup (fmap_of_list (zip tyvars args)) v = Some t"
  hence "(v, t) \<in> set (zip tyvars args)" by (simp add: fmlookup_of_list map_of_SomeD)
  hence "t \<in> set args" by (rule set_zip_rightD)
  with assms(2) show "math_free t" by (simp add: list_all_iff)
qed


section \<open>Helpers\<close>

lemma enc_encode_zero:
  "valid_encoding enc \<Longrightarrow> enc_encode enc s b 0 = replicate (byte_width b) 0"
  by (simp add: valid_encoding_def)

lemma encode_val_zero:
  "valid_encoding enc \<Longrightarrow> encode_val enc (MV_Int s b 0) = replicate (byte_width b) (MB_Byte 0)"
  by (simp add: enc_encode_zero)

lemma int_fits_zero: "int_fits s b 0"
  by (cases s; cases b; simp)

lemma int_in_range_zero: "int_in_range (int_range s b) 0"
  using int_fits_zero[of s b] by simp

lemma fixed_dim_sizes_dims_sizes:
  "dims_all_fixed dims \<Longrightarrow> fixed_dim_sizes dims = dims_sizes dims"
  by (induction dims rule: fixed_dim_sizes.induct) (simp_all add: dims_all_fixed_def dims_sizes_def)

lemma sizes_match_dims_fixed_I:
  "dims_all_fixed dims \<Longrightarrow> sizes_match_dims (dims_sizes dims) dims"
proof (induction dims)
  case (Cons a dims)
  then show ?case by (cases a) (auto simp: dims_all_fixed_def dims_sizes_def)
qed (simp add: dims_sizes_def)

(* Uniform dims are all fixed or none is. *)
lemma dims_uniform_cases:
  "dims_uniform dims \<Longrightarrow> dims_all_fixed dims \<or> list_all (\<lambda>d. dim_category d \<noteq> DimCat_Fixed) dims"
proof (induction dims rule: dims_uniform.induct)
  case (3 d1 d2 ds)
  then show ?case by (cases "dim_category d2 = DimCat_Fixed") (auto simp: dims_all_fixed_def)
qed (auto simp: dims_all_fixed_def)

lemma sizes_match_dims_zero:
  "list_all (\<lambda>d. dim_category d \<noteq> DimCat_Fixed) dims \<Longrightarrow> sizes_match_dims (replicate (length dims) 0) dims"
proof (induction dims)
  case (Cons a dims)
  then show ?case by (cases a) auto
qed simp

lemma sizes_valid_zero: "sizes_valid (replicate d 0)"
  by (simp add: sizes_valid_def list_all_iff)

lemma sizes_count_zero: "d > 0 \<Longrightarrow> sizes_count (replicate d 0) = 0"
  by (cases d) (simp_all add: sizes_count_def)

lemma index_in_bounds_zero_dim: "index_in_bounds (0 # ns) idx \<Longrightarrow> False"
proof -
  assume a: "index_in_bounds (0 # ns) idx"
  have b: "\<exists>i is. idx = i # is \<and> 0 \<le> i \<and> i < 0 \<and> index_in_bounds ns is"
    using a index_in_bounds_Cons[of 0 ns idx] by (rule iffD1[rotated])
  from b obtain i where "\<exists>is. idx = i # is \<and> 0 \<le> i \<and> i < 0 \<and> index_in_bounds ns is" by (rule exE)
  then obtain "is" where c: "idx = i # is \<and> 0 \<le> i \<and> i < 0 \<and> index_in_bounds ns is" by (rule exE)
  have "0 \<le> i" "i < 0" using c by simp_all
  thus False by linarith
qed

lemma all_indices_zero: "d > 0 \<Longrightarrow> set (all_indices (replicate d 0)) = {}"
proof -
  assume "d > 0"
  then obtain d' where d: "d = Suc d'" by (cases d) auto
  have r: "replicate d (0::int) = 0 # replicate d' 0" by (simp add: d)
  have "\<And>idx. idx \<notin> set (all_indices (replicate d 0))"
    unfolding in_all_indices_iff r by (rule notI) (erule index_in_bounds_zero_dim)
  hence "\<forall>idx. idx \<notin> set (all_indices (replicate d 0))" by (rule allI)
  thus ?thesis unfolding set_eq_iff by simp
qed

lemma desc_dims_ok_zero:
  assumes "valid_encoding enc"
  shows "desc_dims_ok enc (replicate d 0) (replicate (desc_size (enc_ptr_size enc) d) (MB_Byte 0))"
  unfolding desc_dims_ok_def
proof (intro allI impI)
  fix k assume "k < length (replicate d (0 :: int))"
  hence "desc_dim_offset (enc_ptr_size enc) k + 8 \<le> desc_size (enc_ptr_size enc) d"
    by (intro desc_dim_offset_bound) simp
  thus "slice (desc_dim_offset (enc_ptr_size enc) k) 8 (replicate (desc_size (enc_ptr_size enc) d) (MB_Byte 0))
        = encode_val enc (MV_U64 (replicate d 0 ! k))"
    using \<open>k < length (replicate d (0 :: int))\<close> by (simp add: slice_replicate enc_encode_zero[OF assms])
qed

(* The payload of the first constructor fits after the tag. *)
lemma payload_inside:
  assumes "datatypes_acyclic env" and "dt_tables_ok env"
    and "ctor \<in> set (dt_ctors env dt)"
    and "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
    and "length tyvars = length args"
  shows "tag_size env dt + type_size env P sz (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)
         \<le> type_size env P sz (CoreTy_Datatype dt args)"
proof -
  have dist: "distinct tyvars"
    using assms(2,4) unfolding dt_tables_ok_def tyenv_ctor_tyvars_distinct_def by blast
  have wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars \<rparr>) payloadTy"
    using assms(2,4) unfolding dt_tables_ok_def tyenv_payloads_well_kinded_def by blast
  have sub: "type_tyvars payloadTy \<subseteq> set tyvars"
    using is_well_kinded_type_tyvars_subset[OF wk] assms(2) unfolding dt_tables_ok_def
    by (simp add: fset_of_list.rep_eq)
  show ?thesis
    unfolding type_size_subst_zip[OF dist assms(5) sub]
    by (rule type_size_payload_le[OF assms(1,3,4)])
qed


section \<open>The lemma\<close>

lemma default_value_rep_zero_aux:
  assumes enc: "valid_encoding enc" and acyc: "datatypes_acyclic env" and tabs: "dt_tables_ok env"
    and mf: "tables_math_free env" and hmap0: "hmap 0 = MP_Null"
    and ctors: "IS_DataCtors st = TE_DataCtors env" and bytype: "IS_DataCtorsByType st = TE_DataCtorsByType env"
  shows "(\<forall>ty v. is_well_kinded env ty \<longrightarrow> math_free ty \<longrightarrow> default_value fuel st ty = Inr v
            \<longrightarrow> rep_val env enc hmap mem ty v (replicate (gsz env enc ty) (MB_Byte 0)))
         \<and> (\<forall>tys vs. list_all (is_well_kinded env) tys \<longrightarrow> list_all math_free tys
            \<longrightarrow> default_value_list fuel st tys = Inr vs
            \<longrightarrow> list_all2 (\<lambda>ty v. rep_val env enc hmap mem ty v (replicate (gsz env enc ty) (MB_Byte 0))) tys vs)"
proof (induction fuel)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  note IHv = conjunct1[OF Suc.IH, rule_format]
  note IHl = conjunct2[OF Suc.IH, rule_format]
  have val: "\<And>ty v. is_well_kinded env ty \<Longrightarrow> math_free ty \<Longrightarrow> default_value (Suc fuel) st ty = Inr v
            \<Longrightarrow> rep_val env enc hmap mem ty v (replicate (gsz env enc ty) (MB_Byte 0))"
  proof -
    fix ty v assume wk: "is_well_kinded env ty" and mfree: "math_free ty" and dv: "default_value (Suc fuel) st ty = Inr v"
    show "rep_val env enc hmap mem ty v (replicate (gsz env enc ty) (MB_Byte 0))"
    proof (cases ty)
      case CoreTy_Bool
      from dv have v: "v = CV_Bool False" unfolding CoreTy_Bool by simp
      show ?thesis unfolding CoreTy_Bool v by (simp add: enc_encode_zero[OF enc])
    next
      case (CoreTy_FiniteInt s b)
      from dv have v: "v = CV_FiniteInt s b 0" unfolding CoreTy_FiniteInt by simp
      show ?thesis unfolding CoreTy_FiniteInt v by (simp add: enc_encode_zero[OF enc] int_in_range_zero)
    next
      case (CoreTy_Extern n l)
      from dv have v: "v = CV_Extern n l 0" unfolding CoreTy_Extern by simp
      show ?thesis unfolding CoreTy_Extern v by (simp add: hmap0)
    next
      case CoreTy_MathInt
      with mfree show ?thesis by simp
    next
      case CoreTy_MathReal
      with mfree show ?thesis by simp
    next
      case (CoreTy_Var x)
      with dv show ?thesis by simp
    next
      case (CoreTy_Record flds)
      from dv obtain vals where dl: "default_value_list fuel st (map snd flds) = Inr vals"
        and v: "v = CV_Record (zip (map fst flds) vals)"
        unfolding CoreTy_Record by (auto split: sum.splits)
      have dist: "distinct (map fst flds)" and wks: "list_all (is_well_kinded env) (map snd flds)"
        using wk unfolding CoreTy_Record by simp_all
      have mfs: "list_all math_free (map snd flds)" using mfree unfolding CoreTy_Record by (simp add: list_all_iff)
      note L = IHl[OF wks mfs dl]
      have lens: "length vals = length flds" using list_all2_lengthD[OF L] by simp
      define N where "N = gsz env enc (CoreTy_Record flds)"
      let ?bs = "replicate N (MB_Byte 0)"
      have "list_all2 (\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
             rep_val env enc hmap mem fty v
               (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) flds n2) (gsz env enc fty) ?bs))
             (zip (map fst flds) vals) flds"
      proof (rule list_all2_all_nthI)
        show "length (zip (map fst flds) vals) = length flds" using lens by simp
      next
        fix i assume i: "i < length (zip (map fst flds) vals)"
        hence il: "i < length flds" using lens by simp
        obtain n fty where fi: "flds ! i = (n, fty)" by (cases "flds ! i")
        have mo: "map_of flds n = Some fty" unfolding map_of_eq_Some_iff[OF dist] using nth_mem[OF il] fi by simp
        have bnd: "field_offset env (enc_ptr_size enc) (\<lambda>_. 0) flds n + gsz env enc fty \<le> N"
          unfolding N_def by (rule field_offset_bound[OF mo])
        have sl: "slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) flds n) (gsz env enc fty) ?bs
                  = replicate (gsz env enc fty) (MB_Byte 0)"
          by (rule slice_replicate[OF bnd])
        have r: "rep_val env enc hmap mem fty (vals ! i) (replicate (gsz env enc fty) (MB_Byte 0))"
          using list_all2_nthD[OF L, of i] il lens fi by simp
        show "(\<lambda>(n1, v) (n2, fty). n1 = n2 \<and>
             rep_val env enc hmap mem fty v
               (slice (field_offset env (enc_ptr_size enc) (\<lambda>_. 0) flds n2) (gsz env enc fty) ?bs))
             (zip (map fst flds) vals ! i) (flds ! i)"
          using il lens fi r sl by simp
      qed
      with dist show ?thesis unfolding CoreTy_Record v by (simp add: N_def)
    next
      case (CoreTy_Datatype dt args)
      obtain ctor cs where bt: "fmlookup (IS_DataCtorsByType st) dt = Some (ctor # cs)"
      proof (cases "fmlookup (IS_DataCtorsByType st) dt")
        case None
        with dv show ?thesis unfolding CoreTy_Datatype by simp
      next
        case (Some l)
        show ?thesis
        proof (cases l)
          case Nil
          with dv Some show ?thesis unfolding CoreTy_Datatype by simp
        next
          case (Cons c cs)
          show ?thesis by (rule that[OF Some[unfolded Cons]])
        qed
      qed
      obtain dt' tyvars payloadTy where lk0: "fmlookup (IS_DataCtors st) ctor = Some (dt', tyvars, payloadTy)"
      proof (cases "fmlookup (IS_DataCtors st) ctor")
        case None
        with dv bt show ?thesis unfolding CoreTy_Datatype by simp
      next
        case (Some x)
        obtain dt' tyvars payloadTy where x: "x = (dt', tyvars, payloadTy)" by (cases x) auto
        show ?thesis by (rule that[OF Some[unfolded x]])
      qed
      have cons: "tyenv_ctors_by_type_consistent env" using tabs unfolding dt_tables_ok_def by blast
      note iff = cons[unfolded tyenv_ctors_by_type_consistent_def, rule_format, OF bt[unfolded bytype]]
      have dt': "dt' = dt" using iff[of ctor] lk0[unfolded ctors] by simp
      note lk = lk0[unfolded dt']
      note dv1 = dv[unfolded CoreTy_Datatype default_value.simps bt option.case list.case lk prod.case Let_def]
      have len: "length tyvars = length args"
        using dv1 by (cases "length tyvars = length args") (simp_all split: if_splits)
      note dv2 = dv1[unfolded if_P[OF len]]
      obtain pv where dp: "default_value fuel st (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) = Inr pv"
        and v: "v = CV_Variant ctor pv"
      proof (cases "default_value fuel st (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)")
        case (Inl e)
        with dv2 show ?thesis by simp
      next
        case (Inr pv)
        with dv2 have "v = CV_Variant ctor pv" by simp
        with Inr show ?thesis by (rule that)
      qed
      note lkE = lk[unfolded ctors] and btE = bt[unfolded bytype]
      have inctors: "ctor \<in> set (dt_ctors env dt)" using btE by (simp add: dt_ctors_def)
      have first: "dt_ctors env dt = ctor # cs" using btE by (simp add: dt_ctors_def)
      let ?pty = "apply_subst (fmap_of_list (zip tyvars args)) payloadTy"
      let ?bs = "replicate (gsz env enc (CoreTy_Datatype dt args)) (MB_Byte 0)"
      \<comment> \<open>The substituted payload is well-kinded and math-free.\<close>
      have args_wk: "list_all (is_well_kinded env) args" using wk unfolding CoreTy_Datatype by (auto split: option.splits)
      have pw: "tyenv_payloads_well_kinded env" and cd: "tyenv_ctor_tyvars_distinct env"
        using tabs unfolding dt_tables_ok_def by blast+
      note pwk0 = pw[unfolded tyenv_payloads_well_kinded_def, rule_format, OF lkE]
      note dist = cd[unfolded tyenv_ctor_tyvars_distinct_def, rule_format, OF lkE]
      have pwk: "is_well_kinded env ?pty"
      proof (rule apply_subst_preserves_well_kinded[OF pwk0])
        show "TE_Datatypes env = TE_Datatypes (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars \<rparr>)" by simp
      next
        fix n assume "n |\<in>| TE_TypeVars (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars \<rparr>)"
        hence "n \<in> set tyvars" using tabs unfolding dt_tables_ok_def by (simp add: fset_of_list.rep_eq)
        then obtain i where i: "i < length tyvars" and ni: "tyvars ! i = n" by (auto simp: in_set_conv_nth)
        have "(n, args ! i) \<in> set (zip tyvars args)"
          using i len ni by (metis nth_zip nth_mem length_zip min_less_iff_conj)
        hence "fmlookup (fmap_of_list (zip tyvars args)) n = Some (args ! i)"
          using dist len by (simp add: fmlookup_of_list)
        thus "case fmlookup (fmap_of_list (zip tyvars args)) n of
                Some ty' \<Rightarrow> is_well_kinded env ty' | None \<Rightarrow> n |\<in>| TE_TypeVars env"
          using args_wk i len by (simp add: list_all_length)
      qed
      have pmf: "math_free ?pty"
        using mf lkE mfree unfolding tables_math_free_def CoreTy_Datatype by (intro math_free_subst_zip) auto
      note P = IHv[OF pwk pmf dp]
      \<comment> \<open>The tag of the first constructor is 0, and the payload lies after it.\<close>
      have inside: "tag_size env dt + gsz env enc ?pty \<le> gsz env enc (CoreTy_Datatype dt args)"
        by (rule payload_inside[OF acyc tabs inctors lkE len])
      have tag: "take (tag_size env dt) ?bs = encode_val enc (MV_Int Unsigned (tag_bits env dt) (int (ctor_tag env dt ctor)))"
        using inside ctor_tag_first[OF first] by (simp add: enc_encode_zero[OF enc] tag_size_def)
      have payload: "slice (tag_size env dt) (gsz env enc ?pty) ?bs = replicate (gsz env enc ?pty) (MB_Byte 0)"
        by (rule slice_replicate[OF inside])
      show ?thesis unfolding CoreTy_Datatype v
        using lkE len inctors tag P[unfolded payload[symmetric]] by simp
    next
      case (CoreTy_Array elemTy dims)
      have ewk: "is_well_kinded env elemTy" and dwk: "array_dims_well_kinded dims"
        using wk unfolding CoreTy_Array by simp_all
      have emf: "math_free elemTy" using mfree unfolding CoreTy_Array by simp
      let ?esz = "gsz env enc elemTy"
      show ?thesis
      proof (cases "dims_all_fixed dims")
        case True
        hence fixed: "list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims" by (simp add: dims_all_fixed_def)
        from dv obtain ev where de: "default_value fuel st elemTy = Inr ev"
          and v: "v = CV_Array (fixed_dim_sizes dims) (fmap_of_list (map (\<lambda>idx. (idx, ev)) (all_indices (fixed_dim_sizes dims))))"
          unfolding CoreTy_Array using fixed by (auto simp: Let_def split: sum.splits)
        note E = IHv[OF ewk emf de]
        have sizes: "fixed_dim_sizes dims = dims_sizes dims" by (rule fixed_dim_sizes_dims_sizes[OF True])
        let ?sizes = "dims_sizes dims"
        define N where "N = gsz env enc (CoreTy_Array elemTy dims)"
        let ?bs = "replicate N (MB_Byte 0)"
        have lenbs: "length ?bs = ?esz * sizes_count ?sizes" unfolding N_def using True by simp
        have elems: "\<And>idx w. fmlookup (fmap_of_list (map (\<lambda>idx. (idx, ev)) (all_indices ?sizes))) idx = Some w \<Longrightarrow>
                       rep_val env enc hmap mem elemTy w (slice (elem_offset ?esz ?sizes idx) ?esz ?bs)"
        proof -
          fix idx w assume "fmlookup (fmap_of_list (map (\<lambda>idx. (idx, ev)) (all_indices ?sizes))) idx = Some w"
          hence "(idx, w) \<in> set (map (\<lambda>idx. (idx, ev)) (all_indices ?sizes))"
            unfolding fmlookup_of_list by (rule map_of_SomeD)
          hence w: "w = ev" and inb: "index_in_bounds ?sizes idx" by (auto simp: in_all_indices_iff)
          have "elem_offset ?esz ?sizes idx + ?esz \<le> N"
            using lenbs elem_offset_bound[OF inb, of ?esz] by simp
          hence "slice (elem_offset ?esz ?sizes idx) ?esz ?bs = replicate ?esz (MB_Byte 0)"
            by (rule slice_replicate)
          thus "rep_val env enc hmap mem elemTy w (slice (elem_offset ?esz ?sizes idx) ?esz ?bs)"
            using E w by simp
        qed
        show ?thesis unfolding CoreTy_Array v sizes
          using sizes_match_dims_fixed_I[OF True] True lenbs elems by (simp add: comp_def N_def)
      next
        case False
        hence nfixed: "\<not> list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims" by (simp add: dims_all_fixed_def)
        from dv have v: "v = CV_Array (replicate (length dims) 0) fmempty"
          unfolding CoreTy_Array using nfixed by simp
        have d: "length dims > 0" using dwk unfolding array_dims_well_kinded_def by (cases dims) auto
        have nonfixed: "list_all (\<lambda>d. dim_category d \<noteq> DimCat_Fixed) dims"
          using dims_uniform_cases dwk False unfolding array_dims_well_kinded_def by blast
        let ?P = "enc_ptr_size enc"
        let ?bs = "replicate (desc_size ?P (length dims)) (MB_Byte 0)"
        have ptr: "take ?P ?bs = encode_ptr enc MP_Null" by (simp add: desc_size_def)
        have dom: "fmdom (fmempty :: (int list, CoreValue) fmap) = fset_of_list (all_indices (replicate (length dims) 0))"
          using all_indices_zero[OF d] by (simp add: fset_of_list_elem fset_eq_iff)
        show ?thesis unfolding CoreTy_Array v
          using False sizes_match_dims_zero[OF nonfixed] dom sizes_valid_zero sizes_count_zero[OF d]
                desc_dims_ok_zero[OF enc] ptr
          by simp
      qed
    qed
  qed
  have lst: "\<And>tys vs. list_all (is_well_kinded env) tys \<Longrightarrow> list_all math_free tys
            \<Longrightarrow> default_value_list (Suc fuel) st tys = Inr vs
            \<Longrightarrow> list_all2 (\<lambda>ty v. rep_val env enc hmap mem ty v (replicate (gsz env enc ty) (MB_Byte 0))) tys vs"
  proof -
    fix tys vs assume wks: "list_all (is_well_kinded env) tys" and mfs: "list_all math_free tys"
      and dl: "default_value_list (Suc fuel) st tys = Inr vs"
    show "list_all2 (\<lambda>ty v. rep_val env enc hmap mem ty v (replicate (gsz env enc ty) (MB_Byte 0))) tys vs"
    proof (cases tys)
      case Nil
      with dl show ?thesis by simp
    next
      case (Cons ty tys')
      from dl obtain v vs' where "default_value fuel st ty = Inr v" and "default_value_list fuel st tys' = Inr vs'"
        and vs: "vs = v # vs'"
        unfolding Cons by (auto split: sum.splits)
      with IHv[of ty v] IHl[of tys' vs'] wks mfs show ?thesis unfolding Cons vs by simp
    qed
  qed
  show ?case
  proof (intro conjI allI impI)
    fix ty v assume "is_well_kinded env ty" "math_free ty" "default_value (Suc fuel) st ty = Inr v"
    thus "rep_val env enc hmap mem ty v (replicate (gsz env enc ty) (MB_Byte 0))" by (rule val)
  next
    fix tys vs assume "list_all (is_well_kinded env) tys" "list_all math_free tys" "default_value_list (Suc fuel) st tys = Inr vs"
    thus "list_all2 (\<lambda>ty v. rep_val env enc hmap mem ty v (replicate (gsz env enc ty) (MB_Byte 0))) tys vs" by (rule lst)
  qed
qed

theorem default_value_rep_zero:
  assumes "valid_encoding enc" and "datatypes_acyclic env" and "dt_tables_ok env"
    and "tables_math_free env" and "hmap 0 = MP_Null"
    and "IS_DataCtors st = TE_DataCtors env" and "IS_DataCtorsByType st = TE_DataCtorsByType env"
    and "is_well_kinded env ty" and "math_free ty"
    and "default_value fuel st ty = Inr v"
  shows "rep_val env enc hmap mem ty v (replicate (gsz env enc ty) (MB_Byte 0))"
  using conjunct1[OF default_value_rep_zero_aux[where enc = enc and env = env and hmap = hmap and st = st
                                                   and fuel = fuel and mem = mem, OF assms(1-7)],
                  rule_format, OF assms(8-10)] .

end

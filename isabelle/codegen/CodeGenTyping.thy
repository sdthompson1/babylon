theory CodeGenTyping
  imports CodeGenTypingStmt RepValPath "../ghost_erasure/GhostFree"
begin

declare int_fits.simps [simp del]
declare term_types.simps [simp del]

(* ========================================================================== *)
(* The typing theorem: globals, functions, main, the module                  *)
(* ========================================================================== *)

section \<open>Effect-free statement lists\<close>

(* Statements that declare nothing and are typed in E, whatever the scope's
   declared names and the generator state. *)
definition pure_ok :: "MProgram \<Rightarrow> CTy option \<Rightarrow> MTyEnv \<Rightarrow> MStmt list \<Rightarrow> bool" where
  "pure_ok prog rt E S = (\<forall>st ds. scope_ok prog (E, ds) st \<longrightarrow> lowered_ok prog rt (E, ds) st S st (E, ds))"

lemma pure_ok_nil: "pure_ok prog rt E []"
  by (simp add: pure_ok_def lowered_ok_nil)

lemma pure_ok_append: "pure_ok prog rt E S1 \<Longrightarrow> pure_ok prog rt E S2 \<Longrightarrow> pure_ok prog rt E (S1 @ S2)"
  unfolding pure_ok_def using lowered_ok_append by blast

lemma pure_ok_Cons: "pure_ok prog rt E [s] \<Longrightarrow> pure_ok prog rt E S \<Longrightarrow> pure_ok prog rt E (s # S)"
  using pure_ok_append[of prog rt E "[s]" S] by simp

lemma pure_ok_concat: "(\<And>S. S \<in> set Ss \<Longrightarrow> pure_ok prog rt E S) \<Longrightarrow> pure_ok prog rt E (concat Ss)"
  by (induction Ss) (auto simp: pure_ok_nil pure_ok_append)

lemma pure_ok_list: "(\<And>s. s \<in> set S \<Longrightarrow> pure_ok prog rt E [s]) \<Longrightarrow> pure_ok prog rt E S"
  by (induction S) (auto simp: pure_ok_nil pure_ok_Cons)

lemma pure_ok_store: "expr_ok E p CTy_CharPtr \<Longrightarrow> expr_ok E e cty \<Longrightarrow> pure_ok prog rt E [MS_Store cty p e]"
  unfolding pure_ok_def by (auto intro!: store_ok[where cty' = cty] simp: ty_compat_def)

(* A state in which the scope is in use. *)
definition scope_state :: "MProgram \<Rightarrow> MTyEnv \<Rightarrow> string list \<Rightarrow> CGState" where
  "scope_state prog E ds = \<lparr> CS_Counter = 0, CS_Used = fmdom E |\<union>| fset_of_list ds |\<union>| fset_of_list (fun_names prog) \<rparr>"

lemma scope_ok_scope_state: "scope_ok prog (E, ds) (scope_state prog E ds)"
  by (auto simp: scope_ok_def scope_state_def fset_of_list.rep_eq)

lemma pure_ok_stmts_ok: "pure_ok prog rt E S \<Longrightarrow> stmts_ok (mk_ctx prog rt) (E, ds) S = Some (E, ds)"
  unfolding pure_ok_def using scope_ok_scope_state lowered_ok_stmts_ok by blast

lemma pure_ok_wf: "pure_ok prog rt E S \<Longrightarrow> stmts_wf prog l S"
  unfolding pure_ok_def using scope_ok_scope_state lowered_ok_wf by blast


section \<open>Closed types\<close>

lemma sizes_in_closed: "type_tyvars ty = {} \<Longrightarrow> sizes_in E (type_tyvars ty)"
  by (simp add: sizes_in_def)

lemma size_of_closed_ok: "type_tyvars ty = {} \<Longrightarrow> fits env ty \<Longrightarrow> u64_ok E (size_of env ty)"
  by (rule size_of_ok) (simp_all add: sizes_in_def fits_def)

lemma field_off_closed_ok:
  "type_tyvars (CoreTy_Record flds) = {} \<Longrightarrow> fits env (CoreTy_Record flds) \<Longrightarrow> u64_ok E (field_off env flds f)"
  by (rule field_off_ok) (simp_all add: sizes_in_def fits_def)

lemma type_tyvars_Record_fld: "type_tyvars (CoreTy_Record flds) = {} \<Longrightarrow> (f, fty) \<in> set flds \<Longrightarrow> type_tyvars fty = {}"
  by force

lemma tag_off_ok [simp]: "u64_ok E (tag_off env d)"
  by (simp add: u64_ok_def)


section \<open>Element offsets of literal indices\<close>

lemma eval0_flat_index_expr:
  assumes "index_in_bounds sizes idx"
  shows "eval0 (flat_index_expr (map (\<lambda>n. u64_lit (nat n)) sizes) (map (\<lambda>i. u64_lit (nat i)) idx)) = nat (flat_index sizes idx)"
  using assms
proof (induction sizes arbitrary: idx)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  from Cons.prems obtain i "is" where idx: "idx = i # is" and i: "0 \<le> i" "i < n" and ib: "index_in_bounds ns is"
    unfolding index_in_bounds_Cons by blast
  have fb: "0 \<le> flat_index ns is" using flat_index_bounds[OF ib] by simp
  show ?case unfolding idx using Cons.IH[OF ib] i fb by (simp add: nat_add_distrib nat_mult_distrib)
qed

lemma u64_ok_flat_index_expr:
  assumes "index_in_bounds sizes idx" and "sizes_count sizes < u64_max"
  shows "u64_ok E (flat_index_expr (map (\<lambda>n. u64_lit (nat n)) sizes) (map (\<lambda>i. u64_lit (nat i)) idx))"
  using assms
proof (induction sizes arbitrary: idx)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  from Cons.prems(1) obtain i "is" where idx: "idx = i # is" and i: "0 \<le> i" "i < n" and ib: "index_in_bounds ns is"
    unfolding index_in_bounds_Cons by blast
  have pos: "0 < sizes_count ns" using index_in_bounds_count_pos[OF ib] .
  have cnt: "sizes_count (n # ns) = nat n * sizes_count ns" by (simp add: sizes_count_def)
  have n1: "1 \<le> nat n" using i by simp
  have cnt_ns: "sizes_count ns < u64_max"
  proof -
    have "sizes_count ns \<le> nat n * sizes_count ns" using mult_le_mono1[OF n1, of "sizes_count ns"] by simp
    then show ?thesis using Cons.prems(2)[unfolded cnt] by (rule le_less_trans)
  qed
  have n_lt: "nat n < u64_max"
  proof -
    have "nat n \<le> nat n * sizes_count ns" using mult_le_mono2[OF Suc_leI[OF pos], of "nat n"] by simp
    then show ?thesis using Cons.prems(2)[unfolded cnt] by (rule le_less_trans)
  qed
  have IH: "u64_ok E (flat_index_expr (map (\<lambda>n. u64_lit (nat n)) ns) (map (\<lambda>i. u64_lit (nat i)) is))"
    by (rule Cons.IH[OF ib cnt_ns])
  have ev: "eval0 (flat_index_expr (map (\<lambda>n. u64_lit (nat n)) ns) (map (\<lambda>i. u64_lit (nat i)) is)) = nat (flat_index ns is)"
    by (rule eval0_flat_index_expr[OF ib])
  have fb: "0 \<le> flat_index ns is" "flat_index ns is < int (sizes_count ns)" using flat_index_bounds[OF ib] by simp_all
  have whole: "nat i + nat n * nat (flat_index ns is) < u64_max"
  proof -
    have "nat i + nat n * nat (flat_index ns is) = nat (flat_index (n # ns) (i # is))"
      using i fb by (simp add: nat_add_distrib nat_mult_distrib)
    also have "\<dots> < sizes_count (n # ns)"
      using flat_index_bounds[OF Cons.prems(1)[unfolded idx]] by (auto simp: nat_less_iff)
    finally show ?thesis using Cons.prems(2) by simp
  qed
  let ?fi = "flat_index_expr (map (\<lambda>n. u64_lit (nat n)) ns) (map (\<lambda>i. u64_lit (nat i)) is)"
  have nlit: "u64_ok E (u64_lit (nat n))" unfolding u64_ok_lit by (rule n_lt)
  have ilit: "u64_ok E (u64_lit (nat i))"
    unfolding u64_ok_lit by (rule le_less_trans[OF nat_mono[OF less_imp_le[OF i(2)]] n_lt])
  have mul_bound: "eval0 (u64_lit (nat n)) * eval0 ?fi < u64_max"
    unfolding eval0_u64_lit ev by (rule le_less_trans[OF le_add2 whole])
  have mul: "u64_ok E (e_mul (u64_lit (nat n)) ?fi)"
    by (rule u64_ok_e_fold2) (rule nlit, rule IH, rule mul_bound, simp)
  have add_bound: "eval0 (u64_lit (nat i)) + eval0 (e_mul (u64_lit (nat n)) ?fi) < u64_max"
    unfolding eval0_e_mul eval0_u64_lit ev by (rule whole)
  show ?case unfolding idx
    by (simp only: list.map flat_index_expr.simps) (rule u64_ok_e_fold2, rule ilit, rule mul, rule add_bound, simp)
qed

(* The offset of an element of an array value at a closed element type. *)
lemma elem_offset_lit_ok:
  assumes "index_in_bounds sizes idx" and "sizes_count sizes < u64_max"
    and "type_tyvars elemTy = {}" and "fits env elemTy"
    and "type_size env 0 (\<lambda>_. 0) elemTy * sizes_count sizes < u64_max"
  shows "u64_ok E (elem_offset_expr (size_of env elemTy) (map (\<lambda>n. u64_lit (nat n)) sizes) (map (\<lambda>i. u64_lit (nat i)) idx))"
proof -
  have sz: "u64_ok E (size_of env elemTy)" using size_of_closed_ok[OF assms(3,4)] .
  have fi: "u64_ok E (flat_index_expr (map (\<lambda>n. u64_lit (nat n)) sizes) (map (\<lambda>i. u64_lit (nat i)) idx))"
    using u64_ok_flat_index_expr[OF assms(1,2)] .
  have lt: "nat (flat_index sizes idx) < sizes_count sizes" using flat_index_bounds[OF assms(1)] by (auto simp: nat_less_iff)
  have bound': "type_size env 0 (\<lambda>_. 0) elemTy * nat (flat_index sizes idx) < u64_max"
    by (rule le_less_trans[OF mult_le_mono2[OF less_imp_le[OF lt]] assms(5)])
  have fi_eval: "eval0 (flat_index_expr (map (\<lambda>n. u64_lit (nat n)) sizes) (map (\<lambda>i. u64_lit (nat i)) idx)) = nat (flat_index sizes idx)"
    by (rule eval0_flat_index_expr[OF assms(1)])
  show ?thesis unfolding elem_offset_expr_def
    by (rule u64_ok_e_fold2[OF sz fi]) (unfold fi_eval eval0_size_of, rule bound', simp)
qed


section \<open>Monadic maps\<close>

lemma cg_mapM_all:
  assumes "cg_mapM f xs st = Inr (ys, st')"
    and "\<And>x y st1 st2. x \<in> set xs \<Longrightarrow> f x st1 = Inr (y, st2) \<Longrightarrow> P y"
  shows "\<forall>y \<in> set ys. P y"
  using assms
proof (induction xs arbitrary: st ys)
  case Nil
  then show ?case by (simp add: cg_mapM.simps)
next
  case (Cons x xs)
  from Cons.prems(1) obtain y st1 ys' where fx: "f x st = Inr (y, st1)" and rest: "cg_mapM f xs st1 = Inr (ys', st')"
    and ys: "ys = y # ys'"
    by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  show ?case unfolding ys using Cons.prems(2)[OF _ fx] Cons.IH[OF rest] Cons.prems(2) by auto
qed

(* The names generated by a monadic map: fresh before, in use after, distinct. *)
lemma cg_mapM_names:
  assumes "cg_mapM f xs st = Inr (ys, st')"
    and "\<And>x y st1 st2. x \<in> set xs \<Longrightarrow> f x st1 = Inr (y, st2) \<Longrightarrow>
           used_le st1 st2 \<and> (\<forall>n \<in> set (names y). n |\<notin>| CS_Used st1 \<and> n |\<in>| CS_Used st2) \<and> distinct (names y)"
  shows "used_le st st' \<and> (\<forall>n \<in> set (concat (map names ys)). n |\<notin>| CS_Used st \<and> n |\<in>| CS_Used st')
         \<and> distinct (concat (map names ys))"
  using assms
proof (induction xs arbitrary: st ys)
  case Nil
  then show ?case by (simp add: cg_mapM.simps)
next
  case (Cons x xs)
  from Cons.prems(1) obtain y st1 ys' where fx: "f x st = Inr (y, st1)" and rest: "cg_mapM f xs st1 = Inr (ys', st')"
    and ys: "ys = y # ys'"
    by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  have h: "used_le st st1 \<and> (\<forall>n \<in> set (names y). n |\<notin>| CS_Used st \<and> n |\<in>| CS_Used st1) \<and> distinct (names y)"
    using Cons.prems(2)[OF _ fx] by simp
  have IH: "used_le st1 st' \<and> (\<forall>n \<in> set (concat (map names ys')). n |\<notin>| CS_Used st1 \<and> n |\<in>| CS_Used st')
            \<and> distinct (concat (map names ys'))"
  proof (rule Cons.IH[OF rest])
    fix xa st1 y st2 assume a1: "xa \<in> set xs" and a2: "f xa st1 = Inr (y, st2)"
    show "used_le st1 st2 \<and> (\<forall>n \<in> set (names y). n |\<notin>| CS_Used st1 \<and> n |\<in>| CS_Used st2) \<and> distinct (names y)"
      using Cons.prems(2)[OF _ a2] a1 by simp
  qed
  show ?case unfolding ys using h IH
    by (auto simp: used_le_def intro: used_le_trans[unfolded used_le_def])
qed


section \<open>Global values\<close>

lemma value_has_type_Record:
  assumes "value_has_type env (CV_Record fvs) (CoreTy_Record fldTys)" and "(f, v) \<in> set fvs"
  shows "\<exists>fty. map_of fldTys f = Some fty \<and> value_has_type env v fty"
proof -
  from assms(1) have dist: "distinct (map fst fldTys)"
    and la: "list_all2 (\<lambda>(name1, fldVal) (name2, fldTy). name1 = name2 \<and> value_has_type env fldVal fldTy) fvs fldTys"
    by simp_all
  from assms(2) obtain i where i: "i < length fvs" and fi: "fvs ! i = (f, v)" by (auto simp: in_set_conv_nth)
  have len: "length fldTys = length fvs" using list_all2_lengthD[OF la] by simp
  have "fst (fldTys ! i) = f" and vt: "value_has_type env v (snd (fldTys ! i))"
    using list_all2_nthD[OF la i] fi by (auto simp: split_beta)
  then have "map_of fldTys f = Some (snd (fldTys ! i))"
    using dist i len by (metis map_of_eq_Some_iff nth_mem prod.collapse)
  then show ?thesis using vt by blast
qed

lemma fmap_matches_sizes_lookup:
  assumes "fmap_matches_sizes sizes elems" and "idx \<in> set (all_indices sizes)"
  shows "\<exists>v. fmlookup elems idx = Some v"
  using assms unfolding fmap_matches_sizes_def by (auto simp: fmlookup_dom_iff fset_of_list.rep_eq)

lemma sizes_valid_lt: "sizes_valid sizes \<Longrightarrow> k < length sizes \<Longrightarrow> nat (sizes ! k) < u64_max"
  unfolding sizes_valid_def list_all_length by (auto simp: int_range.simps u64_max_def)

(* The data buffer of an array value: a closed uint64_t expression. *)
lemma data_buf_size_ok:
  assumes "type_tyvars elemTy = {}" and "fits env elemTy" and "sizes_count sizes < u64_max"
    and "type_size env 0 (\<lambda>_. 0) elemTy * sizes_count sizes < u64_max"
  shows "u64_ok E (buf_size (e_mul (size_of env elemTy) (u64_lit (sizes_count sizes))))"
  using size_of_closed_ok[OF assms(1,2), of E] assms(3,4)
  by (intro buf_size_ok u64_ok_e_fold2) (simp_all add: eval0_size_of)

(* The initialisation statements of a global value are typed in any
   environment that has the value's data buffers and the base's variables. *)
lemma init_value_ok:
  "init_value env g ty v base st = Inr ((gs, S), st') \<Longrightarrow> value_has_type env v ty \<Longrightarrow> fits env ty
   \<Longrightarrow> tyenv_well_formed env \<Longrightarrow> (\<And>d. dt_tags_fit env d)
   \<Longrightarrow> (\<And>n mg. (n, mg) \<in> set gs \<Longrightarrow> fmlookup E n = Some (global_var_ty mg))
   \<Longrightarrow> expr_ok E base CTy_CharPtr
   \<Longrightarrow> pure_ok prog rt E S"
proof (induction env g ty v base arbitrary: st gs S st' rule: init_value.induct)
  case (1 env g ty b base)
  then have "ty = CoreTy_Bool" "S = [MS_Store CTy_U8 base (ME_Int Unsigned IntBits_8 (if b then 1 else 0))]"
    by (auto simp: cg_return_def)
  then show ?case using 1(7) by (auto intro!: pure_ok_store simp: expr_ok_def)
next
  case (2 env g ty s b i base)
  then have "ty = CoreTy_FiniteInt s b" "int_fits s b i" "S = [MS_Store (CTy_Int s b) base (ME_Int s b i)]"
    by (auto simp: cg_return_def)
  then show ?case using 2(7) by (auto intro!: pure_ok_store simp: expr_ok_def)
next
  case (3 env g ty fvs base)
  obtain fldTys where ty: "ty = CoreTy_Record fldTys" using 3(3) by (cases ty) auto
  let ?f = "\<lambda>(f, v). cg_bind (cg_lift g ''unknown field in a global value'' (map_of fldTys f))
                       (\<lambda>fty. init_value env g fty v (ptr_add base (field_off env fldTys f)))"
  from 3(2) obtain rs where lm: "cg_mapM ?f fvs st = Inr (rs, st')" and gs: "gs = concat (map fst rs)" and S: "S = concat (map snd rs)"
    unfolding init_value.simps ty by (auto simp: cg_return_def elim!: cg_bind_InrE)
  have closed: "type_tyvars (CoreTy_Record fldTys) = {}" using value_has_type_ground[OF 3(3)] ty by simp
  have fo: "\<And>f. u64_ok E (field_off env fldTys f)" using field_off_closed_ok[OF closed 3(4)[unfolded ty]] .
  have "\<forall>r \<in> set rs. (\<forall>n mg. (n, mg) \<in> set (fst r) \<longrightarrow> fmlookup E n = Some (global_var_ty mg)) \<longrightarrow> pure_ok prog rt E (snd r)"
  proof (rule cg_mapM_all[OF lm])
    fix x r st1 st2
    assume x: "x \<in> set fvs" and fx: "?f x st1 = Inr (r, st2)"
    obtain f v where xfv: "x = (f, v)" by (cases x)
    obtain fty where mo: "map_of fldTys f = Some fty" and vt: "value_has_type env v fty"
      using value_has_type_Record[OF 3(3)[unfolded ty] x[unfolded xfv]] by blast
    have fx': "cg_bind (cg_lift g ''unknown field in a global value'' (map_of fldTys f))
                 (\<lambda>fty. init_value env g fty v (ptr_add base (field_off env fldTys f))) st1 = Inr (r, st2)"
      using fx unfolding xfv by simp
    from fx' obtain fty' st1' where cl: "cg_lift g ''unknown field in a global value'' (map_of fldTys f) st1 = Inr (fty', st1')"
      and iv: "init_value env g fty' v (ptr_add base (field_off env fldTys f)) st1' = Inr (r, st2)"
      by (rule cg_bind_InrE)
    have fty': "fty' = fty" and st1': "st1' = st1" using cl mo by (simp_all add: cg_lift_Inr)
    obtain gs' S' where r: "r = (gs', S')" by (cases r)
    show "(\<forall>n mg. (n, mg) \<in> set (fst r) \<longrightarrow> fmlookup E n = Some (global_var_ty mg)) \<longrightarrow> pure_ok prog rt E (snd r)"
    proof
      assume A: "\<forall>n mg. (n, mg) \<in> set (fst r) \<longrightarrow> fmlookup E n = Some (global_var_ty mg)"
      show "pure_ok prog rt E (snd r)"
        unfolding r snd_conv
        by (rule 3(1)[OF ty x xfv[symmetric] cl iv[unfolded st1' r] vt[folded fty'] fits_Record_fld[OF 3(4)[unfolded ty] mo[folded fty']] 3(5,6)])
           (use A in \<open>auto simp: r fo intro!: expr_ok_ptr_add[OF 3(8)]\<close>)
    qed
  qed
  then show ?case unfolding S using 3(7) gs by (intro pure_ok_concat) auto
next
  case (4 env g ty c p base)
  obtain dtName args where ty: "ty = CoreTy_Datatype dtName args" using 4(3) by (cases ty) auto
  obtain tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) c = Some (dtName, tyvars, payloadTy)"
    and vt: "value_has_type env p (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)"
    using 4(3) unfolding ty by (auto split: option.splits)
  let ?pty = "apply_subst (fmap_of_list (zip tyvars args)) payloadTy"
  from 4(2) have chk: "size_fits env 0 (\<lambda>_. 0) ?pty"
    unfolding init_value.simps ty lk by (auto simp: cg_fail_def split: if_splits)
  from 4(2) obtain gs' S' where iv: "init_value env g ?pty p (ptr_add base (tag_off env dtName)) st = Inr ((gs', S'), st')"
    and gs: "gs = gs'" and S: "S = MS_Store (tag_ty env dtName) base (tag_lit env dtName c) # S'"
    unfolding init_value.simps ty lk using chk by (auto simp: cg_return_def elim!: cg_bind_InrE)
  have tag: "expr_ok E (tag_lit env dtName c) (tag_ty env dtName)"
    using tag_lit_type[OF ctor_in_dt_ctors[OF 4(5) lk] 4(6)] by (simp add: expr_ok_def)
  have st: "pure_ok prog rt E [MS_Store (tag_ty env dtName) base (tag_lit env dtName c)]"
    by (rule pure_ok_store[OF 4(8) tag])
  have rest: "pure_ok prog rt E S'"
    by (rule 4(1)[OF ty lk refl refl _ iv vt _ 4(5,6)])
       (use chk in simp, simp add: fits_def chk, use 4(7) gs in blast, intro expr_ok_ptr_add[OF 4(8)], simp_all)
  show ?case unfolding S by (rule pure_ok_Cons[OF st rest])
next
  case (5 env g ty sizes elems base)
  obtain elemTy dims where ty: "ty = CoreTy_Array elemTy dims" using 5(3) by (cases ty) auto
  have closed: "type_tyvars elemTy = {}" and vts: "\<And>idx v. fmlookup elems idx = Some v \<Longrightarrow> value_has_type env v elemTy"
    and fms: "fmap_matches_sizes sizes elems" and smd: "sizes_match_dims sizes dims"
    using 5(3) unfolding ty by auto
  have sv: "sizes_valid sizes" using fms unfolding fmap_matches_sizes_def by simp
  let ?esz = "size_of env elemTy"
  let ?ns = "map (\<lambda>n. u64_lit (nat n)) sizes"
  let ?off = "\<lambda>idx. elem_offset_expr ?esz ?ns (map (\<lambda>i. u64_lit (nat i)) idx)"
  let ?ef = "\<lambda>data idx. (case fmlookup elems idx of
                 Some v \<Rightarrow> init_value env g elemTy v (ptr_add data (?off idx))
               | None \<Rightarrow> cg_fail (CGE_Internal g ''missing array element in a global value''))"
  let ?initElems = "\<lambda>data. cg_mapM (?ef data) (all_indices sizes)"
  let ?dimStores = "map (\<lambda>k. MS_Store CTy_U64 (ptr_add base (dim_off k)) (u64_lit (nat (sizes ! k)))) [0..<length sizes]"
  let ?chk = "size_fits env 0 (\<lambda>_. 0) elemTy \<and> sizes_count sizes < u64_max
              \<and> type_size env 0 (\<lambda>_. 0) elemTy * sizes_count sizes < u64_max"
  have unf: "init_value env g ty (CV_Array sizes elems) base =
      (if dims_all_fixed dims then cg_bind (?initElems base) (\<lambda>rs. cg_return (concat (map fst rs), concat (map snd rs)))
       else if \<not> ?chk then cg_fail (CGE_Internal g ''global array value too large'')
       else if sizes_count sizes = 0 then cg_return ([], ?dimStores)
       else cg_bind (fresh_name g (g @ [dollar] @ ''data'')) (\<lambda>data.
            cg_bind (?initElems (ME_AddrOf data)) (\<lambda>rs.
            cg_return ((data, MG_Buf (buf_size (e_mul ?esz (u64_lit (sizes_count sizes))))) # concat (map fst rs),
                       MS_Store CTy_CharPtr base (ME_AddrOf data) # ?dimStores @ concat (map snd rs)))))"
    unfolding init_value.simps ty by (simp only: Let_def CoreType.case)
  (* the elements, at any data base, under the bounds *)
  have elems_ok: "\<And>data rs st1 st2. ?initElems data st1 = Inr (rs, st2) \<Longrightarrow> expr_ok E data CTy_CharPtr
      \<Longrightarrow> fits env elemTy \<Longrightarrow> sizes_count sizes < u64_max \<Longrightarrow> type_size env 0 (\<lambda>_. 0) elemTy * sizes_count sizes < u64_max
      \<Longrightarrow> (\<And>n mg. (n, mg) \<in> set (concat (map fst rs)) \<Longrightarrow> fmlookup E n = Some (global_var_ty mg))
      \<Longrightarrow> pure_ok prog rt E (concat (map snd rs))"
  proof -
    fix data rs st1 st2
    assume ie: "?initElems data st1 = Inr (rs, st2)" and dok: "expr_ok E data CTy_CharPtr" and fe: "fits env elemTy"
      and cnt: "sizes_count sizes < u64_max" and bound: "type_size env 0 (\<lambda>_. 0) elemTy * sizes_count sizes < u64_max"
      and gsE: "\<And>n mg. (n, mg) \<in> set (concat (map fst rs)) \<Longrightarrow> fmlookup E n = Some (global_var_ty mg)"
    have "\<forall>r \<in> set rs. (\<forall>n mg. (n, mg) \<in> set (fst r) \<longrightarrow> fmlookup E n = Some (global_var_ty mg)) \<longrightarrow> pure_ok prog rt E (snd r)"
    proof (rule cg_mapM_all[OF ie])
      fix idx r st3 st4
      assume idx: "idx \<in> set (all_indices sizes)" and fr: "?ef data idx st3 = Inr (r, st4)"
      obtain v where lk: "fmlookup elems idx = Some v" using fmap_matches_sizes_lookup[OF fms idx] by blast
      have iv: "init_value env g elemTy v (ptr_add data (?off idx)) st3 = Inr (r, st4)" using fr lk by simp
      obtain gs' S' where r: "r = (gs', S')" by (cases r)
      have ib: "index_in_bounds sizes idx" using idx by (simp add: in_all_indices_iff)
      have off: "u64_ok E (?off idx)" by (rule elem_offset_lit_ok[OF ib cnt closed fe bound])
      have po: "expr_ok E (ptr_add data (?off idx)) CTy_CharPtr" by (rule expr_ok_ptr_add[OF dok]) (simp, rule off)
      show "(\<forall>n mg. (n, mg) \<in> set (fst r) \<longrightarrow> fmlookup E n = Some (global_var_ty mg)) \<longrightarrow> pure_ok prog rt E (snd r)"
      proof
        assume A: "\<forall>n mg. (n, mg) \<in> set (fst r) \<longrightarrow> fmlookup E n = Some (global_var_ty mg)"
        show "pure_ok prog rt E (snd r)"
          unfolding r snd_conv
          by (rule 5(1)[OF ty refl refl idx lk iv[unfolded r] vts[OF lk] fe 5(5,6)])
             (use A po in \<open>auto simp: r\<close>)
      qed
    qed
    then show "pure_ok prog rt E (concat (map snd rs))" using gsE by (intro pure_ok_concat) auto
  qed
  show ?case
  proof (cases "dims_all_fixed dims")
    case True
    from 5(2)[unfolded unf] obtain rs where ie: "?initElems base st = Inr (rs, st')"
      and gs: "gs = concat (map fst rs)" and S: "S = concat (map snd rs)"
      using True by (auto simp: cg_return_def elim!: cg_bind_InrE)
    have sizes: "sizes = dims_sizes dims" using sizes_match_dims_fixed[OF smd True] .
    have fe: "fits env elemTy" using fits_Array_elem_fixed[OF 5(4)[unfolded ty] True] .
    have cnt: "sizes_count sizes < u64_max" and bound: "type_size env 0 (\<lambda>_. 0) elemTy * sizes_count sizes < u64_max"
      using 5(4) True unfolding ty sizes fits_def size_fits_def type_size_def by (simp_all add: tsz_fits.simps)
    show ?thesis unfolding S by (rule elems_ok[OF ie 5(8) fe cnt bound]) (use 5(7) gs in blast)
  next
    case False
    have chk: "?chk" using 5(2)[unfolded unf] False by (auto simp: cg_fail_def split: if_splits)
    have fe: "fits env elemTy" using chk by (simp add: fits_def)
    have len: "length sizes = length dims" using sizes_match_dims_length[OF smd] .
    have desc: "8 * length dims < u64_max" using fits_Array_desc[OF 5(4)[unfolded ty] False] .
    have dims_ok: "pure_ok prog rt E ?dimStores"
    proof (rule pure_ok_list)
      fix s assume "s \<in> set ?dimStores"
      then obtain k where k: "k < length sizes" and s: "s = MS_Store CTy_U64 (ptr_add base (dim_off k)) (u64_lit (nat (sizes ! k)))" by auto
      have "8 * k < u64_max" using k len desc by simp
      then have p: "expr_ok E (ptr_add base (dim_off k)) CTy_CharPtr"
        by (intro expr_ok_ptr_add[OF 5(8)]) (simp_all add: u64_ok_def)
      have v: "expr_ok E (u64_lit (nat (sizes ! k))) CTy_U64"
        unfolding expr_ok_u64 u64_ok_lit by (rule sizes_valid_lt[OF sv k])
      show "pure_ok prog rt E [s]" unfolding s by (rule pure_ok_store[OF p v])
    qed
    show ?thesis
    proof (cases "sizes_count sizes = 0")
      case True
      have S: "S = ?dimStores" using 5(2)[unfolded unf] False chk True by (auto simp: cg_return_def)
      show ?thesis unfolding S by (rule dims_ok)
    next
      case nz: False
      from 5(2)[unfolded unf] obtain data st1 rs where fr: "fresh_name g (g @ [dollar] @ ''data'') st = Inr (data, st1)"
        and ie: "?initElems (ME_AddrOf data) st1 = Inr (rs, st')"
        and gs: "gs = (data, MG_Buf (buf_size (e_mul ?esz (u64_lit (sizes_count sizes))))) # concat (map fst rs)"
        and S: "S = MS_Store CTy_CharPtr base (ME_AddrOf data) # ?dimStores @ concat (map snd rs)"
        using False chk nz by (auto simp: cg_return_def elim!: cg_bind_InrE)
      have dE: "fmlookup E data = Some VT_Buf"
        using 5(7)[of data "MG_Buf (buf_size (e_mul ?esz (u64_lit (sizes_count sizes))))"] unfolding gs
        by (simp add: global_var_ty_def)
      have dok: "expr_ok E (ME_AddrOf data) CTy_CharPtr" using dE by (intro expr_ok_AddrOf)
      have s1: "pure_ok prog rt E [MS_Store CTy_CharPtr base (ME_AddrOf data)]" by (rule pure_ok_store[OF 5(8) dok])
      have cnt': "sizes_count sizes < u64_max" and bound': "type_size env 0 (\<lambda>_. 0) elemTy * sizes_count sizes < u64_max"
        using chk by blast+
      have gsE: "\<And>n mg. (n, mg) \<in> set (concat (map fst rs)) \<Longrightarrow> fmlookup E n = Some (global_var_ty mg)"
        by (rule 5(7)) (simp add: gs)
      have els: "pure_ok prog rt E (concat (map snd rs))"
        by (rule elems_ok[OF ie dok fe cnt' bound' gsE])
      show ?thesis unfolding S by (intro pure_ok_Cons[OF s1] pure_ok_append[OF dims_ok els])
    qed
  qed
qed (auto simp: cg_fail_def cg_return_def pure_ok_nil split: if_splits)

(* The data buffers of a global value: fresh names, typed sizes. *)
lemma init_value_names:
  "init_value env g ty v base st = Inr ((gs, S), st') \<Longrightarrow> value_has_type env v ty
   \<Longrightarrow> used_le st st' \<and> (\<forall>n \<in> set (map fst gs). n |\<notin>| CS_Used st \<and> n |\<in>| CS_Used st') \<and> distinct (map fst gs)
       \<and> (\<forall>(n, mg) \<in> set gs. \<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e)"
proof (induction env g ty v base arbitrary: st gs S st' rule: init_value.induct)
  case (3 env g ty fvs base)
  obtain fldTys where ty: "ty = CoreTy_Record fldTys" using 3(3) by (cases ty) auto
  let ?f = "\<lambda>(f, v). cg_bind (cg_lift g ''unknown field in a global value'' (map_of fldTys f))
                       (\<lambda>fty. init_value env g fty v (ptr_add base (field_off env fldTys f)))"
  from 3(2) obtain rs where lm: "cg_mapM ?f fvs st = Inr (rs, st')" and gs: "gs = concat (map fst rs)"
    unfolding init_value.simps ty by (auto simp: cg_return_def elim!: cg_bind_InrE)
  have names: "used_le st st' \<and> (\<forall>n \<in> set (concat (map (map fst \<circ> fst) rs)). n |\<notin>| CS_Used st \<and> n |\<in>| CS_Used st')
         \<and> distinct (concat (map (map fst \<circ> fst) rs))"
  proof (rule cg_mapM_names[OF lm])
    fix x r st1 st2
    assume x: "x \<in> set fvs" and fx: "?f x st1 = Inr (r, st2)"
    obtain f v where xfv: "x = (f, v)" by (cases x)
    obtain fty where mo: "map_of fldTys f = Some fty" and vt: "value_has_type env v fty"
      using value_has_type_Record[OF 3(3)[unfolded ty] x[unfolded xfv]] by blast
    have fx': "cg_bind (cg_lift g ''unknown field in a global value'' (map_of fldTys f))
                 (\<lambda>fty. init_value env g fty v (ptr_add base (field_off env fldTys f))) st1 = Inr (r, st2)"
      using fx unfolding xfv by simp
    from fx' obtain fty' st1' where cl: "cg_lift g ''unknown field in a global value'' (map_of fldTys f) st1 = Inr (fty', st1')"
      and iv: "init_value env g fty' v (ptr_add base (field_off env fldTys f)) st1' = Inr (r, st2)"
      by (rule cg_bind_InrE)
    have fty': "fty' = fty" and st1': "st1' = st1" using cl mo by (simp_all add: cg_lift_Inr)
    obtain gs' S' where r: "r = (gs', S')" by (cases r)
    show "used_le st1 st2 \<and> (\<forall>n \<in> set ((map fst \<circ> fst) r). n |\<notin>| CS_Used st1 \<and> n |\<in>| CS_Used st2) \<and> distinct ((map fst \<circ> fst) r)"
      using 3(1)[OF ty x xfv[symmetric] cl iv[unfolded st1' r] vt[folded fty']] unfolding r by simp
  qed
  have bufs: "\<forall>r \<in> set rs. \<forall>(n, mg) \<in> set (fst r). \<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e"
  proof (rule cg_mapM_all[OF lm])
    fix x r st1 st2
    assume x: "x \<in> set fvs" and fx: "?f x st1 = Inr (r, st2)"
    obtain f v where xfv: "x = (f, v)" by (cases x)
    obtain fty where mo: "map_of fldTys f = Some fty" and vt: "value_has_type env v fty"
      using value_has_type_Record[OF 3(3)[unfolded ty] x[unfolded xfv]] by blast
    have fx': "cg_bind (cg_lift g ''unknown field in a global value'' (map_of fldTys f))
                 (\<lambda>fty. init_value env g fty v (ptr_add base (field_off env fldTys f))) st1 = Inr (r, st2)"
      using fx unfolding xfv by simp
    from fx' obtain fty' st1' where cl: "cg_lift g ''unknown field in a global value'' (map_of fldTys f) st1 = Inr (fty', st1')"
      and iv: "init_value env g fty' v (ptr_add base (field_off env fldTys f)) st1' = Inr (r, st2)"
      by (rule cg_bind_InrE)
    have fty': "fty' = fty" and st1': "st1' = st1" using cl mo by (simp_all add: cg_lift_Inr)
    obtain gs' S' where r: "r = (gs', S')" by (cases r)
    show "\<forall>(n, mg) \<in> set (fst r). \<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e"
      using 3(1)[OF ty x xfv[symmetric] cl iv[unfolded st1' r] vt[folded fty']] unfolding r by simp
  qed
  have eq: "map fst gs = concat (map (map fst \<circ> fst) rs)" unfolding gs by (simp add: map_concat)
  show ?case unfolding eq using names bufs gs by auto
next
  case (4 env g ty c p base)
  obtain dtName args where ty: "ty = CoreTy_Datatype dtName args" using 4(3) by (cases ty) auto
  obtain tyvars payloadTy where lk: "fmlookup (TE_DataCtors env) c = Some (dtName, tyvars, payloadTy)"
    and vt: "value_has_type env p (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)"
    using 4(3) unfolding ty by (auto split: option.splits)
  let ?pty = "apply_subst (fmap_of_list (zip tyvars args)) payloadTy"
  from 4(2) have chk: "size_fits env 0 (\<lambda>_. 0) ?pty"
    unfolding init_value.simps ty lk by (auto simp: cg_fail_def split: if_splits)
  from 4(2) obtain S' where iv: "init_value env g ?pty p (ptr_add base (tag_off env dtName)) st = Inr ((gs, S'), st')"
    unfolding init_value.simps ty lk using chk by (auto simp: cg_return_def elim!: cg_bind_InrE)
  show ?case by (rule 4(1)[OF ty lk refl refl _ iv vt]) (use chk in simp)
next
  case (5 env g ty sizes elems base)
  obtain elemTy dims where ty: "ty = CoreTy_Array elemTy dims" using 5(3) by (cases ty) auto
  have closed: "type_tyvars elemTy = {}" and vts: "\<And>idx v. fmlookup elems idx = Some v \<Longrightarrow> value_has_type env v elemTy"
    and fms: "fmap_matches_sizes sizes elems"
    using 5(3) unfolding ty by auto
  let ?esz = "size_of env elemTy"
  let ?ns = "map (\<lambda>n. u64_lit (nat n)) sizes"
  let ?off = "\<lambda>idx. elem_offset_expr ?esz ?ns (map (\<lambda>i. u64_lit (nat i)) idx)"
  let ?ef = "\<lambda>data idx. (case fmlookup elems idx of
                 Some v \<Rightarrow> init_value env g elemTy v (ptr_add data (?off idx))
               | None \<Rightarrow> cg_fail (CGE_Internal g ''missing array element in a global value''))"
  let ?initElems = "\<lambda>data. cg_mapM (?ef data) (all_indices sizes)"
  let ?dimStores = "map (\<lambda>k. MS_Store CTy_U64 (ptr_add base (dim_off k)) (u64_lit (nat (sizes ! k)))) [0..<length sizes]"
  let ?chk = "size_fits env 0 (\<lambda>_. 0) elemTy \<and> sizes_count sizes < u64_max
              \<and> type_size env 0 (\<lambda>_. 0) elemTy * sizes_count sizes < u64_max"
  have unf: "init_value env g ty (CV_Array sizes elems) base =
      (if dims_all_fixed dims then cg_bind (?initElems base) (\<lambda>rs. cg_return (concat (map fst rs), concat (map snd rs)))
       else if \<not> ?chk then cg_fail (CGE_Internal g ''global array value too large'')
       else if sizes_count sizes = 0 then cg_return ([], ?dimStores)
       else cg_bind (fresh_name g (g @ [dollar] @ ''data'')) (\<lambda>data.
            cg_bind (?initElems (ME_AddrOf data)) (\<lambda>rs.
            cg_return ((data, MG_Buf (buf_size (e_mul ?esz (u64_lit (sizes_count sizes))))) # concat (map fst rs),
                       MS_Store CTy_CharPtr base (ME_AddrOf data) # ?dimStores @ concat (map snd rs)))))"
    unfolding init_value.simps ty by (simp only: Let_def CoreType.case)
  have elems: "\<And>data rs st1 st2. ?initElems data st1 = Inr (rs, st2) \<Longrightarrow>
      used_le st1 st2 \<and> (\<forall>n \<in> set (concat (map (map fst \<circ> fst) rs)). n |\<notin>| CS_Used st1 \<and> n |\<in>| CS_Used st2)
      \<and> distinct (concat (map (map fst \<circ> fst) rs))
      \<and> (\<forall>r \<in> set rs. \<forall>(n, mg) \<in> set (fst r). \<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e)"
  proof -
    fix data rs st1 st2
    assume ie: "?initElems data st1 = Inr (rs, st2)"
    have step: "\<And>idx r st3 st4. idx \<in> set (all_indices sizes) \<Longrightarrow> ?ef data idx st3 = Inr (r, st4) \<Longrightarrow>
        used_le st3 st4 \<and> (\<forall>n \<in> set ((map fst \<circ> fst) r). n |\<notin>| CS_Used st3 \<and> n |\<in>| CS_Used st4) \<and> distinct ((map fst \<circ> fst) r)
        \<and> (\<forall>(n, mg) \<in> set (fst r). \<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e)"
    proof -
      fix idx r st3 st4
      assume idx: "idx \<in> set (all_indices sizes)" and fr: "?ef data idx st3 = Inr (r, st4)"
      obtain v where lk: "fmlookup elems idx = Some v" using fmap_matches_sizes_lookup[OF fms idx] by blast
      have iv: "init_value env g elemTy v (ptr_add data (?off idx)) st3 = Inr (r, st4)" using fr lk by simp
      obtain gs' S' where r: "r = (gs', S')" by (cases r)
      show "used_le st3 st4 \<and> (\<forall>n \<in> set ((map fst \<circ> fst) r). n |\<notin>| CS_Used st3 \<and> n |\<in>| CS_Used st4) \<and> distinct ((map fst \<circ> fst) r)
        \<and> (\<forall>(n, mg) \<in> set (fst r). \<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e)"
        using 5(1)[OF ty refl refl idx lk iv[unfolded r] vts[OF lk]] unfolding r by simp
    qed
    show "used_le st1 st2 \<and> (\<forall>n \<in> set (concat (map (map fst \<circ> fst) rs)). n |\<notin>| CS_Used st1 \<and> n |\<in>| CS_Used st2)
      \<and> distinct (concat (map (map fst \<circ> fst) rs))
      \<and> (\<forall>r \<in> set rs. \<forall>(n, mg) \<in> set (fst r). \<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e)"
      using cg_mapM_names[OF ie, of "map fst \<circ> fst"] cg_mapM_all[OF ie, of "\<lambda>r. \<forall>(n, mg) \<in> set (fst r). \<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e"]
        step by blast
  qed
  show ?case
  proof (cases "dims_all_fixed dims")
    case True
    from 5(2)[unfolded unf] obtain rs where ie: "?initElems base st = Inr (rs, st')" and gs: "gs = concat (map fst rs)"
      using True by (auto simp: cg_return_def elim!: cg_bind_InrE)
    have eq: "map fst gs = concat (map (map fst \<circ> fst) rs)" unfolding gs by (simp add: map_concat)
    show ?thesis unfolding eq using elems[OF ie] gs by auto
  next
    case False
    have chk: "?chk" using 5(2)[unfolded unf] False by (auto simp: cg_fail_def split: if_splits)
    show ?thesis
    proof (cases "sizes_count sizes = 0")
      case True
      have "gs = []" "st' = st" using 5(2)[unfolded unf] False chk True by (auto simp: cg_return_def)
      then show ?thesis by simp
    next
      case nz: False
      from 5(2)[unfolded unf] obtain data st1 rs where fr: "fresh_name g (g @ [dollar] @ ''data'') st = Inr (data, st1)"
        and ie: "?initElems (ME_AddrOf data) st1 = Inr (rs, st')"
        and gs: "gs = (data, MG_Buf (buf_size (e_mul ?esz (u64_lit (sizes_count sizes))))) # concat (map fst rs)"
        using False chk nz by (auto simp: cg_return_def elim!: cg_bind_InrE)
      note fn = fresh_name_Inr[OF fr]
      have ul: "used_le st st1" using fn(2) by (auto simp: used_le_def less_eq_fset.rep_eq)
      have buf: "expr_is_int fmempty (buf_size (e_mul ?esz (u64_lit (sizes_count sizes))))"
        using data_buf_size_ok[OF closed, of env sizes fmempty] chk by (simp add: u64_ok_def expr_is_int_def fits_def)
      have eq: "map fst gs = data # concat (map (map fst \<circ> fst) rs)" unfolding gs by (simp add: map_concat)
      show ?thesis unfolding eq using elems[OF ie] fn(1,2) ul buf gs
        by (auto simp: used_le_def intro: used_le_trans[unfolded used_le_def])
    qed
  qed
qed (auto simp: cg_fail_def cg_return_def split: if_splits)

section \<open>Parameters and prototypes\<close>

lemma first_dup_None: "first_dup xs = None \<longleftrightarrow> distinct xs"
  by (induction xs) auto

lemma rk_cty_case: "(case rk of RK_Scalar cty \<Rightarrow> Some cty | _ \<Rightarrow> None) = rk_cty rk"
  by (cases rk) simp_all

(* Reserving the parameter names: they were all free, they are distinct,
   and they are in use afterwards. *)
lemma reserve_names:
  assumes "cg_mapM (\<lambda>(x, _). reserve_name (err x) x) ps st = Inr (us, st')"
  shows "distinct (map fst ps) \<and> (\<forall>x \<in> set (map fst ps). x |\<notin>| CS_Used st)
         \<and> fset (CS_Used st') = fset (CS_Used st) \<union> set (map fst ps)"
  using assms
proof (induction ps arbitrary: st us)
  case Nil
  then show ?case by (simp add: cg_mapM.simps)
next
  case (Cons p ps)
  obtain x c where p: "p = (x, c)" by (cases p)
  from Cons.prems obtain u st1 us' where r: "reserve_name (err x) x st = Inr (u, st1)"
    and rest: "cg_mapM (\<lambda>(x, _). reserve_name (err x) x) ps st1 = Inr (us', st')"
    unfolding p by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  note rn = reserve_name_Inr[OF r]
  have IH: "distinct (map fst ps) \<and> (\<forall>x \<in> set (map fst ps). x |\<notin>| CS_Used st1)
            \<and> fset (CS_Used st') = fset (CS_Used st1) \<union> set (map fst ps)"
    by (rule Cons.IH[OF rest])
  show ?case using IH rn unfolding p by auto
qed

(* What a successful name check of a function says. *)
lemma check_fun_names_Inr:
  assumes "check_fun_names funNames f cf info st = Inr (u, st')"
  shows "length (CF_Args cf) = length (FI_TmArgs info)" and "distinct (CF_Args cf)"
    and "\<And>x. x \<in> set (CF_Args cf) \<Longrightarrow> x |\<notin>| funNames"
    and "distinct (map fst (fun_params cf info))"
    and "\<And>x. x \<in> set (map fst (fun_params cf info)) \<Longrightarrow> x |\<notin>| CS_Used st"
    and "fset (CS_Used st') = fset (CS_Used st) \<union> set (map fst (fun_params cf info))"
proof -
  have A: "length (CF_Args cf) = length (FI_TmArgs info) \<and> first_dup (CF_Args cf) = None
        \<and> find (\<lambda>x. x |\<in>| funNames) (CF_Args cf) = None
        \<and> (\<exists>us. cg_mapM (\<lambda>(x, _). reserve_name (CGE_Internal f (''parameter '' @ x @ '' clashes with a global'')) x)
                   (fun_params cf info) st = Inr (us, st'))"
    using assms unfolding check_fun_names_def
    by (auto elim!: cg_bind_InrE split: if_splits option.splits)
  from A show "length (CF_Args cf) = length (FI_TmArgs info)" by blast
  from A show "distinct (CF_Args cf)" by (simp add: first_dup_None)
  from A show "\<And>x. x \<in> set (CF_Args cf) \<Longrightarrow> x |\<notin>| funNames" by (auto simp: find_None_iff)
  from A obtain us where R: "cg_mapM (\<lambda>(x, _). reserve_name (CGE_Internal f (''parameter '' @ x @ '' clashes with a global'')) x)
                                (fun_params cf info) st = Inr (us, st')" by blast
  note rn = reserve_names[OF R]
  from rn show "distinct (map fst (fun_params cf info))" by blast
  from rn show "\<And>x. x \<in> set (map fst (fun_params cf info)) \<Longrightarrow> x |\<notin>| CS_Used st" by blast
  from rn show "fset (CS_Used st') = fset (CS_Used st) \<union> set (map fst (fun_params cf info))" by blast
qed

(* Declaring distinct fresh parameters in the MiniC scope. *)
lemma declare_params_fresh:
  assumes "distinct (map fst ps)"
    and "\<And>x. x \<in> set (map fst ps) \<Longrightarrow> x \<notin> set ds \<and> x \<notin> set (fun_names (TC_Prog ctx)) \<and> x |\<notin>| fmdom E"
  shows "\<exists>E' ds'. declare_params ctx (E, ds) ps = Some (E', ds') \<and> env_le E E'
         \<and> (\<forall>x cty. (x, cty) \<in> set ps \<longrightarrow> fmlookup E' x = Some (VT_Scalar cty))
         \<and> (\<forall>x. x \<notin> set (map fst ps) \<longrightarrow> fmlookup E' x = fmlookup E x)
         \<and> fset (fmdom E') = fset (fmdom E) \<union> set (map fst ps) \<and> set ds' = set ds \<union> set (map fst ps)"
  using assms
proof (induction ps arbitrary: E ds)
  case Nil
  then show ?case by auto
next
  case (Cons p ps)
  obtain x cty where p: "p = (x, cty)" by (cases p)
  have xf: "x \<notin> set ds" "x \<notin> set (fun_names (TC_Prog ctx))" "x |\<notin>| fmdom E"
    using Cons.prems(2)[of x] by (simp_all add: p)
  have xps: "x \<notin> set (map fst ps)" using Cons.prems(1) by (simp add: p)
  let ?E1 = "fmupd x (VT_Scalar cty) E"
  have decl: "sc_declare ctx (E, ds) x (VT_Scalar cty) = Some (?E1, x # ds)"
    using xf by (simp add: sc_declare_def)
  have "\<exists>E' ds'. declare_params ctx (?E1, x # ds) ps = Some (E', ds') \<and> env_le ?E1 E'
         \<and> (\<forall>x cty. (x, cty) \<in> set ps \<longrightarrow> fmlookup E' x = Some (VT_Scalar cty))
         \<and> (\<forall>y. y \<notin> set (map fst ps) \<longrightarrow> fmlookup E' y = fmlookup ?E1 y)
         \<and> fset (fmdom E') = fset (fmdom ?E1) \<union> set (map fst ps) \<and> set ds' = set (x # ds) \<union> set (map fst ps)"
  proof (rule Cons.IH)
    show "distinct (map fst ps)" using Cons.prems(1) by simp
    fix y assume y: "y \<in> set (map fst ps)"
    then have "y \<noteq> x" using xps by auto
    then show "y \<notin> set (x # ds) \<and> y \<notin> set (fun_names (TC_Prog ctx)) \<and> y |\<notin>| fmdom ?E1"
      using Cons.prems(2)[of y] y by (simp add: p)
  qed
  then obtain E' ds' where dp: "declare_params ctx (?E1, x # ds) ps = Some (E', ds')" and le: "env_le ?E1 E'"
    and lk: "\<forall>x cty. (x, cty) \<in> set ps \<longrightarrow> fmlookup E' x = Some (VT_Scalar cty)"
    and other: "\<forall>y. y \<notin> set (map fst ps) \<longrightarrow> fmlookup E' y = fmlookup ?E1 y"
    and dom: "fset (fmdom E') = fset (fmdom ?E1) \<union> set (map fst ps)" and ds: "set ds' = set (x # ds) \<union> set (map fst ps)"
    by blast
  have le0: "env_le E E'" using env_le_trans[OF env_le_upd[OF xf(3)] le] .
  have lkx: "fmlookup E' x = Some (VT_Scalar cty)" using other xps by simp
  show ?case
    unfolding p using decl dp le0 lk lkx other dom ds by (intro exI[of _ E'] exI[of _ ds']) auto
qed

(* The representations of the parameters over the globals. *)
lemma fold_param_rep_lookup:
  "distinct (map fst ps) \<Longrightarrow>
   fmlookup (fold (\<lambda>(x, (ty, vor, _)). fmupd x (param_rep x ty vor)) ps base) y =
     (case map_of ps y of Some (ty, vor, _) \<Rightarrow> Some (param_rep y ty vor) | None \<Rightarrow> fmlookup base y)"
proof (induction ps arbitrary: base)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  obtain x ty vor gh where p: "p = (x, ty, vor, gh)" by (rule prod_cases4)
  have xps: "x \<notin> set (map fst ps)" using Cons.prems by (simp add: p)
  have dps: "distinct (map fst ps)" using Cons.prems by simp
  note IH = Cons.IH[OF dps, of "fmupd x (param_rep x ty vor) base"]
  show ?case
  proof (cases "y = x")
    case True
    have "map_of ps x = None" using xps by (simp add: map_of_eq_None_iff)
    then show ?thesis using IH True unfolding p by simp
  next
    case False
    then have ne: "x \<noteq> y" by (rule not_sym)
    show ?thesis using IH ne unfolding p by (auto split: option.splits)
  qed
qed

lemma map_of_zip_map_snd: "map_of (zip xs (map f ys)) k = map_option f (map_of (zip xs ys) k)"
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  then show ?case by (cases ys) auto
qed simp

lemma fun_params_ret:
  "ret_kind (FI_ReturnType info) = RK_Buf \<Longrightarrow> (ret_param, CTy_CharPtr) \<in> set (fun_params cf info)"
  by (simp add: fun_params_def)

lemma fun_params_size:
  "v \<in> set (FI_TyArgs info) \<Longrightarrow> (size_param v, CTy_U64) \<in> set (fun_params cf info)"
  by (simp add: fun_params_def)

lemma fun_params_arg:
  "(x, (ty, vor, gh)) \<in> set (zip (CF_Args cf) (FI_TmArgs info)) \<Longrightarrow> (x, param_cty ty vor) \<in> set (fun_params cf info)"
  unfolding fun_params_def by (force simp: image_iff)

(* The generator's environment of a function body, as lower_function
   builds it. *)
definition param_reps :: "CoreModule \<Rightarrow> CoreFunction \<Rightarrow> FunInfo \<Rightarrow> (string, VarRep) fmap" where
  "param_reps m cf info =
    fold (\<lambda>(x, (ty, vor, _)). fmupd x (param_rep x ty vor)) (zip (CF_Args cf) (FI_TmArgs info)) (global_reps (CM_TyEnv m))"

definition fun_cg :: "CoreModule \<Rightarrow> string \<Rightarrow> CoreFunction \<Rightarrow> FunInfo \<Rightarrow> CGEnv" where
  "fun_cg m f cf info =
    \<lparr> CG_TyEnv = module_body_env_for (CM_TyEnv m) (CF_Args cf) info, CG_Vars = param_reps m cf info,
      CG_Ret = ret_kind (FI_ReturnType info), CG_Fun = f \<rparr>"

lemma lower_function_Inr:
  assumes "lower_function m cnames funNames usedNames f cf = Inr mf"
  shows "\<exists>info u st1. fmlookup (TE_Functions (CM_TyEnv m)) f = Some info
    \<and> check_fun_names funNames f cf info \<lparr> CS_Counter = 0, CS_Used = usedNames \<rparr> = Inr (u, st1)
    \<and> MF_Name mf = f \<and> MF_Params mf = fun_params cf info
    \<and> MF_Ret mf = rk_cty (ret_kind (FI_ReturnType info))
    \<and> (CF_Body cf = None \<longrightarrow> MF_Extern mf \<noteq> None)
    \<and> (\<forall>body. CF_Body cf = Some body \<longrightarrow>
           MF_Extern mf = None \<and> (\<exists>cg' st2. lower_stmts (fun_cg m f cf info) body st1 = Inr ((MF_Body mf, cg'), st2)))"
proof -
  from assms obtain info where info: "fmlookup (TE_Functions (CM_TyEnv m)) f = Some info"
    unfolding lower_function_def by (auto split: option.splits)
  from assms obtain u st1 where chk: "check_fun_names funNames f cf info \<lparr> CS_Counter = 0, CS_Used = usedNames \<rparr> = Inr (u, st1)"
    unfolding lower_function_def Let_def by (auto simp: info split: sum.splits)
  have A: "MF_Name mf = f" "MF_Params mf = fun_params cf info" "MF_Ret mf = rk_cty (ret_kind (FI_ReturnType info))"
    using assms unfolding lower_function_def Let_def
    by (auto split: option.splits sum.splits prod.splits simp: info chk rk_cty_case)
  have B: "CF_Body cf = None \<longrightarrow> MF_Extern mf \<noteq> None"
    using assms unfolding lower_function_def Let_def by (auto split: option.splits sum.splits simp: info chk)
  have C: "\<forall>body. CF_Body cf = Some body \<longrightarrow>
      MF_Extern mf = None \<and> (\<exists>cg' st2. lower_stmts (fun_cg m f cf info) body st1 = Inr ((MF_Body mf, cg'), st2))"
  proof (intro allI impI)
    fix body assume b: "CF_Body cf = Some body"
    show "MF_Extern mf = None \<and> (\<exists>cg' st2. lower_stmts (fun_cg m f cf info) body st1 = Inr ((MF_Body mf, cg'), st2))"
      using assms unfolding lower_function_def Let_def
      by (auto split: sum.splits prod.splits simp: info chk b fun_cg_def param_reps_def)
  qed
  show ?thesis
    by (intro exI[of _ info] exI[of _ u] exI[of _ st1] conjI) (rule info chk A B C)+
qed

lemma lower_function_name:
  assumes "lower_function m cnames funNames usedNames f cf = Inr mf"
  shows "MF_Name mf = f"
  using lower_function_Inr[OF assms] by blast

(* The invariant holds at the start of a function body: the MiniC
   environment has the globals and the parameters. *)
lemma fun_cg_ok:
  assumes wf: "tyenv_well_formed (CM_TyEnv m)" and closed: "TE_TypeVars (CM_TyEnv m) = {||}"
    and info: "fmlookup (TE_Functions (CM_TyEnv m)) f = Some info"
    and len: "length (CF_Args cf) = length (FI_TmArgs info)" and dist: "distinct (CF_Args cf)"
    and prog: "prog_ok prog (CM_TyEnv m)"
    and tags: "\<And>d. dt_tags_fit (CM_TyEnv m) d"
    and retfits: "size_fits (CM_TyEnv m) 0 (\<lambda>_. 0) (FI_ReturnType info)"
    and G: "\<And>g ty. fmlookup (TE_GlobalVars (CM_TyEnv m)) g = Some ty \<Longrightarrow> fmlookup E g = Some (global_var_ty (global_decl (CM_TyEnv m) ty))"
    and P: "\<And>x cty. (x, cty) \<in> set (fun_params cf info) \<Longrightarrow> fmlookup E x = Some (VT_Scalar cty)"
  shows "cg_ok prog E (fun_cg m f cf info)"
proof -
  let ?env = "CM_TyEnv m"
  let ?benv = "module_body_env_for ?env (CF_Args cf) info"
  let ?cg = "fun_cg m f cf info"
  have abs: "TE_AbstractTypes ?env = {||}"
    using wf closed unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by simp
  have benv_simps: "TE_TypeVars ?benv = fset_of_list (FI_TyArgs info)" "TE_ReturnType ?benv = FI_ReturnType info"
    "TE_DataCtors ?benv = TE_DataCtors ?env" "TE_DataCtorsByType ?benv = TE_DataCtorsByType ?env"
    "TE_Functions ?benv = TE_Functions ?env" "TE_GlobalVars ?benv = TE_GlobalVars ?env"
    "TE_LocalVars ?benv = fmap_of_list (zip (CF_Args cf) (map fst (FI_TmArgs info)))"
    by (simp_all add: module_body_env_for_def abs)
  have dz: "distinct (map fst (zip (CF_Args cf) (FI_TmArgs info)))" using dist len by (simp add: map_fst_zip)
  have cgE: "CG_TyEnv ?cg = ?benv" "CG_Vars ?cg = param_reps m cf info" "CG_Ret ?cg = ret_kind (FI_ReturnType info)"
    by (simp_all add: fun_cg_def)
  show ?thesis
  proof (rule cg_okI)
    show "tyenv_well_formed (CG_TyEnv ?cg)"
      unfolding cgE by (rule module_body_env_for_well_formed[OF wf info len])
    show "sizes_in E (fset (TE_TypeVars (CG_TyEnv ?cg)))"
      using P[OF fun_params_size] unfolding cgE benv_simps sizes_in_def by (simp add: fset_of_list.rep_eq)
    show "CG_Ret ?cg = ret_kind (TE_ReturnType (CG_TyEnv ?cg))" by (simp add: cgE benv_simps)
    show "CG_Ret ?cg = RK_Buf \<Longrightarrow> fmlookup E ret_param = Some (VT_Scalar CTy_CharPtr)"
      using P[OF fun_params_ret] by (simp add: cgE)
    show "size_fits (CG_TyEnv ?cg) 0 (\<lambda>_. 0) (TE_ReturnType (CG_TyEnv ?cg))"
      using retfits unfolding cgE benv_simps(2) by (simp add: size_fits_cong_env[OF benv_simps(3,4)])
    show "\<And>d. dt_tags_fit (CG_TyEnv ?cg) d"
      using tags unfolding cgE by (simp add: dt_tags_fit_def dt_ctors_def benv_simps)
    show "prog_ok prog (CG_TyEnv ?cg)" using prog unfolding cgE by (simp add: prog_ok_def benv_simps)
    fix x rep assume lk: "fmlookup (CG_Vars ?cg) x = Some rep"
    show "\<exists>ty. tyenv_lookup_var (CG_TyEnv ?cg) x = Some ty \<and> rep_ok E (CG_TyEnv ?cg) ty rep"
    proof (cases "map_of (zip (CF_Args cf) (FI_TmArgs info)) x")
      case None
      then have nl: "fmlookup (TE_LocalVars ?benv) x = None"
        by (simp add: benv_simps fmlookup_of_list map_of_zip_map_snd)
      from None lk obtain ty where gty: "fmlookup (TE_GlobalVars ?env) x = Some ty" and rep: "rep = global_rep x ty"
        unfolding cgE param_reps_def by (auto simp: fold_param_rep_lookup[OF dz] global_reps_def)
      have "rep_ok E ?benv ty (global_rep x ty)"
        using G[OF gty] by (cases "scalar_ty ty") (auto simp: global_rep_def global_decl_def global_var_ty_def)
      then show ?thesis using nl gty rep unfolding cgE by (auto simp: tyenv_lookup_var_def benv_simps)
    next
      case (Some a)
      obtain ty vor gh where a: "a = (ty, vor, gh)" by (rule prod_cases3)
      have inz: "(x, (ty, vor, gh)) \<in> set (zip (CF_Args cf) (FI_TmArgs info))" using map_of_SomeD[OF Some] a by simp
      have ll: "fmlookup (TE_LocalVars ?benv) x = Some ty"
        by (simp add: benv_simps fmlookup_of_list map_of_zip_map_snd Some a)
      have rep: "rep = param_rep x ty vor" using lk Some a unfolding cgE param_reps_def by (simp add: fold_param_rep_lookup[OF dz])
      have Ex: "fmlookup E x = Some (VT_Scalar (param_cty ty vor))" using P[OF fun_params_arg[OF inz]] .
      have "rep_ok E ?benv ty (param_rep x ty vor)"
        using Ex unfolding param_rep_def param_cty_def param_by_ptr_def by (cases "scalar_ty ty"; cases vor) auto
      then show ?thesis using ll rep unfolding cgE by (auto simp: tyenv_lookup_var_def)
    qed
  qed
qed


section \<open>Facts from the pipeline's checks\<close>

lemma all_tags_fit:
  assumes "core_module_sizeable P m"
  shows "dt_tags_fit (CM_TyEnv m) d"
proof (cases "fmlookup (TE_DataCtorsByType (CM_TyEnv m)) d")
  case None
  then show ?thesis by (simp add: dt_tags_fit_def dt_ctors_def)
next
  case Some
  then show ?thesis using assms by (intro sizeable_tags_fit) simp_all
qed

lemma sizeable_fun_types:
  assumes "core_module_sizeable P m" and "fmlookup (CM_Functions m) f = Some cf"
  shows "\<exists>tys. fun_types m f = Some tys \<and> (\<forall>ty \<in> set tys. fits (CM_TyEnv m) ty)"
proof -
  have chk: "check_fun_sizes P m f = None" using sizeable_parts(5)[OF assms(1)] assms(2) by simp
  then obtain tys where ft: "fun_types m f = Some tys" by (auto simp: check_fun_sizes_def split: option.splits)
  have "\<And>ty. ty \<in> set tys \<Longrightarrow> fits (CM_TyEnv m) ty"
    unfolding fits_def by (rule sizeable_fun_type_fits[OF assms(1) _ ft]) (use assms(2) in simp_all)
  then show ?thesis using ft by blast
qed

lemma fun_types_body:
  assumes "fun_types m f = Some tys" and "fmlookup (CM_Functions m) f = Some cf"
    and "fmlookup (TE_Functions (CM_TyEnv m)) f = Some info"
  shows "FI_ReturnType info \<in> set tys"
    and "\<And>body. CF_Body cf = Some body \<Longrightarrow>
           \<exists>l. stmts_types (module_body_env_for (CM_TyEnv m) (CF_Args cf) info) body = Some l \<and> set l \<subseteq> set tys"
  using assms unfolding fun_types_def by (auto simp: Let_def split: option.splits)

lemma global_type_closed:
  assumes "tyenv_well_formed env" and "TE_TypeVars env = {||}" and "fmlookup (TE_GlobalVars env) g = Some ty"
  shows "type_tyvars ty = {}"
proof -
  have abs: "TE_AbstractTypes env = {||}"
    using assms(1,2) unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by simp
  have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
    using assms(1,3) unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  from is_well_kinded_type_tyvars_subset[OF this] show ?thesis by (simp add: abs)
qed

lemma in_sorted_list_of_fmap: "(k, v) \<in> set (sorted_list_of_fmap M) \<longleftrightarrow> fmlookup M k = Some v"
  by (auto simp: sorted_list_of_fmap_def fmlookup_dom_iff image_iff)

lemma distinct_sorted_list_of_fmap_keys: "distinct (map fst (sorted_list_of_fmap M))"
  by (simp add: sorted_list_of_fmap_def comp_def distinct_map inj_on_def sorted_list_of_fset.rep_eq)

lemma set_sorted_list_of_fmap_keys: "fst ` set (sorted_list_of_fmap M) = fset (fmdom M)"
  by (auto simp: sorted_list_of_fmap_def image_iff)

lemma set_map_fst_sorted_list_of_fmap: "set (map fst (sorted_list_of_fmap M)) = fset (fmdom M)"
  by (simp add: set_sorted_list_of_fmap_keys)

lemma check_module_names_None:
  assumes "check_module_names m = None"
  shows "''main'' \<notin> set (module_fun_names m)" and "''main'' |\<notin>| fmdom (TE_GlobalVars (CM_TyEnv m))"
    and "\<And>g. g |\<in>| fmdom (TE_GlobalVars (CM_TyEnv m)) \<Longrightarrow> g \<notin> set (module_fun_names m)"
proof -
  let ?globNames = "map fst (sorted_list_of_fmap (TE_GlobalVars (CM_TyEnv m)))"
  have A: "''main'' \<notin> set (module_fun_names m) \<and> ''main'' \<notin> set ?globNames
           \<and> find (\<lambda>g. g \<in> set (module_fun_names m)) ?globNames = None"
    using assms unfolding check_module_names_def Let_def by (auto split: if_splits option.splits)
  have S: "set ?globNames = fset (fmdom (TE_GlobalVars (CM_TyEnv m)))" by (rule set_map_fst_sorted_list_of_fmap)
  show "''main'' \<notin> set (module_fun_names m)" using A by blast
  show "''main'' |\<notin>| fmdom (TE_GlobalVars (CM_TyEnv m))" using A S by blast
  show "\<And>g. g |\<in>| fmdom (TE_GlobalVars (CM_TyEnv m)) \<Longrightarrow> g \<notin> set (module_fun_names m)"
    using A S unfolding find_None_iff by blast
qed

lemma check_main_None:
  assumes "check_main m mainName = None"
  obtains mainFn info where "fmlookup (CM_Functions m) mainName = Some mainFn"
    and "fmlookup (TE_Functions (CM_TyEnv m)) mainName = Some info"
    and "FI_TyArgs info = []" and "FI_TmArgs info = []" and "FI_ReturnType info = CoreTy_Record []"
  using assms unfolding check_main_def by (auto split: option.splits if_splits)

lemma lower_functions_Inr:
  "lower_functions m cnames funNames usedNames fcs = Inr mfs \<Longrightarrow>
   list_all2 (\<lambda>fc mf. lower_function m cnames funNames usedNames (fst fc) (snd fc) = Inr mf) fcs mfs"
proof (induction fcs arbitrary: mfs)
  case Nil
  then show ?case by simp
next
  case (Cons fc fcs)
  obtain f cf where fc: "fc = (f, cf)" by (cases fc)
  from Cons.prems obtain mf mfs' where "lower_function m cnames funNames usedNames f cf = Inr mf"
    and "lower_functions m cnames funNames usedNames fcs = Inr mfs'" and "mfs = mf # mfs'"
    unfolding fc by (auto split: sum.splits)
  then show ?case using Cons.IH by (simp add: fc)
qed

lemma find_append_cases: "find P (xs @ ys) = (case find P xs of None \<Rightarrow> find P ys | Some x \<Rightarrow> Some x)"
  by (induction xs) auto

lemma find_name_distinct:
  assumes "distinct (map MF_Name fs)" and "mf \<in> set fs"
  shows "find (\<lambda>x. MF_Name x = MF_Name mf) fs = Some mf"
  using assms by (induction fs) force+

lemma map_fst_global_var_ty: "map fst (map (\<lambda>(x, g). (x, global_var_ty g)) l) = map fst l"
  by (induction l) auto

lemma globals_env_lookup:
  assumes "distinct (map fst (MP_Globals prog))" and "(n, mg) \<in> set (MP_Globals prog)"
  shows "fmlookup (globals_env prog) n = Some (global_var_ty mg)"
proof -
  have "(n, global_var_ty mg) \<in> set (map (\<lambda>(x, g). (x, global_var_ty g)) (MP_Globals prog))" using assms(2) by force
  moreover have "distinct (map fst (map (\<lambda>(x, g). (x, global_var_ty g)) (MP_Globals prog)))"
    unfolding map_fst_global_var_ty by (rule assms(1))
  ultimately show ?thesis unfolding globals_env_def fmlookup_of_list by (intro map_of_is_SomeI)
qed

lemma globals_env_dom: "fset (fmdom (globals_env prog)) = set (map fst (MP_Globals prog))"
  unfolding globals_env_def fmdom_fmap_of_list map_fst_global_var_ty by (simp add: fset_of_list.rep_eq)


section \<open>The globals\<close>

(* The lowering of one global, as in lower_globals. *)
definition lower_global_f :: "CoreTyEnv \<Rightarrow> string \<times> CoreValue \<Rightarrow> ((string \<times> MGlobal) list \<times> MStmt list) CG" where
  "lower_global_f env = (\<lambda>(g, v). do {
      ty \<leftarrow> cg_lift g ''global without a declared type'' (fmlookup (TE_GlobalVars env) g);
      (gs, S) \<leftarrow> init_value env g ty v (ME_AddrOf g);
      cg_return ((g, global_decl env ty) # gs, S) })"

lemma lower_globals_unfold:
  "lower_globals m = do {
     rs \<leftarrow> cg_mapM (lower_global_f (CM_TyEnv m)) (sorted_list_of_fmap (CM_GlobalVars m));
     cg_return (concat (map fst rs), concat (map snd rs)) }"
  unfolding lower_globals_def lower_global_f_def by (rule refl)

lemma lower_global_f_InrE:
  assumes "lower_global_f env (g, v) st = Inr (r, st')"
  obtains ty gs S where "fmlookup (TE_GlobalVars env) g = Some ty"
    and "init_value env g ty v (ME_AddrOf g) st = Inr ((gs, S), st')"
    and "r = ((g, global_decl env ty) # gs, S)"
  using assms unfolding lower_global_f_def by (auto simp: cg_lift_Inr elim!: cg_bind_InrE split: prod.splits)

(* The names of the generated globals: the Core globals (in use from the
   start) and the fresh data buffers, all distinct. *)
lemma lower_globals_names:
  assumes "cg_mapM (lower_global_f env) gvs st = Inr (rs, st')"
    and "distinct (map fst gvs)" and "set (map fst gvs) \<subseteq> fset (CS_Used st)"
    and "\<And>g v. (g, v) \<in> set gvs \<Longrightarrow> \<exists>ty. fmlookup (TE_GlobalVars env) g = Some ty \<and> value_has_type env v ty"
  shows "used_le st st'
         \<and> distinct (map fst (concat (map fst rs)))
         \<and> set (map fst (concat (map fst rs))) \<subseteq> fset (CS_Used st')
         \<and> (\<forall>n mg. (n, mg) \<in> set (concat (map fst rs)) \<longrightarrow>
              (n \<in> set (map fst gvs) \<and> (\<exists>ty. fmlookup (TE_GlobalVars env) n = Some ty \<and> mg = global_decl env ty))
              \<or> (n \<notin> fset (CS_Used st) \<and> (\<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e)))
         \<and> (\<forall>g v. (g, v) \<in> set gvs \<longrightarrow> (\<exists>ty. fmlookup (TE_GlobalVars env) g = Some ty \<and> (g, global_decl env ty) \<in> set (concat (map fst rs))))"
  using assms
proof (induction gvs arbitrary: st rs)
  case Nil
  then show ?case by (simp add: cg_mapM.simps)
next
  case (Cons p gvs)
  obtain g v where p: "p = (g, v)" by (cases p)
  from Cons.prems(1) obtain r st1 rs' where fr: "lower_global_f env (g, v) st = Inr (r, st1)"
    and rest: "cg_mapM (lower_global_f env) gvs st1 = Inr (rs', st')" and rs: "rs = r # rs'"
    unfolding p by (auto simp: cg_mapM.simps elim!: cg_bind_InrE)
  from fr obtain ty gs S where gty: "fmlookup (TE_GlobalVars env) g = Some ty"
    and iv: "init_value env g ty v (ME_AddrOf g) st = Inr ((gs, S), st1)" and r: "r = ((g, global_decl env ty) # gs, S)"
    by (rule lower_global_f_InrE)
  have vt: "value_has_type env v ty" using Cons.prems(4)[of g v] gty by (simp add: p)
  note names = init_value_names[OF iv vt]
  have ul1: "used_le st st1" using names by blast
  have g_used: "g \<in> fset (CS_Used st)" using Cons.prems(3) by (simp add: p)
  have gvs_used: "set (map fst gvs) \<subseteq> fset (CS_Used st1)"
    using Cons.prems(3) ul1 by (auto simp: p used_le_def less_eq_fset.rep_eq)
  have IH: "used_le st1 st'
         \<and> distinct (map fst (concat (map fst rs')))
         \<and> set (map fst (concat (map fst rs'))) \<subseteq> fset (CS_Used st')
         \<and> (\<forall>n mg. (n, mg) \<in> set (concat (map fst rs')) \<longrightarrow>
              (n \<in> set (map fst gvs) \<and> (\<exists>ty. fmlookup (TE_GlobalVars env) n = Some ty \<and> mg = global_decl env ty))
              \<or> (n \<notin> fset (CS_Used st1) \<and> (\<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e)))
         \<and> (\<forall>g v. (g, v) \<in> set gvs \<longrightarrow> (\<exists>ty. fmlookup (TE_GlobalVars env) g = Some ty \<and> (g, global_decl env ty) \<in> set (concat (map fst rs'))))"
    using Cons.prems(2,4) gvs_used by (intro Cons.IH[OF rest]) (auto simp: p)
  have ul2: "used_le st1 st'" and dist2: "distinct (map fst (concat (map fst rs')))"
    and sub2: "set (map fst (concat (map fst rs'))) \<subseteq> fset (CS_Used st')"
    and kinds2: "\<forall>n mg. (n, mg) \<in> set (concat (map fst rs')) \<longrightarrow>
              (n \<in> set (map fst gvs) \<and> (\<exists>ty. fmlookup (TE_GlobalVars env) n = Some ty \<and> mg = global_decl env ty))
              \<or> (n \<notin> fset (CS_Used st1) \<and> (\<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e))"
    and cover2: "\<forall>g v. (g, v) \<in> set gvs \<longrightarrow> (\<exists>ty. fmlookup (TE_GlobalVars env) g = Some ty \<and> (g, global_decl env ty) \<in> set (concat (map fst rs')))"
    using IH by blast+
  have N1: "map fst (concat (map fst rs)) = (g # map fst gs) @ map fst (concat (map fst rs'))" by (simp add: rs r)
  have gs_fresh: "\<And>n. n \<in> set (map fst gs) \<Longrightarrow> n \<notin> fset (CS_Used st) \<and> n \<in> fset (CS_Used st1)" using names by blast
  have gs_fresh': "\<And>n mg. (n, mg) \<in> set gs \<Longrightarrow> n \<notin> fset (CS_Used st) \<and> n \<in> fset (CS_Used st1)"
    using gs_fresh by force
  have dist1: "distinct (g # map fst gs)" using names gs_fresh g_used by auto
  have g_notin_gvs: "g \<notin> set (map fst gvs)" using Cons.prems(2) by (simp add: p)
  have rest_names: "\<And>n. n \<in> set (map fst (concat (map fst rs'))) \<Longrightarrow> n \<in> set (map fst gvs) \<or> n \<notin> fset (CS_Used st1)"
  proof -
    fix n assume "n \<in> set (map fst (concat (map fst rs')))"
    then obtain q where "n = fst q" and "q \<in> set (concat (map fst rs'))" unfolding set_map by (rule imageE)
    then have "(n, snd q) \<in> set (concat (map fst rs'))" by simp
    then show "n \<in> set (map fst gvs) \<or> n \<notin> fset (CS_Used st1)" using kinds2 by blast
  qed
  have disj: "set (g # map fst gs) \<inter> set (map fst (concat (map fst rs'))) = {}"
  proof -
    { fix n assume n1: "n \<in> set (g # map fst gs)" and n2: "n \<in> set (map fst (concat (map fst rs')))"
      have "n \<in> fset (CS_Used st1)" using n1 g_used gs_fresh ul1 by (auto simp: used_le_def less_eq_fset.rep_eq)
      then have "n \<in> set (map fst gvs)" using rest_names[OF n2] by blast
      then have "n \<in> fset (CS_Used st)" using Cons.prems(3) by (auto simp: p)
      then have "n = g" using n1 gs_fresh by auto
      then have False using g_notin_gvs \<open>n \<in> set (map fst gvs)\<close> by simp }
    then show ?thesis by blast
  qed
  have dist: "distinct (map fst (concat (map fst rs)))" unfolding N1 using dist1 dist2 disj by (simp add: distinct_append)
  have sub: "set (map fst (concat (map fst rs))) \<subseteq> fset (CS_Used st')"
  proof -
    have "set (g # map fst gs) \<subseteq> fset (CS_Used st1)"
      using g_used gs_fresh gs_fresh' ul1 by (auto simp: used_le_def less_eq_fset.rep_eq)
    then show ?thesis unfolding N1 using sub2 ul2 by (auto simp: used_le_def less_eq_fset.rep_eq)
  qed
  have ul: "used_le st st'" using used_le_trans[OF ul1 ul2] .
  have kinds: "\<forall>n mg. (n, mg) \<in> set (concat (map fst rs)) \<longrightarrow>
              (n \<in> set (map fst (p # gvs)) \<and> (\<exists>ty. fmlookup (TE_GlobalVars env) n = Some ty \<and> mg = global_decl env ty))
              \<or> (n \<notin> fset (CS_Used st) \<and> (\<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e))"
  proof (intro allI impI)
    fix n mg assume "(n, mg) \<in> set (concat (map fst rs))"
    then have "(n, mg) = (g, global_decl env ty) \<or> (n, mg) \<in> set gs \<or> (n, mg) \<in> set (concat (map fst rs'))"
      by (auto simp: rs r)
    then show "(n \<in> set (map fst (p # gvs)) \<and> (\<exists>ty. fmlookup (TE_GlobalVars env) n = Some ty \<and> mg = global_decl env ty))
              \<or> (n \<notin> fset (CS_Used st) \<and> (\<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e))"
    proof (elim disjE)
      assume "(n, mg) = (g, global_decl env ty)"
      then show ?thesis using gty by (simp add: p)
    next
      assume "(n, mg) \<in> set gs"
      then show ?thesis using names gs_fresh by force
    next
      assume c3: "(n, mg) \<in> set (concat (map fst rs'))"
      show ?thesis using kinds2[rule_format, OF c3] ul1 by (auto simp: p used_le_def less_eq_fset.rep_eq)
    qed
  qed
  have cover: "\<forall>g' v'. (g', v') \<in> set (p # gvs) \<longrightarrow>
       (\<exists>ty. fmlookup (TE_GlobalVars env) g' = Some ty \<and> (g', global_decl env ty) \<in> set (concat (map fst rs)))"
  proof (intro allI impI)
    fix g' v' assume "(g', v') \<in> set (p # gvs)"
    then have "(g', v') = (g, v) \<or> (g', v') \<in> set gvs" by (simp add: p)
    then show "\<exists>ty. fmlookup (TE_GlobalVars env) g' = Some ty \<and> (g', global_decl env ty) \<in> set (concat (map fst rs))"
    proof
      assume "(g', v') = (g, v)"
      then show ?thesis using gty by (intro exI[of _ ty]) (simp add: rs r)
    next
      assume "(g', v') \<in> set gvs"
      then obtain ty' where "fmlookup (TE_GlobalVars env) g' = Some ty'"
        and "(g', global_decl env ty') \<in> set (concat (map fst rs'))" using cover2 by blast
      then show ?thesis by (intro exI[of _ ty']) (simp add: rs r)
    qed
  qed
  show ?case using ul dist sub kinds cover by blast
qed

(* The initialisation statements of the globals are typed in any
   environment that has every generated global. *)
lemma lower_globals_init_ok:
  assumes "cg_mapM (lower_global_f env) gvs st = Inr (rs, st')"
    and vt: "\<And>g v. (g, v) \<in> set gvs \<Longrightarrow> \<exists>ty. fmlookup (TE_GlobalVars env) g = Some ty \<and> value_has_type env v ty \<and> fits env ty"
    and wf: "tyenv_well_formed env" and tags: "\<And>d. dt_tags_fit env d"
    and G: "\<And>n mg. (n, mg) \<in> set (concat (map fst rs)) \<Longrightarrow> fmlookup G n = Some (global_var_ty mg)"
  shows "pure_ok prog rt G (concat (map snd rs))"
proof -
  have "\<forall>r \<in> set rs. (\<forall>n mg. (n, mg) \<in> set (fst r) \<longrightarrow> fmlookup G n = Some (global_var_ty mg)) \<longrightarrow> pure_ok prog rt G (snd r)"
  proof (rule cg_mapM_all[OF assms(1)])
    fix x r st1 st2
    assume x: "x \<in> set gvs" and fx: "lower_global_f env x st1 = Inr (r, st2)"
    obtain g v where xgv: "x = (g, v)" by (cases x)
    from fx obtain ty gs S where gty: "fmlookup (TE_GlobalVars env) g = Some ty"
      and iv: "init_value env g ty v (ME_AddrOf g) st1 = Inr ((gs, S), st2)" and r: "r = ((g, global_decl env ty) # gs, S)"
      unfolding xgv by (rule lower_global_f_InrE)
    have vtf: "value_has_type env v ty" "fits env ty" using vt[OF x[unfolded xgv]] gty by auto
    show "(\<forall>n mg. (n, mg) \<in> set (fst r) \<longrightarrow> fmlookup G n = Some (global_var_ty mg)) \<longrightarrow> pure_ok prog rt G (snd r)"
    proof
      assume A: "\<forall>n mg. (n, mg) \<in> set (fst r) \<longrightarrow> fmlookup G n = Some (global_var_ty mg)"
      have gE: "fmlookup G g = Some (global_var_ty (global_decl env ty))" using A by (simp add: r)
      show "pure_ok prog rt G (snd r)"
        unfolding r snd_conv
        by (rule init_value_ok[OF iv vtf wf tags]) (use A in \<open>auto simp: r intro!: expr_ok_AddrOf[OF gE]\<close>)
    qed
  qed
  then show ?thesis using G by (intro pure_ok_concat) auto
qed


section \<open>Functions\<close>

(* A generated function is well typed and well formed. *)
lemma lower_function_ok:
  assumes lf: "lower_function m cnames funNames usedNames f cf = Inr mf"
    and cf: "fmlookup (CM_Functions m) f = Some cf"
    and wt: "normalized_module_well_typed m" and closed: "core_module_closed m" and gf: "core_module_ghost_free m"
    and sz: "core_module_sizeable P m"
    and prog: "prog_ok prog (CM_TyEnv m)"
    and G: "\<And>g ty. fmlookup (TE_GlobalVars (CM_TyEnv m)) g = Some ty \<Longrightarrow>
              fmlookup (globals_env prog) g = Some (global_var_ty (global_decl (CM_TyEnv m) ty))"
    and dom: "fset (fmdom (globals_env prog)) \<subseteq> fset usedNames"
    and fn: "set (fun_names prog) \<subseteq> fset usedNames"
  shows "fun_ok prog mf" and "fun_wf prog mf"
proof -
  let ?env = "CM_TyEnv m"
  from lower_function_Inr[OF lf] obtain info u st1 where info: "fmlookup (TE_Functions ?env) f = Some info"
    and chk: "check_fun_names funNames f cf info \<lparr> CS_Counter = 0, CS_Used = usedNames \<rparr> = Inr (u, st1)"
    and name: "MF_Name mf = f" and params: "MF_Params mf = fun_params cf info"
    and ret: "MF_Ret mf = rk_cty (ret_kind (FI_ReturnType info))"
    and ext: "CF_Body cf = None \<longrightarrow> MF_Extern mf \<noteq> None"
    and body: "\<forall>body. CF_Body cf = Some body \<longrightarrow>
           MF_Extern mf = None \<and> (\<exists>cg' st2. lower_stmts (fun_cg m f cf info) body st1 = Inr ((MF_Body mf, cg'), st2))"
    by (elim exE conjE)
  let ?benv = "module_body_env_for ?env (CF_Args cf) info"
  note cfn = check_fun_names_Inr[OF chk]
  have wf: "tyenv_well_formed ?env" and fwt: "module_functions_well_typed ?env (CM_Functions m)"
    using wt unfolding normalized_module_well_typed_def by blast+
  have tv: "TE_TypeVars ?env = {||}" using closed unfolding core_module_closed_def by blast
  let ?ps = "fun_params cf info"
  let ?G = "globals_env prog"
  let ?ctx = "mk_ctx prog (MF_Ret mf)"
  have fresh: "\<And>x. x \<in> set (map fst ?ps) \<Longrightarrow> x \<notin> set [] \<and> x \<notin> set (fun_names (TC_Prog ?ctx)) \<and> x |\<notin>| fmdom ?G"
    using cfn(5) dom fn by auto
  obtain E0 ds0 where dp: "declare_params ?ctx (?G, []) ?ps = Some (E0, ds0)" and le: "env_le ?G E0"
    and lkP: "\<forall>x cty. (x, cty) \<in> set ?ps \<longrightarrow> fmlookup E0 x = Some (VT_Scalar cty)"
    and lkO: "\<forall>x. x \<notin> set (map fst ?ps) \<longrightarrow> fmlookup E0 x = fmlookup ?G x"
    and dom0: "fset (fmdom E0) = fset (fmdom ?G) \<union> set (map fst ?ps)" and ds0: "set ds0 = set (map fst ?ps)"
    using declare_params_fresh[OF cfn(4) fresh] by auto
  have ctx: "\<lparr> TC_Prog = prog, TC_Ret = MF_Ret mf \<rparr> = ?ctx" by (simp add: mk_ctx_def)
  (* the body of a non-extern function *)
  have bodyok: "\<And>body. CF_Body cf = Some body \<Longrightarrow>
      stmts_ok ?ctx (E0, ds0) (MF_Body mf) \<noteq> None \<and> stmts_wf prog False (MF_Body mf)"
  proof -
    fix body assume b: "CF_Body cf = Some body"
    let ?cg = "fun_cg m f cf info"
    from body b obtain cg' st2 where ls: "lower_stmts ?cg body st1 = Inr ((MF_Body mf, cg'), st2)" by blast
    have cgE: "CG_TyEnv ?cg = ?benv" "CG_Ret ?cg = ret_kind (FI_ReturnType info)" by (simp_all add: fun_cg_def)
    have benv_dc: "TE_DataCtors ?benv = TE_DataCtors ?env" "TE_DataCtorsByType ?benv = TE_DataCtorsByType ?env"
      by (simp_all add: module_body_env_for_def)
    obtain tys where ft: "fun_types m f = Some tys" and fits_tys: "\<And>ty. ty \<in> set tys \<Longrightarrow> fits ?env ty"
      using sizeable_fun_types[OF sz cf] by blast
    have retfits: "size_fits ?env 0 (\<lambda>_. 0) (FI_ReturnType info)"
      using fits_tys[OF fun_types_body(1)[OF ft cf info]] unfolding fits_def .
    have G': "\<And>g ty. fmlookup (TE_GlobalVars ?env) g = Some ty \<Longrightarrow> fmlookup E0 g = Some (global_var_ty (global_decl ?env ty))"
    proof -
      fix g ty assume gty: "fmlookup (TE_GlobalVars ?env) g = Some ty"
      have "g |\<in>| fmdom ?G" using G[OF gty] by (simp add: fmlookup_dom_iff)
      then have "g \<in> fset usedNames" using dom by auto
      then have "g \<notin> set (map fst ?ps)" using cfn(5) by auto
      then show "fmlookup E0 g = Some (global_var_ty (global_decl ?env ty))" using lkO G[OF gty] by simp
    qed
    have P': "\<And>x cty. (x, cty) \<in> set ?ps \<Longrightarrow> fmlookup E0 x = Some (VT_Scalar cty)" using lkP by blast
    have cgok: "cg_ok prog E0 ?cg"
      by (rule fun_cg_ok[OF wf tv info cfn(1,2) prog all_tags_fit[OF sz] retfits G' P'])
    have scope: "scope_ok prog (E0, ds0) st1"
      using dom0 ds0 cfn(6) dom fn unfolding scope_ok_def by auto
    obtain l where sl: "stmts_types ?benv body = Some l" and lsub: "set l \<subseteq> set tys"
      using fun_types_body(2)[OF ft cf info b] by blast
    have sfits: "stmts_fits (CG_TyEnv ?cg) body"
      unfolding cgE stmts_fits_def using sl fits_tys lsub fits_locals_irrelevant[OF benv_dc] by blast
    have ng: "FI_Ghost info = NotGhost" using gf info unfolding core_module_ghost_free_def by blast
    from fwt cf obtain info' where info': "fmlookup (TE_Functions ?env) f = Some info'"
      and C: "(case CF_Body cf of None \<Rightarrow> True
               | Some body \<Rightarrow> core_statement_list_type (module_body_env_for ?env (CF_Args cf) info') (FI_Ghost info') body \<noteq> None)"
      unfolding module_functions_well_typed_def by blast
    have typed0: "core_statement_list_type (module_body_env_for ?env (CF_Args cf) info') (FI_Ghost info') body \<noteq> None"
      using C[unfolded b] by simp
    have "info' = info" using info info' by simp
    then obtain env' where typed: "core_statement_list_type (CG_TyEnv ?cg) NotGhost body = Some env'"
      using typed0 ng unfolding cgE by auto
    obtain E' ds' where lo: "lowered_ok prog (rk_cty (CG_Ret ?cg)) (E0, ds0) st1 (MF_Body mf) st2 (E', ds')"
      by (rule lower_stmts_ok[OF ls cgok scope sfits typed])
    have so: "stmts_ok ?ctx (E0, ds0) (MF_Body mf) = Some (E', ds')"
      using lowered_ok_stmts_ok[OF lo] by (simp add: cgE ret)
    show "stmts_ok ?ctx (E0, ds0) (MF_Body mf) \<noteq> None \<and> stmts_wf prog False (MF_Body mf)"
      using so lowered_ok_wf[OF lo] by simp
  qed
  show "fun_ok prog mf"
    unfolding fun_ok_def Let_def ctx params dp using ext bodyok by (cases "CF_Body cf") auto
  show "fun_wf prog mf"
    unfolding fun_wf_def params using cfn(4) ext bodyok by (cases "CF_Body cf") auto
qed


section \<open>The typing theorem\<close>

theorem codegen_well_typed:
  assumes wt: "core_module_well_typed m" and closed: "core_module_closed m" and gf: "core_module_ghost_free m"
    and norm: "CM_TypeSubst m = fmempty" and sz: "core_module_sizeable P m"
    and cg: "codegen_module cnames mainName m = Inr prog"
  shows "program_wf prog" and "program_well_typed prog"
proof -
  let ?env = "CM_TyEnv m"
  have nwt: "normalized_module_well_typed m" using wt norm core_module_well_typed_on_normalized by blast
  have wf: "tyenv_well_formed ?env" and gwt: "module_globals_well_typed ?env (CM_GlobalVars m)"
    using nwt unfolding normalized_module_well_typed_def by blast+
  have tv: "TE_TypeVars ?env = {||}" and domG: "fmdom (TE_GlobalVars ?env) = fmdom (CM_GlobalVars m)"
    and domF: "fmdom (TE_Functions ?env) = fmdom (CM_Functions m)"
    using closed unfolding core_module_closed_def by blast+
  have tags: "\<And>d. dt_tags_fit ?env d" using all_tags_fit[OF sz] .
  (* the pieces of the generator *)
  let ?funNames = "fset_of_list (module_fun_names m)"
  let ?used0 = "?funNames |\<union>| fmdom (TE_GlobalVars ?env) |\<union>| {|''main''|}"
  let ?gst = "\<lparr> CS_Counter = 0, CS_Used = ?used0 \<rparr>"
  from cg obtain globals init gst' funs where
    cmn: "check_module_names m = None" and cm: "check_main m mainName = None"
    and lg: "lower_globals m ?gst = Inr ((globals, init), gst')"
    and lfs: "lower_functions m cnames ?funNames (CS_Used gst') (sorted_list_of_fmap (CM_Functions m)) = Inr funs"
    and prog: "prog = \<lparr> MP_Globals = globals, MP_Funcs = funs @ [main_fun mainName init] \<rparr>"
    unfolding codegen_module_def Let_def by (auto split: option.splits sum.splits prod.splits)
  note cmn' = check_module_names_None[OF cmn]
  from cm obtain mainFn mainInfo where mainFn: "fmlookup (CM_Functions m) mainName = Some mainFn"
    and mainInfo: "fmlookup (TE_Functions ?env) mainName = Some mainInfo"
    and mainTy: "FI_TyArgs mainInfo = []" "FI_TmArgs mainInfo = []" "FI_ReturnType mainInfo = CoreTy_Record []"
    by (rule check_main_None)
  (* the globals *)
  let ?gvs = "sorted_list_of_fmap (CM_GlobalVars m)"
  from lg obtain rs where lgm: "cg_mapM (lower_global_f ?env) ?gvs ?gst = Inr (rs, gst')"
    and globals: "globals = concat (map fst rs)" and init: "init = concat (map snd rs)"
    unfolding lower_globals_unfold by (auto elim!: cg_bind_InrE)
  have gvs_dist: "distinct (map fst ?gvs)" by (rule distinct_sorted_list_of_fmap_keys)
  have gvs_set: "set (map fst ?gvs) = fset (fmdom (TE_GlobalVars ?env))" by (simp add: set_sorted_list_of_fmap_keys domG)
  have gvs_used: "set (map fst ?gvs) \<subseteq> fset (CS_Used ?gst)" unfolding gvs_set by auto
  have gvs_vt: "\<And>g v. (g, v) \<in> set ?gvs \<Longrightarrow> \<exists>ty. fmlookup (TE_GlobalVars ?env) g = Some ty \<and> value_has_type ?env v ty \<and> fits ?env ty"
  proof -
    fix g v assume "(g, v) \<in> set ?gvs"
    then have "fmlookup (CM_GlobalVars m) g = Some v" by (simp add: in_sorted_list_of_fmap)
    then obtain ty where ty: "fmlookup (TE_GlobalVars ?env) g = Some ty" and "value_has_type ?env v ty"
      using gwt unfolding module_globals_well_typed_def by blast
    moreover have "fits ?env ty" unfolding fits_def by (rule sizeable_global_fits[OF sz ty]) simp
    ultimately show "\<exists>ty. fmlookup (TE_GlobalVars ?env) g = Some ty \<and> value_has_type ?env v ty \<and> fits ?env ty" by blast
  qed
  have gvs_vt2: "\<And>g v. (g, v) \<in> set ?gvs \<Longrightarrow> \<exists>ty. fmlookup (TE_GlobalVars ?env) g = Some ty \<and> value_has_type ?env v ty"
    using gvs_vt by blast
  note gn = lower_globals_names[OF lgm gvs_dist gvs_used gvs_vt2]
  have gn_ul: "used_le ?gst gst'" and gn_dist: "distinct (map fst globals)"
    and gn_sub: "set (map fst globals) \<subseteq> fset (CS_Used gst')"
    and gn_kinds: "\<forall>n mg. (n, mg) \<in> set globals \<longrightarrow>
              (n \<in> set (map fst ?gvs) \<and> (\<exists>ty. fmlookup (TE_GlobalVars ?env) n = Some ty \<and> mg = global_decl ?env ty))
              \<or> (n \<notin> fset (CS_Used ?gst) \<and> (\<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e))"
    and gn_cover: "\<forall>g v. (g, v) \<in> set ?gvs \<longrightarrow> (\<exists>ty. fmlookup (TE_GlobalVars ?env) g = Some ty \<and> (g, global_decl ?env ty) \<in> set globals)"
    using gn unfolding globals by blast+
  have prog_globals: "MP_Globals prog = globals" and prog_funcs: "MP_Funcs prog = funs @ [main_fun mainName init]"
    by (simp_all add: prog)
  let ?G = "globals_env prog"
  have G_lookup: "\<And>n mg. (n, mg) \<in> set globals \<Longrightarrow> fmlookup ?G n = Some (global_var_ty mg)"
    by (intro globals_env_lookup) (simp_all add: prog_globals gn_dist)
  have G_glob: "\<And>g ty. fmlookup (TE_GlobalVars ?env) g = Some ty \<Longrightarrow> fmlookup ?G g = Some (global_var_ty (global_decl ?env ty))"
  proof -
    fix g ty assume gty: "fmlookup (TE_GlobalVars ?env) g = Some ty"
    have "g |\<in>| fmdom (CM_GlobalVars m)" using fmdomI[OF gty] by (simp add: domG)
    then obtain v where "fmlookup (CM_GlobalVars m) g = Some v" by (auto simp: fmlookup_dom_iff)
    then have "(g, v) \<in> set ?gvs" by (simp add: in_sorted_list_of_fmap)
    then obtain ty' where "fmlookup (TE_GlobalVars ?env) g = Some ty'" and mem: "(g, global_decl ?env ty') \<in> set globals"
      using gn_cover by blast
    then have "ty' = ty" using gty by simp
    then show "fmlookup ?G g = Some (global_var_ty (global_decl ?env ty))" using G_lookup[OF mem] by simp
  qed
  have G_dom: "fset (fmdom ?G) \<subseteq> fset (CS_Used gst')" using globals_env_dom gn_sub prog_globals by simp
  (* the functions *)
  note la = lower_functions_Inr[OF lfs]
  have funs_names: "map MF_Name funs = module_fun_names m"
  proof -
    have "list_all2 (\<lambda>fc mf. MF_Name mf = fst fc) (sorted_list_of_fmap (CM_Functions m)) funs"
      using la by (rule list_all2_mono) (rule lower_function_name)
    then show ?thesis unfolding module_fun_names_def by (induction rule: list_all2_induct) simp_all
  qed
  have fun_names_prog: "fun_names prog = module_fun_names m @ [''main'']"
    by (simp add: fun_names_def prog funs_names main_fun_def)
  have fun_names_dist: "distinct (fun_names prog)"
    using cmn'(1) distinct_module_fun_names by (simp add: fun_names_prog)
  have fn_used: "set (fun_names prog) \<subseteq> fset (CS_Used gst')"
    using gn_ul by (auto simp: fun_names_prog used_le_def less_eq_fset.rep_eq fset_of_list.rep_eq)
  have lookup_funs: "\<And>f info. fmlookup (TE_Functions ?env) f = Some info \<Longrightarrow>
      \<exists>cf mf. fmlookup (CM_Functions m) f = Some cf \<and> mf \<in> set funs
              \<and> lower_function m cnames ?funNames (CS_Used gst') f cf = Inr mf \<and> lookup_fun prog f = Some mf"
  proof -
    fix f info assume fi: "fmlookup (TE_Functions ?env) f = Some info"
    have "f |\<in>| fmdom (CM_Functions m)" using fmdomI[OF fi] by (simp add: domF)
    then obtain cf where cf: "fmlookup (CM_Functions m) f = Some cf" by (auto simp: fmlookup_dom_iff)
    then have "(f, cf) \<in> set (sorted_list_of_fmap (CM_Functions m))" by (simp add: in_sorted_list_of_fmap)
    then obtain i where i: "i < length (sorted_list_of_fmap (CM_Functions m))" "sorted_list_of_fmap (CM_Functions m) ! i = (f, cf)"
      by (auto simp: in_set_conv_nth)
    have lf: "lower_function m cnames ?funNames (CS_Used gst') f cf = Inr (funs ! i)"
      and len: "length funs = length (sorted_list_of_fmap (CM_Functions m))"
      using la i unfolding list_all2_conv_all_nth by auto
    have mem: "funs ! i \<in> set funs" using i len by simp
    have name: "MF_Name (funs ! i) = f" using lower_function_name[OF lf] .
    have "find (\<lambda>x. MF_Name x = f) funs = Some (funs ! i)"
      using find_name_distinct[OF _ mem] fun_names_dist name by (simp add: fun_names_prog funs_names)
    then have "lookup_fun prog f = Some (funs ! i)" by (simp add: lookup_fun_def prog find_append_cases)
    then show "\<exists>cf mf. fmlookup (CM_Functions m) f = Some cf \<and> mf \<in> set funs
              \<and> lower_function m cnames ?funNames (CS_Used gst') f cf = Inr mf \<and> lookup_fun prog f = Some mf"
      using cf mem lf by blast
  qed
  have prog_ok: "prog_ok prog ?env"
    unfolding prog_ok_def
  proof (intro allI impI)
    fix f info assume info: "fmlookup (TE_Functions ?env) f = Some info"
    have ngp: "no_ghost_params info" using gf info unfolding core_module_ghost_free_def by blast
    from lookup_funs[OF info] obtain cf mf where mf: "mf \<in> set funs"
      and lf: "lower_function m cnames ?funNames (CS_Used gst') f cf = Inr mf" and lk: "lookup_fun prog f = Some mf" by blast
    from lower_function_Inr[OF lf] obtain info' u st1 where info': "fmlookup (TE_Functions ?env) f = Some info'"
      and chk: "check_fun_names ?funNames f cf info' \<lparr> CS_Counter = 0, CS_Used = CS_Used gst' \<rparr> = Inr (u, st1)"
      and params: "MF_Params mf = fun_params cf info'" and ret: "MF_Ret mf = rk_cty (ret_kind (FI_ReturnType info'))"
      by (elim exE conjE)
    have eq: "info' = info" using info info' by simp
    have mp: "map snd (MF_Params mf) = param_ctys info"
      using params fun_params_ctys[OF check_fun_names_Inr(1)[OF chk]] unfolding eq by simp
    have mr: "MF_Ret mf = rk_cty (ret_kind (FI_ReturnType info))" using ret unfolding eq by simp
    show "no_ghost_params info \<and> (\<exists>fn. lookup_fun prog f = Some fn \<and> map snd (MF_Params fn) = param_ctys info
                                     \<and> MF_Ret fn = rk_cty (ret_kind (FI_ReturnType info)))"
      using ngp lk mp mr by (intro conjI exI[of _ mf]) simp_all
  qed
  have funs_ok: "\<And>mf. mf \<in> set funs \<Longrightarrow> fun_ok prog mf \<and> fun_wf prog mf"
  proof -
    fix mf assume "mf \<in> set funs"
    then obtain i where i: "i < length funs" "funs ! i = mf" by (auto simp: in_set_conv_nth)
    obtain f cf where fc: "sorted_list_of_fmap (CM_Functions m) ! i = (f, cf)"
      by (cases "sorted_list_of_fmap (CM_Functions m) ! i")
    have len: "length funs = length (sorted_list_of_fmap (CM_Functions m))" using la by (simp add: list_all2_conv_all_nth)
    have lf: "lower_function m cnames ?funNames (CS_Used gst') f cf = Inr mf"
      using la i fc unfolding list_all2_conv_all_nth by auto
    have "(f, cf) \<in> set (sorted_list_of_fmap (CM_Functions m))"
      using nth_mem[of i "sorted_list_of_fmap (CM_Functions m)"] i len fc by simp
    then have cf: "fmlookup (CM_Functions m) f = Some cf" by (simp add: in_sorted_list_of_fmap)
    show "fun_ok prog mf \<and> fun_wf prog mf"
      using lower_function_ok[OF lf cf nwt closed gf sz prog_ok G_glob G_dom fn_used] by blast
  qed
  (* the generated main *)
  let ?main = "main_fun mainName init"
  have main_lookup: "lookup_fun prog ''main'' = Some ?main"
  proof -
    have "find (\<lambda>x. MF_Name x = ''main'') funs = None"
      using cmn'(1) unfolding funs_names[symmetric] find_None_iff by (auto simp: image_iff)
    then show ?thesis by (simp add: lookup_fun_def prog find_append_cases main_fun_def)
  qed
  obtain mainMf where mainMf: "lookup_fun prog mainName = Some mainMf" "MF_Params mainMf = []"
  proof -
    from prog_ok mainInfo obtain fn where "lookup_fun prog mainName = Some fn" "map snd (MF_Params fn) = param_ctys mainInfo"
      unfolding prog_ok_def by blast
    moreover have "param_ctys mainInfo = []" by (simp add: param_ctys_def mainTy ret_kind_def)
    ultimately show thesis using that by simp
  qed
  have init_ok: "pure_ok prog (Some CTy_I32) ?G init"
    unfolding init by (rule lower_globals_init_ok[OF lgm gvs_vt wf tags]) (assumption, rule G_lookup[unfolded globals])
  have main_ok: "fun_ok prog ?main"
  proof -
    let ?ctx = "mk_ctx prog (Some CTy_I32)"
    have c1: "stmts_ok ?ctx (?G, []) init = Some (?G, [])" by (rule pure_ok_stmts_ok[OF init_ok])
    have c2: "stmt_ok ?ctx (?G, []) (MS_Call None mainName []) = Some (?G, [])" using mainMf by simp
    have c3: "stmt_ok ?ctx (?G, []) (MS_Return (Some (ME_Int Signed IntBits_32 0))) = Some (?G, [])"
      by (simp add: expr_compat_def)
    have "stmts_ok ?ctx (?G, []) (init @ [MS_Call None mainName [], MS_Return (Some (ME_Int Signed IntBits_32 0))]) = Some (?G, [])"
      using c1 c2 c3 by (simp add: stmts_ok_append)
    then show ?thesis unfolding fun_ok_def main_fun_def Let_def by (simp add: mk_ctx_def)
  qed
  have main_wf: "fun_wf prog ?main"
    using pure_ok_wf[OF init_ok, of False] mainMf by (simp add: fun_wf_def main_fun_def stmts_wf_append)
  (* the globals are well typed *)
  have globals_ok: "\<And>x. x \<in> set globals \<Longrightarrow> global_ok prog x"
  proof -
    fix x assume x: "x \<in> set globals"
    obtain n mg where xnm: "x = (n, mg)" by (cases x)
    from gn_kinds x have "(n \<in> set (map fst ?gvs) \<and> (\<exists>ty. fmlookup (TE_GlobalVars ?env) n = Some ty \<and> mg = global_decl ?env ty))
              \<or> (n \<notin> fset (CS_Used ?gst) \<and> (\<exists>e. mg = MG_Buf e \<and> expr_is_int fmempty e))" unfolding xnm by blast
    then show "global_ok prog x" unfolding xnm
    proof (elim disjE conjE exE)
      fix ty assume n: "n \<in> set (map fst ?gvs)" and ty: "fmlookup (TE_GlobalVars ?env) n = Some ty" and mg: "mg = global_decl ?env ty"
      have nd: "n |\<in>| fmdom (TE_GlobalVars ?env)" using n unfolding gvs_set .
      have nf: "n \<notin> set (fun_names prog)" using cmn'(2) cmn'(3)[OF nd] nd by (auto simp: fun_names_prog)
      have closed_ty: "type_tyvars ty = {}" by (rule global_type_closed[OF wf tv ty])
      have fits_ty: "fits ?env ty" unfolding fits_def by (rule sizeable_global_fits[OF sz ty]) simp
      have "u64_ok fmempty (buf_size (size_of ?env ty))" by (rule buf_size_ok[OF size_of_closed_ok[OF closed_ty fits_ty]])
      then show "global_ok prog (n, mg)" using nf unfolding global_ok_def mg global_decl_def
        by (auto simp: u64_ok_def expr_is_int_def split: option.splits)
    next
      fix e assume n: "n \<notin> fset (CS_Used ?gst)" and mg: "mg = MG_Buf e" and e: "expr_is_int fmempty e"
      have "n \<notin> set (fun_names prog)" using n by (auto simp: fun_names_prog fset_of_list.rep_eq)
      then show "global_ok prog (n, mg)" using mg e by (simp add: global_ok_def)
    qed
  qed
  show "program_wf prog"
  proof -
    have "list_all (fun_wf prog) (MP_Funcs prog)" using funs_ok main_wf by (auto simp: prog list_all_iff)
    then show ?thesis using fun_names_dist[unfolded fun_names_def] gn_dist main_lookup
      unfolding program_wf_def by (simp add: prog main_fun_def)
  qed
  show "program_well_typed prog"
    unfolding program_well_typed_def using globals_ok funs_ok main_ok by (auto simp: prog list_all_iff)
qed

end

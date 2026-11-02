theory CoreLayout
  imports Babylon.CoreValue Babylon.MiniCMemory
    "HOL-Library.Char_ord" "HOL-Library.List_Lexorder"
begin

(* ========================================================================== *)
(* The byte layout of Core types (minic/DESIGN.md, sections 2.3 and 3.2)      *)
(* ========================================================================== *)

(* This theory gives, for a Core type, the number of bytes of its C
   representation and the offsets of its components, exactly as
   docs/c-interface.md prescribes:

     bool                      1 byte (uint8_t)
     iN / uN                   N/8 bytes
     extern type               P bytes (a void pointer; P is the pointer size)
     record {f1: T1, ...}      |T1| + ... (packed, declaration order)
     datatype D<args>          tag + max over the constructors of the payload size
     fixed array T[n1, .., nd] |T| * n1 * ... * nd, Fortran order
     allocatable / incomplete  P + 8d (a descriptor: data pointer, then one
                               uint64_t per dimension)
     type variable T           the size assigned to T (a run-time parameter)
     int / real                0 (ghost-only types; they never reach the
                               code generator)

   The functions are parametrised by the datatype tables of a CoreTyEnv
   (only TE_DataCtors and TE_DataCtorsByType are read: tsz_cong_env), the
   pointer size P, and an assignment sz of sizes to type variables.

   Recursion through datatype payloads is not structural, so the size
   function is fuelled: tsz spends one unit of fuel on each datatype
   unfolding and none elsewhere. The payload of a constructor is measured
   *uninstantiated*, with the sizes of the type arguments as the assignment
   of its type variables (tsz_subst shows this equals measuring the
   substituted payload). type_size fixes the fuel at one more than the number
   of datatypes; DatatypeAcyclic.thy shows that this is enough whenever the
   datatypes are acyclic, and derives the unfolding equation for datatypes
   (type_size_Datatype). All other equations hold unconditionally. *)


section \<open>Helpers\<close>

(* The maximum of a list of naturals (0 for the empty list). *)
definition max_list :: "nat list \<Rightarrow> nat" where
  "max_list xs = foldr max xs 0"

lemma max_list_Nil [simp]: "max_list [] = 0"
  by (simp add: max_list_def)

lemma max_list_Cons [simp]: "max_list (x # xs) = max x (max_list xs)"
  by (simp add: max_list_def)

lemma max_list_ge: "x \<in> set xs \<Longrightarrow> x \<le> max_list xs"
  by (induction xs) auto

lemma max_list_le: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<le> b) \<Longrightarrow> max_list xs \<le> b"
  by (induction xs) auto

lemma max_list_ge_map: "x \<in> set xs \<Longrightarrow> f x \<le> max_list (map f xs)"
  by (induction xs) (auto intro: order_trans[OF _ max.cobounded2])

lemma max_list_mono:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x) \<Longrightarrow> max_list (map f xs) \<le> max_list (map g xs)"
  by (induction xs) (auto intro: order_trans[OF _ max.cobounded1] order_trans[OF _ max.cobounded2])

lemma max_list_cong:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> max_list (map f xs) = max_list (map g xs)"
  by (induction xs) auto

lemma max_list_eq_0: "max_list xs = 0 \<longleftrightarrow> (\<forall>x \<in> set xs. x = 0)"
  by (induction xs) auto

lemma sum_list_mono_nat:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x \<le> g x) \<Longrightarrow> sum_list (map f xs) \<le> sum_list (map (g :: 'a \<Rightarrow> nat) xs)"
  by (induction xs) (auto intro: add_mono)

lemma sum_list_cong:
  "(\<And>x. x \<in> set xs \<Longrightarrow> f x = g x) \<Longrightarrow> sum_list (map f xs) = sum_list (map g xs)"
  by (induction xs) auto

(* The size assigned to each type variable of a list, given the sizes of the
   corresponding type arguments (0 for a variable not in the list). *)
definition tyvar_sizes :: "string list \<Rightarrow> nat list \<Rightarrow> string \<Rightarrow> nat" where
  "tyvar_sizes tyvars sizes v = (case map_of (zip tyvars sizes) v of Some n \<Rightarrow> n | None \<Rightarrow> 0)"

lemma tyvar_sizes_mono:
  assumes "list_all2 (\<le>) sizes sizes'"
  shows "tyvar_sizes tyvars sizes v \<le> tyvar_sizes tyvars sizes' v"
  using assms
proof (induction tyvars arbitrary: sizes sizes')
  case Nil
  then show ?case by (simp add: tyvar_sizes_def)
next
  case (Cons t ts)
  show ?case
  proof (cases sizes)
    case Nil
    with Cons.prems have "sizes' = []" by simp
    with Nil show ?thesis by (simp add: tyvar_sizes_def)
  next
    case (Cons s ss)
    with Cons.prems obtain s' ss' where sizes': "sizes' = s' # ss'" and le: "s \<le> s'"
      and rest: "list_all2 (\<le>) ss ss'"
      by (auto simp: list_all2_Cons1)
    show ?thesis
      using Cons.IH[OF rest] le Cons sizes' by (simp add: tyvar_sizes_def)
  qed
qed

(* Only the sizes of the listed type variables matter. *)
lemma tyvar_sizes_notin: "v \<notin> set tyvars \<Longrightarrow> tyvar_sizes tyvars sizes v = 0"
  by (auto simp: tyvar_sizes_def split: option.splits dest!: map_of_SomeD set_zip_leftD)


section \<open>Datatype tables\<close>

(* The constructors of a datatype, in declaration order (empty for an unknown
   datatype). *)
definition dt_ctors :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> string list" where
  "dt_ctors env dtName = (case fmlookup (TE_DataCtorsByType env) dtName of Some cs \<Rightarrow> cs | None \<Rightarrow> [])"

(* The tag width for a datatype with k constructors (get_tag_size in
   src/codegen.c): uint8_t up to 256 constructors, uint16_t up to 65536,
   uint32_t beyond. *)
definition tag_bits_of :: "nat \<Rightarrow> IntBits" where
  "tag_bits_of k = (if k \<le> 256 then IntBits_8 else if k \<le> 65536 then IntBits_16 else IntBits_32)"

definition tag_bits :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> IntBits" where
  "tag_bits env dtName = tag_bits_of (length (dt_ctors env dtName))"

definition tag_ty :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> CTy" where
  "tag_ty env dtName = CTy_Int Unsigned (tag_bits env dtName)"

definition tag_size :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> nat" where
  "tag_size env dtName = byte_width (tag_bits env dtName)"

lemma tag_size_cases: "tag_size env dtName \<in> {1, 2, 4}"
  by (simp add: tag_size_def tag_bits_def tag_bits_of_def)

lemma tag_size_pos: "tag_size env dtName > 0"
  using tag_size_cases[of env dtName] by auto

lemma tag_size_le_4: "tag_size env dtName \<le> 4"
  using tag_size_cases[of env dtName] by auto

lemma length_takeWhile_neq_lt: "x \<in> set xs \<Longrightarrow> length (takeWhile (\<lambda>c. c \<noteq> x) xs) < length xs"
  by (induction xs) auto

(* The tag of a constructor is its index in its datatype's constructor list. *)
definition ctor_tag :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> string \<Rightarrow> nat" where
  "ctor_tag env dtName ctor = length (takeWhile (\<lambda>c. c \<noteq> ctor) (dt_ctors env dtName))"

lemma ctor_tag_lt:
  assumes "ctor \<in> set (dt_ctors env dtName)"
  shows "ctor_tag env dtName ctor < length (dt_ctors env dtName)"
  unfolding ctor_tag_def using assms by (rule length_takeWhile_neq_lt)

lemma ctor_tag_nth:
  assumes "ctor \<in> set (dt_ctors env dtName)"
  shows "dt_ctors env dtName ! ctor_tag env dtName ctor = ctor"
  unfolding ctor_tag_def using nth_length_takeWhile[OF length_takeWhile_neq_lt[OF assms]] by simp

(* A datatype's tags fit its tag type when it has at most 2^32 constructors
   (codegen.c aborts with "too many variants" beyond that; the static checker
   of SizeBound.thy checks this for every datatype). *)
definition dt_tags_fit :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> bool" where
  "dt_tags_fit env dtName = (length (dt_ctors env dtName) \<le> 2 ^ 32)"

(* The tag of a constructor fits the datatype's tag type. *)
lemma ctor_tag_fits:
  assumes "ctor \<in> set (dt_ctors env dtName)" and "dt_tags_fit env dtName"
  shows "int_fits Unsigned (tag_bits env dtName) (int (ctor_tag env dtName ctor))"
proof -
  have lt: "ctor_tag env dtName ctor < length (dt_ctors env dtName)" by (rule ctor_tag_lt[OF assms(1)])
  show ?thesis
    unfolding int_fits_unsigned tag_bits_def tag_bits_of_def
    using lt assms(2) unfolding dt_tags_fit_def by (auto split: if_splits)
qed

lemma ctor_tag_first: "dt_ctors env dtName = c # cs \<Longrightarrow> ctor_tag env dtName c = 0"
  by (simp add: ctor_tag_def)

(* Distinct constructors have distinct tags. *)
lemma ctor_tag_inj:
  assumes "ctor1 \<in> set (dt_ctors env dtName)" and "ctor2 \<in> set (dt_ctors env dtName)"
    and "ctor_tag env dtName ctor1 = ctor_tag env dtName ctor2"
  shows "ctor1 = ctor2"
proof -
  have "ctor1 = dt_ctors env dtName ! ctor_tag env dtName ctor1" using ctor_tag_nth[OF assms(1)] by simp
  also have "\<dots> = dt_ctors env dtName ! ctor_tag env dtName ctor2" using assms(3) by simp
  also have "\<dots> = ctor2" by (rule ctor_tag_nth[OF assms(2)])
  finally show ?thesis .
qed


section \<open>Array dimensions\<close>

(* Are all dimensions fixed? (Otherwise the array is a descriptor.) *)
definition dims_all_fixed :: "CoreDimension list \<Rightarrow> bool" where
  "dims_all_fixed dims = list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims"

(* The size of a fixed dimension (0 for a non-fixed one; only used when all
   dimensions are fixed, where a well-kinded dimension is non-negative). *)
fun dim_size :: "CoreDimension \<Rightarrow> nat" where
  "dim_size (CoreDim_Fixed n) = nat n"
| "dim_size _ = 0"

(* The number of elements of a fixed array. *)
definition dims_count :: "CoreDimension list \<Rightarrow> nat" where
  "dims_count dims = prod_list (map dim_size dims)"

(* The sizes of a fixed array, as the int list that CV_Array carries. *)
definition dims_sizes :: "CoreDimension list \<Rightarrow> int list" where
  "dims_sizes dims = map (int \<circ> dim_size) dims"

lemma length_dims_sizes [simp]: "length (dims_sizes dims) = length dims"
  by (simp add: dims_sizes_def)

(* The number of elements of an array with the given run-time sizes
   (sizes_valid: all non-negative). *)
definition sizes_count :: "int list \<Rightarrow> nat" where
  "sizes_count sizes = prod_list (map nat sizes)"

lemma sizes_count_dims_sizes [simp]: "sizes_count (dims_sizes dims) = dims_count dims"
  by (simp add: sizes_count_def dims_sizes_def dims_count_def comp_def)

(* The flat (Fortran-order) index of a multi-dimensional index: the first
   index varies fastest.  flat_index [n1, n2, n3] [i1, i2, i3]
     = i1 + n1 * (i2 + n2 * i3). *)
fun flat_index :: "int list \<Rightarrow> int list \<Rightarrow> int" where
  "flat_index (n # ns) (i # is) = i + n * flat_index ns is"
| "flat_index _ _ = 0"

(* An index is in bounds for the given sizes. *)
definition index_in_bounds :: "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "index_in_bounds sizes idx =
    (length idx = length sizes \<and> (\<forall>k < length sizes. 0 \<le> idx ! k \<and> idx ! k < sizes ! k))"

lemma index_in_bounds_Nil [simp]: "index_in_bounds [] idx \<longleftrightarrow> idx = []"
  by (simp add: index_in_bounds_def)

lemma index_in_bounds_Cons:
  "index_in_bounds (n # ns) idx \<longleftrightarrow>
     (\<exists>i is. idx = i # is \<and> 0 \<le> i \<and> i < n \<and> index_in_bounds ns is)"
proof
  assume H: "index_in_bounds (n # ns) idx"
  then obtain i "is" where idx: "idx = i # is" unfolding index_in_bounds_def by (cases idx) auto
  from H idx have "0 \<le> i" "i < n" unfolding index_in_bounds_def by (auto dest: spec[of _ 0])
  moreover from H idx have "index_in_bounds ns is"
    unfolding index_in_bounds_def by (auto dest: spec[of _ "Suc _"])
  ultimately show "\<exists>i is. idx = i # is \<and> 0 \<le> i \<and> i < n \<and> index_in_bounds ns is" using idx by blast
next
  assume "\<exists>i is. idx = i # is \<and> 0 \<le> i \<and> i < n \<and> index_in_bounds ns is"
  then show "index_in_bounds (n # ns) idx"
    unfolding index_in_bounds_def by (auto simp: nth_Cons split: nat.splits)
qed

(* Membership in all_indices (CoreValue.thy) is exactly being in bounds. *)
lemma in_all_indices_iff: "idx \<in> set (all_indices sizes) \<longleftrightarrow> index_in_bounds sizes idx"
proof (induction sizes arbitrary: idx)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  show ?case
  proof
    assume "idx \<in> set (all_indices (n # ns))"
    then obtain i "is" where idx: "idx = i # is" and i_in: "i \<in> set (map int [0..<nat n])"
      and is_in: "is \<in> set (all_indices ns)"
      by (auto simp: Let_def)
    from i_in have "0 \<le> i" "i < n" by auto
    with idx is_in Cons.IH show "index_in_bounds (n # ns) idx"
      by (auto simp: index_in_bounds_Cons)
  next
    assume "index_in_bounds (n # ns) idx"
    then obtain i "is" where idx: "idx = i # is" and bnds: "0 \<le> i" "i < n"
      and is_ok: "index_in_bounds ns is"
      by (auto simp: index_in_bounds_Cons)
    have "i \<in> set (map int [0..<nat n])"
      using bnds by (auto simp: image_iff zless_nat_conj intro!: bexI[where x = "nat i"])
    with idx is_ok Cons.IH show "idx \<in> set (all_indices (n # ns))"
      by (auto simp: Let_def)
  qed
qed

(* An in-bounds index has a flat index below the element count. *)
lemma flat_index_bounds:
  assumes "index_in_bounds sizes idx"
  shows "0 \<le> flat_index sizes idx \<and> flat_index sizes idx < int (sizes_count sizes)"
  using assms
proof (induction sizes arbitrary: idx)
  case Nil
  then show ?case by (simp add: sizes_count_def)
next
  case (Cons n ns)
  from Cons.prems obtain i "is" where idx: "idx = i # is" and i_bnds: "0 \<le> i" "i < n"
    and is_ok: "index_in_bounds ns is"
    by (auto simp: index_in_bounds_Cons)
  from Cons.IH[OF is_ok] have ih: "0 \<le> flat_index ns is" "flat_index ns is < int (sizes_count ns)" by auto
  have n_eq: "int (nat n) = n" using i_bnds by simp
  have "flat_index ns is + 1 \<le> int (sizes_count ns)" using ih by simp
  hence "n * (flat_index ns is + 1) \<le> n * int (sizes_count ns)"
    using i_bnds by (intro mult_left_mono) auto
  hence "i + n * flat_index ns is < n * int (sizes_count ns)"
    using i_bnds by (simp add: algebra_simps)
  moreover have "int (sizes_count (n # ns)) = int (nat n) * int (sizes_count ns)"
    by (simp add: sizes_count_def)
  ultimately show ?case using idx ih i_bnds n_eq by simp
qed

(* Distinct in-bounds indices have distinct flat indices (so that the byte
   ranges of distinct elements are disjoint). *)
lemma flat_index_inj:
  assumes "index_in_bounds sizes idx1" and "index_in_bounds sizes idx2"
    and "flat_index sizes idx1 = flat_index sizes idx2"
  shows "idx1 = idx2"
  using assms
proof (induction sizes arbitrary: idx1 idx2)
  case Nil
  then show ?case by simp
next
  case (Cons n ns)
  from Cons.prems(1) obtain i1 is1 where idx1: "idx1 = i1 # is1" and b1: "0 \<le> i1" "i1 < n"
    and ok1: "index_in_bounds ns is1" by (auto simp: index_in_bounds_Cons)
  from Cons.prems(2) obtain i2 is2 where idx2: "idx2 = i2 # is2" and b2: "0 \<le> i2" "i2 < n"
    and ok2: "index_in_bounds ns is2" by (auto simp: index_in_bounds_Cons)
  from Cons.prems(3) idx1 idx2 have eq: "i1 + n * flat_index ns is1 = i2 + n * flat_index ns is2" by simp
  have d: "i1 - i2 = n * (flat_index ns is2 - flat_index ns is1)" using eq by (simp add: algebra_simps)
  have "flat_index ns is1 = flat_index ns is2"
  proof (rule ccontr)
    assume ne: "flat_index ns is1 \<noteq> flat_index ns is2"
    hence "1 \<le> \<bar>flat_index ns is2 - flat_index ns is1\<bar>" by auto
    hence "n * 1 \<le> n * \<bar>flat_index ns is2 - flat_index ns is1\<bar>"
      using b1 by (intro mult_left_mono) auto
    hence "n \<le> \<bar>n * (flat_index ns is2 - flat_index ns is1)\<bar>"
      using b1 by (simp add: abs_mult)
    with d have "n \<le> \<bar>i1 - i2\<bar>" by simp
    moreover have "\<bar>i1 - i2\<bar> < n" using b1 b2 by auto
    ultimately show False by simp
  qed
  with eq have "i1 = i2" by simp
  moreover from Cons.IH[OF ok1 ok2 \<open>flat_index ns is1 = flat_index ns is2\<close>] have "is1 = is2" .
  ultimately show ?case using idx1 idx2 by simp
qed

(* The byte offset of an element: element size times flat index. *)
definition elem_offset :: "nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> nat" where
  "elem_offset esz sizes idx = esz * nat (flat_index sizes idx)"

lemma elem_offset_bound:
  assumes "index_in_bounds sizes idx"
  shows "elem_offset esz sizes idx + esz \<le> esz * sizes_count sizes"
proof -
  from flat_index_bounds[OF assms] have "nat (flat_index sizes idx) < sizes_count sizes"
    by (simp add: nat_less_iff)
  hence "nat (flat_index sizes idx) + 1 \<le> sizes_count sizes" by simp
  hence "esz * (nat (flat_index sizes idx) + 1) \<le> esz * sizes_count sizes" by (rule mult_le_mono2)
  thus ?thesis by (simp add: elem_offset_def algebra_simps)
qed

(* The byte ranges of two distinct in-bounds elements are disjoint. *)
lemma elem_offset_disjoint:
  assumes "index_in_bounds sizes idx1" and "index_in_bounds sizes idx2" and "idx1 \<noteq> idx2"
  shows "elem_offset esz sizes idx1 + esz \<le> elem_offset esz sizes idx2
         \<or> elem_offset esz sizes idx2 + esz \<le> elem_offset esz sizes idx1"
proof -
  have "flat_index sizes idx1 \<noteq> flat_index sizes idx2"
    using flat_index_inj[OF assms(1,2)] assms(3) by blast
  moreover have "0 \<le> flat_index sizes idx1" "0 \<le> flat_index sizes idx2"
    using flat_index_bounds[OF assms(1)] flat_index_bounds[OF assms(2)] by auto
  ultimately have "nat (flat_index sizes idx1) + 1 \<le> nat (flat_index sizes idx2)
                   \<or> nat (flat_index sizes idx2) + 1 \<le> nat (flat_index sizes idx1)"
    by auto
  moreover have "\<And>a b. a + 1 \<le> b \<Longrightarrow> esz * a + esz \<le> esz * b"
  proof -
    fix a b :: nat assume "a + 1 \<le> b"
    hence "esz * (a + 1) \<le> esz * b" by (rule mult_le_mono2)
    thus "esz * a + esz \<le> esz * b" by (simp add: distrib_left)
  qed
  ultimately show ?thesis unfolding elem_offset_def by blast
qed


section \<open>The descriptor layout\<close>

(* An allocatable or incomplete array of d dimensions is a descriptor: the data
   pointer at offset 0, then the size of dimension k as a uint64_t at
   P + 8k, for a total of P + 8d bytes. *)
definition desc_size :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "desc_size P d = P + 8 * d"

definition desc_dim_offset :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "desc_dim_offset P k = P + 8 * k"

lemma desc_dim_offset_bound: "k < d \<Longrightarrow> desc_dim_offset P k + 8 \<le> desc_size P d"
  by (simp add: desc_dim_offset_def desc_size_def)


section \<open>The size of a type\<close>

(* The fuelled size function. The fuel is spent only on datatype unfoldings;
   when it runs out, the size of a datatype is 0 (DatatypeAcyclic.thy shows
   this never happens at the fuel type_size uses, given acyclic datatypes).
   The payload of a constructor is measured uninstantiated, with the sizes of
   the type arguments assigned to its type variables; by tsz_subst this is the
   size of the substituted payload. *)
fun tsz :: "nat \<Rightarrow> CoreTyEnv \<Rightarrow> nat \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> CoreType \<Rightarrow> nat" where
  "tsz fuel env P sz (CoreTy_Datatype dtName args) =
    (if fuel = 0 then 0
     else tag_size env dtName
          + max_list (map (\<lambda>ctor.
                case fmlookup (TE_DataCtors env) ctor of
                  Some (_, tyvars, payloadTy) \<Rightarrow>
                    tsz (fuel - 1) env P
                        (tyvar_sizes tyvars (map (tsz fuel env P sz) args))
                        payloadTy
                | None \<Rightarrow> 0)
              (dt_ctors env dtName)))"
| "tsz fuel env P sz CoreTy_Bool = 1"
| "tsz fuel env P sz (CoreTy_FiniteInt s b) = byte_width b"
| "tsz fuel env P sz CoreTy_MathInt = 0"
| "tsz fuel env P sz CoreTy_MathReal = 0"
| "tsz fuel env P sz (CoreTy_Record flds) = sum_list (map (\<lambda>fld. tsz fuel env P sz (snd fld)) flds)"
| "tsz fuel env P sz (CoreTy_Array elemTy dims) =
    (if dims_all_fixed dims then tsz fuel env P sz elemTy * dims_count dims
     else desc_size P (length dims))"
| "tsz fuel env P sz (CoreTy_Var v) = sz v"
| "tsz fuel env P sz (CoreTy_Extern _ _) = P"

(* The size of the payload of a constructor, given the sizes of the type
   arguments of its datatype (0 for an unknown constructor). *)
definition ctor_tsz :: "nat \<Rightarrow> CoreTyEnv \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> string \<Rightarrow> nat" where
  "ctor_tsz fuel env P argSizes ctor =
    (case fmlookup (TE_DataCtors env) ctor of
       Some (_, tyvars, payloadTy) \<Rightarrow> tsz fuel env P (tyvar_sizes tyvars argSizes) payloadTy
     | None \<Rightarrow> 0)"

(* The two datatype equations, in terms of ctor_tsz. *)
lemma tsz_0_Datatype [simp]: "tsz 0 env P sz (CoreTy_Datatype dtName args) = 0"
  by simp

lemma tsz_Suc_Datatype:
  "tsz (Suc fuel) env P sz (CoreTy_Datatype dtName args)
   = tag_size env dtName
     + max_list (map (ctor_tsz fuel env P (map (tsz (Suc fuel) env P sz) args)) (dt_ctors env dtName))"
  by (simp add: ctor_tsz_def[abs_def] cong: option.case_cong)

declare tsz.simps(1) [simp del]

lemma tsz_Datatype_cases:
  "tsz fuel env P sz (CoreTy_Datatype dtName args)
   = (case fuel of 0 \<Rightarrow> 0
      | Suc f \<Rightarrow> tag_size env dtName
          + max_list (map (ctor_tsz f env P (map (tsz fuel env P sz) args)) (dt_ctors env dtName)))"
  by (cases fuel) (simp_all add: tsz_Suc_Datatype)

(* The fuel type_size uses: one more than the number of datatypes. *)
definition dt_fuel :: "CoreTyEnv \<Rightarrow> nat" where
  "dt_fuel env = Suc (length (sorted_list_of_fmap (TE_DataCtorsByType env)))"

lemma dt_fuel_pos: "dt_fuel env > 0"
  by (simp add: dt_fuel_def)

(* The size of a type: the pointer size P and the assignment sz of sizes to
   type variables are parameters. *)
definition type_size :: "CoreTyEnv \<Rightarrow> nat \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> CoreType \<Rightarrow> nat" where
  "type_size env P sz ty = tsz (dt_fuel env) env P sz ty"

(* The size of a ground type (the assignment is irrelevant: type_size_ground). *)
abbreviation gsize :: "CoreTyEnv \<Rightarrow> nat \<Rightarrow> CoreType \<Rightarrow> nat" where
  "gsize env P ty \<equiv> type_size env P (\<lambda>_. 0) ty"

(* The unconditional equations of type_size (the datatype case is in
   DatatypeAcyclic.thy, since it needs acyclicity). *)
lemma type_size_simps [simp]:
  "type_size env P sz CoreTy_Bool = 1"
  "type_size env P sz (CoreTy_FiniteInt s b) = byte_width b"
  "type_size env P sz CoreTy_MathInt = 0"
  "type_size env P sz CoreTy_MathReal = 0"
  "type_size env P sz (CoreTy_Record flds) = sum_list (map (\<lambda>fld. type_size env P sz (snd fld)) flds)"
  "type_size env P sz (CoreTy_Array elemTy dims) =
     (if dims_all_fixed dims then type_size env P sz elemTy * dims_count dims
      else desc_size P (length dims))"
  "type_size env P sz (CoreTy_Var v) = sz v"
  "type_size env P sz (CoreTy_Extern n l) = P"
  by (simp_all add: type_size_def)

(* A record field's induction hypothesis, in the form the proofs below need. *)
lemma record_fld_IH:
  assumes "\<And>x b. x \<in> set flds \<Longrightarrow> b \<in> Basic_BNFs.snds x \<Longrightarrow> Q b" and "fld \<in> set flds"
  shows "Q (snd fld)"
  using assms snds.intros by blast

(* The same, for an induction hypothesis with a side condition. *)
lemma record_fld_IH2:
  assumes IH: "\<And>x b. x \<in> set flds \<Longrightarrow> b \<in> Basic_BNFs.snds x \<Longrightarrow> R b \<Longrightarrow> Q b"
    and fld: "fld \<in> set flds" and r: "R (snd fld)"
  shows "Q (snd fld)"
  by (rule IH[OF fld snds.intros r])


subsection \<open>Congruence\<close>

(* The proofs below are by induction on the fuel and then on the type: the
   type arguments of a datatype are measured at the same fuel (inner
   induction), the payloads at one unit less (outer induction). *)

lemma ctor_tsz_cong:
  assumes "\<And>x tyvars payloadTy. fmlookup (TE_DataCtors env) ctor = Some (x, tyvars, payloadTy)
             \<Longrightarrow> tsz fuel env P (tyvar_sizes tyvars as) payloadTy = tsz fuel' env' P' (tyvar_sizes tyvars as') payloadTy"
    and "fmlookup (TE_DataCtors env') ctor = fmlookup (TE_DataCtors env) ctor"
  shows "ctor_tsz fuel env P as ctor = ctor_tsz fuel' env' P' as' ctor"
  using assms unfolding ctor_tsz_def by (auto split: option.splits)

(* The size depends on the assignment only at the type variables of the type. *)
lemma tsz_cong_sz:
  "(\<And>v. v \<in> type_tyvars ty \<Longrightarrow> sz v = sz' v) \<Longrightarrow> tsz fuel env P sz ty = tsz fuel env P sz' ty"
proof (induction ty)
  case (CoreTy_Datatype dtName args)
  define as where "as = map (tsz fuel env P sz) args"
  have e1: "map (tsz fuel env P sz) args = as" by (simp add: as_def)
  have e2: "map (tsz fuel env P sz') args = as"
    unfolding as_def
  proof (intro map_cong refl)
    fix x assume x: "x \<in> set args"
    have "tsz fuel env P sz x = tsz fuel env P sz' x"
      by (rule CoreTy_Datatype.IH[OF x]) (use CoreTy_Datatype.prems x in force)
    thus "tsz fuel env P sz' x = tsz fuel env P sz x" by simp
  qed
  show ?case unfolding tsz_Datatype_cases e1 e2 ..
next
  case (CoreTy_Record flds)
  have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz fuel env P sz (snd fld) = tsz fuel env P sz' (snd fld)"
  proof -
    fix fld assume fld: "fld \<in> set flds"
    show "tsz fuel env P sz (snd fld) = tsz fuel env P sz' (snd fld)"
      by (rule CoreTy_Record.IH[OF fld snds.intros]) (use CoreTy_Record.prems fld in force)
  qed
  then show ?case by (simp cong: sum_list_cong)
qed simp_all

lemma type_size_cong_sz:
  assumes "\<And>v. v \<in> type_tyvars ty \<Longrightarrow> sz v = sz' v"
  shows "type_size env P sz ty = type_size env P sz' ty"
  unfolding type_size_def using assms by (rule tsz_cong_sz)

(* A ground type has the same size under every assignment. *)
lemma type_size_ground:
  assumes "type_tyvars ty = {}"
  shows "type_size env P sz ty = gsize env P ty"
  using assms by (intro type_size_cong_sz) simp

(* The size depends on the environment only through the datatype tables. *)
lemma tsz_cong_env:
  assumes "TE_DataCtors env' = TE_DataCtors env"
    and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "tsz fuel env' P sz ty = tsz fuel env P sz ty"
proof (induction fuel arbitrary: ty sz)
  case 0
  then show ?case
  proof (induction ty)
    case (CoreTy_Record flds)
    have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz 0 env' P sz (snd fld) = tsz 0 env P sz (snd fld)"
      by (rule record_fld_IH[OF CoreTy_Record.IH])
    then show ?case by (simp cong: sum_list_cong)
  qed simp_all
next
  case (Suc fuel)
  show ?case
  proof (induction ty)
    case (CoreTy_Datatype dtName args)
    have ctors: "dt_ctors env' dtName = dt_ctors env dtName"
      by (simp add: dt_ctors_def assms)
    have tag: "tag_size env' dtName = tag_size env dtName"
      by (simp add: tag_size_def tag_bits_def ctors)
    define as where "as = map (tsz (Suc fuel) env P sz) args"
    have e1: "map (tsz (Suc fuel) env P sz) args = as" by (simp add: as_def)
    have e2: "map (tsz (Suc fuel) env' P sz) args = as"
      unfolding as_def using CoreTy_Datatype.IH by (intro map_cong refl)
    have "\<And>ctor. ctor_tsz fuel env' P as ctor = ctor_tsz fuel env P as ctor"
      by (intro ctor_tsz_cong) (simp_all add: Suc.IH assms)
    then show ?case unfolding tsz_Suc_Datatype e1 e2 ctors tag by (simp cong: max_list_cong)
  next
    case (CoreTy_Record flds)
    have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz (Suc fuel) env' P sz (snd fld) = tsz (Suc fuel) env P sz (snd fld)"
      by (rule record_fld_IH[OF CoreTy_Record.IH])
    then show ?case by (simp cong: sum_list_cong)
  qed simp_all
qed

lemma type_size_cong_env:
  assumes "TE_DataCtors env' = TE_DataCtors env"
    and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "type_size env' P sz ty = type_size env P sz ty"
  unfolding type_size_def dt_fuel_def assms(2) by (rule tsz_cong_env[OF assms])


subsection \<open>Substitution\<close>

(* The sizes of the type variables after substitution. *)
definition subst_sizes :: "nat \<Rightarrow> CoreTyEnv \<Rightarrow> nat \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> TypeSubst \<Rightarrow> string \<Rightarrow> nat" where
  "subst_sizes fuel env P sz subst v =
    (case fmlookup subst v of Some t \<Rightarrow> tsz fuel env P sz t | None \<Rightarrow> sz v)"

(* Measuring a substituted type is measuring the type with the sizes of the
   substituted variables (at any fuel). *)
lemma tsz_subst:
  "tsz fuel env P sz (apply_subst subst ty) = tsz fuel env P (subst_sizes fuel env P sz subst) ty"
proof (induction ty)
  case (CoreTy_Datatype dtName args)
  define as where "as = map (tsz fuel env P (subst_sizes fuel env P sz subst)) args"
  have e1: "map (tsz fuel env P (subst_sizes fuel env P sz subst)) args = as" by (simp add: as_def)
  have e2: "map (tsz fuel env P sz) (map (apply_subst subst) args) = as"
    unfolding as_def map_map using CoreTy_Datatype.IH by (intro map_cong refl) simp
  show ?case unfolding apply_subst.simps tsz_Datatype_cases e1 e2 ..
next
  case (CoreTy_Record flds)
  have IH: "\<And>fld. fld \<in> set flds \<Longrightarrow>
          tsz fuel env P sz (apply_subst subst (snd fld)) = tsz fuel env P (subst_sizes fuel env P sz subst) (snd fld)"
    by (rule record_fld_IH[OF CoreTy_Record.IH])
  have eq: "map (\<lambda>fld. tsz fuel env P sz (snd fld)) (map (\<lambda>(name, ty). (name, apply_subst subst ty)) flds)
        = map (\<lambda>fld. tsz fuel env P (subst_sizes fuel env P sz subst) (snd fld)) flds"
    unfolding map_map by (intro map_cong refl) (simp add: case_prod_beta IH)
  show ?case by (simp only: apply_subst.simps tsz.simps eq)
next
  case (CoreTy_Var v)
  then show ?case by (simp add: subst_sizes_def split: option.splits)
qed simp_all

(* The same for type_size, with subst_sizes at type_size's fuel. *)
definition type_subst_sizes :: "CoreTyEnv \<Rightarrow> nat \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> TypeSubst \<Rightarrow> string \<Rightarrow> nat" where
  "type_subst_sizes env P sz subst v =
    (case fmlookup subst v of Some t \<Rightarrow> type_size env P sz t | None \<Rightarrow> sz v)"

lemma type_size_subst:
  "type_size env P sz (apply_subst subst ty) = type_size env P (type_subst_sizes env P sz subst) ty"
proof -
  have "type_subst_sizes env P sz subst = subst_sizes (dt_fuel env) env P sz subst"
    by (rule ext) (simp add: type_subst_sizes_def subst_sizes_def type_size_def split: option.splits)
  thus ?thesis unfolding type_size_def by (simp add: tsz_subst)
qed

(* The instantiation of a datatype's or function's type variables by a list
   of type arguments, as value_has_type and the interpreter build it. *)
lemma type_size_subst_zip:
  assumes "distinct tyvars" and "length tyvars = length tys" and "type_tyvars ty \<subseteq> set tyvars"
  shows "type_size env P sz (apply_subst (fmap_of_list (zip tyvars tys)) ty)
         = type_size env P (tyvar_sizes tyvars (map (type_size env P sz) tys)) ty"
proof -
  have "\<And>v. v \<in> type_tyvars ty \<Longrightarrow>
          type_subst_sizes env P sz (fmap_of_list (zip tyvars tys)) v
          = (if v \<in> set tyvars then tyvar_sizes tyvars (map (type_size env P sz) tys) v else sz v)"
  proof -
    fix v
    show "type_subst_sizes env P sz (fmap_of_list (zip tyvars tys)) v
          = (if v \<in> set tyvars then tyvar_sizes tyvars (map (type_size env P sz) tys) v else sz v)"
    proof (cases "v \<in> set tyvars")
      case True
      then obtain i where i: "i < length tyvars" "tyvars ! i = v" by (meson in_set_conv_nth)
      have lk1: "map_of (zip tyvars tys) v = Some (tys ! i)"
        using map_of_zip_nth[OF assms(2) assms(1), of i] i assms(2) by simp
      have lk2: "map_of (zip tyvars (map (type_size env P sz) tys)) v = Some (type_size env P sz (tys ! i))"
        using map_of_zip_nth[of tyvars "map (type_size env P sz) tys" i] i assms by simp
      show ?thesis using True lk1 lk2
        by (simp add: type_subst_sizes_def tyvar_sizes_def fmlookup_of_list)
    next
      case False
      hence "map_of (zip tyvars tys) v = None" by (simp add: map_of_zip_is_None assms(2))
      with False show ?thesis by (simp add: type_subst_sizes_def fmlookup_of_list)
    qed
  qed
  thus ?thesis
    unfolding type_size_subst using assms(3)
    by (intro type_size_cong_sz) auto
qed


subsection \<open>Monotonicity\<close>

lemma ctor_tsz_mono:
  assumes "\<And>x tyvars payloadTy. fmlookup (TE_DataCtors env) ctor = Some (x, tyvars, payloadTy)
             \<Longrightarrow> tsz fuel env P (tyvar_sizes tyvars as) payloadTy \<le> tsz fuel env P' (tyvar_sizes tyvars as') payloadTy"
  shows "ctor_tsz fuel env P as ctor \<le> ctor_tsz fuel env P' as' ctor"
  using assms unfolding ctor_tsz_def by (auto split: option.splits)

(* Sizes are monotone in the assignment and in the pointer size. *)
lemma tsz_mono:
  assumes "P \<le> P'"
  shows "(\<And>v. sz v \<le> sz' v) \<Longrightarrow> tsz fuel env P sz ty \<le> tsz fuel env P' sz' ty"
proof (induction fuel arbitrary: ty sz sz')
  case 0
  then show ?case
  proof (induction ty)
    case (CoreTy_Record flds)
    have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz 0 env P sz (snd fld) \<le> tsz 0 env P' sz' (snd fld)"
      by (rule CoreTy_Record.IH[OF _ snds.intros]) (use CoreTy_Record.prems in force)+
    then show ?case by (simp add: sum_list_mono_nat)
  next
    case (CoreTy_Array elemTy dims)
    then show ?case using assms by (simp add: desc_size_def mult_le_mono1)
  qed (simp_all add: assms)
next
  case (Suc fuel)
  from Suc.prems show ?case
  proof (induction ty)
    case (CoreTy_Datatype dtName args)
    have args_le: "list_all2 (\<le>) (map (tsz (Suc fuel) env P sz) args) (map (tsz (Suc fuel) env P' sz') args)"
      using CoreTy_Datatype.IH CoreTy_Datatype.prems by (auto simp: list_all2_conv_all_nth)
    have "\<And>ctor. ctor_tsz fuel env P (map (tsz (Suc fuel) env P sz) args) ctor
                 \<le> ctor_tsz fuel env P' (map (tsz (Suc fuel) env P' sz') args) ctor"
      by (intro ctor_tsz_mono Suc.IH tyvar_sizes_mono[OF args_le])
    then show ?case unfolding tsz_Suc_Datatype by (intro add_left_mono max_list_mono)
  next
    case (CoreTy_Record flds)
    have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz (Suc fuel) env P sz (snd fld) \<le> tsz (Suc fuel) env P' sz' (snd fld)"
      by (rule CoreTy_Record.IH[OF _ snds.intros]) (use CoreTy_Record.prems in force)+
    then show ?case by (simp add: sum_list_mono_nat)
  next
    case (CoreTy_Array elemTy dims)
    then show ?case using assms by (simp add: desc_size_def mult_le_mono1)
  qed (simp_all add: assms)
qed

lemma type_size_mono:
  assumes "\<And>v. sz v \<le> sz' v" and "P \<le> P'"
  shows "type_size env P sz ty \<le> type_size env P' sz' ty"
  unfolding type_size_def using assms by (intro tsz_mono)

end

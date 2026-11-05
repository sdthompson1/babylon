theory DatatypeAcyclic
  imports CoreLayout "../graph/Dependency"
begin

(* ========================================================================== *)
(* Acyclicity of the datatypes, and the datatype equation of type_size         *)
(* ========================================================================== *)

(* A datatype depends on every datatype mentioned anywhere in the payload type
   of any of its constructors. datatypes_acyclic is the executable check that
   this dependency graph has no cycle (self-loops included); it reuses the
   generic dependency analysis of graph/Dependency.thy (Kosaraju's algorithm).

   Its soundness lemma, datatypes_acyclic_rank, produces a rank function on
   datatype names that decreases along dependencies and is bounded by the
   number of datatypes. From the rank: the fuel of type_size (dt_fuel) is
   enough (tsz_type_size), the result is independent of any larger fuel, and
   type_size unfolds at a datatype exactly as section 2.3 of minic/DESIGN.md
   says (type_size_Datatype, type_size_Datatype_subst).

   The elaborator already rejects recursive datatypes (check_sccs in
   ElabModule.thy), so the check cannot fail on elaborator output; it is run
   anyway (run_compiler, CodeExport.thy), by the principle of section 3.9 of
   the design: no unchecked hypothesis on the Core input. *)


section \<open>The datatypes mentioned in a type\<close>

fun type_datatype_list :: "CoreType \<Rightarrow> string list" where
  "type_datatype_list (CoreTy_Datatype dtName args) = dtName # concat (map type_datatype_list args)"
| "type_datatype_list (CoreTy_Record flds) = concat (map (\<lambda>fld. type_datatype_list (snd fld)) flds)"
| "type_datatype_list (CoreTy_Array elemTy dims) = type_datatype_list elemTy"
| "type_datatype_list _ = []"

(* Substitution only adds the datatypes of the substituted types. *)
lemma type_datatype_list_subst:
  "set (type_datatype_list (apply_subst subst ty))
   \<subseteq> set (type_datatype_list ty) \<union> (\<Union>t \<in> fmran' subst. set (type_datatype_list t))"
proof (induction ty)
  case (CoreTy_Datatype dtName args)
  show ?case
  proof
    fix d assume "d \<in> set (type_datatype_list (apply_subst subst (CoreTy_Datatype dtName args)))"
    then consider "d = dtName"
      | arg where "arg \<in> set args" "d \<in> set (type_datatype_list (apply_subst subst arg))"
      by auto
    then show "d \<in> set (type_datatype_list (CoreTy_Datatype dtName args))
               \<union> (\<Union>t \<in> fmran' subst. set (type_datatype_list t))"
    proof cases
      case 1 then show ?thesis by simp
    next
      case 2
      with CoreTy_Datatype.IH[OF 2(1)] show ?thesis by auto
    qed
  qed
next
  case (CoreTy_Record flds)
  have IH: "\<And>fld. fld \<in> set flds \<Longrightarrow>
       set (type_datatype_list (apply_subst subst (snd fld)))
       \<subseteq> set (type_datatype_list (snd fld)) \<union> (\<Union>t \<in> fmran' subst. set (type_datatype_list t))"
    by (rule record_fld_IH[OF CoreTy_Record.IH])
  show ?case
  proof
    fix d assume "d \<in> set (type_datatype_list (apply_subst subst (CoreTy_Record flds)))"
    then obtain fld where fld: "fld \<in> set flds"
      and d: "d \<in> set (type_datatype_list (apply_subst subst (snd fld)))"
      by (auto simp: case_prod_beta)
    with IH[OF fld] show "d \<in> set (type_datatype_list (CoreTy_Record flds))
                           \<union> (\<Union>t \<in> fmran' subst. set (type_datatype_list t))"
      by auto
  qed
next
  case (CoreTy_Array elemTy dims)
  then show ?case by simp
next
  case (CoreTy_Var v)
  show ?case
  proof (cases "fmlookup subst v")
    case None then show ?thesis by simp
  next
    case (Some t)
    hence "t \<in> fmran' subst" by (rule fmran'I)
    with Some show ?thesis by auto
  qed
qed simp_all


section \<open>The dependency graph and the check\<close>

(* The datatypes of the environment: the keys of TE_DataCtorsByType. *)
definition dt_known :: "CoreTyEnv \<Rightarrow> string list" where
  "dt_known env = map fst (sorted_list_of_fmap (TE_DataCtorsByType env))"

lemma set_dt_known: "set (dt_known env) = fset (fmdom (TE_DataCtorsByType env))"
  by (auto simp: dt_known_def sorted_list_of_fmap_def comp_def fmlookup_dom_iff)

lemma dt_known_iff: "dtName \<in> set (dt_known env) \<longleftrightarrow> fmlookup (TE_DataCtorsByType env) dtName \<noteq> None"
  by (auto simp: set_dt_known fmlookup_dom_iff)

lemma distinct_dt_known: "distinct (dt_known env)"
  by (simp add: dt_known_def sorted_list_of_fmap_def comp_def distinct_map inj_on_def
                sorted_list_of_fset.rep_eq)

lemma length_dt_known: "length (dt_known env) = length (sorted_list_of_fmap (TE_DataCtorsByType env))"
  by (simp add: dt_known_def)

(* The datatypes mentioned in the payload of a constructor. *)
definition ctor_payload_dts :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> string list" where
  "ctor_payload_dts env ctor =
    (case fmlookup (TE_DataCtors env) ctor of
       Some (_, _, payloadTy) \<Rightarrow> type_datatype_list payloadTy
     | None \<Rightarrow> [])"

(* The datatypes mentioned in the payloads of a datatype's constructors
   (known or not). *)
definition dt_payload_dts :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> string list" where
  "dt_payload_dts env dtName = concat (map (ctor_payload_dts env) (dt_ctors env dtName))"

(* The edges of the dependency graph: the known datatypes among them. *)
definition dt_deps :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> string list" where
  "dt_deps env dtName =
    filter (\<lambda>d. fmlookup (TE_DataCtorsByType env) d \<noteq> None) (remdups (dt_payload_dts env dtName))"

(* The check: None if the datatypes are acyclic, otherwise Some cycle (the
   datatypes of a non-trivial strongly connected component, or a single
   self-dependent datatype). *)
definition datatype_cycle :: "CoreTyEnv \<Rightarrow> string list option" where
  "datatype_cycle env =
    (case analyze_dependencies_generic (dt_known env) id (dt_deps env) of
       Inl _ \<Rightarrow> Some []
     | Inr sccs \<Rightarrow>
         (case find (\<lambda>scc. length scc \<noteq> 1) sccs of
            Some scc \<Rightarrow> Some scc
          | None \<Rightarrow>
              (case find (\<lambda>d. d \<in> set (dt_deps env d)) (dt_known env) of
                 Some d \<Rightarrow> Some [d]
               | None \<Rightarrow> None)))"

definition datatypes_acyclic :: "CoreTyEnv \<Rightarrow> bool" where
  "datatypes_acyclic env = (datatype_cycle env = None)"

(* Both depend only on the datatype tables. *)
lemma dt_deps_cong_env:
  assumes "TE_DataCtors env' = TE_DataCtors env"
    and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "dt_deps env' = dt_deps env"
  by (rule ext) (simp add: dt_deps_def dt_payload_dts_def ctor_payload_dts_def[abs_def] dt_ctors_def assms)

lemma datatypes_acyclic_cong_env:
  assumes "TE_DataCtors env' = TE_DataCtors env"
    and "TE_DataCtorsByType env' = TE_DataCtorsByType env"
  shows "datatypes_acyclic env' = datatypes_acyclic env"
  unfolding datatypes_acyclic_def datatype_cycle_def dt_known_def dt_deps_cong_env[OF assms] assms ..


section \<open>Ranks\<close>

(* A rank function for the datatypes: positive on the known datatypes, zero
   elsewhere, and strictly decreasing from a datatype to every datatype
   mentioned in one of its payloads. *)
definition dt_rank_ok :: "CoreTyEnv \<Rightarrow> (string \<Rightarrow> nat) \<Rightarrow> bool" where
  "dt_rank_ok env r =
    ((\<forall>d. fmlookup (TE_DataCtorsByType env) d = None \<longrightarrow> r d = 0)
     \<and> (\<forall>d. fmlookup (TE_DataCtorsByType env) d \<noteq> None \<longrightarrow>
            0 < r d \<and> (\<forall>d' \<in> set (dt_payload_dts env d). r d' < r d)))"

(* The position of an element in a list. *)
definition list_index :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "list_index xs x = length (takeWhile (\<lambda>y. y \<noteq> x) xs)"

lemma list_index_nth:
  assumes "distinct xs" and "i < length xs"
  shows "list_index xs (xs ! i) = i"
  using assms
proof (induction xs arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by (simp add: list_index_def)
  next
    case (Suc i')
    with Cons.prems have "i' < length xs" and "xs ! i' \<in> set xs" by auto
    with Cons.prems(1) have "xs ! i' \<noteq> x" by auto
    with Suc Cons show ?thesis by (simp add: list_index_def)
  qed
qed

lemma list_index_lt: "x \<in> set xs \<Longrightarrow> list_index xs x < length xs"
  unfolding list_index_def by (rule length_takeWhile_neq_lt)

(* The soundness of the check: an accepted environment has a rank function
   bounded by the number of datatypes. *)
lemma datatypes_acyclic_rank:
  assumes "datatypes_acyclic env"
  shows "\<exists>r. dt_rank_ok env r \<and> (\<forall>d. r d \<le> length (dt_known env))"
proof -
  let ?items = "dt_known env"
  from assms obtain sccs where
    res: "analyze_dependencies_generic ?items id (dt_deps env) = Inr sccs"
    and single: "\<forall>scc \<in> set sccs. length scc = 1"
    and no_self: "\<forall>d \<in> set ?items. d \<notin> set (dt_deps env d)"
    unfolding datatypes_acyclic_def datatype_cycle_def
    by (auto simp del: analyze_dependencies_generic.simps simp: find_None_iff
             split: sum.splits option.splits)
  define order where "order = concat sccs"
  have perm: "mset order = mset ?items"
    using analyze_dependencies_generic_permutation[OF res] unfolding order_def by simp
  have set_order: "set order = set ?items" using perm by (rule mset_eq_setD)
  have len_order: "length order = length ?items" using perm by (rule mset_eq_length)
  have dist_items: "distinct ?items" by (rule distinct_dt_known)
  have dist_order: "distinct order"
    by (rule iffD2[OF mset_eq_imp_distinct_iff[OF perm] dist_items])
  \<comment> \<open>Every component is a singleton, so the concatenation is indexed as the list of components.\<close>
  have order_eq: "order = map hd sccs"
    unfolding order_def using single
  proof (induction sccs)
    case Nil then show ?case by simp
  next
    case (Cons scc sccs)
    then obtain d where "scc = [d]" by (cases scc) auto
    with Cons show ?case by simp
  qed
  have scc_nth: "\<And>i. i < length sccs \<Longrightarrow> sccs ! i = [order ! i]"
  proof -
    fix i assume i: "i < length sccs"
    have "length (sccs ! i) = 1" using single i by simp
    then obtain d where d: "sccs ! i = [d]" by (cases "sccs ! i") auto
    thus "sccs ! i = [order ! i]" using order_eq i by simp
  qed
  have len_sccs: "length sccs = length order" using order_eq by simp
  define r where "r = (\<lambda>d. if d \<in> set order then Suc (list_index order d) else 0)"
  have known_iff: "\<And>d. d \<in> set order \<longleftrightarrow> fmlookup (TE_DataCtorsByType env) d \<noteq> None"
    using set_order dt_known_iff by blast
  have r_bound: "\<And>d. r d \<le> length ?items"
    using list_index_lt len_order unfolding r_def by fastforce
  have dec: "\<And>d d'. fmlookup (TE_DataCtorsByType env) d \<noteq> None \<Longrightarrow> d' \<in> set (dt_payload_dts env d)
                  \<Longrightarrow> r d' < r d"
  proof -
    fix d d'
    assume known_d: "fmlookup (TE_DataCtorsByType env) d \<noteq> None" and d'_in: "d' \<in> set (dt_payload_dts env d)"
    have d_in: "d \<in> set order" using known_iff known_d by blast
    show "r d' < r d"
    proof (cases "fmlookup (TE_DataCtorsByType env) d' = None")
      case True
      hence "r d' = 0" using known_iff unfolding r_def by auto
      with d_in show ?thesis unfolding r_def by simp
    next
      case False
      hence d'_in_order: "d' \<in> set order" using known_iff by blast
      have dep: "d' \<in> set (dt_deps env d)" using d'_in False unfolding dt_deps_def by simp
      have d_items: "d \<in> set ?items" using d_in set_order by simp
      have d'_items: "d' \<in> set ?items" using d'_in_order set_order by simp
      from analyze_dependencies_generic_topological_order[OF res d_items d'_items, of] dep
      obtain i j where ij: "i \<le> j" "i < length sccs" "j < length sccs"
        and d'_i: "d' \<in> set (sccs ! i)" and d_j: "d \<in> set (sccs ! j)"
        by auto
      from d'_i scc_nth[OF ij(2)] have d'_eq: "d' = order ! i" by simp
      from d_j scc_nth[OF ij(3)] have d_eq: "d = order ! j" by simp
      have "i \<noteq> j"
      proof
        assume "i = j"
        with d'_eq d_eq have "d' = d" by simp
        with dep no_self d_items show False by blast
      qed
      with ij have "i < j" by simp
      moreover have "list_index order d' = i"
        using d'_eq list_index_nth[OF dist_order] ij(2) len_sccs by simp
      moreover have "list_index order d = j"
        using d_eq list_index_nth[OF dist_order] ij(3) len_sccs by simp
      ultimately show ?thesis using d_in d'_in_order unfolding r_def by simp
    qed
  qed
  have "dt_rank_ok env r"
    unfolding dt_rank_ok_def
  proof (intro conjI allI impI)
    fix d assume "fmlookup (TE_DataCtorsByType env) d = None"
    thus "r d = 0" using known_iff unfolding r_def by auto
  next
    fix d assume known: "fmlookup (TE_DataCtorsByType env) d \<noteq> None"
    hence "d \<in> set order" using known_iff by blast
    thus "0 < r d" unfolding r_def by simp
  next
    fix d assume known: "fmlookup (TE_DataCtorsByType env) d \<noteq> None"
    show "\<forall>d' \<in> set (dt_payload_dts env d). r d' < r d" using dec[OF known] by blast
  qed
  with r_bound show ?thesis by blast
qed


section \<open>Enough fuel\<close>

(* All datatypes of a type have rank below n. *)
definition dt_bounded :: "(string \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> CoreType \<Rightarrow> bool" where
  "dt_bounded r n ty = (\<forall>d \<in> set (type_datatype_list ty). r d < n)"

lemma dt_bounded_args:
  "dt_bounded r n (CoreTy_Datatype dtName args) \<Longrightarrow> arg \<in> set args \<Longrightarrow> dt_bounded r n arg"
  unfolding dt_bounded_def by auto

lemma dt_bounded_fld:
  "dt_bounded r n (CoreTy_Record flds) \<Longrightarrow> fld \<in> set flds \<Longrightarrow> dt_bounded r n (snd fld)"
  unfolding dt_bounded_def by auto

lemma dt_bounded_elem:
  "dt_bounded r n (CoreTy_Array elemTy dims) \<Longrightarrow> dt_bounded r n elemTy"
  unfolding dt_bounded_def by auto

lemma dt_bounded_mono: "dt_bounded r n ty \<Longrightarrow> n \<le> m \<Longrightarrow> dt_bounded r m ty"
  unfolding dt_bounded_def by auto

(* The payload of a constructor of a datatype of rank below Suc n is bounded
   by n. *)
lemma dt_bounded_payload:
  assumes rank: "dt_rank_ok env r"
    and bnd: "dt_bounded r (Suc n) (CoreTy_Datatype dtName args)"
    and ctor: "ctor \<in> set (dt_ctors env dtName)"
    and lk: "fmlookup (TE_DataCtors env) ctor = Some (x, tyvars, payloadTy)"
  shows "dt_bounded r n payloadTy"
proof -
  have known: "fmlookup (TE_DataCtorsByType env) dtName \<noteq> None"
    using ctor unfolding dt_ctors_def by (cases "fmlookup (TE_DataCtorsByType env) dtName") auto
  have r_lt: "r dtName < Suc n" using bnd unfolding dt_bounded_def by simp
  have "\<And>d'. d' \<in> set (type_datatype_list payloadTy) \<Longrightarrow> d' \<in> set (dt_payload_dts env dtName)"
    using ctor lk unfolding dt_payload_dts_def ctor_payload_dts_def by force
  with rank known have "\<And>d'. d' \<in> set (type_datatype_list payloadTy) \<Longrightarrow> r d' < r dtName"
    unfolding dt_rank_ok_def by blast
  with r_lt show ?thesis unfolding dt_bounded_def by fastforce
qed

(* One more unit of fuel changes nothing once the fuel exceeds every rank. *)
lemma tsz_Suc_stable:
  assumes rank: "dt_rank_ok env r"
  shows "dt_bounded r fuel ty \<Longrightarrow> tsz (Suc fuel) env P sz ty = tsz fuel env P sz ty"
proof (induction fuel arbitrary: ty sz)
  case 0
  then show ?case
  proof (induction ty)
    case (CoreTy_Datatype dtName args)
    then show ?case using CoreTy_Datatype.prems[unfolded dt_bounded_def, THEN bspec, of dtName] by simp
  next
    case (CoreTy_Record flds)
    have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz (Suc 0) env P sz (snd fld) = tsz 0 env P sz (snd fld)"
      by (rule record_fld_IH2[OF CoreTy_Record.IH]) (auto intro: dt_bounded_fld[OF CoreTy_Record.prems])
    then show ?case by (simp cong: sum_list_cong)
  qed (auto simp: dt_bounded_elem)
next
  case (Suc fuel)
  note IH_fuel = Suc.IH
  from Suc.prems show ?case
  proof (induction ty)
    case (CoreTy_Datatype dtName args)
    define as where "as = map (tsz (Suc fuel) env P sz) args"
    have args_eq: "map (tsz (Suc (Suc fuel)) env P sz) args = as"
      unfolding as_def using CoreTy_Datatype.IH CoreTy_Datatype.prems dt_bounded_args by (intro map_cong) auto
    have "\<And>ctor. ctor \<in> set (dt_ctors env dtName) \<Longrightarrow>
            ctor_tsz (Suc fuel) env P as ctor = ctor_tsz fuel env P as ctor"
    proof -
      fix ctor assume c: "ctor \<in> set (dt_ctors env dtName)"
      show "ctor_tsz (Suc fuel) env P as ctor = ctor_tsz fuel env P as ctor"
      proof (rule ctor_tsz_cong)
        fix x tyvars payloadTy
        assume lk: "fmlookup (TE_DataCtors env) ctor = Some (x, tyvars, payloadTy)"
        show "tsz (Suc fuel) env P (tyvar_sizes tyvars as) payloadTy = tsz fuel env P (tyvar_sizes tyvars as) payloadTy"
          by (rule IH_fuel[OF dt_bounded_payload[OF rank CoreTy_Datatype.prems c lk]])
      qed simp
    qed
    then show ?case
      unfolding tsz_Suc_Datatype args_eq as_def[symmetric] by (simp cong: max_list_cong)
  next
    case (CoreTy_Record flds)
    have "\<And>fld. fld \<in> set flds \<Longrightarrow> tsz (Suc (Suc fuel)) env P sz (snd fld) = tsz (Suc fuel) env P sz (snd fld)"
      by (rule record_fld_IH2[OF CoreTy_Record.IH]) (auto intro: dt_bounded_fld[OF CoreTy_Record.prems])
    then show ?case by (simp cong: sum_list_cong)
  qed (auto simp: dt_bounded_elem)
qed

lemma tsz_stable:
  assumes rank: "dt_rank_ok env r" and bnd: "dt_bounded r fuel ty" and le: "fuel \<le> fuel'"
  shows "tsz fuel' env P sz ty = tsz fuel env P sz ty"
  using le
proof (induction fuel' )
  case 0
  then show ?case by simp
next
  case (Suc fuel')
  show ?case
  proof (cases "fuel = Suc fuel'")
    case True then show ?thesis by simp
  next
    case False
    with Suc.prems have "fuel \<le> fuel'" by simp
    with Suc.IH have "tsz fuel' env P sz ty = tsz fuel env P sz ty" by simp
    moreover have "tsz (Suc fuel') env P sz ty = tsz fuel' env P sz ty"
      using tsz_Suc_stable[OF rank dt_bounded_mono[OF bnd \<open>fuel \<le> fuel'\<close>]] .
    ultimately show ?thesis by simp
  qed
qed

(* A rank bounded by the number of datatypes bounds every type by dt_fuel. *)
lemma dt_bounded_dt_fuel:
  assumes "\<forall>d. r d \<le> length (dt_known env)"
  shows "dt_bounded r (dt_fuel env) ty"
  using assms unfolding dt_bounded_def dt_fuel_def length_dt_known by (simp add: less_Suc_eq_le)

(* type_size is the size at every fuel from dt_fuel up. *)
lemma tsz_type_size:
  assumes "datatypes_acyclic env" and "dt_fuel env \<le> fuel"
  shows "tsz fuel env P sz ty = type_size env P sz ty"
proof -
  from datatypes_acyclic_rank[OF assms(1)] obtain r where
    rank: "dt_rank_ok env r" and bnd: "\<forall>d. r d \<le> length (dt_known env)" by blast
  show ?thesis
    unfolding type_size_def
    by (rule tsz_stable[OF rank dt_bounded_dt_fuel[OF bnd] assms(2)])
qed

(* The datatype equation: the tag, plus the maximum over the constructors of
   the size of the payload, measured with the sizes of the type arguments
   assigned to the constructor's type variables. *)
lemma type_size_Datatype_ctor:
  assumes "datatypes_acyclic env"
  shows "type_size env P sz (CoreTy_Datatype dtName args)
         = tag_size env dtName
           + max_list (map (ctor_tsz (dt_fuel env) env P (map (type_size env P sz) args)) (dt_ctors env dtName))"
proof -
  from datatypes_acyclic_rank[OF assms] obtain r where
    rank: "dt_rank_ok env r" and bnd: "\<forall>d. r d \<le> length (dt_known env)" by blast
  obtain n where n: "dt_fuel env = Suc n" using dt_fuel_pos[of env] by (cases "dt_fuel env") auto
  have bnd_ty: "dt_bounded r (Suc n) (CoreTy_Datatype dtName args)"
    using dt_bounded_dt_fuel[OF bnd] n by simp
  have payload_eq: "\<And>ctor x tyvars payloadTy sz'. ctor \<in> set (dt_ctors env dtName)
          \<Longrightarrow> fmlookup (TE_DataCtors env) ctor = Some (x, tyvars, payloadTy)
          \<Longrightarrow> tsz n env P sz' payloadTy = tsz (Suc n) env P sz' payloadTy"
    using tsz_Suc_stable[OF rank dt_bounded_payload[OF rank bnd_ty]] by simp
  have eq: "\<And>ctor. ctor \<in> set (dt_ctors env dtName) \<Longrightarrow>
          ctor_tsz n env P (map (tsz (Suc n) env P sz) args) ctor
          = ctor_tsz (Suc n) env P (map (tsz (Suc n) env P sz) args) ctor"
    by (rule ctor_tsz_cong) (auto intro: payload_eq)
  show ?thesis
    unfolding type_size_def n tsz_Suc_Datatype by (simp cong: max_list_cong add: eq)
qed

(* The same, with the constructor sizes written out. *)
lemma type_size_Datatype:
  assumes "datatypes_acyclic env"
  shows "type_size env P sz (CoreTy_Datatype dtName args)
         = tag_size env dtName
           + max_list (map (\<lambda>ctor.
                case fmlookup (TE_DataCtors env) ctor of
                  Some (_, tyvars, payloadTy) \<Rightarrow>
                    type_size env P (tyvar_sizes tyvars (map (type_size env P sz) args)) payloadTy
                | None \<Rightarrow> 0)
              (dt_ctors env dtName))"
  unfolding type_size_Datatype_ctor[OF assms]
  unfolding ctor_tsz_def[abs_def] type_size_def ..

(* The same, with the payload instantiated by substitution, as value_has_type
   and the interpreter do. *)
lemma type_size_Datatype_subst:
  assumes "datatypes_acyclic env"
    and "\<And>ctor dt tyvars payloadTy. ctor \<in> set (dt_ctors env dtName)
           \<Longrightarrow> fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)
           \<Longrightarrow> distinct tyvars \<and> length tyvars = length args \<and> type_tyvars payloadTy \<subseteq> set tyvars"
  shows "type_size env P sz (CoreTy_Datatype dtName args)
         = tag_size env dtName
           + max_list (map (\<lambda>ctor.
                case fmlookup (TE_DataCtors env) ctor of
                  Some (_, tyvars, payloadTy) \<Rightarrow>
                    type_size env P sz (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)
                | None \<Rightarrow> 0)
              (dt_ctors env dtName))"
  unfolding type_size_Datatype[OF assms(1)]
  using assms(2) by (intro arg_cong2[where f = "(+)"] refl max_list_cong)
                     (auto split: option.splits simp: type_size_subst_zip)

(* The payload of a constructor is no larger than the datatype minus its tag. *)
lemma type_size_payload_le:
  assumes "datatypes_acyclic env"
    and "ctor \<in> set (dt_ctors env dtName)"
    and "fmlookup (TE_DataCtors env) ctor = Some (dt, tyvars, payloadTy)"
  shows "tag_size env dtName
         + type_size env P (tyvar_sizes tyvars (map (type_size env P sz) args)) payloadTy
         \<le> type_size env P sz (CoreTy_Datatype dtName args)"
proof -
  let ?f = "ctor_tsz (dt_fuel env) env P (map (type_size env P sz) args)"
  have "?f ctor \<le> max_list (map ?f (dt_ctors env dtName))" by (rule max_list_ge_map[OF assms(2)])
  moreover have "?f ctor = type_size env P (tyvar_sizes tyvars (map (type_size env P sz) args)) payloadTy"
    using assms(3) by (simp add: ctor_tsz_def type_size_def)
  ultimately show ?thesis unfolding type_size_Datatype_ctor[OF assms(1)] by simp
qed

lemma type_size_Datatype_ge_tag:
  assumes "datatypes_acyclic env"
  shows "tag_size env dtName \<le> type_size env P sz (CoreTy_Datatype dtName args)"
  unfolding type_size_Datatype[OF assms] by simp

end

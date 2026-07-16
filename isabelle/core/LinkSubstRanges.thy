theory LinkSubstRanges
  imports SubstAbsorption LinkModules
begin

(* ========================================================================== *)
(* Transfer of typesubst_well_kinded through linking.                         *)
(*                                                                            *)
(* Setting: two sub-links A and B (link_modules as = Inr a, link_modules bs   *)
(* = Inr b) and the whole-program link (link_modules ms = Inr m, with set ms  *)
(* = set as \<union> set bs). Their merged substitutions \<sigma>A, \<sigma>B, \<sigma>M are the           *)
(* idempotent closures of the raw unions uA, uB, uM of the input modules'     *)
(* CM_TypeSubsts. Each side vouches for the well-kindedness of its own        *)
(* abstract-type resolutions (the typesubst_well_kinded conjunct of           *)
(* core_module_well_typed); this file transfers that to the merged closure:   *)
(*                                                                            *)
(*   typesubst_well_kinded (CM_TyEnv a) \<sigma>A                                    *)
(*   \<and> typesubst_well_kinded (CM_TyEnv b) \<sigma>B                                  *)
(*   \<Longrightarrow> typesubst_well_kinded (CM_TyEnv m) \<sigma>M                                 *)
(*                                                                            *)
(* The difficulty is that \<sigma>M's ranges interleave A- and B-material (a chain   *)
(* T \<mapsto> U resolved by A with U \<mapsto> \<tau> resolved by B), terminating only by        *)
(* acyclicity of the union's dependency relation. The proof is a well-founded *)
(* induction over subst_dep_rel (\<sigma>A ++f \<sigma>B), enabled by:                      *)
(*                                                                            *)
(* - closure absorption over the raw union (SubstAbsorption.thy), unlocked    *)
(*   by "a sub-link's union is a submap of the whole link's union";           *)
(* - is_subst_closure (\<sigma>A ++f \<sigma>B) \<sigma>M: the whole link's substitution is the   *)
(*   closure of the two sub-links' substitutions (linking is "associative"    *)
(*   at the substitution level);                                              *)
(* - every dependency edge of \<sigma>A ++f \<sigma>B maps to a nonempty path of the raw    *)
(*   union's relation (sigma_tyvars_reach, recovered from the binary-era      *)
(*   MergeSubstsHelpers.thy), so acyclicity transfers;                        *)
(* - a monotone variant of is_well_kinded_transfer (more type variables, a    *)
(*   datatype table that preserves the source's lookups - the existing        *)
(*   transfer demands table equality, which linking breaks).                  *)
(* ========================================================================== *)


(* ========================================================================== *)
(* Submap toolkit                                                             *)
(*                                                                            *)
(* "t is a submap of s" is carried as the lookup-preservation hypothesis      *)
(* (\<And>k v. fmlookup t k = Some v \<Longrightarrow> fmlookup s k = Some v) throughout.          *)
(* ========================================================================== *)

(* Adding a submap on the right changes nothing. *)
lemma fmadd_absorb_submap:
  assumes sub: "\<And>k v. fmlookup t k = Some v \<Longrightarrow> fmlookup s k = Some v"
  shows "s ++\<^sub>f t = s"
proof (rule fmap_ext)
  fix k
  show "fmlookup (s ++\<^sub>f t) k = fmlookup s k"
  proof (cases "k |\<in>| fmdom t")
    case True
    then obtain v where v: "fmlookup t k = Some v"
      by (auto simp: fmlookup_dom_iff)
    show ?thesis using True v sub[OF v] by simp
  next
    case False
    then show ?thesis by simp
  qed
qed

(* A map decomposes as a submap plus the rest, with disjoint domains. This is
   the shape sigma_tyvars_reach consumes (u ++f w with dom u and dom w
   disjoint). *)
lemma fmadd_drop_submap:
  assumes sub: "\<And>k v. fmlookup t k = Some v \<Longrightarrow> fmlookup s k = Some v"
  shows "t ++\<^sub>f fmdrop_fset (fmdom t) s = s"
proof (rule fmap_ext)
  fix k
  show "fmlookup (t ++\<^sub>f fmdrop_fset (fmdom t) s) k = fmlookup s k"
  proof (cases "k |\<in>| fmdom t")
    case True
    then obtain v where v: "fmlookup t k = Some v"
      by (auto simp: fmlookup_dom_iff)
    show ?thesis using True v sub[OF v] by simp
  next
    case False
    then show ?thesis by (simp add: fmdom_notD)
  qed
qed

(* The disjoint union over a sub-list is a submap of the union over the full
   list. (Both lists must be pairwise disjoint; link success supplies that
   for every projected family.) *)
lemma fmlist_union_sublist_lookup:
  assumes disj_full: "fmdisjoint_list ss"
      and disj_sub: "fmdisjoint_list ts"
      and sub: "set ts \<subseteq> set ss"
      and lk: "fmlookup (fmlist_union ts) k = Some v"
  shows "fmlookup (fmlist_union ss) k = Some v"
proof -
  obtain t where t_in: "t \<in> set ts" and t_lk: "fmlookup t k = Some v"
    using fmlist_union_lookup[OF disj_sub] lk by blast
  have "t \<in> set ss" using t_in sub by auto
  then show ?thesis using t_lk fmlist_union_lookup[OF disj_full] by blast
qed


(* ========================================================================== *)
(* Absorption of a sub-link's closure by the whole link's closure             *)
(* (R3 step 1)                                                                *)
(* ========================================================================== *)

(* Let \<sigma>A be the closure of a sub-link's union uA and \<sigma>M the closure of the
   whole link's union uM, with uA a submap of uM. Then applying \<sigma>A first is a
   no-op under \<sigma>M. The submap hypothesis turns the whole link's union into a
   "p ++f uA" over-union, which is exactly closure_absorb_type_raw's shape. *)
lemma sublink_closure_absorb:
  assumes acycA: "acyclic_subst_deps uA"
      and closA: "is_subst_closure uA \<sigma>A"
      and closM: "is_subst_closure uM \<sigma>M"
      and subA: "\<And>k v. fmlookup uA k = Some v \<Longrightarrow> fmlookup uM k = Some v"
  shows "apply_subst \<sigma>M (apply_subst \<sigma>A ty) = apply_subst \<sigma>M ty"
proof -
  have "uM ++\<^sub>f uA = uM" using fmadd_absorb_submap[OF subA] .
  then have cl: "is_subst_closure (uM ++\<^sub>f uA) \<sigma>M" using closM by simp
  show ?thesis using closure_absorb_type_raw[OF acycA closA cl] .
qed

(* Link-level corollary, in the form the whole-program theorem's assembly
   (work round R4) consumes: the whole link's substitution absorbs a
   sub-link's. *)
theorem link_modules_closure_absorb:
  assumes linkA: "link_modules as = Inr a"
      and linkM: "link_modules ms = Inr m"
      and sub: "set as \<subseteq> set ms"
  shows "apply_subst (CM_TypeSubst m) (apply_subst (CM_TypeSubst a) ty)
           = apply_subst (CM_TypeSubst m) ty"
proof -
  obtain \<sigma>A where sdisjA: "fmdisjoint_list (map CM_TypeSubst as)"
      and acycA: "acyclic_subst_deps (fmlist_union (map CM_TypeSubst as))"
      and closA: "is_subst_closure (fmlist_union (map CM_TypeSubst as)) \<sigma>A"
      and aeq: "a = link_result as \<sigma>A"
    using linkA link_modules_Inr_iff_closure by blast
  obtain \<sigma>M where sdisjM: "fmdisjoint_list (map CM_TypeSubst ms)"
      and closM: "is_subst_closure (fmlist_union (map CM_TypeSubst ms)) \<sigma>M"
      and meq: "m = link_result ms \<sigma>M"
    using linkM link_modules_Inr_iff_closure by blast
  have \<sigma>A_eq: "CM_TypeSubst a = \<sigma>A" and \<sigma>M_eq: "CM_TypeSubst m = \<sigma>M"
    using aeq meq by (simp_all add: link_result_def)
  have mapsub: "set (map CM_TypeSubst as) \<subseteq> set (map CM_TypeSubst ms)"
    using sub by auto
  have subm: "\<And>k v. fmlookup (fmlist_union (map CM_TypeSubst as)) k = Some v
                \<Longrightarrow> fmlookup (fmlist_union (map CM_TypeSubst ms)) k = Some v"
    using fmlist_union_sublist_lookup[OF sdisjM sdisjA mapsub] by blast
  show ?thesis
    unfolding \<sigma>A_eq \<sigma>M_eq
    using sublink_closure_absorb[OF acycA closA closM subm] .
qed


(* ========================================================================== *)
(* The whole link's closure is the closure of the sub-links' closures         *)
(* (R3 step 2)                                                                *)
(* ========================================================================== *)

(* is_subst_closure (\<sigma>A ++f \<sigma>B) \<sigma>M. On a key both sides resolve (a shared
   interface module's abstract type), the two expansions \<sigma>A(T) and \<sigma>B(T) may
   differ - but absorption makes either satisfy the closure equation, and the
   right-biased ++f picks \<sigma>B's. *)
lemma is_subst_closure_merged_pair:
  assumes acycA: "acyclic_subst_deps uA"
      and closA: "is_subst_closure uA \<sigma>A"
      and acycB: "acyclic_subst_deps uB"
      and closB: "is_subst_closure uB \<sigma>B"
      and closM: "is_subst_closure uM \<sigma>M"
      and subA: "\<And>k v. fmlookup uA k = Some v \<Longrightarrow> fmlookup uM k = Some v"
      and subB: "\<And>k v. fmlookup uB k = Some v \<Longrightarrow> fmlookup uM k = Some v"
      and domM: "fmdom uM = fmdom uA |\<union>| fmdom uB"
  shows "is_subst_closure (\<sigma>A ++\<^sub>f \<sigma>B) \<sigma>M"
proof -
  have domA: "fmdom \<sigma>A = fmdom uA" and domB: "fmdom \<sigma>B = fmdom uB"
    and domMM: "fmdom \<sigma>M = fmdom uM"
    using closA closB closM unfolding is_subst_closure_def by auto
  have absorbA: "apply_subst \<sigma>M (apply_subst \<sigma>A ty) = apply_subst \<sigma>M ty" for ty
    using sublink_closure_absorb[OF acycA closA closM subA] .
  have absorbB: "apply_subst \<sigma>M (apply_subst \<sigma>B ty) = apply_subst \<sigma>M ty" for ty
    using sublink_closure_absorb[OF acycB closB closM subB] .
  show ?thesis
    unfolding is_subst_closure_def
  proof (intro conjI allI impI)
    show "idempotent_subst \<sigma>M"
      using closM unfolding is_subst_closure_def by blast
  next
    show "fmdom \<sigma>M = fmdom (\<sigma>A ++\<^sub>f \<sigma>B)"
      using domMM domM domA domB by simp
  next
    fix T ty assume lk: "fmlookup (\<sigma>A ++\<^sub>f \<sigma>B) T = Some ty"
    show "fmlookup \<sigma>M T = Some (apply_subst \<sigma>M ty)"
    proof (cases "T |\<in>| fmdom \<sigma>B")
      case True
      then have lkB: "fmlookup \<sigma>B T = Some ty" using lk by simp
      from True domB obtain uty where uty: "fmlookup uB T = Some uty"
        by (auto simp: fmlookup_dom_iff)
      have ty_eq: "ty = apply_subst \<sigma>B uty"
        using closB uty lkB unfolding is_subst_closure_def by auto
      have "fmlookup \<sigma>M T = Some (apply_subst \<sigma>M uty)"
        using closM subB[OF uty] unfolding is_subst_closure_def by blast
      then show ?thesis using ty_eq absorbB by simp
    next
      case False
      then have lkA: "fmlookup \<sigma>A T = Some ty" using lk by simp
      then have "T |\<in>| fmdom \<sigma>A" by (rule fmdomI)
      with domA obtain uty where uty: "fmlookup uA T = Some uty"
        by (auto simp: fmlookup_dom_iff)
      have ty_eq: "ty = apply_subst \<sigma>A uty"
        using closA uty lkA unfolding is_subst_closure_def by auto
      have "fmlookup \<sigma>M T = Some (apply_subst \<sigma>M uty)"
        using closM subA[OF uty] unfolding is_subst_closure_def by blast
      then show ?thesis using ty_eq absorbA by simp
    qed
  qed
qed


(* ========================================================================== *)
(* Dependency edges of the merged pair map to raw-union paths                 *)
(* (R3 steps 3-4)                                                             *)
(* ========================================================================== *)

(* Path lemma: every type variable c of \<sigma>(b) (for a domain variable b of u) is
   reachable from b by a nonempty (u ++f w)-path - provided c is itself a vertex of
   u ++f w. Proved by wf-induction on subst_dep_rel u: a c surviving directly from
   u(b) gives a single edge; a c arising by substituting some a in u(b) gives an
   edge (a, b) followed by the (inductively shorter) path from a. *)
lemma sigma_tyvars_reach:
  assumes acyc_u: "acyclic_subst_deps u"
      and disj: "fmdom u |\<inter>| fmdom w = {||}"
      and cl_u: "is_subst_closure u \<sigma>"
      and b_dom: "b |\<in>| fmdom u"
      and c_in: "c \<in> type_tyvars (apply_subst \<sigma> (CoreTy_Var b))"
      and c_vtx: "c |\<in>| fmdom (u ++\<^sub>f w)"
  shows "(c, b) \<in> (subst_dep_rel (u ++\<^sub>f w))\<^sup>+"
proof -
  have wf: "wf (subst_dep_rel u)" using acyc_u by (rule acyclic_subst_deps_wf)
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  show ?thesis
    using b_dom c_in proof (induction b rule: wf_induct_rule[OF wf])
    case (1 b)
    then have b_du: "b |\<in>| fmdom u" by simp
    then obtain tb where tb: "fmlookup u b = Some tb"
      by (auto simp: fmlookup_dom_iff)
    \<comment> \<open>b is a domain variable of u, hence outside w (disjointness); so u wins in u ++f w. \<close>
    have b_ndw: "b |\<notin>| fmdom w" using disj b_du by auto
    have b_uw: "fmlookup (u ++\<^sub>f w) b = Some tb" using tb b_ndw by simp
    have b_uw_dom: "b |\<in>| fmdom (u ++\<^sub>f w)" using b_du by simp
    \<comment> \<open>\<sigma>(b) = apply_subst \<sigma> tb, so c is a tyvar of that. \<close>
    have \<sigma>_b: "fmlookup \<sigma> b = Some (apply_subst \<sigma> tb)"
      using cl_u tb unfolding is_subst_closure_def by blast
    from "1.prems"(2) \<sigma>_b have c_in_tb: "c \<in> type_tyvars (apply_subst \<sigma> tb)" by simp
    \<comment> \<open>Decompose: c either survives directly from tb, or comes from substituting some
        domain variable a occurring in tb. \<close>
    from type_tyvars_apply_subst_decompose[OF c_in_tb]
    show ?case
    proof (elim disjE conjE bexE)
      \<comment> \<open>Case 1: c is a tyvar of tb outside dom \<sigma>; (c, b) is a single (u ++f w)-edge. \<close>
      assume c_tb: "c \<in> type_tyvars tb" and "c |\<notin>| fmdom \<sigma>"
      have "c \<in> type_tyvars (the (fmlookup (u ++\<^sub>f w) b))" using c_tb b_uw by simp
      then have "(c, b) \<in> subst_dep_rel (u ++\<^sub>f w)"
        unfolding subst_dep_rel_def using c_vtx b_uw_dom by auto
      then show ?thesis by (rule r_into_trancl)
    next
      \<comment> \<open>Case 2: c arises by substituting a domain variable a occurring in tb. Then
          (a, b) is an edge, and the path from a to b composes with the IH path c \<rightarrow> a. \<close>
      fix a assume a_tb: "a \<in> type_tyvars tb"
        and a_d\<sigma>: "a |\<in>| fmdom \<sigma>"
        and c_in_\<sigma>a: "c \<in> type_tyvars (apply_subst \<sigma> (CoreTy_Var a))"
      have a_du: "a |\<in>| fmdom u" using a_d\<sigma> dom_\<sigma> by simp
      \<comment> \<open>(a, b) is a u-edge, hence a (u ++f w)-edge, and a is a strict predecessor of b. \<close>
      have edge_u: "(a, b) \<in> subst_dep_rel u"
        unfolding subst_dep_rel_def using a_du b_du a_tb tb by auto
      have a_uw: "a |\<in>| fmdom (u ++\<^sub>f w)" using a_du by simp
      have edge_uw: "(a, b) \<in> subst_dep_rel (u ++\<^sub>f w)"
        unfolding subst_dep_rel_def using a_uw b_uw_dom a_tb b_uw by auto
      \<comment> \<open>IH at a: c reaches a by a (u ++f w)-path. \<close>
      have "(c, a) \<in> (subst_dep_rel (u ++\<^sub>f w))\<^sup>+"
        using "1.IH"[OF edge_u a_du c_in_\<sigma>a] .
      with edge_uw show ?thesis by (rule trancl_into_trancl[rotated])
    qed
  qed
qed

(* Acyclicity transfer: an edge of subst_dep_rel (\<sigma>A ++f \<sigma>B) is a nonempty
   path of subst_dep_rel uM (each closure entry \<sigma>A(b) / \<sigma>B(b) expands, by
   sigma_tyvars_reach, into raw-union steps), so a cycle in the merged pair
   would yield a cycle in the raw union - which acyclic_subst_deps uM rules
   out. *)
lemma subst_dep_rel_merged_pair_acyclic:
  assumes acycA: "acyclic_subst_deps uA"
      and closA: "is_subst_closure uA \<sigma>A"
      and acycB: "acyclic_subst_deps uB"
      and closB: "is_subst_closure uB \<sigma>B"
      and subA: "\<And>k v. fmlookup uA k = Some v \<Longrightarrow> fmlookup uM k = Some v"
      and subB: "\<And>k v. fmlookup uB k = Some v \<Longrightarrow> fmlookup uM k = Some v"
      and domM: "fmdom uM = fmdom uA |\<union>| fmdom uB"
      and acycM: "acyclic_subst_deps uM"
  shows "acyclic (subst_dep_rel (\<sigma>A ++\<^sub>f \<sigma>B))"
proof -
  have domA: "fmdom \<sigma>A = fmdom uA" and domB: "fmdom \<sigma>B = fmdom uB"
    using closA closB unfolding is_subst_closure_def by auto
  \<comment> \<open>Decompose the whole union around each sub-union, for sigma_tyvars_reach.\<close>
  define wA where "wA = fmdrop_fset (fmdom uA) uM"
  define wB where "wB = fmdrop_fset (fmdom uB) uM"
  have uMA: "uA ++\<^sub>f wA = uM"
    unfolding wA_def by (rule fmadd_drop_submap[OF subA])
  have uMB: "uB ++\<^sub>f wB = uM"
    unfolding wB_def by (rule fmadd_drop_submap[OF subB])
  have disjWA: "fmdom uA |\<inter>| fmdom wA = {||}"
    unfolding wA_def by (rule fset_eqI) auto
  have disjWB: "fmdom uB |\<inter>| fmdom wB = {||}"
    unfolding wB_def by (rule fset_eqI) auto
  \<comment> \<open>Every merged-pair edge is a nonempty raw-union path.\<close>
  have sub: "subst_dep_rel (\<sigma>A ++\<^sub>f \<sigma>B) \<subseteq> (subst_dep_rel uM)\<^sup>+"
  proof
    fix p assume "p \<in> subst_dep_rel (\<sigma>A ++\<^sub>f \<sigma>B)"
    then obtain c b where p_eq: "p = (c, b)"
      and c_in: "c |\<in>| fmdom (\<sigma>A ++\<^sub>f \<sigma>B)"
      and b_in: "b |\<in>| fmdom (\<sigma>A ++\<^sub>f \<sigma>B)"
      and c_val: "c \<in> type_tyvars (the (fmlookup (\<sigma>A ++\<^sub>f \<sigma>B) b))"
      unfolding subst_dep_rel_def by auto
    have c_uM: "c |\<in>| fmdom uM" using c_in domA domB domM by auto
    have "(c, b) \<in> (subst_dep_rel uM)\<^sup>+"
    proof (cases "b |\<in>| fmdom \<sigma>B")
      case True
      then have b_uB: "b |\<in>| fmdom uB" using domB by simp
      obtain bty where bty: "fmlookup \<sigma>B b = Some bty"
        using True by (auto simp: fmlookup_dom_iff)
      have c_bty: "c \<in> type_tyvars bty"
        using c_val True bty by simp
      have c_in_\<sigma>b: "c \<in> type_tyvars (apply_subst \<sigma>B (CoreTy_Var b))"
        using bty c_bty by simp
      have c_vtxB: "c |\<in>| fmdom (uB ++\<^sub>f wB)"
        using uMB c_uM by simp
      have "(c, b) \<in> (subst_dep_rel (uB ++\<^sub>f wB))\<^sup>+"
        using sigma_tyvars_reach[OF acycB disjWB closB b_uB c_in_\<sigma>b c_vtxB] .
      then show ?thesis using uMB by simp
    next
      case False
      then have b_\<sigma>A: "b |\<in>| fmdom \<sigma>A" using b_in by auto
      then have b_uA: "b |\<in>| fmdom uA" using domA by simp
      obtain bty where bty: "fmlookup \<sigma>A b = Some bty"
        using b_\<sigma>A by (auto simp: fmlookup_dom_iff)
      have c_bty: "c \<in> type_tyvars bty"
        using c_val False bty by simp
      have c_in_\<sigma>a: "c \<in> type_tyvars (apply_subst \<sigma>A (CoreTy_Var b))"
        using bty c_bty by simp
      have c_vtxA: "c |\<in>| fmdom (uA ++\<^sub>f wA)"
        using uMA c_uM by simp
      have "(c, b) \<in> (subst_dep_rel (uA ++\<^sub>f wA))\<^sup>+"
        using sigma_tyvars_reach[OF acycA disjWA closA b_uA c_in_\<sigma>a c_vtxA] .
      then show ?thesis using uMA by simp
    qed
    then show "p \<in> (subst_dep_rel uM)\<^sup>+" using p_eq by simp
  qed
  have "acyclic ((subst_dep_rel uM)\<^sup>+)"
    using acycM unfolding acyclic_subst_deps_def
    by (simp add: acycM acyclic_subst_deps_wf wf_acyclic wf_trancl)
  then show ?thesis using sub acyclic_subset by blast
qed


(* ========================================================================== *)
(* Monotone transfer of is_well_kinded (R3 step 5)                            *)
(* ========================================================================== *)

(* If ty is well-kinded in one env, every type variable of ty is in scope in a
   second env, and the second env's datatype table PRESERVES the first's
   lookups (it may be strictly larger - the linked table is the disjoint union
   of the inputs'), then ty is well-kinded in the second env. The existing
   is_well_kinded_transfer (CoreKindcheck.thy) demands datatype-table EQUALITY,
   which linking breaks. *)
lemma is_well_kinded_transfer_mono:
  assumes wk: "is_well_kinded env1 ty"
    and tvs: "type_tyvars ty \<subseteq> fset (TE_TypeVars env2)"
    and dt: "\<And>n v. fmlookup (TE_Datatypes env1) n = Some v
               \<Longrightarrow> fmlookup (TE_Datatypes env2) n = Some v"
  shows "is_well_kinded env2 ty"
  using wk tvs
proof (induction ty)
  case (CoreTy_Datatype name argTypes)
  from CoreTy_Datatype.prems(1) obtain numTyVars where
    dt_lookup: "fmlookup (TE_Datatypes env1) name = Some numTyVars" and
    len_eq: "length argTypes = numTyVars" and
    args_wk: "list_all (is_well_kinded env1) argTypes"
    by (auto split: option.splits)
  have args_tyvars: "\<And>arg. arg \<in> set argTypes \<Longrightarrow> type_tyvars arg \<subseteq> fset (TE_TypeVars env2)"
    using CoreTy_Datatype.prems(2) by auto
  have args_wk': "list_all (is_well_kinded env2) argTypes"
    unfolding list_all_iff
  proof
    fix arg assume arg_in: "arg \<in> set argTypes"
    have "is_well_kinded env1 arg" using args_wk arg_in by (simp add: list_all_iff)
    then show "is_well_kinded env2 arg"
      using CoreTy_Datatype.IH[OF arg_in] args_tyvars[OF arg_in] by blast
  qed
  show ?case using dt[OF dt_lookup] len_eq args_wk' by simp
next
  case (CoreTy_Record flds)
  have flds_wk: "\<And>nm ty'. (nm, ty') \<in> set flds \<Longrightarrow> is_well_kinded env2 ty'"
  proof -
    fix nm ty' assume mem: "(nm, ty') \<in> set flds"
    have wk1: "is_well_kinded env1 ty'"
      using CoreTy_Record.prems(1) mem by (auto simp: list_all_iff)
    have tvs': "type_tyvars ty' \<subseteq> fset (TE_TypeVars env2)"
      using CoreTy_Record.prems(2) mem by force
    show "is_well_kinded env2 ty'"
      using CoreTy_Record.IH mem wk1 tvs' by auto
  qed
  show ?case using CoreTy_Record.prems(1) flds_wk by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  then show ?case by auto
next
  case (CoreTy_Var n)
  then show ?case by auto
qed simp_all


(* ========================================================================== *)
(* The transfer theorem (R3 step 6)                                           *)
(* ========================================================================== *)

(* If two sub-links A and B are each well-typed enough to vouch for their own
   abstract-type resolutions (the typesubst_well_kinded conjunct of
   core_module_well_typed), and the whole-program link of their combined
   module lists succeeds, then the whole link's merged substitution has
   well-kinded ranges in the linked environment.

   Proof: \<sigma>M is the closure of \<sigma>A ++f \<sigma>B (is_subst_closure_merged_pair), whose
   dependency relation is well-founded (subst_dep_rel_merged_pair_acyclic). By
   wf-induction over it: \<sigma>M's entry at n is apply_subst \<sigma>M e where e is \<sigma>A's or
   \<sigma>B's entry at n - well-kinded in that side's env by hypothesis. Lift e into
   (CM_TyEnv m with type variables cut down to e's own tyvars) by the monotone
   transfer, then apply_subst_preserves_well_kinded: a tyvar of e that \<sigma>M
   resolves is a dependency edge (IH); one it leaves alone survives into
   TE_TypeVars (CM_TyEnv m) by set algebra. *)
theorem link_modules_typesubst_well_kinded:
  assumes linkA: "link_modules as = Inr a"
      and linkB: "link_modules bs = Inr b"
      and linkM: "link_modules ms = Inr m"
      and setMS: "set ms = set as \<union> set bs"
      and wkA: "typesubst_well_kinded (CM_TyEnv a) (CM_TypeSubst a)"
      and wkB: "typesubst_well_kinded (CM_TyEnv b) (CM_TypeSubst b)"
  shows "typesubst_well_kinded (CM_TyEnv m) (CM_TypeSubst m)"
proof -
  define uA where "uA = fmlist_union (map CM_TypeSubst as)"
  define uB where "uB = fmlist_union (map CM_TypeSubst bs)"
  define uM where "uM = fmlist_union (map CM_TypeSubst ms)"

  \<comment> \<open>Unpack the three links' success characterizations.\<close>
  obtain \<sigma>A where fdisjA: "link_fields_disjoint as"
      and sdisjA: "fmdisjoint_list (map CM_TypeSubst as)"
      and acycA: "acyclic_subst_deps uA"
      and closA: "is_subst_closure uA \<sigma>A"
      and aeq: "a = link_result as \<sigma>A"
    using linkA link_modules_Inr_iff_closure unfolding uA_def by blast
  obtain \<sigma>B where fdisjB: "link_fields_disjoint bs"
      and sdisjB: "fmdisjoint_list (map CM_TypeSubst bs)"
      and acycB: "acyclic_subst_deps uB"
      and closB: "is_subst_closure uB \<sigma>B"
      and beq: "b = link_result bs \<sigma>B"
    using linkB link_modules_Inr_iff_closure unfolding uB_def by blast
  obtain \<sigma>M where fdisjM: "link_fields_disjoint ms"
      and sdisjM: "fmdisjoint_list (map CM_TypeSubst ms)"
      and acycM: "acyclic_subst_deps uM"
      and closM: "is_subst_closure uM \<sigma>M"
      and meq: "m = link_result ms \<sigma>M"
    using linkM link_modules_Inr_iff_closure unfolding uM_def by blast

  have \<sigma>A_eq: "CM_TypeSubst a = \<sigma>A"
    and \<sigma>B_eq: "CM_TypeSubst b = \<sigma>B"
    and \<sigma>M_eq: "CM_TypeSubst m = \<sigma>M"
    using aeq beq meq by (simp_all add: link_result_def)

  have wkA': "\<forall>k ty. fmlookup \<sigma>A k = Some ty \<longrightarrow> is_well_kinded (CM_TyEnv a) ty"
    using wkA \<sigma>A_eq by (simp add: typesubst_well_kinded_def)
  have wkB': "\<forall>k ty. fmlookup \<sigma>B k = Some ty \<longrightarrow> is_well_kinded (CM_TyEnv b) ty"
    using wkB \<sigma>B_eq by (simp add: typesubst_well_kinded_def)

  have setA: "set as \<subseteq> set ms" and setB: "set bs \<subseteq> set ms"
    using setMS by auto

  \<comment> \<open>The sub-links' raw unions are submaps of the whole link's.\<close>
  have mapsubA: "set (map CM_TypeSubst as) \<subseteq> set (map CM_TypeSubst ms)"
    using setA by auto
  have mapsubB: "set (map CM_TypeSubst bs) \<subseteq> set (map CM_TypeSubst ms)"
    using setB by auto
  have subA: "\<And>k v. fmlookup uA k = Some v \<Longrightarrow> fmlookup uM k = Some v"
    unfolding uA_def uM_def
    using fmlist_union_sublist_lookup[OF sdisjM sdisjA mapsubA] by blast
  have subB: "\<And>k v. fmlookup uB k = Some v \<Longrightarrow> fmlookup uM k = Some v"
    unfolding uB_def uM_def
    using fmlist_union_sublist_lookup[OF sdisjM sdisjB mapsubB] by blast

  \<comment> \<open>The whole union's domain splits as the two sub-unions'.\<close>
  have dom_char: "\<And>xs x. x |\<in>| fmdom (fmlist_union (map CM_TypeSubst xs))
                    \<longleftrightarrow> (\<exists>y \<in> set xs. x |\<in>| fmdom (CM_TypeSubst y))"
    by (auto simp: fmdom_fmlist_union funion_list_member)
  have domM_eq: "fmdom uM = fmdom uA |\<union>| fmdom uB"
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| fmdom uM \<longleftrightarrow> x |\<in>| fmdom uA |\<union>| fmdom uB"
      unfolding uA_def uB_def uM_def
      using setMS by (auto simp: dom_char)
  qed

  \<comment> \<open>Steps 2-4: the merged pair's closure and well-founded dependency relation.\<close>
  have closPair: "is_subst_closure (\<sigma>A ++\<^sub>f \<sigma>B) \<sigma>M"
    by (rule is_subst_closure_merged_pair[OF acycA closA acycB closB closM subA subB domM_eq])
  have acycPair: "acyclic (subst_dep_rel (\<sigma>A ++\<^sub>f \<sigma>B))"
    by (rule subst_dep_rel_merged_pair_acyclic[OF acycA closA acycB closB subA subB domM_eq acycM])
  have wfPair: "wf (subst_dep_rel (\<sigma>A ++\<^sub>f \<sigma>B))"
    using acycPair finite_subst_dep_rel finite_acyclic_wf by blast
  have \<sigma>M_dom_pair: "fmdom \<sigma>M = fmdom (\<sigma>A ++\<^sub>f \<sigma>B)"
    using closPair unfolding is_subst_closure_def by simp

  \<comment> \<open>Fields of the linked result's env.\<close>
  have mDT: "TE_Datatypes (CM_TyEnv m) = fmlist_union (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"
    using meq by (simp add: link_result_def)
  have mTV: "TE_TypeVars (CM_TyEnv m)
               = funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms) |-| fmdom \<sigma>M"
    using meq by (simp add: link_result_def)
  have aDT: "TE_Datatypes (CM_TyEnv a) = fmlist_union (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) as)"
    using aeq by (simp add: link_result_def)
  have aTV: "TE_TypeVars (CM_TyEnv a)
               = funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) as) |-| fmdom \<sigma>A"
    using aeq by (simp add: link_result_def)
  have bDT: "TE_Datatypes (CM_TyEnv b) = fmlist_union (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) bs)"
    using beq by (simp add: link_result_def)
  have bTV: "TE_TypeVars (CM_TyEnv b)
               = funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) bs) |-| fmdom \<sigma>B"
    using beq by (simp add: link_result_def)

  have dtdisjA: "fmdisjoint_list (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) as)"
    using fdisjA unfolding link_fields_disjoint_def by blast
  have dtdisjB: "fmdisjoint_list (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) bs)"
    using fdisjB unfolding link_fields_disjoint_def by blast
  have dtdisjM: "fmdisjoint_list (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"
    using fdisjM unfolding link_fields_disjoint_def by blast

  \<comment> \<open>Each side's datatype lookups are preserved into the linked table...\<close>
  have dtmapsubA: "set (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) as)
                     \<subseteq> set (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"
    using setA by auto
  have dtmapsubB: "set (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) bs)
                     \<subseteq> set (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"
    using setB by auto
  have dtA_sub: "\<forall>k v. fmlookup (TE_Datatypes (CM_TyEnv a)) k = Some v
                   \<longrightarrow> fmlookup (TE_Datatypes (CM_TyEnv m)) k = Some v"
    unfolding aDT mDT
    using fmlist_union_sublist_lookup[OF dtdisjM dtdisjA dtmapsubA] by blast
  have dtB_sub: "\<forall>k v. fmlookup (TE_Datatypes (CM_TyEnv b)) k = Some v
                   \<longrightarrow> fmlookup (TE_Datatypes (CM_TyEnv m)) k = Some v"
    unfolding bDT mDT
    using fmlist_union_sublist_lookup[OF dtdisjM dtdisjB dtmapsubB] by blast

  \<comment> \<open>...and each side's type variables are among the inputs' union.\<close>
  have tvA_sub: "\<forall>x. x |\<in>| TE_TypeVars (CM_TyEnv a)
                   \<longrightarrow> x |\<in>| funion_list (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) ms)"
  proof (intro allI impI)
    fix x assume "x |\<in>| TE_TypeVars (CM_TyEnv a)"
    then have "x |\<in>| funion_list (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) as)"
      using aTV by auto
    then obtain s where s_in: "s \<in> set (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) as)"
                    and x_s: "x |\<in>| s"
      using funion_list_member by metis
    have "s \<in> set (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) ms)"
      using s_in setA by auto
    then show "x |\<in>| funion_list (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) ms)"
      using x_s funion_list_member by metis
  qed
  have tvB_sub: "\<forall>x. x |\<in>| TE_TypeVars (CM_TyEnv b)
                   \<longrightarrow> x |\<in>| funion_list (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) ms)"
  proof (intro allI impI)
    fix x assume "x |\<in>| TE_TypeVars (CM_TyEnv b)"
    then have "x |\<in>| funion_list (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) bs)"
      using bTV by auto
    then obtain s where s_in: "s \<in> set (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) bs)"
                    and x_s: "x |\<in>| s"
      using funion_list_member by metis
    have "s \<in> set (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) ms)"
      using s_in setB by auto
    then show "x |\<in>| funion_list (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) ms)"
      using x_s funion_list_member by metis
  qed

  \<comment> \<open>The main well-founded induction.\<close>
  have main: "\<forall>ty. fmlookup \<sigma>M n = Some ty \<longrightarrow> is_well_kinded (CM_TyEnv m) ty" for n
  proof (induction n rule: wf_induct_rule[OF wfPair])
    case (1 n)
    show ?case
    proof (intro allI impI)
      fix ty assume \<sigma>M_n: "fmlookup \<sigma>M n = Some ty"
      then have "n |\<in>| fmdom \<sigma>M" by (rule fmdomI)
      then have n_pair: "n |\<in>| fmdom (\<sigma>A ++\<^sub>f \<sigma>B)" using \<sigma>M_dom_pair by simp
      then obtain e where entry: "fmlookup (\<sigma>A ++\<^sub>f \<sigma>B) n = Some e"
        by (meson fmlookup_dom_iff)
      have ty_eq: "ty = apply_subst \<sigma>M e"
        using closPair entry \<sigma>M_n unfolding is_subst_closure_def by auto

      \<comment> \<open>The entry at n is one side's resolution, well-kinded in that side's env.\<close>
      have side: "\<exists>env0. is_well_kinded env0 e
           \<and> (\<forall>k v. fmlookup (TE_Datatypes env0) k = Some v
                     \<longrightarrow> fmlookup (TE_Datatypes (CM_TyEnv m)) k = Some v)
           \<and> (\<forall>x. x |\<in>| TE_TypeVars env0
                     \<longrightarrow> x |\<in>| funion_list (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) ms))"
      proof (cases "n |\<in>| fmdom \<sigma>B")
        case True
        then have "fmlookup \<sigma>B n = Some e" using entry by simp
        then have "is_well_kinded (CM_TyEnv b) e" using wkB' by blast
        then show ?thesis using dtB_sub tvB_sub by blast
      next
        case False
        then have "fmlookup \<sigma>A n = Some e" using entry by simp
        then have "is_well_kinded (CM_TyEnv a) e" using wkA' by blast
        then show ?thesis using dtA_sub tvA_sub by blast
      qed
      then obtain env0 where wk0: "is_well_kinded env0 e"
        and dt0: "\<forall>k v. fmlookup (TE_Datatypes env0) k = Some v
                   \<longrightarrow> fmlookup (TE_Datatypes (CM_TyEnv m)) k = Some v"
        and tv0: "\<forall>x. x |\<in>| TE_TypeVars env0
                   \<longrightarrow> x |\<in>| funion_list (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) ms)"
        by blast
      have e_tyvars: "type_tyvars e \<subseteq> fset (TE_TypeVars env0)"
        using is_well_kinded_type_tyvars_subset[OF wk0] .

      \<comment> \<open>Source env for the substitution step: m's env with type variables cut
          down to e's own tyvars (so the coverage obligation below quantifies
          over exactly the tyvars of e).\<close>
      define S where "S = ffilter (\<lambda>x. x \<in> type_tyvars e) (TE_TypeVars env0)"
      have S_mem: "\<And>x. x |\<in>| S \<longleftrightarrow> x \<in> type_tyvars e"
        unfolding S_def using e_tyvars by auto
      define srcEnv where "srcEnv = (CM_TyEnv m) \<lparr> TE_TypeVars := S \<rparr>"
      have wk_src: "is_well_kinded srcEnv e"
      proof (rule is_well_kinded_transfer_mono[OF wk0])
        show "type_tyvars e \<subseteq> fset (TE_TypeVars srcEnv)"
          unfolding srcEnv_def using S_mem by auto
      next
        show "\<And>k v. fmlookup (TE_Datatypes env0) k = Some v \<Longrightarrow>
                     fmlookup (TE_Datatypes srcEnv) k = Some v"
          using dt0 unfolding srcEnv_def by auto
      qed

      have "is_well_kinded (CM_TyEnv m) (apply_subst \<sigma>M e)"
      proof (rule apply_subst_preserves_well_kinded[OF wk_src])
        show "TE_Datatypes (CM_TyEnv m) = TE_Datatypes srcEnv"
          unfolding srcEnv_def by simp
      next
        fix k assume k_src: "k |\<in>| TE_TypeVars srcEnv"
        have k_S: "k |\<in>| S" using k_src unfolding srcEnv_def by simp
        have k_e: "k \<in> type_tyvars e" using k_S S_mem by blast
        have k_env0: "k |\<in>| TE_TypeVars env0" using k_S unfolding S_def by auto
        show "case fmlookup \<sigma>M k of
                Some ty' \<Rightarrow> is_well_kinded (CM_TyEnv m) ty'
              | None \<Rightarrow> k |\<in>| TE_TypeVars (CM_TyEnv m)"
        proof (cases "fmlookup \<sigma>M k")
          case (Some ty')
          \<comment> \<open>k is resolved: (k, n) is a dependency edge of the merged pair,
              so the induction hypothesis applies.\<close>
          have "k |\<in>| fmdom \<sigma>M" using Some by (rule fmdomI)
          then have k_dom: "k |\<in>| fmdom (\<sigma>A ++\<^sub>f \<sigma>B)" using \<sigma>M_dom_pair by simp
          have edge: "(k, n) \<in> subst_dep_rel (\<sigma>A ++\<^sub>f \<sigma>B)"
            unfolding subst_dep_rel_def using k_dom n_pair k_e entry by auto
          have "is_well_kinded (CM_TyEnv m) ty'"
            using "1.IH"[OF edge] Some by blast
          then show ?thesis using Some by simp
        next
          case None
          \<comment> \<open>k is unresolved: it survives into the linked env's type variables.\<close>
          have k_un: "k |\<in>| funion_list (map (\<lambda>y. TE_TypeVars (CM_TyEnv y)) ms)"
            using tv0 k_env0 by blast
          have k_nd: "k |\<notin>| fmdom \<sigma>M"
            using None by (simp add: fmlookup_dom_iff)
          show ?thesis using None k_un k_nd mTV by simp
        qed
      qed
      then show "is_well_kinded (CM_TyEnv m) ty" using ty_eq by simp
    qed
  qed

  show ?thesis
    unfolding typesubst_well_kinded_def \<sigma>M_eq
    using main by blast
qed

end

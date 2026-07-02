theory SubstClosureExistsUnique
  imports MergeSubstsPrelims "HOL-Library.Char_ord" "HOL-Library.List_Lexorder"
begin

(* ========================================================================== *)
(* This file proves that if acyclic_subst_deps u, then there exists a unique \<sigma>
   such that is_subst_closure u \<sigma>. The main result is subst_closure_exists_unique,
   at the end of the file. *)
(* ========================================================================== *)

(* The strict dependencies of T: its subst_dep_rel-predecessors. *)
definition subst_deps :: "TypeSubst \<Rightarrow> string \<Rightarrow> string set" where
  "subst_deps u T = {T'. (T', T) \<in> subst_dep_rel u}"

lemma subst_deps_subset_dom:
  "subst_deps u T \<subseteq> fset (fmdom u)"
  unfolding subst_deps_def using subst_dep_rel_subset by auto

lemma finite_subst_deps:
  "finite (subst_deps u T)"
  by (rule finite_subset[OF subst_deps_subset_dom]) simp

(* The functional whose wfrec fixpoint is the per-variable resolution. It maps a
   recursive callback rec and a variable T to u(T) with each strict dependency T'
   of T replaced by rec T'. Note rec is consulted only at T' \<in> subst_deps u T, all
   of which are subst_dep_rel-predecessors of T - so under cut it sees only
   already-resolved values. *)
definition resolve_F :: "TypeSubst \<Rightarrow> (string \<Rightarrow> CoreType) \<Rightarrow> string \<Rightarrow> CoreType" where
  "resolve_F u rec T =
     apply_subst (fmap_of_list (map (\<lambda>T'. (T', rec T'))
                                    (sorted_list_of_set (subst_deps u T))))
                 (the (fmlookup u T))"

definition resolve :: "TypeSubst \<Rightarrow> string \<Rightarrow> CoreType" where
  "resolve u = wfrec (subst_dep_rel u) (resolve_F u)"

(* resolve_F only consults rec at strict predecessors, so it is admissible: two
   callbacks that agree on T's predecessors give the same result. *)
lemma resolve_F_cong:
  assumes "\<And>T'. (T', T) \<in> subst_dep_rel u \<Longrightarrow> f T' = g T'"
  shows "resolve_F u f T = resolve_F u g T"
proof -
  have fin: "finite (subst_deps u T)" by (rule finite_subst_deps)
  have "map (\<lambda>T'. (T', f T')) (sorted_list_of_set (subst_deps u T))
      = map (\<lambda>T'. (T', g T')) (sorted_list_of_set (subst_deps u T))"
  proof (rule map_cong[OF refl])
    fix T' assume "T' \<in> set (sorted_list_of_set (subst_deps u T))"
    then have "(T', T) \<in> subst_dep_rel u"
      using fin by (simp add: subst_deps_def)
    then show "(T', f T') = (T', g T')" using assms by simp
  qed
  thus ?thesis unfolding resolve_F_def by presburger
qed

(* The wfrec unfolding for resolve. *)
lemma resolve_unfold:
  assumes wf: "wf (subst_dep_rel u)"
  shows "resolve u T = resolve_F u (resolve u) T"
proof -
  have "resolve u T = resolve_F u (cut (resolve u) (subst_dep_rel u) T) T"
    unfolding resolve_def using wf by (simp add: wfrec)
  also have "\<dots> = resolve_F u (resolve u) T"
    by (rule resolve_F_cong) (auto simp: cut_apply)
  finally show ?thesis .
qed

(* The map built by resolving every domain variable. *)
definition resolve_subst :: "TypeSubst \<Rightarrow> TypeSubst" where
  "resolve_subst u =
     fmap_of_list (map (\<lambda>T. (T, resolve u T)) (sorted_list_of_set (fset (fmdom u))))"

lemma fmlookup_resolve_subst:
  "fmlookup (resolve_subst u) T =
     (if T |\<in>| fmdom u then Some (resolve u T) else None)"
proof -
  have dist: "distinct (map fst (map (\<lambda>T. (T, resolve u T)) (sorted_list_of_set (fset (fmdom u)))))"
    by (simp add: comp_def)
  show ?thesis
    unfolding resolve_subst_def
    by (auto simp: fmlookup_of_list map_of_eq_None_iff image_image
                   fmlookup_dom_iff dest!: map_of_SomeD
             intro!: map_of_is_SomeI[OF dist])
qed

lemma fmdom_resolve_subst:
  "fmdom (resolve_subst u) = fmdom u"
proof (rule fset_eqI)
  fix T
  show "T |\<in>| fmdom (resolve_subst u) \<longleftrightarrow> T |\<in>| fmdom u"
    by (simp add: fmlookup_dom_iff fmlookup_resolve_subst)
qed

(* The realization of any variable is free of domain variables. By wf-induction:
   the strict dependencies of T are resolved (IH) to domain-free types, so the
   dep-restricted substitution maps every domain variable of (u T) away, and any
   remaining variable is a non-domain variable. *)
lemma resolve_dom_free:
  assumes wf: "wf (subst_dep_rel u)"
      and "T |\<in>| fmdom u"
  shows "type_tyvars (resolve u T) \<inter> fset (fmdom u) = {}"
using assms(2) proof (induction T rule: wf_induct_rule[OF wf])
  case (1 T)
  then have T_dom: "T |\<in>| fmdom u" by simp
  define s where "s = fmap_of_list (map (\<lambda>T'. (T', resolve u T'))
                                        (sorted_list_of_set (subst_deps u T)))"
  have res: "resolve u T = apply_subst s (the (fmlookup u T))"
    unfolding s_def using resolve_unfold[OF wf] resolve_F_def by metis
  \<comment> \<open>Domain of s is exactly the strict dependencies of T. \<close>
  have dom_s: "fset (fmdom s) = subst_deps u T"
    unfolding s_def
    by (simp add: fset_of_list.rep_eq image_image finite_subst_deps)
  \<comment> \<open>By apply_subst_tyvars_result, the result's tyvars are split into the
      (u T)-tyvars not in dom s, plus the range tyvars of s. \<close>
  have bound: "type_tyvars (apply_subst s (the (fmlookup u T))) \<subseteq>
        (type_tyvars (the (fmlookup u T)) - fset (fmdom s)) \<union> subst_range_tyvars s"
    by (rule apply_subst_tyvars_result)
  \<comment> \<open>(1) Range tyvars of s avoid dom u: each value is resolve u T' for a strict
      dependency T' (a domain variable), domain-free by the IH. \<close>
  have range_free: "subst_range_tyvars s \<inter> fset (fmdom u) = {}"
  proof -
    have "\<And>ty. ty \<in> fmran' s \<Longrightarrow> type_tyvars ty \<inter> fset (fmdom u) = {}"
    proof -
      fix ty assume "ty \<in> fmran' s"
      then obtain T' where look: "fmlookup s T' = Some ty" by (auto simp: fmran'_def)
      then have T'_deps: "T' \<in> subst_deps u T"
        using dom_s by force
      then have edge: "(T', T) \<in> subst_dep_rel u" by (simp add: subst_deps_def)
      then have T'_dom: "T' |\<in>| fmdom u" by (auto simp: subst_dep_rel_def)
      have "ty = resolve u T'"
        using look unfolding s_def
        by (auto simp: fmlookup_of_list finite_subst_deps subst_deps_def
                 dest!: map_of_SomeD split: if_splits)
      with "1.IH"[OF edge T'_dom] show "type_tyvars ty \<inter> fset (fmdom u) = {}"
        by simp
    qed
    thus ?thesis unfolding subst_range_tyvars_def by auto
  qed
  \<comment> \<open>(2) The (u T)-tyvars not in dom s: any domain variable of (u T) is a strict
      dependency of T, hence in dom s; so the leftover avoids dom u. \<close>
  have left_free: "(type_tyvars (the (fmlookup u T)) - fset (fmdom s)) \<inter> fset (fmdom u) = {}"
  proof -
    have "\<And>v. v \<in> type_tyvars (the (fmlookup u T)) \<Longrightarrow> v |\<in>| fmdom u \<Longrightarrow> v \<in> fset (fmdom s)"
    proof -
      fix v assume v_in: "v \<in> type_tyvars (the (fmlookup u T))" and v_dom: "v |\<in>| fmdom u"
      have "(v, T) \<in> subst_dep_rel u"
        unfolding subst_dep_rel_def using T_dom v_dom v_in by auto
      thus "v \<in> fset (fmdom s)" using dom_s by (simp add: subst_deps_def)
    qed
    thus ?thesis by auto
  qed
  from bound range_free left_free res show ?case by auto
qed

(* The constructed witness resolve_subst u is an idempotent closure of u: it has
   domain fmdom u (fmdom_resolve_subst), every value is domain-free
   (resolve_dom_free) giving idempotence, and it satisfies each closure equation
   because resolve u T = apply_subst (resolve_subst u) (u T) (the dep-restricted
   substitution inside resolve agrees with resolve_subst on the tyvars of (u T),
   by apply_subst_cong_on_tyvars). This is the existence witness consumed by
   subst_closure_exists in MergeSubst.thy. *)
lemma resolve_subst_is_closure:
  assumes acyc: "acyclic_subst_deps u"
  shows "is_subst_closure u (resolve_subst u)"
proof -
  have wf: "wf (subst_dep_rel u)" using acyc by (rule acyclic_subst_deps_wf)
  let ?\<sigma> = "resolve_subst u"
  \<comment> \<open>Domain. \<close>
  have dom: "fmdom ?\<sigma> = fmdom u" by (rule fmdom_resolve_subst)
  \<comment> \<open>Idempotence (disjointness): every value is domain-free. \<close>
  have idem: "idempotent_subst ?\<sigma>"
  proof -
    have "\<And>ty. ty \<in> fmran' ?\<sigma> \<Longrightarrow> type_tyvars ty \<inter> fset (fmdom u) = {}"
    proof -
      fix ty assume "ty \<in> fmran' ?\<sigma>"
      then obtain T where look: "fmlookup ?\<sigma> T = Some ty" by (auto simp: fmran'_def)
      then have T_dom: "T |\<in>| fmdom u"
        by (simp add: fmlookup_resolve_subst split: if_splits)
      from look T_dom have "ty = resolve u T"
        by (simp add: fmlookup_resolve_subst)
      thus "type_tyvars ty \<inter> fset (fmdom u) = {}"
        using resolve_dom_free[OF wf T_dom] by simp
    qed
    thus ?thesis
      unfolding idempotent_subst_def subst_range_tyvars_def dom by auto
  qed
  \<comment> \<open>Equations: for a domain variable T with u(T) = ty, \<sigma>(T) = apply_subst \<sigma> ty. \<close>
  have eqs: "\<And>T ty. fmlookup u T = Some ty \<Longrightarrow> fmlookup ?\<sigma> T = Some (apply_subst ?\<sigma> ty)"
  proof -
    fix T ty assume look: "fmlookup u T = Some ty"
    then have T_dom: "T |\<in>| fmdom u" by (simp add: fmlookup_dom_iff)
    define s where "s = fmap_of_list (map (\<lambda>T'. (T', resolve u T'))
                                          (sorted_list_of_set (subst_deps u T)))"
    have res: "resolve u T = apply_subst s ty"
      unfolding s_def using resolve_unfold[OF wf] resolve_F_def look by (metis option.sel)
    have dom_s: "fset (fmdom s) = subst_deps u T"
      unfolding s_def
      by (simp add: fset_of_list.rep_eq image_image finite_subst_deps)
    \<comment> \<open>Lookup in s: Some (resolve u v) on a strict dependency, None elsewhere. \<close>
    have lookup_s: "\<And>v. fmlookup s v =
        (if v \<in> subst_deps u T then Some (resolve u v) else None)"
    proof -
      fix v
      have dist: "distinct (map fst (map (\<lambda>T'. (T', resolve u T'))
                                         (sorted_list_of_set (subst_deps u T))))"
        by (simp add: comp_def finite_subst_deps)
      show "fmlookup s v =
          (if v \<in> subst_deps u T then Some (resolve u v) else None)"
        unfolding s_def
        by (auto simp: fmlookup_of_list map_of_eq_None_iff image_image finite_subst_deps
                 dest!: map_of_SomeD intro!: map_of_is_SomeI[OF dist])
    qed
    \<comment> \<open>s and \<sigma> agree on every tyvar of ty, so apply_subst gives the same. \<close>
    have agree: "\<And>v. v \<in> type_tyvars ty \<Longrightarrow> fmlookup s v = fmlookup ?\<sigma> v"
    proof -
      fix v assume v_in: "v \<in> type_tyvars ty"
      show "fmlookup s v = fmlookup ?\<sigma> v"
      proof (cases "v |\<in>| fmdom u")
        case True
        \<comment> \<open>v is a domain variable of ty, hence a strict dependency of T: in dom s,
            and both maps return resolve u v there. \<close>
        have edge: "(v, T) \<in> subst_dep_rel u"
          unfolding subst_dep_rel_def using T_dom True v_in look by auto
        then have v_deps: "v \<in> subst_deps u T" by (simp add: subst_deps_def)
        have "fmlookup s v = Some (resolve u v)" using v_deps by (simp add: lookup_s)
        moreover have "fmlookup ?\<sigma> v = Some (resolve u v)"
          using True by (simp add: fmlookup_resolve_subst)
        ultimately show ?thesis by simp
      next
        case False
        \<comment> \<open>v is not a domain variable: absent from dom s (\<subseteq> dom u) and from \<sigma>. \<close>
        have "v \<notin> subst_deps u T" using False subst_deps_subset_dom by auto
        then have "fmlookup s v = None" by (simp add: lookup_s)
        moreover have "fmlookup ?\<sigma> v = None"
          using False by (simp add: fmlookup_resolve_subst fmlookup_dom_iff)
        ultimately show ?thesis by simp
      qed
    qed
    have "apply_subst s ty = apply_subst ?\<sigma> ty"
      by (rule apply_subst_cong_on_tyvars[OF agree])
    with res have "resolve u T = apply_subst ?\<sigma> ty" by simp
    moreover have "fmlookup ?\<sigma> T = Some (resolve u T)"
      using T_dom by (simp add: fmlookup_resolve_subst)
    ultimately show "fmlookup ?\<sigma> T = Some (apply_subst ?\<sigma> ty)" by simp
  qed
  show ?thesis
    unfolding is_subst_closure_def using idem dom eqs by blast
qed

(* Uniqueness of subst closure, given acyclic_subst_deps *)
lemma subst_closure_unique:
  assumes acyc: "acyclic_subst_deps u"
      and c1: "is_subst_closure u \<sigma>1"
      and c2: "is_subst_closure u \<sigma>2"
  shows "\<sigma>1 = \<sigma>2"
proof (rule fmap_ext)
  fix n0
  have wf: "wf (subst_dep_rel u)" using acyc by (rule acyclic_subst_deps_wf)
  have dom1: "fmdom \<sigma>1 = fmdom u" and dom2: "fmdom \<sigma>2 = fmdom u"
    using c1 c2 unfolding is_subst_closure_def by simp_all
  show "fmlookup \<sigma>1 n0 = fmlookup \<sigma>2 n0"
  proof (cases "n0 |\<in>| fmdom u")
    case False
    then show ?thesis
      using dom1 dom2 by (simp add: fmdom_notD)
  next
    case True
    show ?thesis
    using True proof (induction n0 rule: wf_induct_rule[OF wf])
      case (1 n)
      then have n_dom: "n |\<in>| fmdom u" by simp
      then obtain ty where ty: "fmlookup u n = Some ty"
        by (auto simp: fmlookup_dom_iff)
      \<comment> \<open>\<sigma>1, \<sigma>2 agree on every type variable of ty. \<close>
      have agree: "\<And>v. v \<in> type_tyvars ty \<Longrightarrow> fmlookup \<sigma>1 v = fmlookup \<sigma>2 v"
      proof -
        fix v assume v_in: "v \<in> type_tyvars ty"
        show "fmlookup \<sigma>1 v = fmlookup \<sigma>2 v"
        proof (cases "v |\<in>| fmdom u")
          case False
          then show ?thesis using dom1 dom2 by (simp add: fmdom_notD)
        next
          case True
          \<comment> \<open>(v, n) is a dependency edge, so the IH applies at v. \<close>
          have "(v, n) \<in> subst_dep_rel u"
            unfolding subst_dep_rel_def using n_dom True v_in ty by auto
          with True 1 show ?thesis by blast
        qed
      qed
      have l1: "fmlookup \<sigma>1 n = Some (apply_subst \<sigma>1 ty)"
        using c1 ty unfolding is_subst_closure_def by blast
      have l2: "fmlookup \<sigma>2 n = Some (apply_subst \<sigma>2 ty)"
        using c2 ty unfolding is_subst_closure_def by blast
      from agree have "apply_subst \<sigma>1 ty = apply_subst \<sigma>2 ty"
        using apply_subst_cong_on_tyvars by blast
      with l1 l2 show ?case by simp
    qed
  qed
qed

(* Main result: acyclic_subst_deps implies existence and uniqueness. *)
theorem subst_closure_exists_unique:
  assumes "acyclic_subst_deps u"
  shows "\<exists>!\<sigma>. is_subst_closure u \<sigma>"
  using assms resolve_subst_is_closure subst_closure_unique by auto


end

theory MergeSubstsHelpers
  imports MergeSubstsPrelims "HOL-Library.Char_ord" "HOL-Library.List_Lexorder"
begin

(* Helpers for the proofs in MergeSubsts.thy. *)


(* ========================================================================== *)
(* Existence and uniqueness of subst closure  *)
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


(* ========================================================================== *)
(* merge_substs associativity helpers *)
(* ========================================================================== *)

(* Associativity is subtle because merge_substs s1 s2 returns the *closure* \<sigma> of
   the union s1 ++f s2, not the raw union. So merge_substs (merge_substs s1 s2) s3
   closes \<sigma> ++f s3, whereas the "all at once" reading would close (s1 ++f s2) ++f s3.
   The whole argument reduces to showing these have the *same* closure: replacing a
   piece of the union by its own closure does not change the final fixed point.

   The engine is one absorption identity: under the final closure \<tau>, applying the
   intermediate closure \<sigma> first is a no-op (apply_subst \<tau> \<circ> apply_subst \<sigma> =
   apply_subst \<tau>). The recursion in apply_subst \<sigma> follows u's dependency relation,
   so the identity is proved by well-founded induction on subst_dep_rel u, exactly
   as in subst_closure_unique. We then transfer closures from the closure-substituted
   union back to the raw union (is_subst_closure_absorb): a closure of \<sigma> ++f w is a
   closure of u ++f w. This direction needs no acyclicity of the raw union - acyclicity
   of u alone drives the induction.

   The intermediate closure can sit on either operand of the outer merge, so we need
   two forms:
   - LEFT (\<sigma> ++f w): used when the inner merge's result is the left operand. Here ++f
     keeps w's equation on the overlap, so a *consistency* hypothesis (consistent \<sigma> w)
     is required to know w agrees with \<sigma> there.
   - RIGHT (p ++f \<sigma>): used when the inner result is the right operand. Here \<sigma> always
     wins on the overlap, so NO consistency hypothesis is needed. This matters: in
     merge_substs_assoc the right-hand grouping does not give us a consistency fact
     strong enough to commute the operands. *)

(* The (left-form) absorption identity on a single domain variable of u, proved for
   all such variables simultaneously by wf-induction on subst_dep_rel u. The closure
   \<tau> is a closure of the closure-substituted union \<sigma> ++f w. *)
lemma closure_absorb_var:
  assumes acyc: "acyclic_subst_deps u"
      and cons: "consistent_subst \<sigma> w"
      and cl_u: "is_subst_closure u \<sigma>"
      and cl_\<sigma>w: "is_subst_closure (\<sigma> ++\<^sub>f w) \<tau>"
      and v_dom: "v |\<in>| fmdom u"
  shows "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var v)) = apply_subst \<tau> (CoreTy_Var v)"
proof -
  have wf: "wf (subst_dep_rel u)" using acyc by (rule acyclic_subst_deps_wf)
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  show ?thesis
  using v_dom proof (induction v rule: wf_induct_rule[OF wf])
    case (1 v)
    then have v_domu: "v |\<in>| fmdom u" by simp
    then obtain ty where ty_u: "fmlookup u v = Some ty"
      by (auto simp: fmlookup_dom_iff)
    \<comment> \<open>\<sigma> resolves v to apply_subst \<sigma> ty (\<sigma> is the closure of u). \<close>
    have \<sigma>_v: "fmlookup \<sigma> v = Some (apply_subst \<sigma> ty)"
      using cl_u ty_u unfolding is_subst_closure_def by blast
    \<comment> \<open>So the goal LHS is apply_subst \<tau> (apply_subst \<sigma> ty). \<close>
    have lhs: "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var v))
             = apply_subst \<tau> (apply_subst \<sigma> ty)"
      using \<sigma>_v by simp
    \<comment> \<open>Step 1: \<tau> absorbs \<sigma> on ty, because every domain variable x of u occurring in
        ty is a strict dependency of v, so the IH applies at x. \<close>
    have absorb_ty: "apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
    proof -
      have pt: "\<And>x. x \<in> type_tyvars ty \<Longrightarrow>
                  apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var x)) = apply_subst \<tau> (CoreTy_Var x)"
      proof -
        fix x assume x_in: "x \<in> type_tyvars ty"
        show "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var x)) = apply_subst \<tau> (CoreTy_Var x)"
        proof (cases "x |\<in>| fmdom u")
          case False
          then have "fmlookup \<sigma> x = None" using dom_\<sigma> by (simp add: fmdom_notD)
          then show ?thesis by simp
        next
          case True
          have edge: "(x, v) \<in> subst_dep_rel u"
            unfolding subst_dep_rel_def using v_domu True x_in ty_u by auto
          show ?thesis using "1.IH"[OF edge True] .
        qed
      qed
      \<comment> \<open>Lift the pointwise identity to ty via val-congruence: \<tau> \<circ> \<sigma> and \<tau> have the
          same effect on every tyvar of ty. \<close>
      have "apply_subst (compose_subst \<tau> \<sigma>) ty = apply_subst \<tau> ty"
      proof (rule apply_subst_cong_on_tyvars_val)
        fix x assume "x \<in> type_tyvars ty"
        from pt[OF this]
        show "apply_subst (compose_subst \<tau> \<sigma>) (CoreTy_Var x) = apply_subst \<tau> (CoreTy_Var x)"
          using compose_subst_correct by presburger
      qed
      then show ?thesis by (simp add: compose_subst_correct)
    qed
    \<comment> \<open>Step 2: apply_subst \<tau> ty = \<tau>(v). In both cases \<tau> closes the (\<sigma> ++f w)-equation
        at v, whose right-hand side is apply_subst \<sigma> ty; Step 1 then finishes. \<close>
    have tau_v: "apply_subst \<tau> ty = apply_subst \<tau> (CoreTy_Var v)"
    proof -
      have look_\<sigma>w: "fmlookup (\<sigma> ++\<^sub>f w) v = Some (apply_subst \<sigma> ty)"
      proof (cases "v |\<in>| fmdom w")
        case False
        \<comment> \<open>v only in \<sigma>: the union keeps \<sigma>(v) = apply_subst \<sigma> ty. \<close>
        show ?thesis using \<sigma>_v False by simp
      next
        case True
        \<comment> \<open>v shared: consistency of \<sigma>, w gives w(v) = \<sigma>(v) = apply_subst \<sigma> ty. \<close>
        have "fmlookup w v = fmlookup \<sigma> v"
          using cons v_domu dom_\<sigma> True unfolding consistent_subst_def by simp
        then have "fmlookup w v = Some (apply_subst \<sigma> ty)" using \<sigma>_v by simp
        then show ?thesis using True by simp
      qed
      have "fmlookup \<tau> v = Some (apply_subst \<tau> (apply_subst \<sigma> ty))"
        using cl_\<sigma>w look_\<sigma>w unfolding is_subst_closure_def by blast
      then show ?thesis using absorb_ty by simp
    qed
    show ?case using lhs absorb_ty tau_v by simp
  qed
qed

(* Absorption lifted from variables to arbitrary types: under the union's closure
   \<tau>, the intermediate closure \<sigma> has no further effect. *)
lemma closure_absorb_type:
  assumes acyc: "acyclic_subst_deps u"
      and cons: "consistent_subst \<sigma> w"
      and cl_u: "is_subst_closure u \<sigma>"
      and cl_\<sigma>w: "is_subst_closure (\<sigma> ++\<^sub>f w) \<tau>"
  shows "apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
proof -
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  \<comment> \<open>\<tau> \<circ> \<sigma> and \<tau> have the same effect on every type variable of ty (val-congruence),
      hence the same effect on ty. \<close>
  have "apply_subst (compose_subst \<tau> \<sigma>) ty = apply_subst \<tau> ty"
  proof (rule apply_subst_cong_on_tyvars_val)
    fix x assume "x \<in> type_tyvars ty"
    have "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var x)) = apply_subst \<tau> (CoreTy_Var x)"
    proof (cases "x |\<in>| fmdom u")
      case False
      then have "fmlookup \<sigma> x = None" using dom_\<sigma> by (simp add: fmdom_notD)
      then show ?thesis by simp
    next
      case True
      then show ?thesis using closure_absorb_var[OF acyc cons cl_u cl_\<sigma>w] by simp
    qed
    then show "apply_subst (compose_subst \<tau> \<sigma>) (CoreTy_Var x) = apply_subst \<tau> (CoreTy_Var x)"
      using compose_subst_correct by presburger
  qed
  then show ?thesis by (simp add: compose_subst_correct)
qed

(* Workhorse: replacing u by its closure \<sigma> inside the union does not change the
   closure. A closure \<tau> of the closure-substituted union \<sigma> ++f w is also a closure
   of the raw union u ++f w. (This is the direction merge_substs_assoc needs on the
   left side: it has the closure of \<sigma> ++f w and wants the closure of the raw union.) *)
lemma is_subst_closure_absorb:
  assumes acyc: "acyclic_subst_deps u"
      and cons: "consistent_subst \<sigma> w"
      and cl_u: "is_subst_closure u \<sigma>"
      and cl_\<sigma>w: "is_subst_closure (\<sigma> ++\<^sub>f w) \<tau>"
  shows "is_subst_closure (u ++\<^sub>f w) \<tau>"
proof -
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  have idem_\<tau>: "idempotent_subst \<tau>" using cl_\<sigma>w unfolding is_subst_closure_def by simp
  \<comment> \<open>u ++f w and \<sigma> ++f w have the same domain, which is \<tau>'s domain. \<close>
  have dom_\<tau>: "fmdom \<tau> = fmdom (u ++\<^sub>f w)"
    using cl_\<sigma>w dom_\<sigma> unfolding is_subst_closure_def by simp
  \<comment> \<open>Each equation of u ++f w is closed by \<tau>. \<close>
  have eqs: "\<And>T ty. fmlookup (u ++\<^sub>f w) T = Some ty \<Longrightarrow> fmlookup \<tau> T = Some (apply_subst \<tau> ty)"
  proof -
    fix T ty assume look: "fmlookup (u ++\<^sub>f w) T = Some ty"
    show "fmlookup \<tau> T = Some (apply_subst \<tau> ty)"
    proof (cases "T |\<in>| fmdom w")
      case True
      \<comment> \<open>w wins in both unions; \<tau> closes the (shared) w-equation. \<close>
      then have "fmlookup w T = Some ty" using look by simp
      then have "fmlookup (\<sigma> ++\<^sub>f w) T = Some ty" using True by simp
      then show ?thesis using cl_\<sigma>w unfolding is_subst_closure_def by blast
    next
      case False
      \<comment> \<open>T \<in> dom u; u(T) = ty. \<sigma> closes u's equation: \<sigma>(T) = apply_subst \<sigma> ty, and \<tau>
          closes that \<sigma>-equation; the extra \<sigma> is absorbed by closure_absorb_type. \<close>
      then have u_T: "fmlookup u T = Some ty" using look by simp
      have \<sigma>_T: "fmlookup \<sigma> T = Some (apply_subst \<sigma> ty)"
        using cl_u u_T unfolding is_subst_closure_def by blast
      then have "fmlookup (\<sigma> ++\<^sub>f w) T = Some (apply_subst \<sigma> ty)"
        using False by simp
      then have "fmlookup \<tau> T = Some (apply_subst \<tau> (apply_subst \<sigma> ty))"
        using cl_\<sigma>w unfolding is_subst_closure_def by blast
      then show ?thesis
        using closure_absorb_type[OF acyc cons cl_u cl_\<sigma>w] by simp
    qed
  qed
  show ?thesis
    unfolding is_subst_closure_def using idem_\<tau> dom_\<tau> eqs by blast
qed

(* ---------------------------------------------------------------------------- *)
(* Right-operand absorption                                                     *)
(*                                                                            *)
(* The mirror of the above, for when the closure \<sigma> sits on the RIGHT of the      *)
(* union: p ++f \<sigma>. Because ++f is right-biased, \<sigma> always wins on the overlap with  *)
(* p, so its substituted values are never discarded - and consequently NO         *)
(* consistency hypothesis is needed here (unlike the left form, where w could      *)
(* override \<sigma>). This is exactly the shape merge_substs produces on the r' side,    *)
(* where the outer merge is merge_substs s1 b with the closure b on the right and   *)
(* the operands are NOT known to be consistent enough to commute.                  *)
(* ---------------------------------------------------------------------------- *)

(* Right-form absorption identity on a single domain variable of u, \<tau> a closure of
   p ++f \<sigma>. Same wf-induction as closure_absorb_var, but Step 2 needs no case split:
   \<sigma> wins in p ++f \<sigma> at every domain variable of u. *)
lemma closure_absorb_var_right:
  assumes acyc: "acyclic_subst_deps u"
      and cl_u: "is_subst_closure u \<sigma>"
      and cl_p\<sigma>: "is_subst_closure (p ++\<^sub>f \<sigma>) \<tau>"
      and v_dom: "v |\<in>| fmdom u"
  shows "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var v)) = apply_subst \<tau> (CoreTy_Var v)"
proof -
  have wf: "wf (subst_dep_rel u)" using acyc by (rule acyclic_subst_deps_wf)
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  show ?thesis
  using v_dom proof (induction v rule: wf_induct_rule[OF wf])
    case (1 v)
    then have v_domu: "v |\<in>| fmdom u" by simp
    then obtain ty where ty_u: "fmlookup u v = Some ty"
      by (auto simp: fmlookup_dom_iff)
    have \<sigma>_v: "fmlookup \<sigma> v = Some (apply_subst \<sigma> ty)"
      using cl_u ty_u unfolding is_subst_closure_def by blast
    have lhs: "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var v))
             = apply_subst \<tau> (apply_subst \<sigma> ty)"
      using \<sigma>_v by simp
    \<comment> \<open>Step 1 (identical to the left form): \<tau> absorbs \<sigma> on ty via the IH. \<close>
    have absorb_ty: "apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
    proof -
      have pt: "\<And>x. x \<in> type_tyvars ty \<Longrightarrow>
                  apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var x)) = apply_subst \<tau> (CoreTy_Var x)"
      proof -
        fix x assume x_in: "x \<in> type_tyvars ty"
        show "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var x)) = apply_subst \<tau> (CoreTy_Var x)"
        proof (cases "x |\<in>| fmdom u")
          case False
          then have "fmlookup \<sigma> x = None" using dom_\<sigma> by (simp add: fmdom_notD)
          then show ?thesis by simp
        next
          case True
          have edge: "(x, v) \<in> subst_dep_rel u"
            unfolding subst_dep_rel_def using v_domu True x_in ty_u by auto
          show ?thesis using "1.IH"[OF edge True] .
        qed
      qed
      have "apply_subst (compose_subst \<tau> \<sigma>) ty = apply_subst \<tau> ty"
      proof (rule apply_subst_cong_on_tyvars_val)
        fix x assume "x \<in> type_tyvars ty"
        from pt[OF this]
        show "apply_subst (compose_subst \<tau> \<sigma>) (CoreTy_Var x) = apply_subst \<tau> (CoreTy_Var x)"
          using compose_subst_correct by presburger
      qed
      then show ?thesis by (simp add: compose_subst_correct)
    qed
    \<comment> \<open>Step 2: \<sigma> wins on dom \<sigma> = dom u in p ++f \<sigma>, with NO case split and NO
        consistency. \<tau> closes the \<sigma>-equation at v. \<close>
    have tau_v: "apply_subst \<tau> ty = apply_subst \<tau> (CoreTy_Var v)"
    proof -
      have "fmlookup (p ++\<^sub>f \<sigma>) v = Some (apply_subst \<sigma> ty)"
        by (simp add: \<sigma>_v dom_\<sigma> v_domu)
      then have "fmlookup \<tau> v = Some (apply_subst \<tau> (apply_subst \<sigma> ty))"
        using cl_p\<sigma> unfolding is_subst_closure_def by blast
      then show ?thesis using absorb_ty by simp
    qed
    show ?case using lhs absorb_ty tau_v by simp
  qed
qed

lemma closure_absorb_type_right:
  assumes acyc: "acyclic_subst_deps u"
      and cl_u: "is_subst_closure u \<sigma>"
      and cl_p\<sigma>: "is_subst_closure (p ++\<^sub>f \<sigma>) \<tau>"
  shows "apply_subst \<tau> (apply_subst \<sigma> ty) = apply_subst \<tau> ty"
proof -
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  have "apply_subst (compose_subst \<tau> \<sigma>) ty = apply_subst \<tau> ty"
  proof (rule apply_subst_cong_on_tyvars_val)
    fix x assume "x \<in> type_tyvars ty"
    have "apply_subst \<tau> (apply_subst \<sigma> (CoreTy_Var x)) = apply_subst \<tau> (CoreTy_Var x)"
    proof (cases "x |\<in>| fmdom u")
      case False
      then have "fmlookup \<sigma> x = None" using dom_\<sigma> by (simp add: fmdom_notD)
      then show ?thesis by simp
    next
      case True
      then show ?thesis using closure_absorb_var_right[OF acyc cl_u cl_p\<sigma>] by simp
    qed
    then show "apply_subst (compose_subst \<tau> \<sigma>) (CoreTy_Var x) = apply_subst \<tau> (CoreTy_Var x)"
      using compose_subst_correct by presburger
  qed
  then show ?thesis by (simp add: compose_subst_correct)
qed

(* Right-operand workhorse: a closure \<tau> of the closure-substituted union p ++f \<sigma> is
   also a closure of the raw union p ++f u. No consistency or big-union acyclicity is
   needed - only acyclicity of u (driving the absorption identity). *)
lemma is_subst_closure_absorb_right:
  assumes acyc: "acyclic_subst_deps u"
      and cl_u: "is_subst_closure u \<sigma>"
      and cl_p\<sigma>: "is_subst_closure (p ++\<^sub>f \<sigma>) \<tau>"
  shows "is_subst_closure (p ++\<^sub>f u) \<tau>"
proof -
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  have idem_\<tau>: "idempotent_subst \<tau>" using cl_p\<sigma> unfolding is_subst_closure_def by simp
  \<comment> \<open>p ++f u and p ++f \<sigma> have the same domain (dom u = dom \<sigma>), which is \<tau>'s. \<close>
  have dom_\<tau>: "fmdom \<tau> = fmdom (p ++\<^sub>f u)"
    using cl_p\<sigma> dom_\<sigma> unfolding is_subst_closure_def by simp
  have eqs: "\<And>T ty. fmlookup (p ++\<^sub>f u) T = Some ty \<Longrightarrow> fmlookup \<tau> T = Some (apply_subst \<tau> ty)"
  proof -
    fix T ty assume look: "fmlookup (p ++\<^sub>f u) T = Some ty"
    show "fmlookup \<tau> T = Some (apply_subst \<tau> ty)"
    proof (cases "T |\<in>| fmdom u")
      case True
      \<comment> \<open>u wins in p ++f u; \<sigma> wins in p ++f \<sigma> (dom \<sigma> = dom u). \<sigma>(T) = apply_subst \<sigma> ty,
          and \<tau> absorbs the extra \<sigma> by the right-form absorption identity. \<close>
      then have u_T: "fmlookup u T = Some ty" using look by simp
      have \<sigma>_T: "fmlookup \<sigma> T = Some (apply_subst \<sigma> ty)"
        using cl_u u_T unfolding is_subst_closure_def by blast
      then have "fmlookup (p ++\<^sub>f \<sigma>) T = Some (apply_subst \<sigma> ty)"
        using dom_\<sigma> True by simp
      then have "fmlookup \<tau> T = Some (apply_subst \<tau> (apply_subst \<sigma> ty))"
        using cl_p\<sigma> unfolding is_subst_closure_def by blast
      then show ?thesis
        using closure_absorb_type_right[OF acyc cl_u cl_p\<sigma>] by simp
    next
      case False
      \<comment> \<open>T \<notin> dom u = dom \<sigma>, so p wins in both unions; \<tau> closes the p-equation. \<close>
      then have "fmlookup (p ++\<^sub>f u) T = fmlookup p T" by simp
      moreover have "fmlookup (p ++\<^sub>f \<sigma>) T = fmlookup p T"
        using False dom_\<sigma> by simp
      ultimately have "fmlookup (p ++\<^sub>f \<sigma>) T = Some ty" using look by simp
      then show ?thesis using cl_p\<sigma> unfolding is_subst_closure_def by blast
    qed
  qed
  show ?thesis
    unfolding is_subst_closure_def using idem_\<tau> dom_\<tau> eqs by blast
qed

(* fmadd is associative, so the two full nestings have equal raw unions. *)
lemma subst_union_assoc:
  "(s1 ++\<^sub>f s2) ++\<^sub>f s3 = s1 ++\<^sub>f (s2 ++\<^sub>f s3)"
  by simp


(* ========================================================================== *)
(* Acyclicity transfer                                                        *)
(*                                                                            *)
(* A naive associativity proof would need the acyclicity of the combined  *)
(* union (s1 ++f s2) ++f s3 as a hypothesis. But this is actually derivable  *)
(* from the merge successes: from merge_substs (merge_substs s1 s2) s3 = Inr,  *)
(* we know the closure-substituted union a ++f s3 is acyclic, and below we      *)
(* transfer that back to the raw union (s1 ++f s2) ++f s3.                      *)
(*                                                                            *)
(* The statement: if u is acyclic, \<sigma> is its closure, \<sigma> and w are consistent,   *)
(* and \<sigma> ++f w is acyclic, then the raw union u ++f w is acyclic. Intuitively,  *)
(* replacing u by its (path-collapsed) closure \<sigma> can only DELETE dependency    *)
(* edges (\<sigma> is idempotent, so has no internal dom-u \<rightarrow> dom-u edges); the extra   *)
(* edges in u ++f w are exactly u's internal edges, and a cycle using them is   *)
(* either a pure-u cycle (impossible, u acyclic) or, after collapsing the       *)
(* internal detours through \<sigma>, a \<sigma> ++f w cycle (impossible by hypothesis).      *)
(* ========================================================================== *)

(* \<sigma> propagates type variables backward along one u-dependency edge: if a occurs
   in u(b), then every type variable of \<sigma>(a) occurs in \<sigma>(b). (Because
   \<sigma>(b) = apply_subst \<sigma> (u b) rewrites the occurrence of a to \<sigma>(a).) *)
lemma subst_dep_rel_sigma_mono:
  assumes cl_u: "is_subst_closure u \<sigma>"
      and edge: "(a, b) \<in> subst_dep_rel u"
  shows "type_tyvars (apply_subst \<sigma> (CoreTy_Var a))
       \<subseteq> type_tyvars (apply_subst \<sigma> (CoreTy_Var b))"
proof -
  from edge have b_du: "b |\<in>| fmdom u" by (auto simp: subst_dep_rel_def)
  from edge have a_in_val: "a \<in> type_tyvars (the (fmlookup u b))"
    by (auto simp: subst_dep_rel_def)
  from b_du obtain tb where tb: "fmlookup u b = Some tb"
    by (auto simp: fmlookup_dom_iff)
  with a_in_val have a_in: "a \<in> type_tyvars tb" by simp
  have \<sigma>_b: "fmlookup \<sigma> b = Some (apply_subst \<sigma> tb)"
    using cl_u tb unfolding is_subst_closure_def by blast
  have sub: "type_tyvars (apply_subst \<sigma> (CoreTy_Var a)) \<subseteq> type_tyvars (apply_subst \<sigma> tb)"
    using type_tyvars_apply_subst_mono[OF a_in] .
  have "apply_subst \<sigma> (CoreTy_Var b) = apply_subst \<sigma> tb"
    using \<sigma>_b by simp
  with sub show ?thesis by simp
qed

(* Single-step bridge: an edge of \<sigma> ++f w followed by an edge of u is again an edge
   of \<sigma> ++f w. Consistency of \<sigma> and w is used here, at a variable shared between
   \<sigma> and w (where ++f keeps w's value): consistency makes w's value equal \<sigma>'s, so
   the dependency information is not lost. *)
lemma subst_dep_rel_bridge_step:
  assumes cons: "consistent_subst \<sigma> w"
      and cl_u: "is_subst_closure u \<sigma>"
      and xy: "(x, y) \<in> subst_dep_rel (\<sigma> ++\<^sub>f w)"
      and yz: "(y, z) \<in> subst_dep_rel u"
  shows "(x, z) \<in> subst_dep_rel (\<sigma> ++\<^sub>f w)"
proof -
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  from yz have y_du: "y |\<in>| fmdom u" and z_du: "z |\<in>| fmdom u"
    unfolding subst_dep_rel_def by auto
  from xy have x_in: "x |\<in>| fmdom (\<sigma> ++\<^sub>f w)"
            and x_val: "x \<in> type_tyvars (the (fmlookup (\<sigma> ++\<^sub>f w) y))"
    unfolding subst_dep_rel_def by auto
  have x_in_\<sigma>y: "x \<in> type_tyvars (apply_subst \<sigma> (CoreTy_Var y))"
  proof (cases "y |\<in>| fmdom w")
    case False
    then have "fmlookup (\<sigma> ++\<^sub>f w) y = fmlookup \<sigma> y" by simp
    with x_val have "x \<in> type_tyvars (the (fmlookup \<sigma> y))" by simp
    moreover obtain ty where "fmlookup \<sigma> y = Some ty"
      using y_du dom_\<sigma> by fastforce
    ultimately show ?thesis by simp
  next
    case True
    have y_d\<sigma>: "y |\<in>| fmdom \<sigma>" using y_du dom_\<sigma> by simp
    have eq: "fmlookup \<sigma> y = fmlookup w y"
      using cons y_d\<sigma> True unfolding consistent_subst_def by blast
    obtain ty where ty: "fmlookup \<sigma> y = Some ty"
      using y_d\<sigma> by (auto simp: fmlookup_dom_iff)
    have "x \<in> type_tyvars (the (fmlookup (\<sigma> ++\<^sub>f w) y))" using x_val .
    then have "x \<in> type_tyvars ty" using True eq ty by auto
    then show ?thesis using ty by simp
  qed
  have x_in_\<sigma>z: "x \<in> type_tyvars (apply_subst \<sigma> (CoreTy_Var z))"
    using x_in_\<sigma>y subst_dep_rel_sigma_mono[OF cl_u yz] by blast
  have x_in_val_z: "x \<in> type_tyvars (the (fmlookup (\<sigma> ++\<^sub>f w) z))"
  proof (cases "z |\<in>| fmdom w")
    case False
    then have "fmlookup (\<sigma> ++\<^sub>f w) z = fmlookup \<sigma> z" by simp
    moreover obtain ty where "fmlookup \<sigma> z = Some ty"
      using z_du dom_\<sigma> by fastforce
    ultimately show ?thesis using x_in_\<sigma>z by simp
  next
    case True
    have z_d\<sigma>: "z |\<in>| fmdom \<sigma>" using z_du dom_\<sigma> by simp
    have eq: "fmlookup \<sigma> z = fmlookup w z"
      using cons z_d\<sigma> True unfolding consistent_subst_def by blast
    obtain ty where ty: "fmlookup \<sigma> z = Some ty"
      using z_d\<sigma> by (auto simp: fmlookup_dom_iff)
    have "x \<in> type_tyvars ty" using x_in_\<sigma>z ty by simp
    then show ?thesis using True eq ty by auto
  qed
  have z_in: "z |\<in>| fmdom (\<sigma> ++\<^sub>f w)" using z_du dom_\<sigma> by simp
  show ?thesis
    unfolding subst_dep_rel_def using x_in z_in x_in_val_z by auto
qed

(* Edge classification: every edge of u ++f w is either an edge of \<sigma> ++f w or an
   edge of u. *)
lemma subst_dep_rel_union_classify:
  assumes cl_u: "is_subst_closure u \<sigma>"
      and edge: "(a, b) \<in> subst_dep_rel (u ++\<^sub>f w)"
  shows "(a, b) \<in> subst_dep_rel (\<sigma> ++\<^sub>f w) \<union> subst_dep_rel u"
proof -
  have dom_\<sigma>: "fmdom \<sigma> = fmdom u" using cl_u unfolding is_subst_closure_def by simp
  from edge have a_in: "a |\<in>| fmdom (u ++\<^sub>f w)" and b_in: "b |\<in>| fmdom (u ++\<^sub>f w)"
            and a_val: "a \<in> type_tyvars (the (fmlookup (u ++\<^sub>f w) b))"
    unfolding subst_dep_rel_def by auto
  have dom_eq: "fmdom (u ++\<^sub>f w) = fmdom (\<sigma> ++\<^sub>f w)" using dom_\<sigma> by simp
  show ?thesis
  proof (cases "b |\<in>| fmdom w")
    case True
    have "the (fmlookup (\<sigma> ++\<^sub>f w) b) = the (fmlookup (u ++\<^sub>f w) b)"
      using True by simp
    with a_val have a_val\<sigma>: "a \<in> type_tyvars (the (fmlookup (\<sigma> ++\<^sub>f w) b))" by simp
    have "a |\<in>| fmdom (\<sigma> ++\<^sub>f w)" using a_in dom_eq by auto
    moreover have "b |\<in>| fmdom (\<sigma> ++\<^sub>f w)" using b_in dom_eq by auto
    ultimately have "(a, b) \<in> subst_dep_rel (\<sigma> ++\<^sub>f w)"
      unfolding subst_dep_rel_def using a_val\<sigma> by auto
    then show ?thesis by simp
  next
    case False
    have b_ndw: "b |\<notin>| fmdom w" using False .
    have b_du: "b |\<in>| fmdom u" using b_in b_ndw by simp
    then obtain tb where tb: "fmlookup u b = Some tb"
      by (auto simp: fmlookup_dom_iff)
    have "the (fmlookup (u ++\<^sub>f w) b) = tb" using b_ndw tb by simp
    with a_val have a_in_tb: "a \<in> type_tyvars tb" by simp
    show ?thesis
    proof (cases "a |\<in>| fmdom u")
      case True
      have "(a, b) \<in> subst_dep_rel u"
        unfolding subst_dep_rel_def using True b_du tb a_in_tb by auto
      then show ?thesis by simp
    next
      case False
      have a_nd\<sigma>: "a |\<notin>| fmdom \<sigma>" using False dom_\<sigma> by simp
      have \<sigma>_b: "fmlookup \<sigma> b = Some (apply_subst \<sigma> tb)"
        using cl_u tb unfolding is_subst_closure_def by blast
      have "apply_subst \<sigma> (CoreTy_Var a) = CoreTy_Var a"
        using a_nd\<sigma> by (simp add: fmdom_notD)
      then have "a \<in> type_tyvars (apply_subst \<sigma> (CoreTy_Var a))" by simp
      then have a_in_\<sigma>tb: "a \<in> type_tyvars (apply_subst \<sigma> tb)"
        using type_tyvars_apply_subst_mono[OF a_in_tb] by blast
      have "fmlookup (\<sigma> ++\<^sub>f w) b = Some (apply_subst \<sigma> tb)"
        using \<sigma>_b b_ndw by simp
      then have val_b\<sigma>: "the (fmlookup (\<sigma> ++\<^sub>f w) b) = apply_subst \<sigma> tb" by simp
      have a_in\<sigma>: "a |\<in>| fmdom (\<sigma> ++\<^sub>f w)" using a_in dom_eq by auto
      have b_in\<sigma>: "b |\<in>| fmdom (\<sigma> ++\<^sub>f w)" using b_du dom_\<sigma> by simp
      have "(a, b) \<in> subst_dep_rel (\<sigma> ++\<^sub>f w)"
        unfolding subst_dep_rel_def using a_in\<sigma> b_in\<sigma> val_b\<sigma> a_in_\<sigma>tb by auto
      then show ?thesis by simp
    qed
  qed
qed

(* The transfer lemma: acyclicity of the closure-substituted union \<sigma> ++f w
   transfers to the raw union u ++f w. *)
lemma acyclic_subst_deps_transfer:
  assumes acyc_u:   "acyclic_subst_deps u"
      and cons:     "consistent_subst \<sigma> w"
      and cl_u:     "is_subst_closure u \<sigma>"
      and acyc_\<sigma>w:  "acyclic_subst_deps (\<sigma> ++\<^sub>f w)"
    shows "acyclic_subst_deps (u ++\<^sub>f w)"
proof -
  define A where "A = subst_dep_rel (\<sigma> ++\<^sub>f w)"
  define B where "B = subst_dep_rel u"
  have accA: "acyclic A" using acyc_\<sigma>w unfolding acyclic_subst_deps_def A_def .
  have accB: "acyclic B" using acyc_u unfolding acyclic_subst_deps_def B_def .
  \<comment> \<open>The single-step bridge, packaged on the abstract relations. \<close>
  have bridge: "\<And>x y z. (x, y) \<in> A \<Longrightarrow> (y, z) \<in> B \<Longrightarrow> (x, z) \<in> A"
    unfolding A_def B_def using subst_dep_rel_bridge_step[OF cons cl_u] by blast
  \<comment> \<open>Lift the bridge: a nonempty A-path followed by a B-edge stays a nonempty A-path. \<close>
  have absorbB: "\<And>x z. (x, z) \<in> A\<^sup>+ O B \<Longrightarrow> (x, z) \<in> A\<^sup>+"
  proof -
    fix x z assume "(x, z) \<in> A\<^sup>+ O B"
    then obtain y where xy: "(x, y) \<in> A\<^sup>+" and yz: "(y, z) \<in> B" by auto
    from xy have "(x, y) \<in> A\<^sup>* O A" by (metis trancl_unfold_right)
    then obtain p where xp: "(x, p) \<in> A\<^sup>*" and pq: "(p, y) \<in> A" by auto
    have "(p, z) \<in> A" using bridge[OF pq yz] .
    then have "(x, z) \<in> A\<^sup>* O A" using xp by auto
    then show "(x, z) \<in> A\<^sup>+" by (metis trancl_unfold_right)
  qed
  \<comment> \<open>And after a (possibly empty) B-path. \<close>
  have absorbBstar: "\<And>p r q. (r, q) \<in> B\<^sup>* \<Longrightarrow> (p, r) \<in> A\<^sup>+ \<Longrightarrow> (p, q) \<in> A\<^sup>+"
  proof -
    fix p r q assume rq: "(r, q) \<in> B\<^sup>*" and pr: "(p, r) \<in> A\<^sup>+"
    have "(p, r) \<in> A\<^sup>+ \<longrightarrow> (p, q) \<in> A\<^sup>+" using rq
    proof (induction rule: rtrancl_induct)
      case base
      then show ?case by simp
    next
      case (step r' q')
      show ?case
      proof
        assume "(p, r) \<in> A\<^sup>+"
        then have "(p, r') \<in> A\<^sup>+" using step.IH by simp
        then have "(p, q') \<in> A\<^sup>+ O B" using step.hyps(2) by auto
        then show "(p, q') \<in> A\<^sup>+" using absorbB by blast
      qed
    qed
    then show "(p, q) \<in> A\<^sup>+" using pr by simp
  qed
  \<comment> \<open>Normal form for a nonempty (A \<union> B)-path: a pure-B path, or a (possibly empty)
      B-prefix followed by a nonempty A-suffix. \<close>
  have normal: "\<And>x y. (x, y) \<in> (A \<union> B)\<^sup>+ \<Longrightarrow> (x, y) \<in> B\<^sup>+ \<union> B\<^sup>* O A\<^sup>+"
  proof -
    fix x y assume "(x, y) \<in> (A \<union> B)\<^sup>+"
    then show "(x, y) \<in> B\<^sup>+ \<union> B\<^sup>* O A\<^sup>+"
    proof (induction rule: trancl_induct)
      case (base y)
      from base show ?case
      proof (elim UnE)
        assume "(x, y) \<in> A"
        then have "(x, y) \<in> A\<^sup>+" by (rule r_into_trancl)
        with rtrancl_refl have "(x, y) \<in> B\<^sup>* O A\<^sup>+" by (rule relcompI)
        then show ?thesis by simp
      next
        assume "(x, y) \<in> B"
        then have "(x, y) \<in> B\<^sup>+" by (rule r_into_trancl)
        then show ?thesis by simp
      qed
    next
      case (step y z)
      from step.hyps(2) show ?case
      proof (elim UnE)
        assume yz: "(y, z) \<in> A"
        from step.IH show ?thesis
        proof (elim UnE)
          assume "(x, y) \<in> B\<^sup>+"
          then have xy: "(x, y) \<in> B\<^sup>*" by (rule trancl_into_rtrancl)
          from yz have "(y, z) \<in> A\<^sup>+" by (rule r_into_trancl)
          with xy have "(x, z) \<in> B\<^sup>* O A\<^sup>+" by (rule relcompI)
          then show ?thesis by simp
        next
          assume "(x, y) \<in> B\<^sup>* O A\<^sup>+"
          then obtain m where xm: "(x, m) \<in> B\<^sup>*" and my: "(m, y) \<in> A\<^sup>+" by auto
          have "(m, z) \<in> A\<^sup>+" using my yz by (rule trancl_into_trancl)
          with xm have "(x, z) \<in> B\<^sup>* O A\<^sup>+" by (rule relcompI)
          then show ?thesis by simp
        qed
      next
        assume yz: "(y, z) \<in> B"
        from step.IH show ?thesis
        proof (elim UnE)
          assume "(x, y) \<in> B\<^sup>+"
          then have "(x, z) \<in> B\<^sup>+" using yz by (rule trancl_into_trancl)
          then show ?thesis by simp
        next
          assume "(x, y) \<in> B\<^sup>* O A\<^sup>+"
          then obtain m where xm: "(x, m) \<in> B\<^sup>*" and my: "(m, y) \<in> A\<^sup>+" by auto
          from my yz have "(m, z) \<in> A\<^sup>+ O B" by (rule relcompI)
          then have "(m, z) \<in> A\<^sup>+" using absorbB by blast
          with xm have "(x, z) \<in> B\<^sup>* O A\<^sup>+" by (rule relcompI)
          then show ?thesis by simp
        qed
      qed
    qed
  qed
  have "acyclic (A \<union> B)"
  proof (rule acyclicI, intro allI)
    fix x
    show "(x, x) \<notin> (A \<union> B)\<^sup>+"
    proof
      assume "(x, x) \<in> (A \<union> B)\<^sup>+"
      from normal[OF this] show False
      proof (elim UnE)
        assume "(x, x) \<in> B\<^sup>+"
        then show False using accB unfolding acyclic_def by blast
      next
        assume "(x, x) \<in> B\<^sup>* O A\<^sup>+"
        then obtain m where xm: "(x, m) \<in> B\<^sup>*" and mx: "(m, x) \<in> A\<^sup>+" by auto
        have "(m, m) \<in> A\<^sup>+" using absorbBstar[OF xm mx] .
        then show False using accA unfolding acyclic_def by blast
      qed
    qed
  qed
  have "subst_dep_rel (u ++\<^sub>f w) \<subseteq> A \<union> B"
    unfolding A_def B_def using subst_dep_rel_union_classify[OF cl_u] by auto
  then have "acyclic (subst_dep_rel (u ++\<^sub>f w))"
    using \<open>acyclic (A \<union> B)\<close> acyclic_subset by blast
  then show ?thesis unfolding acyclic_subst_deps_def .
qed


end

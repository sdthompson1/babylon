theory LinkCollapse
  imports LinkModules SubstAbsorption
begin

(* The **collapse lemma** (step 6b of LINKING.md):

     link_modules as = Inr a \<Longrightarrow> link_modules (as @ [m]) = Inr L
       \<Longrightarrow> link_modules [a, m] = Inr L

   This bridges the two shapes in which links appear downstream: the pipeline
   computes FLAT links over original (unlinked) modules, while the elaborator
   correctness theorem elab_link_well_typed (elaborator/ElabDeclCorrect.thy)
   is stated in the TWO-MODULE form "link_modules [I, M] = Inr L". The
   collapse lemma manufactures the two-module premise from the flat links the
   pipeline actually computes; it is consumed inside elab_module_well_typed.

   Note this does NOT contradict "linked results never compose": the
   composition here re-links a's ORIGINAL inputs plus m (that is what the
   hypothesis link_modules (as @ [m]) = Inr L says), so no original module
   appears twice. The lemma says that, GIVEN that the flat link succeeds,
   the same result is reached through the already-linked a.

   The proof works off the success characterizations (link_modules_Inr_iff /
   merge_all_substs_Inr_iff). The interesting part is the substitution layer:
   a's substitution is the idempotent closure \<sigma>a of the union ua of as's
   substitutions, so we must show that the closure \<sigma> of ua ++f sm (sm = m's
   substitution) is also the closure of \<sigma>a ++f sm:
    - the closure equations transfer by the absorption identity
      (closure_absorb_type_raw, SubstAbsorption.thy);
    - acyclicity transfers because every dependency edge of \<sigma>a ++f sm maps
      into the transitive closure of the dependency relation of ua ++f sm
      (\<sigma>a's entries are resolved-through versions of ua's, so their tyvars
      are reached along ua-chains).
   Everything else is finite-map/fset algebra: the field-wise unions over
   [a, m] equal those over as @ [m] because a's fields are already the
   unions over as. *)


(* ========================================================================== *)
(* List-union algebra: append and snoc forms                                  *)
(* ========================================================================== *)

(* The union of an appended list is the union of the unions. (No disjointness
   needed: both sides are right-biased in the same order.) *)
lemma fmlist_union_append:
  "fmlist_union (xs @ ys) = fmlist_union xs ++\<^sub>f fmlist_union ys"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons x xs)
  show ?case
    by (simp add: fmlist_union_Cons Cons.IH)
qed

lemma funion_list_append:
  "funion_list (xs @ ys) = funion_list xs |\<union>| funion_list ys"
proof (rule fset_eqI)
  fix n
  show "n |\<in>| funion_list (xs @ ys) \<longleftrightarrow> n |\<in>| funion_list xs |\<union>| funion_list ys"
    by (auto simp: funion_list_member)
qed

(* Subtracting a larger set absorbs an earlier subtraction of a smaller one:
   the shape of the type-variable fields of a collapsed link result. *)
lemma fminus_union_absorb:
  assumes "d1 |\<subseteq>| d2"
  shows "((X |-| d1) |\<union>| Y) |-| d2 = (X |\<union>| Y) |-| d2"
proof (rule fset_eqI)
  fix n
  show "n |\<in>| ((X |-| d1) |\<union>| Y) |-| d2 \<longleftrightarrow> n |\<in>| (X |\<union>| Y) |-| d2"
    using assms by (auto dest: fsubsetD)
qed


(* ========================================================================== *)
(* Disjointness algebra: snoc and pair forms                                  *)
(* ========================================================================== *)

lemma fmdisjoint_list_snoc:
  "fmdisjoint_list (xs @ [y]) \<longleftrightarrow> (\<forall>t \<in> set xs. fmdisjoint t y) \<and> fmdisjoint_list xs"
proof -
  have "fmdisjoint_list (xs @ [y]) = fmdisjoint_list (y # xs)"
    by (rule fmdisjoint_list_mset_cong) simp
  also have "\<dots> = ((\<forall>t \<in> set xs. fmdisjoint y t) \<and> fmdisjoint_list xs)"
    by (rule fmdisjoint_list_Cons)
  also have "\<dots> = ((\<forall>t \<in> set xs. fmdisjoint t y) \<and> fmdisjoint_list xs)"
    using fmdisjoint_sym by blast
  finally show ?thesis .
qed

lemma fmdisjoint_list_pair:
  "fmdisjoint_list [x, y] \<longleftrightarrow> fmdisjoint x y"
  by (simp add: fmdisjoint_list_Cons)

(* A map disjoint from every element of a list is disjoint from their union. *)
lemma fmdisjoint_fmlist_union_left:
  assumes each: "\<forall>t \<in> set xs. fmdisjoint t y"
  shows "fmdisjoint (fmlist_union xs) y"
  unfolding fmdisjoint_def
proof (rule fset_eqI)
  fix n
  show "n |\<in>| fmdom (fmlist_union xs) |\<inter>| fmdom y \<longleftrightarrow> n |\<in>| {||}"
  proof
    assume "n |\<in>| fmdom (fmlist_union xs) |\<inter>| fmdom y"
    then have n_u: "n |\<in>| fmdom (fmlist_union xs)" and n_y: "n |\<in>| fmdom y" by auto
    have "n |\<in>| funion_list (map fmdom xs)"
      using n_u by (simp add: fmdom_fmlist_union)
    then obtain t where "t \<in> set xs" and "n |\<in>| fmdom t"
      by (auto simp: funion_list_member)
    then show "n |\<in>| {||}" using each n_y fmdisjoint_not_both by metis
  qed simp
qed

(* Collapsing the head: if a snoc list is pairwise disjoint, so is the pair
   "union of the prefix, last element". *)
lemma fmdisjoint_list_collapse_head:
  assumes "fmdisjoint_list (xs @ [y])"
  shows "fmdisjoint_list [fmlist_union xs, y]"
proof -
  have "\<forall>t \<in> set xs. fmdisjoint t y"
    using assms fmdisjoint_list_snoc by blast
  then have "fmdisjoint (fmlist_union xs) y"
    by (rule fmdisjoint_fmlist_union_left)
  then show ?thesis by (simp add: fmdisjoint_list_pair)
qed


(* ========================================================================== *)
(* The merged substitution's names come from the inputs                       *)
(* ========================================================================== *)

(* A standalone form of the "names_sub" step inside
   link_modules_capture_avoiding (LinkModules.thy): every name touched by the
   idempotent closure of a disjoint union is touched by some input. Domain
   side: the closure's domain IS the union of the input domains. Range side:
   the closure's range tyvars are leftover names of the raw union
   (is_subst_closure_range_tyvars, MergeSubstsPrelims.thy). *)
lemma merge_closure_subst_names:
  assumes sdisj: "fmdisjoint_list ss"
      and acyc: "acyclic_subst_deps (fmlist_union ss)"
      and clos: "is_subst_closure (fmlist_union ss) \<sigma>"
      and n_in: "n |\<in>| subst_names \<sigma>"
  shows "\<exists>s \<in> set ss. n |\<in>| subst_names s"
proof -
  let ?u = "fmlist_union ss"
  from n_in consider (dom) "n |\<in>| fmdom \<sigma>" | (rng) "n \<in> subst_range_tyvars \<sigma>"
    using subst_names_member by auto
  then show ?thesis
  proof cases
    case dom
    then have "n |\<in>| fmdom ?u"
      using clos unfolding is_subst_closure_def by simp
    then obtain ty where "fmlookup ?u n = Some ty"
      by (auto simp: fmlookup_dom_iff)
    then obtain s where s_in: "s \<in> set ss" and s_lk: "fmlookup s n = Some ty"
      using fmlist_union_lookup[OF sdisj] by blast
    have "n |\<in>| fmdom s" using s_lk by (rule fmdomI)
    then show ?thesis using s_in by (auto simp: subst_names_member)
  next
    case rng
    then have "n \<in> subst_range_tyvars ?u"
      using is_subst_closure_range_tyvars[OF acyc clos] by auto
    then obtain ty where "ty \<in> fmran' ?u" and n_ty: "n \<in> type_tyvars ty"
      unfolding subst_range_tyvars_def by auto
    then obtain k where "fmlookup ?u k = Some ty"
      by (auto simp: fmlookup_ran'_iff)
    then obtain s where s_in: "s \<in> set ss" and s_lk: "fmlookup s k = Some ty"
      using fmlist_union_lookup[OF sdisj] by blast
    have "ty \<in> fmran' s" using s_lk by (rule fmran'I)
    then have "n \<in> subst_range_tyvars s"
      using n_ty unfolding subst_range_tyvars_def by auto
    then show ?thesis using s_in by (auto simp: subst_names_member)
  qed
qed


(* ========================================================================== *)
(* Bound tyvars of a link result come from the inputs                         *)
(* ========================================================================== *)

lemma module_bound_tyvars_link_result:
  assumes disj: "link_fields_disjoint ms"
      and n_in: "n |\<in>| module_bound_tyvars (link_result ms \<sigma>)"
  shows "\<exists>x \<in> set ms. n |\<in>| module_bound_tyvars x"
proof -
  have djF: "fmdisjoint_list (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)"
   and djC: "fmdisjoint_list (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)"
    using disj unfolding link_fields_disjoint_def by blast+
  from module_bound_tyvars_E[OF n_in] show ?thesis
  proof
    assume "\<exists>name info. fmlookup (TE_Functions (CM_TyEnv (link_result ms \<sigma>))) name = Some info
                        \<and> n \<in> set (FI_TyArgs info)"
    then obtain name info where
      lk: "fmlookup (TE_Functions (CM_TyEnv (link_result ms \<sigma>))) name = Some info" and
      n_args: "n \<in> set (FI_TyArgs info)" by blast
    have "TE_Functions (CM_TyEnv (link_result ms \<sigma>))
            = fmlist_union (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)"
      by (simp add: link_result_def)
    with lk have "\<exists>f \<in> set (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms).
                    fmlookup f name = Some info"
      using fmlist_union_lookup[OF djF] by simp
    then obtain x where "x \<in> set ms"
        and "fmlookup (TE_Functions (CM_TyEnv x)) name = Some info" by auto
    then show ?thesis using module_bound_tyvars_fun n_args by blast
  next
    assume "\<exists>ctorName dtName tyVars payload.
              fmlookup (TE_DataCtors (CM_TyEnv (link_result ms \<sigma>))) ctorName
                = Some (dtName, tyVars, payload) \<and> n \<in> set tyVars"
    then obtain ctorName dtName tyVars payload where
      lk: "fmlookup (TE_DataCtors (CM_TyEnv (link_result ms \<sigma>))) ctorName
             = Some (dtName, tyVars, payload)" and
      n_tvs: "n \<in> set tyVars" by blast
    have "TE_DataCtors (CM_TyEnv (link_result ms \<sigma>))
            = fmlist_union (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)"
      by (simp add: link_result_def)
    with lk have "\<exists>f \<in> set (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms).
                    fmlookup f ctorName = Some (dtName, tyVars, payload)"
      using fmlist_union_lookup[OF djC] by simp
    then obtain x where "x \<in> set ms"
        and "fmlookup (TE_DataCtors (CM_TyEnv x)) ctorName = Some (dtName, tyVars, payload)"
      by auto
    then show ?thesis using module_bound_tyvars_ctor n_tvs by blast
  qed
qed


(* ========================================================================== *)
(* The substitution layer: \<sigma> is also the closure of \<sigma>a ++f sm                  *)
(* ========================================================================== *)

(* A dependency of a CLOSURE entry maps into a dependency CHAIN of the raw
   union: if x (a domain variable of ua ++f sm) occurs in \<sigma>a's resolution of
   S, then x is reachable from S in the dependency relation of ua ++f sm.
   By well-founded induction over ua's own (acyclic) dependency relation:
   \<sigma>a(S) = apply_subst \<sigma>a (ua S), and each tyvar of that either survives raw
   from ua(S) - a direct edge - or was introduced by resolving a dependency a
   of S, giving an edge (a, S) and, recursively, a chain from a. *)
lemma closure_entry_deps_trancl:
  assumes djsm: "fmdom ua |\<inter>| fmdom sm = {||}"
      and acyc_ua: "acyclic_subst_deps ua"
      and cl_a: "is_subst_closure ua \<sigma>a"
      and x_dom: "x |\<in>| fmdom (ua ++\<^sub>f sm)"
      and S_dom: "S |\<in>| fmdom ua"
      and x_in: "x \<in> type_tyvars (the (fmlookup \<sigma>a S))"
  shows "(x, S) \<in> (subst_dep_rel (ua ++\<^sub>f sm))\<^sup>+"
proof -
  have wf: "wf (subst_dep_rel ua)" using acyc_ua by (rule acyclic_subst_deps_wf)
  have dom_\<sigma>a: "fmdom \<sigma>a = fmdom ua" using cl_a unfolding is_subst_closure_def by simp
  let ?u = "ua ++\<^sub>f sm"
  show ?thesis
    using S_dom x_in
  proof (induction S rule: wf_induct_rule[OF wf])
    case (1 S)
    have S_domua: "S |\<in>| fmdom ua" using "1.prems" by simp
    then obtain uty where uty: "fmlookup ua S = Some uty"
      by (auto simp: fmlookup_dom_iff)
    have \<sigma>a_S: "fmlookup \<sigma>a S = Some (apply_subst \<sigma>a uty)"
      using cl_a uty unfolding is_subst_closure_def by blast
    have x_apply: "x \<in> type_tyvars (apply_subst \<sigma>a uty)"
      using "1.prems" \<sigma>a_S by simp
    \<comment> \<open>The union's entry at S is ua's own (S is not in sm's domain).\<close>
    have S_not_sm: "S |\<notin>| fmdom sm" using S_domua djsm by auto
    have u_S: "fmlookup ?u S = Some uty"
      using uty S_not_sm by simp
    have S_domU: "S |\<in>| fmdom ?u" using S_domua by auto
    from type_tyvars_apply_subst_decompose[OF x_apply]
    show ?case
    proof (elim disjE conjE bexE)
      \<comment> \<open>x survives raw from ua(S), outside \<sigma>a's domain: a direct edge.\<close>
      assume x_uty: "x \<in> type_tyvars uty"
      have "(x, S) \<in> subst_dep_rel ?u"
        unfolding subst_dep_rel_def
        using x_dom S_domU u_S x_uty by auto
      then show ?case by (rule r_into_trancl)
    next
      \<comment> \<open>x was introduced by resolving a dependency a of S: recurse on a.\<close>
      fix a assume a_uty: "a \<in> type_tyvars uty" and a_dom: "a |\<in>| fmdom \<sigma>a"
        and x_a: "x \<in> type_tyvars (apply_subst \<sigma>a (CoreTy_Var a))"
      have a_domua: "a |\<in>| fmdom ua" using a_dom dom_\<sigma>a by simp
      have edge_ua: "(a, S) \<in> subst_dep_rel ua"
        unfolding subst_dep_rel_def using S_domua a_domua a_uty uty by auto
      have edge_u: "(a, S) \<in> subst_dep_rel ?u"
        unfolding subst_dep_rel_def using S_domU a_domua u_S a_uty by auto
      obtain aty where \<sigma>a_a: "fmlookup \<sigma>a a = Some aty"
        using a_dom by (auto simp: fmlookup_dom_iff)
      have x_aty: "x \<in> type_tyvars (the (fmlookup \<sigma>a a))"
        using x_a \<sigma>a_a by simp
      have "(x, a) \<in> (subst_dep_rel ?u)\<^sup>+"
        using "1.IH"[OF edge_ua a_domua x_aty] .
      then show ?case using edge_u by (rule trancl_into_trancl)
    qed
  qed
qed

(* Hence every dependency edge of \<sigma>a ++f sm lies in the transitive closure of
   the dependency relation of ua ++f sm: sm's entries are identical in both
   unions (direct edges), and \<sigma>a's entries map into chains by the previous
   lemma. *)
lemma subst_dep_rel_closure_union_subset:
  assumes djsm: "fmdom ua |\<inter>| fmdom sm = {||}"
      and acyc_ua: "acyclic_subst_deps ua"
      and cl_a: "is_subst_closure ua \<sigma>a"
  shows "subst_dep_rel (\<sigma>a ++\<^sub>f sm) \<subseteq> (subst_dep_rel (ua ++\<^sub>f sm))\<^sup>+"
proof
  fix p assume p_in: "p \<in> subst_dep_rel (\<sigma>a ++\<^sub>f sm)"
  obtain T' T where p_eq: "p = (T', T)" by (cases p) auto
  have T_dom: "T |\<in>| fmdom (\<sigma>a ++\<^sub>f sm)"
   and T'_dom: "T' |\<in>| fmdom (\<sigma>a ++\<^sub>f sm)"
   and T'_in: "T' \<in> type_tyvars (the (fmlookup (\<sigma>a ++\<^sub>f sm) T))"
    using p_in p_eq unfolding subst_dep_rel_def by auto
  have dom_\<sigma>a: "fmdom \<sigma>a = fmdom ua" using cl_a unfolding is_subst_closure_def by simp
  have dom_eq: "fmdom (\<sigma>a ++\<^sub>f sm) = fmdom (ua ++\<^sub>f sm)" using dom_\<sigma>a by simp
  show "p \<in> (subst_dep_rel (ua ++\<^sub>f sm))\<^sup>+"
  proof (cases "T |\<in>| fmdom sm")
    case True
    \<comment> \<open>sm's own entry: identical in both unions, so a direct edge.\<close>
    have "fmlookup (\<sigma>a ++\<^sub>f sm) T = fmlookup sm T"
     and "fmlookup (ua ++\<^sub>f sm) T = fmlookup sm T"
      using True by simp_all
    then have "(T', T) \<in> subst_dep_rel (ua ++\<^sub>f sm)"
      unfolding subst_dep_rel_def
      using T_dom T'_dom T'_in dom_eq by auto
    then have "(T', T) \<in> (subst_dep_rel (ua ++\<^sub>f sm))\<^sup>+"
      by (rule r_into_trancl)
    then show ?thesis using p_eq by simp
  next
    case False
    then have T_ua: "T |\<in>| fmdom ua" using T_dom dom_\<sigma>a by auto
    have "fmlookup (\<sigma>a ++\<^sub>f sm) T = fmlookup \<sigma>a T" using False by simp
    then have T'_in_\<sigma>a: "T' \<in> type_tyvars (the (fmlookup \<sigma>a T))" using T'_in by simp
    have T'_domU: "T' |\<in>| fmdom (ua ++\<^sub>f sm)" using T'_dom dom_eq by auto
    have "(T', T) \<in> (subst_dep_rel (ua ++\<^sub>f sm))\<^sup>+"
      using closure_entry_deps_trancl[OF djsm acyc_ua cl_a T'_domU T_ua T'_in_\<sigma>a] .
    then show ?thesis using p_eq by simp
  qed
qed

(* Acyclicity transfers from the raw union to the closed-prefix union. *)
lemma acyclic_closure_union:
  assumes djsm: "fmdom ua |\<inter>| fmdom sm = {||}"
      and acyc_ua: "acyclic_subst_deps ua"
      and cl_a: "is_subst_closure ua \<sigma>a"
      and acyc_u: "acyclic_subst_deps (ua ++\<^sub>f sm)"
  shows "acyclic_subst_deps (\<sigma>a ++\<^sub>f sm)"
proof -
  have "acyclic ((subst_dep_rel (ua ++\<^sub>f sm))\<^sup>+)"
    using acyc_u unfolding acyclic_subst_deps_def acyclic_def
    by (simp add: trancl_id[OF trans_trancl])
  then show ?thesis
    unfolding acyclic_subst_deps_def
    using subst_dep_rel_closure_union_subset[OF djsm acyc_ua cl_a] acyclic_subset
    by blast
qed

(* The closure equations transfer: \<sigma> (the closure of ua ++f sm) also closes
   \<sigma>a ++f sm. sm's entries are common to both unions; \<sigma>a's entries are
   apply_subst \<sigma>a images of ua's, and \<sigma> absorbs the inner \<sigma>a application
   (closure_absorb_type_raw). *)
lemma is_subst_closure_collapse:
  assumes djsm: "fmdom ua |\<inter>| fmdom sm = {||}"
      and acyc_ua: "acyclic_subst_deps ua"
      and cl_a: "is_subst_closure ua \<sigma>a"
      and cl_u: "is_subst_closure (ua ++\<^sub>f sm) \<sigma>"
  shows "is_subst_closure (\<sigma>a ++\<^sub>f sm) \<sigma>"
proof -
  have dom_\<sigma>a: "fmdom \<sigma>a = fmdom ua" using cl_a unfolding is_subst_closure_def by simp
  have idem: "idempotent_subst \<sigma>" using cl_u unfolding is_subst_closure_def by blast
  have dom_ok: "fmdom \<sigma> = fmdom (\<sigma>a ++\<^sub>f sm)"
    using cl_u dom_\<sigma>a unfolding is_subst_closure_def by simp
  \<comment> \<open>The absorption engine wants the union with ua as the right operand;
      commute using disjointness.\<close>
  have comm: "ua ++\<^sub>f sm = sm ++\<^sub>f ua"
    using djsm by (metis fmdisjoint_add_commute fmdisjoint_def)
  have cl_u': "is_subst_closure (sm ++\<^sub>f ua) \<sigma>" using cl_u comm by simp
  have absorb: "\<And>ty. apply_subst \<sigma> (apply_subst \<sigma>a ty) = apply_subst \<sigma> ty"
    using closure_absorb_type_raw[OF acyc_ua cl_a cl_u'] .
  have eqs: "fmlookup \<sigma> T = Some (apply_subst \<sigma> ty)"
    if lk: "fmlookup (\<sigma>a ++\<^sub>f sm) T = Some ty" for T ty
  proof (cases "T |\<in>| fmdom sm")
    case True
    then have "fmlookup sm T = Some ty" using lk by simp
    then have "fmlookup (ua ++\<^sub>f sm) T = Some ty" using True by simp
    then show ?thesis using cl_u unfolding is_subst_closure_def by blast
  next
    case False
    then have \<sigma>a_T: "fmlookup \<sigma>a T = Some ty" using lk by simp
    then have T_ua: "T |\<in>| fmdom ua" using dom_\<sigma>a by (metis fmdomI)
    then obtain uty where uty: "fmlookup ua T = Some uty"
      by (auto simp: fmlookup_dom_iff)
    have ty_eq: "ty = apply_subst \<sigma>a uty"
      using cl_a uty \<sigma>a_T unfolding is_subst_closure_def by auto
    have u_T: "fmlookup (ua ++\<^sub>f sm) T = Some uty" using uty False by simp
    have "fmlookup \<sigma> T = Some (apply_subst \<sigma> uty)"
      using cl_u u_T unfolding is_subst_closure_def by blast
    then show ?thesis using ty_eq absorb by simp
  qed
  show ?thesis
    unfolding is_subst_closure_def using idem dom_ok eqs by blast
qed


(* ========================================================================== *)
(* Collapsing a link result                                                   *)
(* ========================================================================== *)

(* Replacing a list prefix by its own link result leaves the outer link
   result unchanged: each field of link_result as \<sigma>a is already the union
   over as (the unions re-associate), and the type-variable fields' earlier
   subtraction of fmdom \<sigma>a is absorbed by the outer subtraction of the larger
   fmdom \<sigma>. *)
lemma link_result_collapse:
  assumes dom_sub: "fmdom \<sigma>a |\<subseteq>| fmdom \<sigma>"
  shows "link_result (link_result as \<sigma>a # ms) \<sigma> = link_result (as @ ms) \<sigma>"
  unfolding link_result_def
  by (simp add: fmlist_union_Cons fmlist_union_append funion_list_append
                fminus_union_absorb[OF dom_sub])

(* The pairwise-disjointness of [link_result as \<sigma>, m] follows from that of
   as @ [m]: each of the seven families of the link result is the union of
   the corresponding family over as. *)
lemma link_fields_disjoint_collapse:
  assumes disj: "link_fields_disjoint (as @ [m])"
  shows "link_fields_disjoint [link_result as \<sigma>, m]"
proof -
  have d1: "fmdisjoint_list (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) as
              @ [TE_GlobalVars (CM_TyEnv m)])"
   and d2: "fmdisjoint_list (map (\<lambda>x. TE_Functions (CM_TyEnv x)) as
              @ [TE_Functions (CM_TyEnv m)])"
   and d3: "fmdisjoint_list (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) as
              @ [TE_Datatypes (CM_TyEnv m)])"
   and d4: "fmdisjoint_list (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) as
              @ [TE_DataCtors (CM_TyEnv m)])"
   and d5: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) as
              @ [TE_DataCtorsByType (CM_TyEnv m)])"
   and d6: "fmdisjoint_list (map CM_GlobalVars as @ [CM_GlobalVars m])"
   and d7: "fmdisjoint_list (map CM_Functions as @ [CM_Functions m])"
    using disj unfolding link_fields_disjoint_def by simp_all
  show ?thesis
    unfolding link_fields_disjoint_def
    by (simp add: link_result_def
                  fmdisjoint_list_collapse_head[OF d1] fmdisjoint_list_collapse_head[OF d2]
                  fmdisjoint_list_collapse_head[OF d3] fmdisjoint_list_collapse_head[OF d4]
                  fmdisjoint_list_collapse_head[OF d5] fmdisjoint_list_collapse_head[OF d6]
                  fmdisjoint_list_collapse_head[OF d7])
qed


(* ========================================================================== *)
(* The collapse lemma                                                         *)
(* ========================================================================== *)

theorem link_modules_collapse:
  assumes ok_a: "link_modules as = Inr a"
      and ok_L: "link_modules (as @ [m]) = Inr L"
  shows "link_modules [a, m] = Inr L"
proof -
  \<comment> \<open>Unpack both successful links via the declarative characterization.\<close>
  obtain \<sigma>a where
    disj_a: "link_fields_disjoint as" and
    sdisj_a: "fmdisjoint_list (map CM_TypeSubst as)" and
    acyc_a: "acyclic_subst_deps (fmlist_union (map CM_TypeSubst as))" and
    clos_a: "is_subst_closure (fmlist_union (map CM_TypeSubst as)) \<sigma>a" and
    a_eq: "a = link_result as \<sigma>a"
    using ok_a link_modules_Inr_iff_closure by blast
  obtain \<sigma> where
    disj_L: "link_fields_disjoint (as @ [m])" and
    cap_L: "link_capture_ok (as @ [m])" and
    sdisj_L: "fmdisjoint_list (map CM_TypeSubst (as @ [m]))" and
    acyc_L: "acyclic_subst_deps (fmlist_union (map CM_TypeSubst (as @ [m])))" and
    clos_L: "is_subst_closure (fmlist_union (map CM_TypeSubst (as @ [m]))) \<sigma>" and
    rok_L: "link_runtime_ok (as @ [m]) \<sigma>" and
    L_eq: "L = link_result (as @ [m]) \<sigma>"
    using ok_L link_modules_Inr_iff_closure by blast

  define ua where "ua = fmlist_union (map CM_TypeSubst as)"
  define sm where "sm = CM_TypeSubst m"

  have subst_a: "CM_TypeSubst a = \<sigma>a"
    using a_eq by (simp add: link_result_def)
  have u_eq: "fmlist_union (map CM_TypeSubst (as @ [m])) = ua ++\<^sub>f sm"
    by (simp add: fmlist_union_append ua_def sm_def)

  have acyc_ua: "acyclic_subst_deps ua" using acyc_a unfolding ua_def .
  have clos_ua: "is_subst_closure ua \<sigma>a" using clos_a unfolding ua_def .
  have acyc_u: "acyclic_subst_deps (ua ++\<^sub>f sm)" using acyc_L u_eq by simp
  have clos_u: "is_subst_closure (ua ++\<^sub>f sm) \<sigma>" using clos_L u_eq by simp

  \<comment> \<open>m's substitution domain avoids ua's (from the flat link's disjointness).\<close>
  have sm_dj_each: "\<forall>t \<in> set (map CM_TypeSubst as). fmdisjoint t sm"
  proof -
    have "fmdisjoint_list (map CM_TypeSubst as @ [sm])"
      using sdisj_L by (simp add: sm_def)
    then show ?thesis using fmdisjoint_list_snoc by blast
  qed
  have djsm: "fmdom ua |\<inter>| fmdom sm = {||}"
    using fmdisjoint_fmlist_union_left[OF sm_dj_each]
    unfolding ua_def fmdisjoint_def .

  have dom_\<sigma>a: "fmdom \<sigma>a = fmdom ua"
    using clos_ua unfolding is_subst_closure_def by simp
  have dom_\<sigma>a_sub: "fmdom \<sigma>a |\<subseteq>| fmdom \<sigma>"
  proof -
    have "fmdom \<sigma> = fmdom (ua ++\<^sub>f sm)"
      using clos_u unfolding is_subst_closure_def by simp
    then show ?thesis using dom_\<sigma>a by auto
  qed

  \<comment> \<open>(1) The result modules agree.\<close>
  have lr_eq: "link_result [a, m] \<sigma> = link_result (as @ [m]) \<sigma>"
    by (simp add: a_eq link_result_collapse[OF dom_\<sigma>a_sub])
  have L_am: "L = link_result [a, m] \<sigma>"
    using L_eq lr_eq by simp

  \<comment> \<open>(2) Field disjointness of the pair.\<close>
  have disj_am: "link_fields_disjoint [a, m]"
    using link_fields_disjoint_collapse[OF disj_L, of \<sigma>a] by (simp add: a_eq)

  \<comment> \<open>(3) The capture check on the pair: every name of the pair's
      substitutions is a name of some flat input's substitution, and every
      bound tyvar of the pair is a bound tyvar of some flat input; the flat
      check then applies.\<close>
  have cap_am: "link_capture_ok [a, m]"
    unfolding link_capture_ok_def
  proof (rule fset_eqI)
    fix n
    show "n |\<in>| funion_list (map (\<lambda>x. subst_names (CM_TypeSubst x)) [a, m])
             |\<inter>| funion_list (map module_bound_tyvars [a, m]) \<longleftrightarrow> n |\<in>| {||}"
    proof
      assume n_in: "n |\<in>| funion_list (map (\<lambda>x. subst_names (CM_TypeSubst x)) [a, m])
                       |\<inter>| funion_list (map module_bound_tyvars [a, m])"
      have n_subst: "n |\<in>| subst_names \<sigma>a \<or> n |\<in>| subst_names sm"
        using n_in by (auto simp: funion_list_member subst_a sm_def)
      have n_bound: "n |\<in>| module_bound_tyvars a \<or> n |\<in>| module_bound_tyvars m"
        using n_in by (auto simp: funion_list_member)
      have ex_subst: "\<exists>x \<in> set (as @ [m]). n |\<in>| subst_names (CM_TypeSubst x)"
        using n_subst
      proof (elim disjE)
        assume "n |\<in>| subst_names \<sigma>a"
        then obtain s where "s \<in> set (map CM_TypeSubst as)" "n |\<in>| subst_names s"
          using merge_closure_subst_names[OF sdisj_a acyc_a clos_a] by blast
        then obtain x where "x \<in> set as" "n |\<in>| subst_names (CM_TypeSubst x)" by auto
        then show ?thesis by auto
      next
        assume "n |\<in>| subst_names sm"
        then show ?thesis using sm_def by auto
      qed
      have ex_bound: "\<exists>x \<in> set (as @ [m]). n |\<in>| module_bound_tyvars x"
        using n_bound
      proof (elim disjE)
        assume "n |\<in>| module_bound_tyvars a"
        then have "n |\<in>| module_bound_tyvars (link_result as \<sigma>a)" using a_eq by simp
        then have "\<exists>x \<in> set as. n |\<in>| module_bound_tyvars x"
          using module_bound_tyvars_link_result[OF disj_a] by blast
        then show ?thesis by auto
      next
        assume "n |\<in>| module_bound_tyvars m"
        then show ?thesis by auto
      qed
      have "n |\<in>| funion_list (map (\<lambda>x. subst_names (CM_TypeSubst x)) (as @ [m]))"
        using ex_subst by (auto simp: funion_list_member)
      moreover have "n |\<in>| funion_list (map module_bound_tyvars (as @ [m]))"
        using ex_bound by (auto simp: funion_list_member)
      ultimately have False
        using cap_L unfolding link_capture_ok_def by auto
      then show "n |\<in>| {||}" ..
    qed simp
  qed

  \<comment> \<open>(4) The substitution merge of the pair yields the same \<sigma>.\<close>
  have merge_am: "merge_all_substs (map CM_TypeSubst [a, m]) = Inr \<sigma>"
  proof -
    have l_eq: "map CM_TypeSubst [a, m] = [\<sigma>a, sm]"
      by (simp add: subst_a sm_def)
    have dj_pair: "fmdisjoint_list [\<sigma>a, sm]"
      by (simp add: fmdisjoint_list_pair fmdisjoint_def dom_\<sigma>a djsm)
    have un_pair: "fmlist_union [\<sigma>a, sm] = \<sigma>a ++\<^sub>f sm"
      by (simp add: fmlist_union_Cons)
    have acyc_pair: "acyclic_subst_deps (\<sigma>a ++\<^sub>f sm)"
      using acyclic_closure_union[OF djsm acyc_ua clos_ua acyc_u] .
    have clos_pair: "is_subst_closure (\<sigma>a ++\<^sub>f sm) \<sigma>"
      using is_subst_closure_collapse[OF djsm acyc_ua clos_ua clos_u] .
    show ?thesis
      unfolding l_eq merge_all_substs_Inr_iff un_pair
      using dj_pair acyc_pair clos_pair by blast
  qed

  \<comment> \<open>(5) The runtime-resolution check on the pair: the pair's runtime tyvars
      are among the flat inputs', and the linked envs agree by (1).\<close>
  have rok_am: "link_runtime_ok [a, m] \<sigma>"
    unfolding link_runtime_ok_def
  proof (intro allI impI)
    fix n
    assume n_in: "n |\<in>| fmdom \<sigma>
                    |\<inter>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) [a, m])"
    then have n_dom: "n |\<in>| fmdom \<sigma>" by auto
    have n_rtv: "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv a)
               \<or> n |\<in>| TE_RuntimeTypeVars (CM_TyEnv m)"
      using n_in by (auto simp: funion_list_member)
    have "n |\<in>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) (as @ [m]))"
      using n_rtv
    proof (elim disjE)
      assume "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv a)"
      then have "n |\<in>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) as)"
        by (auto simp: a_eq link_result_def)
      then show ?thesis by (auto simp: funion_list_member)
    next
      assume "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv m)"
      then show ?thesis by (auto simp: funion_list_member)
    qed
    with n_dom have "n |\<in>| fmdom \<sigma>
                       |\<inter>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) (as @ [m]))"
      by simp
    then have "is_runtime_type (CM_TyEnv (link_result (as @ [m]) \<sigma>)) (the (fmlookup \<sigma> n))"
      using rok_L unfolding link_runtime_ok_def by blast
    then show "is_runtime_type (CM_TyEnv (link_result [a, m] \<sigma>)) (the (fmlookup \<sigma> n))"
      using lr_eq by simp
  qed

  show ?thesis
    using disj_am cap_am merge_am rok_am L_am link_modules_Inr_iff[of "[a, m]" L]
    by blast
qed


(* ========================================================================== *)
(* Link transfer plumbing                                                     *)
(* ========================================================================== *)

(* Facts transferring per-input properties through a successful link. The
   elab_module correctness theorem (step 6b) needs these to establish the
   context premises of elab_link_well_typed when the context module is itself
   a link of compiled imports: its substitution must be empty, and its type
   variables and function type parameters must inherit the inputs'
   metavariable-freshness. *)

(* A link of substitution-free modules is substitution-free: the merged
   substitution is the closure of the union of the inputs' substitutions, and
   a closure of the empty substitution has an empty domain. *)
lemma link_modules_empty_subst:
  assumes ok: "link_modules ms = Inr L"
      and each: "\<forall>x \<in> set ms. CM_TypeSubst x = fmempty"
  shows "CM_TypeSubst L = fmempty"
proof -
  obtain \<sigma> where
    clos: "is_subst_closure (fmlist_union (map CM_TypeSubst ms)) \<sigma>" and
    meq: "L = link_result ms \<sigma>"
    using ok link_modules_Inr_iff_closure[of ms L] by blast
  have u_empty: "fmlist_union (map CM_TypeSubst ms) = fmempty"
    using each by (induction ms) (simp_all add: fmlist_union_Cons)
  have "fmdom \<sigma> = {||}"
    using clos unfolding u_empty is_subst_closure_def by simp
  then have "\<sigma> = fmempty"
    by (metis fmrestrict_fset_dom fmrestrict_fset_null)
  then show ?thesis
    using meq by (simp add: link_result_def)
qed

(* Every in-scope type variable of a linked module comes from some input: the
   linked TE_TypeVars is the union of the inputs' minus the resolved names. *)
lemma link_modules_TypeVars_member:
  assumes ok: "link_modules ms = Inr L"
      and n_in: "n |\<in>| TE_TypeVars (CM_TyEnv L)"
  shows "\<exists>x \<in> set ms. n |\<in>| TE_TypeVars (CM_TyEnv x)"
proof -
  obtain \<sigma> where meq: "L = link_result ms \<sigma>"
    using ok link_modules_Inr_iff[of ms L] by blast
  have "n |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms) |-| fmdom \<sigma>"
    using n_in unfolding meq by (simp add: link_result_def)
  then show ?thesis
    by (auto simp: funion_list_member)
qed

(* Under empty input substitutions nothing is subtracted from the tyvar
   fields: each input's type variables all survive into the linked env. *)
lemma link_modules_TypeVars_superset:
  assumes ok: "link_modules ms = Inr L"
      and empty: "\<forall>x \<in> set ms. CM_TypeSubst x = fmempty"
      and x_in: "x \<in> set ms"
  shows "TE_TypeVars (CM_TyEnv x) |\<subseteq>| TE_TypeVars (CM_TyEnv L)"
proof
  fix n assume n_in: "n |\<in>| TE_TypeVars (CM_TyEnv x)"
  obtain \<sigma> where meq: "L = link_result ms \<sigma>"
    using ok link_modules_Inr_iff[of ms L] by blast
  have "CM_TypeSubst L = fmempty"
    using link_modules_empty_subst[OF ok empty] .
  then have \<sigma>_empty: "\<sigma> = fmempty"
    using meq by (simp add: link_result_def)
  have "n |\<in>| funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms)"
    using x_in n_in by (auto simp: funion_list_member)
  then show "n |\<in>| TE_TypeVars (CM_TyEnv L)"
    unfolding meq link_result_def by (simp add: \<sigma>_empty)
qed

(* Hence, for substitution-free inputs, the type variables of a sub-link
   embed in the whole link's. (False in general: the whole link may RESOLVE
   a type variable the sub-link leaves abstract.) *)
lemma link_modules_TypeVars_mono:
  assumes okA: "link_modules as = Inr a"
      and okM: "link_modules ms = Inr m"
      and empty: "\<forall>x \<in> set ms. CM_TypeSubst x = fmempty"
      and sub: "set as \<subseteq> set ms"
  shows "TE_TypeVars (CM_TyEnv a) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
proof
  fix n assume "n |\<in>| TE_TypeVars (CM_TyEnv a)"
  then obtain x where x_in: "x \<in> set as" and n_x: "n |\<in>| TE_TypeVars (CM_TyEnv x)"
    using link_modules_TypeVars_member[OF okA] by blast
  have "x \<in> set ms" using x_in sub by blast
  then show "n |\<in>| TE_TypeVars (CM_TyEnv m)"
    using link_modules_TypeVars_superset[OF okM empty] n_x by (blast dest: fsubsetD)
qed

(* For substitution-free inputs, every sub-multiset of a linkable list itself
   links: field disjointness restricts to sub-multisets, and the remaining
   checks (capture, substitution merge, runtime resolution) are trivial when
   every input's substitution is empty. This is how the derived sub-links of
   the pipeline (the dep-only contexts, the linked interface) are known to
   succeed from the one link elab_module actually computes. *)
lemma link_modules_empty_substs_sublink:
  assumes ok: "link_modules ms = Inr m"
      and empty: "\<forall>x \<in> set ms. CM_TypeSubst x = fmempty"
      and sub: "mset as \<subseteq># mset ms"
  shows "\<exists>a. link_modules as = Inr a"
proof -
  have set_sub: "set as \<subseteq> set ms"
    using sub by (metis set_mset_mono set_mset_mset)
  have empty_as: "\<forall>x \<in> set as. CM_TypeSubst x = fmempty"
    using empty set_sub by blast
  \<comment> \<open>Field disjointness restricts to the sub-multiset, family by family.\<close>
  have msub: "mset (map f as) \<subseteq># mset (map f ms)" for f :: "CoreModule \<Rightarrow> 'b"
    using sub by (metis image_mset_subseteq_mono mset_map)
  have disj_ms: "link_fields_disjoint ms"
    using ok link_modules_Inr_iff[of ms m] by blast
  have disj_as: "link_fields_disjoint as"
    using disj_ms
    unfolding link_fields_disjoint_def
    by (metis fmdisjoint_list_submset msub)
  \<comment> \<open>The capture check: substitution-free inputs touch no names at all.\<close>
  have names_empty: "funion_list (map (\<lambda>x. subst_names (CM_TypeSubst x)) as) = {||}"
    using empty_as by (induction as) auto
  have cap: "link_capture_ok as"
    unfolding link_capture_ok_def by (simp add: names_empty)
  \<comment> \<open>The substitution merge: the union of empty substitutions is empty, whose
     dependency relation is empty and whose closure is itself.\<close>
  have u_empty: "fmlist_union (map CM_TypeSubst as) = fmempty"
    using empty_as by (induction as) (simp_all add: fmlist_union_Cons)
  have sdisj: "fmdisjoint_list (map CM_TypeSubst as)"
    using empty_as by (induction as) (auto simp: fmdisjoint_list_Cons)
  have acyc: "acyclic_subst_deps fmempty"
    unfolding acyclic_subst_deps_def subst_dep_rel_def acyclic_def by simp
  have clos: "is_subst_closure fmempty fmempty"
    unfolding is_subst_closure_def by simp
  have merge: "merge_all_substs (map CM_TypeSubst as) = Inr fmempty"
    unfolding merge_all_substs_Inr_iff u_empty
    using sdisj acyc clos by blast
  \<comment> \<open>The runtime-resolution check is vacuous for an empty substitution.\<close>
  have rok: "link_runtime_ok as fmempty"
    unfolding link_runtime_ok_def by simp
  show ?thesis
    using disj_as cap merge rok link_modules_Inr_iff[of as] by blast
qed

(* Every function signature of a linked module is some input's signature,
   verbatim (linking applies no substitution). *)
lemma link_modules_Functions_lookup:
  assumes ok: "link_modules ms = Inr L"
      and lk: "fmlookup (TE_Functions (CM_TyEnv L)) name = Some info"
  shows "\<exists>x \<in> set ms. fmlookup (TE_Functions (CM_TyEnv x)) name = Some info"
proof -
  obtain \<sigma> where disj: "link_fields_disjoint ms" and meq: "L = link_result ms \<sigma>"
    using ok link_modules_Inr_iff[of ms L] by blast
  have djF: "fmdisjoint_list (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)"
    using disj unfolding link_fields_disjoint_def by blast
  have "fmlookup (fmlist_union (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)) name
          = Some info"
    using lk unfolding meq by (simp add: link_result_def)
  then show ?thesis
    using fmlist_union_lookup[OF djF] by auto
qed

end

theory ElabPatternCorrect
  imports ElabPattern
    "../core/CoreTypecheck" ExtendEnvWithTyvars
begin

(* Correctness proofs for ElabPattern.thy. *)


section \<open>Properties of extend_env_one_var, extend_env_with_pattern_vars\<close>

(* extend_env_one_var only modifies TE_LocalVars / TE_ConstLocals / TE_GhostLocals,
   so it leaves TE_TypeVars / TE_RuntimeTypeVars / TE_Datatypes / etc. alone. *)
lemma extend_env_one_var_TE_TypeVars [simp]:
  "TE_TypeVars (extend_env_one_var constOf ghost b env) = TE_TypeVars env"
  by (cases b) (simp add: extend_env_one_var_def)

lemma extend_env_one_var_TE_RuntimeTypeVars [simp]:
  "TE_RuntimeTypeVars (extend_env_one_var constOf ghost b env) = TE_RuntimeTypeVars env"
  by (cases b) (simp add: extend_env_one_var_def)

lemma foldr_extend_env_one_var_TE_TypeVars [simp]:
  "TE_TypeVars (foldr (extend_env_one_var constOf ghost) bs env) = TE_TypeVars env"
  by (induction bs) simp_all

lemma foldr_extend_env_one_var_TE_RuntimeTypeVars [simp]:
  "TE_RuntimeTypeVars (foldr (extend_env_one_var constOf ghost) bs env) = TE_RuntimeTypeVars env"
  by (induction bs) simp_all

lemma extend_env_with_pattern_vars_TE_TypeVars [simp]:
  "TE_TypeVars (extend_env_with_pattern_vars env constOf ghost ps) = TE_TypeVars env"
  unfolding extend_env_with_pattern_vars_def by simp

lemma extend_env_with_pattern_vars_TE_RuntimeTypeVars [simp]:
  "TE_RuntimeTypeVars (extend_env_with_pattern_vars env constOf ghost ps) = TE_RuntimeTypeVars env"
  unfolding extend_env_with_pattern_vars_def by simp

lemma extend_env_one_var_TE_Datatypes [simp]:
  "TE_Datatypes (extend_env_one_var constOf ghost b env) = TE_Datatypes env"
  by (cases b) (simp add: extend_env_one_var_def)

lemma extend_env_one_var_TE_GhostDatatypes [simp]:
  "TE_GhostDatatypes (extend_env_one_var constOf ghost b env) = TE_GhostDatatypes env"
  by (cases b) (simp add: extend_env_one_var_def)

lemma foldr_extend_env_one_var_TE_Datatypes [simp]:
  "TE_Datatypes (foldr (extend_env_one_var constOf ghost) bs env) = TE_Datatypes env"
  by (induction bs) simp_all

lemma foldr_extend_env_one_var_TE_GhostDatatypes [simp]:
  "TE_GhostDatatypes (foldr (extend_env_one_var constOf ghost) bs env) = TE_GhostDatatypes env"
  by (induction bs) simp_all

lemma extend_env_with_pattern_vars_TE_Datatypes [simp]:
  "TE_Datatypes (extend_env_with_pattern_vars env constOf ghost ps) = TE_Datatypes env"
  unfolding extend_env_with_pattern_vars_def by simp

lemma extend_env_with_pattern_vars_TE_GhostDatatypes [simp]:
  "TE_GhostDatatypes (extend_env_with_pattern_vars env constOf ghost ps) = TE_GhostDatatypes env"
  unfolding extend_env_with_pattern_vars_def by simp

(* extend_env_one_var preserves TE_DataCtors. *)
lemma extend_env_one_var_TE_DataCtors [simp]:
  "TE_DataCtors (extend_env_one_var constOf ghost b env) = TE_DataCtors env"
  by (cases b) (simp add: extend_env_one_var_def)

lemma foldr_extend_env_one_var_TE_DataCtors [simp]:
  "TE_DataCtors (foldr (extend_env_one_var constOf ghost) bs env) = TE_DataCtors env"
  by (induction bs) simp_all

lemma extend_env_with_pattern_vars_TE_DataCtors [simp]:
  "TE_DataCtors (extend_env_with_pattern_vars env constOf ghost ps) = TE_DataCtors env"
  unfolding extend_env_with_pattern_vars_def by simp

(* extend_env_one_var preserves TE_ReturnType. *)
lemma extend_env_one_var_TE_ReturnType [simp]:
  "TE_ReturnType (extend_env_one_var constOf ghost b env) = TE_ReturnType env"
  by (cases b) (simp add: extend_env_one_var_def)

lemma foldr_extend_env_one_var_TE_ReturnType [simp]:
  "TE_ReturnType (foldr (extend_env_one_var constOf ghost) bs env) = TE_ReturnType env"
  by (induction bs) simp_all

lemma extend_env_with_pattern_vars_TE_ReturnType [simp]:
  "TE_ReturnType (extend_env_with_pattern_vars env constOf ghost ps) = TE_ReturnType env"
  unfolding extend_env_with_pattern_vars_def by simp

(* extend_env_one_var preserves TE_Functions. *)
lemma extend_env_one_var_TE_Functions [simp]:
  "TE_Functions (extend_env_one_var constOf ghost b env) = TE_Functions env"
  by (cases b) (simp add: extend_env_one_var_def)

lemma foldr_extend_env_one_var_TE_Functions [simp]:
  "TE_Functions (foldr (extend_env_one_var constOf ghost) bs env) = TE_Functions env"
  by (induction bs) simp_all

lemma extend_env_with_pattern_vars_TE_Functions [simp]:
  "TE_Functions (extend_env_with_pattern_vars env constOf ghost ps) = TE_Functions env"
  unfolding extend_env_with_pattern_vars_def by simp

(* extend_env_one_var commutes (in observable env state) when the two
   bindings use distinct names. Quantified over the VarOrRef components
   vr1, vr2 so the lemma survives any future use of that field. *)
lemma extend_env_one_var_commute:
  assumes "x \<noteq> y"
  shows "extend_env_one_var constOf ghost (vr1, x, t1) (extend_env_one_var constOf ghost (vr2, y, t2) env)
       = extend_env_one_var constOf ghost (vr2, y, t2) (extend_env_one_var constOf ghost (vr1, x, t1) env)"
proof -
  have fmupd_commute: "fmupd y t2 (fmupd x t1 (TE_LocalVars env))
                       = fmupd x t1 (fmupd y t2 (TE_LocalVars env))"
    using assms by (simp add: fmupd_reorder_neq)
  \<comment> \<open>The ConstLocals updates commute in all four constOf combinations
      (finsert/finsert, finsert/fminus, fminus/finsert, fminus/fminus),
      since x and y are distinct. Stated componentwise, because simp splits
      the ifs in the goal before a combined if-equation could apply.\<close>
  have const_ins_ins:
    "finsert x (finsert y (TE_ConstLocals env)) = finsert y (finsert x (TE_ConstLocals env))"
    by (rule finsert_commute)
  have const_ins_del:
    "finsert x (TE_ConstLocals env |-| {|y|}) = finsert x (TE_ConstLocals env) |-| {|y|}"
    using assms by (auto simp: fset_eq_iff)
  have const_del_ins:
    "finsert y (TE_ConstLocals env) |-| {|x|} = finsert y (TE_ConstLocals env |-| {|x|})"
    using assms by (auto simp: fset_eq_iff)
  have const_del_del:
    "TE_ConstLocals env |-| {|y|} |-| {|x|} = TE_ConstLocals env |-| {|x|} |-| {|y|}"
    by (auto simp: fset_eq_iff)
  have ghost_ins:
    "finsert y (finsert x (TE_GhostLocals env)) = finsert x (finsert y (TE_GhostLocals env))"
    by (rule finsert_commute)
  have ghost_del:
    "TE_GhostLocals env |-| {|x|} |-| {|y|} = TE_GhostLocals env |-| {|y|} |-| {|x|}"
    by blast
  show ?thesis
    by (cases "ghost = Ghost")
       (simp_all add: extend_env_one_var_def fmupd_commute const_ins_ins const_ins_del
                      const_del_ins const_del_del ghost_ins ghost_del)
qed

(* extend_env_with_tyvars and extend_env_one_var commute (operate on disjoint
   record fields: extend_env_with_tyvars only touches TE_TypeVars/TE_RuntimeTypeVars;
   extend_env_one_var only touches TE_LocalVars/TE_ConstLocals/TE_GhostLocals). *)
lemma extend_env_with_tyvars_extend_env_one_var_commute:
  "extend_env_with_tyvars (extend_env_one_var constOf ghost b env) ghost lo hi
   = extend_env_one_var constOf ghost b (extend_env_with_tyvars env ghost lo hi)"
  unfolding extend_env_with_tyvars_def extend_env_one_var_def
  by (cases b) (simp split: GhostOrNot.splits)

lemma extend_env_with_tyvars_foldr_extend_env_one_var_commute:
  "extend_env_with_tyvars (foldr (extend_env_one_var constOf ghost) bs env) ghost lo hi
   = foldr (extend_env_one_var constOf ghost) bs (extend_env_with_tyvars env ghost lo hi)"
  by (induction bs)
     (simp_all add: extend_env_with_tyvars_extend_env_one_var_commute)

lemma extend_env_with_tyvars_extend_env_with_pattern_vars_commute:
  "extend_env_with_tyvars (extend_env_with_pattern_vars env constOf ghost ps) ghost lo hi
   = extend_env_with_pattern_vars (extend_env_with_tyvars env ghost lo hi) constOf ghost ps"
  unfolding extend_env_with_pattern_vars_def
  by (rule extend_env_with_tyvars_foldr_extend_env_one_var_commute)

(* Two foldr-extend orderings agree when all binding names are distinct
   across the two lists. *)
lemma foldr_extend_env_one_var_append_swap:
  assumes "distinct (map (\<lambda>(_, x, _). x) (xs @ ys))"
  shows "foldr (extend_env_one_var constOf ghost) (xs @ ys) env
       = foldr (extend_env_one_var constOf ghost) ys
                (foldr (extend_env_one_var constOf ghost) xs env)"
  using assms
proof (induction xs arbitrary: env)
  case Nil
  show ?case by simp
next
  case (Cons b xs)
  obtain vr x ty where b_eq: "b = (vr, x, ty)" by (cases b) auto
  have x_fresh:
    "x \<notin> set (map (\<lambda>(_, x, _). x) xs)"
    "x \<notin> set (map (\<lambda>(_, x, _). x) ys)"
    using Cons.prems b_eq by auto
  have distinct_rest:
    "distinct (map (\<lambda>(_, x, _). x) (xs @ ys))"
    using Cons.prems b_eq by auto
  have IH:
    "foldr (extend_env_one_var constOf ghost) (xs @ ys) env
     = foldr (extend_env_one_var constOf ghost) ys
              (foldr (extend_env_one_var constOf ghost) xs env)"
    using Cons.IH[OF distinct_rest] .
  let ?env_xs = "foldr (extend_env_one_var constOf ghost) xs env"
  let ?env_xs_ys = "foldr (extend_env_one_var constOf ghost) ys ?env_xs"
  \<comment> \<open>Goal: extend_env_one_var constOf ghost (vr, x, ty) ?env_xs_ys
              = foldr (extend_env_one_var constOf ghost) ys
                       (extend_env_one_var constOf ghost (vr, x, ty) ?env_xs)
      That follows from commuting `extend_env_one_var constOf ghost (vr, x, ty)` with
      each entry of ys (all of which have names \<noteq> x). \<close>
  have commute_through_ys:
    "\<And>e. extend_env_one_var constOf ghost (vr, x, ty)
            (foldr (extend_env_one_var constOf ghost) ys e)
        = foldr (extend_env_one_var constOf ghost) ys
                 (extend_env_one_var constOf ghost (vr, x, ty) e)"
  proof -
    fix e
    show "extend_env_one_var constOf ghost (vr, x, ty)
            (foldr (extend_env_one_var constOf ghost) ys e)
        = foldr (extend_env_one_var constOf ghost) ys
                 (extend_env_one_var constOf ghost (vr, x, ty) e)"
      using x_fresh(2) proof (induction ys arbitrary: e)
      case Nil thus ?case by simp
    next
      case (Cons c ys' e)
      obtain vr' y t' where c_eq: "c = (vr', y, t')" by (cases c) auto
      have x_neq_y: "x \<noteq> y" using Cons.prems c_eq by simp
      have x_fresh_ys':
        "x \<notin> set (map (\<lambda>(_, x, _). x) ys')"
        using Cons.prems c_eq by simp
      let ?e1 = "foldr (extend_env_one_var constOf ghost) ys' e"
      have step1:
        "extend_env_one_var constOf ghost (vr, x, ty) ?e1
         = foldr (extend_env_one_var constOf ghost) ys'
                 (extend_env_one_var constOf ghost (vr, x, ty) e)"
        using Cons.IH[OF x_fresh_ys'] .
      have commute_step:
        "extend_env_one_var constOf ghost (vr, x, ty)
            (extend_env_one_var constOf ghost (vr', y, t') ?e1)
         = extend_env_one_var constOf ghost (vr', y, t')
            (extend_env_one_var constOf ghost (vr, x, ty) ?e1)"
        using extend_env_one_var_commute[OF \<open>x \<noteq> y\<close>] by simp
      show ?case
        unfolding c_eq
        using step1 commute_step
        by simp
    qed
  qed
  show ?case
    using b_eq IH commute_through_ys[of ?env_xs]
    by simp
qed

(* Pushing extend_env_one_var for a fresh name through a foldr of
   extend_env_one_var: when x doesn't appear in bs's names, the
   single binding can be commuted to the outside. *)
lemma foldr_extend_env_one_var_push:
  assumes "x \<notin> set (map (\<lambda>(_, x, _). x) bs)"
  shows "foldr (extend_env_one_var constOf ghost) bs
                (extend_env_one_var constOf ghost (vr, x, ty) env)
       = extend_env_one_var constOf ghost (vr, x, ty)
            (foldr (extend_env_one_var constOf ghost) bs env)"
  using assms
proof (induction bs arbitrary: env)
  case Nil thus ?case by simp
next
  case (Cons b bs)
  obtain vr' x' ty' where b_eq: "b = (vr', x', ty')" by (cases b) auto
  have x_neq_x': "x \<noteq> x'" using Cons.prems b_eq by simp
  have x_fresh_bs: "x \<notin> set (map (\<lambda>(_, x, _). x) bs)"
    using Cons.prems b_eq by simp
  let ?e1 = "foldr (extend_env_one_var constOf ghost) bs env"
  have IH:
    "foldr (extend_env_one_var constOf ghost) bs
            (extend_env_one_var constOf ghost (vr, x, ty) env)
     = extend_env_one_var constOf ghost (vr, x, ty) ?e1"
    using Cons.IH[OF x_fresh_bs] .
  have commute_step:
    "extend_env_one_var constOf ghost (vr', x', ty')
        (extend_env_one_var constOf ghost (vr, x, ty) ?e1)
     = extend_env_one_var constOf ghost (vr, x, ty)
        (extend_env_one_var constOf ghost (vr', x', ty') ?e1)"
    using extend_env_one_var_commute[OF x_neq_x'[symmetric]] by simp
  show ?case
    unfolding b_eq
    using IH commute_step by simp
qed

(* If a term doesn't reference variable x, its type is unchanged when
   env is extended by a new binding for x. Quantified over the VarOrRef
   component vr. *)
lemma core_term_type_extend_env_one_var_irrelevant:
  assumes "x |\<notin>| core_term_free_vars tm"
      and "core_term_type env ghost tm = Some ty"
  shows "core_term_type (extend_env_one_var constOf ghost (vr, x, bindTy) env) ghost tm = Some ty"
proof -
  let ?env_modified = "env \<lparr> TE_LocalVars := fmupd x bindTy (TE_LocalVars env),
                              TE_GhostLocals := (if ghost = Ghost
                                                 then finsert x (TE_GhostLocals env)
                                                 else fminus (TE_GhostLocals env) {|x|}) \<rparr>"
  have ghost_eq: "\<forall>y. y \<noteq> x \<longrightarrow>
                    (y |\<in>| (if ghost = Ghost
                            then finsert x (TE_GhostLocals env)
                            else fminus (TE_GhostLocals env) {|x|})
                     \<longleftrightarrow> y |\<in>| TE_GhostLocals env)"
    by auto
  have step1: "core_term_type ?env_modified ghost tm = Some ty"
    using core_term_type_irrelevant_var[OF assms(1) assms(2) ghost_eq] .
  have step2: "extend_env_one_var constOf ghost (vr, x, bindTy) env
               = ?env_modified \<lparr> TE_ConstLocals := (if constOf vr
                                                    then finsert x (TE_ConstLocals env)
                                                    else fminus (TE_ConstLocals env) {|x|}) \<rparr>"
    by (simp add: extend_env_one_var_def)
  show ?thesis
    using step1 step2 core_term_type_TE_ConstLocals_irrelevant by simp
qed

(* extend_env_with_pattern_vars commutes with extend_env_one_var when the
   bind's name doesn't appear in the pattern-list's DP_Var names. *)
lemma extend_env_with_pattern_vars_extend_env_one_var_swap:
  assumes "x |\<notin>| dec_pattern_var_names_list ps"
  shows "extend_env_with_pattern_vars (extend_env_one_var constOf ghost (vr, x, ty) env) constOf ghost ps
       = extend_env_one_var constOf ghost (vr, x, ty) (extend_env_with_pattern_vars env constOf ghost ps)"
proof -
  let ?bs = "dec_pattern_var_bindings_list ps"
  have names_match:
    "fset_of_list (map (\<lambda>(_, x, _). x) ?bs) = dec_pattern_var_names_list ps"
  proof -
    have helper:
      "fset_of_list (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings p))
       = dec_pattern_var_names p"
      "fset_of_list (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list qs))
       = dec_pattern_var_names_list qs"
      for p qs
      by (induction p and qs
          rule: dec_pattern_var_bindings_dec_pattern_var_bindings_list.induct)
         auto
    show ?thesis using helper(2) .
  qed
  have x_not_in_bs: "x \<notin> set (map (\<lambda>(_, x, _). x) ?bs)"
    using assms names_match by (metis fset_of_list.rep_eq)
  show ?thesis
    unfolding extend_env_with_pattern_vars_def
    using foldr_extend_env_one_var_push[OF x_not_in_bs] .
qed

(* is_well_kinded only depends on TE_TypeVars and TE_Datatypes (is_well_kinded_cong_env);
   extend_env_with_pattern_vars doesn't touch either. *)
lemma is_well_kinded_extend_env_with_pattern_vars [simp]:
  "is_well_kinded (extend_env_with_pattern_vars env constOf ghost ps) ty = is_well_kinded env ty"
  using is_well_kinded_cong_env[of "extend_env_with_pattern_vars env constOf ghost ps" env ty] by simp

(* is_runtime_type only depends on TE_RuntimeTypeVars and TE_GhostDatatypes;
   extend_env_with_pattern_vars doesn't touch either. *)
lemma is_runtime_type_extend_env_with_pattern_vars [simp]:
  "is_runtime_type (extend_env_with_pattern_vars env constOf ghost ps) ty = is_runtime_type env ty"
  using is_runtime_type_cong_env[of "extend_env_with_pattern_vars env constOf ghost ps" env ty] by simp

(* tyenv_well_formed is preserved by extend_env_one_var, given the binding's
   type is well-kinded (and runtime if the extension is non-ghost). *)
lemma tyenv_well_formed_extend_env_one_var:
  assumes wf: "tyenv_well_formed env"
      and ty_wk: "is_well_kinded env (snd (snd b))"
      and ty_rt: "ghost = NotGhost \<Longrightarrow> is_runtime_type env (snd (snd b))"
  shows "tyenv_well_formed (extend_env_one_var constOf ghost b env)"
proof -
  obtain vr name ty where b_eq: "b = (vr, name, ty)" by (cases b) auto
  show ?thesis
  proof (cases ghost)
    case Ghost
    \<comment> \<open>Ghost mode: extend_env_one_var sets TE_GhostLocals := finsert name (...).
        Use tyenv_well_formed_add_ghost_var (modulo TE_ConstLocals irrelevance). \<close>
    let ?env_no_const = "env \<lparr> TE_LocalVars := fmupd name ty (TE_LocalVars env),
                                TE_GhostLocals := finsert name (TE_GhostLocals env) \<rparr>"
    have step1: "tyenv_well_formed ?env_no_const"
      using tyenv_well_formed_add_ghost_var[OF wf] ty_wk b_eq by simp
    have full_eq:
      "extend_env_one_var constOf ghost b env
       = ?env_no_const \<lparr> TE_ConstLocals := (if constOf vr
                                            then finsert name (TE_ConstLocals env)
                                            else fminus (TE_ConstLocals env) {|name|}) \<rparr>"
      using b_eq Ghost by (simp add: extend_env_one_var_def)
    show ?thesis
      using step1 tyenv_well_formed_TE_ConstLocals_irrelevant full_eq by simp
  next
    case NotGhost
    let ?env_no_const = "env \<lparr> TE_LocalVars := fmupd name ty (TE_LocalVars env),
                                TE_GhostLocals := fminus (TE_GhostLocals env) {|name|} \<rparr>"
    have step1: "tyenv_well_formed ?env_no_const"
      using tyenv_well_formed_add_var[OF wf] ty_wk ty_rt[OF NotGhost] b_eq by simp
    have full_eq:
      "extend_env_one_var constOf ghost b env
       = ?env_no_const \<lparr> TE_ConstLocals := (if constOf vr
                                            then finsert name (TE_ConstLocals env)
                                            else fminus (TE_ConstLocals env) {|name|}) \<rparr>"
      using b_eq NotGhost by (simp add: extend_env_one_var_def)
    show ?thesis
      using step1 tyenv_well_formed_TE_ConstLocals_irrelevant full_eq by simp
  qed
qed

lemma tyenv_well_formed_foldr_extend_env_one_var:
  assumes wf: "tyenv_well_formed env"
      and bs_wk: "list_all (\<lambda>b. is_well_kinded env (snd (snd b))) bs"
      and bs_rt: "ghost = NotGhost \<Longrightarrow> list_all (\<lambda>b. is_runtime_type env (snd (snd b))) bs"
  shows "tyenv_well_formed (foldr (extend_env_one_var constOf ghost) bs env)"
using bs_wk bs_rt proof (induction bs)
  case Nil
  show ?case using wf by simp
next
  case (Cons b rest)
  let ?env_rest = "foldr (extend_env_one_var constOf ghost) rest env"
  from Cons have wf_rest: "tyenv_well_formed ?env_rest" by simp
  \<comment> \<open>The binding type is well-kinded under env, hence under ?env_rest by
      cong (since foldr extend_env_one_var preserves TE_TypeVars and TE_Datatypes). \<close>
  have tv_eq: "TE_TypeVars ?env_rest = TE_TypeVars env" by simp
  have dt_eq: "TE_Datatypes ?env_rest = TE_Datatypes env"
    by (induction rest) simp_all
  have rtv_eq: "TE_RuntimeTypeVars ?env_rest = TE_RuntimeTypeVars env" by simp
  have gd_eq: "TE_GhostDatatypes ?env_rest = TE_GhostDatatypes env"
    by (induction rest) simp_all
  from Cons.prems(1) have b_wk: "is_well_kinded env (snd (snd b))" by simp
  have wk_lift: "is_well_kinded ?env_rest (snd (snd b))"
    using is_well_kinded_cong_env[OF tv_eq dt_eq] b_wk by simp
  have rt_lift: "ghost = NotGhost \<Longrightarrow> is_runtime_type ?env_rest (snd (snd b))"
  proof -
    assume ng: "ghost = NotGhost"
    from Cons.prems(2)[OF ng] have b_rt: "is_runtime_type env (snd (snd b))" by simp
    show "is_runtime_type ?env_rest (snd (snd b))"
      using is_runtime_type_cong_env[OF gd_eq rtv_eq] b_rt by simp
  qed
  show ?case
    using tyenv_well_formed_extend_env_one_var[OF wf_rest wk_lift rt_lift] by simp
qed

lemma tyenv_well_formed_extend_env_with_pattern_vars:
  assumes "tyenv_well_formed env"
      and "list_all (\<lambda>(_, _, ty). is_well_kinded env ty) (dec_pattern_var_bindings_list ps)"
      and "ghost = NotGhost \<Longrightarrow>
             list_all (\<lambda>(_, _, ty). is_runtime_type env ty) (dec_pattern_var_bindings_list ps)"
  shows "tyenv_well_formed (extend_env_with_pattern_vars env constOf ghost ps)"
  unfolding extend_env_with_pattern_vars_def
  using assms tyenv_well_formed_foldr_extend_env_one_var
  by (auto simp: list_all_iff case_prod_unfold)

(* elabenv_well_formed only depends on env's TE_TypeVars/TE_Datatypes (via
   is_well_kinded inside typedefs_well_formed) and TE_DataCtors. All three are
   invariant under extend_env_with_pattern_vars. *)
lemma elabenv_well_formed_extend_env_with_pattern_vars:
  assumes "elabenv_well_formed env elabEnv"
  shows "elabenv_well_formed (extend_env_with_pattern_vars env constOf ghost ps) elabEnv"
proof -
  let ?env' = "extend_env_with_pattern_vars env constOf ghost ps"
  have tv_eq: "TE_TypeVars ?env' = TE_TypeVars env" by simp
  have dt_eq: "TE_Datatypes ?env' = TE_Datatypes env"
    unfolding extend_env_with_pattern_vars_def by simp
  have dc_eq: "TE_DataCtors ?env' = TE_DataCtors env" by simp
  have rt_eq: "TE_ReturnType ?env' = TE_ReturnType env" by simp
  have fn_eq: "TE_Functions ?env' = TE_Functions env" by simp
  show ?thesis
    using assms elabenv_well_formed_cong_env[OF tv_eq dt_eq dc_eq rt_eq fn_eq] by simp
qed


section \<open>Monotonicity of next_mv\<close>

(* decorate_pattern and decorate_pattern_list only ever advance the next_mv counter. *)
lemma decorate_pattern_next_mv_monotone:
  "decorate_pattern env elabEnv ghost pat scrutTy accSubst next_mv = Inr (dp, accSubst', next_mv')
   \<Longrightarrow> next_mv \<le> next_mv'"
and decorate_pattern_list_next_mv_monotone:
  "decorate_pattern_list env elabEnv ghost pats tys accSubst next_mv = Inr (dps, accSubst', next_mv')
   \<Longrightarrow> next_mv \<le> next_mv'"
proof (induction env elabEnv ghost pat scrutTy accSubst next_mv
       and env elabEnv ghost pats tys accSubst next_mv
       arbitrary: dp accSubst' next_mv'
       and dps accSubst' next_mv'
       rule: decorate_pattern_decorate_pattern_list.induct)
  case (1 env elabEnv ghost loc vr name scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Var: next_mv unchanged\<close>
  from "1.prems" show ?case by simp
next
  case (2 env elabEnv ghost loc scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Wildcard: next_mv unchanged\<close>
  from "2.prems" show ?case by simp
next
  case (3 env elabEnv ghost loc b scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Bool: next_mv unchanged\<close>
  from "3.prems" show ?case by (auto split: option.splits)
next
  case (4 env elabEnv ghost loc i scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Int: next_mv unchanged\<close>
  from "4.prems" show ?case
    by (auto simp: Let_def split: CoreType.splits option.splits if_splits)
next
  case (5 env elabEnv ghost loc pats scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Tuple: bumps next_mv by length pats, then recurses on the list\<close>
  from "5.prems" "5.IH" show ?case
    by (auto simp: Let_def split: option.splits sum.splits, fastforce)
next
  case (6 env elabEnv ghost loc userFlds scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Record: forwards decorate_pattern_list's next_mv\<close>
  from "6.prems" "6.IH" show ?case
    by (auto simp: Let_def split: option.splits CoreType.splits list.splits sum.splits)
next
  case (7 env elabEnv ghost loc ctorName optPayload scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Variant: bumps next_mv by length tyvars, then recurses on the inner pattern (if any)\<close>
  from "7.prems" "7.IH" show ?case
    by (auto simp: Let_def
             split: sum.splits option.splits prod.splits,
        fastforce+)
next
  case (8 env elabEnv ghost tys accSubst next_mv)
  \<comment> \<open>decorate_pattern_list: empty list\<close>
  from "8.prems" show ?case by simp
next
  case (9 env elabEnv ghost p ps tys accSubst next_mv)
  \<comment> \<open>decorate_pattern_list: cons\<close>
  from "9.prems" "9.IH" show ?case
    by (auto simp: Let_def split: sum.splits prod.splits, fastforce)
qed

(* decorate_match_arms only advances next_mv. *)
lemma decorate_match_arms_next_mv_monotone:
  "decorate_match_arms env elabEnv ghost scrutTy allowRefs accSubst next_mv arms
     = Inr (decoratedArms, accSubst', next_mv')
   \<Longrightarrow> next_mv \<le> next_mv'"
proof (induction arms arbitrary: accSubst next_mv decoratedArms accSubst' next_mv')
  case Nil
  thus ?case by simp
next
  case (Cons hd rest)
  obtain pat body where hd_eq: "hd = (pat, body)" by (cases hd) auto
  from Cons.prems hd_eq obtain dp accSubst1 next_mv1 where
    dec: "decorate_pattern env elabEnv ghost pat scrutTy accSubst next_mv
          = Inr (dp, accSubst1, next_mv1)"
    by (auto split: sum.splits)
  from Cons.prems hd_eq dec obtain check_res where
    chk_eq: "check_match_pattern allowRefs (bab_pattern_location pat) dp = Inr check_res"
    by (auto split: sum.splits)
  from Cons.prems hd_eq dec chk_eq obtain restRows where
    rec: "decorate_match_arms env elabEnv ghost scrutTy allowRefs accSubst1 next_mv1 rest
          = Inr (restRows, accSubst', next_mv')"
    by (auto simp: Let_def split: sum.splits)
  have m1: "next_mv \<le> next_mv1"
    using decorate_pattern_next_mv_monotone[OF dec] .
  have m2: "next_mv1 \<le> next_mv'"
    using Cons.IH[OF rec] .
  from m1 m2 show ?case by simp
qed


section \<open>DecPattern type compatibility\<close>

(* Definition: Compatibility of a DecPattern with a CoreType under env. Mirrors
   Core's pattern_compatible but at the decorated-pattern level. *)
fun dec_pattern_compatible :: "CoreTyEnv \<Rightarrow> DecPattern \<Rightarrow> CoreType \<Rightarrow> bool"
and dec_pattern_compatible_list :: "CoreTyEnv \<Rightarrow> DecPattern list \<Rightarrow> CoreType list \<Rightarrow> bool"
where
  "dec_pattern_compatible env (DP_Var _ _ vTy) ty = (vTy = ty)"
| "dec_pattern_compatible env DP_Wildcard _ = True"
| "dec_pattern_compatible env (DP_Bool _) ty = (ty = CoreTy_Bool)"
| "dec_pattern_compatible env (DP_Int i) ty =
    (case ty of
       CoreTy_FiniteInt sign bits \<Rightarrow> int_in_range (int_range sign bits) i
     | _ \<Rightarrow> False)"
| "dec_pattern_compatible env (DP_Variant ctorName payload_opt) ty =
    (case fmlookup (TE_DataCtors env) ctorName of
       None \<Rightarrow> False
     | Some (dtName, tyvars, payloadTy) \<Rightarrow>
         (case ty of
            CoreTy_Datatype tyName tyArgs \<Rightarrow>
              tyName = dtName
              \<and> length tyArgs = length tyvars
              \<and> (case payload_opt of
                   None \<Rightarrow> True
                 | Some inner \<Rightarrow>
                     dec_pattern_compatible env inner
                       (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy))
          | _ \<Rightarrow> False))"
| "dec_pattern_compatible env (DP_Record flds) ty =
    (case ty of
       CoreTy_Record fieldTypes \<Rightarrow>
         map fst flds = map fst fieldTypes
         \<and> dec_pattern_compatible_list env (map snd flds) (map snd fieldTypes)
     | _ \<Rightarrow> False)"
| "dec_pattern_compatible_list env [] [] = True"
| "dec_pattern_compatible_list env (p # ps) (t # ts) =
     (dec_pattern_compatible env p t \<and> dec_pattern_compatible_list env ps ts)"
| "dec_pattern_compatible_list env _ _ = False"

(* dec_pattern_compatible_list is structural in lockstep on the two lists.
   It can be re-expressed as a lockstep nth-condition. *)
lemma dec_pattern_compatible_list_iff:
  "dec_pattern_compatible_list env ps ts
   \<longleftrightarrow> length ps = length ts
       \<and> (\<forall>i < length ps. dec_pattern_compatible env (ps ! i) (ts ! i))"
proof (induction ps arbitrary: ts)
  case Nil
  thus ?case by (cases ts) auto
next
  case (Cons p ps)
  show ?case
  proof (cases ts)
    case Nil
    thus ?thesis by simp
  next
    case (Cons t ts')
    show ?thesis
    proof
      assume "dec_pattern_compatible_list env (p # ps) ts"
      with Cons have
        head: "dec_pattern_compatible env p t" and
        rest: "dec_pattern_compatible_list env ps ts'"
        by auto
      from rest Cons.IH have
        len: "length ps = length ts'" and
        nth: "\<forall>i < length ps. dec_pattern_compatible env (ps ! i) (ts' ! i)"
        by auto
      have len_full: "length (p # ps) = length ts" using Cons len by simp
      have nth_full: "\<forall>i < length (p # ps).
                        dec_pattern_compatible env ((p # ps) ! i) (ts ! i)"
      proof (intro allI impI)
        fix i assume "i < length (p # ps)"
        show "dec_pattern_compatible env ((p # ps) ! i) (ts ! i)"
          using head nth Cons \<open>i < length (p # ps)\<close>
          by (cases i) auto
      qed
      from len_full nth_full show "length (p # ps) = length ts \<and>
                                    (\<forall>i < length (p # ps).
                                      dec_pattern_compatible env ((p # ps) ! i) (ts ! i))"
        by simp
    next
      assume rhs: "length (p # ps) = length ts \<and>
                   (\<forall>i < length (p # ps). dec_pattern_compatible env ((p # ps) ! i) (ts ! i))"
      with Cons have len_eq: "length ps = length ts'" by simp
      from rhs have head: "dec_pattern_compatible env p (ts ! 0)" by auto
      have head_t: "ts ! 0 = t" using Cons by simp
      have rest_nth: "\<forall>i < length ps. dec_pattern_compatible env (ps ! i) (ts' ! i)"
      proof (intro allI impI)
        fix i assume "i < length ps"
        hence "Suc i < length (p # ps)" by simp
        with rhs have "dec_pattern_compatible env ((p # ps) ! Suc i) (ts ! Suc i)" by blast
        thus "dec_pattern_compatible env (ps ! i) (ts' ! i)"
          using Cons by simp
      qed
      from Cons.IH[of ts'] len_eq rest_nth
      have rest: "dec_pattern_compatible_list env ps ts'" by simp
      from head head_t rest Cons show "dec_pattern_compatible_list env (p # ps) ts" by simp
    qed
  qed
qed

(* dec_pattern_compatible only inspects env via TE_DataCtors, so any env
   modification that leaves TE_DataCtors unchanged preserves it. *)
lemma dec_pattern_compatible_TE_DataCtors_cong:
  "TE_DataCtors env1 = TE_DataCtors env2
   \<Longrightarrow> dec_pattern_compatible env1 p t = dec_pattern_compatible env2 p t"
and dec_pattern_compatible_list_TE_DataCtors_cong:
  "TE_DataCtors env1 = TE_DataCtors env2
   \<Longrightarrow> dec_pattern_compatible_list env1 ps ts = dec_pattern_compatible_list env2 ps ts"
proof (induction env1 p t and env1 ps ts arbitrary: env2 and env2
       rule: dec_pattern_compatible_dec_pattern_compatible_list.induct)
qed (auto split: option.splits CoreType.splits prod.splits)

(* dec_pattern_compatible is invariant under extend_env_one_var. *)
lemma dec_pattern_compatible_extend_env_one_var:
  "dec_pattern_compatible (extend_env_one_var constOf ghost b env) p t
   = dec_pattern_compatible env p t"
  using dec_pattern_compatible_TE_DataCtors_cong[of "extend_env_one_var constOf ghost b env" env p t]
  by (cases b) (simp add: extend_env_one_var_def)

(* If a DecPattern is compatible with a well-kinded scrutinee type, every
   variable binding it introduces is well-kinded. Proof goes by mutual
   induction on dp/list following dec_pattern_compatible's structure;
   variant case uses tyenv_well_formed's payload-well-kindedness +
   apply_subst_specializes_well_kinded. *)
lemma dec_pattern_compatible_vars_well_kinded:
  "dec_pattern_compatible env dp ty
   \<Longrightarrow> is_well_kinded env ty
   \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy) (dec_pattern_var_bindings dp)"
  and dec_pattern_compatible_list_vars_well_kinded:
  "dec_pattern_compatible_list env dps tys
   \<Longrightarrow> list_all (is_well_kinded env) tys
   \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy) (dec_pattern_var_bindings_list dps)"
proof (induction env dp ty and env dps tys
       rule: dec_pattern_compatible_dec_pattern_compatible_list.induct)
  case (1 env vr n ty t)
  thus ?case by simp
next
  case (2 env t)
  thus ?case by simp
next
  case (3 env b t)
  thus ?case by simp
next
  case (4 env i t)
  thus ?case by simp
next
  case (5 env ctorName payload_opt t)
  show ?case
  proof (cases "fmlookup (TE_DataCtors env) ctorName")
    case None
    thus ?thesis using "5.prems"(1) by simp
  next
    case (Some triple)
    obtain dtName tyvars payloadTy where triple_eq:
      "triple = (dtName, tyvars, payloadTy)" by (cases triple) auto
    show ?thesis
    proof (cases t)
      case (CoreTy_Datatype tyName tyArgs)
      from "5.prems"(1) Some triple_eq CoreTy_Datatype have
        ty_match: "tyName = dtName"
        and len_args: "length tyArgs = length tyvars"
        by auto
      show ?thesis
      proof (cases payload_opt)
        case None
        thus ?thesis by simp
      next
        case (Some inner_pat)
        from "5.prems"(1) \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close>
             triple_eq CoreTy_Datatype Some
        have inner_compat:
          "dec_pattern_compatible env inner_pat
                (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
          by auto
        \<comment> \<open>The substituted payload type is well-kinded under env. \<close>
        have payload_wk_at_tyvars:
          "is_well_kinded (env\<lparr>TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars\<rparr>) payloadTy"
          using "5.prems"(3) \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close> triple_eq
          unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by force
        have abs_sub: "TE_AbstractTypes env |\<subseteq>| TE_TypeVars env"
          using "5.prems"(3) unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
        have tyArgs_wk: "list_all (is_well_kinded env) tyArgs"
          using "5.prems"(2) CoreTy_Datatype
          using case_optionE is_well_kinded.simps(1) by blast
        have substituted_payload_wk:
          "is_well_kinded env (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
          using apply_subst_specializes_well_kinded[OF payload_wk_at_tyvars tyArgs_wk len_args[symmetric] abs_sub] .
        show ?thesis
          by (simp add: "5.IH" "5.prems"(3) CoreTy_Datatype Some
              \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close> inner_compat substituted_payload_wk
              triple_eq)
      qed
    qed (use "5.prems"(1) Some triple_eq in \<open>auto split: option.splits prod.splits\<close>)
  qed
next
  case (6 env flds t)
  show ?case
  proof (cases t)
    case (CoreTy_Record fieldTypes)
    from "6.prems"(1) CoreTy_Record have
      names_eq: "map fst flds = map fst fieldTypes"
      and list_compat: "dec_pattern_compatible_list env (map snd flds) (map snd fieldTypes)"
      by auto
    have fieldTypes_wk: "list_all (is_well_kinded env) (map snd fieldTypes)"
      using "6.prems"(2) CoreTy_Record by auto
    have list_vars_wk:
      "list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy)
                (dec_pattern_var_bindings_list (map snd flds))"
      using "6.IH" "6.prems"(3) CoreTy_Record fieldTypes_wk list_compat by auto
    show ?thesis using list_vars_wk by simp
  qed (use "6.prems"(1) in \<open>auto split: CoreType.splits\<close>)
next
  case (7 env)
  thus ?case by simp
next
  case (8 env p ps t ts)
  thus ?case
    by (auto split: prod.splits)
next
  case ("9_1" env v vb)
  thus ?case by simp
next
  case ("9_2" env v vb)
  thus ?case by simp
qed

lemma dec_pattern_compatible_vars_runtime:
  "dec_pattern_compatible env dp ty
   \<Longrightarrow> is_runtime_type env ty
   \<Longrightarrow> is_well_kinded env ty
   \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy) (dec_pattern_var_bindings dp)"
  and dec_pattern_compatible_list_vars_runtime:
  "dec_pattern_compatible_list env dps tys
   \<Longrightarrow> list_all (is_runtime_type env) tys
   \<Longrightarrow> list_all (is_well_kinded env) tys
   \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy) (dec_pattern_var_bindings_list dps)"
proof (induction env dp ty and env dps tys
       rule: dec_pattern_compatible_dec_pattern_compatible_list.induct)
  case (1 env vr n ty t)
  thus ?case by simp
next
  case (2 env t)
  thus ?case by simp
next
  case (3 env b t)
  thus ?case by simp
next
  case (4 env i t)
  thus ?case by simp
next
  case (5 env ctorName payload_opt t)
  show ?case
  proof (cases "fmlookup (TE_DataCtors env) ctorName")
    case None
    thus ?thesis using "5.prems"(1) by simp
  next
    case (Some triple)
    obtain dtName tyvars payloadTy where triple_eq:
      "triple = (dtName, tyvars, payloadTy)" by (cases triple) auto
    show ?thesis
    proof (cases t)
      case (CoreTy_Datatype tyName tyArgs)
      from "5.prems"(1) Some triple_eq CoreTy_Datatype have
        ty_match: "tyName = dtName"
        and len_args: "length tyArgs = length tyvars"
        by auto
      show ?thesis
      proof (cases payload_opt)
        case None
        thus ?thesis by simp
      next
        case (Some inner_pat)
        from "5.prems"(1) \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close>
             triple_eq CoreTy_Datatype Some
        have inner_compat:
          "dec_pattern_compatible env inner_pat
                (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
          by auto
        have payload_wk_at_tyvars:
          "is_well_kinded (env\<lparr>TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars\<rparr>) payloadTy"
          using "5.prems"(4) \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close> triple_eq
          unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by force
        have abs_sub: "TE_AbstractTypes env |\<subseteq>| TE_TypeVars env"
          using "5.prems"(4) unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
        have tyArgs_wk: "list_all (is_well_kinded env) tyArgs"
          using "5.prems"(3) CoreTy_Datatype by (auto split: option.splits)
        have substituted_payload_wk:
          "is_well_kinded env (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
          using apply_subst_specializes_well_kinded[OF payload_wk_at_tyvars tyArgs_wk len_args[symmetric] abs_sub] .
        \<comment> \<open>Runtime side: from is_runtime_type env (CoreTy_Datatype dtName tyArgs),
            dtName is non-ghost and tyArgs all runtime. Then by tyenv_nonghost_payloads_runtime,
            payloadTy is runtime in env extended with tyvars. Specialize with tyArgs. \<close>
        have ng: "dtName |\<notin>| TE_GhostDatatypes env"
          using "5.prems"(2) CoreTy_Datatype ty_match by auto
        have tyArgs_rt: "list_all (is_runtime_type env) tyArgs"
          using "5.prems"(2) CoreTy_Datatype by auto
        have payload_rt_at_tyvars:
          "is_runtime_type (env\<lparr>TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
                                  TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                                         |\<union>| fset_of_list tyvars\<rparr>) payloadTy"
          using "5.prems"(4) \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close> triple_eq ng
          unfolding tyenv_well_formed_def tyenv_nonghost_payloads_runtime_def by force
        have substituted_payload_rt:
          "is_runtime_type env (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
          using apply_subst_specializes_runtime[OF payload_rt_at_tyvars tyArgs_rt len_args[symmetric]] .
        show ?thesis
          by (simp add: "5.IH" "5.prems"(4) CoreTy_Datatype Some
              \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close> inner_compat substituted_payload_rt
              substituted_payload_wk triple_eq)
      qed
    qed (use "5.prems"(1) Some triple_eq in \<open>auto split: option.splits prod.splits\<close>)
  qed
next
  case (6 env flds t)
  show ?case
  proof (cases t)
    case (CoreTy_Record fieldTypes)
    from "6.prems"(1) CoreTy_Record have
      names_eq: "map fst flds = map fst fieldTypes"
      and list_compat: "dec_pattern_compatible_list env (map snd flds) (map snd fieldTypes)"
      by auto
    have fieldTypes_rt: "list_all (is_runtime_type env) (map snd fieldTypes)"
      using "6.prems"(2) CoreTy_Record by auto
    have fieldTypes_wk: "list_all (is_well_kinded env) (map snd fieldTypes)"
      using "6.prems"(3) CoreTy_Record by auto
    have list_vars_rt:
      "list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy)
                (dec_pattern_var_bindings_list (map snd flds))"
      using "6.IH" "6.prems"(4) CoreTy_Record fieldTypes_rt fieldTypes_wk list_compat
      by auto
    show ?thesis using list_vars_rt by simp
  qed (use "6.prems"(1) in \<open>auto split: CoreType.splits\<close>)
next
  case (7 env)
  thus ?case by simp
next
  case (8 env p ps t ts)
  thus ?case by (auto split: prod.splits)
next
  case ("9_1" env v vb)
  thus ?case by simp
next
  case ("9_2" env v vb)
  thus ?case by simp
qed


section \<open>Correctness of decorate_pattern\<close>

(* decorate_pattern_list preserves length (when scrutTys has matching length). *)
lemma decorate_pattern_list_length:
  "decorate_pattern_list env elabEnv ghost pats scrutTys accSubst next_mv
     = Inr (dps, accSubst', next_mv')
   \<Longrightarrow> length pats = length scrutTys
   \<Longrightarrow> length dps = length pats"
proof (induction pats arbitrary: scrutTys accSubst next_mv dps accSubst' next_mv')
  case Nil
  thus ?case by simp
next
  case (Cons p ps)
  from Cons.prems(2) obtain t tsRest where
    scruts_eq: "scrutTys = t # tsRest" and
    len_rest: "length ps = length tsRest"
    by (cases scrutTys) auto
  from Cons.prems(1) scruts_eq obtain dp s mv where
    dec_head: "decorate_pattern env elabEnv ghost p t accSubst next_mv = Inr (dp, s, mv)"
    by (auto simp: Let_def split: sum.splits)
  from Cons.prems(1) scruts_eq dec_head obtain dpsRest where
    dec_rest: "decorate_pattern_list env elabEnv ghost ps tsRest s mv
                = Inr (dpsRest, accSubst', next_mv')" and
    dps_eq: "dps = dp # dpsRest"
    by (auto simp: Let_def split: sum.splits)
  from Cons.IH[OF dec_rest len_rest] have "length dpsRest = length ps" .
  thus ?case using dps_eq by simp
qed

(* apply_subst_to_dec_pattern distributes over compose_subst. *)
lemma apply_subst_to_dec_pattern_compose:
  "apply_subst_to_dec_pattern s2 (apply_subst_to_dec_pattern s1 dp)
   = apply_subst_to_dec_pattern (compose_subst s2 s1) dp"
proof (induction dp)
  case (DP_Var vr n ty)
  thus ?case by (simp add: compose_subst_correct)
next
  case (DP_Record flds)
  have "\<And>name p. (name, p) \<in> set flds \<Longrightarrow>
          apply_subst_to_dec_pattern s2 (apply_subst_to_dec_pattern s1 p)
          = apply_subst_to_dec_pattern (compose_subst s2 s1) p"
  proof -
    fix name p assume mem: "(name, p) \<in> set flds"
    have p_in_snds: "p \<in> Basic_BNFs.snds (name, p)" by simp
    show "apply_subst_to_dec_pattern s2 (apply_subst_to_dec_pattern s1 p)
          = apply_subst_to_dec_pattern (compose_subst s2 s1) p"
      using DP_Record.IH[OF mem p_in_snds] .
  qed
  hence map_eq:
    "map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern s2 (apply_subst_to_dec_pattern s1 p))) flds
     = map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern (compose_subst s2 s1) p)) flds"
    by (induction flds) auto
  show ?case
    using map_eq by fastforce
next
  case (DP_Variant cn opt)
  show ?case
  proof (cases opt)
    case None thus ?thesis by simp
  next
    case (Some inner) with DP_Variant show ?thesis by simp
  qed
qed simp_all

(* Applying a further substitution to a decorated pattern preserves
   compatibility, given the new substitution is applied uniformly to
   both the pattern's embedded types and the scrutinee type. Used both
   as a final post-pass and inside decorate_pattern_correct itself, to
   lift compatibility through later substitutions. *)
lemma apply_subst_to_dec_pattern_preserves_compatibility:
  "dec_pattern_compatible env dp scrutTy \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   (\<And>n. n |\<in>| TE_AbstractTypes env \<Longrightarrow> fmlookup subst n = None) \<Longrightarrow>
   dec_pattern_compatible env (apply_subst_to_dec_pattern subst dp)
                              (apply_subst subst scrutTy)"
  and apply_subst_to_dec_pattern_list_preserves_compatibility:
  "dec_pattern_compatible_list env dps scrutTys \<Longrightarrow>
   tyenv_well_formed env \<Longrightarrow>
   (\<And>n. n |\<in>| TE_AbstractTypes env \<Longrightarrow> fmlookup subst n = None) \<Longrightarrow>
   dec_pattern_compatible_list env (map (apply_subst_to_dec_pattern subst) dps)
                                   (map (apply_subst subst) scrutTys)"
proof (induction env dp scrutTy and env dps scrutTys
       rule: dec_pattern_compatible_dec_pattern_compatible_list.induct)
  case (1 env vr n ty t)
  thus ?case by simp
next
  case (2 env t)
  thus ?case by simp
next
  case (3 env b t)
  from "3" have t_eq: "t = CoreTy_Bool" by simp
  hence "apply_subst subst t = CoreTy_Bool" by simp
  thus ?case by simp
next
  case (4 env i t)
  then show ?case by (cases t) auto
next
  case (5 env ctorName payload_opt t)
  show ?case
  proof (cases "fmlookup (TE_DataCtors env) ctorName")
    case None
    thus ?thesis using "5.prems" by simp
  next
    case (Some triple)
    obtain dtName triple2 where triple_split1: "(dtName, triple2) = triple"
      by (cases triple) auto
    obtain tyvars payloadTy where triple_split2: "(tyvars, payloadTy) = triple2"
      by (cases triple2) auto
    have triple_eq_rev: "triple = (dtName, tyvars, payloadTy)"
      using triple_split1 triple_split2 by simp
    show ?thesis
    proof (cases t)
      case (CoreTy_Datatype tyName tyArgs)
      from "5.prems" Some triple_eq_rev CoreTy_Datatype have
        ty_eq: "tyName = dtName" and
        len_args: "length tyArgs = length tyvars"
        by auto
      have apply_t_eq: "apply_subst subst t
                        = CoreTy_Datatype tyName (map (apply_subst subst) tyArgs)"
        using CoreTy_Datatype by simp
      have len_args_subst: "length (map (apply_subst subst) tyArgs) = length tyvars"
        using len_args by simp
      show ?thesis
      proof (cases payload_opt)
        case None
        have lhs: "apply_subst_to_dec_pattern subst (DP_Variant ctorName payload_opt)
                   = DP_Variant ctorName None"
          using None by simp
        show ?thesis
          unfolding lhs apply_t_eq
          using Some triple_eq_rev ty_eq len_args_subst by simp
      next
        case (Some inner_pat)
        from "5.prems" \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close> triple_eq_rev
             CoreTy_Datatype Some
        have inner_compat:
          "dec_pattern_compatible env inner_pat
                (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
          by auto
        from "5.IH"[OF \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close>
                       triple_split1 triple_split2
                       CoreTy_Datatype Some inner_compat "5.prems"(2) "5.prems"(3)]
        have inner_subst_compat:
          "dec_pattern_compatible env (apply_subst_to_dec_pattern subst inner_pat)
              (apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy))" .
        have payload_wk:
          "is_well_kinded (env\<lparr>TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars\<rparr>) payloadTy"
          using "5.prems"(2) \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close> triple_eq_rev
          unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by force
        \<comment> \<open>The payload's tyvars are either the ctor's own type parameters or abstract types,
            which the substitution leaves untouched (capture-avoidance, "5.prems"(3)). \<close>
        have payload_tyvars_ok:
          "\<And>n. n \<in> type_tyvars payloadTy \<Longrightarrow> n \<in> set tyvars \<or> n |\<notin>| fmdom subst"
        proof -
          fix n assume ni: "n \<in> type_tyvars payloadTy"
          from is_well_kinded_type_tyvars_subset[OF payload_wk] ni
          have "n |\<in>| TE_AbstractTypes env \<or> n \<in> set tyvars"
            by (auto simp: fset_of_list.rep_eq)
          thus "n \<in> set tyvars \<or> n |\<notin>| fmdom subst"
            using "5.prems"(3) by (auto simp: fmdom_notI)
        qed
        have tyvars_distinct: "distinct tyvars"
          using "5.prems"(2) \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close> triple_eq_rev
          unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by force
        have rewrite:
          "apply_subst subst (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)
           = apply_subst (fmap_of_list (zip tyvars (map (apply_subst subst) tyArgs))) payloadTy"
          using apply_subst_compose_zip_extra[OF len_args[symmetric] payload_tyvars_ok tyvars_distinct]
          by simp
        have lhs: "apply_subst_to_dec_pattern subst (DP_Variant ctorName payload_opt)
                   = DP_Variant ctorName (Some (apply_subst_to_dec_pattern subst inner_pat))"
          using Some by simp
        show ?thesis
          unfolding lhs apply_t_eq
          using \<open>fmlookup (TE_DataCtors env) ctorName = Some triple\<close> triple_eq_rev ty_eq
                len_args_subst inner_subst_compat rewrite
          by simp
      qed
    qed (use "5.prems" Some triple_eq_rev in \<open>auto split: option.splits prod.splits\<close>)
  qed
next
  case (6 env flds t)
  show ?case
  proof (cases t)
    case (CoreTy_Record fieldTypes)
    from "6.prems" CoreTy_Record have
      names_eq: "map fst flds = map fst fieldTypes" and
      list_compat: "dec_pattern_compatible_list env (map snd flds) (map snd fieldTypes)"
      by auto
    from "6.IH"[OF CoreTy_Record list_compat "6.prems"(2) "6.prems"(3)]
    have ih_list:
      "dec_pattern_compatible_list env
         (map (apply_subst_to_dec_pattern subst) (map snd flds))
         (map (apply_subst subst) (map snd fieldTypes))" .
    have map_fst_subst:
      "map fst (map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern subst p)) flds)
       = map fst flds"
      by (induction flds) auto
    have map_snd_subst:
      "map snd (map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern subst p)) flds)
       = map (apply_subst_to_dec_pattern subst) (map snd flds)"
      by (induction flds) auto
    have map_fst_subst_types:
      "map fst (map (\<lambda>(name, ty). (name, apply_subst subst ty)) fieldTypes)
       = map fst fieldTypes"
      by (induction fieldTypes) auto
    have map_snd_subst_types:
      "map snd (map (\<lambda>(name, ty). (name, apply_subst subst ty)) fieldTypes)
       = map (apply_subst subst) (map snd fieldTypes)"
      by (induction fieldTypes) auto
    let ?subst_flds = "map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern subst p)) flds"
    let ?subst_fts = "map (\<lambda>(name, ty). (name, apply_subst subst ty)) fieldTypes"
    have lhs_eq: "apply_subst_to_dec_pattern subst (DP_Record flds) = DP_Record ?subst_flds"
      by simp
    have rhs_eq: "apply_subst subst t = CoreTy_Record ?subst_fts"
      using CoreTy_Record by simp
    have step_names: "map fst ?subst_flds = map fst ?subst_fts"
      using names_eq map_fst_subst map_fst_subst_types by simp
    have step_compat:
      "dec_pattern_compatible_list env (map snd ?subst_flds) (map snd ?subst_fts)"
      using ih_list map_snd_subst map_snd_subst_types by metis
    show ?thesis
      unfolding lhs_eq rhs_eq
      using step_names step_compat by simp
  qed (use "6.prems" in \<open>auto split: CoreType.splits\<close>)
next
  case (7 env)
  thus ?case by simp
next
  case (8 env p ps t ts)
  have hd_compat: "dec_pattern_compatible env p t"
    and tl_compat: "dec_pattern_compatible_list env ps ts"
    using "8.prems"(1) by auto
  have hd_subst: "dec_pattern_compatible env (apply_subst_to_dec_pattern subst p) (apply_subst subst t)"
    using "8.IH"(1)[OF hd_compat "8.prems"(2) "8.prems"(3)] .
  have tl_subst: "dec_pattern_compatible_list env (map (apply_subst_to_dec_pattern subst) ps)
                                                  (map (apply_subst subst) ts)"
    using "8.IH"(2)[OF tl_compat "8.prems"(2) "8.prems"(3)] .
  from hd_subst tl_subst show ?case by simp
next
  case ("9_1" env v vb)
  thus ?case by simp
next
  case ("9_2" env v vb)
  thus ?case by simp
qed


(* Main correctness theorem for decorate_pattern.

   This shows that if decorate_pattern succeeds, then the substituted DecPattern is 
   compatible with the substituted scrutinee type.

   The conclusion also includes:
   - the compose-shape (\<exists>T. accSubst' = compose_subst T accSubst) so that any
     equality at the result-time substitution can be lifted back through
     intermediate refinements;
   - factoring relations that imply idempotence of accSubst';
   - well-kindedness preservation of accSubst's range across the call.

   The well-kindedness premises use an extended environment
   `extend_env_with_tyvars env ghost lo next_mv`, where `lo` is the caller's
   outer bound on next_mv and tyvars in `[lo, next_mv)` are the fresh
   metavariables introduced so far. This is the same pattern used by
   elab_term_correct. *)
lemma decorate_pattern_correct:
  "decorate_pattern env elabEnv ghost pat scrutTy accSubst next_mv
       = Inr (dp, accSubst', next_mv')
   \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> subst_factors_through accSubst accSubst
   \<Longrightarrow> lo \<le> next_mv
   \<Longrightarrow> is_well_kinded (extend_env_with_tyvars env ghost lo next_mv) scrutTy
   \<Longrightarrow> \<forall>ty \<in> fmran' accSubst.
         is_well_kinded (extend_env_with_tyvars env ghost lo next_mv) ty
   \<Longrightarrow> fmdom accSubst |\<inter>| TE_TypeVars env = {||}
   \<Longrightarrow> (ghost = NotGhost \<Longrightarrow>
         is_runtime_type (extend_env_with_tyvars env ghost lo next_mv) scrutTy)
   \<Longrightarrow> (ghost = NotGhost \<Longrightarrow>
         \<forall>ty \<in> fmran' accSubst.
           is_runtime_type (extend_env_with_tyvars env ghost lo next_mv) ty)
   \<Longrightarrow> dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                  (apply_subst accSubst' scrutTy)
        \<and> next_mv \<le> next_mv'
        \<and> (\<exists>T. accSubst' = compose_subst T accSubst)
        \<and> subst_factors_through accSubst' accSubst
        \<and> subst_factors_through accSubst' accSubst'
        \<and> (\<forall>ty \<in> fmran' accSubst'.
              is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty)
        \<and> fmdom accSubst' |\<inter>| TE_TypeVars env = {||}
        \<and> (ghost = NotGhost \<longrightarrow>
             (\<forall>ty \<in> fmran' accSubst'.
                 is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty))"
and decorate_pattern_list_correct:
  "decorate_pattern_list env elabEnv ghost pats scrutTys accSubst next_mv
       = Inr (dps, accSubst', next_mv')
   \<Longrightarrow> length pats = length scrutTys
   \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> subst_factors_through accSubst accSubst
   \<Longrightarrow> lo \<le> next_mv
   \<Longrightarrow> list_all (is_well_kinded (extend_env_with_tyvars env ghost lo next_mv)) scrutTys
   \<Longrightarrow> \<forall>ty \<in> fmran' accSubst.
         is_well_kinded (extend_env_with_tyvars env ghost lo next_mv) ty
   \<Longrightarrow> fmdom accSubst |\<inter>| TE_TypeVars env = {||}
   \<Longrightarrow> (ghost = NotGhost \<Longrightarrow>
         list_all (is_runtime_type (extend_env_with_tyvars env ghost lo next_mv)) scrutTys)
   \<Longrightarrow> (ghost = NotGhost \<Longrightarrow>
         \<forall>ty \<in> fmran' accSubst.
           is_runtime_type (extend_env_with_tyvars env ghost lo next_mv) ty)
   \<Longrightarrow> dec_pattern_compatible_list env (map (apply_subst_to_dec_pattern accSubst') dps)
                                       (map (apply_subst accSubst') scrutTys)
        \<and> next_mv \<le> next_mv'
        \<and> (\<exists>T. accSubst' = compose_subst T accSubst)
        \<and> subst_factors_through accSubst' accSubst
        \<and> subst_factors_through accSubst' accSubst'
        \<and> (\<forall>ty \<in> fmran' accSubst'.
              is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty)
        \<and> fmdom accSubst' |\<inter>| TE_TypeVars env = {||}
        \<and> (ghost = NotGhost \<longrightarrow>
             (\<forall>ty \<in> fmran' accSubst'.
                 is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty))"
proof (induction env elabEnv ghost pat scrutTy accSubst next_mv
       and env elabEnv ghost pats scrutTys accSubst next_mv
       arbitrary: dp accSubst' next_mv' and dps accSubst' next_mv'
       rule: decorate_pattern_decorate_pattern_list.induct)
  case (1 env elabEnv ghost loc vr name scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Var. \<close>
  from "1.prems" have eq:
    "dp = DP_Var vr name (apply_subst accSubst scrutTy)"
    "accSubst' = accSubst" "next_mv' = next_mv"
    by auto
  have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
    by (metis compose_subst_empty_left eq(2))
  have factors_self: "subst_factors_through accSubst' accSubst'"
    using "1.prems"(3) eq by simp
  have factors_acc: "subst_factors_through accSubst' accSubst"
    using "1.prems"(3) eq by simp
  have type_eq: "apply_subst accSubst' (apply_subst accSubst scrutTy) = apply_subst accSubst' scrutTy"
    using factors_acc unfolding subst_factors_through_def by simp
  have compat: "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                            (apply_subst accSubst' scrutTy)"
    using eq type_eq by simp
  have range_wk: "\<forall>ty \<in> fmran' accSubst'. is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty"
    using "1.prems"(6) eq by simp
  have dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}"
    using "1.prems"(7) eq by simp
  have range_rt: "ghost = NotGhost \<longrightarrow>
                    (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
    using "1.prems"(9) eq by simp
  show ?case
    using eq refine compat factors_self factors_acc range_wk dom_flex range_rt
    by simp
next
  case (2 env elabEnv ghost loc scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Wildcard. \<close>
  from "2.prems" have eq:
    "dp = DP_Wildcard" "accSubst' = accSubst" "next_mv' = next_mv"
    by simp_all
  have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
    by (metis compose_subst_empty_left eq(2))
  have range_wk: "\<forall>ty \<in> fmran' accSubst'. is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty"
    using "2.prems"(6) eq by simp
  have dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}"
    using "2.prems"(7) eq by simp
  have range_rt: "ghost = NotGhost \<longrightarrow>
                    (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
    using "2.prems"(9) eq by simp
  show ?case
    using eq refine "2.prems"(3) range_wk dom_flex range_rt by simp
next
  case (3 env elabEnv ghost loc b scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Bool. \<close>
  from "3.prems" obtain s where
    tuc: "try_unify_compose env CoreTy_Bool scrutTy accSubst = Some s" and
    eq: "dp = DP_Bool b" "accSubst' = s" "next_mv' = next_mv"
    by (auto split: option.splits)
  have eq_bool: "apply_subst s CoreTy_Bool = apply_subst s scrutTy"
    using try_unify_compose_makes_equal[OF tuc] .
  hence "apply_subst s scrutTy = CoreTy_Bool" by simp
  hence compat: "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                            (apply_subst accSubst' scrutTy)"
    using eq by simp
  have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
    using try_unify_compose_compose_shape[OF tuc] eq by simp
  have factors_acc: "subst_factors_through accSubst' accSubst"
    using try_unify_compose_factors_through[OF tuc "3.prems"(3)] eq by simp
  have factors_self: "subst_factors_through accSubst' accSubst'"
    using try_unify_compose_idem[OF tuc "3.prems"(3)] eq by simp
  let ?wkEnv = "extend_env_with_tyvars env ghost lo next_mv"
  have bool_wk: "is_well_kinded ?wkEnv CoreTy_Bool" by simp
  have range_wk: "\<forall>ty \<in> fmran' accSubst'. is_well_kinded ?wkEnv ty"
    using try_unify_compose_preserves_well_kinded[OF tuc "3.prems"(6) bool_wk "3.prems"(5)]
          eq by simp
  have range_wk_at_next': "\<forall>ty \<in> fmran' accSubst'.
                              is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty"
    using range_wk eq by simp
  have dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}"
    using try_unify_compose_dom_flex[OF tuc "3.prems"(7)] eq by simp
  have range_rt: "ghost = NotGhost \<longrightarrow>
                    (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
  proof
    assume ng: "ghost = NotGhost"
    have bool_rt: "is_runtime_type ?wkEnv CoreTy_Bool" by simp
    have rt: "\<forall>ty \<in> fmran' accSubst'. is_runtime_type ?wkEnv ty"
      using try_unify_compose_preserves_runtime[OF tuc "3.prems"(9)[OF ng] bool_rt "3.prems"(8)[OF ng]]
            eq by simp
    thus "\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty"
      using eq by simp
  qed
  show ?case using compat refine eq factors_acc factors_self range_wk_at_next' dom_flex range_rt
    by simp
next
  case (4 env elabEnv ghost loc i scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Int: split on shape of apply_subst accSubst scrutTy. \<close>
  let ?e = "apply_subst accSubst scrutTy"

  \<comment> \<open>Helper for the "fall-through" cases that go through try_unify_compose. \<close>
  have fallthrough:
    "\<And>s. try_unify_compose env int_literal_default_type scrutTy accSubst = Some s
          \<Longrightarrow> int_in_range (int_range Signed IntBits_32) i
          \<Longrightarrow> dp = DP_Int i \<Longrightarrow> accSubst' = s \<Longrightarrow> next_mv' = next_mv
          \<Longrightarrow> ?case"
  proof -
    fix s assume tuc: "try_unify_compose env int_literal_default_type scrutTy accSubst = Some s"
       and rng: "int_in_range (int_range Signed IntBits_32) i"
       and eq: "dp = DP_Int i" "accSubst' = s" "next_mv' = next_mv"
    have "apply_subst s int_literal_default_type = apply_subst s scrutTy"
      using try_unify_compose_makes_equal[OF tuc] .
    hence "apply_subst s scrutTy = CoreTy_FiniteInt Signed IntBits_32"
      by (simp add: int_literal_default_type_def)
    hence compat: "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                              (apply_subst accSubst' scrutTy)"
      using eq rng by simp
    have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
      using try_unify_compose_compose_shape[OF tuc] eq by simp
    have factors_acc: "subst_factors_through accSubst' accSubst"
      using try_unify_compose_factors_through[OF tuc "4.prems"(3)] eq by simp
    have factors_self: "subst_factors_through accSubst' accSubst'"
      using try_unify_compose_idem[OF tuc "4.prems"(3)] eq by simp
    let ?wkEnv = "extend_env_with_tyvars env ghost lo next_mv"
    have int_wk: "is_well_kinded ?wkEnv int_literal_default_type"
      by (simp add: int_literal_default_type_def)
    have range_wk: "\<forall>ty \<in> fmran' accSubst'. is_well_kinded ?wkEnv ty"
      using try_unify_compose_preserves_well_kinded[OF tuc "4.prems"(6) int_wk "4.prems"(5)]
            eq by simp
    have range_wk': "\<forall>ty \<in> fmran' accSubst'.
                       is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty"
      using range_wk eq by simp
    have dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}"
      using try_unify_compose_dom_flex[OF tuc "4.prems"(7)] eq by simp
    have range_rt: "ghost = NotGhost \<longrightarrow>
                      (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
    proof
      assume ng: "ghost = NotGhost"
      have int_rt: "is_runtime_type ?wkEnv int_literal_default_type"
        by (simp add: int_literal_default_type_def)
      have rt: "\<forall>ty \<in> fmran' accSubst'. is_runtime_type ?wkEnv ty"
        using try_unify_compose_preserves_runtime[OF tuc "4.prems"(9)[OF ng] int_rt "4.prems"(8)[OF ng]]
              eq by simp
      thus "\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty"
        using eq by simp
    qed
    show ?case using compat refine eq factors_acc factors_self range_wk' dom_flex range_rt
      by simp
  qed

  \<comment> \<open>Helper for the "no unification" case (FiniteInt scrutinee, literal in range).
      apply_subst accSubst' scrutTy is already a finite int type; substituted dp = dp. \<close>
  have noop:
    "\<And>sign bits. accSubst' = accSubst \<Longrightarrow> dp = DP_Int i \<Longrightarrow> next_mv' = next_mv
        \<Longrightarrow> apply_subst accSubst' scrutTy = CoreTy_FiniteInt sign bits
        \<Longrightarrow> int_in_range (int_range sign bits) i \<Longrightarrow> ?case"
  proof -
    fix sign bits
    assume eq: "accSubst' = accSubst" "dp = DP_Int i" "next_mv' = next_mv"
       and shape_eq: "apply_subst accSubst' scrutTy = CoreTy_FiniteInt sign bits"
       and shape_rng: "int_in_range (int_range sign bits) i"
    have compat: "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                              (apply_subst accSubst' scrutTy)"
      using eq shape_eq shape_rng by simp
    have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
      by (metis compose_subst_empty_left eq(1))
    have range_wk: "\<forall>ty \<in> fmran' accSubst'.
                      is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty"
      using "4.prems"(6) eq by simp
    have dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}"
      using "4.prems"(7) eq by simp
    have range_rt: "ghost = NotGhost \<longrightarrow>
                      (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
      using "4.prems"(9) eq by simp
    show ?case using compat refine eq "4.prems"(3) range_wk dom_flex range_rt
      by simp
  qed

  show ?case
  proof (cases ?e)
    case (CoreTy_FiniteInt sign bits)
    from "4.prems" CoreTy_FiniteInt have eq:
      "dp = DP_Int i" "accSubst' = accSubst" "next_mv' = next_mv"
      and rng: "int_in_range (int_range sign bits) i"
      by (auto simp: Let_def split: if_splits)
    have shape: "apply_subst accSubst' scrutTy = CoreTy_FiniteInt sign bits"
      using eq CoreTy_FiniteInt by simp
    show ?thesis using noop[OF eq(2) eq(1) eq(3) shape rng] by simp
  next
    case CoreTy_MathInt
    from "4.prems" CoreTy_MathInt obtain s where
      tuc: "try_unify_compose env int_literal_default_type scrutTy accSubst = Some s" and
      rng: "int_in_range (int_range Signed IntBits_32) i" and
      eq: "dp = DP_Int i" "accSubst' = s" "next_mv' = next_mv"
      by (auto simp: Let_def split: option.splits if_splits)
    show ?thesis using fallthrough[OF tuc rng eq(1) eq(2) eq(3)] .
  next
    case (CoreTy_Var n)
    from "4.prems" CoreTy_Var obtain s where
      tuc: "try_unify_compose env int_literal_default_type scrutTy accSubst = Some s" and
      rng: "int_in_range (int_range Signed IntBits_32) i" and
      eq: "dp = DP_Int i" "accSubst' = s" "next_mv' = next_mv"
      by (auto simp: Let_def split: option.splits if_splits)
    show ?thesis using fallthrough[OF tuc rng eq(1) eq(2) eq(3)] .
  next
    case (CoreTy_Datatype name tyArgs)
    from "4.prems" CoreTy_Datatype obtain s where
      tuc: "try_unify_compose env int_literal_default_type scrutTy accSubst = Some s" and
      rng: "int_in_range (int_range Signed IntBits_32) i" and
      eq: "dp = DP_Int i" "accSubst' = s" "next_mv' = next_mv"
      by (auto simp: Let_def split: option.splits if_splits)
    show ?thesis using fallthrough[OF tuc rng eq(1) eq(2) eq(3)] .
  next
    case CoreTy_Bool
    from "4.prems" CoreTy_Bool obtain s where
      tuc: "try_unify_compose env int_literal_default_type scrutTy accSubst = Some s" and
      rng: "int_in_range (int_range Signed IntBits_32) i" and
      eq: "dp = DP_Int i" "accSubst' = s" "next_mv' = next_mv"
      by (auto simp: Let_def split: option.splits if_splits)
    show ?thesis using fallthrough[OF tuc rng eq(1) eq(2) eq(3)] .
  next
    case CoreTy_MathReal
    from "4.prems" CoreTy_MathReal obtain s where
      tuc: "try_unify_compose env int_literal_default_type scrutTy accSubst = Some s" and
      rng: "int_in_range (int_range Signed IntBits_32) i" and
      eq: "dp = DP_Int i" "accSubst' = s" "next_mv' = next_mv"
      by (auto simp: Let_def split: option.splits if_splits)
    show ?thesis using fallthrough[OF tuc rng eq(1) eq(2) eq(3)] .
  next
    case (CoreTy_Record flds)
    from "4.prems" CoreTy_Record obtain s where
      tuc: "try_unify_compose env int_literal_default_type scrutTy accSubst = Some s" and
      rng: "int_in_range (int_range Signed IntBits_32) i" and
      eq: "dp = DP_Int i" "accSubst' = s" "next_mv' = next_mv"
      by (auto simp: Let_def split: option.splits if_splits)
    show ?thesis using fallthrough[OF tuc rng eq(1) eq(2) eq(3)] .
  next
    case (CoreTy_Array elemTy dims)
    from "4.prems" CoreTy_Array obtain s where
      tuc: "try_unify_compose env int_literal_default_type scrutTy accSubst = Some s" and
      rng: "int_in_range (int_range Signed IntBits_32) i" and
      eq: "dp = DP_Int i" "accSubst' = s" "next_mv' = next_mv"
      by (auto simp: Let_def split: option.splits if_splits)
    show ?thesis using fallthrough[OF tuc rng eq(1) eq(2) eq(3)] .
  qed
next
  case (5 env elabEnv ghost loc pats scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Tuple: builds an expected record type with fresh metas, unifies, recurses. \<close>
  let ?n = "length pats"
  let ?names = "tuple_field_names ?n"
  let ?freshFieldTys = "mv_block next_mv (next_mv + ?n)"
  let ?next_mv_init = "next_mv + ?n"
  let ?recTy = "CoreTy_Record (zip ?names ?freshFieldTys)"

  from "5.prems"(1) obtain s where
    tuc: "try_unify_compose env ?recTy scrutTy accSubst = Some s"
    by (auto simp: Let_def split: option.splits)
  from "5.prems"(1) tuc obtain decPats where
    rec: "decorate_pattern_list env elabEnv ghost pats ?freshFieldTys s ?next_mv_init
            = Inr (decPats, accSubst', next_mv')" and
    dp_eq: "dp = DP_Record (zip ?names decPats)"
    by (auto simp: Let_def split: sum.splits)

  have len_pats_fresh: "length pats = length ?freshFieldTys" by simp

  \<comment> \<open>s is idempotent (try_unify_compose preserves idempotence). \<close>
  have s_idem: "subst_factors_through s s"
    using try_unify_compose_idem[OF tuc "5.prems"(3)] .
  have s_factors_acc: "subst_factors_through s accSubst"
    using try_unify_compose_factors_through[OF tuc "5.prems"(3)] .

  have eq_n: "?n = length pats" by simp
  have eq_names: "?names = tuple_field_names ?n" by simp
  have eq_fresh: "?freshFieldTys = mv_block next_mv (next_mv + ?n)" by simp
  have eq_next_init: "?next_mv_init = next_mv + ?n" by simp
  have eq_recTy: "?recTy = CoreTy_Record (zip ?names ?freshFieldTys)" by simp

  \<comment> \<open>Well-kindedness preliminaries for the IH. \<close>
  let ?wkEnv = "extend_env_with_tyvars env ghost lo next_mv"
  let ?wkEnv_init = "extend_env_with_tyvars env ghost lo ?next_mv_init"
  have lo_le_init: "lo \<le> ?next_mv_init" using "5.prems"(4) by simp
  have lo_le_next_mv: "lo \<le> next_mv" using "5.prems"(4) .
  have next_mv_le_init: "next_mv \<le> ?next_mv_init" by simp

  \<comment> \<open>Each fresh tyvar is well-kinded under wkEnv_init (since its name is in
      mv_fset lo ?next_mv_init, which the env extension adds to TE_TypeVars). \<close>
  have fresh_wk_init: "list_all (is_well_kinded ?wkEnv_init) ?freshFieldTys"
  proof -
    have "\<forall>k \<in> set [next_mv ..< ?next_mv_init].
            is_well_kinded ?wkEnv_init (CoreTy_Var (mv_name k))"
    proof
      fix k assume k_in: "k \<in> set [next_mv ..< ?next_mv_init]"
      hence "lo \<le> k \<and> k < ?next_mv_init" using lo_le_next_mv by auto
      hence "mv_name k |\<in>| mv_fset lo ?next_mv_init" by auto
      hence "mv_name k |\<in>| TE_TypeVars ?wkEnv_init"
        unfolding extend_env_with_tyvars_def by simp
      thus "is_well_kinded ?wkEnv_init (CoreTy_Var (mv_name k))" by simp
    qed
    thus ?thesis by (simp add: mv_block_eq_map_CoreTy_Var list_all_iff)
  qed

  \<comment> \<open>recTy is well-kinded under wkEnv_init: tuple_field_names produces distinct names, and
      the field types are the fresh vars (just shown well-kinded). \<close>
  have names_distinct: "distinct ?names" by (simp add: distinct_tuple_field_names)
  have len_names_fresh': "length ?names = length ?freshFieldTys"
    by (simp add: tuple_field_names_def)
  have recTy_wk_init: "is_well_kinded ?wkEnv_init ?recTy"
  proof -
    have map_fst: "map fst (zip ?names ?freshFieldTys) = ?names"
      using len_names_fresh' by simp
    have map_snd: "map snd (zip ?names ?freshFieldTys) = ?freshFieldTys"
      using len_names_fresh' by simp
    show ?thesis
      using names_distinct fresh_wk_init map_fst map_snd by simp
  qed

  \<comment> \<open>scrutTy is well-kinded under wkEnv (premise) and hence under wkEnv_init (widening). \<close>
  have scrutTy_wk_init: "is_well_kinded ?wkEnv_init scrutTy"
    using is_well_kinded_extend_env_with_tyvars_mono[OF "5.prems"(5) order_refl next_mv_le_init] .

  \<comment> \<open>accSubst's range is well-kinded under wkEnv (premise) and hence under wkEnv_init. \<close>
  have acc_range_wk_init: "\<forall>ty \<in> fmran' accSubst. is_well_kinded ?wkEnv_init ty"
    using "5.prems"(6) is_well_kinded_extend_env_with_tyvars_mono[OF _ order_refl next_mv_le_init]
    by blast

  \<comment> \<open>s's range is well-kinded under wkEnv_init via try_unify_compose_preserves_well_kinded. \<close>
  have s_range_wk_init: "\<forall>ty \<in> fmran' s. is_well_kinded ?wkEnv_init ty"
    using try_unify_compose_preserves_well_kinded[OF tuc acc_range_wk_init recTy_wk_init scrutTy_wk_init] .

  \<comment> \<open>s's domain remains flex via try_unify_compose_dom_flex. \<close>
  have s_dom_flex: "fmdom s |\<inter>| TE_TypeVars env = {||}"
    using try_unify_compose_dom_flex[OF tuc "5.prems"(7)] .

  \<comment> \<open>Runtime-type variants of the well-kinded facts. Ghost-conditional. \<close>
  have fresh_rt_init:
    "ghost = NotGhost \<Longrightarrow> list_all (is_runtime_type ?wkEnv_init) ?freshFieldTys"
  proof -
    assume ng: "ghost = NotGhost"
    have "\<forall>k \<in> set [next_mv ..< ?next_mv_init].
            is_runtime_type ?wkEnv_init (CoreTy_Var (mv_name k))"
    proof
      fix k assume k_in: "k \<in> set [next_mv ..< ?next_mv_init]"
      hence "lo \<le> k \<and> k < ?next_mv_init" using lo_le_next_mv by auto
      hence "mv_name k |\<in>| mv_fset lo ?next_mv_init" by auto
      hence "mv_name k |\<in>| TE_RuntimeTypeVars ?wkEnv_init"
        unfolding extend_env_with_tyvars_def using ng by simp
      thus "is_runtime_type ?wkEnv_init (CoreTy_Var (mv_name k))" by simp
    qed
    thus ?thesis by (simp add: mv_block_eq_map_CoreTy_Var list_all_iff)
  qed
  have recTy_rt_init: "ghost = NotGhost \<Longrightarrow> is_runtime_type ?wkEnv_init ?recTy"
  proof -
    assume ng: "ghost = NotGhost"
    have map_snd: "map snd (zip ?names ?freshFieldTys) = ?freshFieldTys"
      using len_names_fresh' by simp
    show ?thesis using fresh_rt_init[OF ng] map_snd by simp
  qed
  have scrutTy_rt_init: "ghost = NotGhost \<Longrightarrow> is_runtime_type ?wkEnv_init scrutTy"
    using "5.prems"(8) is_runtime_type_extend_env_with_tyvars_mono[OF _ order_refl next_mv_le_init]
    by blast
  have acc_range_rt_init:
    "ghost = NotGhost \<Longrightarrow> \<forall>ty \<in> fmran' accSubst. is_runtime_type ?wkEnv_init ty"
    using "5.prems"(9) is_runtime_type_extend_env_with_tyvars_mono[OF _ order_refl next_mv_le_init]
    by blast
  have s_range_rt_init: "ghost = NotGhost \<Longrightarrow> \<forall>ty \<in> fmran' s. is_runtime_type ?wkEnv_init ty"
  proof -
    assume ng: "ghost = NotGhost"
    show "\<forall>ty \<in> fmran' s. is_runtime_type ?wkEnv_init ty"
      using try_unify_compose_preserves_runtime[OF tuc acc_range_rt_init[OF ng] recTy_rt_init[OF ng]
                                                   scrutTy_rt_init[OF ng]] .
  qed

  from "5.IH"[OF eq_n eq_names eq_fresh eq_next_init eq_recTy
                 tuc rec len_pats_fresh "5.prems"(2) s_idem
                 lo_le_init fresh_wk_init s_range_wk_init s_dom_flex
                 fresh_rt_init s_range_rt_init] have
    rec_compat: "dec_pattern_compatible_list env (map (apply_subst_to_dec_pattern accSubst') decPats)
                                                   (map (apply_subst accSubst') ?freshFieldTys)" and
    rec_mono: "?next_mv_init \<le> next_mv'" and
    rec_refine: "\<exists>T. accSubst' = compose_subst T s" and
    rec_factors_s: "subst_factors_through accSubst' s" and
    rec_factors_self: "subst_factors_through accSubst' accSubst'" and
    rec_range_wk: "\<forall>ty \<in> fmran' accSubst'.
                     is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty" and
    rec_dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}" and
    rec_range_rt: "ghost = NotGhost \<longrightarrow>
                     (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
    by simp_all

  obtain T_rec where T_rec: "accSubst' = compose_subst T_rec s"
    using rec_refine by blast

  \<comment> \<open>refine through accSubst. \<close>
  have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
    using compose_subst_chain_exists[OF try_unify_compose_compose_shape[OF tuc] rec_refine] .

  \<comment> \<open>factors through accSubst (transitive). \<close>
  have factors_acc: "subst_factors_through accSubst' accSubst"
    using subst_factors_through_compose[OF s_factors_acc T_rec] .

  \<comment> \<open>Compatibility: apply_subst accSubst' ?recTy = apply_subst accSubst' scrutTy. \<close>
  have eq_at_s: "apply_subst s ?recTy = apply_subst s scrutTy"
    using try_unify_compose_makes_equal[OF tuc] .
  have eq_at_acc': "apply_subst accSubst' ?recTy = apply_subst accSubst' scrutTy"
    using eq_at_s T_rec compose_subst_correct by presburger

  \<comment> \<open>apply_subst accSubst' ?recTy unfolds. \<close>
  have len_names_fresh: "length ?names = length ?freshFieldTys"
    by (simp add: tuple_field_names_def)
  have lhs_record_eq:
    "apply_subst accSubst' ?recTy
     = CoreTy_Record (zip ?names (map (apply_subst accSubst') ?freshFieldTys))"
  proof -
    have step1: "apply_subst accSubst' ?recTy
                  = CoreTy_Record (map (\<lambda>(name, ty). (name, apply_subst accSubst' ty))
                                       (zip ?names ?freshFieldTys))"
      by simp
    have step2: "map (\<lambda>(name, ty). (name, apply_subst accSubst' ty))
                     (zip ?names ?freshFieldTys)
                  = zip ?names (map (apply_subst accSubst') ?freshFieldTys)"
      using len_names_fresh by (metis zip_map2)
    show ?thesis using step1 step2 by simp
  qed
  have rhs_eq:
    "apply_subst accSubst' scrutTy
     = CoreTy_Record (zip ?names (map (apply_subst accSubst') ?freshFieldTys))"
    using eq_at_acc' lhs_record_eq by simp

  \<comment> \<open>length of decPats = length pats. \<close>
  have len_dec_pats: "length decPats = length pats"
    using decorate_pattern_list_length[OF rec len_pats_fresh] .
  have len_names: "length ?names = ?n"
    by (simp add: tuple_field_names_def)

  \<comment> \<open>The substituted dp = DP_Record (zip ?names (map (apply_subst_to_dec_pattern accSubst') decPats)). \<close>
  have substituted_dp:
    "apply_subst_to_dec_pattern accSubst' dp
     = DP_Record (zip ?names (map (apply_subst_to_dec_pattern accSubst') decPats))"
  proof -
    have step1: "apply_subst_to_dec_pattern accSubst' dp
                  = DP_Record (map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern accSubst' p))
                                   (zip ?names decPats))"
      using dp_eq by simp
    have step2: "map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern accSubst' p))
                     (zip ?names decPats)
                 = zip ?names (map (apply_subst_to_dec_pattern accSubst') decPats)"
      using len_names len_dec_pats
      by (simp add: zip_map2)
    show ?thesis using step1 step2 by simp
  qed

  \<comment> \<open>Compatibility: name lists match, list compat at field types. \<close>
  have map_fst_left:
    "map fst (zip ?names (map (apply_subst_to_dec_pattern accSubst') decPats)) = ?names"
    using len_names len_dec_pats by simp
  have map_fst_right:
    "map fst (zip ?names (map (apply_subst accSubst') ?freshFieldTys)) = ?names"
    using len_names by simp
  have map_snd_left:
    "map snd (zip ?names (map (apply_subst_to_dec_pattern accSubst') decPats))
     = map (apply_subst_to_dec_pattern accSubst') decPats"
    using len_names len_dec_pats by simp
  have map_snd_right:
    "map snd (zip ?names (map (apply_subst accSubst') ?freshFieldTys))
     = map (apply_subst accSubst') ?freshFieldTys"
    using len_names by simp
  have list_compat':
    "dec_pattern_compatible_list env
       (map snd (zip ?names (map (apply_subst_to_dec_pattern accSubst') decPats)))
       (map snd (zip ?names (map (apply_subst accSubst') ?freshFieldTys)))"
    using rec_compat map_snd_left map_snd_right by simp

  have compat:
    "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                (apply_subst accSubst' scrutTy)"
    unfolding substituted_dp rhs_eq
    using map_fst_left map_fst_right list_compat' by simp

  have mono: "next_mv \<le> next_mv'" using rec_mono by simp

  show ?case using compat mono refine factors_acc rec_factors_self rec_range_wk rec_dom_flex rec_range_rt by simp
next
  case (6 env elabEnv ghost loc userFlds scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Record. The user supplies a partial subset of fields; the recursive
      call typechecks those user fields against the corresponding declared types,
      and build_record_dec_patterns then reorders into declaration order, filling
      DP_Wildcard for omitted fields. \<close>
  from "6.prems"(1) have no_dup: "first_duplicate_name fst userFlds = None"
    by (auto split: option.splits)
  let ?e = "apply_subst accSubst scrutTy"
  from "6.prems"(1) no_dup obtain fieldTypes where
    e_record: "?e = CoreTy_Record fieldTypes"
    by (auto simp: Let_def split: CoreType.splits)
  from "6.prems"(1) no_dup e_record have
    no_unknown: "unknown_field_names fieldTypes userFlds = []"
    by (auto simp: Let_def split: list.splits)
  from "6.prems"(1) no_dup e_record no_unknown obtain decPats where
    rec: "decorate_pattern_list env elabEnv ghost (map snd userFlds)
            (user_field_types fieldTypes userFlds) accSubst next_mv
            = Inr (decPats, accSubst', next_mv')" and
    dp_eq: "dp = DP_Record (build_record_dec_patterns fieldTypes
                              (map fst userFlds) decPats)"
    by (auto simp: Let_def split: sum.splits)

  have len_user: "length (map snd userFlds) = length (user_field_types fieldTypes userFlds)"
    by (simp add: user_field_types_def)

  \<comment> \<open>Well-kindedness of apply_subst accSubst scrutTy = CoreTy_Record fieldTypes.
      Used both for IH well-kindedness premises and for distinctness of fieldTypes. \<close>
  let ?wkEnv = "extend_env_with_tyvars env ghost lo next_mv"
  have e_wk: "is_well_kinded ?wkEnv ?e"
    using apply_subst_preserves_well_kinded_same_env[OF "6.prems"(5) "6.prems"(6)] .
  have ft_wk: "is_well_kinded ?wkEnv (CoreTy_Record fieldTypes)"
    using e_wk e_record by simp
  have ft_distinct: "distinct (map fst fieldTypes)"
    using ft_wk by simp
  have ft_snd_wk: "list_all (is_well_kinded ?wkEnv) (map snd fieldTypes)"
    using ft_wk by simp

  \<comment> \<open>user_field_types extracts a sublist of (substituted) field types via map_of.
      All entries are well-kinded under ?wkEnv. \<close>
  have ufts_wk: "list_all (is_well_kinded ?wkEnv) (user_field_types fieldTypes userFlds)"
  proof -
    have all: "\<forall>j < length userFlds. is_well_kinded ?wkEnv (user_field_types fieldTypes userFlds ! j)"
    proof (intro allI impI)
      fix j assume j_bound: "j < length userFlds"
      let ?nm = "fst (userFlds ! j)"
      have nm_in: "?nm \<in> set (map fst userFlds)"
        using j_bound by simp
      have "filter (\<lambda>n. map_of fieldTypes n = None) (map fst userFlds) = []"
        using no_unknown unfolding unknown_field_names_def by simp
      hence "\<forall>n \<in> set (map fst userFlds). map_of fieldTypes n \<noteq> None"
        by (auto simp: filter_empty_conv)
      hence "map_of fieldTypes ?nm \<noteq> None" using nm_in by auto
      then obtain ty_j where look_j: "map_of fieldTypes ?nm = Some ty_j" by auto
      have ty_j_in: "ty_j \<in> set (map snd fieldTypes)"
        using look_j by (metis in_set_zipE map_of_SomeD zip_map_fst_snd)
      have ty_j_wk: "is_well_kinded ?wkEnv ty_j"
        using ft_snd_wk ty_j_in by (metis all_nth_imp_all_set list_all_length)
      have ufts_j: "user_field_types fieldTypes userFlds ! j = ty_j"
        unfolding user_field_types_def using j_bound look_j
        by (simp add: case_prod_unfold)
      show "is_well_kinded ?wkEnv (user_field_types fieldTypes userFlds ! j)"
        using ufts_j ty_j_wk by simp
    qed
    have len_ufts: "length (user_field_types fieldTypes userFlds) = length userFlds"
      unfolding user_field_types_def by simp
    show ?thesis using all by (simp add: list_all_length len_ufts)
  qed

  \<comment> \<open>Runtime-type version of ufts_wk: each user-field type is runtime under ?wkEnv
      when ghost = NotGhost. Parallel structure to ufts_wk above. \<close>
  have ufts_rt:
    "ghost = NotGhost \<Longrightarrow> list_all (is_runtime_type ?wkEnv) (user_field_types fieldTypes userFlds)"
  proof -
    assume ng: "ghost = NotGhost"
    have e_rt: "is_runtime_type ?wkEnv ?e"
      using "6.prems"(8,9) apply_subst_preserves_runtime_same_env ng by blast
    have ft_rt: "is_runtime_type ?wkEnv (CoreTy_Record fieldTypes)"
      using e_rt e_record by simp
    have ft_snd_rt: "list_all (is_runtime_type ?wkEnv) (map snd fieldTypes)"
      using ft_rt by simp

    have all: "\<forall>j < length userFlds. is_runtime_type ?wkEnv (user_field_types fieldTypes userFlds ! j)"
    proof (intro allI impI)
      fix j assume j_bound: "j < length userFlds"
      let ?nm = "fst (userFlds ! j)"
      have nm_in: "?nm \<in> set (map fst userFlds)"
        using j_bound by simp
      have "filter (\<lambda>n. map_of fieldTypes n = None) (map fst userFlds) = []"
        using no_unknown unfolding unknown_field_names_def by simp
      hence "\<forall>n \<in> set (map fst userFlds). map_of fieldTypes n \<noteq> None"
        by (auto simp: filter_empty_conv)
      hence "map_of fieldTypes ?nm \<noteq> None" using nm_in by auto
      then obtain ty_j where look_j: "map_of fieldTypes ?nm = Some ty_j" by auto
      have ty_j_in: "ty_j \<in> set (map snd fieldTypes)"
        using look_j by (metis in_set_zipE map_of_SomeD zip_map_fst_snd)
      have ty_j_rt: "is_runtime_type ?wkEnv ty_j"
        using ft_snd_rt ty_j_in by (metis all_nth_imp_all_set list_all_length)
      have ufts_j: "user_field_types fieldTypes userFlds ! j = ty_j"
        unfolding user_field_types_def using j_bound look_j
        by (simp add: case_prod_unfold)
      show "is_runtime_type ?wkEnv (user_field_types fieldTypes userFlds ! j)"
        using ufts_j ty_j_rt by simp
    qed
    have len_ufts: "length (user_field_types fieldTypes userFlds) = length userFlds"
      unfolding user_field_types_def by simp
    show "list_all (is_runtime_type ?wkEnv) (user_field_types fieldTypes userFlds)"
      using all by (simp add: list_all_length len_ufts)
  qed

  \<comment> \<open>Apply IH to the recursive call. \<close>
  have e_let: "?e = ?e" by simp
  from "6.IH"[OF no_dup e_let e_record no_unknown rec
                 len_user "6.prems"(2) "6.prems"(3)
                 "6.prems"(4) ufts_wk "6.prems"(6) "6.prems"(7)
                 ufts_rt "6.prems"(9)] have
    rec_compat: "dec_pattern_compatible_list env (map (apply_subst_to_dec_pattern accSubst') decPats)
                                                 (map (apply_subst accSubst') (user_field_types fieldTypes userFlds))" and
    rec_mono: "next_mv \<le> next_mv'" and
    rec_refine: "\<exists>T. accSubst' = compose_subst T accSubst" and
    rec_factors_acc: "subst_factors_through accSubst' accSubst" and
    rec_factors_self: "subst_factors_through accSubst' accSubst'" and
    rec_range_wk: "\<forall>ty \<in> fmran' accSubst'.
                     is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty" and
    rec_dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}" and
    rec_range_rt: "ghost = NotGhost \<longrightarrow>
                     (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
    by simp_all

  obtain T_rec where T_rec: "accSubst' = compose_subst T_rec accSubst"
    using rec_refine by blast

  have len_dec_pats: "length decPats = length userFlds"
    using decorate_pattern_list_length[OF rec] by (simp add: user_field_types_def)

  \<comment> \<open>accSubst is idempotent (premise 3 of the outer lemma). \<close>
  have acc_idem: "\<And>ty. apply_subst accSubst (apply_subst accSubst ty) = apply_subst accSubst ty"
    using "6.prems"(3) unfolding subst_factors_through_def by simp

  \<comment> \<open>The substituted scrutTy unfolds to a record with substituted field types. \<close>
  have scrut_at_acc'_eq:
    "apply_subst accSubst' scrutTy
     = CoreTy_Record (map (\<lambda>(name, ty). (name, apply_subst accSubst' ty)) fieldTypes)"
  proof -
    have step1: "apply_subst accSubst' scrutTy = apply_subst T_rec (apply_subst accSubst scrutTy)"
      using T_rec by (simp add: compose_subst_correct)
    have step2: "apply_subst accSubst' (CoreTy_Record fieldTypes)
                  = CoreTy_Record (map (\<lambda>(name, ty). (name, apply_subst accSubst' ty)) fieldTypes)"
      by simp
    have step3: "apply_subst T_rec (apply_subst accSubst (CoreTy_Record fieldTypes))
                  = apply_subst accSubst' (CoreTy_Record fieldTypes)"
      using T_rec compose_subst_correct by auto
    have idem_rec:
      "apply_subst accSubst (CoreTy_Record fieldTypes) = CoreTy_Record fieldTypes"
      using acc_idem[of scrutTy] e_record by simp
    show ?thesis
      using step1 step2 step3 idem_rec e_record by argo
  qed

  \<comment> \<open>Substituted dp = DP_Record over the build_record_dec_patterns output, fields substituted. \<close>
  let ?builtFlds = "build_record_dec_patterns fieldTypes (map fst userFlds) decPats"
  let ?substBuiltFlds = "map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern accSubst' p)) ?builtFlds"
  let ?substFieldTypes = "map (\<lambda>(name, ty). (name, apply_subst accSubst' ty)) fieldTypes"
  have dp_subst_eq:
    "apply_subst_to_dec_pattern accSubst' dp = DP_Record ?substBuiltFlds"
    using dp_eq by simp

  \<comment> \<open>Names of substituted built flds = names of fieldTypes. \<close>
  have map_fst_built: "map fst ?builtFlds = map fst fieldTypes"
    unfolding build_record_dec_patterns_def Let_def by (induction fieldTypes) auto
  have map_fst_subst_built: "map fst ?substBuiltFlds = map fst ?builtFlds"
    by (induction ?builtFlds) auto
  have map_fst_subst_ft: "map fst ?substFieldTypes = map fst fieldTypes"
    by (induction fieldTypes) auto
  have names_match: "map fst ?substBuiltFlds = map fst ?substFieldTypes"
    using map_fst_built map_fst_subst_built map_fst_subst_ft by simp

  \<comment> \<open>Lengths line up. \<close>
  have len_built: "length ?builtFlds = length fieldTypes"
    unfolding build_record_dec_patterns_def Let_def by simp
  have len_subst_built: "length ?substBuiltFlds = length fieldTypes"
    using len_built by simp
  have len_subst_ft: "length ?substFieldTypes = length fieldTypes"
    by simp

  \<comment> \<open>Distinct user-supplied names (from the no-duplicate check). \<close>
  have user_distinct: "distinct (map fst userFlds)"
    using no_dup by (rule first_duplicate_name_None_implies_distinct)

  \<comment> \<open>Every user field name occurs in fieldTypes. \<close>
  have user_in_field: "\<forall>n \<in> set (map fst userFlds). n \<in> set (map fst fieldTypes)"
  proof -
    have "filter (\<lambda>n. map_of fieldTypes n = None) (map fst userFlds) = []"
      using no_unknown unfolding unknown_field_names_def by simp
    hence "\<forall>n \<in> set (map fst userFlds). map_of fieldTypes n \<noteq> None"
      by (auto simp: filter_empty_conv)
    thus ?thesis by (simp add: map_of_eq_None_iff)
  qed

  \<comment> \<open>For each i in fieldTypes, the i-th built pattern is compatible with the i-th field type
      (after substitution). \<close>
  have pointwise:
    "\<forall>i < length fieldTypes.
       dec_pattern_compatible env (snd (?substBuiltFlds ! i)) (snd (?substFieldTypes ! i))"
  proof (intro allI impI)
    fix i assume i_bound: "i < length fieldTypes"
    let ?fi_name = "fst (fieldTypes ! i)"
    let ?fi_ty = "snd (fieldTypes ! i)"
    let ?userMap = "zip (map fst userFlds) decPats"

    have built_ith:
      "?builtFlds ! i = (?fi_name, lookup_or_wildcard ?userMap ?fi_name)"
      unfolding build_record_dec_patterns_def Let_def using i_bound
      by (simp add: case_prod_unfold)
    have subst_built_ith:
      "?substBuiltFlds ! i
        = (?fi_name, apply_subst_to_dec_pattern accSubst'
                       (lookup_or_wildcard ?userMap ?fi_name))"
      using built_ith len_built i_bound by simp
    have subst_ft_ith:
      "?substFieldTypes ! i = (?fi_name, apply_subst accSubst' ?fi_ty)"
      using i_bound by (simp add: case_prod_unfold)

    show "dec_pattern_compatible env (snd (?substBuiltFlds ! i)) (snd (?substFieldTypes ! i))"
    proof (cases "?fi_name \<in> set (map fst userFlds)")
      case True
      \<comment> \<open>User supplied this field. Use IH at the user's index. \<close>
      then obtain j where j_bound: "j < length userFlds" and j_eq: "map fst userFlds ! j = ?fi_name"
        by (metis in_set_conv_nth length_map)
      have user_j_name: "fst (userFlds ! j) = ?fi_name"
        using j_eq j_bound by simp

      \<comment> \<open>Look up the user's name in the userMap = the j-th decPat. \<close>
      have len_userMap: "length ?userMap = length userFlds"
        using len_dec_pats by simp
      have userMap_j: "?userMap ! j = (?fi_name, decPats ! j)"
        using j_bound j_eq len_dec_pats by simp
      have map_of_userMap:
        "map_of ?userMap ?fi_name = Some (decPats ! j)"
        using user_distinct j_bound j_eq len_dec_pats
        by (metis (no_types) length_map map_of_zip_nth)
      have lookup_eq:
        "lookup_or_wildcard ?userMap ?fi_name = decPats ! j"
        unfolding lookup_or_wildcard_def using map_of_userMap by simp

      \<comment> \<open>The user-supplied type at position j equals ?fi_ty. Distinctness of
          fieldTypes (derived above from well-kindedness of apply_subst accSubst scrutTy)
          identifies the j-th map_of result with the i-th positional entry. \<close>
      have ft_zip: "fieldTypes = zip (map fst fieldTypes) (map snd fieldTypes)"
        by (induction fieldTypes) auto
      have map_of_ft: "map_of fieldTypes ?fi_name = Some ?fi_ty"
      proof -
        have len_eq: "length (map fst fieldTypes) = length (map snd fieldTypes)" by simp
        have name_at_i: "(map fst fieldTypes) ! i = ?fi_name"
          using i_bound by simp
        have ty_at_i: "(map snd fieldTypes) ! i = ?fi_ty"
          using i_bound by simp
        have "map_of (zip (map fst fieldTypes) (map snd fieldTypes)) ?fi_name
                = Some ?fi_ty"
          using ft_distinct len_eq i_bound name_at_i ty_at_i
          by (metis length_map map_of_zip_nth)
        thus ?thesis using ft_zip by simp
      qed

      have ufts_j: "user_field_types fieldTypes userFlds ! j = ?fi_ty"
        unfolding user_field_types_def
        using j_bound user_j_name map_of_ft
        by (simp add: case_prod_unfold)

      \<comment> \<open>From IH (rec_compat) at index j, decPat j is compatible with the user's expected type. \<close>
      have len_ih_lhs: "length (map (apply_subst_to_dec_pattern accSubst') decPats) = length decPats"
        by simp
      have len_ih_rhs:
        "length (map (apply_subst accSubst') (user_field_types fieldTypes userFlds))
         = length userFlds"
        unfolding user_field_types_def by simp
      have len_decPats_userFlds: "length decPats = length userFlds"
        using len_dec_pats .
      have ih_at_j:
        "dec_pattern_compatible env
          (apply_subst_to_dec_pattern accSubst' (decPats ! j))
          (apply_subst accSubst' (user_field_types fieldTypes userFlds ! j))"
        using rec_compat dec_pattern_compatible_list_iff[of env
                "map (apply_subst_to_dec_pattern accSubst') decPats"
                "map (apply_subst accSubst') (user_field_types fieldTypes userFlds)"]
              j_bound len_decPats_userFlds len_ih_rhs
        by force
      hence ih_at_j':
        "dec_pattern_compatible env
          (apply_subst_to_dec_pattern accSubst' (decPats ! j))
          (apply_subst accSubst' ?fi_ty)"
        using ufts_j by simp

      have lhs_unfold:
        "snd (?substBuiltFlds ! i)
          = apply_subst_to_dec_pattern accSubst' (decPats ! j)"
        using subst_built_ith lookup_eq by simp
      have rhs_unfold:
        "snd (?substFieldTypes ! i) = apply_subst accSubst' ?fi_ty"
        using subst_ft_ith by simp

      show ?thesis using ih_at_j' lhs_unfold rhs_unfold by simp
    next
      case False
      \<comment> \<open>User did NOT supply this field. lookup_or_wildcard returns DP_Wildcard. \<close>
      have map_of_userMap_None: "map_of ?userMap ?fi_name = None"
      proof -
        have "map_of ?userMap ?fi_name = None
              \<longleftrightarrow> ?fi_name \<notin> set (map fst ?userMap)"
          by (auto simp: map_of_eq_None_iff)
        moreover have "set (map fst ?userMap) = set (map fst userFlds)"
          using len_dec_pats by (simp add: set_zip_leftD subsetI subset_antisym)
        ultimately show ?thesis using False by simp
      qed
      have lookup_wild: "lookup_or_wildcard ?userMap ?fi_name = DP_Wildcard"
        unfolding lookup_or_wildcard_def using map_of_userMap_None by simp

      have lhs_wild: "snd (?substBuiltFlds ! i) = DP_Wildcard"
        using subst_built_ith lookup_wild by simp

      show ?thesis using lhs_wild by simp
    qed
  qed

  \<comment> \<open>Lengths and pointwise compat \<Longrightarrow> list compat. \<close>
  have map_snd_subst_built_len: "length (map snd ?substBuiltFlds) = length fieldTypes"
    using len_subst_built by simp
  have map_snd_subst_ft_len: "length (map snd ?substFieldTypes) = length fieldTypes"
    by simp
  have list_compat:
    "dec_pattern_compatible_list env (map snd ?substBuiltFlds) (map snd ?substFieldTypes)"
    using pointwise len_subst_built len_subst_ft
    by (simp add: dec_pattern_compatible_list_iff)

  have compat:
    "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                (apply_subst accSubst' scrutTy)"
    unfolding dp_subst_eq scrut_at_acc'_eq
    using names_match list_compat by simp

  show ?case using compat rec_mono rec_refine rec_factors_acc rec_factors_self rec_range_wk rec_dom_flex rec_range_rt by simp
next
  case (7 env elabEnv ghost loc ctorName optPayload scrutTy accSubst next_mv)
  \<comment> \<open>BabPat_Variant. \<close>
  from "7.prems"(1) obtain dtName tyvars payloadTy isNullary where
    rpc: "resolve_pattern_ctor env elabEnv ghost loc ctorName
            = Inr (dtName, tyvars, payloadTy, isNullary)"
    by (auto split: sum.splits)
  let ?freshTyArgs = "mv_block next_mv (next_mv + length tyvars)"
  let ?next_mv_init = "next_mv + length tyvars"
  let ?dtTy = "CoreTy_Datatype dtName ?freshTyArgs"
  from "7.prems"(1) rpc obtain s where
    tuc: "try_unify_compose env ?dtTy scrutTy accSubst = Some s"
    by (auto simp: Let_def split: option.splits)
  from "7.prems"(1) rpc tuc obtain res where
    chk: "check_payload_presence loc ctorName isNullary optPayload = Inr res"
    by (auto simp: Let_def split: sum.splits)

  have ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)"
    using rpc unfolding resolve_pattern_ctor_def
    by (auto split: option.splits if_splits)

  \<comment> \<open>s is idempotent and factors through accSubst. \<close>
  have s_idem: "subst_factors_through s s"
    using try_unify_compose_idem[OF tuc "7.prems"(3)] .
  have s_factors_acc: "subst_factors_through s accSubst"
    using try_unify_compose_factors_through[OF tuc "7.prems"(3)] .
  have s_compose_shape: "\<exists>T. s = compose_subst T accSubst"
    using try_unify_compose_compose_shape[OF tuc] .

  \<comment> \<open>Equality at s lifted to equality at any later substitution. \<close>
  have eq_at_s: "apply_subst s ?dtTy = apply_subst s scrutTy"
    using try_unify_compose_makes_equal[OF tuc] .

  \<comment> \<open>Well-kindedness of payloadTy under env (well-formed env), in the
      abstract-types-aware shape; its tyvars are within the abstract types and tyvars. \<close>
  have payload_wk:
    "is_well_kinded (env\<lparr>TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars\<rparr>) payloadTy"
    using "7.prems"(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by force
  have payload_tyvars: "type_tyvars payloadTy \<subseteq> fset (TE_AbstractTypes env) \<union> set tyvars"
    using is_well_kinded_type_tyvars_subset[OF payload_wk]
    by (simp add: fset_of_list.rep_eq sup_commute)
  have tyvars_distinct: "distinct tyvars"
    using "7.prems"(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def by force
  have len_freshTyArgs: "length ?freshTyArgs = length tyvars" by simp

  \<comment> \<open>The datatype's arity in env equals length tyvars (consistency). \<close>
  have dt_consistent: "fmlookup (TE_Datatypes env) dtName = Some (length tyvars)"
    using "7.prems"(2) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_ctors_consistent_def by force

  \<comment> \<open>Well-kindedness preliminaries for the IH. \<close>
  let ?wkEnv = "extend_env_with_tyvars env ghost lo next_mv"
  let ?wkEnv_init = "extend_env_with_tyvars env ghost lo ?next_mv_init"
  \<comment> \<open>?wkEnv_init is well-formed (extension of a well-formed env), and inherits env's
      abstract types, which are within its TE_TypeVars (needed for the specialization
      lemmas in the abstract-types-aware shape). \<close>
  have wkEnv_init_wf: "tyenv_well_formed ?wkEnv_init"
    using "7.prems"(2) tyenv_well_formed_extend_env_with_tyvars by blast
  have abs_sub_init: "TE_AbstractTypes ?wkEnv_init |\<subseteq>| TE_TypeVars ?wkEnv_init"
    using wkEnv_init_wf unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
  have lo_le_init: "lo \<le> ?next_mv_init" using "7.prems"(4) by simp
  have lo_le_next_mv: "lo \<le> next_mv" using "7.prems"(4) .
  have next_mv_le_init: "next_mv \<le> ?next_mv_init" by simp

  \<comment> \<open>Each fresh tyvar is well-kinded under wkEnv_init. \<close>
  have fresh_wk_init: "list_all (is_well_kinded ?wkEnv_init) ?freshTyArgs"
  proof -
    have "\<forall>k \<in> set [next_mv ..< ?next_mv_init].
            is_well_kinded ?wkEnv_init (CoreTy_Var (mv_name k))"
    proof
      fix k assume k_in: "k \<in> set [next_mv ..< ?next_mv_init]"
      hence "lo \<le> k \<and> k < ?next_mv_init" using lo_le_next_mv by auto
      hence "mv_name k |\<in>| mv_fset lo ?next_mv_init" by auto
      hence "mv_name k |\<in>| TE_TypeVars ?wkEnv_init"
        unfolding extend_env_with_tyvars_def by simp
      thus "is_well_kinded ?wkEnv_init (CoreTy_Var (mv_name k))" by simp
    qed
    thus ?thesis by (simp add: mv_block_eq_map_CoreTy_Var list_all_iff)
  qed

  \<comment> \<open>?dtTy is well-kinded under wkEnv_init: dtName has the right arity, and freshTyArgs
      are all well-kinded. \<close>
  have dt_consistent_wkEnv:
    "fmlookup (TE_Datatypes ?wkEnv_init) dtName = Some (length tyvars)"
    using dt_consistent unfolding extend_env_with_tyvars_def by simp
  have dtTy_wk_init: "is_well_kinded ?wkEnv_init ?dtTy"
    using dt_consistent_wkEnv fresh_wk_init len_freshTyArgs by simp

  \<comment> \<open>scrutTy is well-kinded under wkEnv (premise) and hence under wkEnv_init. \<close>
  have scrutTy_wk_init: "is_well_kinded ?wkEnv_init scrutTy"
    using is_well_kinded_extend_env_with_tyvars_mono[OF "7.prems"(5) order_refl next_mv_le_init] .

  \<comment> \<open>accSubst's range is well-kinded under wkEnv_init. \<close>
  have acc_range_wk_init: "\<forall>ty \<in> fmran' accSubst. is_well_kinded ?wkEnv_init ty"
    using "7.prems"(6) is_well_kinded_extend_env_with_tyvars_mono[OF _ order_refl next_mv_le_init]
    by blast

  \<comment> \<open>s's range is well-kinded under wkEnv_init. \<close>
  have s_range_wk_init: "\<forall>ty \<in> fmran' s. is_well_kinded ?wkEnv_init ty"
    using try_unify_compose_preserves_well_kinded[OF tuc acc_range_wk_init dtTy_wk_init scrutTy_wk_init] .

  \<comment> \<open>s's domain remains flex. \<close>
  have s_dom_flex: "fmdom s |\<inter>| TE_TypeVars env = {||}"
    using try_unify_compose_dom_flex[OF tuc "7.prems"(7)] .

  \<comment> \<open>Runtime variants of fresh_wk_init / dtTy_wk_init / scrutTy_wk_init / acc_range_wk_init / s_range_wk_init.
      Ghost-conditional. \<close>
  have fresh_rt_init: "ghost = NotGhost \<Longrightarrow> list_all (is_runtime_type ?wkEnv_init) ?freshTyArgs"
  proof -
    assume ng: "ghost = NotGhost"
    have "\<forall>k \<in> set [next_mv ..< ?next_mv_init].
            is_runtime_type ?wkEnv_init (CoreTy_Var (mv_name k))"
    proof
      fix k assume k_in: "k \<in> set [next_mv ..< ?next_mv_init]"
      hence "lo \<le> k \<and> k < ?next_mv_init" using lo_le_next_mv by auto
      hence "mv_name k |\<in>| mv_fset lo ?next_mv_init" by auto
      hence "mv_name k |\<in>| TE_RuntimeTypeVars ?wkEnv_init"
        unfolding extend_env_with_tyvars_def using ng by simp
      thus "is_runtime_type ?wkEnv_init (CoreTy_Var (mv_name k))" by simp
    qed
    thus ?thesis by (simp add: mv_block_eq_map_CoreTy_Var list_all_iff)
  qed

  \<comment> \<open>?dtTy is runtime under wkEnv_init: dtName is not a ghost datatype (resolve_pattern_ctor enforces),
      and freshTyArgs are all runtime in NotGhost context. \<close>
  have dtTy_rt_init: "ghost = NotGhost \<Longrightarrow> is_runtime_type ?wkEnv_init ?dtTy"
  proof -
    assume ng: "ghost = NotGhost"
    have not_ghost: "dtName |\<notin>| TE_GhostDatatypes env"
      using rpc unfolding resolve_pattern_ctor_def
      using ng by (auto split: option.splits if_splits)
    have not_ghost_wkEnv: "dtName |\<notin>| TE_GhostDatatypes ?wkEnv_init"
      using not_ghost unfolding extend_env_with_tyvars_def by simp
    have args_rt: "list_all (is_runtime_type ?wkEnv_init) ?freshTyArgs"
      using fresh_rt_init[OF ng] .
    show "is_runtime_type ?wkEnv_init ?dtTy"
      using not_ghost_wkEnv args_rt by simp
  qed

  have scrutTy_rt_init: "ghost = NotGhost \<Longrightarrow> is_runtime_type ?wkEnv_init scrutTy"
    using "7.prems"(8) is_runtime_type_extend_env_with_tyvars_mono[OF _ order_refl next_mv_le_init]
    by blast
  have acc_range_rt_init:
    "ghost = NotGhost \<Longrightarrow> \<forall>ty \<in> fmran' accSubst. is_runtime_type ?wkEnv_init ty"
    using "7.prems"(9) is_runtime_type_extend_env_with_tyvars_mono[OF _ order_refl next_mv_le_init]
    by blast
  have s_range_rt_init: "ghost = NotGhost \<Longrightarrow> \<forall>ty \<in> fmran' s. is_runtime_type ?wkEnv_init ty"
  proof -
    assume ng: "ghost = NotGhost"
    show "\<forall>ty \<in> fmran' s. is_runtime_type ?wkEnv_init ty"
      using try_unify_compose_preserves_runtime[OF tuc acc_range_rt_init[OF ng] dtTy_rt_init[OF ng]
                                                   scrutTy_rt_init[OF ng]] .
  qed

  show ?case
  proof (cases res)
    case None
    from "7.prems"(1) rpc tuc chk None have eqs:
      "dp = DP_Variant ctorName None" "accSubst' = s" "next_mv' = ?next_mv_init"
      by (auto simp: Let_def)

    \<comment> \<open>Compatibility for the nullary variant. \<close>
    have lhs_dp:
      "apply_subst_to_dec_pattern accSubst' dp = DP_Variant ctorName None"
      using eqs by simp
    have eq_at_acc':
      "apply_subst accSubst' ?dtTy = apply_subst accSubst' scrutTy"
      using eq_at_s eqs by simp
    have rhs_eq:
      "apply_subst accSubst' scrutTy
       = CoreTy_Datatype dtName (map (apply_subst accSubst') ?freshTyArgs)"
      using eq_at_acc' by simp
    have len_args_subst:
      "length (map (apply_subst accSubst') ?freshTyArgs) = length tyvars"
      using len_freshTyArgs by simp
    have compat:
      "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                  (apply_subst accSubst' scrutTy)"
      unfolding lhs_dp rhs_eq
      using ctor_lookup len_args_subst by simp

    have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
      using s_compose_shape eqs by simp
    have factors_acc: "subst_factors_through accSubst' accSubst"
      using s_factors_acc eqs by simp
    have factors_self: "subst_factors_through accSubst' accSubst'"
      using s_idem eqs by simp
    have mono: "next_mv \<le> next_mv'" using eqs by simp
    have range_wk_at_next': "\<forall>ty \<in> fmran' accSubst'.
                                is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty"
      using s_range_wk_init eqs by simp
    have dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}"
      using s_dom_flex eqs by simp
    have range_rt: "ghost = NotGhost \<longrightarrow>
                      (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
      using s_range_rt_init eqs by simp
    show ?thesis using compat refine factors_acc factors_self mono range_wk_at_next' dom_flex range_rt by simp
  next
    case (Some inner_pat)
    let ?tyvarSubst = "fmap_of_list (zip tyvars ?freshTyArgs)"
    let ?instPayloadTy = "apply_subst ?tyvarSubst payloadTy"
    from "7.prems"(1) rpc tuc chk Some obtain dp_inner s' mv' where
      rec: "decorate_pattern env elabEnv ghost inner_pat ?instPayloadTy s ?next_mv_init
              = Inr (dp_inner, s', mv')" and
      eqs: "dp = DP_Variant ctorName (Some dp_inner)"
           "accSubst' = s'" "next_mv' = mv'"
      by (auto simp: Let_def split: sum.splits)

    \<comment> \<open>instPayloadTy is runtime under wkEnv_init when ghost = NotGhost.
        Uses tyenv_nonghost_payloads_runtime + apply_subst_specializes_runtime. \<close>
    have instPayloadTy_rt_init:
      "ghost = NotGhost \<Longrightarrow> is_runtime_type ?wkEnv_init ?instPayloadTy"
    proof -
      assume ng: "ghost = NotGhost"
      have not_ghost: "dtName |\<notin>| TE_GhostDatatypes ?wkEnv_init"
        using rpc unfolding resolve_pattern_ctor_def extend_env_with_tyvars_def
        using ng by (auto split: option.splits if_splits)
      have ctor_lookup_init:
        "fmlookup (TE_DataCtors ?wkEnv_init) ctorName = Some (dtName, tyvars, payloadTy)"
        using ctor_lookup unfolding extend_env_with_tyvars_def by simp
      \<comment> \<open>Extract the payload's runtime-ness directly in ?wkEnv_init, in the
          abstract-types-aware shape. \<close>
      have payload_rt_wkEnv:
        "is_runtime_type (?wkEnv_init \<lparr>TE_TypeVars := TE_AbstractTypes ?wkEnv_init |\<union>| fset_of_list tyvars,
              TE_RuntimeTypeVars := (TE_AbstractTypes ?wkEnv_init |\<inter>| TE_RuntimeTypeVars ?wkEnv_init)
                                     |\<union>| fset_of_list tyvars\<rparr>) payloadTy"
        using wkEnv_init_wf ctor_lookup_init not_ghost
        unfolding tyenv_well_formed_def tyenv_nonghost_payloads_runtime_def by force
      show "is_runtime_type ?wkEnv_init ?instPayloadTy"
        using apply_subst_specializes_runtime[OF payload_rt_wkEnv fresh_rt_init[OF ng] len_freshTyArgs[symmetric]]
        by simp
    qed

    \<comment> \<open>instPayloadTy is well-kinded under wkEnv_init: payload is well-kinded under
        env\<lparr>TE_TypeVars := fset_of_list tyvars\<rparr>, the substitution maps tyvars to
        freshTyArgs (each well-kinded under wkEnv_init), via apply_subst_specializes. \<close>
    have instPayloadTy_wk_init:
      "is_well_kinded ?wkEnv_init ?instPayloadTy"
    proof -
      have ctor_lookup_init:
        "fmlookup (TE_DataCtors ?wkEnv_init) ctorName = Some (dtName, tyvars, payloadTy)"
        using ctor_lookup unfolding extend_env_with_tyvars_def by simp
      \<comment> \<open>Extract the payload's well-kindedness directly in ?wkEnv_init, in the
          abstract-types-aware shape. \<close>
      have payload_wk_wkEnv_init:
        "is_well_kinded (?wkEnv_init \<lparr> TE_TypeVars := TE_AbstractTypes ?wkEnv_init |\<union>| fset_of_list tyvars \<rparr>) payloadTy"
        using wkEnv_init_wf ctor_lookup_init
        unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by force
      have fresh_wk_list:
        "list_all (is_well_kinded ?wkEnv_init) ?freshTyArgs"
        using fresh_wk_init .
      show ?thesis
        using apply_subst_specializes_well_kinded[OF payload_wk_wkEnv_init fresh_wk_list
                len_freshTyArgs[symmetric] abs_sub_init] .
    qed

    \<comment> \<open>Apply IH to the recursive call. \<close>
    have b_eq: "(dtName, tyvars, payloadTy, isNullary) = (dtName, tyvars, payloadTy, isNullary)" by simp
    have y_eq: "(tyvars, payloadTy, isNullary) = (tyvars, payloadTy, isNullary)" by simp
    have ya_eq: "(payloadTy, isNullary) = (payloadTy, isNullary)" by simp
    from "7.IH"(1)[OF rpc b_eq y_eq ya_eq refl refl refl tuc chk Some refl refl rec
                       "7.prems"(2) s_idem
                       lo_le_init instPayloadTy_wk_init s_range_wk_init s_dom_flex
                       instPayloadTy_rt_init s_range_rt_init]
    have
      inner_compat: "dec_pattern_compatible env
                       (apply_subst_to_dec_pattern accSubst' dp_inner)
                       (apply_subst accSubst' ?instPayloadTy)" and
      inner_mono: "?next_mv_init \<le> next_mv'" and
      inner_refine: "\<exists>T. accSubst' = compose_subst T s" and
      inner_factors_s: "subst_factors_through accSubst' s" and
      inner_factors_self: "subst_factors_through accSubst' accSubst'" and
      inner_range_wk: "\<forall>ty \<in> fmran' accSubst'.
                         is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty" and
      inner_dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}" and
      inner_range_rt: "ghost = NotGhost \<longrightarrow>
                         (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
      using eqs by simp_all

    obtain T_rec where T_rec: "accSubst' = compose_subst T_rec s"
      using inner_refine by blast

    have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
      using compose_subst_chain_exists[OF s_compose_shape inner_refine] .
    have factors_acc: "subst_factors_through accSubst' accSubst"
      using subst_factors_through_compose[OF s_factors_acc T_rec] .

    \<comment> \<open>Lift the variant unification equality to accSubst'. \<close>
    have eq_at_acc':
      "apply_subst accSubst' ?dtTy = apply_subst accSubst' scrutTy"
      using eq_at_s T_rec compose_subst_correct by presburger
    have rhs_eq:
      "apply_subst accSubst' scrutTy
       = CoreTy_Datatype dtName (map (apply_subst accSubst') ?freshTyArgs)"
      using eq_at_acc' by simp
    have len_args_subst:
      "length (map (apply_subst accSubst') ?freshTyArgs) = length tyvars"
      using len_freshTyArgs by simp

    \<comment> \<open>Rewrite the substituted payload type using the capture-avoiding compose lemma.
        accSubst' is flex (its domain is disjoint from env's type variables, hence from
        the abstract types), so it leaves the payload's abstract-type vars untouched. \<close>
    have accSubst'_dom_flex: "\<And>n. n |\<in>| fmdom accSubst' \<Longrightarrow> n |\<notin>| TE_TypeVars env"
      using inner_dom_flex by auto
    have abs_no_subst': "\<And>n. n |\<in>| TE_AbstractTypes env \<Longrightarrow> fmlookup accSubst' n = None"
    proof -
      fix n assume "n |\<in>| TE_AbstractTypes env"
      hence "n |\<in>| TE_TypeVars env"
        using "7.prems"(2) unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
      with accSubst'_dom_flex have "n |\<notin>| fmdom accSubst'" by blast
      thus "fmlookup accSubst' n = None" by (simp add: fmdom_notD)
    qed
    have payload_tyvars_ok:
      "\<And>n. n \<in> type_tyvars payloadTy \<Longrightarrow> n \<in> set tyvars \<or> n |\<notin>| fmdom accSubst'"
    proof -
      fix n assume ni: "n \<in> type_tyvars payloadTy"
      with payload_tyvars have "n |\<in>| TE_AbstractTypes env \<or> n \<in> set tyvars"
        by auto
      thus "n \<in> set tyvars \<or> n |\<notin>| fmdom accSubst'"
        using abs_no_subst' by (auto simp: fmdom_notI)
    qed
    have rewrite:
      "apply_subst accSubst' (apply_subst (fmap_of_list (zip tyvars ?freshTyArgs)) payloadTy)
       = apply_subst (fmap_of_list (zip tyvars (map (apply_subst accSubst') ?freshTyArgs))) payloadTy"
      using apply_subst_compose_zip_extra[OF len_freshTyArgs[symmetric] payload_tyvars_ok tyvars_distinct]
      by simp

    have inner_compat':
      "dec_pattern_compatible env
         (apply_subst_to_dec_pattern accSubst' dp_inner)
         (apply_subst (fmap_of_list (zip tyvars (map (apply_subst accSubst') ?freshTyArgs))) payloadTy)"
      using inner_compat rewrite by simp

    \<comment> \<open>Build the variant compatibility. \<close>
    have lhs_dp:
      "apply_subst_to_dec_pattern accSubst' dp
       = DP_Variant ctorName (Some (apply_subst_to_dec_pattern accSubst' dp_inner))"
      using eqs by simp
    have compat:
      "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                  (apply_subst accSubst' scrutTy)"
      unfolding lhs_dp rhs_eq
      using ctor_lookup len_args_subst inner_compat' by simp

    have mono: "next_mv \<le> next_mv'" using inner_mono by simp
    show ?thesis using compat refine factors_acc inner_factors_self mono inner_range_wk inner_dom_flex inner_range_rt by simp
  qed
next
  case (8 env elabEnv ghost tys accSubst next_mv)
  \<comment> \<open>decorate_pattern_list: empty. \<close>
  from "8.prems"(1) have eq:
    "dps = []" "accSubst' = accSubst" "next_mv' = next_mv"
    by simp_all
  from "8.prems"(2) eq have tys_eq: "tys = []" by (cases tys) auto
  have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
    by (metis compose_subst_empty_left eq(2))
  have range_wk: "\<forall>ty \<in> fmran' accSubst'.
                     is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty"
    using "8.prems"(7) eq by simp
  have dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}"
    using "8.prems"(8) eq by simp
  have range_rt: "ghost = NotGhost \<longrightarrow>
                     (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
    using "8.prems"(10) eq by simp
  show ?case
    using eq tys_eq refine "8.prems"(4) range_wk dom_flex range_rt by simp
next
  case (9 env elabEnv ghost p ps tys accSubst next_mv)
  \<comment> \<open>decorate_pattern_list: cons. \<close>
  from "9.prems"(2) obtain t tsRest where
    tys_eq: "tys = t # tsRest" and len_rest: "length ps = length tsRest"
    by (cases tys) auto
  from "9.prems"(1) tys_eq obtain dp s mv where
    dec_head: "decorate_pattern env elabEnv ghost p t accSubst next_mv = Inr (dp, s, mv)"
    by (auto simp: Let_def split: sum.splits)
  from "9.prems"(1) tys_eq dec_head obtain dpsRest where
    dec_rest: "decorate_pattern_list env elabEnv ghost ps tsRest s mv
                = Inr (dpsRest, accSubst', next_mv')" and
    dps_eq: "dps = dp # dpsRest"
    by (auto simp: Let_def split: sum.splits)

  let ?t_let = "case tys of [] \<Rightarrow> CoreTy_Var '''' | t # _ \<Rightarrow> t"
  let ?tsRest_let = "case tys of [] \<Rightarrow> [] | _ # tsRest \<Rightarrow> tsRest"
  have t_let_eq: "t = ?t_let" using tys_eq by simp
  have tsRest_let_eq: "tsRest = ?tsRest_let" using tys_eq by simp

  \<comment> \<open>Well-kindedness of head and rest from the list-form premise. \<close>
  have t_wk: "is_well_kinded (extend_env_with_tyvars env ghost lo next_mv) t"
    using "9.prems"(6) tys_eq by simp
  have tsRest_wk: "list_all (is_well_kinded (extend_env_with_tyvars env ghost lo next_mv)) tsRest"
    using "9.prems"(6) tys_eq by simp

  \<comment> \<open>Runtime-type variants of head and rest. Ghost-conditional. \<close>
  have t_rt: "ghost = NotGhost \<Longrightarrow> is_runtime_type (extend_env_with_tyvars env ghost lo next_mv) t"
    using "9.prems"(9) tys_eq by simp
  have tsRest_rt:
    "ghost = NotGhost \<Longrightarrow> list_all (is_runtime_type (extend_env_with_tyvars env ghost lo next_mv)) tsRest"
    using "9.prems"(9) tys_eq by simp

  from "9.IH"(1)[OF t_let_eq tsRest_let_eq dec_head "9.prems"(3) "9.prems"(4)
                     "9.prems"(5) t_wk "9.prems"(7) "9.prems"(8) t_rt "9.prems"(10)] have
    head_compat: "dec_pattern_compatible env (apply_subst_to_dec_pattern s dp) (apply_subst s t)" and
    head_mono: "next_mv \<le> mv" and
    head_refine: "\<exists>T. s = compose_subst T accSubst" and
    head_factors_acc: "subst_factors_through s accSubst" and
    head_factors_self: "subst_factors_through s s" and
    head_range_wk: "\<forall>ty \<in> fmran' s. is_well_kinded (extend_env_with_tyvars env ghost lo mv) ty" and
    head_dom_flex: "fmdom s |\<inter>| TE_TypeVars env = {||}" and
    head_range_rt: "ghost = NotGhost \<longrightarrow>
                      (\<forall>ty \<in> fmran' s. is_runtime_type (extend_env_with_tyvars env ghost lo mv) ty)"
    by simp_all

  \<comment> \<open>Rest premises: lo \<le> mv (from lo \<le> next_mv \<le> mv), and tsRest's well-kindedness widened. \<close>
  have lo_le_mv: "lo \<le> mv" using "9.prems"(5) head_mono by simp
  have tsRest_wk_at_mv:
    "list_all (is_well_kinded (extend_env_with_tyvars env ghost lo mv)) tsRest"
    using tsRest_wk is_well_kinded_extend_env_with_tyvars_mono[OF _ order_refl head_mono]
    by (simp add: list_all_iff)
  have tsRest_rt_at_mv:
    "ghost = NotGhost \<Longrightarrow>
       list_all (is_runtime_type (extend_env_with_tyvars env ghost lo mv)) tsRest"
    using tsRest_rt is_runtime_type_extend_env_with_tyvars_mono[OF _ order_refl head_mono]
    by (simp add: list_all_iff)
  have head_range_rt_imp:
    "ghost = NotGhost \<Longrightarrow> \<forall>ty \<in> fmran' s. is_runtime_type (extend_env_with_tyvars env ghost lo mv) ty"
    using head_range_rt by simp

  have pair1: "(dp, s, mv) = (dp, s, mv)" by simp
  have pair2: "(s, mv) = (s, mv)" by simp
  from "9.IH"(3)[OF t_let_eq tsRest_let_eq dec_head pair1 pair2
                       dec_rest len_rest "9.prems"(3) head_factors_self
                       lo_le_mv tsRest_wk_at_mv head_range_wk head_dom_flex
                       tsRest_rt_at_mv head_range_rt_imp] have
    rest_compat: "dec_pattern_compatible_list env (map (apply_subst_to_dec_pattern accSubst') dpsRest)
                                                    (map (apply_subst accSubst') tsRest)" and
    rest_mono: "mv \<le> next_mv'" and
    rest_refine: "\<exists>T. accSubst' = compose_subst T s" and
    rest_factors_s: "subst_factors_through accSubst' s" and
    rest_factors_self: "subst_factors_through accSubst' accSubst'" and
    rest_range_wk: "\<forall>ty \<in> fmran' accSubst'.
                       is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty" and
    rest_dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}" and
    rest_range_rt: "ghost = NotGhost \<longrightarrow>
                      (\<forall>ty \<in> fmran' accSubst'. is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
    by simp_all

  obtain T_rest where T_rest: "accSubst' = compose_subst T_rest s"
    using rest_refine by blast
  have factors_acc: "subst_factors_through accSubst' accSubst"
    using subst_factors_through_compose[OF head_factors_acc T_rest] .

  have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
    using compose_subst_chain_exists[OF head_refine rest_refine] .

  \<comment> \<open>Lift head's compat from s-version to accSubst'-version. T_rest's domain is part
      of accSubst's domain, which is flex (disjoint from env's type variables, hence
      from its abstract types). \<close>
  have T_rest_dom_flex: "\<And>n. n |\<in>| fmdom T_rest \<Longrightarrow> n |\<notin>| TE_TypeVars env"
    using rest_dom_flex T_rest by (auto simp: fmdom_compose_subst)
  have abs_no_subst_T: "\<And>n. n |\<in>| TE_AbstractTypes env \<Longrightarrow> fmlookup T_rest n = None"
  proof -
    fix n assume "n |\<in>| TE_AbstractTypes env"
    hence "n |\<in>| TE_TypeVars env"
      using "9.prems"(3) unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
    with T_rest_dom_flex have "n |\<notin>| fmdom T_rest" by blast
    thus "fmlookup T_rest n = None" by (simp add: fmdom_notD)
  qed
  have head_compat_T:
    "dec_pattern_compatible env
       (apply_subst_to_dec_pattern T_rest (apply_subst_to_dec_pattern s dp))
       (apply_subst T_rest (apply_subst s t))"
    using apply_subst_to_dec_pattern_preserves_compatibility[OF head_compat "9.prems"(3) abs_no_subst_T] .
  have rhs_eq: "apply_subst T_rest (apply_subst s t) = apply_subst accSubst' t"
    using T_rest by (simp add: compose_subst_correct)
  have lhs_compose:
    "apply_subst_to_dec_pattern T_rest (apply_subst_to_dec_pattern s dp)
     = apply_subst_to_dec_pattern (compose_subst T_rest s) dp"
    using apply_subst_to_dec_pattern_compose .
  have lhs_eq: "apply_subst_to_dec_pattern T_rest (apply_subst_to_dec_pattern s dp)
                 = apply_subst_to_dec_pattern accSubst' dp"
    using lhs_compose T_rest by simp
  have head_compat_at_acc':
    "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
       (apply_subst accSubst' t)"
    using head_compat_T lhs_eq rhs_eq by simp

  have map_eq: "map (apply_subst accSubst') tys
                 = (apply_subst accSubst' t) # map (apply_subst accSubst') tsRest"
    using tys_eq by simp
  have map_dps_eq:
    "map (apply_subst_to_dec_pattern accSubst') dps
     = (apply_subst_to_dec_pattern accSubst' dp) # map (apply_subst_to_dec_pattern accSubst') dpsRest"
    using dps_eq by simp
  have list_compat:
    "dec_pattern_compatible_list env (map (apply_subst_to_dec_pattern accSubst') dps)
                                     (map (apply_subst accSubst') tys)"
    using map_eq map_dps_eq head_compat_at_acc' rest_compat by simp

  have mono: "next_mv \<le> next_mv'" using head_mono rest_mono by simp

  show ?case
    using list_compat mono refine factors_acc rest_factors_self rest_range_wk rest_dom_flex rest_range_rt by simp
qed


section \<open>Pattern-variable distinctness\<close>

(* A pattern (or pattern list) is "var-names-distinct" if every DP_Var
   name appears at most once across the whole list. The elaborator
   enforces this on each user-written pattern via
   `check_pattern_no_duplicates`; the same predicate captures it in
   downstream proofs. *)
definition pattern_var_names_distinct :: "DecPattern list \<Rightarrow> bool" where
  "pattern_var_names_distinct ps =
     distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list ps))"


section \<open>Correctness of DecPattern to CorePattern translation\<close>

(* Translating a DecPattern that's compatible with a well-kinded CoreType
   produces a CorePattern that's compatible with that same type. The
   DecPattern's variable binders become wildcards, so all structure is
   preserved. The well-kinded precondition gives distinct field names in
   any record type encountered, so that map_of and positional indexing
   on the field-type list agree. The well-formed-env precondition is
   used in the variant case to discharge well-kindedness of the
   substituted ctor payload type. *)
lemma dec_to_core_pat_pattern_compatible:
  "dec_pattern_compatible env dp ty
   \<Longrightarrow> is_well_kinded env ty
   \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> pattern_compatible env (dec_to_core_pat dp) ty"
proof (induction dp arbitrary: ty)
  case (DP_Variant ctorName payload_opt)
  show ?case
  proof (cases payload_opt)
    case None
    show ?thesis using DP_Variant.prems(1) None
      by (auto split: option.splits prod.splits CoreType.splits)
  next
    case (Some inner)
    obtain dtName tyvars payloadTy where
      ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)"
      using DP_Variant.prems(1) Some
      by (auto split: option.splits CoreType.splits)
    obtain tyName tyArgs where
      ty_eq: "ty = CoreTy_Datatype tyName tyArgs"
      using DP_Variant.prems(1) Some ctor_lookup
      by (auto split: option.splits CoreType.splits)
    have tyName_eq: "tyName = dtName"
     and len_eq: "length tyArgs = length tyvars"
     and inner_compat: "dec_pattern_compatible env inner
                          (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      using DP_Variant.prems(1) Some ctor_lookup ty_eq
      by (auto split: option.splits CoreType.splits)
    \<comment> \<open>The substituted payload type is well-kinded: by
        tyenv_payloads_well_kinded the stored payloadTy is well-kinded in
        env with TypeVars set to tyvars; the tyArgs are well-kinded in env
        (from is_well_kinded ty); apply_subst_specializes_well_kinded closes. \<close>
    have payload_src_wk:
      "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars \<rparr>) payloadTy"
      using DP_Variant.prems(3) ctor_lookup
      unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def
      by blast
    have abs_sub: "TE_AbstractTypes env |\<subseteq>| TE_TypeVars env"
      using DP_Variant.prems(3) unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
    have tyArgs_wk: "list_all (is_well_kinded env) tyArgs"
      using DP_Variant.prems(2) ty_eq
      by (auto split: option.splits)
    have payload_wk:
      "is_well_kinded env
         (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      using apply_subst_specializes_well_kinded[OF payload_src_wk tyArgs_wk len_eq[symmetric] abs_sub] .
    have IH: "pattern_compatible env (dec_to_core_pat inner)
                (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)"
      using DP_Variant.IH(1) Some inner_compat payload_wk DP_Variant.prems(3) by simp
    show ?thesis
      using ctor_lookup ty_eq tyName_eq len_eq IH Some by simp
  qed
next
  case (DP_Record flds)
  obtain fieldTypes where
    ty_eq: "ty = CoreTy_Record fieldTypes"
   and names_eq: "map fst flds = map fst fieldTypes"
   and inner_compat:
     "dec_pattern_compatible_list env (map snd flds) (map snd fieldTypes)"
    using DP_Record.prems(1) by (auto split: CoreType.splits)
  have len_eq: "length flds = length fieldTypes"
    using names_eq map_eq_imp_length_eq by metis
  have fieldTypes_wk: "list_all (is_well_kinded env) (map snd fieldTypes)"
    using DP_Record.prems(2) ty_eq by simp

  let ?pflds = "map (\<lambda>(n, p). (n, dec_to_core_pat p)) flds"
  have pflds_nth:
    "\<And>i. i < length flds \<Longrightarrow> ?pflds ! i = (fst (flds ! i), dec_to_core_pat (snd (flds ! i)))"
    by (auto simp: case_prod_unfold)

  have IH_each:
    "\<And>i. i < length flds \<Longrightarrow>
        pattern_compatible env (dec_to_core_pat (snd (flds ! i))) (snd (fieldTypes ! i))"
  proof -
    fix i assume i_lt: "i < length flds"
    have pair_in_set: "(fst (flds ! i), snd (flds ! i)) \<in> set flds"
      using i_lt by (metis nth_mem prod.collapse)
    have ih_step:
      "\<And>fty. dec_pattern_compatible env (snd (flds ! i)) fty
              \<Longrightarrow> is_well_kinded env fty
              \<Longrightarrow> pattern_compatible env (dec_to_core_pat (snd (flds ! i))) fty"
      using DP_Record.IH[OF pair_in_set] DP_Record.prems(3) by (simp add: snds.intros)
    have inner_at_i: "dec_pattern_compatible env (snd (flds ! i)) (snd (fieldTypes ! i))"
      using inner_compat dec_pattern_compatible_list_iff len_eq i_lt by auto
    have fty_wk: "is_well_kinded env (snd (fieldTypes ! i))"
      using fieldTypes_wk i_lt len_eq by (auto simp: list_all_length)
    show "pattern_compatible env (dec_to_core_pat (snd (flds ! i))) (snd (fieldTypes ! i))"
      using ih_step[OF inner_at_i fty_wk] .
  qed

  have pflds_la2:
    "list_all2 (\<lambda>(pn, p) (fn, fty). pn = fn \<and> pattern_compatible env p fty)
               ?pflds fieldTypes"
  proof (rule list_all2_all_nthI)
    show "length ?pflds = length fieldTypes" using len_eq by simp
  next
    fix i assume i_lt: "i < length ?pflds"
    hence i_lt': "i < length flds" by simp
    have name_at_i: "fst (flds ! i) = fst (fieldTypes ! i)"
      using names_eq by (metis i_lt' len_eq nth_map)
    obtain pn p where pf_i: "?pflds ! i = (pn, p)"
      using pflds_nth[OF i_lt'] by simp
    obtain fn' fty where ft_i: "fieldTypes ! i = (fn', fty)"
      by (cases "fieldTypes ! i") auto
    from pflds_nth[OF i_lt'] pf_i have pn_p_eq:
      "pn = fst (flds ! i)" "p = dec_to_core_pat (snd (flds ! i))"
      by auto
    from ft_i have fn_fty_eq:
      "fn' = fst (fieldTypes ! i)" "fty = snd (fieldTypes ! i)"
      by auto
    show "(case ?pflds ! i of (pn, p) \<Rightarrow>
             \<lambda>(fn, fty). pn = fn \<and> pattern_compatible env p fty)
          (fieldTypes ! i)"
      using pf_i ft_i pn_p_eq fn_fty_eq name_at_i IH_each[OF i_lt']
      by force
  qed
  show ?case
    using ty_eq pflds_la2 by simp
qed (auto split: option.splits prod.splits CoreType.splits)


section \<open>dec_pattern_projections properties; wrap_lets preserves typing\<close>

(* The binding triples of dec_pattern_projections are exactly
   dec_pattern_var_bindings, in the same (pattern-traversal) order. *)
lemma dec_pattern_projections_var_bindings:
  "map (\<lambda>(vr, n, ty, _). (vr, n, ty)) (dec_pattern_projections base dp)
     = dec_pattern_var_bindings dp"
and dec_pattern_projections_record_var_bindings:
  "map (\<lambda>(vr, n, ty, _). (vr, n, ty)) (dec_pattern_projections_record base flds)
     = dec_pattern_var_bindings_list (map snd flds)"
proof (induction base dp and base flds
       rule: dec_pattern_projections_dec_pattern_projections_record.induct)
qed auto

(* The binding names of a DecPattern, as a finite set. *)
lemma dec_pattern_var_bindings_names:
  "fset_of_list (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings dp))
     = dec_pattern_var_names dp"
and dec_pattern_var_bindings_list_names:
  "fset_of_list (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings_list dps))
     = dec_pattern_var_names_list dps"
  by (induction dp and dps
      rule: dec_pattern_var_bindings_dec_pattern_var_bindings_list.induct)
     auto

(* Every projection term has exactly the base term's free variables
   (projections only wrap base in CoreTm_VariantProj / CoreTm_RecordProj). *)
lemma dec_pattern_projections_free_vars:
  "(vr, n, vTy, proj) \<in> set (dec_pattern_projections base dp)
   \<Longrightarrow> core_term_free_vars proj = core_term_free_vars base"
and dec_pattern_projections_record_free_vars:
  "(vr, n, vTy, proj) \<in> set (dec_pattern_projections_record base flds)
   \<Longrightarrow> core_term_free_vars proj = core_term_free_vars base"
proof (induction base dp and base flds
       rule: dec_pattern_projections_dec_pattern_projections_record.induct)
qed auto

(* Each projection term typechecks at its binding's declared type, given that
   the base term typechecks at the (compatible, well-kinded) scrutinee type.

   The mutual second statement handles a partial record-field list `flds`
   that lives at base of type `CoreTy_Record fldTys`, in per-field "lookup"
   form, so that the tail of a record's field list still satisfies the IH. *)
lemma dec_pattern_projections_typed:
  "dec_pattern_compatible env dp baseTy
   \<Longrightarrow> core_term_type env ghost base = Some baseTy
   \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> is_well_kinded env baseTy
   \<Longrightarrow> (vr, n, vTy, proj) \<in> set (dec_pattern_projections base dp)
   \<Longrightarrow> core_term_type env ghost proj = Some vTy"
and dec_pattern_projections_record_typed:
  "core_term_type env ghost base = Some (CoreTy_Record fldTys)
   \<Longrightarrow> tyenv_well_formed env
   \<Longrightarrow> is_well_kinded env (CoreTy_Record fldTys)
   \<Longrightarrow> list_all
         (\<lambda>(fn, p). \<exists>fty. map_of fldTys fn = Some fty
                          \<and> dec_pattern_compatible env p fty)
         flds
   \<Longrightarrow> (vr, n, vTy, proj) \<in> set (dec_pattern_projections_record base flds)
   \<Longrightarrow> core_term_type env ghost proj = Some vTy"
proof (induction base dp and base flds
       arbitrary: baseTy and fldTys
       rule: dec_pattern_projections_dec_pattern_projections_record.induct)

  case (1 base vr' name' vTy')
    \<comment> \<open>DP_Var: the (single) projection is base itself, at type vTy' = baseTy. \<close>
  thus ?case by auto

next
  case (6 base cn inner)
    \<comment> \<open>DP_Variant cn (Some inner): recurse at base' = CoreTm_VariantProj base cn. \<close>
  obtain dtName tyvars stored_payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) cn = Some (dtName, tyvars, stored_payloadTy)"
    using "6.prems"(1)
    by (auto split: option.splits CoreType.splits)
  obtain tyName tyArgs where
    baseTy_eq: "baseTy = CoreTy_Datatype tyName tyArgs"
    using "6.prems"(1) ctor_lookup
    by (auto split: option.splits CoreType.splits)
  have tyName_eq: "tyName = dtName"
   and len_eq: "length tyArgs = length tyvars"
   and inner_compat: "dec_pattern_compatible env inner
                       (apply_subst (fmap_of_list (zip tyvars tyArgs)) stored_payloadTy)"
    using "6.prems"(1) ctor_lookup baseTy_eq
    by (auto split: option.splits CoreType.splits)

  let ?payloadTy = "apply_subst (fmap_of_list (zip tyvars tyArgs)) stored_payloadTy"

  have base'_typed: "core_term_type env ghost (CoreTm_VariantProj base cn) = Some ?payloadTy"
    using "6.prems"(2) ctor_lookup baseTy_eq tyName_eq len_eq
    by simp

  have stored_wk:
    "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars \<rparr>) stored_payloadTy"
    using "6.prems"(3) ctor_lookup
    unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def
    by blast
  have abs_sub: "TE_AbstractTypes env |\<subseteq>| TE_TypeVars env"
    using "6.prems"(3) unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
  have tyArgs_wk: "list_all (is_well_kinded env) tyArgs"
    using "6.prems"(4) baseTy_eq
    by (auto split: option.splits)
  have payloadTy_wk: "is_well_kinded env ?payloadTy"
    using apply_subst_specializes_well_kinded[OF stored_wk tyArgs_wk len_eq[symmetric] abs_sub] .

  show ?case
    using "6.IH"[OF inner_compat base'_typed "6.prems"(3) payloadTy_wk] "6.prems"(5)
    by simp

next
  case (7 base flds)
    \<comment> \<open>DP_Record flds: dispatch to the record statement. \<close>
  obtain fieldTypes where
    baseTy_eq: "baseTy = CoreTy_Record fieldTypes"
   and names_eq: "map fst flds = map fst fieldTypes"
   and inner_compat:
     "dec_pattern_compatible_list env (map snd flds) (map snd fieldTypes)"
    using "7.prems"(1)
    by (auto split: CoreType.splits)
  have len_eq: "length flds = length fieldTypes"
    using names_eq map_eq_imp_length_eq by metis
  have fieldTypes_distinct: "distinct (map fst fieldTypes)"
    using "7.prems"(4) baseTy_eq by simp

  \<comment> \<open>Translate the structural compatibility into the per-field "lookup" form. \<close>
  have flds_lookup:
    "list_all (\<lambda>(fn, p). \<exists>fty. map_of fieldTypes fn = Some fty
                              \<and> dec_pattern_compatible env p fty) flds"
  proof -
    have "\<forall>i < length flds.
            case flds ! i of (fn, p) \<Rightarrow>
              \<exists>fty. map_of fieldTypes fn = Some fty
                    \<and> dec_pattern_compatible env p fty"
    proof (intro allI impI)
      fix i assume i_lt: "i < length flds"
      have name_eq: "fst (flds ! i) = fst (fieldTypes ! i)"
        using names_eq by (metis i_lt len_eq nth_map)
      have lookup_eq:
        "map_of fieldTypes (fst (fieldTypes ! i)) = Some (snd (fieldTypes ! i))"
        using fieldTypes_distinct i_lt len_eq
        by (metis len_eq map_of_eq_Some_iff nth_mem prod.collapse)
      have inner_at_i: "dec_pattern_compatible env (snd (flds ! i)) (snd (fieldTypes ! i))"
        using inner_compat dec_pattern_compatible_list_iff len_eq i_lt by auto
      show "case flds ! i of (fn, p) \<Rightarrow>
              \<exists>fty. map_of fieldTypes fn = Some fty
                    \<and> dec_pattern_compatible env p fty"
        using lookup_eq inner_at_i name_eq
        by (auto simp: case_prod_unfold)
    qed
    thus ?thesis unfolding list_all_length .
  qed

  have base_typed_record:
    "core_term_type env ghost base = Some (CoreTy_Record fieldTypes)"
    using "7.prems"(2) baseTy_eq by simp
  have baseTy_wk_record: "is_well_kinded env (CoreTy_Record fieldTypes)"
    using "7.prems"(4) baseTy_eq by simp

  show ?case
    using "7.IH"[OF base_typed_record "7.prems"(3) baseTy_wk_record flds_lookup] "7.prems"(5)
    by simp

next
  case (9 base fn p rest)
    \<comment> \<open>Record cons: the projection is either among p's (via RecordProj base fn)
        or among rest's. \<close>
  obtain fty where
    fty_lookup: "map_of fldTys fn = Some fty"
   and p_compat: "dec_pattern_compatible env p fty"
    using "9.prems"(4) by auto

  have proj_typed:
    "core_term_type env ghost (CoreTm_RecordProj base fn) = Some fty"
    using "9.prems"(1) fty_lookup by simp

  have fty_in: "(fn, fty) \<in> set fldTys"
    using fty_lookup by (rule map_of_SomeD)
  have fldTys_wk: "list_all (is_well_kinded env) (map snd fldTys)"
    using "9.prems"(3) by simp
  have fty_wk: "is_well_kinded env fty"
    using fty_in fldTys_wk by (auto simp: list_all_iff)

  have rest_lookup:
    "list_all (\<lambda>(fn, p). \<exists>fty. map_of fldTys fn = Some fty
                              \<and> dec_pattern_compatible env p fty) rest"
    using "9.prems"(4) by simp

  from "9.prems"(5)
  consider (InP) "(vr, n, vTy, proj) \<in> set (dec_pattern_projections (CoreTm_RecordProj base fn) p)"
         | (InRest) "(vr, n, vTy, proj) \<in> set (dec_pattern_projections_record base rest)"
    by auto
  thus ?case
  proof cases
    case InP
    show ?thesis
      using "9.IH"(1)[OF p_compat proj_typed "9.prems"(2) fty_wk InP] .
  next
    case InRest
    show ?thesis
      using "9.IH"(2)[OF "9.prems"(1) "9.prems"(2) "9.prems"(3) rest_lookup InRest] .
  qed

qed auto

(* Typing of a foldr of CoreTm_Lets over a projection list: if every
   projection typechecks at its binding's type (under env), no projection
   mentions any of the binding names, the names are distinct, and the body
   typechecks under env extended by all the bindings (Let-style: every
   binding const), then the wrapped term typechecks at the body's type. *)
lemma foldr_let_preserves_typing:
  "(\<And>vr n vTy proj. (vr, n, vTy, proj) \<in> set projs
      \<Longrightarrow> core_term_type env ghost proj = Some vTy)
   \<Longrightarrow> (\<And>vr n vTy proj n'. (vr, n, vTy, proj) \<in> set projs
      \<Longrightarrow> n' \<in> set (map (\<lambda>(_, m, _, _). m) projs)
      \<Longrightarrow> n' |\<notin>| core_term_free_vars proj)
   \<Longrightarrow> core_term_type
         (foldr (extend_env_one_var (\<lambda>_. True) ghost)
                (map (\<lambda>(vr, n, ty, _). (vr, n, ty)) projs) env)
         ghost body = Some bodyTy
   \<Longrightarrow> distinct (map (\<lambda>(_, m, _, _). m) projs)
   \<Longrightarrow> core_term_type env ghost
         (foldr (\<lambda>(_, n, _, proj). CoreTm_Let n proj) projs body) = Some bodyTy"
proof (induction projs arbitrary: env)
  case Nil
  thus ?case by simp
next
  case (Cons q rest)
  obtain vr n vTy proj where q_eq: "q = (vr, n, vTy, proj)" by (cases q) auto

  have proj_typed: "core_term_type env ghost proj = Some vTy"
    using Cons.prems(1) q_eq by auto

  let ?env' = "extend_env_one_var (\<lambda>_. True) ghost (vr, n, vTy) env"

  \<comment> \<open>Premises of the IH, at env := ?env'. \<close>
  have rest_typed:
    "\<And>vr' n' vTy' proj'. (vr', n', vTy', proj') \<in> set rest
       \<Longrightarrow> core_term_type ?env' ghost proj' = Some vTy'"
  proof -
    fix vr' n' vTy' proj'
    assume in_rest: "(vr', n', vTy', proj') \<in> set rest"
    have typed_env: "core_term_type env ghost proj' = Some vTy'"
      using Cons.prems(1) q_eq in_rest by auto
    have n_fresh: "n |\<notin>| core_term_free_vars proj'"
      using Cons.prems(2)[of vr' n' vTy' proj' n] q_eq in_rest by simp
    show "core_term_type ?env' ghost proj' = Some vTy'"
      using core_term_type_extend_env_one_var_irrelevant[OF n_fresh typed_env] .
  qed

  have rest_fresh:
    "\<And>vr' n' vTy' proj' n''. (vr', n', vTy', proj') \<in> set rest
       \<Longrightarrow> n'' \<in> set (map (\<lambda>(_, m, _, _). m) rest)
       \<Longrightarrow> n'' |\<notin>| core_term_free_vars proj'"
    using Cons.prems(2) by fastforce

  have n_not_in_rest: "n \<notin> set (map (\<lambda>(_, x, _). x) (map (\<lambda>(vr, n, ty, _). (vr, n, ty)) rest))"
    using Cons.prems(4) q_eq by (auto simp: case_prod_unfold)

  have body_typed_env':
    "core_term_type
       (foldr (extend_env_one_var (\<lambda>_. True) ghost)
              (map (\<lambda>(vr, n, ty, _). (vr, n, ty)) rest) ?env')
       ghost body = Some bodyTy"
    using Cons.prems(3) q_eq
          foldr_extend_env_one_var_push[OF n_not_in_rest, of "\<lambda>_. True" ghost vr vTy env]
    by simp

  have distinct_rest: "distinct (map (\<lambda>(_, m, _, _). m) rest)"
    using Cons.prems(4) q_eq by (simp add: case_prod_unfold)

  have inner_typed:
    "core_term_type ?env' ghost
       (foldr (\<lambda>(_, n, _, proj). CoreTm_Let n proj) rest body) = Some bodyTy"
    using Cons.IH[OF rest_typed rest_fresh body_typed_env' distinct_rest] .

  \<comment> \<open>Assemble the CoreTm_Let: its typing rule extends env exactly like
      extend_env_one_var (\<lambda>_. True). \<close>
  have inner_typed':
    "core_term_type
       (env \<lparr> TE_LocalVars := fmupd n vTy (TE_LocalVars env),
              TE_GhostLocals := (if ghost = Ghost
                                 then finsert n (TE_GhostLocals env)
                                 else fminus (TE_GhostLocals env) {|n|}),
              TE_ConstLocals := finsert n (TE_ConstLocals env) \<rparr>)
       ghost (foldr (\<lambda>(_, n, _, proj). CoreTm_Let n proj) rest body) = Some bodyTy"
    using inner_typed by (simp add: extend_env_one_var_def)

  show ?case
    using q_eq proj_typed inner_typed' by (simp add: Let_def)
qed

(* Well-typedness of wrap_lets: if the scrutinee variable has the type the
   pattern is compatible with, the variable is not shadowed by any pattern
   variable, and the body is well-typed in env extended by all of dp's
   pattern-variable bindings (Let-style const bindings), then the wrapped
   form is well-typed at the body type. *)
lemma wrap_lets_preserves_typing:
  assumes compat: "dec_pattern_compatible env dp baseTy"
      and base_typed: "core_term_type env ghost (CoreTm_Var scrutVar) = Some baseTy"
      and wf: "tyenv_well_formed env"
      and wk: "is_well_kinded env baseTy"
      and fresh: "core_term_free_vars (CoreTm_Var scrutVar) |\<inter>| dec_pattern_var_names dp = {||}"
      and body_typed:
        "core_term_type
           (foldr (extend_env_one_var (\<lambda>_. True) ghost) (dec_pattern_var_bindings dp) env)
           ghost body = Some bodyTy"
      and dist: "distinct (map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings dp))"
  shows "core_term_type env ghost (wrap_lets scrutVar dp body) = Some bodyTy"
proof -
  let ?projs = "dec_pattern_projections (CoreTm_Var scrutVar) dp"

  \<comment> \<open>The projection names are the binding names. \<close>
  have names_eq:
    "map (\<lambda>(_, m, _, _). m) ?projs = map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings dp)"
  proof -
    have "map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings dp)
            = map ((\<lambda>(_, x, _). x) \<circ> (\<lambda>(vr, n, ty, _). (vr, n, ty))) ?projs"
      by (metis dec_pattern_projections_var_bindings list.map_comp)
    also have "\<dots> = map (\<lambda>(_, m, _, _). m) ?projs"
      by (rule map_cong[OF refl]) (auto simp: case_prod_unfold)
    finally show ?thesis by simp
  qed

  have projs_typed:
    "\<And>vr n vTy proj. (vr, n, vTy, proj) \<in> set ?projs
       \<Longrightarrow> core_term_type env ghost proj = Some vTy"
    using dec_pattern_projections_typed[OF compat base_typed wf wk] .

  \<comment> \<open>Every projection's free vars = {scrutVar}, which is disjoint from the
      binding names by the freshness assumption. \<close>
  have projs_fresh:
    "\<And>vr n vTy proj n'. (vr, n, vTy, proj) \<in> set ?projs
       \<Longrightarrow> n' \<in> set (map (\<lambda>(_, m, _, _). m) ?projs)
       \<Longrightarrow> n' |\<notin>| core_term_free_vars proj"
  proof -
    fix vr n vTy proj n'
    assume in_projs: "(vr, n, vTy, proj) \<in> set ?projs"
       and n'_name: "n' \<in> set (map (\<lambda>(_, m, _, _). m) ?projs)"
    have fv_eq: "core_term_free_vars proj = {|scrutVar|}"
      using dec_pattern_projections_free_vars[OF in_projs] by simp
    have "n' |\<in>| dec_pattern_var_names dp"
      using n'_name names_eq dec_pattern_var_bindings_names[of dp]
      by (metis fset_of_list_elem)
    hence "n' \<noteq> scrutVar" using fresh by auto
    thus "n' |\<notin>| core_term_free_vars proj" using fv_eq by simp
  qed

  have body_typed':
    "core_term_type
       (foldr (extend_env_one_var (\<lambda>_. True) ghost)
              (map (\<lambda>(vr, n, ty, _). (vr, n, ty)) ?projs) env)
       ghost body = Some bodyTy"
    using body_typed by (simp add: dec_pattern_projections_var_bindings)

  have dist': "distinct (map (\<lambda>(_, m, _, _). m) ?projs)"
    using dist names_eq by simp

  show ?thesis
    unfolding wrap_lets_def
    using foldr_let_preserves_typing[OF projs_typed projs_fresh body_typed' dist'] .
qed


section \<open>Correctness for decorate_match_arms, finalize_match_arms\<close>

lemma map_snd_map_apply_subst_to_dec_pattern_flds:
  "map snd (map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern subst p)) flds)
   = map (apply_subst_to_dec_pattern subst) (map snd flds)"
  by (induction flds) auto


(* Patterns accepted by check_pattern_no_duplicates (and hence by
   check_match_pattern, which runs it first) have distinct variable names. *)
lemma check_pattern_no_duplicates_implies_distinctness:
  assumes "check_pattern_no_duplicates loc dp = Inr r"
  shows "pattern_var_names_distinct [dp]"
proof -
  have none: "first_duplicate_name (\<lambda>(_, name, _). name) (dec_pattern_var_bindings dp) = None"
    using assms unfolding check_pattern_no_duplicates_def
    by (cases "first_duplicate_name (\<lambda>(_, name, _). name) (dec_pattern_var_bindings dp)") auto
  have "distinct (map (\<lambda>(_, name, _). name) (dec_pattern_var_bindings dp))"
    using none by (rule first_duplicate_name_None_implies_distinct)
  thus "pattern_var_names_distinct [dp]"
    unfolding pattern_var_names_distinct_def
    by simp
qed

lemma check_match_pattern_implies_distinctness:
  assumes "check_match_pattern allowRefs loc dp = Inr r"
  shows "pattern_var_names_distinct [dp]"
proof -
  have "check_pattern_no_duplicates loc dp = Inr ()"
    using assms unfolding check_match_pattern_def
    by (cases "check_pattern_no_duplicates loc dp")
       (auto split: if_splits list.splits prod.splits)
  thus ?thesis by (rule check_pattern_no_duplicates_implies_distinctness)
qed


(* Correctness for the per-arm pattern-decoration loop. After decorate_match_arms
   succeeds: every output row carries a DecPattern that — once accSubst' is
   applied uniformly to both the pattern and the scrutinee type — is compatible
   in the dec_pattern_compatible sense; pairwise distinct pattern-var names;
   and the original body term unchanged from arms.

   Strengthened with well-kindedness threading parallel to decorate_pattern_correct,
   plus exposure of compose-shape and factoring properties of accSubst' so callers
   (BabTm_Match elaborator correctness) can lift facts through the substitution chain. *)
lemma decorate_match_arms_correct:
  assumes dec: "decorate_match_arms env elabEnv ghost scrutTy allowRefs accSubst next_mv arms
                  = Inr (rows, accSubst', next_mv')"
      and wf: "tyenv_well_formed env"
      and acc_idem: "subst_factors_through accSubst accSubst"
      and lo_le: "lo \<le> next_mv"
      and scrut_wk: "is_well_kinded (extend_env_with_tyvars env ghost lo next_mv) scrutTy"
      and acc_wk: "\<forall>ty \<in> fmran' accSubst.
                      is_well_kinded (extend_env_with_tyvars env ghost lo next_mv) ty"
      and acc_dom: "fmdom accSubst |\<inter>| TE_TypeVars env = {||}"
      and scrut_rt: "ghost = NotGhost \<Longrightarrow>
                       is_runtime_type (extend_env_with_tyvars env ghost lo next_mv) scrutTy"
      and acc_rt: "ghost = NotGhost \<Longrightarrow>
                     \<forall>ty \<in> fmran' accSubst.
                       is_runtime_type (extend_env_with_tyvars env ghost lo next_mv) ty"
  shows "length rows = length arms
       \<and> map snd rows = map snd arms
       \<and> list_all2
           (\<lambda>(dp, body) (pat, body').
              dec_pattern_compatible env
                (apply_subst_to_dec_pattern accSubst' dp)
                (apply_subst accSubst' scrutTy)
              \<and> pattern_var_names_distinct [dp]
              \<and> body = body')
           rows arms
       \<and> next_mv \<le> next_mv'
       \<and> (\<exists>T. accSubst' = compose_subst T accSubst)
       \<and> subst_factors_through accSubst' accSubst
       \<and> subst_factors_through accSubst' accSubst'
       \<and> (\<forall>ty \<in> fmran' accSubst'.
            is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty)
       \<and> fmdom accSubst' |\<inter>| TE_TypeVars env = {||}
       \<and> (ghost = NotGhost \<longrightarrow>
            (\<forall>ty \<in> fmran' accSubst'.
                is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty))"
using assms proof (induction arms arbitrary: accSubst next_mv rows)
  case Nil
  hence eqs: "rows = []" "accSubst' = accSubst" "next_mv' = next_mv" by simp_all
  have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
    using eqs by (metis compose_subst_empty_left)
  show ?case
    using eqs Nil.prems(2-9) refine by simp
next
  case (Cons arm rest)
  obtain pat body where arm_eq: "arm = (pat, body)" by (cases arm) auto

  \<comment> \<open>Decompose the cons step. \<close>
  from Cons.prems(1) arm_eq obtain dp accSubst1 next_mv1 where
    dec_eq: "decorate_pattern env elabEnv ghost pat scrutTy accSubst next_mv
             = Inr (dp, accSubst1, next_mv1)"
    by (auto split: sum.splits)
  from Cons.prems(1) arm_eq dec_eq obtain check_res where
    chk_eq: "check_match_pattern allowRefs (bab_pattern_location pat) dp = Inr check_res"
    by (auto split: sum.splits)
  from Cons.prems(1) arm_eq dec_eq chk_eq obtain restRows where
    rec_eq: "decorate_match_arms env elabEnv ghost scrutTy allowRefs accSubst1 next_mv1 rest
             = Inr (restRows, accSubst', next_mv')" and
    rows_eq: "rows = (dp, body) # restRows"
    by (auto simp: Let_def split: sum.splits)

  \<comment> \<open>Apply decorate_pattern_correct to the head. \<close>
  from decorate_pattern_correct[OF dec_eq Cons.prems(2) Cons.prems(3)
                                   Cons.prems(4) Cons.prems(5) Cons.prems(6) Cons.prems(7)
                                   Cons.prems(8) Cons.prems(9)]
  have
    dp_compat_at_acc1:
      "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst1 dp)
                                  (apply_subst accSubst1 scrutTy)" and
    head_mono: "next_mv \<le> next_mv1" and
    head_refine: "\<exists>T. accSubst1 = compose_subst T accSubst" and
    head_factors_acc: "subst_factors_through accSubst1 accSubst" and
    head_factors_self: "subst_factors_through accSubst1 accSubst1" and
    head_range_wk: "\<forall>ty \<in> fmran' accSubst1.
                       is_well_kinded (extend_env_with_tyvars env ghost lo next_mv1) ty" and
    head_dom_flex: "fmdom accSubst1 |\<inter>| TE_TypeVars env = {||}" and
    head_range_rt: "ghost = NotGhost \<longrightarrow>
                      (\<forall>ty \<in> fmran' accSubst1.
                          is_runtime_type (extend_env_with_tyvars env ghost lo next_mv1) ty)"
    by simp_all

  \<comment> \<open>Distinctness of the head DP from check_match_pattern. \<close>
  have dp_distinct: "pattern_var_names_distinct [dp]"
    using check_match_pattern_implies_distinctness[OF chk_eq] .

  \<comment> \<open>Premises for the recursive IH. \<close>
  have lo_le_mv1: "lo \<le> next_mv1" using Cons.prems(4) head_mono by simp
  have scrut_wk_at_mv1: "is_well_kinded (extend_env_with_tyvars env ghost lo next_mv1) scrutTy"
    using is_well_kinded_extend_env_with_tyvars_mono[OF Cons.prems(5) order_refl head_mono] .
  have scrut_rt_at_mv1: "ghost = NotGhost \<Longrightarrow>
                            is_runtime_type (extend_env_with_tyvars env ghost lo next_mv1) scrutTy"
    using is_runtime_type_extend_env_with_tyvars_mono[OF _ order_refl head_mono] Cons.prems(8)
    by blast
  have head_range_rt_imp: "ghost = NotGhost \<Longrightarrow>
                              \<forall>ty \<in> fmran' accSubst1.
                                is_runtime_type (extend_env_with_tyvars env ghost lo next_mv1) ty"
    using head_range_rt by blast

  \<comment> \<open>Apply IH to the recursive call. \<close>
  from Cons.IH[OF rec_eq Cons.prems(2) head_factors_self lo_le_mv1
                  scrut_wk_at_mv1 head_range_wk head_dom_flex
                  scrut_rt_at_mv1 head_range_rt_imp] have
    ih_len: "length restRows = length rest" and
    ih_bodies: "map snd restRows = map snd rest" and
    ih_pred:
      "list_all2
         (\<lambda>(dp', body') (pat', body'').
            dec_pattern_compatible env
              (apply_subst_to_dec_pattern accSubst' dp')
              (apply_subst accSubst' scrutTy)
            \<and> pattern_var_names_distinct [dp']
            \<and> body' = body'')
         restRows rest" and
    ih_mono: "next_mv1 \<le> next_mv'" and
    ih_refine: "\<exists>T. accSubst' = compose_subst T accSubst1" and
    ih_factors_acc1: "subst_factors_through accSubst' accSubst1" and
    ih_factors_self: "subst_factors_through accSubst' accSubst'" and
    ih_range_wk: "\<forall>ty \<in> fmran' accSubst'.
                     is_well_kinded (extend_env_with_tyvars env ghost lo next_mv') ty" and
    ih_dom_flex: "fmdom accSubst' |\<inter>| TE_TypeVars env = {||}" and
    ih_range_rt: "ghost = NotGhost \<longrightarrow>
                    (\<forall>ty \<in> fmran' accSubst'.
                        is_runtime_type (extend_env_with_tyvars env ghost lo next_mv') ty)"
    by simp_all

  obtain T_rec where T_rec: "accSubst' = compose_subst T_rec accSubst1"
    using ih_refine by blast

  \<comment> \<open>Lift the head's compatibility through the IH-accumulated substitution. T_rec's
      domain is part of accSubst's domain, which is flex (disjoint from env's type
      variables, hence from its abstract types). \<close>
  have T_rec_dom_flex: "\<And>n. n |\<in>| fmdom T_rec \<Longrightarrow> n |\<notin>| TE_TypeVars env"
    using ih_dom_flex T_rec by (auto simp: fmdom_compose_subst)
  have abs_no_subst_T: "\<And>n. n |\<in>| TE_AbstractTypes env \<Longrightarrow> fmlookup T_rec n = None"
  proof -
    fix n assume "n |\<in>| TE_AbstractTypes env"
    hence "n |\<in>| TE_TypeVars env"
      using wf unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
    with T_rec_dom_flex have "n |\<notin>| fmdom T_rec" by blast
    thus "fmlookup T_rec n = None" by (simp add: fmdom_notD)
  qed
  have head_compat_T:
    "dec_pattern_compatible env
       (apply_subst_to_dec_pattern T_rec (apply_subst_to_dec_pattern accSubst1 dp))
       (apply_subst T_rec (apply_subst accSubst1 scrutTy))"
    using apply_subst_to_dec_pattern_preserves_compatibility[OF dp_compat_at_acc1 wf abs_no_subst_T] .
  have rhs_eq: "apply_subst T_rec (apply_subst accSubst1 scrutTy) = apply_subst accSubst' scrutTy"
    using T_rec by (simp add: compose_subst_correct)
  have lhs_compose:
    "apply_subst_to_dec_pattern T_rec (apply_subst_to_dec_pattern accSubst1 dp)
     = apply_subst_to_dec_pattern (compose_subst T_rec accSubst1) dp"
    using apply_subst_to_dec_pattern_compose .
  have lhs_eq: "apply_subst_to_dec_pattern T_rec (apply_subst_to_dec_pattern accSubst1 dp)
                 = apply_subst_to_dec_pattern accSubst' dp"
    using lhs_compose T_rec by simp
  have head_compat:
    "dec_pattern_compatible env (apply_subst_to_dec_pattern accSubst' dp)
                                (apply_subst accSubst' scrutTy)"
    using head_compat_T lhs_eq rhs_eq by simp

  \<comment> \<open>Refinement / factoring / monotonicity. \<close>
  have refine: "\<exists>T. accSubst' = compose_subst T accSubst"
    using compose_subst_chain_exists[OF head_refine ih_refine] .
  have factors_acc: "subst_factors_through accSubst' accSubst"
    using subst_factors_through_compose[OF head_factors_acc T_rec] .
  have mono: "next_mv \<le> next_mv'" using head_mono ih_mono by simp

  show ?case
    using ih_len ih_bodies ih_pred head_compat dp_distinct
          rows_eq arm_eq mono refine factors_acc ih_factors_self ih_range_wk ih_dom_flex ih_range_rt
    by simp
qed

(* apply_subst_to_dec_pattern only changes the embedded types; it preserves
   the (vr, name) parts of the bindings. *)

(* Bindings under substitution: same vr/name, types are substituted. *)
lemma dec_pattern_var_bindings_apply_subst:
  "dec_pattern_var_bindings (apply_subst_to_dec_pattern subst dp)
   = map (\<lambda>(vr, n, ty). (vr, n, apply_subst subst ty)) (dec_pattern_var_bindings dp)"
  and dec_pattern_var_bindings_list_apply_subst:
  "dec_pattern_var_bindings_list (map (apply_subst_to_dec_pattern subst) dps)
   = map (\<lambda>(vr, n, ty). (vr, n, apply_subst subst ty)) (dec_pattern_var_bindings_list dps)"
proof (induction dp and dps rule: dec_pattern_var_bindings_dec_pattern_var_bindings_list.induct)
  case (7 flds)
  show ?case using "7" map_snd_map_apply_subst_to_dec_pattern_flds[of subst flds]
    using apply_subst_to_dec_pattern.simps(5) dec_pattern_var_bindings.simps(7)
    by presburger
qed auto

lemma apply_subst_to_dec_pattern_preserves_distinct:
  assumes "pattern_var_names_distinct [dp]"
  shows "pattern_var_names_distinct [apply_subst_to_dec_pattern subst dp]"
proof -
  have list_eq: "dec_pattern_var_bindings_list [apply_subst_to_dec_pattern subst dp]
                  = dec_pattern_var_bindings (apply_subst_to_dec_pattern subst dp)"
    by simp
  have list_eq_orig: "dec_pattern_var_bindings_list [dp] = dec_pattern_var_bindings dp"
    by simp
  have bindings_subst:
    "dec_pattern_var_bindings (apply_subst_to_dec_pattern subst dp)
     = map (\<lambda>(vr, n, ty). (vr, n, apply_subst subst ty)) (dec_pattern_var_bindings dp)"
    using dec_pattern_var_bindings_apply_subst .
  have names_eq:
    "map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings (apply_subst_to_dec_pattern subst dp))
     = map (\<lambda>(_, x, _). x) (dec_pattern_var_bindings dp)"
    unfolding bindings_subst by (induction "dec_pattern_var_bindings dp") auto
  show ?thesis
    using assms
    unfolding pattern_var_names_distinct_def list_eq list_eq_orig names_eq .
qed


(* If every meta in every binding type of dp lies in a fixed tyvar set that's
   disjoint from finalSubst's domain, then apply_subst is identity on every
   binding type. *)
lemma dec_pattern_var_bindings_apply_subst_id_of_meta_safe:
  assumes meta_safe:
    "list_all (\<lambda>(_, _, vTy). list_all (\<lambda>n. n |\<in>| flexSet) (type_tyvars_list vTy))
              (dec_pattern_var_bindings dp)"
      and dom_disjoint: "fmdom subst |\<inter>| flexSet = {||}"
  shows "list_all (\<lambda>(_, _, vTy). apply_subst subst vTy = vTy)
                  (dec_pattern_var_bindings dp)"
proof -
  have "\<And>vr n vTy. (vr, n, vTy) \<in> set (dec_pattern_var_bindings dp)
                    \<Longrightarrow> apply_subst subst vTy = vTy"
  proof -
    fix vr n vTy
    assume in_set: "(vr, n, vTy) \<in> set (dec_pattern_var_bindings dp)"
    with meta_safe have all_in_flex: "list_all (\<lambda>m. m |\<in>| flexSet) (type_tyvars_list vTy)"
      by (auto simp: list_all_iff)
    \<comment> \<open>type_tyvars_list = sorted_list_of_fset of type_tyvars; turn it into a set claim. \<close>
    have "type_tyvars vTy \<inter> fset (fmdom subst) = {}"
    proof (rule ccontr)
      assume "type_tyvars vTy \<inter> fset (fmdom subst) \<noteq> {}"
      then obtain n' where n'_in_ty: "n' \<in> type_tyvars vTy"
                       and n'_in_dom: "n' |\<in>| fmdom subst" by auto
      from n'_in_ty have "n' \<in> set (type_tyvars_list vTy)"
        by (simp add: set_type_tyvars_list)
      with all_in_flex have "n' |\<in>| flexSet"
        by (auto simp: list_all_iff)
      with n'_in_dom dom_disjoint show False by auto
    qed
    thus "apply_subst subst vTy = vTy" by (rule apply_subst_disjoint_id)
  qed
  thus ?thesis by (auto simp: list_all_iff)
qed


(* If a binding-list bound on a record decomposes into one for a member field. *)
lemma dec_pattern_var_bindings_record_field_subset:
  assumes "(name, p) \<in> set flds"
  shows "set (dec_pattern_var_bindings p)
           \<subseteq> set (dec_pattern_var_bindings_list (map snd flds))"
using assms proof (induction flds)
  case Nil
  thus ?case by simp
next
  case (Cons hd rest)
  obtain n0 p0 where hd_eq: "hd = (n0, p0)" by (cases hd) auto
  show ?case
  proof (cases "(name, p) = hd")
    case True
    with hd_eq have "p = p0" by simp
    thus ?thesis using hd_eq by simp
  next
    case False
    with Cons.prems have "(name, p) \<in> set rest" by simp
    from Cons.IH[OF this] have
      "set (dec_pattern_var_bindings p)
         \<subseteq> set (dec_pattern_var_bindings_list (map snd rest))" .
    thus ?thesis using hd_eq by force
  qed
qed

(* When finalSubst is identity on dp's binding types, applying it to dp
   yields dp unchanged. *)
lemma apply_subst_to_dec_pattern_id_of_bindings_id:
  assumes "list_all (\<lambda>(_, _, vTy). apply_subst subst vTy = vTy)
                    (dec_pattern_var_bindings dp)"
  shows "apply_subst_to_dec_pattern subst dp = dp"
  using assms
proof (induction dp)
  case (DP_Var vr n ty)
  thus ?case by simp
next
  case (DP_Record flds)
  have all_pairs:
    "\<And>name p. (name, p) \<in> set flds \<Longrightarrow> apply_subst_to_dec_pattern subst p = p"
  proof -
    fix name p assume mem: "(name, p) \<in> set flds"
    have sub: "set (dec_pattern_var_bindings p)
                 \<subseteq> set (dec_pattern_var_bindings_list (map snd flds))"
      using dec_pattern_var_bindings_record_field_subset[OF mem] .
    have "list_all (\<lambda>(_, _, vTy). apply_subst subst vTy = vTy)
                   (dec_pattern_var_bindings_list (map snd flds))"
      using DP_Record.prems by simp
    hence pre_p: "list_all (\<lambda>(_, _, vTy). apply_subst subst vTy = vTy)
                           (dec_pattern_var_bindings p)"
      using sub by (auto simp: list_all_iff)
    have p_in_snds: "p \<in> Basic_BNFs.snds (name, p)" by simp
    show "apply_subst_to_dec_pattern subst p = p"
      using DP_Record.IH[OF mem p_in_snds pre_p] .
  qed
  have list_eq:
    "\<And>xs :: (string \<times> DecPattern) list.
       (\<forall>(name, p) \<in> set xs. apply_subst_to_dec_pattern subst p = p)
       \<Longrightarrow> map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern subst p)) xs = xs"
    subgoal for xs by (induction xs) auto
    done
  have "map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern subst p)) flds = flds"
    using list_eq[of flds] all_pairs by blast
  thus ?case by simp
next
  case (DP_Variant cn opt)
  show ?case
  proof (cases opt)
    case None
    thus ?thesis by simp
  next
    case (Some inner)
    with DP_Variant have "apply_subst_to_dec_pattern subst inner = inner" by simp
    thus ?thesis using Some by simp
  qed
qed simp_all


(* fmlookup on TE_LocalVars of a foldr extend_env_one_var: returns either
   the type from the binding list (last-write-wins for foldr) or the
   underlying env's lookup. *)
lemma fmlookup_TE_LocalVars_foldr_extend_env_one_var:
  "fmlookup (TE_LocalVars (foldr (extend_env_one_var constOf ghost) bs env)) name
   = (case map_of (map (\<lambda>(vr, n, ty). (n, ty)) bs) name of
        Some ty \<Rightarrow> Some ty
      | None \<Rightarrow> fmlookup (TE_LocalVars env) name)"
proof (induction bs arbitrary: env)
  case Nil
  thus ?case by simp
next
  case (Cons b rest)
  obtain vr n ty where b_eq: "b = (vr, n, ty)" by (cases b) auto
  show ?case
  proof (cases "name = n")
    case True
    thus ?thesis
      using b_eq by (simp add: extend_env_one_var_def)
  next
    case False
    have step: "TE_LocalVars (extend_env_one_var constOf ghost b
                  (foldr (extend_env_one_var constOf ghost) rest env))
                = fmupd n ty (TE_LocalVars (foldr (extend_env_one_var constOf ghost) rest env))"
      using b_eq by (simp add: extend_env_one_var_def)
    show ?thesis
      using False b_eq step Cons.IH
      by simp
  qed
qed

(* Correctness for finalize_match_arms. After it returns Inr finalizedArms:
   each (dp, env_i) pair satisfies dp = apply_subst_to_dec_pattern accSubst (raw dp_i),
   env_i = extend_env_with_pattern_vars env constOf ghost [dp], dp's variable bindings are all
   meta-free under env's tyvars, and env_i is well-formed (both tyenv_well_formed
   and elabenv_well_formed). *)
lemma finalize_match_arms_correct:
  assumes "finalize_match_arms env constOf ghost loc accSubst rawDps = Inr finalizedArms"
      and "tyenv_well_formed env"
      and "elabenv_well_formed env elabEnv"
      \<comment> \<open>Substituted dps' bindings are well-kinded under env. \<close>
      and substDps_bind_wk:
        "list_all (\<lambda>dp. list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy)
                                 (dec_pattern_var_bindings dp))
                  (map (apply_subst_to_dec_pattern accSubst) rawDps)"
      \<comment> \<open>And runtime, in non-ghost contexts. \<close>
      and substDps_bind_rt:
        "ghost = NotGhost \<Longrightarrow>
         list_all (\<lambda>dp. list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy)
                                 (dec_pattern_var_bindings dp))
                  (map (apply_subst_to_dec_pattern accSubst) rawDps)"
  shows "length finalizedArms = length rawDps
       \<and> list_all2
           (\<lambda>(dp, env_i) rawDp.
              dp = apply_subst_to_dec_pattern accSubst rawDp
              \<and> env_i = extend_env_with_pattern_vars env constOf ghost [dp]
              \<and> list_all (\<lambda>(_, _, vTy).
                            list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                         (dec_pattern_var_bindings dp)
              \<and> tyenv_well_formed env_i
              \<and> elabenv_well_formed env_i elabEnv)
           finalizedArms rawDps"
proof -
  let ?substDps = "map (apply_subst_to_dec_pattern accSubst) rawDps"
  \<comment> \<open>The if-condition was False (else assms(1) would be Inl). \<close>
  have not_clash:
    "\<not> list_ex (\<lambda>dp. list_ex (\<lambda>(_, _, vTy).
                       \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                              (dec_pattern_var_bindings dp)) ?substDps"
    using assms(1)
    unfolding finalize_match_arms_def Let_def
    by (simp split: if_splits)
  have finalizedArms_eq:
    "finalizedArms = map (\<lambda>dp. (dp, extend_env_with_pattern_vars env constOf ghost [dp])) ?substDps"
    using assms(1) not_clash
    unfolding finalize_match_arms_def Let_def
    by (simp split: if_splits)

  have len_eq: "length finalizedArms = length rawDps"
    using finalizedArms_eq by simp

  \<comment> \<open>Per-substDp meta-safety from the negated list_ex condition. \<close>
  have meta_safe:
    "list_all (\<lambda>dp. list_all (\<lambda>(_, _, vTy).
                      list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                              (dec_pattern_var_bindings dp))
              ?substDps"
    using not_clash
    by (force simp: list_all_iff list_ex_iff case_prod_unfold)

  \<comment> \<open>Build the per-arm conjunction. \<close>
  have per_arm:
    "list_all2
       (\<lambda>(dp, env_i) rawDp.
          dp = apply_subst_to_dec_pattern accSubst rawDp
          \<and> env_i = extend_env_with_pattern_vars env constOf ghost [dp]
          \<and> list_all (\<lambda>(_, _, vTy).
                        list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                     (dec_pattern_var_bindings dp)
          \<and> tyenv_well_formed env_i
          \<and> elabenv_well_formed env_i elabEnv)
       finalizedArms rawDps"
  proof -
    have "\<And>i. i < length rawDps \<Longrightarrow>
           (case finalizedArms ! i of (dp, env_i) \<Rightarrow>
             dp = apply_subst_to_dec_pattern accSubst (rawDps ! i)
             \<and> env_i = extend_env_with_pattern_vars env constOf ghost [dp]
             \<and> list_all (\<lambda>(_, _, vTy).
                           list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                        (dec_pattern_var_bindings dp)
             \<and> tyenv_well_formed env_i
             \<and> elabenv_well_formed env_i elabEnv)"
    proof -
      fix i assume i_lt: "i < length rawDps"
      let ?dp_i = "apply_subst_to_dec_pattern accSubst (rawDps ! i)"
      let ?env_i = "extend_env_with_pattern_vars env constOf ghost [?dp_i]"
      have nth_eq: "finalizedArms ! i = (?dp_i, ?env_i)"
        using finalizedArms_eq i_lt by simp
      have substDp_in: "?dp_i \<in> set ?substDps"
        using i_lt by simp
      have ms_at: "list_all (\<lambda>(_, _, vTy).
                              list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                            (dec_pattern_var_bindings ?dp_i)"
        using meta_safe substDp_in by (simp add: i_lt list_all_length)
      \<comment> \<open>Well-kinded: from substDps_bind_wk. \<close>
      have wk_at: "list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy) (dec_pattern_var_bindings ?dp_i)"
        using substDps_bind_wk substDp_in by (simp add: i_lt list_all_length)
      \<comment> \<open>Runtime: from substDps_bind_rt (in non-ghost). \<close>
      have rt_at_ng:
        "ghost = NotGhost \<Longrightarrow>
         list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy) (dec_pattern_var_bindings ?dp_i)"
        using substDps_bind_rt substDp_in by (simp add: i_lt list_all_length)
      \<comment> \<open>Well-formedness of env_i. The hypotheses of
          tyenv_well_formed_extend_env_with_pattern_vars are over
          dec_pattern_var_bindings_list [?dp_i], which reduces to
          dec_pattern_var_bindings ?dp_i. \<close>
      have wk_at_list:
        "list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy)
                  (dec_pattern_var_bindings_list [?dp_i])"
        using wk_at by simp
      have rt_at_ng_list:
        "ghost = NotGhost \<Longrightarrow>
         list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy)
                  (dec_pattern_var_bindings_list [?dp_i])"
        using rt_at_ng by simp
      have env_i_wf: "tyenv_well_formed ?env_i"
        using tyenv_well_formed_extend_env_with_pattern_vars[OF assms(2) wk_at_list rt_at_ng_list] .
      have env_i_wf_elab: "elabenv_well_formed ?env_i elabEnv"
        by (simp add: assms(3) elabenv_well_formed_extend_env_with_pattern_vars)
      show "(case finalizedArms ! i of (dp, env_i) \<Rightarrow>
              dp = apply_subst_to_dec_pattern accSubst (rawDps ! i)
              \<and> env_i = extend_env_with_pattern_vars env constOf ghost [dp]
              \<and> list_all (\<lambda>(_, _, vTy).
                            list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                         (dec_pattern_var_bindings dp)
              \<and> tyenv_well_formed env_i
              \<and> elabenv_well_formed env_i elabEnv)"
        unfolding nth_eq using ms_at env_i_wf env_i_wf_elab by simp
    qed
    thus ?thesis
      unfolding list_all2_conv_all_nth using len_eq by (simp add: case_prod_app)
  qed

  show ?thesis using len_eq per_arm by simp
qed


end

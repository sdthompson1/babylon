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

(* A successfully resolved pattern constructor is a data constructor of env. *)
lemma resolve_pattern_ctor_lookup:
  assumes "resolve_pattern_ctor env elabEnv ghost loc ctorName
             = Inr (dtName, tyvars, payloadTy, isNullary)"
  shows "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)"
  using assms unfolding resolve_pattern_ctor_def
  by (auto split: option.splits if_splits)

(* decorate_pattern_list produces one decorated pattern per input pattern. *)
lemma decorate_pattern_list_length:
  "decorate_pattern_list env elabEnv ghost pats scrutTys = Inr dps
   \<Longrightarrow> length dps = length pats"
proof (induction pats arbitrary: scrutTys dps)
  case Nil
  thus ?case by simp
next
  case (Cons p ps)
  let ?tsRest = "case scrutTys of [] \<Rightarrow> [] | _ # tsRest \<Rightarrow> tsRest"
  from Cons.prems obtain dp dpsRest where
    dec_rest: "decorate_pattern_list env elabEnv ghost ps ?tsRest = Inr dpsRest" and
    dps_eq: "dps = dp # dpsRest"
    by (auto simp: Let_def split: sum.splits)
  from Cons.IH[OF dec_rest] show ?case using dps_eq by simp
qed

(* The variables bound by a pattern list are those bound by its members. *)
lemma set_dec_pattern_var_bindings_list:
  "set (dec_pattern_var_bindings_list ps)
   = (\<Union>p \<in> set ps. set (dec_pattern_var_bindings p))"
  by (induction ps) auto

(* The types that a record pattern's sub-patterns are checked against are
   field types of the record. *)
lemma user_field_types_subset:
  assumes no_unknown: "unknown_field_names fieldTypes userFlds = []"
  shows "set (user_field_types fieldTypes userFlds) \<subseteq> set (map snd fieldTypes)"
proof
  fix ty assume "ty \<in> set (user_field_types fieldTypes userFlds)"
  then obtain name pat where
    in_flds: "(name, pat) \<in> set userFlds" and
    ty_eq: "ty = (case map_of fieldTypes name of Some t \<Rightarrow> t | None \<Rightarrow> CoreTy_Var '''')"
    unfolding user_field_types_def by auto
  have name_in: "name \<in> set (map fst userFlds)" using in_flds by force
  have "filter (\<lambda>n. map_of fieldTypes n = None) (map fst userFlds) = []"
    using no_unknown unfolding unknown_field_names_def by simp
  hence "\<forall>n \<in> set (map fst userFlds). map_of fieldTypes n \<noteq> None"
    by (auto simp: filter_empty_conv)
  hence "map_of fieldTypes name \<noteq> None" using name_in by blast
  then obtain t where lk: "map_of fieldTypes name = Some t" by auto
  hence "(name, t) \<in> set fieldTypes" by (rule map_of_SomeD)
  hence "t \<in> set (map snd fieldTypes)" by force
  thus "ty \<in> set (map snd fieldTypes)" using ty_eq lk by simp
qed

(* build_record_dec_patterns introduces no variables: every pattern it emits is
   either a wildcard or one of the user's (decorated) sub-patterns. *)
lemma build_record_dec_patterns_bindings_subset:
  "set (dec_pattern_var_bindings_list
          (map snd (build_record_dec_patterns fieldTypes names decPats)))
   \<subseteq> set (dec_pattern_var_bindings_list decPats)"
proof
  let ?built = "build_record_dec_patterns fieldTypes names decPats"
  fix b assume "b \<in> set (dec_pattern_var_bindings_list (map snd ?built))"
  then obtain q where
    q_in: "q \<in> set (map snd ?built)" and
    b_in: "b \<in> set (dec_pattern_var_bindings q)"
    unfolding set_dec_pattern_var_bindings_list by blast
  from q_in obtain n where q_eq: "q = lookup_or_wildcard (zip names decPats) n"
    unfolding build_record_dec_patterns_def Let_def by auto
  have "q \<in> set decPats"
  proof (cases "map_of (zip names decPats) n")
    case None
    hence "q = DP_Wildcard" using q_eq unfolding lookup_or_wildcard_def by simp
    thus ?thesis using b_in by simp
  next
    case (Some p)
    hence "(n, p) \<in> set (zip names decPats)" by (rule map_of_SomeD)
    hence "p \<in> set decPats" by (rule set_zip_rightD)
    thus ?thesis using q_eq Some unfolding lookup_or_wildcard_def by simp
  qed
  thus "b \<in> set (dec_pattern_var_bindings_list decPats)"
    unfolding set_dec_pattern_var_bindings_list using b_in by blast
qed

(* The record pattern assembled by build_record_dec_patterns is compatible with
   the record type, given that each of the user's sub-patterns is compatible with
   the type of the field it names. Fields the user omitted become wildcards. *)
lemma build_record_dec_patterns_compatible:
  assumes compat: "dec_pattern_compatible_list env decPats
                     (user_field_types fieldTypes userFlds)"
      and user_distinct: "distinct (map fst userFlds)"
      and ft_distinct: "distinct (map fst fieldTypes)"
  shows "dec_pattern_compatible env
           (DP_Record (build_record_dec_patterns fieldTypes (map fst userFlds) decPats))
           (CoreTy_Record fieldTypes)"
proof -
  let ?builtFlds = "build_record_dec_patterns fieldTypes (map fst userFlds) decPats"
  let ?userMap = "zip (map fst userFlds) decPats"
  let ?ufts = "user_field_types fieldTypes userFlds"

  have len_ufts: "length ?ufts = length userFlds"
    unfolding user_field_types_def by simp
  have len_dec_pats: "length decPats = length userFlds"
    using compat len_ufts by (simp add: dec_pattern_compatible_list_iff)
  have compat_nth:
    "\<forall>k < length decPats. dec_pattern_compatible env (decPats ! k) (?ufts ! k)"
    using compat by (simp add: dec_pattern_compatible_list_iff)

  have map_fst_built: "map fst ?builtFlds = map fst fieldTypes"
    unfolding build_record_dec_patterns_def Let_def by (induction fieldTypes) auto
  have len_built: "length ?builtFlds = length fieldTypes"
    unfolding build_record_dec_patterns_def Let_def by simp

  \<comment> \<open>The i-th emitted pattern is compatible with the i-th field type.\<close>
  have pointwise:
    "\<forall>i < length fieldTypes.
       dec_pattern_compatible env (snd (?builtFlds ! i)) (snd (fieldTypes ! i))"
  proof (intro allI impI)
    fix i assume i_bound: "i < length fieldTypes"
    let ?fi_name = "fst (fieldTypes ! i)"
    let ?fi_ty = "snd (fieldTypes ! i)"
    have built_ith:
      "?builtFlds ! i = (?fi_name, lookup_or_wildcard ?userMap ?fi_name)"
      unfolding build_record_dec_patterns_def Let_def using i_bound
      by (simp add: case_prod_unfold)
    show "dec_pattern_compatible env (snd (?builtFlds ! i)) (snd (fieldTypes ! i))"
    proof (cases "?fi_name \<in> set (map fst userFlds)")
      case True
      \<comment> \<open>The user supplied this field, at index j of the pattern.\<close>
      then obtain j where j_bound: "j < length userFlds"
                      and j_eq: "map fst userFlds ! j = ?fi_name"
        by (metis in_set_conv_nth length_map)
      have user_j_name: "fst (userFlds ! j) = ?fi_name"
        using j_eq j_bound by simp
      have map_of_userMap: "map_of ?userMap ?fi_name = Some (decPats ! j)"
        using user_distinct j_bound j_eq len_dec_pats
        by (metis (no_types) length_map map_of_zip_nth)
      have lookup_eq: "lookup_or_wildcard ?userMap ?fi_name = decPats ! j"
        unfolding lookup_or_wildcard_def using map_of_userMap by simp

      \<comment> \<open>The type the j-th sub-pattern was checked against is the i-th field type:
          the field names of the record type are distinct, so looking the name up
          and indexing by position agree.\<close>
      have ft_zip: "fieldTypes = zip (map fst fieldTypes) (map snd fieldTypes)"
        by (simp add: zip_map_fst_snd)
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
      have ufts_j: "?ufts ! j = ?fi_ty"
        unfolding user_field_types_def
        using j_bound user_j_name map_of_ft
        by (simp add: case_prod_unfold)

      have j_lt: "j < length decPats" using j_bound len_dec_pats by simp
      have "dec_pattern_compatible env (decPats ! j) (?ufts ! j)"
        using compat_nth j_lt by blast
      thus ?thesis using built_ith lookup_eq ufts_j by simp
    next
      case False
      \<comment> \<open>The user did not supply this field: the emitted pattern is a wildcard.\<close>
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
      show ?thesis using built_ith lookup_wild by simp
    qed
  qed

  have list_compat:
    "dec_pattern_compatible_list env (map snd ?builtFlds) (map snd fieldTypes)"
    using pointwise len_built by (simp add: dec_pattern_compatible_list_iff)
  show ?thesis using map_fst_built list_compat by simp
qed

(* Main correctness theorem for decorate_pattern: a successfully decorated
   pattern is compatible with the scrutinee type it was checked against.

   The scrutinee type must be well-kinded (this is what makes the field names
   of a record type distinct, so that looking a field up by name and by
   position agree). It may be well-kinded in a larger env than the one the
   decorator ran in (envK; in practice env extended with the metavariables of
   the statement being elaborated), so long as that env has the same data
   constructors. *)
lemma decorate_pattern_correct:
  "decorate_pattern env elabEnv ghost pat scrutTy = Inr dp
   \<Longrightarrow> tyenv_well_formed envK
   \<Longrightarrow> TE_DataCtors envK = TE_DataCtors env
   \<Longrightarrow> is_well_kinded envK scrutTy
   \<Longrightarrow> dec_pattern_compatible env dp scrutTy"
and decorate_pattern_list_correct:
  "decorate_pattern_list env elabEnv ghost pats scrutTys = Inr dps
   \<Longrightarrow> length pats = length scrutTys
   \<Longrightarrow> tyenv_well_formed envK
   \<Longrightarrow> TE_DataCtors envK = TE_DataCtors env
   \<Longrightarrow> list_all (is_well_kinded envK) scrutTys
   \<Longrightarrow> dec_pattern_compatible_list env dps scrutTys"
proof (induction env elabEnv ghost pat scrutTy
       and env elabEnv ghost pats scrutTys
       arbitrary: dp and dps
       rule: decorate_pattern_decorate_pattern_list.induct)
  case (1 env elabEnv ghost loc vr name scrutTy)
  \<comment> \<open>BabPat_Var. \<close>
  from "1.prems"(1) have "dp = DP_Var vr name scrutTy"
    by (auto split: if_splits)
  thus ?case by simp
next
  case (2 env elabEnv ghost loc scrutTy)
  \<comment> \<open>BabPat_Wildcard. \<close>
  from "2.prems"(1) have "dp = DP_Wildcard" by auto
  thus ?case by simp
next
  case (3 env elabEnv ghost loc b scrutTy)
  \<comment> \<open>BabPat_Bool. \<close>
  from "3.prems"(1) have "scrutTy = CoreTy_Bool" and "dp = DP_Bool b"
    by (auto split: if_splits)
  thus ?case by simp
next
  case (4 env elabEnv ghost loc i scrutTy)
  \<comment> \<open>BabPat_Int. \<close>
  from "4.prems"(1) obtain sign bits where
    "scrutTy = CoreTy_FiniteInt sign bits" and
    "int_in_range (int_range sign bits) i" and
    "dp = DP_Int i"
    by (auto split: CoreType.splits if_splits)
  thus ?case by simp
next
  case (5 env elabEnv ghost loc pats scrutTy)
  \<comment> \<open>BabPat_Tuple: the scrutinee is a record with the tuple field names; the
      sub-patterns are checked against its field types, in order. \<close>
  from "5.prems"(1) obtain fieldTypes where
    scrut_eq: "scrutTy = CoreTy_Record fieldTypes"
    by (auto split: CoreType.splits)
  from "5.prems"(1) scrut_eq have
    names_eq: "map fst fieldTypes = tuple_field_names (length pats)"
    by (auto split: if_splits)
  from "5.prems"(1) scrut_eq names_eq obtain decPats where
    rec: "decorate_pattern_list env elabEnv ghost pats (map snd fieldTypes) = Inr decPats" and
    dp_eq: "dp = DP_Record (zip (map fst fieldTypes) decPats)"
    by (auto split: sum.splits)

  have len_ft: "length fieldTypes = length pats"
    using names_eq by (metis length_map length_tuple_field_names)
  have len_pats: "length pats = length (map snd fieldTypes)"
    using len_ft by simp
  have fts_wk: "list_all (is_well_kinded envK) (map snd fieldTypes)"
    using "5.prems"(4) scrut_eq by simp

  have rec_compat: "dec_pattern_compatible_list env decPats (map snd fieldTypes)"
    using "5.IH"[OF scrut_eq names_eq rec len_pats "5.prems"(2) "5.prems"(3) fts_wk] .
  have len_dec: "length decPats = length fieldTypes"
    using decorate_pattern_list_length[OF rec] len_ft by simp

  show ?case
    unfolding dp_eq scrut_eq
    using rec_compat len_dec by simp
next
  case (6 env elabEnv ghost loc userFlds scrutTy)
  \<comment> \<open>BabPat_Record. The user supplies a subset of the fields; the recursive call
      checks those against the corresponding field types, and
      build_record_dec_patterns then reorders into declaration order, filling
      DP_Wildcard for omitted fields. \<close>
  from "6.prems"(1) have no_dup: "first_duplicate_name fst userFlds = None"
    by (auto split: option.splits)
  from "6.prems"(1) no_dup obtain fieldTypes where
    scrut_eq: "scrutTy = CoreTy_Record fieldTypes"
    by (auto split: CoreType.splits)
  from "6.prems"(1) no_dup scrut_eq have
    no_unknown: "unknown_field_names fieldTypes userFlds = []"
    by (auto split: list.splits)
  from "6.prems"(1) no_dup scrut_eq no_unknown obtain decPats where
    rec: "decorate_pattern_list env elabEnv ghost (map snd userFlds)
            (user_field_types fieldTypes userFlds) = Inr decPats" and
    dp_eq: "dp = DP_Record (build_record_dec_patterns fieldTypes
                              (map fst userFlds) decPats)"
    by (auto split: sum.splits)

  have len_user: "length (map snd userFlds) = length (user_field_types fieldTypes userFlds)"
    by (simp add: user_field_types_def)

  \<comment> \<open>The record type is well-kinded: distinct field names, well-kinded field types. \<close>
  have ft_wk: "is_well_kinded envK (CoreTy_Record fieldTypes)"
    using "6.prems"(4) scrut_eq by simp
  have ft_distinct: "distinct (map fst fieldTypes)"
    using ft_wk by simp
  have ft_snd_wk: "list_all (is_well_kinded envK) (map snd fieldTypes)"
    using ft_wk by simp
  have ufts_wk: "list_all (is_well_kinded envK) (user_field_types fieldTypes userFlds)"
    using ft_snd_wk user_field_types_subset[OF no_unknown]
    unfolding list_all_iff by blast

  have rec_compat:
    "dec_pattern_compatible_list env decPats (user_field_types fieldTypes userFlds)"
    using "6.IH"[OF no_dup scrut_eq no_unknown rec len_user
                    "6.prems"(2) "6.prems"(3) ufts_wk] .

  have user_distinct: "distinct (map fst userFlds)"
    using no_dup by (rule first_duplicate_name_None_implies_distinct)

  show ?case
    unfolding dp_eq scrut_eq
    using build_record_dec_patterns_compatible[OF rec_compat user_distinct ft_distinct] .
next
  case (7 env elabEnv ghost loc ctorName optPayload scrutTy)
  \<comment> \<open>BabPat_Variant: the scrutinee is an instance of the constructor's datatype;
      the payload pattern (if any) is checked against the instantiated payload type. \<close>
  from "7.prems"(1) obtain dtName tyvars payloadTy isNullary where
    rpc: "resolve_pattern_ctor env elabEnv ghost loc ctorName
            = Inr (dtName, tyvars, payloadTy, isNullary)"
    by (auto split: sum.splits)
  from "7.prems"(1) rpc obtain scrutDtName tyArgs where
    scrut_eq: "scrutTy = CoreTy_Datatype scrutDtName tyArgs"
    by (auto split: CoreType.splits)
  from "7.prems"(1) rpc scrut_eq have
    shape_ok: "scrutDtName = dtName \<and> length tyArgs = length tyvars"
    by (auto split: if_splits)
  from "7.prems"(1) rpc scrut_eq shape_ok obtain res where
    chk: "check_payload_presence loc ctorName isNullary optPayload = Inr res"
    by (auto split: sum.splits)

  have ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)"
    using resolve_pattern_ctor_lookup[OF rpc] .

  show ?case
  proof (cases res)
    case None
    from "7.prems"(1) rpc scrut_eq shape_ok chk None
    have dp_eq: "dp = DP_Variant ctorName None"
      by auto
    show ?thesis
      unfolding dp_eq scrut_eq
      using ctor_lookup shape_ok by simp
  next
    case (Some inner)
    let ?instPayloadTy = "apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    from "7.prems"(1) rpc scrut_eq shape_ok chk Some obtain dpInner where
      rec: "decorate_pattern env elabEnv ghost inner ?instPayloadTy = Inr dpInner" and
      dp_eq: "dp = DP_Variant ctorName (Some dpInner)"
      by (auto simp: Let_def split: sum.splits)

    \<comment> \<open>The instantiated payload type is well-kinded (in envK): the declared payload
        type is well-kinded over the constructor's type parameters, and the
        scrutinee's type arguments are well-kinded. \<close>
    have ctor_lookup_K:
      "fmlookup (TE_DataCtors envK) ctorName = Some (dtName, tyvars, payloadTy)"
      using ctor_lookup "7.prems"(3) by simp
    have payload_wk:
      "is_well_kinded (envK\<lparr>TE_TypeVars := TE_AbstractTypes envK |\<union>| fset_of_list tyvars\<rparr>)
                      payloadTy"
      using "7.prems"(2) ctor_lookup_K
      unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by force
    have abs_sub: "TE_AbstractTypes envK |\<subseteq>| TE_TypeVars envK"
      using "7.prems"(2)
      unfolding tyenv_well_formed_def tyenv_abstract_types_subset_def by blast
    have tyArgs_wk: "list_all (is_well_kinded envK) tyArgs"
      using "7.prems"(4) scrut_eq by (auto split: option.splits)
    have len_eq: "length tyvars = length tyArgs"
      using shape_ok by simp
    have inst_wk: "is_well_kinded envK ?instPayloadTy"
      using apply_subst_specializes_well_kinded[OF payload_wk tyArgs_wk len_eq abs_sub] .

    have inner_compat: "dec_pattern_compatible env dpInner ?instPayloadTy"
      using "7.IH"[OF rpc refl refl refl scrut_eq shape_ok chk Some refl rec
                      "7.prems"(2) "7.prems"(3) inst_wk] .

    show ?thesis
      unfolding dp_eq scrut_eq
      using ctor_lookup shape_ok inner_compat by simp
  qed
next
  case (8 env elabEnv ghost tys)
  \<comment> \<open>decorate_pattern_list: empty. \<close>
  from "8.prems"(1) have "dps = []" by simp
  moreover from "8.prems"(2) have "tys = []" by simp
  ultimately show ?case by simp
next
  case (9 env elabEnv ghost p ps tys)
  \<comment> \<open>decorate_pattern_list: cons. \<close>
  from "9.prems"(2) obtain t tsRest where
    tys_eq: "tys = t # tsRest" and len_rest: "length ps = length tsRest"
    by (cases tys) auto
  from "9.prems"(1) tys_eq obtain dp where
    dec_head: "decorate_pattern env elabEnv ghost p t = Inr dp"
    by (auto simp: Let_def split: sum.splits)
  from "9.prems"(1) tys_eq dec_head obtain dpsRest where
    dec_rest: "decorate_pattern_list env elabEnv ghost ps tsRest = Inr dpsRest" and
    dps_eq: "dps = dp # dpsRest"
    by (auto simp: Let_def split: sum.splits)

  let ?t_let = "case tys of [] \<Rightarrow> CoreTy_Var '''' | t # _ \<Rightarrow> t"
  let ?tsRest_let = "case tys of [] \<Rightarrow> [] | _ # tsRest \<Rightarrow> tsRest"
  have t_let_eq: "t = ?t_let" using tys_eq by simp
  have tsRest_let_eq: "tsRest = ?tsRest_let" using tys_eq by simp

  have t_wk: "is_well_kinded envK t"
    using "9.prems"(5) tys_eq by simp
  have tsRest_wk: "list_all (is_well_kinded envK) tsRest"
    using "9.prems"(5) tys_eq by simp

  have head_compat: "dec_pattern_compatible env dp t"
    using "9.IH"(1)[OF t_let_eq tsRest_let_eq dec_head "9.prems"(3) "9.prems"(4) t_wk] .
  have rest_compat: "dec_pattern_compatible_list env dpsRest tsRest"
    using "9.IH"(3)[OF t_let_eq tsRest_let_eq dec_head dec_rest len_rest
                       "9.prems"(3) "9.prems"(4) tsRest_wk] .

  show ?case
    using head_compat rest_compat dps_eq tys_eq by simp
qed

(* Every pattern variable is bound at a type with no unresolved metavariables:
   this is the check made in the variable case of decorate_pattern. *)
lemma decorate_pattern_bindings_closed:
  "decorate_pattern env elabEnv ghost pat scrutTy = Inr dp
   \<Longrightarrow> list_all (\<lambda>(_, _, vTy).
                  list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
               (dec_pattern_var_bindings dp)"
and decorate_pattern_list_bindings_closed:
  "decorate_pattern_list env elabEnv ghost pats scrutTys = Inr dps
   \<Longrightarrow> list_all (\<lambda>(_, _, vTy).
                  list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
               (dec_pattern_var_bindings_list dps)"
proof (induction env elabEnv ghost pat scrutTy
       and env elabEnv ghost pats scrutTys
       arbitrary: dp and dps
       rule: decorate_pattern_decorate_pattern_list.induct)
  case (1 env elabEnv ghost loc vr name scrutTy)
  \<comment> \<open>BabPat_Var: the check itself. \<close>
  from "1.prems" show ?case by (auto split: if_splits)
next
  case (2 env elabEnv ghost loc scrutTy)
  from "2.prems" show ?case by auto
next
  case (3 env elabEnv ghost loc b scrutTy)
  from "3.prems" show ?case by (auto split: if_splits)
next
  case (4 env elabEnv ghost loc i scrutTy)
  from "4.prems" show ?case by (auto split: CoreType.splits if_splits)
next
  case (5 env elabEnv ghost loc pats scrutTy)
  \<comment> \<open>BabPat_Tuple: the bindings are those of the sub-patterns. \<close>
  from "5.prems" obtain fieldTypes where
    scrut_eq: "scrutTy = CoreTy_Record fieldTypes"
    by (auto split: CoreType.splits)
  from "5.prems" scrut_eq have
    names_eq: "map fst fieldTypes = tuple_field_names (length pats)"
    by (auto split: if_splits)
  from "5.prems" scrut_eq names_eq obtain decPats where
    rec: "decorate_pattern_list env elabEnv ghost pats (map snd fieldTypes) = Inr decPats" and
    dp_eq: "dp = DP_Record (zip (map fst fieldTypes) decPats)"
    by (auto split: sum.splits)
  have len_ft: "length fieldTypes = length pats"
    using names_eq by (metis length_map length_tuple_field_names)
  have len_dec: "length decPats = length fieldTypes"
    using decorate_pattern_list_length[OF rec] len_ft by simp
  have snd_eq: "map snd (zip (map fst fieldTypes) decPats) = decPats"
    using len_dec by simp
  show ?case
    unfolding dp_eq
    using "5.IH"[OF scrut_eq names_eq rec] snd_eq len_dec by simp
next
  case (6 env elabEnv ghost loc userFlds scrutTy)
  \<comment> \<open>BabPat_Record: build_record_dec_patterns only adds wildcards. \<close>
  from "6.prems" have no_dup: "first_duplicate_name fst userFlds = None"
    by (auto split: option.splits)
  from "6.prems" no_dup obtain fieldTypes where
    scrut_eq: "scrutTy = CoreTy_Record fieldTypes"
    by (auto split: CoreType.splits)
  from "6.prems" no_dup scrut_eq have
    no_unknown: "unknown_field_names fieldTypes userFlds = []"
    by (auto split: list.splits)
  from "6.prems" no_dup scrut_eq no_unknown obtain decPats where
    rec: "decorate_pattern_list env elabEnv ghost (map snd userFlds)
            (user_field_types fieldTypes userFlds) = Inr decPats" and
    dp_eq: "dp = DP_Record (build_record_dec_patterns fieldTypes
                              (map fst userFlds) decPats)"
    by (auto split: sum.splits)
  have rec_closed:
    "list_all (\<lambda>(_, _, vTy).
                 list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
              (dec_pattern_var_bindings_list decPats)"
    using "6.IH"[OF no_dup scrut_eq no_unknown rec] .
  have sub: "set (dec_pattern_var_bindings dp)
               \<subseteq> set (dec_pattern_var_bindings_list decPats)"
    unfolding dp_eq
    using build_record_dec_patterns_bindings_subset[of fieldTypes "map fst userFlds" decPats]
    by simp
  show ?case
    using rec_closed sub unfolding list_all_iff by blast
next
  case (7 env elabEnv ghost loc ctorName optPayload scrutTy)
  \<comment> \<open>BabPat_Variant: the bindings are those of the payload pattern (if any). \<close>
  from "7.prems" obtain dtName tyvars payloadTy isNullary where
    rpc: "resolve_pattern_ctor env elabEnv ghost loc ctorName
            = Inr (dtName, tyvars, payloadTy, isNullary)"
    by (auto split: sum.splits)
  from "7.prems" rpc obtain scrutDtName tyArgs where
    scrut_eq: "scrutTy = CoreTy_Datatype scrutDtName tyArgs"
    by (auto split: CoreType.splits)
  from "7.prems" rpc scrut_eq have
    shape_ok: "scrutDtName = dtName \<and> length tyArgs = length tyvars"
    by (auto split: if_splits)
  from "7.prems" rpc scrut_eq shape_ok obtain res where
    chk: "check_payload_presence loc ctorName isNullary optPayload = Inr res"
    by (auto split: sum.splits)
  show ?case
  proof (cases res)
    case None
    from "7.prems" rpc scrut_eq shape_ok chk None
    have "dp = DP_Variant ctorName None"
      by auto
    thus ?thesis by simp
  next
    case (Some inner)
    let ?instPayloadTy = "apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    from "7.prems" rpc scrut_eq shape_ok chk Some obtain dpInner where
      rec: "decorate_pattern env elabEnv ghost inner ?instPayloadTy = Inr dpInner" and
      dp_eq: "dp = DP_Variant ctorName (Some dpInner)"
      by (auto simp: Let_def split: sum.splits)
    show ?thesis
      unfolding dp_eq
      using "7.IH"[OF rpc refl refl refl scrut_eq shape_ok chk Some refl rec] by simp
  qed
next
  case (8 env elabEnv ghost tys)
  from "8.prems" show ?case by simp
next
  case (9 env elabEnv ghost p ps tys)
  \<comment> \<open>decorate_pattern_list: cons. \<close>
  let ?t_let = "case tys of [] \<Rightarrow> CoreTy_Var '''' | t # _ \<Rightarrow> t"
  let ?tsRest_let = "case tys of [] \<Rightarrow> [] | _ # tsRest \<Rightarrow> tsRest"
  from "9.prems" obtain dp where
    dec_head: "decorate_pattern env elabEnv ghost p ?t_let = Inr dp"
    by (auto simp: Let_def split: sum.splits)
  from "9.prems" dec_head obtain dpsRest where
    dec_rest: "decorate_pattern_list env elabEnv ghost ps ?tsRest_let = Inr dpsRest" and
    dps_eq: "dps = dp # dpsRest"
    by (auto simp: Let_def split: sum.splits)
  have head_closed:
    "list_all (\<lambda>(_, _, vTy).
                 list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
              (dec_pattern_var_bindings dp)"
    using "9.IH"(1)[OF refl refl dec_head] .
  have rest_closed:
    "list_all (\<lambda>(_, _, vTy).
                 list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
              (dec_pattern_var_bindings_list dpsRest)"
    using "9.IH"(3)[OF refl refl dec_head dec_rest] .
  show ?case
    using head_closed rest_closed dps_eq by simp
qed

(* The types of the variables bound by a decorated pattern are well-kinded, and
   runtime in NotGhost mode, in the env the decorator ran in. This holds even when
   the scrutinee type itself mentions metavariables of the statement being
   elaborated (the interval [lo, hi)): the variable types are components of the
   scrutinee type, and contain no metavariables. *)
lemma decorate_pattern_bindings_well_kinded_runtime:
  assumes dec: "decorate_pattern env elabEnv ghost pat scrutTy = Inr dp"
      and wf: "tyenv_well_formed env"
      and scrut_wk: "is_well_kinded (extend_env_with_tyvars env ghost lo hi) scrutTy"
      and scrut_rt: "ghost = NotGhost
                       \<Longrightarrow> is_runtime_type (extend_env_with_tyvars env ghost lo hi) scrutTy"
      and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n lo"
  shows "list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy) (dec_pattern_var_bindings dp)"
    and "ghost = NotGhost
           \<Longrightarrow> list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy) (dec_pattern_var_bindings dp)"
proof -
  let ?envE = "extend_env_with_tyvars env ghost lo hi"
  have wfE: "tyenv_well_formed ?envE"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast
  have dcE: "TE_DataCtors ?envE = TE_DataCtors env"
    unfolding extend_env_with_tyvars_def by simp
  have dtE: "TE_Datatypes env = TE_Datatypes ?envE"
    unfolding extend_env_with_tyvars_def by simp
  have gdE: "TE_GhostDatatypes env = TE_GhostDatatypes ?envE"
    unfolding extend_env_with_tyvars_def by simp

  \<comment> \<open>In the extended env, the variable types are well-kinded / runtime because
      the pattern is compatible with the (well-kinded / runtime) scrutinee type. \<close>
  have compat: "dec_pattern_compatible env dp scrutTy"
    using decorate_pattern_correct[OF dec wfE dcE scrut_wk] .
  have compatE: "dec_pattern_compatible ?envE dp scrutTy"
    using compat dec_pattern_compatible_TE_DataCtors_cong[OF dcE] by simp
  have wkE: "list_all (\<lambda>(_, _, vTy). is_well_kinded ?envE vTy) (dec_pattern_var_bindings dp)"
    using dec_pattern_compatible_vars_well_kinded[OF compatE scrut_wk wfE] .

  \<comment> \<open>The variable types mention only type variables of env. \<close>
  have closed:
    "list_all (\<lambda>(_, _, vTy).
                 list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
              (dec_pattern_var_bindings dp)"
    using decorate_pattern_bindings_closed[OF dec] .
  have tvs_sub:
    "\<And>vr n vTy. (vr, n, vTy) \<in> set (dec_pattern_var_bindings dp)
        \<Longrightarrow> type_tyvars vTy \<subseteq> fset (TE_TypeVars env)"
  proof -
    fix vr n vTy assume b_in: "(vr, n, vTy) \<in> set (dec_pattern_var_bindings dp)"
    have "list_all (\<lambda>k. k |\<in>| TE_TypeVars env) (type_tyvars_list vTy)"
      using closed b_in by (auto simp: list_all_iff)
    thus "type_tyvars vTy \<subseteq> fset (TE_TypeVars env)"
      unfolding list_all_iff set_type_tyvars_list[symmetric] by auto
  qed

  show "list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy) (dec_pattern_var_bindings dp)"
  proof -
    have "\<And>vr n vTy. (vr, n, vTy) \<in> set (dec_pattern_var_bindings dp)
            \<Longrightarrow> is_well_kinded env vTy"
    proof -
      fix vr n vTy assume b_in: "(vr, n, vTy) \<in> set (dec_pattern_var_bindings dp)"
      have vTy_wkE: "is_well_kinded ?envE vTy"
        using wkE b_in by (auto simp: list_all_iff)
      show "is_well_kinded env vTy"
        using is_well_kinded_transfer[OF vTy_wkE tvs_sub[OF b_in] dtE] .
    qed
    thus ?thesis by (auto simp: list_all_iff)
  qed

  show "ghost = NotGhost
          \<Longrightarrow> list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy) (dec_pattern_var_bindings dp)"
  proof -
    assume ng: "ghost = NotGhost"
    have rtE: "list_all (\<lambda>(_, _, vTy). is_runtime_type ?envE vTy)
                        (dec_pattern_var_bindings dp)"
      using dec_pattern_compatible_vars_runtime[OF compatE scrut_rt[OF ng] scrut_wk wfE] .
    have rtvE: "TE_RuntimeTypeVars ?envE = TE_RuntimeTypeVars env |\<union>| mv_fset lo hi"
      unfolding extend_env_with_tyvars_def using ng by simp
    have "\<And>vr n vTy. (vr, n, vTy) \<in> set (dec_pattern_var_bindings dp)
            \<Longrightarrow> is_runtime_type env vTy"
    proof -
      fix vr n vTy assume b_in: "(vr, n, vTy) \<in> set (dec_pattern_var_bindings dp)"
      have vTy_rtE: "is_runtime_type ?envE vTy"
        using rtE b_in by (auto simp: list_all_iff)
      \<comment> \<open>Every type variable of vTy is in TE_TypeVars env, hence allocated below lo,
          hence not one of the interval's metavariables; being a runtime type variable
          of the extended env, it is therefore a runtime type variable of env. \<close>
      have tvs_rt: "type_tyvars vTy \<subseteq> fset (TE_RuntimeTypeVars env)"
      proof
        fix k assume k_in: "k \<in> type_tyvars vTy"
        have "k |\<in>| TE_TypeVars env" using tvs_sub[OF b_in] k_in by auto
        hence "tyvar_fresh_ok k lo" using bound by simp
        hence k_not_mv: "k |\<notin>| mv_fset lo hi"
          by (rule tyvar_fresh_ok_notin_mv_fset)
        have "k |\<in>| TE_RuntimeTypeVars ?envE"
          using is_runtime_type_tyvars_subset[OF vTy_rtE] k_in by auto
        thus "k \<in> fset (TE_RuntimeTypeVars env)"
          using k_not_mv unfolding rtvE by auto
      qed
      show "is_runtime_type env vTy"
        using is_runtime_type_transfer[OF vTy_rtE tvs_rt gdE] .
    qed
    thus "list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy) (dec_pattern_var_bindings dp)"
      by (auto simp: list_all_iff)
  qed
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


section \<open>Correctness for decorate_match_arms\<close>

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

(* Unpacking a successful decorate_match_arms: one output row per arm, carrying
   the arm's body unchanged; every decorated pattern is the result of decorating
   some pattern against the scrutinee type, and binds distinct variable names. *)
lemma decorate_match_arms_facts:
  "decorate_match_arms env elabEnv ghost scrutTy allowRefs arms = Inr rows
   \<Longrightarrow> length rows = length arms
       \<and> map snd rows = map snd arms
       \<and> (\<forall>dp \<in> set (map fst rows).
            (\<exists>pat. decorate_pattern env elabEnv ghost pat scrutTy = Inr dp)
            \<and> pattern_var_names_distinct [dp])"
proof (induction arms arbitrary: rows)
  case Nil
  thus ?case by simp
next
  case (Cons arm rest)
  obtain pat body where arm_eq: "arm = (pat, body)" by (cases arm) auto
  from Cons.prems arm_eq obtain dp where
    dec_eq: "decorate_pattern env elabEnv ghost pat scrutTy = Inr dp"
    by (auto split: sum.splits)
  from Cons.prems arm_eq dec_eq obtain check_res where
    chk_eq: "check_match_pattern allowRefs (bab_pattern_location pat) dp = Inr check_res"
    by (auto split: sum.splits)
  from Cons.prems arm_eq dec_eq chk_eq obtain restRows where
    rec_eq: "decorate_match_arms env elabEnv ghost scrutTy allowRefs rest = Inr restRows" and
    rows_eq: "rows = (dp, body) # restRows"
    by (auto split: sum.splits)
  have head:
    "(\<exists>pat. decorate_pattern env elabEnv ghost pat scrutTy = Inr dp)
     \<and> pattern_var_names_distinct [dp]"
    using dec_eq check_match_pattern_implies_distinctness[OF chk_eq] by blast
  show ?case
    using Cons.IH[OF rec_eq] head rows_eq arm_eq by simp
qed

(* Correctness for the per-arm pattern-decoration loop. After decorate_match_arms
   succeeds, every decorated pattern is compatible with the scrutinee type and
   binds distinct variable names; and the types of the variables it binds contain
   no unresolved metavariables, so they are well-kinded (and runtime, in NotGhost
   mode) in env itself -- even though the scrutinee type may mention metavariables
   of the statement being elaborated (the interval [lo, hi)). *)
lemma decorate_match_arms_correct:
  assumes dec: "decorate_match_arms env elabEnv ghost scrutTy allowRefs arms = Inr rows"
      and wf: "tyenv_well_formed env"
      and scrut_wk: "is_well_kinded (extend_env_with_tyvars env ghost lo hi) scrutTy"
      and scrut_rt: "ghost = NotGhost
                       \<longrightarrow> is_runtime_type (extend_env_with_tyvars env ghost lo hi) scrutTy"
      and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n lo"
  shows "length rows = length arms"
    and "map snd rows = map snd arms"
    and "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow> dec_pattern_compatible env dp scrutTy"
    and "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow> pattern_var_names_distinct [dp]"
    and "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow>
           list_all (\<lambda>(_, _, vTy).
                       list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                    (dec_pattern_var_bindings dp)"
    and "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow>
           list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy) (dec_pattern_var_bindings dp)"
    and "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow> ghost = NotGhost \<Longrightarrow>
           list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy) (dec_pattern_var_bindings dp)"
proof -
  note facts = decorate_match_arms_facts[OF dec]
  have per_dp:
    "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow>
       (\<exists>pat. decorate_pattern env elabEnv ghost pat scrutTy = Inr dp)
       \<and> pattern_var_names_distinct [dp]"
    using facts by blast
  let ?envE = "extend_env_with_tyvars env ghost lo hi"
  have wfE: "tyenv_well_formed ?envE"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast
  have dcE: "TE_DataCtors ?envE = TE_DataCtors env"
    unfolding extend_env_with_tyvars_def by simp

  show "length rows = length arms" using facts by simp
  show "map snd rows = map snd arms" using facts by simp
  show "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow> dec_pattern_compatible env dp scrutTy"
  proof -
    fix dp assume dp_in: "dp \<in> set (map fst rows)"
    from per_dp[OF dp_in] obtain pat where
      dpat: "decorate_pattern env elabEnv ghost pat scrutTy = Inr dp" by blast
    show "dec_pattern_compatible env dp scrutTy"
      using decorate_pattern_correct[OF dpat wfE dcE scrut_wk] .
  qed
  show "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow> pattern_var_names_distinct [dp]"
    using per_dp by blast
  show "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow>
          list_all (\<lambda>(_, _, vTy).
                      list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                   (dec_pattern_var_bindings dp)"
  proof -
    fix dp assume dp_in: "dp \<in> set (map fst rows)"
    from per_dp[OF dp_in] obtain pat where
      dpat: "decorate_pattern env elabEnv ghost pat scrutTy = Inr dp" by blast
    show "list_all (\<lambda>(_, _, vTy).
                      list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                   (dec_pattern_var_bindings dp)"
      using decorate_pattern_bindings_closed[OF dpat] .
  qed
  show "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow>
          list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy) (dec_pattern_var_bindings dp)"
  proof -
    fix dp assume dp_in: "dp \<in> set (map fst rows)"
    from per_dp[OF dp_in] obtain pat where
      dpat: "decorate_pattern env elabEnv ghost pat scrutTy = Inr dp" by blast
    show "list_all (\<lambda>(_, _, vTy). is_well_kinded env vTy) (dec_pattern_var_bindings dp)"
      using decorate_pattern_bindings_well_kinded_runtime(1)
              [OF dpat wf scrut_wk scrut_rt[rule_format] bound] .
  qed
  show "\<And>dp. dp \<in> set (map fst rows) \<Longrightarrow> ghost = NotGhost \<Longrightarrow>
          list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy) (dec_pattern_var_bindings dp)"
  proof -
    fix dp assume dp_in: "dp \<in> set (map fst rows)" and ng: "ghost = NotGhost"
    from per_dp[OF dp_in] obtain pat where
      dpat: "decorate_pattern env elabEnv ghost pat scrutTy = Inr dp" by blast
    show "list_all (\<lambda>(_, _, vTy). is_runtime_type env vTy) (dec_pattern_var_bindings dp)"
      using decorate_pattern_bindings_well_kinded_runtime(2)
              [OF dpat wf scrut_wk scrut_rt[rule_format] bound ng] .
  qed
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


end

theory MakeInterpStateCorrect
  imports MakeInterpState TypeSoundness "../core/CoreModuleTypecheck"
begin

(* ========================================================================== *)
(* Correctness of make_interp_state                                           *)
(* ========================================================================== *)

(* This theory proves that make_interp_state, applied to a closed and
   well-typed CoreModule (with contract-satisfying extern functions),
   produces a state satisfying state_matches_env against the normalized
   module's type environment, with an empty store typing.

   Proof plan. Write m' = normalize_module m and env = CM_TyEnv m'. The
   constructed state is base_interp_state with CM_GlobalVars m' installed as
   IS_Globals and the built function map as IS_Functions. The globals clause
   of state_matches_env follows directly: every declared global is defined
   (by closedness's domain equality) and its stored value has the declared
   type (module_globals_well_typed - the elaborator evaluated the
   initializers at compile time). Every declared non-ghost function got a
   matching InterpFun (build_interp_funs). *)


(* ========================================================================== *)
(* default_ctors_map                                                          *)
(* ========================================================================== *)

(* default_ctors_map answers exactly the lookups default_ctors_match asks
   about. *)
lemma default_ctors_map_lookup:
  assumes byType: "fmlookup (TE_DataCtorsByType env) dtName
                     = Some (defCtorName # otherCtors)"
      and ctor: "fmlookup (TE_DataCtors env) defCtorName
                     = Some (dtName', tyVars, payload)"
  shows "fmlookup (default_ctors_map env) dtName = Some (defCtorName, tyVars, payload)"
proof -
  have dc: "default_ctor_for env dtName = Some (defCtorName, tyVars, payload)"
    using byType ctor by (simp add: default_ctor_for_def)
  show ?thesis
    using byType dc by (simp add: default_ctors_map_def)
qed

(* Any state carrying default_ctors_map env satisfies default_ctors_match
   against any environment with the same datatype tables as env. *)
lemma default_ctors_map_match:
  assumes dcs: "IS_DefaultCtors state = default_ctors_map env0"
      and byType_eq: "TE_DataCtorsByType env = TE_DataCtorsByType env0"
      and ctors_eq: "TE_DataCtors env = TE_DataCtors env0"
  shows "default_ctors_match state env"
  unfolding default_ctors_match_def
proof (intro allI impI)
  fix dtName defCtorName otherCtors dtName' tyvars payload
  assume "fmlookup (TE_DataCtorsByType env) dtName = Some (defCtorName # otherCtors)"
     and "fmlookup (TE_DataCtors env) defCtorName = Some (dtName', tyvars, payload)"
  hence "fmlookup (default_ctors_map env0) dtName = Some (defCtorName, tyvars, payload)"
    unfolding byType_eq ctors_eq by (rule default_ctors_map_lookup)
  thus "fmlookup (IS_DefaultCtors state) dtName = Some (defCtorName, tyvars, payload)"
    by (simp add: dcs)
qed


(* ========================================================================== *)
(* Body environments                                                          *)
(* ========================================================================== *)

(* For a non-ghost function in a module with no abstract types, the module
   typechecker's body environment coincides with the interpreter's. *)
lemma module_body_env_for_eq_body_env_for:
  assumes abs_empty: "TE_AbstractTypes env = {||}"
      and ng: "FI_Ghost info = NotGhost"
  shows "module_body_env_for env names info = body_env_for env names info"
  using assms unfolding module_body_env_for_def body_env_for_def by simp


(* ========================================================================== *)
(* build_interp_funs                                                          *)
(* ========================================================================== *)

(* A successful build gives every listed non-ghost function a matching
   InterpFun: the fields of make_interp_fun, with the Core body, or the
   supplied ExternFunc for an extern function. *)
lemma build_interp_funs_lookup_some:
  assumes ok: "build_interp_funs externs env pairs = Inr funs"
      and mem: "(name, f) \<in> set pairs"
      and dist: "distinct (map fst pairs)"
      and info_lk: "fmlookup (TE_Functions env) name = Some info"
      and ng: "FI_Ghost info = NotGhost"
  shows "\<exists>body. fmlookup funs name = Some (make_interp_fun info f body)
              \<and> (case CF_Body f of
                   Some stmts \<Rightarrow> body = Inl stmts
                 | None \<Rightarrow> (\<exists>externFun. fmlookup externs name = Some externFun
                                       \<and> body = Inr externFun))"
  using ok mem dist
proof (induction pairs arbitrary: funs)
  case Nil
  then show ?case by simp
next
  case (Cons p rest)
  obtain n1 f1 where p_eq: "p = (n1, f1)" by (cases p) auto
  from Cons.prems(1) p_eq obtain info1 where
    info1_lk: "fmlookup (TE_Functions env) n1 = Some info1"
    by (auto split: option.splits)
  from Cons.prems(1) p_eq info1_lk obtain acc where
    rest_ok: "build_interp_funs externs env rest = Inr acc"
    by (auto split: sum.splits)
  show ?case
  proof (cases "n1 = name")
    case True
    with Cons.prems(3) p_eq have not_in_rest: "name \<notin> fst ` set rest"
      by simp
    from Cons.prems(2) p_eq True not_in_rest have f1_eq: "f1 = f"
      by (metis fst_conv image_eqI set_ConsD prod.inject)
    from True info1_lk info_lk have info1_eq: "info1 = info" by simp
    show ?thesis
    proof (cases "CF_Body f")
      case (Some stmts)
      have "funs = fmupd name (make_interp_fun info f (Inl stmts)) acc"
        using Cons.prems(1) p_eq True f1_eq info1_lk info1_eq rest_ok ng Some
        by (auto split: if_splits)
      then show ?thesis using Some by simp
    next
      case None
      from Cons.prems(1) p_eq True f1_eq info1_lk info1_eq rest_ok ng None
      obtain externFun where
        ext_lk: "fmlookup externs name = Some externFun" and
        funs_eq: "funs = fmupd name (make_interp_fun info f (Inr externFun)) acc"
        by (auto split: if_splits option.splits)
      then show ?thesis using None by auto
    qed
  next
    case False
    from Cons.prems(1) p_eq info1_lk rest_ok False
    have lk_eq: "fmlookup funs name = fmlookup acc name"
      by (auto split: if_splits option.splits)
    from Cons.prems(2) p_eq False have mem_rest: "(name, f) \<in> set rest" by auto
    from Cons.prems(3) have dist_rest: "distinct (map fst rest)" by simp
    from Cons.IH[OF rest_ok mem_rest dist_rest] lk_eq show ?thesis by simp
  qed
qed

(* Names that occur in the list only as ghost functions (or not at all) are
   absent from the built map. *)
lemma build_interp_funs_lookup_none:
  assumes ok: "build_interp_funs externs env pairs = Inr funs"
      and ghost_only:
        "\<And>f. (name, f) \<in> set pairs \<Longrightarrow>
           \<exists>info. fmlookup (TE_Functions env) name = Some info \<and> FI_Ghost info = Ghost"
  shows "fmlookup funs name = None"
  using ok ghost_only
proof (induction pairs arbitrary: funs)
  case Nil
  then show ?case by simp
next
  case (Cons p rest)
  obtain n1 f1 where p_eq: "p = (n1, f1)" by (cases p) auto
  from Cons.prems(1) p_eq obtain info1 where
    info1_lk: "fmlookup (TE_Functions env) n1 = Some info1"
    by (auto split: option.splits)
  from Cons.prems(1) p_eq info1_lk obtain acc where
    rest_ok: "build_interp_funs externs env rest = Inr acc"
    by (auto split: sum.splits)
  have acc_none: "fmlookup acc name = None"
    using Cons.IH[OF rest_ok] Cons.prems(2) p_eq by auto
  show ?case
  proof (cases "n1 = name")
    case True
    from Cons.prems(2) p_eq True obtain info where
      "fmlookup (TE_Functions env) name = Some info" and "FI_Ghost info = Ghost"
      by auto
    with True info1_lk have ghost1: "FI_Ghost info1 = Ghost" by simp
    have "funs = acc"
      using Cons.prems(1) p_eq info1_lk rest_ok ghost1 by auto
    then show ?thesis using acc_none by simp
  next
    case False
    from Cons.prems(1) p_eq info1_lk rest_ok False
    have "fmlookup funs name = fmlookup acc name"
      by (auto split: if_splits option.splits)
    then show ?thesis using acc_none by simp
  qed
qed


(* ========================================================================== *)
(* sorted_list_of_fmap                                                        *)
(* ========================================================================== *)

(* The keys of the sorted association list are distinct. *)
lemma distinct_map_fst_sorted_list_of_fmap:
  "distinct (map fst (sorted_list_of_fmap m))"
proof -
  have "map fst (sorted_list_of_fmap m) = sorted_list_of_fset (fmdom m)"
    unfolding sorted_list_of_fmap_def by (simp add: comp_def)
  moreover have "distinct (sorted_list_of_fset (fmdom m))"
    by (simp add: sorted_list_of_fset.rep_eq)
  ultimately show ?thesis by simp
qed

(* Membership in the sorted association list is exactly map lookup. *)
lemma sorted_list_of_fmap_mem_iff:
  "((name, v) \<in> set (sorted_list_of_fmap m)) = (fmlookup m name = Some v)"
proof
  assume "(name, v) \<in> set (sorted_list_of_fmap m)"
  hence "map_of (sorted_list_of_fmap m) name = Some v"
    by (rule map_of_is_SomeI[OF distinct_map_fst_sorted_list_of_fmap])
  thus "fmlookup m name = Some v" by simp
next
  assume "fmlookup m name = Some v"
  hence "map_of (sorted_list_of_fmap m) name = Some v" by simp
  thus "(name, v) \<in> set (sorted_list_of_fmap m)" by (rule map_of_SomeD)
qed


(* ========================================================================== *)
(* The assembled state (globals + functions) matches the environment          *)
(* ========================================================================== *)

(* The state holding the module's global values and the built function map
   matches env: every declared global is defined (by the domain equality from
   closedness) and its stored value has the declared type
   (module_globals_well_typed); every declared non-ghost function has a
   matching InterpFun; nothing extra exists. *)
lemma assembled_state_matches:
  assumes wf: "tyenv_well_formed env"
      and scope: "tyenv_module_scope env"
      and tv: "TE_TypeVars env = {||}"
      and rtv: "TE_RuntimeTypeVars env = {||}"
      and gdom: "fmdom (TE_GlobalVars env) = fmdom globals"
      and fdom: "fmdom (TE_Functions env) = fmdom funDefs"
      and gwt: "module_globals_well_typed env globals"
      and fwt: "module_functions_well_typed env funDefs"
      and funs_ok: "build_interp_funs externs env (sorted_list_of_fmap funDefs) = Inr funs"
      and externs_ok: "\<And>name info externFun.
            \<lbrakk> fmlookup (TE_Functions env) name = Some info;
              fmlookup externs name = Some externFun \<rbrakk> \<Longrightarrow>
            extern_fun_contract env info externFun"
  shows "state_matches_env
           (base_interp_state env world \<lparr> IS_Globals := globals, IS_Functions := funs \<rparr>)
           env []"
proof -
  let ?st = "base_interp_state env world \<lparr> IS_Globals := globals, IS_Functions := funs \<rparr>"

  from scope have locals: "TE_LocalVars env = fmempty"
    and ghostlocals: "TE_GhostLocals env = {||}"
    and constlocals: "TE_ConstLocals env = {||}"
    and abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    unfolding tyenv_module_scope_def by simp_all
  have abs: "TE_AbstractTypes env = {||}" using abs_tv tv by simp

  have st_sel:
    "IS_Globals ?st = globals"
    "IS_Locals ?st = fmempty"
    "IS_Refs ?st = fmempty"
    "IS_Store ?st = []"
    "IS_ConstLocals ?st = {||}"
    "IS_TyArgs ?st = fmempty"
    "IS_DefaultCtors ?st = default_ctors_map env"
    "IS_Functions ?st = funs"
    by (simp_all add: base_interp_state_def)

  \<comment> \<open>Conjunct: declared globals exist with their declared types.\<close>
  have gv: "global_vars_exist_in_state ?st env"
    unfolding global_vars_exist_in_state_def
  proof (intro allI impI)
    fix n ty
    assume decl: "fmlookup (TE_GlobalVars env) n = Some ty"
    have "n |\<in>| fmdom globals" using fmdomI[OF decl] gdom by simp
    then obtain v where v_lk: "fmlookup globals n = Some v"
      by (auto simp add: fmlookup_dom_iff)
    obtain declTy where
      decl': "fmlookup (TE_GlobalVars env) n = Some declTy" and
      vt0: "value_has_type env v declTy"
      using gwt v_lk unfolding module_globals_well_typed_def by blast
    have "declTy = ty" using decl decl' by simp
    hence vt: "value_has_type env v ty" using vt0 by simp
    show "global_var_in_state_with_type ?st env n ty"
      unfolding global_var_in_state_with_type_def
      by (simp add: st_sel v_lk vt)
  qed

  \<comment> \<open>Conjunct: no globals beyond the declared ones.\<close>
  have neg: "no_extra_global_vars ?st env"
    unfolding no_extra_global_vars_def
  proof (intro allI impI)
    fix n
    assume a: "fmlookup (TE_GlobalVars env) n = None"
    have "n |\<notin>| fmdom (TE_GlobalVars env)"
      using a by (auto simp add: fmlookup_dom_iff)
    hence "n |\<notin>| fmdom globals" using gdom by simp
    thus "fmlookup (IS_Globals ?st) n = None"
      using fmdom_notD by (simp add: st_sel)
  qed

  \<comment> \<open>Conjunct: declared non-ghost functions exist with matching InterpFuns.\<close>
  have fe: "funs_exist_in_state ?st env"
    unfolding funs_exist_in_state_def
  proof (intro allI impI)
    fix name info
    assume a: "fmlookup (TE_Functions env) name = Some info \<and> FI_Ghost info = NotGhost"
    hence decl: "fmlookup (TE_Functions env) name = Some info"
      and ng: "FI_Ghost info = NotGhost" by auto
    have "name |\<in>| fmdom funDefs" using fmdomI[OF decl] fdom by simp
    then obtain f where f_lk: "fmlookup funDefs name = Some f"
      by (auto simp add: fmlookup_dom_iff)
    have mem: "(name, f) \<in> set (sorted_list_of_fmap funDefs)"
      using f_lk by (simp add: sorted_list_of_fmap_mem_iff)
    obtain body where
      funs_lk: "fmlookup funs name = Some (make_interp_fun info f body)" and
      body_ok: "(case CF_Body f of
                   Some stmts \<Rightarrow> body = Inl stmts
                 | None \<Rightarrow> (\<exists>externFun. fmlookup externs name = Some externFun
                                       \<and> body = Inr externFun))"
      using build_interp_funs_lookup_some[OF funs_ok mem
              distinct_map_fst_sorted_list_of_fmap decl ng]
      by auto

    \<comment> \<open>Definition-vs-declaration consistency from the module typecheck.\<close>
    obtain info' where
      decl2: "fmlookup (TE_Functions env) name = Some info'" and
      len0: "length (CF_Args f) = length (FI_TmArgs info')" and
      distArgs: "distinct (CF_Args f)" and
      body_wt: "(case CF_Body f of
                   None \<Rightarrow> True
                 | Some stmts \<Rightarrow>
                     core_statement_list_type
                       (module_body_env_for env (CF_Args f) info')
                       (FI_Ghost info') stmts \<noteq> None)"
      using fwt f_lk unfolding module_functions_well_typed_def by blast
    have info'_eq: "info' = info" using decl decl2 by simp
    have len: "length (CF_Args f) = length (FI_TmArgs info)"
      using len0 info'_eq by simp

    \<comment> \<open>The five conjuncts of fun_info_matches_interp_fun.\<close>
    have if_sel:
      "IF_TyArgs (make_interp_fun info f body) = FI_TyArgs info"
      "IF_Args (make_interp_fun info f body) = zip (CF_Args f) (map snd (FI_TmArgs info))"
      "IF_Body (make_interp_fun info f body) = body"
      "IF_Impure (make_interp_fun info f body) = FI_Impure info"
      by (simp_all add: make_interp_fun_def)
    have mapfst: "map fst (zip (CF_Args f) (map snd (FI_TmArgs info))) = CF_Args f"
      by (simp add: len)
    have markers: "list_all2 (\<lambda>(_, vor1) (_, vor2). vor1 = vor2)
                     (FI_TmArgs info) (zip (CF_Args f) (map snd (FI_TmArgs info)))"
      by (auto simp add: list_all2_conv_all_nth len split_def)
    have distZip: "distinct (map fst (zip (CF_Args f) (map snd (FI_TmArgs info))))"
      unfolding mapfst by (rule distArgs)
    have body_match: "case body of
           Inl bodyStmts \<Rightarrow>
             core_statement_list_type
               (body_env_for env
                  (map fst (zip (CF_Args f) (map snd (FI_TmArgs info)))) info)
               NotGhost bodyStmts \<noteq> None
         | Inr externFun \<Rightarrow> extern_fun_contract env info externFun"
      unfolding mapfst
    proof (cases "CF_Body f")
      case (Some stmts)
      with body_ok have body_eq: "body = Inl stmts" by simp
      from body_wt Some info'_eq ng
      have "core_statement_list_type
              (module_body_env_for env (CF_Args f) info) NotGhost stmts \<noteq> None"
        by simp
      thus "case body of
              Inl bodyStmts \<Rightarrow>
                core_statement_list_type
                  (body_env_for env (CF_Args f) info) NotGhost bodyStmts \<noteq> None
            | Inr externFun \<Rightarrow> extern_fun_contract env info externFun"
        unfolding body_eq
        by (simp add: module_body_env_for_eq_body_env_for[OF abs ng])
    next
      case None
      with body_ok obtain externFun where
        ext_lk: "fmlookup externs name = Some externFun" and
        body_eq: "body = Inr externFun"
        by auto
      show "case body of
              Inl bodyStmts \<Rightarrow>
                core_statement_list_type
                  (body_env_for env (CF_Args f) info) NotGhost bodyStmts \<noteq> None
            | Inr externFun \<Rightarrow> extern_fun_contract env info externFun"
        unfolding body_eq
        using externs_ok[OF decl ext_lk] by simp
    qed
    have match: "fun_info_matches_interp_fun env info (make_interp_fun info f body)"
      unfolding fun_info_matches_interp_fun_def if_sel
      using markers distZip body_match by simp

    show "case fmlookup (IS_Functions ?st) name of
            Some interpFun \<Rightarrow> fun_info_matches_interp_fun env info interpFun
          | None \<Rightarrow> False"
      by (simp add: st_sel funs_lk match)
  qed

  \<comment> \<open>Conjunct: no functions beyond the declared non-ghost ones.\<close>
  have nef: "no_extra_funs ?st env"
    unfolding no_extra_funs_def
  proof (intro allI impI)
    fix n
    assume a: "case fmlookup (TE_Functions env) n of
                 None \<Rightarrow> True | Some info \<Rightarrow> FI_Ghost info = Ghost"
    have "fmlookup funs n = None"
    proof (rule build_interp_funs_lookup_none[OF funs_ok])
      fix f assume "(n, f) \<in> set (sorted_list_of_fmap funDefs)"
      hence "fmlookup funDefs n = Some f" by (simp add: sorted_list_of_fmap_mem_iff)
      hence "n |\<in>| fmdom (TE_Functions env)" using fmdomI fdom by fastforce
      then obtain info where info_lk: "fmlookup (TE_Functions env) n = Some info"
        by (auto simp add: fmlookup_dom_iff)
      with a have "FI_Ghost info = Ghost" by simp
      with info_lk
      show "\<exists>info. fmlookup (TE_Functions env) n = Some info \<and> FI_Ghost info = Ghost"
        by auto
    qed
    thus "fmlookup (IS_Functions ?st) n = None" by (simp add: st_sel)
  qed

  have ranEmpty: "fmran' (fmempty :: (string, CoreType) fmap) = {}"
    by (auto simp: fmlookup_ran'_iff)
  have srtEmpty: "subst_range_tyvars fmempty = {}"
    by (simp add: subst_range_tyvars_def ranEmpty)

  show ?thesis
    unfolding state_matches_env_def
  proof (intro conjI)
    show "local_vars_exist_in_state ?st env []"
      unfolding local_vars_exist_in_state_def by (simp add: locals)
    show "global_vars_exist_in_state ?st env" by (rule gv)
    show "no_extra_local_vars ?st env"
      unfolding no_extra_local_vars_def by (simp add: st_sel)
    show "no_extra_global_vars ?st env" by (rule neg)
    show "funs_exist_in_state ?st env" by (rule fe)
    show "no_extra_funs ?st env" by (rule nef)
    show "const_locals_match ?st env"
      unfolding const_locals_match_def
      by (simp add: st_sel constlocals ghostlocals)
    show "store_well_typed ?st env []"
      unfolding store_well_typed_def by (simp add: st_sel)
    show "ty_args_well_formed ?st env"
      unfolding ty_args_well_formed_def
      by (simp add: st_sel rtv ranEmpty srtEmpty)
    show "default_ctors_match ?st env"
    proof -
      have "IS_DefaultCtors ?st = default_ctors_map env" by (rule st_sel(7))
      moreover have "TE_DataCtorsByType env = TE_DataCtorsByType env" by (rule refl)
      moreover have "TE_DataCtors env = TE_DataCtors env" by (rule refl)
      ultimately show ?thesis by (rule default_ctors_map_match)
    qed
    show "TE_AbstractTypes env = {||}" by (rule abs)
  qed
qed


(* ========================================================================== *)
(* Main theorem                                                               *)
(* ========================================================================== *)

(* Building an InterpState from a closed, well-typed CoreModule (with
   contract-satisfying extern functions) yields a state that matches the
   normalized module's type environment, with an empty store typing. *)
theorem make_interp_state_matches_env:
  assumes wt: "core_module_well_typed m"
      and closed: "core_module_closed m"
      and externs_ok: "\<And>name info externFun.
            \<lbrakk> fmlookup (TE_Functions (CM_TyEnv (normalize_module m))) name = Some info;
              fmlookup externs name = Some externFun \<rbrakk> \<Longrightarrow>
            extern_fun_contract (CM_TyEnv (normalize_module m)) info externFun"
      and ok: "make_interp_state world externs m = Inr state"
  shows "state_matches_env state (CM_TyEnv (normalize_module m)) []"
proof -
  define m' where "m' = normalize_module m"
  define env where "env = CM_TyEnv m'"
  define funPairs where "funPairs = sorted_list_of_fmap (CM_Functions m')"

  \<comment> \<open>Facts about the normalized module.\<close>
  have nwt: "normalized_module_well_typed m'"
    using wt unfolding core_module_well_typed_def m'_def by blast
  have wf: "tyenv_well_formed env"
    and scope: "tyenv_module_scope env"
    and gwt: "module_globals_well_typed env (CM_GlobalVars m')"
    and fwt: "module_functions_well_typed env (CM_Functions m')"
    using nwt unfolding normalized_module_well_typed_def env_def by blast+
  have closed': "core_module_closed m'"
    using closed unfolding m'_def by simp
  have gdom: "fmdom (TE_GlobalVars env) = fmdom (CM_GlobalVars m')"
    and fdom: "fmdom (TE_Functions env) = fmdom (CM_Functions m')"
    and tv: "TE_TypeVars env = {||}"
    using closed' unfolding core_module_closed_def env_def by blast+
  have rtv: "TE_RuntimeTypeVars env = {||}"
  proof -
    have "TE_RuntimeTypeVars env |\<subseteq>| TE_TypeVars env"
      using wf
      unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by blast
    thus ?thesis using tv by simp
  qed
  have externs_ok': "\<And>name info externFun.
        \<lbrakk> fmlookup (TE_Functions env) name = Some info;
          fmlookup externs name = Some externFun \<rbrakk> \<Longrightarrow>
        extern_fun_contract env info externFun"
    using externs_ok unfolding env_def m'_def by blast

  \<comment> \<open>Decompose the construction.\<close>
  from ok obtain funs where
    funs_ok: "build_interp_funs externs env funPairs = Inr funs" and
    state_eq: "state = base_interp_state env world
                         \<lparr> IS_Globals := CM_GlobalVars m', IS_Functions := funs \<rparr>"
    unfolding make_interp_state_def Let_def
              m'_def[symmetric] env_def[symmetric] funPairs_def[symmetric]
    by (auto split: sum.splits)

  show ?thesis
    unfolding m'_def[symmetric] env_def[symmetric] state_eq
    by (rule assembled_state_matches[OF wf scope tv rtv gdom fdom gwt fwt
          funs_ok[unfolded funPairs_def] externs_ok'])
qed

end

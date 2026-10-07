theory EraseGhostModuleTyping
  imports EraseGhostStmtTyping "../core/LinkPreservesWellTyped"
begin

(* Ghost-erasing a well-typed module gives a well-typed module.

   The parts:
    - the erased environment is well-formed;
    - the globals have their types in the erased environment;
    - the erased function bodies are typed in the erased environment. *)


(* ========================================================================== *)
(* Runtime types, with the type variables changed *)
(* ========================================================================== *)

(* The lemma tyenv_erased_runtime_type, from weaker hypotheses. The clauses of
   tyenv_well_formed check types in environments whose type variables have
   been replaced (by the abstract types and some type parameters), and those
   environments are not related by tyenv_erased. *)
lemma runtime_type_transfer_erased:
  assumes tv: "\<And>n. n |\<in>| TE_RuntimeTypeVars env1
                 \<Longrightarrow> n |\<in>| TE_TypeVars env2 \<and> n |\<in>| TE_RuntimeTypeVars env2"
    and dt: "\<And>dtName n. fmlookup (TE_Datatypes env1) dtName = Some n
                 \<Longrightarrow> dtName |\<notin>| TE_GhostDatatypes env1
                 \<Longrightarrow> fmlookup (TE_Datatypes env2) dtName = Some n"
    and gd: "TE_GhostDatatypes env2 = {||}"
  shows "is_well_kinded env1 ty \<Longrightarrow> is_runtime_type env1 ty
           \<Longrightarrow> is_well_kinded env2 ty \<and> is_runtime_type env2 ty"
proof (induction ty)
  case (CoreTy_Datatype nm args)
  from CoreTy_Datatype.prems(1) obtain n where
      lk: "fmlookup (TE_Datatypes env1) nm = Some n" and
      len: "length args = n" and
      wks: "list_all (is_well_kinded env1) args"
    by (auto split: option.splits)
  from CoreTy_Datatype.prems(2) have
      ng: "nm |\<notin>| TE_GhostDatatypes env1" and
      rts: "list_all (is_runtime_type env1) args"
    by simp_all
  have lk2: "fmlookup (TE_Datatypes env2) nm = Some n"
    by (rule dt[OF lk ng])
  have each: "is_well_kinded env2 a \<and> is_runtime_type env2 a" if a_in: "a \<in> set args" for a
  proof -
    have wk: "is_well_kinded env1 a" using wks a_in by (simp add: list_all_iff)
    have rt: "is_runtime_type env1 a" using rts a_in by (simp add: list_all_iff)
    show ?thesis by (rule CoreTy_Datatype.IH[OF a_in wk rt])
  qed
  show ?case
    using lk2 len each by (simp add: list_all_iff gd)
next
  case (CoreTy_Record flds)
  have each: "is_well_kinded env2 fty \<and> is_runtime_type env2 fty"
    if f_in: "(nm, fty) \<in> set flds" for nm fty
  proof -
    have sn: "fty \<in> Basic_BNFs.snds (nm, fty)" by simp
    have wk: "is_well_kinded env1 fty"
      using CoreTy_Record.prems(1) f_in by (force simp: list_all_iff)
    have rt: "is_runtime_type env1 fty"
      using CoreTy_Record.prems(2) f_in by (force simp: list_all_iff)
    show ?thesis by (rule CoreTy_Record.IH[OF f_in sn wk rt])
  qed
  show ?case
    using CoreTy_Record.prems(1) each by (auto simp: list_all_iff)
next
  case (CoreTy_Array elemTy dims)
  then show ?case by simp
next
  case (CoreTy_Var n)
  then show ?case using tv[of n] by simp
qed simp_all

lemma fset_scoped_tyvars_eq1:
  "(A |\<union>| T) |\<inter>| ((A |\<inter>| R) |\<union>| T) = (A |\<inter>| R) |\<union>| T"
  by (rule fset_eqI) auto

lemma fset_scoped_tyvars_eq2:
  "((A |\<inter>| R) |\<inter>| R) |\<union>| T = (A |\<inter>| R) |\<union>| T"
  by (rule fset_eqI) auto

(* A type checked with the abstract types and the type variables T in scope.
   This is the form in which tyenv_well_formed checks the types of functions
   and of constructor payloads. *)
lemma erase_ghost_tyenv_scoped_type:
  assumes wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| T \<rparr>) ty"
    and rt: "is_runtime_type
               (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| T,
                      TE_RuntimeTypeVars :=
                        (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env) |\<union>| T \<rparr>) ty"
  shows "is_well_kinded
           ((erase_ghost_tyenv env)
              \<lparr> TE_TypeVars := TE_AbstractTypes (erase_ghost_tyenv env) |\<union>| T \<rparr>) ty"
    and "is_runtime_type
           ((erase_ghost_tyenv env)
              \<lparr> TE_TypeVars := TE_AbstractTypes (erase_ghost_tyenv env) |\<union>| T,
                TE_RuntimeTypeVars :=
                  (TE_AbstractTypes (erase_ghost_tyenv env)
                     |\<inter>| TE_RuntimeTypeVars (erase_ghost_tyenv env)) |\<union>| T \<rparr>) ty"
proof -
  let ?env1 = "env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| T,
                      TE_RuntimeTypeVars :=
                        (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env) |\<union>| T \<rparr>"
  let ?E = "erase_ghost_tyenv env"
  let ?env2 = "?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| T,
                     TE_RuntimeTypeVars :=
                       (TE_AbstractTypes ?E |\<inter>| TE_RuntimeTypeVars ?E) |\<union>| T \<rparr>"
  have "is_well_kinded ?env1 ty
          = is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| T \<rparr>) ty"
    by (rule is_well_kinded_cong_env) simp_all
  hence wk1: "is_well_kinded ?env1 ty" using wk by simp
  have both: "is_well_kinded ?env2 ty \<and> is_runtime_type ?env2 ty"
    by (rule runtime_type_transfer_erased[OF _ _ _ wk1 rt]) auto
  have "is_well_kinded (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| T \<rparr>) ty
          = is_well_kinded ?env2 ty"
    by (rule is_well_kinded_cong_env) simp_all
  thus "is_well_kinded (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| T \<rparr>) ty"
    using both by simp
  show "is_runtime_type ?env2 ty" using both by simp
qed

(* The same with no extra type variables: the form used for global variables. *)
lemma erase_ghost_tyenv_global_type:
  assumes wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
    and rt: "is_runtime_type
               (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                      TE_RuntimeTypeVars :=
                        TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
  shows "is_well_kinded
           ((erase_ghost_tyenv env)
              \<lparr> TE_TypeVars := TE_AbstractTypes (erase_ghost_tyenv env) \<rparr>) ty"
    and "is_runtime_type
           ((erase_ghost_tyenv env)
              \<lparr> TE_TypeVars := TE_AbstractTypes (erase_ghost_tyenv env),
                TE_RuntimeTypeVars :=
                  TE_AbstractTypes (erase_ghost_tyenv env)
                    |\<inter>| TE_RuntimeTypeVars (erase_ghost_tyenv env) \<rparr>) ty"
proof -
  have wk0: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| {||} \<rparr>) ty"
    using wk by simp
  have rt0: "is_runtime_type
               (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| {||},
                      TE_RuntimeTypeVars :=
                        (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env) |\<union>| {||} \<rparr>) ty"
    using rt by simp
  from erase_ghost_tyenv_scoped_type(1)[OF wk0 rt0]
  show "is_well_kinded
          ((erase_ghost_tyenv env)
             \<lparr> TE_TypeVars := TE_AbstractTypes (erase_ghost_tyenv env) \<rparr>) ty"
    by simp
  from erase_ghost_tyenv_scoped_type(2)[OF wk0 rt0]
  show "is_runtime_type
          ((erase_ghost_tyenv env)
             \<lparr> TE_TypeVars := TE_AbstractTypes (erase_ghost_tyenv env),
               TE_RuntimeTypeVars :=
                 TE_AbstractTypes (erase_ghost_tyenv env)
                   |\<inter>| TE_RuntimeTypeVars (erase_ghost_tyenv env) \<rparr>) ty"
    by simp
qed


(* ========================================================================== *)
(* The erased environment is well-formed *)
(* ========================================================================== *)

(* For an environment at module scope. (With local variables it would not
   hold: a ghost local may have a type that does not exist after erasure.) *)
theorem erase_ghost_tyenv_well_formed:
  assumes wf: "tyenv_well_formed env" and scope: "tyenv_module_scope env"
  shows "tyenv_well_formed (erase_ghost_tyenv env)"
proof -
  let ?E = "erase_ghost_tyenv env"

  have a1: "tyenv_vars_well_kinded env"
    and a2: "tyenv_vars_runtime env"
    and a3: "tyenv_ghost_vars_subset env"
    and a6: "tyenv_return_type_complete env"
    and a7: "tyenv_ctors_consistent env"
    and a8: "tyenv_payloads_well_kinded env"
    and a9: "tyenv_ctor_tyvars_distinct env"
    and a10: "tyenv_ctors_by_type_consistent env"
    and a11: "tyenv_fun_types_well_kinded env"
    and a12: "tyenv_fun_tyvars_distinct env"
    and a13: "tyenv_fun_ghost_constraint env"
    and a14: "tyenv_fun_return_types_complete env"
    and a15: "tyenv_nonghost_payloads_runtime env"
    and a17: "tyenv_runtime_tyvars_subset env"
    and a18: "tyenv_abstract_types_subset env"
    and a19: "tyenv_datatypes_nonempty env"
    using wf unfolding tyenv_well_formed_def by simp_all

  have locals: "TE_LocalVars env = fmempty"
    and ret: "TE_ReturnType env = CoreTy_Record []"
    using scope unfolding tyenv_module_scope_def by simp_all

  \<comment> \<open>What is in the erased tables is in the original ones, and is not ghost.\<close>
  have ctorD: "fmlookup (TE_DataCtors env) c = Some (dt, tvs, p)
               \<and> dt |\<notin>| TE_GhostDatatypes env"
    if "fmlookup (TE_DataCtors ?E) c = Some (dt, tvs, p)" for c dt tvs p
    using that unfolding erase_ghost_tyenv_ctor_lookup .
  have funD: "\<exists>info0. fmlookup (TE_Functions env) f = Some info0
                     \<and> FI_Ghost info0 = NotGhost
                     \<and> info = erase_ghost_funinfo info0"
    if "fmlookup (TE_Functions ?E) f = Some info" for f info
    using that unfolding erase_ghost_tyenv_fun_lookup .

  have c1: "tyenv_vars_well_kinded ?E"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix name ty assume "fmlookup (TE_LocalVars ?E) name = Some ty"
    thus "is_well_kinded ?E ty" using locals by simp
  next
    fix name ty assume "fmlookup (TE_GlobalVars ?E) name = Some ty"
    hence lk: "fmlookup (TE_GlobalVars env) name = Some ty" by simp
    have wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
      using a1 lk unfolding tyenv_vars_well_kinded_def by blast
    have rt: "is_runtime_type
                (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                       TE_RuntimeTypeVars :=
                         TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
      using a2 lk unfolding tyenv_vars_runtime_def by blast
    show "is_well_kinded (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E \<rparr>) ty"
      by (rule erase_ghost_tyenv_global_type(1)[OF wk rt])
  qed

  have c2: "tyenv_vars_runtime ?E"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix name ty
    assume "fmlookup (TE_LocalVars ?E) name = Some ty \<and> name |\<notin>| TE_GhostLocals ?E"
    thus "is_runtime_type ?E ty" using locals by simp
  next
    fix name ty assume "fmlookup (TE_GlobalVars ?E) name = Some ty"
    hence lk: "fmlookup (TE_GlobalVars env) name = Some ty" by simp
    have wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
      using a1 lk unfolding tyenv_vars_well_kinded_def by blast
    have rt: "is_runtime_type
                (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                       TE_RuntimeTypeVars :=
                         TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
      using a2 lk unfolding tyenv_vars_runtime_def by blast
    show "is_runtime_type
            (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E,
                  TE_RuntimeTypeVars :=
                    TE_AbstractTypes ?E |\<inter>| TE_RuntimeTypeVars ?E \<rparr>) ty"
      by (rule erase_ghost_tyenv_global_type(2)[OF wk rt])
  qed

  have c3: "tyenv_ghost_vars_subset ?E"
    using a3 unfolding tyenv_ghost_vars_subset_def by simp

  have c4: "tyenv_return_type_well_kinded ?E"
    unfolding tyenv_return_type_well_kinded_def by (simp add: ret)

  have c5: "tyenv_return_type_runtime ?E"
    unfolding tyenv_return_type_runtime_def by (simp add: ret)

  have c6: "tyenv_return_type_complete ?E"
    using a6 unfolding tyenv_return_type_complete_def by simp

  have c7: "tyenv_ctors_consistent ?E"
    unfolding tyenv_ctors_consistent_def
  proof (intro allI impI)
    fix c dt tvs p
    assume lkE: "fmlookup (TE_DataCtors ?E) c = Some (dt, tvs, p)"
    note d = ctorD[OF lkE]
    have "fmlookup (TE_Datatypes env) dt = Some (length tvs)"
      using a7 d unfolding tyenv_ctors_consistent_def by blast
    thus "fmlookup (TE_Datatypes ?E) dt = Some (length tvs)" using d by simp
  qed

  have c8: "tyenv_payloads_well_kinded ?E"
    unfolding tyenv_payloads_well_kinded_def
  proof (intro allI impI)
    fix c dt tvs p
    assume lkE: "fmlookup (TE_DataCtors ?E) c = Some (dt, tvs, p)"
    note d = ctorD[OF lkE]
    have wk: "is_well_kinded
                (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tvs \<rparr>) p"
      using a8 d unfolding tyenv_payloads_well_kinded_def by blast
    have rt: "is_runtime_type
                (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tvs,
                       TE_RuntimeTypeVars :=
                         (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                           |\<union>| fset_of_list tvs \<rparr>) p"
      using a15 d unfolding tyenv_nonghost_payloads_runtime_def by blast
    show "is_well_kinded
            (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| fset_of_list tvs \<rparr>) p"
      by (rule erase_ghost_tyenv_scoped_type(1)[OF wk rt])
  qed

  have c9: "tyenv_ctor_tyvars_distinct ?E"
    unfolding tyenv_ctor_tyvars_distinct_def
  proof (intro allI impI)
    fix c dt tvs p
    assume lkE: "fmlookup (TE_DataCtors ?E) c = Some (dt, tvs, p)"
    note d = ctorD[OF lkE]
    show "distinct tvs"
      using a9 d unfolding tyenv_ctor_tyvars_distinct_def by blast
  qed

  have c10: "tyenv_ctors_by_type_consistent ?E"
    unfolding tyenv_ctors_by_type_consistent_def
  proof (intro allI impI)
    fix dt ctors c
    assume lkE: "fmlookup (TE_DataCtorsByType ?E) dt = Some ctors"
    hence lk: "fmlookup (TE_DataCtorsByType env) dt = Some ctors"
      and ng: "dt |\<notin>| TE_GhostDatatypes env"
      unfolding erase_ghost_tyenv_ctors_by_type_lookup by simp_all
    have orig: "(c \<in> set ctors)
                  = (\<exists>tvs p. fmlookup (TE_DataCtors env) c = Some (dt, tvs, p))"
      using a10 lk unfolding tyenv_ctors_by_type_consistent_def by blast
    show "(c \<in> set ctors)
            = (\<exists>tvs p. fmlookup (TE_DataCtors ?E) c = Some (dt, tvs, p))"
      unfolding erase_ghost_tyenv_ctor_lookup using orig ng by blast
  qed

  have c11: "tyenv_fun_types_well_kinded ?E"
    unfolding tyenv_fun_types_well_kinded_def
  proof (intro allI impI)
    fix f info
    assume lkE: "fmlookup (TE_Functions ?E) f = Some info"
    from funD[OF lkE] obtain info0 where
        lk0: "fmlookup (TE_Functions env) f = Some info0" and
        ng0: "FI_Ghost info0 = NotGhost" and
        info_eq: "info = erase_ghost_funinfo info0"
      by blast
    let ?T = "fset_of_list (FI_TyArgs info0)"
    let ?wenv = "env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| ?T \<rparr>"
    let ?renv = "env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| ?T,
                        TE_RuntimeTypeVars :=
                          (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env) |\<union>| ?T \<rparr>"
    have wks: "(\<forall>ty \<in> fst ` set (FI_TmArgs info0). is_well_kinded ?wenv ty)
               \<and> is_well_kinded ?wenv (FI_ReturnType info0)"
      using a11 lk0 unfolding tyenv_fun_types_well_kinded_def by blast
    have rts: "(\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info0)
                           \<longrightarrow> is_runtime_type ?renv ty)
               \<and> is_runtime_type ?renv (FI_ReturnType info0)"
      using a13 lk0 ng0 unfolding tyenv_fun_ghost_constraint_def Let_def by blast
    \<comment> \<open>A parameter of the erased signature is a non-ghost parameter of the
        original one.\<close>
    have kept: "\<exists>vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info0)"
      if "ty \<in> fst ` set (FI_TmArgs info)" for ty
      using that unfolding info_eq by force
    note S = erase_ghost_tyenv_scoped_type(1)[where env = env and T = ?T]
    show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
              is_well_kinded
                (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                ty)
          \<and> is_well_kinded
              (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
              (FI_ReturnType info)"
    proof (intro conjI ballI)
      fix ty assume "ty \<in> fst ` set (FI_TmArgs info)"
      from kept[OF this] obtain vor where
          m: "(ty, vor, NotGhost) \<in> set (FI_TmArgs info0)"
        by blast
      have wk: "is_well_kinded ?wenv ty" using wks m by force
      have rt: "is_runtime_type ?renv ty" using rts m by blast
      show "is_well_kinded
              (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
              ty"
        unfolding info_eq erase_ghost_funinfo_simps by (rule S[OF wk rt])
    next
      show "is_well_kinded
              (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
              (FI_ReturnType info)"
        unfolding info_eq erase_ghost_funinfo_simps using S wks rts by blast
    qed
  qed

  have c12: "tyenv_fun_tyvars_distinct ?E"
    unfolding tyenv_fun_tyvars_distinct_def
  proof (intro allI impI)
    fix f info
    assume lkE: "fmlookup (TE_Functions ?E) f = Some info"
    from funD[OF lkE] obtain info0 where
        lk0: "fmlookup (TE_Functions env) f = Some info0" and
        info_eq: "info = erase_ghost_funinfo info0"
      by blast
    have "distinct (FI_TyArgs info0)"
      using a12 lk0 unfolding tyenv_fun_tyvars_distinct_def by blast
    thus "distinct (FI_TyArgs info)" by (simp add: info_eq)
  qed

  have c13: "tyenv_fun_ghost_constraint ?E"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI)
    fix f info
    assume A: "fmlookup (TE_Functions ?E) f = Some info \<and> FI_Ghost info = NotGhost"
    hence lkE: "fmlookup (TE_Functions ?E) f = Some info" by simp
    from funD[OF lkE] obtain info0 where
        lk0: "fmlookup (TE_Functions env) f = Some info0" and
        ng0: "FI_Ghost info0 = NotGhost" and
        info_eq: "info = erase_ghost_funinfo info0"
      by blast
    let ?T = "fset_of_list (FI_TyArgs info0)"
    let ?wenv = "env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| ?T \<rparr>"
    let ?renv = "env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| ?T,
                        TE_RuntimeTypeVars :=
                          (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env) |\<union>| ?T \<rparr>"
    let ?rE = "\<lambda>tvs. ?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| fset_of_list tvs,
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes ?E |\<inter>| TE_RuntimeTypeVars ?E)
                               |\<union>| fset_of_list tvs \<rparr>"
    have wks: "(\<forall>ty \<in> fst ` set (FI_TmArgs info0). is_well_kinded ?wenv ty)
               \<and> is_well_kinded ?wenv (FI_ReturnType info0)"
      using a11 lk0 unfolding tyenv_fun_types_well_kinded_def by blast
    have rts: "(\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info0)
                           \<longrightarrow> is_runtime_type ?renv ty)
               \<and> is_runtime_type ?renv (FI_ReturnType info0)"
      using a13 lk0 ng0 unfolding tyenv_fun_ghost_constraint_def Let_def by blast
    note S = erase_ghost_tyenv_scoped_type(2)[where env = env and T = ?T]
    show "(\<forall>ty vor. (ty, vor, NotGhost) \<in> set (FI_TmArgs info)
                      \<longrightarrow> is_runtime_type (?rE (FI_TyArgs info)) ty)
          \<and> is_runtime_type (?rE (FI_TyArgs info)) (FI_ReturnType info)"
    proof (intro conjI allI impI)
      fix ty vor assume "(ty, vor, NotGhost) \<in> set (FI_TmArgs info)"
      hence m: "(ty, vor, NotGhost) \<in> set (FI_TmArgs info0)"
        by (simp add: info_eq)
      have wk: "is_well_kinded ?wenv ty" using wks m by force
      have rt: "is_runtime_type ?renv ty" using rts m by blast
      show "is_runtime_type (?rE (FI_TyArgs info)) ty"
        unfolding info_eq erase_ghost_funinfo_simps by (rule S[OF wk rt])
    next
      show "is_runtime_type (?rE (FI_TyArgs info)) (FI_ReturnType info)"
        unfolding info_eq erase_ghost_funinfo_simps using S wks rts by blast
    qed
  qed

  have c14: "tyenv_fun_return_types_complete ?E"
    unfolding tyenv_fun_return_types_complete_def
  proof (intro allI impI)
    fix f info
    assume A: "fmlookup (TE_Functions ?E) f = Some info \<and> FI_Ghost info = NotGhost"
    hence lkE: "fmlookup (TE_Functions ?E) f = Some info" by simp
    from funD[OF lkE] obtain info0 where
        lk0: "fmlookup (TE_Functions env) f = Some info0" and
        ng0: "FI_Ghost info0 = NotGhost" and
        info_eq: "info = erase_ghost_funinfo info0"
      by blast
    have "is_complete_type (FI_ReturnType info0)"
      using a14 lk0 ng0 unfolding tyenv_fun_return_types_complete_def by blast
    thus "is_complete_type (FI_ReturnType info)" by (simp add: info_eq)
  qed

  have c15: "tyenv_nonghost_payloads_runtime ?E"
    unfolding tyenv_nonghost_payloads_runtime_def
  proof (intro allI impI)
    fix c dt tvs p
    assume lkE: "fmlookup (TE_DataCtors ?E) c = Some (dt, tvs, p)"
    note d = ctorD[OF lkE]
    have wk: "is_well_kinded
                (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tvs \<rparr>) p"
      using a8 d unfolding tyenv_payloads_well_kinded_def by blast
    have rt: "is_runtime_type
                (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tvs,
                       TE_RuntimeTypeVars :=
                         (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                           |\<union>| fset_of_list tvs \<rparr>) p"
      using a15 d unfolding tyenv_nonghost_payloads_runtime_def by blast
    show "is_runtime_type
            (?E \<lparr> TE_TypeVars := TE_AbstractTypes ?E |\<union>| fset_of_list tvs,
                  TE_RuntimeTypeVars :=
                    (TE_AbstractTypes ?E |\<inter>| TE_RuntimeTypeVars ?E)
                      |\<union>| fset_of_list tvs \<rparr>) p"
      by (rule erase_ghost_tyenv_scoped_type(2)[OF wk rt])
  qed

  have c16: "tyenv_ghost_datatypes_subset ?E"
    unfolding tyenv_ghost_datatypes_subset_def by simp

  have c17: "tyenv_runtime_tyvars_subset ?E"
    using a17 unfolding tyenv_runtime_tyvars_subset_def by auto

  have c18: "tyenv_abstract_types_subset ?E"
    using a18 unfolding tyenv_abstract_types_subset_def by auto

  have c19: "tyenv_datatypes_nonempty ?E"
    using a19 unfolding tyenv_datatypes_nonempty_def
    by (auto split: if_splits)

  show ?thesis
    unfolding tyenv_well_formed_def
    using c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19
    by blast
qed


(* ========================================================================== *)
(* Values *)
(* ========================================================================== *)

(* A value of a runtime type of env has that type in envE: it is built from
   constructors of datatypes that are not ghost. *)
lemma value_has_type_erased:
  assumes rel: "tyenv_erased env envE" and wf: "tyenv_well_formed env"
  shows "value_has_type env val ty \<Longrightarrow> is_runtime_type env ty
           \<Longrightarrow> value_has_type envE val ty"
proof (induction val arbitrary: ty)
  case (CV_Bool b)
  then show ?case by simp
next
  case (CV_FiniteInt sign bits i)
  then show ?case by simp
next
  case (CV_Record fieldValues)
  let ?P = "\<lambda>e. (\<lambda>(name1, fldVal) (name2, fldTy).
               name1 = name2 \<and> value_has_type e fldVal fldTy)"
  from CV_Record.prems(1) obtain fieldTypes where
      ty_eq: "ty = CoreTy_Record fieldTypes" and
      dist: "distinct (map fst fieldTypes)" and
      all2: "list_all2 (?P env) fieldValues fieldTypes"
    by (cases ty) auto
  from CV_Record.prems(2) ty_eq have
      rts: "list_all (is_runtime_type env) (map snd fieldTypes)"
    by simp
  have len: "length fieldValues = length fieldTypes"
    using all2 by (rule list_all2_lengthD)
  have all2E: "list_all2 (?P envE) fieldValues fieldTypes"
  proof (rule list_all2_all_nthI)
    show "length fieldValues = length fieldTypes" by (rule len)
  next
    fix i assume i: "i < length fieldValues"
    obtain n1 v where fv: "fieldValues ! i = (n1, v)" by (cases "fieldValues ! i")
    obtain n2 t where ft: "fieldTypes ! i = (n2, t)" by (cases "fieldTypes ! i")
    from all2 i have "?P env (fieldValues ! i) (fieldTypes ! i)" by (rule list_all2_nthD)
    hence nm: "n1 = n2" and vt: "value_has_type env v t"
      using fv ft by simp_all
    have in_v: "(n1, v) \<in> set fieldValues" using i fv by (metis nth_mem)
    have "fieldTypes ! i \<in> set fieldTypes" using i len by simp
    hence rt: "is_runtime_type env t" using rts ft by (force simp: list_all_iff)
    have sn: "v \<in> Basic_BNFs.snds (n1, v)" by simp
    have "value_has_type envE v t"
      by (rule CV_Record.IH[OF in_v sn vt rt])
    thus "?P envE (fieldValues ! i) (fieldTypes ! i)" using fv ft nm by simp
  qed
  show ?case using ty_eq dist all2E by simp
next
  case (CV_Variant ctor payload)
  from CV_Variant.prems(1) obtain dtName argTypes tyvars payloadTy where
      ty_eq: "ty = CoreTy_Datatype dtName argTypes" and
      lk: "fmlookup (TE_DataCtors env) ctor = Some (dtName, tyvars, payloadTy)" and
      len: "length tyvars = length argTypes" and
      args_wk: "list_all (is_well_kinded env) argTypes" and
      args_ground: "list_all (\<lambda>a. type_tyvars a = {}) argTypes" and
      pv: "value_has_type env payload
             (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
    by (cases ty) (auto split: option.splits prod.splits)
  from CV_Variant.prems(2) ty_eq have
      ng: "dtName |\<notin>| TE_GhostDatatypes env" and
      rts: "list_all (is_runtime_type env) argTypes"
    by simp_all
  have "tyenv_nonghost_payloads_runtime env"
    using wf unfolding tyenv_well_formed_def by blast
  hence payload_rt:
    "is_runtime_type
       (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
              TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                     |\<union>| fset_of_list tyvars \<rparr>) payloadTy"
    using lk ng unfolding tyenv_nonghost_payloads_runtime_def by blast
  have rt': "is_runtime_type env
               (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
    by (rule apply_subst_specializes_runtime[OF payload_rt rts len])
  have pvE: "value_has_type envE payload
               (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)"
    by (rule CV_Variant.IH[OF pv rt'])
  have lkE: "fmlookup (TE_DataCtors envE) ctor = Some (dtName, tyvars, payloadTy)"
    by (rule tyenv_erased_ctor_lookup[OF rel lk ng])
  note tysE = tyenv_erased_runtime_type_list[OF rel args_wk rts]
  show ?case using ty_eq lkE len tysE args_ground pvE by simp
next
  case (CV_Array sizes valuesMap)
  from CV_Array.prems(1) obtain elemTy dims where
      ty_eq: "ty = CoreTy_Array elemTy dims" and
      elem_wk: "is_well_kinded env elemTy" and
      elem_ground: "type_tyvars elemTy = {}" and
      elems: "\<forall>idx val. fmlookup valuesMap idx = Some val
                          \<longrightarrow> value_has_type env val elemTy" and
      dims_wk: "array_dims_well_kinded dims" and
      matches: "fmap_matches_sizes sizes valuesMap" and
      sizes_ok: "sizes_match_dims sizes dims"
    by (cases ty) auto
  from CV_Array.prems(2) ty_eq have rt: "is_runtime_type env elemTy" by simp
  note tt = tyenv_erased_runtime_type[OF rel elem_wk rt]
  have elemsE: "\<forall>idx val. fmlookup valuesMap idx = Some val
                            \<longrightarrow> value_has_type envE val elemTy"
  proof (intro allI impI)
    fix idx val assume lk: "fmlookup valuesMap idx = Some val"
    have vt: "value_has_type env val elemTy" using elems lk by blast
    have "val \<in> fmran' valuesMap" using lk by (rule fmran'I)
    thus "value_has_type envE val elemTy"
      by (rule CV_Array.IH[OF _ vt rt])
  qed
  show ?case using ty_eq tt elem_ground elemsE dims_wk matches sizes_ok by simp
next
  case (CV_Int i)
  then show ?case by simp
next
  case (CV_Real r)
  then show ?case by simp
qed


(* ========================================================================== *)
(* Function body environments *)
(* ========================================================================== *)

(* The erased parameter list has no ghost parameter. *)
lemma erased_params_no_ghost:
  "filter (\<lambda>(_, _, gh). gh = Ghost)
          (zip xs (map snd (filter (\<lambda>(_, _, gh). gh = NotGhost) params))) = []"
  by (auto simp: filter_empty_conv dest!: set_zip_rightD)

(* A name that is not the name of a ghost parameter: it is bound to the same
   type (or to nothing) by the parameters and by the parameters that are not
   ghost. *)
lemma body_env_locals_erased:
  assumes "length names = length params"
    and "name \<notin> fst ` set (filter (\<lambda>(_, _, gh). gh = Ghost) (zip names (map snd params)))"
  shows "map_of (zip (drop_ghost (map (\<lambda>(_, _, gh). gh) params) names)
                     (map fst (filter (\<lambda>(_, _, gh). gh = NotGhost) params))) name
           = map_of (zip names (map fst params)) name"
  using assms
proof (induction names params rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons n names p params)
  obtain ty vor gh where p: "p = (ty, vor, gh)" by (cases p)
  have rest: "name \<notin> fst ` set (filter (\<lambda>(_, _, gh). gh = Ghost)
                                        (zip names (map snd params)))"
    by (cases gh) (use Cons.prems in \<open>auto simp: p\<close>)
  note IH = Cons.IH[OF rest]
  show ?case
  proof (cases gh)
    case NotGhost
    show ?thesis using IH by (simp add: p NotGhost)
  next
    case Ghost
    have "name \<noteq> n" using Cons.prems by (auto simp: p Ghost)
    then show ?thesis using IH by (simp add: p Ghost)
  qed
qed

(* The same, for being a Var parameter (a const local of the body). *)
lemma body_env_consts_erased:
  assumes "length names = length params"
    and "name \<notin> fst ` set (filter (\<lambda>(_, _, gh). gh = Ghost) (zip names (map snd params)))"
  shows "name \<in> fst ` set (filter (\<lambda>(_, vor, _). vor = Var)
                             (zip (drop_ghost (map (\<lambda>(_, _, gh). gh) params) names)
                                  (map snd (filter (\<lambda>(_, _, gh). gh = NotGhost) params))))
         \<longleftrightarrow> name \<in> fst ` set (filter (\<lambda>(_, vor, _). vor = Var)
                                  (zip names (map snd params)))"
  using assms
proof (induction names params rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons n names p params)
  obtain ty vor gh where p: "p = (ty, vor, gh)" by (cases p)
  have rest: "name \<notin> fst ` set (filter (\<lambda>(_, _, gh). gh = Ghost)
                                        (zip names (map snd params)))"
    by (cases gh) (use Cons.prems in \<open>auto simp: p\<close>)
  note IH = Cons.IH[OF rest]
  show ?case
  proof (cases gh)
    case NotGhost
    show ?thesis by (cases vor) (use IH in \<open>simp_all add: p NotGhost\<close>)
  next
    case Ghost
    have ne: "name \<noteq> n" using Cons.prems by (auto simp: p Ghost)
    show ?thesis by (cases vor) (use IH ne in \<open>simp_all add: p Ghost\<close>)
  qed
qed

(* For a function that is not ghost, the body environment of the erased
   function is related to the body environment of the original one. The erased
   function has lost its ghost parameters; in the original body environment
   they are ghost locals, about which the relation says nothing. *)
lemma tyenv_erased_module_body_env:
  assumes ng: "FI_Ghost info = NotGhost"
    and len: "length names = length (FI_TmArgs info)"
  shows "tyenv_erased (module_body_env_for env names info)
                      (module_body_env_for (erase_ghost_tyenv env)
                         (drop_ghost (param_ghost_flags info) names)
                         (erase_ghost_funinfo info))"
    (is "tyenv_erased ?B ?BE")
proof -
  have flds: "TE_Functions ?B = TE_Functions env"
             "TE_Datatypes ?B = TE_Datatypes env"
             "TE_DataCtors ?B = TE_DataCtors env"
             "TE_DataCtorsByType ?B = TE_DataCtorsByType env"
             "TE_GhostDatatypes ?B = TE_GhostDatatypes env"
    by (simp_all add: module_body_env_for_def)
  have f: "tyenv_nonghost_fun ?B = tyenv_nonghost_fun env"
    by (rule ext) (unfold tyenv_nonghost_fun_def flds, rule refl)
  have c: "tyenv_nonghost_ctor ?B = tyenv_nonghost_ctor env"
    by (rule ext) (unfold tyenv_nonghost_ctor_def flds, rule refl)
  have g: "TE_GlobalVars ?BE = TE_GlobalVars ?B"
    by (simp add: module_body_env_for_def)
  have tvE: "TE_TypeVars ?BE = TE_TypeVars ?B |\<inter>| TE_RuntimeTypeVars ?B"
    using ng by (simp add: module_body_env_for_def fset_scoped_tyvars_eq1)
  have rtvE: "TE_RuntimeTypeVars ?BE = TE_RuntimeTypeVars ?B"
    using ng by (simp add: module_body_env_for_def fset_scoped_tyvars_eq2)
  have fE: "TE_Functions ?BE
              = fmmap erase_ghost_funinfo (fmfilter (tyenv_nonghost_fun env) (TE_Functions env))"
    by (simp add: module_body_env_for_def)
  have dE: "TE_Datatypes ?BE
              = fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env) (TE_Datatypes env)"
    by (simp add: module_body_env_for_def)
  have cE: "TE_DataCtors ?BE = fmfilter (tyenv_nonghost_ctor env) (TE_DataCtors env)"
    by (simp add: module_body_env_for_def)
  have bE: "TE_DataCtorsByType ?BE
              = fmfilter (\<lambda>dtName. dtName |\<notin>| TE_GhostDatatypes env)
                         (TE_DataCtorsByType env)"
    by (simp add: module_body_env_for_def)
  have gdE: "TE_GhostDatatypes ?BE = {||}"
    by (simp add: module_body_env_for_def)
  have decls: "tyenv_decls_erased ?B ?BE"
    unfolding tyenv_decls_erased_def f c flds
    using g tvE rtvE fE dE cE bE gdE by blast
  have ret: "TE_ReturnType ?BE = TE_ReturnType ?B"
    and fg: "TE_FunctionGhost ?BE = TE_FunctionGhost ?B"
    and fi: "TE_FunctionImpure ?BE = TE_FunctionImpure ?B"
    and gl: "TE_GhostLocals ?BE = {||}"
    using ng by (simp_all add: module_body_env_for_def erased_params_no_ghost)
  \<comment> \<open>A name that is not a ghost local of the original body environment is not
      the name of a ghost parameter, and so it means the same on both sides.\<close>
  have locals: "fmlookup (TE_LocalVars ?BE) name = fmlookup (TE_LocalVars ?B) name
                \<and> (name |\<in>| TE_ConstLocals ?BE \<longleftrightarrow> name |\<in>| TE_ConstLocals ?B)"
    if nv: "\<not> tyenv_var_ghost ?B name" for name
  proof -
    \<comment> \<open>The fields of the two body environments, written out. They are stated
        as equations and used by unfolding, so that simp does not get to
        rewrite the two sides of the goal into different forms.\<close>
    have glB: "TE_GhostLocals ?B
                 = fset_of_list (map fst (filter (\<lambda>(_, _, gh). gh = Ghost)
                                                 (zip names (map snd (FI_TmArgs info)))))"
      using ng by (simp add: module_body_env_for_def)
    have lvB: "fmlookup (TE_LocalVars ?B) name
                 = map_of (zip names (map fst (FI_TmArgs info))) name"
      by (simp add: module_body_env_for_def fmlookup_of_list)
    have lvE: "fmlookup (TE_LocalVars ?BE) name
                 = map_of (zip (drop_ghost (map (\<lambda>(_, _, gh). gh) (FI_TmArgs info)) names)
                               (map fst (filter (\<lambda>(_, _, gh). gh = NotGhost)
                                                (FI_TmArgs info)))) name"
      by (simp add: module_body_env_for_def fmlookup_of_list param_ghost_flags_def)
    have clB: "TE_ConstLocals ?B
                 = fset_of_list (map fst (filter (\<lambda>(_, vor, _). vor = Var)
                                                 (zip names (map snd (FI_TmArgs info)))))"
      by (simp add: module_body_env_for_def)
    have clE: "TE_ConstLocals ?BE
                 = fset_of_list
                     (map fst (filter (\<lambda>(_, vor, _). vor = Var)
                        (zip (drop_ghost (map (\<lambda>(_, _, gh). gh) (FI_TmArgs info)) names)
                             (map snd (filter (\<lambda>(_, _, gh). gh = NotGhost)
                                              (FI_TmArgs info))))))"
      by (simp add: module_body_env_for_def param_ghost_flags_def)
    have mem: "(name |\<in>| fset_of_list (map fst xs)) = (name \<in> fst ` set xs)"
      for xs :: "(string \<times> VarOrRef \<times> GhostOrNot) list"
      by (simp only: fset_of_list_elem set_map)
    have notg: "name \<notin> fst ` set (filter (\<lambda>(_, _, gh). gh = Ghost)
                                          (zip names (map snd (FI_TmArgs info))))"
    proof
      assume a: "name \<in> fst ` set (filter (\<lambda>(_, _, gh). gh = Ghost)
                                           (zip names (map snd (FI_TmArgs info))))"
      hence "name \<in> set names" by (auto dest: set_zip_leftD)
      hence "\<exists>y. map_of (zip names (map fst (FI_TmArgs info))) name = Some y"
        using len map_of_zip_is_Some[of names "map fst (FI_TmArgs info)" name] by simp
      hence bound: "fmlookup (TE_LocalVars ?B) name \<noteq> None"
        unfolding lvB by simp
      have "name |\<in>| TE_GhostLocals ?B"
        unfolding glB mem by (rule a)
      with bound nv show False unfolding tyenv_var_ghost_def by simp
    qed
    show ?thesis
      unfolding lvB lvE clB clE mem
      using body_env_locals_erased[OF len notg] body_env_consts_erased[OF len notg]
      by blast
  qed
  show ?thesis
    unfolding tyenv_erased_def using decls ret fg fi gl locals by blast
qed


(* ========================================================================== *)
(* The module *)
(* ========================================================================== *)

(* Erasure preserves well-typedness, for a normalized module. *)
theorem erase_ghost_module_well_typed:
  assumes wt: "core_module_well_typed m" and norm: "CM_TypeSubst m = fmempty"
  shows "core_module_well_typed (erase_ghost_module m)"
proof -
  let ?env = "CM_TyEnv m"
  let ?E = "erase_ghost_tyenv ?env"
  have nwt: "normalized_module_well_typed m"
    using wt core_module_well_typed_on_normalized[OF norm] by simp
  hence wf: "tyenv_well_formed ?env"
    and scope: "tyenv_module_scope ?env"
    and glob: "module_globals_well_typed ?env (CM_GlobalVars m)"
    and funs: "module_functions_well_typed ?env (CM_Functions m)"
    unfolding normalized_module_well_typed_def by simp_all

  have wfE: "tyenv_well_formed ?E"
    by (rule erase_ghost_tyenv_well_formed[OF wf scope])
  have scopeE: "tyenv_module_scope ?E"
    using scope unfolding tyenv_module_scope_def by simp
  have gl: "TE_GhostLocals ?env = {||}"
    using scope unfolding tyenv_module_scope_def by simp
  have rel: "tyenv_erased ?env ?E"
    by (rule tyenv_erased_erase_ghost_tyenv[OF gl])

  have globE: "module_globals_well_typed ?E (CM_GlobalVars m)"
    unfolding module_globals_well_typed_def
  proof (intro allI impI)
    fix name v assume lk: "fmlookup (CM_GlobalVars m) name = Some v"
    from glob lk obtain declTy where
        d: "fmlookup (TE_GlobalVars ?env) name = Some declTy" and
        vt: "value_has_type ?env v declTy"
      unfolding module_globals_well_typed_def by blast
    have ground: "type_tyvars declTy = {}" by (rule value_has_type_ground[OF vt])
    have "tyenv_vars_runtime ?env"
      using wf unfolding tyenv_well_formed_def by simp
    hence rt0: "is_runtime_type
                  (?env \<lparr> TE_TypeVars := TE_AbstractTypes ?env,
                          TE_RuntimeTypeVars :=
                            TE_AbstractTypes ?env |\<inter>| TE_RuntimeTypeVars ?env \<rparr>) declTy"
      using d unfolding tyenv_vars_runtime_def by blast
    have "is_runtime_type ?env declTy
            = is_runtime_type
                (?env \<lparr> TE_TypeVars := TE_AbstractTypes ?env,
                        TE_RuntimeTypeVars :=
                          TE_AbstractTypes ?env |\<inter>| TE_RuntimeTypeVars ?env \<rparr>) declTy"
      by (rule is_runtime_type_ground_cong_env[OF ground]) simp
    hence rt: "is_runtime_type ?env declTy" using rt0 by simp
    have vtE: "value_has_type ?E v declTy"
      by (rule value_has_type_erased[OF rel wf vt rt])
    show "\<exists>declTy. fmlookup (TE_GlobalVars ?E) name = Some declTy
                   \<and> value_has_type ?E v declTy"
      using d vtE by simp
  qed

  have funsE: "module_functions_well_typed ?E (CM_Functions (erase_ghost_module m))"
    unfolding module_functions_well_typed_def
  proof (intro allI impI)
    fix name f
    assume lkE: "fmlookup (CM_Functions (erase_ghost_module m)) name = Some f"
    let ?F = "TE_Functions ?env"
    from lkE obtain f0 where
        lk0: "fmlookup (CM_Functions m) name = Some f0" and
        ngf: "tyenv_nonghost_fun ?env name" and
        f: "f = erase_ghost_function ?F name f0"
      unfolding erase_ghost_module_fun_lookup by blast
    from funs lk0 obtain info where
        fi: "fmlookup (TE_Functions ?env) name = Some info" and
        len: "length (CF_Args f0) = length (FI_TmArgs info)" and
        dist: "distinct (CF_Args f0)" and
        body: "case CF_Body f0 of
                 None \<Rightarrow> True
               | Some body \<Rightarrow>
                   core_statement_list_type
                     (module_body_env_for ?env (CF_Args f0) info) (FI_Ghost info) body
                   \<noteq> None"
      unfolding module_functions_well_typed_def by blast
    have ng: "FI_Ghost info = NotGhost"
      using ngf fi unfolding tyenv_nonghost_fun_def by simp
    \<comment> \<open>The erased signature and the erased parameter names.\<close>
    let ?infoE = "erase_ghost_funinfo info"
    let ?namesE = "drop_ghost (param_ghost_flags info) (CF_Args f0)"
    have fiE: "fmlookup (TE_Functions ?E) name = Some ?infoE"
      by (rule tyenv_erased_fun_lookup[OF rel fi ng])
    have argsE: "CF_Args f = ?namesE"
      unfolding f by (simp add: erase_ghost_args_def fi)
    have bodyE: "case CF_Body f0 of
                   None \<Rightarrow> True
                 | Some body \<Rightarrow>
                     core_statement_list_type
                       (module_body_env_for ?E ?namesE ?infoE) NotGhost
                       (erase_ghost_statement_list ?F body)
                     \<noteq> None"
    proof (cases "CF_Body f0")
      case None
      then show ?thesis by simp
    next
      case (Some body0)
      from body Some ng obtain envB where
          t: "core_statement_list_type
                (module_body_env_for ?env (CF_Args f0) info) NotGhost body0 = Some envB"
        by auto
      have wfB: "tyenv_well_formed (module_body_env_for ?env (CF_Args f0) info)"
        by (rule module_body_env_for_well_formed[OF wf fi len])
      have relB: "tyenv_erased (module_body_env_for ?env (CF_Args f0) info)
                               (module_body_env_for ?E ?namesE ?infoE)"
        by (rule tyenv_erased_module_body_env[OF ng len])
      have fnB: "TE_Functions (module_body_env_for ?env (CF_Args f0) info) = ?F"
        by (simp add: module_body_env_for_def)
      from erase_ghost_statement_list_typed[OF t wfB relB, unfolded fnB] obtain envBE where
          "core_statement_list_type
             (module_body_env_for ?E ?namesE ?infoE) NotGhost
             (erase_ghost_statement_list ?F body0) = Some envBE"
        by blast
      thus ?thesis using Some by simp
    qed
    have bodyE': "case CF_Body f of
                    None \<Rightarrow> True
                  | Some body \<Rightarrow>
                      core_statement_list_type
                        (module_body_env_for ?E (CF_Args f) ?infoE) (FI_Ghost ?infoE) body
                      \<noteq> None"
      unfolding argsE using bodyE ng unfolding f by (cases "CF_Body f0") simp_all
    have lenE: "length (CF_Args f) = length (FI_TmArgs ?infoE)"
      unfolding argsE param_ghost_flags_def
      using length_drop_ghost_params[OF len] by simp
    have distE: "distinct (CF_Args f)"
      unfolding argsE by (rule distinct_drop_ghost[OF dist])
    show "\<exists>info. fmlookup (TE_Functions ?E) name = Some info
                 \<and> length (CF_Args f) = length (FI_TmArgs info)
                 \<and> distinct (CF_Args f)
                 \<and> (case CF_Body f of
                      None \<Rightarrow> True
                    | Some body \<Rightarrow>
                        core_statement_list_type
                          (module_body_env_for ?E (CF_Args f) info) (FI_Ghost info) body
                        \<noteq> None)"
      by (intro exI[of _ ?infoE] conjI) (rule fiE lenE distE bodyE')+
  qed

  have nwtE: "normalized_module_well_typed (erase_ghost_module m)"
    unfolding normalized_module_well_typed_def
    using wfE scopeE globE funsE by simp
  have normE: "CM_TypeSubst (erase_ghost_module m) = fmempty"
    using norm by simp
  show ?thesis
    using nwtE core_module_well_typed_on_normalized[OF normE] by simp
qed

end

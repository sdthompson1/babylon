theory ElabDeclCorrect
  imports ElabDecl ElabStmtCorrect "../core/LinkPreservesWellTyped"
begin

(* Correctness of the declaration-list elaborator: "elaboration produces
   well-typed modules".

   Elaboration does not on its own produce a well-typed CoreModule: a module
   elaborated in isolation refers to types/constants/functions it does not
   itself declare (it is elaborated against a non-empty CoreTyEnv describing
   exactly those external names), so its raw output has dangling references.
   Well-typedness is established the moment it is linked with a module
   supplying those references:

     If I is a well-typed CoreModule with an empty substitution, and
     elaborating some declarations in CM_TyEnv I produces M, and
     link_modules [I, M] succeeds producing L, then L is well-typed.

   (The empty-substitution hypothesis is no restriction in practice: the
   contexts the pipeline elaborates against are links of interface faces
   only, and interface elaboration never realizes an abstract type, so
   those contexts always carry empty substitutions. It buys a lot: I is
   already normalized, CM_TyEnv I is directly tyenv_well_formed, and the
   merged substitution of the link is CM_TypeSubst M alone.)

   Note the contrast with link_preserves_well_typed: there BOTH operands are
   independently well-typed and linking preserves that; here M is NOT
   well-typed in isolation, and the link is what closes it.

   The heart of the proof is a fold invariant on elab_declaration_list,
   stated below as elab_decls_invariant: the elaborator's state env is the
   substitution image of the context combined with the module's recorded
   declarations, and everything recorded so far typechecks in the state env.
   This file defines the invariant and states the main lemmas; the proofs
   (the per-declaration preservation induction, and the final link-step
   assembly) follow separately. *)


(* ========================================================================== *)
(* Metavariable freshness of declaration binders                              *)
(* ========================================================================== *)

(* The type-variable names a declaration binds: a function's or datatype's
   type parameters; a typedef's parameters plus, for "type T;", the abstract
   type name itself (which enters TE_TypeVars). Constants bind none. *)
fun decl_tyvar_binders :: "BabDeclaration \<Rightarrow> string list" where
  "decl_tyvar_binders (BabDecl_Const dc) = []"
| "decl_tyvar_binders (BabDecl_Function df) = DF_TyArgs df"
| "decl_tyvar_binders (BabDecl_Datatype dd) = DD_TyArgs dd"
| "decl_tyvar_binders (BabDecl_Typedef dt) = DT_Name dt # DT_TyArgs dt"

(* The statement/term elaborator requires every in-scope type variable to be
   distinct from every metavariable name (the "tyvar_fresh_ok n next_mv" entry
   invariant of elab_statement_correct); since the metavariable counter
   restarts at 0 for each declaration, we need the binders fresh at 0, i.e.
   never of the mv_name shape at all. This is a hypothesis on the input
   (discharged by the renamer's naming discipline), not an elaborator check -
   matching the treatment at the statement level. *)
definition decl_tyvars_fresh_ok :: "BabDeclaration \<Rightarrow> bool" where
  "decl_tyvars_fresh_ok d = list_all (\<lambda>n. tyvar_fresh_ok n 0) (decl_tyvar_binders d)"


(* ========================================================================== *)
(* The state env as a function of the context and the module                  *)
(* ========================================================================== *)

(* The elaborator's state env, reconstructed from the (fixed) context env and
   the (growing) module: field-wise combination of the context with the
   module's recorded declarations - definition maps right-biased-unioned, ghost
   fsets unioned, the three type-variable fields unioned minus the domain of
   the module's substitution (a realized abstract type is no longer abstract) -
   with the module's substitution then applied to all recorded signatures.
   The scope fields (locals, return type, proof fields) are inherited from the
   context, which is at module scope.

   The field formulas deliberately mirror link_result on the two-module list
   [context, m] followed by normalize_module's env rewrite: when the link of
   the context's module and m succeeds, the state env IS the normalized linked
   env. That equation is the M-side of the final assembly. *)
definition module_context_env :: "CoreTyEnv \<Rightarrow> CoreModule \<Rightarrow> CoreTyEnv" where
  "module_context_env ctx m =
     apply_subst_to_tyenv (CM_TypeSubst m)
       (ctx \<lparr>
          TE_GlobalVars := TE_GlobalVars ctx ++\<^sub>f TE_GlobalVars (CM_TyEnv m),
          TE_GhostGlobals := TE_GhostGlobals ctx |\<union>| TE_GhostGlobals (CM_TyEnv m),
          TE_TypeVars := (TE_TypeVars ctx |\<union>| TE_TypeVars (CM_TyEnv m))
                           |-| fmdom (CM_TypeSubst m),
          TE_RuntimeTypeVars := (TE_RuntimeTypeVars ctx |\<union>| TE_RuntimeTypeVars (CM_TyEnv m))
                           |-| fmdom (CM_TypeSubst m),
          TE_AbstractTypes := (TE_AbstractTypes ctx |\<union>| TE_AbstractTypes (CM_TyEnv m))
                           |-| fmdom (CM_TypeSubst m),
          TE_Functions := TE_Functions ctx ++\<^sub>f TE_Functions (CM_TyEnv m),
          TE_Datatypes := TE_Datatypes ctx ++\<^sub>f TE_Datatypes (CM_TyEnv m),
          TE_DataCtors := TE_DataCtors ctx ++\<^sub>f TE_DataCtors (CM_TyEnv m),
          TE_DataCtorsByType := TE_DataCtorsByType ctx ++\<^sub>f TE_DataCtorsByType (CM_TyEnv m),
          TE_GhostDatatypes := TE_GhostDatatypes ctx |\<union>| TE_GhostDatatypes (CM_TyEnv m)
        \<rparr>)"


(* ========================================================================== *)
(* Standing facts about the elaboration context                               *)
(* ========================================================================== *)

(* The facts about the (fixed) context env and ownAbstract set that the fold
   invariant carries along unchanged: the context is a well-formed module-scope
   env; the realizable abstract types are among the context's abstract types;
   and the context's type variables and function type parameters are all
   metavariable-fresh. (When the context is CM_TyEnv I for a well-typed
   normalized I, the first two conjuncts come from I's well-typedness.) *)
definition elab_context_ok :: "CoreTyEnv \<Rightarrow> string fset \<Rightarrow> bool" where
  "elab_context_ok env0 ownAbstract =
    (tyenv_well_formed env0
     \<and> tyenv_module_scope env0
     \<and> ownAbstract |\<subseteq>| TE_TypeVars env0
     \<and> (\<forall>n. n |\<in>| TE_TypeVars env0 \<longrightarrow> tyvar_fresh_ok n 0)
     \<and> (\<forall>name info. fmlookup (TE_Functions env0) name = Some info \<longrightarrow>
          list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)))"


(* ========================================================================== *)
(* The fold invariant                                                         *)
(* ========================================================================== *)

(* The invariant maintained by elab_declaration over the state triple
   (env, elabEnv, m), with env0 the (fixed) context env and ownAbstract the
   (fixed) set of realizable abstract types. The conjuncts:

   - the standing context facts (elab_context_ok);
   - env is exactly the context combined with the module and resolved through
     the module's substitution (module_context_env) - the single equation from
     which the M-side of the link assembly falls out;
   - the module satisfies the standing structural invariant
     (core_module_invariant: idempotent capture-avoiding substitution, ghost
     markers on own declarations only, substitution domain disjoint from its
     own abstract types, module scope);
   - the module's own abstract types are new names, not realizable ones
     (needed to keep the substitution domain disjoint from TE_TypeVars
     (CM_TyEnv m) when a realization is recorded);
   - the state env is well-formed and the elab env is well-formed over it
     (the entry conditions of the term/statement elaborator lemmas);
   - the substitution's ranges are well-kinded in the state env (they must be,
     to survive into core_module_well_typed of the link);
   - only ownAbstract names are realized, and realized names keep their
     EE_Typedefs entry (so a later declaration of the same name is caught by
     type_name_in_scope - the state env has forgotten the name, the typedef
     table has not);
   - no name touched by the substitution (domain or range tyvars) is a bound
     type parameter anywhere in scope: functions' FI_TyArgs, data constructor
     tyvars, or typedef parameters, across BOTH the context's entries and the
     module's own. Strictly stronger than capture_avoiding m; the typedef
     clause is needed because apply_realization rewrites typedef ranges
     binder-blindly, and the context clause because the final link's capture
     check spans both modules;
   - metavariable freshness: every in-scope type variable, and every type
     parameter of every function in scope, is metavariable-fresh (entry
     conditions for elaborating later declarations' bodies at counter 0);
   - everything recorded so far typechecks in the state env: the module's
     globals and functions, with the substitution applied (phrased via
     normalize_module m, whose globals/bodies are exactly the substituted
     ones). Entries recorded before a realization are re-established by the
     substitution-preservation engine when the realization rewrites env;
     entries recorded after are born resolved (their types avoid the
     substitution domain, so applying it is the identity). *)
definition elab_decls_invariant ::
  "CoreTyEnv \<Rightarrow> string fset \<Rightarrow> CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> CoreModule \<Rightarrow> bool" where
  "elab_decls_invariant env0 ownAbstract env elabEnv m =
    (elab_context_ok env0 ownAbstract
     \<and> env = module_context_env env0 m
     \<and> core_module_invariant m
     \<and> ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}
     \<and> tyenv_well_formed env
     \<and> elabenv_well_formed env elabEnv
     \<and> typesubst_well_kinded env (CM_TypeSubst m)
     \<and> fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract
     \<and> fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs elabEnv)
     \<and> subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}
     \<and> (\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0)
     \<and> (\<forall>name info. fmlookup (TE_Functions env) name = Some info \<longrightarrow>
          list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info))
     \<and> module_globals_well_typed env (CM_GlobalVars (normalize_module m))
     \<and> module_functions_well_typed env (CM_Functions (normalize_module m)))"


(* ========================================================================== *)
(* The invariant holds initially                                              *)
(* ========================================================================== *)

(* At the start of the fold the module is empty, so the state env is the
   context itself and almost every conjunct is trivial or comes straight from
   the two assumptions. *)
lemma elab_decls_invariant_init:
  assumes ctx: "elab_context_ok env0 ownAbstract"
      and ee: "elabenv_well_formed env0 elabEnv0"
  shows "elab_decls_invariant env0 ownAbstract env0 elabEnv0 empty_core_module"
proof -
  have env_eq: "module_context_env env0 empty_core_module = env0"
    unfolding module_context_env_def empty_core_module_def empty_module_tyenv_def
    by (simp add: funion_fempty_right)
  have inv: "core_module_invariant empty_core_module"
    unfolding core_module_invariant_def capture_avoiding_def
              module_ghost_subsets_ok_def tyenv_module_scope_def
              empty_core_module_def empty_module_tyenv_def
    by simp
  have norm: "normalize_module empty_core_module = empty_core_module"
    by (rule normalize_module_id_when_empty) (simp add: empty_core_module_def)
  \<comment> \<open>Keep empty_core_module folded in the final goal (so env_eq, inv and norm
      match it), providing just the projections the remaining clauses need.\<close>
  have proj: "CM_TypeSubst empty_core_module = fmempty"
             "CM_GlobalVars empty_core_module = fmempty"
             "CM_Functions empty_core_module = fmempty"
             "TE_TypeVars (CM_TyEnv empty_core_module) = {||}"
    by (simp_all add: empty_core_module_def empty_module_tyenv_def)
  show ?thesis
    unfolding elab_decls_invariant_def
    using ctx ee inv
    by (simp add: env_eq norm proj elab_context_ok_def
                  typesubst_well_kinded_def
                  module_globals_well_typed_def module_functions_well_typed_def)
qed


(* ========================================================================== *)
(* Helpers for the per-declaration preservation proof                         *)
(* ========================================================================== *)

(* Intersecting with a subset of a disjoint set. *)
lemma empty_inter_subset:
  fixes A B C :: "string fset"
  assumes "A |\<inter>| C = {||}"
      and "B |\<subseteq>| C"
  shows "A |\<inter>| B = {||}"
  using assms by (metis inf_mono le_bot order_refl)

(* The type-variable fields of the state env, read off from its definition
   (apply_subst_to_tyenv does not touch them). *)
lemma module_context_env_tyvar_fields:
  "TE_TypeVars (module_context_env ctx m)
     = (TE_TypeVars ctx |\<union>| TE_TypeVars (CM_TyEnv m)) |-| fmdom (CM_TypeSubst m)"
  "TE_RuntimeTypeVars (module_context_env ctx m)
     = (TE_RuntimeTypeVars ctx |\<union>| TE_RuntimeTypeVars (CM_TyEnv m)) |-| fmdom (CM_TypeSubst m)"
  "TE_AbstractTypes (module_context_env ctx m)
     = (TE_AbstractTypes ctx |\<union>| TE_AbstractTypes (CM_TyEnv m)) |-| fmdom (CM_TypeSubst m)"
  unfolding module_context_env_def apply_subst_to_tyenv_def by simp_all

(* The realizable abstract types are covered by the state env's type
   variables together with the recorded substitution domain: they live in the
   context's TE_TypeVars, and the state env only subtracts realized
   (substitution-domain) names from that. *)
lemma elab_decls_invariant_ownAbstract_cover:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
  shows "ownAbstract |\<subseteq>| TE_TypeVars env |\<union>| fmdom (CM_TypeSubst m)"
proof -
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
    using inv unfolding elab_decls_invariant_def by blast+
  have own_sub: "ownAbstract |\<subseteq>| TE_TypeVars env0"
    using ctx unfolding elab_context_ok_def by blast
  show ?thesis
    unfolding env_eq module_context_env_tyvar_fields(1)
    using own_sub by auto
qed

(* Growing TE_AbstractTypes (within TE_TypeVars) preserves tyenv_well_formed.
   The clauses that read TE_AbstractTypes only use it as (part of) the
   TE_TypeVars / TE_RuntimeTypeVars override of an inner env; the override
   grows pointwise, so monotonicity of is_well_kinded / is_runtime_type
   carries them over. The remaining clauses do not read the field. *)
lemma tyenv_well_formed_grow_abstract_types:
  assumes wf: "tyenv_well_formed env"
      and sub: "eAB |\<subseteq>| TE_TypeVars env"
  shows "tyenv_well_formed (env \<lparr> TE_AbstractTypes := TE_AbstractTypes env |\<union>| eAB \<rparr>)"
proof -
  let ?env' = "env \<lparr> TE_AbstractTypes := TE_AbstractTypes env |\<union>| eAB \<rparr>"
  from wf have
    vars_wk: "tyenv_vars_well_kinded env" and
    vars_rt: "tyenv_vars_runtime env" and
    ghost_sub: "tyenv_ghost_vars_subset env" and
    ret_wk: "tyenv_return_type_well_kinded env" and
    ret_rt: "tyenv_return_type_runtime env" and
    ctors_cons: "tyenv_ctors_consistent env" and
    pay_wk: "tyenv_payloads_well_kinded env" and
    ctor_dist: "tyenv_ctor_tyvars_distinct env" and
    bytype: "tyenv_ctors_by_type_consistent env" and
    fun_wk: "tyenv_fun_types_well_kinded env" and
    fun_dist: "tyenv_fun_tyvars_distinct env" and
    fun_ghost: "tyenv_fun_ghost_constraint env" and
    ng_pay: "tyenv_nonghost_payloads_runtime env" and
    gdt_sub: "tyenv_ghost_datatypes_subset env" and
    rtv_sub: "tyenv_runtime_tyvars_subset env" and
    abs_sub: "tyenv_abstract_types_subset env" and
    dt_ne: "tyenv_datatypes_nonempty env"
    unfolding tyenv_well_formed_def by blast+
  \<comment> \<open>?env' agrees with env on everything the plain-env kind/runtime checks read.\<close>
  have wk_cong: "\<And>ty. is_well_kinded ?env' ty = is_well_kinded env ty"
    by (rule is_well_kinded_cong_env) simp_all
  have rt_cong: "\<And>ty. is_runtime_type ?env' ty = is_runtime_type env ty"
    by (rule is_runtime_type_cong_env) simp_all

  have vars_wk': "tyenv_vars_well_kinded ?env'"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix name ty assume "fmlookup (TE_LocalVars ?env') name = Some ty"
    then have lk: "fmlookup (TE_LocalVars env) name = Some ty" by simp
    have "is_well_kinded env ty"
      using vars_wk lk unfolding tyenv_vars_well_kinded_def by blast
    then show "is_well_kinded ?env' ty" by (simp add: wk_cong)
  next
    fix name ty assume "fmlookup (TE_GlobalVars ?env') name = Some ty"
    then have lk: "fmlookup (TE_GlobalVars env) name = Some ty" by simp
    have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
      using vars_wk lk unfolding tyenv_vars_well_kinded_def by blast
    then show "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' \<rparr>) ty"
      by (rule is_well_kinded_mono) auto
  qed

  have vars_rt': "tyenv_vars_runtime ?env'"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix name ty
    assume "fmlookup (TE_LocalVars ?env') name = Some ty \<and> name |\<notin>| TE_GhostLocals ?env'"
    then have "fmlookup (TE_LocalVars env) name = Some ty \<and> name |\<notin>| TE_GhostLocals env"
      by simp
    then have "is_runtime_type env ty"
      using vars_rt unfolding tyenv_vars_runtime_def by blast
    then show "is_runtime_type ?env' ty" by (simp add: rt_cong)
  next
    fix name ty
    assume "fmlookup (TE_GlobalVars ?env') name = Some ty \<and> name |\<notin>| TE_GhostGlobals ?env'"
    then have "fmlookup (TE_GlobalVars env) name = Some ty \<and> name |\<notin>| TE_GhostGlobals env"
      by simp
    then have "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                    TE_RuntimeTypeVars := TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
      using vars_rt unfolding tyenv_vars_runtime_def by blast
    then show "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env',
                    TE_RuntimeTypeVars := TE_AbstractTypes ?env' |\<inter>| TE_RuntimeTypeVars ?env' \<rparr>) ty"
      by (rule is_runtime_type_mono_rtv) auto
  qed

  have ret_wk': "tyenv_return_type_well_kinded ?env'"
    using ret_wk unfolding tyenv_return_type_well_kinded_def by (simp add: wk_cong)
  have ret_rt': "tyenv_return_type_runtime ?env'"
    using ret_rt unfolding tyenv_return_type_runtime_def by (simp add: rt_cong)
  have ghost_sub': "tyenv_ghost_vars_subset ?env'"
    using ghost_sub unfolding tyenv_ghost_vars_subset_def by simp
  have ctors_cons': "tyenv_ctors_consistent ?env'"
    using ctors_cons unfolding tyenv_ctors_consistent_def by simp
  have ctor_dist': "tyenv_ctor_tyvars_distinct ?env'"
    using ctor_dist unfolding tyenv_ctor_tyvars_distinct_def by simp
  have bytype': "tyenv_ctors_by_type_consistent ?env'"
    using bytype unfolding tyenv_ctors_by_type_consistent_def by simp
  have fun_dist': "tyenv_fun_tyvars_distinct ?env'"
    using fun_dist unfolding tyenv_fun_tyvars_distinct_def by simp
  have gdt_sub': "tyenv_ghost_datatypes_subset ?env'"
    using gdt_sub unfolding tyenv_ghost_datatypes_subset_def by simp
  have rtv_sub': "tyenv_runtime_tyvars_subset ?env'"
    using rtv_sub unfolding tyenv_runtime_tyvars_subset_def by simp
  have dt_ne': "tyenv_datatypes_nonempty ?env'"
    using dt_ne unfolding tyenv_datatypes_nonempty_def by simp
  have abs_sub': "tyenv_abstract_types_subset ?env'"
    using abs_sub sub unfolding tyenv_abstract_types_subset_def by auto

  have pay_wk': "tyenv_payloads_well_kinded ?env'"
    unfolding tyenv_payloads_well_kinded_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?env') ctorName = Some (dtName, tyVars, payload)"
    then have lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
      by simp
    have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars \<rparr>)
                         payload"
      using pay_wk lk unfolding tyenv_payloads_well_kinded_def by blast
    then show "is_well_kinded
                 (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' |\<union>| fset_of_list tyVars \<rparr>)
                 payload"
      by (rule is_well_kinded_mono) auto
  qed

  have fun_wk': "tyenv_fun_types_well_kinded ?env'"
    unfolding tyenv_fun_types_well_kinded_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?env') funName = Some info"
    then have lk: "fmlookup (TE_Functions env) funName = Some info" by simp
    have base: "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
                   is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                \<and> is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                 (FI_ReturnType info)"
      using fun_wk lk unfolding tyenv_fun_types_well_kinded_def by blast
    have args: "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                  is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                           |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
    proof
      fix ty assume "ty \<in> fst ` set (FI_TmArgs info)"
      then have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                        |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        using base by blast
      then show "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        by (rule is_well_kinded_mono) auto
    qed
    have ret: "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                        |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                              (FI_ReturnType info)"
    proof -
      have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                   |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) (FI_ReturnType info)"
        using base by blast
      then show ?thesis by (rule is_well_kinded_mono) auto
    qed
    show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
             is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                      |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
          \<and> is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                      |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                           (FI_ReturnType info)"
      using args ret by blast
  qed

  have fun_ghost': "tyenv_fun_ghost_constraint ?env'"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?env') funName = Some info \<and> FI_Ghost info = NotGhost"
    then have lk: "fmlookup (TE_Functions env) funName = Some info"
          and ng: "FI_Ghost info = NotGhost"
      by simp_all
    have base: "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
                   is_runtime_type
                     (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                              |\<union>| fset_of_list (FI_TyArgs info),
                            TE_RuntimeTypeVars := (TE_AbstractTypes env
                                                    |\<inter>| TE_RuntimeTypeVars env)
                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                \<and> is_runtime_type
                     (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                              |\<union>| fset_of_list (FI_TyArgs info),
                            TE_RuntimeTypeVars := (TE_AbstractTypes env
                                                    |\<inter>| TE_RuntimeTypeVars env)
                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                     (FI_ReturnType info)"
      using fun_ghost lk ng unfolding tyenv_fun_ghost_constraint_def Let_def by blast
    have mono: "\<And>ty. is_runtime_type
                     (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                              |\<union>| fset_of_list (FI_TyArgs info),
                            TE_RuntimeTypeVars := (TE_AbstractTypes env
                                                    |\<inter>| TE_RuntimeTypeVars env)
                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                \<Longrightarrow> is_runtime_type
                     (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars := (TE_AbstractTypes ?env'
                                                      |\<inter>| TE_RuntimeTypeVars ?env')
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
      by (erule is_runtime_type_mono_rtv) auto
    show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
             is_runtime_type
               (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                          |\<union>| fset_of_list (FI_TyArgs info),
                        TE_RuntimeTypeVars := (TE_AbstractTypes ?env'
                                                |\<inter>| TE_RuntimeTypeVars ?env')
                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
          \<and> is_runtime_type
               (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                          |\<union>| fset_of_list (FI_TyArgs info),
                        TE_RuntimeTypeVars := (TE_AbstractTypes ?env'
                                                |\<inter>| TE_RuntimeTypeVars ?env')
                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
               (FI_ReturnType info)"
      using base mono by blast
  qed

  have ng_pay': "tyenv_nonghost_payloads_runtime ?env'"
    unfolding tyenv_nonghost_payloads_runtime_def
  proof (intro allI impI)
    fix ctorName dtName tyVars payload
    assume lk': "fmlookup (TE_DataCtors ?env') ctorName = Some (dtName, tyVars, payload)"
       and ng': "dtName |\<notin>| TE_GhostDatatypes ?env'"
    have lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
      using lk' by simp
    have ng: "dtName |\<notin>| TE_GhostDatatypes env" using ng' by simp
    have "is_runtime_type
            (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars,
                   TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                          |\<union>| fset_of_list tyVars \<rparr>) payload"
      using ng_pay lk ng unfolding tyenv_nonghost_payloads_runtime_def by blast
    then show "is_runtime_type
                 (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' |\<union>| fset_of_list tyVars,
                          TE_RuntimeTypeVars := (TE_AbstractTypes ?env'
                                                  |\<inter>| TE_RuntimeTypeVars ?env')
                                                 |\<union>| fset_of_list tyVars \<rparr>) payload"
      by (rule is_runtime_type_mono_rtv) auto
  qed

  show ?thesis
    unfolding tyenv_well_formed_def
    using vars_wk' vars_rt' ghost_sub' ret_wk' ret_rt' ctors_cons' pay_wk' ctor_dist'
          bytype' fun_wk' fun_dist' fun_ghost' ng_pay' gdt_sub' rtv_sub' abs_sub' dt_ne'
    by blast
qed

(* Growing all three type-variable fields together. *)
lemma tyenv_well_formed_grow_tyvar_fields:
  assumes wf: "tyenv_well_formed env"
      and rt_sub: "eRT |\<subseteq>| eTV"
      and ab_sub: "eAB |\<subseteq>| eTV"
  shows "tyenv_well_formed
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| eTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| eRT,
                  TE_AbstractTypes := TE_AbstractTypes env |\<union>| eAB \<rparr>)"
proof -
  let ?mid = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| eTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| eRT \<rparr>"
  have wf_mid: "tyenv_well_formed ?mid"
    using tyenv_well_formed_extend_tyvars[OF wf rt_sub] .
  have sub_mid: "eAB |\<subseteq>| TE_TypeVars ?mid"
    using ab_sub by auto
  have "tyenv_well_formed (?mid \<lparr> TE_AbstractTypes := TE_AbstractTypes ?mid |\<union>| eAB \<rparr>)"
    using tyenv_well_formed_grow_abstract_types[OF wf_mid sub_mid] .
  then show ?thesis by simp
qed

(* tyenv_add_abstract_type, phrased as a growth of the three tyvar fields. *)
lemma tyenv_add_abstract_type_as_grow:
  "tyenv_add_abstract_type name ghost env
     = env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env
                |\<union>| (if ghost = NotGhost then {|name|} else {||}),
             TE_AbstractTypes := TE_AbstractTypes env |\<union>| {|name|} \<rparr>"
  unfolding tyenv_add_abstract_type_def by (cases ghost) simp_all

lemma tyenv_well_formed_add_abstract_type:
  assumes wf: "tyenv_well_formed env"
  shows "tyenv_well_formed (tyenv_add_abstract_type name ghost env)"
  unfolding tyenv_add_abstract_type_as_grow
  by (rule tyenv_well_formed_grow_tyvar_fields[OF wf]) (auto split: if_splits)

(* Recorded globals stay well-typed when the tyvar fields grow: the
   TE_TypeVars / TE_RuntimeTypeVars growth is the irrelevant-tyvar weakening,
   and the TE_AbstractTypes change is invisible to the typechecker (it is not
   pinned by tyenv_extends). *)
lemma module_globals_well_typed_grow_tyvar_fields:
  assumes gwt: "module_globals_well_typed env globals"
      and cons: "tyenv_ctors_consistent env"
  shows "module_globals_well_typed
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| eTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| eRT,
                  TE_AbstractTypes := TE_AbstractTypes env |\<union>| eAB \<rparr>) globals"
proof -
  let ?mid = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| eTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| eRT \<rparr>"
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| eTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| eRT,
                     TE_AbstractTypes := TE_AbstractTypes env |\<union>| eAB \<rparr>"
  have ext: "tyenv_extends ?mid ?env'"
    unfolding tyenv_extends_def by simp
  have cons_mid: "tyenv_ctors_consistent ?mid"
    using cons unfolding tyenv_ctors_consistent_def by simp
  show ?thesis
    unfolding module_globals_well_typed_def
  proof (intro allI impI)
    fix name tm
    assume "fmlookup globals name = Some tm"
    then obtain declTy where
        decl: "fmlookup (TE_GlobalVars env) name = Some declTy" and
        typed: "if name |\<in>| TE_GhostGlobals env
                then core_term_type env Ghost tm = Some declTy
                else is_constant_term tm \<and> core_term_type env NotGhost tm = Some declTy"
      using gwt unfolding module_globals_well_typed_def by blast
    have decl': "fmlookup (TE_GlobalVars ?env') name = Some declTy" using decl by simp
    have typed': "if name |\<in>| TE_GhostGlobals ?env'
                  then core_term_type ?env' Ghost tm = Some declTy
                  else is_constant_term tm \<and> core_term_type ?env' NotGhost tm = Some declTy"
    proof (cases "name |\<in>| TE_GhostGlobals env")
      case True
      then have "core_term_type env Ghost tm = Some declTy" using typed by simp
      then have "core_term_type ?mid Ghost tm = Some declTy"
        by (rule core_term_type_irrelevant_tyvar)
      then have "core_term_type ?env' Ghost tm = Some declTy"
        using core_term_type_tyenv_extends[OF ext cons_mid] by blast
      then show ?thesis using True by simp
    next
      case False
      then have c: "is_constant_term tm"
            and t: "core_term_type env NotGhost tm = Some declTy"
        using typed by simp_all
      have "core_term_type ?mid NotGhost tm = Some declTy"
        using t by (rule core_term_type_irrelevant_tyvar)
      then have "core_term_type ?env' NotGhost tm = Some declTy"
        using core_term_type_tyenv_extends[OF ext cons_mid] by blast
      then show ?thesis using False c by simp
    qed
    show "\<exists>declTy. fmlookup (TE_GlobalVars ?env') name = Some declTy \<and>
            (if name |\<in>| TE_GhostGlobals ?env'
             then core_term_type ?env' Ghost tm = Some declTy
             else is_constant_term tm \<and> core_term_type ?env' NotGhost tm = Some declTy)"
      using decl' typed' by blast
  qed
qed

(* Recorded function bodies stay well-typed when the tyvar fields grow. The
   body env's TE_TypeVars / TE_RuntimeTypeVars are derived from
   TE_AbstractTypes, so they grow pointwise (irrelevant-tyvar weakening), and
   the leftover TE_AbstractTypes difference is again invisible. *)
lemma module_functions_well_typed_grow_tyvar_fields:
  assumes fwt: "module_functions_well_typed env funs"
      and cons: "tyenv_ctors_consistent env"
  shows "module_functions_well_typed
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| eTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| eRT,
                  TE_AbstractTypes := TE_AbstractTypes env |\<union>| eAB \<rparr>) funs"
proof -
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| eTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| eRT,
                     TE_AbstractTypes := TE_AbstractTypes env |\<union>| eAB \<rparr>"
  show ?thesis
    unfolding module_functions_well_typed_def
  proof (intro allI impI)
    fix name f
    assume "fmlookup funs name = Some f"
    then obtain info where
        decl: "fmlookup (TE_Functions env) name = Some info" and
        len: "length (CF_Args f) = length (FI_TmArgs info)" and
        dist: "distinct (CF_Args f)" and
        body_ok: "case CF_Body f of
                    None \<Rightarrow> True
                  | Some body \<Rightarrow>
                      core_statement_list_type (module_body_env_for env (CF_Args f) info)
                        (FI_Ghost info) body \<noteq> None"
      using fwt unfolding module_functions_well_typed_def by blast
    have decl': "fmlookup (TE_Functions ?env') name = Some info" using decl by simp
    have body_ok': "case CF_Body f of
                      None \<Rightarrow> True
                    | Some body \<Rightarrow>
                        core_statement_list_type (module_body_env_for ?env' (CF_Args f) info)
                          (FI_Ghost info) body \<noteq> None"
    proof (cases "CF_Body f")
      case None then show ?thesis by simp
    next
      case (Some body)
      let ?B = "module_body_env_for env (CF_Args f) info"
      let ?B' = "module_body_env_for ?env' (CF_Args f) info"
      have bt: "core_statement_list_type ?B (FI_Ghost info) body \<noteq> None"
        using body_ok Some by simp
      then obtain out where t0: "core_statement_list_type ?B (FI_Ghost info) body = Some out"
        by (cases "core_statement_list_type ?B (FI_Ghost info) body") auto
      let ?mid = "?B \<lparr> TE_TypeVars := TE_TypeVars ?B |\<union>| TE_TypeVars ?B',
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars ?B
                                              |\<union>| TE_RuntimeTypeVars ?B' \<rparr>"
      have t1: "core_statement_list_type ?mid (FI_Ghost info) body
                  = Some (out \<lparr> TE_TypeVars := TE_TypeVars out |\<union>| TE_TypeVars ?B',
                                TE_RuntimeTypeVars := TE_RuntimeTypeVars out
                                                       |\<union>| TE_RuntimeTypeVars ?B' \<rparr>)"
        using core_statement_list_type_irrelevant_tyvar[OF t0] .
      have ext: "tyenv_extends ?mid ?B'"
        unfolding tyenv_extends_def module_body_env_for_def
        by (intro conjI allI impI fset_eqI) auto
      have cons_mid: "tyenv_ctors_consistent ?mid"
        using cons unfolding tyenv_ctors_consistent_def module_body_env_for_def by simp
      obtain out2 where t2: "core_statement_list_type ?B' (FI_Ghost info) body = Some out2"
        using core_statement_list_type_tyenv_extends[OF t1 ext cons_mid] by blast
      then show ?thesis using Some by simp
    qed
    show "\<exists>info. fmlookup (TE_Functions ?env') name = Some info \<and>
            length (CF_Args f) = length (FI_TmArgs info) \<and>
            distinct (CF_Args f) \<and>
            (case CF_Body f of
               None \<Rightarrow> True
             | Some body \<Rightarrow>
                 core_statement_list_type (module_body_env_for ?env' (CF_Args f) info)
                   (FI_Ghost info) body \<noteq> None)"
      using decl' len dist body_ok' by blast
  qed
qed

(* Declaring a new abstract type commutes with reconstructing the state env,
   provided the name is not touched by the recorded substitution. *)
lemma module_context_env_add_abstract_type:
  assumes fresh: "name |\<notin>| fmdom (CM_TypeSubst m)"
  shows "module_context_env ctx
           (m \<lparr> CM_TyEnv := tyenv_add_abstract_type name ghost (CM_TyEnv m) \<rparr>)
       = tyenv_add_abstract_type name ghost (module_context_env ctx m)"
proof -
  have ins_minus: "\<And>X. finsert name X |-| fmdom (CM_TypeSubst m)
                     = finsert name (X |-| fmdom (CM_TypeSubst m))"
    using fresh by (intro fset_eqI) auto
  show ?thesis
    unfolding module_context_env_def tyenv_add_abstract_type_def apply_subst_to_tyenv_def
    by (cases ghost) (simp_all add: ins_minus)
qed

(* typedefs_well_formed is monotone in the env's type variables (with the
   datatype table unchanged). *)
lemma typedefs_well_formed_mono:
  assumes twf: "typedefs_well_formed env tds"
      and tv: "TE_TypeVars env |\<subseteq>| TE_TypeVars env'"
      and dt: "TE_Datatypes env' = TE_Datatypes env"
  shows "typedefs_well_formed env' tds"
  unfolding typedefs_well_formed_def
proof (intro allI impI)
  fix name tyvars targetTy
  assume lk: "fmlookup tds name = Some (tyvars, targetTy)"
  have d: "distinct tyvars"
   and wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
                           targetTy"
    using twf lk unfolding typedefs_well_formed_def by blast+
  have "is_well_kinded (env' \<lparr> TE_TypeVars := TE_TypeVars env' |\<union>| fset_of_list tyvars \<rparr>)
                       targetTy"
    using wk by (rule is_well_kinded_mono)
                (use tv dt in \<open>auto simp: less_eq_fset.rep_eq\<close>)
  then show "distinct tyvars
             \<and> is_well_kinded (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                        |\<union>| fset_of_list tyvars \<rparr>) targetTy"
    using d by blast
qed

(* Registering an in-scope type variable in the typedef table keeps the table
   well-formed. *)
lemma typedefs_well_formed_upd_tyvar:
  assumes twf: "typedefs_well_formed env tds"
      and tv: "v |\<in>| TE_TypeVars env"
  shows "typedefs_well_formed env (fmupd v ([], CoreTy_Var v) tds)"
  unfolding typedefs_well_formed_def
proof (intro allI impI)
  fix name tyvars targetTy
  assume lk: "fmlookup (fmupd v ([], CoreTy_Var v) tds) name = Some (tyvars, targetTy)"
  show "distinct tyvars
        \<and> is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
                         targetTy"
  proof (cases "name = v")
    case True
    then have "tyvars = []" and "targetTy = CoreTy_Var v" using lk by auto
    then show ?thesis using tv by simp
  next
    case False
    then have "fmlookup tds name = Some (tyvars, targetTy)" using lk by simp
    then show ?thesis using twf unfolding typedefs_well_formed_def by blast
  qed
qed

(* ... and hence so does registering a whole parameter list. *)
lemma typedefs_well_formed_tyvar_entries:
  assumes twf: "typedefs_well_formed env tds"
      and tvs: "fset_of_list tyvars |\<subseteq>| TE_TypeVars env"
  shows "typedefs_well_formed env (tyvar_typedef_entries tyvars tds)"
  using assms
proof (induction tyvars arbitrary: tds)
  case Nil
  then show ?case by (simp add: tyvar_typedef_entries_def)
next
  case (Cons v vs)
  have v_in: "v |\<in>| TE_TypeVars env" using Cons.prems(2) by auto
  have step: "typedefs_well_formed env (fmupd v ([], CoreTy_Var v) tds)"
    using typedefs_well_formed_upd_tyvar[OF Cons.prems(1) v_in] .
  have unfold: "tyvar_typedef_entries (v # vs) tds
                  = tyvar_typedef_entries vs (fmupd v ([], CoreTy_Var v) tds)"
    unfolding tyvar_typedef_entries_def by simp
  show ?case
    unfolding unfold
    by (rule Cons.IH[OF step]) (use Cons.prems(2) in auto)
qed

(* An fmupd contributes at most one entry's worth to a union over the range. *)
lemma ffUnion_fmran_fmupd_member:
  assumes "x |\<in>| ffUnion (f |`| fmran (fmupd k v m))"
  shows "x |\<in>| f v \<or> x |\<in>| ffUnion (f |`| fmran m)"
proof -
  obtain e where e_ran: "e |\<in>| fmran (fmupd k v m)" and x_in: "x |\<in>| f e"
    using assms unfolding fmember_ffUnion_iff by auto
  obtain k' where lk: "fmlookup (fmupd k v m) k' = Some e"
    using e_ran by (auto simp: fmlookup_ran_iff)
  show ?thesis
  proof (cases "k' = k")
    case True
    then have "e = v" using lk by simp
    then show ?thesis using x_in by simp
  next
    case False
    then have "fmlookup m k' = Some e" using lk by simp
    then have "e |\<in>| fmran m" by (rule fmranI)
    then have "f e |\<in>| f |`| fmran m" by simp
    then have "x |\<in>| ffUnion (f |`| fmran m)"
      unfolding fmember_ffUnion_iff using x_in by blast
    then show ?thesis by simp
  qed
qed

(* Updating one typedef entry grows scope_bound_tyvars by at most that
   entry's parameter list. *)
lemma scope_bound_tyvars_typedefs_upd:
  "scope_bound_tyvars env
     (elabEnv \<lparr> EE_Typedefs := fmupd name (tvs, ty) (EE_Typedefs elabEnv) \<rparr>)
   |\<subseteq>| fset_of_list tvs |\<union>| scope_bound_tyvars env elabEnv"
proof
  fix x
  assume "x |\<in>| scope_bound_tyvars env
                  (elabEnv \<lparr> EE_Typedefs := fmupd name (tvs, ty) (EE_Typedefs elabEnv) \<rparr>)"
  then consider
      (fn) "x |\<in>| ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info))
                             |`| fmran (TE_Functions env))"
    | (dc) "x |\<in>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars)
                             |`| fmran (TE_DataCtors env))"
    | (td) "x |\<in>| ffUnion ((\<lambda>(tyVars, _). fset_of_list tyVars)
                             |`| fmran (fmupd name (tvs, ty) (EE_Typedefs elabEnv)))"
    unfolding scope_bound_tyvars_def by auto
  then show "x |\<in>| fset_of_list tvs |\<union>| scope_bound_tyvars env elabEnv"
  proof cases
    case fn then show ?thesis unfolding scope_bound_tyvars_def by auto
  next
    case dc then show ?thesis unfolding scope_bound_tyvars_def by auto
  next
    case td
    then have "x |\<in>| (\<lambda>(tyVars, _). fset_of_list tyVars) (tvs, ty)
               \<or> x |\<in>| ffUnion ((\<lambda>(tyVars, _). fset_of_list tyVars)
                                  |`| fmran (EE_Typedefs elabEnv))"
      by (rule ffUnion_fmran_fmupd_member)
    then show ?thesis unfolding scope_bound_tyvars_def by auto
  qed
qed

(* scope_bound_tyvars reads the env only through TE_Functions and
   TE_DataCtors. *)
lemma scope_bound_tyvars_cong_env:
  assumes "TE_Functions env' = TE_Functions env"
      and "TE_DataCtors env' = TE_DataCtors env"
  shows "scope_bound_tyvars env' elabEnv = scope_bound_tyvars env elabEnv"
  using assms unfolding scope_bound_tyvars_def by simp

(* elabenv_well_formed transfers to an env with grown type-variable fields:
   typedef targets stay well-kinded, and the data-constructor / return-type
   clauses read only unchanged fields. *)
lemma elabenv_well_formed_grow_tyvar_fields:
  assumes ee: "elabenv_well_formed env elabEnv"
  shows "elabenv_well_formed
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| eTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| eRT,
                  TE_AbstractTypes := TE_AbstractTypes env |\<union>| eAB \<rparr>) elabEnv"
proof -
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| eTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| eRT,
                     TE_AbstractTypes := TE_AbstractTypes env |\<union>| eAB \<rparr>"
  have td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
   and vd: "nullary_data_ctors_consistent env elabEnv"
   and void: "EE_CurrentFunctionVoid elabEnv \<longrightarrow> TE_ReturnType env = CoreTy_Record []"
    using ee unfolding elabenv_well_formed_def by blast+
  have td': "typedefs_well_formed ?env' (EE_Typedefs elabEnv)"
    by (rule typedefs_well_formed_mono[OF td]) auto
  have vd': "nullary_data_ctors_consistent ?env' elabEnv"
    using vd unfolding nullary_data_ctors_consistent_def by simp
  show ?thesis
    unfolding elabenv_well_formed_def using td' vd' void by simp
qed

(* typesubst_well_kinded is monotone in the env's type variables. *)
lemma typesubst_well_kinded_mono:
  assumes ts: "typesubst_well_kinded env s"
      and tv: "TE_TypeVars env |\<subseteq>| TE_TypeVars env'"
      and dt: "TE_Datatypes env' = TE_Datatypes env"
  shows "typesubst_well_kinded env' s"
  unfolding typesubst_well_kinded_def
proof (intro allI impI)
  fix n ty
  assume "fmlookup s n = Some ty"
  then have "is_well_kinded env ty"
    using ts unfolding typesubst_well_kinded_def by blast
  then show "is_well_kinded env' ty"
    by (rule is_well_kinded_mono)
       (use tv dt in \<open>auto simp: less_eq_fset.rep_eq\<close>)
qed


(* -------------------------------------------------------------------------- *)
(* The state env absorbs the module's substitution                            *)
(* -------------------------------------------------------------------------- *)

(* Subtracting a set makes the result disjoint from it. *)
lemma fminus_finter_disjoint:
  fixes A B :: "string fset"
  shows "(A |-| B) |\<inter>| B = {||}"
  by (rule fset_eqI) auto

(* The state env's type-variable fields avoid the substitution domain (they
   are built by subtracting it). *)
lemma module_context_env_subst_disjoint:
  "TE_TypeVars (module_context_env env0 m) |\<inter>| fmdom (CM_TypeSubst m) = {||}"
  "TE_RuntimeTypeVars (module_context_env env0 m) |\<inter>| fmdom (CM_TypeSubst m) = {||}"
  unfolding module_context_env_tyvar_fields by (rule fminus_finter_disjoint)+

(* A type well-kinded in an env whose type variables avoid a substitution's
   domain is untouched by that substitution. *)
lemma apply_subst_id_on_env_type:
  assumes disj: "TE_TypeVars env |\<inter>| fmdom s = {||}"
      and wk: "is_well_kinded env ty"
  shows "apply_subst s ty = ty"
proof -
  have tvs: "type_tyvars ty \<subseteq> fset (TE_TypeVars env)"
    by (rule is_well_kinded_type_tyvars_subset[OF wk])
  have disj': "\<And>x. x |\<in>| TE_TypeVars env \<Longrightarrow> x |\<notin>| fmdom s"
    using disj by (metis fempty_iff finter_iff)
  have "type_tyvars ty \<inter> fset (fmdom s) = {}"
    using tvs disj' by blast
  then show ?thesis by (rule apply_subst_disjoint_id)
qed

(* module_context_env stays at module scope: the scope fields are inherited
   from the context, and both operands' abstract types coincide with their
   type variables, so the combined fields coincide too. *)
lemma module_context_env_module_scope:
  assumes "tyenv_module_scope env0"
      and "tyenv_module_scope (CM_TyEnv m)"
  shows "tyenv_module_scope (module_context_env env0 m)"
  using assms
  unfolding tyenv_module_scope_def module_context_env_def apply_subst_to_tyenv_def
  by simp

(* ... and hence so does the invariant's state env. *)
lemma elab_decls_invariant_module_scope:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
  shows "tyenv_module_scope env"
proof -
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope0: "tyenv_module_scope env0"
    using ctx unfolding elab_context_ok_def by blast
  have scopem: "tyenv_module_scope (CM_TyEnv m)"
    using minv unfolding core_module_invariant_def by blast
  show ?thesis
    using module_context_env_module_scope[OF scope0 scopem] env_eq by simp
qed

(* Per-entry views of the capture conjunct: any one function's type parameters,
   or any one constructor's type variables, are below scope_bound_tyvars. *)
lemma scope_bound_tyvars_fun_entry:
  assumes lk: "fmlookup (TE_Functions env) funName = Some info"
  shows "fset_of_list (FI_TyArgs info) |\<subseteq>| scope_bound_tyvars env elabEnv"
proof
  fix x assume x_in: "x |\<in>| fset_of_list (FI_TyArgs info)"
  have "info |\<in>| fmran (TE_Functions env)" using lk by (rule fmranI)
  then have "fset_of_list (FI_TyArgs info)
               |\<in>| (\<lambda>info. fset_of_list (FI_TyArgs info)) |`| fmran (TE_Functions env)"
    by (rule fimageI)
  then have "x |\<in>| ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info))
                              |`| fmran (TE_Functions env))"
    unfolding fmember_ffUnion_iff using x_in by blast
  then show "x |\<in>| scope_bound_tyvars env elabEnv"
    unfolding scope_bound_tyvars_def by simp
qed

lemma scope_bound_tyvars_ctor_entry:
  assumes lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
  shows "fset_of_list tyVars |\<subseteq>| scope_bound_tyvars env elabEnv"
proof
  fix x assume x_in: "x |\<in>| fset_of_list tyVars"
  have "(dtName, tyVars, payload) |\<in>| fmran (TE_DataCtors env)"
    using lk by (rule fmranI)
  then have "(\<lambda>(_, tyVars, _). fset_of_list tyVars) (dtName, tyVars, payload)
               |\<in>| (\<lambda>(_, tyVars, _). fset_of_list tyVars) |`| fmran (TE_DataCtors env)"
    by (rule fimageI)
  then have "fset_of_list tyVars
               |\<in>| (\<lambda>(_, tyVars, _). fset_of_list tyVars) |`| fmran (TE_DataCtors env)"
    by simp
  then have "x |\<in>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars)
                              |`| fmran (TE_DataCtors env))"
    unfolding fmember_ffUnion_iff using x_in by blast
  then show "x |\<in>| scope_bound_tyvars env elabEnv"
    unfolding scope_bound_tyvars_def by simp
qed

(* The state env, used as both source and target, satisfies the module-level
   substitution engine's side conditions: its tyvar fields avoid the domain
   (so the tyvar-coverage clauses reduce to their None branches), and the
   capture clauses are per-entry views of the invariant's capture conjunct. *)
lemma elab_decls_invariant_module_env_subst_ok:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
  shows "module_env_subst_ok (CM_TypeSubst m) env env"
    and "module_env_subst_runtime_ok (CM_TypeSubst m) env env"
proof -
  have env_eq: "env = module_context_env env0 m"
   and cap: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
    using inv unfolding elab_decls_invariant_def by blast+
  have tv_disj: "TE_TypeVars env |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
  have rtv_disj: "TE_RuntimeTypeVars env |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using module_context_env_subst_disjoint(2)[of env0 m] env_eq by simp
  show "module_env_subst_ok (CM_TypeSubst m) env env"
    unfolding module_env_subst_ok_def
  proof (intro conjI allI impI)
    show "TE_Datatypes env = TE_Datatypes env" by simp
    show "TE_GhostDatatypes env = TE_GhostDatatypes env" by simp
  next
    fix n assume nT: "n |\<in>| TE_TypeVars env"
    then have "n |\<notin>| fmdom (CM_TypeSubst m)"
      using tv_disj by (metis fempty_iff finter_iff)
    then have "fmlookup (CM_TypeSubst m) n = None" by (rule fmdom_notD)
    then show "case fmlookup (CM_TypeSubst m) n of
                 Some ty' \<Rightarrow> is_well_kinded env ty'
               | None \<Rightarrow> n |\<in>| TE_TypeVars env"
      using nT by simp
  next
    fix funName info
    assume lk: "fmlookup (TE_Functions env) funName = Some info"
    show "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
      using empty_inter_subset[OF cap scope_bound_tyvars_fun_entry[OF lk]] .
  next
    fix ctorName dtName tyVars payload
    assume lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
    show "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
      using empty_inter_subset[OF cap scope_bound_tyvars_ctor_entry[OF lk]] .
  qed
  show "module_env_subst_runtime_ok (CM_TypeSubst m) env env"
    unfolding module_env_subst_runtime_ok_def
  proof (intro allI impI)
    fix n assume nR: "n |\<in>| TE_RuntimeTypeVars env"
    then have "n |\<notin>| fmdom (CM_TypeSubst m)"
      using rtv_disj by (metis fempty_iff finter_iff)
    then have "fmlookup (CM_TypeSubst m) n = None" by (rule fmdom_notD)
    then show "case fmlookup (CM_TypeSubst m) n of
                 Some ty' \<Rightarrow> is_runtime_type env ty'
               | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env"
      using nR by simp
  qed
qed

(* Pointwise idempotence lifts through the funinfo / datactor wrappers. *)
lemma apply_subst_to_funinfo_idem:
  assumes idem: "idempotent_subst s"
  shows "apply_subst_to_funinfo s (apply_subst_to_funinfo s info)
       = apply_subst_to_funinfo s info"
  unfolding apply_subst_to_funinfo_def
  by (simp add: idempotent_subst_twice[OF idem] case_prod_beta o_def)

lemma apply_subst_to_datactor_idem:
  assumes idem: "idempotent_subst s"
  shows "apply_subst_to_datactor s (apply_subst_to_datactor s e)
       = apply_subst_to_datactor s e"
  unfolding apply_subst_to_datactor_def
  by (simp add: idempotent_subst_twice[OF idem] case_prod_beta)

(* The heart of "born resolved": the state env already carries the
   substitution's image (its tables are fmmap'd, its scope fields are at
   module scope), so applying the module-level substitution engine to it is
   the identity. *)
lemma state_env_subst_absorb:
  assumes env_eq: "env = module_context_env env0 m"
      and scope0: "tyenv_module_scope env0"
      and idem: "idempotent_subst (CM_TypeSubst m)"
  shows "apply_subst_to_module_env (CM_TypeSubst m) env env = env"
proof -
  let ?s = "CM_TypeSubst m"
  have map_idem: "fmmap (apply_subst ?s) (fmmap (apply_subst ?s) X)
                = fmmap (apply_subst ?s) X" for X :: "(string, CoreType) fmap"
  proof (rule fmap_ext)
    fix k show "fmlookup (fmmap (apply_subst ?s) (fmmap (apply_subst ?s) X)) k
              = fmlookup (fmmap (apply_subst ?s) X) k"
      by (cases "fmlookup X k") (simp_all add: idempotent_subst_twice[OF idem])
  qed
  have fi_idem: "fmmap (apply_subst_to_funinfo ?s) (fmmap (apply_subst_to_funinfo ?s) F)
               = fmmap (apply_subst_to_funinfo ?s) F" for F :: "(string, FunInfo) fmap"
  proof (rule fmap_ext)
    fix k show "fmlookup (fmmap (apply_subst_to_funinfo ?s)
                            (fmmap (apply_subst_to_funinfo ?s) F)) k
              = fmlookup (fmmap (apply_subst_to_funinfo ?s) F) k"
      by (cases "fmlookup F k") (simp_all add: apply_subst_to_funinfo_idem[OF idem])
  qed
  have dc_idem: "fmmap (apply_subst_to_datactor ?s) (fmmap (apply_subst_to_datactor ?s) D)
               = fmmap (apply_subst_to_datactor ?s) D"
    for D :: "(string, string \<times> string list \<times> CoreType) fmap"
  proof (rule fmap_ext)
    fix k show "fmlookup (fmmap (apply_subst_to_datactor ?s)
                            (fmmap (apply_subst_to_datactor ?s) D)) k
              = fmlookup (fmmap (apply_subst_to_datactor ?s) D) k"
      by (cases "fmlookup D k") (simp_all add: apply_subst_to_datactor_idem[OF idem])
  qed
  have locals: "TE_LocalVars env = fmempty"
   and ret: "TE_ReturnType env = CoreTy_Record []"
   and goal_none: "TE_ProofGoal env = None"
    using scope0
    unfolding env_eq module_context_env_def apply_subst_to_tyenv_def
              tyenv_module_scope_def
    by simp_all
  have gv: "TE_GlobalVars env
          = fmmap (apply_subst ?s) (TE_GlobalVars env0 ++\<^sub>f TE_GlobalVars (CM_TyEnv m))"
   and fns: "TE_Functions env
          = fmmap (apply_subst_to_funinfo ?s)
                  (TE_Functions env0 ++\<^sub>f TE_Functions (CM_TyEnv m))"
   and dcs: "TE_DataCtors env
          = fmmap (apply_subst_to_datactor ?s)
                  (TE_DataCtors env0 ++\<^sub>f TE_DataCtors (CM_TyEnv m))"
    unfolding env_eq module_context_env_def apply_subst_to_tyenv_def by simp_all
  show ?thesis
    by (rule CoreTyEnv.equality)
       (simp_all add: apply_subst_to_module_env_def locals ret goal_none
                      gv fns dcs map_idem fi_idem dc_idem)
qed

(* Putting it together: a term typed in the state env at a type of the state
   env stays typed (at the same type) after the module's substitution is
   applied to it - which is exactly what normalize_module does to recorded
   initializers. *)
lemma elab_decls_invariant_subst_typing:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and typed: "core_term_type env ghost tm = Some ty"
      and wk: "is_well_kinded env ty"
  shows "core_term_type env ghost (apply_subst_to_term (CM_TypeSubst m) tm) = Some ty"
proof -
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and wf: "tyenv_well_formed env"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope0: "tyenv_module_scope env0"
    using ctx unfolding elab_context_ok_def by blast
  have idem: "idempotent_subst (CM_TypeSubst m)"
    using minv unfolding core_module_invariant_def by blast
  have tv_disj: "TE_TypeVars env |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
  have ok: "module_env_subst_ok (CM_TypeSubst m) env env"
   and rt_ok: "module_env_subst_runtime_ok (CM_TypeSubst m) env env"
    using elab_decls_invariant_module_env_subst_ok[OF inv] by blast+
  have "core_term_type (apply_subst_to_module_env (CM_TypeSubst m) env env) ghost
          (apply_subst_to_term (CM_TypeSubst m) tm)
        = Some (apply_subst (CM_TypeSubst m) ty)"
    using core_term_type_subst_module_env[OF typed wf ok] rt_ok by blast
  moreover have "apply_subst_to_module_env (CM_TypeSubst m) env env = env"
    using state_env_subst_absorb[OF env_eq scope0 idem] .
  moreover have "apply_subst (CM_TypeSubst m) ty = ty"
    using apply_subst_id_on_env_type[OF tv_disj wk] .
  ultimately show ?thesis by simp
qed


(* -------------------------------------------------------------------------- *)
(* Declared global types at module scope                                      *)
(* -------------------------------------------------------------------------- *)

(* At module scope the "globals-only" kinding env of tyenv_vars_well_kinded /
   tyenv_vars_runtime collapses to the env itself (TE_AbstractTypes =
   TE_TypeVars, and TE_RuntimeTypeVars is absorbed by the intersection). *)
lemma global_decl_well_kinded_module_scope:
  assumes wf: "tyenv_well_formed env"
      and scope: "tyenv_module_scope env"
      and lk: "fmlookup (TE_GlobalVars env) name = Some ty"
  shows "is_well_kinded env ty"
proof -
  have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
    using wf lk unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  moreover have "TE_AbstractTypes env = TE_TypeVars env"
    using scope unfolding tyenv_module_scope_def by blast
  ultimately show ?thesis by simp
qed

lemma global_decl_runtime_module_scope:
  assumes wf: "tyenv_well_formed env"
      and scope: "tyenv_module_scope env"
      and lk: "fmlookup (TE_GlobalVars env) name = Some ty"
      and ng: "name |\<notin>| TE_GhostGlobals env"
  shows "is_runtime_type env ty"
proof -
  have "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                               TE_RuntimeTypeVars := TE_AbstractTypes env
                                                      |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
    using wf lk ng unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
  moreover have "TE_AbstractTypes env = TE_TypeVars env"
    using scope unfolding tyenv_module_scope_def by blast
  moreover have "TE_TypeVars env |\<inter>| TE_RuntimeTypeVars env = TE_RuntimeTypeVars env"
    using wf unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def
    by (simp add: inf.absorb2)
  ultimately show ?thesis by simp
qed


(* -------------------------------------------------------------------------- *)
(* Adding a global declaration to an env                                      *)
(* -------------------------------------------------------------------------- *)

(* Adding a fresh global is a tyenv extension (old entries survive; the ghost
   marker changes only at the new name, which is outside the old domain). *)
lemma tyenv_extends_add_global:
  assumes fresh: "name |\<notin>| fmdom (TE_GlobalVars env)"
  shows "tyenv_extends env (tyenv_add_global name ty ghost env)"
  unfolding tyenv_extends_def tyenv_add_global_def
  using fresh by (auto split: if_splits)

(* Adding a well-kinded global (runtime if non-ghost) to a module-scope env
   preserves well-formedness. Only the TE_GlobalVars / TE_GhostGlobals
   clauses do real work; everything else transfers by congruence. *)
lemma tyenv_well_formed_add_global:
  assumes wf: "tyenv_well_formed env"
      and scope: "tyenv_module_scope env"
      and wk: "is_well_kinded env ty"
      and rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
  shows "tyenv_well_formed (tyenv_add_global name ty ghost env)"
proof -
  let ?env' = "tyenv_add_global name ty ghost env"
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope unfolding tyenv_module_scope_def by blast
  have rtv_tv: "TE_RuntimeTypeVars env |\<subseteq>| TE_TypeVars env"
    using wf unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by blast
  have tv_int: "TE_TypeVars env |\<inter>| TE_RuntimeTypeVars env = TE_RuntimeTypeVars env"
    using rtv_tv by (simp add: inf.absorb2)
  have wk_cong: "\<And>tvs ty'. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) ty'
                          = is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) ty'"
    by (rule is_well_kinded_cong_env) (simp_all add: tyenv_add_global_def)
  have wk_cong0: "\<And>ty'. is_well_kinded ?env' ty' = is_well_kinded env ty'"
    by (rule is_well_kinded_cong_env) (simp_all add: tyenv_add_global_def)
  have rt_cong: "\<And>tvs rtvs ty'.
        is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty'
      = is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty'"
    by (rule is_runtime_type_cong_env) (simp_all add: tyenv_add_global_def)
  have rt_cong0: "\<And>ty'. is_runtime_type ?env' ty' = is_runtime_type env ty'"
    by (rule is_runtime_type_cong_env) (simp_all add: tyenv_add_global_def)
  \<comment> \<open>Folded projections: rewriting with these (rather than unfolding the
      definition) keeps the cong rules' left-hand sides intact.\<close>
  have proj: "TE_LocalVars ?env' = TE_LocalVars env"
             "TE_GhostLocals ?env' = TE_GhostLocals env"
             "TE_TypeVars ?env' = TE_TypeVars env"
             "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env"
             "TE_AbstractTypes ?env' = TE_AbstractTypes env"
             "TE_ReturnType ?env' = TE_ReturnType env"
             "TE_FunctionGhost ?env' = TE_FunctionGhost env"
             "TE_Functions ?env' = TE_Functions env"
             "TE_Datatypes ?env' = TE_Datatypes env"
             "TE_DataCtors ?env' = TE_DataCtors env"
             "TE_DataCtorsByType ?env' = TE_DataCtorsByType env"
             "TE_GhostDatatypes ?env' = TE_GhostDatatypes env"
    by (simp_all add: tyenv_add_global_def)
  have vwk: "tyenv_vars_well_kinded env"
   and vrt: "tyenv_vars_runtime env"
   and gvs: "tyenv_ghost_vars_subset env"
   and rwk: "tyenv_return_type_well_kinded env"
   and rrt: "tyenv_return_type_runtime env"
   and cons: "tyenv_ctors_consistent env"
   and pwk: "tyenv_payloads_well_kinded env"
   and ctd: "tyenv_ctor_tyvars_distinct env"
   and cbt: "tyenv_ctors_by_type_consistent env"
   and fwk: "tyenv_fun_types_well_kinded env"
   and ftd: "tyenv_fun_tyvars_distinct env"
   and fgc: "tyenv_fun_ghost_constraint env"
   and npr: "tyenv_nonghost_payloads_runtime env"
   and gds: "tyenv_ghost_datatypes_subset env"
   and rts: "tyenv_runtime_tyvars_subset env"
   and ats: "tyenv_abstract_types_subset env"
   and dne: "tyenv_datatypes_nonempty env"
    using wf unfolding tyenv_well_formed_def by blast+
  have vwk': "tyenv_vars_well_kinded ?env'"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix n ty' assume "fmlookup (TE_LocalVars ?env') n = Some ty'"
    then have "fmlookup (TE_LocalVars env) n = Some ty'"
      by (simp add: tyenv_add_global_def)
    then have "is_well_kinded env ty'"
      using vwk unfolding tyenv_vars_well_kinded_def by blast
    then show "is_well_kinded ?env' ty'" by (simp add: wk_cong0)
  next
    fix n ty' assume lk: "fmlookup (TE_GlobalVars ?env') n = Some ty'"
    show "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' \<rparr>) ty'"
    proof (cases "n = name")
      case True
      then have ty'_eq: "ty' = ty" using lk by (simp add: tyenv_add_global_def)
      show ?thesis
        using wk ty'_eq abs_tv by (simp add: proj wk_cong wk_cong0)
    next
      case False
      then have "fmlookup (TE_GlobalVars env) n = Some ty'"
        using lk by (simp add: tyenv_add_global_def)
      then have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty'"
        using vwk unfolding tyenv_vars_well_kinded_def by blast
      then show ?thesis by (simp add: proj wk_cong wk_cong0 abs_tv)
    qed
  qed
  have vrt': "tyenv_vars_runtime ?env'"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix n ty'
    assume "fmlookup (TE_LocalVars ?env') n = Some ty' \<and> n |\<notin>| TE_GhostLocals ?env'"
    then have "fmlookup (TE_LocalVars env) n = Some ty'" "n |\<notin>| TE_GhostLocals env"
      by (simp_all add: tyenv_add_global_def)
    then have "is_runtime_type env ty'"
      using vrt unfolding tyenv_vars_runtime_def by blast
    then show "is_runtime_type ?env' ty'" by (simp add: rt_cong0)
  next
    fix n ty'
    assume h: "fmlookup (TE_GlobalVars ?env') n = Some ty'
               \<and> n |\<notin>| TE_GhostGlobals ?env'"
    then have lk: "fmlookup (fmupd name ty (TE_GlobalVars env)) n = Some ty'"
          and ng: "n |\<notin>| TE_GhostGlobals ?env'"
      by (simp_all add: tyenv_add_global_def)
    show "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env',
                                   TE_RuntimeTypeVars := TE_AbstractTypes ?env'
                                     |\<inter>| TE_RuntimeTypeVars ?env' \<rparr>) ty'"
    proof (cases "n = name")
      case True
      then have ty'_eq: "ty' = ty" using lk by simp
      have "ghost \<noteq> Ghost"
        using ng True by (auto simp: tyenv_add_global_def)
      then have gng: "ghost = NotGhost" by (cases ghost) auto
      have "is_runtime_type env ty" using rt gng by simp
      then show ?thesis
        using ty'_eq by (simp add: proj rt_cong rt_cong0 abs_tv tv_int)
    next
      case False
      then have lk_env: "fmlookup (TE_GlobalVars env) n = Some ty'" using lk by simp
      have ng_env: "n |\<notin>| TE_GhostGlobals env"
        using ng by (cases ghost) (auto simp: tyenv_add_global_def)
      have "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                                   TE_RuntimeTypeVars := TE_AbstractTypes env
                                     |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty'"
        using vrt lk_env ng_env unfolding tyenv_vars_runtime_def by blast
      then show ?thesis by (simp add: proj rt_cong rt_cong0 abs_tv tv_int)
    qed
  qed
  have gvs': "tyenv_ghost_vars_subset ?env'"
    using gvs unfolding tyenv_ghost_vars_subset_def
    by (cases ghost) (auto simp: tyenv_add_global_def)
  have rwk': "tyenv_return_type_well_kinded ?env'"
    using rwk unfolding tyenv_return_type_well_kinded_def
    by (simp add: proj wk_cong0)
  have rrt': "tyenv_return_type_runtime ?env'"
    using rrt unfolding tyenv_return_type_runtime_def
    by (simp add: proj rt_cong0)
  have cons': "tyenv_ctors_consistent ?env'"
    using cons unfolding tyenv_ctors_consistent_def
    by (simp add: tyenv_add_global_def)
  have pwk': "tyenv_payloads_well_kinded ?env'"
    using pwk unfolding tyenv_payloads_well_kinded_def
    by (simp add: proj wk_cong)
  have ctd': "tyenv_ctor_tyvars_distinct ?env'"
    using ctd unfolding tyenv_ctor_tyvars_distinct_def
    by (simp add: tyenv_add_global_def)
  have cbt': "tyenv_ctors_by_type_consistent ?env'"
    using cbt unfolding tyenv_ctors_by_type_consistent_def
    by (simp add: tyenv_add_global_def)
  have fwk': "tyenv_fun_types_well_kinded ?env'"
    using fwk unfolding tyenv_fun_types_well_kinded_def
    by (simp add: proj wk_cong)
  have ftd': "tyenv_fun_tyvars_distinct ?env'"
    using ftd unfolding tyenv_fun_tyvars_distinct_def
    by (simp add: tyenv_add_global_def)
  have fgc': "tyenv_fun_ghost_constraint ?env'"
    using fgc unfolding tyenv_fun_ghost_constraint_def Let_def
    by (simp add: proj rt_cong)
  have npr': "tyenv_nonghost_payloads_runtime ?env'"
    using npr unfolding tyenv_nonghost_payloads_runtime_def
    by (simp add: proj rt_cong)
  have gds': "tyenv_ghost_datatypes_subset ?env'"
    using gds unfolding tyenv_ghost_datatypes_subset_def
    by (simp add: tyenv_add_global_def)
  have rts': "tyenv_runtime_tyvars_subset ?env'"
    using rts unfolding tyenv_runtime_tyvars_subset_def
    by (simp add: tyenv_add_global_def)
  have ats': "tyenv_abstract_types_subset ?env'"
    using ats unfolding tyenv_abstract_types_subset_def
    by (simp add: tyenv_add_global_def)
  have dne': "tyenv_datatypes_nonempty ?env'"
    using dne unfolding tyenv_datatypes_nonempty_def
    by (simp add: tyenv_add_global_def)
  show ?thesis
    unfolding tyenv_well_formed_def
    using vwk' vrt' gvs' rwk' rrt' cons' pwk' ctd' cbt' fwk' ftd' fgc' npr'
          gds' rts' ats' dne'
    by blast
qed

(* Recorded globals / functions stay well-typed across a tyenv extension
   (with unchanged abstract types, for the function bodies' envs). *)
lemma module_globals_well_typed_tyenv_extends:
  assumes gwt: "module_globals_well_typed env G"
      and ext: "tyenv_extends env env'"
      and cons: "tyenv_ctors_consistent env"
  shows "module_globals_well_typed env' G"
  unfolding module_globals_well_typed_def
proof (intro allI impI)
  fix name tm assume lk: "fmlookup G name = Some tm"
  from gwt lk obtain declTy where
    d: "fmlookup (TE_GlobalVars env) name = Some declTy" and
    br: "if name |\<in>| TE_GhostGlobals env
         then core_term_type env Ghost tm = Some declTy
         else is_constant_term tm \<and> core_term_type env NotGhost tm = Some declTy"
    unfolding module_globals_well_typed_def by blast
  have d': "fmlookup (TE_GlobalVars env') name = Some declTy"
    using ext d unfolding tyenv_extends_def by blast
  have gg_eq: "(name |\<in>| TE_GhostGlobals env') = (name |\<in>| TE_GhostGlobals env)"
    using ext d unfolding tyenv_extends_def by (blast intro: fmdomI)
  show "\<exists>declTy. fmlookup (TE_GlobalVars env') name = Some declTy \<and>
          (if name |\<in>| TE_GhostGlobals env'
           then core_term_type env' Ghost tm = Some declTy
           else is_constant_term tm \<and> core_term_type env' NotGhost tm = Some declTy)"
  proof (cases "name |\<in>| TE_GhostGlobals env")
    case True
    then have "core_term_type env Ghost tm = Some declTy" using br by simp
    then have "core_term_type env' Ghost tm = Some declTy"
      using core_term_type_tyenv_extends[OF ext cons] by blast
    then show ?thesis using d' gg_eq True by auto
  next
    case False
    then have c: "is_constant_term tm"
          and "core_term_type env NotGhost tm = Some declTy"
      using br by simp_all
    then have "core_term_type env' NotGhost tm = Some declTy"
      using core_term_type_tyenv_extends[OF ext cons] by blast
    then show ?thesis using d' gg_eq False c by auto
  qed
qed

lemma module_functions_well_typed_tyenv_extends:
  assumes fwt: "module_functions_well_typed env F"
      and ext: "tyenv_extends env env'"
      and cons: "tyenv_ctors_consistent env"
      and abs_eq: "TE_AbstractTypes env' = TE_AbstractTypes env"
  shows "module_functions_well_typed env' F"
  unfolding module_functions_well_typed_def
proof (intro allI impI)
  fix name f assume lk: "fmlookup F name = Some f"
  from fwt lk obtain info where
    info: "fmlookup (TE_Functions env) name = Some info" and
    len: "length (CF_Args f) = length (FI_TmArgs info)" and
    dst: "distinct (CF_Args f)" and
    body: "case CF_Body f of
             None \<Rightarrow> True
           | Some body \<Rightarrow> core_statement_list_type
               (module_body_env_for env (CF_Args f) info) (FI_Ghost info) body \<noteq> None"
    unfolding module_functions_well_typed_def by blast
  have info': "fmlookup (TE_Functions env') name = Some info"
    using ext info unfolding tyenv_extends_def by blast
  have body_ext: "tyenv_extends (module_body_env_for env (CF_Args f) info)
                                (module_body_env_for env' (CF_Args f) info)"
    using ext[unfolded tyenv_extends_def] abs_eq
    unfolding tyenv_extends_def module_body_env_for_def by auto
  have cons_body: "tyenv_ctors_consistent (module_body_env_for env (CF_Args f) info)"
    using cons unfolding tyenv_ctors_consistent_def module_body_env_for_def by simp
  have body': "case CF_Body f of
                 None \<Rightarrow> True
               | Some body \<Rightarrow> core_statement_list_type
                   (module_body_env_for env' (CF_Args f) info) (FI_Ghost info) body \<noteq> None"
  proof (cases "CF_Body f")
    case None then show ?thesis by simp
  next
    case (Some body)
    then obtain out where t: "core_statement_list_type
        (module_body_env_for env (CF_Args f) info) (FI_Ghost info) body = Some out"
      using body
      by (cases "core_statement_list_type
                   (module_body_env_for env (CF_Args f) info) (FI_Ghost info) body")
         auto
    obtain out2 where "core_statement_list_type
        (module_body_env_for env' (CF_Args f) info) (FI_Ghost info) body = Some out2"
      using core_statement_list_type_tyenv_extends[OF t body_ext cons_body] by blast
    then show ?thesis using Some by simp
  qed
  show "\<exists>info. fmlookup (TE_Functions env') name = Some info \<and>
               length (CF_Args f) = length (FI_TmArgs info) \<and>
               distinct (CF_Args f) \<and>
               (case CF_Body f of
                  None \<Rightarrow> True
                | Some body \<Rightarrow> core_statement_list_type
                    (module_body_env_for env' (CF_Args f) info) (FI_Ghost info) body \<noteq> None)"
    using info' len dst body' by blast
qed

(* tyenv_add_global commutes with module_context_env, provided the new type
   is untouched by the module's substitution. *)
lemma module_context_env_add_global:
  assumes subst_id: "apply_subst (CM_TypeSubst m) ty = ty"
  shows "tyenv_add_global name ty ghost (module_context_env env0 m)
       = module_context_env env0 (m \<lparr> CM_TyEnv := tyenv_add_global name ty ghost (CM_TyEnv m) \<rparr>)"
  unfolding module_context_env_def apply_subst_to_tyenv_def tyenv_add_global_def
  by (cases ghost) (simp_all add: fmmap_fmupd subst_id)


(* -------------------------------------------------------------------------- *)
(* Correctness of the constant-initializer helpers                            *)
(* -------------------------------------------------------------------------- *)

(* The coerce-then-clear composite: if the elaborated rhs typechecks in the
   metavariable-extended env and coercion to a (metavariable-free) target type
   succeeds, the cleared coerced term typechecks to the target type in the
   original env. This is the same argument as the annotated VarDecl branch of
   elab_vardecl_pure_correct, factored out for reuse at declaration level. *)
lemma coerce_clear_typed_in_env:
  assumes typed: "core_term_type (extend_env_with_tyvars env ghost next_mv next_mv')
                    ghost coreTm = Some rhsTy"
      and coerce: "coerce_term_to_type env loc coreTm rhsTy tgtTy = Inr coreTm'"
      and wf: "tyenv_well_formed env"
      and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n next_mv"
      and wk: "is_well_kinded env tgtTy"
      and rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env tgtTy"
  shows "core_term_type env ghost (clear_metavars next_mv next_mv' coreTm') = Some tgtTy"
proof -
  let ?envD = "extend_env_with_tyvars env ghost next_mv next_mv'"
  let ?is_flex = "\<lambda>n. n |\<notin>| TE_TypeVars env"
  have tgtTy_below: "type_tyvars tgtTy \<subseteq> {n. tyvar_fresh_ok n next_mv}"
    using is_well_kinded_type_tyvars_subset[OF wk] bound by auto
  have wfD: "tyenv_well_formed ?envD"
    using wf tyenv_well_formed_extend_env_with_tyvars by blast
  have tgtTy_wkD: "is_well_kinded ?envD tgtTy"
  proof -
    have "type_tyvars tgtTy \<subseteq> fset (TE_TypeVars ?envD)"
      using is_well_kinded_type_tyvars_subset[OF wk]
      unfolding extend_env_with_tyvars_def by auto
    moreover have "TE_Datatypes ?envD = TE_Datatypes env"
      unfolding extend_env_with_tyvars_def by simp
    ultimately show ?thesis using is_well_kinded_transfer[OF wk] by blast
  qed
  have tgtTy_rtD: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envD tgtTy"
  proof
    assume dng: "ghost = NotGhost"
    then have "is_runtime_type env tgtTy" using rt by simp
    then show "is_runtime_type ?envD tgtTy"
      using is_runtime_type_extend_runtime_tyvars dng
      unfolding extend_env_with_tyvars_def by fastforce
  qed
  show ?thesis
  proof (cases "unify ?is_flex rhsTy tgtTy")
    case (Some subst)
    then have tm'_eq: "coreTm' = apply_subst_to_term subst coreTm"
      using coerce unfolding coerce_term_to_type_def by simp
    have rhsTy_wk: "is_well_kinded ?envD rhsTy"
      using core_term_type_well_kinded[OF typed wfD] .
    have rhsTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type ?envD rhsTy"
      using core_term_type_notghost_runtime typed wfD by auto
    have subst_wk: "\<forall>ty' \<in> fmran' subst. is_well_kinded ?envD ty'"
      using unify_preserves_well_kinded[OF Some rhsTy_wk tgtTy_wkD] .
    have subst_rt: "ghost = NotGhost \<longrightarrow> (\<forall>ty' \<in> fmran' subst. is_runtime_type ?envD ty')"
      using unify_preserves_runtime[OF Some] rhsTy_rt tgtTy_rtD by blast
    have dom_flex: "\<forall>n. n |\<in>| fmdom subst \<longrightarrow> ?is_flex n"
      using unify_unify_list_dom_flex(1)[OF Some] .
    have envD_locals: "TE_LocalVars ?envD = TE_LocalVars env"
      unfolding extend_env_with_tyvars_def by simp
    have envD_ret: "TE_ReturnType ?envD = TE_ReturnType env"
      unfolding extend_env_with_tyvars_def by simp
    from flex_subst_identity_on_env[OF dom_flex wf envD_locals envD_ret]
    have locals_unaffected: "\<And>vname ty'. fmlookup (TE_LocalVars ?envD) vname = Some ty'
                                          \<Longrightarrow> apply_subst subst ty' = ty'"
      and ret_unaffected: "apply_subst subst (TE_ReturnType ?envD) = TE_ReturnType ?envD"
      by blast+
    have envD_abs: "TE_AbstractTypes ?envD = TE_AbstractTypes env"
      unfolding extend_env_with_tyvars_def by simp
    have abs_no_subst: "\<And>n. n |\<in>| TE_AbstractTypes ?envD \<Longrightarrow> fmlookup subst n = None"
      using flex_subst_abs_no_subst[OF dom_flex[rule_format] wf envD_abs] .
    have subst_typed: "core_term_type ?envD ghost (apply_subst_to_term subst coreTm)
                         = Some (apply_subst subst rhsTy)"
      using apply_subst_to_term_preserves_typing
              [OF typed wfD subst_wk subst_rt locals_unaffected ret_unaffected
                  abs_no_subst] .
    have tgt_tvs: "type_tyvars tgtTy \<subseteq> fset (TE_TypeVars env)"
      using is_well_kinded_type_tyvars_subset[OF wk] .
    have dom_disj: "type_tyvars tgtTy \<inter> fset (fmdom subst) = {}"
      using dom_flex tgt_tvs by auto
    have "apply_subst subst rhsTy = apply_subst subst tgtTy"
      using unify_sound[OF Some] .
    also have "apply_subst subst tgtTy = tgtTy"
      using apply_subst_disjoint_id[OF dom_disj] .
    finally have st: "core_term_type ?envD ghost (apply_subst_to_term subst coreTm)
                        = Some tgtTy"
      using subst_typed by simp
    show ?thesis
      unfolding tm'_eq
      using clear_metavars_typed_in_env[OF st wf bound tgtTy_below] .
  next
    case None
    then have ints: "is_integer_type rhsTy \<and> is_integer_type tgtTy"
          and tm'_eq: "coreTm' = CoreTm_Cast tgtTy coreTm"
      using coerce unfolding coerce_term_to_type_def
      by (auto split: if_splits)
    have cast_typed: "core_term_type ?envD ghost (CoreTm_Cast tgtTy coreTm) = Some tgtTy"
      using typed ints tgtTy_wkD tgtTy_rtD by auto
    show ?thesis
      unfolding tm'_eq
      using clear_metavars_typed_in_env[OF cast_typed wf bound tgtTy_below] .
  qed
qed

(* A successful elab_const_rhs produces a term of the declared type (and a
   compile-time constant, in the non-ghost case). *)
lemma elab_const_rhs_correct:
  assumes elab: "elab_const_rhs env elabEnv ghost loc declTy rhs = Inr finalTm"
      and wf: "tyenv_well_formed env"
      and eewf: "elabenv_well_formed env elabEnv"
      and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
      and wk: "is_well_kinded env declTy"
      and rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env declTy"
  shows "core_term_type env ghost finalTm = Some declTy"
    and "ghost = NotGhost \<longrightarrow> is_constant_term finalTm"
proof -
  from elab obtain coreTm rhsTy next_mv coreTm' where
    etm: "elab_term env elabEnv ghost rhs 0 = Inr (coreTm, rhsTy, next_mv)" and
    co: "coerce_term_to_type env loc coreTm rhsTy declTy = Inr coreTm'" and
    fin: "finalTm = clear_metavars 0 next_mv coreTm'"
    unfolding elab_const_rhs_def
    by (auto simp: Let_def split: sum.splits prod.splits if_splits)
  show "ghost = NotGhost \<longrightarrow> is_constant_term finalTm"
    using elab unfolding elab_const_rhs_def
    by (auto simp: Let_def split: sum.splits prod.splits if_splits)
  have typed_ext: "core_term_type (extend_env_with_tyvars env ghost 0 next_mv)
                     ghost coreTm = Some rhsTy"
    using elab_term_correct(1)[OF etm wf eewf] bound by simp
  show "core_term_type env ghost finalTm = Some declTy"
    unfolding fin
    using coerce_clear_typed_in_env[OF typed_ext co wf bound wk rt] .
qed

(* Likewise for the inferred-type form; here the result type is additionally
   well-kinded (runtime, if non-ghost) courtesy of the no-metavariable check. *)
lemma elab_const_rhs_infer_correct:
  assumes elab: "elab_const_rhs_infer env elabEnv ghost loc rhs = Inr (finalTm, resTy)"
      and wf: "tyenv_well_formed env"
      and eewf: "elabenv_well_formed env elabEnv"
      and bound: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
  shows "core_term_type env ghost finalTm = Some resTy"
    and "is_well_kinded env resTy"
    and "ghost = NotGhost \<longrightarrow> is_runtime_type env resTy"
    and "ghost = NotGhost \<longrightarrow> is_constant_term finalTm"
proof -
  from elab obtain coreTm next_mv where
    etm: "elab_term env elabEnv ghost rhs 0 = Inr (coreTm, resTy, next_mv)" and
    no_meta: "list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list resTy)" and
    fin: "finalTm = clear_metavars 0 next_mv coreTm"
    unfolding elab_const_rhs_infer_def
    by (auto simp: Let_def split: sum.splits prod.splits if_splits)
  show "ghost = NotGhost \<longrightarrow> is_constant_term finalTm"
    using elab unfolding elab_const_rhs_infer_def
    by (auto simp: Let_def split: sum.splits prod.splits if_splits)
  have wkrt: "is_well_kinded env resTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env resTy)"
    using elab_term_inferred_type_well_kinded_runtime[OF etm wf eewf bound no_meta] .
  then show "is_well_kinded env resTy"
        and "ghost = NotGhost \<longrightarrow> is_runtime_type env resTy" by blast+
  have typed_ext: "core_term_type (extend_env_with_tyvars env ghost 0 next_mv)
                     ghost coreTm = Some resTy"
    using elab_term_correct(1)[OF etm wf eewf] bound by simp
  have wk_res: "is_well_kinded env resTy" using wkrt by blast
  have below: "type_tyvars resTy \<subseteq> {n. tyvar_fresh_ok n 0}"
    using is_well_kinded_type_tyvars_subset[OF wk_res] bound by auto
  show "core_term_type env ghost finalTm = Some resTy"
    unfolding fin
    using clear_metavars_typed_in_env[OF typed_ext wf bound below] .
qed


(* ========================================================================== *)
(* Each declaration preserves the invariant                                   *)
(* ========================================================================== *)

(* The main induction: elaborating one declaration (with metavariable-fresh
   binders) preserves the invariant. *)
(* ---- Constants ---- *)

(* Step 1: declaring a fresh global (in both the state env and the module's
   CM_TyEnv) preserves the invariant. *)
lemma elab_decls_invariant_add_global:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and notin: "\<not> term_name_in_scope env name"
      and wk: "is_well_kinded env ty"
      and rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
  shows "elab_decls_invariant env0 ownAbstract
           (tyenv_add_global name ty ghost env) elabEnv
           (m \<lparr> CM_TyEnv := tyenv_add_global name ty ghost (CM_TyEnv m) \<rparr>)"
proof -
  let ?env' = "tyenv_add_global name ty ghost env"
  let ?m' = "m \<lparr> CM_TyEnv := tyenv_add_global name ty ghost (CM_TyEnv m) \<rparr>"
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and own_disj: "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and swk: "typesubst_well_kinded env (CM_TypeSubst m)"
   and dom_own: "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract"
   and dom_td: "fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs elabEnv)"
   and cap_env: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
   and mv_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and mv_fn: "\<forall>fname info. fmlookup (TE_Functions env) fname = Some info \<longrightarrow>
                 list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
   and gwt: "module_globals_well_typed env (CM_GlobalVars (normalize_module m))"
   and fwt: "module_functions_well_typed env (CM_Functions (normalize_module m))"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  have tv_disj: "TE_TypeVars env |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
  have subst_id: "apply_subst (CM_TypeSubst m) ty = ty"
    using apply_subst_id_on_env_type[OF tv_disj wk] .
  have fresh_g: "name |\<notin>| fmdom (TE_GlobalVars env)"
    using notin unfolding term_name_in_scope_def by blast
  have ext: "tyenv_extends env ?env'"
    using tyenv_extends_add_global[OF fresh_g] .
  have cons: "tyenv_ctors_consistent env"
    using wf unfolding tyenv_well_formed_def by blast
  \<comment> \<open>The individual conjuncts.\<close>
  have env_eq': "?env' = module_context_env env0 ?m'"
    using module_context_env_add_global[OF subst_id, of name ghost env0] env_eq by simp
  have minv': "core_module_invariant ?m'"
    using minv
    unfolding core_module_invariant_def capture_avoiding_def
              module_ghost_subsets_ok_def tyenv_module_scope_def
    by (cases ghost) (auto simp: tyenv_add_global_def)
  have own_disj': "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}"
    using own_disj by (simp add: tyenv_add_global_def)
  have wf': "tyenv_well_formed ?env'"
    using tyenv_well_formed_add_global[OF wf scope_env wk rt] .
  have cong_ee: "elabenv_well_formed ?env' elabEnv = elabenv_well_formed env elabEnv"
    by (rule elabenv_well_formed_cong_env) (simp_all add: tyenv_add_global_def)
  have eewf': "elabenv_well_formed ?env' elabEnv"
    using eewf cong_ee by simp
  have swk_env': "typesubst_well_kinded ?env' (CM_TypeSubst m)"
    by (rule typesubst_well_kinded_mono[OF swk]) (simp_all add: tyenv_add_global_def)
  have sbt_cong: "scope_bound_tyvars ?env' elabEnv = scope_bound_tyvars env elabEnv"
    by (rule scope_bound_tyvars_cong_env) (simp_all add: tyenv_add_global_def)
  have mv_tv': "\<forall>n. n |\<in>| TE_TypeVars ?env' \<longrightarrow> tyvar_fresh_ok n 0"
    using mv_tv by (simp add: tyenv_add_global_def)
  have mv_fn': "\<forall>fname info. fmlookup (TE_Functions ?env') fname = Some info \<longrightarrow>
                  list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
    using mv_fn by (simp add: tyenv_add_global_def)
  have glb_same: "CM_GlobalVars (normalize_module ?m') = CM_GlobalVars (normalize_module m)"
    by (simp add: normalize_module_def)
  have fns_same: "CM_Functions (normalize_module ?m') = CM_Functions (normalize_module m)"
    by (simp add: normalize_module_def)
  have gwt': "module_globals_well_typed ?env' (CM_GlobalVars (normalize_module ?m'))"
    unfolding glb_same
    by (rule module_globals_well_typed_tyenv_extends[OF gwt ext cons])
  have fwt': "module_functions_well_typed ?env' (CM_Functions (normalize_module ?m'))"
    unfolding fns_same
    by (rule module_functions_well_typed_tyenv_extends[OF fwt ext cons])
       (simp add: tyenv_add_global_def)
  show ?thesis
    unfolding elab_decls_invariant_def
  proof (intro conjI)
    show "elab_context_ok env0 ownAbstract" using ctx .
    show "?env' = module_context_env env0 ?m'" using env_eq' .
    show "core_module_invariant ?m'" using minv' .
    show "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}" using own_disj' .
    show "tyenv_well_formed ?env'" using wf' .
    show "elabenv_well_formed ?env' elabEnv" using eewf' .
    show "typesubst_well_kinded ?env' (CM_TypeSubst ?m')" using swk_env' by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| ownAbstract" using dom_own by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| fmdom (EE_Typedefs elabEnv)" using dom_td by simp
    show "subst_names (CM_TypeSubst ?m') |\<inter>| scope_bound_tyvars ?env' elabEnv = {||}"
      using cap_env sbt_cong by simp
    show "\<forall>n. n |\<in>| TE_TypeVars ?env' \<longrightarrow> tyvar_fresh_ok n 0" using mv_tv' .
    show "\<forall>fname info. fmlookup (TE_Functions ?env') fname = Some info \<longrightarrow>
            list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)" using mv_fn' .
    show "module_globals_well_typed ?env' (CM_GlobalVars (normalize_module ?m'))"
      using gwt' .
    show "module_functions_well_typed ?env' (CM_Functions (normalize_module ?m'))"
      using fwt' .
  qed
qed

(* Step 2: recording an initializer for an already-declared global (only
   CM_GlobalVars changes). The recorded term is "born resolved": applying the
   module's substitution to it (as normalize_module does) leaves it typed at
   the declared type, by elab_decls_invariant_subst_typing. *)
lemma elab_decls_invariant_define_global:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and decl: "fmlookup (TE_GlobalVars env) name = Some declTy"
      and gm: "(name |\<in>| TE_GhostGlobals env) = (ghost = Ghost)"
      and typed: "core_term_type env ghost finalTm = Some declTy"
      and const: "ghost = NotGhost \<longrightarrow> is_constant_term finalTm"
  shows "elab_decls_invariant env0 ownAbstract env elabEnv
           (m \<lparr> CM_GlobalVars := fmupd name finalTm (CM_GlobalVars m) \<rparr>)"
proof -
  let ?m' = "m \<lparr> CM_GlobalVars := fmupd name finalTm (CM_GlobalVars m) \<rparr>"
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and own_disj: "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and swk: "typesubst_well_kinded env (CM_TypeSubst m)"
   and dom_own: "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract"
   and dom_td: "fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs elabEnv)"
   and cap_env: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
   and mv_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and mv_fn: "\<forall>fname info. fmlookup (TE_Functions env) fname = Some info \<longrightarrow>
                 list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
   and gwt: "module_globals_well_typed env (CM_GlobalVars (normalize_module m))"
   and fwt: "module_functions_well_typed env (CM_Functions (normalize_module m))"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  have mce_same: "module_context_env env0 ?m' = module_context_env env0 m"
    unfolding module_context_env_def by simp
  have minv': "core_module_invariant ?m'"
    using minv
    unfolding core_module_invariant_def capture_avoiding_def
              module_ghost_subsets_ok_def tyenv_module_scope_def
    by simp
  \<comment> \<open>The new normalized globals map: the substituted initializer joins the
      old normalized entries.\<close>
  have norm_glb: "CM_GlobalVars (normalize_module ?m')
                = fmupd name (apply_subst_to_term (CM_TypeSubst m) finalTm)
                        (CM_GlobalVars (normalize_module m))"
    by (simp add: normalize_module_def fmmap_fmupd)
  have wk_decl: "is_well_kinded env declTy"
    using global_decl_well_kinded_module_scope[OF wf scope_env decl] .
  have typed_subst: "core_term_type env ghost
                       (apply_subst_to_term (CM_TypeSubst m) finalTm) = Some declTy"
    using elab_decls_invariant_subst_typing[OF inv typed wk_decl] .
  have gwt': "module_globals_well_typed env (CM_GlobalVars (normalize_module ?m'))"
    unfolding norm_glb module_globals_well_typed_def
  proof (intro allI impI)
    fix n tm
    assume lk: "fmlookup (fmupd name (apply_subst_to_term (CM_TypeSubst m) finalTm)
                                (CM_GlobalVars (normalize_module m))) n = Some tm"
    show "\<exists>dTy. fmlookup (TE_GlobalVars env) n = Some dTy \<and>
            (if n |\<in>| TE_GhostGlobals env
             then core_term_type env Ghost tm = Some dTy
             else is_constant_term tm \<and> core_term_type env NotGhost tm = Some dTy)"
    proof (cases "n = name")
      case True
      then have tm_eq: "tm = apply_subst_to_term (CM_TypeSubst m) finalTm"
        using lk by simp
      show ?thesis
      proof (cases ghost)
        case Ghost
        then have "name |\<in>| TE_GhostGlobals env" using gm by simp
        then show ?thesis using decl typed_subst True tm_eq Ghost by auto
      next
        case NotGhost
        then have nn: "name |\<notin>| TE_GhostGlobals env" using gm by simp
        have "is_constant_term tm" using const NotGhost tm_eq by simp
        then show ?thesis using decl typed_subst True tm_eq NotGhost nn by auto
      qed
    next
      case False
      then have "fmlookup (CM_GlobalVars (normalize_module m)) n = Some tm"
        using lk by simp
      then show ?thesis using gwt unfolding module_globals_well_typed_def by blast
    qed
  qed
  have fns_same: "CM_Functions (normalize_module ?m') = CM_Functions (normalize_module m)"
    by (simp add: normalize_module_def)
  show ?thesis
    unfolding elab_decls_invariant_def
  proof (intro conjI)
    show "elab_context_ok env0 ownAbstract" using ctx .
    show "env = module_context_env env0 ?m'" using env_eq mce_same by simp
    show "core_module_invariant ?m'" using minv' .
    show "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}" using own_disj by simp
    show "tyenv_well_formed env" using wf .
    show "elabenv_well_formed env elabEnv" using eewf .
    show "typesubst_well_kinded env (CM_TypeSubst ?m')" using swk by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| ownAbstract" using dom_own by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| fmdom (EE_Typedefs elabEnv)" using dom_td by simp
    show "subst_names (CM_TypeSubst ?m') |\<inter>| scope_bound_tyvars env elabEnv = {||}"
      using cap_env by simp
    show "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0" using mv_tv .
    show "\<forall>fname info. fmlookup (TE_Functions env) fname = Some info \<longrightarrow>
            list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)" using mv_fn .
    show "module_globals_well_typed env (CM_GlobalVars (normalize_module ?m'))"
      using gwt' .
    show "module_functions_well_typed env (CM_Functions (normalize_module ?m'))"
      using fwt unfolding fns_same .
  qed
qed

(* Steps 1+2 composed: declaring and defining a fresh global at once. *)
lemma elab_decls_invariant_declare_define_global:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and notin: "\<not> term_name_in_scope env name"
      and wk: "is_well_kinded env ty"
      and rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
      and typed: "core_term_type env ghost finalTm = Some ty"
      and const: "ghost = NotGhost \<longrightarrow> is_constant_term finalTm"
  shows "elab_decls_invariant env0 ownAbstract
           (tyenv_add_global name ty ghost env) elabEnv
           (m \<lparr> CM_TyEnv := tyenv_add_global name ty ghost (CM_TyEnv m),
                CM_GlobalVars := fmupd name finalTm (CM_GlobalVars m) \<rparr>)"
proof -
  let ?env1 = "tyenv_add_global name ty ghost env"
  let ?m1 = "m \<lparr> CM_TyEnv := tyenv_add_global name ty ghost (CM_TyEnv m) \<rparr>"
  have wf: "tyenv_well_formed env"
    using inv unfolding elab_decls_invariant_def by blast
  have inv1: "elab_decls_invariant env0 ownAbstract ?env1 elabEnv ?m1"
    by (rule elab_decls_invariant_add_global[OF inv notin wk rt])
  have fresh_g: "name |\<notin>| fmdom (TE_GlobalVars env)"
    using notin unfolding term_name_in_scope_def by blast
  have lk1: "fmlookup (TE_GlobalVars ?env1) name = Some ty"
    by (simp add: tyenv_add_global_def)
  have ng_env: "name |\<notin>| TE_GhostGlobals env"
    using wf fresh_g
    unfolding tyenv_well_formed_def tyenv_ghost_vars_subset_def by blast
  have gm1: "(name |\<in>| TE_GhostGlobals ?env1) = (ghost = Ghost)"
    using ng_env by (cases ghost) (auto simp: tyenv_add_global_def)
  have ext: "tyenv_extends env ?env1"
    using tyenv_extends_add_global[OF fresh_g] .
  have cons: "tyenv_ctors_consistent env"
    using wf unfolding tyenv_well_formed_def by blast
  have typed1: "core_term_type ?env1 ghost finalTm = Some ty"
    using core_term_type_tyenv_extends[OF ext cons typed] .
  have "elab_decls_invariant env0 ownAbstract ?env1 elabEnv
          (?m1 \<lparr> CM_GlobalVars := fmupd name finalTm (CM_GlobalVars ?m1) \<rparr>)"
    by (rule elab_decls_invariant_define_global[OF inv1 lk1 gm1 typed1 const])
  then show ?thesis by simp
qed

(* The elimination rule for elab_const_decl success: one case per branch of
   the elaborator (declaration only; definition of a previously-declared
   constant; declare-and-define with inferred type; declare-and-define with
   annotated type). Each case records the guards that must have passed and
   states the defining equations of the result. The proof peels the
   scrutinees one at a time (auto with split rules loops on this
   definition). *)
lemma elab_const_decl_Inr_elim:
  assumes ok: "elab_const_decl env elabEnv m dc = Inr (env', elabEnv', m')"
  obtains (DeclOnly) ty coreTy where
    "DC_Value dc = None"
    "\<not> term_name_in_scope env (DC_Name dc)"
    "DC_Type dc = Some ty"
    "elab_type env elabEnv (DC_Ghost dc) ty = Inr coreTy"
    "env' = tyenv_add_global (DC_Name dc) coreTy (DC_Ghost dc) env"
    "elabEnv' = elabEnv"
    "m' = m \<lparr> CM_TyEnv := tyenv_add_global (DC_Name dc) coreTy (DC_Ghost dc)
                            (CM_TyEnv m) \<rparr>"
  | (DefineDeclared) rhs declTy finalTm where
    "DC_Value dc = Some rhs"
    "fmlookup (TE_GlobalVars env) (DC_Name dc) = Some declTy"
    "DC_Name dc |\<notin>| fmdom (CM_GlobalVars m)"
    "(DC_Name dc |\<in>| TE_GhostGlobals env) = (DC_Ghost dc = Ghost)"
    "elab_const_rhs env elabEnv (DC_Ghost dc) (DC_Location dc) declTy rhs
       = Inr finalTm"
    "env' = env"
    "elabEnv' = elabEnv"
    "m' = m \<lparr> CM_GlobalVars := fmupd (DC_Name dc) finalTm (CM_GlobalVars m) \<rparr>"
  | (InferDefine) rhs finalTm declTy where
    "DC_Value dc = Some rhs"
    "fmlookup (TE_GlobalVars env) (DC_Name dc) = None"
    "DC_Type dc = None"
    "\<not> term_name_in_scope env (DC_Name dc)"
    "elab_const_rhs_infer env elabEnv (DC_Ghost dc) (DC_Location dc) rhs
       = Inr (finalTm, declTy)"
    "env' = tyenv_add_global (DC_Name dc) declTy (DC_Ghost dc) env"
    "elabEnv' = elabEnv"
    "m' = m \<lparr> CM_TyEnv := tyenv_add_global (DC_Name dc) declTy (DC_Ghost dc)
                            (CM_TyEnv m),
              CM_GlobalVars := fmupd (DC_Name dc) finalTm (CM_GlobalVars m) \<rparr>"
  | (AnnotDefine) rhs ty declTy finalTm where
    "DC_Value dc = Some rhs"
    "fmlookup (TE_GlobalVars env) (DC_Name dc) = None"
    "DC_Type dc = Some ty"
    "\<not> term_name_in_scope env (DC_Name dc)"
    "elab_type env elabEnv (DC_Ghost dc) ty = Inr declTy"
    "elab_const_rhs env elabEnv (DC_Ghost dc) (DC_Location dc) declTy rhs
       = Inr finalTm"
    "env' = tyenv_add_global (DC_Name dc) declTy (DC_Ghost dc) env"
    "elabEnv' = elabEnv"
    "m' = m \<lparr> CM_TyEnv := tyenv_add_global (DC_Name dc) declTy (DC_Ghost dc)
                            (CM_TyEnv m),
              CM_GlobalVars := fmupd (DC_Name dc) finalTm (CM_GlobalVars m) \<rparr>"
proof (cases "DC_Value dc")
  case None
  \<comment> \<open>Collapse the outer case with the known discriminator first (no
      splitting), so that the branch extraction below only splits within
      this one branch.\<close>
  from ok have elabA:
    "(if term_name_in_scope env (DC_Name dc)
      then Inl [TyErr_DuplicateName (DC_Location dc) (DC_Name dc)]
      else case DC_Type dc of
             None \<Rightarrow> Inl [TyErr_ConstDeclNeedsType (DC_Location dc) (DC_Name dc)]
           | Some ty \<Rightarrow>
               (case elab_type env elabEnv (DC_Ghost dc) ty of
                  Inl errs \<Rightarrow> Inl errs
                | Inr coreTy \<Rightarrow>
                    Inr (tyenv_add_global (DC_Name dc) coreTy (DC_Ghost dc) env,
                         elabEnv,
                         m \<lparr> CM_TyEnv := tyenv_add_global (DC_Name dc) coreTy
                                           (DC_Ghost dc) (CM_TyEnv m) \<rparr>)))
     = Inr (env', elabEnv', m')"
    unfolding elab_const_decl_def Let_def by (simp add: None)
  have notin: "\<not> term_name_in_scope env (DC_Name dc)"
    using elabA by (cases "term_name_in_scope env (DC_Name dc)") simp_all
  from elabA notin obtain ty where dty: "DC_Type dc = Some ty"
    by (cases "DC_Type dc") auto
  from elabA notin dty obtain coreTy where
    ety: "elab_type env elabEnv (DC_Ghost dc) ty = Inr coreTy" and
    env'_eq: "env' = tyenv_add_global (DC_Name dc) coreTy (DC_Ghost dc) env" and
    ee'_eq: "elabEnv' = elabEnv" and
    m'_eq: "m' = m \<lparr> CM_TyEnv := tyenv_add_global (DC_Name dc) coreTy
                                   (DC_Ghost dc) (CM_TyEnv m) \<rparr>"
    by (cases "elab_type env elabEnv (DC_Ghost dc) ty") auto
  show thesis
    by (rule DeclOnly[OF None notin dty ety env'_eq ee'_eq m'_eq])
next
  case (Some rhs)
  show thesis
  proof (cases "fmlookup (TE_GlobalVars env) (DC_Name dc)")
    case lkSome: (Some declTy)
    from ok have elabB:
      "(if DC_Name dc |\<in>| fmdom (CM_GlobalVars m)
        then Inl [TyErr_AlreadyDefined (DC_Location dc) (DC_Name dc)]
        else if (DC_Name dc |\<in>| TE_GhostGlobals env) \<noteq> (DC_Ghost dc = Ghost)
        then Inl [TyErr_GhostMismatch (DC_Location dc) (DC_Name dc)]
        else
          (case (case DC_Type dc of
                   None \<Rightarrow> Inr declTy
                 | Some ty \<Rightarrow>
                     (case elab_type env elabEnv (DC_Ghost dc) ty of
                        Inl errs \<Rightarrow> Inl errs
                      | Inr coreTy \<Rightarrow>
                          if coreTy \<noteq> declTy
                          then Inl [TyErr_TypeMismatch (DC_Location dc) declTy coreTy]
                          else Inr declTy)) of
             Inl errs \<Rightarrow> Inl errs
           | Inr _ \<Rightarrow>
               (case elab_const_rhs env elabEnv (DC_Ghost dc) (DC_Location dc)
                       declTy rhs of
                  Inl errs \<Rightarrow> Inl errs
                | Inr finalTm \<Rightarrow>
                    Inr (env, elabEnv,
                         m \<lparr> CM_GlobalVars := fmupd (DC_Name dc) finalTm
                                                (CM_GlobalVars m) \<rparr>))))
       = Inr (env', elabEnv', m')"
      unfolding elab_const_decl_def Let_def
      by (simp add: Some lkSome)
    have nd: "DC_Name dc |\<notin>| fmdom (CM_GlobalVars m)"
      using elabB by (cases "DC_Name dc |\<in>| fmdom (CM_GlobalVars m)") simp_all
    have gm: "(DC_Name dc |\<in>| TE_GhostGlobals env) = (DC_Ghost dc = Ghost)"
      using elabB nd
      by (cases "(DC_Name dc |\<in>| TE_GhostGlobals env) \<noteq> (DC_Ghost dc = Ghost)")
         simp_all
    \<comment> \<open>Dispose of the annotation check, leaving only the rhs elaboration.\<close>
    have elabB':
      "(case elab_const_rhs env elabEnv (DC_Ghost dc) (DC_Location dc) declTy rhs of
          Inl errs \<Rightarrow> Inl errs
        | Inr finalTm \<Rightarrow>
            Inr (env, elabEnv,
                 m \<lparr> CM_GlobalVars := fmupd (DC_Name dc) finalTm (CM_GlobalVars m) \<rparr>))
       = Inr (env', elabEnv', m')"
    proof (cases "DC_Type dc")
      case None
      with elabB nd gm show ?thesis by simp
    next
      case (Some ty)
      show ?thesis
      proof (cases "elab_type env elabEnv (DC_Ghost dc) ty")
        case (Inl errs)
        with elabB nd gm Some show ?thesis by simp
      next
        case (Inr coreTy)
        with elabB nd gm Some show ?thesis
          by (cases "coreTy = declTy") simp_all
      qed
    qed
    from elabB' obtain finalTm where
      rhs_ok: "elab_const_rhs env elabEnv (DC_Ghost dc) (DC_Location dc) declTy rhs
                 = Inr finalTm" and
      env'_eq: "env' = env" and
      ee'_eq: "elabEnv' = elabEnv" and
      m'_eq: "m' = m \<lparr> CM_GlobalVars := fmupd (DC_Name dc) finalTm (CM_GlobalVars m) \<rparr>"
      by (cases "elab_const_rhs env elabEnv (DC_Ghost dc) (DC_Location dc) declTy rhs")
         auto
    show thesis
      by (rule DefineDeclared[OF Some lkSome nd gm rhs_ok env'_eq ee'_eq m'_eq])
  next
    case lkNone: None
    show thesis
    proof (cases "DC_Type dc")
      case tyNone: None
      from ok tyNone have elabC:
        "(if term_name_in_scope env (DC_Name dc)
          then Inl [TyErr_DuplicateName (DC_Location dc) (DC_Name dc)]
          else case elab_const_rhs_infer env elabEnv (DC_Ghost dc)
                      (DC_Location dc) rhs of
                 Inl errs \<Rightarrow> Inl errs
               | Inr (finalTm, declTy) \<Rightarrow>
                   Inr (tyenv_add_global (DC_Name dc) declTy (DC_Ghost dc) env,
                        elabEnv,
                        m \<lparr> CM_TyEnv := tyenv_add_global (DC_Name dc) declTy
                                          (DC_Ghost dc) (CM_TyEnv m),
                            CM_GlobalVars := fmupd (DC_Name dc) finalTm
                                               (CM_GlobalVars m) \<rparr>))
         = Inr (env', elabEnv', m')"
        unfolding elab_const_decl_def Let_def
        using lkNone Some by auto
      have notin: "\<not> term_name_in_scope env (DC_Name dc)"
        using elabC by (cases "term_name_in_scope env (DC_Name dc)") simp_all
      from elabC notin obtain finalTm declTy where
        infer_ok: "elab_const_rhs_infer env elabEnv (DC_Ghost dc) (DC_Location dc) rhs
                     = Inr (finalTm, declTy)" and
        env'_eq: "env' = tyenv_add_global (DC_Name dc) declTy (DC_Ghost dc) env" and
        ee'_eq: "elabEnv' = elabEnv" and
        m'_eq: "m' = m \<lparr> CM_TyEnv := tyenv_add_global (DC_Name dc) declTy
                                       (DC_Ghost dc) (CM_TyEnv m),
                         CM_GlobalVars := fmupd (DC_Name dc) finalTm (CM_GlobalVars m) \<rparr>"
        by (cases "elab_const_rhs_infer env elabEnv (DC_Ghost dc) (DC_Location dc) rhs")
           (auto split: prod.splits)
      show thesis
        by (rule InferDefine[OF Some lkNone tyNone notin infer_ok
                                env'_eq ee'_eq m'_eq])
    next
      case tySome: (Some ty)
      from ok tySome have elabD:
        "(if term_name_in_scope env (DC_Name dc)
          then Inl [TyErr_DuplicateName (DC_Location dc) (DC_Name dc)]
          else case elab_type env elabEnv (DC_Ghost dc) ty of
                 Inl errs \<Rightarrow> Inl errs
               | Inr declTy \<Rightarrow>
                   (case elab_const_rhs env elabEnv (DC_Ghost dc) (DC_Location dc)
                           declTy rhs of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr finalTm \<Rightarrow>
                        Inr (tyenv_add_global (DC_Name dc) declTy (DC_Ghost dc) env,
                             elabEnv,
                             m \<lparr> CM_TyEnv := tyenv_add_global (DC_Name dc) declTy
                                               (DC_Ghost dc) (CM_TyEnv m),
                                 CM_GlobalVars := fmupd (DC_Name dc) finalTm
                                                    (CM_GlobalVars m) \<rparr>)))
         = Inr (env', elabEnv', m')"
        unfolding elab_const_decl_def Let_def
        using lkNone Some by auto
      have notin: "\<not> term_name_in_scope env (DC_Name dc)"
        using elabD by (cases "term_name_in_scope env (DC_Name dc)") simp_all
      from elabD notin obtain declTy where
        ety: "elab_type env elabEnv (DC_Ghost dc) ty = Inr declTy"
        by (cases "elab_type env elabEnv (DC_Ghost dc) ty") auto
      from elabD notin ety obtain finalTm where
        rhs_ok: "elab_const_rhs env elabEnv (DC_Ghost dc) (DC_Location dc) declTy rhs
                   = Inr finalTm" and
        env'_eq: "env' = tyenv_add_global (DC_Name dc) declTy (DC_Ghost dc) env" and
        ee'_eq: "elabEnv' = elabEnv" and
        m'_eq: "m' = m \<lparr> CM_TyEnv := tyenv_add_global (DC_Name dc) declTy
                                       (DC_Ghost dc) (CM_TyEnv m),
                         CM_GlobalVars := fmupd (DC_Name dc) finalTm (CM_GlobalVars m) \<rparr>"
        by (cases "elab_const_rhs env elabEnv (DC_Ghost dc) (DC_Location dc) declTy rhs")
           auto
      show thesis
        by (rule AnnotDefine[OF Some lkNone tySome notin ety rhs_ok
                                env'_eq ee'_eq m'_eq])
    qed
  qed
qed

(* The four branches of elab_const_decl, dispatched to the step lemmas. *)
lemma elab_const_decl_invariant:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and elab: "elab_const_decl env elabEnv m dc = Inr (env', elabEnv', m')"
  shows "elab_decls_invariant env0 ownAbstract env' elabEnv' m'"
proof -
  have wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and mv_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
    using inv unfolding elab_decls_invariant_def by blast+
  have td_wf: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using eewf unfolding elabenv_well_formed_def by blast
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  from elab show ?thesis
  proof (cases rule: elab_const_decl_Inr_elim)
    case (DeclOnly ty coreTy)
    \<comment> \<open>Declaration without definition (requires a type annotation).\<close>
    note notin = DeclOnly(2) and ety = DeclOnly(4)
    have wk: "is_well_kinded env coreTy"
      using elab_type_is_well_kinded(1)[OF td_wf wf ety] .
    have rt: "DC_Ghost dc = NotGhost \<longrightarrow> is_runtime_type env coreTy"
      using elab_type_notghost_is_runtime(1)[OF td_wf wf] ety by auto
    show ?thesis
      unfolding DeclOnly(5) DeclOnly(6) DeclOnly(7)
      by (rule elab_decls_invariant_add_global[OF inv notin wk rt])
  next
    case (DefineDeclared rhs declTy finalTm)
    \<comment> \<open>Definition of a previously-declared constant.\<close>
    note lk = DefineDeclared(2) and gm = DefineDeclared(4)
     and rhs_ok = DefineDeclared(5)
    have wk_decl: "is_well_kinded env declTy"
      using global_decl_well_kinded_module_scope[OF wf scope_env lk] .
    have rt_decl: "DC_Ghost dc = NotGhost \<longrightarrow> is_runtime_type env declTy"
    proof
      assume ng: "DC_Ghost dc = NotGhost"
      then have "DC_Name dc |\<notin>| TE_GhostGlobals env" using gm by simp
      then show "is_runtime_type env declTy"
        using global_decl_runtime_module_scope[OF wf scope_env lk] by blast
    qed
    have typed: "core_term_type env (DC_Ghost dc) finalTm = Some declTy"
     and const: "DC_Ghost dc = NotGhost \<longrightarrow> is_constant_term finalTm"
      using elab_const_rhs_correct[OF rhs_ok wf eewf mv_tv wk_decl rt_decl] by blast+
    show ?thesis
      unfolding DefineDeclared(6) DefineDeclared(7) DefineDeclared(8)
      by (rule elab_decls_invariant_define_global[OF inv lk gm typed const])
  next
    case (InferDefine rhs finalTm declTy)
    \<comment> \<open>No annotation: the constant's type is inferred from the rhs.\<close>
    note notin = InferDefine(4) and infer_ok = InferDefine(5)
    have typed: "core_term_type env (DC_Ghost dc) finalTm = Some declTy"
     and wk: "is_well_kinded env declTy"
     and rt: "DC_Ghost dc = NotGhost \<longrightarrow> is_runtime_type env declTy"
     and const: "DC_Ghost dc = NotGhost \<longrightarrow> is_constant_term finalTm"
      using elab_const_rhs_infer_correct[OF infer_ok wf eewf mv_tv] by blast+
    show ?thesis
      unfolding InferDefine(6) InferDefine(7) InferDefine(8)
      by (rule elab_decls_invariant_declare_define_global
                 [OF inv notin wk rt typed const])
  next
    case (AnnotDefine rhs ty declTy finalTm)
    \<comment> \<open>Annotated: the annotation fixes the type, the rhs is coerced to it.\<close>
    note notin = AnnotDefine(4) and ety = AnnotDefine(5)
     and rhs_ok = AnnotDefine(6)
    have wk: "is_well_kinded env declTy"
      using elab_type_is_well_kinded(1)[OF td_wf wf ety] .
    have rt: "DC_Ghost dc = NotGhost \<longrightarrow> is_runtime_type env declTy"
      using elab_type_notghost_is_runtime(1)[OF td_wf wf] ety by auto
    have typed: "core_term_type env (DC_Ghost dc) finalTm = Some declTy"
     and const: "DC_Ghost dc = NotGhost \<longrightarrow> is_constant_term finalTm"
      using elab_const_rhs_correct[OF rhs_ok wf eewf mv_tv wk rt] by blast+
    show ?thesis
      unfolding AnnotDefine(7) AnnotDefine(8) AnnotDefine(9)
      by (rule elab_decls_invariant_declare_define_global
                 [OF inv notin wk rt typed const])
  qed
qed

(* ---- Functions ---- *)

(* -------------------------------------------------------------------------- *)
(* Adding a function declaration to an env                                    *)
(* -------------------------------------------------------------------------- *)

(* Adding a fresh function is a tyenv extension (old entries survive; no
   other field changes). *)
lemma tyenv_extends_add_function:
  assumes fresh: "name |\<notin>| fmdom (TE_Functions env)"
  shows "tyenv_extends env (tyenv_add_function name info env)"
  unfolding tyenv_extends_def tyenv_add_function_def
  using fresh by (auto split: if_splits)

(* Adding a function whose signature satisfies the three per-function clauses
   (argument/return types well-kinded over the declaration's own type
   parameters, parameters distinct, runtime types if non-ghost) preserves
   well-formedness. Only the TE_Functions clauses do real work; everything
   else transfers by congruence. *)
lemma tyenv_well_formed_add_function:
  assumes wf: "tyenv_well_formed env"
      and dist_fi: "distinct (FI_TyArgs info)"
      and wk_args: "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                      is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
      and wk_ret: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                     (FI_ReturnType info)"
      and rt_p: "FI_Ghost info = NotGhost \<Longrightarrow>
                   (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                      is_runtime_type
                        (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                 |\<union>| fset_of_list (FI_TyArgs info),
                               TE_RuntimeTypeVars :=
                                 (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                 |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                   \<and> is_runtime_type
                       (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                       (FI_ReturnType info)"
  shows "tyenv_well_formed (tyenv_add_function name info env)"
proof -
  let ?env' = "tyenv_add_function name info env"
  have wk_cong: "\<And>tvs ty'. is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) ty'
                          = is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) ty'"
    by (rule is_well_kinded_cong_env) (simp_all add: tyenv_add_function_def)
  have wk_cong0: "\<And>ty'. is_well_kinded ?env' ty' = is_well_kinded env ty'"
    by (rule is_well_kinded_cong_env) (simp_all add: tyenv_add_function_def)
  have rt_cong: "\<And>tvs rtvs ty'.
        is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty'
      = is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty'"
    by (rule is_runtime_type_cong_env) (simp_all add: tyenv_add_function_def)
  have rt_cong0: "\<And>ty'. is_runtime_type ?env' ty' = is_runtime_type env ty'"
    by (rule is_runtime_type_cong_env) (simp_all add: tyenv_add_function_def)
  \<comment> \<open>Folded projections: rewriting with these (rather than unfolding the
      definition) keeps the cong rules' left-hand sides intact.\<close>
  have proj: "TE_LocalVars ?env' = TE_LocalVars env"
             "TE_GlobalVars ?env' = TE_GlobalVars env"
             "TE_GhostLocals ?env' = TE_GhostLocals env"
             "TE_GhostGlobals ?env' = TE_GhostGlobals env"
             "TE_TypeVars ?env' = TE_TypeVars env"
             "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env"
             "TE_AbstractTypes ?env' = TE_AbstractTypes env"
             "TE_ReturnType ?env' = TE_ReturnType env"
             "TE_FunctionGhost ?env' = TE_FunctionGhost env"
             "TE_Datatypes ?env' = TE_Datatypes env"
             "TE_DataCtors ?env' = TE_DataCtors env"
             "TE_DataCtorsByType ?env' = TE_DataCtorsByType env"
             "TE_GhostDatatypes ?env' = TE_GhostDatatypes env"
    by (simp_all add: tyenv_add_function_def)
  have fns: "TE_Functions ?env' = fmupd name info (TE_Functions env)"
    by (simp add: tyenv_add_function_def)
  have vwk: "tyenv_vars_well_kinded env"
   and vrt: "tyenv_vars_runtime env"
   and gvs: "tyenv_ghost_vars_subset env"
   and rwk: "tyenv_return_type_well_kinded env"
   and rrt: "tyenv_return_type_runtime env"
   and cons: "tyenv_ctors_consistent env"
   and pwk: "tyenv_payloads_well_kinded env"
   and ctd: "tyenv_ctor_tyvars_distinct env"
   and cbt: "tyenv_ctors_by_type_consistent env"
   and fwk: "tyenv_fun_types_well_kinded env"
   and ftd: "tyenv_fun_tyvars_distinct env"
   and fgc: "tyenv_fun_ghost_constraint env"
   and npr: "tyenv_nonghost_payloads_runtime env"
   and gds: "tyenv_ghost_datatypes_subset env"
   and rts: "tyenv_runtime_tyvars_subset env"
   and ats: "tyenv_abstract_types_subset env"
   and dne: "tyenv_datatypes_nonempty env"
    using wf unfolding tyenv_well_formed_def by blast+
  have vwk': "tyenv_vars_well_kinded ?env'"
    using vwk unfolding tyenv_vars_well_kinded_def
    by (simp add: proj wk_cong wk_cong0)
  have vrt': "tyenv_vars_runtime ?env'"
    using vrt unfolding tyenv_vars_runtime_def
    by (simp add: proj rt_cong rt_cong0)
  have gvs': "tyenv_ghost_vars_subset ?env'"
    using gvs unfolding tyenv_ghost_vars_subset_def
    by (simp add: tyenv_add_function_def)
  have rwk': "tyenv_return_type_well_kinded ?env'"
    using rwk unfolding tyenv_return_type_well_kinded_def
    by (simp add: proj wk_cong0)
  have rrt': "tyenv_return_type_runtime ?env'"
    using rrt unfolding tyenv_return_type_runtime_def
    by (simp add: proj rt_cong0)
  have cons': "tyenv_ctors_consistent ?env'"
    using cons unfolding tyenv_ctors_consistent_def
    by (simp add: tyenv_add_function_def)
  have pwk': "tyenv_payloads_well_kinded ?env'"
    using pwk unfolding tyenv_payloads_well_kinded_def
    by (simp add: proj wk_cong)
  have ctd': "tyenv_ctor_tyvars_distinct ?env'"
    using ctd unfolding tyenv_ctor_tyvars_distinct_def
    by (simp add: tyenv_add_function_def)
  have cbt': "tyenv_ctors_by_type_consistent ?env'"
    using cbt unfolding tyenv_ctors_by_type_consistent_def
    by (simp add: tyenv_add_function_def)
  \<comment> \<open>The three function clauses: case split at the new name.\<close>
  have entry_cases: "\<And>funName inf.
      fmlookup (TE_Functions ?env') funName = Some inf \<Longrightarrow>
      inf = info \<or> fmlookup (TE_Functions env) funName = Some inf"
  proof -
    fix funName inf
    assume "fmlookup (TE_Functions ?env') funName = Some inf"
    then have "fmlookup (fmupd name info (TE_Functions env)) funName = Some inf"
      by (simp add: fns)
    then show "inf = info \<or> fmlookup (TE_Functions env) funName = Some inf"
      by (cases "funName = name") auto
  qed
  have fwk': "tyenv_fun_types_well_kinded ?env'"
    unfolding tyenv_fun_types_well_kinded_def
  proof (intro allI impI)
    fix funName inf
    assume "fmlookup (TE_Functions ?env') funName = Some inf"
    then have "inf = info \<or> fmlookup (TE_Functions env) funName = Some inf"
      by (rule entry_cases)
    then show "(\<forall>ty \<in> fst ` set (FI_TmArgs inf).
                  is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                            |\<union>| fset_of_list (FI_TyArgs inf) \<rparr>) ty)
               \<and> is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                           |\<union>| fset_of_list (FI_TyArgs inf) \<rparr>)
                   (FI_ReturnType inf)"
    proof (elim disjE)
      assume inf_eq: "inf = info"
      show ?thesis
        using wk_args wk_ret unfolding inf_eq by (simp add: proj wk_cong)
    next
      assume "fmlookup (TE_Functions env) funName = Some inf"
      then have "(\<forall>ty \<in> fst ` set (FI_TmArgs inf).
                    is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                            |\<union>| fset_of_list (FI_TyArgs inf) \<rparr>) ty)
                 \<and> is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                           |\<union>| fset_of_list (FI_TyArgs inf) \<rparr>)
                     (FI_ReturnType inf)"
        using fwk unfolding tyenv_fun_types_well_kinded_def by blast
      then show ?thesis by (simp add: proj wk_cong)
    qed
  qed
  have ftd': "tyenv_fun_tyvars_distinct ?env'"
    unfolding tyenv_fun_tyvars_distinct_def
  proof (intro allI impI)
    fix funName inf
    assume "fmlookup (TE_Functions ?env') funName = Some inf"
    then have "inf = info \<or> fmlookup (TE_Functions env) funName = Some inf"
      by (rule entry_cases)
    then show "distinct (FI_TyArgs inf)"
      using dist_fi ftd unfolding tyenv_fun_tyvars_distinct_def by blast
  qed
  have fgc': "tyenv_fun_ghost_constraint ?env'"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI)
    fix funName inf
    assume h: "fmlookup (TE_Functions ?env') funName = Some inf
               \<and> FI_Ghost inf = NotGhost"
    then have ng: "FI_Ghost inf = NotGhost" by blast
    from h have "inf = info \<or> fmlookup (TE_Functions env) funName = Some inf"
      using entry_cases by blast
    then show "(\<forall>ty \<in> fst ` set (FI_TmArgs inf).
                  is_runtime_type
                    (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                               |\<union>| fset_of_list (FI_TyArgs inf),
                             TE_RuntimeTypeVars :=
                               (TE_AbstractTypes ?env' |\<inter>| TE_RuntimeTypeVars ?env')
                               |\<union>| fset_of_list (FI_TyArgs inf) \<rparr>) ty)
               \<and> is_runtime_type
                   (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                              |\<union>| fset_of_list (FI_TyArgs inf),
                            TE_RuntimeTypeVars :=
                              (TE_AbstractTypes ?env' |\<inter>| TE_RuntimeTypeVars ?env')
                              |\<union>| fset_of_list (FI_TyArgs inf) \<rparr>)
                   (FI_ReturnType inf)"
    proof (elim disjE)
      assume inf_eq: "inf = info"
      have ng': "FI_Ghost info = NotGhost"
        using ng unfolding inf_eq .
      show ?thesis
        using rt_p[OF ng'] unfolding inf_eq by (simp add: proj rt_cong)
    next
      assume "fmlookup (TE_Functions env) funName = Some inf"
      then have "(\<forall>ty \<in> fst ` set (FI_TmArgs inf).
                    is_runtime_type
                      (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                               |\<union>| fset_of_list (FI_TyArgs inf),
                             TE_RuntimeTypeVars :=
                               (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                               |\<union>| fset_of_list (FI_TyArgs inf) \<rparr>) ty)
                 \<and> is_runtime_type
                     (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                              |\<union>| fset_of_list (FI_TyArgs inf),
                            TE_RuntimeTypeVars :=
                              (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                              |\<union>| fset_of_list (FI_TyArgs inf) \<rparr>)
                     (FI_ReturnType inf)"
        using fgc ng unfolding tyenv_fun_ghost_constraint_def Let_def by blast
      then show ?thesis by (simp add: proj rt_cong)
    qed
  qed
  have npr': "tyenv_nonghost_payloads_runtime ?env'"
    using npr unfolding tyenv_nonghost_payloads_runtime_def
    by (simp add: proj rt_cong)
  have gds': "tyenv_ghost_datatypes_subset ?env'"
    using gds unfolding tyenv_ghost_datatypes_subset_def
    by (simp add: tyenv_add_function_def)
  have rts': "tyenv_runtime_tyvars_subset ?env'"
    using rts unfolding tyenv_runtime_tyvars_subset_def
    by (simp add: tyenv_add_function_def)
  have ats': "tyenv_abstract_types_subset ?env'"
    using ats unfolding tyenv_abstract_types_subset_def
    by (simp add: tyenv_add_function_def)
  have dne': "tyenv_datatypes_nonempty ?env'"
    using dne unfolding tyenv_datatypes_nonempty_def
    by (simp add: tyenv_add_function_def)
  show ?thesis
    unfolding tyenv_well_formed_def
    using vwk' vrt' gvs' rwk' rrt' cons' pwk' ctd' cbt' fwk' ftd' fgc' npr'
          gds' rts' ats' dne'
    by blast
qed

(* A FunInfo whose types are well-kinded over type variables that avoid a
   substitution's domain is untouched by that substitution. *)
lemma funinfo_subst_id:
  assumes disj: "(TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info))
                   |\<inter>| fmdom s = {||}"
      and wk_args: "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                      is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
      and wk_ret: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                           |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                     (FI_ReturnType info)"
  shows "apply_subst_to_funinfo s info = info"
proof -
  let ?wkEnv = "env \<lparr> TE_TypeVars := TE_AbstractTypes env
                        |\<union>| fset_of_list (FI_TyArgs info) \<rparr>"
  have tv_disj: "TE_TypeVars ?wkEnv |\<inter>| fmdom s = {||}"
    using disj by simp
  have args_eq: "map (\<lambda>(ty, vr). (apply_subst s ty, vr)) (FI_TmArgs info)
               = FI_TmArgs info"
  proof (rule map_idI)
    fix x assume x_in: "x \<in> set (FI_TmArgs info)"
    obtain ty vr where x_eq: "x = (ty, vr)" by (cases x) auto
    have "ty \<in> fst ` set (FI_TmArgs info)" using x_in x_eq by force
    then have "is_well_kinded ?wkEnv ty" using wk_args by blast
    then have "apply_subst s ty = ty"
      using apply_subst_id_on_env_type[OF tv_disj] by blast
    then show "(\<lambda>(ty, vr). (apply_subst s ty, vr)) x = x" by (simp add: x_eq)
  qed
  have ret_eq: "apply_subst s (FI_ReturnType info) = FI_ReturnType info"
    using apply_subst_id_on_env_type[OF tv_disj wk_ret] .
  show ?thesis
    unfolding apply_subst_to_funinfo_def by (simp add: args_eq ret_eq)
qed

(* tyenv_add_function commutes with module_context_env, provided the new
   FunInfo is untouched by the module's substitution. *)
lemma module_context_env_add_function:
  assumes subst_id: "apply_subst_to_funinfo (CM_TypeSubst m) info = info"
  shows "tyenv_add_function name info (module_context_env env0 m)
       = module_context_env env0
           (m \<lparr> CM_TyEnv := tyenv_add_function name info (CM_TyEnv m) \<rparr>)"
  unfolding module_context_env_def apply_subst_to_tyenv_def tyenv_add_function_def
  by (simp add: fmmap_fmupd subst_id)

(* Adding a function grows scope_bound_tyvars by at most its type
   parameters. *)
lemma scope_bound_tyvars_add_function:
  "scope_bound_tyvars (tyenv_add_function name info env) elabEnv
     |\<subseteq>| fset_of_list (FI_TyArgs info) |\<union>| scope_bound_tyvars env elabEnv"
proof
  fix x
  assume "x |\<in>| scope_bound_tyvars (tyenv_add_function name info env) elabEnv"
  then consider
      (fn) "x |\<in>| ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info))
                             |`| fmran (fmupd name info (TE_Functions env)))"
    | (dc) "x |\<in>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars)
                             |`| fmran (TE_DataCtors env))"
    | (td) "x |\<in>| ffUnion ((\<lambda>(tyVars, _). fset_of_list tyVars)
                             |`| fmran (EE_Typedefs elabEnv))"
    unfolding scope_bound_tyvars_def tyenv_add_function_def by auto
  then show "x |\<in>| fset_of_list (FI_TyArgs info) |\<union>| scope_bound_tyvars env elabEnv"
  proof cases
    case fn
    from ffUnion_fmran_fmupd_member[OF fn]
    show ?thesis unfolding scope_bound_tyvars_def by auto
  next
    case dc
    then show ?thesis unfolding scope_bound_tyvars_def by auto
  next
    case td
    then show ?thesis unfolding scope_bound_tyvars_def by auto
  qed
qed

(* The invariant only reads three ElabEnv fields (the typedef table, the
   nullary data-constructor set and the void flag); changing any other field - the
   void-functions set, in particular - preserves it. *)
lemma elab_decls_invariant_ee_cong:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and td_eq: "EE_Typedefs elabEnv' = EE_Typedefs elabEnv"
      and vd_ctor_eq: "EE_NullaryDataCtors elabEnv' = EE_NullaryDataCtors elabEnv"
      and vd_eq: "EE_CurrentFunctionVoid elabEnv' = EE_CurrentFunctionVoid elabEnv"
  shows "elab_decls_invariant env0 ownAbstract env elabEnv' m"
proof -
  have sbt_eq: "scope_bound_tyvars env elabEnv' = scope_bound_tyvars env elabEnv"
    unfolding scope_bound_tyvars_def by (simp add: td_eq)
  have ee_eq: "elabenv_well_formed env elabEnv' = elabenv_well_formed env elabEnv"
    unfolding elabenv_well_formed_def nullary_data_ctors_consistent_def
    by (simp add: td_eq vd_ctor_eq vd_eq)
  show ?thesis
    using inv unfolding elab_decls_invariant_def
    using ee_eq sbt_eq td_eq by auto
qed


(* -------------------------------------------------------------------------- *)
(* Correctness of signature elaboration                                       *)
(* -------------------------------------------------------------------------- *)

(* A successfully elaborated signature has the declaration's type parameters
   and flags, one argument entry per declared parameter, and argument/return
   types well-kinded (runtime, for a non-ghost function) over the env
   extended with the type parameters. A void declaration's return type is
   unit. *)
lemma elab_fun_signature_correct:
  assumes wf: "tyenv_well_formed env"
      and td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
      and sig: "elab_fun_signature env elabEnv df = Inr info"
  shows "FI_TyArgs info = DF_TyArgs df"
    and "FI_Ghost info = DF_Ghost df"
    and "FI_Impure info = DF_Impure df"
    and "length (FI_TmArgs info) = length (DF_TmArgs df)"
    and "\<forall>ty \<in> fst ` set (FI_TmArgs info).
           is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env
                                   |\<union>| fset_of_list (DF_TyArgs df) \<rparr>) ty"
    and "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env
                                 |\<union>| fset_of_list (DF_TyArgs df) \<rparr>)
           (FI_ReturnType info)"
    and "DF_Ghost df = NotGhost \<Longrightarrow>
           (\<forall>ty \<in> fst ` set (FI_TmArgs info).
              is_runtime_type
                (env \<lparr> TE_TypeVars := TE_TypeVars env
                         |\<union>| fset_of_list (DF_TyArgs df),
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars env
                         |\<union>| fset_of_list (DF_TyArgs df) \<rparr>) ty)
           \<and> is_runtime_type
               (env \<lparr> TE_TypeVars := TE_TypeVars env
                        |\<union>| fset_of_list (DF_TyArgs df),
                      TE_RuntimeTypeVars := TE_RuntimeTypeVars env
                        |\<union>| fset_of_list (DF_TyArgs df) \<rparr>)
               (FI_ReturnType info)"
    and "DF_ReturnType df = None \<Longrightarrow> FI_ReturnType info = CoreTy_Record []"
proof -
  let ?tyvars = "DF_TyArgs df"
  let ?ghost = "DF_Ghost df"
  let ?sigEnv = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list ?tyvars,
                       TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>|
                         (if ?ghost = NotGhost then fset_of_list ?tyvars
                          else {||}) \<rparr>"
  let ?sigEE = "elabEnv \<lparr> EE_Typedefs :=
                   tyvar_typedef_entries ?tyvars (EE_Typedefs elabEnv) \<rparr>"
  let ?wkEnv = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list ?tyvars \<rparr>"
  \<comment> \<open>Peel the two scrutinees one at a time.\<close>
  from sig obtain argTys where
    args: "elab_type_list ?sigEnv ?sigEE ?ghost
             (map (\<lambda>(_, _, ty). ty) (DF_TmArgs df)) = Inr argTys"
    unfolding elab_fun_signature_def Let_def
    by (cases "elab_type_list ?sigEnv ?sigEE ?ghost
                 (map (\<lambda>(_, _, ty). ty) (DF_TmArgs df))") auto
  from sig args obtain retTy where
    ret: "(case DF_ReturnType df of
             None \<Rightarrow> Inr (CoreTy_Record [])
           | Some rty \<Rightarrow> elab_type ?sigEnv ?sigEE ?ghost rty) = Inr retTy" and
    info_eq: "info = \<lparr> FI_TyArgs = ?tyvars,
                       FI_TmArgs = zip argTys
                                     (map (\<lambda>(_, vor, _). vor) (DF_TmArgs df)),
                       FI_ReturnType = retTy,
                       FI_Ghost = ?ghost,
                       FI_Impure = DF_Impure df \<rparr>"
    unfolding elab_fun_signature_def Let_def
    by (cases "case DF_ReturnType df of
                 None \<Rightarrow> Inr (CoreTy_Record [])
               | Some rty \<Rightarrow> elab_type ?sigEnv ?sigEE ?ghost rty") auto
  \<comment> \<open>Structural conclusions.\<close>
  show tyargs: "FI_TyArgs info = DF_TyArgs df" by (simp add: info_eq)
  show "FI_Ghost info = DF_Ghost df" by (simp add: info_eq)
  show "FI_Impure info = DF_Impure df" by (simp add: info_eq)
  have len_args: "length argTys = length (DF_TmArgs df)"
    using elab_type_list_length[OF args] by simp
  show "length (FI_TmArgs info) = length (DF_TmArgs df)"
    using len_args by (simp add: info_eq)
  have fst_tm: "fst ` set (FI_TmArgs info) = set argTys"
  proof -
    have "map fst (zip argTys (map (\<lambda>(_, vor, _). vor) (DF_TmArgs df))) = argTys"
      by (rule map_fst_zip) (simp add: len_args)
    then show ?thesis
      unfolding info_eq by (metis FunInfo.select_convs(2) set_map)
  qed
  \<comment> \<open>Entry conditions for the type elaborator at the signature env.\<close>
  have rt_sub: "(if ?ghost = NotGhost then fset_of_list ?tyvars else {||})
                  |\<subseteq>| fset_of_list ?tyvars"
    by simp
  have wf_sig: "tyenv_well_formed ?sigEnv"
    using tyenv_well_formed_extend_tyvars[OF wf rt_sub] .
  have td_grow: "typedefs_well_formed ?sigEnv (EE_Typedefs elabEnv)"
    by (rule typedefs_well_formed_mono[OF td]) auto
  have td_sig: "typedefs_well_formed ?sigEnv (EE_Typedefs ?sigEE)"
    using typedefs_well_formed_tyvar_entries[OF td_grow, of ?tyvars] by auto
  \<comment> \<open>Well-kindedness of the argument and return types; the runtime-tyvar
      override is invisible to is_well_kinded.\<close>
  have wk_drop: "\<And>ty. is_well_kinded ?sigEnv ty = is_well_kinded ?wkEnv ty"
    by (rule is_well_kinded_cong_env) simp_all
  have args_wk: "list_all (is_well_kinded ?sigEnv) argTys"
    using elab_type_is_well_kinded(2)[OF td_sig wf_sig args] .
  show "\<forall>ty \<in> fst ` set (FI_TmArgs info). is_well_kinded ?wkEnv ty"
    using args_wk unfolding fst_tm list_all_iff wk_drop by blast
  have ret_wk: "is_well_kinded ?sigEnv retTy"
  proof (cases "DF_ReturnType df")
    case None
    then have "retTy = CoreTy_Record []" using ret by simp
    then show ?thesis by simp
  next
    case (Some rty)
    then have "elab_type ?sigEnv ?sigEE ?ghost rty = Inr retTy" using ret by simp
    then show ?thesis using elab_type_is_well_kinded(1)[OF td_sig wf_sig] by blast
  qed
  show "is_well_kinded ?wkEnv (FI_ReturnType info)"
    using ret_wk unfolding wk_drop by (simp add: info_eq)
  \<comment> \<open>Runtime types, in the non-ghost case (where the signature env's
      runtime-tyvar conditional resolves).\<close>
  show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
           is_runtime_type
             (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list ?tyvars,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars env
                      |\<union>| fset_of_list ?tyvars \<rparr>) ty)
        \<and> is_runtime_type
            (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list ?tyvars,
                   TE_RuntimeTypeVars := TE_RuntimeTypeVars env
                     |\<union>| fset_of_list ?tyvars \<rparr>)
            (FI_ReturnType info)"
    if ng: "DF_Ghost df = NotGhost"
  proof -
    have env_res: "?sigEnv = env \<lparr> TE_TypeVars := TE_TypeVars env
                                     |\<union>| fset_of_list ?tyvars,
                                   TE_RuntimeTypeVars := TE_RuntimeTypeVars env
                                     |\<union>| fset_of_list ?tyvars \<rparr>"
      by (simp add: ng)
    have args_rt: "list_all (is_runtime_type ?sigEnv) argTys"
      using elab_type_notghost_is_runtime(2)[OF td_sig wf_sig] args ng by simp
    have ret_rt: "is_runtime_type ?sigEnv retTy"
    proof (cases "DF_ReturnType df")
      case None
      then have "retTy = CoreTy_Record []" using ret by simp
      then show ?thesis by simp
    next
      case (Some rty)
      then have "elab_type ?sigEnv ?sigEE ?ghost rty = Inr retTy" using ret by simp
      then show ?thesis
        using elab_type_notghost_is_runtime(1)[OF td_sig wf_sig] ng by simp
    qed
    show ?thesis
      using args_rt ret_rt
      unfolding env_res [symmetric] fst_tm list_all_iff
      by (simp add: info_eq)
  qed
  \<comment> \<open>Void return.\<close>
  show "FI_ReturnType info = CoreTy_Record []" if "DF_ReturnType df = None"
  proof -
    have "retTy = CoreTy_Record []" using ret that by simp
    then show ?thesis by (simp add: info_eq)
  qed
qed


(* -------------------------------------------------------------------------- *)
(* The invariant step for declaring a function                                *)
(* -------------------------------------------------------------------------- *)

(* Declaring a fresh function (in both the state env and the module's
   CM_TyEnv) preserves the invariant, given the signature facts in the
   well-formedness clauses' own (TE_AbstractTypes-based) form and the
   binder-capture check's disjointness. The ElabEnv is unchanged here; the
   elaborator's void-functions update is invisible to the invariant
   (elab_decls_invariant_ee_cong). *)
lemma elab_decls_invariant_add_function:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and notin: "\<not> term_name_in_scope env name"
      and fi_cap: "subst_names (CM_TypeSubst m)
                     |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
      and fi_fresh: "list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
      and dist_fi: "distinct (FI_TyArgs info)"
      and wk_args: "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                      is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
      and wk_ret: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                           |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                     (FI_ReturnType info)"
      and rt_p: "FI_Ghost info = NotGhost \<Longrightarrow>
                   (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                      is_runtime_type
                        (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                 |\<union>| fset_of_list (FI_TyArgs info),
                               TE_RuntimeTypeVars :=
                                 (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                 |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                   \<and> is_runtime_type
                       (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                       (FI_ReturnType info)"
  shows "elab_decls_invariant env0 ownAbstract
           (tyenv_add_function name info env) elabEnv
           (m \<lparr> CM_TyEnv := tyenv_add_function name info (CM_TyEnv m) \<rparr>)"
proof -
  let ?env' = "tyenv_add_function name info env"
  let ?m' = "m \<lparr> CM_TyEnv := tyenv_add_function name info (CM_TyEnv m) \<rparr>"
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and own_disj: "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and swk: "typesubst_well_kinded env (CM_TypeSubst m)"
   and dom_own: "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract"
   and dom_td: "fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs elabEnv)"
   and cap_env: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
   and mv_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and mv_fn: "\<forall>fname inf. fmlookup (TE_Functions env) fname = Some inf \<longrightarrow>
                 list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)"
   and gwt: "module_globals_well_typed env (CM_GlobalVars (normalize_module m))"
   and fwt: "module_functions_well_typed env (CM_Functions (normalize_module m))"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope_env unfolding tyenv_module_scope_def by blast
  have tv_disj: "TE_TypeVars env |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
  \<comment> \<open>The new type parameters avoid the substitution's whole name set, so in
      particular its domain.\<close>
  have dom_sub: "fmdom (CM_TypeSubst m) |\<subseteq>| subst_names (CM_TypeSubst m)"
    unfolding subst_names_def by simp
  have fi_cap': "fset_of_list (FI_TyArgs info)
                   |\<inter>| subst_names (CM_TypeSubst m) = {||}"
    using fi_cap by (simp add: inf_commute)
  have fi_dom: "fset_of_list (FI_TyArgs info) |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using empty_inter_subset[OF fi_cap' dom_sub] .
  have wk_disj: "(TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info))
                   |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    by (simp add: abs_tv inf_sup_distrib2 tv_disj fi_dom)
  have subst_id: "apply_subst_to_funinfo (CM_TypeSubst m) info = info"
    using funinfo_subst_id[OF wk_disj wk_args wk_ret] .
  have fresh_fn: "name |\<notin>| fmdom (TE_Functions env)"
    using notin unfolding term_name_in_scope_def by blast
  have ext: "tyenv_extends env ?env'"
    using tyenv_extends_add_function[OF fresh_fn] .
  have cons: "tyenv_ctors_consistent env"
    using wf unfolding tyenv_well_formed_def by blast
  \<comment> \<open>The individual conjuncts.\<close>
  have env_eq': "?env' = module_context_env env0 ?m'"
    using module_context_env_add_function[OF subst_id, of name env0] env_eq by simp
  have minv': "core_module_invariant ?m'"
  proof -
    have cap_m: "capture_avoiding m"
      using minv unfolding core_module_invariant_def by blast
    have cap': "capture_avoiding ?m'"
      unfolding capture_avoiding_def
    proof (intro conjI allI impI)
      fix funName inf
      assume "fmlookup (TE_Functions (CM_TyEnv ?m')) funName = Some inf"
      then have "fmlookup (fmupd name info (TE_Functions (CM_TyEnv m))) funName
                   = Some inf"
        by (simp add: tyenv_add_function_def)
      then have "inf = info \<or> fmlookup (TE_Functions (CM_TyEnv m)) funName = Some inf"
        by (cases "funName = name") auto
      then show "subst_names (CM_TypeSubst ?m')
                   |\<inter>| fset_of_list (FI_TyArgs inf) = {||}"
        using fi_cap cap_m unfolding capture_avoiding_def by auto
    next
      fix ctorName dtName tyVars payload
      assume "fmlookup (TE_DataCtors (CM_TyEnv ?m')) ctorName
                = Some (dtName, tyVars, payload)"
      then have "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName
                   = Some (dtName, tyVars, payload)"
        by (simp add: tyenv_add_function_def)
      then show "subst_names (CM_TypeSubst ?m') |\<inter>| fset_of_list tyVars = {||}"
        using cap_m unfolding capture_avoiding_def by fastforce
    qed
    show ?thesis
      using minv cap'
      unfolding core_module_invariant_def module_ghost_subsets_ok_def
                tyenv_module_scope_def
      by (simp add: tyenv_add_function_def)
  qed
  have own_disj': "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}"
    using own_disj by (simp add: tyenv_add_function_def)
  have wf': "tyenv_well_formed ?env'"
    using tyenv_well_formed_add_function[OF wf dist_fi wk_args wk_ret rt_p] .
  have cong_ee: "elabenv_well_formed ?env' elabEnv = elabenv_well_formed env elabEnv"
    by (rule elabenv_well_formed_cong_env) (simp_all add: tyenv_add_function_def)
  have eewf': "elabenv_well_formed ?env' elabEnv"
    using eewf cong_ee by simp
  have swk_env': "typesubst_well_kinded ?env' (CM_TypeSubst m)"
    by (rule typesubst_well_kinded_mono[OF swk])
       (simp_all add: tyenv_add_function_def)
  have sbt_bound: "scope_bound_tyvars ?env' elabEnv
                     |\<subseteq>| fset_of_list (FI_TyArgs info)
                          |\<union>| scope_bound_tyvars env elabEnv"
    by (rule scope_bound_tyvars_add_function)
  have cap_new: "subst_names (CM_TypeSubst m)
                   |\<inter>| (fset_of_list (FI_TyArgs info)
                        |\<union>| scope_bound_tyvars env elabEnv) = {||}"
    using fi_cap cap_env by (simp add: inf_sup_distrib1)
  have cap': "subst_names (CM_TypeSubst m)
                |\<inter>| scope_bound_tyvars ?env' elabEnv = {||}"
    using empty_inter_subset[OF cap_new sbt_bound] .
  have mv_tv': "\<forall>n. n |\<in>| TE_TypeVars ?env' \<longrightarrow> tyvar_fresh_ok n 0"
    using mv_tv by (simp add: tyenv_add_function_def)
  have mv_fn': "\<forall>fname inf. fmlookup (TE_Functions ?env') fname = Some inf \<longrightarrow>
                  list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)"
  proof (intro allI impI)
    fix fname inf
    assume "fmlookup (TE_Functions ?env') fname = Some inf"
    then have "fmlookup (fmupd name info (TE_Functions env)) fname = Some inf"
      by (simp add: tyenv_add_function_def)
    then have "inf = info \<or> fmlookup (TE_Functions env) fname = Some inf"
      by (cases "fname = name") auto
    then show "list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)"
      using fi_fresh mv_fn by blast
  qed
  have glb_same: "CM_GlobalVars (normalize_module ?m')
                = CM_GlobalVars (normalize_module m)"
    by (simp add: normalize_module_def)
  have fns_same: "CM_Functions (normalize_module ?m')
                = CM_Functions (normalize_module m)"
    by (simp add: normalize_module_def)
  have gwt': "module_globals_well_typed ?env' (CM_GlobalVars (normalize_module ?m'))"
    unfolding glb_same
    by (rule module_globals_well_typed_tyenv_extends[OF gwt ext cons])
  have fwt': "module_functions_well_typed ?env' (CM_Functions (normalize_module ?m'))"
    unfolding fns_same
    by (rule module_functions_well_typed_tyenv_extends[OF fwt ext cons])
       (simp add: tyenv_add_function_def)
  show ?thesis
    unfolding elab_decls_invariant_def
  proof (intro conjI)
    show "elab_context_ok env0 ownAbstract" using ctx .
    show "?env' = module_context_env env0 ?m'" using env_eq' .
    show "core_module_invariant ?m'" using minv' .
    show "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}" using own_disj' .
    show "tyenv_well_formed ?env'" using wf' .
    show "elabenv_well_formed ?env' elabEnv" using eewf' .
    show "typesubst_well_kinded ?env' (CM_TypeSubst ?m')" using swk_env' by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| ownAbstract" using dom_own by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| fmdom (EE_Typedefs elabEnv)" using dom_td by simp
    show "subst_names (CM_TypeSubst ?m') |\<inter>| scope_bound_tyvars ?env' elabEnv = {||}"
      using cap' by simp
    show "\<forall>n. n |\<in>| TE_TypeVars ?env' \<longrightarrow> tyvar_fresh_ok n 0" using mv_tv' .
    show "\<forall>fname inf. fmlookup (TE_Functions ?env') fname = Some inf \<longrightarrow>
            list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)" using mv_fn' .
    show "module_globals_well_typed ?env' (CM_GlobalVars (normalize_module ?m'))"
      using gwt' .
    show "module_functions_well_typed ?env' (CM_Functions (normalize_module ?m'))"
      using fwt' .
  qed
qed

(* -------------------------------------------------------------------------- *)
(* Function bodies are "born resolved"                                        *)
(* -------------------------------------------------------------------------- *)

(* The body env of a declared function absorbs the module's substitution just
   as the state env does (state_env_subst_absorb): its declaration tables are
   the state env's own, its parameter and return types come from the
   function's signature - whose types avoid the substitution domain, by
   well-formedness and the capture conjunct - and its type-variable fields
   are supplied by the target env, which is the body env itself. *)
lemma elab_decls_invariant_body_env_absorb:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and lk: "fmlookup (TE_Functions env) fname = Some info"
  shows "apply_subst_to_module_env (CM_TypeSubst m)
           (module_body_env_for env names info)
           (module_body_env_for env names info)
         = module_body_env_for env names info"
proof -
  let ?s = "CM_TypeSubst m"
  let ?be = "module_body_env_for env names info"
  let ?wkEnv = "env \<lparr> TE_TypeVars := TE_AbstractTypes env
                        |\<union>| fset_of_list (FI_TyArgs info) \<rparr>"
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and wf: "tyenv_well_formed env"
   and cap_env: "subst_names ?s |\<inter>| scope_bound_tyvars env elabEnv = {||}"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope0: "tyenv_module_scope env0"
    using ctx unfolding elab_context_ok_def by blast
  have idem: "idempotent_subst ?s"
    using minv unfolding core_module_invariant_def by blast
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope_env unfolding tyenv_module_scope_def by blast
  have tv_disj: "TE_TypeVars env |\<inter>| fmdom ?s = {||}"
    using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
  have dom_sub: "fmdom ?s |\<subseteq>| subst_names ?s"
    unfolding subst_names_def by simp
  have fi_cap: "subst_names ?s |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
    using empty_inter_subset[OF cap_env scope_bound_tyvars_fun_entry[OF lk]] .
  have fi_cap': "fset_of_list (FI_TyArgs info) |\<inter>| subst_names ?s = {||}"
    using fi_cap by (simp add: inf_commute)
  have fi_dom: "fset_of_list (FI_TyArgs info) |\<inter>| fmdom ?s = {||}"
    using empty_inter_subset[OF fi_cap' dom_sub] .
  \<comment> \<open>The signature's types are fixed by the substitution.\<close>
  have wk_args: "\<forall>ty \<in> fst ` set (FI_TmArgs info). is_well_kinded ?wkEnv ty"
   and wk_ret: "is_well_kinded ?wkEnv (FI_ReturnType info)"
    using wf lk
    unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast+
  have tv_wk: "TE_TypeVars ?wkEnv |\<inter>| fmdom ?s = {||}"
    by (simp add: abs_tv inf_sup_distrib2 tv_disj fi_dom)
  have args_id: "\<And>ty. ty \<in> fst ` set (FI_TmArgs info) \<Longrightarrow> apply_subst ?s ty = ty"
    using apply_subst_id_on_env_type[OF tv_wk] wk_args by blast
  have ret_id: "apply_subst ?s (FI_ReturnType info) = FI_ReturnType info"
    using apply_subst_id_on_env_type[OF tv_wk wk_ret] .
  \<comment> \<open>Hence so are the parameter locals.\<close>
  have locals_id: "fmmap (apply_subst ?s)
                     (fmap_of_list (zip names (map fst (FI_TmArgs info))))
                 = fmap_of_list (zip names (map fst (FI_TmArgs info)))"
  proof (rule fmap_ext)
    fix k
    show "fmlookup (fmmap (apply_subst ?s)
                      (fmap_of_list (zip names (map fst (FI_TmArgs info))))) k
        = fmlookup (fmap_of_list (zip names (map fst (FI_TmArgs info)))) k"
    proof (cases "fmlookup (fmap_of_list (zip names (map fst (FI_TmArgs info)))) k")
      case None
      then show ?thesis by simp
    next
      case (Some ty)
      then have "(k, ty) \<in> set (zip names (map fst (FI_TmArgs info)))"
        by (auto simp: fmlookup_of_list dest: map_of_SomeD)
      then have "ty \<in> fst ` set (FI_TmArgs info)"
        by (auto dest: set_zip_rightD)
      then show ?thesis using Some by (simp add: args_id)
    qed
  qed
  \<comment> \<open>The shared declaration tables absorb the substitution exactly as they
      do in the state env.\<close>
  have absorb: "apply_subst_to_module_env ?s env env = env"
    using state_env_subst_absorb[OF env_eq scope0 idem] .
  have gv_abs: "fmmap (apply_subst ?s) (TE_GlobalVars env) = TE_GlobalVars env"
    using arg_cong[where f = TE_GlobalVars, OF absorb] by simp
  have fn_abs: "fmmap (apply_subst_to_funinfo ?s) (TE_Functions env)
              = TE_Functions env"
    using arg_cong[where f = TE_Functions, OF absorb] by simp
  have dc_abs: "fmmap (apply_subst_to_datactor ?s) (TE_DataCtors env)
              = TE_DataCtors env"
    using arg_cong[where f = TE_DataCtors, OF absorb] by simp
  show ?thesis
    by (rule CoreTyEnv.equality)
       (simp_all add: apply_subst_to_module_env_def module_body_env_for_def
                      locals_id ret_id gv_abs fn_abs dc_abs)
qed

(* The body env, used as both source and target, satisfies the substitution
   engine's side conditions - the analogue of
   elab_decls_invariant_module_env_subst_ok at a function's body env. Its
   tyvar fields (the abstract types plus the function's own type parameters)
   avoid the substitution domain, and its declaration tables are the state
   env's, so the capture clauses are the same per-entry views. *)
lemma elab_decls_invariant_body_env_subst_ok:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and lk: "fmlookup (TE_Functions env) fname = Some info"
  shows "module_env_subst_ok (CM_TypeSubst m)
           (module_body_env_for env names info)
           (module_body_env_for env names info)"
    and "module_env_subst_runtime_ok (CM_TypeSubst m)
           (module_body_env_for env names info)
           (module_body_env_for env names info)"
proof -
  let ?s = "CM_TypeSubst m"
  let ?be = "module_body_env_for env names info"
  have env_eq: "env = module_context_env env0 m"
   and cap_env: "subst_names ?s |\<inter>| scope_bound_tyvars env elabEnv = {||}"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope_env unfolding tyenv_module_scope_def by blast
  have tv_disj: "TE_TypeVars env |\<inter>| fmdom ?s = {||}"
    using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
  have rtv_disj: "TE_RuntimeTypeVars env |\<inter>| fmdom ?s = {||}"
    using module_context_env_subst_disjoint(2)[of env0 m] env_eq by simp
  have dom_sub: "fmdom ?s |\<subseteq>| subst_names ?s"
    unfolding subst_names_def by simp
  have fi_cap: "subst_names ?s |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
    using empty_inter_subset[OF cap_env scope_bound_tyvars_fun_entry[OF lk]] .
  have fi_cap': "fset_of_list (FI_TyArgs info) |\<inter>| subst_names ?s = {||}"
    using fi_cap by (simp add: inf_commute)
  have fi_dom: "fset_of_list (FI_TyArgs info) |\<inter>| fmdom ?s = {||}"
    using empty_inter_subset[OF fi_cap' dom_sub] .
  have tv_be: "TE_TypeVars ?be |\<inter>| fmdom ?s = {||}"
    by (simp add: module_body_env_for_def abs_tv inf_sup_distrib2 tv_disj fi_dom)
  have dom_rtv: "fmdom ?s |\<inter>| TE_RuntimeTypeVars env = {||}"
    using rtv_disj by (simp add: inf_commute)
  have abs_rtv_disj: "(TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                        |\<inter>| fmdom ?s = {||}"
    using empty_inter_subset[OF dom_rtv inf_le2] by (simp add: inf_commute)
  have rtv_be: "TE_RuntimeTypeVars ?be |\<inter>| fmdom ?s = {||}"
    by (simp add: module_body_env_for_def inf_sup_distrib2 abs_rtv_disj fi_dom)
  show "module_env_subst_ok ?s ?be ?be"
    unfolding module_env_subst_ok_def
  proof (intro conjI allI impI)
    show "TE_Datatypes ?be = TE_Datatypes ?be" by simp
    show "TE_GhostDatatypes ?be = TE_GhostDatatypes ?be" by simp
  next
    fix n assume nT: "n |\<in>| TE_TypeVars ?be"
    then have "n |\<notin>| fmdom ?s"
      using tv_be by (metis fempty_iff finter_iff)
    then have "fmlookup ?s n = None" by (rule fmdom_notD)
    then show "case fmlookup ?s n of
                 Some ty' \<Rightarrow> is_well_kinded ?be ty'
               | None \<Rightarrow> n |\<in>| TE_TypeVars ?be"
      using nT by simp
  next
    fix funName inf
    assume "fmlookup (TE_Functions ?be) funName = Some inf"
    then have lk': "fmlookup (TE_Functions env) funName = Some inf"
      by (simp add: module_body_env_for_def)
    show "subst_names ?s |\<inter>| fset_of_list (FI_TyArgs inf) = {||}"
      using empty_inter_subset[OF cap_env scope_bound_tyvars_fun_entry[OF lk']] .
  next
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?be) ctorName = Some (dtName, tyVars, payload)"
    then have lk': "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
      by (simp add: module_body_env_for_def)
    show "subst_names ?s |\<inter>| fset_of_list tyVars = {||}"
      using empty_inter_subset[OF cap_env scope_bound_tyvars_ctor_entry[OF lk']] .
  qed
  show "module_env_subst_runtime_ok ?s ?be ?be"
    unfolding module_env_subst_runtime_ok_def
  proof (intro allI impI)
    fix n assume nR: "n |\<in>| TE_RuntimeTypeVars ?be"
    then have "n |\<notin>| fmdom ?s"
      using rtv_be by (metis fempty_iff finter_iff)
    then have "fmlookup ?s n = None" by (rule fmdom_notD)
    then show "case fmlookup ?s n of
                 Some ty' \<Rightarrow> is_runtime_type ?be ty'
               | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars ?be"
      using nR by simp
  qed
qed

(* Putting the two together: a function body typed in its body env stays
   typed after the module's substitution is applied to it - which is exactly
   what normalize_module does to recorded bodies. *)
lemma elab_decls_invariant_body_subst_typing:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and lk: "fmlookup (TE_Functions env) fname = Some info"
      and len: "length names = length (FI_TmArgs info)"
      and typed: "core_statement_list_type (module_body_env_for env names info)
                    (FI_Ghost info) body = Some envOut"
  shows "core_statement_list_type (module_body_env_for env names info)
           (FI_Ghost info)
           (apply_subst_to_statement_list (CM_TypeSubst m) body) \<noteq> None"
proof -
  let ?s = "CM_TypeSubst m"
  let ?be = "module_body_env_for env names info"
  have wf: "tyenv_well_formed env"
    using inv unfolding elab_decls_invariant_def by blast
  have wf_be: "tyenv_well_formed ?be"
    using module_body_env_for_well_formed[OF wf lk len] .
  have ok: "module_env_subst_ok ?s ?be ?be"
   and rt_ok: "module_env_subst_runtime_ok ?s ?be ?be"
    using elab_decls_invariant_body_env_subst_ok[OF inv lk] by blast+
  have "core_statement_list_type (apply_subst_to_module_env ?s ?be ?be)
          (FI_Ghost info) (apply_subst_to_statement_list ?s body)
        = Some (apply_subst_to_module_env ?s ?be envOut)"
    using core_statement_list_type_subst_module_env[OF typed wf_be ok] rt_ok
    by blast
  then show ?thesis
    using elab_decls_invariant_body_env_absorb[OF inv lk] by simp
qed


(* -------------------------------------------------------------------------- *)
(* Correctness of body elaboration                                            *)
(* -------------------------------------------------------------------------- *)

(* Elaborating a function's body (when present) produces a statement list
   that typechecks in the body env - the same env in which the module-level
   check will re-check the recorded body. The contracts are elaborated only
   to flag errors and are dropped, so only their success matters here. The
   entry conditions of the statement-elaborator theorem hold at the body env:
   well-formedness by module_body_env_for_well_formed, metavariable freshness
   at counter 0 from the invariant's two freshness conjuncts (the body
   counter restarts at 0), and the ghost/proof-goal fields are set directly
   by module_body_env_for. *)
lemma elab_fun_body_and_contracts_correct:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and lk: "fmlookup (TE_Functions env) fname = Some funInfo"
      and tyargs: "FI_TyArgs funInfo = DF_TyArgs df"
      and ghost_eq: "FI_Ghost funInfo = DF_Ghost df"
      and len: "length (map (\<lambda>(n, _, _). n) (DF_TmArgs df))
                  = length (FI_TmArgs funInfo)"
      and void_ret: "DF_ReturnType df = None \<Longrightarrow>
                       FI_ReturnType funInfo = CoreTy_Record []"
      and elab: "elab_fun_body_and_contracts env elabEnv df funInfo = Inr bodyOpt"
  shows "case bodyOpt of
           None \<Rightarrow> True
         | Some coreBody \<Rightarrow>
             core_statement_list_type
               (module_body_env_for env (map (\<lambda>(n, _, _). n) (DF_TmArgs df)) funInfo)
               (FI_Ghost funInfo) coreBody \<noteq> None"
proof -
  let ?be = "module_body_env_for env (map (\<lambda>(n, _, _). n) (DF_TmArgs df)) funInfo"
  let ?bodyEE = "elabEnv \<lparr> EE_Typedefs := tyvar_typedef_entries (DF_TyArgs df)
                                            (EE_Typedefs elabEnv),
                           EE_CurrentFunctionVoid := (DF_ReturnType df = None) \<rparr>"
  let ?postEnv = "(if DF_ReturnType df = None then ?be
                   else vardecl_add_local ?be Ghost ''return'' (FI_ReturnType funInfo))"
  have wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and mv_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and mv_fn: "\<forall>fname inf. fmlookup (TE_Functions env) fname = Some inf \<longrightarrow>
                 list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope_env unfolding tyenv_module_scope_def by blast
  \<comment> \<open>Entry conditions at the body env.\<close>
  have wf_be: "tyenv_well_formed ?be"
    using module_body_env_for_well_formed[OF wf lk len] .
  have td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using eewf unfolding elabenv_well_formed_def by blast
  have td_grow: "typedefs_well_formed ?be (EE_Typedefs elabEnv)"
    by (rule typedefs_well_formed_mono[OF td])
       (simp_all add: module_body_env_for_def abs_tv)
  have fi_sub: "fset_of_list (DF_TyArgs df) |\<subseteq>| TE_TypeVars ?be"
    unfolding tyargs [symmetric] by (simp add: module_body_env_for_def)
  have td_be: "typedefs_well_formed ?be
                 (tyvar_typedef_entries (DF_TyArgs df) (EE_Typedefs elabEnv))"
    using typedefs_well_formed_tyvar_entries[OF td_grow fi_sub] .
  have eewf_be: "elabenv_well_formed ?be ?bodyEE"
    unfolding elabenv_well_formed_def
  proof (intro conjI allI impI)
    show "typedefs_well_formed ?be (EE_Typedefs ?bodyEE)"
      using td_be by simp
  next
    have "nullary_data_ctors_consistent env elabEnv"
      using eewf unfolding elabenv_well_formed_def by blast
    then show "nullary_data_ctors_consistent ?be ?bodyEE"
      unfolding nullary_data_ctors_consistent_def
      by (simp add: module_body_env_for_def)
  next
    assume "EE_CurrentFunctionVoid ?bodyEE"
    then have "DF_ReturnType df = None" by simp
    then show "TE_ReturnType ?be = CoreTy_Record []"
      using void_ret by (simp add: module_body_env_for_def)
  qed
  have mv_be: "\<forall>n. n |\<in>| TE_TypeVars ?be \<longrightarrow> tyvar_fresh_ok n 0"
  proof (intro allI impI)
    fix n assume "n |\<in>| TE_TypeVars ?be"
    then have "n |\<in>| TE_TypeVars env \<or> n |\<in>| fset_of_list (FI_TyArgs funInfo)"
      by (auto simp: module_body_env_for_def abs_tv)
    moreover have "list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs funInfo)"
      using mv_fn lk by blast
    ultimately show "tyvar_fresh_ok n 0"
      using mv_tv by (auto simp: list_all_iff fset_of_list_elem)
  qed
  have gh_be: "TE_FunctionGhost ?be = Ghost \<longrightarrow> DF_Ghost df = Ghost"
    by (simp add: module_body_env_for_def ghost_eq)
  have pg_be: "DF_Ghost df = NotGhost \<longrightarrow> TE_ProofGoal ?be = None"
    by (simp add: module_body_env_for_def)
  \<comment> \<open>Peel the contracts (opaquely) and dispatch on the body.\<close>
  from elab obtain k where
    con: "elab_fun_contracts ?be ?postEnv ?bodyEE (DF_Attributes df) 0 = Inr k"
    unfolding elab_fun_body_and_contracts_def Let_def
    by (cases "elab_fun_contracts ?be ?postEnv ?bodyEE (DF_Attributes df) 0") auto
  show ?thesis
  proof (cases "DF_Body df")
    case None
    then have "bodyOpt = None"
      using elab con unfolding elab_fun_body_and_contracts_def Let_def
      by (simp add: None)
    then show ?thesis by simp
  next
    case (Some body)
    from elab con obtain coreBody envOut mv' where
      elabS: "elab_statement_list ?be ?bodyEE (DF_Ghost df) body 0
                = Inr (coreBody, envOut, mv')" and
      bodyOpt_eq: "bodyOpt = Some coreBody"
      unfolding elab_fun_body_and_contracts_def Let_def
      by (cases "elab_statement_list ?be ?bodyEE (DF_Ghost df) body 0")
         (auto simp: Some split: prod.splits)
    have typed: "core_statement_list_type ?be (DF_Ghost df) coreBody = Some envOut"
      by (rule elab_statement_list_correct[OF elabS wf_be eewf_be mv_be gh_be pg_be])
    show ?thesis
      unfolding bodyOpt_eq using typed by (simp add: ghost_eq)
  qed
qed


(* -------------------------------------------------------------------------- *)
(* The invariant step for defining a function                                 *)
(* -------------------------------------------------------------------------- *)

(* Recording a definition for an already-declared function (only CM_Functions
   changes). The recorded body is "born resolved": the normalized module
   applies the substitution to it, and the body-env substitution engine shows
   the substituted body still typechecks. *)
lemma elab_decls_invariant_define_function:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and lk: "fmlookup (TE_Functions env) name = Some funInfo"
      and len: "length paramNames = length (FI_TmArgs funInfo)"
      and dst: "distinct paramNames"
      and body_ok: "case bodyOpt of
                      None \<Rightarrow> True
                    | Some coreBody \<Rightarrow>
                        core_statement_list_type
                          (module_body_env_for env paramNames funInfo)
                          (FI_Ghost funInfo) coreBody \<noteq> None"
  shows "elab_decls_invariant env0 ownAbstract env elabEnv
           (m \<lparr> CM_Functions := fmupd name \<lparr> CF_Args = paramNames,
                                             CF_Body = bodyOpt \<rparr>
                                      (CM_Functions m) \<rparr>)"
proof -
  let ?m' = "m \<lparr> CM_Functions := fmupd name \<lparr> CF_Args = paramNames,
                                              CF_Body = bodyOpt \<rparr>
                                       (CM_Functions m) \<rparr>"
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and own_disj: "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and swk: "typesubst_well_kinded env (CM_TypeSubst m)"
   and dom_own: "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract"
   and dom_td: "fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs elabEnv)"
   and cap_env: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
   and mv_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and mv_fn: "\<forall>fname inf. fmlookup (TE_Functions env) fname = Some inf \<longrightarrow>
                 list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)"
   and gwt: "module_globals_well_typed env (CM_GlobalVars (normalize_module m))"
   and fwt: "module_functions_well_typed env (CM_Functions (normalize_module m))"
    using inv unfolding elab_decls_invariant_def by blast+
  have mce_same: "module_context_env env0 ?m' = module_context_env env0 m"
    unfolding module_context_env_def by simp
  have minv': "core_module_invariant ?m'"
    using minv
    unfolding core_module_invariant_def capture_avoiding_def
              module_ghost_subsets_ok_def tyenv_module_scope_def
    by simp
  \<comment> \<open>The new normalized functions map: the substituted body joins the old
      normalized entries.\<close>
  have norm_fns: "CM_Functions (normalize_module ?m')
                = fmupd name \<lparr> CF_Args = paramNames,
                               CF_Body = map_option
                                 (apply_subst_to_statement_list (CM_TypeSubst m))
                                 bodyOpt \<rparr>
                        (CM_Functions (normalize_module m))"
    by (simp add: normalize_module_def fmmap_fmupd)
  \<comment> \<open>The new entry's (substituted) body typechecks in its body env.\<close>
  have body': "case map_option (apply_subst_to_statement_list (CM_TypeSubst m)) bodyOpt of
                 None \<Rightarrow> True
               | Some body \<Rightarrow>
                   core_statement_list_type
                     (module_body_env_for env paramNames funInfo)
                     (FI_Ghost funInfo) body \<noteq> None"
  proof (cases bodyOpt)
    case None
    then show ?thesis by simp
  next
    case (Some coreBody)
    then have ne: "core_statement_list_type
                     (module_body_env_for env paramNames funInfo)
                     (FI_Ghost funInfo) coreBody \<noteq> None"
      using body_ok by simp
    then obtain envOut where
      typed: "core_statement_list_type
                (module_body_env_for env paramNames funInfo)
                (FI_Ghost funInfo) coreBody = Some envOut"
      by (cases "core_statement_list_type
                   (module_body_env_for env paramNames funInfo)
                   (FI_Ghost funInfo) coreBody") auto
    show ?thesis
      using elab_decls_invariant_body_subst_typing[OF inv lk len typed]
      by (simp add: Some)
  qed
  have fwt': "module_functions_well_typed env (CM_Functions (normalize_module ?m'))"
    unfolding norm_fns module_functions_well_typed_def
  proof (intro allI impI)
    fix n f
    assume lkf: "fmlookup
                   (fmupd name \<lparr> CF_Args = paramNames,
                                 CF_Body = map_option
                                   (apply_subst_to_statement_list (CM_TypeSubst m))
                                   bodyOpt \<rparr>
                          (CM_Functions (normalize_module m))) n = Some f"
    show "\<exists>info. fmlookup (TE_Functions env) n = Some info \<and>
                 length (CF_Args f) = length (FI_TmArgs info) \<and>
                 distinct (CF_Args f) \<and>
                 (case CF_Body f of
                    None \<Rightarrow> True
                  | Some body \<Rightarrow>
                      core_statement_list_type
                        (module_body_env_for env (CF_Args f) info)
                        (FI_Ghost info) body \<noteq> None)"
    proof (cases "n = name")
      case True
      then have f_eq: "f = \<lparr> CF_Args = paramNames,
                             CF_Body = map_option
                               (apply_subst_to_statement_list (CM_TypeSubst m))
                               bodyOpt \<rparr>"
        using lkf by simp
      show ?thesis
      proof (intro exI[of _ funInfo] conjI)
        show "fmlookup (TE_Functions env) n = Some funInfo"
          using lk True by simp
        show "length (CF_Args f) = length (FI_TmArgs funInfo)"
          using len by (simp add: f_eq)
        show "distinct (CF_Args f)"
          using dst by (simp add: f_eq)
        show "case CF_Body f of
                None \<Rightarrow> True
              | Some body \<Rightarrow>
                  core_statement_list_type
                    (module_body_env_for env (CF_Args f) funInfo)
                    (FI_Ghost funInfo) body \<noteq> None"
          using body' by (simp add: f_eq option.case_eq_if)
      qed
    next
      case False
      then have "fmlookup (CM_Functions (normalize_module m)) n = Some f"
        using lkf by simp
      then show ?thesis
        using fwt unfolding module_functions_well_typed_def by blast
    qed
  qed
  have glb_same: "CM_GlobalVars (normalize_module ?m')
                = CM_GlobalVars (normalize_module m)"
    by (simp add: normalize_module_def)
  show ?thesis
    unfolding elab_decls_invariant_def
  proof (intro conjI)
    show "elab_context_ok env0 ownAbstract" using ctx .
    show "env = module_context_env env0 ?m'" using env_eq mce_same by simp
    show "core_module_invariant ?m'" using minv' .
    show "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}" using own_disj by simp
    show "tyenv_well_formed env" using wf .
    show "elabenv_well_formed env elabEnv" using eewf .
    show "typesubst_well_kinded env (CM_TypeSubst ?m')" using swk by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| ownAbstract" using dom_own by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| fmdom (EE_Typedefs elabEnv)" using dom_td by simp
    show "subst_names (CM_TypeSubst ?m') |\<inter>| scope_bound_tyvars env elabEnv = {||}"
      using cap_env by simp
    show "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0" using mv_tv .
    show "\<forall>fname inf. fmlookup (TE_Functions env) fname = Some inf \<longrightarrow>
            list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)" using mv_fn .
    show "module_globals_well_typed env (CM_GlobalVars (normalize_module ?m'))"
      using gwt unfolding glb_same .
    show "module_functions_well_typed env (CM_Functions (normalize_module ?m'))"
      using fwt' .
  qed
qed


(* -------------------------------------------------------------------------- *)
(* The function-declaration dispatcher                                        *)
(* -------------------------------------------------------------------------- *)

(* The elimination rule for elab_function_decl success: one case per shape of
   the result (a definition of a previously-declared function, or a fresh
   declaration - possibly with a body). Each case names the elaborated
   signature and body, records the guards that must have passed, and states
   the defining equations of the result. *)
lemma elab_function_decl_Inr_elim:
  assumes ok: "elab_function_decl env elabEnv m df = Inr (env', elabEnv', m')"
  obtains (Define) funInfo bodyOpt where
    "first_duplicate_name (\<lambda>x. x) (DF_TyArgs df) = None"
    "first_duplicate_name (\<lambda>(n, _, _). n) (DF_TmArgs df) = None"
    "\<not> binder_captures env m (DF_TyArgs df)"
    "\<not> (DF_Extern df \<and> DF_Body df \<noteq> None)"
    "elab_fun_signature env elabEnv df = Inr funInfo"
    "fmlookup (TE_Functions env) (DF_Name df) = Some funInfo"
    "DF_Extern df \<or> DF_Body df \<noteq> None"
    "DF_Name df |\<notin>| fmdom (CM_Functions m)"
    "(DF_Name df |\<in>| EE_VoidFunctions elabEnv) = (DF_ReturnType df = None)"
    "elab_fun_body_and_contracts env elabEnv df funInfo = Inr bodyOpt"
    "env' = env"
    "elabEnv' = elabEnv"
    "m' = m \<lparr> CM_Functions :=
                fmupd (DF_Name df)
                      \<lparr> CF_Args = map (\<lambda>(n, _, _). n) (DF_TmArgs df),
                        CF_Body = bodyOpt \<rparr>
                      (CM_Functions m) \<rparr>"
  | (Declare) funInfo bodyOpt where
    "first_duplicate_name (\<lambda>x. x) (DF_TyArgs df) = None"
    "first_duplicate_name (\<lambda>(n, _, _). n) (DF_TmArgs df) = None"
    "\<not> binder_captures env m (DF_TyArgs df)"
    "\<not> (DF_Extern df \<and> DF_Body df \<noteq> None)"
    "elab_fun_signature env elabEnv df = Inr funInfo"
    "fmlookup (TE_Functions env) (DF_Name df) = None"
    "\<not> term_name_in_scope env (DF_Name df)"
    "elab_fun_body_and_contracts
       (tyenv_add_function (DF_Name df) funInfo env)
       (if DF_ReturnType df = None
        then elabEnv \<lparr> EE_VoidFunctions :=
               finsert (DF_Name df) (EE_VoidFunctions elabEnv) \<rparr>
        else elabEnv)
       df funInfo = Inr bodyOpt"
    "env' = tyenv_add_function (DF_Name df) funInfo env"
    "elabEnv' = (if DF_ReturnType df = None
                 then elabEnv \<lparr> EE_VoidFunctions :=
                        finsert (DF_Name df) (EE_VoidFunctions elabEnv) \<rparr>
                 else elabEnv)"
    "m' = (if DF_Extern df \<or> DF_Body df \<noteq> None
           then m \<lparr> CM_TyEnv := tyenv_add_function (DF_Name df) funInfo (CM_TyEnv m),
                    CM_Functions :=
                      fmupd (DF_Name df)
                            \<lparr> CF_Args = map (\<lambda>(n, _, _). n) (DF_TmArgs df),
                              CF_Body = bodyOpt \<rparr>
                            (CM_Functions m) \<rparr>
           else m \<lparr> CM_TyEnv := tyenv_add_function (DF_Name df) funInfo
                                  (CM_TyEnv m) \<rparr>)"
proof -
  \<comment> \<open>Peel the guards and the signature one at a time (auto with the full
      split set loops on this definition).\<close>
  have g1: "first_duplicate_name (\<lambda>x. x) (DF_TyArgs df) = None"
    using ok unfolding elab_function_decl_def Let_def
    by (cases "first_duplicate_name (\<lambda>x. x) (DF_TyArgs df)") auto
  have g2: "first_duplicate_name (\<lambda>(n, _, _). n) (DF_TmArgs df) = None"
    using ok unfolding elab_function_decl_def Let_def
    by (cases "first_duplicate_name (\<lambda>(n, _, _). n) (DF_TmArgs df)") (auto simp: g1)
  have g3: "\<not> binder_captures env m (DF_TyArgs df)"
    using ok unfolding elab_function_decl_def Let_def
    by (cases "binder_captures env m (DF_TyArgs df)") (auto simp: g1 g2)
  have g4: "\<not> (DF_Extern df \<and> DF_Body df \<noteq> None)"
    using ok unfolding elab_function_decl_def Let_def
    by (cases "DF_Extern df \<and> DF_Body df \<noteq> None") (auto simp: g1 g2 g3)
  \<comment> \<open>The same guard in the simplifier's normal form for the body option
      ("\<noteq> None" normalizes to an existential, so g4 itself does not fire as
      a rewrite on the normalized elaborator equation).\<close>
  have g4': "\<not> (DF_Extern df \<and> (\<exists>y. DF_Body df = Some y))"
    using g4 by simp
  from ok obtain funInfo where
    sig: "elab_fun_signature env elabEnv df = Inr funInfo"
    unfolding elab_function_decl_def Let_def
    by (cases "elab_fun_signature env elabEnv df") (auto simp: g1 g2 g3 g4 g4')
  show thesis
  proof (cases "fmlookup (TE_Functions env) (DF_Name df)")
    case (Some declInfo)
    from ok obtain bodyOpt where
      isdef: "DF_Extern df \<or> DF_Body df \<noteq> None" and
      nd: "DF_Name df |\<notin>| fmdom (CM_Functions m)" and
      fi_eq: "funInfo = declInfo" and
      vd: "(DF_Name df |\<in>| EE_VoidFunctions elabEnv) = (DF_ReturnType df = None)" and
      elabB: "elab_fun_body_and_contracts env elabEnv df funInfo = Inr bodyOpt" and
      eq1: "env' = env" and
      eq2: "elabEnv' = elabEnv" and
      eq3: "m' = m \<lparr> CM_Functions :=
                       fmupd (DF_Name df)
                             \<lparr> CF_Args = map (\<lambda>(n, _, _). n) (DF_TmArgs df),
                               CF_Body = bodyOpt \<rparr>
                             (CM_Functions m) \<rparr>"
      unfolding elab_function_decl_def Let_def
      by (cases "elab_fun_body_and_contracts env elabEnv df funInfo")
         (auto simp: g1 g2 g3 g4 g4' sig Some split: if_splits)
    have lk: "fmlookup (TE_Functions env) (DF_Name df) = Some funInfo"
      using Some fi_eq by simp
    show thesis
      by (rule Define[OF g1 g2 g3 g4 sig lk isdef nd vd elabB eq1 eq2 eq3])
  next
    case None
    have notin: "\<not> term_name_in_scope env (DF_Name df)"
      using ok unfolding elab_function_decl_def Let_def
      by (cases "term_name_in_scope env (DF_Name df)")
         (auto simp: g1 g2 g3 g4 g4' sig None)
    let ?env1 = "tyenv_add_function (DF_Name df) funInfo env"
    let ?ee1 = "(if DF_ReturnType df = None
                 then elabEnv \<lparr> EE_VoidFunctions :=
                        finsert (DF_Name df) (EE_VoidFunctions elabEnv) \<rparr>
                 else elabEnv)"
    from ok obtain bodyOpt where
      elabB: "elab_fun_body_and_contracts ?env1 ?ee1 df funInfo = Inr bodyOpt" and
      eq1: "env' = ?env1" and
      eq2: "elabEnv' = ?ee1" and
      eq3: "m' = (if DF_Extern df \<or> DF_Body df \<noteq> None
                  then m \<lparr> CM_TyEnv := tyenv_add_function (DF_Name df) funInfo
                                         (CM_TyEnv m),
                           CM_Functions :=
                             fmupd (DF_Name df)
                                   \<lparr> CF_Args = map (\<lambda>(n, _, _). n) (DF_TmArgs df),
                                     CF_Body = bodyOpt \<rparr>
                                   (CM_Functions m) \<rparr>
                  else m \<lparr> CM_TyEnv := tyenv_add_function (DF_Name df) funInfo
                                         (CM_TyEnv m) \<rparr>)"
      unfolding elab_function_decl_def Let_def
      by (cases "elab_fun_body_and_contracts ?env1 ?ee1 df funInfo")
         (auto simp: g1 g2 g3 g4 g4' sig None notin)
    show thesis
      by (rule Declare[OF g1 g2 g3 g4 sig None notin elabB eq1 eq2 eq3])
  qed
qed

(* The branches of elab_function_decl, dispatched to the step lemmas:
   declare-only, declare-and-define, and define-previously-declared. *)
lemma elab_function_decl_invariant:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and fresh: "list_all (\<lambda>n. tyvar_fresh_ok n 0) (DF_TyArgs df)"
      and elab: "elab_function_decl env elabEnv m df = Inr (env', elabEnv', m')"
  shows "elab_decls_invariant env0 ownAbstract env' elabEnv' m'"
proof -
  let ?name = "DF_Name df"
  let ?paramNames = "map (\<lambda>(n, _, _). n) (DF_TmArgs df)"
  have wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope_env unfolding tyenv_module_scope_def by blast
  have rtv_sub: "TE_RuntimeTypeVars env |\<subseteq>| TE_TypeVars env"
    using wf unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by blast
  have abs_rtv: "TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env
               = TE_RuntimeTypeVars env"
    unfolding abs_tv by (rule inf_absorb2[OF rtv_sub])
  \<comment> \<open>The guard facts and the elaborated signature, common to both cases of
      the elimination rule.\<close>
  from elab obtain funInfo where
    g1: "first_duplicate_name (\<lambda>x. x) (DF_TyArgs df) = None" and
    g2: "first_duplicate_name (\<lambda>(n, _, _). n) (DF_TmArgs df) = None" and
    g3: "\<not> binder_captures env m (DF_TyArgs df)" and
    sig: "elab_fun_signature env elabEnv df = Inr funInfo"
    by (cases rule: elab_function_decl_Inr_elim) blast+
  \<comment> \<open>Signature facts, and their module-scope (TE_AbstractTypes) forms.\<close>
  have td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using eewf unfolding elabenv_well_formed_def by blast
  note sigc = elab_fun_signature_correct[OF wf td sig]
  have len_pn: "length ?paramNames = length (FI_TmArgs funInfo)"
    by (simp add: sigc(4))
  have dst_pn: "distinct ?paramNames"
    using first_duplicate_name_None_implies_distinct[OF g2] .
  have dist_fi: "distinct (FI_TyArgs funInfo)"
    using first_duplicate_name_None_implies_distinct[OF g1] by (simp add: sigc(1))
  have fi_fresh: "list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs funInfo)"
    using fresh by (simp add: sigc(1))
  have bc: "fset_of_list (DF_TyArgs df)
              |\<inter>| (TE_TypeVars env |\<union>| subst_names (CM_TypeSubst m)) = {||}"
    using g3 unfolding binder_captures_def by simp
  have names_sub: "subst_names (CM_TypeSubst m)
                     |\<subseteq>| TE_TypeVars env |\<union>| subst_names (CM_TypeSubst m)"
    by simp
  have fi_cap: "subst_names (CM_TypeSubst m)
                  |\<inter>| fset_of_list (FI_TyArgs funInfo) = {||}"
    using empty_inter_subset[OF bc names_sub] by (simp add: sigc(1) inf_commute)
  have wk_args': "\<forall>ty \<in> fst ` set (FI_TmArgs funInfo).
                    is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                            |\<union>| fset_of_list (FI_TyArgs funInfo) \<rparr>) ty"
    using sigc(5) unfolding abs_tv sigc(1) .
  have wk_ret': "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                         |\<union>| fset_of_list (FI_TyArgs funInfo) \<rparr>)
                   (FI_ReturnType funInfo)"
    using sigc(6) unfolding abs_tv sigc(1) .
  have rt_p': "(\<forall>ty \<in> fst ` set (FI_TmArgs funInfo).
                  is_runtime_type
                    (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                             |\<union>| fset_of_list (FI_TyArgs funInfo),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                             |\<union>| fset_of_list (FI_TyArgs funInfo) \<rparr>) ty)
               \<and> is_runtime_type
                   (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                            |\<union>| fset_of_list (FI_TyArgs funInfo),
                          TE_RuntimeTypeVars :=
                            (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                            |\<union>| fset_of_list (FI_TyArgs funInfo) \<rparr>)
                   (FI_ReturnType funInfo)"
    if ng: "FI_Ghost funInfo = NotGhost"
  proof -
    have ng_df: "DF_Ghost df = NotGhost" using ng sigc(2) by simp
    show ?thesis
      by (metis abs_rtv abs_tv ng_df sigc(1,7))
  qed
  \<comment> \<open>Dispatch on whether the function is already declared.\<close>
  from elab show ?thesis
  proof (cases rule: elab_function_decl_Inr_elim)
    case (Define funInfo2 bodyOpt)
    \<comment> \<open>Definition of a previously-declared function: only CM_Functions
        changes, and the guards force the elaborated signature to coincide
        with the declared one.\<close>
    have fi: "funInfo2 = funInfo" using Define(5) sig by simp
    have lk: "fmlookup (TE_Functions env) ?name = Some funInfo"
      using Define(6) fi by simp
    have elabB: "elab_fun_body_and_contracts env elabEnv df funInfo = Inr bodyOpt"
      using Define(10) fi by simp
    have body_ok: "case bodyOpt of
                     None \<Rightarrow> True
                   | Some coreBody \<Rightarrow>
                       core_statement_list_type
                         (module_body_env_for env ?paramNames funInfo)
                         (FI_Ghost funInfo) coreBody \<noteq> None"
      by (rule elab_fun_body_and_contracts_correct
                 [OF inv lk sigc(1) sigc(2) len_pn sigc(8) elabB])
    have "elab_decls_invariant env0 ownAbstract env elabEnv
            (m \<lparr> CM_Functions := fmupd ?name \<lparr> CF_Args = ?paramNames,
                                                CF_Body = bodyOpt \<rparr>
                                       (CM_Functions m) \<rparr>)"
      by (rule elab_decls_invariant_define_function[OF inv lk len_pn dst_pn body_ok])
    then show ?thesis using Define(11) Define(12) Define(13) by simp
  next
    case (Declare funInfo2 bodyOpt)
    \<comment> \<open>Fresh declaration: add the function to the state env and the module's
        own type env, then (for a definition) record the body.\<close>
    have fi: "funInfo2 = funInfo" using Declare(5) sig by simp
    note notin = Declare(7)
    let ?env1 = "tyenv_add_function ?name funInfo env"
    let ?ee1 = "(if DF_ReturnType df = None
                 then elabEnv \<lparr> EE_VoidFunctions :=
                        finsert ?name (EE_VoidFunctions elabEnv) \<rparr>
                 else elabEnv)"
    let ?m1 = "m \<lparr> CM_TyEnv := tyenv_add_function ?name funInfo (CM_TyEnv m) \<rparr>"
    have elabB: "elab_fun_body_and_contracts ?env1 ?ee1 df funInfo = Inr bodyOpt"
      using Declare(8) fi by simp
    have inv1: "elab_decls_invariant env0 ownAbstract ?env1 elabEnv ?m1"
      by (rule elab_decls_invariant_add_function
                 [OF inv notin fi_cap fi_fresh dist_fi wk_args' wk_ret' rt_p'])
    have ee_td: "EE_Typedefs ?ee1 = EE_Typedefs elabEnv"
      by (cases "DF_ReturnType df = None") simp_all
    have ee_vc: "EE_NullaryDataCtors ?ee1 = EE_NullaryDataCtors elabEnv"
      by (cases "DF_ReturnType df = None") simp_all
    have ee_vd: "EE_CurrentFunctionVoid ?ee1 = EE_CurrentFunctionVoid elabEnv"
      by (cases "DF_ReturnType df = None") simp_all
    have inv2: "elab_decls_invariant env0 ownAbstract ?env1 ?ee1 ?m1"
      by (rule elab_decls_invariant_ee_cong[OF inv1 ee_td ee_vc ee_vd])
    have lk1: "fmlookup (TE_Functions ?env1) ?name = Some funInfo"
      by (simp add: tyenv_add_function_def)
    have body_ok: "case bodyOpt of
                     None \<Rightarrow> True
                   | Some coreBody \<Rightarrow>
                       core_statement_list_type
                         (module_body_env_for ?env1 ?paramNames funInfo)
                         (FI_Ghost funInfo) coreBody \<noteq> None"
      by (rule elab_fun_body_and_contracts_correct
                 [OF inv2 lk1 sigc(1) sigc(2) len_pn sigc(8) elabB])
    show ?thesis
    proof (cases "DF_Extern df \<or> DF_Body df \<noteq> None")
      case True
      have "elab_decls_invariant env0 ownAbstract ?env1 ?ee1
              (?m1 \<lparr> CM_Functions := fmupd ?name \<lparr> CF_Args = ?paramNames,
                                                    CF_Body = bodyOpt \<rparr>
                                           (CM_Functions ?m1) \<rparr>)"
        by (rule elab_decls_invariant_define_function[OF inv2 lk1 len_pn dst_pn body_ok])
      then show ?thesis using Declare(9) Declare(10) Declare(11) fi True by simp
    next
      case False
      then show ?thesis using inv2 Declare(9) Declare(10) Declare(11) fi by simp
    qed
  qed
qed

(* ---- Realizations (shared by datatypes and typedefs) ---- *)

(* -------------------------------------------------------------------------- *)
(* The updated substitution is a composition                                   *)
(* -------------------------------------------------------------------------- *)

(* apply_realization updates the module's substitution to
   "fmupd name target (fmmap (apply_subst {name |-> target}) sigma)": the new
   binding, with the old ranges rewritten through it. Since name is a type
   variable of the state env it is fresh for the old domain, and then this is
   exactly compose_subst of the singleton after sigma - which makes the whole
   compose-subst lemma inventory (TypeSubst.thy) available. *)

(* Adding a right-biased singleton whose key is fresh is just fmupd. *)
lemma fmadd_singleton_fresh:
  assumes "k |\<notin>| fmdom M"
  shows "fmupd k v fmempty ++\<^sub>f M = fmupd k v M"
proof (rule fmap_ext)
  fix n
  show "fmlookup (fmupd k v fmempty ++\<^sub>f M) n = fmlookup (fmupd k v M) n"
    using assms by (cases "n = k") auto
qed

lemma realization_subst_compose:
  assumes "name |\<notin>| fmdom \<sigma>"
  shows "fmupd name target (fmmap (apply_subst (fmupd name target fmempty)) \<sigma>)
           = compose_subst (fmupd name target fmempty) \<sigma>"
  unfolding compose_subst_def
  using fmadd_singleton_fresh
          [of name "fmmap (apply_subst (fmupd name target fmempty)) \<sigma>" target]
        assms
  by simp

(* The name set of the singleton substitution: its domain name plus the
   target's type variables (the fset realization_captures checks against). *)
lemma subst_names_singleton_subset:
  "subst_names (fmupd name target fmempty)
     |\<subseteq>| finsert name (fset_of_list (type_tyvars_list target))"
proof
  fix x assume "x |\<in>| subst_names (fmupd name target fmempty)"
  then have "x |\<in>| fmdom (fmupd name target fmempty)
           \<or> x \<in> subst_range_tyvars (fmupd name target fmempty)"
    by (simp add: subst_names_member)
  moreover have "fmran' (fmupd name target fmempty) = {target}"
    by (auto simp: fmlookup_ran'_iff split: if_splits)
  ultimately show "x |\<in>| finsert name (fset_of_list (type_tyvars_list target))"
    unfolding subst_range_tyvars_def
    by (auto simp: fset_of_list_elem set_type_tyvars_list)
qed

(* Composition can only mention names of the two operands. *)
lemma subst_names_compose_subset:
  "subst_names (compose_subst s2 s1) |\<subseteq>| subst_names s2 |\<union>| subst_names s1"
proof
  fix x assume "x |\<in>| subst_names (compose_subst s2 s1)"
  then have "x |\<in>| fmdom (compose_subst s2 s1)
           \<or> x \<in> subst_range_tyvars (compose_subst s2 s1)"
    by (simp add: subst_names_member)
  then show "x |\<in>| subst_names s2 |\<union>| subst_names s1"
  proof
    assume "x |\<in>| fmdom (compose_subst s2 s1)"
    then show ?thesis
      by (auto simp: fmdom_compose_subst subst_names_def)
  next
    assume "x \<in> subst_range_tyvars (compose_subst s2 s1)"
    then obtain ty where ty_in: "ty \<in> fmran' (compose_subst s2 s1)"
                     and x_ty: "x \<in> type_tyvars ty"
      unfolding subst_range_tyvars_def by auto
    from compose_subst_range[OF ty_in] show ?thesis
    proof
      assume "ty \<in> fmran' s2"
      then have "x \<in> subst_range_tyvars s2"
        using x_ty unfolding subst_range_tyvars_def by auto
      then show ?thesis by (auto simp: subst_names_member)
    next
      assume "\<exists>ty1 \<in> fmran' s1. ty = apply_subst s2 ty1"
      then obtain ty1 where ty1_in: "ty1 \<in> fmran' s1"
                        and ty_eq: "ty = apply_subst s2 ty1" by auto
      have "x \<in> (type_tyvars ty1 - fset (fmdom s2)) \<union> subst_range_tyvars s2"
        using x_ty apply_subst_tyvars_result[of s2 ty1] unfolding ty_eq by auto
      then have "x \<in> subst_range_tyvars s1 \<or> x \<in> subst_range_tyvars s2"
        using ty1_in unfolding subst_range_tyvars_def by auto
      then show ?thesis by (auto simp: subst_names_member)
    qed
  qed
qed

(* Composition lifts through the funinfo / datactor wrappers. *)
lemma apply_subst_to_funinfo_compose:
  "apply_subst_to_funinfo (compose_subst s2 s1) info
     = apply_subst_to_funinfo s2 (apply_subst_to_funinfo s1 info)"
  unfolding apply_subst_to_funinfo_def
  by (simp add: compose_subst_correct case_prod_beta o_def)

lemma apply_subst_to_datactor_compose:
  "apply_subst_to_datactor (compose_subst s2 s1) e
     = apply_subst_to_datactor s2 (apply_subst_to_datactor s1 e)"
  unfolding apply_subst_to_datactor_def
  by (simp add: compose_subst_correct split: prod.splits)

(* -------------------------------------------------------------------------- *)
(* Removing a type variable a type does not mention                            *)
(* -------------------------------------------------------------------------- *)

(* The realization drops name from the state env's type-variable fields; any
   type that does not mention name keeps its well-kindedness / runtime-ness.
   (These are the shrinking counterparts of is_well_kinded_mono /
   is_runtime_type_mono_rtv, via the transfer lemmas.) *)
lemma is_well_kinded_shrink_tyvar:
  assumes wk: "is_well_kinded env ty"
      and notin: "name \<notin> type_tyvars ty"
      and tv: "TE_TypeVars env' = TE_TypeVars env |-| {|name|}"
      and dt: "TE_Datatypes env' = TE_Datatypes env"
  shows "is_well_kinded env' ty"
proof (rule is_well_kinded_transfer[OF wk _ dt])
  have "type_tyvars ty \<subseteq> fset (TE_TypeVars env)"
    by (rule is_well_kinded_type_tyvars_subset[OF wk])
  then show "type_tyvars ty \<subseteq> fset (TE_TypeVars env')"
    unfolding tv using notin by auto
qed

lemma is_runtime_type_shrink_tyvar:
  assumes rt: "is_runtime_type env ty"
      and notin: "name \<notin> type_tyvars ty"
      and rtv: "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env |-| {|name|}"
      and gd: "TE_GhostDatatypes env' = TE_GhostDatatypes env"
  shows "is_runtime_type env' ty"
proof (rule is_runtime_type_transfer[OF rt _ gd])
  have "type_tyvars ty \<subseteq> fset (TE_RuntimeTypeVars env)"
    by (rule is_runtime_type_tyvars_subset[OF rt])
  then show "type_tyvars ty \<subseteq> fset (TE_RuntimeTypeVars env')"
    unfolding rtv using notin by auto
qed

(* -------------------------------------------------------------------------- *)
(* Small helpers                                                               *)
(* -------------------------------------------------------------------------- *)

(* Monotone variant of empty_inter_subset: disjointness descends to subsets
   on both sides. *)
lemma empty_inter_mono:
  fixes A B A' B' :: "string fset"
  assumes "A |\<subseteq>| A'"
      and "B |\<subseteq>| B'"
      and "A' |\<inter>| B' = {||}"
  shows "A |\<inter>| B = {||}"
  using assms by (metis inf_mono le_bot)

(* Per-entry view of the typedef summand of scope_bound_tyvars (mirror of
   scope_bound_tyvars_fun_entry / _ctor_entry). *)
lemma scope_bound_tyvars_typedef_entry:
  assumes lk: "fmlookup (EE_Typedefs elabEnv) tdName = Some (tyvars, ty)"
  shows "fset_of_list tyvars |\<subseteq>| scope_bound_tyvars env elabEnv"
proof
  fix x assume x_in: "x |\<in>| fset_of_list tyvars"
  have "(tyvars, ty) |\<in>| fmran (EE_Typedefs elabEnv)"
    using lk by (rule fmranI)
  then have "(\<lambda>(tyVars, _). fset_of_list tyVars) (tyvars, ty)
               |\<in>| (\<lambda>(tyVars, _). fset_of_list tyVars) |`| fmran (EE_Typedefs elabEnv)"
    by (rule fimageI)
  then have "fset_of_list tyvars
               |\<in>| (\<lambda>(tyVars, _). fset_of_list tyVars) |`| fmran (EE_Typedefs elabEnv)"
    by simp
  then have "x |\<in>| ffUnion ((\<lambda>(tyVars, _). fset_of_list tyVars)
                              |`| fmran (EE_Typedefs elabEnv))"
    unfolding fmember_ffUnion_iff using x_in by blast
  then show "x |\<in>| scope_bound_tyvars env elabEnv"
    unfolding scope_bound_tyvars_def by simp
qed

(* -------------------------------------------------------------------------- *)
(* The realization commutes with module_context_env                            *)
(* -------------------------------------------------------------------------- *)

(* Applying the singleton substitution to the state env and dropping name from
   its type-variable fields IS the state env of the module with the extended
   substitution: composing the table maps and absorbing the extra subtraction
   into the enlarged substitution domain. This is invariant conjunct 2 for the
   realization step. *)
lemma apply_realization_env_eq:
  assumes env_eq: "env = module_context_env env0 m"
      and name_dom: "name |\<notin>| fmdom (CM_TypeSubst m)"
  shows "(apply_subst_to_tyenv (fmupd name target fmempty) env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>
         = module_context_env env0
             (m \<lparr> CM_TypeSubst := fmupd name target
                    (fmmap (apply_subst (fmupd name target fmempty)) (CM_TypeSubst m)) \<rparr>)"
proof -
  let ?s = "fmupd name target fmempty"
  let ?\<sigma> = "CM_TypeSubst m"
  let ?\<sigma>' = "fmupd name target (fmmap (apply_subst ?s) ?\<sigma>)"
  have comp: "?\<sigma>' = compose_subst ?s ?\<sigma>"
    by (rule realization_subst_compose[OF name_dom])
  have pt: "\<And>ty. apply_subst ?\<sigma>' ty = apply_subst ?s (apply_subst ?\<sigma> ty)"
    unfolding comp by (rule compose_subst_correct)
  have pt_fi: "\<And>i. apply_subst_to_funinfo ?\<sigma>' i
                 = apply_subst_to_funinfo ?s (apply_subst_to_funinfo ?\<sigma> i)"
    unfolding comp by (rule apply_subst_to_funinfo_compose)
  have pt_dc: "\<And>e. apply_subst_to_datactor ?\<sigma>' e
                 = apply_subst_to_datactor ?s (apply_subst_to_datactor ?\<sigma> e)"
    unfolding comp by (rule apply_subst_to_datactor_compose)
  have map_ty: "fmmap (apply_subst ?s) (fmmap (apply_subst ?\<sigma>) X)
                  = fmmap (apply_subst ?\<sigma>') X"
    for X :: "(string, CoreType) fmap"
  proof (rule fmap_ext)
    fix k show "fmlookup (fmmap (apply_subst ?s) (fmmap (apply_subst ?\<sigma>) X)) k
              = fmlookup (fmmap (apply_subst ?\<sigma>') X) k"
      by (cases "fmlookup X k") (simp_all add: pt)
  qed
  have map_fi: "fmmap (apply_subst_to_funinfo ?s) (fmmap (apply_subst_to_funinfo ?\<sigma>) F)
                  = fmmap (apply_subst_to_funinfo ?\<sigma>') F"
    for F :: "(string, FunInfo) fmap"
  proof (rule fmap_ext)
    fix k show "fmlookup (fmmap (apply_subst_to_funinfo ?s)
                            (fmmap (apply_subst_to_funinfo ?\<sigma>) F)) k
              = fmlookup (fmmap (apply_subst_to_funinfo ?\<sigma>') F) k"
      by (cases "fmlookup F k") (simp_all add: pt_fi)
  qed
  have map_dc: "fmmap (apply_subst_to_datactor ?s) (fmmap (apply_subst_to_datactor ?\<sigma>) D)
                  = fmmap (apply_subst_to_datactor ?\<sigma>') D"
    for D :: "(string, string \<times> string list \<times> CoreType) fmap"
  proof (rule fmap_ext)
    fix k show "fmlookup (fmmap (apply_subst_to_datactor ?s)
                            (fmmap (apply_subst_to_datactor ?\<sigma>) D)) k
              = fmlookup (fmmap (apply_subst_to_datactor ?\<sigma>') D) k"
      by (cases "fmlookup D k") (simp_all add: pt_dc)
  qed
  have tv_alg: "(A |-| B) |-| {|name|} = A |-| finsert name B"
    for A B :: "string fset"
    by (rule fset_eqI) auto
  show ?thesis
    unfolding env_eq module_context_env_def apply_subst_to_tyenv_def
    by (simp add: map_ty map_fi map_dc tv_alg)
qed

(* -------------------------------------------------------------------------- *)
(* The extended substitution keeps core_module_invariant                       *)
(* -------------------------------------------------------------------------- *)

(* Idempotence: the new ranges (target, and the old ranges rewritten through
   the singleton) avoid the enlarged domain - target's type variables live in
   the state env's TE_TypeVars, which is disjoint from both the old domain and
   (by the no-self-reference check) from name itself; surviving old range
   variables avoid the old domain by the old idempotence and are not name
   (they survived the rewrite). *)
lemma apply_realization_idempotent:
  assumes idem: "idempotent_subst \<sigma>"
      and name_dom: "name |\<notin>| fmdom \<sigma>"
      and tgt_dom: "type_tyvars target \<inter> fset (fmdom \<sigma>) = {}"
      and noself: "name \<notin> type_tyvars target"
  shows "idempotent_subst (fmupd name target (fmmap (apply_subst (fmupd name target fmempty)) \<sigma>))"
proof -
  let ?s = "fmupd name target fmempty"
  let ?\<sigma>' = "fmupd name target (fmmap (apply_subst ?s) \<sigma>)"
  have ran_s: "fmran' ?s = {target}"
    by (auto simp: fmlookup_ran'_iff split: if_splits)
  have srt_s: "subst_range_tyvars ?s = type_tyvars target"
    unfolding subst_range_tyvars_def ran_s by simp
  have "subst_range_tyvars ?\<sigma>' \<inter> fset (fmdom ?\<sigma>') = {}"
  proof -
    have "c \<notin> fset (fmdom ?\<sigma>')" if c_in: "c \<in> subst_range_tyvars ?\<sigma>'" for c
    proof -
      from c_in obtain ty where ty_ran: "ty \<in> fmran' ?\<sigma>'"
                            and c_ty: "c \<in> type_tyvars ty"
        unfolding subst_range_tyvars_def by auto
      from ty_ran obtain k where lk: "fmlookup ?\<sigma>' k = Some ty"
        by (auto simp: fmlookup_ran'_iff)
      show ?thesis
      proof (cases "k = name")
        case True
        then have "ty = target" using lk by simp
        then have "c \<in> type_tyvars target" using c_ty by simp
        then show ?thesis using tgt_dom noself by auto
      next
        case False
        then obtain ty0 where lk0: "fmlookup \<sigma> k = Some ty0"
                          and ty_eq: "ty = apply_subst ?s ty0"
          using lk by (cases "fmlookup \<sigma> k") auto
        have c_dec: "c \<in> (type_tyvars ty0 - fset (fmdom ?s)) \<union> subst_range_tyvars ?s"
          using c_ty apply_subst_tyvars_result[of ?s ty0] unfolding ty_eq by auto
        show ?thesis
        proof (cases "c \<in> type_tyvars target")
          case True
          then show ?thesis using tgt_dom noself by auto
        next
          case False
          then have c_old: "c \<in> type_tyvars ty0" and c_name: "c \<noteq> name"
            using c_dec unfolding srt_s by auto
          have "ty0 \<in> fmran' \<sigma>" using lk0 by (auto simp: fmlookup_ran'_iff)
          then have "c \<in> subst_range_tyvars \<sigma>"
            using c_old unfolding subst_range_tyvars_def by auto
          then have "c \<notin> fset (fmdom \<sigma>)"
            using idem unfolding idempotent_subst_def by auto
          then show ?thesis using c_name by auto
        qed
      qed
    qed
    then show ?thesis by auto
  qed
  then show ?thesis unfolding idempotent_subst_def .
qed

(* The whole standing module invariant survives the realization: the module's
   own type environment is untouched, so only the substitution-facing clauses
   need work. Capture-avoidance is re-derived from the scope_bound_tyvars
   discipline (every CM_TyEnv m binder also appears in the state env, whose
   binders both the old substitution and the new binding avoid). *)
lemma apply_realization_module_invariant:
  assumes minv: "core_module_invariant m"
      and env_eq: "env = module_context_env env0 m"
      and name_dom: "name |\<notin>| fmdom (CM_TypeSubst m)"
      and name_m: "name |\<notin>| TE_TypeVars (CM_TyEnv m)"
      and tgt_dom: "type_tyvars target \<inter> fset (fmdom (CM_TypeSubst m)) = {}"
      and noself: "name \<notin> type_tyvars target"
      and cap: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
      and cap_new: "finsert name (fset_of_list (type_tyvars_list target))
                      |\<inter>| scope_bound_tyvars env elabEnv = {||}"
  shows "core_module_invariant
           (m \<lparr> CM_TypeSubst := fmupd name target
                  (fmmap (apply_subst (fmupd name target fmempty)) (CM_TypeSubst m)) \<rparr>)"
proof -
  let ?s = "fmupd name target fmempty"
  let ?\<sigma> = "CM_TypeSubst m"
  let ?\<sigma>' = "fmupd name target (fmmap (apply_subst ?s) ?\<sigma>)"
  let ?m' = "m \<lparr> CM_TypeSubst := ?\<sigma>' \<rparr>"
  have idem0: "idempotent_subst ?\<sigma>"
   and disj0: "fmdom ?\<sigma> |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and rtv0: "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
   and scope0m: "tyenv_module_scope (CM_TyEnv m)"
    using minv unfolding core_module_invariant_def by blast+
  have ghost0: "module_ghost_subsets_ok m"
    by (rule core_module_invariant_ghost_subsets_ok[OF minv])
  have comp: "?\<sigma>' = compose_subst ?s ?\<sigma>"
    by (rule realization_subst_compose[OF name_dom])
  have idem': "idempotent_subst ?\<sigma>'"
    by (rule apply_realization_idempotent[OF idem0 name_dom tgt_dom noself])
  have sn': "subst_names ?\<sigma>'
               |\<subseteq>| finsert name (fset_of_list (type_tyvars_list target))
                     |\<union>| subst_names ?\<sigma>"
    unfolding comp
    using subst_names_compose_subset[of ?s ?\<sigma>] subst_names_singleton_subset
    by auto
  have cap_all: "(finsert name (fset_of_list (type_tyvars_list target))
                    |\<union>| subst_names ?\<sigma>) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
    using cap cap_new by (simp add: inf_sup_distrib2)
  have cap': "capture_avoiding ?m'"
    unfolding capture_avoiding_def
  proof (intro conjI allI impI)
    fix funName info
    assume "fmlookup (TE_Functions (CM_TyEnv ?m')) funName = Some info"
    then have lkm0: "fmlookup (TE_Functions (CM_TyEnv m)) funName = Some info" by simp
    have lke: "fmlookup (TE_Functions env) funName
                 = Some (apply_subst_to_funinfo ?\<sigma> info)"
    proof -
      have fns: "TE_Functions env
              = fmmap (apply_subst_to_funinfo ?\<sigma>)
                      (TE_Functions env0 ++\<^sub>f TE_Functions (CM_TyEnv m))"
        unfolding env_eq module_context_env_def apply_subst_to_tyenv_def by simp
      show ?thesis
        by (simp add: fns lkm0 fmdomI[OF lkm0])
    qed
    have fi_sub: "fset_of_list (FI_TyArgs info) |\<subseteq>| scope_bound_tyvars env elabEnv"
      using scope_bound_tyvars_fun_entry[OF lke] by simp
    show "subst_names (CM_TypeSubst ?m') |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
      using empty_inter_mono[OF sn' fi_sub cap_all] by simp
  next
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors (CM_TyEnv ?m')) ctorName = Some (dtName, tyVars, payload)"
    then have lkm0: "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName
                       = Some (dtName, tyVars, payload)" by simp
    have lke: "fmlookup (TE_DataCtors env) ctorName
                 = Some (dtName, tyVars, apply_subst ?\<sigma> payload)"
    proof -
      have dcs: "TE_DataCtors env
              = fmmap (apply_subst_to_datactor ?\<sigma>)
                      (TE_DataCtors env0 ++\<^sub>f TE_DataCtors (CM_TyEnv m))"
        unfolding env_eq module_context_env_def apply_subst_to_tyenv_def by simp
      show ?thesis
        by (simp add: dcs lkm0 fmdomI[OF lkm0])
    qed
    have tvs_sub: "fset_of_list tyVars |\<subseteq>| scope_bound_tyvars env elabEnv"
      by (rule scope_bound_tyvars_ctor_entry[OF lke])
    show "subst_names (CM_TypeSubst ?m') |\<inter>| fset_of_list tyVars = {||}"
      using empty_inter_mono[OF sn' tvs_sub cap_all] by simp
  qed
  have dom_disj: "fmdom ?\<sigma>' |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
  proof (rule fset_eqI)
    fix x
    have "x |\<in>| fmdom ?\<sigma> \<Longrightarrow> x |\<notin>| TE_TypeVars (CM_TyEnv m)"
      using disj0 by (metis fempty_iff finter_iff)
    then show "x |\<in>| fmdom ?\<sigma>' |\<inter>| TE_TypeVars (CM_TyEnv m) \<longleftrightarrow> x |\<in>| {||}"
      using name_m by auto
  qed
  have ghost': "module_ghost_subsets_ok ?m'"
    using ghost0 unfolding module_ghost_subsets_ok_def by simp
  show ?thesis
    unfolding core_module_invariant_def
    using idem' cap' ghost' dom_disj rtv0 scope0m by simp
qed

(* -------------------------------------------------------------------------- *)
(* The realization does not grow the bound-type-parameter set                  *)
(* -------------------------------------------------------------------------- *)

(* The realized env/elabEnv pair binds no new type parameters: the funinfo /
   datactor substitutions keep FI_TyArgs / ctor tyvars, the rewritten typedef
   entries keep their parameter lists, and the new typedef entry for name has
   no parameters. *)
lemma apply_realization_scope_bound:
  assumes env'_eq: "env' = (apply_subst_to_tyenv (fmupd name target fmempty) env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>"
      and ee'_eq: "elabEnv' = elabEnv
           \<lparr> EE_Typedefs := fmupd name ([], target)
               (fmmap (\<lambda>(tyvars, ty). (tyvars, apply_subst (fmupd name target fmempty) ty))
                      (EE_Typedefs elabEnv)) \<rparr>"
  shows "scope_bound_tyvars env' elabEnv' |\<subseteq>| scope_bound_tyvars env elabEnv"
proof
  let ?s = "fmupd name target fmempty"
  fix x assume "x |\<in>| scope_bound_tyvars env' elabEnv'"
  then consider
      (fn) "x |\<in>| ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info))
                             |`| fmran (TE_Functions env'))"
    | (dc) "x |\<in>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars)
                             |`| fmran (TE_DataCtors env'))"
    | (td) "x |\<in>| ffUnion ((\<lambda>(tyVars, _). fset_of_list tyVars)
                             |`| fmran (EE_Typedefs elabEnv'))"
    unfolding scope_bound_tyvars_def by auto
  then show "x |\<in>| scope_bound_tyvars env elabEnv"
  proof cases
    case fn
    then obtain S where S_in: "S |\<in>| (\<lambda>info. fset_of_list (FI_TyArgs info))
                                       |`| fmran (TE_Functions env')"
                    and x_S: "x |\<in>| S"
      unfolding fmember_ffUnion_iff by auto
    then obtain i where i_ran: "i |\<in>| fmran (TE_Functions env')"
                    and S_eq: "S = fset_of_list (FI_TyArgs i)" by auto
    obtain k where lk: "fmlookup (TE_Functions env') k = Some i"
      using i_ran by (auto simp: fmlookup_ran_iff)
    have fe: "TE_Functions env' = fmmap (apply_subst_to_funinfo ?s) (TE_Functions env)"
      unfolding env'_eq apply_subst_to_tyenv_def by simp
    from lk obtain i0 where lk0: "fmlookup (TE_Functions env) k = Some i0"
        and i_eq: "i = apply_subst_to_funinfo ?s i0"
      unfolding fe by (cases "fmlookup (TE_Functions env) k") auto
    have "fset_of_list (FI_TyArgs i0) |\<subseteq>| scope_bound_tyvars env elabEnv"
      by (rule scope_bound_tyvars_fun_entry[OF lk0])
    then show ?thesis using x_S S_eq i_eq by auto
  next
    case dc
    then obtain S where S_in: "S |\<in>| (\<lambda>(_, tyVars, _). fset_of_list tyVars)
                                       |`| fmran (TE_DataCtors env')"
                    and x_S: "x |\<in>| S"
      unfolding fmember_ffUnion_iff by blast
    then obtain e where e_ran: "e |\<in>| fmran (TE_DataCtors env')"
                    and S_eq: "S = (\<lambda>(_, tyVars, _). fset_of_list tyVars) e" by auto
    obtain k where lk: "fmlookup (TE_DataCtors env') k = Some e"
      using e_ran by (auto simp: fmlookup_ran_iff)
    have dce: "TE_DataCtors env' = fmmap (apply_subst_to_datactor ?s) (TE_DataCtors env)"
      unfolding env'_eq apply_subst_to_tyenv_def by simp
    from lk obtain e0 where lk0: "fmlookup (TE_DataCtors env) k = Some e0"
        and e_eq: "e = apply_subst_to_datactor ?s e0"
      unfolding dce by (cases "fmlookup (TE_DataCtors env) k") auto
    obtain dt tvs pay where e0_eq: "e0 = (dt, tvs, pay)"
      using prod_cases3 by blast
    have "fset_of_list tvs |\<subseteq>| scope_bound_tyvars env elabEnv"
      by (rule scope_bound_tyvars_ctor_entry[OF lk0[unfolded e0_eq]])
    then show ?thesis using x_S S_eq e_eq e0_eq by auto
  next
    case td
    then obtain S where S_in: "S |\<in>| (\<lambda>(tyVars, _). fset_of_list tyVars)
                                       |`| fmran (EE_Typedefs elabEnv')"
                    and x_S: "x |\<in>| S"
      unfolding fmember_ffUnion_iff by auto
    then obtain e where e_ran: "e |\<in>| fmran (EE_Typedefs elabEnv')"
                    and S_eq: "S = (\<lambda>(tyVars, _). fset_of_list tyVars) e" by auto
    obtain k where lk: "fmlookup (EE_Typedefs elabEnv') k = Some e"
      using e_ran by (auto simp: fmlookup_ran_iff)
    show ?thesis
    proof (cases "k = name")
      case True
      then have "e = ([], target)" using lk unfolding ee'_eq by simp
      then have "S = {||}" using S_eq by simp
      then show ?thesis using x_S by simp
    next
      case False
      from lk False obtain tvs ty0
        where lk0: "fmlookup (EE_Typedefs elabEnv) k = Some (tvs, ty0)"
          and e_eq: "e = (tvs, apply_subst ?s ty0)"
        unfolding ee'_eq by (cases "fmlookup (EE_Typedefs elabEnv) k") auto
      have "fset_of_list tvs |\<subseteq>| scope_bound_tyvars env elabEnv"
        by (rule scope_bound_tyvars_typedef_entry[OF lk0])
      then show ?thesis using x_S S_eq e_eq by auto
    qed
  qed
qed

(* -------------------------------------------------------------------------- *)
(* The realized env as the engine's output                                     *)
(* -------------------------------------------------------------------------- *)

(* The realized state env is the module-level substitution engine's image of
   the old state env under the singleton substitution, with itself as the
   tyvar-supplying target: at module scope the extra fields the engine touches
   (locals, return type, proof goal) are all trivial. *)
lemma apply_realization_state_absorb:
  assumes env'_eq: "env' = (apply_subst_to_tyenv (fmupd name target fmempty) env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>"
      and scope_env: "tyenv_module_scope env"
  shows "apply_subst_to_module_env (fmupd name target fmempty) env' env = env'"
proof -
  have locals: "TE_LocalVars env = fmempty"
   and ret: "TE_ReturnType env = CoreTy_Record []"
   and goal_none: "TE_ProofGoal env = None"
    using scope_env unfolding tyenv_module_scope_def by simp_all
  show ?thesis
    by (rule CoreTyEnv.equality)
       (simp_all add: env'_eq apply_subst_to_module_env_def apply_subst_to_tyenv_def
                      locals ret goal_none)
qed

(* The engine's side conditions for that pass: name is covered by the
   singleton (its image target is well-kinded in the realized env), every
   other type variable survives, and the singleton's names avoid all bound
   type parameters (from the realization_captures check). *)
lemma apply_realization_subst_ok:
  assumes env'_eq: "env' = (apply_subst_to_tyenv (fmupd name target fmempty) env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>"
      and wk': "is_well_kinded env' target"
      and rt': "name |\<in>| TE_RuntimeTypeVars env \<Longrightarrow> is_runtime_type env' target"
      and cap_new: "finsert name (fset_of_list (type_tyvars_list target))
                      |\<inter>| scope_bound_tyvars env elabEnv = {||}"
  shows "module_env_subst_ok (fmupd name target fmempty) env' env"
    and "module_env_subst_runtime_ok (fmupd name target fmempty) env' env"
proof -
  let ?s = "fmupd name target fmempty"
  have sn_sub: "subst_names ?s
                  |\<subseteq>| finsert name (fset_of_list (type_tyvars_list target))"
    by (rule subst_names_singleton_subset)
  have tv_env': "TE_TypeVars env' = TE_TypeVars env |-| {|name|}"
   and rtv_env': "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env |-| {|name|}"
    unfolding env'_eq by simp_all
  have dt_env': "TE_Datatypes env' = TE_Datatypes env"
   and gd_env': "TE_GhostDatatypes env' = TE_GhostDatatypes env"
    unfolding env'_eq apply_subst_to_tyenv_def by simp_all
  show "module_env_subst_ok ?s env' env"
    unfolding module_env_subst_ok_def
  proof (intro conjI allI impI)
    show "TE_Datatypes env' = TE_Datatypes env" by (rule dt_env')
    show "TE_GhostDatatypes env' = TE_GhostDatatypes env" by (rule gd_env')
  next
    fix n assume nT: "n |\<in>| TE_TypeVars env"
    show "case fmlookup ?s n of
            Some ty' \<Rightarrow> is_well_kinded env' ty'
          | None \<Rightarrow> n |\<in>| TE_TypeVars env'"
    proof (cases "n = name")
      case True then show ?thesis using wk' by simp
    next
      case False
      then have "n |\<in>| TE_TypeVars env'"
        unfolding tv_env' using nT by simp
      with False show ?thesis by simp
    qed
  next
    fix funName info
    assume lk: "fmlookup (TE_Functions env) funName = Some info"
    show "subst_names ?s |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
      by (rule empty_inter_mono[OF sn_sub scope_bound_tyvars_fun_entry[OF lk] cap_new])
  next
    fix ctorName dtName tyVars payload
    assume lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
    show "subst_names ?s |\<inter>| fset_of_list tyVars = {||}"
      by (rule empty_inter_mono[OF sn_sub scope_bound_tyvars_ctor_entry[OF lk] cap_new])
  qed
  show "module_env_subst_runtime_ok ?s env' env"
    unfolding module_env_subst_runtime_ok_def
  proof (intro allI impI)
    fix n assume nR: "n |\<in>| TE_RuntimeTypeVars env"
    show "case fmlookup ?s n of
            Some ty' \<Rightarrow> is_runtime_type env' ty'
          | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars env'"
    proof (cases "n = name")
      case True then show ?thesis using rt' nR by simp
    next
      case False
      then have "n |\<in>| TE_RuntimeTypeVars env'"
        unfolding rtv_env' using nR by simp
      with False show ?thesis by simp
    qed
  qed
qed

(* -------------------------------------------------------------------------- *)
(* The rewritten typedef table stays well-formed                               *)
(* -------------------------------------------------------------------------- *)

lemma apply_realization_typedefs:
  assumes td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
      and env'_eq: "env' = (apply_subst_to_tyenv (fmupd name target fmempty) env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>"
      and wk': "is_well_kinded env' target"
      and cap_new: "finsert name (fset_of_list (type_tyvars_list target))
                      |\<inter>| scope_bound_tyvars env elabEnv = {||}"
  shows "typedefs_well_formed env'
           (fmupd name ([], target)
              (fmmap (\<lambda>(tyvars, ty). (tyvars, apply_subst (fmupd name target fmempty) ty))
                     (EE_Typedefs elabEnv)))"
proof -
  let ?s = "fmupd name target fmempty"
  have tv_env': "TE_TypeVars env' = TE_TypeVars env |-| {|name|}"
    unfolding env'_eq by simp
  have dt_env': "TE_Datatypes env' = TE_Datatypes env"
    unfolding env'_eq apply_subst_to_tyenv_def by simp
  have name_sb: "name |\<notin>| scope_bound_tyvars env elabEnv"
    using cap_new by (metis fempty_iff finsertCI finter_iff)
  show ?thesis
    unfolding typedefs_well_formed_def
  proof (intro allI impI)
    fix tdName tyvars targetTy
    assume lk: "fmlookup (fmupd name ([], target)
                   (fmmap (\<lambda>(tyvars, ty). (tyvars, apply_subst ?s ty))
                          (EE_Typedefs elabEnv))) tdName
                  = Some (tyvars, targetTy)"
    show "distinct tyvars
          \<and> is_well_kinded (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                     |\<union>| fset_of_list tyvars \<rparr>) targetTy"
    proof (cases "tdName = name")
      case True
      then have e: "tyvars = []" "targetTy = target" using lk by auto
      have "is_well_kinded (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                     |\<union>| fset_of_list tyvars \<rparr>) target"
        by (rule is_well_kinded_mono[OF wk']) auto
      then show ?thesis using e by simp
    next
      case False
      from lk False obtain ty0
        where lk0: "fmlookup (EE_Typedefs elabEnv) tdName = Some (tyvars, ty0)"
          and t_eq: "targetTy = apply_subst ?s ty0"
        by (cases "fmlookup (EE_Typedefs elabEnv) tdName") auto
      from td lk0 have d: "distinct tyvars"
          and wk0: "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env
                                            |\<union>| fset_of_list tyvars \<rparr>) ty0"
        unfolding typedefs_well_formed_def by blast+
      have "{|name|} |\<inter>| fset_of_list tyvars = {||}"
        by (rule empty_inter_mono[OF _ scope_bound_tyvars_typedef_entry[OF lk0] cap_new])
           auto
      then have name_tvs: "name |\<notin>| fset_of_list tyvars"
        by (metis fempty_iff finsertCI finter_iff)
      have wk1: "is_well_kinded (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                          |\<union>| fset_of_list tyvars \<rparr>)
                                (apply_subst ?s ty0)"
      proof (rule apply_subst_preserves_well_kinded[OF wk0])
        show "TE_Datatypes (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                     |\<union>| fset_of_list tyvars \<rparr>)
                = TE_Datatypes (env \<lparr> TE_TypeVars := TE_TypeVars env
                                        |\<union>| fset_of_list tyvars \<rparr>)"
          by (simp add: dt_env')
      next
        fix k assume kT: "k |\<in>| TE_TypeVars (env \<lparr> TE_TypeVars := TE_TypeVars env
                                                     |\<union>| fset_of_list tyvars \<rparr>)"
        show "case fmlookup ?s k of
                Some ty' \<Rightarrow> is_well_kinded (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                                     |\<union>| fset_of_list tyvars \<rparr>) ty'
              | None \<Rightarrow> k |\<in>| TE_TypeVars (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                                    |\<union>| fset_of_list tyvars \<rparr>)"
        proof (cases "k = name")
          case True
          have "is_well_kinded (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                         |\<union>| fset_of_list tyvars \<rparr>) target"
            by (rule is_well_kinded_mono[OF wk']) auto
          then show ?thesis using True by simp
        next
          case False
          then have "k |\<in>| TE_TypeVars env' |\<union>| fset_of_list tyvars"
            using kT unfolding tv_env' by auto
          with False show ?thesis by simp
        qed
      qed
      show ?thesis using d wk1 t_eq by simp
    qed
  qed
qed

(* -------------------------------------------------------------------------- *)
(* Nullary data constructors survive the payload rewrite                          *)
(* -------------------------------------------------------------------------- *)

(* A nullary constructor's unit payload is a substitution fixpoint, so realization
   preserves nullary-consistency. *)
lemma apply_realization_nullary_ctors:
  assumes vd: "nullary_data_ctors_consistent env elabEnv"
      and env'_eq: "env' = (apply_subst_to_tyenv (fmupd name target fmempty) env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>"
      and ee'_eq: "EE_NullaryDataCtors elabEnv' = EE_NullaryDataCtors elabEnv"
  shows "nullary_data_ctors_consistent env' elabEnv'"
proof -
  let ?s = "fmupd name target fmempty"
  show ?thesis
    unfolding nullary_data_ctors_consistent_def
  proof (intro allI impI)
    fix cname assume "cname |\<in>| EE_NullaryDataCtors elabEnv'"
    then have "cname |\<in>| EE_NullaryDataCtors elabEnv" using ee'_eq by simp
    then obtain dtName tyvars where
      lk: "fmlookup (TE_DataCtors env) cname = Some (dtName, tyvars, CoreTy_Record [])"
      using vd unfolding nullary_data_ctors_consistent_def by blast
    have lk': "fmlookup (TE_DataCtors env') cname
                 = Some (dtName, tyvars, CoreTy_Record [])"
      unfolding env'_eq apply_subst_to_tyenv_def by (simp add: lk)
    then show "\<exists>dtName tyvars. fmlookup (TE_DataCtors env') cname
                 = Some (dtName, tyvars, CoreTy_Record [])" by blast
  qed
qed

(* -------------------------------------------------------------------------- *)
(* Body envs under the realization                                             *)
(* -------------------------------------------------------------------------- *)

(* Substituting a recorded function's body env with the singleton, with the
   realized env's body env (built over the substituted signature) as the
   tyvar-supplying target, IS the realized body env - the commutation that
   lets the statement-level engine re-establish recorded bodies. *)
lemma apply_realization_body_collapse:
  assumes env'_eq: "env' = (apply_subst_to_tyenv (fmupd name target fmempty) env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>"
  shows "apply_subst_to_module_env (fmupd name target fmempty)
           (module_body_env_for env' names
              (apply_subst_to_funinfo (fmupd name target fmempty) info))
           (module_body_env_for env names info)
       = module_body_env_for env' names
           (apply_subst_to_funinfo (fmupd name target fmempty) info)"
proof -
  let ?s = "fmupd name target fmempty"
  let ?info' = "apply_subst_to_funinfo ?s info"
  have compF: "\<And>sb. fst \<circ> (\<lambda>(ty, y). (apply_subst sb ty, y)) = apply_subst sb \<circ> fst"
    by (rule ext) auto
  have compS: "\<And>sb. snd \<circ> (\<lambda>(ty, y). (apply_subst sb ty, y)) = snd"
    by (rule ext) auto
  have locals_eq: "fmmap (apply_subst ?s)
                     (fmap_of_list (zip names (map fst (FI_TmArgs info))))
                     = fmap_of_list (zip names (map fst (FI_TmArgs ?info')))"
  proof -
    have "fmmap (apply_subst ?s) (fmap_of_list (zip names (map fst (FI_TmArgs info))))
            = fmap_of_list (zip names (map (apply_subst ?s) (map fst (FI_TmArgs info))))"
      by (simp add: fmmap_fmap_of_list zip_map2[symmetric])
    also have "... = fmap_of_list (zip names (map fst (FI_TmArgs ?info')))"
      by (simp add: compF)
    finally show ?thesis .
  qed
  show ?thesis
    by (rule CoreTyEnv.equality)
       (simp_all add: apply_subst_to_module_env_def module_body_env_for_def
                      env'_eq apply_subst_to_tyenv_def locals_eq compS)
qed

(* The engine's side conditions at the body env: the body env's type variables
   are the ambient abstract types (name covered by the singleton, the rest
   surviving) plus the function's own type parameters (which avoid name by the
   capture discipline); the capture clauses are inherited from the enclosing
   env because the body env keeps its declaration tables. *)
lemma apply_realization_body_subst_ok:
  assumes env'_eq: "env' = (apply_subst_to_tyenv (fmupd name target fmempty) env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>"
      and abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
      and rtv_sub: "TE_RuntimeTypeVars env |\<subseteq>| TE_TypeVars env"
      and wk': "is_well_kinded env' target"
      and rt': "name |\<in>| TE_RuntimeTypeVars env \<Longrightarrow> is_runtime_type env' target"
      and name_fi: "name |\<notin>| fset_of_list (FI_TyArgs info)"
      and cap_new: "finsert name (fset_of_list (type_tyvars_list target))
                      |\<inter>| scope_bound_tyvars env elabEnv = {||}"
  shows "module_env_subst_ok (fmupd name target fmempty)
           (module_body_env_for env' names
              (apply_subst_to_funinfo (fmupd name target fmempty) info))
           (module_body_env_for env names info)"
    and "module_env_subst_runtime_ok (fmupd name target fmempty)
           (module_body_env_for env' names
              (apply_subst_to_funinfo (fmupd name target fmempty) info))
           (module_body_env_for env names info)"
proof -
  let ?s = "fmupd name target fmempty"
  let ?tb = "module_body_env_for env' names (apply_subst_to_funinfo ?s info)"
  let ?sb = "module_body_env_for env names info"
  have sn_sub: "subst_names ?s
                  |\<subseteq>| finsert name (fset_of_list (type_tyvars_list target))"
    by (rule subst_names_singleton_subset)
  have tv_env': "TE_TypeVars env' = TE_TypeVars env |-| {|name|}"
   and rtv_env': "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env |-| {|name|}"
   and abs_env': "TE_AbstractTypes env' = TE_AbstractTypes env |-| {|name|}"
    unfolding env'_eq by simp_all
  have dt_env': "TE_Datatypes env' = TE_Datatypes env"
   and gd_env': "TE_GhostDatatypes env' = TE_GhostDatatypes env"
    unfolding env'_eq apply_subst_to_tyenv_def by simp_all
  have abs_rtv: "TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env
                   = TE_RuntimeTypeVars env"
    unfolding abs_tv by (rule inf_absorb2[OF rtv_sub])
  have abs_rtv': "TE_AbstractTypes env' |\<inter>| TE_RuntimeTypeVars env'
                    = TE_RuntimeTypeVars env'"
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| TE_AbstractTypes env' |\<inter>| TE_RuntimeTypeVars env'
            \<longleftrightarrow> x |\<in>| TE_RuntimeTypeVars env'"
      unfolding abs_env' rtv_env' abs_tv using rtv_sub by auto
  qed
  have tv_tb: "TE_TypeVars ?tb
                 = (TE_TypeVars env |-| {|name|}) |\<union>| fset_of_list (FI_TyArgs info)"
    by (simp add: module_body_env_for_def abs_env' abs_tv)
  have tv_sb: "TE_TypeVars ?sb = TE_TypeVars env |\<union>| fset_of_list (FI_TyArgs info)"
    by (simp add: module_body_env_for_def abs_tv)
  have rtv_tb: "TE_RuntimeTypeVars ?tb
                  = (TE_RuntimeTypeVars env |-| {|name|})
                    |\<union>| (if FI_Ghost info = NotGhost
                          then fset_of_list (FI_TyArgs info) else {||})"
    by (simp add: module_body_env_for_def abs_rtv'[unfolded rtv_env'] rtv_env')
  have rtv_sb: "TE_RuntimeTypeVars ?sb
                  = TE_RuntimeTypeVars env
                    |\<union>| (if FI_Ghost info = NotGhost
                          then fset_of_list (FI_TyArgs info) else {||})"
    by (simp add: module_body_env_for_def abs_rtv)
  have dt_tb: "TE_Datatypes ?tb = TE_Datatypes env'"
   and dt_sb: "TE_Datatypes ?sb = TE_Datatypes env"
   and gd_tb: "TE_GhostDatatypes ?tb = TE_GhostDatatypes env'"
   and gd_sb: "TE_GhostDatatypes ?sb = TE_GhostDatatypes env"
    by (simp_all add: module_body_env_for_def)
  have wk_tb: "is_well_kinded ?tb target"
  proof (rule is_well_kinded_mono[OF wk'])
    show "fset (TE_TypeVars env') \<subseteq> fset (TE_TypeVars ?tb)"
      unfolding tv_tb tv_env' by auto
    show "\<And>k v. fmlookup (TE_Datatypes env') k = Some v
            \<Longrightarrow> fmlookup (TE_Datatypes ?tb) k = Some v"
      unfolding dt_tb by simp
  qed
  show "module_env_subst_ok ?s ?tb ?sb"
    unfolding module_env_subst_ok_def
  proof (intro conjI allI impI)
    show "TE_Datatypes ?tb = TE_Datatypes ?sb"
      unfolding dt_tb dt_sb by (rule dt_env')
    show "TE_GhostDatatypes ?tb = TE_GhostDatatypes ?sb"
      unfolding gd_tb gd_sb by (rule gd_env')
  next
    fix n assume nT: "n |\<in>| TE_TypeVars ?sb"
    show "case fmlookup ?s n of
            Some ty' \<Rightarrow> is_well_kinded ?tb ty'
          | None \<Rightarrow> n |\<in>| TE_TypeVars ?tb"
    proof (cases "n = name")
      case True then show ?thesis using wk_tb by simp
    next
      case False
      then have "n |\<in>| TE_TypeVars ?tb"
        using nT unfolding tv_tb tv_sb by auto
      with False show ?thesis by simp
    qed
  next
    fix funName finfo
    assume "fmlookup (TE_Functions ?sb) funName = Some finfo"
    then have lk: "fmlookup (TE_Functions env) funName = Some finfo"
      by (simp add: module_body_env_for_def)
    show "subst_names ?s |\<inter>| fset_of_list (FI_TyArgs finfo) = {||}"
      by (rule empty_inter_mono[OF sn_sub scope_bound_tyvars_fun_entry[OF lk] cap_new])
  next
    fix ctorName dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?sb) ctorName = Some (dtName, tyVars, payload)"
    then have lk: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
      by (simp add: module_body_env_for_def)
    show "subst_names ?s |\<inter>| fset_of_list tyVars = {||}"
      by (rule empty_inter_mono[OF sn_sub scope_bound_tyvars_ctor_entry[OF lk] cap_new])
  qed
  have rt_tb: "is_runtime_type ?tb target" if nR: "name |\<in>| TE_RuntimeTypeVars env"
  proof -
    have rt_env': "is_runtime_type env' target" using rt'[OF nR] .
    have "type_tyvars target \<subseteq> fset (TE_RuntimeTypeVars env')"
      by (rule is_runtime_type_tyvars_subset[OF rt_env'])
    then have tvs: "type_tyvars target \<subseteq> fset (TE_RuntimeTypeVars ?tb)"
      unfolding rtv_tb rtv_env' by auto
    show ?thesis
      by (rule is_runtime_type_transfer[OF rt_env' tvs gd_tb])
  qed
  show "module_env_subst_runtime_ok ?s ?tb ?sb"
    unfolding module_env_subst_runtime_ok_def
  proof (intro allI impI)
    fix n assume nR: "n |\<in>| TE_RuntimeTypeVars ?sb"
    show "case fmlookup ?s n of
            Some ty' \<Rightarrow> is_runtime_type ?tb ty'
          | None \<Rightarrow> n |\<in>| TE_RuntimeTypeVars ?tb"
    proof (cases "n = name")
      case True
      have nR0: "name |\<in>| TE_RuntimeTypeVars env"
        using nR name_fi unfolding rtv_sb True by (auto split: if_splits)
      show ?thesis using rt_tb[OF nR0] True by simp
    next
      case False
      then have "n |\<in>| TE_RuntimeTypeVars ?tb"
        using nR unfolding rtv_sb rtv_tb by (auto split: if_splits)
      with False show ?thesis by simp
    qed
  qed
qed

(* Recording a realization "name |-> target" of one of the module's own
   abstract types preserves the invariant, given the elaborator's checks:
   the target is well-kinded (in particular its type variables are in scope,
   hence disjoint from the substitution domain), does not mention the name
   being realized, is a runtime type if the abstract type was declared
   non-ghost, and neither the name nor the target's type variables collide
   with any bound type parameter in scope. *)
lemma apply_realization_invariant:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and own: "name |\<in>| ownAbstract"
      and tv: "name |\<in>| TE_TypeVars env"
      and wk: "is_well_kinded env target"
      and noself: "name \<notin> type_tyvars target"
      and rt_ok: "name |\<in>| TE_RuntimeTypeVars env \<longrightarrow> is_runtime_type env target"
      and nocap: "\<not> realization_captures env elabEnv name target"
      and res: "apply_realization name target env elabEnv m = (env', elabEnv', m')"
  shows "elab_decls_invariant env0 ownAbstract env' elabEnv' m'"
proof -
  let ?s = "fmupd name target fmempty"
  let ?\<sigma> = "CM_TypeSubst m"
  let ?\<sigma>' = "fmupd name target (fmmap (apply_subst ?s) ?\<sigma>)"

  \<comment> \<open>The three components of the result.\<close>
  have env'_eq: "env' = (apply_subst_to_tyenv ?s env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>"
   and ee'_eq: "elabEnv' = elabEnv
           \<lparr> EE_Typedefs := fmupd name ([], target)
               (fmmap (\<lambda>(tyvars, ty). (tyvars, apply_subst ?s ty))
                      (EE_Typedefs elabEnv)) \<rparr>"
   and m'_eq: "m' = m \<lparr> CM_TypeSubst := ?\<sigma>' \<rparr>"
    using res unfolding apply_realization_def Let_def by auto

  \<comment> \<open>Unpack the invariant.\<close>
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and own_disj: "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and tswk: "typesubst_well_kinded env (CM_TypeSubst m)"
   and dom_own: "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract"
   and dom_td: "fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs elabEnv)"
   and cap: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
   and fresh_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and fresh_fn: "\<forall>fname inf. fmlookup (TE_Functions env) fname = Some inf \<longrightarrow>
                    list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)"
   and glb: "module_globals_well_typed env (CM_GlobalVars (normalize_module m))"
   and fnw: "module_functions_well_typed env (CM_Functions (normalize_module m))"
    using inv unfolding elab_decls_invariant_def by blast+

  \<comment> \<open>Standing facts about the state env and the new binding.\<close>
  have scope_env: "tyenv_module_scope env"
    by (rule elab_decls_invariant_module_scope[OF inv])
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope_env unfolding tyenv_module_scope_def by blast
  have rtv_sub: "TE_RuntimeTypeVars env |\<subseteq>| TE_TypeVars env"
    using wf[unfolded tyenv_well_formed_def]
    unfolding tyenv_runtime_tyvars_subset_def by simp
  have tv_disj: "TE_TypeVars env |\<inter>| fmdom ?\<sigma> = {||}"
    using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
  have name_dom: "name |\<notin>| fmdom ?\<sigma>"
    using tv tv_disj by (metis fempty_iff finter_iff)
  have name_m: "name |\<notin>| TE_TypeVars (CM_TyEnv m)"
    using own own_disj by (metis fempty_iff finter_iff)
  have cap_new: "finsert name (fset_of_list (type_tyvars_list target))
                   |\<inter>| scope_bound_tyvars env elabEnv = {||}"
    using nocap unfolding realization_captures_def by blast
  have tgt_tvs: "type_tyvars target \<subseteq> fset (TE_TypeVars env)"
    by (rule is_well_kinded_type_tyvars_subset[OF wk])
  have tv_disj': "\<And>x. x |\<in>| TE_TypeVars env \<Longrightarrow> x |\<notin>| fmdom ?\<sigma>"
    using tv_disj by (metis fempty_iff finter_iff)
  have tgt_dom: "type_tyvars target \<inter> fset (fmdom ?\<sigma>) = {}"
    using tgt_tvs tv_disj' by blast
  have comp: "?\<sigma>' = compose_subst ?s ?\<sigma>"
    by (rule realization_subst_compose[OF name_dom])

  \<comment> \<open>Field projections of the realized env.\<close>
  have tv_env': "TE_TypeVars env' = TE_TypeVars env |-| {|name|}"
   and rtv_env': "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env |-| {|name|}"
   and abs_env': "TE_AbstractTypes env' = TE_AbstractTypes env |-| {|name|}"
    unfolding env'_eq by simp_all
  have dt_env': "TE_Datatypes env' = TE_Datatypes env"
   and gd_env': "TE_GhostDatatypes env' = TE_GhostDatatypes env"
   and gg_env': "TE_GhostGlobals env' = TE_GhostGlobals env"
   and gv_env': "TE_GlobalVars env' = fmmap (apply_subst ?s) (TE_GlobalVars env)"
   and fn_env': "TE_Functions env' = fmmap (apply_subst_to_funinfo ?s) (TE_Functions env)"
   and rty_env': "TE_ReturnType env' = TE_ReturnType env"
    unfolding env'_eq apply_subst_to_tyenv_def by simp_all

  \<comment> \<open>The target at the realized env.\<close>
  have wk': "is_well_kinded env' target"
    by (rule is_well_kinded_shrink_tyvar[OF wk noself tv_env' dt_env'])
  have rt': "is_runtime_type env' target" if nR: "name |\<in>| TE_RuntimeTypeVars env"
  proof -
    have "is_runtime_type env target" using rt_ok nR by blast
    then show ?thesis
      by (rule is_runtime_type_shrink_tyvar[OF _ noself rtv_env' gd_env'])
  qed

  \<comment> \<open>The engine pass with the singleton substitution.\<close>
  have ok: "module_env_subst_ok ?s env' env"
   and ok_rt: "module_env_subst_runtime_ok ?s env' env"
    using apply_realization_subst_ok[OF env'_eq wk' rt' cap_new] by blast+
  have absorb: "apply_subst_to_module_env ?s env' env = env'"
    by (rule apply_realization_state_absorb[OF env'_eq scope_env])

  \<comment> \<open>Conjunct 2: the state-env equation.\<close>
  have env_eq': "env' = module_context_env env0 m'"
    unfolding env'_eq m'_eq by (rule apply_realization_env_eq[OF env_eq name_dom])

  \<comment> \<open>Conjunct 3: the module invariant.\<close>
  have minv': "core_module_invariant m'"
    unfolding m'_eq
    by (rule apply_realization_module_invariant
               [OF minv env_eq name_dom name_m tgt_dom noself cap cap_new])

  \<comment> \<open>Conjunct 5: well-formedness of the realized env.\<close>
  have wf': "tyenv_well_formed env'"
  proof -
    have abs_target: "TE_AbstractTypes env' = TE_TypeVars env'"
      unfolding tv_env' abs_env' abs_tv by simp
    have rtv_target: "TE_RuntimeTypeVars env' |\<subseteq>| TE_TypeVars env'"
      unfolding tv_env' rtv_env' using rtv_sub by auto
    have "tyenv_well_formed (apply_subst_to_module_env ?s env' env)"
      by (rule tyenv_well_formed_apply_subst_to_module_env
                 [OF wf ok ok_rt abs_tv abs_target rtv_target])
    then show ?thesis unfolding absorb .
  qed

  \<comment> \<open>Conjunct 6: the elab env over the realized env.\<close>
  have eewf': "elabenv_well_formed env' elabEnv'"
  proof -
    have td0: "typedefs_well_formed env (EE_Typedefs elabEnv)"
     and vd_ctor0: "nullary_data_ctors_consistent env elabEnv"
     and vd0: "EE_CurrentFunctionVoid elabEnv \<longrightarrow> TE_ReturnType env = CoreTy_Record []"
      using eewf unfolding elabenv_well_formed_def by blast+
    have td': "typedefs_well_formed env' (EE_Typedefs elabEnv')"
      unfolding ee'_eq
      using apply_realization_typedefs[OF td0 env'_eq wk' cap_new] by simp
    have vd_ctor': "nullary_data_ctors_consistent env' elabEnv'"
      by (rule apply_realization_nullary_ctors[OF vd_ctor0 env'_eq])
         (simp add: ee'_eq)
    have vd': "EE_CurrentFunctionVoid elabEnv' \<longrightarrow> TE_ReturnType env' = CoreTy_Record []"
      using vd0 rty_env' unfolding ee'_eq by simp
    show ?thesis
      unfolding elabenv_well_formed_def using td' vd_ctor' vd' by simp
  qed

  \<comment> \<open>Conjunct 7: the extended substitution's ranges are well-kinded.\<close>
  have tswk': "typesubst_well_kinded env' ?\<sigma>'"
    unfolding typesubst_well_kinded_def
  proof (intro allI impI)
    fix n ty assume lk: "fmlookup ?\<sigma>' n = Some ty"
    show "is_well_kinded env' ty"
    proof (cases "n = name")
      case True
      then have "ty = target" using lk by simp
      then show ?thesis using wk' by simp
    next
      case False
      then obtain ty0 where lk0: "fmlookup ?\<sigma> n = Some ty0"
                        and ty_eq: "ty = apply_subst ?s ty0"
        using lk by (cases "fmlookup ?\<sigma> n") auto
      have wk0: "is_well_kinded env ty0"
        using tswk lk0 unfolding typesubst_well_kinded_def by blast
      show ?thesis
        unfolding ty_eq
      proof (rule apply_subst_preserves_well_kinded[OF wk0])
        show "TE_Datatypes env' = TE_Datatypes env" by (rule dt_env')
      next
        fix k assume kT: "k |\<in>| TE_TypeVars env"
        show "case fmlookup ?s k of
                Some ty' \<Rightarrow> is_well_kinded env' ty'
              | None \<Rightarrow> k |\<in>| TE_TypeVars env'"
        proof (cases "k = name")
          case True then show ?thesis using wk' by simp
        next
          case False
          then have "k |\<in>| TE_TypeVars env'" unfolding tv_env' using kT by simp
          with False show ?thesis by simp
        qed
      qed
    qed
  qed

  \<comment> \<open>Conjuncts 4, 8, 9, 10: domains, coverage and capture of the extension.\<close>
  have own_disj': "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m') = {||}"
    unfolding m'_eq using own_disj by simp
  have dom_own': "fmdom ?\<sigma>' |\<subseteq>| ownAbstract"
    using dom_own own by auto
  have dom_td': "fmdom ?\<sigma>' |\<subseteq>| fmdom (EE_Typedefs elabEnv')"
    unfolding ee'_eq using dom_td by auto
  have sn': "subst_names ?\<sigma>'
               |\<subseteq>| finsert name (fset_of_list (type_tyvars_list target))
                     |\<union>| subst_names ?\<sigma>"
    unfolding comp
    using subst_names_compose_subset[of ?s ?\<sigma>] subst_names_singleton_subset by auto
  have cap_all: "(finsert name (fset_of_list (type_tyvars_list target))
                    |\<union>| subst_names ?\<sigma>) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
    using cap cap_new by (simp add: inf_sup_distrib2)
  have cap': "subst_names ?\<sigma>' |\<inter>| scope_bound_tyvars env' elabEnv' = {||}"
    by (rule empty_inter_mono
               [OF sn' apply_realization_scope_bound[OF env'_eq ee'_eq] cap_all])

  \<comment> \<open>Conjuncts 11, 12: metavariable freshness survives (nothing is added).\<close>
  have fresh_tv': "\<forall>n. n |\<in>| TE_TypeVars env' \<longrightarrow> tyvar_fresh_ok n 0"
    unfolding tv_env' using fresh_tv by auto
  have fresh_fn': "\<forall>fname inf. fmlookup (TE_Functions env') fname = Some inf \<longrightarrow>
                     list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)"
  proof (intro allI impI)
    fix fname inf assume "fmlookup (TE_Functions env') fname = Some inf"
    then obtain inf0 where lk0: "fmlookup (TE_Functions env) fname = Some inf0"
                       and i_eq: "inf = apply_subst_to_funinfo ?s inf0"
      unfolding fn_env' by (cases "fmlookup (TE_Functions env) fname") auto
    have "list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf0)"
      using fresh_fn lk0 by blast
    then show "list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)"
      unfolding i_eq by simp
  qed

  \<comment> \<open>Conjunct 13: recorded globals re-typecheck through the singleton pass.\<close>
  have glb': "module_globals_well_typed env' (CM_GlobalVars (normalize_module m'))"
  proof -
    have norm': "CM_GlobalVars (normalize_module m')
                   = fmmap (apply_subst_to_term ?\<sigma>') (CM_GlobalVars m)"
      unfolding m'_eq normalize_module_def by simp
    have norm0: "CM_GlobalVars (normalize_module m)
                   = fmmap (apply_subst_to_term ?\<sigma>) (CM_GlobalVars m)"
      unfolding normalize_module_def by simp
    have tm_comp: "\<And>tm. apply_subst_to_term ?\<sigma>' tm
                     = apply_subst_to_term ?s (apply_subst_to_term ?\<sigma> tm)"
      unfolding apply_subst_to_term_compose comp by (rule refl)
    show ?thesis
      unfolding module_globals_well_typed_def
    proof (intro allI impI)
      fix gname tm'
      assume "fmlookup (CM_GlobalVars (normalize_module m')) gname = Some tm'"
      then obtain tm0 where lk0: "fmlookup (CM_GlobalVars m) gname = Some tm0"
                        and tm_eq: "tm' = apply_subst_to_term ?\<sigma>' tm0"
        unfolding norm' by (cases "fmlookup (CM_GlobalVars m) gname") auto
      have lkn: "fmlookup (CM_GlobalVars (normalize_module m)) gname
                   = Some (apply_subst_to_term ?\<sigma> tm0)"
        unfolding norm0 by (simp add: lk0)
      from glb lkn obtain declTy
        where dlk: "fmlookup (TE_GlobalVars env) gname = Some declTy"
          and body: "if gname |\<in>| TE_GhostGlobals env
                     then core_term_type env Ghost (apply_subst_to_term ?\<sigma> tm0)
                            = Some declTy
                     else is_constant_term (apply_subst_to_term ?\<sigma> tm0) \<and>
                          core_term_type env NotGhost (apply_subst_to_term ?\<sigma> tm0)
                            = Some declTy"
        unfolding module_globals_well_typed_def by blast
      have dlk': "fmlookup (TE_GlobalVars env') gname = Some (apply_subst ?s declTy)"
        unfolding gv_env' by (simp add: dlk)
      have typed': "core_term_type env' gh (apply_subst_to_term ?\<sigma>' tm0)
                      = Some (apply_subst ?s declTy)"
        if t: "core_term_type env gh (apply_subst_to_term ?\<sigma> tm0) = Some declTy" for gh
      proof -
        have "core_term_type (apply_subst_to_module_env ?s env' env) gh
                (apply_subst_to_term ?s (apply_subst_to_term ?\<sigma> tm0))
              = Some (apply_subst ?s declTy)"
          using core_term_type_subst_module_env[OF t wf ok] ok_rt by blast
        then show ?thesis unfolding absorb tm_comp .
      qed
      show "\<exists>declTy'. fmlookup (TE_GlobalVars env') gname = Some declTy' \<and>
              (if gname |\<in>| TE_GhostGlobals env'
               then core_term_type env' Ghost tm' = Some declTy'
               else is_constant_term tm' \<and>
                    core_term_type env' NotGhost tm' = Some declTy')"
      proof (intro exI[of _ "apply_subst ?s declTy"] conjI)
        show "fmlookup (TE_GlobalVars env') gname = Some (apply_subst ?s declTy)"
          by (rule dlk')
        show "if gname |\<in>| TE_GhostGlobals env'
              then core_term_type env' Ghost tm' = Some (apply_subst ?s declTy)
              else is_constant_term tm' \<and>
                   core_term_type env' NotGhost tm' = Some (apply_subst ?s declTy)"
        proof (cases "gname |\<in>| TE_GhostGlobals env")
          case True
          with body have t: "core_term_type env Ghost (apply_subst_to_term ?\<sigma> tm0)
                               = Some declTy"
            by simp
          show ?thesis using typed'[OF t] True gg_env' tm_eq by simp
        next
          case False
          with body have c: "is_constant_term (apply_subst_to_term ?\<sigma> tm0)"
                     and t: "core_term_type env NotGhost (apply_subst_to_term ?\<sigma> tm0)
                               = Some declTy"
            by simp_all
          show ?thesis using typed'[OF t] False gg_env' tm_eq c by simp
        qed
      qed
    qed
  qed

  \<comment> \<open>Conjunct 14: recorded function bodies re-typecheck at the realized
      body envs.\<close>
  have fnw': "module_functions_well_typed env' (CM_Functions (normalize_module m'))"
  proof -
    have normf': "CM_Functions (normalize_module m')
        = fmmap (\<lambda>f. f \<lparr> CF_Body := map_option (apply_subst_to_statement_list ?\<sigma>')
                                       (CF_Body f) \<rparr>)
                (CM_Functions m)"
      unfolding m'_eq normalize_module_def by simp
    have normf0: "CM_Functions (normalize_module m)
        = fmmap (\<lambda>f. f \<lparr> CF_Body := map_option (apply_subst_to_statement_list ?\<sigma>)
                                       (CF_Body f) \<rparr>)
                (CM_Functions m)"
      unfolding normalize_module_def by simp
    have st_comp: "\<And>stmts. apply_subst_to_statement_list ?\<sigma>' stmts
                     = apply_subst_to_statement_list ?s
                         (apply_subst_to_statement_list ?\<sigma> stmts)"
      unfolding apply_subst_to_statement_list_compose comp by (rule refl)
    show ?thesis
      unfolding module_functions_well_typed_def
    proof (intro allI impI)
      fix fname f'
      assume "fmlookup (CM_Functions (normalize_module m')) fname = Some f'"
      then obtain f0 where lk0: "fmlookup (CM_Functions m) fname = Some f0"
          and f'_eq: "f' = f0 \<lparr> CF_Body := map_option (apply_subst_to_statement_list ?\<sigma>')
                                              (CF_Body f0) \<rparr>"
        unfolding normf' by (cases "fmlookup (CM_Functions m) fname") auto
      let ?f\<sigma> = "f0 \<lparr> CF_Body := map_option (apply_subst_to_statement_list ?\<sigma>)
                                     (CF_Body f0) \<rparr>"
      have lkn: "fmlookup (CM_Functions (normalize_module m)) fname = Some ?f\<sigma>"
        unfolding normf0 by (simp add: lk0)
      from fnw lkn obtain info
        where ilk: "fmlookup (TE_Functions env) fname = Some info"
          and len\<sigma>: "length (CF_Args ?f\<sigma>) = length (FI_TmArgs info)"
          and dst\<sigma>: "distinct (CF_Args ?f\<sigma>)"
          and body\<sigma>: "case CF_Body ?f\<sigma> of
                        None \<Rightarrow> True
                      | Some body \<Rightarrow>
                          core_statement_list_type
                            (module_body_env_for env (CF_Args ?f\<sigma>) info)
                            (FI_Ghost info) body \<noteq> None"
        unfolding module_functions_well_typed_def by blast
      have len: "length (CF_Args f0) = length (FI_TmArgs info)" using len\<sigma> by simp
      have dst: "distinct (CF_Args f0)" using dst\<sigma> by simp
      have body: "case CF_Body f0 of
                    None \<Rightarrow> True
                  | Some body0 \<Rightarrow>
                      core_statement_list_type
                        (module_body_env_for env (CF_Args f0) info)
                        (FI_Ghost info)
                        (apply_subst_to_statement_list ?\<sigma> body0) \<noteq> None"
        using body\<sigma> by (cases "CF_Body f0") simp_all
      let ?info' = "apply_subst_to_funinfo ?s info"
      have ilk': "fmlookup (TE_Functions env') fname = Some ?info'"
        unfolding fn_env' by (simp add: ilk)
      have wf_be: "tyenv_well_formed (module_body_env_for env (CF_Args f0) info)"
        by (rule module_body_env_for_well_formed[OF wf ilk len])
      have name_fi: "name |\<notin>| fset_of_list (FI_TyArgs info)"
      proof -
        have "{|name|} |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
          by (rule empty_inter_mono
                     [OF _ scope_bound_tyvars_fun_entry[OF ilk] cap_new]) auto
        then show ?thesis by (metis fempty_iff finsertCI finter_iff)
      qed
      have ok_be: "module_env_subst_ok ?s
                     (module_body_env_for env' (CF_Args f0) ?info')
                     (module_body_env_for env (CF_Args f0) info)"
       and ok_rt_be: "module_env_subst_runtime_ok ?s
                     (module_body_env_for env' (CF_Args f0) ?info')
                     (module_body_env_for env (CF_Args f0) info)"
        using apply_realization_body_subst_ok
                [OF env'_eq abs_tv rtv_sub wk' rt' name_fi cap_new]
        by blast+
      have collapse: "apply_subst_to_module_env ?s
                        (module_body_env_for env' (CF_Args f0) ?info')
                        (module_body_env_for env (CF_Args f0) info)
                      = module_body_env_for env' (CF_Args f0) ?info'"
        by (rule apply_realization_body_collapse[OF env'_eq])
      have body': "case CF_Body f' of
                     None \<Rightarrow> True
                   | Some body \<Rightarrow>
                       core_statement_list_type
                         (module_body_env_for env' (CF_Args f') ?info')
                         (FI_Ghost ?info') body \<noteq> None"
      proof (cases "CF_Body f0")
        case None then show ?thesis using f'_eq by simp
      next
        case (Some body0)
        from body Some obtain envOut
          where typed: "core_statement_list_type
                          (module_body_env_for env (CF_Args f0) info)
                          (FI_Ghost info)
                          (apply_subst_to_statement_list ?\<sigma> body0) = Some envOut"
          by (cases "core_statement_list_type
                       (module_body_env_for env (CF_Args f0) info)
                       (FI_Ghost info)
                       (apply_subst_to_statement_list ?\<sigma> body0)") auto
        have "core_statement_list_type
                (apply_subst_to_module_env ?s
                   (module_body_env_for env' (CF_Args f0) ?info')
                   (module_body_env_for env (CF_Args f0) info))
                (FI_Ghost info)
                (apply_subst_to_statement_list ?s
                   (apply_subst_to_statement_list ?\<sigma> body0))
              = Some (apply_subst_to_module_env ?s
                         (module_body_env_for env' (CF_Args f0) ?info') envOut)"
          using core_statement_list_type_subst_module_env[OF typed wf_be ok_be] ok_rt_be
          by blast
        then have "core_statement_list_type
                     (module_body_env_for env' (CF_Args f0) ?info')
                     (FI_Ghost info)
                     (apply_subst_to_statement_list ?\<sigma>' body0) \<noteq> None"
          unfolding collapse st_comp by simp
        then show ?thesis using f'_eq Some by simp
      qed
      show "\<exists>info'. fmlookup (TE_Functions env') fname = Some info' \<and>
              length (CF_Args f') = length (FI_TmArgs info') \<and>
              distinct (CF_Args f') \<and>
              (case CF_Body f' of
                 None \<Rightarrow> True
               | Some body \<Rightarrow>
                   core_statement_list_type
                     (module_body_env_for env' (CF_Args f') info')
                     (FI_Ghost info') body \<noteq> None)"
      proof (intro exI[of _ ?info'] conjI)
        show "fmlookup (TE_Functions env') fname = Some ?info'" by (rule ilk')
        show "length (CF_Args f') = length (FI_TmArgs ?info')"
          using len f'_eq by simp
        show "distinct (CF_Args f')" using dst f'_eq by simp
        show "case CF_Body f' of
                None \<Rightarrow> True
              | Some body \<Rightarrow>
                  core_statement_list_type
                    (module_body_env_for env' (CF_Args f') ?info')
                    (FI_Ghost ?info') body \<noteq> None"
          by (rule body')
      qed
    qed
  qed

  show ?thesis
    unfolding elab_decls_invariant_def
  proof (intro conjI)
    show "elab_context_ok env0 ownAbstract" by (rule ctx)
    show "env' = module_context_env env0 m'" by (rule env_eq')
    show "core_module_invariant m'" by (rule minv')
    show "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m') = {||}" by (rule own_disj')
    show "tyenv_well_formed env'" by (rule wf')
    show "elabenv_well_formed env' elabEnv'" by (rule eewf')
    show "typesubst_well_kinded env' (CM_TypeSubst m')"
      unfolding m'_eq using tswk' by simp
    show "fmdom (CM_TypeSubst m') |\<subseteq>| ownAbstract"
      unfolding m'_eq using dom_own' by simp
    show "fmdom (CM_TypeSubst m') |\<subseteq>| fmdom (EE_Typedefs elabEnv')"
      unfolding m'_eq using dom_td' by simp
    show "subst_names (CM_TypeSubst m') |\<inter>| scope_bound_tyvars env' elabEnv' = {||}"
      unfolding m'_eq using cap' by simp
    show "\<forall>n. n |\<in>| TE_TypeVars env' \<longrightarrow> tyvar_fresh_ok n 0" by (rule fresh_tv')
    show "\<forall>fname inf. fmlookup (TE_Functions env') fname = Some inf \<longrightarrow>
            list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs inf)" by (rule fresh_fn')
    show "module_globals_well_typed env' (CM_GlobalVars (normalize_module m'))"
      by (rule glb')
    show "module_functions_well_typed env' (CM_Functions (normalize_module m'))"
      by (rule fnw')
  qed
qed

(* ---- Datatypes ---- *)

(* -------------------------------------------------------------------------- *)
(* Lookup/domain/commutation facts for the two constructor folds              *)
(* -------------------------------------------------------------------------- *)

(* tyenv_add_datatype registers the constructors with
   "fold (\<lambda>(cn, payload). fmupd cn (name, tyvars, payload)) ctors",
   and the elaborator registers arities with
   "fold (\<lambda>(cn, _, arity). fmupd cn arity) ctorInfo". The lemmas below give
   the lookup, domain and commutation behaviour of these folds. *)

(* A name not among the new constructors looks up as before. *)
lemma fold_ctor_upd_lookup_fresh:
  assumes "cn \<notin> fst ` set ctors"
  shows "fmlookup (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors M) cn = fmlookup M cn"
  using assms
proof (induction ctors arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  obtain c1 p1 where c_eq: "c = (c1, p1)" by (cases c) auto
  have cn_ne: "cn \<noteq> c1" and cn_rest: "cn \<notin> fst ` set cs"
    using Cons.prems c_eq by auto
  show ?case
    using Cons.IH[OF cn_rest] cn_ne by (simp add: c_eq)
qed

(* Any entry of the folded map is either a new-shaped one or an old one. *)
lemma fold_ctor_upd_lookup_cases:
  assumes "fmlookup (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors M) cn = Some entry"
  shows "(\<exists>payload. (cn, payload) \<in> set ctors \<and> entry = (dtName, tyVars, payload))
         \<or> fmlookup M cn = Some entry"
  using assms
proof (induction ctors arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  obtain c1 p1 where c_eq: "c = (c1, p1)" by (cases c) auto
  from Cons.prems have "fmlookup (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) cs
                          (fmupd c1 (dtName, tyVars, p1) M)) cn = Some entry"
    by (simp add: c_eq)
  from Cons.IH[OF this] show ?case
    using c_eq by (cases "cn = c1") auto
qed

(* With distinct constructor names, a registered constructor looks up exactly
   as registered. *)
lemma fold_ctor_upd_lookup_hit:
  assumes dist: "distinct (map fst ctors)"
      and mem: "(cn, payload) \<in> set ctors"
  shows "fmlookup (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors M) cn
           = Some (dtName, tyVars, payload)"
  using assms
proof (induction ctors arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  obtain c1 p1 where c_eq: "c = (c1, p1)" by (cases c) auto
  show ?case
  proof (cases "(cn, payload) \<in> set cs")
    case True
    have "distinct (map fst cs)" using Cons.prems(1) by simp
    from Cons.IH[OF this True] show ?thesis by (simp add: c_eq)
  next
    case False
    with Cons.prems(2) c_eq have cn_eq: "cn = c1" and p_eq: "payload = p1" by auto
    have notin_cs: "cn \<notin> fst ` set cs"
      using Cons.prems(1) c_eq cn_eq by auto
    have "fmlookup (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) cs
            (fmupd c1 (dtName, tyVars, p1) M)) cn
            = fmlookup (fmupd c1 (dtName, tyVars, p1) M) cn"
      by (rule fold_ctor_upd_lookup_fresh[OF notin_cs])
    then show ?thesis using cn_eq p_eq by (simp add: c_eq)
  qed
qed

lemma fold_ctor_upd_fmdom:
  "fmdom (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors M)
     = fset_of_list (map fst ctors) |\<union>| fmdom M"
proof (induction ctors arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  show ?case by (cases c) (simp add: Cons.IH)
qed

(* The fold lands on the right of a map union: fmupd goes pointwise through
   ++\<^sub>f (fmadd_fmupd), so the whole fold does. *)
lemma fold_ctor_upd_fmadd:
  "A ++\<^sub>f fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors M
     = fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors (A ++\<^sub>f M)"
proof (induction ctors arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  show ?case by (cases c) (simp add: Cons.IH)
qed

(* Substituting through the folded map: if the substitution fixes every new
   payload, the fold commutes with the entry-wise substitution map. *)
lemma fold_ctor_upd_fmmap_subst:
  assumes idp: "\<And>cn payload. (cn, payload) \<in> set ctors \<Longrightarrow> apply_subst s payload = payload"
  shows "fmmap (apply_subst_to_datactor s)
           (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors M)
       = fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors
           (fmmap (apply_subst_to_datactor s) M)"
  using assms
proof (induction ctors arbitrary: M)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  obtain c1 p1 where c_eq: "c = (c1, p1)" by (cases c) auto
  have p1_id: "apply_subst s p1 = p1" using Cons.prems c_eq by auto
  have step: "fmmap (apply_subst_to_datactor s)
                (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) cs
                   (fmupd c1 (dtName, tyVars, p1) M))
              = fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) cs
                  (fmmap (apply_subst_to_datactor s) (fmupd c1 (dtName, tyVars, p1) M))"
    using Cons.prems by (intro Cons.IH) auto
  have upd: "fmmap (apply_subst_to_datactor s) (fmupd c1 (dtName, tyVars, p1) M)
               = fmupd c1 (dtName, tyVars, p1) (fmmap (apply_subst_to_datactor s) M)"
    by (simp add: fmmap_fmupd apply_subst_to_datactor_def p1_id)
  show ?case using step by (simp add: c_eq upd)
qed

(* Membership in the nullary-constructor name set built from ctorInfo. *)
lemma nullary_ctor_names_mem:
  "cn |\<in>| fset_of_list (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))
     \<longleftrightarrow> (\<exists>pay. (cn, pay, True) \<in> set ctorInfo)"
  by (force simp: fset_of_list_elem)

(* -------------------------------------------------------------------------- *)
(* Datatype-growth variants of the env-monotonicity lemmas                    *)
(* -------------------------------------------------------------------------- *)

(* typedefs_well_formed_mono and typesubst_well_kinded_mono demand an
   UNCHANGED datatype table; registering a datatype grows it. These variants
   ask only that old entries survive. *)
lemma typedefs_well_formed_grow_datatypes:
  assumes twf: "typedefs_well_formed env tds"
      and tv: "TE_TypeVars env' = TE_TypeVars env"
      and dt: "\<And>n v. fmlookup (TE_Datatypes env) n = Some v
                 \<Longrightarrow> fmlookup (TE_Datatypes env') n = Some v"
  shows "typedefs_well_formed env' tds"
  unfolding typedefs_well_formed_def
proof (intro allI impI)
  fix name tyvars targetTy
  assume lk: "fmlookup tds name = Some (tyvars, targetTy)"
  have d: "distinct tyvars"
   and wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars \<rparr>)
                           targetTy"
    using twf lk unfolding typedefs_well_formed_def by blast+
  have "is_well_kinded (env' \<lparr> TE_TypeVars := TE_TypeVars env' |\<union>| fset_of_list tyvars \<rparr>)
                       targetTy"
  proof (rule is_well_kinded_mono[OF wk])
    show "fset (TE_TypeVars (env \<lparr> TE_TypeVars := TE_TypeVars env
                                     |\<union>| fset_of_list tyvars \<rparr>))
            \<subseteq> fset (TE_TypeVars (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                           |\<union>| fset_of_list tyvars \<rparr>))"
      by (simp add: tv)
  next
    fix n v
    assume "fmlookup (TE_Datatypes (env \<lparr> TE_TypeVars := TE_TypeVars env
                                             |\<union>| fset_of_list tyvars \<rparr>)) n = Some v"
    then have "fmlookup (TE_Datatypes env) n = Some v" by simp
    then show "fmlookup (TE_Datatypes (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                                 |\<union>| fset_of_list tyvars \<rparr>)) n = Some v"
      using dt by simp
  qed
  then show "distinct tyvars
             \<and> is_well_kinded (env' \<lparr> TE_TypeVars := TE_TypeVars env'
                                        |\<union>| fset_of_list tyvars \<rparr>) targetTy"
    using d by blast
qed

lemma typesubst_well_kinded_grow_datatypes:
  assumes ts: "typesubst_well_kinded env s"
      and tv: "TE_TypeVars env' = TE_TypeVars env"
      and dt: "\<And>n v. fmlookup (TE_Datatypes env) n = Some v
                 \<Longrightarrow> fmlookup (TE_Datatypes env') n = Some v"
  shows "typesubst_well_kinded env' s"
  unfolding typesubst_well_kinded_def
proof (intro allI impI)
  fix n ty
  assume "fmlookup s n = Some ty"
  then have wk: "is_well_kinded env ty"
    using ts unfolding typesubst_well_kinded_def by blast
  show "is_well_kinded env' ty"
  proof (rule is_well_kinded_mono[OF wk])
    show "fset (TE_TypeVars env) \<subseteq> fset (TE_TypeVars env')" by (simp add: tv)
  next
    fix n v assume "fmlookup (TE_Datatypes env) n = Some v"
    then show "fmlookup (TE_Datatypes env') n = Some v" by (rule dt)
  qed
qed

(* -------------------------------------------------------------------------- *)
(* tyenv_add_datatype: extension, well-formedness, state-env commutation      *)
(* -------------------------------------------------------------------------- *)

(* Registering a datatype under fresh names is a tyenv extension. The
   freshness of the name in TE_DataCtorsByType is NOT a separate premise at
   the use site: it follows from freshness in TE_Datatypes via
   tyenv_bytype_dom_subset. *)
lemma tyenv_extends_add_datatype:
  assumes fresh_dt: "name |\<notin>| fmdom (TE_Datatypes env)"
      and fresh_bt: "name |\<notin>| fmdom (TE_DataCtorsByType env)"
      and fresh_ctors: "\<And>cn. cn \<in> fst ` set ctors \<Longrightarrow> cn |\<notin>| fmdom (TE_DataCtors env)"
  shows "tyenv_extends env (tyenv_add_datatype name tyvars ctors isGhost env)"
proof -
  have dt: "\<And>n v. fmlookup (TE_Datatypes env) n = Some v \<Longrightarrow>
              fmlookup (fmupd name (length tyvars) (TE_Datatypes env)) n = Some v"
    using fresh_dt by (metis fmdomI fmupd_lookup)
  have bt: "\<And>n cs. fmlookup (TE_DataCtorsByType env) n = Some cs \<Longrightarrow>
              fmlookup (fmupd name (map fst ctors) (TE_DataCtorsByType env)) n = Some cs"
    using fresh_bt by (metis fmdomI fmupd_lookup)
  have dc: "\<And>n e. fmlookup (TE_DataCtors env) n = Some e \<Longrightarrow>
              fmlookup (fold (\<lambda>(cn, payload). fmupd cn (name, tyvars, payload)) ctors
                          (TE_DataCtors env)) n = Some e"
  proof -
    fix n e assume lk: "fmlookup (TE_DataCtors env) n = Some e"
    have "n \<notin> fst ` set ctors"
      using fresh_ctors fmdomI[OF lk] by blast
    then show "fmlookup (fold (\<lambda>(cn, payload). fmupd cn (name, tyvars, payload)) ctors
                           (TE_DataCtors env)) n = Some e"
      using fold_ctor_upd_lookup_fresh lk by metis
  qed
  have gd: "\<And>n. n |\<in>| fmdom (TE_Datatypes env) \<Longrightarrow>
              (n |\<in>| (if isGhost then finsert name (TE_GhostDatatypes env)
                      else TE_GhostDatatypes env)
               \<longleftrightarrow> n |\<in>| TE_GhostDatatypes env)"
    using fresh_dt by (auto split: if_splits)
  show ?thesis
    unfolding tyenv_extends_def tyenv_add_datatype_def
    using dt bt dc gd by auto
qed

(* Registering a datatype with fresh names, nonempty distinct constructors
   and well-kinded (runtime, if computed non-ghost) payloads preserves
   tyenv_well_formed. The payload hypotheses are phrased over exactly the env
   in which the elaborator checked them. *)
lemma tyenv_well_formed_add_datatype:
  assumes wf: "tyenv_well_formed env"
      and fresh_dt: "name |\<notin>| fmdom (TE_Datatypes env)"
      and fresh_ctors: "\<And>cn. cn \<in> fst ` set ctors \<Longrightarrow> cn |\<notin>| fmdom (TE_DataCtors env)"
      and nonempty: "ctors \<noteq> []"
      and dist_names: "distinct (map fst ctors)"
      and dist_tvs: "distinct tyvars"
      and wk_p: "\<And>cn payload. (cn, payload) \<in> set ctors \<Longrightarrow>
                   is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                            |\<union>| fset_of_list tyvars \<rparr>) payload"
      and rt_p: "\<And>cn payload. \<not> isGhost \<Longrightarrow> (cn, payload) \<in> set ctors \<Longrightarrow>
                   is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                             |\<union>| fset_of_list tyvars,
                                          TE_RuntimeTypeVars :=
                                            (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                            |\<union>| fset_of_list tyvars \<rparr>) payload"
  shows "tyenv_well_formed (tyenv_add_datatype name tyvars ctors isGhost env)"
proof -
  let ?env' = "tyenv_add_datatype name tyvars ctors isGhost env"
  have vwk: "tyenv_vars_well_kinded env"
   and vrt: "tyenv_vars_runtime env"
   and gvs: "tyenv_ghost_vars_subset env"
   and rwk: "tyenv_return_type_well_kinded env"
   and rrt: "tyenv_return_type_runtime env"
   and cons: "tyenv_ctors_consistent env"
   and pwk: "tyenv_payloads_well_kinded env"
   and ctd: "tyenv_ctor_tyvars_distinct env"
   and cbt: "tyenv_ctors_by_type_consistent env"
   and fwk: "tyenv_fun_types_well_kinded env"
   and ftd: "tyenv_fun_tyvars_distinct env"
   and fgc: "tyenv_fun_ghost_constraint env"
   and npr: "tyenv_nonghost_payloads_runtime env"
   and gds: "tyenv_ghost_datatypes_subset env"
   and rts: "tyenv_runtime_tyvars_subset env"
   and ats: "tyenv_abstract_types_subset env"
   and dne: "tyenv_datatypes_nonempty env"
    using wf unfolding tyenv_well_formed_def by blast+
  \<comment> \<open>Folded projections of the unchanged fields, and the four changed fields.\<close>
  have proj: "TE_LocalVars ?env' = TE_LocalVars env"
             "TE_GhostLocals ?env' = TE_GhostLocals env"
             "TE_GlobalVars ?env' = TE_GlobalVars env"
             "TE_GhostGlobals ?env' = TE_GhostGlobals env"
             "TE_TypeVars ?env' = TE_TypeVars env"
             "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env"
             "TE_AbstractTypes ?env' = TE_AbstractTypes env"
             "TE_ReturnType ?env' = TE_ReturnType env"
             "TE_FunctionGhost ?env' = TE_FunctionGhost env"
             "TE_Functions ?env' = TE_Functions env"
    by (simp_all add: tyenv_add_datatype_def)
  have dt_new: "TE_Datatypes ?env' = fmupd name (length tyvars) (TE_Datatypes env)"
   and dc_new: "TE_DataCtors ?env'
                  = fold (\<lambda>(cn, payload). fmupd cn (name, tyvars, payload)) ctors
                      (TE_DataCtors env)"
   and bt_new: "TE_DataCtorsByType ?env'
                  = fmupd name (map fst ctors) (TE_DataCtorsByType env)"
   and gd_new: "TE_GhostDatatypes ?env'
                  = (if isGhost then finsert name (TE_GhostDatatypes env)
                     else TE_GhostDatatypes env)"
    by (simp_all add: tyenv_add_datatype_def)
  \<comment> \<open>Growth of the datatype table, and ghost-marker agreement on its old
      domain (the new name is outside it).\<close>
  have dt_grow: "\<And>n v. fmlookup (TE_Datatypes env) n = Some v
                   \<Longrightarrow> fmlookup (TE_Datatypes ?env') n = Some v"
    using fresh_dt unfolding dt_new by (metis fmdomI fmupd_lookup)
  have gd_agree: "\<And>n. n |\<in>| fmdom (TE_Datatypes env) \<Longrightarrow>
                    (n |\<in>| TE_GhostDatatypes ?env' \<longleftrightarrow> n |\<in>| TE_GhostDatatypes env)"
    using fresh_dt unfolding gd_new by (auto split: if_splits)
  \<comment> \<open>Entry dichotomy for the grown constructor table.\<close>
  have entry_cases: "\<And>cn dtName tyVars payload.
     fmlookup (TE_DataCtors ?env') cn = Some (dtName, tyVars, payload) \<Longrightarrow>
     ((cn, payload) \<in> set ctors \<and> dtName = name \<and> tyVars = tyvars)
     \<or> fmlookup (TE_DataCtors env) cn = Some (dtName, tyVars, payload)"
  proof -
    fix cn dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?env') cn = Some (dtName, tyVars, payload)"
    then have "fmlookup (fold (\<lambda>(c, p). fmupd c (name, tyvars, p)) ctors
                 (TE_DataCtors env)) cn = Some (dtName, tyVars, payload)"
      by (simp add: dc_new)
    from fold_ctor_upd_lookup_cases[OF this]
    show "((cn, payload) \<in> set ctors \<and> dtName = name \<and> tyVars = tyvars)
          \<or> fmlookup (TE_DataCtors env) cn = Some (dtName, tyVars, payload)"
      by auto
  qed
  \<comment> \<open>Transfer engines: well-kindedness survives the table growth, and
      runtime-ness of well-kinded types survives it too (the ghost markers
      agree on all old datatypes). Each comes in a bare and an
      overridden-tyvar-fields form.\<close>
  have wk_tr0: "\<And>ty. is_well_kinded env ty \<Longrightarrow> is_well_kinded ?env' ty"
  proof -
    fix ty assume w: "is_well_kinded env ty"
    show "is_well_kinded ?env' ty"
    proof (rule is_well_kinded_mono[OF w])
      show "fset (TE_TypeVars env) \<subseteq> fset (TE_TypeVars ?env')" by (simp add: proj)
    next
      fix n v assume "fmlookup (TE_Datatypes env) n = Some v"
      then show "fmlookup (TE_Datatypes ?env') n = Some v" by (rule dt_grow)
    qed
  qed
  have wk_tr: "\<And>tvs ty. is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) ty
                 \<Longrightarrow> is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) ty"
  proof -
    fix tvs ty assume w: "is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) ty"
    show "is_well_kinded (?env' \<lparr> TE_TypeVars := tvs \<rparr>) ty"
    proof (rule is_well_kinded_mono[OF w])
      show "fset (TE_TypeVars (env \<lparr> TE_TypeVars := tvs \<rparr>))
              \<subseteq> fset (TE_TypeVars (?env' \<lparr> TE_TypeVars := tvs \<rparr>))" by simp
    next
      fix n v assume "fmlookup (TE_Datatypes (env \<lparr> TE_TypeVars := tvs \<rparr>)) n = Some v"
      then have "fmlookup (TE_Datatypes env) n = Some v" by simp
      then show "fmlookup (TE_Datatypes (?env' \<lparr> TE_TypeVars := tvs \<rparr>)) n = Some v"
        using dt_grow by simp
    qed
  qed
  have rt_tr0: "\<And>ty. is_well_kinded env ty \<Longrightarrow> is_runtime_type env ty
                  \<Longrightarrow> is_runtime_type ?env' ty"
  proof -
    fix ty assume w: "is_well_kinded env ty" and r: "is_runtime_type env ty"
    show "is_runtime_type ?env' ty"
    proof (rule is_runtime_type_transfer_mono[OF w r])
      show "fset (TE_RuntimeTypeVars env) \<subseteq> fset (TE_RuntimeTypeVars ?env')"
        by (simp add: proj)
    next
      fix n assume "n |\<in>| fmdom (TE_Datatypes env)"
      then show "(n |\<in>| TE_GhostDatatypes ?env') = (n |\<in>| TE_GhostDatatypes env)"
        using gd_agree by blast
    qed
  qed
  have rt_tr: "\<And>tvs rtvs ty.
        is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) ty \<Longrightarrow>
        is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty \<Longrightarrow>
        is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty"
  proof -
    fix tvs rtvs ty
    assume w: "is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) ty"
       and r: "is_runtime_type (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty"
    have w_cong: "is_well_kinded (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty
                    = is_well_kinded (env \<lparr> TE_TypeVars := tvs \<rparr>) ty"
      by (rule is_well_kinded_cong_env) simp_all
    have w2: "is_well_kinded (env \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty"
      using w w_cong by simp
    show "is_runtime_type (?env' \<lparr> TE_TypeVars := tvs, TE_RuntimeTypeVars := rtvs \<rparr>) ty"
    proof (rule is_runtime_type_transfer_mono[OF w2 r])
      show "fset (TE_RuntimeTypeVars (env \<lparr> TE_TypeVars := tvs,
                                            TE_RuntimeTypeVars := rtvs \<rparr>))
              \<subseteq> fset (TE_RuntimeTypeVars (?env' \<lparr> TE_TypeVars := tvs,
                                                   TE_RuntimeTypeVars := rtvs \<rparr>))" by simp
    next
      fix n
      assume "n |\<in>| fmdom (TE_Datatypes (env \<lparr> TE_TypeVars := tvs,
                                               TE_RuntimeTypeVars := rtvs \<rparr>))"
      then have n_in: "n |\<in>| fmdom (TE_Datatypes env)" by simp
      show "(n |\<in>| TE_GhostDatatypes (?env' \<lparr> TE_TypeVars := tvs,
                                              TE_RuntimeTypeVars := rtvs \<rparr>))
              = (n |\<in>| TE_GhostDatatypes (env \<lparr> TE_TypeVars := tvs,
                                                TE_RuntimeTypeVars := rtvs \<rparr>))"
        using gd_agree[OF n_in] by simp
    qed
  qed
  \<comment> \<open>The seventeen clauses.\<close>
  have vwk': "tyenv_vars_well_kinded ?env'"
    unfolding tyenv_vars_well_kinded_def
  proof (intro conjI allI impI)
    fix n ty assume "fmlookup (TE_LocalVars ?env') n = Some ty"
    then have "fmlookup (TE_LocalVars env) n = Some ty" by (simp add: proj)
    then have "is_well_kinded env ty"
      using vwk unfolding tyenv_vars_well_kinded_def by blast
    then show "is_well_kinded ?env' ty" using wk_tr0 by blast
  next
    fix n ty assume "fmlookup (TE_GlobalVars ?env') n = Some ty"
    then have "fmlookup (TE_GlobalVars env) n = Some ty" by (simp add: proj)
    then have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
      using vwk unfolding tyenv_vars_well_kinded_def by blast
    then have "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
      using wk_tr by blast
    then show "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env' \<rparr>) ty"
      by (simp add: proj)
  qed
  have vrt': "tyenv_vars_runtime ?env'"
    unfolding tyenv_vars_runtime_def
  proof (intro conjI allI impI)
    fix n ty
    assume "fmlookup (TE_LocalVars ?env') n = Some ty \<and> n |\<notin>| TE_GhostLocals ?env'"
    then have "fmlookup (TE_LocalVars env) n = Some ty" and "n |\<notin>| TE_GhostLocals env"
      by (simp_all add: proj)
    then have "is_runtime_type env ty" and "is_well_kinded env ty"
      using vrt vwk unfolding tyenv_vars_runtime_def tyenv_vars_well_kinded_def by blast+
    then show "is_runtime_type ?env' ty" using rt_tr0 by blast
  next
    fix n ty
    assume "fmlookup (TE_GlobalVars ?env') n = Some ty \<and> n |\<notin>| TE_GhostGlobals ?env'"
    then have lk: "fmlookup (TE_GlobalVars env) n = Some ty"
          and ng: "n |\<notin>| TE_GhostGlobals env"
      by (simp_all add: proj)
    have "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env,
                                 TE_RuntimeTypeVars := TE_AbstractTypes env
                                   |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
      using vrt lk ng unfolding tyenv_vars_runtime_def by blast
    moreover have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
      using vwk lk unfolding tyenv_vars_well_kinded_def by blast
    ultimately have "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env,
                                              TE_RuntimeTypeVars := TE_AbstractTypes env
                                                |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
      using rt_tr by blast
    then show "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env',
                                        TE_RuntimeTypeVars := TE_AbstractTypes ?env'
                                          |\<inter>| TE_RuntimeTypeVars ?env' \<rparr>) ty"
      by (simp add: proj)
  qed
  have gvs': "tyenv_ghost_vars_subset ?env'"
    using gvs unfolding tyenv_ghost_vars_subset_def by (simp add: proj)
  have rwk': "tyenv_return_type_well_kinded ?env'"
  proof -
    have "is_well_kinded env (TE_ReturnType env)"
      using rwk unfolding tyenv_return_type_well_kinded_def .
    then have "is_well_kinded ?env' (TE_ReturnType env)" using wk_tr0 by blast
    then show ?thesis
      unfolding tyenv_return_type_well_kinded_def by (simp add: proj)
  qed
  have rrt': "tyenv_return_type_runtime ?env'"
    unfolding tyenv_return_type_runtime_def
  proof (intro impI)
    assume "TE_FunctionGhost ?env' = NotGhost"
    then have "TE_FunctionGhost env = NotGhost" by (simp add: proj)
    then have "is_runtime_type env (TE_ReturnType env)"
      using rrt unfolding tyenv_return_type_runtime_def by simp
    moreover have "is_well_kinded env (TE_ReturnType env)"
      using rwk unfolding tyenv_return_type_well_kinded_def .
    ultimately have "is_runtime_type ?env' (TE_ReturnType env)"
      using rt_tr0 by blast
    then show "is_runtime_type ?env' (TE_ReturnType ?env')" by (simp add: proj)
  qed
  have cons': "tyenv_ctors_consistent ?env'"
    unfolding tyenv_ctors_consistent_def
  proof (intro allI impI)
    fix cn dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?env') cn = Some (dtName, tyVars, payload)"
    from entry_cases[OF this]
    show "fmlookup (TE_Datatypes ?env') dtName = Some (length tyVars)"
    proof (elim disjE conjE)
      assume "dtName = name" and "tyVars = tyvars"
      then show ?thesis by (simp add: dt_new)
    next
      assume "fmlookup (TE_DataCtors env) cn = Some (dtName, tyVars, payload)"
      then have "fmlookup (TE_Datatypes env) dtName = Some (length tyVars)"
        using cons unfolding tyenv_ctors_consistent_def by blast
      then show ?thesis using dt_grow by blast
    qed
  qed
  have pwk': "tyenv_payloads_well_kinded ?env'"
    unfolding tyenv_payloads_well_kinded_def
  proof (intro allI impI)
    fix cn dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?env') cn = Some (dtName, tyVars, payload)"
    from entry_cases[OF this]
    show "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                     |\<union>| fset_of_list tyVars \<rparr>) payload"
    proof (elim disjE conjE)
      assume mem: "(cn, payload) \<in> set ctors" and tvs_eq: "tyVars = tyvars"
      have "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env
                                       |\<union>| fset_of_list tyvars \<rparr>) payload"
        using wk_tr wk_p[OF mem] by blast
      then show ?thesis using tvs_eq by (simp add: proj)
    next
      assume "fmlookup (TE_DataCtors env) cn = Some (dtName, tyVars, payload)"
      then have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                          |\<union>| fset_of_list tyVars \<rparr>) payload"
        using pwk unfolding tyenv_payloads_well_kinded_def by blast
      then have "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env
                                            |\<union>| fset_of_list tyVars \<rparr>) payload"
        using wk_tr by blast
      then show ?thesis by (simp add: proj)
    qed
  qed
  have ctd': "tyenv_ctor_tyvars_distinct ?env'"
    unfolding tyenv_ctor_tyvars_distinct_def
  proof (intro allI impI)
    fix cn dtName tyVars payload
    assume "fmlookup (TE_DataCtors ?env') cn = Some (dtName, tyVars, payload)"
    from entry_cases[OF this] show "distinct tyVars"
      using ctd dist_tvs unfolding tyenv_ctor_tyvars_distinct_def by blast
  qed
  have cbt': "tyenv_ctors_by_type_consistent ?env'"
    unfolding tyenv_ctors_by_type_consistent_def
  proof (intro allI impI)
    fix dtName cs ctorName
    assume lk: "fmlookup (TE_DataCtorsByType ?env') dtName = Some cs"
    show "ctorName \<in> set cs \<longleftrightarrow>
            (\<exists>tyVars payload.
               fmlookup (TE_DataCtors ?env') ctorName = Some (dtName, tyVars, payload))"
    proof (rule iffI)
      assume mem: "ctorName \<in> set cs"
      show "\<exists>tyVars payload.
              fmlookup (TE_DataCtors ?env') ctorName = Some (dtName, tyVars, payload)"
      proof (cases "dtName = name")
        case True
        then have "cs = map fst ctors" using lk by (simp add: bt_new)
        then have "ctorName \<in> fst ` set ctors" using mem by simp
        then obtain q where q_in: "q \<in> set ctors" and q_fst: "ctorName = fst q" by auto
        then obtain p where pmem: "(ctorName, p) \<in> set ctors" by (metis eq_fst_iff)
        have "fmlookup (TE_DataCtors ?env') ctorName = Some (name, tyvars, p)"
          unfolding dc_new by (rule fold_ctor_upd_lookup_hit[OF dist_names pmem])
        then show ?thesis using True by blast
      next
        case False
        then have lk_old: "fmlookup (TE_DataCtorsByType env) dtName = Some cs"
          using lk by (simp add: bt_new)
        obtain tyVars payload where
          old: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
          using cbt lk_old mem unfolding tyenv_ctors_by_type_consistent_def by blast
        have "ctorName \<notin> fst ` set ctors"
          using fresh_ctors fmdomI[OF old] by blast
        then have "fmlookup (TE_DataCtors ?env') ctorName = Some (dtName, tyVars, payload)"
          unfolding dc_new using fold_ctor_upd_lookup_fresh old by metis
        then show ?thesis by blast
      qed
    next
      assume "\<exists>tyVars payload.
                fmlookup (TE_DataCtors ?env') ctorName = Some (dtName, tyVars, payload)"
      then obtain tyVars payload where
        l2: "fmlookup (TE_DataCtors ?env') ctorName = Some (dtName, tyVars, payload)"
        by blast
      from entry_cases[OF l2] show "ctorName \<in> set cs"
      proof (elim disjE conjE)
        assume mem2: "(ctorName, payload) \<in> set ctors" and dn: "dtName = name"
        have cs_eq: "cs = map fst ctors" using lk dn by (simp add: bt_new)
        have "ctorName \<in> fst ` set ctors" using mem2 by force
        then show ?thesis using cs_eq by simp
      next
        assume old: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
        have "fmlookup (TE_Datatypes env) dtName = Some (length tyVars)"
          using cons old unfolding tyenv_ctors_consistent_def by blast
        then have "dtName \<noteq> name" using fresh_dt by (auto dest: fmdomI)
        then have lk_old: "fmlookup (TE_DataCtorsByType env) dtName = Some cs"
          using lk by (simp add: bt_new)
        then show ?thesis
          using cbt old unfolding tyenv_ctors_by_type_consistent_def by blast
      qed
    qed
  qed
  have fwk': "tyenv_fun_types_well_kinded ?env'"
    unfolding tyenv_fun_types_well_kinded_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?env') funName = Some info"
    then have lk: "fmlookup (TE_Functions env) funName = Some info" by (simp add: proj)
    have argswk: "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                    is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
     and retwk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                         |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                (FI_ReturnType info)"
      using fwk lk unfolding tyenv_fun_types_well_kinded_def by blast+
    have argswk': "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                     is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env
                                               |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
      using argswk wk_tr by blast
    have retwk': "is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env
                                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                 (FI_ReturnType info)"
      using retwk wk_tr by blast
    show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
             is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                       |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
          \<and> is_well_kinded (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                      |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                           (FI_ReturnType info)"
      using argswk' retwk' by (simp add: proj)
  qed
  have ftd': "tyenv_fun_tyvars_distinct ?env'"
    using ftd unfolding tyenv_fun_tyvars_distinct_def by (simp add: proj)
  have fgc': "tyenv_fun_ghost_constraint ?env'"
    unfolding tyenv_fun_ghost_constraint_def Let_def
  proof (intro allI impI)
    fix funName info
    assume "fmlookup (TE_Functions ?env') funName = Some info \<and> FI_Ghost info = NotGhost"
    then have lk: "fmlookup (TE_Functions env) funName = Some info"
          and ng: "FI_Ghost info = NotGhost"
      by (simp_all add: proj)
    have argswk: "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                    is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
     and retwk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                         |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                (FI_ReturnType info)"
      using fwk lk unfolding tyenv_fun_types_well_kinded_def by blast+
    have argsrt: "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                    is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                             |\<union>| fset_of_list (FI_TyArgs info),
                                           TE_RuntimeTypeVars :=
                                             (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
     and retrt: "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                          |\<union>| fset_of_list (FI_TyArgs info),
                                        TE_RuntimeTypeVars :=
                                          (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                 (FI_ReturnType info)"
      using fgc lk ng unfolding tyenv_fun_ghost_constraint_def Let_def by blast+
    have argsrt': "\<forall>ty \<in> fst ` set (FI_TmArgs info).
                     is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env
                                                |\<union>| fset_of_list (FI_TyArgs info),
                                              TE_RuntimeTypeVars :=
                                                (TE_AbstractTypes env
                                                   |\<inter>| TE_RuntimeTypeVars env)
                                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
      using argsrt argswk rt_tr by blast
    have retrt': "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env
                                             |\<union>| fset_of_list (FI_TyArgs info),
                                           TE_RuntimeTypeVars :=
                                             (TE_AbstractTypes env
                                                |\<inter>| TE_RuntimeTypeVars env)
                                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                  (FI_ReturnType info)"
      using retrt retwk rt_tr by blast
    show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
             is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                        |\<union>| fset_of_list (FI_TyArgs info),
                                      TE_RuntimeTypeVars :=
                                        (TE_AbstractTypes ?env'
                                           |\<inter>| TE_RuntimeTypeVars ?env')
                                        |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
          \<and> is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                       |\<union>| fset_of_list (FI_TyArgs info),
                                     TE_RuntimeTypeVars :=
                                       (TE_AbstractTypes ?env'
                                          |\<inter>| TE_RuntimeTypeVars ?env')
                                       |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                            (FI_ReturnType info)"
      using argsrt' retrt' by (simp add: proj)
  qed
  have npr': "tyenv_nonghost_payloads_runtime ?env'"
    unfolding tyenv_nonghost_payloads_runtime_def
  proof (intro allI impI)
    fix cn dtName tyVars payload
    assume lk: "fmlookup (TE_DataCtors ?env') cn = Some (dtName, tyVars, payload)"
       and ng: "dtName |\<notin>| TE_GhostDatatypes ?env'"
    from entry_cases[OF lk]
    show "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes ?env'
                                      |\<union>| fset_of_list tyVars,
                                   TE_RuntimeTypeVars :=
                                     (TE_AbstractTypes ?env' |\<inter>| TE_RuntimeTypeVars ?env')
                                     |\<union>| fset_of_list tyVars \<rparr>) payload"
    proof (elim disjE conjE)
      assume mem: "(cn, payload) \<in> set ctors"
         and dt_eq: "dtName = name" and tvs_eq: "tyVars = tyvars"
      have ngh: "\<not> isGhost"
        using ng dt_eq unfolding gd_new by (auto split: if_splits)
      have "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env
                                        |\<union>| fset_of_list tyvars,
                                     TE_RuntimeTypeVars :=
                                       (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                       |\<union>| fset_of_list tyvars \<rparr>) payload"
        using rt_tr wk_p[OF mem] rt_p[OF ngh mem] by blast
      then show ?thesis using tvs_eq by (simp add: proj)
    next
      assume old: "fmlookup (TE_DataCtors env) cn = Some (dtName, tyVars, payload)"
      have ng_env: "dtName |\<notin>| TE_GhostDatatypes env"
        using ng unfolding gd_new by (auto split: if_splits)
      have "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                      |\<union>| fset_of_list tyVars,
                                   TE_RuntimeTypeVars :=
                                     (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                     |\<union>| fset_of_list tyVars \<rparr>) payload"
        using npr old ng_env unfolding tyenv_nonghost_payloads_runtime_def by blast
      moreover have "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                             |\<union>| fset_of_list tyVars \<rparr>) payload"
        using pwk old unfolding tyenv_payloads_well_kinded_def by blast
      ultimately have "is_runtime_type (?env' \<lparr> TE_TypeVars := TE_AbstractTypes env
                                                   |\<union>| fset_of_list tyVars,
                                                TE_RuntimeTypeVars :=
                                                  (TE_AbstractTypes env
                                                     |\<inter>| TE_RuntimeTypeVars env)
                                                  |\<union>| fset_of_list tyVars \<rparr>) payload"
        using rt_tr by blast
      then show ?thesis by (simp add: proj)
    qed
  qed
  have gds': "tyenv_ghost_datatypes_subset ?env'"
    using gds unfolding tyenv_ghost_datatypes_subset_def gd_new dt_new
    by (auto split: if_splits)
  have rts': "tyenv_runtime_tyvars_subset ?env'"
    using rts unfolding tyenv_runtime_tyvars_subset_def by (simp add: proj)
  have ats': "tyenv_abstract_types_subset ?env'"
    using ats unfolding tyenv_abstract_types_subset_def by (simp add: proj)
  have dne': "tyenv_datatypes_nonempty ?env'"
  proof -
    have H1: "fmdom (TE_Datatypes ?env') |\<subseteq>| fmdom (TE_DataCtorsByType ?env')"
      using dne unfolding tyenv_datatypes_nonempty_def dt_new bt_new
      by (auto dest: fsubsetD)
    have H2: "\<And>dtName cs. fmlookup (TE_DataCtorsByType ?env') dtName = Some cs
                \<Longrightarrow> cs \<noteq> []"
    proof -
      fix dtName cs
      assume "fmlookup (TE_DataCtorsByType ?env') dtName = Some cs"
      then have "cs = map fst ctors
                 \<or> fmlookup (TE_DataCtorsByType env) dtName = Some cs"
        unfolding bt_new by (auto split: if_splits)
      then show "cs \<noteq> []"
        using nonempty dne unfolding tyenv_datatypes_nonempty_def by auto
    qed
    show ?thesis
      unfolding tyenv_datatypes_nonempty_def using H1 H2 by auto
  qed
  show ?thesis
    unfolding tyenv_well_formed_def
    using vwk' vrt' gvs' rwk' rrt' cons' pwk' ctd' cbt' fwk' ftd' fgc' npr'
          gds' rts' ats' dne'
    by blast
qed

(* tyenv_add_datatype commutes with reconstructing the state env, provided
   the module's substitution fixes every new payload type. (The datatype and
   by-type tables and the ghost markers are untouched by the substitution;
   the constructor fold passes through the map union and the entry-wise
   substitution map by the fold lemmas above.) *)
lemma module_context_env_add_datatype:
  assumes subst_id: "\<And>cn payload. (cn, payload) \<in> set ctors \<Longrightarrow>
                       apply_subst (CM_TypeSubst m) payload = payload"
  shows "tyenv_add_datatype name tyvars ctors isGhost (module_context_env env0 m)
           = module_context_env env0
               (m \<lparr> CM_TyEnv := tyenv_add_datatype name tyvars ctors isGhost (CM_TyEnv m) \<rparr>)"
  unfolding module_context_env_def apply_subst_to_tyenv_def tyenv_add_datatype_def
  by (cases isGhost)
     (simp_all add: fold_ctor_upd_fmadd fold_ctor_upd_fmmap_subst[OF subst_id])

(* -------------------------------------------------------------------------- *)
(* Correctness of the constructor elaboration                                 *)
(* -------------------------------------------------------------------------- *)

(* elab_data_ctors returns the declared constructor names in order, and each
   payload type is well-kinded (in the env it elaborated in); a constructor
   declared without a payload (isNullary) gets the unit payload CoreTy_Record []
   (the shape nullary_data_ctors_consistent requires). *)
lemma elab_data_ctors_correct:
  assumes wf: "tyenv_well_formed penv"
      and td: "typedefs_well_formed penv (EE_Typedefs pee)"
      and ec: "elab_data_ctors penv pee dcs = Inr ctorInfo"
  shows "map fst ctorInfo = map (\<lambda>(_, n, _). n) dcs
         \<and> (\<forall>cn pay isNullary. (cn, pay, isNullary) \<in> set ctorInfo \<longrightarrow>
              is_well_kinded penv pay
              \<and> (isNullary \<longrightarrow> pay = CoreTy_Record []))"
  using ec
proof (induction dcs arbitrary: ctorInfo)
  case Nil
  then show ?case by simp
next
  case (Cons dc rest)
  obtain cloc cname payloadOpt where dc_eq: "dc = (cloc, cname, payloadOpt)"
    by (cases dc) auto
  \<comment> \<open>Peel the two scrutinees of the Cons clause, one at a time.\<close>
  have "\<exists>p. (case payloadOpt of None \<Rightarrow> Inr (CoreTy_Record [])
             | Some ty \<Rightarrow> elab_type penv pee Ghost ty) = Inr p"
  proof (cases "(case payloadOpt of None \<Rightarrow> Inr (CoreTy_Record [])
                 | Some ty \<Rightarrow> elab_type penv pee Ghost ty)")
    case (Inl errs)
    then have "elab_data_ctors penv pee (dc # rest) = Inl errs"
      by (simp add: dc_eq)
    then show ?thesis using Cons.prems by simp
  next
    case (Inr p)
    then show ?thesis by blast
  qed
  then obtain payloadTy where
    pt: "(case payloadOpt of None \<Rightarrow> Inr (CoreTy_Record [])
          | Some ty \<Rightarrow> elab_type penv pee Ghost ty) = Inr payloadTy"
    by blast
  have "\<exists>r. elab_data_ctors penv pee rest = Inr r"
  proof (cases "elab_data_ctors penv pee rest")
    case (Inl errs)
    then have "elab_data_ctors penv pee (dc # rest) = Inl errs"
      using pt by (simp add: dc_eq)
    then show ?thesis using Cons.prems by simp
  next
    case (Inr r)
    then show ?thesis by blast
  qed
  then obtain rest' where er: "elab_data_ctors penv pee rest = Inr rest'"
    by blast
  have info_eq: "ctorInfo = (cname, payloadTy, payloadOpt = None) # rest'"
    using Cons.prems pt er by (simp add: dc_eq)
  \<comment> \<open>Tail facts from the induction hypothesis.\<close>
  have tail_names: "map fst rest' = map (\<lambda>(_, n, _). n) rest"
   and tail_all: "\<forall>cn pay isNullary. (cn, pay, isNullary) \<in> set rest' \<longrightarrow>
                    is_well_kinded penv pay
                    \<and> (isNullary \<longrightarrow> pay = CoreTy_Record [])"
    using Cons.IH[OF er] by blast+
  \<comment> \<open>The head payload is well-kinded.\<close>
  have head_wk: "is_well_kinded penv payloadTy"
  proof (cases payloadOpt)
    case None
    then have "payloadTy = CoreTy_Record []" using pt by simp
    then show ?thesis by simp
  next
    case (Some ty)
    then have "elab_type penv pee Ghost ty = Inr payloadTy" using pt by simp
    then show ?thesis using elab_type_is_well_kinded(1)[OF td wf] by blast
  qed
  \<comment> \<open>A payload-less declaration elaborates to the unit payload.\<close>
  have head_shape: "payloadOpt = None \<longrightarrow> payloadTy = CoreTy_Record []"
    using pt by (cases payloadOpt) auto
  show ?case
  proof (rule conjI)
    show "map fst ctorInfo = map (\<lambda>(_, n, _). n) (dc # rest)"
      using tail_names by (simp add: info_eq dc_eq)
  next
    show "\<forall>cn pay isNullary. (cn, pay, isNullary) \<in> set ctorInfo \<longrightarrow>
            is_well_kinded penv pay
            \<and> (isNullary \<longrightarrow> pay = CoreTy_Record [])"
    proof (intro allI impI)
      fix cn pay isNullary
      assume "(cn, pay, isNullary) \<in> set ctorInfo"
      then consider
          (hd) "cn = cname" "pay = payloadTy" "isNullary = (payloadOpt = None)"
        | (tl) "(cn, pay, isNullary) \<in> set rest'"
        by (auto simp: info_eq)
      then show "is_well_kinded penv pay
                 \<and> (isNullary \<longrightarrow> pay = CoreTy_Record [])"
      proof cases
        case hd
        then show ?thesis using head_wk head_shape by simp
      next
        case tl
        then show ?thesis using tail_all by blast
      qed
    qed
  qed
qed

(* -------------------------------------------------------------------------- *)
(* The bound-type-parameter footprint of a new datatype                       *)
(* -------------------------------------------------------------------------- *)

(* Every entry of the folded constructor table is either new-shaped (so its
   contribution to a union over the range is that of a new entry) or an old
   one. Companion of ffUnion_fmran_fmupd_member for the constructor fold. *)
lemma ffUnion_fmran_fold_ctor_member:
  assumes "x |\<in>| ffUnion (f |`| fmran (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors M))"
  shows "(\<exists>p. x |\<in>| f (dtName, tyVars, p)) \<or> x |\<in>| ffUnion (f |`| fmran M)"
proof -
  obtain e where
      e_ran: "e |\<in>| fmran (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors M)"
      and x_in: "x |\<in>| f e"
    using assms unfolding fmember_ffUnion_iff by auto
  obtain k where lk: "fmlookup (fold (\<lambda>(c, p). fmupd c (dtName, tyVars, p)) ctors M) k
                        = Some e"
    using e_ran by (auto simp: fmlookup_ran_iff)
  from fold_ctor_upd_lookup_cases[OF lk]
  show ?thesis
  proof (elim disjE exE conjE)
    fix p
    assume "(k, p) \<in> set ctors" and "e = (dtName, tyVars, p)"
    then show ?thesis using x_in by auto
  next
    assume "fmlookup M k = Some e"
    then have "e |\<in>| fmran M" by (rule fmranI)
    then have "f e |\<in>| f |`| fmran M" by simp
    then have "x |\<in>| ffUnion (f |`| fmran M)"
      unfolding fmember_ffUnion_iff using x_in by blast
    then show ?thesis by simp
  qed
qed

(* Registering a datatype grows scope_bound_tyvars by at most the datatype's
   own type parameters (each new constructor entry carries exactly them). *)
lemma scope_bound_tyvars_add_datatype:
  "scope_bound_tyvars (tyenv_add_datatype name tyvars ctors isGhost env) elabEnv2
     |\<subseteq>| fset_of_list tyvars |\<union>| scope_bound_tyvars env elabEnv2"
proof
  fix x
  assume "x |\<in>| scope_bound_tyvars (tyenv_add_datatype name tyvars ctors isGhost env)
                  elabEnv2"
  then consider
      (fn) "x |\<in>| ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info))
                             |`| fmran (TE_Functions env))"
    | (dc) "x |\<in>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars)
                             |`| fmran (fold (\<lambda>(cn, payload). fmupd cn (name, tyvars, payload))
                                          ctors (TE_DataCtors env)))"
    | (td) "x |\<in>| ffUnion ((\<lambda>(tyVars, _). fset_of_list tyVars)
                             |`| fmran (EE_Typedefs elabEnv2))"
    unfolding scope_bound_tyvars_def tyenv_add_datatype_def by auto
  then show "x |\<in>| fset_of_list tyvars |\<union>| scope_bound_tyvars env elabEnv2"
  proof cases
    case fn
    then show ?thesis unfolding scope_bound_tyvars_def by auto
  next
    case dc
    from ffUnion_fmran_fold_ctor_member[OF dc]
    show ?thesis
    proof (elim disjE exE)
      fix p :: CoreType
      assume "x |\<in>| (\<lambda>(_, tyVars, _). fset_of_list tyVars) (name, tyvars, p)"
      then show ?thesis by auto
    next
      assume "x |\<in>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars)
                               |`| fmran (TE_DataCtors env))"
      then show ?thesis unfolding scope_bound_tyvars_def by auto
    qed
  next
    case td
    then show ?thesis unfolding scope_bound_tyvars_def by auto
  qed
qed

(* -------------------------------------------------------------------------- *)
(* The invariant step for registering a datatype                              *)
(* -------------------------------------------------------------------------- *)

(* Registering a datatype (constructor table entries, by-type list, nullary
   constructor names, ghost marker) preserves the fold invariant. The
   constructor list is given in the elaborator's (name, payload, isNullary) form;
   the conclusion is phrased with the projection map and the nullary-name set
   exactly as the elaborator writes them. *)
lemma elab_decls_invariant_add_datatype:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and fresh_dt: "name |\<notin>| fmdom (TE_Datatypes env)"
      and nonempty: "ctorInfo \<noteq> []"
      and dist_names: "distinct (map fst ctorInfo)"
      and fresh_ctors: "\<And>cn. cn \<in> fst ` set ctorInfo \<Longrightarrow> \<not> term_name_in_scope env cn"
      and dist_tvs: "distinct tyvars"
      and nocap: "\<not> binder_captures env m tyvars"
      and wk_p: "\<And>cn pay v. (cn, pay, v) \<in> set ctorInfo \<Longrightarrow>
                   is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                            |\<union>| fset_of_list tyvars \<rparr>) pay"
      and rt_p: "\<And>cn pay v. \<not> isGhost \<Longrightarrow> (cn, pay, v) \<in> set ctorInfo \<Longrightarrow>
                   is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                             |\<union>| fset_of_list tyvars,
                                          TE_RuntimeTypeVars :=
                                            (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                            |\<union>| fset_of_list tyvars \<rparr>) pay"
      and shape: "\<And>cn pay. (cn, pay, True) \<in> set ctorInfo \<Longrightarrow> pay = CoreTy_Record []"
  shows "elab_decls_invariant env0 ownAbstract
           (tyenv_add_datatype name tyvars (map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo)
              isGhost env)
           (elabEnv \<lparr> EE_NullaryDataCtors :=
                        fset_of_list
                          (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))
                        |\<union>| EE_NullaryDataCtors elabEnv \<rparr>)
           (m \<lparr> CM_TyEnv := tyenv_add_datatype name tyvars
                              (map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo) isGhost
                              (CM_TyEnv m) \<rparr>)"
proof -
  let ?ctors = "map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo"
  let ?env' = "tyenv_add_datatype name tyvars ?ctors isGhost env"
  let ?ee' = "elabEnv \<lparr> EE_NullaryDataCtors :=
                          fset_of_list
                            (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))
                          |\<union>| EE_NullaryDataCtors elabEnv \<rparr>"
  let ?m' = "m \<lparr> CM_TyEnv := tyenv_add_datatype name tyvars ?ctors isGhost (CM_TyEnv m) \<rparr>"
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and own_disj: "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and swk: "typesubst_well_kinded env (CM_TypeSubst m)"
   and dom_own: "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract"
   and dom_td: "fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs elabEnv)"
   and cap_env: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
   and mv_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and mv_fn: "\<forall>fname info. fmlookup (TE_Functions env) fname = Some info \<longrightarrow>
                 list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
   and gwt: "module_globals_well_typed env (CM_GlobalVars (normalize_module m))"
   and fwt: "module_functions_well_typed env (CM_Functions (normalize_module m))"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope_env unfolding tyenv_module_scope_def by blast
  have cons: "tyenv_ctors_consistent env"
   and cbt: "tyenv_ctors_by_type_consistent env"
   and dne: "tyenv_datatypes_nonempty env"
    using wf unfolding tyenv_well_formed_def by blast+
  \<comment> \<open>The two views of the constructor list.\<close>
  have ctors_names: "map fst ?ctors = map fst ctorInfo"
    by (induction ctorInfo) auto
  have fst_sets: "fst ` set ?ctors = fst ` set ctorInfo"
    by (metis ctors_names set_map)
  have ctors_mem: "\<And>cn pay. (cn, pay) \<in> set ?ctors \<Longrightarrow> \<exists>ar. (cn, pay, ar) \<in> set ctorInfo"
    by force
  have ctors_mem2: "\<And>cn pay ar. (cn, pay, ar) \<in> set ctorInfo \<Longrightarrow> (cn, pay) \<in> set ?ctors"
    by force
  have nonempty': "?ctors \<noteq> []" using nonempty by simp
  have dist_names': "distinct (map fst ?ctors)" using dist_names ctors_names by presburger
  \<comment> \<open>Freshness of the new names in the relevant tables.\<close>
  have fresh_dc: "\<And>cn. cn \<in> fst ` set ?ctors \<Longrightarrow> cn |\<notin>| fmdom (TE_DataCtors env)"
  proof -
    fix cn assume "cn \<in> fst ` set ?ctors"
    then have "cn \<in> fst ` set ctorInfo" using fst_sets by simp
    then have "\<not> term_name_in_scope env cn" by (rule fresh_ctors)
    then show "cn |\<notin>| fmdom (TE_DataCtors env)"
      unfolding term_name_in_scope_def by blast
  qed
  have fresh_bt: "name |\<notin>| fmdom (TE_DataCtorsByType env)"
    using tyenv_bytype_dom_subset[OF cons cbt dne] fresh_dt by blast
  have ext: "tyenv_extends env ?env'"
    using tyenv_extends_add_datatype[OF fresh_dt fresh_bt fresh_dc] .
  \<comment> \<open>Payload hypotheses in the pair view.\<close>
  have wk_p': "\<And>cn pay. (cn, pay) \<in> set ?ctors \<Longrightarrow>
                 is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                          |\<union>| fset_of_list tyvars \<rparr>) pay"
  proof -
    fix cn pay assume "(cn, pay) \<in> set ?ctors"
    then obtain ar where "(cn, pay, ar) \<in> set ctorInfo" using ctors_mem by blast
    then show "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                        |\<union>| fset_of_list tyvars \<rparr>) pay"
      by (rule wk_p)
  qed
  have rt_p': "\<And>cn pay. \<not> isGhost \<Longrightarrow> (cn, pay) \<in> set ?ctors \<Longrightarrow>
                 is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                           |\<union>| fset_of_list tyvars,
                                        TE_RuntimeTypeVars :=
                                          (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                          |\<union>| fset_of_list tyvars \<rparr>) pay"
  proof -
    fix cn pay assume ng: "\<not> isGhost" and "(cn, pay) \<in> set ?ctors"
    then obtain ar where "(cn, pay, ar) \<in> set ctorInfo" using ctors_mem by blast
    then show "is_runtime_type (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                         |\<union>| fset_of_list tyvars,
                                      TE_RuntimeTypeVars :=
                                        (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                        |\<union>| fset_of_list tyvars \<rparr>) pay"
      using ng by (simp add: rt_p)
  qed
  have wf': "tyenv_well_formed ?env'"
    using tyenv_well_formed_add_datatype[OF wf fresh_dt fresh_dc nonempty' dist_names'
                                            dist_tvs wk_p' rt_p'] .
  \<comment> \<open>Folded projections of the changed and unchanged fields.\<close>
  have dt_new: "TE_Datatypes ?env' = fmupd name (length tyvars) (TE_Datatypes env)"
   and dc_new: "TE_DataCtors ?env'
                  = fold (\<lambda>(cn, payload). fmupd cn (name, tyvars, payload)) ?ctors
                      (TE_DataCtors env)"
   and tv_proj: "TE_TypeVars ?env' = TE_TypeVars env"
   and rtv_proj: "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env"
   and abs_proj: "TE_AbstractTypes ?env' = TE_AbstractTypes env"
   and ret_proj: "TE_ReturnType ?env' = TE_ReturnType env"
   and fn_proj: "TE_Functions ?env' = TE_Functions env"
    by (simp_all add: tyenv_add_datatype_def)
  have dt_grow: "\<And>n v. fmlookup (TE_Datatypes env) n = Some v
                   \<Longrightarrow> fmlookup (TE_Datatypes ?env') n = Some v"
    using fresh_dt unfolding dt_new by (metis fmdomI fmupd_lookup)
  \<comment> \<open>The substitution fixes every new payload (its type variables are among
      the state env's type variables and the datatype's parameters, both
      disjoint from the substitution domain).\<close>
  have tv_disj: "TE_TypeVars env |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
  have snames_tvs: "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyvars = {||}"
    using nocap unfolding binder_captures_def by auto
  have tvs_dom_disj: "fset_of_list tyvars |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using nocap unfolding binder_captures_def subst_names_def by auto
  have subst_id: "\<And>cn pay. (cn, pay) \<in> set ?ctors \<Longrightarrow>
                    apply_subst (CM_TypeSubst m) pay = pay"
  proof -
    fix cn pay assume mem: "(cn, pay) \<in> set ?ctors"
    have disj: "TE_TypeVars (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                      |\<union>| fset_of_list tyvars \<rparr>)
                  |\<inter>| fmdom (CM_TypeSubst m) = {||}"
      by (simp add: abs_tv inf_sup_distrib2 tv_disj tvs_dom_disj)
    show "apply_subst (CM_TypeSubst m) pay = pay"
      using apply_subst_id_on_env_type[OF disj wk_p'[OF mem]] .
  qed
  \<comment> \<open>The individual conjuncts.\<close>
  have env_eq': "?env' = module_context_env env0 ?m'"
    using env_eq module_context_env_add_datatype subst_id by presburger
  have minv': "core_module_invariant ?m'"
  proof -
    have idem: "idempotent_subst (CM_TypeSubst m)"
     and cap_m: "capture_avoiding m"
     and ghost_ok: "module_ghost_subsets_ok m"
     and disj: "fmdom (CM_TypeSubst m) |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
     and rtv: "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
     and scope: "tyenv_module_scope (CM_TyEnv m)"
      using minv unfolding core_module_invariant_def by blast+
    have cap': "capture_avoiding ?m'"
      unfolding capture_avoiding_def
    proof (intro conjI allI impI)
      fix funName info
      assume "fmlookup (TE_Functions (CM_TyEnv ?m')) funName = Some info"
      then have "fmlookup (TE_Functions (CM_TyEnv m)) funName = Some info"
        by (simp add: tyenv_add_datatype_def)
      then show "subst_names (CM_TypeSubst ?m') |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
        using cap_m unfolding capture_avoiding_def by simp
    next
      fix ctorName dtName tyVars payload
      assume "fmlookup (TE_DataCtors (CM_TyEnv ?m')) ctorName
                = Some (dtName, tyVars, payload)"
      then have "fmlookup (fold (\<lambda>(cn, p). fmupd cn (name, tyvars, p)) ?ctors
                   (TE_DataCtors (CM_TyEnv m))) ctorName = Some (dtName, tyVars, payload)"
        by (simp add: tyenv_add_datatype_def)
      from fold_ctor_upd_lookup_cases[OF this]
      show "subst_names (CM_TypeSubst ?m') |\<inter>| fset_of_list tyVars = {||}"
      proof (elim disjE exE conjE)
        fix p
        assume "(ctorName, p) \<in> set ?ctors"
           and "(dtName, tyVars, payload) = (name, tyvars, p)"
        then show ?thesis using snames_tvs by simp
      next
        assume "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName
                  = Some (dtName, tyVars, payload)"
        then show ?thesis using cap_m unfolding capture_avoiding_def by fastforce
      qed
    qed
    have ghost_ok': "module_ghost_subsets_ok ?m'"
      using ghost_ok unfolding module_ghost_subsets_ok_def tyenv_add_datatype_def
      by (cases isGhost) auto
    have disj': "fmdom (CM_TypeSubst ?m') |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}"
      using disj by (simp add: tyenv_add_datatype_def)
    have rtv': "TE_RuntimeTypeVars (CM_TyEnv ?m') |\<subseteq>| TE_TypeVars (CM_TyEnv ?m')"
      using rtv by (simp add: tyenv_add_datatype_def)
    have scope': "tyenv_module_scope (CM_TyEnv ?m')"
      using scope unfolding tyenv_module_scope_def tyenv_add_datatype_def by simp
    show ?thesis
      unfolding core_module_invariant_def
      using idem cap' ghost_ok' disj' rtv' scope' by simp
  qed
  have own_disj': "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}"
    using own_disj by (simp add: tyenv_add_datatype_def)
  \<comment> \<open>The elab env stays well-formed over the grown env.\<close>
  have td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
   and void_old: "EE_CurrentFunctionVoid elabEnv \<longrightarrow> TE_ReturnType env = CoreTy_Record []"
    using eewf unfolding elabenv_well_formed_def by blast+
  have td': "typedefs_well_formed ?env' (EE_Typedefs elabEnv)"
    by (rule typedefs_well_formed_grow_datatypes[OF td tv_proj dt_grow])
  have nullary': "nullary_data_ctors_consistent ?env' ?ee'"
    unfolding nullary_data_ctors_consistent_def
  proof (intro allI impI)
    fix cn
    assume "cn |\<in>| EE_NullaryDataCtors ?ee'"
    then have "cn |\<in>| fset_of_list (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))
                 \<or> cn |\<in>| EE_NullaryDataCtors elabEnv"
      by auto
    then show "\<exists>dtN tvs. fmlookup (TE_DataCtors ?env') cn
                 = Some (dtN, tvs, CoreTy_Record [])"
    proof (elim disjE)
      assume "cn |\<in>| fset_of_list (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))"
      then obtain pay where mem: "(cn, pay, True) \<in> set ctorInfo"
        using nullary_ctor_names_mem by metis
      have lk: "fmlookup (TE_DataCtors ?env') cn = Some (name, tyvars, pay)"
        unfolding dc_new
        by (rule fold_ctor_upd_lookup_hit[OF dist_names' ctors_mem2[OF mem]])
      then show ?thesis using shape[OF mem] by blast
    next
      assume "cn |\<in>| EE_NullaryDataCtors elabEnv"
      then obtain dtName' tyVars' where
        old_dc: "fmlookup (TE_DataCtors env) cn = Some (dtName', tyVars', CoreTy_Record [])"
        using eewf unfolding elabenv_well_formed_def nullary_data_ctors_consistent_def by blast
      have "cn \<notin> fst ` set ?ctors"
        using fresh_dc fmdomI[OF old_dc] by blast
      then have "fmlookup (TE_DataCtors ?env') cn = Some (dtName', tyVars', CoreTy_Record [])"
        unfolding dc_new using fold_ctor_upd_lookup_fresh old_dc by metis
      then show ?thesis by blast
    qed
  qed
  have eewf': "elabenv_well_formed ?env' ?ee'"
    unfolding elabenv_well_formed_def
    using td' nullary' void_old ret_proj by simp
  \<comment> \<open>Substitution facts.\<close>
  have swk': "typesubst_well_kinded ?env' (CM_TypeSubst m)"
    by (rule typesubst_well_kinded_grow_datatypes[OF swk tv_proj dt_grow])
  have sbt_ee: "scope_bound_tyvars ?env' ?ee' = scope_bound_tyvars ?env' elabEnv"
    unfolding scope_bound_tyvars_def by simp
  have sbt_bound: "scope_bound_tyvars ?env' elabEnv
                     |\<subseteq>| fset_of_list tyvars |\<union>| scope_bound_tyvars env elabEnv"
    by (rule scope_bound_tyvars_add_datatype)
  have cap': "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars ?env' ?ee' = {||}"
  proof -
    have "subst_names (CM_TypeSubst m)
            |\<inter>| (fset_of_list tyvars |\<union>| scope_bound_tyvars env elabEnv) = {||}"
      by (simp add: inf_sup_distrib1 snames_tvs cap_env)
    then show ?thesis
      unfolding sbt_ee by (rule empty_inter_subset[OF _ sbt_bound])
  qed
  \<comment> \<open>Metavariable freshness.\<close>
  have mv_tv': "\<forall>n. n |\<in>| TE_TypeVars ?env' \<longrightarrow> tyvar_fresh_ok n 0"
    using mv_tv tv_proj by simp
  have mv_fn': "\<forall>fname info. fmlookup (TE_Functions ?env') fname = Some info \<longrightarrow>
                  list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
    using mv_fn fn_proj by simp
  \<comment> \<open>Recorded definitions stay well-typed in the grown env.\<close>
  have glb_same: "CM_GlobalVars (normalize_module ?m') = CM_GlobalVars (normalize_module m)"
    by (simp add: normalize_module_def)
  have fns_same: "CM_Functions (normalize_module ?m') = CM_Functions (normalize_module m)"
    by (simp add: normalize_module_def)
  have gwt': "module_globals_well_typed ?env' (CM_GlobalVars (normalize_module ?m'))"
    unfolding glb_same
    by (rule module_globals_well_typed_tyenv_extends[OF gwt ext cons])
  have fwt': "module_functions_well_typed ?env' (CM_Functions (normalize_module ?m'))"
    unfolding fns_same
    by (rule module_functions_well_typed_tyenv_extends[OF fwt ext cons abs_proj])
  \<comment> \<open>Assemble.\<close>
  show ?thesis
    unfolding elab_decls_invariant_def
  proof (intro conjI)
    show "elab_context_ok env0 ownAbstract" using ctx .
    show "?env' = module_context_env env0 ?m'" using env_eq' .
    show "core_module_invariant ?m'" using minv' .
    show "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}" using own_disj' .
    show "tyenv_well_formed ?env'" using wf' .
    show "elabenv_well_formed ?env' ?ee'" using eewf' .
    show "typesubst_well_kinded ?env' (CM_TypeSubst ?m')" using swk' by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| ownAbstract" using dom_own by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| fmdom (EE_Typedefs ?ee')" using dom_td by simp
    show "subst_names (CM_TypeSubst ?m') |\<inter>| scope_bound_tyvars ?env' ?ee' = {||}"
      using cap' by simp
    show "\<forall>n. n |\<in>| TE_TypeVars ?env' \<longrightarrow> tyvar_fresh_ok n 0" using mv_tv' .
    show "\<forall>fname info. fmlookup (TE_Functions ?env') fname = Some info \<longrightarrow>
            list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)" using mv_fn' .
    show "module_globals_well_typed ?env' (CM_GlobalVars (normalize_module ?m'))"
      using gwt' .
    show "module_functions_well_typed ?env' (CM_Functions (normalize_module ?m'))"
      using fwt' .
  qed
qed

(* The same step, but with the elaborator's own checks as premises: the
   constructor-list facts come from elab_data_ctors_correct, elaborated in the
   payload env (the env in which the elaborator kind-checks payloads and
   computes ghost status). The ghost flag in the conclusion is spelled out as
   the elaborator computes it. *)
lemma elab_decls_invariant_datatype_step:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and fresh_dt: "name |\<notin>| fmdom (TE_Datatypes env)"
      and ne_dcs: "dcs \<noteq> []"
      and dup_tvs: "first_duplicate_name (\<lambda>x. x) tyvars = None"
      and nocap: "\<not> binder_captures env m tyvars"
      and dup_ctors: "first_duplicate_name (\<lambda>(_, n, _). n) dcs = None"
      and fresh_ck: "find (\<lambda>(_, n, _). term_name_in_scope env n) dcs = None"
      and ec: "elab_data_ctors
                 (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
                        TE_RuntimeTypeVars :=
                          (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                          |\<union>| fset_of_list tyvars \<rparr>)
                 (elabEnv \<lparr> EE_Typedefs := tyvar_typedef_entries tyvars
                                             (EE_Typedefs elabEnv) \<rparr>)
                 dcs = Inr ctorInfo"
  shows "elab_decls_invariant env0 ownAbstract
           (tyenv_add_datatype name tyvars (map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo)
              (\<not> list_all (\<lambda>(_, payloadTy, _).
                    is_runtime_type
                      (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
                             TE_RuntimeTypeVars :=
                               (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                               |\<union>| fset_of_list tyvars \<rparr>) payloadTy) ctorInfo)
              env)
           (elabEnv \<lparr> EE_NullaryDataCtors :=
                        fset_of_list
                          (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))
                        |\<union>| EE_NullaryDataCtors elabEnv \<rparr>)
           (m \<lparr> CM_TyEnv := tyenv_add_datatype name tyvars
                              (map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo)
                              (\<not> list_all (\<lambda>(_, payloadTy, _).
                                    is_runtime_type
                                      (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                               |\<union>| fset_of_list tyvars,
                                             TE_RuntimeTypeVars :=
                                               (TE_AbstractTypes env
                                                  |\<inter>| TE_RuntimeTypeVars env)
                                               |\<union>| fset_of_list tyvars \<rparr>) payloadTy)
                                  ctorInfo)
                              (CM_TyEnv m) \<rparr>)"
proof -
  let ?pEnv = "env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyvars,
                     TE_RuntimeTypeVars :=
                       (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                       |\<union>| fset_of_list tyvars \<rparr>"
  let ?isGhost = "\<not> list_all (\<lambda>(_, payloadTy, _). is_runtime_type ?pEnv payloadTy) ctorInfo"
  have wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
    using inv unfolding elab_decls_invariant_def by blast+
  have scope_env: "tyenv_module_scope env"
    using elab_decls_invariant_module_scope[OF inv] .
  have abs_tv: "TE_AbstractTypes env = TE_TypeVars env"
    using scope_env unfolding tyenv_module_scope_def by blast
  have rtv_sub: "TE_RuntimeTypeVars env |\<subseteq>| TE_TypeVars env"
    using wf unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by blast
  have tv_int: "TE_TypeVars env |\<inter>| TE_RuntimeTypeVars env = TE_RuntimeTypeVars env"
    using rtv_sub by (rule inf_absorb2)
  \<comment> \<open>The payload env is a plain tyvar-fields extension of the state env.\<close>
  have pEnv_eq: "?pEnv = env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tyvars,
                               TE_RuntimeTypeVars := TE_RuntimeTypeVars env
                                                     |\<union>| fset_of_list tyvars \<rparr>"
    by (simp add: abs_tv tv_int)
  have wf_p: "tyenv_well_formed ?pEnv"
    unfolding pEnv_eq
    by (rule tyenv_well_formed_extend_tyvars[OF wf]) simp
  have td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using eewf unfolding elabenv_well_formed_def by blast
  have td_mono: "typedefs_well_formed ?pEnv (EE_Typedefs elabEnv)"
    by (rule typedefs_well_formed_mono[OF td]) (auto simp: abs_tv)
  have td_p: "typedefs_well_formed ?pEnv
                (EE_Typedefs (elabEnv \<lparr> EE_Typedefs :=
                   tyvar_typedef_entries tyvars (EE_Typedefs elabEnv) \<rparr>))"
    using typedefs_well_formed_tyvar_entries[OF td_mono, of tyvars] by auto
  \<comment> \<open>Facts from the constructor elaboration.\<close>
  have names_eq: "map fst ctorInfo = map (\<lambda>(_, n, _). n) dcs"
   and all_facts: "\<forall>cn pay isNullary. (cn, pay, isNullary) \<in> set ctorInfo \<longrightarrow>
                     is_well_kinded ?pEnv pay
                     \<and> (isNullary \<longrightarrow> pay = CoreTy_Record [])"
    using elab_data_ctors_correct[OF wf_p td_p ec] by blast+
  have nonempty: "ctorInfo \<noteq> []"
  proof
    assume "ctorInfo = []"
    then have "map (\<lambda>(_, n, _). n) dcs = []" using names_eq by simp
    then show False using ne_dcs by simp
  qed
  have dist_names: "distinct (map fst ctorInfo)"
    using first_duplicate_name_None_implies_distinct[OF dup_ctors] names_eq by simp
  have dist_tvs: "distinct tyvars"
    using first_duplicate_name_None_implies_distinct[OF dup_tvs] by simp
  have fresh_ctors: "\<And>cn. cn \<in> fst ` set ctorInfo \<Longrightarrow> \<not> term_name_in_scope env cn"
  proof -
    fix cn assume "cn \<in> fst ` set ctorInfo"
    then have "cn \<in> set (map (\<lambda>(_, n, _). n) dcs)"
      by (metis names_eq set_map)
    then obtain x where x_in: "x \<in> set dcs" and cn_eq: "cn = (\<lambda>(_, n, _). n) x"
      by auto
    obtain xl xn xp where x_eq: "x = (xl, xn, xp)" by (cases x) auto
    have "\<not> (\<lambda>(_, n, _). term_name_in_scope env n) x"
      using fresh_ck x_in unfolding find_None_iff by blast
    then show "\<not> term_name_in_scope env cn"
      using cn_eq x_eq by simp
  qed
  have wk_p: "\<And>cn pay v. (cn, pay, v) \<in> set ctorInfo \<Longrightarrow>
                is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                         |\<union>| fset_of_list tyvars \<rparr>) pay"
  proof -
    fix cn pay v assume "(cn, pay, v) \<in> set ctorInfo"
    then have w: "is_well_kinded ?pEnv pay" using all_facts by blast
    have cong: "is_well_kinded ?pEnv pay
                  = is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                             |\<union>| fset_of_list tyvars \<rparr>) pay"
      by (rule is_well_kinded_cong_env) simp_all
    show "is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                   |\<union>| fset_of_list tyvars \<rparr>) pay"
      using w cong by simp
  qed
  have rt_p: "\<And>cn pay v. \<not> ?isGhost \<Longrightarrow> (cn, pay, v) \<in> set ctorInfo \<Longrightarrow>
                is_runtime_type ?pEnv pay"
  proof -
    fix cn pay v
    assume ng: "\<not> ?isGhost" and mem: "(cn, pay, v) \<in> set ctorInfo"
    have "list_all (\<lambda>(_, payloadTy, _). is_runtime_type ?pEnv payloadTy) ctorInfo"
      using ng by simp
    then show "is_runtime_type ?pEnv pay"
      using mem by (auto simp: list_all_iff)
  qed
  have shape: "\<And>cn pay. (cn, pay, True) \<in> set ctorInfo \<Longrightarrow> pay = CoreTy_Record []"
    using all_facts by blast
  show ?thesis
    by (rule elab_decls_invariant_add_datatype[OF inv fresh_dt nonempty dist_names
              fresh_ctors dist_tvs nocap wk_p rt_p shape])
qed

(* The elimination rule for elab_datatype_decl success: one case per result
   shape (a realization of one of the module's own abstract types, or a plain
   new datatype). Each case names the elaborated constructor info and the
   computed ghost flag, records the guards that must have passed, and states
   the defining equation of the result. *)
lemma elab_datatype_decl_Inr_elim:
  assumes ok: "elab_datatype_decl env elabEnv ownAbstract m dd
                 = Inr (env', elabEnv', m')"
  obtains (Realize) ctorInfo isGhost where
    "DD_Name dd |\<in>| TE_TypeVars env"
    "DD_Name dd |\<in>| ownAbstract"
    "DD_TyArgs dd = []"
    "DD_Name dd |\<notin>| fmdom (TE_Datatypes env)"
    "DD_Ctors dd \<noteq> []"
    "first_duplicate_name (\<lambda>x. x) (DD_TyArgs dd) = None"
    "\<not> binder_captures env m (DD_TyArgs dd)"
    "first_duplicate_name (\<lambda>(_, n, _). n) (DD_Ctors dd) = None"
    "find (\<lambda>(_, n, _). term_name_in_scope env n) (DD_Ctors dd) = None"
    "elab_data_ctors
       (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (DD_TyArgs dd),
              TE_RuntimeTypeVars :=
                (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                |\<union>| fset_of_list (DD_TyArgs dd) \<rparr>)
       (elabEnv \<lparr> EE_Typedefs := tyvar_typedef_entries (DD_TyArgs dd)
                                   (EE_Typedefs elabEnv) \<rparr>)
       (DD_Ctors dd) = Inr ctorInfo"
    "isGhost = (\<not> list_all
       (\<lambda>(_, payloadTy, _).
          is_runtime_type
            (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                     |\<union>| fset_of_list (DD_TyArgs dd),
                   TE_RuntimeTypeVars :=
                     (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                     |\<union>| fset_of_list (DD_TyArgs dd) \<rparr>) payloadTy)
       ctorInfo)"
    "\<not> (DD_Name dd |\<in>| TE_RuntimeTypeVars env \<and> isGhost)"
    "\<not> realization_captures env elabEnv (DD_Name dd)
         (CoreTy_Datatype (DD_Name dd) [])"
    "apply_realization (DD_Name dd) (CoreTy_Datatype (DD_Name dd) [])
       (tyenv_add_datatype (DD_Name dd) (DD_TyArgs dd)
          (map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo) isGhost env)
       (elabEnv \<lparr> EE_NullaryDataCtors :=
                    fset_of_list
                      (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))
                    |\<union>| EE_NullaryDataCtors elabEnv \<rparr>)
       (m \<lparr> CM_TyEnv := tyenv_add_datatype (DD_Name dd) (DD_TyArgs dd)
                          (map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo) isGhost
                          (CM_TyEnv m) \<rparr>)
     = (env', elabEnv', m')"
  | (Plain) ctorInfo isGhost where
    "DD_Name dd |\<notin>| TE_TypeVars env"
    "\<not> type_name_in_scope env elabEnv (DD_Name dd)"
    "DD_Ctors dd \<noteq> []"
    "first_duplicate_name (\<lambda>x. x) (DD_TyArgs dd) = None"
    "\<not> binder_captures env m (DD_TyArgs dd)"
    "first_duplicate_name (\<lambda>(_, n, _). n) (DD_Ctors dd) = None"
    "find (\<lambda>(_, n, _). term_name_in_scope env n) (DD_Ctors dd) = None"
    "elab_data_ctors
       (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (DD_TyArgs dd),
              TE_RuntimeTypeVars :=
                (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                |\<union>| fset_of_list (DD_TyArgs dd) \<rparr>)
       (elabEnv \<lparr> EE_Typedefs := tyvar_typedef_entries (DD_TyArgs dd)
                                   (EE_Typedefs elabEnv) \<rparr>)
       (DD_Ctors dd) = Inr ctorInfo"
    "isGhost = (\<not> list_all
       (\<lambda>(_, payloadTy, _).
          is_runtime_type
            (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                     |\<union>| fset_of_list (DD_TyArgs dd),
                   TE_RuntimeTypeVars :=
                     (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                     |\<union>| fset_of_list (DD_TyArgs dd) \<rparr>) payloadTy)
       ctorInfo)"
    "env' = tyenv_add_datatype (DD_Name dd) (DD_TyArgs dd)
              (map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo) isGhost env"
    "elabEnv' = elabEnv \<lparr> EE_NullaryDataCtors :=
                            fset_of_list
                              (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))
                            |\<union>| EE_NullaryDataCtors elabEnv \<rparr>"
    "m' = m \<lparr> CM_TyEnv := tyenv_add_datatype (DD_Name dd) (DD_TyArgs dd)
                            (map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo) isGhost
                            (CM_TyEnv m) \<rparr>"
  using ok unfolding elab_datatype_decl_def Let_def
  by (auto split: if_splits option.splits sum.splits)

lemma elab_datatype_decl_invariant:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and fresh: "list_all (\<lambda>n. tyvar_fresh_ok n 0) (DD_TyArgs dd)"
      and elab: "elab_datatype_decl env elabEnv ownAbstract m dd = Inr (env', elabEnv', m')"
  shows "elab_decls_invariant env0 ownAbstract env' elabEnv' m'"
  using elab
proof (cases rule: elab_datatype_decl_Inr_elim)
  case (Realize ctorInfo isGhost)
  \<comment> \<open>A realization of one of the module's own abstract types.\<close>
  note r = Realize(1) and own = Realize(2) and tv0 = Realize(3)
   and fresh_dt = Realize(4) and ne_dcs = Realize(5) and dup_tvs = Realize(6)
   and nocap = Realize(7) and dup_ctors = Realize(8) and find_ck = Realize(9)
   and ec = Realize(10) and gdef = Realize(11) and g10 = Realize(12)
   and g11 = Realize(13) and res = Realize(14)
  let ?name = "DD_Name dd"
  let ?tyvars = "DD_TyArgs dd"
  let ?ctors1 = "map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo"
  let ?env1 = "tyenv_add_datatype ?name ?tyvars ?ctors1 isGhost env"
  let ?ee1 = "elabEnv \<lparr> EE_NullaryDataCtors :=
                          fset_of_list
                            (map fst (filter (\<lambda>(_, _, isNullary). isNullary) ctorInfo))
                          |\<union>| EE_NullaryDataCtors elabEnv \<rparr>"
  let ?m1 = "m \<lparr> CM_TyEnv := tyenv_add_datatype ?name ?tyvars ?ctors1 isGhost
                               (CM_TyEnv m) \<rparr>"
  have inv1: "elab_decls_invariant env0 ownAbstract ?env1 ?ee1 ?m1"
    unfolding gdef
    by (rule elab_decls_invariant_datatype_step[OF inv fresh_dt ne_dcs dup_tvs nocap
              dup_ctors find_ck ec])
    \<comment> \<open>The remaining premises of the shared realization lemma.\<close>
    have gds: "tyenv_ghost_datatypes_subset env"
      using inv unfolding elab_decls_invariant_def tyenv_well_formed_def by blast
    have name_ngd: "?name |\<notin>| TE_GhostDatatypes env"
      using gds fresh_dt unfolding tyenv_ghost_datatypes_subset_def by blast
    have tv1: "?name |\<in>| TE_TypeVars ?env1"
      using r by (simp add: tyenv_add_datatype_def)
    have wk1: "is_well_kinded ?env1 (CoreTy_Datatype ?name [])"
      by (simp add: tyenv_add_datatype_def tv0)
    have noself1: "?name \<notin> type_tyvars (CoreTy_Datatype ?name [])"
      by simp
    have rt1: "?name |\<in>| TE_RuntimeTypeVars ?env1 \<longrightarrow>
                 is_runtime_type ?env1 (CoreTy_Datatype ?name [])"
    proof
      assume "?name |\<in>| TE_RuntimeTypeVars ?env1"
      then have "?name |\<in>| TE_RuntimeTypeVars env"
        by (simp add: tyenv_add_datatype_def)
      then have ng: "\<not> isGhost" using g10 by blast
      have "TE_GhostDatatypes ?env1 = TE_GhostDatatypes env"
        using ng by (simp add: tyenv_add_datatype_def)
      then show "is_runtime_type ?env1 (CoreTy_Datatype ?name [])"
        using name_ngd by simp
    qed
    have nocap1: "\<not> realization_captures ?env1 ?ee1 ?name (CoreTy_Datatype ?name [])"
    proof -
      have old_disj: "finsert ?name
                        (fset_of_list (type_tyvars_list (CoreTy_Datatype ?name [])))
                        |\<inter>| scope_bound_tyvars env elabEnv = {||}"
        using g11 unfolding realization_captures_def by simp
      have sbt1_ee: "scope_bound_tyvars ?env1 ?ee1 = scope_bound_tyvars ?env1 elabEnv"
        unfolding scope_bound_tyvars_def by simp
      have bnd: "scope_bound_tyvars ?env1 elabEnv
                   |\<subseteq>| fset_of_list ?tyvars |\<union>| scope_bound_tyvars env elabEnv"
        by (rule scope_bound_tyvars_add_datatype)
      then have bnd2: "scope_bound_tyvars ?env1 elabEnv
                         |\<subseteq>| scope_bound_tyvars env elabEnv"
        using tv0 by simp
      have "finsert ?name (fset_of_list (type_tyvars_list (CoreTy_Datatype ?name [])))
              |\<inter>| scope_bound_tyvars ?env1 ?ee1 = {||}"
        unfolding sbt1_ee
        by (rule empty_inter_subset[OF old_disj bnd2])
      then show ?thesis
        unfolding realization_captures_def by simp
    qed
    show ?thesis
      by (rule apply_realization_invariant[OF inv1 own tv1 wk1 noself1 rt1 nocap1 res])
next
  case (Plain ctorInfo isGhost)
  \<comment> \<open>An ordinary (non-realizing) datatype declaration.\<close>
  note notin = Plain(2) and ne_dcs = Plain(3) and dup_tvs = Plain(4)
   and nocap = Plain(5) and dup_ctors = Plain(6) and find_ck = Plain(7)
   and ec = Plain(8) and gdef = Plain(9)
  have fresh_dt: "DD_Name dd |\<notin>| fmdom (TE_Datatypes env)"
    using notin unfolding type_name_in_scope_def by blast
  show ?thesis
    unfolding Plain(10) Plain(11) Plain(12) gdef
    by (rule elab_decls_invariant_datatype_step[OF inv fresh_dt ne_dcs dup_tvs nocap
              dup_ctors find_ck ec])
qed

(* ---- Typedefs ---- *)

(* Recording a transparent typedef: only EE_Typedefs changes. *)
lemma elab_decls_invariant_add_typedef:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and dist: "distinct tyvars"
      and nocap: "\<not> binder_captures env m tyvars"
      and wk: "is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env
                                       |\<union>| fset_of_list tyvars \<rparr>) target"
  shows "elab_decls_invariant env0 ownAbstract env
           (elabEnv \<lparr> EE_Typedefs := fmupd name (tyvars, target) (EE_Typedefs elabEnv) \<rparr>) m"
proof -
  let ?ee' = "elabEnv \<lparr> EE_Typedefs := fmupd name (tyvars, target) (EE_Typedefs elabEnv) \<rparr>"
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and own_disj: "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and swk: "typesubst_well_kinded env (CM_TypeSubst m)"
   and dom_own: "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract"
   and dom_td: "fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs elabEnv)"
   and cap_env: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
   and mv_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and mv_fn: "\<forall>fname info. fmlookup (TE_Functions env) fname = Some info \<longrightarrow>
                 list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
   and gwt: "module_globals_well_typed env (CM_GlobalVars (normalize_module m))"
   and fwt: "module_functions_well_typed env (CM_Functions (normalize_module m))"
    using inv unfolding elab_decls_invariant_def by blast+
  \<comment> \<open>The elab env stays well-formed: the new entry is exactly the shape of
      the typedefs_well_formed clause.\<close>
  have td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using eewf unfolding elabenv_well_formed_def by blast
  have td': "typedefs_well_formed env (fmupd name (tyvars, target) (EE_Typedefs elabEnv))"
    unfolding typedefs_well_formed_def
  proof (intro allI impI)
    fix nm tvs tt
    assume lk: "fmlookup (fmupd name (tyvars, target) (EE_Typedefs elabEnv)) nm
                  = Some (tvs, tt)"
    show "distinct tvs
          \<and> is_well_kinded (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list tvs \<rparr>) tt"
    proof (cases "nm = name")
      case True
      then have "tvs = tyvars" and "tt = target" using lk by auto
      then show ?thesis using dist wk by simp
    next
      case False
      then have "fmlookup (EE_Typedefs elabEnv) nm = Some (tvs, tt)" using lk by simp
      then show ?thesis using td unfolding typedefs_well_formed_def by blast
    qed
  qed
  have eewf': "elabenv_well_formed env ?ee'"
    using eewf td' unfolding elabenv_well_formed_def nullary_data_ctors_consistent_def by simp
  \<comment> \<open>Capture-avoidance: the new entry's parameters were binder-checked.\<close>
  have tv_disj: "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyvars = {||}"
    using nocap unfolding binder_captures_def by auto
  have sbt': "scope_bound_tyvars env ?ee'
                |\<subseteq>| fset_of_list tyvars |\<union>| scope_bound_tyvars env elabEnv"
    by (rule scope_bound_tyvars_typedefs_upd)
  have cap': "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env ?ee' = {||}"
  proof -
    have "subst_names (CM_TypeSubst m)
            |\<inter>| (fset_of_list tyvars |\<union>| scope_bound_tyvars env elabEnv) = {||}"
      by (simp add: inf_sup_distrib1 tv_disj cap_env)
    then show ?thesis by (rule empty_inter_subset[OF _ sbt'])
  qed
  show ?thesis
    unfolding elab_decls_invariant_def
  proof (intro conjI)
    show "elab_context_ok env0 ownAbstract" using ctx .
    show "env = module_context_env env0 m" using env_eq .
    show "core_module_invariant m" using minv .
    show "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}" using own_disj .
    show "tyenv_well_formed env" using wf .
    show "elabenv_well_formed env ?ee'" using eewf' .
    show "typesubst_well_kinded env (CM_TypeSubst m)" using swk .
    show "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract" using dom_own .
    show "fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs ?ee')" using dom_td by auto
    show "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env ?ee' = {||}" using cap' .
    show "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0" using mv_tv .
    show "\<forall>fname info. fmlookup (TE_Functions env) fname = Some info \<longrightarrow>
            list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)" using mv_fn .
    show "module_globals_well_typed env (CM_GlobalVars (normalize_module m))" using gwt .
    show "module_functions_well_typed env (CM_Functions (normalize_module m))" using fwt .
  qed
qed

(* Recording a new abstract type ("type T;"): env, elabEnv and the module all
   gain the name. *)
lemma elab_decls_invariant_add_abstract_type:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and notin: "\<not> type_name_in_scope env elabEnv name"
      and fresh: "tyvar_fresh_ok name 0"
  shows "elab_decls_invariant env0 ownAbstract
           (tyenv_add_abstract_type name ghost env)
           (elabEnv \<lparr> EE_Typedefs := fmupd name ([], CoreTy_Var name)
                                           (EE_Typedefs elabEnv) \<rparr>)
           (m \<lparr> CM_TyEnv := tyenv_add_abstract_type name ghost (CM_TyEnv m) \<rparr>)"
proof -
  let ?env' = "tyenv_add_abstract_type name ghost env"
  let ?ee' = "elabEnv \<lparr> EE_Typedefs := fmupd name ([], CoreTy_Var name)
                                            (EE_Typedefs elabEnv) \<rparr>"
  let ?m' = "m \<lparr> CM_TyEnv := tyenv_add_abstract_type name ghost (CM_TyEnv m) \<rparr>"
  have ctx: "elab_context_ok env0 ownAbstract"
   and env_eq: "env = module_context_env env0 m"
   and minv: "core_module_invariant m"
   and own_disj: "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
   and wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
   and swk: "typesubst_well_kinded env (CM_TypeSubst m)"
   and dom_own: "fmdom (CM_TypeSubst m) |\<subseteq>| ownAbstract"
   and dom_td: "fmdom (CM_TypeSubst m) |\<subseteq>| fmdom (EE_Typedefs elabEnv)"
   and cap_env: "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
   and mv_tv: "\<forall>n. n |\<in>| TE_TypeVars env \<longrightarrow> tyvar_fresh_ok n 0"
   and mv_fn: "\<forall>fname info. fmlookup (TE_Functions env) fname = Some info \<longrightarrow>
                 list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
   and gwt: "module_globals_well_typed env (CM_GlobalVars (normalize_module m))"
   and fwt: "module_functions_well_typed env (CM_Functions (normalize_module m))"
    using inv unfolding elab_decls_invariant_def by blast+
  \<comment> \<open>Freshness of the new name.\<close>
  have name_td: "name |\<notin>| fmdom (EE_Typedefs elabEnv)"
   and name_tv: "name |\<notin>| TE_TypeVars env"
    using notin unfolding type_name_in_scope_def by blast+
  have name_subst: "name |\<notin>| fmdom (CM_TypeSubst m)"
    using dom_td name_td by blast
  have name_own: "name |\<notin>| ownAbstract"
    using elab_decls_invariant_ownAbstract_cover[OF inv] name_tv name_subst by blast
  \<comment> \<open>The state-env equation.\<close>
  have env_eq': "?env' = module_context_env env0 ?m'"
    using module_context_env_add_abstract_type[OF name_subst] env_eq by simp
  \<comment> \<open>The module invariant.\<close>
  have minv': "core_module_invariant ?m'"
  proof -
    have idem: "idempotent_subst (CM_TypeSubst m)"
     and cap: "capture_avoiding m"
     and ghost_ok: "module_ghost_subsets_ok m"
     and disj: "fmdom (CM_TypeSubst m) |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
     and rtv: "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
     and scope: "tyenv_module_scope (CM_TyEnv m)"
      using minv unfolding core_module_invariant_def by blast+
    have cap': "capture_avoiding ?m'"
      using cap unfolding capture_avoiding_def tyenv_add_abstract_type_def by simp
    have ghost_ok': "module_ghost_subsets_ok ?m'"
      using ghost_ok unfolding module_ghost_subsets_ok_def tyenv_add_abstract_type_def
      by simp
    have disj': "fmdom (CM_TypeSubst ?m') |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}"
      using disj name_subst unfolding tyenv_add_abstract_type_def by simp
    have rtv': "TE_RuntimeTypeVars (CM_TyEnv ?m') |\<subseteq>| TE_TypeVars (CM_TyEnv ?m')"
      using rtv unfolding tyenv_add_abstract_type_def by (cases ghost) auto
    have scope': "tyenv_module_scope (CM_TyEnv ?m')"
      using scope unfolding tyenv_module_scope_def tyenv_add_abstract_type_def by simp
    show ?thesis
      unfolding core_module_invariant_def
      using idem cap' ghost_ok' disj' rtv' scope' by simp
  qed
  \<comment> \<open>The realizable names stay disjoint from the module's own type variables.\<close>
  have own_disj': "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}"
    using own_disj name_own unfolding tyenv_add_abstract_type_def by simp
  \<comment> \<open>Well-formedness of the grown envs.\<close>
  have wf': "tyenv_well_formed ?env'"
    using tyenv_well_formed_add_abstract_type[OF wf] .
  have eewf_grown: "elabenv_well_formed ?env' elabEnv"
    unfolding tyenv_add_abstract_type_as_grow
    by (rule elabenv_well_formed_grow_tyvar_fields[OF eewf])
  have tdg: "typedefs_well_formed ?env' (EE_Typedefs elabEnv)"
    using eewf_grown unfolding elabenv_well_formed_def by blast
  have name_tv': "name |\<in>| TE_TypeVars ?env'"
    unfolding tyenv_add_abstract_type_def by simp
  have td': "typedefs_well_formed ?env'
               (fmupd name ([], CoreTy_Var name) (EE_Typedefs elabEnv))"
    using typedefs_well_formed_upd_tyvar[OF tdg name_tv'] .
  have eewf': "elabenv_well_formed ?env' ?ee'"
    using eewf_grown td' unfolding elabenv_well_formed_def nullary_data_ctors_consistent_def by simp
  \<comment> \<open>Substitution facts.\<close>
  have swk': "typesubst_well_kinded ?env' (CM_TypeSubst m)"
    by (rule typesubst_well_kinded_mono[OF swk])
       (auto simp: tyenv_add_abstract_type_def)
  have sbt_cong: "scope_bound_tyvars ?env' ?ee' = scope_bound_tyvars env ?ee'"
    by (rule scope_bound_tyvars_cong_env)
       (simp_all add: tyenv_add_abstract_type_def)
  have sbt_sub: "scope_bound_tyvars env ?ee' |\<subseteq>| scope_bound_tyvars env elabEnv"
    using scope_bound_tyvars_typedefs_upd[where env = env and elabEnv = elabEnv
                                            and name = name and tvs = "[]"
                                            and ty = "CoreTy_Var name"]
    by simp
  have cap': "subst_names (CM_TypeSubst m) |\<inter>| scope_bound_tyvars ?env' ?ee' = {||}"
    unfolding sbt_cong by (rule empty_inter_subset[OF cap_env sbt_sub])
  \<comment> \<open>Metavariable freshness.\<close>
  have mv_tv': "\<forall>n. n |\<in>| TE_TypeVars ?env' \<longrightarrow> tyvar_fresh_ok n 0"
    using mv_tv fresh unfolding tyenv_add_abstract_type_def by auto
  have mv_fn': "\<forall>fname info. fmlookup (TE_Functions ?env') fname = Some info \<longrightarrow>
                  list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
    using mv_fn unfolding tyenv_add_abstract_type_def by simp
  \<comment> \<open>Recorded definitions stay well-typed in the grown env.\<close>
  have cons: "tyenv_ctors_consistent env"
    using wf unfolding tyenv_well_formed_def by blast
  have glb_same: "CM_GlobalVars (normalize_module ?m') = CM_GlobalVars (normalize_module m)"
    by (simp add: normalize_module_def)
  have fns_same: "CM_Functions (normalize_module ?m') = CM_Functions (normalize_module m)"
    by (simp add: normalize_module_def)
  have gwt0: "module_globals_well_typed ?env' (CM_GlobalVars (normalize_module m))"
    unfolding tyenv_add_abstract_type_as_grow
    by (rule module_globals_well_typed_grow_tyvar_fields[OF gwt cons])
  have gwt': "module_globals_well_typed ?env' (CM_GlobalVars (normalize_module ?m'))"
    using gwt0 unfolding glb_same .
  have fwt0: "module_functions_well_typed ?env' (CM_Functions (normalize_module m))"
    unfolding tyenv_add_abstract_type_as_grow
    by (rule module_functions_well_typed_grow_tyvar_fields[OF fwt cons])
  have fwt': "module_functions_well_typed ?env' (CM_Functions (normalize_module ?m'))"
    using fwt0 unfolding fns_same .
  \<comment> \<open>Assemble.\<close>
  show ?thesis
    unfolding elab_decls_invariant_def
  proof (intro conjI)
    show "elab_context_ok env0 ownAbstract" using ctx .
    show "?env' = module_context_env env0 ?m'" using env_eq' .
    show "core_module_invariant ?m'" using minv' .
    show "ownAbstract |\<inter>| TE_TypeVars (CM_TyEnv ?m') = {||}" using own_disj' .
    show "tyenv_well_formed ?env'" using wf' .
    show "elabenv_well_formed ?env' ?ee'" using eewf' .
    show "typesubst_well_kinded ?env' (CM_TypeSubst ?m')" using swk' by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| ownAbstract" using dom_own by simp
    show "fmdom (CM_TypeSubst ?m') |\<subseteq>| fmdom (EE_Typedefs ?ee')" using dom_td by auto
    show "subst_names (CM_TypeSubst ?m') |\<inter>| scope_bound_tyvars ?env' ?ee' = {||}"
      using cap' by simp
    show "\<forall>n. n |\<in>| TE_TypeVars ?env' \<longrightarrow> tyvar_fresh_ok n 0" using mv_tv' .
    show "\<forall>fname info. fmlookup (TE_Functions ?env') fname = Some info \<longrightarrow>
            list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)" using mv_fn' .
    show "module_globals_well_typed ?env' (CM_GlobalVars (normalize_module ?m'))"
      using gwt' .
    show "module_functions_well_typed ?env' (CM_Functions (normalize_module ?m'))"
      using fwt' .
  qed
qed

(* The elimination rule for elab_typedef_decl success: one case per branch of
   the elaborator (a realization of one of the module's own abstract types; a
   new abstract type; an ordinary transparent typedef). Each case records the
   guards that must have passed and states the defining equations of the
   result. *)
lemma elab_typedef_decl_Inr_elim:
  assumes ok: "elab_typedef_decl env elabEnv ownAbstract m dt
                 = Inr (env', elabEnv', m')"
  obtains (Realize) ty target where
    "\<not> DT_Extern dt"
    "DT_Name dt |\<in>| TE_TypeVars env"
    "DT_Name dt |\<in>| ownAbstract"
    "DT_Definition dt = Some ty"
    "DT_TyArgs dt = []"
    "elab_type env elabEnv Ghost ty = Inr target"
    "DT_Name dt \<notin> type_tyvars target"
    "DT_Name dt |\<in>| TE_RuntimeTypeVars env \<longrightarrow> is_runtime_type env target"
    "\<not> realization_captures env elabEnv (DT_Name dt) target"
    "apply_realization (DT_Name dt) target env elabEnv m = (env', elabEnv', m')"
  | (NewAbstract) where
    "\<not> DT_Extern dt"
    "DT_Name dt |\<notin>| TE_TypeVars env"
    "\<not> type_name_in_scope env elabEnv (DT_Name dt)"
    "DT_Definition dt = None"
    "DT_TyArgs dt = []"
    "env' = tyenv_add_abstract_type (DT_Name dt) (DT_Ghost dt) env"
    "elabEnv' = elabEnv \<lparr> EE_Typedefs := fmupd (DT_Name dt)
                            ([], CoreTy_Var (DT_Name dt)) (EE_Typedefs elabEnv) \<rparr>"
    "m' = m \<lparr> CM_TyEnv := tyenv_add_abstract_type (DT_Name dt) (DT_Ghost dt)
                            (CM_TyEnv m) \<rparr>"
  | (Transparent) ty target where
    "\<not> DT_Extern dt"
    "DT_Name dt |\<notin>| TE_TypeVars env"
    "\<not> type_name_in_scope env elabEnv (DT_Name dt)"
    "DT_Definition dt = Some ty"
    "first_duplicate_name (\<lambda>x. x) (DT_TyArgs dt) = None"
    "\<not> binder_captures env m (DT_TyArgs dt)"
    "elab_type (env \<lparr> TE_TypeVars := TE_TypeVars env
                        |\<union>| fset_of_list (DT_TyArgs dt) \<rparr>)
               (elabEnv \<lparr> EE_Typedefs := tyvar_typedef_entries (DT_TyArgs dt)
                                           (EE_Typedefs elabEnv) \<rparr>)
               Ghost ty = Inr target"
    "env' = env"
    "elabEnv' = elabEnv \<lparr> EE_Typedefs := fmupd (DT_Name dt) (DT_TyArgs dt, target)
                                           (EE_Typedefs elabEnv) \<rparr>"
    "m' = m"
  using ok unfolding elab_typedef_decl_def Let_def
  by (auto split: if_splits option.splits sum.splits)

lemma elab_typedef_decl_invariant:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and fresh: "list_all (\<lambda>n. tyvar_fresh_ok n 0) (DT_Name dt # DT_TyArgs dt)"
      and elab: "elab_typedef_decl env elabEnv ownAbstract m dt = Inr (env', elabEnv', m')"
  shows "elab_decls_invariant env0 ownAbstract env' elabEnv' m'"
  using elab
proof (cases rule: elab_typedef_decl_Inr_elim)
  case (Realize ty target)
  \<comment> \<open>A realization of one of the module's own abstract types.\<close>
  note own = Realize(3) and et = Realize(6) and noself = Realize(7)
   and rt_ok = Realize(8) and nocap = Realize(9) and res = Realize(10)
  have wf: "tyenv_well_formed env"
   and eewf: "elabenv_well_formed env elabEnv"
    using inv unfolding elab_decls_invariant_def by blast+
  have td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
    using eewf unfolding elabenv_well_formed_def by blast
  have wk: "is_well_kinded env target"
    using elab_type_is_well_kinded(1)[OF td wf et] .
  show ?thesis
    by (rule apply_realization_invariant
               [OF inv own Realize(2) wk noself rt_ok nocap res])
next
  case NewAbstract
  note notin = NewAbstract(3)
  have fr: "tyvar_fresh_ok (DT_Name dt) 0" using fresh by simp
  show ?thesis
    unfolding NewAbstract(6) NewAbstract(7) NewAbstract(8)
    by (rule elab_decls_invariant_add_abstract_type[OF inv notin fr])
next
  case (Transparent ty target)
  note dupck = Transparent(5) and nocap = Transparent(6) and et = Transparent(7)
   and res = Transparent(8) Transparent(9) Transparent(10)
    have dist: "distinct (DT_TyArgs dt)"
      using first_duplicate_name_None_implies_distinct[OF dupck] by simp
    have wf: "tyenv_well_formed env"
     and eewf: "elabenv_well_formed env elabEnv"
      using inv unfolding elab_decls_invariant_def by blast+
    have td: "typedefs_well_formed env (EE_Typedefs elabEnv)"
      using eewf unfolding elabenv_well_formed_def by blast
    \<comment> \<open>The target is well-kinded in the parameter-extended env - the exact
        shape of the typedefs_well_formed clause.\<close>
    let ?tdEnv = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| fset_of_list (DT_TyArgs dt) \<rparr>"
    have wf_td: "tyenv_well_formed ?tdEnv"
      using tyenv_well_formed_extend_tyvars[OF wf,
              where extraTV = "fset_of_list (DT_TyArgs dt)" and extraRT = "{||}"]
      by simp
    have td_mono: "typedefs_well_formed ?tdEnv (EE_Typedefs elabEnv)"
      by (rule typedefs_well_formed_mono[OF td]) auto
    have td_entries: "typedefs_well_formed ?tdEnv
                        (EE_Typedefs (elabEnv \<lparr> EE_Typedefs :=
                           tyvar_typedef_entries (DT_TyArgs dt) (EE_Typedefs elabEnv) \<rparr>))"
      using typedefs_well_formed_tyvar_entries[OF td_mono, of "DT_TyArgs dt"] by auto
    have wk: "is_well_kinded ?tdEnv target"
      using elab_type_is_well_kinded(1)[OF td_entries wf_td et] .
    show ?thesis
      unfolding res
      by (rule elab_decls_invariant_add_typedef[OF inv dist nocap wk])
qed

(* ---- The dispatcher ---- *)

lemma elab_declaration_invariant:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and fresh: "decl_tyvars_fresh_ok d"
      and elab: "elab_declaration env elabEnv ownAbstract m d = Inr (env', elabEnv', m')"
  shows "elab_decls_invariant env0 ownAbstract env' elabEnv' m'"
proof (cases d)
  case (BabDecl_Const dc)
  then have e: "elab_const_decl env elabEnv m dc = Inr (env', elabEnv', m')"
    using elab by simp
  show ?thesis by (rule elab_const_decl_invariant[OF inv e])
next
  case (BabDecl_Function df)
  then have e: "elab_function_decl env elabEnv m df = Inr (env', elabEnv', m')"
    using elab by simp
  have f: "list_all (\<lambda>n. tyvar_fresh_ok n 0) (DF_TyArgs df)"
    using fresh BabDecl_Function unfolding decl_tyvars_fresh_ok_def by simp
  show ?thesis by (rule elab_function_decl_invariant[OF inv f e])
next
  case (BabDecl_Datatype dd)
  then have e: "elab_datatype_decl env elabEnv ownAbstract m dd = Inr (env', elabEnv', m')"
    using elab by simp
  have f: "list_all (\<lambda>n. tyvar_fresh_ok n 0) (DD_TyArgs dd)"
    using fresh BabDecl_Datatype unfolding decl_tyvars_fresh_ok_def by simp
  show ?thesis by (rule elab_datatype_decl_invariant[OF inv f e])
next
  case (BabDecl_Typedef dt)
  then have e: "elab_typedef_decl env elabEnv ownAbstract m dt = Inr (env', elabEnv', m')"
    using elab by simp
  have f: "list_all (\<lambda>n. tyvar_fresh_ok n 0) (DT_Name dt # DT_TyArgs dt)"
    using fresh BabDecl_Typedef unfolding decl_tyvars_fresh_ok_def by simp
  show ?thesis by (rule elab_typedef_decl_invariant[OF inv f e])
qed

(* Lifted to the declaration list. *)
lemma elab_declaration_list_invariant:
  assumes "elab_declaration_list env elabEnv ownAbstract m ds = Inr (env', elabEnv', m')"
      and "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and "list_all decl_tyvars_fresh_ok ds"
  shows "elab_decls_invariant env0 ownAbstract env' elabEnv' m'"
  using assms
proof (induction ds arbitrary: env elabEnv m)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  from Cons.prems(1) obtain env1 elabEnv1 m1 where
    step: "elab_declaration env elabEnv ownAbstract m d = Inr (env1, elabEnv1, m1)" and
    rest: "elab_declaration_list env1 elabEnv1 ownAbstract m1 ds = Inr (env', elabEnv', m')"
    by (auto split: sum.splits prod.splits)
  have fd: "decl_tyvars_fresh_ok d" and fds: "list_all decl_tyvars_fresh_ok ds"
    using Cons.prems(3) by simp_all
  have inv1: "elab_decls_invariant env0 ownAbstract env1 elabEnv1 m1"
    using elab_declaration_invariant[OF Cons.prems(2) fd step] .
  show ?case
    using Cons.IH[OF rest inv1 fds] .
qed


(* ========================================================================== *)
(* Runtime-soundness of the recorded realizations                             *)
(* ========================================================================== *)

(* The linker's final gate, link_runtime_ok, re-checks that no *runtime*
   abstract type is realized by a ghost type. The links the pipeline derives
   but never executes (LINKING.md step 8(b): the implementation module linked
   against its interface context) need that gate discharged by proof, from
   the checks the elaborator ran at each realization site. This section
   carries those site checks to the end of the fold: every entry of
   CM_TypeSubst m whose name is a runtime abstract type of the *context* maps
   to a type that is runtime in the state env. The property is a parallel
   fold lemma rather than a new elab_decls_invariant conjunct: it consumes
   the invariant, but nothing in the invariant needs it.

   The name's runtime-ness is judged against the context env0: the state env
   forgets a name at the moment it is realized (apply_realization deletes it
   from the type-variable fields), but env0 - for the implementation run, the
   linked interface context - remembers it, and it is env0's
   TE_RuntimeTypeVars that the link-time check is keyed on. *)

definition subst_runtime_ok :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> CoreModule \<Rightarrow> bool" where
  "subst_runtime_ok env0 env m =
    (\<forall>n ty. fmlookup (CM_TypeSubst m) n = Some ty \<longrightarrow>
            n |\<in>| TE_RuntimeTypeVars env0 \<longrightarrow> is_runtime_type env ty)"

(* Counterpart of is_runtime_type_shrink_tyvar for a growing runtime set
   (the new-abstract-type step). *)
lemma is_runtime_type_grow_runtime_tyvars:
  assumes rt: "is_runtime_type env ty"
      and sub: "TE_RuntimeTypeVars env |\<subseteq>| TE_RuntimeTypeVars env'"
      and gd: "TE_GhostDatatypes env' = TE_GhostDatatypes env"
  shows "is_runtime_type env' ty"
proof (rule is_runtime_type_transfer[OF rt _ gd])
  have "type_tyvars ty \<subseteq> fset (TE_RuntimeTypeVars env)"
    by (rule is_runtime_type_tyvars_subset[OF rt])
  then show "type_tyvars ty \<subseteq> fset (TE_RuntimeTypeVars env')"
    using sub by (metis less_eq_fset.rep_eq subset_trans)
qed

(* Steps that touch neither the substitution nor the two env fields
   is_runtime_type reads (constants, functions, transparent typedefs). *)
lemma subst_runtime_ok_env_cong:
  assumes rtok: "subst_runtime_ok env0 env m"
      and subst_eq: "CM_TypeSubst m' = CM_TypeSubst m"
      and rtv: "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env"
      and gd: "TE_GhostDatatypes env' = TE_GhostDatatypes env"
  shows "subst_runtime_ok env0 env' m'"
  using rtok is_runtime_type_cong_env[OF gd rtv]
  unfolding subst_runtime_ok_def subst_eq by blast

(* Adding a datatype can grow TE_GhostDatatypes, but only at a name that was
   not previously a datatype; the recorded entries are well-kinded in the old
   env, so their datatype heads all resolve there and keep their ghost
   status. *)
lemma subst_runtime_ok_add_datatype:
  assumes rtok: "subst_runtime_ok env0 env m"
      and tswk: "typesubst_well_kinded env (CM_TypeSubst m)"
      and fresh_dt: "name |\<notin>| fmdom (TE_Datatypes env)"
      and env'_eq: "env' = tyenv_add_datatype name tyvars ctors isGhost env"
      and subst_eq: "CM_TypeSubst m' = CM_TypeSubst m"
  shows "subst_runtime_ok env0 env' m'"
unfolding subst_runtime_ok_def proof (intro allI impI)
  fix n ty
  assume lk: "fmlookup (CM_TypeSubst m') n = Some ty"
     and n0: "n |\<in>| TE_RuntimeTypeVars env0"
  have lk0: "fmlookup (CM_TypeSubst m) n = Some ty"
    using lk unfolding subst_eq .
  have rt: "is_runtime_type env ty"
    using rtok lk0 n0 unfolding subst_runtime_ok_def by blast
  have wk: "is_well_kinded env ty"
    using tswk lk0 unfolding typesubst_well_kinded_def by blast
  show "is_runtime_type env' ty"
  proof (rule is_runtime_type_transfer_mono[OF wk rt])
    show "fset (TE_RuntimeTypeVars env) \<subseteq> fset (TE_RuntimeTypeVars env')"
      unfolding env'_eq tyenv_add_datatype_def by simp
  next
    fix nn assume nn_in: "nn |\<in>| fmdom (TE_Datatypes env)"
    then have "nn \<noteq> name" using fresh_dt by auto
    then show "nn |\<in>| TE_GhostDatatypes env' \<longleftrightarrow> nn |\<in>| TE_GhostDatatypes env"
      unfolding env'_eq tyenv_add_datatype_def by auto
  qed
qed

(* The realization step. The new entry is runtime by the site check
   (transported past the deletion of name, which it cannot mention); the old
   entries have the singleton substitution applied, which preserves
   runtime-ness because it replaces a runtime type variable by a runtime
   type (apply_subst_preserves_runtime). *)
lemma apply_realization_subst_runtime:
  assumes rtok: "subst_runtime_ok env0 env m"
      and bridge: "name |\<in>| TE_RuntimeTypeVars env0 \<longrightarrow> name |\<in>| TE_RuntimeTypeVars env"
      and tgt: "name |\<in>| TE_RuntimeTypeVars env \<longrightarrow> is_runtime_type env target"
      and noself: "name \<notin> type_tyvars target"
      and res: "apply_realization name target env elabEnv m = (env', elabEnv', m')"
  shows "subst_runtime_ok env0 env' m'"
proof -
  let ?s = "fmupd name target fmempty"
  have env'_eq: "env' = (apply_subst_to_tyenv ?s env)
           \<lparr> TE_TypeVars := TE_TypeVars env |-| {|name|},
             TE_RuntimeTypeVars := TE_RuntimeTypeVars env |-| {|name|},
             TE_AbstractTypes := TE_AbstractTypes env |-| {|name|} \<rparr>"
   and m'_eq: "m' = m \<lparr> CM_TypeSubst := fmupd name target
                          (fmmap (apply_subst ?s) (CM_TypeSubst m)) \<rparr>"
    using res unfolding apply_realization_def Let_def by auto
  have rtv': "TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env |-| {|name|}"
   and gd': "TE_GhostDatatypes env' = TE_GhostDatatypes env"
    unfolding env'_eq apply_subst_to_tyenv_def by simp_all
  have tgt': "name |\<in>| TE_RuntimeTypeVars env \<longrightarrow> is_runtime_type env' target"
    using tgt is_runtime_type_shrink_tyvar[OF _ noself rtv' gd'] by blast
  show ?thesis
  unfolding subst_runtime_ok_def proof (intro allI impI)
    fix n ty
    assume lk: "fmlookup (CM_TypeSubst m') n = Some ty"
       and n0: "n |\<in>| TE_RuntimeTypeVars env0"
    show "is_runtime_type env' ty"
    proof (cases "n = name")
      case True
      then have "ty = target" using lk unfolding m'_eq by simp
      then show ?thesis using True n0 bridge tgt' by blast
    next
      case False
      then have "fmlookup (fmmap (apply_subst ?s) (CM_TypeSubst m)) n = Some ty"
        using lk unfolding m'_eq by simp
      then obtain ty0 where lk0: "fmlookup (CM_TypeSubst m) n = Some ty0"
                        and ty_eq: "ty = apply_subst ?s ty0"
        by auto
      have rt0: "is_runtime_type env ty0"
        using rtok lk0 n0 unfolding subst_runtime_ok_def by blast
      have "is_runtime_type env' (apply_subst ?s ty0)"
      proof (rule apply_subst_preserves_runtime[OF rt0 gd'])
        fix v assume v_rt: "v |\<in>| TE_RuntimeTypeVars env"
        show "case fmlookup ?s v of
                Some ty' \<Rightarrow> is_runtime_type env' ty'
              | None \<Rightarrow> v |\<in>| TE_RuntimeTypeVars env'"
          using v_rt tgt' rtv' by (cases "v = name") auto
      qed
      then show ?thesis using ty_eq by simp
    qed
  qed
qed

(* ---- The four declaration kinds ---- *)

lemma elab_const_decl_subst_runtime:
  assumes rtok: "subst_runtime_ok env0 env m"
      and e: "elab_const_decl env elabEnv m dc = Inr (env', elabEnv', m')"
  shows "subst_runtime_ok env0 env' m'"
proof -
  have "CM_TypeSubst m' = CM_TypeSubst m
        \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env
        \<and> TE_GhostDatatypes env' = TE_GhostDatatypes env"
    using e unfolding elab_const_decl_def tyenv_add_global_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis
    using subst_runtime_ok_env_cong[OF rtok] by blast
qed

lemma elab_function_decl_subst_runtime:
  assumes rtok: "subst_runtime_ok env0 env m"
      and e: "elab_function_decl env elabEnv m df = Inr (env', elabEnv', m')"
  shows "subst_runtime_ok env0 env' m'"
proof -
  have "CM_TypeSubst m' = CM_TypeSubst m
        \<and> TE_RuntimeTypeVars env' = TE_RuntimeTypeVars env
        \<and> TE_GhostDatatypes env' = TE_GhostDatatypes env"
    using e unfolding elab_function_decl_def tyenv_add_function_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis
    using subst_runtime_ok_env_cong[OF rtok] by blast
qed

lemma elab_datatype_decl_subst_runtime:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and rtok: "subst_runtime_ok env0 env m"
      and e: "elab_datatype_decl env elabEnv ownAbstract m dd = Inr (env', elabEnv', m')"
  shows "subst_runtime_ok env0 env' m'"
proof -
  let ?name = "DD_Name dd"
  have env_eq: "env = module_context_env env0 m"
   and tswk: "typesubst_well_kinded env (CM_TypeSubst m)"
   and wf: "tyenv_well_formed env"
    using inv unfolding elab_decls_invariant_def by blast+
  from e show ?thesis
  proof (cases rule: elab_datatype_decl_Inr_elim)
    case (Plain ctorInfo isGhost)
    \<comment> \<open>A plain datatype: the substitution is untouched, and the (possibly
       ghost) new datatype is a fresh name.\<close>
    have fresh_dt: "?name |\<notin>| fmdom (TE_Datatypes env)"
      using Plain(2) unfolding type_name_in_scope_def by blast
    show ?thesis
      by (rule subst_runtime_ok_add_datatype[OF rtok tswk fresh_dt Plain(10)])
         (simp add: Plain(12))
  next
    case (Realize ctorInfo isGhost)
    \<comment> \<open>The ADT realization: add the datatype (fresh as a datatype name, by
       the duplicate check), then realize name by it. If the abstract type
       was runtime, the guard forced the datatype non-ghost.\<close>
    note r = Realize(1) and fresh_dt = Realize(4) and res = Realize(14)
    have rt_g: "?name |\<in>| TE_RuntimeTypeVars env \<longrightarrow> \<not> isGhost"
      using Realize(12) by blast
    let ?ctors1 = "map (\<lambda>(cn, pay, _). (cn, pay)) ctorInfo"
    let ?env1 = "tyenv_add_datatype ?name (DD_TyArgs dd) ?ctors1 isGhost env"
    let ?m1 = "m \<lparr> CM_TyEnv := tyenv_add_datatype ?name (DD_TyArgs dd) ?ctors1 isGhost
                                 (CM_TyEnv m) \<rparr>"
    have rtok1: "subst_runtime_ok env0 ?env1 ?m1"
      by (rule subst_runtime_ok_add_datatype[OF rtok tswk fresh_dt refl]) simp
    have rtv1: "TE_RuntimeTypeVars ?env1 = TE_RuntimeTypeVars env"
      unfolding tyenv_add_datatype_def by simp
    have tv_disj: "TE_TypeVars env |\<inter>| fmdom (CM_TypeSubst m) = {||}"
      using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
    have ndom: "?name |\<notin>| fmdom (CM_TypeSubst m)"
      using r tv_disj by (metis fempty_iff finter_iff)
    have bridge: "?name |\<in>| TE_RuntimeTypeVars env0
                    \<longrightarrow> ?name |\<in>| TE_RuntimeTypeVars ?env1"
      unfolding rtv1 env_eq module_context_env_tyvar_fields(2)
      using ndom env_eq module_context_env_tyvar_fields(2) rtv1 by force
    have ghost_sub: "TE_GhostDatatypes env |\<subseteq>| fmdom (TE_Datatypes env)"
      using wf unfolding tyenv_well_formed_def tyenv_ghost_datatypes_subset_def by blast
    have name_ng: "?name |\<notin>| TE_GhostDatatypes env"
      using ghost_sub fresh_dt by blast
    have tgt: "?name |\<in>| TE_RuntimeTypeVars ?env1
                 \<longrightarrow> is_runtime_type ?env1 (CoreTy_Datatype ?name [])"
      using rt_g name_ng unfolding tyenv_add_datatype_def by auto
    have noself: "?name \<notin> type_tyvars (CoreTy_Datatype ?name [])"
      by simp
    show ?thesis
      by (rule apply_realization_subst_runtime[OF rtok1 bridge tgt noself res])
  qed
qed

lemma elab_typedef_decl_subst_runtime:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and rtok: "subst_runtime_ok env0 env m"
      and e: "elab_typedef_decl env elabEnv ownAbstract m dt = Inr (env', elabEnv', m')"
  shows "subst_runtime_ok env0 env' m'"
  using e
proof (cases rule: elab_typedef_decl_Inr_elim)
  case (Realize ty target)
  \<comment> \<open>A realization: the site checks are exactly the hypotheses of the
     realization step.\<close>
  note noself = Realize(7) and rt_ok = Realize(8) and res = Realize(10)
  have env_eq: "env = module_context_env env0 m"
    using inv unfolding elab_decls_invariant_def by blast
  have tv_disj: "TE_TypeVars env |\<inter>| fmdom (CM_TypeSubst m) = {||}"
    using module_context_env_subst_disjoint(1)[of env0 m] env_eq by simp
  have ndom: "DT_Name dt |\<notin>| fmdom (CM_TypeSubst m)"
    using Realize(2) tv_disj by (metis fempty_iff finter_iff)
  have bridge: "DT_Name dt |\<in>| TE_RuntimeTypeVars env0
                  \<longrightarrow> DT_Name dt |\<in>| TE_RuntimeTypeVars env"
    unfolding env_eq module_context_env_tyvar_fields(2) using ndom by auto
  show ?thesis
    by (rule apply_realization_subst_runtime[OF rtok bridge rt_ok noself res])
next
  case NewAbstract
  \<comment> \<open>A new abstract type: the runtime type variables can only grow.\<close>
  have grow: "TE_RuntimeTypeVars env |\<subseteq>| TE_RuntimeTypeVars env'"
   and gd: "TE_GhostDatatypes env' = TE_GhostDatatypes env"
    unfolding NewAbstract(6) tyenv_add_abstract_type_def by auto
  have subst_eq: "CM_TypeSubst m' = CM_TypeSubst m"
    unfolding NewAbstract(8) by simp
  show ?thesis
    using rtok is_runtime_type_grow_runtime_tyvars[OF _ grow gd]
    unfolding subst_runtime_ok_def subst_eq by blast
next
  case (Transparent ty target)
  \<comment> \<open>A transparent typedef changes neither the env nor the module.\<close>
  show ?thesis using rtok unfolding Transparent(8) Transparent(10) .
qed

(* ---- The dispatcher, the list, and the top-level fold ---- *)

lemma elab_declaration_subst_runtime:
  assumes inv: "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and rtok: "subst_runtime_ok env0 env m"
      and elab: "elab_declaration env elabEnv ownAbstract m d = Inr (env', elabEnv', m')"
  shows "subst_runtime_ok env0 env' m'"
proof (cases d)
  case (BabDecl_Const dc)
  then have e: "elab_const_decl env elabEnv m dc = Inr (env', elabEnv', m')"
    using elab by simp
  show ?thesis by (rule elab_const_decl_subst_runtime[OF rtok e])
next
  case (BabDecl_Function df)
  then have e: "elab_function_decl env elabEnv m df = Inr (env', elabEnv', m')"
    using elab by simp
  show ?thesis by (rule elab_function_decl_subst_runtime[OF rtok e])
next
  case (BabDecl_Datatype dd)
  then have e: "elab_datatype_decl env elabEnv ownAbstract m dd = Inr (env', elabEnv', m')"
    using elab by simp
  show ?thesis by (rule elab_datatype_decl_subst_runtime[OF inv rtok e])
next
  case (BabDecl_Typedef dt)
  then have e: "elab_typedef_decl env elabEnv ownAbstract m dt = Inr (env', elabEnv', m')"
    using elab by simp
  show ?thesis by (rule elab_typedef_decl_subst_runtime[OF inv rtok e])
qed

lemma elab_declaration_list_subst_runtime:
  assumes "elab_declaration_list env elabEnv ownAbstract m ds = Inr (env', elabEnv', m')"
      and "elab_decls_invariant env0 ownAbstract env elabEnv m"
      and "subst_runtime_ok env0 env m"
      and "list_all decl_tyvars_fresh_ok ds"
  shows "subst_runtime_ok env0 env' m'"
  using assms
proof (induction ds arbitrary: env elabEnv m)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  from Cons.prems(1) obtain env1 elabEnv1 m1 where
    step: "elab_declaration env elabEnv ownAbstract m d = Inr (env1, elabEnv1, m1)" and
    rest: "elab_declaration_list env1 elabEnv1 ownAbstract m1 ds = Inr (env', elabEnv', m')"
    by (auto split: sum.splits prod.splits)
  have fd: "decl_tyvars_fresh_ok d" and fds: "list_all decl_tyvars_fresh_ok ds"
    using Cons.prems(4) by simp_all
  have inv1: "elab_decls_invariant env0 ownAbstract env1 elabEnv1 m1"
    using elab_declaration_invariant[OF Cons.prems(2) fd step] .
  have rtok1: "subst_runtime_ok env0 env1 m1"
    using elab_declaration_subst_runtime[OF Cons.prems(2) Cons.prems(3) step] .
  show ?case
    using Cons.IH[OF rest inv1 rtok1 fds] .
qed

(* Companion of elab_declarations_invariant (ElabModuleCorrect.thy): the same
   final state env additionally satisfies the runtime-soundness of the
   recorded substitution. *)
lemma elab_declarations_subst_runtime:
  assumes ctx: "elab_context_ok env0 ownAbstract"
      and ee: "elabenv_well_formed env0 elabEnv0"
      and fresh: "list_all decl_tyvars_fresh_ok decls"
      and elab: "elab_declarations env0 elabEnv0 ownAbstract decls = Inr (M, elabEnv')"
  obtains envF where "elab_decls_invariant env0 ownAbstract envF elabEnv' M"
                 and "subst_runtime_ok env0 envF M"
proof -
  have init: "elab_decls_invariant env0 ownAbstract env0 elabEnv0 empty_core_module"
    using elab_decls_invariant_init[OF ctx ee] .
  have init_rt: "subst_runtime_ok env0 env0 empty_core_module"
    unfolding subst_runtime_ok_def empty_core_module_def by simp
  from elab obtain envF where
    run: "elab_declaration_list env0 elabEnv0 ownAbstract empty_core_module decls
            = Inr (envF, elabEnv', M)"
    unfolding elab_declarations_def
    by (auto split: sum.splits prod.splits)
  have "elab_decls_invariant env0 ownAbstract envF elabEnv' M"
    using elab_declaration_list_invariant[OF run init fresh] .
  moreover have "subst_runtime_ok env0 envF M"
    using elab_declaration_list_subst_runtime[OF run init init_rt fresh] .
  ultimately show thesis by (rule that)
qed


(* ========================================================================== *)
(* Provenance of the module's own type variables                              *)
(* ========================================================================== *)

(* The abstract types a declaration list can introduce: the names of its
   definition-less typedefs. This is what connects the produced module's
   TE_TypeVars to the syntax - the whole-program composition (step 8) needs
   "every abstract type of a module's interface is realized by its own
   implementation", and check_completeness speaks about abstract typedef
   declarations while the module's env speaks about TE_TypeVars; the fold
   lemma below is the bridge. *)
fun decl_abstract_names :: "BabDeclaration \<Rightarrow> string fset" where
  "decl_abstract_names (BabDecl_Typedef dt) =
     (if DT_Definition dt = None then {|DT_Name dt|} else {||})"
| "decl_abstract_names _ = {||}"

definition decls_abstract_names :: "BabDeclaration list \<Rightarrow> string fset" where
  "decls_abstract_names ds = funion_list (map decl_abstract_names ds)"

(* A single declaration grows the module's TE_TypeVars by at most its own
   abstract-typedef name: only the new-abstract-type branch of
   elab_typedef_decl touches the module's type-variable field
   (tyenv_add_global, tyenv_add_function and tyenv_add_datatype record other
   fields; apply_realization does not rewrite the module's own CM_TyEnv at
   all). *)
lemma elab_declaration_own_tyvars:
  assumes e: "elab_declaration env elabEnv ownAbstract m d = Inr (env', elabEnv', m')"
  shows "TE_TypeVars (CM_TyEnv m') |\<subseteq>| TE_TypeVars (CM_TyEnv m) |\<union>| decl_abstract_names d"
proof (cases d)
  case (BabDecl_Const dc)
  have "TE_TypeVars (CM_TyEnv m') = TE_TypeVars (CM_TyEnv m)"
    using e unfolding BabDecl_Const elab_declaration.simps
                      elab_const_decl_def tyenv_add_global_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis by (simp add: BabDecl_Const)
next
  case (BabDecl_Function df)
  have "TE_TypeVars (CM_TyEnv m') = TE_TypeVars (CM_TyEnv m)"
    using e unfolding BabDecl_Function elab_declaration.simps
                      elab_function_decl_def tyenv_add_function_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis by (simp add: BabDecl_Function)
next
  case (BabDecl_Datatype dd)
  have "TE_TypeVars (CM_TyEnv m') = TE_TypeVars (CM_TyEnv m)"
    using e unfolding BabDecl_Datatype elab_declaration.simps
                      elab_datatype_decl_def apply_realization_def
                      tyenv_add_datatype_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis by (simp add: BabDecl_Datatype)
next
  case (BabDecl_Typedef dt)
  show ?thesis
    using e unfolding BabDecl_Typedef elab_declaration.simps
                      elab_typedef_decl_def apply_realization_def
                      tyenv_add_abstract_type_def Let_def
    by (auto split: option.splits sum.splits if_splits)
qed

(* Lifted to the declaration list. *)
lemma elab_declaration_list_own_tyvars:
  assumes "elab_declaration_list env elabEnv ownAbstract m ds = Inr (env', elabEnv', m')"
  shows "TE_TypeVars (CM_TyEnv m') |\<subseteq>| TE_TypeVars (CM_TyEnv m) |\<union>| decls_abstract_names ds"
  using assms
proof (induction ds arbitrary: env elabEnv m)
  case Nil
  then show ?case by (simp add: decls_abstract_names_def)
next
  case (Cons d ds)
  from Cons.prems obtain env1 elabEnv1 m1 where
    step: "elab_declaration env elabEnv ownAbstract m d = Inr (env1, elabEnv1, m1)" and
    rest: "elab_declaration_list env1 elabEnv1 ownAbstract m1 ds = Inr (env', elabEnv', m')"
    by (auto split: sum.splits prod.splits)
  have s1: "TE_TypeVars (CM_TyEnv m1)
              |\<subseteq>| TE_TypeVars (CM_TyEnv m) |\<union>| decl_abstract_names d"
    using elab_declaration_own_tyvars[OF step] .
  have s2: "TE_TypeVars (CM_TyEnv m')
              |\<subseteq>| TE_TypeVars (CM_TyEnv m1) |\<union>| decls_abstract_names ds"
    using Cons.IH[OF rest] .
  show ?case
    using s1 s2 unfolding decls_abstract_names_def by auto
qed

(* The top-level form: the produced module's type variables all name abstract
   typedefs of the input list (the fold starts from the empty module). *)
lemma elab_declarations_own_tyvars:
  assumes "elab_declarations env elabEnv ownAbstract decls = Inr (M, elabEnv')"
  shows "TE_TypeVars (CM_TyEnv M) |\<subseteq>| decls_abstract_names decls"
proof -
  from assms obtain envF where
    run: "elab_declaration_list env elabEnv ownAbstract empty_core_module decls
            = Inr (envF, elabEnv', M)"
    unfolding elab_declarations_def by (auto split: sum.splits prod.splits)
  have "TE_TypeVars (CM_TyEnv empty_core_module) = {||}"
    by (simp add: empty_core_module_def empty_module_tyenv_def)
  then show ?thesis
    using elab_declaration_list_own_tyvars[OF run] by auto
qed

(* The collected names depend only on the multiset of declarations, so they
   survive the dependency sort. *)
lemma decls_abstract_names_mset_cong:
  assumes "mset ds = mset ds'"
  shows "decls_abstract_names ds = decls_abstract_names ds'"
  unfolding decls_abstract_names_def
  using funion_list_map_cong[OF assms] .


(* ========================================================================== *)
(* Provenance of the module's declared-but-undefined names                    *)
(* ========================================================================== *)

(* The global-variable (resp. function) names a declaration list can declare
   without defining: consts without a value, non-extern functions without a
   body. Whole-program closedness (step 8c) needs "everything the linked
   program declares is defined"; per module, the env speaks about the domains
   of TE_GlobalVars/TE_Functions versus CM_GlobalVars/CM_Functions, while
   check_completeness and check_impl_definitions speak about declarations -
   the fold lemmas below are the bridge. *)
fun decl_undefined_consts :: "BabDeclaration \<Rightarrow> string fset" where
  "decl_undefined_consts (BabDecl_Const dc) =
     (if DC_Value dc = None then {|DC_Name dc|} else {||})"
| "decl_undefined_consts _ = {||}"

fun decl_undefined_funs :: "BabDeclaration \<Rightarrow> string fset" where
  "decl_undefined_funs (BabDecl_Function df) =
     (if DF_Body df = None \<and> \<not> DF_Extern df then {|DF_Name df|} else {||})"
| "decl_undefined_funs _ = {||}"

definition decls_undefined_consts :: "BabDeclaration list \<Rightarrow> string fset" where
  "decls_undefined_consts ds = funion_list (map decl_undefined_consts ds)"

definition decls_undefined_funs :: "BabDeclaration list \<Rightarrow> string fset" where
  "decls_undefined_funs ds = funion_list (map decl_undefined_funs ds)"

(* A single declaration grows the module's declared-but-undefined globals
   (the TE_GlobalVars names without a CM_GlobalVars entry) by at most its own
   undefined-const name: elab_const_decl adds the declaration and the
   definition together except in its no-value case, and definitions are never
   removed; no other declaration form touches either field. *)
lemma elab_declaration_undefined_globals:
  assumes e: "elab_declaration env elabEnv ownAbstract m d = Inr (env', elabEnv', m')"
  shows "fmdom (TE_GlobalVars (CM_TyEnv m')) |-| fmdom (CM_GlobalVars m')
           |\<subseteq>| (fmdom (TE_GlobalVars (CM_TyEnv m)) |-| fmdom (CM_GlobalVars m))
                |\<union>| decl_undefined_consts d"
proof (cases d)
  case (BabDecl_Const dc)
  show ?thesis
    using e unfolding BabDecl_Const elab_declaration.simps
                      elab_const_decl_def tyenv_add_global_def Let_def
    by (auto split: option.splits sum.splits if_splits)
next
  case (BabDecl_Function df)
  have "TE_GlobalVars (CM_TyEnv m') = TE_GlobalVars (CM_TyEnv m)
        \<and> CM_GlobalVars m' = CM_GlobalVars m"
    using e unfolding BabDecl_Function elab_declaration.simps
                      elab_function_decl_def tyenv_add_function_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis by (simp add: BabDecl_Function)
next
  case (BabDecl_Datatype dd)
  have "TE_GlobalVars (CM_TyEnv m') = TE_GlobalVars (CM_TyEnv m)
        \<and> CM_GlobalVars m' = CM_GlobalVars m"
    using e unfolding BabDecl_Datatype elab_declaration.simps
                      elab_datatype_decl_def apply_realization_def
                      tyenv_add_datatype_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis by (simp add: BabDecl_Datatype)
next
  case (BabDecl_Typedef dt)
  have "TE_GlobalVars (CM_TyEnv m') = TE_GlobalVars (CM_TyEnv m)
        \<and> CM_GlobalVars m' = CM_GlobalVars m"
    using e unfolding BabDecl_Typedef elab_declaration.simps
                      elab_typedef_decl_def apply_realization_def
                      tyenv_add_abstract_type_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis by (simp add: BabDecl_Typedef)
qed

(* The same for functions: only elab_function_decl touches TE_Functions or
   CM_Functions, and it withholds the CM_Functions entry exactly for a
   bodiless non-extern function (an extern declaration IS a definition - its
   entry carries CF_Body = None). *)
lemma elab_declaration_undefined_funs:
  assumes e: "elab_declaration env elabEnv ownAbstract m d = Inr (env', elabEnv', m')"
  shows "fmdom (TE_Functions (CM_TyEnv m')) |-| fmdom (CM_Functions m')
           |\<subseteq>| (fmdom (TE_Functions (CM_TyEnv m)) |-| fmdom (CM_Functions m))
                |\<union>| decl_undefined_funs d"
proof (cases d)
  case (BabDecl_Const dc)
  have "TE_Functions (CM_TyEnv m') = TE_Functions (CM_TyEnv m)
        \<and> CM_Functions m' = CM_Functions m"
    using e unfolding BabDecl_Const elab_declaration.simps
                      elab_const_decl_def tyenv_add_global_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis by (simp add: BabDecl_Const)
next
  case (BabDecl_Function df)
  show ?thesis
    using e unfolding BabDecl_Function elab_declaration.simps
                      elab_function_decl_def tyenv_add_function_def Let_def
    by (auto split: option.splits sum.splits if_splits)
next
  case (BabDecl_Datatype dd)
  have "TE_Functions (CM_TyEnv m') = TE_Functions (CM_TyEnv m)
        \<and> CM_Functions m' = CM_Functions m"
    using e unfolding BabDecl_Datatype elab_declaration.simps
                      elab_datatype_decl_def apply_realization_def
                      tyenv_add_datatype_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis by (simp add: BabDecl_Datatype)
next
  case (BabDecl_Typedef dt)
  have "TE_Functions (CM_TyEnv m') = TE_Functions (CM_TyEnv m)
        \<and> CM_Functions m' = CM_Functions m"
    using e unfolding BabDecl_Typedef elab_declaration.simps
                      elab_typedef_decl_def apply_realization_def
                      tyenv_add_abstract_type_def Let_def
    by (auto split: option.splits sum.splits if_splits)
  then show ?thesis by (simp add: BabDecl_Typedef)
qed

(* Lifted to the declaration list. *)
lemma elab_declaration_list_undefined_globals:
  assumes "elab_declaration_list env elabEnv ownAbstract m ds = Inr (env', elabEnv', m')"
  shows "fmdom (TE_GlobalVars (CM_TyEnv m')) |-| fmdom (CM_GlobalVars m')
           |\<subseteq>| (fmdom (TE_GlobalVars (CM_TyEnv m)) |-| fmdom (CM_GlobalVars m))
                |\<union>| decls_undefined_consts ds"
  using assms
proof (induction ds arbitrary: env elabEnv m)
  case Nil
  then show ?case by (simp add: decls_undefined_consts_def)
next
  case (Cons d ds)
  from Cons.prems obtain env1 elabEnv1 m1 where
    step: "elab_declaration env elabEnv ownAbstract m d = Inr (env1, elabEnv1, m1)" and
    rest: "elab_declaration_list env1 elabEnv1 ownAbstract m1 ds = Inr (env', elabEnv', m')"
    by (auto split: sum.splits prod.splits)
  have s1: "fmdom (TE_GlobalVars (CM_TyEnv m1)) |-| fmdom (CM_GlobalVars m1)
              |\<subseteq>| (fmdom (TE_GlobalVars (CM_TyEnv m)) |-| fmdom (CM_GlobalVars m))
                   |\<union>| decl_undefined_consts d"
    using elab_declaration_undefined_globals[OF step] .
  have s2: "fmdom (TE_GlobalVars (CM_TyEnv m')) |-| fmdom (CM_GlobalVars m')
              |\<subseteq>| (fmdom (TE_GlobalVars (CM_TyEnv m1)) |-| fmdom (CM_GlobalVars m1))
                   |\<union>| decls_undefined_consts ds"
    using Cons.IH[OF rest] .
  show ?case
    using s1 s2 unfolding decls_undefined_consts_def by auto
qed

lemma elab_declaration_list_undefined_funs:
  assumes "elab_declaration_list env elabEnv ownAbstract m ds = Inr (env', elabEnv', m')"
  shows "fmdom (TE_Functions (CM_TyEnv m')) |-| fmdom (CM_Functions m')
           |\<subseteq>| (fmdom (TE_Functions (CM_TyEnv m)) |-| fmdom (CM_Functions m))
                |\<union>| decls_undefined_funs ds"
  using assms
proof (induction ds arbitrary: env elabEnv m)
  case Nil
  then show ?case by (simp add: decls_undefined_funs_def)
next
  case (Cons d ds)
  from Cons.prems obtain env1 elabEnv1 m1 where
    step: "elab_declaration env elabEnv ownAbstract m d = Inr (env1, elabEnv1, m1)" and
    rest: "elab_declaration_list env1 elabEnv1 ownAbstract m1 ds = Inr (env', elabEnv', m')"
    by (auto split: sum.splits prod.splits)
  have s1: "fmdom (TE_Functions (CM_TyEnv m1)) |-| fmdom (CM_Functions m1)
              |\<subseteq>| (fmdom (TE_Functions (CM_TyEnv m)) |-| fmdom (CM_Functions m))
                   |\<union>| decl_undefined_funs d"
    using elab_declaration_undefined_funs[OF step] .
  have s2: "fmdom (TE_Functions (CM_TyEnv m')) |-| fmdom (CM_Functions m')
              |\<subseteq>| (fmdom (TE_Functions (CM_TyEnv m1)) |-| fmdom (CM_Functions m1))
                   |\<union>| decls_undefined_funs ds"
    using Cons.IH[OF rest] .
  show ?case
    using s1 s2 unfolding decls_undefined_funs_def by auto
qed

(* The top-level forms: the fold starts from the empty module, so every
   declared name of the produced module is either defined by the module or
   named by an undefined-const/-function declaration of the input list. *)
lemma elab_declarations_undefined_globals:
  assumes "elab_declarations env elabEnv ownAbstract decls = Inr (M, elabEnv')"
  shows "fmdom (TE_GlobalVars (CM_TyEnv M))
           |\<subseteq>| fmdom (CM_GlobalVars M) |\<union>| decls_undefined_consts decls"
proof -
  from assms obtain envF where
    run: "elab_declaration_list env elabEnv ownAbstract empty_core_module decls
            = Inr (envF, elabEnv', M)"
    unfolding elab_declarations_def by (auto split: sum.splits prod.splits)
  have "fmdom (TE_GlobalVars (CM_TyEnv empty_core_module)) = {||}"
    by (simp add: empty_core_module_def empty_module_tyenv_def)
  then show ?thesis
    using elab_declaration_list_undefined_globals[OF run] by auto
qed

lemma elab_declarations_undefined_funs:
  assumes "elab_declarations env elabEnv ownAbstract decls = Inr (M, elabEnv')"
  shows "fmdom (TE_Functions (CM_TyEnv M))
           |\<subseteq>| fmdom (CM_Functions M) |\<union>| decls_undefined_funs decls"
proof -
  from assms obtain envF where
    run: "elab_declaration_list env elabEnv ownAbstract empty_core_module decls
            = Inr (envF, elabEnv', M)"
    unfolding elab_declarations_def by (auto split: sum.splits prod.splits)
  have "fmdom (TE_Functions (CM_TyEnv empty_core_module)) = {||}"
    by (simp add: empty_core_module_def empty_module_tyenv_def)
  then show ?thesis
    using elab_declaration_list_undefined_funs[OF run] by auto
qed

(* The collected names depend only on the multiset of declarations, so they
   survive the dependency sort. *)
lemma decls_undefined_consts_mset_cong:
  assumes "mset ds = mset ds'"
  shows "decls_undefined_consts ds = decls_undefined_consts ds'"
  unfolding decls_undefined_consts_def
  using funion_list_map_cong[OF assms] .

lemma decls_undefined_funs_mset_cong:
  assumes "mset ds = mset ds'"
  shows "decls_undefined_funs ds = decls_undefined_funs ds'"
  unfolding decls_undefined_funs_def
  using funion_list_map_cong[OF assms] .


(* ========================================================================== *)
(* The link-step assembly                                                     *)
(* ========================================================================== *)

(* On a two-module link whose left operand carries no substitution, the merged
   substitution is the right operand's own: the raw union of the two input
   substitutions is the right one alone, and an idempotent substitution is its
   own (unique) closure. *)
lemma link_pair_subst:
  assumes link: "link_modules [i, m] = Inr l"
      and i_empty: "CM_TypeSubst i = fmempty"
      and idem: "idempotent_subst (CM_TypeSubst m)"
  shows "CM_TypeSubst l = CM_TypeSubst m"
proof -
  have u_eq: "fmlist_union (map CM_TypeSubst [i, m]) = CM_TypeSubst m"
    by (simp add: fmlist_union_def i_empty)
  have acyc: "acyclic_subst_deps (CM_TypeSubst m)"
    using link_modules_success_facts(3)[OF link] u_eq by simp
  have clos: "is_subst_closure (CM_TypeSubst m) (CM_TypeSubst l)"
    using link_modules_success_facts(4)[OF link] u_eq by simp
  show ?thesis
    using subst_closure_unique[OF acyc clos is_subst_closure_self[OF idem]] .
qed

(* On such a link (with the left operand at module scope), the normalized
   linked env is exactly the left env combined with the right module and
   resolved through its substitution - i.e. module_context_env. This equation
   is the M-side pivot of the assembly below: the fold invariant speaks about
   module_context_env, the linked result about CM_TyEnv (normalize_module l),
   and they are the same env. *)
lemma module_context_env_link_pair:
  assumes link: "link_modules [i, m] = Inr l"
      and i_empty: "CM_TypeSubst i = fmempty"
      and idem: "idempotent_subst (CM_TypeSubst m)"
      and scope_i: "tyenv_module_scope (CM_TyEnv i)"
  shows "CM_TyEnv (normalize_module l) = module_context_env (CM_TyEnv i) m"
proof -
  note fL = link_modules_result_fields[OF link]
  have subst_eq: "CM_TypeSubst l = CM_TypeSubst m"
    using link_pair_subst[OF link i_empty idem] .
  let ?pre = "(CM_TyEnv i) \<lparr>
          TE_GlobalVars := TE_GlobalVars (CM_TyEnv i) ++\<^sub>f TE_GlobalVars (CM_TyEnv m),
          TE_GhostGlobals := TE_GhostGlobals (CM_TyEnv i) |\<union>| TE_GhostGlobals (CM_TyEnv m),
          TE_TypeVars := (TE_TypeVars (CM_TyEnv i) |\<union>| TE_TypeVars (CM_TyEnv m))
                           |-| fmdom (CM_TypeSubst m),
          TE_RuntimeTypeVars := (TE_RuntimeTypeVars (CM_TyEnv i)
                                 |\<union>| TE_RuntimeTypeVars (CM_TyEnv m))
                           |-| fmdom (CM_TypeSubst m),
          TE_AbstractTypes := (TE_AbstractTypes (CM_TyEnv i)
                               |\<union>| TE_AbstractTypes (CM_TyEnv m))
                           |-| fmdom (CM_TypeSubst m),
          TE_Functions := TE_Functions (CM_TyEnv i) ++\<^sub>f TE_Functions (CM_TyEnv m),
          TE_Datatypes := TE_Datatypes (CM_TyEnv i) ++\<^sub>f TE_Datatypes (CM_TyEnv m),
          TE_DataCtors := TE_DataCtors (CM_TyEnv i) ++\<^sub>f TE_DataCtors (CM_TyEnv m),
          TE_DataCtorsByType := TE_DataCtorsByType (CM_TyEnv i)
                                  ++\<^sub>f TE_DataCtorsByType (CM_TyEnv m),
          TE_GhostDatatypes := TE_GhostDatatypes (CM_TyEnv i)
                                 |\<union>| TE_GhostDatatypes (CM_TyEnv m)
        \<rparr>"
  have pre: "CM_TyEnv l = ?pre"
  proof (rule CoreTyEnv.equality)
    show "TE_LocalVars (CM_TyEnv l) = TE_LocalVars ?pre"
      using fL(1) scope_i unfolding tyenv_module_scope_def by simp
    show "TE_GlobalVars (CM_TyEnv l) = TE_GlobalVars ?pre"
      by (simp add: fL(2) fmlist_union_def)
    show "TE_GhostLocals (CM_TyEnv l) = TE_GhostLocals ?pre"
      using fL(3) scope_i unfolding tyenv_module_scope_def by simp
    show "TE_GhostGlobals (CM_TyEnv l) = TE_GhostGlobals ?pre"
      by (simp add: fL(4) funion_list_def funion_fempty_right)
    show "TE_ConstLocals (CM_TyEnv l) = TE_ConstLocals ?pre"
      using fL(5) scope_i unfolding tyenv_module_scope_def by simp
    show "TE_TypeVars (CM_TyEnv l) = TE_TypeVars ?pre"
      by (simp add: fL(6) subst_eq funion_list_def funion_fempty_right)
    show "TE_RuntimeTypeVars (CM_TyEnv l) = TE_RuntimeTypeVars ?pre"
      by (simp add: fL(7) subst_eq funion_list_def funion_fempty_right)
    show "TE_AbstractTypes (CM_TyEnv l) = TE_AbstractTypes ?pre"
      by (simp add: fL(8) subst_eq funion_list_def funion_fempty_right)
    show "TE_ReturnType (CM_TyEnv l) = TE_ReturnType ?pre"
      using fL(9) scope_i unfolding tyenv_module_scope_def by simp
    show "TE_FunctionGhost (CM_TyEnv l) = TE_FunctionGhost ?pre"
      using fL(10) scope_i unfolding tyenv_module_scope_def by simp
    show "TE_ProofGoal (CM_TyEnv l) = TE_ProofGoal ?pre"
      using fL(11) scope_i unfolding tyenv_module_scope_def by simp
    show "TE_ProofTopLevel (CM_TyEnv l) = TE_ProofTopLevel ?pre"
      using fL(12) scope_i unfolding tyenv_module_scope_def by simp
    show "TE_Functions (CM_TyEnv l) = TE_Functions ?pre"
      by (simp add: fL(13) fmlist_union_def)
    show "TE_Datatypes (CM_TyEnv l) = TE_Datatypes ?pre"
      by (simp add: fL(14) fmlist_union_def)
    show "TE_DataCtors (CM_TyEnv l) = TE_DataCtors ?pre"
      by (simp add: fL(15) fmlist_union_def)
    show "TE_DataCtorsByType (CM_TyEnv l) = TE_DataCtorsByType ?pre"
      by (simp add: fL(16) fmlist_union_def)
    show "TE_GhostDatatypes (CM_TyEnv l) = TE_GhostDatatypes ?pre"
      by (simp add: fL(17) funion_list_def funion_fempty_right)
    show "CoreTyEnv.more (CM_TyEnv l) = CoreTyEnv.more ?pre"
      by simp
  qed
  show ?thesis
    unfolding normalize_module_def module_context_env_def
    using pre subst_eq by simp
qed

(* The typechecking-transfer halves of the assembly, one for globals and one
   for functions. Each splits a defined name of L between the two operands:
    - M side: the state env equation makes the fold invariant's typechecking
      conjunct literally a statement about the normalized linked env, so M's
      entries transfer by rewriting;
    - I side: I's own globals and functions, rewritten by M's substitution
      (which genuinely rewrites them - realizations resolve I's abstract
      types), re-typecheck in the wider linked env, via the
      substitution-preservation engine (TypeSubstModuleEnv) followed by the
      env-extension lemmas (TyEnvExtension). *)
(* The I-side typing transfer: a term well-typed in I's own env stays
   well-typed (with M's substitution applied to it and its type) in the
   normalized linked env. This is the substitution-preservation engine
   (TypeSubstModuleEnv) run over a mixed intermediate env in the style of
   link_mid_env, followed by its collapse onto the normalized linked env;
   asymmetric here because M is not well-typed on its own - the intermediate
   env's well-formedness comes from I's env and the fold invariant's state
   env instead of from two well-typed operands. *)
(* Well-formedness of the mixed intermediate env. This is the asymmetric
   analogue of link_mid_env_well_formed: M is not well-typed on its own, so
   the M-side entries' conditions come from the fold invariant's state env
   (whose entries are exactly the mid env's M-side ones) rather than from a
   per-module well-typedness hypothesis. *)
lemma elab_link_mid_env_well_formed:
  assumes I_wt: "core_module_well_typed I"
      and I_norm: "CM_TypeSubst I = fmempty"
      and inv: "elab_decls_invariant (CM_TyEnv I) ownAbstract env elabEnv M"
      and link: "link_modules [I, M] = Inr L"
  shows "tyenv_well_formed (link_mid_env I M L)"
proof -
  let ?mid = "link_mid_env I M L"
  let ?\<sigma> = "CM_TypeSubst M"
  let ?envB = "CM_TyEnv (normalize_module M)"

  \<comment> \<open>Shared setup.\<close>
  have env_def: "env = module_context_env (CM_TyEnv I) M"
    and invM: "core_module_invariant M"
    and wf_env: "tyenv_well_formed env"
    using inv unfolding elab_decls_invariant_def by blast+
  have idemM: "idempotent_subst ?\<sigma>"
    using invM unfolding core_module_invariant_def by blast
  have scope_M: "tyenv_module_scope (CM_TyEnv M)"
    and rtvM: "TE_RuntimeTypeVars (CM_TyEnv M) |\<subseteq>| TE_TypeVars (CM_TyEnv M)"
    using invM unfolding core_module_invariant_def by blast+
  have absM: "TE_AbstractTypes (CM_TyEnv M) = TE_TypeVars (CM_TyEnv M)"
    using scope_M unfolding tyenv_module_scope_def by blast
  have I_nwt: "normalized_module_well_typed I"
    using core_module_well_typed_on_normalized[OF I_norm] I_wt by blast
  have wfI: "tyenv_well_formed (CM_TyEnv I)"
    and scope_I: "tyenv_module_scope (CM_TyEnv I)"
    using I_nwt unfolding normalized_module_well_typed_def by blast+
  have absI: "TE_AbstractTypes (CM_TyEnv I) = TE_TypeVars (CM_TyEnv I)"
    using scope_I unfolding tyenv_module_scope_def by blast
  have rtvI: "TE_RuntimeTypeVars (CM_TyEnv I) |\<subseteq>| TE_TypeVars (CM_TyEnv I)"
    using wfI unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def by blast
  have invI: "core_module_invariant I"
    using core_module_well_typed_invariant[OF I_wt] .
  have subst_eq: "CM_TypeSubst L = ?\<sigma>"
    using link_pair_subst[OF link I_norm idemM] .
  have env_eq: "CM_TyEnv (normalize_module L) = env"
    unfolding env_def
    by (rule module_context_env_link_pair[OF link I_norm idemM scope_I])
  note fL = link_modules_result_fields[OF link]
  have normI: "normalize_module I = I"
    using normalize_module_id_when_empty[OF I_norm] .
  have linkI: "link_modules [I] = Inr I"
    using link_modules_singleton[OF invI] .
  have subI: "set [I] \<subseteq> set [I, M]" by auto
  have ghostOK: "\<forall>x \<in> set [I, M]. module_ghost_subsets_ok x"
    by (simp add: core_module_invariant_ghost_subsets_ok[OF invI]
                  core_module_invariant_ghost_subsets_ok[OF invM])

  \<comment> \<open>The substitution-invariant fields of the state env are the linked env's
      (the state env IS the normalized linked env, and these fields are
      untouched by apply_subst_to_tyenv).\<close>
  have dt_env: "TE_Datatypes env = TE_Datatypes (CM_TyEnv L)"
    unfolding env_eq[symmetric] by simp
  have gd_env: "TE_GhostDatatypes env = TE_GhostDatatypes (CM_TyEnv L)"
    unfolding env_eq[symmetric] by simp
  have gg_env: "TE_GhostGlobals env = TE_GhostGlobals (CM_TyEnv L)"
    unfolding env_eq[symmetric] by simp
  have tv_env: "TE_TypeVars env = TE_TypeVars (CM_TyEnv L)"
    unfolding env_eq[symmetric] by simp
  have rtv_env: "TE_RuntimeTypeVars env = TE_RuntimeTypeVars (CM_TyEnv L)"
    unfolding env_eq[symmetric] by simp
  have abs_env: "TE_AbstractTypes env = TE_AbstractTypes (CM_TyEnv L)"
    unfolding env_eq[symmetric] by simp
  have bt_env: "TE_DataCtorsByType env = TE_DataCtorsByType (CM_TyEnv L)"
    unfolding env_eq[symmetric] by simp

  \<comment> \<open>The linked env's type-variable fields as two-sided unions minus the
      substitution domain.\<close>
  have tvL_eq: "TE_TypeVars (CM_TyEnv L)
                  = (TE_TypeVars (CM_TyEnv I) |\<union>| TE_TypeVars (CM_TyEnv M))
                    |-| fmdom ?\<sigma>"
    by (simp add: fL(6) subst_eq funion_list_def funion_fempty_right)
  have rtvL_eq: "TE_RuntimeTypeVars (CM_TyEnv L)
                  = (TE_RuntimeTypeVars (CM_TyEnv I) |\<union>| TE_RuntimeTypeVars (CM_TyEnv M))
                    |-| fmdom ?\<sigma>"
    by (simp add: fL(7) subst_eq funion_list_def funion_fempty_right)
  have absL_eq: "TE_AbstractTypes (CM_TyEnv L)
                  = (TE_TypeVars (CM_TyEnv I) |\<union>| TE_TypeVars (CM_TyEnv M))
                    |-| fmdom ?\<sigma>"
    by (simp add: fL(8) subst_eq funion_list_def funion_fempty_right absI absM)

  \<comment> \<open>The state env's substituted tables.\<close>
  have gv_env: "TE_GlobalVars env
                  = fmmap (apply_subst ?\<sigma>)
                          (TE_GlobalVars (CM_TyEnv I) ++\<^sub>f TE_GlobalVars (CM_TyEnv M))"
    unfolding env_def module_context_env_def by simp
  have fn_env: "TE_Functions env
                  = fmmap (apply_subst_to_funinfo ?\<sigma>)
                          (TE_Functions (CM_TyEnv I) ++\<^sub>f TE_Functions (CM_TyEnv M))"
    unfolding env_def module_context_env_def by simp
  have dc_env: "TE_DataCtors env
                  = fmmap (apply_subst_to_datactor ?\<sigma>)
                          (TE_DataCtors (CM_TyEnv I) ++\<^sub>f TE_DataCtors (CM_TyEnv M))"
    unfolding env_def module_context_env_def by simp

  \<comment> \<open>Overlaid-family dichotomies: the I side is raw (its substitution is
      empty), the M side is normalize_module M's - i.e. exactly the state
      env's entries on M-declared names.\<close>
  have gv_cases: "\<And>name ty. fmlookup (TE_GlobalVars ?mid) name = Some ty \<Longrightarrow>
                    fmlookup (TE_GlobalVars (CM_TyEnv I)) name = Some ty
                    \<or> fmlookup (TE_GlobalVars ?envB) name = Some ty"
    unfolding link_mid_env_simps normI using fmadd_drop_lookup_Some by fastforce
  have fn_cases: "\<And>name info. fmlookup (TE_Functions ?mid) name = Some info \<Longrightarrow>
                    fmlookup (TE_Functions (CM_TyEnv I)) name = Some info
                    \<or> fmlookup (TE_Functions ?envB) name = Some info"
    unfolding link_mid_env_simps normI using fmadd_drop_lookup_Some by fastforce
  have dc_cases: "\<And>name entry. fmlookup (TE_DataCtors ?mid) name = Some entry \<Longrightarrow>
                    fmlookup (TE_DataCtors (CM_TyEnv I)) name = Some entry
                    \<or> fmlookup (TE_DataCtors ?envB) name = Some entry"
    unfolding link_mid_env_simps normI using fmadd_drop_lookup_Some by fastforce

  \<comment> \<open>M-side entries of the mid env are state-env entries verbatim.\<close>
  have gvB_env: "\<And>name ty. fmlookup (TE_GlobalVars ?envB) name = Some ty \<Longrightarrow>
                   fmlookup (TE_GlobalVars env) name = Some ty"
    unfolding gv_env by (auto simp: fmlookup_dom_iff)
  have fnB_env: "\<And>name info. fmlookup (TE_Functions ?envB) name = Some info \<Longrightarrow>
                   fmlookup (TE_Functions env) name = Some info"
    unfolding fn_env by (auto simp: fmlookup_dom_iff)
  have dcB_env: "\<And>name entry. fmlookup (TE_DataCtors ?envB) name = Some entry \<Longrightarrow>
                   fmlookup (TE_DataCtors env) name = Some entry"
    unfolding dc_env by (auto simp: fmlookup_dom_iff)

  \<comment> \<open>The mid env's global-variable domain is the state env's.\<close>
  have gv_dom: "fmdom (TE_GlobalVars ?mid) = fmdom (TE_GlobalVars env)"
    unfolding link_mid_env_simps normI gv_env
    by (simp add: fmadd_drop_dom)

  \<comment> \<open>Data-constructor correspondence between the mid env and the state env:
      the same keys resolve, with the same datatype name and binder list
      (only the payload differs - raw on the I side of the mid env,
      substituted in the state env). The two tables differ only on I-declared
      constructors, and the link's disjointness pins each key to one side.\<close>
  have dc_disj: "fmdom (TE_DataCtors (CM_TyEnv I))
                   |\<inter>| fmdom (TE_DataCtors (CM_TyEnv M)) = {||}"
    using link_modules_success_facts(1)[OF link]
    unfolding link_fields_disjoint_def
    by (simp add: fmdisjoint_list_Cons fmdisjoint_def)
  have mid_lk: "\<And>c. fmlookup (TE_DataCtors ?mid) c
                  = (if c |\<in>| fmdom (TE_DataCtors (CM_TyEnv I))
                     then fmlookup (TE_DataCtors (CM_TyEnv I)) c
                     else fmlookup (fmmap (apply_subst_to_datactor ?\<sigma>)
                                          (TE_DataCtors (CM_TyEnv M))) c)"
    unfolding link_mid_env_simps normI by fastforce
  have dc_mid_env: "\<And>c dt tvs pl.
        fmlookup (TE_DataCtors ?mid) c = Some (dt, tvs, pl) \<Longrightarrow>
        \<exists>pl'. fmlookup (TE_DataCtors env) c = Some (dt, tvs, pl')"
  proof -
    fix c dt tvs pl
    assume lk: "fmlookup (TE_DataCtors ?mid) c = Some (dt, tvs, pl)"
    show "\<exists>pl'. fmlookup (TE_DataCtors env) c = Some (dt, tvs, pl')"
    proof (cases "c |\<in>| fmdom (TE_DataCtors (CM_TyEnv I))")
      case True
      then have ilk: "fmlookup (TE_DataCtors (CM_TyEnv I)) c = Some (dt, tvs, pl)"
        using lk mid_lk by metis
      have notM: "c |\<notin>| fmdom (TE_DataCtors (CM_TyEnv M))"
        using True dc_disj by (meson disjoint_iff_fnot_equal)
      show ?thesis
        unfolding dc_env using ilk notM by auto
    next
      case False
      then have blk: "fmlookup (fmmap (apply_subst_to_datactor ?\<sigma>)
                                      (TE_DataCtors (CM_TyEnv M))) c
                        = Some (dt, tvs, pl)"
        using lk mid_lk by metis
      then obtain e0 where
          mlk: "fmlookup (TE_DataCtors (CM_TyEnv M)) c = Some e0" and
          e_eq: "(dt, tvs, pl) = apply_subst_to_datactor ?\<sigma> e0"
        by (auto split: option.splits)
      obtain pl0 where e0_shape: "e0 = (dt, tvs, pl0)"
        using e_eq by (cases e0) auto
      show ?thesis
        unfolding dc_env using mlk e0_shape fmdomI[OF mlk] by auto
    qed
  qed
  have dc_env_mid: "\<And>c dt tvs pl.
        fmlookup (TE_DataCtors env) c = Some (dt, tvs, pl) \<Longrightarrow>
        \<exists>pl'. fmlookup (TE_DataCtors ?mid) c = Some (dt, tvs, pl')"
  proof -
    fix c dt tvs pl
    assume lk: "fmlookup (TE_DataCtors env) c = Some (dt, tvs, pl)"
    have mo: "map_option (apply_subst_to_datactor ?\<sigma>)
                (fmlookup (TE_DataCtors (CM_TyEnv I) ++\<^sub>f TE_DataCtors (CM_TyEnv M)) c)
              = Some (dt, tvs, pl)"
      using lk unfolding dc_env by (simp only: fmlookup_map)
    then obtain e0 where
        raw: "fmlookup (TE_DataCtors (CM_TyEnv I) ++\<^sub>f TE_DataCtors (CM_TyEnv M)) c
                = Some e0" and
        e_eq: "(dt, tvs, pl) = apply_subst_to_datactor ?\<sigma> e0"
      by (cases "fmlookup (TE_DataCtors (CM_TyEnv I) ++\<^sub>f TE_DataCtors (CM_TyEnv M)) c") auto
    obtain pl0 where e0_shape: "e0 = (dt, tvs, pl0)"
      using e_eq by (cases e0) auto
    show "\<exists>pl'. fmlookup (TE_DataCtors ?mid) c = Some (dt, tvs, pl')"
    proof (cases "c |\<in>| fmdom (TE_DataCtors (CM_TyEnv M))")
      case True
      then have notI: "c |\<notin>| fmdom (TE_DataCtors (CM_TyEnv I))"
        using dc_disj by (meson disjoint_iff_fnot_equal)
      have mlk: "fmlookup (TE_DataCtors (CM_TyEnv M)) c = Some (dt, tvs, pl0)"
        using raw e0_shape True by simp
      show ?thesis
        using mlk notI mid_lk by auto
    next
      case False
      have ilk: "fmlookup (TE_DataCtors (CM_TyEnv I)) c = Some (dt, tvs, pl0)"
        using raw e0_shape False by simp
      show ?thesis
        using ilk fmdomI[OF ilk] mid_lk by auto
    qed
  qed

  \<comment> \<open>Generic transfer steps into the mid env's scoped envs. From I's own env,
      the sub-link transfer lemmas carry both judgments across (the datatype
      table grows, ghost markers agree on I's datatypes). From the state env,
      plain monotonicity suffices: the mid env has the SAME datatype table and
      ghost markers, and only re-adds the substitution's domain to the
      type-variable fields.\<close>
  have wk_I_to_mid: "\<And>tvs1 tvs2 t.
        is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars := tvs1 \<rparr>) t \<Longrightarrow>
        fset tvs1 \<subseteq> fset tvs2 \<Longrightarrow>
        is_well_kinded (?mid \<lparr> TE_TypeVars := tvs2 \<rparr>) t"
  proof -
    fix tvs1 tvs2 t
    assume wk: "is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars := tvs1 \<rparr>) t"
       and sub: "fset tvs1 \<subseteq> fset tvs2"
    show "is_well_kinded (?mid \<lparr> TE_TypeVars := tvs2 \<rparr>) t"
      by (rule link_side_wk_transfer[OF linkI link subI wk]) (use sub in \<open>auto\<close>)
  qed
  have rt_I_to_mid: "\<And>tvs1 rtvs1 tvs2 rtvs2 t.
        is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars := tvs1,
                                       TE_RuntimeTypeVars := rtvs1 \<rparr>) t \<Longrightarrow>
        is_runtime_type ((CM_TyEnv I) \<lparr> TE_TypeVars := tvs1,
                                        TE_RuntimeTypeVars := rtvs1 \<rparr>) t \<Longrightarrow>
        fset rtvs1 \<subseteq> fset rtvs2 \<Longrightarrow>
        is_runtime_type (?mid \<lparr> TE_TypeVars := tvs2,
                                TE_RuntimeTypeVars := rtvs2 \<rparr>) t"
  proof -
    fix tvs1 rtvs1 tvs2 rtvs2 t
    assume wk: "is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars := tvs1,
                                               TE_RuntimeTypeVars := rtvs1 \<rparr>) t"
       and rt: "is_runtime_type ((CM_TyEnv I) \<lparr> TE_TypeVars := tvs1,
                                                TE_RuntimeTypeVars := rtvs1 \<rparr>) t"
       and sub: "fset rtvs1 \<subseteq> fset rtvs2"
    show "is_runtime_type (?mid \<lparr> TE_TypeVars := tvs2,
                                  TE_RuntimeTypeVars := rtvs2 \<rparr>) t"
      by (rule link_side_rt_transfer[OF linkI link subI ghostOK wk rt])
         (use sub in \<open>auto\<close>)
  qed
  have wk_env_to_mid: "\<And>tvs1 tvs2 t.
        is_well_kinded (env \<lparr> TE_TypeVars := tvs1 \<rparr>) t \<Longrightarrow>
        fset tvs1 \<subseteq> fset tvs2 \<Longrightarrow>
        is_well_kinded (?mid \<lparr> TE_TypeVars := tvs2 \<rparr>) t"
  proof -
    fix tvs1 tvs2 t
    assume wk: "is_well_kinded (env \<lparr> TE_TypeVars := tvs1 \<rparr>) t"
       and sub: "fset tvs1 \<subseteq> fset tvs2"
    have dt: "\<And>n v. fmlookup (TE_Datatypes (env \<lparr> TE_TypeVars := tvs1 \<rparr>)) n = Some v \<Longrightarrow>
                fmlookup (TE_Datatypes (?mid \<lparr> TE_TypeVars := tvs2 \<rparr>)) n = Some v"
      by (simp add: dt_env)
    have tv: "fset (TE_TypeVars (env \<lparr> TE_TypeVars := tvs1 \<rparr>))
                \<subseteq> fset (TE_TypeVars (?mid \<lparr> TE_TypeVars := tvs2 \<rparr>))"
      using sub by simp
    show "is_well_kinded (?mid \<lparr> TE_TypeVars := tvs2 \<rparr>) t"
      using is_well_kinded_mono[OF wk tv dt] .
  qed
  have rt_env_to_mid: "\<And>tvs1 rtvs1 tvs2 rtvs2 t.
        is_runtime_type (env \<lparr> TE_TypeVars := tvs1,
                               TE_RuntimeTypeVars := rtvs1 \<rparr>) t \<Longrightarrow>
        fset rtvs1 \<subseteq> fset rtvs2 \<Longrightarrow>
        is_runtime_type (?mid \<lparr> TE_TypeVars := tvs2,
                                TE_RuntimeTypeVars := rtvs2 \<rparr>) t"
  proof -
    fix tvs1 rtvs1 tvs2 rtvs2 t
    assume rt: "is_runtime_type (env \<lparr> TE_TypeVars := tvs1,
                                       TE_RuntimeTypeVars := rtvs1 \<rparr>) t"
       and sub: "fset rtvs1 \<subseteq> fset rtvs2"
    have rtv: "fset (TE_RuntimeTypeVars (env \<lparr> TE_TypeVars := tvs1,
                                               TE_RuntimeTypeVars := rtvs1 \<rparr>))
                 \<subseteq> fset (TE_RuntimeTypeVars (?mid \<lparr> TE_TypeVars := tvs2,
                                                    TE_RuntimeTypeVars := rtvs2 \<rparr>))"
      using sub by simp
    have gd: "TE_GhostDatatypes (?mid \<lparr> TE_TypeVars := tvs2,
                                        TE_RuntimeTypeVars := rtvs2 \<rparr>)
                = TE_GhostDatatypes (env \<lparr> TE_TypeVars := tvs1,
                                           TE_RuntimeTypeVars := rtvs1 \<rparr>)"
      by (simp add: gd_env)
    show "is_runtime_type (?mid \<lparr> TE_TypeVars := tvs2,
                                  TE_RuntimeTypeVars := rtvs2 \<rparr>) t"
      using is_runtime_type_mono_rtv[OF rt rtv gd] .
  qed

  \<comment> \<open>Per-clause extractions: I's own well-formedness for the raw I-side
      entries, the state env's for the (substituted) M-side entries.\<close>
  have gvwkI: "\<And>name ty. fmlookup (TE_GlobalVars (CM_TyEnv I)) name = Some ty \<Longrightarrow>
                 is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                                   TE_AbstractTypes (CM_TyEnv I) \<rparr>) ty"
    using wfI unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  have gvrtI: "\<And>name ty. fmlookup (TE_GlobalVars (CM_TyEnv I)) name = Some ty \<Longrightarrow>
                 name |\<notin>| TE_GhostGlobals (CM_TyEnv I) \<Longrightarrow>
                 is_runtime_type ((CM_TyEnv I) \<lparr>
                     TE_TypeVars := TE_AbstractTypes (CM_TyEnv I),
                     TE_RuntimeTypeVars :=
                       TE_AbstractTypes (CM_TyEnv I)
                       |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I) \<rparr>) ty"
    using wfI unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
  have ccI: "\<And>ctorName dtName tyVars payload.
               fmlookup (TE_DataCtors (CM_TyEnv I)) ctorName
                 = Some (dtName, tyVars, payload) \<Longrightarrow>
               fmlookup (TE_Datatypes (CM_TyEnv I)) dtName = Some (length tyVars)"
    using wfI unfolding tyenv_well_formed_def tyenv_ctors_consistent_def by blast
  have pwkI: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors (CM_TyEnv I)) ctorName
                  = Some (dtName, tyVars, payload) \<Longrightarrow>
                is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                    TE_AbstractTypes (CM_TyEnv I) |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wfI unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  have ftwkI: "\<And>funName info. fmlookup (TE_Functions (CM_TyEnv I)) funName = Some info \<Longrightarrow>
                 (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                    is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                        TE_AbstractTypes (CM_TyEnv I)
                        |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                 \<and> is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                       TE_AbstractTypes (CM_TyEnv I)
                       |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                  (FI_ReturnType info)"
    using wfI unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fgcI: "\<And>funName info. fmlookup (TE_Functions (CM_TyEnv I)) funName = Some info \<Longrightarrow>
                FI_Ghost info = NotGhost \<Longrightarrow>
                (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                   is_runtime_type
                     ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                             |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes (CM_TyEnv I)
                                 |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                \<and> is_runtime_type
                    ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                            |\<union>| fset_of_list (FI_TyArgs info),
                             TE_RuntimeTypeVars :=
                               (TE_AbstractTypes (CM_TyEnv I)
                                |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                               |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                    (FI_ReturnType info)"
    using wfI
    unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def by blast
  have nprI: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors (CM_TyEnv I)) ctorName
                  = Some (dtName, tyVars, payload) \<Longrightarrow>
                dtName |\<notin>| TE_GhostDatatypes (CM_TyEnv I) \<Longrightarrow>
                is_runtime_type
                  ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                          |\<union>| fset_of_list tyVars,
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes (CM_TyEnv I)
                              |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                             |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wfI
    unfolding tyenv_well_formed_def tyenv_nonghost_payloads_runtime_def by blast
  have gvwkE: "\<And>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<Longrightarrow>
                 is_well_kinded (env \<lparr> TE_TypeVars := TE_AbstractTypes env \<rparr>) ty"
    using wf_env unfolding tyenv_well_formed_def tyenv_vars_well_kinded_def by blast
  have gvrtE: "\<And>name ty. fmlookup (TE_GlobalVars env) name = Some ty \<Longrightarrow>
                 name |\<notin>| TE_GhostGlobals env \<Longrightarrow>
                 is_runtime_type (env \<lparr>
                     TE_TypeVars := TE_AbstractTypes env,
                     TE_RuntimeTypeVars :=
                       TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
    using wf_env unfolding tyenv_well_formed_def tyenv_vars_runtime_def by blast
  have pwkE: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                is_well_kinded (env \<lparr> TE_TypeVars :=
                    TE_AbstractTypes env |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wf_env unfolding tyenv_well_formed_def tyenv_payloads_well_kinded_def by blast
  have btcE: "\<And>dtName ctors ctorName.
                fmlookup (TE_DataCtorsByType env) dtName = Some ctors \<Longrightarrow>
                (ctorName \<in> set ctors)
                  = (\<exists>tyVars payload.
                       fmlookup (TE_DataCtors env) ctorName
                         = Some (dtName, tyVars, payload))"
    using wf_env unfolding tyenv_well_formed_def tyenv_ctors_by_type_consistent_def
    by blast
  have ftwkE: "\<And>funName info. fmlookup (TE_Functions env) funName = Some info \<Longrightarrow>
                 (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                    is_well_kinded (env \<lparr> TE_TypeVars :=
                        TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                 \<and> is_well_kinded (env \<lparr> TE_TypeVars :=
                       TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                                  (FI_ReturnType info)"
    using wf_env unfolding tyenv_well_formed_def tyenv_fun_types_well_kinded_def by blast
  have fgcE: "\<And>funName info. fmlookup (TE_Functions env) funName = Some info \<Longrightarrow>
                FI_Ghost info = NotGhost \<Longrightarrow>
                (\<forall>ty \<in> fst ` set (FI_TmArgs info).
                   is_runtime_type
                     (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                           |\<union>| fset_of_list (FI_TyArgs info),
                            TE_RuntimeTypeVars :=
                              (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
                \<and> is_runtime_type
                    (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                          |\<union>| fset_of_list (FI_TyArgs info),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                    (FI_ReturnType info)"
    using wf_env
    unfolding tyenv_well_formed_def tyenv_fun_ghost_constraint_def Let_def by blast
  have nprE: "\<And>ctorName dtName tyVars payload.
                fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload) \<Longrightarrow>
                dtName |\<notin>| TE_GhostDatatypes env \<Longrightarrow>
                is_runtime_type
                  (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars,
                         TE_RuntimeTypeVars :=
                           (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                           |\<union>| fset_of_list tyVars \<rparr>) payload"
    using wf_env
    unfolding tyenv_well_formed_def tyenv_nonghost_payloads_runtime_def by blast
  have dneE0: "tyenv_datatypes_nonempty env"
    using wf_env unfolding tyenv_well_formed_def by blast

  show ?thesis
    unfolding tyenv_well_formed_def
  proof (intro conjI)
    show "tyenv_vars_well_kinded ?mid"
      unfolding tyenv_vars_well_kinded_def
    proof (intro conjI allI impI)
      fix name ty assume "fmlookup (TE_LocalVars ?mid) name = Some ty"
      then show "is_well_kinded ?mid ty" by (simp add: fL(1))
    next
      fix name ty assume lk: "fmlookup (TE_GlobalVars ?mid) name = Some ty"
      from gv_cases[OF lk]
      show "is_well_kinded (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid \<rparr>) ty"
      proof
        assume lkI: "fmlookup (TE_GlobalVars (CM_TyEnv I)) name = Some ty"
        show ?thesis
          by (rule wk_I_to_mid[OF gvwkI[OF lkI]]) (auto simp: absI)
      next
        assume lkB: "fmlookup (TE_GlobalVars ?envB) name = Some ty"
        show ?thesis
          by (rule wk_env_to_mid[OF gvwkE[OF gvB_env[OF lkB]]])
             (auto simp: abs_env absL_eq)
      qed
    qed
  next
    show "tyenv_vars_runtime ?mid"
      unfolding tyenv_vars_runtime_def
    proof (intro conjI allI impI)
      fix name ty
      assume "fmlookup (TE_LocalVars ?mid) name = Some ty
                \<and> name |\<notin>| TE_GhostLocals ?mid"
      then show "is_runtime_type ?mid ty" by (simp add: fL(1))
    next
      fix name ty
      assume asm: "fmlookup (TE_GlobalVars ?mid) name = Some ty
                     \<and> name |\<notin>| TE_GhostGlobals ?mid"
      then have lk: "fmlookup (TE_GlobalVars ?mid) name = Some ty"
            and ngL: "name |\<notin>| TE_GhostGlobals (CM_TyEnv L)"
        by simp_all
      from gv_cases[OF lk]
      show "is_runtime_type
              (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid,
                      TE_RuntimeTypeVars :=
                        TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid \<rparr>) ty"
      proof
        assume lkI: "fmlookup (TE_GlobalVars (CM_TyEnv I)) name = Some ty"
        have domI: "name |\<in>| fmdom (TE_GlobalVars (CM_TyEnv I))"
          using lkI by (rule fmdomI)
        have ngI: "name |\<notin>| TE_GhostGlobals (CM_TyEnv I)"
          using link_ghost_globals_agree[OF linkI link subI ghostOK domI] ngL by simp
        have rt1: "is_runtime_type ((CM_TyEnv I) \<lparr>
                       TE_TypeVars := TE_AbstractTypes (CM_TyEnv I),
                       TE_RuntimeTypeVars :=
                         TE_AbstractTypes (CM_TyEnv I)
                         |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I) \<rparr>) ty"
          using gvrtI[OF lkI ngI] .
        have "is_well_kinded ((CM_TyEnv I) \<lparr>
                  TE_TypeVars := TE_AbstractTypes (CM_TyEnv I),
                  TE_RuntimeTypeVars :=
                    TE_AbstractTypes (CM_TyEnv I)
                    |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I) \<rparr>) ty
              = is_well_kinded ((CM_TyEnv I) \<lparr>
                    TE_TypeVars := TE_AbstractTypes (CM_TyEnv I) \<rparr>) ty"
          by (intro is_well_kinded_cong_env) simp_all
        then have wk1: "is_well_kinded ((CM_TyEnv I) \<lparr>
                            TE_TypeVars := TE_AbstractTypes (CM_TyEnv I),
                            TE_RuntimeTypeVars :=
                              TE_AbstractTypes (CM_TyEnv I)
                              |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I) \<rparr>) ty"
          using gvwkI[OF lkI] by simp
        show ?thesis
          by (rule rt_I_to_mid[OF wk1 rt1]) (auto simp: absI)
      next
        assume lkB: "fmlookup (TE_GlobalVars ?envB) name = Some ty"
        have ngE: "name |\<notin>| TE_GhostGlobals env"
          using ngL by (simp add: gg_env)
        have rt1: "is_runtime_type (env \<lparr>
                       TE_TypeVars := TE_AbstractTypes env,
                       TE_RuntimeTypeVars :=
                         TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env \<rparr>) ty"
          using gvrtE[OF gvB_env[OF lkB] ngE] .
        show ?thesis
          by (rule rt_env_to_mid[OF rt1])
             (auto simp: abs_env absL_eq rtv_env rtvL_eq)
      qed
    qed
  next
    show "tyenv_ghost_vars_subset ?mid"
      unfolding tyenv_ghost_vars_subset_def
    proof (intro conjI)
      show "TE_GhostLocals ?mid |\<subseteq>| fmdom (TE_LocalVars ?mid)"
        by (simp add: fL(3))
      have "TE_GhostGlobals env |\<subseteq>| fmdom (TE_GlobalVars env)"
        using wf_env unfolding tyenv_well_formed_def tyenv_ghost_vars_subset_def
        by blast
      then show "TE_GhostGlobals ?mid |\<subseteq>| fmdom (TE_GlobalVars ?mid)"
        using gv_dom by (simp add: gg_env)
    qed
  next
    show "tyenv_return_type_well_kinded ?mid"
      unfolding tyenv_return_type_well_kinded_def by (simp add: fL(9))
  next
    show "tyenv_return_type_runtime ?mid"
      unfolding tyenv_return_type_runtime_def by (simp add: fL(9))
  next
    show "tyenv_ctors_consistent ?mid"
      unfolding tyenv_ctors_consistent_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
      obtain pl' where
        "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, pl')"
        using dc_mid_env[OF lk] by blast
      then have "fmlookup (TE_Datatypes env) dtName = Some (length tyVars)"
        using wf_env unfolding tyenv_well_formed_def tyenv_ctors_consistent_def
        by blast
      then show "fmlookup (TE_Datatypes ?mid) dtName = Some (length tyVars)"
        by (simp add: dt_env)
    qed
  next
    show "tyenv_payloads_well_kinded ?mid"
      unfolding tyenv_payloads_well_kinded_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
      from dc_cases[OF lk]
      show "is_well_kinded (?mid \<lparr> TE_TypeVars :=
                TE_AbstractTypes ?mid |\<union>| fset_of_list tyVars \<rparr>) payload"
      proof
        assume lkI: "fmlookup (TE_DataCtors (CM_TyEnv I)) ctorName
                       = Some (dtName, tyVars, payload)"
        show ?thesis
          by (rule wk_I_to_mid[OF pwkI[OF lkI]]) (auto simp: absI)
      next
        assume lkB: "fmlookup (TE_DataCtors ?envB) ctorName
                       = Some (dtName, tyVars, payload)"
        show ?thesis
          by (rule wk_env_to_mid[OF pwkE[OF dcB_env[OF lkB]]])
             (auto simp: abs_env absL_eq)
      qed
    qed
  next
    show "tyenv_ctor_tyvars_distinct ?mid"
      unfolding tyenv_ctor_tyvars_distinct_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
      obtain pl' where
        "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, pl')"
        using dc_mid_env[OF lk] by blast
      then show "distinct tyVars"
        using wf_env unfolding tyenv_well_formed_def tyenv_ctor_tyvars_distinct_def
        by blast
    qed
  next
    show "tyenv_ctors_by_type_consistent ?mid"
      unfolding tyenv_ctors_by_type_consistent_def
    proof (intro allI impI)
      fix dtName ctors ctorName
      assume btlk: "fmlookup (TE_DataCtorsByType ?mid) dtName = Some ctors"
      have btE: "fmlookup (TE_DataCtorsByType env) dtName = Some ctors"
        using btlk by (simp add: bt_env)
      show "(ctorName \<in> set ctors)
              = (\<exists>tyVars payload.
                   fmlookup (TE_DataCtors ?mid) ctorName
                     = Some (dtName, tyVars, payload))"
      proof
        assume "ctorName \<in> set ctors"
        then obtain tyVars payload where
          "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyVars, payload)"
          using btcE[OF btE] by blast
        then show "\<exists>tyVars payload.
                     fmlookup (TE_DataCtors ?mid) ctorName
                       = Some (dtName, tyVars, payload)"
          using dc_env_mid by blast
      next
        assume "\<exists>tyVars payload.
                  fmlookup (TE_DataCtors ?mid) ctorName
                    = Some (dtName, tyVars, payload)"
        then show "ctorName \<in> set ctors"
          using dc_mid_env btcE[OF btE] by blast
      qed
    qed
  next
    show "tyenv_fun_types_well_kinded ?mid"
      unfolding tyenv_fun_types_well_kinded_def
    proof (intro allI impI)
      fix funName info
      assume lk: "fmlookup (TE_Functions ?mid) funName = Some info"
      from fn_cases[OF lk]
      show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
               is_well_kinded (?mid \<lparr> TE_TypeVars :=
                   TE_AbstractTypes ?mid |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
            \<and> is_well_kinded (?mid \<lparr> TE_TypeVars :=
                  TE_AbstractTypes ?mid |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                             (FI_ReturnType info)"
      proof
        assume lkI: "fmlookup (TE_Functions (CM_TyEnv I)) funName = Some info"
        have step: "\<And>ty. is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                             TE_AbstractTypes (CM_TyEnv I)
                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                      \<Longrightarrow> is_well_kinded (?mid \<lparr> TE_TypeVars :=
                              TE_AbstractTypes ?mid
                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        proof -
          fix ty
          assume w: "is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                         TE_AbstractTypes (CM_TyEnv I)
                         |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          show "is_well_kinded (?mid \<lparr> TE_TypeVars :=
                    TE_AbstractTypes ?mid
                    |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (rule wk_I_to_mid[OF w]) (auto simp: absI)
        qed
        show ?thesis using ftwkI[OF lkI] step by blast
      next
        assume lkB: "fmlookup (TE_Functions ?envB) funName = Some info"
        have step: "\<And>ty. is_well_kinded (env \<lparr> TE_TypeVars :=
                             TE_AbstractTypes env
                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                      \<Longrightarrow> is_well_kinded (?mid \<lparr> TE_TypeVars :=
                              TE_AbstractTypes ?mid
                              |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        proof -
          fix ty
          assume w: "is_well_kinded (env \<lparr> TE_TypeVars :=
                         TE_AbstractTypes env
                         |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          show "is_well_kinded (?mid \<lparr> TE_TypeVars :=
                    TE_AbstractTypes ?mid
                    |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (rule wk_env_to_mid[OF w]) (auto simp: abs_env absL_eq)
        qed
        show ?thesis using ftwkE[OF fnB_env[OF lkB]] step by blast
      qed
    qed
  next
    show "tyenv_fun_tyvars_distinct ?mid"
      unfolding tyenv_fun_tyvars_distinct_def
    proof (intro allI impI)
      fix funName info
      assume lk: "fmlookup (TE_Functions ?mid) funName = Some info"
      from fn_cases[OF lk] show "distinct (FI_TyArgs info)"
      proof
        assume "fmlookup (TE_Functions (CM_TyEnv I)) funName = Some info"
        then show ?thesis
          using wfI unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def
          by blast
      next
        assume "fmlookup (TE_Functions ?envB) funName = Some info"
        then have "fmlookup (TE_Functions env) funName = Some info"
          by (rule fnB_env)
        then show ?thesis
          using wf_env unfolding tyenv_well_formed_def tyenv_fun_tyvars_distinct_def
          by blast
      qed
    qed
  next
    show "tyenv_fun_ghost_constraint ?mid"
      unfolding tyenv_fun_ghost_constraint_def Let_def
    proof (intro allI impI)
      fix funName info
      assume asm: "fmlookup (TE_Functions ?mid) funName = Some info
                     \<and> FI_Ghost info = NotGhost"
      then have lk: "fmlookup (TE_Functions ?mid) funName = Some info"
            and ng: "FI_Ghost info = NotGhost"
        by simp_all
      from fn_cases[OF lk]
      show "(\<forall>ty \<in> fst ` set (FI_TmArgs info).
               is_runtime_type
                 (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                        |\<union>| fset_of_list (FI_TyArgs info),
                         TE_RuntimeTypeVars :=
                           (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                           |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty)
            \<and> is_runtime_type
                (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                       |\<union>| fset_of_list (FI_TyArgs info),
                        TE_RuntimeTypeVars :=
                          (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>)
                (FI_ReturnType info)"
      proof
        assume lkI: "fmlookup (TE_Functions (CM_TyEnv I)) funName = Some info"
        have step: "\<And>ty.
                is_runtime_type
                  ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                          |\<union>| fset_of_list (FI_TyArgs info),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes (CM_TyEnv I)
                              |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                \<Longrightarrow> is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                        TE_AbstractTypes (CM_TyEnv I)
                        |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                \<Longrightarrow> is_runtime_type
                      (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                             |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        proof -
          fix ty
          assume r: "is_runtime_type
                       ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                               |\<union>| fset_of_list (FI_TyArgs info),
                                TE_RuntimeTypeVars :=
                                  (TE_AbstractTypes (CM_TyEnv I)
                                   |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                                  |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
             and w0: "is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                          TE_AbstractTypes (CM_TyEnv I)
                          |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          have "is_well_kinded
                  ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                          |\<union>| fset_of_list (FI_TyArgs info),
                           TE_RuntimeTypeVars :=
                             (TE_AbstractTypes (CM_TyEnv I)
                              |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                             |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                = is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                      TE_AbstractTypes (CM_TyEnv I)
                      |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (intro is_well_kinded_cong_env) simp_all
          then have w: "is_well_kinded
                          ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                                  |\<union>| fset_of_list (FI_TyArgs info),
                                   TE_RuntimeTypeVars :=
                                     (TE_AbstractTypes (CM_TyEnv I)
                                      |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                                     |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            using w0 by simp
          show "is_runtime_type
                  (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                         |\<union>| fset_of_list (FI_TyArgs info),
                          TE_RuntimeTypeVars :=
                            (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (rule rt_I_to_mid[OF w r]) (auto simp: absI)
        qed
        show ?thesis using fgcI[OF lkI ng] ftwkI[OF lkI] step by blast
      next
        assume lkB: "fmlookup (TE_Functions ?envB) funName = Some info"
        have step: "\<And>ty.
                is_runtime_type
                  (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                        |\<union>| fset_of_list (FI_TyArgs info),
                         TE_RuntimeTypeVars :=
                           (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                           |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty
                \<Longrightarrow> is_runtime_type
                      (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                             |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
        proof -
          fix ty
          assume r: "is_runtime_type
                       (env \<lparr> TE_TypeVars := TE_AbstractTypes env
                                             |\<union>| fset_of_list (FI_TyArgs info),
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                                |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
          show "is_runtime_type
                  (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid
                                         |\<union>| fset_of_list (FI_TyArgs info),
                          TE_RuntimeTypeVars :=
                            (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                            |\<union>| fset_of_list (FI_TyArgs info) \<rparr>) ty"
            by (rule rt_env_to_mid[OF r])
               (auto simp: abs_env absL_eq rtv_env rtvL_eq)
        qed
        show ?thesis using fgcE[OF fnB_env[OF lkB] ng] step by blast
      qed
    qed
  next
    show "tyenv_nonghost_payloads_runtime ?mid"
      unfolding tyenv_nonghost_payloads_runtime_def
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors ?mid) ctorName = Some (dtName, tyVars, payload)"
         and ng: "dtName |\<notin>| TE_GhostDatatypes ?mid"
      have ngL: "dtName |\<notin>| TE_GhostDatatypes (CM_TyEnv L)" using ng by simp
      from dc_cases[OF lk]
      show "is_runtime_type
              (?mid \<lparr> TE_TypeVars := TE_AbstractTypes ?mid |\<union>| fset_of_list tyVars,
                      TE_RuntimeTypeVars :=
                        (TE_AbstractTypes ?mid |\<inter>| TE_RuntimeTypeVars ?mid)
                        |\<union>| fset_of_list tyVars \<rparr>) payload"
      proof
        assume lkI: "fmlookup (TE_DataCtors (CM_TyEnv I)) ctorName
                       = Some (dtName, tyVars, payload)"
        have dtdomI: "dtName |\<in>| fmdom (TE_Datatypes (CM_TyEnv I))"
          using ccI[OF lkI] by (auto intro: fmdomI)
        have ngI: "dtName |\<notin>| TE_GhostDatatypes (CM_TyEnv I)"
          using link_ghost_datatypes_agree[OF linkI link subI ghostOK dtdomI] ngL
          by simp
        have rt1: "is_runtime_type
                     ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                             |\<union>| fset_of_list tyVars,
                              TE_RuntimeTypeVars :=
                                (TE_AbstractTypes (CM_TyEnv I)
                                 |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                                |\<union>| fset_of_list tyVars \<rparr>) payload"
          using nprI[OF lkI ngI] .
        have "is_well_kinded
                ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                        |\<union>| fset_of_list tyVars,
                         TE_RuntimeTypeVars :=
                           (TE_AbstractTypes (CM_TyEnv I)
                            |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                           |\<union>| fset_of_list tyVars \<rparr>) payload
              = is_well_kinded ((CM_TyEnv I) \<lparr> TE_TypeVars :=
                    TE_AbstractTypes (CM_TyEnv I) |\<union>| fset_of_list tyVars \<rparr>) payload"
          by (intro is_well_kinded_cong_env) simp_all
        then have wk1: "is_well_kinded
                          ((CM_TyEnv I) \<lparr> TE_TypeVars := TE_AbstractTypes (CM_TyEnv I)
                                                  |\<union>| fset_of_list tyVars,
                                   TE_RuntimeTypeVars :=
                                     (TE_AbstractTypes (CM_TyEnv I)
                                      |\<inter>| TE_RuntimeTypeVars (CM_TyEnv I))
                                     |\<union>| fset_of_list tyVars \<rparr>) payload"
          using pwkI[OF lkI] by simp
        show ?thesis
          by (rule rt_I_to_mid[OF wk1 rt1]) (auto simp: absI)
      next
        assume lkB: "fmlookup (TE_DataCtors ?envB) ctorName
                       = Some (dtName, tyVars, payload)"
        have ngE: "dtName |\<notin>| TE_GhostDatatypes env"
          using ngL by (simp add: gd_env)
        have rt1: "is_runtime_type
                     (env \<lparr> TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list tyVars,
                            TE_RuntimeTypeVars :=
                              (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                              |\<union>| fset_of_list tyVars \<rparr>) payload"
          using nprE[OF dcB_env[OF lkB] ngE] .
        show ?thesis
          by (rule rt_env_to_mid[OF rt1])
             (auto simp: abs_env absL_eq rtv_env rtvL_eq)
      qed
    qed
  next
    show "tyenv_ghost_datatypes_subset ?mid"
      unfolding tyenv_ghost_datatypes_subset_def
      using wf_env
      unfolding tyenv_well_formed_def tyenv_ghost_datatypes_subset_def
      by (simp add: gd_env dt_env)
  next
    show "tyenv_runtime_tyvars_subset ?mid"
      unfolding tyenv_runtime_tyvars_subset_def
    proof
      fix n assume "n |\<in>| TE_RuntimeTypeVars ?mid"
      then show "n |\<in>| TE_TypeVars ?mid"
        using rtvI rtvM by (auto dest: fsubsetD)
    qed
  next
    show "tyenv_abstract_types_subset ?mid"
      unfolding tyenv_abstract_types_subset_def by simp
  next
    show "tyenv_datatypes_nonempty ?mid"
      using dneE0 unfolding tyenv_datatypes_nonempty_def
      by (simp add: dt_env bt_env)
  qed
qed

(* The substitution side conditions over the mixed intermediate env: the
   ranges are well-kinded in the target env (the fold invariant's
   typesubst_well_kinded clause, read through the state env equation), the
   unresolved type variables survive into the target env, and the mid env's
   binders avoid the substitution's names (the fold invariant's
   scope_bound_tyvars clause - every mid entry's binders appear verbatim on a
   state env entry). *)
lemma elab_link_mid_env_subst_ok:
  assumes I_wt: "core_module_well_typed I"
      and I_norm: "CM_TypeSubst I = fmempty"
      and inv: "elab_decls_invariant (CM_TyEnv I) ownAbstract env elabEnv M"
      and link: "link_modules [I, M] = Inr L"
  shows "module_env_subst_ok (CM_TypeSubst L) (CM_TyEnv (normalize_module L))
                             (link_mid_env I M L)"
proof -
  have env_def: "env = module_context_env (CM_TyEnv I) M"
    and invM: "core_module_invariant M"
    and wk_env: "typesubst_well_kinded env (CM_TypeSubst M)"
    and cap_env: "subst_names (CM_TypeSubst M) |\<inter>| scope_bound_tyvars env elabEnv = {||}"
    using inv unfolding elab_decls_invariant_def by blast+
  have idemM: "idempotent_subst (CM_TypeSubst M)"
    using invM unfolding core_module_invariant_def by blast
  have I_nwt: "normalized_module_well_typed I"
    using core_module_well_typed_on_normalized[OF I_norm] I_wt by blast
  have scope_I: "tyenv_module_scope (CM_TyEnv I)"
    using I_nwt unfolding normalized_module_well_typed_def by blast
  have invI: "core_module_invariant I"
    using core_module_well_typed_invariant[OF I_wt] .
  have subst_eq: "CM_TypeSubst L = CM_TypeSubst M"
    using link_pair_subst[OF link I_norm idemM] .
  have env_eq: "CM_TyEnv (normalize_module L) = env"
    unfolding env_def
    by (rule module_context_env_link_pair[OF link I_norm idemM scope_I])
  note fL = link_modules_result_fields[OF link]
  have linkI: "link_modules [I] = Inr I"
    using link_modules_singleton[OF invI] .
  have linkM1: "link_modules [M] = Inr M"
    using link_modules_singleton[OF invM] .
  have setMS: "set [I, M] = set [I] \<union> set [M]" by auto

  \<comment> \<open>Intersecting with a subset of a disjoint set.\<close>
  have empty_inter: "\<And>A B C. A |\<inter>| C = {||} \<Longrightarrow> B |\<subseteq>| C \<Longrightarrow> A |\<inter>| B = ({||} :: string fset)"
    by (metis inf_mono le_bot order_refl)

  \<comment> \<open>The state env's tables, as substitution images of the two-sided unions.\<close>
  have fn_env: "TE_Functions env
                  = fmmap (apply_subst_to_funinfo (CM_TypeSubst M))
                          (TE_Functions (CM_TyEnv I) ++\<^sub>f TE_Functions (CM_TyEnv M))"
    unfolding env_def module_context_env_def by simp
  have dc_env: "TE_DataCtors env
                  = fmmap (apply_subst_to_datactor (CM_TypeSubst M))
                          (TE_DataCtors (CM_TyEnv I) ++\<^sub>f TE_DataCtors (CM_TyEnv M))"
    unfolding env_def module_context_env_def by simp
  have fnL: "TE_Functions (CM_TyEnv L)
               = TE_Functions (CM_TyEnv I) ++\<^sub>f TE_Functions (CM_TyEnv M)"
    by (simp add: fL(13) fmlist_union_def)
  have dcL: "TE_DataCtors (CM_TyEnv L)
               = TE_DataCtors (CM_TyEnv I) ++\<^sub>f TE_DataCtors (CM_TyEnv M)"
    by (simp add: fL(15) fmlist_union_def)

  show ?thesis
    unfolding module_env_subst_ok_def
  proof (intro conjI)
    show "TE_Datatypes (CM_TyEnv (normalize_module L)) = TE_Datatypes (link_mid_env I M L)"
      by simp
    show "TE_GhostDatatypes (CM_TyEnv (normalize_module L))
            = TE_GhostDatatypes (link_mid_env I M L)"
      by simp
    show "\<forall>n. n |\<in>| TE_TypeVars (link_mid_env I M L) \<longrightarrow>
            (case fmlookup (CM_TypeSubst L) n of
               Some ty' \<Rightarrow> is_well_kinded (CM_TyEnv (normalize_module L)) ty'
             | None \<Rightarrow> n |\<in>| TE_TypeVars (CM_TyEnv (normalize_module L)))"
    proof (intro allI impI)
      fix n assume n_in: "n |\<in>| TE_TypeVars (link_mid_env I M L)"
      show "case fmlookup (CM_TypeSubst L) n of
              Some ty' \<Rightarrow> is_well_kinded (CM_TyEnv (normalize_module L)) ty'
            | None \<Rightarrow> n |\<in>| TE_TypeVars (CM_TyEnv (normalize_module L))"
      proof (cases "fmlookup (CM_TypeSubst L) n")
        case None
        have n_union: "n |\<in>| TE_TypeVars (CM_TyEnv I) |\<union>| TE_TypeVars (CM_TyEnv M)"
          using n_in by simp
        have n_out: "n |\<notin>| fmdom (CM_TypeSubst L)"
          using fmdom_notI[OF None] .
        have "n |\<in>| TE_TypeVars (CM_TyEnv L)"
          using n_union n_out
          by (simp add: fL(6) funion_list_def funion_fempty_right)
        then show ?thesis using None by simp
      next
        case (Some ty')
        have "fmlookup (CM_TypeSubst M) n = Some ty'"
          using Some subst_eq by simp
        then have wk: "is_well_kinded env ty'"
          using wk_env unfolding typesubst_well_kinded_def by blast
        show ?thesis
          using Some wk unfolding env_eq[symmetric] by simp
      qed
    qed
    show "\<forall>funName info.
            fmlookup (TE_Functions (link_mid_env I M L)) funName = Some info \<longrightarrow>
            subst_names (CM_TypeSubst L) |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
    proof (intro allI impI)
      fix funName info
      assume lk: "fmlookup (TE_Functions (link_mid_env I M L)) funName = Some info"
      obtain info0 where
        raw: "fmlookup (TE_Functions (CM_TyEnv L)) funName = Some info0" and
        "info = apply_subst_to_funinfo (CM_TypeSubst I) info0
           \<or> info = apply_subst_to_funinfo (CM_TypeSubst M) info0" and
        tyargs: "FI_TyArgs info = FI_TyArgs info0" and
        "FI_Ghost info = FI_Ghost info0" and
        "apply_subst_to_funinfo (CM_TypeSubst L) info
           = apply_subst_to_funinfo (CM_TypeSubst L) info0"
        by (rule link_mid_env_functions_lookup[OF linkI linkM1 link setMS lk])
      have env_lk: "fmlookup (TE_Functions env) funName
                      = Some (apply_subst_to_funinfo (CM_TypeSubst M) info0)"
        unfolding fn_env using raw[unfolded fnL] by auto
      have ran: "apply_subst_to_funinfo (CM_TypeSubst M) info0 |\<in>| fmran (TE_Functions env)"
        using fmranI[OF env_lk] .
      have img: "fset_of_list (FI_TyArgs info0)
                   |\<in>| (\<lambda>info. fset_of_list (FI_TyArgs info)) |`| fmran (TE_Functions env)"
        using fimageI[OF ran, of "\<lambda>info. fset_of_list (FI_TyArgs info)"] by simp
      have "fset_of_list (FI_TyArgs info0)
              |\<subseteq>| ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info))
                            |`| fmran (TE_Functions env))"
        by (metis fequalityE ffUnion_fsubset_iff img)
      then have sub: "fset_of_list (FI_TyArgs info0) |\<subseteq>| scope_bound_tyvars env elabEnv"
        unfolding scope_bound_tyvars_def by auto
      show "subst_names (CM_TypeSubst L) |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
        unfolding subst_eq tyargs
        by (rule empty_inter[OF cap_env sub])
    qed
    show "\<forall>ctorName dtName tyVars payload.
            fmlookup (TE_DataCtors (link_mid_env I M L)) ctorName
              = Some (dtName, tyVars, payload) \<longrightarrow>
            subst_names (CM_TypeSubst L) |\<inter>| fset_of_list tyVars = {||}"
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors (link_mid_env I M L)) ctorName
                    = Some (dtName, tyVars, payload)"
      obtain payload0 where
        raw: "fmlookup (TE_DataCtors (CM_TyEnv L)) ctorName = Some (dtName, tyVars, payload0)"
        by (rule link_mid_env_ctors_lookup[OF linkI linkM1 link setMS lk])
      have env_lk: "fmlookup (TE_DataCtors env) ctorName
                      = Some (dtName, tyVars, apply_subst (CM_TypeSubst M) payload0)"
        unfolding dc_env using raw[unfolded dcL] by auto
      have ran: "(dtName, tyVars, apply_subst (CM_TypeSubst M) payload0)
                   |\<in>| fmran (TE_DataCtors env)"
        using fmranI[OF env_lk] .
      have img: "fset_of_list tyVars
                   |\<in>| (\<lambda>(_, tyVars, _). fset_of_list tyVars) |`| fmran (TE_DataCtors env)"
        using fimageI[OF ran, of "\<lambda>(_, tyVars, _). fset_of_list tyVars"] by simp
      have "fset_of_list tyVars
              |\<subseteq>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars)
                            |`| fmran (TE_DataCtors env))"
        by (metis ffUnion_fsubset_iff img verit_comp_simplify1(2))
      then have sub: "fset_of_list tyVars |\<subseteq>| scope_bound_tyvars env elabEnv"
        unfolding scope_bound_tyvars_def by auto
      show "subst_names (CM_TypeSubst L) |\<inter>| fset_of_list tyVars = {||}"
        unfolding subst_eq
        by (rule empty_inter[OF cap_env sub])
    qed
  qed
qed

lemma elab_link_term_transfer:
  assumes I_wt: "core_module_well_typed I"
      and I_norm: "CM_TypeSubst I = fmempty"
      and inv: "elab_decls_invariant (CM_TyEnv I) ownAbstract env elabEnv M"
      and link: "link_modules [I, M] = Inr L"
      and t0: "core_term_type (CM_TyEnv I) ghost tm = Some ty"
  shows "core_term_type (CM_TyEnv (normalize_module L)) ghost
                        (apply_subst_to_term (CM_TypeSubst M) tm)
           = Some (apply_subst (CM_TypeSubst M) ty)"
proof -
  have invM: "core_module_invariant M"
    using inv unfolding elab_decls_invariant_def by blast
  have idemM: "idempotent_subst (CM_TypeSubst M)"
    using invM unfolding core_module_invariant_def by blast
  have I_nwt: "normalized_module_well_typed I"
    using core_module_well_typed_on_normalized[OF I_norm] I_wt by blast
  have wfI: "tyenv_well_formed (CM_TyEnv I)"
    using I_nwt unfolding normalized_module_well_typed_def by blast
  have invI: "core_module_invariant I"
    using core_module_well_typed_invariant[OF I_wt] .
  have subst_eq: "CM_TypeSubst L = CM_TypeSubst M"
    using link_pair_subst[OF link I_norm idemM] .
  have normI: "normalize_module I = I"
    using normalize_module_id_when_empty[OF I_norm] .
  have linkI: "link_modules [I] = Inr I"
    using link_modules_singleton[OF invI] .
  have linkM1: "link_modules [M] = Inr M"
    using link_modules_singleton[OF invM] .
  have setMS: "set [I, M] = set [I] \<union> set [M]" by auto
  have ghostOK: "\<forall>x \<in> set [I, M]. module_ghost_subsets_ok x"
    by (simp add: core_module_invariant_ghost_subsets_ok[OF invI]
                  core_module_invariant_ghost_subsets_ok[OF invM])

  let ?e1 = "(CM_TyEnv I)
               \<lparr> TE_TypeVars := TE_TypeVars (CM_TyEnv I) |\<union>| TE_TypeVars (CM_TyEnv M),
                 TE_RuntimeTypeVars :=
                   TE_RuntimeTypeVars (CM_TyEnv I)
                   |\<union>| TE_RuntimeTypeVars (CM_TyEnv M) \<rparr>"
  \<comment> \<open>Widen the tyvar fields by the M side's.\<close>
  have t1: "core_term_type ?e1 ghost tm = Some ty"
    using core_term_type_irrelevant_tyvar[OF t0,
            where extraTV = "TE_TypeVars (CM_TyEnv M)"
              and extraRT = "TE_RuntimeTypeVars (CM_TyEnv M)"]
    by simp
  \<comment> \<open>Extend along the declaration axis into the mid env.\<close>
  have ext: "tyenv_extends ?e1 (link_mid_env I M L)"
    using link_mid_env_extends[OF linkI linkM1 link setMS ghostOK]
    unfolding normI .
  have cons1: "tyenv_ctors_consistent ?e1"
    using wfI unfolding tyenv_well_formed_def tyenv_ctors_consistent_def by simp
  have t2: "core_term_type (link_mid_env I M L) ghost tm = Some ty"
    using core_term_type_tyenv_extends[OF ext cons1 t1] .
  \<comment> \<open>Substitute with the link's substitution, then collapse the env.\<close>
  have t3: "core_term_type
              (apply_subst_to_module_env (CM_TypeSubst L)
                 (CM_TyEnv (normalize_module L)) (link_mid_env I M L))
              ghost (apply_subst_to_term (CM_TypeSubst L) tm)
              = Some (apply_subst (CM_TypeSubst L) ty)"
    using core_term_type_subst_module_env[OF t2
            elab_link_mid_env_well_formed[OF I_wt I_norm inv link]
            elab_link_mid_env_subst_ok[OF I_wt I_norm inv link]]
          link_mid_env_runtime_ok[OF linkI linkM1 link setMS]
    by blast
  show ?thesis
    using t3
    unfolding link_mid_env_collapse[OF linkI linkM1 link setMS] subst_eq
    using
      \<open>apply_subst_to_module_env (CM_TypeSubst L) (CM_TyEnv (normalize_module L)) (link_mid_env I M L) = CM_TyEnv (normalize_module L)\<close>
      subst_eq by auto
qed

lemma elab_link_globals:
  assumes I_wt: "core_module_well_typed I"
      and I_norm: "CM_TypeSubst I = fmempty"
      and inv: "elab_decls_invariant (CM_TyEnv I) ownAbstract env elabEnv M"
      and link: "link_modules [I, M] = Inr L"
  shows "module_globals_well_typed (CM_TyEnv (normalize_module L))
                                   (CM_GlobalVars (normalize_module L))"
proof -
  let ?\<sigma> = "CM_TypeSubst M"
  \<comment> \<open>Shared setup.\<close>
  have env_def: "env = module_context_env (CM_TyEnv I) M"
    and invM: "core_module_invariant M"
    and gwtM: "module_globals_well_typed env (CM_GlobalVars (normalize_module M))"
    using inv unfolding elab_decls_invariant_def by blast+
  have idemM: "idempotent_subst ?\<sigma>"
    using invM unfolding core_module_invariant_def by blast
  have I_nwt: "normalized_module_well_typed I"
    using core_module_well_typed_on_normalized[OF I_norm] I_wt by blast
  have scope_I: "tyenv_module_scope (CM_TyEnv I)"
    and gwtI: "module_globals_well_typed (CM_TyEnv I) (CM_GlobalVars I)"
    using I_nwt unfolding normalized_module_well_typed_def by blast+
  have invI: "core_module_invariant I"
    using core_module_well_typed_invariant[OF I_wt] .
  have subst_eq: "CM_TypeSubst L = ?\<sigma>"
    using link_pair_subst[OF link I_norm idemM] .
  have env_eq: "CM_TyEnv (normalize_module L) = env"
    unfolding env_def
    by (rule module_context_env_link_pair[OF link I_norm idemM scope_I])
  note fL = link_modules_result_fields[OF link]

  \<comment> \<open>Domain disjointness of the two operands' global tables.\<close>
  have disj: "link_fields_disjoint [I, M]"
    using link_modules_success_facts(1)[OF link] .
  have gv_decl_disj: "fmdom (TE_GlobalVars (CM_TyEnv I))
                        |\<inter>| fmdom (TE_GlobalVars (CM_TyEnv M)) = {||}"
    using disj unfolding link_fields_disjoint_def
    by (simp add: fmdisjoint_list_Cons fmdisjoint_def)

  \<comment> \<open>Ghost-marker agreement for I-declared names.\<close>
  have linkI: "link_modules [I] = Inr I"
    using link_modules_singleton[OF invI] .
  have ghostOK: "\<forall>x \<in> set [I, M]. module_ghost_subsets_ok x"
    by (simp add: core_module_invariant_ghost_subsets_ok[OF invI]
                  core_module_invariant_ghost_subsets_ok[OF invM])
  have gg_env: "TE_GhostGlobals env = TE_GhostGlobals (CM_TyEnv L)"
    unfolding env_eq[symmetric] by simp

  show ?thesis
    unfolding module_globals_well_typed_def
  proof (intro allI impI)
    fix name tm'
    assume look': "fmlookup (CM_GlobalVars (normalize_module L)) name = Some tm'"
    have gvL: "CM_GlobalVars L = CM_GlobalVars I ++\<^sub>f CM_GlobalVars M"
      by (simp add: fL(18) fmlist_union_def)
    from look' obtain tm where
      raw: "fmlookup (CM_GlobalVars L) name = Some tm" and
      tm'_eq: "tm' = apply_subst_to_term ?\<sigma> tm"
      by (auto simp: subst_eq)
    show "\<exists>declTy.
            fmlookup (TE_GlobalVars (CM_TyEnv (normalize_module L))) name = Some declTy \<and>
            (if name |\<in>| TE_GhostGlobals (CM_TyEnv (normalize_module L))
             then core_term_type (CM_TyEnv (normalize_module L)) Ghost tm' = Some declTy
             else is_constant_term tm' \<and>
                  core_term_type (CM_TyEnv (normalize_module L)) NotGhost tm' = Some declTy)"
    proof (cases "fmlookup (CM_GlobalVars M) name")
      case (Some tmM)
      \<comment> \<open>M-side entry: the fold invariant's typechecking clause is already a
          statement about the normalized linked env.\<close>
      have inM: "name |\<in>| fmdom (CM_GlobalVars M)"
        using Some by (auto simp: fmlookup_dom_iff)
      have tm_eq: "tm = tmM"
        using raw Some inM unfolding gvL by simp
      have "fmlookup (CM_GlobalVars (normalize_module M)) name
              = Some (apply_subst_to_term ?\<sigma> tm)"
        using Some tm_eq by simp
      then obtain declTy where
        declM: "fmlookup (TE_GlobalVars env) name = Some declTy" and
        typingM: "if name |\<in>| TE_GhostGlobals env
                  then core_term_type env Ghost (apply_subst_to_term ?\<sigma> tm) = Some declTy
                  else is_constant_term (apply_subst_to_term ?\<sigma> tm) \<and>
                       core_term_type env NotGhost (apply_subst_to_term ?\<sigma> tm) = Some declTy"
        using gwtM unfolding module_globals_well_typed_def by blast
      show ?thesis
        using declM typingM unfolding env_eq tm'_eq by blast
    next
      case None
      \<comment> \<open>I-side entry: transfer I's own typing across the substitution and the
          env extension.\<close>
      have inI: "fmlookup (CM_GlobalVars I) name = Some tm"
        using raw None unfolding gvL by (auto simp: fmlookup_dom_iff split: if_splits)
      obtain declTy0 where
        declI: "fmlookup (TE_GlobalVars (CM_TyEnv I)) name = Some declTy0" and
        typingI: "if name |\<in>| TE_GhostGlobals (CM_TyEnv I)
                  then core_term_type (CM_TyEnv I) Ghost tm = Some declTy0
                  else is_constant_term tm \<and>
                       core_term_type (CM_TyEnv I) NotGhost tm = Some declTy0"
        using gwtI inI unfolding module_globals_well_typed_def by blast
      \<comment> \<open>The declared type in the state env, via the I side of the union.\<close>
      have notinM: "name |\<notin>| fmdom (TE_GlobalVars (CM_TyEnv M))"
        using gv_decl_disj declI by (meson disjoint_iff_fnot_equal fmdomI)
      have declEnv: "fmlookup (TE_GlobalVars env) name = Some (apply_subst ?\<sigma> declTy0)"
        unfolding env_def module_context_env_def
        using declI notinM by simp
      \<comment> \<open>The ghost marker for an I-declared name is I's own.\<close>
      have agree: "name |\<in>| TE_GhostGlobals (CM_TyEnv L)
                     \<longleftrightarrow> name |\<in>| TE_GhostGlobals (CM_TyEnv I)"
        by (rule link_ghost_globals_agree[OF linkI link _ ghostOK])
           (use declI in \<open>auto simp: fmlookup_dom_iff\<close>)
      have agree_env: "name |\<in>| TE_GhostGlobals env
                         \<longleftrightarrow> name |\<in>| TE_GhostGlobals (CM_TyEnv I)"
        using agree gg_env by simp
      show ?thesis
      proof (cases "name |\<in>| TE_GhostGlobals (CM_TyEnv I)")
        case True
        have "core_term_type (CM_TyEnv I) Ghost tm = Some declTy0"
          using typingI True by simp
        then have "core_term_type (CM_TyEnv (normalize_module L)) Ghost
                     (apply_subst_to_term ?\<sigma> tm) = Some (apply_subst ?\<sigma> declTy0)"
          using elab_link_term_transfer[OF I_wt I_norm inv link] by blast
        then show ?thesis
          using declEnv True agree_env unfolding env_eq tm'_eq by auto
      next
        case False
        have const: "is_constant_term tm" and
             "core_term_type (CM_TyEnv I) NotGhost tm = Some declTy0"
          using typingI False by simp_all
        then have "core_term_type (CM_TyEnv (normalize_module L)) NotGhost
                     (apply_subst_to_term ?\<sigma> tm) = Some (apply_subst ?\<sigma> declTy0)"
          using elab_link_term_transfer[OF I_wt I_norm inv link] by blast
        then show ?thesis
          using declEnv const False agree_env unfolding env_eq tm'_eq by auto
      qed
    qed
  qed
qed

(* Functions analogue of elab_link_globals. The M-side entries are covered by
   the fold invariant's own functions clause (already phrased over the
   normalized linked env). An I-side definition is transferred through the
   body-level chain of the whole-program proof - widen the body env's tyvar
   fields by M's, extend along the declaration axis into the mid env's body
   env, substitute, collapse - where the body-level transfer lemmas take the
   needed side conventions (Abs = TV, RTV |<=| TV) from the structural module
   invariants rather than from M's (unavailable) well-typedness. *)
lemma elab_link_functions:
  assumes I_wt: "core_module_well_typed I"
      and I_norm: "CM_TypeSubst I = fmempty"
      and inv: "elab_decls_invariant (CM_TyEnv I) ownAbstract env elabEnv M"
      and link: "link_modules [I, M] = Inr L"
  shows "module_functions_well_typed (CM_TyEnv (normalize_module L))
                                     (CM_Functions (normalize_module L))"
proof -
  let ?\<sigma> = "CM_TypeSubst M"
  let ?mid = "link_mid_env I M L"
  \<comment> \<open>Shared setup.\<close>
  have env_def: "env = module_context_env (CM_TyEnv I) M"
    and invM: "core_module_invariant M"
    and fwtM: "module_functions_well_typed env (CM_Functions (normalize_module M))"
    using inv unfolding elab_decls_invariant_def by blast+
  have idemM: "idempotent_subst ?\<sigma>"
    using invM unfolding core_module_invariant_def by blast
  have I_nwt: "normalized_module_well_typed I"
    using core_module_well_typed_on_normalized[OF I_norm] I_wt by blast
  have wfI: "tyenv_well_formed (CM_TyEnv I)"
    and scope_I: "tyenv_module_scope (CM_TyEnv I)"
    and fwtI: "module_functions_well_typed (CM_TyEnv I) (CM_Functions I)"
    using I_nwt unfolding normalized_module_well_typed_def by blast+
  have invI: "core_module_invariant I"
    using core_module_well_typed_invariant[OF I_wt] .
  have subst_eq: "CM_TypeSubst L = ?\<sigma>"
    using link_pair_subst[OF link I_norm idemM] .
  have env_eq: "CM_TyEnv (normalize_module L) = env"
    unfolding env_def
    by (rule module_context_env_link_pair[OF link I_norm idemM scope_I])
  note fL = link_modules_result_fields[OF link]
  have normI: "normalize_module I = I"
    using normalize_module_id_when_empty[OF I_norm] .
  have linkI: "link_modules [I] = Inr I"
    using link_modules_singleton[OF invI] .
  have linkM1: "link_modules [M] = Inr M"
    using link_modules_singleton[OF invM] .
  have setMS: "set [I, M] = set [I] \<union> set [M]" by auto
  have subI: "set [I] \<subseteq> set [I, M]" by auto
  have ghostOK: "\<forall>x \<in> set [I, M]. module_ghost_subsets_ok x"
    by (simp add: core_module_invariant_ghost_subsets_ok[OF invI]
                  core_module_invariant_ghost_subsets_ok[OF invM])

  \<comment> \<open>Side and whole-link tyvar conventions, from the structural invariants.\<close>
  have absI: "TE_AbstractTypes (CM_TyEnv I) = TE_TypeVars (CM_TyEnv I)"
    using scope_I unfolding tyenv_module_scope_def by blast
  have rtvI: "TE_RuntimeTypeVars (CM_TyEnv I) |\<subseteq>| TE_TypeVars (CM_TyEnv I)"
    using invI unfolding core_module_invariant_def by blast
  have absM: "TE_AbstractTypes (CM_TyEnv M) = TE_TypeVars (CM_TyEnv M)"
    using invM unfolding core_module_invariant_def tyenv_module_scope_def by blast
  have rtvM: "TE_RuntimeTypeVars (CM_TyEnv M) |\<subseteq>| TE_TypeVars (CM_TyEnv M)"
    using invM unfolding core_module_invariant_def by blast
  have invL: "core_module_invariant L"
    by (rule link_modules_invariant[OF link]) (simp add: invI invM)
  have absL: "TE_AbstractTypes (CM_TyEnv L) = TE_TypeVars (CM_TyEnv L)"
    using invL unfolding core_module_invariant_def tyenv_module_scope_def by blast
  have rtvL: "TE_RuntimeTypeVars (CM_TyEnv L) |\<subseteq>| TE_TypeVars (CM_TyEnv L)"
    using invL unfolding core_module_invariant_def by blast

  \<comment> \<open>Domain disjointness of the two operands' function tables.\<close>
  have disj: "link_fields_disjoint [I, M]"
    using link_modules_success_facts(1)[OF link] .
  have fn_decl_disj: "fmdom (TE_Functions (CM_TyEnv I))
                        |\<inter>| fmdom (TE_Functions (CM_TyEnv M)) = {||}"
    using disj unfolding link_fields_disjoint_def
    by (simp add: fmdisjoint_list_Cons fmdisjoint_def)

  show ?thesis
    unfolding module_functions_well_typed_def
  proof (intro allI impI)
    fix name f'
    assume look': "fmlookup (CM_Functions (normalize_module L)) name = Some f'"
    have fnL: "CM_Functions L = CM_Functions I ++\<^sub>f CM_Functions M"
      by (simp add: fL(19) fmlist_union_def)
    from look' obtain f where
      raw: "fmlookup (CM_Functions L) name = Some f" and
      f'_eq: "f' = f \<lparr> CF_Body := map_option (apply_subst_to_statement_list ?\<sigma>)
                                              (CF_Body f) \<rparr>"
      by (auto simp: subst_eq)
    show "\<exists>info.
            fmlookup (TE_Functions (CM_TyEnv (normalize_module L))) name = Some info \<and>
            length (CF_Args f') = length (FI_TmArgs info) \<and>
            distinct (CF_Args f') \<and>
            (case CF_Body f' of
               None \<Rightarrow> True
             | Some body \<Rightarrow>
                 core_statement_list_type
                   (module_body_env_for (CM_TyEnv (normalize_module L))
                                        (CF_Args f') info)
                   (FI_Ghost info) body \<noteq> None)"
    proof (cases "fmlookup (CM_Functions M) name")
      case (Some fM)
      \<comment> \<open>M-side entry: the fold invariant's typechecking clause is already a
          statement about the normalized linked env.\<close>
      have inM: "name |\<in>| fmdom (CM_Functions M)"
        using Some by (auto simp: fmlookup_dom_iff)
      have f_eq: "f = fM"
        using raw Some inM unfolding fnL by simp
      have f'_isM: "fmlookup (CM_Functions (normalize_module M)) name = Some f'"
        using Some by (simp add: f'_eq f_eq)
      obtain info where
        declM: "fmlookup (TE_Functions env) name = Some info" and
        lenM: "length (CF_Args f') = length (FI_TmArgs info)" and
        distM: "distinct (CF_Args f')" and
        bodyM: "case CF_Body f' of
                  None \<Rightarrow> True
                | Some body \<Rightarrow>
                    core_statement_list_type
                      (module_body_env_for env (CF_Args f') info)
                      (FI_Ghost info) body \<noteq> None"
        using fwtM f'_isM unfolding module_functions_well_typed_def by blast
      show ?thesis
        unfolding env_eq using declM lenM distM bodyM by blast
    next
      case None
      \<comment> \<open>I-side entry: transfer I's own body typing across the substitution
          and the env extension, at the body-env level.\<close>
      have inI: "fmlookup (CM_Functions I) name = Some f"
        using raw None unfolding fnL by (auto simp: fmlookup_dom_iff split: if_splits)
      obtain info0 where
        a_decl: "fmlookup (TE_Functions (CM_TyEnv I)) name = Some info0" and
        len0: "length (CF_Args f) = length (FI_TmArgs info0)" and
        dist0: "distinct (CF_Args f)" and
        body0_ok: "case CF_Body f of
                     None \<Rightarrow> True
                   | Some body \<Rightarrow>
                       core_statement_list_type
                         (module_body_env_for (CM_TyEnv I) (CF_Args f) info0)
                         (FI_Ghost info0) body \<noteq> None"
        using fwtI inI unfolding module_functions_well_typed_def by blast
      have m_raw: "fmlookup (TE_Functions (CM_TyEnv L)) name = Some info0"
        using link_modules_decl_submaps(2)[OF linkI link subI a_decl] .
      let ?infoM = "apply_subst_to_funinfo ?\<sigma> info0"
      \<comment> \<open>The declared FunInfo in the state env, via the I side of the union.\<close>
      have notinM: "name |\<notin>| fmdom (TE_Functions (CM_TyEnv M))"
        using fn_decl_disj a_decl by (meson disjoint_iff_fnot_equal fmdomI)
      have m_decl: "fmlookup (TE_Functions env) name = Some ?infoM"
        unfolding env_def module_context_env_def
        using a_decl notinM by simp
      have lenM: "length (CF_Args f) = length (FI_TmArgs ?infoM)"
        using len0 by (simp add: apply_subst_to_funinfo_def)
      have ghost_pres: "FI_Ghost ?infoM = FI_Ghost info0"
        by (simp add: apply_subst_to_funinfo_def)
      \<comment> \<open>The body chain (if there is a body).\<close>
      have body_case: "case CF_Body f' of
                         None \<Rightarrow> True
                       | Some body' \<Rightarrow>
                           core_statement_list_type
                             (module_body_env_for env (CF_Args f) ?infoM)
                             (FI_Ghost ?infoM) body' \<noteq> None"
      proof (cases "CF_Body f")
        case None
        then have "CF_Body f' = None" by (simp add: f'_eq)
        then show ?thesis by simp
      next
        case (Some body0)
        let ?beI = "module_body_env_for (CM_TyEnv I) (CF_Args f) info0"
        let ?e1 = "?beI \<lparr> TE_TypeVars := TE_TypeVars ?beI |\<union>| TE_TypeVars (CM_TyEnv M),
                          TE_RuntimeTypeVars :=
                            TE_RuntimeTypeVars ?beI
                            |\<union>| TE_RuntimeTypeVars (CM_TyEnv M) \<rparr>"
        let ?sb = "module_body_env_for ?mid (CF_Args f) info0"
        let ?tb = "module_body_env_for (CM_TyEnv (normalize_module L))
                                       (CF_Args f) ?infoM"
        have "core_statement_list_type ?beI (FI_Ghost info0) body0 \<noteq> None"
          using body0_ok Some by simp
        then obtain envOut where
            t0: "core_statement_list_type ?beI (FI_Ghost info0) body0 = Some envOut"
          by blast
        \<comment> \<open>Widen the tyvar fields by the M side's.\<close>
        have t1: "core_statement_list_type ?e1 (FI_Ghost info0) body0
                    = Some (envOut
                        \<lparr> TE_TypeVars := TE_TypeVars envOut |\<union>| TE_TypeVars (CM_TyEnv M),
                          TE_RuntimeTypeVars :=
                            TE_RuntimeTypeVars envOut
                            |\<union>| TE_RuntimeTypeVars (CM_TyEnv M) \<rparr>)"
          using core_statement_list_type_irrelevant_tyvar[OF t0,
                  where extraTV = "TE_TypeVars (CM_TyEnv M)"
                    and extraRT = "TE_RuntimeTypeVars (CM_TyEnv M)"] .
        \<comment> \<open>Extend along the declaration axis into the mid env's body env.\<close>
        have body_ext: "tyenv_extends ?e1 ?sb"
          using link_mid_body_env_extends[OF linkI linkM1 link setMS ghostOK
                                             absI rtvI absM rtvM,
                                           where names = "CF_Args f" and info = info0]
          unfolding normI .
        have cons1: "tyenv_ctors_consistent ?e1"
          using wfI unfolding tyenv_well_formed_def tyenv_ctors_consistent_def
          by (simp add: module_body_env_for_def)
        obtain envOut2 where
            t2: "core_statement_list_type ?sb (FI_Ghost info0) body0 = Some envOut2"
          using core_statement_list_type_tyenv_extends[OF t1 body_ext cons1] by blast
        \<comment> \<open>Substitute with the link's substitution, then collapse the env.\<close>
        have mid_lk: "fmlookup (TE_Functions ?mid) name = Some info0"
          unfolding link_mid_env_simps normI
          using a_decl fmdomI[OF a_decl] by (simp add: fmadd_drop_lookup)
        have wf_sb: "tyenv_well_formed ?sb"
          using module_body_env_for_well_formed[OF
                  elab_link_mid_env_well_formed[OF I_wt I_norm inv link]
                  mid_lk len0] .
        have ok_sb: "module_env_subst_ok ?\<sigma> ?tb ?sb"
          using link_mid_body_env_subst_ok[OF link m_raw refl
                  elab_link_mid_env_subst_ok[OF I_wt I_norm inv link] absL,
                  where names = "CF_Args f"]
          by (simp add: subst_eq)
        have rt_sb: "module_env_subst_runtime_ok ?\<sigma> ?tb ?sb"
          using link_mid_body_env_runtime_ok[OF linkI linkM1 link setMS m_raw
                                                refl refl absL rtvL,
                                             where names = "CF_Args f"]
          by (simp add: subst_eq)
        have t3: "core_statement_list_type (apply_subst_to_module_env ?\<sigma> ?tb ?sb)
                    (FI_Ghost info0)
                    (apply_subst_to_statement_list ?\<sigma> body0)
                    = Some (apply_subst_to_module_env ?\<sigma> ?tb envOut2)"
          using core_statement_list_type_subst_module_env[OF t2 wf_sb ok_sb] rt_sb
          by blast
        have info_rel: "info0 = apply_subst_to_funinfo (CM_TypeSubst I) info0"
          by (simp add: I_norm)
        have collapse: "apply_subst_to_module_env ?\<sigma> ?tb ?sb = ?tb"
          using link_mid_body_env_collapse[OF linkI linkM1 link setMS info_rel,
                                           where names = "CF_Args f"]
          by (simp add: subst_eq)
        have t4: "core_statement_list_type ?tb (FI_Ghost info0)
                    (apply_subst_to_statement_list ?\<sigma> body0)
                    = Some (apply_subst_to_module_env ?\<sigma> ?tb envOut2)"
          using t3 unfolding collapse .
        have cf': "CF_Body f' = Some (apply_subst_to_statement_list ?\<sigma> body0)"
          by (simp add: f'_eq Some)
        show ?thesis
          unfolding cf' using t4 env_eq by auto
      qed
      have args_eq: "CF_Args f' = CF_Args f"
        by (simp add: f'_eq)
      show ?thesis
        unfolding env_eq args_eq
        using m_decl lenM dist0 body_case by blast
    qed
  qed
qed

(* From the final invariant instance, a successful link of I and M is
   well-typed: the structural invariant comes from link_modules_invariant,
   the substitution well-kindedness and env well-formedness transfer through
   the state env equation, and the two definition-typechecking clauses are the
   transfer lemmas above. *)
lemma elab_decls_invariant_link:
  assumes I_wt: "core_module_well_typed I"
      and I_norm: "CM_TypeSubst I = fmempty"
      and inv: "elab_decls_invariant (CM_TyEnv I) ownAbstract env elabEnv M"
      and link: "link_modules [I, M] = Inr L"
  shows "core_module_well_typed L"
proof -
  \<comment> \<open>Unpack the conjuncts used here.\<close>
  have env_def: "env = module_context_env (CM_TyEnv I) M"
    and invM: "core_module_invariant M"
    and wf_env: "tyenv_well_formed env"
    and wk_env: "typesubst_well_kinded env (CM_TypeSubst M)"
    using inv unfolding elab_decls_invariant_def by blast+
  have idemM: "idempotent_subst (CM_TypeSubst M)"
    using invM unfolding core_module_invariant_def by blast
  have I_nwt: "normalized_module_well_typed I"
    using core_module_well_typed_on_normalized[OF I_norm] I_wt by blast
  have scope_I: "tyenv_module_scope (CM_TyEnv I)"
    using I_nwt unfolding normalized_module_well_typed_def by blast

  \<comment> \<open>The two pivot equations.\<close>
  have subst_eq: "CM_TypeSubst L = CM_TypeSubst M"
    using link_pair_subst[OF link I_norm idemM] .
  have env_eq: "CM_TyEnv (normalize_module L) = env"
    unfolding env_def
    by (rule module_context_env_link_pair[OF link I_norm idemM scope_I])

  \<comment> \<open>The structural invariant of L.\<close>
  have invI: "core_module_invariant I"
    using core_module_well_typed_invariant[OF I_wt] .
  have A: "core_module_invariant L"
    by (rule link_modules_invariant[OF link]) (simp add: invI invM)

  \<comment> \<open>Substitution ranges well-kinded in CM_TyEnv L: the invariant states this
      over env, and env is the substitution image of CM_TyEnv L, which touches
      neither TE_TypeVars nor TE_Datatypes.\<close>
  have B: "typesubst_well_kinded (CM_TyEnv L) (CM_TypeSubst L)"
  proof -
    have tv: "TE_TypeVars (CM_TyEnv L) = TE_TypeVars env"
      unfolding env_eq[symmetric] by simp
    have dt: "TE_Datatypes (CM_TyEnv L) = TE_Datatypes env"
      unfolding env_eq[symmetric] by simp
    show ?thesis
      unfolding typesubst_well_kinded_def subst_eq
    proof (intro allI impI)
      fix n ty assume "fmlookup (CM_TypeSubst M) n = Some ty"
      then have "is_well_kinded env ty"
        using wk_env unfolding typesubst_well_kinded_def by blast
      then show "is_well_kinded (CM_TyEnv L) ty"
        using is_well_kinded_cong_env[OF tv dt] by blast
    qed
  qed

  \<comment> \<open>The normalized module.\<close>
  have C1: "tyenv_well_formed (CM_TyEnv (normalize_module L))"
    unfolding env_eq by (rule wf_env)
  have scope_L: "tyenv_module_scope (CM_TyEnv L)"
    using A unfolding core_module_invariant_def by blast
  have C2: "tyenv_module_scope (CM_TyEnv (normalize_module L))"
    using subst_preserves_tyenv_module_scope[OF scope_L] by simp
  have C3: "module_globals_well_typed (CM_TyEnv (normalize_module L))
                                      (CM_GlobalVars (normalize_module L))"
    using elab_link_globals[OF I_wt I_norm inv link] .
  have C4: "module_functions_well_typed (CM_TyEnv (normalize_module L))
                                        (CM_Functions (normalize_module L))"
    using elab_link_functions[OF I_wt I_norm inv link] .
  have C: "normalized_module_well_typed (normalize_module L)"
    unfolding normalized_module_well_typed_def
    using C1 C2 C3 C4 by blast

  show ?thesis
    unfolding core_module_well_typed_def
    using A B C by blast
qed


(* ========================================================================== *)
(* The main theorem                                                           *)
(* ========================================================================== *)

theorem elab_link_well_typed:
  assumes I_wt: "core_module_well_typed I"
      and I_norm: "CM_TypeSubst I = fmempty"
      and ee_wf: "elabenv_well_formed (CM_TyEnv I) elabEnv0"
      and own: "ownAbstract |\<subseteq>| TE_TypeVars (CM_TyEnv I)"
      and ctx_fresh: "\<forall>n. n |\<in>| TE_TypeVars (CM_TyEnv I) \<longrightarrow> tyvar_fresh_ok n 0"
      and fun_fresh: "\<forall>name info. fmlookup (TE_Functions (CM_TyEnv I)) name = Some info \<longrightarrow>
                        list_all (\<lambda>n. tyvar_fresh_ok n 0) (FI_TyArgs info)"
      and decl_fresh: "list_all decl_tyvars_fresh_ok decls"
      and elab: "elab_declarations (CM_TyEnv I) elabEnv0 ownAbstract decls = Inr (M, elabEnv')"
      and link: "link_modules [I, M] = Inr L"
  shows "core_module_well_typed L"
proof -
  have I_nwt: "normalized_module_well_typed I"
    using I_wt I_norm core_module_well_typed_on_normalized by blast
  have ctx: "elab_context_ok (CM_TyEnv I) ownAbstract"
    using I_nwt own ctx_fresh fun_fresh
    unfolding elab_context_ok_def normalized_module_well_typed_def by blast
  have init: "elab_decls_invariant (CM_TyEnv I) ownAbstract (CM_TyEnv I) elabEnv0
                empty_core_module"
    using elab_decls_invariant_init[OF ctx ee_wf] .
  from elab obtain envF where
    run: "elab_declaration_list (CM_TyEnv I) elabEnv0 ownAbstract empty_core_module decls
            = Inr (envF, elabEnv', M)"
    unfolding elab_declarations_def
    by (auto split: sum.splits prod.splits)
  have invF: "elab_decls_invariant (CM_TyEnv I) ownAbstract envF elabEnv' M"
    using elab_declaration_list_invariant[OF run init decl_fresh] .
  show ?thesis
    using elab_decls_invariant_link[OF I_wt I_norm invF link] .
qed

end

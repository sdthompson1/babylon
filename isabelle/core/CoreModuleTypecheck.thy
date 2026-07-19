theory CoreModuleTypecheck
  imports CoreModule CoreStmtTypecheck CoreTyEnvWellFormed
begin

(* Module-level well-typedness *)

(* A CoreModule is *well-typed* (predicate core_module_well_typed) if:
    - The module satisfies core_module_invariant from CoreModule.thy.
    - The types in the range of CM_TypeSubst are well-kinded in the module's
      own type env.
    - The *normalized* module (see normalize_module in CoreModule.thy)
      satisfies normalized_module_well_typed.

   A *normalized* module (one with an empty CM_TypeSubst) is well-typed (predicate
   normalized_module_well_typed) if:
    - The type environment is well-formed (tyenv_well_formed).
    - Every global variable defined in CM_GlobalVars, and every function defined
      in CM_Functions, is well-typed in the CM_TyEnv of the module.
    - The type environment is at module scope (tyenv_module_scope).

   Relationships:
    - core_module_well_typed implies core_module_invariant, but not conversely
      (lemma core_module_well_typed_invariant).
    - If a module's CM_TypeSubst is empty, then normalized_module_well_typed
      is equivalent to core_module_well_typed (lemma core_module_well_typed_on_normalized).
*)

(* Note: well-typedness is checked *after* substitution, e.g. if the substitution
   maps "T" to "i32", then it's legal to have a global constant of type "T" whose
   value is an i32; the value's type is checked only after T has been resolved
   to its definition (i32). *)



(* ========================================================================== *)
(* The body environment for checking a function definition                    *)
(* ========================================================================== *)

(* This defines the type environment in which the body of a function must
   typecheck.

   This is the module-level analogue of body_env_for (interpreter/StateMatchesEnv.thy)
   generalized in two ways:
     - the module env may have unresolved abstract types, so TE_TypeVars is
       TE_AbstractTypes env plus the function's own type parameters (rather
       than the type parameters alone); and
     - ghost functions are covered (body_env_for hard-wires NotGhost because
       the interpreter skips ghost calls): a ghost function's parameters are
       ghost locals and its type parameters are not runtime type variables.

   In the NotGhost case, the TE_RuntimeTypeVars formula is the same one used
   by tyenv_fun_ghost_constraint (CoreTyEnvWellFormed.thy) when it checks a
   non-ghost function's argument/return types for being runtime types, so
   runtime-type facts about the signature transfer directly to the body env.

   On a *closed* module (TE_AbstractTypes env = {||}) with a NotGhost
   function, this definition coincides field-for-field with body_env_for -
   which is why state_matches_env's body-typecheck obligation will match the
   module-level check when an InterpState is built. *)

definition module_body_env_for :: "CoreTyEnv \<Rightarrow> string list \<Rightarrow> FunInfo \<Rightarrow> CoreTyEnv" where
  "module_body_env_for env names info =
    env \<lparr>
      TE_LocalVars := fmap_of_list (zip names (map fst (FI_TmArgs info))),
      TE_GhostLocals := (if FI_Ghost info = Ghost then fset_of_list names else {||}),
      TE_ConstLocals := fset_of_list
        (map fst
             (filter (\<lambda>(_, vor). vor = Var) (zip names (map snd (FI_TmArgs info))))),
      TE_TypeVars := TE_AbstractTypes env |\<union>| fset_of_list (FI_TyArgs info),
      TE_RuntimeTypeVars := (TE_AbstractTypes env |\<inter>| TE_RuntimeTypeVars env)
                             |\<union>| (if FI_Ghost info = NotGhost
                                   then fset_of_list (FI_TyArgs info)
                                   else {||}),
      TE_ReturnType := FI_ReturnType info,
      TE_FunctionGhost := FI_Ghost info,
      TE_ProofGoal := None,
      TE_ProofTopLevel := False
    \<rparr>"


(* ========================================================================== *)
(* Clauses of normalized_module_well_typed                                    *)
(* ========================================================================== *)

(* Typechecking of global variables:

   Every defined global is declared in TE_GlobalVars, and its value has the
   declared type. (The elaborator evaluates constant initializers at compile
   time, so CM_GlobalVars holds ground CoreValues - not CoreTerms.)

   Note that it is allowed for a global to be declared in TE_GlobalVars, but
   not defined - this is exactly what an interface is. *)
definition module_globals_well_typed :: "CoreTyEnv \<Rightarrow> (string, CoreValue) fmap \<Rightarrow> bool" where
  "module_globals_well_typed env globals =
    (\<forall>name v. fmlookup globals name = Some v \<longrightarrow>
       (\<exists>declTy. fmlookup (TE_GlobalVars env) name = Some declTy \<and>
          value_has_type env v declTy))"

(* Typechecking of functions:

   Every defined function is declared in TE_Functions, and the CoreFunction
   is consistent with its FunInfo: the parameter names are distinct and line
   up one-for-one with the types and Var/Ref tags in FI_TmArgs, and the body
   (if any - extern functions have CF_Body = None) typechecks in the body
   environment. (Distinctness of parameter names is also required - this matches
   the same requirement in fun_info_matches_interp_fun.) *)
definition module_functions_well_typed :: "CoreTyEnv \<Rightarrow> (string, CoreFunction) fmap \<Rightarrow> bool" where
  "module_functions_well_typed env funs =
    (\<forall>name f. fmlookup funs name = Some f \<longrightarrow>
       (\<exists>info. fmlookup (TE_Functions env) name = Some info \<and>
               length (CF_Args f) = length (FI_TmArgs info) \<and>
               distinct (CF_Args f) \<and>
               (case CF_Body f of
                  None \<Rightarrow> True
                | Some body \<Rightarrow>
                    core_statement_list_type
                      (module_body_env_for env (CF_Args f) info)
                      (FI_Ghost info) body \<noteq> None)))"


(* ========================================================================== *)
(* normalized_module_well_typed                                               *)
(* ========================================================================== *)

(* The main predicate that states that an *already-normalized* module is
   well-typed. (A normalized module is one whose CM_TypeSubst is empty.)

   The definition basically just says that the type env is well-formed and
   at "module scope" (e.g. no local variables or type parameters present);
   and that the globals and functions are all well-typed in this env. *)

definition normalized_module_well_typed :: "CoreModule \<Rightarrow> bool" where
  "normalized_module_well_typed m =
    (tyenv_well_formed (CM_TyEnv m)
     \<and> tyenv_module_scope (CM_TyEnv m)
     \<and> module_globals_well_typed (CM_TyEnv m) (CM_GlobalVars m)
     \<and> module_functions_well_typed (CM_TyEnv m) (CM_Functions m))"


(* ========================================================================== *)
(* Recovering core_module_invariant from normalized well-typedness            *)
(* ========================================================================== *)

(* Except for three properties (idempotence, capture-avoidance, and the
   substitution-domain/TE_TypeVars disjointness), every conjunct of
   core_module_invariant already follows from normalized_module_well_typed of
   the normalized module. *)
lemma core_module_invariant_intro:
  assumes idem: "idempotent_subst (CM_TypeSubst m)"
      and cap:  "capture_avoiding m"
      and tv:   "fmdom (CM_TypeSubst m) |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
      and nwt:  "normalized_module_well_typed (normalize_module m)"
  shows "core_module_invariant m"
proof -
  have wf: "tyenv_well_formed (CM_TyEnv (normalize_module m))"
    and scope: "tyenv_module_scope (CM_TyEnv (normalize_module m))"
    using nwt unfolding normalized_module_well_typed_def by blast+
  have ghost: "module_ghost_subsets_ok m"
    using wf
    unfolding tyenv_well_formed_def tyenv_ghost_vars_subset_def
              tyenv_ghost_datatypes_subset_def module_ghost_subsets_ok_def
              normalize_module_def apply_subst_to_tyenv_def
    by simp
  have rtv: "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
    using wf
    unfolding tyenv_well_formed_def tyenv_runtime_tyvars_subset_def
              normalize_module_def apply_subst_to_tyenv_def
    by simp
  have scope_m: "tyenv_module_scope (CM_TyEnv m)"
    using scope
    unfolding tyenv_module_scope_def normalize_module_def
              apply_subst_to_tyenv_def
    by simp
  show ?thesis
    unfolding core_module_invariant_def
    using idem cap tv ghost rtv scope_m by blast
qed


(* ========================================================================== *)
(* core_module_well_typed                                                     *)
(* ========================================================================== *)

(* The main definition of what it means for a CoreModule to be well-typed:
   core_module_invariant must hold, every type in the range of CM_TypeSubst
   must be well-kinded, and the module must satisfy normalized_module_well_typed
   after normalization. *)

definition core_module_well_typed :: "CoreModule \<Rightarrow> bool" where
  "core_module_well_typed m =
    (core_module_invariant m
     \<and> typesubst_well_kinded (CM_TyEnv m) (CM_TypeSubst m)
     \<and> normalized_module_well_typed (normalize_module m))"

(* A well-typed module satisfies the standing structural invariant. *)
lemma core_module_well_typed_invariant:
  "core_module_well_typed m \<Longrightarrow> core_module_invariant m"
  unfolding core_module_well_typed_def by blast


(* ========================================================================== *)
(* Properties of core_module_well_typed                                       *)
(* ========================================================================== *)

(* On a normalized module (i.e. one whose substitution is empty),
   core_module_well_typed and normalized_module_well_typed are equivalent. *)
lemma core_module_well_typed_on_normalized:
  assumes "CM_TypeSubst m = fmempty"
  shows "core_module_well_typed m \<longleftrightarrow> normalized_module_well_typed m"
proof -
  have norm: "normalize_module m = m"
    using assms normalize_module_id_when_empty by simp
  show ?thesis
  proof
    assume "core_module_well_typed m"
    then show "normalized_module_well_typed m"
      unfolding core_module_well_typed_def norm by blast
  next
    assume nwt: "normalized_module_well_typed m"
    have idem: "idempotent_subst (CM_TypeSubst m)"
      using assms by simp
    have cap: "capture_avoiding m"
      using capture_avoiding_empty_subst[OF assms] .
    have tv: "fmdom (CM_TypeSubst m) |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
      using assms by simp
    have nwt': "normalized_module_well_typed (normalize_module m)"
      using nwt norm by simp
    have inv: "core_module_invariant m"
      using core_module_invariant_intro[OF idem cap tv nwt'] .
    have wk: "typesubst_well_kinded (CM_TyEnv m) (CM_TypeSubst m)"
      using assms unfolding typesubst_well_kinded_def by simp
    show "core_module_well_typed m"
      unfolding core_module_well_typed_def
      using inv wk nwt' by blast
  qed
qed

(* Normalization preserves well-typedness. *)
lemma normalize_module_preserves_well_typed:
  assumes "core_module_well_typed m"
  shows "core_module_well_typed (normalize_module m)"
proof -
  have "normalized_module_well_typed (normalize_module m)"
    using assms unfolding core_module_well_typed_def by blast
  then show ?thesis
    using core_module_well_typed_on_normalized[OF normalized_module_has_empty_subst]
    by simp
qed

end

theory MakeInterpState
  imports CoreInterp "../core/CoreModule" "../core/CoreFreeVars" "../graph/Dependency"
begin

(* ========================================================================== *)
(* InterpState construction                                                   *)
(* ========================================================================== *)

(* This theory builds an InterpState from a closed CoreModule (normally also
   well-typed - see MakeInterpStateCorrect), given ExternFunc implementations
   for its extern (CF_Body = None) functions and an initial world value.

   The construction:
    1. Normalizes the module (grounding all types; the substitution becomes
       empty).
    2. Populates IS_DefaultCtors from the type environment's datatype tables.
    3. Populates IS_Functions from the non-ghost CM_Functions entries (ghost
       functions do not exist at runtime), pairing each extern function with
       its supplied ExternFunc.
    4. Populates IS_Globals with the values of the non-ghost CM_GlobalVars
       initializers. Initializers are compile-time constant terms; they may
       reference other globals, so they are evaluated in dependency order.
       *Cyclic* constant dependencies ({x = a; a = x}) are detected here, by a
       topological-order check - by design this is not a well-typedness
       condition; it belongs with state construction.

   Every global is first given a *placeholder* default value (default_value at
   its declared type) before any initializer runs; the initializers are then
   evaluated in dependency order, each overwriting its placeholder. The
   placeholders are never observed - an initializer's free variables are its
   dependencies, all already overwritten with their real values - so the final
   values are exactly the dependency-order evaluation results. The placeholders
   exist for the correctness proof: they make the state match the module's
   type environment *before* the first initializer runs, and each evaluation
   step preserves that match, so the interpreter soundness theorem applies at
   every step without needing to reason about partially-populated states. *)


(* Errors from InterpState construction. *)
datatype InterpStateError =
  \<comment> \<open>The named global constants form a dependency cycle.\<close>
  ISE_CyclicGlobals "string list"
  \<comment> \<open>An extern (CF_Body = None) function has no supplied ExternFunc.\<close>
| ISE_MissingExtern string
  \<comment> \<open>A defined function has no FunInfo in the type environment
     (impossible for well-typed modules).\<close>
| ISE_MissingFunDecl string
  \<comment> \<open>A defined global has no declared type in the type environment
     (impossible for well-typed modules).\<close>
| ISE_MissingGlobalDecl string
  \<comment> \<open>The dependency analysis failed (impossible: the global names are
     distinct and dependencies are filtered to present names).\<close>
| ISE_DependencyAnalysis
  \<comment> \<open>Evaluating an initializer (or building a placeholder default) failed.\<close>
| ISE_InterpError InterpError


(* ========================================================================== *)
(* Default constructors                                                       *)
(* ========================================================================== *)

(* The IS_DefaultCtors entry for one datatype: the first data constructor in
   the datatype's TE_DataCtorsByType list, with its type variables and payload
   type from TE_DataCtors. None if the tables have no entry (impossible for
   the datatypes of a well-formed env). *)
definition default_ctor_for ::
  "CoreTyEnv \<Rightarrow> string \<Rightarrow> (string \<times> string list \<times> CoreType) option" where
  "default_ctor_for env dtName =
    (case fmlookup (TE_DataCtorsByType env) dtName of
       Some (ctorName # _) \<Rightarrow>
         (case fmlookup (TE_DataCtors env) ctorName of
            Some (_, tyVars, payloadTy) \<Rightarrow> Some (ctorName, tyVars, payloadTy)
          | None \<Rightarrow> None)
     | _ \<Rightarrow> None)"

(* IS_DefaultCtors: one entry per datatype for which default_ctor_for
   succeeds. *)
definition default_ctors_map ::
  "CoreTyEnv \<Rightarrow> (string, string \<times> string list \<times> CoreType) fmap" where
  "default_ctors_map env =
     fmmap_keys (\<lambda>dtName _. the (default_ctor_for env dtName))
       (fmfilter (\<lambda>dtName. default_ctor_for env dtName \<noteq> None)
          (TE_DataCtorsByType env))"


(* ========================================================================== *)
(* Base state                                                                 *)
(* ========================================================================== *)

(* The state before globals and functions are installed: everything empty
   except IS_DefaultCtors (and the world). Placeholder defaults are computed
   against this state - default_value only reads IS_DefaultCtors. *)
definition base_interp_state :: "CoreTyEnv \<Rightarrow> 'w \<Rightarrow> 'w InterpState" where
  "base_interp_state env world =
     \<lparr> IS_Globals = fmempty,
       IS_Locals = fmempty,
       IS_Refs = fmempty,
       IS_Store = [],
       IS_ConstLocals = {||},
       IS_TyArgs = fmempty,
       IS_DefaultCtors = default_ctors_map env,
       IS_Functions = fmempty,
       IS_World = world \<rparr>"


(* ========================================================================== *)
(* Functions                                                                  *)
(* ========================================================================== *)

(* The InterpFun for one non-ghost function: type parameters, argument Var/Ref
   tags and the impure flag come from the FunInfo; argument names from the
   CoreFunction; the body is supplied by the caller (the Core body, or the
   ExternFunc for an extern function). *)
definition make_interp_fun ::
  "FunInfo \<Rightarrow> CoreFunction \<Rightarrow> (CoreStatement list + 'w ExternFunc) \<Rightarrow> 'w InterpFun" where
  "make_interp_fun info f body =
     \<lparr> IF_TyArgs = FI_TyArgs info,
       IF_Args = zip (CF_Args f) (map snd (FI_TmArgs info)),
       IF_Body = body,
       IF_Impure = FI_Impure info \<rparr>"

(* Build the IS_Functions map from the (name, CoreFunction) pairs of
   CM_Functions. Ghost functions are skipped (they do not exist at runtime). *)
fun build_interp_funs ::
  "(string, 'w ExternFunc) fmap \<Rightarrow> CoreTyEnv \<Rightarrow> (string \<times> CoreFunction) list
   \<Rightarrow> InterpStateError + (string, 'w InterpFun) fmap" where
  "build_interp_funs externs env [] = Inr fmempty"
| "build_interp_funs externs env ((name, f) # rest) =
    (case fmlookup (TE_Functions env) name of
       None \<Rightarrow> Inl (ISE_MissingFunDecl name)
     | Some info \<Rightarrow>
         (case build_interp_funs externs env rest of
            Inl err \<Rightarrow> Inl err
          | Inr acc \<Rightarrow>
              if FI_Ghost info = Ghost then Inr acc
              else
                (case CF_Body f of
                   Some body \<Rightarrow>
                     Inr (fmupd name (make_interp_fun info f (Inl body)) acc)
                 | None \<Rightarrow>
                     (case fmlookup externs name of
                        None \<Rightarrow> Inl (ISE_MissingExtern name)
                      | Some externFun \<Rightarrow>
                          Inr (fmupd name (make_interp_fun info f (Inr externFun)) acc)))))"


(* ========================================================================== *)
(* Sorting the globals into dependency order                                  *)
(* ========================================================================== *)

(* The dependencies of one global: the free variables of its initializer,
   filtered to the names of the globals being sorted. (At module scope every
   free variable of a well-typed initializer is a global; the filter also
   drops references to ghost globals, which cannot occur in the non-ghost
   initializers we evaluate.) *)
definition global_init_deps ::
  "string fset \<Rightarrow> string \<times> CoreTerm \<Rightarrow> string list" where
  "global_init_deps globalNames p =
     filter (\<lambda>n. n |\<in>| globalNames)
       (sorted_list_of_fset (core_term_free_vars (snd p)))"

(* Split the dependency sorter's output: a non-singleton SCC is a cycle; a
   singleton whose own dependency list contains its own name is a self-cycle
   (a self-loop is a singleton SCC, which the non-singleton check cannot
   catch); otherwise concatenate in topological order. *)
fun check_global_sccs ::
  "(string \<times> CoreTerm \<Rightarrow> string list) \<Rightarrow> (string \<times> CoreTerm) list list
   \<Rightarrow> InterpStateError + (string \<times> CoreTerm) list" where
  "check_global_sccs deps [] = Inr []"
| "check_global_sccs deps ([] # rest) = check_global_sccs deps rest"
| "check_global_sccs deps ([g] # rest) =
    (if fst g \<in> set (deps g)
     then Inl (ISE_CyclicGlobals [fst g])
     else (case check_global_sccs deps rest of
             Inl err \<Rightarrow> Inl err
           | Inr gs \<Rightarrow> Inr (g # gs)))"
| "check_global_sccs deps (scc # rest) =
    Inl (ISE_CyclicGlobals (map fst scc))"

(* Sort the (name, initializer) pairs into dependency order; dependency cycles
   among the global constants are errors. The underlying dependency analysis
   cannot itself fail here: the names come from an fmap's domain so are
   distinct, and dependencies are filtered to names present in the list. *)
definition sort_globals ::
  "(string \<times> CoreTerm) list \<Rightarrow> InterpStateError + (string \<times> CoreTerm) list" where
  "sort_globals pairs =
     (let globalNames = fset_of_list (map fst pairs);
          deps = global_init_deps globalNames
      in case analyze_dependencies_generic pairs fst deps of
           Inl _ \<Rightarrow> Inl ISE_DependencyAnalysis
         | Inr sccs \<Rightarrow> check_global_sccs deps sccs)"

(* check_global_sccs returns exactly the pairs of its SCC list, concatenated
   in topological order: the multiset is preserved. *)
lemma check_global_sccs_mset:
  assumes "check_global_sccs deps sccs = Inr gs"
  shows "mset gs = mset (concat sccs)"
  using assms
proof (induction deps sccs arbitrary: gs rule: check_global_sccs.induct)
  case 1
  then show ?case by auto
next
  case (2 deps rest)
  then show ?case by simp
next
  case (3 deps g rest)
  from "3.prems" have cond: "fst g \<notin> set (deps g)"
    by (auto split: if_splits)
  from "3.prems" cond obtain gs' where
    rest_ok: "check_global_sccs deps rest = Inr gs'" and gs_eq: "gs = g # gs'"
    by (auto split: sum.splits)
  show ?case
    using "3.IH"[OF cond rest_ok] by (simp add: gs_eq)
next
  case 4
  then show ?case by auto
qed

(* Hence sort_globals returns a permutation of its input. *)
lemma sort_globals_mset:
  assumes ok: "sort_globals pairs = Inr sortedPairs"
  shows "mset sortedPairs = mset pairs"
proof -
  define deps where
    "deps = global_init_deps (fset_of_list (map fst pairs))"
  from ok obtain sccs where
    analysis: "analyze_dependencies_generic pairs fst deps = Inr sccs" and
    checked: "check_global_sccs deps sccs = Inr sortedPairs"
    unfolding sort_globals_def Let_def deps_def
    by (auto split: sum.splits)
  have "mset sortedPairs = mset (concat sccs)"
    by (rule check_global_sccs_mset[OF checked])
  also have "\<dots> = mset pairs"
    by (rule analyze_dependencies_generic_permutation[OF analysis])
  finally show ?thesis .
qed


(* ========================================================================== *)
(* Globals                                                                    *)
(* ========================================================================== *)

(* Placeholder defaults: one default_value per global, at its declared type.
   All defaults are computed against the same base state (default_value only
   reads IS_DefaultCtors, which never changes). *)
fun compute_global_defaults ::
  "nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreTyEnv \<Rightarrow> (string \<times> CoreTerm) list
   \<Rightarrow> InterpStateError + (string, CoreValue) fmap" where
  "compute_global_defaults fuel baseState env [] = Inr fmempty"
| "compute_global_defaults fuel baseState env ((name, _) # rest) =
    (case fmlookup (TE_GlobalVars env) name of
       None \<Rightarrow> Inl (ISE_MissingGlobalDecl name)
     | Some declTy \<Rightarrow>
         (case default_value fuel baseState declTy of
            Inl err \<Rightarrow> Inl (ISE_InterpError err)
          | Inr v \<Rightarrow>
              (case compute_global_defaults fuel baseState env rest of
                 Inl err \<Rightarrow> Inl err
               | Inr acc \<Rightarrow> Inr (fmupd name v acc))))"

(* Evaluate the initializers left to right (the caller passes them in
   dependency order), each overwriting its global's placeholder default. *)
fun eval_globals ::
  "nat \<Rightarrow> 'w InterpState \<Rightarrow> (string \<times> CoreTerm) list
   \<Rightarrow> InterpStateError + 'w InterpState" where
  "eval_globals fuel state [] = Inr state"
| "eval_globals fuel state ((name, tm) # rest) =
    (case interp_term fuel state tm of
       Inl err \<Rightarrow> Inl (ISE_InterpError err)
     | Inr v \<Rightarrow>
         eval_globals fuel
           (state \<lparr> IS_Globals := fmupd name v (IS_Globals state) \<rparr>)
           rest)"


(* ========================================================================== *)
(* Main entry point                                                           *)
(* ========================================================================== *)

(* Build an InterpState from a closed CoreModule. `fuel` bounds the work of
   the placeholder-default computation and of each initializer evaluation
   (running out of fuel is an ISE_InterpError InsufficientFuel). `externs`
   supplies an ExternFunc for each extern (CF_Body = None) non-ghost
   function. *)
definition make_interp_state ::
  "nat \<Rightarrow> 'w \<Rightarrow> (string, 'w ExternFunc) fmap \<Rightarrow> CoreModule
   \<Rightarrow> InterpStateError + 'w InterpState" where
  "make_interp_state fuel world externs m =
    (let m' = normalize_module m;
         env = CM_TyEnv m';
         baseState = base_interp_state env world;
         globals = sorted_list_of_fmap (CM_GlobalVars m')
     in (case build_interp_funs externs env (sorted_list_of_fmap (CM_Functions m')) of
          Inl err \<Rightarrow> Inl err
        | Inr funs \<Rightarrow>
       (case compute_global_defaults fuel baseState env globals of
          Inl err \<Rightarrow> Inl err
        | Inr defaults \<Rightarrow>
       (case sort_globals globals of
          Inl err \<Rightarrow> Inl err
        | Inr sortedGlobals \<Rightarrow>
       eval_globals fuel
         (baseState \<lparr> IS_Globals := defaults, IS_Functions := funs \<rparr>)
         sortedGlobals))))"

end

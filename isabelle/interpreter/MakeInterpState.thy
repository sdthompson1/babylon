theory MakeInterpState
  imports CoreInterp "../core/CoreModule"
      "HOL-Library.Char_ord" "HOL-Library.List_Lexorder"
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
    4. Populates IS_Globals directly from CM_GlobalVars: the elaborator has
       already evaluated every constant initializer to a CoreValue at compile
       time, so state construction just installs the values. (There is no
       evaluation, no dependency sorting, and no fuel here.) *)


(* Errors from InterpState construction. *)
datatype InterpStateError =
  \<comment> \<open>An extern (CF_Body = None) function has no supplied ExternFunc.\<close>
  ISE_MissingExtern string
  \<comment> \<open>A defined function has no FunInfo in the type environment
     (impossible for well-typed modules).\<close>
| ISE_MissingFunDecl string


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
   except IS_DefaultCtors (and the world). *)
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
(* Main entry point                                                           *)
(* ========================================================================== *)

(* Build an InterpState from a closed CoreModule. `externs` supplies an
   ExternFunc for each extern (CF_Body = None) non-ghost function. *)
definition make_interp_state ::
  "'w \<Rightarrow> (string, 'w ExternFunc) fmap \<Rightarrow> CoreModule
   \<Rightarrow> InterpStateError + 'w InterpState" where
  "make_interp_state world externs m =
    (let m' = normalize_module m;
         env = CM_TyEnv m'
     in case build_interp_funs externs env (sorted_list_of_fmap (CM_Functions m')) of
          Inl err \<Rightarrow> Inl err
        | Inr funs \<Rightarrow>
            Inr (base_interp_state env world
                   \<lparr> IS_Globals := CM_GlobalVars m', IS_Functions := funs \<rparr>))"

end

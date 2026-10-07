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
    2. Copies the type environment's datatype tables into IS_Datatypes,
       IS_DataCtors and IS_DataCtorsByType.
    3. Populates IS_Functions from the CM_Functions entries, pairing each
       extern function with its supplied ExternFunc.
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
(* Base state                                                                 *)
(* ========================================================================== *)

(* The state before globals and functions are installed: everything empty
   except the datatype tables and the world. *)
definition base_interp_state :: "CoreTyEnv \<Rightarrow> 'w \<Rightarrow> 'w InterpState" where
  "base_interp_state env world =
     \<lparr> IS_Globals = fmempty,
       IS_Locals = fmempty,
       IS_Refs = fmempty,
       IS_Store = [],
       IS_ConstLocals = {||},
       IS_TyArgs = fmempty,
       IS_Datatypes = TE_Datatypes env,
       IS_DataCtors = TE_DataCtors env,
       IS_DataCtorsByType = TE_DataCtorsByType env,
       IS_Functions = fmempty,
       IS_World = world \<rparr>"


(* ========================================================================== *)
(* Functions                                                                  *)
(* ========================================================================== *)

(* The InterpFun for one function: type parameters, argument Var/Ref tags
   and the impure flag come from the FunInfo; argument names from the
   CoreFunction; the body is supplied by the caller (the Core body, or the
   ExternFunc for an extern function). *)
definition make_interp_fun ::
  "FunInfo \<Rightarrow> CoreFunction \<Rightarrow> (CoreStatement list + 'w ExternFunc) \<Rightarrow> 'w InterpFun" where
  "make_interp_fun info f body =
     \<lparr> IF_TyArgs = FI_TyArgs info,
       IF_Args = zip (CF_Args f) (map (fst \<circ> snd) (FI_TmArgs info)),
       IF_Body = body,
       IF_Impure = FI_Impure info \<rparr>"

(* Build the IS_Functions map from the (name, CoreFunction) pairs of
   CM_Functions. Ghost functions are included. *)
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
   ExternFunc for each extern (CF_Body = None) function. *)
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

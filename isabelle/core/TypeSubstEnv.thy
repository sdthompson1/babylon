theory TypeSubstEnv
  imports TypeSubst CoreTyEnv
begin

(* ========================================================================== *)
(* Type substitution on type environments                                     *)
(*                                                                            *)
(* The type-environment analogue of apply_subst_to_term (TypeSubstTerm.thy)   *)
(* and apply_subst_to_statement (TypeSubstStmt.thy). Pushes a type            *)
(* substitution through every CoreType embedded in a CoreTyEnv: global        *)
(* variable types, function argument/return types, and constructor payload    *)
(* types. The type-variable and datatype-arity fields carry no CoreType, so   *)
(* they are left untouched.                                                   *)
(*                                                                            *)
(* Used by normalize_module (CoreModule.thy).                                 *)
(* ========================================================================== *)


(* Substitute through a FunInfo: argument types (keeping their VarOrRef tags)   *)
(* and the return type. The type parameters (FI_TyArgs) and the ghost/impure    *)
(* flags carry no CoreType, so they are unchanged.                              *)
definition apply_subst_to_funinfo :: "TypeSubst \<Rightarrow> FunInfo \<Rightarrow> FunInfo" where
  "apply_subst_to_funinfo subst info =
    info \<lparr>
      FI_TmArgs := map (\<lambda>(ty, vr). (apply_subst subst ty, vr)) (FI_TmArgs info),
      FI_ReturnType := apply_subst subst (FI_ReturnType info)
    \<rparr>"

(* Substitute through a data-constructor entry (datatype name, type variables,  *)
(* payload type): only the payload type carries a CoreType. *)
definition apply_subst_to_datactor ::
    "TypeSubst \<Rightarrow> (string \<times> string list \<times> CoreType) \<Rightarrow> (string \<times> string list \<times> CoreType)" where
  "apply_subst_to_datactor subst entry =
    (case entry of (dtName, tyvars, payloadTy) \<Rightarrow>
       (dtName, tyvars, apply_subst subst payloadTy))"

(* Substitute through every CoreType embedded in a type environment: global      *)
(* variable types (TE_GlobalVars), the argument/return types of each function     *)
(* (TE_Functions), and constructor payload types (TE_DataCtors). The type-variable *)
(* and datatype-arity fields carry no CoreType, so they are unchanged.            *)
definition apply_subst_to_tyenv :: "TypeSubst \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "apply_subst_to_tyenv subst env =
    env \<lparr>
      TE_GlobalVars := fmmap (apply_subst subst) (TE_GlobalVars env),
      TE_Functions  := fmmap (apply_subst_to_funinfo subst) (TE_Functions env),
      TE_DataCtors  := fmmap (apply_subst_to_datactor subst) (TE_DataCtors env)
    \<rparr>"


(* ========================================================================== *)
(* Field projections                                                          *)
(* ========================================================================== *)

lemma apply_subst_to_funinfo_FI_TyArgs [simp]:
  "FI_TyArgs (apply_subst_to_funinfo subst info) = FI_TyArgs info"
  by (simp add: apply_subst_to_funinfo_def)

lemma apply_subst_to_funinfo_FI_TmArgs [simp]:
  "FI_TmArgs (apply_subst_to_funinfo subst info)
     = map (\<lambda>(ty, vr). (apply_subst subst ty, vr)) (FI_TmArgs info)"
  by (simp add: apply_subst_to_funinfo_def)

lemma apply_subst_to_funinfo_FI_ReturnType [simp]:
  "FI_ReturnType (apply_subst_to_funinfo subst info)
     = apply_subst subst (FI_ReturnType info)"
  by (simp add: apply_subst_to_funinfo_def)

lemma apply_subst_to_funinfo_FI_Ghost [simp]:
  "FI_Ghost (apply_subst_to_funinfo subst info) = FI_Ghost info"
  by (simp add: apply_subst_to_funinfo_def)

lemma apply_subst_to_funinfo_FI_Impure [simp]:
  "FI_Impure (apply_subst_to_funinfo subst info) = FI_Impure info"
  by (simp add: apply_subst_to_funinfo_def)

lemma apply_subst_to_datactor_simps [simp]:
  "apply_subst_to_datactor subst (dtName, tyvars, payloadTy)
     = (dtName, tyvars, apply_subst subst payloadTy)"
  by (simp add: apply_subst_to_datactor_def)


(* ========================================================================== *)
(* Empty substitution is the identity                                         *)
(* ========================================================================== *)

(* The empty substitution leaves a function info unchanged. *)
lemma apply_subst_to_funinfo_empty [simp]:
  "apply_subst_to_funinfo fmempty info = info"
  unfolding apply_subst_to_funinfo_def
  by (simp add: list.map_ident_strong split: prod.splits)

(* The empty substitution leaves a data-constructor entry unchanged. *)
lemma apply_subst_to_datactor_empty [simp]:
  "apply_subst_to_datactor fmempty entry = entry"
  unfolding apply_subst_to_datactor_def
  by (simp split: prod.splits)

(* The empty substitution leaves a type environment unchanged. *)
lemma apply_subst_to_tyenv_empty [simp]:
  "apply_subst_to_tyenv fmempty env = env"
  unfolding apply_subst_to_tyenv_def
  by (simp add: fmap.map_ident_strong)

end

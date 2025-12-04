theory ElabType
  imports "../base/IntRange" "../type_system/BabKindcheck" "SubstituteTypes"
begin

(* This file defines type elaboration: checking and transforming user-provided types
   to ensure they are ground (no metavariables), have all typedefs expanded, and are
   well-kinded. Typedef expansion happens inline - when we encounter a typedef name,
   we substitute the type arguments into the typedef body and continue elaborating. *)

datatype TypeError =
  TyErr_OutOfFuel Location
  | TyErr_IntLiteralOutOfRange Location
  | TyErr_InvalidCast Location
  | TyErr_NegateRequiresSigned Location
  | TyErr_ComplementRequiresFiniteInt Location
  | TyErr_NotRequiresBool Location
  | TyErr_UnknownName Location string
  | TyErr_GhostVariableInNonGhost Location string
  | TyErr_WrongNumberOfTypeArgs Location string nat nat  (* name, expected, actual *)
  | TyErr_DataCtorHasPayload Location string  (* For non-nullary constructors used without args *)
  | TyErr_NonRuntimeTypeArg Location
  | TyErr_TypeMismatch Location BabType BabType    (* loc, type1, type2 *)
  | TyErr_ConditionNotBool Location BabType        (* loc, actual condition type *)
  | TyErr_MetavariableInInput                      (* metavariable found in input type *)
  | TyErr_UnknownTypeName Location string
  | TyErr_WrongTypeArity Location string nat nat   (* name, expected, actual *)
  | TyErr_InvalidArrayDimension Location

type_synonym Typedefs = "(string, DeclTypedef) fmap"


(* Type elaboration: check groundness, expand typedefs, kind-check, and check runtime constraints.
   Returns the elaborated type with all typedefs expanded. *)

fun elab_type :: "nat \<Rightarrow> Typedefs \<Rightarrow> BabTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabType
                 \<Rightarrow> TypeError list + BabType"
and elab_type_list :: "nat \<Rightarrow> Typedefs \<Rightarrow> BabTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabType list
                       \<Rightarrow> TypeError list + BabType list"
  where
  "elab_type 0 _ _ _ ty = Inl [TyErr_OutOfFuel (bab_type_location ty)]"

| "elab_type (Suc fuel) typedefs env ghost (BabTy_Meta n) =
    Inl [TyErr_MetavariableInInput]"

| "elab_type (Suc fuel) typedefs env ghost (BabTy_Name loc name tyArgs) =
    \<comment> \<open>First elaborate the type arguments\<close>
    (case elab_type_list fuel typedefs env ghost tyArgs of
      Inl errs \<Rightarrow> Inl errs
    | Inr elabTyArgs \<Rightarrow>
        \<comment> \<open>Check if it's a type variable\<close>
        if name |\<in>| TE_TypeVars env then
          (if elabTyArgs = [] then
            Inr (BabTy_Name loc name [])
          else
            Inl [TyErr_WrongTypeArity loc name 0 (length tyArgs)])
        \<comment> \<open>Check if it's a typedef - if so, expand it\<close>
        else (case fmlookup typedefs name of
          Some td \<Rightarrow>
            (if length elabTyArgs \<noteq> length (DT_TyArgs td) then
              Inl [TyErr_WrongTypeArity loc name (length (DT_TyArgs td)) (length tyArgs)]
            else (case DT_Definition td of
              Some body \<Rightarrow>
                \<comment> \<open>Substitute type args into typedef body and continue elaborating\<close>
                let subst = fmap_of_list (zip (DT_TyArgs td) elabTyArgs);
                    expandedTy = substitute_bab_type subst body
                in elab_type fuel typedefs env ghost expandedTy
            | None \<Rightarrow>
                \<comment> \<open>Abstract/extern type - reject for now (TODO: support later)\<close>
                Inl [TyErr_UnknownTypeName loc name]))
        \<comment> \<open>Check if it's a datatype\<close>
        | None \<Rightarrow>
            (case fmlookup (TE_Datatypes env) name of
              Some dt \<Rightarrow>
                (if length elabTyArgs \<noteq> length (DD_TyArgs dt) then
                  Inl [TyErr_WrongTypeArity loc name (length (DD_TyArgs dt)) (length tyArgs)]
                else
                  let resultTy = BabTy_Name loc name elabTyArgs
                  in if ghost = NotGhost \<and> \<not> is_runtime_type resultTy then
                       Inl [TyErr_NonRuntimeTypeArg loc]
                     else
                       Inr resultTy)
            | None \<Rightarrow> Inl [TyErr_UnknownTypeName loc name])))"

| "elab_type (Suc fuel) typedefs env ghost (BabTy_Bool loc) =
    Inr (BabTy_Bool loc)"

| "elab_type (Suc fuel) typedefs env ghost (BabTy_FiniteInt loc sign bits) =
    Inr (BabTy_FiniteInt loc sign bits)"

| "elab_type (Suc fuel) typedefs env ghost (BabTy_MathInt loc) =
    (if ghost = NotGhost then
      Inl [TyErr_NonRuntimeTypeArg loc]
    else
      Inr (BabTy_MathInt loc))"

| "elab_type (Suc fuel) typedefs env ghost (BabTy_MathReal loc) =
    (if ghost = NotGhost then
      Inl [TyErr_NonRuntimeTypeArg loc]
    else
      Inr (BabTy_MathReal loc))"

| "elab_type (Suc fuel) typedefs env ghost (BabTy_Tuple loc tys) =
    (case elab_type_list fuel typedefs env ghost tys of
      Inl errs \<Rightarrow> Inl errs
    | Inr elabTys \<Rightarrow> Inr (BabTy_Tuple loc elabTys))"

| "elab_type (Suc fuel) typedefs env ghost (BabTy_Record loc flds) =
    (case elab_type_list fuel typedefs env ghost (map snd flds) of
      Inl errs \<Rightarrow> Inl errs
    | Inr elabFldTys \<Rightarrow> Inr (BabTy_Record loc (zip (map fst flds) elabFldTys)))"

| "elab_type (Suc fuel) typedefs env ghost (BabTy_Array loc elemTy dims) =
    (if \<not> array_dims_well_kinded dims then
      Inl [TyErr_InvalidArrayDimension loc]
    else
      (case elab_type fuel typedefs env ghost elemTy of
        Inl errs \<Rightarrow> Inl errs
      | Inr elabElemTy \<Rightarrow> Inr (BabTy_Array loc elabElemTy dims)))"

| "elab_type_list 0 _ _ _ _ = Inl [TyErr_OutOfFuel no_loc]"

| "elab_type_list (Suc fuel) _ _ _ [] = Inr []"

| "elab_type_list (Suc fuel) typedefs env ghost (ty # tys) =
    (case elab_type (Suc fuel) typedefs env ghost ty of
      Inl errs \<Rightarrow> Inl errs
    | Inr ty' \<Rightarrow>
        (case elab_type_list fuel typedefs env ghost tys of
          Inl errs \<Rightarrow> Inl errs
        | Inr tys' \<Rightarrow> Inr (ty' # tys')))"

end

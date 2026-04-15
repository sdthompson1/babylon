theory ElabType
  imports TypeError Typedefs "../core/CoreTyEnv" "../util/NatToString"
begin

(* Input: env, typedefs, ghost mode, input type (or list) *)
(* Output: either a list of errors, or an elaborated type (or list) *)

fun elab_type :: "CoreTyEnv \<Rightarrow> Typedefs \<Rightarrow> GhostOrNot \<Rightarrow> BabType
                  \<Rightarrow> TypeError list + CoreType"
and elab_type_list :: "CoreTyEnv \<Rightarrow> Typedefs \<Rightarrow> GhostOrNot \<Rightarrow> BabType list
                      \<Rightarrow> TypeError list + CoreType list"
where
  "elab_type env typedefs ghost (BabTy_Name loc name tyargs) =
    (case elab_type_list env typedefs ghost tyargs of
      Inl errs \<Rightarrow> Inl errs
    | Inr elabTyArgs \<Rightarrow>
        (case fmlookup typedefs name of
          Some (tyvars, targetTy) \<Rightarrow>
            \<comment> \<open>Typedef case (also handles type variables, which map to CoreTy_Var)\<close>
            (if length elabTyArgs \<noteq> length tyvars then
              Inl [TyErr_WrongTypeArity loc name (length tyvars) (length tyargs)]
             else
              let subst = fmap_of_list (zip tyvars elabTyArgs);
                  resultTy = apply_subst subst targetTy
              in if ghost = NotGhost \<and> \<not> is_runtime_type env resultTy then
                   Inl [TyErr_NonRuntimeType loc]
                 else
                   Inr resultTy)
        | None \<Rightarrow>
            (case fmlookup (TE_Datatypes env) name of
              Some expectedArity \<Rightarrow>
                \<comment> \<open>Datatype case\<close>
                (if length elabTyArgs \<noteq> expectedArity then
                  Inl [TyErr_WrongTypeArity loc name expectedArity (length tyargs)]
                 else if ghost = NotGhost \<and> (\<not> list_all (is_runtime_type env) elabTyArgs
                        \<or> name |\<in>| TE_GhostDatatypes env) then
                  Inl [TyErr_NonRuntimeType loc]
                 else
                  Inr (CoreTy_Datatype name elabTyArgs))
            | None \<Rightarrow>
                \<comment> \<open>Unknown type name\<close>
                Inl [TyErr_UnknownTypeName loc name])))"

| "elab_type env typedefs ghost (BabTy_Bool loc) =
    Inr CoreTy_Bool"

| "elab_type env typedefs ghost (BabTy_FiniteInt loc sign bits) =
    Inr (CoreTy_FiniteInt sign bits)"

| "elab_type env typedefs ghost (BabTy_MathInt loc) =
    (if ghost = NotGhost then
      Inl [TyErr_NonRuntimeType loc]
    else
      Inr CoreTy_MathInt)"

| "elab_type env typedefs ghost (BabTy_MathReal loc) =
    (if ghost = NotGhost then
      Inl [TyErr_NonRuntimeType loc]
    else
      Inr CoreTy_MathReal)"

| "elab_type env typedefs ghost (BabTy_Tuple loc types) =
    (case elab_type_list env typedefs ghost types of
      Inl errs \<Rightarrow> Inl errs
    | Inr elabTys \<Rightarrow> Inr (CoreTy_Record (zip (tuple_field_names (length elabTys)) elabTys)))"

  (* The Record case preserves field names *)
| "elab_type env typedefs ghost (BabTy_Record loc flds) =
    (case elab_type_list env typedefs ghost (map snd flds) of
      Inl errs \<Rightarrow> Inl errs
    | Inr elabTys \<Rightarrow> Inr (CoreTy_Record (zip (map fst flds) elabTys)))"

  (* Array case TODO (as we may have to evaluate constants which we can't do yet) 
     Just elaborate to Bool for now *)
| "elab_type env typedefs ghost (BabTy_Array loc elemTy dims) =
    Inr CoreTy_Bool"

| "elab_type_list env typedefs ghost [] = Inr []"

| "elab_type_list env typedefs ghost (ty # tys) =
    (case (elab_type env typedefs ghost ty,
           elab_type_list env typedefs ghost tys) of
      (Inl errs1, Inl errs2) \<Rightarrow> Inl (errs1 @ errs2)
    | (Inl errs, Inr _) \<Rightarrow> Inl errs
    | (Inr _, Inl errs) \<Rightarrow> Inl errs
    | (Inr ty', Inr tys') \<Rightarrow> Inr (ty' # tys'))"

end

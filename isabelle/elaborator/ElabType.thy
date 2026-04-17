theory ElabType
  imports TypeError ElabEnv "../core/CoreTyEnv" "../util/NatToString" "../util/DistinctCheck"
begin

(* Input: env, elabEnv, ghost mode, input type (or list) *)
(* Output: either a list of errors, or an elaborated type (or list) *)

(* Elaborate a single array dimension.
   BabDim_Fixed must contain a literal integer within uint64 range;
   anything else produces TyErr_InvalidArrayDimension. *)
fun elab_dimension :: "BabDimension \<Rightarrow> Location \<Rightarrow> TypeError + CoreDimension" where
  "elab_dimension BabDim_Unknown loc = Inr CoreDim_Unknown"
| "elab_dimension BabDim_Allocatable loc = Inr CoreDim_Allocatable"
| "elab_dimension (BabDim_Fixed (BabTm_Literal _ (BabLit_Int n))) loc =
    (if int_in_range (int_range Unsigned IntBits_64) n then
       Inr (CoreDim_Fixed n)
     else
       Inl (TyErr_InvalidArrayDimension loc))"
| "elab_dimension (BabDim_Fixed _) loc = Inl (TyErr_InvalidArrayDimension loc)"

fun elab_dimensions :: "BabDimension list \<Rightarrow> Location \<Rightarrow> TypeError list + CoreDimension list" where
  "elab_dimensions [] loc = Inr []"
| "elab_dimensions (d # ds) loc =
    (case (elab_dimension d loc, elab_dimensions ds loc) of
      (Inl err, Inl errs) \<Rightarrow> Inl (err # errs)
    | (Inl err, Inr _) \<Rightarrow> Inl [err]
    | (Inr _, Inl errs) \<Rightarrow> Inl errs
    | (Inr d', Inr ds') \<Rightarrow> Inr (d' # ds'))"

(* Main type elaboration function. *)
fun elab_type :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabType
                  \<Rightarrow> TypeError list + CoreType"
and elab_type_list :: "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabType list
                      \<Rightarrow> TypeError list + CoreType list"
where
  "elab_type env elabEnv ghost (BabTy_Name loc name tyargs) =
    (case elab_type_list env elabEnv ghost tyargs of
      Inl errs \<Rightarrow> Inl errs
    | Inr elabTyArgs \<Rightarrow>
        (case fmlookup (EE_Typedefs elabEnv) name of
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

| "elab_type env elabEnv ghost (BabTy_Bool loc) =
    Inr CoreTy_Bool"

| "elab_type env elabEnv ghost (BabTy_FiniteInt loc sign bits) =
    Inr (CoreTy_FiniteInt sign bits)"

| "elab_type env elabEnv ghost (BabTy_MathInt loc) =
    (if ghost = NotGhost then
      Inl [TyErr_NonRuntimeType loc]
    else
      Inr CoreTy_MathInt)"

| "elab_type env elabEnv ghost (BabTy_MathReal loc) =
    (if ghost = NotGhost then
      Inl [TyErr_NonRuntimeType loc]
    else
      Inr CoreTy_MathReal)"

| "elab_type env elabEnv ghost (BabTy_Tuple loc types) =
    (case elab_type_list env elabEnv ghost types of
      Inl errs \<Rightarrow> Inl errs
    | Inr elabTys \<Rightarrow> Inr (CoreTy_Record (zip (tuple_field_names (length elabTys)) elabTys)))"

  (* The Record case preserves field names *)
| "elab_type env elabEnv ghost (BabTy_Record loc flds) =
    (case first_duplicate_name fst flds of
      Some dupName \<Rightarrow> Inl [TyErr_DuplicateFieldName loc dupName]
    | None \<Rightarrow>
        (case elab_type_list env elabEnv ghost (map snd flds) of
          Inl errs \<Rightarrow> Inl errs
        | Inr elabTys \<Rightarrow> Inr (CoreTy_Record (zip (map fst flds) elabTys))))"

| "elab_type env elabEnv ghost (BabTy_Array loc elemTy dims) =
    (case (elab_type env elabEnv ghost elemTy, elab_dimensions dims loc) of
      (Inl errs1, Inl errs2) \<Rightarrow> Inl (errs1 @ errs2)
    | (Inl errs, Inr _) \<Rightarrow> Inl errs
    | (Inr _, Inl errs) \<Rightarrow> Inl errs
    | (Inr elemTy', Inr dims') \<Rightarrow>
        (if dims = [] \<or> \<not> dims_uniform dims' then
           Inl [TyErr_InvalidArrayDimension loc]
         else
           Inr (CoreTy_Array elemTy' dims')))"

| "elab_type_list env elabEnv ghost [] = Inr []"

| "elab_type_list env elabEnv ghost (ty # tys) =
    (case (elab_type env elabEnv ghost ty,
           elab_type_list env elabEnv ghost tys) of
      (Inl errs1, Inl errs2) \<Rightarrow> Inl (errs1 @ errs2)
    | (Inl errs, Inr _) \<Rightarrow> Inl errs
    | (Inr _, Inl errs) \<Rightarrow> Inl errs
    | (Inr ty', Inr tys') \<Rightarrow> Inr (ty' # tys'))"

end

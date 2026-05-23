theory DecPattern
  imports ElabType UnifyCompose
    "../bab/BabSyntax" "../core/TypeSubst"
begin

section \<open>Decorated pattern type\<close>

(* DecPattern is what the elaborator produces after typechecking each
   source pattern against the scrutinee's type. Compared to BabPattern:
   no Locations, no DP_Tuple (tuples desugar to "0"/"1"/... records),
   and DP_Var carries its elaborated CoreType inline.

   DP_Record invariant (maintained by elaborator): every DP_Record lists
   every field of the record type, in declaration order. Source patterns
   that omit or reorder fields are normalised. This lets downstream
   consumers read the full field list off any DP_Record representative
   via `map fst flds`, and expansion is a parallel walk. *)
datatype DecPattern =
    DP_Var VarOrRef string CoreType
  | DP_Bool bool
  | DP_Int int
  | DP_Record "(string \<times> DecPattern) list"
  | DP_Variant string "DecPattern option"
  | DP_Wildcard


section \<open>Helpers\<close>

(* Look up a name in an association list of (string * DecPattern), or
   return DP_Wildcard if not found. *)
definition lookup_or_wildcard ::
  "(string \<times> DecPattern) list \<Rightarrow> string \<Rightarrow> DecPattern" where
  "lookup_or_wildcard flds name =
    (case map_of flds name of Some p \<Rightarrow> p | None \<Rightarrow> DP_Wildcard)"

(* Reorder record patterns to match the field declaration order, adding
   DP_Wildcard for any fields that were not included by the user. *)
definition build_record_dec_patterns ::
  "(string \<times> CoreType) list \<Rightarrow> string list \<Rightarrow> DecPattern list
   \<Rightarrow> (string \<times> DecPattern) list" where
  "build_record_dec_patterns fieldTypes userNames userDecPats =
    (let userMap = zip userNames userDecPats in
     map (\<lambda>(name, _). (name, lookup_or_wildcard userMap name)) fieldTypes)"

(* Look up the expected type for each user-supplied field.
   Precondition: every userFld is found in fieldTypes, so the map_of always returns Some. *)
definition user_field_types ::
  "(string \<times> CoreType) list \<Rightarrow> (string \<times> BabPattern) list \<Rightarrow> CoreType list" where
  "user_field_types fieldTypes userFlds =
    map (\<lambda>(name, _). case map_of fieldTypes name of
                       Some t \<Rightarrow> t | None \<Rightarrow> CoreTy_Var 0)
        userFlds"

(* Collect names appearing in the user's pattern that are NOT fields of
   the expected record type. *)
definition unknown_field_names ::
  "(string \<times> CoreType) list \<Rightarrow> (string \<times> BabPattern) list \<Rightarrow> string list" where
  "unknown_field_names fieldTypes userFlds =
    filter (\<lambda>n. map_of fieldTypes n = None) (map fst userFlds)"

(* Default type if the scrutinee is still a metavariable type, and is being
   matched against an integer literal pattern. *)
definition int_literal_default_type :: CoreType where
  "int_literal_default_type = CoreTy_FiniteInt Signed IntBits_32"

(* Resolve a constructor name appearing in a pattern: look it up in
   TE_DataCtors, check the ghost-context rule, and look up its arity in
   EE_DataCtorArity. Returns (datatype name, type vars, payload type, arity). *)
definition resolve_pattern_ctor ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string
   \<Rightarrow> TypeError list + (string \<times> nat list \<times> CoreType \<times> nat)" where
  "resolve_pattern_ctor env elabEnv ghost loc ctorName =
    (case fmlookup (TE_DataCtors env) ctorName of
       None \<Rightarrow> Inl [TyErr_InternalError_NameNotFound loc ctorName]
     | Some (dtName, tyvars, payloadTy) \<Rightarrow>
         if ghost = NotGhost \<and> dtName |\<in>| TE_GhostDatatypes env then
           Inl [TyErr_GhostVariableInNonGhost loc ctorName]
         else
           (case fmlookup (EE_DataCtorArity elabEnv) ctorName of
              None \<Rightarrow> Inl [TyErr_InternalError_NameNotFound loc ctorName]
            | Some arity \<Rightarrow> Inr (dtName, tyvars, payloadTy, arity)))"

(* Check that the user-supplied payload (Some/None) matches the
   constructor's arity (0 or non-zero). Returns the inner pattern when
   one is required (and provided), or None for nullary constructors. *)
fun check_payload_arity ::
  "Location \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> BabPattern option
   \<Rightarrow> TypeError list + BabPattern option" where
  "check_payload_arity loc cn 0 None = Inr None"
| "check_payload_arity loc cn 0 (Some _) = Inl [TyErr_WrongNumberOfArgs loc cn 0 1]"
| "check_payload_arity loc cn (Suc n) None = Inl [TyErr_WrongNumberOfArgs loc cn (Suc n) 0]"
| "check_payload_arity loc cn (Suc n) (Some inner) = Inr (Some inner)"

(* If check_payload_arity returns Inr (Some p), then the payload it
   returned is exactly the original optPayload's inner pattern. Used
   in the termination proof. *)
lemma check_payload_arity_Inr_Some:
  "check_payload_arity loc cn arity optPayload = Inr (Some p) \<Longrightarrow> optPayload = Some p"
  by (induction loc cn arity optPayload rule: check_payload_arity.induct) auto


section \<open>The decorator\<close>

(* Convert a BabPattern to a DecPattern, given the type of the scrutinee.
   Requires: CoreTyEnv, ElabEnv (for data ctor arities), ghost flag, the pattern,
   the scrutinee type it's matching against, substitution, and metavariable counter.
   Returns: Either an error; or decorated pattern, new subst, and new counter.  *)
function (sequential)
  decorate_pattern ::
    "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabPattern \<Rightarrow> CoreType
     \<Rightarrow> TypeSubst \<Rightarrow> nat
     \<Rightarrow> TypeError list + (DecPattern \<times> TypeSubst \<times> nat)"
and decorate_pattern_list ::
    "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabPattern list \<Rightarrow> CoreType list
     \<Rightarrow> TypeSubst \<Rightarrow> nat
     \<Rightarrow> TypeError list + (DecPattern list \<times> TypeSubst \<times> nat)" where

  (* Variable: matches anything; becomes a DP_Var of the (substituted) scrutinee type. *)
  "decorate_pattern env elabEnv ghost (BabPat_Var loc vr name) scrutTy accSubst next_mv =
    Inr (DP_Var vr name (apply_subst accSubst scrutTy), accSubst, next_mv)"

  (* Wildcard: matches anything; becomes DP_Wildcard. *)
| "decorate_pattern env elabEnv ghost (BabPat_Wildcard loc) scrutTy accSubst next_mv =
    Inr (DP_Wildcard, accSubst, next_mv)"

  (* Bool literal: scrutTy must match CoreTy_Bool. *)
| "decorate_pattern env elabEnv ghost (BabPat_Bool loc b) scrutTy accSubst next_mv =
    (case try_unify_compose env CoreTy_Bool scrutTy accSubst of
       Some s \<Rightarrow> Inr (DP_Bool b, s, next_mv)
     | None \<Rightarrow> Inl [TyErr_TypeMismatch loc CoreTy_Bool (apply_subst accSubst scrutTy)])"

  (* Int literal: if scrutTy is FiniteInt or MathInt, accept it immediately; otherwise,
     try to unify with i32 (will succeed only if it is an unbound metavariable). *)
| "decorate_pattern env elabEnv ghost (BabPat_Int loc i) scrutTy accSubst next_mv =
    (let e = apply_subst accSubst scrutTy in
     case e of
       CoreTy_FiniteInt _ _ \<Rightarrow> Inr (DP_Int i, accSubst, next_mv)
     | CoreTy_MathInt \<Rightarrow> Inr (DP_Int i, accSubst, next_mv)
     | _ \<Rightarrow>
       (case try_unify_compose env int_literal_default_type scrutTy accSubst of
          Some s \<Rightarrow> Inr (DP_Int i, s, next_mv)
        | None \<Rightarrow> Inl [TyErr_IntegerTypeRequired loc e]))"

  (* Tuple: desugars to a record pattern with synthetic field names.
     This builds an expected record type with fresh metavars for the field types,
     unifies, then recurses. *)
| "decorate_pattern env elabEnv ghost (BabPat_Tuple loc pats) scrutTy accSubst next_mv =
    (let n = length pats;
         names = tuple_field_names n;
         freshFieldTys = map CoreTy_Var [next_mv ..< next_mv + n];
         next_mv' = next_mv + n;
         recTy = CoreTy_Record (zip names freshFieldTys)
     in case try_unify_compose env recTy scrutTy accSubst of
          None \<Rightarrow> Inl [TyErr_TypeMismatch loc recTy (apply_subst accSubst scrutTy)]
        | Some s \<Rightarrow>
            (case decorate_pattern_list env elabEnv ghost pats freshFieldTys s next_mv' of
               Inl errs \<Rightarrow> Inl errs
             | Inr (decPats, s', mv') \<Rightarrow> Inr (DP_Record (zip names decPats), s', mv')))"

  (* Record: like tuple. The scrutinee must be a record type, the pattern's field names
     must be a subset of those in the record, and the pattern must not have duplicate
     field names.
     Unlike the tuple case, we don't try to unify the scrutinee type against an expected record
     type - instead, we just report an error if the scrutinee type is an unresolved metavar
     (or isn't a record). *)
| "decorate_pattern env elabEnv ghost (BabPat_Record loc userFlds) scrutTy accSubst next_mv =
    (case first_duplicate_name fst userFlds of
       Some dupName \<Rightarrow> Inl [TyErr_DuplicateFieldName loc dupName]
     | None \<Rightarrow>
         (let e = apply_subst accSubst scrutTy in
          case e of
            CoreTy_Record fieldTypes \<Rightarrow>
              (case unknown_field_names fieldTypes userFlds of
                 (badName # _) \<Rightarrow> Inl [TyErr_FieldNotFound loc badName e]
               | [] \<Rightarrow>
                   (case decorate_pattern_list env elabEnv ghost
                           (map snd userFlds)
                           (user_field_types fieldTypes userFlds) accSubst next_mv of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr (decPats, s, mv) \<Rightarrow>
                        Inr (DP_Record
                              (build_record_dec_patterns fieldTypes
                                 (map fst userFlds) decPats),
                             s, mv)))
          | _ \<Rightarrow> Inl [TyErr_NotARecordType loc e]))"

  (* Variant: resolve the constructor, unify scrutTy with
     CoreTy_Datatype dtName [fresh metas], check arity vs payload, and
     recurse on the payload (if any). *)
| "decorate_pattern env elabEnv ghost (BabPat_Variant loc ctorName optPayload) scrutTy accSubst next_mv =
    (case resolve_pattern_ctor env elabEnv ghost loc ctorName of
       Inl errs \<Rightarrow> Inl errs
     | Inr (dtName, tyvars, payloadTy, arity) \<Rightarrow>
         let freshTyArgs = map CoreTy_Var [next_mv ..< next_mv + length tyvars];
             next_mv' = next_mv + length tyvars;
             dtTy = CoreTy_Datatype dtName freshTyArgs
         in (case try_unify_compose env dtTy scrutTy accSubst of
              None \<Rightarrow> Inl [TyErr_TypeMismatch loc dtTy (apply_subst accSubst scrutTy)]
            | Some s \<Rightarrow>
                (case check_payload_arity loc ctorName arity optPayload of
                   Inl errs \<Rightarrow> Inl errs
                 | Inr None \<Rightarrow> Inr (DP_Variant ctorName None, s, next_mv')
                 | Inr (Some inner) \<Rightarrow>
                     let tyvarSubst = fmap_of_list (zip tyvars freshTyArgs);
                         instPayloadTy = apply_subst tyvarSubst payloadTy
                     in (case decorate_pattern env elabEnv ghost
                                inner instPayloadTy s next_mv' of
                          Inl errs \<Rightarrow> Inl errs
                        | Inr (dp, s', mv') \<Rightarrow>
                            Inr (DP_Variant ctorName (Some dp), s', mv')))))"

| "decorate_pattern_list env elabEnv ghost [] _ accSubst next_mv =
    Inr ([], accSubst, next_mv)"

| "decorate_pattern_list env elabEnv ghost (p # ps) tys accSubst next_mv =
    (let t = (case tys of [] \<Rightarrow> CoreTy_Var 0 | t # _ \<Rightarrow> t);
         tsRest = (case tys of [] \<Rightarrow> [] | _ # tsRest \<Rightarrow> tsRest) in
     case decorate_pattern env elabEnv ghost p t accSubst next_mv of
       Inl errs1 \<Rightarrow>
         \<comment> \<open>Continue processing the rest to collect more errors\<close>
         (case decorate_pattern_list env elabEnv ghost ps tsRest accSubst next_mv of
            Inl errs2 \<Rightarrow> Inl (errs1 @ errs2)
          | Inr _ \<Rightarrow> Inl errs1)
     | Inr (dp, s, mv) \<Rightarrow>
         (case decorate_pattern_list env elabEnv ghost ps tsRest s mv of
            Inl errs \<Rightarrow> Inl errs
          | Inr (dps, s', mv') \<Rightarrow> Inr (dp # dps, s', mv')))"

  by pat_completeness auto

(* Termination: strict decrease in BabPattern size. Same measure as
   before the substitution+next_mv extension. *)
termination decorate_pattern_list
  by (relation
        "measure (\<lambda>x. case x of
            Inl (_, _, _, p, _, _, _) \<Rightarrow> 2 * bab_pattern_size p
          | Inr (_, _, _, ps, _, _, _) \<Rightarrow> 2 * sum_list (map bab_pattern_size ps) + 1)")
     (auto simp: bab_pattern_size_pos dest: check_payload_arity_Inr_Some)

end

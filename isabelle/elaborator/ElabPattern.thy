theory ElabPattern
  imports ElabType
    "../bab/BabSyntax" "../core/TypeSubst"
begin

(* Pattern match elaborator, split into several steps:
    - decorate_match_arms, to lower patterns to a more Core-like form
    - dec_to_core_pat, to create the CorePatterns
    - wrap_lets, to add Lets for pattern-bound variables
*)


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


section \<open>Bound-variable extraction\<close>

(* Variables introduced by a decorated pattern, in left-to-right order. *)
fun dec_pattern_var_bindings ::
  "DecPattern \<Rightarrow> (VarOrRef \<times> string \<times> CoreType) list"
and dec_pattern_var_bindings_list ::
  "DecPattern list \<Rightarrow> (VarOrRef \<times> string \<times> CoreType) list"
where
  "dec_pattern_var_bindings (DP_Var vr x ty) = [(vr, x, ty)]"
| "dec_pattern_var_bindings (DP_Bool _) = []"
| "dec_pattern_var_bindings (DP_Int _) = []"
| "dec_pattern_var_bindings DP_Wildcard = []"
| "dec_pattern_var_bindings (DP_Variant _ None) = []"
| "dec_pattern_var_bindings (DP_Variant _ (Some inner)) = dec_pattern_var_bindings inner"
| "dec_pattern_var_bindings (DP_Record flds) = dec_pattern_var_bindings_list (map snd flds)"
| "dec_pattern_var_bindings_list [] = []"
| "dec_pattern_var_bindings_list (p # ps) =
     dec_pattern_var_bindings p @ dec_pattern_var_bindings_list ps"

(* Same, but returns only the names, and in an fset instead of a list. *)
(* TODO: perhaps this duplication could be cleaned up somehow. *)
fun dec_pattern_var_names :: "DecPattern \<Rightarrow> string fset"
and dec_pattern_var_names_list :: "DecPattern list \<Rightarrow> string fset"
where
  "dec_pattern_var_names (DP_Var _ name _) = {|name|}"
| "dec_pattern_var_names (DP_Bool _) = {||}"
| "dec_pattern_var_names (DP_Int _) = {||}"
| "dec_pattern_var_names DP_Wildcard = {||}"
| "dec_pattern_var_names (DP_Variant _ None) = {||}"
| "dec_pattern_var_names (DP_Variant _ (Some inner)) = dec_pattern_var_names inner"
| "dec_pattern_var_names (DP_Record flds) = dec_pattern_var_names_list (map snd flds)"
| "dec_pattern_var_names_list [] = {||}"
| "dec_pattern_var_names_list (p # ps) =
     dec_pattern_var_names p |\<union>| dec_pattern_var_names_list ps"


section \<open>Helpers for the decorator\<close>

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
                       Some t \<Rightarrow> t | None \<Rightarrow> CoreTy_Var '''')
        userFlds"

(* Collect names appearing in the user's pattern that are NOT fields of
   the expected record type. *)
definition unknown_field_names ::
  "(string \<times> CoreType) list \<Rightarrow> (string \<times> BabPattern) list \<Rightarrow> string list" where
  "unknown_field_names fieldTypes userFlds =
    filter (\<lambda>n. map_of fieldTypes n = None) (map fst userFlds)"

(* The error to report when the scrutinee type does not have the shape that a
   pattern requires. Patterns are checked against the scrutinee type and never
   contribute to type inference, so if the scrutinee type is still an unresolved
   metavariable (a type variable not in TE_TypeVars env) the error is "unable to
   infer type"; otherwise it is the given shape-specific error. *)
definition pattern_shape_error ::
  "CoreTyEnv \<Rightarrow> Location \<Rightarrow> CoreType \<Rightarrow> TypeError \<Rightarrow> TypeError list" where
  "pattern_shape_error env loc scrutTy err =
    (case scrutTy of
       CoreTy_Var n \<Rightarrow>
         if n |\<notin>| TE_TypeVars env then [TyErr_CannotInferType loc] else [err]
     | _ \<Rightarrow> [err])"

(* Resolve a constructor name appearing in a pattern: look it up in
   TE_DataCtors and check the ghost-context rule. Returns (datatype name,
   type vars, payload type, isNullary), where isNullary records whether the
   constructor was declared without a payload (EE_NullaryDataCtors). *)
definition resolve_pattern_ctor ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string
   \<Rightarrow> TypeError list + (string \<times> string list \<times> CoreType \<times> bool)" where
  "resolve_pattern_ctor env elabEnv ghost loc ctorName =
    (case fmlookup (TE_DataCtors env) ctorName of
       None \<Rightarrow> Inl [TyErr_NameNotFound loc ctorName]
     | Some (dtName, tyvars, payloadTy) \<Rightarrow>
         if ghost = NotGhost \<and> dtName |\<in>| TE_GhostDatatypes env then
           Inl [TyErr_GhostVariableInNonGhost loc ctorName]
         else
           Inr (dtName, tyvars, payloadTy, ctorName |\<in>| EE_NullaryDataCtors elabEnv))"

(* Check that the user-supplied payload (Some/None) matches the
   constructor's declaration (payload-less or not). Returns the inner
   pattern when one is required (and provided), or None for payload-less
   constructors. *)
fun check_payload_presence ::
  "Location \<Rightarrow> string \<Rightarrow> bool \<Rightarrow> BabPattern option
   \<Rightarrow> TypeError list + BabPattern option" where
  "check_payload_presence loc cn True None = Inr None"
| "check_payload_presence loc cn True (Some _) = Inl [TyErr_WrongNumberOfArgs loc cn 0 1]"
| "check_payload_presence loc cn False None = Inl [TyErr_WrongNumberOfArgs loc cn 1 0]"
| "check_payload_presence loc cn False (Some inner) = Inr (Some inner)"

(* If check_payload_presence returns Inr (Some p), then the payload it
   returned is exactly the original optPayload's inner pattern. Used
   in the termination proof. *)
lemma check_payload_presence_Inr_Some:
  "check_payload_presence loc cn isNullary optPayload = Inr (Some p) \<Longrightarrow> optPayload = Some p"
  by (cases isNullary; cases optPayload) auto


section \<open>The decorator\<close>

(* Convert a BabPattern to a DecPattern, given the type of the scrutinee.

   The pattern is checked against the scrutinee type; it never refines it. A
   variable or wildcard pattern accepts any type. Every other pattern requires
   the scrutinee type to already have the matching shape, and reads the types
   of its sub-patterns (record fields, the instantiated constructor payload)
   off the scrutinee type. *)
function (sequential)
  decorate_pattern ::
    "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabPattern \<Rightarrow> CoreType
     \<Rightarrow> TypeError list + DecPattern"
and decorate_pattern_list ::
    "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> BabPattern list \<Rightarrow> CoreType list
     \<Rightarrow> TypeError list + DecPattern list" where

  (* Variable: matches anything; becomes a DP_Var of the scrutinee type. The type
     bound to the variable must contain no unresolved metavariables (mirroring
     BabTm_Let's similar restriction). *)
  "decorate_pattern env elabEnv ghost (BabPat_Var loc vr name) scrutTy =
    (if list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list scrutTy)
     then Inr (DP_Var vr name scrutTy)
     else Inl [TyErr_CannotInferType loc])"

  (* Wildcard: matches anything; becomes DP_Wildcard. *)
| "decorate_pattern env elabEnv ghost (BabPat_Wildcard loc) scrutTy =
    Inr DP_Wildcard"

  (* Bool literal: the scrutinee must have type bool. *)
| "decorate_pattern env elabEnv ghost (BabPat_Bool loc b) scrutTy =
    (if scrutTy = CoreTy_Bool then Inr (DP_Bool b)
     else Inl (pattern_shape_error env loc scrutTy
                 (TyErr_TypeMismatch loc CoreTy_Bool scrutTy)))"

  (* Int literal: the scrutinee must have a finite integer type, and the literal
     must be in range of that type (matching an int literal against a MathInt
     scrutinee is rejected for now; only wildcard/variable patterns can match a
     MathInt). *)
| "decorate_pattern env elabEnv ghost (BabPat_Int loc i) scrutTy =
    (case scrutTy of
       CoreTy_FiniteInt sign bits \<Rightarrow>
         (if int_in_range (int_range sign bits) i
          then Inr (DP_Int i)
          else Inl [TyErr_IntPatternOutOfRange loc scrutTy])
     | _ \<Rightarrow> Inl (pattern_shape_error env loc scrutTy
                   (TyErr_FiniteIntegerTypeRequired loc scrutTy)))"

  (* Tuple: desugars to a record pattern with synthetic field names. The
     scrutinee must be a tuple type (a record with the synthetic field names)
     with the same number of components as the pattern. *)
| "decorate_pattern env elabEnv ghost (BabPat_Tuple loc pats) scrutTy =
    (case scrutTy of
       CoreTy_Record fieldTypes \<Rightarrow>
         (if map fst fieldTypes = tuple_field_names (length pats) then
            (case decorate_pattern_list env elabEnv ghost pats (map snd fieldTypes) of
               Inl errs \<Rightarrow> Inl errs
             | Inr decPats \<Rightarrow> Inr (DP_Record (zip (map fst fieldTypes) decPats)))
          else Inl [TyErr_TuplePatternMismatch loc (length pats) scrutTy])
     | _ \<Rightarrow> Inl (pattern_shape_error env loc scrutTy
                   (TyErr_TuplePatternMismatch loc (length pats) scrutTy)))"

  (* Record: the scrutinee must be a record type, the pattern's field names
     must be a subset of those in the record, and the pattern must not have
     duplicate field names. *)
| "decorate_pattern env elabEnv ghost (BabPat_Record loc userFlds) scrutTy =
    (case first_duplicate_name fst userFlds of
       Some dupName \<Rightarrow> Inl [TyErr_DuplicateFieldName loc dupName]
     | None \<Rightarrow>
         (case scrutTy of
            CoreTy_Record fieldTypes \<Rightarrow>
              (case unknown_field_names fieldTypes userFlds of
                 (badName # _) \<Rightarrow> Inl [TyErr_FieldNotFound loc badName scrutTy]
               | [] \<Rightarrow>
                   (case decorate_pattern_list env elabEnv ghost
                           (map snd userFlds)
                           (user_field_types fieldTypes userFlds) of
                      Inl errs \<Rightarrow> Inl errs
                    | Inr decPats \<Rightarrow>
                        Inr (DP_Record
                              (build_record_dec_patterns fieldTypes
                                 (map fst userFlds) decPats))))
          | _ \<Rightarrow> Inl (pattern_shape_error env loc scrutTy
                        (TyErr_NotARecordType loc scrutTy))))"

  (* Variant: resolve the constructor; the scrutinee must be an instance of the
     constructor's datatype. Check payload presence, and recurse on the payload
     (if any) at the payload type instantiated with the scrutinee's type
     arguments. (In a mismatch error, the expected type is shown as the datatype
     applied to its own type parameters.) *)
| "decorate_pattern env elabEnv ghost (BabPat_Variant loc ctorName optPayload) scrutTy =
    (case resolve_pattern_ctor env elabEnv ghost loc ctorName of
       Inl errs \<Rightarrow> Inl errs
     | Inr (dtName, tyvars, payloadTy, isNullary) \<Rightarrow>
         (case scrutTy of
            CoreTy_Datatype scrutDtName tyArgs \<Rightarrow>
              (if scrutDtName = dtName \<and> length tyArgs = length tyvars then
                 (case check_payload_presence loc ctorName isNullary optPayload of
                    Inl errs \<Rightarrow> Inl errs
                  | Inr None \<Rightarrow> Inr (DP_Variant ctorName None)
                  | Inr (Some inner) \<Rightarrow>
                      let instPayloadTy =
                            apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy
                      in (case decorate_pattern env elabEnv ghost inner instPayloadTy of
                            Inl errs \<Rightarrow> Inl errs
                          | Inr dp \<Rightarrow> Inr (DP_Variant ctorName (Some dp))))
               else Inl [TyErr_TypeMismatch loc
                           (CoreTy_Datatype dtName (map CoreTy_Var tyvars)) scrutTy])
          | _ \<Rightarrow> Inl (pattern_shape_error env loc scrutTy
                        (TyErr_TypeMismatch loc
                           (CoreTy_Datatype dtName (map CoreTy_Var tyvars)) scrutTy))))"

| "decorate_pattern_list env elabEnv ghost [] _ = Inr []"

| "decorate_pattern_list env elabEnv ghost (p # ps) tys =
    (let t = (case tys of [] \<Rightarrow> CoreTy_Var '''' | t # _ \<Rightarrow> t);
         tsRest = (case tys of [] \<Rightarrow> [] | _ # tsRest \<Rightarrow> tsRest) in
     case decorate_pattern env elabEnv ghost p t of
       Inl errs1 \<Rightarrow>
         \<comment> \<open>Continue processing the rest to collect more errors\<close>
         (case decorate_pattern_list env elabEnv ghost ps tsRest of
            Inl errs2 \<Rightarrow> Inl (errs1 @ errs2)
          | Inr _ \<Rightarrow> Inl errs1)
     | Inr dp \<Rightarrow>
         (case decorate_pattern_list env elabEnv ghost ps tsRest of
            Inl errs \<Rightarrow> Inl errs
          | Inr dps \<Rightarrow> Inr (dp # dps)))"

  by pat_completeness auto

(* Termination: strict decrease in BabPattern size. *)
termination decorate_pattern_list
  by (relation
        "measure (\<lambda>x. case x of
            Inl (_, _, _, p, _) \<Rightarrow> 2 * bab_pattern_size p
          | Inr (_, _, _, ps, _) \<Rightarrow> 2 * sum_list (map bab_pattern_size ps) + 1)")
     (auto simp: bab_pattern_size_pos dest: check_payload_presence_Inr_Some)


section \<open>Pattern-list env extension\<close>

(* Env extension corresponding to a single (vr, name, type) binding,
   mirroring exactly the env extension that CoreTm_Let /
   CoreStmt_VarDecl(Var) / CoreStmt_VarDecl(Ref) perform. Ghost arms put
   the variable in TE_GhostLocals. Whether the variable is read-only
   (lands in TE_ConstLocals) depends on the match context, so it is
   supplied by the caller as a function of the binding's VarOrRef marker:
     - term-context matches: every binding is const (Let semantics),
       so constOf = (\<lambda>_. True);
     - statement-context matches: Var bindings are mutable copies, and
       Ref bindings are writable iff the scrutinee lvalue is writable,
       so constOf = (\<lambda>vr. vr = Ref \<and> \<not> scrutinee-writable). *)
definition extend_env_one_var ::
  "(VarOrRef \<Rightarrow> bool) \<Rightarrow> GhostOrNot \<Rightarrow> (VarOrRef \<times> string \<times> CoreType)
   \<Rightarrow> CoreTyEnv \<Rightarrow> CoreTyEnv" where
  "extend_env_one_var constOf ghost binding env =
    (case binding of (vr, name, ty) \<Rightarrow>
      env \<lparr> TE_LocalVars := fmupd name ty (TE_LocalVars env),
            TE_GhostLocals := (if ghost = Ghost
                               then finsert name (TE_GhostLocals env)
                               else fminus (TE_GhostLocals env) {|name|}),
            TE_ConstLocals := (if constOf vr
                               then finsert name (TE_ConstLocals env)
                               else fminus (TE_ConstLocals env) {|name|}) \<rparr>)"

(* Extend env by every (vr, name, type) DP_Var binding in a pattern list. *)
definition extend_env_with_pattern_vars ::
  "CoreTyEnv \<Rightarrow> (VarOrRef \<Rightarrow> bool) \<Rightarrow> GhostOrNot \<Rightarrow> DecPattern list \<Rightarrow> CoreTyEnv" where
  "extend_env_with_pattern_vars env constOf ghost ps =
     foldr (extend_env_one_var constOf ghost)
           (dec_pattern_var_bindings_list ps) env"


section \<open>decorate_match_arms: Calls the decorator and runs some extra checks\<close>

(* A pattern is illegal if it binds the same name twice (e.g. {x, x}). *)
definition check_pattern_no_duplicates ::
  "Location \<Rightarrow> DecPattern \<Rightarrow> TypeError list + unit" where
  "check_pattern_no_duplicates loc dp =
    (case first_duplicate_name (\<lambda>(_, name, _). name) (dec_pattern_var_bindings dp) of
       Some dupName \<Rightarrow> Inl [TyErr_DuplicateVarInPattern loc dupName]
     | None \<Rightarrow> Inr ())"

(* Check a single match-arm pattern. Duplicate variables are always illegal
   (check_pattern_no_duplicates). `ref` patterns are rejected unless allowRefs
   is set: term-context matches (BabTm_Match) forbid them (a ref makes no
   sense in a term), while statement-context matches (BabStmt_Match) permit
   them (provided the scrutinee is an lvalue, which the caller checks
   separately). *)
definition check_match_pattern ::
  "bool \<Rightarrow> Location \<Rightarrow> DecPattern \<Rightarrow> TypeError list + unit" where
  "check_match_pattern allowRefs loc dp =
    (case check_pattern_no_duplicates loc dp of
       Inl errs \<Rightarrow> Inl errs
     | Inr _ \<Rightarrow>
        if allowRefs then Inr ()
        else (case filter (\<lambda>(vr, _, _). vr = Ref) (dec_pattern_var_bindings dp) of
                [] \<Rightarrow> Inr ()
              | (_, name, _) # _ \<Rightarrow> Inl [TyErr_RefPatternInTermContext loc name]))"

(* Walk a list of (BabPattern, body) arms (as produced by the parser for
   BabTm_Match or BabStmt_Match), decorating each pattern against the
   scrutinee type and checking it with check_match_pattern. The returned
   list pairs each arm's decorated pattern with the original body
   unchanged.

   The allowRefs flag is passed through to check_match_pattern: term-context
   matches pass False (ref patterns illegal), statement-context matches pass
   True. *)
fun decorate_match_arms ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot
   \<Rightarrow> CoreType                                     \<comment> \<open>scrutinee type\<close>
   \<Rightarrow> bool                                         \<comment> \<open>allow ref patterns?\<close>
   \<Rightarrow> (BabPattern \<times> 'body) list
   \<Rightarrow> TypeError list + (DecPattern \<times> 'body) list"
where
  "decorate_match_arms env elabEnv ghost scrutTy allowRefs [] = Inr []"

| "decorate_match_arms env elabEnv ghost scrutTy allowRefs ((pat, body) # rest) =
    (case decorate_pattern env elabEnv ghost pat scrutTy of
       Inl errs \<Rightarrow> Inl errs
     | Inr dp \<Rightarrow>
        (case check_match_pattern allowRefs (bab_pattern_location pat) dp of
           Inl errs \<Rightarrow> Inl errs
         | Inr _ \<Rightarrow>
            (case decorate_match_arms env elabEnv ghost scrutTy allowRefs rest of
               Inl errs \<Rightarrow> Inl errs
             | Inr restRows \<Rightarrow> Inr ((dp, body) # restRows))))"


section \<open>Translation to Core patterns and binders\<close>

(* Strip variable binders (replaced with wildcards); preserve structure
   otherwise. Variant payload is unconditional in CorePattern, so a
   no-payload surface variant becomes a Variant with a Wildcard payload. *)
fun dec_to_core_pat :: "DecPattern \<Rightarrow> CorePattern" where
  "dec_to_core_pat (DP_Var _ _ _) = CorePat_Wildcard"
| "dec_to_core_pat DP_Wildcard = CorePat_Wildcard"
| "dec_to_core_pat (DP_Bool b) = CorePat_Bool b"
| "dec_to_core_pat (DP_Int i) = CorePat_Int i"
| "dec_to_core_pat (DP_Variant cn None) = CorePat_Variant cn CorePat_Wildcard"
| "dec_to_core_pat (DP_Variant cn (Some p)) = CorePat_Variant cn (dec_to_core_pat p)"
| "dec_to_core_pat (DP_Record flds) =
     CorePat_Record (map (\<lambda>(n, p). (n, dec_to_core_pat p)) flds)"

(* `dec_pattern_projections base dp` pairs every (vr, name, type) DP_Var
   binding in `dp` with the projection of `base` reaching that variable's
   position in the pattern. Bindings are listed in pattern-traversal
   (left-to-right) order, matching dec_pattern_var_bindings exactly.

   The elaborator passes `CoreTm_Var freshName` as `base`, where freshName
   binds the matched scrutinee. The generalised form (taking an arbitrary
   base term) simplifies the structural-induction typing proof. *)
fun dec_pattern_projections ::
  "CoreTerm \<Rightarrow> DecPattern \<Rightarrow> (VarOrRef \<times> string \<times> CoreType \<times> CoreTerm) list"
and dec_pattern_projections_record ::
  "CoreTerm \<Rightarrow> (string \<times> DecPattern) list
   \<Rightarrow> (VarOrRef \<times> string \<times> CoreType \<times> CoreTerm) list"
where
  "dec_pattern_projections base (DP_Var vr name ty) = [(vr, name, ty, base)]"
| "dec_pattern_projections base DP_Wildcard = []"
| "dec_pattern_projections base (DP_Bool _) = []"
| "dec_pattern_projections base (DP_Int _) = []"
| "dec_pattern_projections base (DP_Variant _ None) = []"
| "dec_pattern_projections base (DP_Variant cn (Some inner)) =
     dec_pattern_projections (CoreTm_VariantProj base cn) inner"
| "dec_pattern_projections base (DP_Record flds) =
     dec_pattern_projections_record base flds"
| "dec_pattern_projections_record base [] = []"
| "dec_pattern_projections_record base ((fn, p) # rest) =
     dec_pattern_projections (CoreTm_RecordProj base fn) p
       @ dec_pattern_projections_record base rest"

(* Wrap a body term in CoreTm_Lets, one per surface-pattern variable in dp,
   each binding the variable to the corresponding projection of
   `CoreTm_Var scrutVar`. Binders are emitted in pattern-traversal order
   with the first binder outermost. *)
definition wrap_lets ::
  "string \<Rightarrow> DecPattern \<Rightarrow> CoreTerm \<Rightarrow> CoreTerm" where
  "wrap_lets scrutVar dp body =
     foldr (\<lambda>(_, name, _, proj). CoreTm_Let name proj)
           (dec_pattern_projections (CoreTm_Var scrutVar) dp) body"

(* Statement analogue of wrap_lets: one CoreStmt_VarDecl per surface-pattern
   variable in dp, each binding the variable (Var = copy, Ref = alias into
   the scrutinee) to the corresponding projection of `CoreTm_Var scrutVar`.
   These are emitted at the head of a match arm's statement list. *)
definition wrap_vardecls ::
  "GhostOrNot \<Rightarrow> string \<Rightarrow> DecPattern \<Rightarrow> CoreStatement list" where
  "wrap_vardecls ghost scrutVar dp =
     map (\<lambda>(vr, name, ty, proj). CoreStmt_VarDecl ghost name vr ty proj)
         (dec_pattern_projections (CoreTm_Var scrutVar) dp)"

end

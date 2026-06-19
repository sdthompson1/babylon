theory ElabPattern
  imports ElabType UnifyCompose
    "../bab/BabSyntax" "../core/TypeSubst"
begin

(* Pattern match elaborator, split into several steps:
    - decorate_match_arms, to lower patterns to a more Core-like form
    - finalize_match_arms, to apply substitutions and return updated envs
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

(* Default type if the scrutinee is still a metavariable type, and is being
   matched against an integer literal pattern. *)
definition int_literal_default_type :: CoreType where
  "int_literal_default_type = CoreTy_FiniteInt Signed IntBits_32"

(* Resolve a constructor name appearing in a pattern: look it up in
   TE_DataCtors, check the ghost-context rule, and look up its arity in
   EE_DataCtorArity. Returns (datatype name, type vars, payload type, arity). *)
definition resolve_pattern_ctor ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> string
   \<Rightarrow> TypeError list + (string \<times> string list \<times> CoreType \<times> nat)" where
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
         freshFieldTys = mv_block next_mv (next_mv + n);
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
         let freshTyArgs = mv_block next_mv (next_mv + length tyvars);
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
    (let t = (case tys of [] \<Rightarrow> CoreTy_Var '''' | t # _ \<Rightarrow> t);
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


section \<open>Substitution into a decorated pattern\<close>

(* Apply a TypeSubst to every CoreType embedded in a DecPattern (i.e.
   the type carried on each DP_Var). Used as a post-pass after all
   arms of a match have been decorated, to propagate type refinements
   discovered in later arms back to earlier-emitted DP_Var bindings. *)
fun apply_subst_to_dec_pattern :: "TypeSubst \<Rightarrow> DecPattern \<Rightarrow> DecPattern" where
  "apply_subst_to_dec_pattern subst (DP_Var vr name ty) =
    DP_Var vr name (apply_subst subst ty)"
| "apply_subst_to_dec_pattern subst (DP_Bool b) = DP_Bool b"
| "apply_subst_to_dec_pattern subst (DP_Int i) = DP_Int i"
| "apply_subst_to_dec_pattern subst DP_Wildcard = DP_Wildcard"
| "apply_subst_to_dec_pattern subst (DP_Record flds) =
    DP_Record (map (\<lambda>(name, p). (name, apply_subst_to_dec_pattern subst p)) flds)"
| "apply_subst_to_dec_pattern subst (DP_Variant cn None) = DP_Variant cn None"
| "apply_subst_to_dec_pattern subst (DP_Variant cn (Some inner)) =
    DP_Variant cn (Some (apply_subst_to_dec_pattern subst inner))"


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

(* Walk a list of (BabPattern, BabTerm) arms (as produced by the parser for
   BabTm_Match or BabStmt_Match), decorating each pattern against the
   scrutinee type and checking it with check_match_pattern. The returned
   list pairs each arm's decorated pattern with the original body term
   unchanged.

   The allowRefs flag is passed through to check_match_pattern: term-context
   matches pass False (ref patterns illegal), statement-context matches pass
   True. *)
fun decorate_match_arms ::
  "CoreTyEnv \<Rightarrow> ElabEnv \<Rightarrow> GhostOrNot
   \<Rightarrow> CoreType                                     \<comment> \<open>scrutinee type\<close>
   \<Rightarrow> bool                                         \<comment> \<open>allow ref patterns?\<close>
   \<Rightarrow> TypeSubst \<Rightarrow> nat
   \<Rightarrow> (BabPattern \<times> 'body) list
   \<Rightarrow> TypeError list + ((DecPattern \<times> 'body) list \<times> TypeSubst \<times> nat)"
where
  "decorate_match_arms env elabEnv ghost scrutTy allowRefs accSubst next_mv [] =
     Inr ([], accSubst, next_mv)"

| "decorate_match_arms env elabEnv ghost scrutTy allowRefs accSubst next_mv ((pat, body) # rest) =
    (case decorate_pattern env elabEnv ghost pat scrutTy accSubst next_mv of
       Inl errs \<Rightarrow> Inl errs
     | Inr (dp, accSubst1, next_mv1) \<Rightarrow>
        (case check_match_pattern allowRefs (bab_pattern_location pat) dp of
           Inl errs \<Rightarrow> Inl errs
         | Inr _ \<Rightarrow>
            (case decorate_match_arms env elabEnv ghost scrutTy allowRefs
                    accSubst1 next_mv1 rest of
               Inl errs \<Rightarrow> Inl errs
             | Inr (restRows, finalSubst, finalMv) \<Rightarrow>
                 Inr ((dp, body) # restRows, finalSubst, finalMv))))"


section \<open>Post-decoration passes\<close>

(* finalize_match_arms:  Given the DecPatterns produced by decorate_match_arms 
   and the final accSubst from that call:

   1. Apply accSubst to every DecPattern, resolving any metavariables that
      were unified later in the loop.
   2. Run an inference check: every variable bound by every (substituted)
      pattern must have a type with no free metavariables. (Free metas
      cannot be inferred from the match arms alone, mirroring BabTm_Let's
      similar restriction.) On failure, return TyErr_CannotInferType at the
      caller-supplied location.
   3. Return per-arm (substituted dp, env) pairs, where env is built by
      extending the outer env with the substituted dp's variable bindings
      (const-ness of each binding determined by constOf — see
      extend_env_one_var).

   Body-agnostic: the caller (BabTm_Match or BabStmt_Match) zips the
   resulting envs with the original body terms. Decoupling the bodies keeps
   termination of the elaborator straightforward, since the body list passed
   to elab_term_list_with_envs is syntactically derived from arms. *)
definition finalize_match_arms ::
  "CoreTyEnv \<Rightarrow> (VarOrRef \<Rightarrow> bool) \<Rightarrow> GhostOrNot \<Rightarrow> Location \<Rightarrow> TypeSubst
   \<Rightarrow> DecPattern list
   \<Rightarrow> TypeError list + (DecPattern \<times> CoreTyEnv) list" where
  "finalize_match_arms env constOf ghost loc accSubst dps =
    (let substDps = map (apply_subst_to_dec_pattern accSubst) dps
     in if list_ex (\<lambda>dp.
            list_ex (\<lambda>(_, _, vTy).
                       \<not> list_all (\<lambda>n. n |\<in>| TE_TypeVars env) (type_tyvars_list vTy))
                    (dec_pattern_var_bindings dp)) substDps
        then Inl [TyErr_CannotInferType loc]
        else Inr (map (\<lambda>dp. (dp, extend_env_with_pattern_vars env constOf ghost [dp])) substDps))"

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

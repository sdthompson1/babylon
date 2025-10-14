theory BabRenamer
  imports Main "HOL-Library.Char_ord" "HOL-Library.List_Lexorder" "HOL-Library.FSet" "HOL-Library.Finite_Map" Location BabSyntax
begin

(*-----------------------------------------------------------------------------*)
(* Renamer errors *)
(*-----------------------------------------------------------------------------*)

datatype RenameError =
  RenameError_NotInScopeTerm Location string    (* not in scope: 'x' *)
  | RenameError_NotInScopeType Location string  (* not in scope: type 'T' *)
  | RenameError_AmbiguousTerm Location string "string list"  (* name 'x' is ambiguous: could be <list> *)
  | RenameError_AmbiguousType Location string "string list"  (* type name 'T' is ambiguous: could be <list> *)
  | RenameError_ModuleNotFound Location string  (* module not found: 'M' *)
  | RenameError_DuplicateAlias Location string  (* multiple imports of module 'M' *)
  | RenameError_DuplicateDefinition Location string  (* variable 'x' is already defined in this scope *)
  | RenameError_ReturnVarOutsidePostcond Location  (* 'return' used as variable, outside postcondition *)
  | RenameError_ReturnVarVoidFunction Location  (* 'return' used as variable, in postcondition of void function *)


(*-----------------------------------------------------------------------------*)
(* Renamer internal data structures *)
(*-----------------------------------------------------------------------------*)

record GlobalName =
  GN_UnqualifiedName :: "string option"  (* e.g. "foo" *)
  GN_QualifiedName :: string   (* e.g. "Foo.foo" or "F.foo" *)
  GN_TrueName :: string   (* e.g. "mypackage:Foo.foo" *)

record RenameEnv =
  RE_LocalTypeNames :: "string fset"
  RE_LocalTermNames :: "string fset"
  RE_CurrentScopeTermNames :: "string fset"
  RE_GlobalTypeNames :: "(string, string list) fmap"
  RE_GlobalTermNames :: "(string, string list) fmap"
  RE_InPostcondition :: bool
  RE_CurrentFunctionReturnType :: "BabType option"


(*-----------------------------------------------------------------------------*)
(* String splitting helpers for dotted names *)
(*-----------------------------------------------------------------------------*)

(* Split at the last dot: "M.N.x" \<rightarrow> Some ("M.N", "x") *)
fun split_at_last_dot :: "string \<Rightarrow> (string \<times> string) option"
  where
"split_at_last_dot s =
  (let prefix = takeWhile (\<lambda>c. c \<noteq> CHR ''.'') (rev s);
       rest = dropWhile (\<lambda>c. c \<noteq> CHR ''.'') (rev s)
   in if rest = [] then None
      else Some (rev (tl rest), rev prefix))"

(* If split_at_last_dot returns Some then the prefix is shorter than the original string *)
lemma split_at_last_dot_shorter:
  assumes "split_at_last_dot s = Some (prefix, suffix)"
  shows "length prefix < length s"
proof -
  from assms have dropWhileNotEmpty: "dropWhile (\<lambda>c. c \<noteq> CHR ''.'') (rev s) \<noteq> []"
    by (auto split: if_splits)
  then obtain rest where rest_def: "dropWhile (\<lambda>c. c \<noteq> CHR ''.'') (rev s) = rest" "rest \<noteq> []"
    by auto
  have 1: "length rest \<le> length (rev s)"
    using rest_def length_dropWhile_le by blast
  have 2: "length (tl rest) < length rest"
    using rest_def(2) by auto
  have 3: "length (tl rest) < length (rev s)"
    using 1 2 by auto
  have 4: "prefix = rev (tl rest)"
    using dropWhileNotEmpty assms rest_def(1) by auto
  show ?thesis
    using "3" "4" by auto
qed

(* Generate all possible splits of a dotted name.
   Returns list of (base_name, [field1, field2, ...]) pairs.
   Example: "M.N.x" \<rightarrow> [("M.N.x", []), ("M.N", ["x"]), ("M", ["N", "x"])] *)
function all_dot_splits :: "string \<Rightarrow> (string \<times> string list) list"
  where
"all_dot_splits s =
  (case split_at_last_dot s of
    None \<Rightarrow> [(s, [])]
    | Some (prefix, suffix) \<Rightarrow>
        (s, []) # map (\<lambda>(base, fields). (base, fields @ [suffix])) (all_dot_splits prefix))"
  by pat_completeness auto
termination
  by (relation "measure length", auto simp: split_at_last_dot_shorter)

(* Strip a package prefix from a module name *)
fun strip_package_prefix :: "string \<Rightarrow> string" where
  "strip_package_prefix s = tl (dropWhile (\<lambda>c. c \<noteq> CHR '':'') s)"


(*-----------------------------------------------------------------------------*)
(* Helpers for finding duplicate names *)
(*-----------------------------------------------------------------------------*)

(* Helper function to find duplicates in a sorted list using a key function *)
fun find_duplicates_in_sorted :: "('a \<Rightarrow> 'k) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"find_duplicates_in_sorted keyFn [] = []"
| "find_duplicates_in_sorted keyFn [x] = []"
| "find_duplicates_in_sorted keyFn (x1 # x2 # rest) =
    (if keyFn x1 = keyFn x2 then
      x2 # find_duplicates_in_sorted keyFn (x2 # rest)
    else
      find_duplicates_in_sorted keyFn (x2 # rest))"

(* Function to check for duplicate alias names in imports, and also check for clashes
   between alias names and the current module name *)
fun check_duplicate_aliases :: "string \<Rightarrow> BabImport list \<Rightarrow> RenameError list"
  where
"check_duplicate_aliases currentModName imports =
  (let aliasLocPairs = map (\<lambda>imp. (Imp_AliasName imp, Imp_Location imp)) imports;
       sortedPairs = sort_key fst aliasLocPairs;
       duplicates = find_duplicates_in_sorted fst sortedPairs;
       duplicateErrs = map (\<lambda>(alias, loc). RenameError_DuplicateAlias loc alias) duplicates;
       currentModNameStripped = strip_package_prefix currentModName;
       clashErrs = map (\<lambda>imp. RenameError_DuplicateAlias (Imp_Location imp) (Imp_AliasName imp))
                       (filter (\<lambda>imp. Imp_AliasName imp = currentModNameStripped) imports)
   in duplicateErrs @ clashErrs)"

(* Function to extract defined type names from a BabDeclaration *)
fun get_type_names_from_decl :: "BabDeclaration \<Rightarrow> (string \<times> Location) list" where
  "get_type_names_from_decl decl =
   (if is_type_decl decl then
     [(get_decl_name decl, bab_declaration_location decl)]
   else [])"

(* Function to extract defined term names from a BabDeclaration *)
fun get_term_names_from_decl :: "BabDeclaration \<Rightarrow> (string \<times> Location) list" where
  "get_term_names_from_decl decl =
   (if is_type_decl decl then
     (case decl of
        BabDecl_Datatype d \<Rightarrow> map (\<lambda>(loc, c, _). (c, loc)) (DD_Ctors d)
      | _ \<Rightarrow> [])
   else
     [(get_decl_name decl, bab_declaration_location decl)])"

(* Function to check for duplicate definitions in interface or implementation *)
fun check_duplicate_decl_names :: "BabDeclaration list \<Rightarrow> RenameError list" where
"check_duplicate_decl_names decls =
  (let typeNameLocPairs = concat (map get_type_names_from_decl decls);
       sortedTypePairs = sort_key fst typeNameLocPairs;
       typeDuplicates = find_duplicates_in_sorted fst sortedTypePairs;
       typeErrors = map (\<lambda>(name, loc). RenameError_DuplicateDefinition loc name) typeDuplicates;

       termNameLocPairs = concat (map get_term_names_from_decl decls);
       sortedTermPairs = sort_key fst termNameLocPairs;
       termDuplicates = find_duplicates_in_sorted fst sortedTermPairs;
       termErrors = map (\<lambda>(name, loc). RenameError_DuplicateDefinition loc name) termDuplicates
   in typeErrors @ termErrors)"


(*-----------------------------------------------------------------------------*)
(* RenameEnv helpers *)
(*-----------------------------------------------------------------------------*)

(* Add local names *)
fun add_local_type_names :: "Location \<Rightarrow> string list \<Rightarrow> RenameEnv \<Rightarrow> RenameError list * RenameEnv"
  where "add_local_type_names loc names env =
    (let sorted = sort names;
         internalDups = find_duplicates_in_sorted id sorted;
         internalDupErrs = map (\<lambda>name. RenameError_DuplicateDefinition loc name) internalDups;
         newNames = fset_of_list names;
         newEnv = env \<lparr> RE_LocalTypeNames := newNames |\<union>| RE_LocalTypeNames env \<rparr>
     in (internalDupErrs, newEnv))"

(* Helper function to check for duplicates in a list and generate errors *)
fun check_duplicate_names :: "Location \<Rightarrow> string list \<Rightarrow> string fset \<Rightarrow> RenameError list"
  where "check_duplicate_names loc names currentScope =
    (let duplicates = filter (\<lambda>name. name |\<in>| currentScope) names
     in map (\<lambda>name. RenameError_DuplicateDefinition loc name) duplicates)"

fun add_local_term_names :: "Location \<Rightarrow> string list \<Rightarrow> RenameEnv \<Rightarrow> RenameError list * RenameEnv"
  where "add_local_term_names loc names env =
    (let sorted = sort names;
         internalDups = find_duplicates_in_sorted id sorted;
         internalDupErrs = map (\<lambda>name. RenameError_DuplicateDefinition loc name) internalDups;
         scopeDupErrs = check_duplicate_names loc names (RE_CurrentScopeTermNames env);
         allErrs = internalDupErrs @ scopeDupErrs;
         newNames = fset_of_list names;
         newEnv = env \<lparr> RE_LocalTermNames := newNames |\<union>| RE_LocalTermNames env,
                         RE_CurrentScopeTermNames := newNames |\<union>| RE_CurrentScopeTermNames env \<rparr>
     in (allErrs, newEnv))"

(* Open a new term scope - clears the current scope names *)
fun open_term_scope :: "RenameEnv \<Rightarrow> RenameEnv"
  where "open_term_scope env = env \<lparr> RE_CurrentScopeTermNames := {||} \<rparr>"

(* Helper to add a mapping to an fmap, prepending to existing list if key exists.
   Only adds trueName if it's not already in the list (prevents spurious ambiguity errors). *)
fun add_to_name_fmap :: "string \<Rightarrow> string \<Rightarrow> (string, string list) fmap \<Rightarrow> (string, string list) fmap"
  where "add_to_name_fmap key trueName fm =
    (case fmlookup fm key of
      None \<Rightarrow> fmupd key [trueName] fm
      | Some existingList \<Rightarrow>
          if List.member existingList trueName then
            fm
          else
            fmupd key (trueName # existingList) fm)"

(* Helper to insert a GlobalName into an fmap *)
fun insert_global_name_into_fmap :: "GlobalName \<Rightarrow> (string, string list) fmap \<Rightarrow> (string, string list) fmap"
  where "insert_global_name_into_fmap gn fm =
    (let trueName = GN_TrueName gn;
         fm1 = (case GN_UnqualifiedName gn of
                  None \<Rightarrow> fm
                  | Some unqual \<Rightarrow> add_to_name_fmap unqual trueName fm);
         fm2 = add_to_name_fmap (GN_QualifiedName gn) trueName fm1
     in fm2)"

(* Add global names *)
fun add_global_type_names :: "GlobalName list \<Rightarrow> RenameEnv \<Rightarrow> RenameEnv"
  where "add_global_type_names gns env =
    env \<lparr> RE_GlobalTypeNames := fold insert_global_name_into_fmap gns (RE_GlobalTypeNames env) \<rparr>"

fun add_global_term_names :: "GlobalName list \<Rightarrow> RenameEnv \<Rightarrow> RenameEnv"
  where "add_global_term_names gns env =
    env \<lparr> RE_GlobalTermNames := fold insert_global_name_into_fmap gns (RE_GlobalTermNames env) \<rparr>"

(* Empty renamer env *)
definition empty_renamer_env :: RenameEnv
  where "empty_renamer_env = \<lparr> RE_LocalTypeNames = {||},
                               RE_LocalTermNames = {||},
                               RE_CurrentScopeTermNames = {||},
                               RE_GlobalTypeNames = fmempty,
                               RE_GlobalTermNames = fmempty,
                               RE_InPostcondition = False,
                               RE_CurrentFunctionReturnType = None \<rparr>"

(* GlobalName construction function *)
fun make_global_name :: "string \<Rightarrow> string \<Rightarrow> bool \<Rightarrow> string \<Rightarrow> GlobalName"
  where
"make_global_name fullModName declName qualified aliasName =
  \<lparr> GN_UnqualifiedName = (if qualified then None else Some declName),
    GN_QualifiedName = aliasName @ ''.'' @ declName,
    GN_TrueName = fullModName @ ''.'' @ declName \<rparr>"

(* Add a new declaration to the environment *)
fun add_decl_to_env :: "string \<Rightarrow> string \<Rightarrow> bool \<Rightarrow> BabDeclaration \<Rightarrow> RenameEnv \<Rightarrow> RenameEnv"
  where
"add_decl_to_env fullModName aliasName qualified decl env =
  (let declName = get_decl_name decl;
       gn = make_global_name fullModName declName qualified aliasName;
       env1 = (if is_type_decl decl then
                add_global_type_names [gn] env
              else
                add_global_term_names [gn] env)
   in
   case decl of
     BabDecl_Datatype dd \<Rightarrow>
       let ctors = DD_Ctors dd;
           ctorGlobalNames = map (\<lambda>(loc, ctorName, optTy).
                                   make_global_name fullModName ctorName qualified aliasName) ctors
       in add_global_term_names ctorGlobalNames env1
     | _ \<Rightarrow> env1)"

(* Add declarations from the current module *)
fun add_current_module_decls :: "BabModule \<Rightarrow> BabDeclaration list \<Rightarrow> RenameEnv \<Rightarrow> RenameEnv"
  where
"add_current_module_decls currentMod decls env =
  (let modName = Mod_Name currentMod;
       aliasName = strip_package_prefix modName
   in fold (\<lambda>decl acc. add_decl_to_env modName aliasName False decl acc) decls env)"



(*-----------------------------------------------------------------------------*)
(* Import processing *)
(*-----------------------------------------------------------------------------*)

(* Convert a list of modules to an fmap keyed by module name *)
fun modules_to_fmap :: "BabModule list \<Rightarrow> (string, BabModule) fmap" where
  "modules_to_fmap mods = fold (\<lambda>m acc. fmupd (Mod_Name m) m acc) mods fmempty"

(* Import processing function *)
(* Note: Imp_ModuleName was resolved by the loader to a full module name (pkg-name:ModName),
   but the alias name doesn't have the package prefix (e.g. ModName) *)
fun process_import :: "BabImport \<Rightarrow> (string, BabModule) fmap \<Rightarrow> RenameEnv
                        \<Rightarrow> RenameError list * RenameEnv"
  where
"process_import imp allMods env =
  (let fullModName = Imp_ModuleName imp;
       aliasName = Imp_AliasName imp;
       qualified = Imp_Qualified imp;
       impLoc = Imp_Location imp
   in
   case fmlookup allMods fullModName of
     Some foundMod \<Rightarrow>
       let newEnv = fold (\<lambda>decl acc. add_decl_to_env fullModName aliasName qualified decl acc)
                         (Mod_Interface foundMod) env
       in ([], newEnv)
     | None \<Rightarrow>
         ([RenameError_ModuleNotFound impLoc fullModName], env))"

(* Helper function to process a list of imports, building up an environment incrementally *)
fun process_import_list :: "BabImport list \<Rightarrow> (string, BabModule) fmap \<Rightarrow> RenameEnv \<Rightarrow> RenameError list * RenameEnv"
  where
"process_import_list imports allMods initialEnv =
  fold (\<lambda>imp (accErrs, accEnv).
          let (errs, newEnv) = process_import imp allMods accEnv
          in (errs @ accErrs, newEnv))
       imports
       ([], initialEnv)"


(*-----------------------------------------------------------------------------*)
(* Name resolution *)
(*-----------------------------------------------------------------------------*)

(* Functions to look up a particular name and return its renamed version.
   May also return errors (currently it will only return upto 1 error). *)
fun rename_name_generic :: "string fset \<Rightarrow> (string, string list) fmap \<Rightarrow>
                           (Location \<Rightarrow> string \<Rightarrow> RenameError) \<Rightarrow>
                           (Location \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> RenameError) \<Rightarrow>
                           Location \<Rightarrow> string \<Rightarrow> (RenameError list * string)"
  where
"rename_name_generic localNames globalNamesMap notFoundError ambiguousError loc name =
  (if name |\<in>| localNames then
    ([], name)
  else
    (case fmlookup globalNamesMap name of
      None \<Rightarrow> ([notFoundError loc name], ''#Error'')
      | Some [trueName] \<Rightarrow> ([], trueName)
      | Some multiple \<Rightarrow> ([ambiguousError loc name multiple], ''#Error'')))"

fun rename_type_name :: "RenameEnv \<Rightarrow> Location \<Rightarrow> string \<Rightarrow>
                         (RenameError list * string)"
  where
"rename_type_name env loc name =
  rename_name_generic (RE_LocalTypeNames env) (RE_GlobalTypeNames env)
                     RenameError_NotInScopeType RenameError_AmbiguousType loc name"

fun rename_term_name :: "RenameEnv \<Rightarrow> Location \<Rightarrow> string \<Rightarrow>
                         (RenameError list * string)"
  where
"rename_term_name env loc name =
  rename_name_generic (RE_LocalTermNames env) (RE_GlobalTermNames env)
                     RenameError_NotInScopeTerm RenameError_AmbiguousTerm loc name"

(* Build a chain of field projections from a base term.
   base_name is the renamed (fully qualified) name, field_names is the list of field names to project. *)
fun build_projection_chain :: "Location \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> BabTerm"
  where
"build_projection_chain loc base_name flds = 
    List.foldl (\<lambda>tm fld. BabTm_RecordProj loc tm fld) (BabTm_Name loc base_name []) flds"

(* Rename a term name, considering field projection interpretations.
   If tyargs is non-empty, only try standard name resolution.
   If tyargs is empty, try all possible dot-splits and report ambiguity if multiple succeed. *)
fun rename_term_name_with_projections :: "RenameEnv \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> BabType list \<Rightarrow>
                                         (RenameError list * BabTerm)"
  where
"rename_term_name_with_projections env loc name tyargs =
  (if tyargs \<noteq> [] then
    (case rename_term_name env loc name of
      (errs, newName) \<Rightarrow> (errs, BabTm_Name loc newName tyargs))
  else
    (let splits = all_dot_splits name;
         attempts = map (\<lambda>(base, flds).
                          case rename_term_name env loc base of
                            ([], resolvedBase) \<Rightarrow> Some (resolvedBase, flds)
                            | (errs, _) \<Rightarrow> None) splits;
         successes = List.map_filter id attempts
     in case successes of
       [] \<Rightarrow>
         (case rename_term_name env loc name of (errs, _) \<Rightarrow> (errs, BabTm_Name loc ''#Error'' []))
       | [(resolvedBase, flds)] \<Rightarrow>
         ([], build_projection_chain loc resolvedBase flds)
       | multiple \<Rightarrow>
         (let descriptions = map (\<lambda>(base, flds).
                                   if flds = [] then base
                                   else base @ '' (with field projections)'') multiple
          in ([RenameError_AmbiguousTerm loc name descriptions],
              BabTm_Name loc ''#Error'' []))))"


(*-----------------------------------------------------------------------------*)
(* Main renaming functions *)
(*-----------------------------------------------------------------------------*)

(* Rename a pattern. Return errors, a renamed pattern, and bound variables. *)
fun rename_pattern :: "RenameEnv \<Rightarrow> BabPattern \<Rightarrow>
                       RenameError list * BabPattern * string list"
  where
"rename_pattern env (BabPat_Var loc vr name) = ([], BabPat_Var loc vr name, [name])"
| "rename_pattern env (BabPat_Bool loc b) = ([], BabPat_Bool loc b, [])"
| "rename_pattern env (BabPat_Int loc i) = ([], BabPat_Int loc i, [])"
| "rename_pattern env (BabPat_Tuple loc pats) =
      (let results = map (rename_pattern env) pats;
           allErrs = concat (map (\<lambda>(errs, _, _). errs) results);
           newPats = map (\<lambda>(_, pat, _). pat) results;
           allBoundVars = concat (map (\<lambda>(_, _, vars). vars) results)
       in (allErrs, BabPat_Tuple loc newPats, allBoundVars))"
| "rename_pattern env (BabPat_Record loc pats) =
      (let results = map (\<lambda>(name, pat). let (errs, newPat, vars) = rename_pattern env pat
                                        in (errs, (name, newPat), vars)) pats;
           allErrs = concat (map (\<lambda>(errs, _, _). errs) results);
           newPats = map (\<lambda>(_, pat, _). pat) results;
           allBoundVars = concat (map (\<lambda>(_, _, vars). vars) results)
       in (allErrs, BabPat_Record loc newPats, allBoundVars))"
| "rename_pattern env (BabPat_Variant loc ctorName optionalPayload) =
      (case rename_term_name env loc ctorName of
        (errs1, newCtorName) \<Rightarrow>
          (case optionalPayload of
            None \<Rightarrow> (errs1, BabPat_Variant loc newCtorName None, [])
            | Some payload \<Rightarrow>
                (case rename_pattern env payload of
                  (errs2, newPayload, boundVars) \<Rightarrow>
                    (errs1 @ errs2, BabPat_Variant loc newCtorName (Some newPayload), boundVars))))"
| "rename_pattern env (BabPat_Wildcard loc) = ([], BabPat_Wildcard loc, [])"

(* Mutually recursive renaming functions *)
fun rename_type :: "RenameEnv \<Rightarrow> BabType \<Rightarrow>
                    RenameError list * BabType"
and rename_term :: "RenameEnv \<Rightarrow> BabTerm \<Rightarrow>
                    RenameError list * BabTerm"
and rename_literal :: "RenameEnv \<Rightarrow> BabLiteral \<Rightarrow>
                       RenameError list * BabLiteral"
and rename_dimension :: "RenameEnv \<Rightarrow> BabDimension \<Rightarrow>
                         RenameError list * BabDimension"
  where
"rename_type env (BabTy_Name loc name tyargs) =
    (case rename_type_name env loc name of
      (errs1, newName) \<Rightarrow>
        (let tyargResults = map (rename_type env) tyargs;
             tyargErrs = concat (map fst tyargResults);
             newTyargs = map snd tyargResults
         in (errs1 @ tyargErrs, BabTy_Name loc newName newTyargs)))"
| "rename_type env (BabTy_Bool loc) = ([], BabTy_Bool loc)"
| "rename_type env (BabTy_FiniteInt loc sign bits) = ([], BabTy_FiniteInt loc sign bits)"
| "rename_type env (BabTy_MathInt loc) = ([], BabTy_MathInt loc)"
| "rename_type env (BabTy_MathReal loc) = ([], BabTy_MathReal loc)"
| "rename_type env (BabTy_Tuple loc types) =
    (let results = map (rename_type env) types;
         allErrs = concat (map fst results);
         newTypes = map snd results
     in (allErrs, BabTy_Tuple loc newTypes))"
| "rename_type env (BabTy_Record loc fieldList) =
    (let results = map (\<lambda>(name, ty). let (errs, newTy) = rename_type env ty
                                      in (errs, (name, newTy))) fieldList;
         allErrs = concat (map fst results);
         newFields = map snd results
     in (allErrs, BabTy_Record loc newFields))"
| "rename_type env (BabTy_Array loc elemType dims) =
    (case rename_type env elemType of
      (errs1, newElemType) \<Rightarrow>
        (let dimResults = map (rename_dimension env) dims;
             dimErrs = concat (map fst dimResults);
             newDims = map snd dimResults
         in (errs1 @ dimErrs, BabTy_Array loc newElemType newDims)))"

| "rename_literal env (BabLit_Bool b) = ([], BabLit_Bool b)"
| "rename_literal env (BabLit_Int i) = ([], BabLit_Int i)"
| "rename_literal env (BabLit_String s) = ([], BabLit_String s)"
| "rename_literal env (BabLit_Array terms) =
    (let results = map (rename_term env) terms;
         allErrs = concat (map fst results);
         newTerms = map snd results
     in (allErrs, BabLit_Array newTerms))"

| "rename_dimension env BabDim_Unknown = ([], BabDim_Unknown)"
| "rename_dimension env BabDim_Allocatable = ([], BabDim_Allocatable)"
| "rename_dimension env (BabDim_Fixed tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow> (errs, BabDim_Fixed newTm))"

| "rename_term env (BabTm_Literal loc lit) =
    (case rename_literal env lit of
      (errs, newLit) \<Rightarrow> (errs, BabTm_Literal loc newLit))"
| "rename_term env (BabTm_Name loc name tyargs) =
    (if name = ''return'' then
      (if \<not> RE_InPostcondition env then
        ([RenameError_ReturnVarOutsidePostcond loc], BabTm_Name loc ''#Error'' [])
      else if RE_CurrentFunctionReturnType env = None then
        ([RenameError_ReturnVarVoidFunction loc], BabTm_Name loc ''#Error'' [])
      else
        ([], BabTm_Name loc ''return'' []))
    else
      (let tyargResults = map (rename_type env) tyargs;
           tyargErrs = concat (map fst tyargResults);
           newTyargs = map snd tyargResults
       in case rename_term_name_with_projections env loc name newTyargs of
         (nameErrs, resultTm) \<Rightarrow> (nameErrs @ tyargErrs, resultTm)))"
| "rename_term env (BabTm_Cast loc ty tm) =
    (case rename_type env ty of
      (errs1, newTy) \<Rightarrow>
        (case rename_term env tm of
          (errs2, newTm) \<Rightarrow>
            (errs1 @ errs2, BabTm_Cast loc newTy newTm)))"
| "rename_term env (BabTm_If loc cond thenTm elseTm) =
    (case rename_term env cond of
      (errs1, newCond) \<Rightarrow>
        (case rename_term env thenTm of
          (errs2, newThenTm) \<Rightarrow>
            (case rename_term env elseTm of
              (errs3, newElseTm) \<Rightarrow>
                (errs1 @ errs2 @ errs3, BabTm_If loc newCond newThenTm newElseTm))))"
| "rename_term env (BabTm_Unop loc op tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow>
        (errs, BabTm_Unop loc op newTm))"
| "rename_term env (BabTm_Binop loc tm1 opTmList) =
    (case rename_term env tm1 of
      (errs1, newTm1) \<Rightarrow>
        (let results = map (\<lambda>(op, tm). let (errs, newTm) = rename_term env tm
                                        in (errs, (op, newTm))) opTmList;
             allErrs = concat (map fst results);
             newOpTmList = map snd results
         in (errs1 @ allErrs, BabTm_Binop loc newTm1 newOpTmList)))"
| "rename_term env (BabTm_Let loc var tm1 tm2) =
    (case rename_term env tm1 of
      (errs1, newTm1) \<Rightarrow>
        (let newScopeEnv = open_term_scope env;
             (varErrs, env2) = add_local_term_names loc [var] newScopeEnv
         in case rename_term env2 tm2 of
           (errs2, newTm2) \<Rightarrow>
             (errs1 @ varErrs @ errs2, BabTm_Let loc var newTm1 newTm2)))"
| "rename_term env (BabTm_Quantifier loc quant var ty tm) =
    (case rename_type env ty of
      (errs1, newTy) \<Rightarrow>
        (let newScopeEnv = open_term_scope env;
             (varErrs, env2) = add_local_term_names loc [var] newScopeEnv
         in case rename_term env2 tm of
           (errs2, newTm) \<Rightarrow>
             (errs1 @ varErrs @ errs2, BabTm_Quantifier loc quant var newTy newTm)))"
| "rename_term env (BabTm_Call loc fn args) =
    (case rename_term env fn of
      (errs1, newFn) \<Rightarrow>
        (let results = map (rename_term env) args;
             allErrs = concat (map fst results);
             newArgs = map snd results
         in (errs1 @ allErrs, BabTm_Call loc newFn newArgs)))"
| "rename_term env (BabTm_Tuple loc terms) =
    (let results = map (rename_term env) terms;
         allErrs = concat (map fst results);
         newTerms = map snd results
     in (allErrs, BabTm_Tuple loc newTerms))"
| "rename_term env (BabTm_Record loc fieldList) =
    (let results = map (\<lambda>(name, tm). let (errs, newTm) = rename_term env tm
                                      in (errs, (name, newTm))) fieldList;
         allErrs = concat (map fst results);
         newFields = map snd results
     in (allErrs, BabTm_Record loc newFields))"
| "rename_term env (BabTm_RecordUpdate loc tm fieldList) =
    (case rename_term env tm of
      (errs1, newTm) \<Rightarrow>
        (let results = map (\<lambda>(name, fieldTm). let (errs, newFieldTm) = rename_term env fieldTm
                                               in (errs, (name, newFieldTm))) fieldList;
             allErrs = concat (map fst results);
             newFields = map snd results
         in (errs1 @ allErrs, BabTm_RecordUpdate loc newTm newFields)))"
| "rename_term env (BabTm_TupleProj loc tm idx) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow>
        (errs, BabTm_TupleProj loc newTm idx))"
| "rename_term env (BabTm_RecordProj loc tm field) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow>
        (errs, BabTm_RecordProj loc newTm field))"
| "rename_term env (BabTm_ArrayProj loc tm indices) =
    (case rename_term env tm of
      (errs1, newTm) \<Rightarrow>
        (let results = map (rename_term env) indices;
             allErrs = concat (map fst results);
             newIndices = map snd results
         in (errs1 @ allErrs, BabTm_ArrayProj loc newTm newIndices)))"
| "rename_term env (BabTm_Match loc tm cases) =
    (case rename_term env tm of
      (errs1, newTm) \<Rightarrow>
        (let results = map (\<lambda>(pat, caseTm).
                              case rename_pattern env pat of
                                (patErrs, newPat, boundVars) \<Rightarrow>
                                  let newScopeEnv = open_term_scope env;
                                      (varErrs, env2) = add_local_term_names loc boundVars newScopeEnv
                                  in case rename_term env2 caseTm of
                                    (tmErrs, newCaseTm) \<Rightarrow>
                                      (patErrs @ varErrs @ tmErrs, (newPat, newCaseTm))) cases;
             allErrs = concat (map fst results);
             newCases = map snd results
         in (errs1 @ allErrs, BabTm_Match loc newTm newCases)))"
| "rename_term env (BabTm_Sizeof loc tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow>
        (errs, BabTm_Sizeof loc newTm))"
| "rename_term env (BabTm_Allocated loc tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow>
        (errs, BabTm_Allocated loc newTm))"
| "rename_term env (BabTm_Old loc tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow>
        (errs, BabTm_Old loc newTm))"

(* Rename an attribute. Return errors and a renamed attribute. *)
fun rename_attribute :: "RenameEnv \<Rightarrow> BabAttribute \<Rightarrow>
                         RenameError list * BabAttribute"
  where
"rename_attribute env (BabAttr_Requires loc tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow> (errs, BabAttr_Requires loc newTm))"
| "rename_attribute env (BabAttr_Ensures loc tm) =
    (let postcondEnv = env \<lparr> RE_InPostcondition := True \<rparr>
     in case rename_term postcondEnv tm of
       (errs, newTm) \<Rightarrow> (errs, BabAttr_Ensures loc newTm))"
| "rename_attribute env (BabAttr_Invariant loc tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow> (errs, BabAttr_Invariant loc newTm))"
| "rename_attribute env (BabAttr_Decreases loc tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow> (errs, BabAttr_Decreases loc newTm))"

(* Mutually recursive statement renaming functions *)
fun rename_statement :: "RenameEnv \<Rightarrow> BabStatement \<Rightarrow>
                         RenameError list * BabStatement * string list"
and rename_statements :: "RenameEnv \<Rightarrow> BabStatement list \<Rightarrow>
                          RenameError list * BabStatement list"
  where
"rename_statement env (BabStmt_VarDecl loc ghost var varOrRef optTy optTm) =
    (let (tyErrs, newOptTy) = (case optTy of
           None \<Rightarrow> ([], None)
           | Some ty \<Rightarrow> let (errs, newTy) = rename_type env ty
                        in (errs, Some newTy));
         (tmErrs, newOptTm) = (case optTm of
           None \<Rightarrow> ([], None)
           | Some tm \<Rightarrow> let (errs, newTm) = rename_term env tm
                        in (errs, Some newTm))
     in (tyErrs @ tmErrs, BabStmt_VarDecl loc ghost var varOrRef newOptTy newOptTm, [var]))"
| "rename_statement env (BabStmt_Fix loc var ty) =
    (case rename_type env ty of
      (errs, newTy) \<Rightarrow> (errs, BabStmt_Fix loc var newTy, [var]))"
| "rename_statement env (BabStmt_Obtain loc var ty tm) =
    (case rename_type env ty of
      (errs1, newTy) \<Rightarrow>
        (let (varErrs, env2) = add_local_term_names loc [var] env
         in case rename_term env2 tm of
          (errs2, newTm) \<Rightarrow>
            (errs1 @ varErrs @ errs2, BabStmt_Obtain loc var newTy newTm, [var])))"
| "rename_statement env (BabStmt_Use loc tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow> (errs, BabStmt_Use loc newTm, []))"
| "rename_statement env (BabStmt_Assign loc ghost lhs rhs) =
    (case rename_term env lhs of
      (errs1, newLhs) \<Rightarrow>
        (case rename_term env rhs of
          (errs2, newRhs) \<Rightarrow>
            (errs1 @ errs2, BabStmt_Assign loc ghost newLhs newRhs, [])))"
| "rename_statement env (BabStmt_Swap loc ghost lhs rhs) =
    (case rename_term env lhs of
      (errs1, newLhs) \<Rightarrow>
        (case rename_term env rhs of
          (errs2, newRhs) \<Rightarrow>
            (errs1 @ errs2, BabStmt_Swap loc ghost newLhs newRhs, [])))"
| "rename_statement env (BabStmt_Return loc ghost optTm) =
    (case optTm of
      None \<Rightarrow> ([], BabStmt_Return loc ghost None, [])
      | Some tm \<Rightarrow>
          (case rename_term env tm of
            (errs, newTm) \<Rightarrow> (errs, BabStmt_Return loc ghost (Some newTm), [])))"
| "rename_statement env (BabStmt_Assert loc optTm stmts) =
    (let (tmErrs, newOptTm) = (case optTm of
           None \<Rightarrow> ([], None)
           | Some tm \<Rightarrow> let (errs, newTm) = rename_term env tm
                        in (errs, Some newTm));
         newScopeEnv = open_term_scope env;
         (stmtErrs, newStmts) = rename_statements newScopeEnv stmts
     in (tmErrs @ stmtErrs, BabStmt_Assert loc newOptTm newStmts, []))"
| "rename_statement env (BabStmt_Assume loc tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow> (errs, BabStmt_Assume loc newTm, []))"
| "rename_statement env (BabStmt_If loc ghost cond thenStmts elseStmts) =
    (case rename_term env cond of
      (errs1, newCond) \<Rightarrow>
        (let thenScopeEnv = open_term_scope env;
             (thenErrs, newThenStmts) = rename_statements thenScopeEnv thenStmts;
             elseScopeEnv = open_term_scope env;
             (elseErrs, newElseStmts) = rename_statements elseScopeEnv elseStmts
         in (errs1 @ thenErrs @ elseErrs, BabStmt_If loc ghost newCond newThenStmts newElseStmts, [])))"
| "rename_statement env (BabStmt_While loc ghost cond attrs bodyStmts) =
    (case rename_term env cond of
      (errs1, newCond) \<Rightarrow>
        (let attrResults = map (rename_attribute env) attrs;
             attrErrs = concat (map fst attrResults);
             newAttrs = map snd attrResults;
             bodyScopeEnv = open_term_scope env;
             (bodyErrs, newBodyStmts) = rename_statements bodyScopeEnv bodyStmts
         in (errs1 @ attrErrs @ bodyErrs, BabStmt_While loc ghost newCond newAttrs newBodyStmts, [])))"
| "rename_statement env (BabStmt_Call loc ghost tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow> (errs, BabStmt_Call loc ghost newTm, []))"
| "rename_statement env (BabStmt_Match loc ghost tm cases) =
    (case rename_term env tm of
      (errs1, newTm) \<Rightarrow>
        (let results = map (\<lambda>(pat, caseStmts).
                              case rename_pattern env pat of
                                (patErrs, newPat, boundVars) \<Rightarrow>
                                  let newScopeEnv = open_term_scope env;
                                      (varErrs, env2) = add_local_term_names loc boundVars newScopeEnv;
                                      (stmtErrs, newCaseStmts) = rename_statements env2 caseStmts
                                  in (patErrs @ varErrs @ stmtErrs, (newPat, newCaseStmts))) cases;
             allErrs = concat (map fst results);
             newCases = map snd results
         in (errs1 @ allErrs, BabStmt_Match loc ghost newTm newCases, [])))"
| "rename_statement env (BabStmt_ShowHide loc showHide name) =
    (case rename_term_name env loc name of
      (errs, newName) \<Rightarrow> (errs, BabStmt_ShowHide loc showHide newName, []))"

| "rename_statements env [] = ([], [])"
| "rename_statements env (stmt#stmts) =
    (case rename_statement env stmt of
      (errs1, newStmt, boundVars) \<Rightarrow>
        (let (varErrs, env2) = add_local_term_names (bab_statement_location newStmt) boundVars env
         in case rename_statements env2 stmts of
          (errs2, newStmts) \<Rightarrow>
            (errs1 @ varErrs @ errs2, newStmt#newStmts)))"

(* Rename a declaration. Return errors and a renamed declaration. *)
fun rename_declaration :: "string \<Rightarrow> RenameEnv \<Rightarrow> BabDeclaration \<Rightarrow>
                           RenameError list * BabDeclaration"
  where
"rename_declaration fullModName env (BabDecl_Const dc) =
    (let newName = fullModName @ ''.'' @ DC_Name dc;
         (tyErrs, newOptTy) = (case DC_Type dc of
           None \<Rightarrow> ([], None)
           | Some ty \<Rightarrow> let (errs, newTy) = rename_type env ty
                        in (errs, Some newTy));
         (tmErrs, newOptTm) = (case DC_Value dc of
           None \<Rightarrow> ([], None)
           | Some tm \<Rightarrow> let (errs, newTm) = rename_term env tm
                        in (errs, Some newTm));
         newDc = dc \<lparr> DC_Name := newName, DC_Type := newOptTy, DC_Value := newOptTm \<rparr>
     in (tyErrs @ tmErrs, BabDecl_Const newDc))"
| "rename_declaration fullModName env (BabDecl_Function df) =
    (let newName = fullModName @ ''.'' @ DF_Name df;
         loc = DF_Location df;
         tyArgNames = DF_TyArgs df;
         tmArgNames = map (\<lambda>(name, _, _). name) (DF_TmArgs df);

         (tyArgNameErrs, env1) = add_local_type_names loc tyArgNames env;
         argResults = map (\<lambda>(name, varRef, ty).
                            let (errs, newTy) = rename_type env1 ty
                            in (errs, (name, varRef, newTy))) (DF_TmArgs df);
         tmArgErrs = concat (map fst argResults);
         newTmArgs = map snd argResults;
         (retTyErrs, newRetTy) = (case DF_ReturnType df of
           None \<Rightarrow> ([], None)
           | Some ty \<Rightarrow> let (errs, newTy) = rename_type env1 ty
                        in (errs, Some newTy));

         (tmArgNameErrs, newEnv) = add_local_term_names loc tmArgNames env1;
         newEnvWithRetTy = newEnv \<lparr> RE_CurrentFunctionReturnType := newRetTy \<rparr>;

         (bodyErrs, newBody) = (case DF_Body df of
           None \<Rightarrow> ([], None)
           | Some stmts \<Rightarrow> let (errs, newStmts) = rename_statements newEnvWithRetTy stmts
                           in (errs, Some newStmts));

         attrResults = map (rename_attribute newEnvWithRetTy) (DF_Attributes df);
         attrErrs = concat (map fst attrResults);
         newAttrs = map snd attrResults;

         newDf = df \<lparr> DF_Name := newName,
                     DF_TmArgs := newTmArgs,
                     DF_ReturnType := newRetTy,
                     DF_Body := newBody,
                     DF_Attributes := newAttrs \<rparr>
     in (tyArgNameErrs @ tmArgNameErrs @ tmArgErrs @ retTyErrs @ bodyErrs @ attrErrs, BabDecl_Function newDf))"
| "rename_declaration fullModName env (BabDecl_Datatype dd) =
    (let newName = fullModName @ ''.'' @ DD_Name dd;
         loc = DD_Location dd;
         tyArgNames = DD_TyArgs dd;
         (tyArgErrs, newEnv) = add_local_type_names loc tyArgNames env;

         ctorResults = map (\<lambda>(loc, name, optTy).
                             let newCtorName = fullModName @ ''.'' @ name
                             in case optTy of
                               None \<Rightarrow> ([], (loc, newCtorName, None))
                               | Some ty \<Rightarrow> let (errs, newTy) = rename_type newEnv ty
                                            in (errs, (loc, newCtorName, Some newTy))) (DD_Ctors dd);
         ctorErrs = concat (map fst ctorResults);
         newCtors = map snd ctorResults;

         newDd = dd \<lparr> DD_Name := newName, DD_Ctors := newCtors \<rparr>
     in (tyArgErrs @ ctorErrs, BabDecl_Datatype newDd))"
| "rename_declaration fullModName env (BabDecl_Typedef dt) =
    (let newName = fullModName @ ''.'' @ DT_Name dt;
         loc = DT_Location dt;
         tyArgNames = DT_TyArgs dt;
         (tyArgErrs, newEnv) = add_local_type_names loc tyArgNames env;

         (defErrs, newDef) = (case DT_Definition dt of
           None \<Rightarrow> ([], None)
           | Some ty \<Rightarrow> let (errs, newTy) = rename_type newEnv ty
                        in (errs, Some newTy));

         newDt = dt \<lparr> DT_Name := newName, DT_Definition := newDef \<rparr>
     in (tyArgErrs @ defErrs, BabDecl_Typedef newDt))"


(*-----------------------------------------------------------------------------*)
(* Main entry point *)
(*-----------------------------------------------------------------------------*)

(* Rename interface declarations of a module.
   Returns: (errors, renamed interface decls, interface env for use by implementation) *)
fun rename_module_interface :: "BabModule \<Rightarrow> (string, BabModule) fmap \<Rightarrow>
                                 RenameError list * BabDeclaration list * RenameEnv"
  where
"rename_module_interface module allMods =
  (let modName = Mod_Name module;
       (importErrs, importEnv) = process_import_list (Mod_InterfaceImports module) allMods empty_renamer_env;
       interfaceEnv = add_current_module_decls module (Mod_Interface module) importEnv;
       declResults = map (rename_declaration modName interfaceEnv) (Mod_Interface module);
       declErrs = concat (map fst declResults);
       newInterface = map snd declResults
   in (importErrs @ declErrs, newInterface, interfaceEnv))"

(* Rename implementation declarations of a module.
   Returns: (errors, renamed implementation decls) *)
fun rename_module_implementation :: "BabModule \<Rightarrow> (string, BabModule) fmap \<Rightarrow> RenameEnv \<Rightarrow>
                                      RenameError list * BabDeclaration list"
  where
"rename_module_implementation module allMods interfaceEnv =
  (let modName = Mod_Name module;
       (importErrs, importEnv) = process_import_list (Mod_ImplementationImports module) allMods interfaceEnv;
       implEnv = add_current_module_decls module (Mod_Implementation module) importEnv;
       declResults = map (rename_declaration modName implEnv) (Mod_Implementation module);
       declErrs = concat (map fst declResults);
       newImplementation = map snd declResults
   in (importErrs @ declErrs, newImplementation))"

(* Main function for renaming a module. *)
fun rename_module :: "BabModule \<Rightarrow> BabModule list \<Rightarrow> (RenameError list, BabModule) sum"
  where
"rename_module module allMods =
  (let allModsFmap = modules_to_fmap allMods;
       dupErrs = check_duplicate_decl_names (Mod_Interface module)
          @ check_duplicate_decl_names (Mod_Implementation module);
       allImports = Mod_InterfaceImports module @ Mod_ImplementationImports module;
       aliasErrs = check_duplicate_aliases (Mod_Name module) allImports;
       (interfaceErrs, newInterface, interfaceEnv) = rename_module_interface module allModsFmap;
       (implErrs, newImplementation) = rename_module_implementation module allModsFmap interfaceEnv;
       allErrors = dupErrs @ aliasErrs @ interfaceErrs @ implErrs;
       newMod = module \<lparr> Mod_Interface := newInterface,
                         Mod_Implementation := newImplementation \<rparr>
   in if allErrors = [] then Inr newMod else Inl allErrors)"


(*-----------------------------------------------------------------------------*)
(* Properties of rename_module *)
(*-----------------------------------------------------------------------------*)

lemma rename_module_preserves_name:
  assumes "rename_module module allMods = Inr newMod"
  shows "Mod_Name newMod = Mod_Name module"
  using assms
proof -
  define allModsFmap where "allModsFmap = modules_to_fmap allMods"
  obtain errs1 decls1 env1 where 1: "rename_module_interface module allModsFmap = (errs1, decls1, env1)"
    using prod_cases3 by blast
  obtain errs2 decls2 where 2: "rename_module_implementation module allModsFmap env1 = (errs2, decls2)"
    using old.prod.exhaust by blast
  show ?thesis proof (cases "rename_module module allMods")
    case (Inl a)
    then show ?thesis using assms by auto
  next
    case (Inr b)
    have "newMod = module \<lparr> Mod_Interface := decls1, Mod_Implementation := decls2 \<rparr>"
      using 1 2 assms Inr allModsFmap_def by (auto simp: Let_def split: if_splits)
    thus ?thesis by auto
  qed
qed

lemma rename_module_preserves_interface_imports:
  assumes "rename_module module allMods = Inr newMod"
  shows "Mod_InterfaceImports newMod = Mod_InterfaceImports module"
  using assms
proof -
  define allModsFmap where "allModsFmap = modules_to_fmap allMods"
  obtain errs1 decls1 env1 where 1: "rename_module_interface module allModsFmap = (errs1, decls1, env1)"
    using prod_cases3 by blast
  obtain errs2 decls2 where 2: "rename_module_implementation module allModsFmap env1 = (errs2, decls2)"
    using old.prod.exhaust by blast
  show ?thesis proof (cases "rename_module module allMods")
    case (Inl a)
    then show ?thesis using assms by auto
  next
    case (Inr b)
    have "newMod = module \<lparr> Mod_Interface := decls1, Mod_Implementation := decls2 \<rparr>"
      using 1 2 assms Inr allModsFmap_def by (auto simp: Let_def split: if_splits)
    thus ?thesis by auto
  qed
qed

lemma rename_module_preserves_implementation_imports:
  assumes "rename_module module allMods = Inr newMod"
  shows "Mod_ImplementationImports newMod = Mod_ImplementationImports module"
  using assms
proof -
  define allModsFmap where "allModsFmap = modules_to_fmap allMods"
  obtain errs1 decls1 env1 where 1: "rename_module_interface module allModsFmap = (errs1, decls1, env1)"
    using prod_cases3 by blast
  obtain errs2 decls2 where 2: "rename_module_implementation module allModsFmap env1 = (errs2, decls2)"
    using old.prod.exhaust by blast
  show ?thesis proof (cases "rename_module module allMods")
    case (Inl a)
    then show ?thesis using assms by auto
  next
    case (Inr b)
    have "newMod = module \<lparr> Mod_Interface := decls1, Mod_Implementation := decls2 \<rparr>"
      using 1 2 assms Inr allModsFmap_def by (auto simp: Let_def split: if_splits)
    thus ?thesis by auto
  qed
qed

lemma rename_module_preserves_interface_length:
  assumes "rename_module module allMods = Inr newMod"
  shows "length (Mod_Interface newMod) = length (Mod_Interface module)"
  using assms
proof -
  define allModsFmap where "allModsFmap = modules_to_fmap allMods"
  obtain errs1 decls1 env1 where 1: "rename_module_interface module allModsFmap = (errs1, decls1, env1)"
    using prod_cases3 by blast
  obtain errs2 decls2 where 2: "rename_module_implementation module allModsFmap env1 = (errs2, decls2)"
    using old.prod.exhaust by blast
  show ?thesis proof (cases "rename_module module allMods")
    case (Inl a)
    then show ?thesis using assms by auto
  next
    case (Inr b)
    have 3: "newMod = module \<lparr> Mod_Interface := decls1, Mod_Implementation := decls2 \<rparr>"
      using 1 2 assms Inr allModsFmap_def by (auto simp: Let_def split: if_splits)
    obtain importErrs env0 where
      4: "(importErrs, env0) = process_import_list (Mod_InterfaceImports module) allModsFmap empty_renamer_env"
      by (metis prod.exhaust)
    define interfaceEnv where
      "interfaceEnv = add_current_module_decls module (Mod_Interface module) env0"
    have 5: "decls1 = map snd (map (rename_declaration (Mod_Name module) interfaceEnv) (Mod_Interface module))"
      by (metis (no_types, lifting) "1" "4" interfaceEnv_def prod.case
          rename_module_interface.simps snd_eqD swap_simp)
    thus ?thesis
      by (simp add: "3")
  qed
qed

lemma rename_module_preserves_implementation_length:
  assumes "rename_module module allMods = Inr newMod"
  shows "length (Mod_Implementation newMod) = length (Mod_Implementation module)"
  using assms
proof -
  define allModsFmap where "allModsFmap = modules_to_fmap allMods"
  obtain errs1 decls1 env1 where 1: "rename_module_interface module allModsFmap = (errs1, decls1, env1)"
    using prod_cases3 by blast
  obtain errs2 decls2 where 2: "rename_module_implementation module allModsFmap env1 = (errs2, decls2)"
    using old.prod.exhaust by blast
  show ?thesis proof (cases "rename_module module allMods")
    case (Inl a)
    then show ?thesis using assms by auto
  next
    case (Inr b)
    have 3: "newMod = module \<lparr> Mod_Interface := decls1, Mod_Implementation := decls2 \<rparr>"
      using 1 2 assms Inr allModsFmap_def by (auto simp: Let_def split: if_splits)
    obtain importErrs env1a where
      4: "(importErrs, env1a) = process_import_list (Mod_ImplementationImports module) allModsFmap env1"
      by (metis prod.exhaust)
    define implEnv where
      "implEnv = add_current_module_decls module (Mod_Implementation module) env1a"
    have 5: "decls2 = map snd (map (rename_declaration (Mod_Name module) implEnv) (Mod_Implementation module))"
      by (metis (no_types, lifting) "2" "4" implEnv_def prod.case
          rename_module_implementation.simps snd_eqD)
    thus ?thesis
      by (simp add: "3")
  qed
qed

end

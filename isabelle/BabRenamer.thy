theory BabRenamer
  imports Main "HOL-Library.Char_ord" "HOL-Library.List_Lexorder" Location BabSyntax
begin

(* Renamer errors *)
datatype RenameError =
  RenameError_NotInScopeTerm Location string    (* not in scope: 'x' *)
  | RenameError_NotInScopeType Location string  (* not in scope: type 'T' *)
  | RenameError_AmbiguousTerm Location string "string list"  (* name 'x' is ambiguous: could be <list> *)
  | RenameError_AmbiguousType Location string "string list"  (* type name 'T' is ambiguous: could be <list> *)
  | RenameError_ModuleNotFound Location string  (* module not found: 'M' *)
  | RenameError_DuplicateAlias Location string  (* multiple imports of module 'M' *)


(* Renamer internal data structures *)
record GlobalName = 
  GN_UnqualifiedName :: "string option"  (* e.g. "foo" *)
  GN_QualifiedName :: string   (* e.g. "Foo.foo" or "F.foo" *)
  GN_TrueName :: string   (* e.g. "mypackage:Foo.foo" *)

record RenameEnv =
  RE_LocalTypeNames :: "string list"
  RE_LocalTermNames :: "string list"
  RE_CurrentModuleTypeNames :: "GlobalName list"
  RE_CurrentModuleTermNames :: "GlobalName list"
  RE_ImportedTypeNames :: "GlobalName list"
  RE_ImportedTermNames :: "GlobalName list"

(* RenamerEnv helpers *)
fun add_local_type_names :: "string list \<Rightarrow> RenameEnv \<Rightarrow> RenameEnv"
  where "add_local_type_names names env = env \<lparr> RE_LocalTypeNames := names @ RE_LocalTypeNames env \<rparr>"

fun add_local_term_names :: "string list \<Rightarrow> RenameEnv \<Rightarrow> RenameEnv"
  where "add_local_term_names names env = env \<lparr> RE_LocalTermNames := names @ RE_LocalTermNames env \<rparr>"

definition empty_renamer_env :: RenameEnv
  where "empty_renamer_env = \<lparr> RE_LocalTypeNames = [],
                               RE_LocalTermNames = [],
                               RE_CurrentModuleTypeNames = [],
                               RE_CurrentModuleTermNames = [],
                               RE_ImportedTypeNames = [],
                               RE_ImportedTermNames = [] \<rparr>"

fun merge_renamer_envs :: "RenameEnv \<Rightarrow> RenameEnv \<Rightarrow> RenameEnv"
  where
"merge_renamer_envs env1 env2 =
  \<lparr> RE_LocalTypeNames = RE_LocalTypeNames env1 @ RE_LocalTypeNames env2,
    RE_LocalTermNames = RE_LocalTermNames env1 @ RE_LocalTermNames env2,
    RE_CurrentModuleTypeNames = RE_CurrentModuleTypeNames env1 @ RE_CurrentModuleTypeNames env2,
    RE_CurrentModuleTermNames = RE_CurrentModuleTermNames env1 @ RE_CurrentModuleTermNames env2,
    RE_ImportedTypeNames = RE_ImportedTypeNames env1 @ RE_ImportedTypeNames env2,
    RE_ImportedTermNames = RE_ImportedTermNames env1 @ RE_ImportedTermNames env2 \<rparr>"

(* Module lookup functions *)
fun find_module_in_package :: "string \<Rightarrow> BabPackage \<Rightarrow> BabModule option"
  where
"find_module_in_package modName pkg =
  (case find (\<lambda>m. Mod_Name m = modName) (Pkg_ExportedModules pkg) of
    Some m \<Rightarrow> Some m
    | None \<Rightarrow> find (\<lambda>m. Mod_Name m = modName) (Pkg_OtherModules pkg))"

fun find_module_in_dependencies :: "string \<Rightarrow> string list \<Rightarrow> BabPackage list \<Rightarrow> (BabPackage * BabModule) option"
  where
"find_module_in_dependencies modName [] allPkgs = None"
| "find_module_in_dependencies modName (depName#restDeps) allPkgs =
    (case find (\<lambda>pkg. Pkg_Name pkg = depName) allPkgs of
      None \<Rightarrow> find_module_in_dependencies modName restDeps allPkgs
      | Some pkg \<Rightarrow>
          (case find (\<lambda>m. Mod_Name m = modName) (Pkg_ExportedModules pkg) of
            Some m \<Rightarrow> Some (pkg, m)
            | None \<Rightarrow> find_module_in_dependencies modName restDeps allPkgs))"

(* Helper function to find duplicates in a sorted list *)
fun find_duplicates_in_sorted :: "('a * 'b) list \<Rightarrow> ('a * 'b) list"
  where
"find_duplicates_in_sorted [] = []"
| "find_duplicates_in_sorted [x] = []"
| "find_duplicates_in_sorted ((a1, b1) # (a2, b2) # rest) =
    (if a1 = a2 then
      (a2, b2) # find_duplicates_in_sorted ((a2, b2) # rest)
    else
      find_duplicates_in_sorted ((a2, b2) # rest))"

(* Function to check for duplicate alias names in imports *)
fun check_duplicate_aliases :: "BabImport list \<Rightarrow> RenameError list"
  where
"check_duplicate_aliases imports =
  (let aliasLocPairs = map (\<lambda>imp. (Imp_AliasName imp, Imp_Location imp)) imports;
       sortedPairs = sort_key fst aliasLocPairs;
       duplicates = find_duplicates_in_sorted sortedPairs
   in map (\<lambda>(alias, loc). RenameError_DuplicateAlias loc alias) duplicates)"

(* GlobalName construction functions *)
fun make_global_name_for_decl :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool \<Rightarrow> string \<Rightarrow> GlobalName"
  where
"make_global_name_for_decl pkgName modName declName qualified aliasName =
  \<lparr> GN_UnqualifiedName = (if qualified then None else Some declName),
    GN_QualifiedName = aliasName @ ''.'' @ declName,
    GN_TrueName = pkgName @ '':'' @ modName @ ''.'' @ declName \<rparr>"

fun add_decl_to_env :: "BabDeclaration \<Rightarrow> GlobalName \<Rightarrow> bool \<Rightarrow> RenameEnv \<Rightarrow> RenameEnv"
  where
"add_decl_to_env decl gn isCurrentModule env =
  (if is_type_decl decl then
    (if isCurrentModule then
      env \<lparr> RE_CurrentModuleTypeNames := gn # RE_CurrentModuleTypeNames env \<rparr>
    else
      env \<lparr> RE_ImportedTypeNames := gn # RE_ImportedTypeNames env \<rparr>)
  else
    (if isCurrentModule then
      env \<lparr> RE_CurrentModuleTermNames := gn # RE_CurrentModuleTermNames env \<rparr>
    else
      env \<lparr> RE_ImportedTermNames := gn # RE_ImportedTermNames env \<rparr>))"

(* Import processing function *)
fun process_import :: "BabImport \<Rightarrow> string \<Rightarrow> BabPackage \<Rightarrow> BabPackage list \<Rightarrow> RenameEnv \<Rightarrow>
                      RenameError list * RenameEnv"
  where
"process_import imp currentPkgName currentPkg allPkgs env =
  (let modName = Imp_ModuleName imp;
       aliasName = Imp_AliasName imp;
       qualified = Imp_Qualified imp;
       impLoc = Imp_Location imp
   in
   case find_module_in_package modName currentPkg of
     Some foundMod \<Rightarrow>
       let declResults = map (\<lambda>decl.
                           let declName = get_decl_name decl;
                               gn = make_global_name_for_decl currentPkgName modName declName qualified aliasName
                           in (decl, gn)) (Mod_Interface foundMod);
           newEnv = fold (\<lambda>(decl, gn) acc. add_decl_to_env decl gn False acc) declResults env
       in ([], newEnv)
     | None \<Rightarrow>
         (case find_module_in_dependencies modName (Pkg_Dependencies currentPkg) allPkgs of
           Some (foundPkg, foundMod) \<Rightarrow>
             let foundPkgName = Pkg_Name foundPkg;
                 declResults = map (\<lambda>decl.
                               let declName = get_decl_name decl;
                                   gn = make_global_name_for_decl foundPkgName modName declName qualified aliasName
                               in (decl, gn)) (Mod_Interface foundMod);
                 newEnv = fold (\<lambda>(decl, gn) acc. add_decl_to_env decl gn False acc) declResults env
             in ([], newEnv)
           | None \<Rightarrow> ([RenameError_ModuleNotFound impLoc modName], env)))"

(* Helper function to process a list of imports *)
fun process_import_list :: "BabImport list \<Rightarrow> string \<Rightarrow> BabPackage \<Rightarrow> BabPackage list \<Rightarrow>
                            RenameError list * RenameEnv"
  where
"process_import_list imports pkgName currentPkg allPkgs =
  (let importResults = map (\<lambda>imp. process_import imp pkgName currentPkg allPkgs empty_renamer_env) imports;
       importErrs = concat (map fst importResults);
       importEnvs = map snd importResults;
       mergedEnv = fold merge_renamer_envs importEnvs empty_renamer_env
   in (importErrs, mergedEnv))"

(* Create a RenameEnv containing the current module's declarations only *)
fun add_current_module_decls :: "string \<Rightarrow> BabModule \<Rightarrow> RenameEnv"
  where
"add_current_module_decls pkgName currentMod =
  (let modName = Mod_Name currentMod;
       declResults = map (\<lambda>decl.
                       let declName = get_decl_name decl;
                           gn = make_global_name_for_decl pkgName modName declName False modName
                       in (decl, gn)) (Mod_Interface currentMod)
   in fold (\<lambda>(decl, gn) acc. add_decl_to_env decl gn True acc) declResults empty_renamer_env)"

(* Create a RenameEnv for a module (just containing local names and interface imports initially) *)
fun create_renamer_env :: "string \<Rightarrow> BabModule \<Rightarrow> BabPackage list \<Rightarrow>
                           RenameError list * RenameEnv"
  where
"create_renamer_env pkgName currentMod allPkgs =
  (let currentPkg = case find (\<lambda>pkg. Pkg_Name pkg = pkgName) allPkgs of
                      Some pkg \<Rightarrow> pkg;
       envWithCurrentDecls = add_current_module_decls pkgName currentMod;
       (interfaceImportErrs, interfaceImportEnv) = process_import_list (Mod_InterfaceImports currentMod) pkgName currentPkg allPkgs;
       finalEnv = merge_renamer_envs envWithCurrentDecls interfaceImportEnv
   in (interfaceImportErrs, finalEnv))"

(* Helper function to find GlobalNames matching a name *)
fun find_global_names :: "string \<Rightarrow> GlobalName list \<Rightarrow> GlobalName list"
  where
"find_global_names name globalNames =
  filter (\<lambda>g. (GN_UnqualifiedName g = Some name) \<or> (GN_QualifiedName g = name)) globalNames"

(* Functions to look up a particular name and return its renamed version.
   May also return errors (currently it will only return upto 1 error). *)
fun rename_name_generic :: "string list \<Rightarrow> GlobalName list \<Rightarrow> GlobalName list \<Rightarrow>
                           (Location \<Rightarrow> string \<Rightarrow> RenameError) \<Rightarrow>
                           (Location \<Rightarrow> string \<Rightarrow> string list \<Rightarrow> RenameError) \<Rightarrow>
                           Location \<Rightarrow> string \<Rightarrow> (RenameError list * string)"
  where
"rename_name_generic localNames currentModuleNames importedNames notFoundError ambiguousError loc name =
  (if find (\<lambda>x. x = name) localNames \<noteq> None then
    ([], name)
  else
    (case find_global_names name currentModuleNames of
      [g] \<Rightarrow> ([], GN_TrueName g)
      | [] \<Rightarrow>
          (case find_global_names name importedNames of
            [] \<Rightarrow> ([notFoundError loc name], ''#Error'')
            | [g] \<Rightarrow> ([], GN_TrueName g)
            | multiple \<Rightarrow> ([ambiguousError loc name (map GN_TrueName multiple)], ''#Error''))
      | multiple \<Rightarrow> ([ambiguousError loc name (map GN_TrueName multiple)], ''#Error'')))"

fun rename_type_name :: "RenameEnv \<Rightarrow> Location \<Rightarrow> string \<Rightarrow>
                         (RenameError list * string)"
  where
"rename_type_name env loc name =
  rename_name_generic (RE_LocalTypeNames env) (RE_CurrentModuleTypeNames env)
                     (RE_ImportedTypeNames env) RenameError_NotInScopeType
                     RenameError_AmbiguousType loc name"

fun rename_term_name :: "RenameEnv \<Rightarrow> Location \<Rightarrow> string \<Rightarrow>
                         (RenameError list * string)"
  where
"rename_term_name env loc name =
  rename_name_generic (RE_LocalTermNames env) (RE_CurrentModuleTermNames env)
                     (RE_ImportedTermNames env) RenameError_NotInScopeTerm
                     RenameError_AmbiguousTerm loc name"

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
    (case rename_term_name env loc name of
      (errs1, newName) \<Rightarrow>
        (let results = map (rename_type env) tyargs;
             allErrs = concat (map fst results);
             newTyargs = map snd results
         in (errs1 @ allErrs, BabTm_Name loc newName newTyargs)))"
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
        (case rename_term (add_local_term_names [var] env) tm2 of
          (errs2, newTm2) \<Rightarrow>
            (errs1 @ errs2, BabTm_Let loc var newTm1 newTm2)))"
| "rename_term env (BabTm_Quantifier loc quant var ty tm) =
    (case rename_type env ty of
      (errs1, newTy) \<Rightarrow>
        (case rename_term (add_local_term_names [var] env) tm of
          (errs2, newTm) \<Rightarrow>
            (errs1 @ errs2, BabTm_Quantifier loc quant var newTy newTm)))"
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
                                  case rename_term (add_local_term_names boundVars env) caseTm of
                                    (tmErrs, newCaseTm) \<Rightarrow>
                                      (patErrs @ tmErrs, (newPat, newCaseTm))) cases;
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
    (case rename_term env tm of
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
        (case rename_term (add_local_term_names [var] env) tm of
          (errs2, newTm) \<Rightarrow>
            (errs1 @ errs2, BabStmt_Obtain loc var newTy newTm, [var])))"
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
         (stmtErrs, newStmts) = rename_statements env stmts
     in (tmErrs @ stmtErrs, BabStmt_Assert loc newOptTm newStmts, []))"
| "rename_statement env (BabStmt_Assume loc tm) =
    (case rename_term env tm of
      (errs, newTm) \<Rightarrow> (errs, BabStmt_Assume loc newTm, []))"
| "rename_statement env (BabStmt_If loc ghost cond thenStmts elseStmts) =
    (case rename_term env cond of
      (errs1, newCond) \<Rightarrow>
        (let (thenErrs, newThenStmts) = rename_statements env thenStmts;
             (elseErrs, newElseStmts) = rename_statements env elseStmts
         in (errs1 @ thenErrs @ elseErrs, BabStmt_If loc ghost newCond newThenStmts newElseStmts, [])))"
| "rename_statement env (BabStmt_While loc ghost cond attrs bodyStmts) =
    (case rename_term env cond of
      (errs1, newCond) \<Rightarrow>
        (let attrResults = map (rename_attribute env) attrs;
             attrErrs = concat (map fst attrResults);
             newAttrs = map snd attrResults;
             (bodyErrs, newBodyStmts) = rename_statements env bodyStmts
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
                                  let newEnv = add_local_term_names boundVars env;
                                      (stmtErrs, newCaseStmts) = rename_statements newEnv caseStmts
                                  in (patErrs @ stmtErrs, (newPat, newCaseStmts))) cases;
             allErrs = concat (map fst results);
             newCases = map snd results
         in (errs1 @ allErrs, BabStmt_Match loc ghost newTm newCases, [])))"
| "rename_statement env (BabStmt_ShowHide loc showHide name) =
    ([], BabStmt_ShowHide loc showHide name, [])"

| "rename_statements env [] = ([], [])"
| "rename_statements env (stmt#stmts) =
    (case rename_statement env stmt of
      (errs1, newStmt, boundVars) \<Rightarrow>
        (case rename_statements (add_local_term_names boundVars env) stmts of
          (errs2, newStmts) \<Rightarrow>
            (errs1 @ errs2, newStmt#newStmts)))"

(* Rename a declaration. Return errors and a renamed declaration. *)
fun rename_declaration :: "RenameEnv \<Rightarrow> BabDeclaration \<Rightarrow>
                           RenameError list * BabDeclaration"
  where
"rename_declaration env (BabDecl_Const dc) =
    (let (nameErrs, newName) = rename_term_name env (DC_Location dc) (DC_Name dc);
         (tyErrs, newOptTy) = (case DC_Type dc of
           None \<Rightarrow> ([], None)
           | Some ty \<Rightarrow> let (errs, newTy) = rename_type env ty
                        in (errs, Some newTy));
         (tmErrs, newOptTm) = (case DC_Value dc of
           None \<Rightarrow> ([], None)
           | Some tm \<Rightarrow> let (errs, newTm) = rename_term env tm
                        in (errs, Some newTm));
         newDc = dc \<lparr> DC_Name := newName, DC_Type := newOptTy, DC_Value := newOptTm \<rparr>
     in (nameErrs @ tyErrs @ tmErrs, BabDecl_Const newDc))"
| "rename_declaration env (BabDecl_Function df) =
    (let (nameErrs, newName) = rename_term_name env (DF_Location df) (DF_Name df);
         tyArgNames = DF_TyArgs df;
         tmArgNames = map (\<lambda>(name, _, _). name) (DF_TmArgs df);
         newEnv = add_local_type_names tyArgNames (add_local_term_names tmArgNames env);

         argResults = map (\<lambda>(name, varRef, ty).
                            let (errs, newTy) = rename_type newEnv ty
                            in (errs, (name, varRef, newTy))) (DF_TmArgs df);
         argErrs = concat (map fst argResults);
         newTmArgs = map snd argResults;

         (retTyErrs, newRetTy) = (case DF_ReturnType df of
           None \<Rightarrow> ([], None)
           | Some ty \<Rightarrow> let (errs, newTy) = rename_type newEnv ty
                        in (errs, Some newTy));

         (bodyErrs, newBody) = (case DF_Body df of
           None \<Rightarrow> ([], None)
           | Some stmts \<Rightarrow> let (errs, newStmts) = rename_statements newEnv stmts
                           in (errs, Some newStmts));

         attrResults = map (rename_attribute newEnv) (DF_Attributes df);
         attrErrs = concat (map fst attrResults);
         newAttrs = map snd attrResults;

         newDf = df \<lparr> DF_Name := newName,
                     DF_TmArgs := newTmArgs,
                     DF_ReturnType := newRetTy,
                     DF_Body := newBody,
                     DF_Attributes := newAttrs \<rparr>
     in (nameErrs @ argErrs @ retTyErrs @ bodyErrs @ attrErrs, BabDecl_Function newDf))"
| "rename_declaration env (BabDecl_Datatype dd) =
    (let (nameErrs, newName) = rename_type_name env (DD_Location dd) (DD_Name dd);
         tyArgNames = DD_TyArgs dd;
         newEnv = add_local_type_names tyArgNames env;

         ctorResults = map (\<lambda>(loc, name, optTy).
                             case optTy of
                               None \<Rightarrow> ([], (loc, name, None))
                               | Some ty \<Rightarrow> let (errs, newTy) = rename_type newEnv ty
                                            in (errs, (loc, name, Some newTy))) (DD_Ctors dd);
         ctorErrs = concat (map fst ctorResults);
         newCtors = map snd ctorResults;

         newDd = dd \<lparr> DD_Name := newName, DD_Ctors := newCtors \<rparr>
     in (nameErrs @ ctorErrs, BabDecl_Datatype newDd))"
| "rename_declaration env (BabDecl_Typedef dt) =
    (let (nameErrs, newName) = rename_type_name env (DT_Location dt) (DT_Name dt);
         tyArgNames = DT_TyArgs dt;
         newEnv = add_local_type_names tyArgNames env;

         (defErrs, newDef) = (case DT_Definition dt of
           None \<Rightarrow> ([], None)
           | Some ty \<Rightarrow> let (errs, newTy) = rename_type newEnv ty
                        in (errs, Some newTy));

         newDt = dt \<lparr> DT_Name := newName, DT_Definition := newDef \<rparr>
     in (nameErrs @ defErrs, BabDecl_Typedef newDt))"

(* Main renaming function for a module. *)
(* Note: Caller is responsible for validating the BabPackages themselves (e.g.
   a package shouldn't declare a dependency on a package that doesn't exist). *)
fun rename_module :: "string \<Rightarrow> BabModule \<Rightarrow> BabPackage list \<Rightarrow>
                      RenameError list * BabModule"
  where
"rename_module pkgName module allPkgs =
  (let allImports = Mod_InterfaceImports module @ Mod_ImplementationImports module;
       aliasErrs = check_duplicate_aliases allImports;
       currentPkg = case find (\<lambda>pkg. Pkg_Name pkg = pkgName) allPkgs of
                      Some pkg \<Rightarrow> pkg;
       (interfaceEnvErrs, interfaceEnv) = create_renamer_env pkgName module allPkgs;
       interfaceResults = map (rename_declaration interfaceEnv) (Mod_Interface module);
       interfaceErrs = concat (map fst interfaceResults);
       newInterface = map snd interfaceResults;

       (implImportErrs, implImportEnv) = process_import_list (Mod_ImplementationImports module) pkgName currentPkg allPkgs;
       implEnv = merge_renamer_envs interfaceEnv implImportEnv;
       implResults = map (rename_declaration implEnv) (Mod_Implementation module);
       implErrs = concat (map fst implResults);
       newImplementation = map snd implResults;

       newMod = module \<lparr> Mod_Interface := newInterface,
                        Mod_Implementation := newImplementation \<rparr>
   in (aliasErrs @ interfaceEnvErrs @ interfaceErrs @ implImportErrs @ implErrs, newMod))"

end

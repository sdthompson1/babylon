theory BabLoader
  imports Main "HOL-Library.Char_ord" "HOL-Library.FSet" "../bab/Location" "../bab/BabSyntax" "BabLexer" "BabParser"
begin

(*-----------------------------------------------------------------------------*)
(* Type definitions *)
(*-----------------------------------------------------------------------------*)

(* RawPackage record - this is the basic input to the compiler *)
record RawPackage =
  RP_Name :: string
  RP_Dependencies :: "string list"  (* names of packages that this one depends on *)
  RP_ExportedModules :: "string list"   (* names of modules that are "exported" by this package *)
  RP_Modules :: "(string \<times> string) list"  (* pairs of (module name, unparsed module text) *)

(* LoaderError datatype covering all error cases *)
datatype LoaderError =
  LoaderError_RootModuleNotFound string string  (* package name, module name *)
  | LoaderError_BadDependency string string  (* package name, missing dependency name *)
  | LoaderError_BadExportedModule string string  (* package name, missing exported module name *)
  | LoaderError_WrongModuleName string string  (* modname in RawPackage list, modname in parsed module *)
  | LoaderError_LexError Location
  | LoaderError_ParseError Location
  | LoaderError_PostParseError Location PostParseError
  | LoaderError_ImportNotFound Location string   (* loc, name of the module that wasn't found *)
  | LoaderError_AmbiguousImport Location string "string list"  (* loc, imported module, list of packages containing the module *)

(* Algorithm state for the main loading loop *)
record LoaderState =
  LS_Stack :: "(string \<times> string) list"  (* stack of (package name, module name) pairs *)
  LS_Errors :: "LoaderError list"
  LS_ParsedModules :: "BabModule list"
  LS_RemainingModules :: "(string \<times> string) fset"  (* set of (package name, module name) pairs *)

(*-----------------------------------------------------------------------------*)
(* Functions for validating the raw package list *)
(*-----------------------------------------------------------------------------*)

(* Helper function to validate that all dependencies exist *)
fun validate_dependencies :: "RawPackage list \<Rightarrow> LoaderError list" where
  "validate_dependencies rawPkgs =
    (let allPkgNames = fset_of_list (map RP_Name rawPkgs);
         checkPkg = (\<lambda>pkg.
           let missingDeps = filter (\<lambda>dep. dep |\<notin>| allPkgNames) (RP_Dependencies pkg)
           in map (\<lambda>dep. LoaderError_BadDependency (RP_Name pkg) dep) missingDeps)
     in concat (map checkPkg rawPkgs))"

(* Helper function to validate that all exported modules exist *)
fun validate_exported_modules :: "RawPackage list \<Rightarrow> LoaderError list" where
  "validate_exported_modules rawPkgs =
    (let checkPkg = (\<lambda>pkg.
           let moduleNames = fset_of_list (map fst (RP_Modules pkg));
               missingExports = filter (\<lambda>module. module |\<notin>| moduleNames) (RP_ExportedModules pkg)
           in map (\<lambda>module. LoaderError_BadExportedModule (RP_Name pkg) module) missingExports)
     in concat (map checkPkg rawPkgs))"

(*-----------------------------------------------------------------------------*)
(* Functions for finding things in the raw package list *)
(*-----------------------------------------------------------------------------*)

(* Helper function to find a package by name *)
fun find_package :: "string \<Rightarrow> RawPackage list \<Rightarrow> RawPackage option" where
  "find_package pkgName [] = None"
| "find_package pkgName (pkg # rest) =
    (if RP_Name pkg = pkgName then
      Some pkg
    else
      find_package pkgName rest)"

(* Helper function to get package dependencies *)
fun get_package_dependencies :: "string \<Rightarrow> RawPackage list \<Rightarrow> string list" where
  "get_package_dependencies pkgName rawPkgs =
    (case find_package pkgName rawPkgs of
      None \<Rightarrow> []
      | Some pkg \<Rightarrow> RP_Dependencies pkg)"

(* Helper function to find a module in RawPackage list *)
fun find_module_in_raw_packages :: "string \<Rightarrow> string \<Rightarrow> RawPackage list \<Rightarrow> string option" where
  "find_module_in_raw_packages pkgName modName rawPkgs =
    (case find_package pkgName rawPkgs of
      None \<Rightarrow> None
      | Some pkg \<Rightarrow>
        (case find (\<lambda>(name, _). name = modName) (RP_Modules pkg) of
          Some (_, text) \<Rightarrow> Some text
          | None \<Rightarrow> None))"

(* Helper function to check if a module is exported by a package *)
fun is_module_exported :: "string \<Rightarrow> string \<Rightarrow> RawPackage list \<Rightarrow> bool" where
  "is_module_exported pkgName modName rawPkgs =
    (case find_package pkgName rawPkgs of
      None \<Rightarrow> False
      | Some pkg \<Rightarrow> List.member (RP_ExportedModules pkg) modName)"

(*-----------------------------------------------------------------------------*)
(* Running the lexer and parser on a module *)
(*-----------------------------------------------------------------------------*)

(* Helper function to convert raw text to BabModule *)
fun parse_module_text :: "string \<Rightarrow> string \<Rightarrow> string \<Rightarrow>
                          (LoaderError list, BabModule) sum" where
  "parse_module_text pkgName modName text =
    (case lex (pkgName @ '':'' @ modName @ ''.b'') text of
      LR_Error lexLoc \<Rightarrow> Inl [LoaderError_LexError lexLoc]
      | LR_Success tokens \<Rightarrow>
        (case run_parser parse_module (pkgName @ '':'' @ modName @ ''.b'') tokens of
          PR_Success module _ _ \<Rightarrow>
            (let postParseErrors = map (\<lambda>(loc, ppe). LoaderError_PostParseError loc ppe) (post_parse_module module);
                 wrongModNameError = if Mod_Name module \<noteq> modName then
                                       [LoaderError_WrongModuleName modName (Mod_Name module)]
                                     else [];
                 allErrors = postParseErrors @ wrongModNameError
             in if allErrors = [] then
                  let fullModName = pkgName @ '':'' @ modName;
                      renamedModule = module \<lparr> Mod_Name := fullModName \<rparr>
                  in Inr renamedModule
                else
                  Inl allErrors)
          | PR_Error parseLoc \<Rightarrow> Inl [LoaderError_ParseError parseLoc]))"

(*-----------------------------------------------------------------------------*)
(* Module loading and import processing logic *)
(*-----------------------------------------------------------------------------*)

(* Helper function to find module in current package or dependencies *)
(* If the imported module is found in the current package, then use that; otherwise,
   search dependency packages -- the imported module must be exported by exactly one
   of the dependencies in that case. *)
fun find_module_for_import :: "string \<Rightarrow> string \<Rightarrow> Location \<Rightarrow> RawPackage list \<Rightarrow>
                               (LoaderError, string \<times> string) sum" where
  "find_module_for_import currentPkgName importModName loc rawPkgs =
    (case find_module_in_raw_packages currentPkgName importModName rawPkgs of
      Some _ \<Rightarrow> Inr (currentPkgName, importModName)
      | None \<Rightarrow>
        (let deps = get_package_dependencies currentPkgName rawPkgs;
             findInDep = (\<lambda>depPkg.
               if is_module_exported depPkg importModName rawPkgs then
                 Some depPkg
               else
                 None);
             matchingDeps = List.map_filter findInDep deps
         in case matchingDeps of
              [] \<Rightarrow> Inl (LoaderError_ImportNotFound loc importModName)
              | [depPkg] \<Rightarrow> Inr (depPkg, importModName)
              | multiple \<Rightarrow> Inl (LoaderError_AmbiguousImport loc importModName multiple)
         ))"

(* Helper function to process imports and update them with package prefixes *)
fun process_imports :: "string \<Rightarrow> RawPackage list \<Rightarrow> BabImport list \<Rightarrow>
                        LoaderError list \<times> BabImport list \<times> (string \<times> string) list" where
  "process_imports pkgName rawPkgs imports =
    (let processImport = (\<lambda>imp.
           case find_module_for_import pkgName (Imp_ModuleName imp) (Imp_Location imp) rawPkgs of
             Inl err \<Rightarrow> (Some err, imp, None)
             | Inr (foundPkg, foundMod) \<Rightarrow>
                 let fullModName = foundPkg @ '':'' @ foundMod;
                     updatedImp = imp \<lparr> Imp_ModuleName := fullModName \<rparr>
                 in (None, updatedImp, Some (foundPkg, foundMod)));
         results = map processImport imports;
         errors = List.map_filter (\<lambda>(err, _, _). err) results;
         updatedImports = map (\<lambda>(_, imp, _). imp) results;
         validPkgMods = List.map_filter (\<lambda>(_, _, pkgMod). pkgMod) results
     in (errors, updatedImports, validPkgMods))"

(* Helper function to process a module that was found *)
fun process_found_module :: "RawPackage list \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> LoaderState \<Rightarrow> LoaderState" where
  "process_found_module rawPkgs pkgName modName moduleText state =
    (case parse_module_text pkgName modName moduleText of
      Inl parseErrors \<Rightarrow>
        state \<lparr> LS_Errors := parseErrors @ LS_Errors state \<rparr>
      | Inr parsedModule \<Rightarrow>
        (let (interfaceErrors, updatedInterfaceImports, interfaceValidImports) =
               process_imports pkgName rawPkgs (Mod_InterfaceImports parsedModule);
             (implErrors, updatedImplementationImports, implValidImports) =
               process_imports pkgName rawPkgs (Mod_ImplementationImports parsedModule);
             finalModule = parsedModule \<lparr> Mod_InterfaceImports := updatedInterfaceImports,
                                            Mod_ImplementationImports := updatedImplementationImports \<rparr>;
             newParsedModules = finalModule # LS_ParsedModules state;
             allValidImports = interfaceValidImports @ implValidImports;
             newStack = allValidImports @ LS_Stack state;
             allErrors = interfaceErrors @ implErrors
         in state \<lparr>
              LS_Stack := newStack,
              LS_Errors := allErrors @ LS_Errors state,
              LS_ParsedModules := newParsedModules
            \<rparr>))"

(* Helper function for processing a module that needs to be loaded *)
(* Note: All modules reaching this function are guaranteed to exist in rawPkgs.
   The root module is checked upfront in load_packages, and imported modules are only
   added to the stack if they exist (via find_module_for_import). *)
fun process_module :: "RawPackage list \<Rightarrow> string \<Rightarrow> string \<Rightarrow> LoaderState \<Rightarrow> LoaderState" where
  "process_module rawPkgs pkgName modName state =
    (let moduleText = the (find_module_in_raw_packages pkgName modName rawPkgs);
         processedState = process_found_module rawPkgs pkgName modName moduleText state;
         remainingWithoutCurrent = LS_RemainingModules state |-| {|(pkgName, modName)|}
     in processedState \<lparr> LS_RemainingModules := remainingWithoutCurrent \<rparr>)"

(* Main loading algorithm - initial state *)
fun initialize_loader_state :: "RawPackage list \<Rightarrow> string \<Rightarrow> string \<Rightarrow> LoaderState" where
  "initialize_loader_state rawPkgs rootPkgName rootModName =
    (let allModules = concat (map (\<lambda>pkg. map (\<lambda>(modName, _). (RP_Name pkg, modName)) (RP_Modules pkg)) rawPkgs)
     in \<lparr>
       LS_Stack = [(rootPkgName, rootModName)],
       LS_Errors = [],
       LS_ParsedModules = [],
       LS_RemainingModules = fset_of_list allModules
     \<rparr>)"

(* Main loading algorithm - single step *)
fun loader_step :: "RawPackage list \<Rightarrow> LoaderState \<Rightarrow> LoaderState" where
  "loader_step rawPkgs state =
    (case LS_Stack state of
      [] \<Rightarrow> state
      | (pkgName, modName) # restStack \<Rightarrow>
        (let poppedState = state \<lparr> LS_Stack := restStack \<rparr>
         in if (pkgName, modName) |\<notin>| LS_RemainingModules state then
              poppedState
            else
              process_module rawPkgs pkgName modName poppedState))"

(* loader_step removes the top of stack from the LS_RemainingModules set *)
lemma loader_step_remaining:
  assumes "LS_Stack state = (pkgName, modName) # restStack"
    and "(pkgName, modName) |\<in>| LS_RemainingModules state"
  shows "LS_RemainingModules (loader_step rawPkgs state) =
          LS_RemainingModules state |-| {|(pkgName, modName)|}"
proof -
  have "loader_step rawPkgs state =
        (let poppedState = state \<lparr> LS_Stack := restStack \<rparr>
         in process_module rawPkgs pkgName modName poppedState)"
    using assms(1) assms(2) by simp
  hence "LS_RemainingModules (loader_step rawPkgs state) =
         LS_RemainingModules (process_module rawPkgs pkgName modName (state \<lparr> LS_Stack := restStack \<rparr>))"
    by metis
  also have "... = LS_RemainingModules (state \<lparr> LS_Stack := restStack \<rparr>) |-| {|(pkgName, modName)|}"
    by simp
  also have "... = LS_RemainingModules state |-| {|(pkgName, modName)|}"
    by simp
  finally show ?thesis .
qed

(* Helper function to run the loader until completion *)
function run_loader_steps :: "RawPackage list \<Rightarrow> LoaderState \<Rightarrow> LoaderState" where
  "run_loader_steps rawPkgs state =
    (if LS_Stack state = [] then
       state
     else
       run_loader_steps rawPkgs (loader_step rawPkgs state))"

  by pat_completeness auto

termination
proof (relation "inv_image (lex_prod less_than less_than) (\<lambda>(rawPkgs, state). (fcard (LS_RemainingModules state), length (LS_Stack state)))")
  show "wf (inv_image (lex_prod less_than less_than) (\<lambda>(rawPkgs, state). (fcard (LS_RemainingModules state), length (LS_Stack state))))"
    by auto
next
  fix rawPkgs :: "RawPackage list" and state :: "LoaderState"
  assume "LS_Stack state \<noteq> []"
  show "((rawPkgs, loader_step rawPkgs state), (rawPkgs, state))
        \<in> inv_image (lex_prod less_than less_than) (\<lambda>(rawPkgs, state). (fcard (LS_RemainingModules state), length (LS_Stack state)))"
  proof (cases "LS_Stack state")
    case Nil
    then show ?thesis using \<open>LS_Stack state \<noteq> []\<close> by contradiction
  next
    case (Cons pair restStack)
    obtain pkgName modName where pair_def: "pair = (pkgName, modName)" by fastforce
    show ?thesis
    proof (cases "(pkgName, modName) |\<in>| LS_RemainingModules state")
      case False
      (* Module already processed - stack decreases but remaining modules stay same *)
      have "LS_RemainingModules (loader_step rawPkgs state) = LS_RemainingModules state"
        using False Cons pair_def by simp
      moreover have "length (LS_Stack (loader_step rawPkgs state)) < length (LS_Stack state)"
        using False Cons pair_def by simp
      ultimately show ?thesis by simp
    next
      case True
      have "LS_RemainingModules (loader_step rawPkgs state) = LS_RemainingModules state |-| {|(pkgName, modName)|}"
        using True Cons pair_def loader_step_remaining by blast
      have "fcard (LS_RemainingModules state |-| {|(pkgName, modName)|}) < fcard (LS_RemainingModules state)"
        by (meson True fcard_fminus1_less)
      hence "fcard (LS_RemainingModules (loader_step rawPkgs state)) < fcard (LS_RemainingModules state)"
        using \<open>LS_RemainingModules (loader_step rawPkgs state) = LS_RemainingModules state |-| {|(pkgName, modName)|}\<close> by simp
      thus ?thesis by simp
    qed
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Main entry point *)
(*-----------------------------------------------------------------------------*)

fun load_packages :: "RawPackage list \<Rightarrow> string \<Rightarrow> string \<Rightarrow>
                      (LoaderError list, BabModule list) sum" where
  "load_packages rawPkgs rootPkgName rootModName =
    (let depErrors = validate_dependencies rawPkgs;
         exportErrors = validate_exported_modules rawPkgs;
         validationErrors = depErrors @ exportErrors
     in case find_module_in_raw_packages rootPkgName rootModName rawPkgs of
          None \<Rightarrow> Inl (validationErrors @ [LoaderError_RootModuleNotFound rootPkgName rootModName])
          | Some _ \<Rightarrow>
            (let finalState = run_loader_steps rawPkgs (initialize_loader_state rawPkgs rootPkgName rootModName);
                 allErrors = validationErrors @ LS_Errors finalState
             in if allErrors = [] then
                  Inr (LS_ParsedModules finalState)
                else
                  Inl allErrors))"

end

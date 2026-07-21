theory CodeExport
  imports
    ShowError
    "HOL-Library.Code_Binary_Nat"

    (* TODO: maybe explore other performance options, e.g. Code_Target_Numeral, or
       red-black tree implementations of fmaps. Deferred for now, as setting these
       kinds of things up might be difficult, and performance is not a priority
       right now anyway. *)

begin

(* Break circular dependency between the generated Set and List modules
   (Haskell does not allow circular imports). Map both to the same Haskell
   module name so they're in one file. *)
code_identifier
  code_module Set \<rightharpoonup> (Haskell) Set_Impl
  | code_module List \<rightharpoonup> (Haskell) Set_Impl

(* Code Export *)

(* Result of a compiler run: either success, or a list of human-readable
   error messages. *)
datatype CompileResult =
  CR_Success
  | CR_Errors "string list"

(* Main compiler entry point for testing.

   The input is a list of (module name, module source text) pairs; the first
   module in the list is the root module for compilation purposes. All the
   modules are placed into a single package named "main".

   This runs the front end (lexer, parser, loader, renamer), and then, if that
   succeeds, elaborates all the modules to Core (which includes typechecking
   them). *)
fun run_compiler :: "(string \<times> string) list \<Rightarrow> CompileResult"
  where
"run_compiler [] = CR_Errors [''no input modules'']"
| "run_compiler ((rootModName, rootModText) # otherModules) =
  (let rawPkg = \<lparr> RP_Name = ''main'',
                  RP_Dependencies = [],
                  RP_ExportedModules = [],
                  RP_Modules = (rootModName, rootModText) # otherModules \<rparr>
   in case compiler_front_end [rawPkg] ''main'' rootModName of
        Inl errs \<Rightarrow> CR_Errors (map frontend_error_to_string errs)
      | Inr babModules \<Rightarrow>
          (case elab_program babModules of
             Inl err \<Rightarrow> CR_Errors (pipeline_error_to_strings err)
           | Inr _ \<Rightarrow> CR_Success))"

export_code run_compiler CR_Success CR_Errors
  in Haskell

end

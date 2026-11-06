theory CodeExport
  imports
    ShowError
    "../ghost_erasure/EraseGhost"
    "../core_passes/MatchCompilePass"
    "../minic/MiniCPrint"
    "../minic/MiniCExample"
    "../codegen/SizeBound"
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

(* The pointer size bound P at which the static size check of
   codegen/SizeBound.thy is run (minic/DESIGN.md, section 3.2): the
   theorems about the generated code take enc_ptr_size enc <= P as a
   hypothesis, so the generated code is covered on every target whose
   pointers are at most this many bytes. This is the only place where the
   bound is a literal. *)
definition codegen_ptr_size_bound :: nat where
  "codegen_ptr_size_bound = 8"

(* The size check's errors in the user's terms. *)
fun size_error_to_strings :: "SizeError \<Rightarrow> string list" where
  "size_error_to_strings (SE_DatatypeCycle []) =
     [''internal compiler error: datatype dependency analysis failed'']"
| "size_error_to_strings (SE_DatatypeCycle ds) =
     [''recursive datatypes are not supported: '' @ ShowError.intercalate '', '' (map quote ds)]"
| "size_error_to_strings (SE_TooManyCtors d) =
     [''datatype '' @ quote d @ '' has more than 4294967296 constructors'']"
| "size_error_to_strings (SE_CallCycle []) =
     [''internal compiler error: call graph analysis failed (a call to an unknown function)'']"
| "size_error_to_strings (SE_CallCycle fs) =
     [''recursive functions are not supported: '' @ ShowError.intercalate '', '' (map quote fs)]"
| "size_error_to_strings (SE_BodyNotTyped f) =
     [''internal compiler error: the body of function '' @ quote f @ '' does not typecheck'']"
| "size_error_to_strings (SE_SizeTooLarge f ty bounds) =
     [''in function '' @ quote f @ '', the type '' @ quote (core_type_to_string ty)
      @ '' may need more than 18446744073709551615 bytes''
      @ (if bounds = [] then []
         else '' (with the type parameters bounded by ''
              @ ShowError.intercalate '', ''
                  (map (\<lambda>(v, n). v @ '' <= '' @ nat_to_string n @ '' bytes'') bounds)
              @ '')'')]"
| "size_error_to_strings (SE_GlobalTooLarge g ty) =
     [''the type '' @ quote (core_type_to_string ty) @ '' of the global '' @ quote g
      @ '' needs more than 18446744073709551615 bytes'']"

(* Main compiler entry point for testing.

   The input is a list of (module name, module source text) pairs; the first
   module in the list is the root module for compilation purposes. All the
   modules are placed into a single package named "main".

   This runs the front end (lexer, parser, loader, renamer), and then, if that
   succeeds, elaborates all the modules to Core (which includes typechecking
   them), runs the whole-program link, normalizes the linked module
   (normalize_module), erases ghost code, compiles the pattern matches to flat ones
   (match_compile_module), and runs the static checks of the code generator on it
   (sizeable_check).

   The link should always succeed on elaborator output, and the hypothesis of the
   match compilation pass (every non-flat match has a variable scrutinee) should
   also always be true, but neither of these facts is proved yet. Therefore, they
   are checked at runtime below, and an internal compiler error is reported if
   a check fails. The acyclicity parts of sizeable_check cannot fail on
   elaborator output either, but the size bound computed by sizeable_check is a
   property of the program and does genuinely have to be checked. *)
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
           | Inr ps \<Rightarrow> 
              (case whole_program_link ps of
                Inl err \<Rightarrow> CR_Errors (whole_program_link_error_to_strings err)
              | Inr linked \<Rightarrow>
                  (let erased = erase_ghost_module (normalize_module linked)
                   in if \<not> core_module_match_scrutinees_ok erased
                      then CR_Errors [''internal error: match scrutinee is not a variable'']
                      else (case sizeable_check codegen_ptr_size_bound
                                   (match_compile_module erased) of
                              Some err \<Rightarrow> CR_Errors (size_error_to_strings err)
                            | None \<Rightarrow> CR_Success)))))"

(* Also exported: the MiniC-to-C printer (print_program, with its options:
   default_print_opts, and the two ways of printing MS_Uninit), the check
   that no extern C name clashes with a mangled name (extern_clashes, with
   extern_clash_message for reporting), and the hand-written MiniC example
   programs with the stdout the MiniC interpreter computes for them
   (minic_examples), which the driver (Main.hs, option --minic) checks and
   prints to a .c file for the C-level check described in minic/DESIGN.md.
   There is no code generator yet (stage 5), so these are the only MiniC
   programs. *)
export_code run_compiler CR_Success CR_Errors
  print_program default_print_opts PO_Uninit_update UP_Memset UP_Omit
  extern_clashes extern_clash_message minic_examples
  in Haskell

end

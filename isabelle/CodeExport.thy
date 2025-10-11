theory CodeExport
  imports
    FrontEnd
    "HOL-Library.Code_Binary_Nat"
    "HOL-Library.RBT_Set"

begin

(* Break circular dependency between Set and RBT_Set *)
(* Map both to the same Haskell module name so they're in one file *)
code_identifier
  code_module Set \<rightharpoonup> (Haskell) Set_Impl
  | code_module RBT_Set \<rightharpoonup> (Haskell) Set_Impl

(* Code Export *)

datatype CompileResult = 
  CR_Success          (* Successful compilation *)
  | CR_LexError       (* Lexical error OR loader problem (module not found, etc.) *)
  | CR_ParseError     (* Parse error *)
  | CR_RenameError    (* Renamer error *)

(* Function to convert front-end errors to a compile result *)
fun frontend_errors_to_result :: "FrontEndError list \<Rightarrow> CompileResult" where
  "frontend_errors_to_result [] = CR_LexError"
| "frontend_errors_to_result (FrontEndError_Loader x # _) =
  (case x of
    LoaderError_ParseError _ \<Rightarrow> CR_ParseError
    | LoaderError_PostParseError _ _ \<Rightarrow> CR_ParseError
    | _ \<Rightarrow> CR_LexError
  )"
| "frontend_errors_to_result (FrontEndError_Renamer _ # _) = CR_RenameError"


(* Main compiler entry point for testing *)
fun run_compiler :: "string \<Rightarrow> CompileResult"
  where
"run_compiler str =
  (let rawPkg = \<lparr> RP_Name = ''main'',
                  RP_Dependencies = [],
                  RP_ExportedModules = [],
                  RP_Modules = [(''Main'', str)] \<rparr>;
       result = compiler_front_end [rawPkg] ''main'' ''Main''
   in case result of
        Inr _ \<Rightarrow> CR_Success
        | Inl errs \<Rightarrow> frontend_errors_to_result errs)"

export_code run_compiler CR_Success CR_LexError CR_ParseError CR_RenameError
  in Haskell

end

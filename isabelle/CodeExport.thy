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
    | LoaderError_RootModuleNotFound _ _ \<Rightarrow> CR_RenameError
    | LoaderError_WrongModuleName _ _ \<Rightarrow> CR_RenameError
    | _ \<Rightarrow> CR_LexError
  )"
| "frontend_errors_to_result (FrontEndError_Renamer _ # _) = CR_RenameError"


(* Main compiler entry point for testing *)
fun run_compiler :: "string \<Rightarrow> CompileResult"
  where
"run_compiler str =
  (let testModule = ''module Test'' @ [CHR 10] @
                    ''interface'' @ [CHR 10] @
                    ''{'' @ [CHR 10] @
                    ''    const I32_MIN: i32 = 0;'' @ [CHR 10] @
                    ''    const I32_MAX: i32 = 0;'' @ [CHR 10] @
                    ''    const U64_MAX: u64 = 0;'' @ [CHR 10] @
                    ''    extern function print_i8 (x: i8);'' @ [CHR 10] @
                    ''    extern function print_i16(x: i16);'' @ [CHR 10] @
                    ''    extern function print_i32(x: i32);'' @ [CHR 10] @
                    ''    extern function print_i64(x: i64);'' @ [CHR 10] @
                    ''    extern function print_u8 (x: u8);'' @ [CHR 10] @
                    ''    extern function print_u16(x: u16);'' @ [CHR 10] @
                    ''    extern function print_u32(x: u32);'' @ [CHR 10] @
                    ''    extern function print_u64(x: u64);'' @ [CHR 10] @
                    ''    extern function print_bool(b: bool);'' @ [CHR 10] @
                    ''    ghost function valid_string(s: u8[]): bool;'' @ [CHR 10] @
                    ''    extern function print_string(s: u8[]);'' @ [CHR 10] @
                    ''    ghost function default<T>(): T;'' @ [CHR 10] @
                    ''    extern function alloc_array<T>(ref array: T[*], dim: u64);'' @ [CHR 10] @
                    ''    extern function free_array<T>(ref array: T[*]);'' @ [CHR 10] @
                    ''    extern function alloc_2d_array<T>(ref array: T[*,*], dim0: u64, dim1: u64);'' @ [CHR 10] @
                    ''    extern function free_2d_array<T>(ref array: T[*,*]);'' @ [CHR 10] @
                    ''    extern function alloc_3d_array<T>(ref array: T[*,*,*], dim0: u64, dim1: u64, dim2: u64);'' @ [CHR 10] @
                    ''    extern function free_3d_array<T>(ref array: T[*,*,*]);'' @ [CHR 10] @
                    ''    extern type AllocTest (allocated_always);'' @ [CHR 10] @
                    ''    datatype MaybeAllocTest = MA_Nothing | MA_Just(AllocTest);    '' @ [CHR 10] @
                    ''    extern function allocate_alloc_test(ref r: MaybeAllocTest)'' @ [CHR 10] @
                    ''    extern function free_alloc_test(ref r: MaybeAllocTest)'' @ [CHR 10] @
                    ''}'' @ [CHR 10];
       rawPkg = \<lparr> RP_Name = ''main'',
                  RP_Dependencies = [],
                  RP_ExportedModules = [],
                  RP_Modules = [(''Main'', str), (''Test'', testModule)] \<rparr>;
       result = compiler_front_end [rawPkg] ''main'' ''Main''
   in case result of
        Inr _ \<Rightarrow> CR_Success
        | Inl errs \<Rightarrow> frontend_errors_to_result errs)"

export_code run_compiler CR_Success CR_LexError CR_ParseError CR_RenameError
  in Haskell

end

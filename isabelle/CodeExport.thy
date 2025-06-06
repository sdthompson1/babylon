theory CodeExport
  imports BabParser BabLexer "HOL-Library.Code_Binary_Nat"

begin

(* Code Export *)

datatype CompileResult = CR_Success | CR_LexError | CR_ParseError

fun run_compiler :: "string \<Rightarrow> CompileResult"
  where
"run_compiler str =
  (case lex ''Main'' str of
    LR_Success tokens \<Rightarrow> 
      (case run_parser parse_module ''stdin'' tokens of
        PR_Success m _ _ \<Rightarrow>
          (case post_parse_module m of
            [] \<Rightarrow> CR_Success
            | _ \<Rightarrow> CR_ParseError)
      | PR_Error _ \<Rightarrow> CR_ParseError)
  | LR_Error _ \<Rightarrow> CR_LexError)"

export_code run_compiler CR_Success CR_LexError CR_ParseError in Haskell

end

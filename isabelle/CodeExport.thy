theory CodeExport
  imports BabParser BabLexer "HOL-Library.Code_Binary_Nat"

begin

(* Code Export *)

(* 0 = Success *)
(* 1 = Lex error *)
(* 2 = Parse error *)
fun run_compiler :: "string \<Rightarrow> nat"
  where
"run_compiler str =
  (case lex ''Main'' str of
    LR_Success tokens \<Rightarrow> 
      (case run_parser parse_module ''stdin'' tokens of
        PR_Success m _ _ \<Rightarrow>
          (case post_parse_module m of
            [] \<Rightarrow> 0
            | _ \<Rightarrow> 2)
      | PR_Error _ \<Rightarrow> 2)
  | LR_Error _ \<Rightarrow> 1)"

export_code run_compiler in Haskell

end

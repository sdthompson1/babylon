theory CodeExport
  imports BabParser BabLexer "HOL-Library.Code_Binary_Nat"

begin

(* Code Export *)

fun lex_test :: "string \<Rightarrow> bool"
  where
"lex_test str =
  (case lex ''Main'' str of
    LR_Success _ \<Rightarrow> True
  | LR_Error _ \<Rightarrow> False)"

fun parse_test :: "string \<Rightarrow> bool"
  where
"parse_test str = 
  (case lex ''Main'' str of
    LR_Success tokens \<Rightarrow> 
      (case run_parser (parse_type \<then> eof) ''stdin'' tokens of
        PR_Success _ _ _ \<Rightarrow> True
      | PR_Error _ \<Rightarrow> False)
  | LR_Error _ \<Rightarrow> False)"

export_code parse_test lex_test in Haskell

end

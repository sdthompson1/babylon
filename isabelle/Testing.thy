theory Testing
  imports Main BabSyntax BabLexer BabParser
begin

(* testing *)

definition test_parser :: "'a Parser \<Rightarrow> string \<Rightarrow> 'a ParseResult"
  where
"test_parser p text =
  (case lex ''Test.b'' text of
    LR_Success result \<Rightarrow> run_parser p ''Test.b'' result
    | LR_Error loc \<Rightarrow> PR_Error loc)"

(* value "lex ''Test.b'' ''0x10000000000000000''" *)

(* value "test_parser (parse_term) ''1''" *)

value "test_parser (parse_module) ''module MRange2 interface {} function test() { assume 1 ; }''"

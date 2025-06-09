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

definition test_post_parse :: "string \<Rightarrow> (Location \<times> PostParseError) list" where
"test_post_parse text =
  (case lex ''Test.b'' text of
    LR_Success result \<Rightarrow>
      (case run_parser parse_module ''Test.b'' result of
        PR_Success module _ _ \<Rightarrow> post_parse_module module
        | _ \<Rightarrow> [])
    | LR_Error loc \<Rightarrow> [])"

(* value "lex ''Test.b'' ''0x10000000000000000''" *)


value "test_parser parse_module ''module C
interface {}

function test()
{ 
    1 + 2();
}''"

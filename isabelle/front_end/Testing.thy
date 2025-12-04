theory Testing
  imports Main "../base/BabSyntax" "../loader/BabLexer" "../loader/BabParser" "../loader/BabLoader" "../renamer/BabRenamer"
begin

(* Scratch space for testing *)

(*
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

value "test_parser parse_term ''{a=1,b=2,c=3,4,5,6,}''"

value "test_parser parse_module ''module Main
interface {}
  const c = match 1 { case (2) => 3 };

''"
*)


definition loadResult :: "(LoaderError list, BabModule list) sum" where
"loadResult = load_packages [\<lparr> RP_Name = ''main'', RP_Dependencies = [], RP_ExportedModules = [],
RP_Modules = [(''Main'',
''module Main interface {}'' @ [CHR 10] @
''function f() {'' @ [CHR 10] @
''assert forall (x: i32) true { }'' @ [CHR 10] @
''}''
)]\<rparr>] ''main'' ''Main''"

value loadResult

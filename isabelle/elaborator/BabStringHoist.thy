(* String-literal hoisting pass.

   The problem this is solving is the following: In the Babylon language, string
   literals are read-only lvalues. However, Core only allows array literals (not
   string literals) and array literals are not lvalues. Therefore, there is no
   direct way to elaborate Babylon string literals to Core.

   It turns out that this only matters in two places:
    - the initializer of a "Ref" VarDecl statement; and
    - the scrutinee of a match statement (so that "ref" patterns can bind into it).

   Our solution is that if a string literal is found in either of those positions,
   then we create a new global constant (with a name like ModName.str@@0), holding
   the string, and then replace the string literal in the source code with a
   reference to that new constant. A named variable reference (CoreTm_Var) is an
   lvalue, so this preserves the intended semantics, without needing to introduce
   a separate "string literal" concept into Core.
*)

theory BabStringHoist
  imports "../bab/BabSyntax" "../util/NatToString"
begin

(* Make the name and declaration for a hoisted string-literal constant.
   The declaration has no type annotation: the constant's type (u8[N]) is
   inferred from the literal by the elaborator. *)
definition make_hoisted_const :: "string \<Rightarrow> nat \<Rightarrow> Location \<Rightarrow> string \<Rightarrow> string \<times> DeclConst"
  where
"make_hoisted_const modName ctr loc str =
  (let name = modName @ ''.str@@'' @ nat_to_string ctr
   in (name, \<lparr> DC_Location = loc,
               DC_Name = name,
               DC_Type = None,
               DC_Value = Some (BabTm_Literal loc (BabLit_String str)),
               DC_Ghost = NotGhost \<rparr>))"

(* If the base of the projection spine of tm is a string literal, replace it
   with a reference to a fresh global constant, returning the rewritten term,
   the new constant's declaration, and the advanced counter. Any other term is
   returned unchanged. *)
fun hoist_string_base :: "string \<Rightarrow> nat \<Rightarrow> BabTerm \<Rightarrow> BabTerm \<times> DeclConst list \<times> nat"
  where
"hoist_string_base modName ctr (BabTm_Literal loc (BabLit_String str)) =
    (case make_hoisted_const modName ctr loc str of
      (name, dc) \<Rightarrow> (BabTm_Name loc name [], [dc], ctr + 1))"
| "hoist_string_base modName ctr (BabTm_ArrayProj loc base idxs) =
    (case hoist_string_base modName ctr base of
      (base', dcs, ctr') \<Rightarrow> (BabTm_ArrayProj loc base' idxs, dcs, ctr'))"
| "hoist_string_base modName ctr (BabTm_RecordProj loc base fld) =
    (case hoist_string_base modName ctr base of
      (base', dcs, ctr') \<Rightarrow> (BabTm_RecordProj loc base' fld, dcs, ctr'))"
| "hoist_string_base modName ctr (BabTm_TupleProj loc base idx) =
    (case hoist_string_base modName ctr base of
      (base', dcs, ctr') \<Rightarrow> (BabTm_TupleProj loc base' idx, dcs, ctr'))"
| "hoist_string_base modName ctr tm = (tm, [], ctr)"

(* Hoist string literals out of the lvalue positions of a statement (list).
   Returns the rewritten statement(s), the declarations of any fresh
   constants, and the advanced counter. *)
fun hoist_statement :: "string \<Rightarrow> nat \<Rightarrow> BabStatement
                        \<Rightarrow> BabStatement \<times> DeclConst list \<times> nat"
and hoist_statements :: "string \<Rightarrow> nat \<Rightarrow> BabStatement list
                         \<Rightarrow> BabStatement list \<times> DeclConst list \<times> nat"
and hoist_match_arms :: "string \<Rightarrow> nat \<Rightarrow> (BabPattern \<times> BabStatement list) list
                         \<Rightarrow> (BabPattern \<times> BabStatement list) list \<times> DeclConst list \<times> nat"
  where
(* "Ref" VarDecl statement: the initializer is an lvalue position. ("Var" VarDecls,
   and "Ref" VarDecls without an initializer, are left unchanged.) *)
"hoist_statement modName ctr (BabStmt_VarDecl loc var Ref optTy (Some tm)) =
    (case hoist_string_base modName ctr tm of
      (tm', dcs, ctr') \<Rightarrow> (BabStmt_VarDecl loc var Ref optTy (Some tm'), dcs, ctr'))"

(* Match statement: the scrutinee is an lvalue position; the arm bodies are
   traversed recursively. *)
| "hoist_statement modName ctr (BabStmt_Match loc scrut arms) =
    (case hoist_string_base modName ctr scrut of
      (scrut', dcs1, ctr1) \<Rightarrow>
        (case hoist_match_arms modName ctr1 arms of
          (arms', dcs2, ctr2) \<Rightarrow> (BabStmt_Match loc scrut' arms', dcs1 @ dcs2, ctr2)))"

(* Compound statements: traverse the nested statement lists. *)
| "hoist_statement modName ctr (BabStmt_Assert loc optTm proofStmts) =
    (case hoist_statements modName ctr proofStmts of
      (proofStmts', dcs, ctr') \<Rightarrow> (BabStmt_Assert loc optTm proofStmts', dcs, ctr'))"
| "hoist_statement modName ctr (BabStmt_If loc cond thenStmts elseStmts) =
    (case hoist_statements modName ctr thenStmts of
      (thenStmts', dcs1, ctr1) \<Rightarrow>
        (case hoist_statements modName ctr1 elseStmts of
          (elseStmts', dcs2, ctr2) \<Rightarrow>
            (BabStmt_If loc cond thenStmts' elseStmts', dcs1 @ dcs2, ctr2)))"
| "hoist_statement modName ctr (BabStmt_While loc cond attrs bodyStmts) =
    (case hoist_statements modName ctr bodyStmts of
      (bodyStmts', dcs, ctr') \<Rightarrow> (BabStmt_While loc cond attrs bodyStmts', dcs, ctr'))"
| "hoist_statement modName ctr (BabStmt_Ghost loc inner) =
    (case hoist_statement modName ctr inner of
      (inner', dcs, ctr') \<Rightarrow> (BabStmt_Ghost loc inner', dcs, ctr'))"

(* All other statements contain no lvalue positions and no nested statements. *)
| "hoist_statement modName ctr stmt = (stmt, [], ctr)"

| "hoist_statements modName ctr [] = ([], [], ctr)"
| "hoist_statements modName ctr (stmt # stmts) =
    (case hoist_statement modName ctr stmt of
      (stmt', dcs1, ctr1) \<Rightarrow>
        (case hoist_statements modName ctr1 stmts of
          (stmts', dcs2, ctr2) \<Rightarrow> (stmt' # stmts', dcs1 @ dcs2, ctr2)))"

| "hoist_match_arms modName ctr [] = ([], [], ctr)"
| "hoist_match_arms modName ctr ((pat, armStmts) # arms) =
    (case hoist_statements modName ctr armStmts of
      (armStmts', dcs1, ctr1) \<Rightarrow>
        (case hoist_match_arms modName ctr1 arms of
          (arms', dcs2, ctr2) \<Rightarrow> ((pat, armStmts') # arms', dcs1 @ dcs2, ctr2)))"

(* Hoist string literals out of a declaration. Only function bodies contain
   statements; all other declarations are returned unchanged. *)
fun hoist_declaration :: "string \<Rightarrow> nat \<Rightarrow> BabDeclaration
                          \<Rightarrow> BabDeclaration \<times> DeclConst list \<times> nat"
  where
"hoist_declaration modName ctr (BabDecl_Function df) =
    (case DF_Body df of
      None \<Rightarrow> (BabDecl_Function df, [], ctr)
      | Some body \<Rightarrow>
          (case hoist_statements modName ctr body of
            (body', dcs, ctr') \<Rightarrow>
              (BabDecl_Function (df \<lparr> DF_Body := Some body' \<rparr>), dcs, ctr')))"
| "hoist_declaration modName ctr decl = (decl, [], ctr)"

(* Hoist string literals out of a declaration list, inserting each fresh
   constant immediately before the declaration it was hoisted out of. *)
fun hoist_decl_list :: "string \<Rightarrow> nat \<Rightarrow> BabDeclaration list
                        \<Rightarrow> BabDeclaration list \<times> nat"
  where
"hoist_decl_list modName ctr [] = ([], ctr)"
| "hoist_decl_list modName ctr (decl # decls) =
    (case hoist_declaration modName ctr decl of
      (decl', dcs, ctr1) \<Rightarrow>
        (case hoist_decl_list modName ctr1 decls of
          (decls', ctr2) \<Rightarrow> (map BabDecl_Const dcs @ [decl'] @ decls', ctr2)))"

(* Hoist string literals in both faces of a module. The counter is threaded
   through both faces so that the fresh names are unique module-wide. *)
definition hoist_module :: "BabModule \<Rightarrow> BabModule"
  where
"hoist_module m =
  (let (newInterface, counter) = hoist_decl_list (Mod_Name m) 0 (Mod_Interface m);
       (newImplementation, _) = hoist_decl_list (Mod_Name m) counter (Mod_Implementation m)
   in m \<lparr> Mod_Interface := newInterface,
          Mod_Implementation := newImplementation \<rparr>)"

end

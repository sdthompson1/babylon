theory MatchCompilePass
  imports MatchCompile "../core/CoreModule" "../ghost_erasure/GhostFree"
begin

(* The match-compilation pass as a whole-module Core-to-Core transformation.

   MatchCompile.thy compiles the arms of one match into a `MatchTree` of flat
   tests. This file:

    - translates a MatchTree back into a CoreTerm (match_tree_to_term) or a
      CoreStatement list (match_tree_to_statements);
    - traverses terms, statements and statement lists, compiling every match
      whose patterns are not already all flat (match_compile_term,
      match_compile_statement, match_compile_statement_list);
    - applies this to every function body of a module (match_compile_module);
    - defines the predicate that the pass guarantees of its output
      (core_module_flat: every pattern of every match is flat), and the
      predicate that it needs of its input (core_module_match_scrutinees_ok:
      every match with a non-flat pattern has a plain variable as scrutinee).

   The theorems about the pass are in MatchCompilePassFlat.thy (flatness),
   MatchCompilePassTyping.thy (typing) and MatchCompilePassSimulation.thy
   (semantics).
*)

(* Further information:

   Why the scrutinee of a non-flat match must be a variable: compile_matrix
   builds its test scrutinees from the original scrutinee by projection
   (CoreTm_VariantProj, CoreTm_RecordProj), and may evaluate the scrutinee
   and these projections several times, once per level of the tree. This is
   only correct if the scrutinee is pure and cheap, and the semantics of the
   compiler (eval_match_scrut in MatchCompileSemantics.thy) is only defined
   for the sublanguage Var | VariantProj | RecordProj. The elaborator always
   binds the scrutinee of a source `match` to a fresh variable (match@@n)
   before the match, so this holds for every match that can have a non-flat
   pattern (see finalize_match_term in elaborator/ElabTerm.thy and
   finalize_match_stmt in elaborator/ElabStmt.thy).

   A match whose patterns are already flat is left as it is (whatever its
   scrutinee), apart from compiling the matches nested inside its arm bodies.
   In particular `if` terms and statements, which elaborate to a match on the
   condition term with the patterns true and false, are left alone.

   Code size: the compiled tree may duplicate an arm body across several
   branches (when a row of the pattern matrix survives several
   specialisations, e.g. a wildcard row below several constructor rows), so
   the output can be larger than the input. The duplication is bounded by the
   number of arms times the number of leaves of the tree, which is small for
   realistic matches. The arm bodies are compiled once, before the match is
   compiled, so nested matches are not re-compiled per copy.

   Assert statements are left untouched: their proof bodies are typed against
   a proof goal that is taken from the assert's condition, and compiling the
   condition would change the goal. The match-compile pass is meant to run
   after ghost erasure, which removes every Assert, so nothing is lost. (The
   flatness theorem is therefore stated for ghost-free modules.) *)


section \<open>From MatchTree back to Core\<close>

(* A term-level tree: MT_Test becomes a CoreTm_Match on the test scrutinee. *)
fun match_tree_to_term :: "CoreTerm MatchTree \<Rightarrow> CoreTerm" where
  "match_tree_to_term (MT_Leaf body) = body"
| "match_tree_to_term (MT_Test s arms) =
    CoreTm_Match s (map (\<lambda>(p, t). (p, match_tree_to_term t)) arms)"

(* A statement-level tree: MT_Test becomes a CoreStmt_Match (with the ghost
   flag of the original statement), whose arms are the translated subtrees.
   An MT_Leaf is the arm body itself, which the enclosing CoreStmt_Match
   runs in its own scope, exactly as the original match ran it. *)
fun match_tree_to_statements ::
    "GhostOrNot \<Rightarrow> CoreStatement list MatchTree \<Rightarrow> CoreStatement list" where
  "match_tree_to_statements g (MT_Leaf body) = body"
| "match_tree_to_statements g (MT_Test s arms) =
    [CoreStmt_Match g s (map (\<lambda>(p, t). (p, match_tree_to_statements g t)) arms)]"


section \<open>Compiling one match\<close>

(* The arms of a match are flat if every pattern is flat. Such a match is
   left as it is by the pass. *)
definition arms_flat :: "(CorePattern \<times> 'a) list \<Rightarrow> bool" where
  "arms_flat arms = list_all (\<lambda>(p, _). flat_pattern p) arms"

(* compile_match (MatchCompile.thy) takes the type of the scrutinee as an
   argument, but does not use it: it is there for the statements of the
   theorems about it. The pass has no type environment, so it calls
   compile_matrix directly, in the same way as compile_match does. *)
definition compile_match_tree ::
    "CoreTerm \<Rightarrow> (CorePattern \<times> 'body) list \<Rightarrow> 'body MatchTree" where
  "compile_match_tree scrut arms = compile_matrix ([scrut], map (\<lambda>(p, b). ([p], b)) arms)"

lemma compile_match_tree_eq_compile_match:
  "compile_match_tree scrut arms = compile_match scrut scrutTy arms"
  by (simp add: compile_match_tree_def compile_match_def)

(* A term match with non-flat arms (whose bodies have already been
   compiled). *)
definition compile_match_term ::
    "CoreTerm \<Rightarrow> (CorePattern \<times> CoreTerm) list \<Rightarrow> CoreTerm" where
  "compile_match_term scrut arms = match_tree_to_term (compile_match_tree scrut arms)"

(* A statement match with non-flat arms. When the tree is a single leaf (the
   first arm is a wildcard, so the match always takes it), the arm body is
   still wrapped in a match with one wildcard arm, so that it runs in its own
   scope and keeps the ghost flag, as in the original statement. *)
definition compile_match_statement ::
    "GhostOrNot \<Rightarrow> CoreTerm \<Rightarrow> (CorePattern \<times> CoreStatement list) list
     \<Rightarrow> CoreStatement list" where
  "compile_match_statement g scrut arms =
    (case compile_match_tree scrut arms of
       MT_Leaf body \<Rightarrow> [CoreStmt_Match g scrut [(CorePat_Wildcard, body)]]
     | t \<Rightarrow> match_tree_to_statements g t)"


section \<open>Traversal of terms and statements\<close>

(* Compile every non-flat match in a term, innermost first. *)
fun match_compile_term :: "CoreTerm \<Rightarrow> CoreTerm" where
  "match_compile_term (CoreTm_LitBool b) = CoreTm_LitBool b"
| "match_compile_term (CoreTm_LitInt i) = CoreTm_LitInt i"
| "match_compile_term (CoreTm_LitArray elemTy tms) =
    CoreTm_LitArray elemTy (map match_compile_term tms)"
| "match_compile_term (CoreTm_Var name) = CoreTm_Var name"
| "match_compile_term (CoreTm_Cast ty tm) = CoreTm_Cast ty (match_compile_term tm)"
| "match_compile_term (CoreTm_Unop op tm) = CoreTm_Unop op (match_compile_term tm)"
| "match_compile_term (CoreTm_Binop op tm1 tm2) =
    CoreTm_Binop op (match_compile_term tm1) (match_compile_term tm2)"
| "match_compile_term (CoreTm_Let name rhs body) =
    CoreTm_Let name (match_compile_term rhs) (match_compile_term body)"
| "match_compile_term (CoreTm_Quantifier q var ty body) =
    CoreTm_Quantifier q var ty (match_compile_term body)"
| "match_compile_term (CoreTm_FunctionCall fnName tyArgs args) =
    CoreTm_FunctionCall fnName tyArgs (map match_compile_term args)"
| "match_compile_term (CoreTm_VariantCtor ctorName tyArgs arg) =
    CoreTm_VariantCtor ctorName tyArgs (match_compile_term arg)"
| "match_compile_term (CoreTm_Record flds) =
    CoreTm_Record (map (\<lambda>(name, tm). (name, match_compile_term tm)) flds)"
| "match_compile_term (CoreTm_RecordProj tm fldName) =
    CoreTm_RecordProj (match_compile_term tm) fldName"
| "match_compile_term (CoreTm_VariantProj tm ctorName) =
    CoreTm_VariantProj (match_compile_term tm) ctorName"
| "match_compile_term (CoreTm_ArrayProj tm idxs) =
    CoreTm_ArrayProj (match_compile_term tm) (map match_compile_term idxs)"
| "match_compile_term (CoreTm_Match scrut arms) =
    (let arms' = map (\<lambda>(p, b). (p, match_compile_term b)) arms
     in if arms_flat arms
        then CoreTm_Match (match_compile_term scrut) arms'
        else compile_match_term (match_compile_term scrut) arms')"
| "match_compile_term (CoreTm_Sizeof tm) = CoreTm_Sizeof (match_compile_term tm)"
| "match_compile_term (CoreTm_Allocated ty tm) = CoreTm_Allocated ty (match_compile_term tm)"
| "match_compile_term (CoreTm_Default ty) = CoreTm_Default ty"

(* The pass keeps the shape of an lvalue. (A match that compiles to a single
   leaf becomes its arm body, which may be an lvalue, so a term that is not an
   lvalue may become one; the typing rules only ever require a term to be an
   lvalue, never require it not to be, except for Sizeof, where the compiled
   term is then accepted on the same terms as before.) *)
lemma lvalue_base_name_match_compile_term [simp]:
  "is_lvalue tm \<Longrightarrow> lvalue_base_name (match_compile_term tm) = lvalue_base_name tm"
  by (induction tm) (auto simp: is_lvalue_def split: if_splits)

lemma is_lvalue_match_compile_term [simp]:
  "is_lvalue tm \<Longrightarrow> is_lvalue (match_compile_term tm)"
  by (simp add: is_lvalue_def)

(* Compile every non-flat match in a statement (giving a statement list, since
   a compiled match statement is a list) or in a statement list. *)
fun match_compile_statement :: "CoreStatement \<Rightarrow> CoreStatement list"
and match_compile_statement_list :: "CoreStatement list \<Rightarrow> CoreStatement list" where
  "match_compile_statement (CoreStmt_VarDecl g varName vr ty initTm) =
    [CoreStmt_VarDecl g varName vr ty (match_compile_term initTm)]"
| "match_compile_statement (CoreStmt_VarDeclCall g varName ty castOpt fnName tyArgs argTms) =
    [CoreStmt_VarDeclCall g varName ty castOpt fnName tyArgs (map match_compile_term argTms)]"
| "match_compile_statement (CoreStmt_Fix varName ty) = [CoreStmt_Fix varName ty]"
| "match_compile_statement (CoreStmt_Obtain varName ty condTm) =
    [CoreStmt_Obtain varName ty (match_compile_term condTm)]"
| "match_compile_statement (CoreStmt_Use tm) = [CoreStmt_Use (match_compile_term tm)]"
| "match_compile_statement (CoreStmt_Assign g lhs rhs) =
    [CoreStmt_Assign g (match_compile_term lhs) (match_compile_term rhs)]"
| "match_compile_statement (CoreStmt_AssignCall g lhs castOpt fnName tyArgs argTms) =
    [CoreStmt_AssignCall g (match_compile_term lhs) castOpt fnName tyArgs
       (map match_compile_term argTms)]"
| "match_compile_statement (CoreStmt_Swap g lhs rhs) =
    [CoreStmt_Swap g (match_compile_term lhs) (match_compile_term rhs)]"
| "match_compile_statement (CoreStmt_Return tm) = [CoreStmt_Return (match_compile_term tm)]"
| "match_compile_statement (CoreStmt_Assert condOpt proofBody) =
    [CoreStmt_Assert condOpt proofBody]"
| "match_compile_statement (CoreStmt_Assume tm) = [CoreStmt_Assume (match_compile_term tm)]"
| "match_compile_statement (CoreStmt_While g condTm invars decrTm body) =
    [CoreStmt_While g (match_compile_term condTm) (map match_compile_term invars)
       (map_option match_compile_term decrTm) (match_compile_statement_list body)]"
| "match_compile_statement (CoreStmt_Match g scrut arms) =
    (let arms' = map (\<lambda>(p, body). (p, match_compile_statement_list body)) arms
     in if arms_flat arms
        then [CoreStmt_Match g (match_compile_term scrut) arms']
        else compile_match_statement g (match_compile_term scrut) arms')"
| "match_compile_statement (CoreStmt_ShowHide sh name) = [CoreStmt_ShowHide sh name]"
| "match_compile_statement (CoreStmt_Block body) =
    [CoreStmt_Block (match_compile_statement_list body)]"

| "match_compile_statement_list [] = []"
| "match_compile_statement_list (stmt # stmts) =
    match_compile_statement stmt @ match_compile_statement_list stmts"

lemma match_compile_statement_list_append [simp]:
  "match_compile_statement_list (stmts1 @ stmts2)
     = match_compile_statement_list stmts1 @ match_compile_statement_list stmts2"
  by (induction stmts1) simp_all


section \<open>The module-level pass\<close>

(* Compile the body of one function. The parameter list is unchanged. *)
definition match_compile_function :: "CoreFunction \<Rightarrow> CoreFunction" where
  "match_compile_function f =
    f \<lparr> CF_Body := map_option match_compile_statement_list (CF_Body f) \<rparr>"

lemma match_compile_function_simps [simp]:
  "CF_Args (match_compile_function f) = CF_Args f"
  "CF_Body (match_compile_function f) = map_option match_compile_statement_list (CF_Body f)"
  by (simp_all add: match_compile_function_def)

(* The pass only rewrites function bodies. The type environment (including
   the function signatures and their contracts), the type substitution and the
   global variables are unchanged. *)
definition match_compile_module :: "CoreModule \<Rightarrow> CoreModule" where
  "match_compile_module m =
    m \<lparr> CM_Functions := fmmap match_compile_function (CM_Functions m) \<rparr>"

lemma match_compile_module_simps [simp]:
  "CM_TyEnv (match_compile_module m) = CM_TyEnv m"
  "CM_TypeSubst (match_compile_module m) = CM_TypeSubst m"
  "CM_GlobalVars (match_compile_module m) = CM_GlobalVars m"
  "CM_Functions (match_compile_module m) = fmmap match_compile_function (CM_Functions m)"
  by (simp_all add: match_compile_module_def)

lemma match_compile_module_fun_lookup:
  "fmlookup (CM_Functions (match_compile_module m)) name
     = map_option match_compile_function (fmlookup (CM_Functions m) name)"
  by simp


section \<open>Flat code\<close>

(* Every pattern of every match in the term / statement is flat. These are
   the preconditions of the code generator. *)
fun core_term_flat :: "CoreTerm \<Rightarrow> bool" where
  "core_term_flat (CoreTm_LitBool _) = True"
| "core_term_flat (CoreTm_LitInt _) = True"
| "core_term_flat (CoreTm_LitArray _ tms) = list_all core_term_flat tms"
| "core_term_flat (CoreTm_Var _) = True"
| "core_term_flat (CoreTm_Cast _ tm) = core_term_flat tm"
| "core_term_flat (CoreTm_Unop _ tm) = core_term_flat tm"
| "core_term_flat (CoreTm_Binop _ tm1 tm2) = (core_term_flat tm1 \<and> core_term_flat tm2)"
| "core_term_flat (CoreTm_Let _ rhs body) = (core_term_flat rhs \<and> core_term_flat body)"
| "core_term_flat (CoreTm_Quantifier _ _ _ body) = core_term_flat body"
| "core_term_flat (CoreTm_FunctionCall _ _ args) = list_all core_term_flat args"
| "core_term_flat (CoreTm_VariantCtor _ _ arg) = core_term_flat arg"
| "core_term_flat (CoreTm_Record flds) = list_all (\<lambda>(_, tm). core_term_flat tm) flds"
| "core_term_flat (CoreTm_RecordProj tm _) = core_term_flat tm"
| "core_term_flat (CoreTm_VariantProj tm _) = core_term_flat tm"
| "core_term_flat (CoreTm_ArrayProj tm idxs) = (core_term_flat tm \<and> list_all core_term_flat idxs)"
| "core_term_flat (CoreTm_Match scrut arms) =
    (core_term_flat scrut
     \<and> list_all (\<lambda>(p, body). flat_pattern p \<and> core_term_flat body) arms)"
| "core_term_flat (CoreTm_Sizeof tm) = core_term_flat tm"
| "core_term_flat (CoreTm_Allocated _ tm) = core_term_flat tm"
| "core_term_flat (CoreTm_Default _) = True"

fun core_statement_flat :: "CoreStatement \<Rightarrow> bool"
and core_statement_list_flat :: "CoreStatement list \<Rightarrow> bool" where
  "core_statement_flat (CoreStmt_VarDecl _ _ _ _ initTm) = core_term_flat initTm"
| "core_statement_flat (CoreStmt_VarDeclCall _ _ _ _ _ _ argTms) = list_all core_term_flat argTms"
| "core_statement_flat (CoreStmt_Fix _ _) = True"
| "core_statement_flat (CoreStmt_Obtain _ _ condTm) = core_term_flat condTm"
| "core_statement_flat (CoreStmt_Use tm) = core_term_flat tm"
| "core_statement_flat (CoreStmt_Assign _ lhs rhs) = (core_term_flat lhs \<and> core_term_flat rhs)"
| "core_statement_flat (CoreStmt_AssignCall _ lhs _ _ _ argTms) =
    (core_term_flat lhs \<and> list_all core_term_flat argTms)"
| "core_statement_flat (CoreStmt_Swap _ lhs rhs) = (core_term_flat lhs \<and> core_term_flat rhs)"
| "core_statement_flat (CoreStmt_Return tm) = core_term_flat tm"
| "core_statement_flat (CoreStmt_Assert condOpt proofBody) =
    ((case condOpt of None \<Rightarrow> True | Some tm \<Rightarrow> core_term_flat tm)
     \<and> core_statement_list_flat proofBody)"
| "core_statement_flat (CoreStmt_Assume tm) = core_term_flat tm"
| "core_statement_flat (CoreStmt_While _ condTm invars decrTm body) =
    (core_term_flat condTm
     \<and> list_all core_term_flat invars
     \<and> (case decrTm of None \<Rightarrow> True | Some tm \<Rightarrow> core_term_flat tm)
     \<and> core_statement_list_flat body)"
| "core_statement_flat (CoreStmt_Match _ scrut arms) =
    (core_term_flat scrut
     \<and> list_all (\<lambda>(p, body). flat_pattern p \<and> core_statement_list_flat body) arms)"
| "core_statement_flat (CoreStmt_ShowHide _ _) = True"
| "core_statement_flat (CoreStmt_Block body) = core_statement_list_flat body"

| "core_statement_list_flat [] = True"
| "core_statement_list_flat (stmt # stmts) =
    (core_statement_flat stmt \<and> core_statement_list_flat stmts)"

lemma core_statement_list_flat_append [simp]:
  "core_statement_list_flat (stmts1 @ stmts2)
     = (core_statement_list_flat stmts1 \<and> core_statement_list_flat stmts2)"
  by (induction stmts1) simp_all

(* Every function body of the module is flat. (Stated with fBall over the
   domain, rather than a HOL quantifier, so that it is executable.) *)
definition core_module_flat :: "CoreModule \<Rightarrow> bool" where
  "core_module_flat m =
    fBall (fmdom (CM_Functions m))
      (\<lambda>name. case fmlookup (CM_Functions m) name of
                None \<Rightarrow> True
              | Some f \<Rightarrow> (case CF_Body f of
                             None \<Rightarrow> True
                           | Some body \<Rightarrow> core_statement_list_flat body))"

lemma core_module_flat_iff:
  "core_module_flat m \<longleftrightarrow>
     (\<forall>name f body. fmlookup (CM_Functions m) name = Some f \<and> CF_Body f = Some body
                    \<longrightarrow> core_statement_list_flat body)"
proof
  assume fb: "core_module_flat m"
  show "\<forall>name f body. fmlookup (CM_Functions m) name = Some f \<and> CF_Body f = Some body
                    \<longrightarrow> core_statement_list_flat body"
  proof (intro allI impI, elim conjE)
    fix name f body
    assume lk: "fmlookup (CM_Functions m) name = Some f" and b: "CF_Body f = Some body"
    from lk have mem: "name |\<in>| fmdom (CM_Functions m)" by (rule fmdomI)
    from fbspec[OF fb[unfolded core_module_flat_def] mem] lk b
    show "core_statement_list_flat body" by simp
  qed
next
  assume "\<forall>name f body. fmlookup (CM_Functions m) name = Some f \<and> CF_Body f = Some body
                    \<longrightarrow> core_statement_list_flat body"
  then show "core_module_flat m"
    unfolding core_module_flat_def by (intro fBallI) (auto split: option.splits)
qed


section \<open>Scrutinees of non-flat matches are variables\<close>

(* Every match (term or statement) whose arms are not all flat has a plain
   variable as its scrutinee. This is what the pass needs of its input; it is
   checked at runtime by the compiler pipeline. *)
fun core_term_match_scrutinees_ok :: "CoreTerm \<Rightarrow> bool" where
  "core_term_match_scrutinees_ok (CoreTm_LitBool _) = True"
| "core_term_match_scrutinees_ok (CoreTm_LitInt _) = True"
| "core_term_match_scrutinees_ok (CoreTm_LitArray _ tms) =
    list_all core_term_match_scrutinees_ok tms"
| "core_term_match_scrutinees_ok (CoreTm_Var _) = True"
| "core_term_match_scrutinees_ok (CoreTm_Cast _ tm) = core_term_match_scrutinees_ok tm"
| "core_term_match_scrutinees_ok (CoreTm_Unop _ tm) = core_term_match_scrutinees_ok tm"
| "core_term_match_scrutinees_ok (CoreTm_Binop _ tm1 tm2) =
    (core_term_match_scrutinees_ok tm1 \<and> core_term_match_scrutinees_ok tm2)"
| "core_term_match_scrutinees_ok (CoreTm_Let _ rhs body) =
    (core_term_match_scrutinees_ok rhs \<and> core_term_match_scrutinees_ok body)"
| "core_term_match_scrutinees_ok (CoreTm_Quantifier _ _ _ body) =
    core_term_match_scrutinees_ok body"
| "core_term_match_scrutinees_ok (CoreTm_FunctionCall _ _ args) =
    list_all core_term_match_scrutinees_ok args"
| "core_term_match_scrutinees_ok (CoreTm_VariantCtor _ _ arg) =
    core_term_match_scrutinees_ok arg"
| "core_term_match_scrutinees_ok (CoreTm_Record flds) =
    list_all (\<lambda>(_, tm). core_term_match_scrutinees_ok tm) flds"
| "core_term_match_scrutinees_ok (CoreTm_RecordProj tm _) = core_term_match_scrutinees_ok tm"
| "core_term_match_scrutinees_ok (CoreTm_VariantProj tm _) = core_term_match_scrutinees_ok tm"
| "core_term_match_scrutinees_ok (CoreTm_ArrayProj tm idxs) =
    (core_term_match_scrutinees_ok tm \<and> list_all core_term_match_scrutinees_ok idxs)"
| "core_term_match_scrutinees_ok (CoreTm_Match scrut arms) =
    ((arms_flat arms \<or> (\<exists>x. scrut = CoreTm_Var x))
     \<and> core_term_match_scrutinees_ok scrut
     \<and> list_all (\<lambda>(_, body). core_term_match_scrutinees_ok body) arms)"
| "core_term_match_scrutinees_ok (CoreTm_Sizeof tm) = core_term_match_scrutinees_ok tm"
| "core_term_match_scrutinees_ok (CoreTm_Allocated _ tm) = core_term_match_scrutinees_ok tm"
| "core_term_match_scrutinees_ok (CoreTm_Default _) = True"

fun core_statement_match_scrutinees_ok :: "CoreStatement \<Rightarrow> bool"
and core_statement_list_match_scrutinees_ok :: "CoreStatement list \<Rightarrow> bool" where
  "core_statement_match_scrutinees_ok (CoreStmt_VarDecl _ _ _ _ initTm) =
    core_term_match_scrutinees_ok initTm"
| "core_statement_match_scrutinees_ok (CoreStmt_VarDeclCall _ _ _ _ _ _ argTms) =
    list_all core_term_match_scrutinees_ok argTms"
| "core_statement_match_scrutinees_ok (CoreStmt_Fix _ _) = True"
| "core_statement_match_scrutinees_ok (CoreStmt_Obtain _ _ condTm) =
    core_term_match_scrutinees_ok condTm"
| "core_statement_match_scrutinees_ok (CoreStmt_Use tm) = core_term_match_scrutinees_ok tm"
| "core_statement_match_scrutinees_ok (CoreStmt_Assign _ lhs rhs) =
    (core_term_match_scrutinees_ok lhs \<and> core_term_match_scrutinees_ok rhs)"
| "core_statement_match_scrutinees_ok (CoreStmt_AssignCall _ lhs _ _ _ argTms) =
    (core_term_match_scrutinees_ok lhs \<and> list_all core_term_match_scrutinees_ok argTms)"
| "core_statement_match_scrutinees_ok (CoreStmt_Swap _ lhs rhs) =
    (core_term_match_scrutinees_ok lhs \<and> core_term_match_scrutinees_ok rhs)"
| "core_statement_match_scrutinees_ok (CoreStmt_Return tm) = core_term_match_scrutinees_ok tm"
| "core_statement_match_scrutinees_ok (CoreStmt_Assert condOpt proofBody) =
    ((case condOpt of None \<Rightarrow> True | Some tm \<Rightarrow> core_term_match_scrutinees_ok tm)
     \<and> core_statement_list_match_scrutinees_ok proofBody)"
| "core_statement_match_scrutinees_ok (CoreStmt_Assume tm) = core_term_match_scrutinees_ok tm"
| "core_statement_match_scrutinees_ok (CoreStmt_While _ condTm invars decrTm body) =
    (core_term_match_scrutinees_ok condTm
     \<and> list_all core_term_match_scrutinees_ok invars
     \<and> (case decrTm of None \<Rightarrow> True | Some tm \<Rightarrow> core_term_match_scrutinees_ok tm)
     \<and> core_statement_list_match_scrutinees_ok body)"
| "core_statement_match_scrutinees_ok (CoreStmt_Match _ scrut arms) =
    ((arms_flat arms \<or> (\<exists>x. scrut = CoreTm_Var x))
     \<and> core_term_match_scrutinees_ok scrut
     \<and> list_all (\<lambda>(_, body). core_statement_list_match_scrutinees_ok body) arms)"
| "core_statement_match_scrutinees_ok (CoreStmt_ShowHide _ _) = True"
| "core_statement_match_scrutinees_ok (CoreStmt_Block body) =
    core_statement_list_match_scrutinees_ok body"

| "core_statement_list_match_scrutinees_ok [] = True"
| "core_statement_list_match_scrutinees_ok (stmt # stmts) =
    (core_statement_match_scrutinees_ok stmt \<and> core_statement_list_match_scrutinees_ok stmts)"

(* The existential in the Match clauses is executable, since the term is
   either a variable or not. *)
lemma ex_var_eq [code_unfold]:
  "(\<exists>x. tm = CoreTm_Var x) = (case tm of CoreTm_Var _ \<Rightarrow> True | _ \<Rightarrow> False)"
  by (cases tm) simp_all

lemma core_statement_list_match_scrutinees_ok_append [simp]:
  "core_statement_list_match_scrutinees_ok (stmts1 @ stmts2)
     = (core_statement_list_match_scrutinees_ok stmts1
        \<and> core_statement_list_match_scrutinees_ok stmts2)"
  by (induction stmts1) simp_all

(* The scrutinee test, in executable form for the code generator. (The code
   preprocessor rewrites the inner equality to HOL.equal before it looks at
   the quantifier, hence the second form.) *)
lemma ex_var_term_code [code_unfold]:
  "(\<exists>x. tm = CoreTm_Var x) \<longleftrightarrow> (case tm of CoreTm_Var _ \<Rightarrow> True | _ \<Rightarrow> False)"
  "(\<exists>x. HOL.equal tm (CoreTm_Var x)) \<longleftrightarrow> (case tm of CoreTm_Var _ \<Rightarrow> True | _ \<Rightarrow> False)"
  unfolding equal_eq by (cases tm; simp)+

definition core_module_match_scrutinees_ok :: "CoreModule \<Rightarrow> bool" where
  "core_module_match_scrutinees_ok m =
    fBall (fmdom (CM_Functions m))
      (\<lambda>name. case fmlookup (CM_Functions m) name of
                None \<Rightarrow> True
              | Some f \<Rightarrow> (case CF_Body f of
                             None \<Rightarrow> True
                           | Some body \<Rightarrow> core_statement_list_match_scrutinees_ok body))"

lemma core_module_match_scrutinees_ok_iff:
  "core_module_match_scrutinees_ok m \<longleftrightarrow>
     (\<forall>name f body. fmlookup (CM_Functions m) name = Some f \<and> CF_Body f = Some body
                    \<longrightarrow> core_statement_list_match_scrutinees_ok body)"
proof
  assume fb: "core_module_match_scrutinees_ok m"
  show "\<forall>name f body. fmlookup (CM_Functions m) name = Some f \<and> CF_Body f = Some body
                    \<longrightarrow> core_statement_list_match_scrutinees_ok body"
  proof (intro allI impI, elim conjE)
    fix name f body
    assume lk: "fmlookup (CM_Functions m) name = Some f" and b: "CF_Body f = Some body"
    from lk have mem: "name |\<in>| fmdom (CM_Functions m)" by (rule fmdomI)
    from fbspec[OF fb[unfolded core_module_match_scrutinees_ok_def] mem] lk b
    show "core_statement_list_match_scrutinees_ok body" by simp
  qed
next
  assume "\<forall>name f body. fmlookup (CM_Functions m) name = Some f \<and> CF_Body f = Some body
                    \<longrightarrow> core_statement_list_match_scrutinees_ok body"
  then show "core_module_match_scrutinees_ok m"
    unfolding core_module_match_scrutinees_ok_def by (intro fBallI) (auto split: option.splits)
qed

end

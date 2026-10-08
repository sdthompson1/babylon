(* Array-dimension rewriting.

   In Babylon, a fixed array dimension can be any compile-time constant
   expression (for example "i32[SIZE]" where SIZE is a global constant), but
   the elaborator's elab_dimension (ElabType.thy) accepts only an integer
   literal. The gap is closed by rewriting every fixed-dimension term to a
   literal before the elaborator sees the type.

   This file provides the purely syntactic part of that: a traversal that
   applies a rewrite function to every fixed-dimension term found anywhere in
   a declaration - in the signature types as well as in the types nested
   inside terms, statements and attributes. The elaborator instantiates the
   rewrite function with a compile-time evaluator (eval_dim_term in
   ElabDecl.thy).

   The traversal is bottom-up: any dimension terms nested inside a dimension
   term are rewritten before the rewrite function is applied to that term.

   The rewrite function returns either a list of errors or the new term.
   Errors from sibling positions are accumulated.
*)

theory BabMapDims
  imports "../bab/BabSyntax"
begin

(* ========================================================================== *)
(* Result combinators                                                         *)
(* ========================================================================== *)

(* Combine two results: both error lists if both fail, otherwise the pair. *)
fun combine_results :: "'e list + 'a \<Rightarrow> 'e list + 'b \<Rightarrow> 'e list + ('a \<times> 'b)" where
  "combine_results (Inl errs1) (Inl errs2) = Inl (errs1 @ errs2)"
| "combine_results (Inl errs) (Inr _) = Inl errs"
| "combine_results (Inr _) (Inl errs) = Inl errs"
| "combine_results (Inr x) (Inr y) = Inr (x, y)"

(* Combine a list of results: all error lists if any fail, otherwise all values. *)
fun collect_results :: "('e list + 'a) list \<Rightarrow> 'e list + 'a list" where
  "collect_results [] = Inr []"
| "collect_results (r # rs) =
    (case combine_results r (collect_results rs) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (x, xs) \<Rightarrow> Inr (x # xs))"

(* Apply a result-returning function under an option. *)
fun map_option_result :: "('a \<Rightarrow> 'e list + 'b) \<Rightarrow> 'a option \<Rightarrow> 'e list + 'b option" where
  "map_option_result g None = Inr None"
| "map_option_result g (Some x) =
    (case g x of
      Inl errs \<Rightarrow> Inl errs
    | Inr y \<Rightarrow> Inr (Some y))"

lemma combine_results_Inr_D:
  "combine_results r1 r2 = Inr (x, y) \<Longrightarrow> r1 = Inr x \<and> r2 = Inr y"
  by (cases r1; cases r2) auto

lemma map_option_result_None_iff:
  "map_option_result g x = Inr y \<Longrightarrow> (y = None) = (x = None)"
  by (cases x) (auto split: sum.splits)


(* ========================================================================== *)
(* Types and terms                                                            *)
(* ========================================================================== *)

fun map_dims_type :: "(BabTerm \<Rightarrow> 'e list + BabTerm) \<Rightarrow> BabType \<Rightarrow> 'e list + BabType"
and map_dims_dimension :: "(BabTerm \<Rightarrow> 'e list + BabTerm) \<Rightarrow> BabDimension
                           \<Rightarrow> 'e list + BabDimension"
and map_dims_literal :: "(BabTerm \<Rightarrow> 'e list + BabTerm) \<Rightarrow> BabLiteral \<Rightarrow> 'e list + BabLiteral"
and map_dims_term :: "(BabTerm \<Rightarrow> 'e list + BabTerm) \<Rightarrow> BabTerm \<Rightarrow> 'e list + BabTerm"
where
  "map_dims_type f (BabTy_Name loc name tyargs) =
    (case collect_results (map (map_dims_type f) tyargs) of
      Inl errs \<Rightarrow> Inl errs
    | Inr tyargs' \<Rightarrow> Inr (BabTy_Name loc name tyargs'))"
| "map_dims_type f (BabTy_Bool loc) = Inr (BabTy_Bool loc)"
| "map_dims_type f (BabTy_FiniteInt loc sign bits) = Inr (BabTy_FiniteInt loc sign bits)"
| "map_dims_type f (BabTy_MathInt loc) = Inr (BabTy_MathInt loc)"
| "map_dims_type f (BabTy_MathReal loc) = Inr (BabTy_MathReal loc)"
| "map_dims_type f (BabTy_Tuple loc tys) =
    (case collect_results (map (map_dims_type f) tys) of
      Inl errs \<Rightarrow> Inl errs
    | Inr tys' \<Rightarrow> Inr (BabTy_Tuple loc tys'))"
| "map_dims_type f (BabTy_Record loc flds) =
    (case collect_results (map (\<lambda>(name, ty).
            case map_dims_type f ty of
              Inl errs \<Rightarrow> Inl errs
            | Inr ty' \<Rightarrow> Inr (name, ty')) flds) of
      Inl errs \<Rightarrow> Inl errs
    | Inr flds' \<Rightarrow> Inr (BabTy_Record loc flds'))"
| "map_dims_type f (BabTy_Array loc elemTy dims) =
    (case combine_results (map_dims_type f elemTy)
                          (collect_results (map (map_dims_dimension f) dims)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (elemTy', dims') \<Rightarrow> Inr (BabTy_Array loc elemTy' dims'))"

| "map_dims_dimension f BabDim_Unknown = Inr BabDim_Unknown"
| "map_dims_dimension f BabDim_Allocatable = Inr BabDim_Allocatable"
  \<comment> \<open>Bottom-up: rewrite inside the term first, then apply f to the result.\<close>
| "map_dims_dimension f (BabDim_Fixed tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow>
        (case f tm' of
          Inl errs \<Rightarrow> Inl errs
        | Inr tm'' \<Rightarrow> Inr (BabDim_Fixed tm'')))"

| "map_dims_literal f (BabLit_Bool b) = Inr (BabLit_Bool b)"
| "map_dims_literal f (BabLit_Int i) = Inr (BabLit_Int i)"
| "map_dims_literal f (BabLit_String s) = Inr (BabLit_String s)"
| "map_dims_literal f (BabLit_Array tms) =
    (case collect_results (map (map_dims_term f) tms) of
      Inl errs \<Rightarrow> Inl errs
    | Inr tms' \<Rightarrow> Inr (BabLit_Array tms'))"

| "map_dims_term f (BabTm_Literal loc lit) =
    (case map_dims_literal f lit of
      Inl errs \<Rightarrow> Inl errs
    | Inr lit' \<Rightarrow> Inr (BabTm_Literal loc lit'))"
| "map_dims_term f (BabTm_Name loc name tyargs) =
    (case collect_results (map (map_dims_type f) tyargs) of
      Inl errs \<Rightarrow> Inl errs
    | Inr tyargs' \<Rightarrow> Inr (BabTm_Name loc name tyargs'))"
| "map_dims_term f (BabTm_Cast loc ty tm) =
    (case combine_results (map_dims_type f ty) (map_dims_term f tm) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (ty', tm') \<Rightarrow> Inr (BabTm_Cast loc ty' tm'))"
| "map_dims_term f (BabTm_If loc cond thenTm elseTm) =
    (case combine_results (map_dims_term f cond)
            (combine_results (map_dims_term f thenTm) (map_dims_term f elseTm)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (cond', thenTm', elseTm') \<Rightarrow> Inr (BabTm_If loc cond' thenTm' elseTm'))"
| "map_dims_term f (BabTm_Unop loc op tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabTm_Unop loc op tm'))"
| "map_dims_term f (BabTm_Binop loc tm items) =
    (case combine_results (map_dims_term f tm)
            (collect_results (map (\<lambda>(op, rhs).
               case map_dims_term f rhs of
                 Inl errs \<Rightarrow> Inl errs
               | Inr rhs' \<Rightarrow> Inr (op, rhs')) items)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (tm', items') \<Rightarrow> Inr (BabTm_Binop loc tm' items'))"
| "map_dims_term f (BabTm_Let loc var rhs body) =
    (case combine_results (map_dims_term f rhs) (map_dims_term f body) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (rhs', body') \<Rightarrow> Inr (BabTm_Let loc var rhs' body'))"
| "map_dims_term f (BabTm_Quantifier loc quant var ty body) =
    (case combine_results (map_dims_type f ty) (map_dims_term f body) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (ty', body') \<Rightarrow> Inr (BabTm_Quantifier loc quant var ty' body'))"
| "map_dims_term f (BabTm_Call loc fn args) =
    (case combine_results (map_dims_term f fn)
                          (collect_results (map (map_dims_term f) args)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (fn', args') \<Rightarrow> Inr (BabTm_Call loc fn' args'))"
| "map_dims_term f (BabTm_Tuple loc tms) =
    (case collect_results (map (map_dims_term f) tms) of
      Inl errs \<Rightarrow> Inl errs
    | Inr tms' \<Rightarrow> Inr (BabTm_Tuple loc tms'))"
| "map_dims_term f (BabTm_Record loc flds) =
    (case collect_results (map (\<lambda>(name, tm).
            case map_dims_term f tm of
              Inl errs \<Rightarrow> Inl errs
            | Inr tm' \<Rightarrow> Inr (name, tm')) flds) of
      Inl errs \<Rightarrow> Inl errs
    | Inr flds' \<Rightarrow> Inr (BabTm_Record loc flds'))"
| "map_dims_term f (BabTm_RecordUpdate loc tm flds) =
    (case combine_results (map_dims_term f tm)
            (collect_results (map (\<lambda>(name, fldTm).
               case map_dims_term f fldTm of
                 Inl errs \<Rightarrow> Inl errs
               | Inr fldTm' \<Rightarrow> Inr (name, fldTm')) flds)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (tm', flds') \<Rightarrow> Inr (BabTm_RecordUpdate loc tm' flds'))"
| "map_dims_term f (BabTm_TupleProj loc tm idx) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabTm_TupleProj loc tm' idx))"
| "map_dims_term f (BabTm_RecordProj loc tm fld) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabTm_RecordProj loc tm' fld))"
| "map_dims_term f (BabTm_ArrayProj loc tm idxs) =
    (case combine_results (map_dims_term f tm)
                          (collect_results (map (map_dims_term f) idxs)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (tm', idxs') \<Rightarrow> Inr (BabTm_ArrayProj loc tm' idxs'))"
  \<comment> \<open>Patterns contain no types, so the arm patterns are kept as they are.\<close>
| "map_dims_term f (BabTm_Match loc scrut arms) =
    (case combine_results (map_dims_term f scrut)
            (collect_results (map (\<lambda>(pat, armTm).
               case map_dims_term f armTm of
                 Inl errs \<Rightarrow> Inl errs
               | Inr armTm' \<Rightarrow> Inr (pat, armTm')) arms)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (scrut', arms') \<Rightarrow> Inr (BabTm_Match loc scrut' arms'))"
| "map_dims_term f (BabTm_Sizeof loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabTm_Sizeof loc tm'))"
| "map_dims_term f (BabTm_Allocated loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabTm_Allocated loc tm'))"
| "map_dims_term f (BabTm_Old loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabTm_Old loc tm'))"


(* ========================================================================== *)
(* Attributes and statements                                                  *)
(* ========================================================================== *)

fun map_dims_attribute :: "(BabTerm \<Rightarrow> 'e list + BabTerm) \<Rightarrow> BabAttribute
                           \<Rightarrow> 'e list + BabAttribute" where
  "map_dims_attribute f (BabAttr_Requires loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabAttr_Requires loc tm'))"
| "map_dims_attribute f (BabAttr_Ensures loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabAttr_Ensures loc tm'))"
| "map_dims_attribute f (BabAttr_Invariant loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabAttr_Invariant loc tm'))"
| "map_dims_attribute f (BabAttr_Decreases loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabAttr_Decreases loc tm'))"

fun map_dims_statement :: "(BabTerm \<Rightarrow> 'e list + BabTerm) \<Rightarrow> BabStatement
                           \<Rightarrow> 'e list + BabStatement"
and map_dims_statements :: "(BabTerm \<Rightarrow> 'e list + BabTerm) \<Rightarrow> BabStatement list
                            \<Rightarrow> 'e list + BabStatement list"
and map_dims_match_arms :: "(BabTerm \<Rightarrow> 'e list + BabTerm)
                            \<Rightarrow> (BabPattern \<times> BabStatement list) list
                            \<Rightarrow> 'e list + (BabPattern \<times> BabStatement list) list"
where
  "map_dims_statement f (BabStmt_VarDecl loc var vr optTy optTm) =
    (case combine_results (map_option_result (map_dims_type f) optTy)
                          (map_option_result (map_dims_term f) optTm) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (optTy', optTm') \<Rightarrow> Inr (BabStmt_VarDecl loc var vr optTy' optTm'))"
| "map_dims_statement f (BabStmt_Fix loc var ty) =
    (case map_dims_type f ty of
      Inl errs \<Rightarrow> Inl errs
    | Inr ty' \<Rightarrow> Inr (BabStmt_Fix loc var ty'))"
| "map_dims_statement f (BabStmt_Obtain loc var ty tm) =
    (case combine_results (map_dims_type f ty) (map_dims_term f tm) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (ty', tm') \<Rightarrow> Inr (BabStmt_Obtain loc var ty' tm'))"
| "map_dims_statement f (BabStmt_Use loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabStmt_Use loc tm'))"
| "map_dims_statement f (BabStmt_Assign loc lhs rhs) =
    (case combine_results (map_dims_term f lhs) (map_dims_term f rhs) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (lhs', rhs') \<Rightarrow> Inr (BabStmt_Assign loc lhs' rhs'))"
| "map_dims_statement f (BabStmt_Swap loc lhs rhs) =
    (case combine_results (map_dims_term f lhs) (map_dims_term f rhs) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (lhs', rhs') \<Rightarrow> Inr (BabStmt_Swap loc lhs' rhs'))"
| "map_dims_statement f (BabStmt_Return loc optTm) =
    (case map_option_result (map_dims_term f) optTm of
      Inl errs \<Rightarrow> Inl errs
    | Inr optTm' \<Rightarrow> Inr (BabStmt_Return loc optTm'))"
| "map_dims_statement f (BabStmt_Assert loc optTm proofStmts) =
    (case combine_results (map_option_result (map_dims_term f) optTm)
                          (map_dims_statements f proofStmts) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (optTm', proofStmts') \<Rightarrow> Inr (BabStmt_Assert loc optTm' proofStmts'))"
| "map_dims_statement f (BabStmt_Assume loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabStmt_Assume loc tm'))"
| "map_dims_statement f (BabStmt_If loc cond thenStmts elseStmts) =
    (case combine_results (map_dims_term f cond)
            (combine_results (map_dims_statements f thenStmts)
                             (map_dims_statements f elseStmts)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (cond', thenStmts', elseStmts') \<Rightarrow> Inr (BabStmt_If loc cond' thenStmts' elseStmts'))"
| "map_dims_statement f (BabStmt_While loc cond attrs body) =
    (case combine_results (map_dims_term f cond)
            (combine_results (collect_results (map (map_dims_attribute f) attrs))
                             (map_dims_statements f body)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (cond', attrs', body') \<Rightarrow> Inr (BabStmt_While loc cond' attrs' body'))"
| "map_dims_statement f (BabStmt_Call loc tm) =
    (case map_dims_term f tm of
      Inl errs \<Rightarrow> Inl errs
    | Inr tm' \<Rightarrow> Inr (BabStmt_Call loc tm'))"
| "map_dims_statement f (BabStmt_Match loc scrut arms) =
    (case combine_results (map_dims_term f scrut) (map_dims_match_arms f arms) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (scrut', arms') \<Rightarrow> Inr (BabStmt_Match loc scrut' arms'))"
| "map_dims_statement f (BabStmt_ShowHide loc sh name) = Inr (BabStmt_ShowHide loc sh name)"
| "map_dims_statement f (BabStmt_Ghost loc inner) =
    (case map_dims_statement f inner of
      Inl errs \<Rightarrow> Inl errs
    | Inr inner' \<Rightarrow> Inr (BabStmt_Ghost loc inner'))"

| "map_dims_statements f [] = Inr []"
| "map_dims_statements f (stmt # stmts) =
    (case combine_results (map_dims_statement f stmt) (map_dims_statements f stmts) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (stmt', stmts') \<Rightarrow> Inr (stmt' # stmts'))"

| "map_dims_match_arms f [] = Inr []"
| "map_dims_match_arms f ((pat, armStmts) # arms) =
    (case combine_results (map_dims_statements f armStmts) (map_dims_match_arms f arms) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (armStmts', arms') \<Rightarrow> Inr ((pat, armStmts') # arms'))"


(* ========================================================================== *)
(* Declarations                                                               *)
(* ========================================================================== *)

(* Rewrite every fixed-dimension term in a declaration. Only the type- and
   term-bearing fields are touched; names, type parameters, ghost/extern
   flags and the like are kept. *)
fun map_dims_declaration :: "(BabTerm \<Rightarrow> 'e list + BabTerm) \<Rightarrow> BabDeclaration
                             \<Rightarrow> 'e list + BabDeclaration" where
  "map_dims_declaration f (BabDecl_Const dc) =
    (case combine_results (map_option_result (map_dims_type f) (DC_Type dc))
                          (map_option_result (map_dims_term f) (DC_Value dc)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (optTy', optTm') \<Rightarrow>
        Inr (BabDecl_Const (dc \<lparr> DC_Type := optTy', DC_Value := optTm' \<rparr>)))"
| "map_dims_declaration f (BabDecl_Function df) =
    (case combine_results
            (collect_results (map (\<lambda>(name, vr, ty, g).
               case map_dims_type f ty of
                 Inl errs \<Rightarrow> Inl errs
               | Inr ty' \<Rightarrow> Inr (name, vr, ty', g)) (DF_TmArgs df)))
            (combine_results
               (map_option_result (map_dims_type f) (DF_ReturnType df))
               (combine_results
                  (map_option_result (map_dims_statements f) (DF_Body df))
                  (collect_results (map (map_dims_attribute f) (DF_Attributes df))))) of
      Inl errs \<Rightarrow> Inl errs
    | Inr (args', retTy', body', attrs') \<Rightarrow>
        Inr (BabDecl_Function (df \<lparr> DF_TmArgs := args',
                                    DF_ReturnType := retTy',
                                    DF_Body := body',
                                    DF_Attributes := attrs' \<rparr>)))"
| "map_dims_declaration f (BabDecl_Datatype dd) =
    (case collect_results (map (\<lambda>(loc, name, optTy).
            case map_option_result (map_dims_type f) optTy of
              Inl errs \<Rightarrow> Inl errs
            | Inr optTy' \<Rightarrow> Inr (loc, name, optTy')) (DD_Ctors dd)) of
      Inl errs \<Rightarrow> Inl errs
    | Inr ctors' \<Rightarrow> Inr (BabDecl_Datatype (dd \<lparr> DD_Ctors := ctors' \<rparr>)))"
| "map_dims_declaration f (BabDecl_Typedef dt) =
    (case map_option_result (map_dims_type f) (DT_Definition dt) of
      Inl errs \<Rightarrow> Inl errs
    | Inr defn' \<Rightarrow> Inr (BabDecl_Typedef (dt \<lparr> DT_Definition := defn' \<rparr>)))"


(* ========================================================================== *)
(* Shape preservation                                                         *)
(* ========================================================================== *)

(* A successful rewrite keeps the declaration's constructor and all of its
   non-type, non-term fields, and keeps each optional field's presence. *)
lemma map_dims_declaration_Inr_cases:
  assumes "map_dims_declaration f d = Inr d'"
  obtains
    (Const) dc optTy optTm where
      "d = BabDecl_Const dc"
      "d' = BabDecl_Const (dc \<lparr> DC_Type := optTy, DC_Value := optTm \<rparr>)"
      "(optTm = None) = (DC_Value dc = None)"
  | (Function) df args retTy body attrs where
      "d = BabDecl_Function df"
      "d' = BabDecl_Function (df \<lparr> DF_TmArgs := args, DF_ReturnType := retTy,
                                  DF_Body := body, DF_Attributes := attrs \<rparr>)"
      "(body = None) = (DF_Body df = None)"
  | (Datatype) dd ctors where
      "d = BabDecl_Datatype dd"
      "d' = BabDecl_Datatype (dd \<lparr> DD_Ctors := ctors \<rparr>)"
  | (Typedef) dt defn where
      "d = BabDecl_Typedef dt"
      "d' = BabDecl_Typedef (dt \<lparr> DT_Definition := defn \<rparr>)"
      "(defn = None) = (DT_Definition dt = None)"
proof (cases d)
  case (BabDecl_Const dc)
  from assms obtain optTy optTm where
    comb: "combine_results (map_option_result (map_dims_type f) (DC_Type dc))
                           (map_option_result (map_dims_term f) (DC_Value dc))
             = Inr (optTy, optTm)" and
    d': "d' = BabDecl_Const (dc \<lparr> DC_Type := optTy, DC_Value := optTm \<rparr>)"
    unfolding BabDecl_Const map_dims_declaration.simps
    by (auto split: sum.splits prod.splits)
  have "map_option_result (map_dims_term f) (DC_Value dc) = Inr optTm"
    using combine_results_Inr_D[OF comb] by simp
  then have none: "(optTm = None) = (DC_Value dc = None)"
    by (rule map_option_result_None_iff)
  show thesis by (rule Const[OF BabDecl_Const d' none])
next
  case (BabDecl_Function df)
  from assms obtain args retTy body attrs where
    comb: "combine_results
             (collect_results (map (\<lambda>(name, vr, ty, g).
                case map_dims_type f ty of
                  Inl errs \<Rightarrow> Inl errs
                | Inr ty' \<Rightarrow> Inr (name, vr, ty', g)) (DF_TmArgs df)))
             (combine_results
                (map_option_result (map_dims_type f) (DF_ReturnType df))
                (combine_results
                   (map_option_result (map_dims_statements f) (DF_Body df))
                   (collect_results (map (map_dims_attribute f) (DF_Attributes df)))))
             = Inr (args, retTy, body, attrs)" and
    d': "d' = BabDecl_Function (df \<lparr> DF_TmArgs := args, DF_ReturnType := retTy,
                                     DF_Body := body, DF_Attributes := attrs \<rparr>)"
    unfolding BabDecl_Function map_dims_declaration.simps
    by (auto split: sum.splits prod.splits)
  from combine_results_Inr_D[OF comb] have
    rest1: "combine_results
              (map_option_result (map_dims_type f) (DF_ReturnType df))
              (combine_results
                 (map_option_result (map_dims_statements f) (DF_Body df))
                 (collect_results (map (map_dims_attribute f) (DF_Attributes df))))
            = Inr (retTy, body, attrs)"
    by simp
  from combine_results_Inr_D[OF rest1] have
    rest2: "combine_results
              (map_option_result (map_dims_statements f) (DF_Body df))
              (collect_results (map (map_dims_attribute f) (DF_Attributes df)))
            = Inr (body, attrs)"
    by simp
  from combine_results_Inr_D[OF rest2] have
    "map_option_result (map_dims_statements f) (DF_Body df) = Inr body"
    by simp
  then have none: "(body = None) = (DF_Body df = None)"
    by (rule map_option_result_None_iff)
  show thesis by (rule Function[OF BabDecl_Function d' none])
next
  case (BabDecl_Datatype dd)
  from assms obtain ctors where
    d': "d' = BabDecl_Datatype (dd \<lparr> DD_Ctors := ctors \<rparr>)"
    unfolding BabDecl_Datatype map_dims_declaration.simps
    by (auto split: sum.splits)
  show thesis by (rule Datatype[OF BabDecl_Datatype d'])
next
  case (BabDecl_Typedef dt)
  from assms obtain defn where
    res: "map_option_result (map_dims_type f) (DT_Definition dt) = Inr defn" and
    d': "d' = BabDecl_Typedef (dt \<lparr> DT_Definition := defn \<rparr>)"
    unfolding BabDecl_Typedef map_dims_declaration.simps
    by (auto split: sum.splits)
  have none: "(defn = None) = (DT_Definition dt = None)"
    by (rule map_option_result_None_iff[OF res])
  show thesis by (rule Typedef[OF BabDecl_Typedef d' none])
qed

(* The declaration's name is kept. *)
lemma map_dims_declaration_name:
  assumes "map_dims_declaration f d = Inr d'"
  shows "get_decl_name d' = get_decl_name d"
  using assms by (cases rule: map_dims_declaration_Inr_cases) simp_all

end

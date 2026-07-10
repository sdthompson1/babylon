theory BabNames
  imports BabSyntax
begin

(* Collectors for the names *referenced* by a piece of Babylon syntax (as
   opposed to the names it *defines* - cf. get_decl_name). Used to compute
   dependency edges when sorting the declarations of a module into
   dependency order.

   These are deliberately a syntactic over-approximation: locally-bound names
   (let-bound variables, quantifier variables, pattern variables, function
   parameters, type parameters) are not tracked, so a reference to a local
   that happens to share its name with a top-level declaration produces a
   spurious edge. After renaming this cannot happen (top-level names are
   dotted, local names are undotted), so on renamer output the collected
   names are exactly the referenced top-level names. *)

fun bab_pattern_names :: "BabPattern \<Rightarrow> string list" where
  "bab_pattern_names (BabPat_Var _ _ _) = []"
| "bab_pattern_names (BabPat_Bool _ _) = []"
| "bab_pattern_names (BabPat_Int _ _) = []"
| "bab_pattern_names (BabPat_Tuple _ pats) = concat (map bab_pattern_names pats)"
| "bab_pattern_names (BabPat_Record _ flds) = concat (map (bab_pattern_names \<circ> snd) flds)"
| "bab_pattern_names (BabPat_Variant _ ctor (Some pat)) = ctor # bab_pattern_names pat"
| "bab_pattern_names (BabPat_Variant _ ctor None) = [ctor]"
| "bab_pattern_names (BabPat_Wildcard _) = []"

fun bab_literal_names :: "BabLiteral \<Rightarrow> string list"
  and bab_dimension_names :: "BabDimension \<Rightarrow> string list"
  and bab_type_names :: "BabType \<Rightarrow> string list"
  and bab_term_names :: "BabTerm \<Rightarrow> string list"
where
  "bab_literal_names (BabLit_Bool _) = []"
| "bab_literal_names (BabLit_Int _) = []"
| "bab_literal_names (BabLit_String _) = []"
| "bab_literal_names (BabLit_Array tms) = concat (map bab_term_names tms)"

| "bab_dimension_names BabDim_Unknown = []"
| "bab_dimension_names BabDim_Allocatable = []"
| "bab_dimension_names (BabDim_Fixed tm) = bab_term_names tm"

| "bab_type_names (BabTy_Name _ name tyargs) = name # concat (map bab_type_names tyargs)"
| "bab_type_names (BabTy_Bool _) = []"
| "bab_type_names (BabTy_FiniteInt _ _ _) = []"
| "bab_type_names (BabTy_MathInt _) = []"
| "bab_type_names (BabTy_MathReal _) = []"
| "bab_type_names (BabTy_Tuple _ tys) = concat (map bab_type_names tys)"
| "bab_type_names (BabTy_Record _ flds) = concat (map (bab_type_names \<circ> snd) flds)"
| "bab_type_names (BabTy_Array _ elemTy dims) =
     bab_type_names elemTy @ concat (map bab_dimension_names dims)"

| "bab_term_names (BabTm_Literal _ lit) = bab_literal_names lit"
| "bab_term_names (BabTm_Name _ name tyargs) = name # concat (map bab_type_names tyargs)"
| "bab_term_names (BabTm_Cast _ ty tm) = bab_type_names ty @ bab_term_names tm"
| "bab_term_names (BabTm_If _ tm1 tm2 tm3) =
     bab_term_names tm1 @ bab_term_names tm2 @ bab_term_names tm3"
| "bab_term_names (BabTm_Unop _ _ tm) = bab_term_names tm"
| "bab_term_names (BabTm_Binop _ tm items) =
     bab_term_names tm @ concat (map (bab_term_names \<circ> snd) items)"
| "bab_term_names (BabTm_Let _ _ rhs body) = bab_term_names rhs @ bab_term_names body"
| "bab_term_names (BabTm_Quantifier _ _ _ ty body) =
     bab_type_names ty @ bab_term_names body"
| "bab_term_names (BabTm_Call _ callee args) =
     bab_term_names callee @ concat (map bab_term_names args)"
| "bab_term_names (BabTm_Tuple _ tms) = concat (map bab_term_names tms)"
| "bab_term_names (BabTm_Record _ flds) = concat (map (bab_term_names \<circ> snd) flds)"
| "bab_term_names (BabTm_RecordUpdate _ tm flds) =
     bab_term_names tm @ concat (map (bab_term_names \<circ> snd) flds)"
| "bab_term_names (BabTm_TupleProj _ tm _) = bab_term_names tm"
| "bab_term_names (BabTm_RecordProj _ tm _) = bab_term_names tm"
| "bab_term_names (BabTm_ArrayProj _ tm idxs) =
     bab_term_names tm @ concat (map bab_term_names idxs)"
| "bab_term_names (BabTm_Match _ scrut arms) =
     bab_term_names scrut
     @ concat (map (bab_pattern_names \<circ> fst) arms)
     @ concat (map (bab_term_names \<circ> snd) arms)"
| "bab_term_names (BabTm_Sizeof _ tm) = bab_term_names tm"
| "bab_term_names (BabTm_Allocated _ tm) = bab_term_names tm"
| "bab_term_names (BabTm_Old _ tm) = bab_term_names tm"

fun bab_attribute_names :: "BabAttribute \<Rightarrow> string list" where
  "bab_attribute_names (BabAttr_Requires _ tm) = bab_term_names tm"
| "bab_attribute_names (BabAttr_Ensures _ tm) = bab_term_names tm"
| "bab_attribute_names (BabAttr_Invariant _ tm) = bab_term_names tm"
| "bab_attribute_names (BabAttr_Decreases _ tm) = bab_term_names tm"

(* Note BabStmt_ShowHide references a name (the function being shown/hidden). *)
fun bab_statement_names :: "BabStatement \<Rightarrow> string list"
  and bab_statement_list_names :: "BabStatement list \<Rightarrow> string list"
where
  "bab_statement_names (BabStmt_VarDecl _ _ _ tyOpt rhsOpt) =
     (case tyOpt of None \<Rightarrow> [] | Some ty \<Rightarrow> bab_type_names ty)
     @ (case rhsOpt of None \<Rightarrow> [] | Some tm \<Rightarrow> bab_term_names tm)"
| "bab_statement_names (BabStmt_Fix _ _ ty) = bab_type_names ty"
| "bab_statement_names (BabStmt_Obtain _ _ ty cond) =
     bab_type_names ty @ bab_term_names cond"
| "bab_statement_names (BabStmt_Use _ tm) = bab_term_names tm"
| "bab_statement_names (BabStmt_Assign _ lhs rhs) =
     bab_term_names lhs @ bab_term_names rhs"
| "bab_statement_names (BabStmt_Swap _ lhs rhs) =
     bab_term_names lhs @ bab_term_names rhs"
| "bab_statement_names (BabStmt_Return _ tmOpt) =
     (case tmOpt of None \<Rightarrow> [] | Some tm \<Rightarrow> bab_term_names tm)"
| "bab_statement_names (BabStmt_Assert _ tmOpt stmts) =
     (case tmOpt of None \<Rightarrow> [] | Some tm \<Rightarrow> bab_term_names tm)
     @ bab_statement_list_names stmts"
| "bab_statement_names (BabStmt_Assume _ tm) = bab_term_names tm"
| "bab_statement_names (BabStmt_If _ cond thens elses) =
     bab_term_names cond @ bab_statement_list_names thens
     @ bab_statement_list_names elses"
| "bab_statement_names (BabStmt_While _ cond attrs body) =
     bab_term_names cond @ concat (map bab_attribute_names attrs)
     @ bab_statement_list_names body"
| "bab_statement_names (BabStmt_Call _ tm) = bab_term_names tm"
| "bab_statement_names (BabStmt_Match _ scrut arms) =
     bab_term_names scrut
     @ concat (map (bab_pattern_names \<circ> fst) arms)
     @ concat (map (bab_statement_list_names \<circ> snd) arms)"
| "bab_statement_names (BabStmt_ShowHide _ _ name) = [name]"
| "bab_statement_names (BabStmt_Ghost _ stmt) = bab_statement_names stmt"

| "bab_statement_list_names [] = []"
| "bab_statement_list_names (s # ss) =
     bab_statement_names s @ bab_statement_list_names ss"

(* The names referenced by a declaration. A declaration's own binders (its
   type parameters and, for a function, its term parameters) are not
   references; nor is the declaration's own name. *)
fun bab_declaration_names :: "BabDeclaration \<Rightarrow> string list" where
  "bab_declaration_names (BabDecl_Const dc) =
     (case DC_Type dc of None \<Rightarrow> [] | Some ty \<Rightarrow> bab_type_names ty)
     @ (case DC_Value dc of None \<Rightarrow> [] | Some tm \<Rightarrow> bab_term_names tm)"
| "bab_declaration_names (BabDecl_Function df) =
     concat (map (\<lambda>(_, _, ty). bab_type_names ty) (DF_TmArgs df))
     @ (case DF_ReturnType df of None \<Rightarrow> [] | Some ty \<Rightarrow> bab_type_names ty)
     @ concat (map bab_attribute_names (DF_Attributes df))
     @ (case DF_Body df of None \<Rightarrow> [] | Some body \<Rightarrow> bab_statement_list_names body)"
| "bab_declaration_names (BabDecl_Datatype dd) =
     concat (map (\<lambda>(_, _, payloadOpt).
                    case payloadOpt of None \<Rightarrow> [] | Some ty \<Rightarrow> bab_type_names ty)
                 (DD_Ctors dd))"
| "bab_declaration_names (BabDecl_Typedef dt) =
     (case DT_Definition dt of None \<Rightarrow> [] | Some ty \<Rightarrow> bab_type_names ty)"

end

(* Contract renaming.

   A purely syntactic pass over a Babylon term that renames free variables,
   using one renaming outside `old(...)` and another inside it:

     - outside `old(...)`, each free variable x is replaced by f x;
     - inside `old(...)`, it is replaced by g x instead, and the `old`
       wrapper is dropped (so `old(x + 1)` becomes `g x + 1`).

   Binders are respected: a `let`, a quantifier, or a match-arm pattern that
   rebinds a name shadows it for its scope, and occurrences in that scope
   are left alone. The pass does not itself avoid capture, so the names
   produced by f and g must not be bound anywhere in the term.

   Types embedded in terms (casts, quantifier variable types, explicit type
   arguments) may carry array-dimension terms, so the renaming descends into
   those too.

   This is used in the elaborator (ElabDecl.thy). A function's contract
   is stored in its FunInfo (FI_Requires, FI_Ensures), which refers to the
   function's parameters positionally, as arg@@i, and (in a postcondition)
   as old@@i (see core/ContractNames.thy). So f maps the i-th parameter's name
   to arg@@i and g maps it to old@@i. These names cannot be written in Babylon
   source (the lexer does not accept `@@`), so they cannot be captured by a
   binder in the term.

   The renamed term is then elaborated in an environment whose locals are
   the positional names (ModuleBodyEnv.thy: contract_arg_names,
   contract_post_names). Renaming the Babylon term before elaboration,
   rather than the Core term after, means the elaborator's correctness
   theorem (elab_term_correct) directly gives the contract's typing in the
   positional environment, with no separate renaming lemma.
*)

theory BabContractRename
  imports "../bab/BabSyntax"
begin

(* The renaming map: froms ! i \<mapsto> tos ! i, identity elsewhere. *)
definition rename_map :: "string list \<Rightarrow> string list \<Rightarrow> string \<Rightarrow> string" where
  "rename_map froms tos x = (case map_of (zip froms tos) x of Some y \<Rightarrow> y | None \<Rightarrow> x)"

(* Make a renaming the identity on a list of (newly bound) names. *)
definition fix_names :: "string list \<Rightarrow> (string \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> string" where
  "fix_names bound f x = (if x \<in> set bound then x else f x)"

(* The variables bound by a (Babylon) pattern. *)
fun bab_pattern_bound_vars :: "BabPattern \<Rightarrow> string list" where
  "bab_pattern_bound_vars (BabPat_Var _ _ name) = [name]"
| "bab_pattern_bound_vars (BabPat_Bool _ _) = []"
| "bab_pattern_bound_vars (BabPat_Int _ _) = []"
| "bab_pattern_bound_vars (BabPat_Tuple _ pats) = concat (map bab_pattern_bound_vars pats)"
| "bab_pattern_bound_vars (BabPat_Record _ flds) =
    concat (map (bab_pattern_bound_vars \<circ> snd) flds)"
| "bab_pattern_bound_vars (BabPat_Variant _ _ None) = []"
| "bab_pattern_bound_vars (BabPat_Variant _ _ (Some pat)) = bab_pattern_bound_vars pat"
| "bab_pattern_bound_vars (BabPat_Wildcard _) = []"

(* The renaming itself. `f` is applied to free variables outside `old`, and
   `g` to free variables inside `old`. *)
fun rename_contract_type ::
  "(string \<Rightarrow> string) \<Rightarrow> (string \<Rightarrow> string) \<Rightarrow> BabType \<Rightarrow> BabType"
and rename_contract_dim ::
  "(string \<Rightarrow> string) \<Rightarrow> (string \<Rightarrow> string) \<Rightarrow> BabDimension \<Rightarrow> BabDimension"
and rename_contract_lit ::
  "(string \<Rightarrow> string) \<Rightarrow> (string \<Rightarrow> string) \<Rightarrow> BabLiteral \<Rightarrow> BabLiteral"
and rename_contract_term ::
  "(string \<Rightarrow> string) \<Rightarrow> (string \<Rightarrow> string) \<Rightarrow> BabTerm \<Rightarrow> BabTerm"
where
  "rename_contract_type f g (BabTy_Name loc name tyargs) =
    BabTy_Name loc name (map (rename_contract_type f g) tyargs)"
| "rename_contract_type f g (BabTy_Bool loc) = BabTy_Bool loc"
| "rename_contract_type f g (BabTy_FiniteInt loc sign bits) = BabTy_FiniteInt loc sign bits"
| "rename_contract_type f g (BabTy_MathInt loc) = BabTy_MathInt loc"
| "rename_contract_type f g (BabTy_MathReal loc) = BabTy_MathReal loc"
| "rename_contract_type f g (BabTy_Tuple loc tys) =
    BabTy_Tuple loc (map (rename_contract_type f g) tys)"
| "rename_contract_type f g (BabTy_Record loc flds) =
    BabTy_Record loc (map (\<lambda>(name, ty). (name, rename_contract_type f g ty)) flds)"
| "rename_contract_type f g (BabTy_Array loc elemTy dims) =
    BabTy_Array loc (rename_contract_type f g elemTy) (map (rename_contract_dim f g) dims)"

| "rename_contract_dim f g BabDim_Unknown = BabDim_Unknown"
| "rename_contract_dim f g BabDim_Allocatable = BabDim_Allocatable"
| "rename_contract_dim f g (BabDim_Fixed tm) = BabDim_Fixed (rename_contract_term f g tm)"

| "rename_contract_lit f g (BabLit_Bool b) = BabLit_Bool b"
| "rename_contract_lit f g (BabLit_Int i) = BabLit_Int i"
| "rename_contract_lit f g (BabLit_String s) = BabLit_String s"
| "rename_contract_lit f g (BabLit_Array tms) =
    BabLit_Array (map (rename_contract_term f g) tms)"

| "rename_contract_term f g (BabTm_Literal loc lit) =
    BabTm_Literal loc (rename_contract_lit f g lit)"
| "rename_contract_term f g (BabTm_Name loc name tyargs) =
    BabTm_Name loc (f name) (map (rename_contract_type f g) tyargs)"
| "rename_contract_term f g (BabTm_Cast loc ty tm) =
    BabTm_Cast loc (rename_contract_type f g ty) (rename_contract_term f g tm)"
| "rename_contract_term f g (BabTm_If loc cond thenTm elseTm) =
    BabTm_If loc (rename_contract_term f g cond)
                 (rename_contract_term f g thenTm)
                 (rename_contract_term f g elseTm)"
| "rename_contract_term f g (BabTm_Unop loc op tm) =
    BabTm_Unop loc op (rename_contract_term f g tm)"
| "rename_contract_term f g (BabTm_Binop loc tm items) =
    BabTm_Binop loc (rename_contract_term f g tm)
                    (map (\<lambda>(op, t). (op, rename_contract_term f g t)) items)"
| "rename_contract_term f g (BabTm_Let loc var rhs body) =
    BabTm_Let loc var (rename_contract_term f g rhs)
                      (rename_contract_term (fix_names [var] f) (fix_names [var] g) body)"
| "rename_contract_term f g (BabTm_Quantifier loc quant var ty body) =
    BabTm_Quantifier loc quant var (rename_contract_type f g ty)
                     (rename_contract_term (fix_names [var] f) (fix_names [var] g) body)"
| "rename_contract_term f g (BabTm_Call loc fn args) =
    BabTm_Call loc (rename_contract_term f g fn) (map (rename_contract_term f g) args)"
| "rename_contract_term f g (BabTm_Tuple loc tms) =
    BabTm_Tuple loc (map (rename_contract_term f g) tms)"
| "rename_contract_term f g (BabTm_Record loc flds) =
    BabTm_Record loc (map (\<lambda>(name, t). (name, rename_contract_term f g t)) flds)"
| "rename_contract_term f g (BabTm_RecordUpdate loc tm flds) =
    BabTm_RecordUpdate loc (rename_contract_term f g tm)
                           (map (\<lambda>(name, t). (name, rename_contract_term f g t)) flds)"
| "rename_contract_term f g (BabTm_TupleProj loc tm idx) =
    BabTm_TupleProj loc (rename_contract_term f g tm) idx"
| "rename_contract_term f g (BabTm_RecordProj loc tm fld) =
    BabTm_RecordProj loc (rename_contract_term f g tm) fld"
| "rename_contract_term f g (BabTm_ArrayProj loc tm idxs) =
    BabTm_ArrayProj loc (rename_contract_term f g tm) (map (rename_contract_term f g) idxs)"
| "rename_contract_term f g (BabTm_Match loc scrut arms) =
    BabTm_Match loc (rename_contract_term f g scrut)
                    (map (\<lambda>(pat, body).
                            (pat, rename_contract_term
                                    (fix_names (bab_pattern_bound_vars pat) f)
                                    (fix_names (bab_pattern_bound_vars pat) g)
                                    body))
                         arms)"
| "rename_contract_term f g (BabTm_Sizeof loc tm) =
    BabTm_Sizeof loc (rename_contract_term f g tm)"
| "rename_contract_term f g (BabTm_Allocated loc tm) =
    BabTm_Allocated loc (rename_contract_term f g tm)"
  \<comment> \<open>`old` switches to the inner map and disappears.\<close>
| "rename_contract_term f g (BabTm_Old loc tm) = rename_contract_term g g tm"

end

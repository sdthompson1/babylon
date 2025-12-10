theory CoreTypecheck
  imports CoreTyEnvWellFormed
begin

(* ========================================================================== *)
(* Helper functions for pattern matching type-checking *)
(* ========================================================================== *)

(* Check if a pattern is compatible with a scrutinee type *)
fun pattern_compatible :: "CoreTyEnv \<Rightarrow> CorePattern \<Rightarrow> CoreType \<Rightarrow> bool" where
  "pattern_compatible env CorePat_Wildcard _ = True"
| "pattern_compatible env (CorePat_Bool _) ty = (ty = CoreTy_Bool)"
| "pattern_compatible env (CorePat_Int _) ty = is_integer_type ty"
| "pattern_compatible env (CorePat_Variant ctorName) ty =
    (case fmlookup (TE_DataCtors env) ctorName of
      None \<Rightarrow> False
    | Some (dtName, _, _) \<Rightarrow>
        (case ty of
          CoreTy_Name tyName _ \<Rightarrow> tyName = dtName
        | _ \<Rightarrow> False))"

(* Check if a list of patterns contains a wildcard *)
fun has_wildcard :: "CorePattern list \<Rightarrow> bool" where
  "has_wildcard [] = False"
| "has_wildcard (CorePat_Wildcard # _) = True"
| "has_wildcard (_ # ps) = has_wildcard ps"

(* Check if there are any patterns after a wildcard (which is not allowed) *)
fun patterns_after_wildcard :: "CorePattern list \<Rightarrow> bool" where
  "patterns_after_wildcard [] = False"
| "patterns_after_wildcard [_] = False"
| "patterns_after_wildcard (CorePat_Wildcard # _ # _) = True"
| "patterns_after_wildcard (_ # ps) = patterns_after_wildcard ps"

(* Check if a list has duplicate patterns *)
fun has_duplicate_patterns :: "CorePattern list \<Rightarrow> bool" where
  "has_duplicate_patterns [] = False"
| "has_duplicate_patterns (p # ps) = (p \<in> set ps \<or> has_duplicate_patterns ps)"

(* Regularity: no duplicates and no patterns after wildcard *)
definition patterns_regular :: "CorePattern list \<Rightarrow> bool" where
  "patterns_regular pats = (\<not> patterns_after_wildcard pats \<and> \<not> has_duplicate_patterns pats)"

(* Check exhaustiveness of patterns for a given scrutinee type *)
fun patterns_exhaustive :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> CorePattern list \<Rightarrow> bool" where
  "patterns_exhaustive env scrutTy pats =
    (if has_wildcard pats then True
     else (case scrutTy of
       CoreTy_Bool \<Rightarrow>
         list_ex (\<lambda>p. p = CorePat_Bool True) pats \<and>
         list_ex (\<lambda>p. p = CorePat_Bool False) pats
     | CoreTy_FiniteInt _ _ \<Rightarrow> False  \<comment> \<open>require wildcard for integers\<close>
     | CoreTy_MathInt \<Rightarrow> False
     | CoreTy_Name dtName _ \<Rightarrow>
         (case fmlookup (TE_DataCtorsByType env) dtName of
           None \<Rightarrow> False
         | Some ctors \<Rightarrow>
             list_all (\<lambda>ctor. list_ex (\<lambda>p. p = CorePat_Variant ctor) pats) ctors)
     | _ \<Rightarrow> False))"  \<comment> \<open>Other types: require wildcard\<close>

(* ========================================================================== *)
(* Main type-checking function *)
(* ========================================================================== *)

(* This function determines whether a CoreTerm is well-typed, and if so, returns its type. *)

function core_term_type :: "CoreTyEnv \<Rightarrow> GhostOrNot \<Rightarrow> CoreTerm \<Rightarrow> CoreType option" where

  (* Bool literals - always type Bool *)
  "core_term_type env ghost (CoreTm_LitBool _) = Some CoreTy_Bool"

  (* Int literals - use types i32, u32, i64, u64 in that order of preference *)
| "core_term_type env ghost (CoreTm_LitInt i) =
    (case get_type_for_int i of
      Some (sign, bits) \<Rightarrow> Some (CoreTy_FiniteInt sign bits)
    | None \<Rightarrow> None)"

  (* TODO: CoreTm_LitArray *)
| "core_term_type env ghost (CoreTm_LitArray tms) = undefined"

  (* Variables - must be found in TE_TermVars and (in NotGhost mode) cannot be a ghost var *)
| "core_term_type env ghost (CoreTm_Var name) =
    (case fmlookup (TE_TermVars env) name of
      Some ty \<Rightarrow> if (ghost = NotGhost \<longrightarrow> name |\<notin>| TE_GhostVars env) then Some ty else None
    | None \<Rightarrow> None)"

  (* Casts - only integet-to-integer for now *)
| "core_term_type env ghost (CoreTm_Cast targetTy operand) =
    (case core_term_type env ghost operand of
      None \<Rightarrow> None
    | Some operandTy \<Rightarrow> 
        if is_integer_type operandTy
        \<and> is_integer_type targetTy
        \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type targetTy) then
          Some targetTy
        else
          None)"

  (* Unary operators - negate, complement, logical-not *)
| "core_term_type env ghost (CoreTm_Unop op operand) =
    (case core_term_type env ghost operand of
      Some operandTy \<Rightarrow>
        (case op of
          CoreUnop_Negate \<Rightarrow>
            (if is_signed_numeric_type operandTy then Some operandTy else None)
        | CoreUnop_Complement \<Rightarrow>
            (if is_finite_integer_type operandTy then Some operandTy else None)
        | CoreUnop_Not \<Rightarrow>
            (if operandTy = CoreTy_Bool then Some CoreTy_Bool else None))
    | None \<Rightarrow> None)"

  (* TODO *)
| "core_term_type env ghost (CoreTm_Binop op lhs rhs) = undefined"
| "core_term_type env ghost (CoreTm_Let var rhs body) = undefined"
| "core_term_type env ghost (CoreTm_Quantifier quant var ty body) = undefined"

(* Function call:
   - Function must exist in environment
   - Number of type args must match
   - Type args must be well-kinded
   - In NotGhost mode: type args must be runtime types, and function must not be ghost
   - Term args must be well-typed with types matching expected arg types (after substitution) *)
| "core_term_type env ghost (CoreTm_FunctionCall fnName tyArgs tmArgs) =
    (case fmlookup (TE_Functions env) fnName of
      None \<Rightarrow> None
    | Some funInfo \<Rightarrow>
        \<comment> \<open>Check number of type arguments\<close>
        if length tyArgs \<noteq> length (FI_TyArgs funInfo) then None
        \<comment> \<open>Check type arguments are well-kinded\<close>
        else if \<not> list_all (is_well_kinded env) tyArgs then None
        \<comment> \<open>In NotGhost mode: check type args are runtime and function is not ghost\<close>
        else if ghost = NotGhost \<and> (\<not> list_all is_runtime_type tyArgs \<or> FI_Ghost funInfo = Ghost)
             then None
        \<comment> \<open>Check number of term arguments\<close>
        else if length tmArgs \<noteq> length (FI_TmArgs funInfo) then None
        else
          let tySubst = fmap_of_list (zip (FI_TyArgs funInfo) tyArgs);
              expectedArgTypes = map (apply_subst tySubst) (FI_TmArgs funInfo)
          in \<comment> \<open>Check each term argument has the expected type\<close>
             if list_all2 (\<lambda>tm expectedTy.
                   case core_term_type env ghost tm of
                     None \<Rightarrow> False
                   | Some actualTy \<Rightarrow> actualTy = expectedTy)
                 tmArgs expectedArgTypes
             then Some (apply_subst tySubst (FI_ReturnType funInfo))
             else None)"

(* TODO *)
| "core_term_type env ghost (CoreTm_VariantCtor variantName tyArgs payload) = undefined"
| "core_term_type env ghost (CoreTm_Record flds) = undefined"
| "core_term_type env ghost (CoreTm_RecordProj tm fldName) = undefined"
| "core_term_type env ghost (CoreTm_ArrayProj arr idxs) = undefined"
| "core_term_type env ghost (CoreTm_VariantProj tm ctorName) = undefined"

(* Pattern matching:
   - Scrutinee must typecheck
   - All patterns must be compatible with scrutinee type
   - Patterns must be regular (no duplicates, wildcard last)
   - Patterns must be exhaustive
   - All arm bodies must have the same type *)
| "core_term_type env ghost (CoreTm_Match scrut arms) =
    (case core_term_type env ghost scrut of
      None \<Rightarrow> None
    | Some scrutTy \<Rightarrow>
        let pats = map fst arms;
            bodies = map snd arms
        in if arms = [] then None  \<comment> \<open>empty match not allowed\<close>
           else if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
           else if \<not> patterns_regular pats then None
           else if \<not> patterns_exhaustive env scrutTy pats then None
           else \<comment> \<open>check all bodies have same type\<close>
             (case core_term_type env ghost (snd (hd arms)) of
               None \<Rightarrow> None
             | Some resultTy \<Rightarrow>
                 if list_all (\<lambda>body. core_term_type env ghost body = Some resultTy) (tl bodies)
                 then Some resultTy
                 else None))"
| "core_term_type env ghost (CoreTm_Sizeof tm) = undefined"

  (* Allocated: only valid in Ghost mode, parameter can be any type, result is bool *)
| "core_term_type env NotGhost (CoreTm_Allocated _) = None"
| "core_term_type env Ghost (CoreTm_Allocated tm) =
    (case core_term_type env Ghost tm of
      Some _ \<Rightarrow> Some CoreTy_Bool
    | None \<Rightarrow> None)"

  (* TODO: Old *)
| "core_term_type env ghost (CoreTm_Old tm) = undefined"

  by pat_completeness auto

termination
proof (relation "measure (\<lambda>(env, ghost, tm). size tm)")
  \<comment> \<open>Goal 1: well-foundedness\<close>
  show "wf (measure (\<lambda>(env, ghost, tm). size tm))" by simp
next
  \<comment> \<open>Goal 2: CoreTm_Cast - operand is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix targetTy operand
  show "((env, ghost, operand), env, ghost, CoreTm_Cast targetTy operand)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 3: CoreTm_Unop - operand is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix op operand
  show "((env, ghost, operand), env, ghost, CoreTm_Unop op operand)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 4: CoreTm_FunctionCall - elements of tmArgs are smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix fnName tyArgs tmArgs x2 x xa yb
  fix z :: CoreTerm
  assume "z \<in> set tmArgs"
  hence "size z < Suc (size_list size tmArgs)"
    using size_list_estimation
    by (metis less_not_refl not_less_eq)
  thus "((env, ghost, z), env, ghost, CoreTm_FunctionCall fnName tyArgs tmArgs)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 5: CoreTm_Match - scrutinee is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix scrut arms
  show "((env, ghost, scrut), env, ghost, CoreTm_Match scrut arms)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 6: CoreTm_Match - first arm body is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix scrut
  fix arms :: "(CorePattern \<times> CoreTerm) list"
  fix x2 x xa
  assume "arms \<noteq> []"
  thus "((env, ghost, snd (hd arms)), env, ghost, CoreTm_Match scrut arms)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by (cases arms) auto
next
  \<comment> \<open>Goal 7: CoreTm_Match - tail arm bodies are smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix scrut :: CoreTerm
  fix arms :: "(CorePattern \<times> CoreTerm) list"
  fix x2 x xa x2a
  fix z :: CoreTerm
  assume "arms \<noteq> []" and "xa = map snd arms" and "z \<in> set (tl xa)"
  hence "z \<in> set (tl (map snd arms))" by simp
  hence "z \<in> set (map snd arms)"
    by (meson \<open>arms \<noteq> []\<close> list.set_sel(2) map_is_Nil_conv)
  hence "z \<in> snd ` set arms" by simp
  then obtain p where p_z_in: "(p, z) \<in> set arms" by auto
  have "size_prod (\<lambda>x. 0) size (p, z) \<le> size_list (size_prod (\<lambda>x. 0) size) arms"
    using p_z_in by (simp add: size_list_estimation')
  hence "size z \<le> size_list (size_prod (\<lambda>x. 0) size) arms"
    by simp
  hence "size z < Suc (size_list (size_prod (\<lambda>x. 0) size) arms)"
    by simp
  thus "((env, ghost, z), env, ghost, CoreTm_Match scrut arms)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 8: CoreTm_Allocated - tm is smaller\<close>
  fix env :: CoreTyEnv
  fix tm
  show "((env, Ghost, tm), env, Ghost, CoreTm_Allocated tm)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
qed


(* If core_term_type succeeds, the resulting type is well-kinded *)
lemma core_term_type_well_kinded:
  assumes "core_term_type env ghost tm = Some ty"
    and "tyenv_well_formed env"
  shows "is_well_kinded env ty"
using assms proof (induction tm arbitrary: env ghost ty)
  case (CoreTm_LitBool b)
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray x)
  then show ?case sorry
next
  case (CoreTm_Var name)
  then obtain varTy where
    lookup: "fmlookup (TE_TermVars env) name = Some varTy" and
    ty_eq: "ty = varTy"
    by (auto split: option.splits if_splits)
  have "tyenv_vars_well_kinded env"
    using CoreTm_Var.prems(2) tyenv_well_formed_def by blast
  thus ?case
    using lookup ty_eq tyenv_vars_well_kinded_def by blast
next
  case (CoreTm_Cast targetTy operand)
  (* targetTy must be an integer type, which is always well-kinded *)
  then show ?case
    by (auto simp: is_integer_type_well_kinded split: option.splits if_splits)
next
  case (CoreTm_Unop op operand)
  then obtain operandTy where
    operand_typed: "core_term_type env ghost operand = Some operandTy"
    by (auto split: option.splits)
  have operand_wk: "is_well_kinded env operandTy"
    using CoreTm_Unop.IH operand_typed CoreTm_Unop.prems(2) by blast
  show ?case using CoreTm_Unop.prems(1) operand_typed operand_wk
    by (cases op) (auto split: if_splits)
next
  case (CoreTm_Binop x1a tm1 tm2)
  then show ?case sorry
next
  case (CoreTm_Let x1a tm1 tm2)
  then show ?case sorry
next
  case (CoreTm_Quantifier x1a x2a x3a tm)
  then show ?case sorry
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  from CoreTm_FunctionCall.prems(1) obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: option.splits if_splits)
  \<comment> \<open>The return type in funInfo is well-kinded (from tyenv_well_formed)\<close>
  have "tyenv_fun_types_well_kinded env"
    using CoreTm_FunctionCall.prems(2) tyenv_well_formed_def by blast
  hence ret_wk: "is_well_kinded env (FI_ReturnType funInfo)"
    using fn_lookup tyenv_fun_types_well_kinded_def by blast
  \<comment> \<open>The substitution maps to well-kinded types\<close>
  have subst_wk: "metasubst_well_kinded env (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))"
    using tyargs_wk metasubst_well_kinded_from_zip by blast
  \<comment> \<open>Therefore the result is well-kinded\<close>
  show ?case using ty_eq ret_wk subst_wk apply_subst_preserves_well_kinded by blast
next
  case (CoreTm_VariantCtor x1a x2a tm)
  then show ?case sorry
next
  case (CoreTm_Record x)
  then show ?case sorry
next
  case (CoreTm_RecordProj tm x2a)
  then show ?case sorry
next
  case (CoreTm_ArrayProj tm x2a)
  then show ?case sorry
next
  case (CoreTm_VariantProj tm x2a)
  then show ?case sorry
next
  case (CoreTm_Match scrut arms)
  \<comment> \<open>Extract facts from the successful typecheck\<close>
  from CoreTm_Match.prems(1) obtain scrutTy where
    scrut_typed: "core_term_type env ghost scrut = Some scrutTy" and
    arms_nonempty: "arms \<noteq> []"
    by (auto simp: Let_def split: option.splits if_splits)
  from CoreTm_Match.prems(1) scrut_typed arms_nonempty obtain resultTy where
    first_body_typed: "core_term_type env ghost (snd (hd arms)) = Some resultTy" and
    ty_eq: "ty = resultTy"
    by (auto simp: Let_def split: option.splits if_splits)
  \<comment> \<open>The first arm body is in the arms list\<close>
  have "snd (hd arms) \<in> snd ` set arms"
    using arms_nonempty by (cases arms) auto
  \<comment> \<open>By IH on the first arm body, the result type is well-kinded\<close>
  have "is_well_kinded env resultTy"
    using CoreTm_Match.IH(2) first_body_typed CoreTm_Match.prems(2)
    using arms_nonempty list.set_sel(1) snds.intros by blast
  thus ?case using ty_eq by simp
next
  case (CoreTm_Sizeof tm)
  then show ?case sorry
next
  case (CoreTm_Allocated tm)
  show ?case using CoreTm_Allocated.prems(1)
    by (cases ghost) (auto split: option.splits)
next
  case (CoreTm_Old tm)
  then show ?case sorry
qed


(* If core_term_type succeeds in NotGhost mode, the resulting type is runtime *)
lemma core_term_type_notghost_runtime:
  assumes "core_term_type env NotGhost tm = Some ty"
    and "tyenv_well_formed env"
  shows "is_runtime_type ty"
using assms proof (induction tm arbitrary: env ty)
  case (CoreTm_LitBool b)
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray x)
  (* Not yet implemented - catch-all returns undefined *)
  then show ?case sorry
next
  case (CoreTm_Var name)
  then obtain varTy where
    lookup: "fmlookup (TE_TermVars env) name = Some varTy" and
    not_ghost: "name |\<notin>| TE_GhostVars env" and
    ty_eq: "ty = varTy"
    by (auto split: option.splits if_splits)
  have "tyenv_vars_runtime env"
    using CoreTm_Var.prems(2) tyenv_well_formed_def by blast
  thus ?case
    using lookup not_ghost ty_eq tyenv_vars_runtime_def by blast
next
  case (CoreTm_Cast targetTy operand)
  then show ?case by (auto split: option.splits if_splits)
next
  case (CoreTm_Unop op operand)
  then obtain operandTy where
    operand_typed: "core_term_type env NotGhost operand = Some operandTy"
    by (auto split: option.splits)
  have operand_runtime: "is_runtime_type operandTy"
    using CoreTm_Unop.IH operand_typed CoreTm_Unop.prems(2) by blast
  show ?case using CoreTm_Unop.prems(1) operand_typed operand_runtime
    by (cases op) (auto split: if_splits)
next
  case (CoreTm_Binop x1a tm1 tm2)
  then show ?case sorry
next
  case (CoreTm_Let x1a tm1 tm2)
  then show ?case sorry
next
  case (CoreTm_Quantifier x1a x2a x3a tm)
  then show ?case sorry
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  from CoreTm_FunctionCall.prems(1) obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    not_ghost_fn: "FI_Ghost funInfo \<noteq> Ghost" and
    tyargs_rt: "list_all is_runtime_type tyArgs" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: option.splits if_splits)
  \<comment> \<open>The return type in funInfo is runtime (from tyenv_well_formed, since function is not ghost)\<close>
  have "tyenv_fun_ghost_constraint env"
    using CoreTm_FunctionCall.prems(2) tyenv_well_formed_def by blast
  hence ret_rt: "is_runtime_type (FI_ReturnType funInfo)"
    using fn_lookup not_ghost_fn tyenv_fun_ghost_constraint_def GhostOrNot.exhaust by blast
  \<comment> \<open>The substitution maps to runtime types\<close>
  have subst_rt: "\<forall>ty \<in> fmran' (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)). is_runtime_type ty"
  proof
    fix x assume "x \<in> fmran' (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))"
    then obtain n where "fmlookup (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) n = Some x"
      by (auto simp: fmran'_def)
    hence "(n, x) \<in> set (zip (FI_TyArgs funInfo) tyArgs)"
      by (simp add: fmap_of_list_SomeD)
    hence "x \<in> set tyArgs" by (auto dest: set_zip_rightD)
    thus "is_runtime_type x" using tyargs_rt by (simp add: list_all_iff)
  qed
  \<comment> \<open>Therefore the result is runtime\<close>
  show ?case using ty_eq ret_rt subst_rt apply_subst_preserves_runtime by blast
next
  case (CoreTm_VariantCtor x1a x2a tm)
  then show ?case sorry
next
  case (CoreTm_Record x)
  then show ?case sorry
next
  case (CoreTm_RecordProj tm x2a)
  then show ?case sorry
next
  case (CoreTm_ArrayProj tm x2a)
  then show ?case sorry
next
  case (CoreTm_VariantProj tm x2a)
  then show ?case sorry
next
  case (CoreTm_Match scrut arms)
  \<comment> \<open>Extract facts from the successful typecheck\<close>
  from CoreTm_Match.prems(1) obtain scrutTy where
    scrut_typed: "core_term_type env NotGhost scrut = Some scrutTy" and
    arms_nonempty: "arms \<noteq> []"
    by (auto simp: Let_def split: option.splits if_splits)
  from CoreTm_Match.prems(1) scrut_typed arms_nonempty obtain resultTy where
    first_body_typed: "core_term_type env NotGhost (snd (hd arms)) = Some resultTy" and
    ty_eq: "ty = resultTy"
    by (auto simp: Let_def split: option.splits if_splits)
  \<comment> \<open>By IH on the first arm body, the result type is runtime\<close>
  have "is_runtime_type resultTy"
    using CoreTm_Match.IH(2) first_body_typed CoreTm_Match.prems(2)
    using arms_nonempty list.set_sel(1) snds.intros by blast
  thus ?case using ty_eq by simp
next
  case (CoreTm_Sizeof tm)
  then show ?case sorry
next
  case (CoreTm_Allocated tm)
  then show ?case by simp
next
  case (CoreTm_Old tm)
  then show ?case sorry
qed

end

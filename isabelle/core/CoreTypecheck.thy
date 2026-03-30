theory CoreTypecheck
  imports CoreTyEnvWellFormed CoreFreeVars
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

  (* Binary operators *)
| "core_term_type env ghost (CoreTm_Binop op lhs rhs) =
    (case (core_term_type env ghost lhs, core_term_type env ghost rhs) of
      (Some lhsTy, Some rhsTy) \<Rightarrow>
        if is_arithmetic_binop op then
          \<comment> \<open>Arithmetic: require identical numeric types, result is same type\<close>
          if is_numeric_type lhsTy \<and> lhsTy = rhsTy then Some lhsTy else None
        else if is_modulo_binop op then
          \<comment> \<open>Modulo: require identical integer types (not real), result is same type\<close>
          if is_integer_type lhsTy \<and> lhsTy = rhsTy then Some lhsTy else None
        else if is_bitwise_binop op \<or> is_shift_binop op then
          \<comment> \<open>Bitwise/shift: require identical finite integer types, result is same type\<close>
          if is_finite_integer_type lhsTy \<and> lhsTy = rhsTy then Some lhsTy else None
        else if is_ordering_binop op then
          \<comment> \<open>Ordering: require identical numeric types, result is bool\<close>
          if is_numeric_type lhsTy \<and> lhsTy = rhsTy then Some CoreTy_Bool else None
        else if is_eq_neq_binop op then
          \<comment> \<open>Equality/inequality: same types; any type in Ghost, bool/numeric in NotGhost\<close>
          if lhsTy = rhsTy \<and> (ghost = Ghost \<or> lhsTy = CoreTy_Bool \<or> is_numeric_type lhsTy)
          then Some CoreTy_Bool else None
        else if is_logical_binop op then
          \<comment> \<open>Logical: require boolean operands, result is bool\<close>
          if lhsTy = CoreTy_Bool \<and> rhsTy = CoreTy_Bool then Some CoreTy_Bool else None
        else None
    | _ \<Rightarrow> None)"
| "core_term_type env ghost (CoreTm_Let var rhs body) =
    (case core_term_type env ghost rhs of
      Some rhsTy \<Rightarrow>
        if \<not> is_ground rhsTy then None
        else let env' = env \<lparr> TE_TermVars := fmupd var rhsTy (TE_TermVars env),
                              TE_GhostVars := (if ghost = Ghost
                                               then finsert var (TE_GhostVars env)
                                               else fminus (TE_GhostVars env) {|var|}) \<rparr>
             in core_term_type env' ghost body
    | None \<Rightarrow> None)"
| "core_term_type env NotGhost (CoreTm_Quantifier _ _ _ _) = None"
| "core_term_type env Ghost (CoreTm_Quantifier quant var ty body) = undefined"

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

(* Variant construction:
   - Constructor must exist in TE_DataCtors
   - Number of type arguments must match metavars
   - Type arguments must be well-kinded
   - In NotGhost mode: type arguments must be runtime types
   - Payload must typecheck to the expected payload type (after substitution) *)
| "core_term_type env ghost (CoreTm_VariantCtor ctorName tyArgs payload) =
    (case fmlookup (TE_DataCtors env) ctorName of
      None \<Rightarrow> None
    | Some (dtName, metavars, payloadTy) \<Rightarrow>
        (if length tyArgs \<noteq> length metavars then None
        else if \<not> list_all (is_well_kinded env) tyArgs then None
        else if ghost = NotGhost \<and> \<not> list_all is_runtime_type tyArgs then None
        else let tySubst = fmap_of_list (zip metavars tyArgs)
             in case core_term_type env ghost payload of
                  None \<Rightarrow> None
                | Some actualPayloadTy \<Rightarrow>
                    if actualPayloadTy = apply_subst tySubst payloadTy
                    then Some (CoreTy_Name dtName tyArgs)
                    else None))"
| "core_term_type env ghost (CoreTm_Record flds) = undefined"

| "core_term_type env ghost (CoreTm_RecordProj tm fldName) =
    (case core_term_type env ghost tm of
      Some (CoreTy_Record fieldTypes) \<Rightarrow> map_of fieldTypes fldName
    | _ \<Rightarrow> None)"
| "core_term_type env ghost (CoreTm_ArrayProj arr idxTms) =
    (case core_term_type env ghost arr of
      Some (CoreTy_Array elemTy dims) \<Rightarrow>
        if length idxTms = length dims
        \<and> list_all (\<lambda>tm. core_term_type env ghost tm
                          = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms
        then Some elemTy
        else None
    | _ \<Rightarrow> None)"
| "core_term_type env ghost (CoreTm_VariantProj tm ctorName) =
    (case core_term_type env ghost tm of
      Some (CoreTy_Name dtName tyArgs) \<Rightarrow>
        (case fmlookup (TE_DataCtors env) ctorName of
          Some (dtName2, metavars, payloadTy) \<Rightarrow>
            if dtName = dtName2 \<and> length tyArgs = length metavars
            then Some (apply_subst (fmap_of_list (zip metavars tyArgs)) payloadTy)
            else None
        | None \<Rightarrow> None)
    | _ \<Rightarrow> None)"

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

  (* Old: only valid in Ghost mode *)
| "core_term_type env NotGhost (CoreTm_Old _) = None"
| "core_term_type env Ghost (CoreTm_Old tm) = undefined"

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
  \<comment> \<open>Goal 4: CoreTm_Binop - lhs is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix op lhs rhs
  show "((env, ghost, lhs), env, ghost, CoreTm_Binop op lhs rhs)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 5: CoreTm_Binop - rhs is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix op lhs rhs
  show "((env, ghost, rhs), env, ghost, CoreTm_Binop op lhs rhs)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 6: CoreTm_FunctionCall - elements of tmArgs are smaller\<close>
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
  \<comment> \<open>Goal 7: CoreTm_VariantCtor - payload is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix ctorName tyArgs payload
  show "((env, ghost, payload), env, ghost, CoreTm_VariantCtor ctorName tyArgs payload)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 8: CoreTm_Match - scrutinee is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix scrut arms
  show "((env, ghost, scrut), env, ghost, CoreTm_Match scrut arms)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 9: CoreTm_Match - first arm body is smaller\<close>
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
  \<comment> \<open>Goal 10: CoreTm_Match - tail arm bodies are smaller\<close>
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
  \<comment> \<open>Goal 11: CoreTm_Allocated - tm is smaller\<close>
  fix env :: CoreTyEnv
  fix tm
  show "((env, Ghost, tm), env, Ghost, CoreTm_Allocated tm)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 12: CoreTm_Let - rhs is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix var rhs body
  show "((env, ghost, rhs), env, ghost, CoreTm_Let var rhs body)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 13: CoreTm_Let - body is smaller (with extended env)\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix var rhs body x2 x
  assume "core_term_type env ghost rhs = Some x2"
    and "x = env \<lparr> TE_TermVars := fmupd var x2 (TE_TermVars env),
                    TE_GhostVars := if ghost = Ghost then finsert var (TE_GhostVars env)
                                    else fminus (TE_GhostVars env) {|var|} \<rparr>"
  show "((x, ghost, body), env, ghost, CoreTm_Let var rhs body)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 14: CoreTm_RecordProj - tm is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix tm fldName
  show "((env, ghost, tm), env, ghost, CoreTm_RecordProj tm fldName)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 15: CoreTm_ArrayProj - arr is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix arr idxTms
  show "((env, ghost, arr), env, ghost, CoreTm_ArrayProj arr idxTms)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 16: CoreTm_ArrayProj - elements of idxTms are smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix arr idxTms x2 x xa
  fix z :: CoreTerm
  assume "z \<in> set idxTms"
  hence "size z < Suc (size_list size idxTms)"
    using size_list_estimation
    by (metis less_not_refl not_less_eq)
  thus "((env, ghost, z), env, ghost, CoreTm_ArrayProj arr idxTms)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>Goal 17: CoreTm_VariantProj - tm is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix tm ctorName
  show "((env, ghost, tm), env, ghost, CoreTm_VariantProj tm ctorName)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
qed


(* ========================================================================== *)
(* Properties of core_term_type *)
(* ========================================================================== *)


(* Weakening/irrelevance: adding a variable to the environment that is not free
   in the term does not affect typing. The ghost vars set may be arbitrarily
   modified at x (to allow for both ghost and non-ghost bindings), as long as
   all other variables' ghost status is preserved. *)
lemma core_term_type_irrelevant_var:
  assumes "x \<notin> core_term_free_vars tm"
    and "core_term_type env ghost tm = Some ty"
    and "\<forall>y. y \<noteq> x \<longrightarrow> (y |\<in>| gv' \<longleftrightarrow> y |\<in>| TE_GhostVars env)"
  shows "core_term_type
           (env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env),
                  TE_GhostVars := gv' \<rparr>)
           ghost tm = Some ty"
using assms proof (induction tm arbitrary: env ghost ty gv')
  case (CoreTm_LitBool b)
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray tms)
  then show ?case sorry
next
  case (CoreTm_Var name)
  \<comment> \<open>x \<noteq> name because x \<notin> {name}\<close>
  from CoreTm_Var.prems(1) have neq: "name \<noteq> x" by simp
  from CoreTm_Var.prems(2) obtain varTy where
    lookup: "fmlookup (TE_TermVars env) name = Some varTy" and
    ghost_ok: "ghost = NotGhost \<longrightarrow> name |\<notin>| TE_GhostVars env" and
    ty_eq: "ty = varTy"
    by (auto split: option.splits if_splits)
  have lookup': "fmlookup (fmupd x ty' (TE_TermVars env)) name = Some varTy"
    using lookup neq by simp
  have ghost_ok': "ghost = NotGhost \<longrightarrow> name |\<notin>| gv'"
    using ghost_ok CoreTm_Var.prems(3) neq by blast
  show ?case using lookup' ghost_ok' ty_eq by simp
next
  case (CoreTm_Cast targetTy operand)
  from CoreTm_Cast.prems(1) have "x \<notin> core_term_free_vars operand" by simp
  from CoreTm_Cast.prems(2) obtain operandTy where
    operand_typed: "core_term_type env ghost operand = Some operandTy"
    by (auto split: option.splits if_splits)
  have IH: "core_term_type (env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env),
                                   TE_GhostVars := gv' \<rparr>) ghost operand = Some operandTy"
    using CoreTm_Cast.IH CoreTm_Cast.prems by (simp add: operand_typed)
  show ?case using CoreTm_Cast.prems(2) operand_typed IH by simp
next
  case (CoreTm_Unop op operand)
  from CoreTm_Unop.prems(1) have "x \<notin> core_term_free_vars operand" by simp
  from CoreTm_Unop.prems(2) obtain operandTy where
    operand_typed: "core_term_type env ghost operand = Some operandTy"
    by (auto split: option.splits)
  have IH: "core_term_type (env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env),
                                   TE_GhostVars := gv' \<rparr>) ghost operand = Some operandTy"
    using CoreTm_Unop.IH CoreTm_Unop.prems by (simp add: operand_typed)
  show ?case using CoreTm_Unop.prems(2) operand_typed IH by simp
next
  case (CoreTm_Binop op lhs rhs)
  from CoreTm_Binop.prems(1) have
    lhs_fresh: "x \<notin> core_term_free_vars lhs" and
    rhs_fresh: "x \<notin> core_term_free_vars rhs" by auto
  from CoreTm_Binop.prems(2) obtain lhsTy rhsTy where
    lhs_typed: "core_term_type env ghost lhs = Some lhsTy" and
    rhs_typed: "core_term_type env ghost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)
  let ?env' = "env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env), TE_GhostVars := gv' \<rparr>"
  have lhs_IH: "core_term_type ?env' ghost lhs = Some lhsTy"
    using CoreTm_Binop.IH(1) lhs_fresh lhs_typed CoreTm_Binop.prems(3) by blast
  have rhs_IH: "core_term_type ?env' ghost rhs = Some rhsTy"
    using CoreTm_Binop.IH(2) rhs_fresh rhs_typed CoreTm_Binop.prems(3) by blast
  show ?case using CoreTm_Binop.prems(2) lhs_typed rhs_typed lhs_IH rhs_IH by simp
next
  case (CoreTm_Let var rhs body)
  from CoreTm_Let.prems(1) have
    rhs_fresh: "x \<notin> core_term_free_vars rhs" and
    body_fresh: "x \<noteq> var \<longrightarrow> x \<notin> core_term_free_vars body" by auto
  from CoreTm_Let.prems(2) obtain rhsTy where
    rhs_typed: "core_term_type env ghost rhs = Some rhsTy" and
    rhs_ground: "is_ground rhsTy"
    by (auto simp: Let_def split: option.splits if_splits)
  let ?gv_let = "if ghost = Ghost then finsert var (TE_GhostVars env)
                  else fminus (TE_GhostVars env) {|var|}"
  let ?env_let = "env \<lparr> TE_TermVars := fmupd var rhsTy (TE_TermVars env),
                        TE_GhostVars := ?gv_let \<rparr>"
  from CoreTm_Let.prems(2) rhs_typed rhs_ground have
    body_typed: "core_term_type ?env_let ghost body = Some ty"
    by (auto simp: Let_def split: option.splits if_splits)
  let ?env' = "env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env), TE_GhostVars := gv' \<rparr>"
  \<comment> \<open>IH on rhs\<close>
  have rhs_IH: "core_term_type ?env' ghost rhs = Some rhsTy"
    using CoreTm_Let.IH(1) rhs_fresh rhs_typed CoreTm_Let.prems(3) by blast
  \<comment> \<open>IH on body - two subcases\<close>
  let ?gv_let' = "if ghost = Ghost then finsert var gv' else fminus gv' {|var|}"
  let ?env_let' = "env \<lparr> TE_TermVars := fmupd var rhsTy (fmupd x ty' (TE_TermVars env)),
                         TE_GhostVars := ?gv_let' \<rparr>"
  have body_IH: "core_term_type ?env_let' ghost body = Some ty"
  proof (cases "x = var")
    case True
    \<comment> \<open>fmupd var overwrites fmupd x since x = var\<close>
    have "fmupd var rhsTy (fmupd x ty' (TE_TermVars env)) = fmupd var rhsTy (TE_TermVars env)"
      using True by simp
    \<comment> \<open>Ghost vars also agree since var = x overwrites\<close>
    moreover have "?gv_let' = ?gv_let"
    proof -
      have "\<And>y. y |\<in>| ?gv_let' \<longleftrightarrow> y |\<in>| ?gv_let"
      proof -
        fix y
        show "y |\<in>| ?gv_let' \<longleftrightarrow> y |\<in>| ?gv_let"
        proof (cases "y = var")
          case True
          then show ?thesis by (cases "ghost = Ghost") auto
        next
          case False
          hence "y \<noteq> x" using \<open>x = var\<close> by simp
          then show ?thesis using CoreTm_Let.prems(3) by (cases "ghost = Ghost") auto
        qed
      qed
      thus ?thesis by (simp add: fset_eqI)
    qed
    ultimately show ?thesis using body_typed by simp
  next
    case False
    hence body_fresh': "x \<notin> core_term_free_vars body" using body_fresh by blast
    \<comment> \<open>Ghost vars condition for IH: gv_let' agrees with TE_GhostVars env_let except at x\<close>
    have gv_cond: "\<forall>y. y \<noteq> x \<longrightarrow> (y |\<in>| ?gv_let' \<longleftrightarrow> y |\<in>| TE_GhostVars ?env_let)"
    proof (intro allI impI)
      fix y assume "y \<noteq> x"
      show "y |\<in>| ?gv_let' \<longleftrightarrow> y |\<in>| TE_GhostVars ?env_let"
      proof (cases "y = var")
        case True
        then show ?thesis by (cases "ghost = Ghost") auto
      next
        case yneqvar: False
        show ?thesis using CoreTm_Let.prems(3) \<open>y \<noteq> x\<close>
          by (cases "ghost = Ghost") auto
      qed
    qed
    \<comment> \<open>Apply IH to body in env_let\<close>
    have body_in_ext: "core_term_type
        (?env_let \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars ?env_let),
                    TE_GhostVars := ?gv_let' \<rparr>)
        ghost body = Some ty"
      using CoreTm_Let.IH(2)[OF body_fresh' body_typed gv_cond] .
    \<comment> \<open>Rewrite to match env_let'\<close>
    show ?thesis using body_in_ext False by (simp add: fmupd_reorder_neq)
  qed
  \<comment> \<open>Combine\<close>
  show ?case using rhs_IH rhs_ground body_IH by (cases "ghost = Ghost") (auto simp: Let_def)
next
  case (CoreTm_Quantifier quant var varTy body)
  then show ?case sorry
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  from CoreTm_FunctionCall.prems(1) have
    args_fresh: "\<forall>tm \<in> set tmArgs. x \<notin> core_term_free_vars tm" by auto
  let ?env' = "env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env), TE_GhostVars := gv' \<rparr>"
  \<comment> \<open>TE_Functions, TE_Datatypes, TE_TypeVars are unchanged\<close>
  have fields_eq: "TE_Functions ?env' = TE_Functions env"
                   "TE_Datatypes ?env' = TE_Datatypes env"
                   "TE_TypeVars ?env' = TE_TypeVars env"
    by simp_all
  have wk_eq: "\<And>t. is_well_kinded ?env' t = is_well_kinded env t"
    using is_well_kinded_cong_env[of ?env' env] fields_eq by simp
  \<comment> \<open>Each term argument typechecks the same way in the extended env\<close>
  have args_IH: "\<And>tm argTy. tm \<in> set tmArgs \<Longrightarrow>
    core_term_type env ghost tm = Some argTy \<Longrightarrow>
    core_term_type ?env' ghost tm = Some argTy"
    using CoreTm_FunctionCall.IH args_fresh CoreTm_FunctionCall.prems(3) by blast
  \<comment> \<open>Extract facts from the original typing\<close>
  from CoreTm_FunctionCall.prems(2) obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    len_tmargs: "length tmArgs = length (FI_TmArgs funInfo)" and
    ghost_ok: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type tyArgs \<and> FI_Ghost funInfo \<noteq> Ghost"
    by (auto simp: Let_def split: option.splits if_splits)
  let ?tySubst = "fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)"
  let ?expectedArgTypes = "map (apply_subst ?tySubst) (FI_TmArgs funInfo)"
  from CoreTm_FunctionCall.prems(2) fn_lookup len_tyargs tyargs_wk len_tmargs ghost_ok have
    args_check: "list_all2 (\<lambda>tm expectedTy.
        case core_term_type env ghost tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
      tmArgs ?expectedArgTypes" and
    ty_eq: "ty = apply_subst ?tySubst (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: option.splits if_splits)
  \<comment> \<open>Transform the list_all2 check to use the extended env\<close>
  have len_eq: "length tmArgs = length ?expectedArgTypes"
    using len_tmargs by simp
  have args_check': "list_all2 (\<lambda>tm expectedTy.
      case core_term_type ?env' ghost tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
    tmArgs ?expectedArgTypes"
  proof (rule list_all2_all_nthI[OF len_eq])
    fix i assume i_bound: "i < length tmArgs"
    let ?tm = "tmArgs ! i"
    let ?ety = "?expectedArgTypes ! i"
    have tm_in: "?tm \<in> set tmArgs" using i_bound by simp
    from args_check i_bound len_eq have
      check: "(case core_term_type env ghost ?tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = ?ety)"
      by (auto dest: list_all2_nthD)
    from check obtain actualTy where
      tm_typed: "core_term_type env ghost ?tm = Some actualTy" and actual_eq: "actualTy = ?ety"
      by (auto split: option.splits)
    have "core_term_type ?env' ghost ?tm = Some actualTy"
      using args_IH[OF tm_in tm_typed] .
    thus "(case core_term_type ?env' ghost ?tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = ?ety)"
      using actual_eq by simp
  qed
  have tyargs_wk': "list_all (is_well_kinded ?env') tyArgs"
    using tyargs_wk wk_eq by (simp add: list_all_iff)
  show ?case
    using fn_lookup len_tyargs tyargs_wk' len_tmargs ghost_ok args_check' ty_eq fields_eq
    by (simp add: Let_def)
next
  case (CoreTm_VariantCtor ctorName tyArgs tm)
  from CoreTm_VariantCtor.prems(1) have tm_fresh: "x \<notin> core_term_free_vars tm" by simp
  let ?env' = "env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env), TE_GhostVars := gv' \<rparr>"
  have fields_eq: "TE_DataCtors ?env' = TE_DataCtors env"
                   "TE_Datatypes ?env' = TE_Datatypes env"
                   "TE_TypeVars ?env' = TE_TypeVars env"
    by simp_all
  have wk_eq: "\<And>t. is_well_kinded ?env' t = is_well_kinded env t"
    using is_well_kinded_cong_env[of ?env' env] fields_eq by simp
  from CoreTm_VariantCtor.prems(2) obtain dtName metavars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, metavars, payloadTy)"
    by (auto simp: Let_def split: option.splits prod.splits if_splits)
  from CoreTm_VariantCtor.prems(2) ctor_lookup obtain payloadActualTy where
    len_eq: "length tyArgs = length metavars" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    tyargs_rt: "ghost = NotGhost \<longrightarrow> list_all is_runtime_type tyArgs" and
    payload_typed: "core_term_type env ghost tm = Some payloadActualTy" and
    payload_ty_eq: "payloadActualTy = apply_subst (fmap_of_list (zip metavars tyArgs)) payloadTy" and
    ty_eq: "ty = CoreTy_Name dtName tyArgs"
    by (auto simp: Let_def split: option.splits prod.splits if_splits)
  have payload_IH: "core_term_type ?env' ghost tm = Some payloadActualTy"
    using CoreTm_VariantCtor.IH tm_fresh payload_typed CoreTm_VariantCtor.prems(3) by blast
  have tyargs_wk': "list_all (is_well_kinded ?env') tyArgs"
    using tyargs_wk wk_eq by (simp add: list_all_iff)
  show ?case using ctor_lookup len_eq tyargs_wk' tyargs_rt payload_IH payload_ty_eq ty_eq
    fields_eq by (simp add: Let_def)
next
  case (CoreTm_Record flds)
  then show ?case sorry
next
  case (CoreTm_RecordProj tm fldName)
  from CoreTm_RecordProj.prems(1) have tm_fresh: "x \<notin> core_term_free_vars tm" by simp
  from CoreTm_RecordProj.prems(2) obtain recTy where
    tm_typed: "core_term_type env ghost tm = Some recTy"
    by (auto split: option.splits CoreType.splits)
  have tm_IH: "core_term_type (env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env),
                                      TE_GhostVars := gv' \<rparr>) ghost tm = Some recTy"
    using CoreTm_RecordProj.IH tm_fresh tm_typed CoreTm_RecordProj.prems(3) by blast
  show ?case using CoreTm_RecordProj.prems(2) tm_typed tm_IH by simp
next
  case (CoreTm_ArrayProj arr idxs)
  from CoreTm_ArrayProj.prems(1) have
    arr_fresh: "x \<notin> core_term_free_vars arr" and
    idxs_fresh: "\<forall>idx \<in> set idxs. x \<notin> core_term_free_vars idx" by auto
  let ?env' = "env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env), TE_GhostVars := gv' \<rparr>"
  have wk_eq: "\<And>t. is_well_kinded ?env' t = is_well_kinded env t"
    using is_well_kinded_cong_env[of ?env' env] by simp
  from CoreTm_ArrayProj.prems(2) obtain arrTy where
    arr_typed: "core_term_type env ghost arr = Some arrTy"
    by (auto split: option.splits CoreType.splits if_splits)
  have arr_IH: "core_term_type ?env' ghost arr = Some arrTy"
    using CoreTm_ArrayProj.IH(1) arr_fresh arr_typed CoreTm_ArrayProj.prems(3) by blast
  have idxs_IH: "\<And>idx idxTy. idx \<in> set idxs \<Longrightarrow>
    core_term_type env ghost idx = Some idxTy \<Longrightarrow>
    core_term_type ?env' ghost idx = Some idxTy"
    using CoreTm_ArrayProj.IH(2) idxs_fresh CoreTm_ArrayProj.prems(3) by blast
  show ?case
  proof (cases arrTy)
    case (CoreTy_Array elemTy dims)
    from CoreTm_ArrayProj.prems(2) arr_typed CoreTy_Array have
      len_eq: "length idxs = length dims" and
      idxs_typed: "list_all (\<lambda>tm. core_term_type env ghost tm
                     = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxs" and
      ty_eq: "ty = elemTy"
      by (auto split: option.splits CoreType.splits if_splits)
    have idxs_typed': "list_all (\<lambda>tm. core_term_type ?env' ghost tm
                        = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxs"
      using idxs_typed idxs_IH by (simp add: list_all_iff)
    show ?thesis using arr_IH idxs_typed' len_eq ty_eq CoreTy_Array by simp
  next
  qed (use CoreTm_ArrayProj.prems(2) arr_typed in \<open>auto split: CoreType.splits\<close>)
next
  case (CoreTm_VariantProj tm ctorName)
  from CoreTm_VariantProj.prems(1) have tm_fresh: "x \<notin> core_term_free_vars tm" by simp
  let ?env' = "env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env), TE_GhostVars := gv' \<rparr>"
  have fields_eq: "TE_DataCtors ?env' = TE_DataCtors env" by simp
  from CoreTm_VariantProj.prems(2) obtain dtName tyArgs where
    tm_typed: "core_term_type env ghost tm = Some (CoreTy_Name dtName tyArgs)"
    by (auto split: option.splits CoreType.splits prod.splits if_splits)
  from CoreTm_VariantProj.prems(2) tm_typed obtain dtName2 metavars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, metavars, payloadTy)" and
    dt_eq: "dtName = dtName2" and
    len_eq: "length tyArgs = length metavars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip metavars tyArgs)) payloadTy"
    by (auto split: option.splits prod.splits if_splits)
  have tm_IH: "core_term_type ?env' ghost tm = Some (CoreTy_Name dtName tyArgs)"
    using CoreTm_VariantProj.IH tm_fresh tm_typed CoreTm_VariantProj.prems(3) by blast
  show ?case using tm_IH ctor_lookup dt_eq len_eq ty_eq fields_eq by simp
next
  case (CoreTm_Match scrut arms)
  from CoreTm_Match.prems(1) have
    scrut_fresh: "x \<notin> core_term_free_vars scrut" and
    arms_fresh: "\<forall>arm \<in> set arms. x \<notin> core_term_free_vars (snd arm)" by auto
  let ?env' = "env \<lparr> TE_TermVars := fmupd x ty' (TE_TermVars env), TE_GhostVars := gv' \<rparr>"
  \<comment> \<open>Pattern-related functions only use TE_DataCtors/TE_DataCtorsByType\<close>
  have fields_eq: "TE_DataCtors ?env' = TE_DataCtors env"
                   "TE_DataCtorsByType ?env' = TE_DataCtorsByType env"
    by simp_all
  have pat_compat_eq: "\<And>p t. pattern_compatible ?env' p t = pattern_compatible env p t"
    by (case_tac p) (simp_all add: fields_eq)
  have pat_exhaust_eq: "\<And>t ps. patterns_exhaustive ?env' t ps = patterns_exhaustive env t ps"
    using fields_eq by (simp split: CoreType.splits)
  \<comment> \<open>IH on scrutinee\<close>
  from CoreTm_Match.prems(2) obtain scrutTy where
    scrut_typed: "core_term_type env ghost scrut = Some scrutTy"
    by (auto split: option.splits if_splits)
  have scrut_IH: "core_term_type ?env' ghost scrut = Some scrutTy"
    using CoreTm_Match.IH(1) scrut_fresh scrut_typed CoreTm_Match.prems(3) by blast
  \<comment> \<open>IH on arm bodies\<close>
  have arms_IH: "\<And>arm armTy. arm \<in> set arms \<Longrightarrow>
    core_term_type env ghost (snd arm) = Some armTy \<Longrightarrow>
    core_term_type ?env' ghost (snd arm) = Some armTy"
  proof -
    fix arm armTy
    assume arm_in: "arm \<in> set arms"
      and arm_typed: "core_term_type env ghost (snd arm) = Some armTy"
    have "x \<notin> core_term_free_vars (snd arm)" using arms_fresh arm_in by blast
    moreover have "snd arm \<in> Basic_BNFs.snds arm" by (cases arm) (auto intro: snds.intros)
    ultimately show "core_term_type ?env' ghost (snd arm) = Some armTy"
      using CoreTm_Match.IH(2)[of arm "snd arm"] arm_in arm_typed CoreTm_Match.prems(3)
      by blast
  qed
  \<comment> \<open>Head body typechecks in extended env\<close>
  from CoreTm_Match.prems(2) scrut_typed obtain resultTy where
    arms_nonempty: "arms \<noteq> []" and
    hd_typed: "core_term_type env ghost (snd (hd arms)) = Some resultTy" and
    ty_eq: "ty = resultTy"
    by (auto simp: Let_def split: option.splits if_splits)
  have hd_in: "hd arms \<in> set arms" using arms_nonempty by (cases arms) auto
  have hd_IH: "core_term_type ?env' ghost (snd (hd arms)) = Some resultTy"
    using arms_IH[OF hd_in hd_typed] .
  \<comment> \<open>Tail bodies typecheck in extended env\<close>
  from CoreTm_Match.prems(2) scrut_typed arms_nonempty hd_typed have
    tl_all: "list_all (\<lambda>body. core_term_type env ghost body = Some resultTy) (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)
  have tl_typed: "\<forall>body \<in> set (tl (map snd arms)). core_term_type env ghost body = Some resultTy"
    using tl_all by (simp add: list_all_iff)
  have tl_IH: "\<forall>body \<in> set (tl (map snd arms)). core_term_type ?env' ghost body = Some resultTy"
  proof
    fix body assume "body \<in> set (tl (map snd arms))"
    hence "body \<in> snd ` set arms"
      by (metis list.sel(2) list.set_map list.set_sel(2))
    then obtain arm where arm_in: "arm \<in> set arms" and body_eq: "body = snd arm" by auto
    have "core_term_type env ghost body = Some resultTy"
      using tl_typed \<open>body \<in> set (tl (map snd arms))\<close> by blast
    thus "core_term_type ?env' ghost body = Some resultTy"
      using arms_IH[OF arm_in] body_eq by simp
  qed
  show ?case using scrut_IH hd_IH tl_IH ty_eq arms_nonempty
    pat_compat_eq pat_exhaust_eq CoreTm_Match.prems(2) scrut_typed
    by (auto simp: Let_def list_all_iff split: option.splits if_splits)
next
  case (CoreTm_Sizeof tm)
  then show ?case sorry
next
  case (CoreTm_Allocated tm)
  from CoreTm_Allocated.prems(1) have tm_fresh: "x \<notin> core_term_free_vars tm" by simp
  show ?case using CoreTm_Allocated.prems(2)
    CoreTm_Allocated.IH[OF tm_fresh _ CoreTm_Allocated.prems(3)]
    by (cases ghost) (auto split: option.splits)
next
  case (CoreTm_Old tm)
  then show ?case sorry
qed


(* core_term_type produces well-kinded types, and in NotGhost mode also runtime types.
   These must be proved simultaneously because the CoreTm_Let case
   needs both properties from the IH to show tyenv_well_formed for the extended env. *)
lemma core_term_type_well_kinded_and_runtime:
  assumes "core_term_type env ghost tm = Some ty"
    and "tyenv_well_formed env"
  shows "is_well_kinded env ty \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type ty)"
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
  have wk: "tyenv_vars_well_kinded env"
    using CoreTm_Var.prems(2) tyenv_well_formed_def by blast
  have var_wk: "is_well_kinded env ty"
    using wk lookup ty_eq tyenv_vars_well_kinded_def by blast
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type ty"
  proof
    assume ng: "ghost = NotGhost"
    from CoreTm_Var.prems(1) ng have not_ghost: "name |\<notin>| TE_GhostVars env"
      by (auto split: option.splits if_splits)
    have "tyenv_vars_runtime env"
      using CoreTm_Var.prems(2) tyenv_well_formed_def by blast
    thus "is_runtime_type ty"
      using lookup not_ghost ty_eq tyenv_vars_runtime_def by blast
  qed
  ultimately show ?case by blast
next
  case (CoreTm_Cast targetTy operand)
  then show ?case
    by (auto simp: is_integer_type_well_kinded split: option.splits if_splits)
next
  case (CoreTm_Unop op operand)
  then obtain operandTy where
    operand_typed: "core_term_type env ghost operand = Some operandTy"
    by (auto split: option.splits)
  have IH: "is_well_kinded env operandTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type operandTy)"
    using CoreTm_Unop.IH operand_typed CoreTm_Unop.prems(2) by blast
  show ?case using CoreTm_Unop.prems(1) operand_typed IH
    by (cases op) (auto split: if_splits)
next
  case (CoreTm_Binop op lhs rhs)
  from CoreTm_Binop.prems(1) obtain lhsTy rhsTy where
    lhs_typed: "core_term_type env ghost lhs = Some lhsTy" and
    rhs_typed: "core_term_type env ghost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)
  have lhs_IH: "is_well_kinded env lhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type lhsTy)"
    using CoreTm_Binop.IH(1) lhs_typed CoreTm_Binop.prems(2) by blast
  \<comment> \<open>Result is either lhsTy (arithmetic/modulo/bitwise/shift) or CoreTy_Bool (ordering/eq_neq/logical)\<close>
  show ?case using CoreTm_Binop.prems(1) lhs_typed rhs_typed lhs_IH
    by (auto split: if_splits)
next
  case (CoreTm_Let var tm1 tm2)
  from CoreTm_Let.prems(1) obtain rhsTy where
    rhs_typed: "core_term_type env ghost tm1 = Some rhsTy" and
    rhs_ground: "is_ground rhsTy" and
    body_typed: "core_term_type
      (env \<lparr> TE_TermVars := fmupd var rhsTy (TE_TermVars env),
             TE_GhostVars := (if ghost = Ghost then finsert var (TE_GhostVars env)
                              else fminus (TE_GhostVars env) {|var|}) \<rparr>)
      ghost tm2 = Some ty"
    by (auto simp: Let_def split: option.splits if_splits)
  let ?env' = "env \<lparr> TE_TermVars := fmupd var rhsTy (TE_TermVars env),
                     TE_GhostVars := (if ghost = Ghost then finsert var (TE_GhostVars env)
                                      else fminus (TE_GhostVars env) {|var|}) \<rparr>"
  have rhs_IH: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type rhsTy)"
    using CoreTm_Let.IH(1) rhs_typed CoreTm_Let.prems(2) by blast
  hence rhs_wk: "is_well_kinded env rhsTy" by blast
  have wf_env': "tyenv_well_formed ?env'"
  proof (cases "ghost = Ghost")
    case True
    then show ?thesis
      using tyenv_well_formed_add_ghost_var[OF CoreTm_Let.prems(2) rhs_wk rhs_ground] by simp
  next
    case False
    hence rhs_rt: "is_runtime_type rhsTy" using rhs_IH GhostOrNot.exhaust by auto
    show ?thesis using False
      tyenv_well_formed_add_var[OF CoreTm_Let.prems(2) rhs_wk rhs_ground rhs_rt] by simp
  qed
  have body_IH: "is_well_kinded ?env' ty \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type ty)"
    using CoreTm_Let.IH(2) body_typed wf_env' by blast
  \<comment> \<open>is_well_kinded only depends on TE_TypeVars and TE_Datatypes\<close>
  have env'_fields: "TE_TypeVars ?env' = TE_TypeVars env"
                     "TE_Datatypes ?env' = TE_Datatypes env"
    by simp_all
  have "is_well_kinded env ty"
    using body_IH is_well_kinded_cong_env[OF env'_fields] by simp
  thus ?case using body_IH by blast
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
  \<comment> \<open>Well-kinded part\<close>
  have "tyenv_fun_types_well_kinded env"
    using CoreTm_FunctionCall.prems(2) tyenv_well_formed_def by blast
  hence ret_wk: "is_well_kinded env (FI_ReturnType funInfo)"
    using fn_lookup tyenv_fun_types_well_kinded_def by blast
  have subst_wk: "metasubst_well_kinded env (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs))"
    using tyargs_wk metasubst_well_kinded_from_zip by blast
  have wk: "is_well_kinded env ty"
    using ty_eq ret_wk subst_wk apply_subst_preserves_well_kinded by blast
  \<comment> \<open>Runtime part (NotGhost only)\<close>
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type ty"
  proof
    assume ng: "ghost = NotGhost"
    from CoreTm_FunctionCall.prems(1) ng fn_lookup have
      not_ghost_fn: "FI_Ghost funInfo \<noteq> Ghost" and
      tyargs_rt: "list_all is_runtime_type tyArgs"
      by (auto simp: Let_def split: option.splits if_splits)
    have "tyenv_fun_ghost_constraint env"
      using CoreTm_FunctionCall.prems(2) tyenv_well_formed_def by blast
    hence ret_rt: "is_runtime_type (FI_ReturnType funInfo)"
      using fn_lookup not_ghost_fn tyenv_fun_ghost_constraint_def GhostOrNot.exhaust by blast
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
    show "is_runtime_type ty"
      using ty_eq ret_rt subst_rt apply_subst_preserves_runtime by blast
  qed
  ultimately show ?case by blast
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  from CoreTm_VariantCtor.prems(1) obtain dtName metavars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, metavars, payloadTy)" and
    len_eq: "length tyArgs = length metavars" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    payload_typed: "core_term_type env ghost payload = Some (apply_subst (fmap_of_list (zip metavars tyArgs)) payloadTy)" and
    ty_eq: "ty = CoreTy_Name dtName tyArgs"
    by (auto simp: Let_def split: option.splits prod.splits if_splits)
  \<comment> \<open>Well-kinded: CoreTy_Name dtName tyArgs requires dtName in TE_Datatypes with matching arity\<close>
  have ctors_consistent: "tyenv_ctors_consistent env"
    using CoreTm_VariantCtor.prems(2) tyenv_well_formed_def by blast
  have dt_lookup: "fmlookup (TE_Datatypes env) dtName = Some (length metavars)"
    using ctors_consistent ctor_lookup tyenv_ctors_consistent_def by blast
  have not_tyvar: "dtName |\<notin>| TE_TypeVars env"
  proof
    assume "dtName |\<in>| TE_TypeVars env"
    hence "dtName |\<in>| TE_TypeVars env |\<inter>| fmdom (TE_Datatypes env)"
      using dt_lookup by (simp add: fmdomI)
    moreover have "TE_TypeVars env |\<inter>| fmdom (TE_Datatypes env) = {||}"
      using CoreTm_VariantCtor.prems(2) tyenv_well_formed_def
        tyenv_tyvars_datatypes_disjoint_def by blast
    ultimately show False by simp
  qed
  have wk: "is_well_kinded env ty"
    using ty_eq dt_lookup len_eq tyargs_wk not_tyvar by simp
  \<comment> \<open>Runtime: CoreTy_Name dtName tyArgs requires list_all is_runtime_type tyArgs\<close>
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type ty"
  proof
    assume ng: "ghost = NotGhost"
    from CoreTm_VariantCtor.prems(1) ng ctor_lookup len_eq have
      tyargs_rt: "list_all is_runtime_type tyArgs"
      by (auto simp: Let_def split: option.splits prod.splits if_splits)
    show "is_runtime_type ty" using ty_eq tyargs_rt by simp
  qed
  ultimately show ?case by blast
next
  case (CoreTm_Record x)
  then show ?case sorry
next
  case (CoreTm_RecordProj tm fldName)
  from CoreTm_RecordProj.prems(1) obtain flds where
    tm_typed: "core_term_type env ghost tm = Some (CoreTy_Record flds)" and
    fld_lookup: "map_of flds fldName = Some ty"
    by (auto split: option.splits CoreType.splits)
  have IH: "is_well_kinded env (CoreTy_Record flds) \<and>
            (ghost = NotGhost \<longrightarrow> is_runtime_type (CoreTy_Record flds))"
    using CoreTm_RecordProj.IH tm_typed CoreTm_RecordProj.prems(2) by blast
  have fld_in_set: "ty \<in> snd ` set flds"
    using fld_lookup
    by (metis Range_iff Range_snd map_of_SomeD)
  have wk: "is_well_kinded env ty"
    using IH fld_in_set by (auto simp: list_all_iff)
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type ty"
    using IH fld_in_set by (auto simp: list_all_iff)
  ultimately show ?case by blast
next
  case (CoreTm_ArrayProj arr idxs)
  from CoreTm_ArrayProj.prems(1) obtain elemTy dims where
    arr_typed: "core_term_type env ghost arr = Some (CoreTy_Array elemTy dims)" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)
  have IH: "is_well_kinded env (CoreTy_Array elemTy dims) \<and>
            (ghost = NotGhost \<longrightarrow> is_runtime_type (CoreTy_Array elemTy dims))"
    using CoreTm_ArrayProj.IH(1) arr_typed CoreTm_ArrayProj.prems(2) by blast
  have wk: "is_well_kinded env ty"
    using IH ty_eq by simp
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type ty"
    using IH ty_eq by simp
  ultimately show ?case by blast
next
  case (CoreTm_VariantProj tm ctorName)
  from CoreTm_VariantProj.prems(1) obtain dtName tyArgs where
    tm_typed: "core_term_type env ghost tm = Some (CoreTy_Name dtName tyArgs)"
    by (auto split: option.splits CoreType.splits prod.splits if_splits)
  from CoreTm_VariantProj.prems(1) tm_typed obtain dtName2 metavars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, metavars, payloadTy)" and
    dt_eq: "dtName = dtName2" and
    len_eq: "length tyArgs = length metavars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip metavars tyArgs)) payloadTy"
    by (auto split: option.splits prod.splits if_splits)
  \<comment> \<open>Well-kinded: apply_subst preserves well-kindedness\<close>
  have payload_wk: "is_well_kinded env payloadTy"
    using CoreTm_VariantProj.prems(2) ctor_lookup tyenv_well_formed_def
      tyenv_payloads_well_kinded_def by blast
  have tm_IH: "is_well_kinded env (CoreTy_Name dtName tyArgs) \<and>
               (ghost = NotGhost \<longrightarrow> is_runtime_type (CoreTy_Name dtName tyArgs))"
    using CoreTm_VariantProj.IH tm_typed CoreTm_VariantProj.prems(2) by blast
  hence tyargs_wk: "list_all (is_well_kinded env) tyArgs"
  proof -
    have ctors_consistent: "tyenv_ctors_consistent env"
      using CoreTm_VariantProj.prems(2) tyenv_well_formed_def by blast
    have dt_lookup: "fmlookup (TE_Datatypes env) dtName = Some (length metavars)"
      using ctors_consistent ctor_lookup dt_eq tyenv_ctors_consistent_def by blast
    have not_tyvar: "dtName |\<notin>| TE_TypeVars env"
    proof
      assume "dtName |\<in>| TE_TypeVars env"
      hence "dtName |\<in>| TE_TypeVars env |\<inter>| fmdom (TE_Datatypes env)"
        using dt_lookup by (simp add: fmdomI)
      moreover have "TE_TypeVars env |\<inter>| fmdom (TE_Datatypes env) = {||}"
        using CoreTm_VariantProj.prems(2) tyenv_well_formed_def
          tyenv_tyvars_datatypes_disjoint_def by blast
      ultimately show False by simp
    qed
    from tm_IH show ?thesis using dt_lookup not_tyvar by simp
  qed
  have subst_wk: "metasubst_well_kinded env (fmap_of_list (zip metavars tyArgs))"
    using tyargs_wk metasubst_well_kinded_from_zip by blast
  have wk: "is_well_kinded env ty"
    using ty_eq payload_wk subst_wk apply_subst_preserves_well_kinded by blast
  \<comment> \<open>Runtime: need tyenv_payloads_runtime (not yet in tyenv_well_formed)
     TODO: Add tyenv_payloads_runtime to tyenv_well_formed to close this sorry\<close>
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type ty" sorry
  ultimately show ?case by blast
next
  case (CoreTm_Match scrut arms)
  from CoreTm_Match.prems(1) obtain scrutTy where
    scrut_typed: "core_term_type env ghost scrut = Some scrutTy" and
    arms_nonempty: "arms \<noteq> []"
    by (auto simp: Let_def split: option.splits if_splits)
  from CoreTm_Match.prems(1) scrut_typed arms_nonempty obtain resultTy where
    first_body_typed: "core_term_type env ghost (snd (hd arms)) = Some resultTy" and
    ty_eq: "ty = resultTy"
    by (auto simp: Let_def split: option.splits if_splits)
  have "snd (hd arms) \<in> snd ` set arms"
    using arms_nonempty by (cases arms) auto
  have IH: "is_well_kinded env resultTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type resultTy)"
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

(* Corollaries for convenient use at call sites *)
lemma core_term_type_well_kinded:
  assumes "core_term_type env ghost tm = Some ty"
    and "tyenv_well_formed env"
  shows "is_well_kinded env ty"
  using core_term_type_well_kinded_and_runtime[OF assms] by blast

lemma core_term_type_notghost_runtime:
  assumes "core_term_type env NotGhost tm = Some ty"
    and "tyenv_well_formed env"
  shows "is_runtime_type ty"
  using core_term_type_well_kinded_and_runtime[OF assms] by blast


end

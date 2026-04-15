theory CoreTypecheck
  imports CoreTyEnvWellFormed CoreFreeVars "../util/NatToString"
begin

(* ========================================================================== *)
(* Auxiliary lemma for 'those' *)
(* ========================================================================== *)

lemma those_eq_Some:
  "those xs = Some ys \<longleftrightarrow> list_all2 (\<lambda>x y. x = Some y) xs ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then show ?case by (cases x) (auto simp: list_all2_Cons1)
qed

(* ========================================================================== *)
(* Helper: sizeof result type, mirroring array_size_to_value in CoreInterp *)
(* ========================================================================== *)

definition u64_type :: CoreType where
  "u64_type = CoreTy_FiniteInt Unsigned IntBits_64"

fun sizeof_type :: "CoreDimension list \<Rightarrow> CoreType" where
  "sizeof_type [_] = u64_type"
| "sizeof_type dims = CoreTy_Record (zip (tuple_field_names (length dims))
                                         (replicate (length dims) u64_type))"

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
          CoreTy_Datatype tyName _ \<Rightarrow> tyName = dtName
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
     | CoreTy_Datatype dtName _ \<Rightarrow>
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

  (* Array literals - fixed sized array type *)
| "core_term_type env ghost (CoreTm_LitArray elemTy tms) =
    (if is_well_kinded env elemTy
       \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env elemTy)
       \<and> list_all (\<lambda>tm. core_term_type env ghost tm = Some elemTy) tms
       \<and> int_in_range (int_range Unsigned IntBits_64) (int (length tms))
     then Some (CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))])
     else None)"

  (* Variables - must be found in locals or globals, and (in NotGhost mode) cannot be ghost *)
| "core_term_type env ghost (CoreTm_Var name) =
    (case tyenv_lookup_var env name of
      Some ty \<Rightarrow> if (ghost = NotGhost \<longrightarrow> \<not> tyenv_var_ghost env name) then Some ty else None
    | None \<Rightarrow> None)"

  (* Casts - only integer-to-integer for now *)
| "core_term_type env ghost (CoreTm_Cast targetTy operand) =
    (case core_term_type env ghost operand of
      None \<Rightarrow> None
    | Some operandTy \<Rightarrow> 
        if is_integer_type operandTy
        \<and> is_integer_type targetTy
        \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env targetTy) then
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

  (* Let *)
| "core_term_type env ghost (CoreTm_Let var rhs body) =
    (case core_term_type env ghost rhs of
      Some rhsTy \<Rightarrow>
        let env' = env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                         TE_GhostLocals := (if ghost = Ghost
                                          then finsert var (TE_GhostLocals env)
                                          else fminus (TE_GhostLocals env) {|var|}),
                         TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>
        in core_term_type env' ghost body
    | None \<Rightarrow> None)"

  (* Quantifier - Ghost mode only *)
| "core_term_type env NotGhost (CoreTm_Quantifier _ _ _ _) = None"
| "core_term_type env Ghost (CoreTm_Quantifier quant var varTy body) =
    (if is_well_kinded env varTy
     then let env' = env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                           TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>
          in (case core_term_type env' Ghost body of
                Some CoreTy_Bool \<Rightarrow> Some CoreTy_Bool
              | _ \<Rightarrow> None)
     else None)"

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
        else if ghost = NotGhost \<and> (\<not> list_all (is_runtime_type env) tyArgs \<or> FI_Ghost funInfo = Ghost)
             then None
        \<comment> \<open>Term-level calls must be pure: no Ref arguments, not impure\<close>
        else if \<not> list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo) then None
        else if FI_Impure funInfo then None
        \<comment> \<open>Check number of term arguments\<close>
        else if length tmArgs \<noteq> length (FI_TmArgs funInfo) then None
        else
          let tySubst = fmap_of_list (zip (FI_TyArgs funInfo) tyArgs);
              expectedArgTypes = map (\<lambda>(_, ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo)
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
   - Number of type arguments must match the constructor's type-vars
   - Type arguments must be well-kinded
   - In NotGhost mode: type arguments must be runtime types
   - Payload must typecheck to the expected payload type (after substitution) *)
| "core_term_type env ghost (CoreTm_VariantCtor ctorName tyArgs payload) =
    (case fmlookup (TE_DataCtors env) ctorName of
      None \<Rightarrow> None
    | Some (dtName, tyvars, payloadTy) \<Rightarrow>
        (if length tyArgs \<noteq> length tyvars then None
        else if \<not> list_all (is_well_kinded env) tyArgs then None
        else if ghost = NotGhost \<and> (\<not> list_all (is_runtime_type env) tyArgs
               \<or> dtName |\<in>| TE_GhostDatatypes env) then None
        else let tySubst = fmap_of_list (zip tyvars tyArgs)
             in case core_term_type env ghost payload of
                  None \<Rightarrow> None
                | Some actualPayloadTy \<Rightarrow>
                    if actualPayloadTy = apply_subst tySubst payloadTy
                    then Some (CoreTy_Datatype dtName tyArgs)
                    else None))"

  (* Record construction *)
| "core_term_type env ghost (CoreTm_Record flds) =
    (case those (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) of
       None \<Rightarrow> None
     | Some tys \<Rightarrow> Some (CoreTy_Record (zip (map fst flds) tys)))"

  (* Record field projection *)
| "core_term_type env ghost (CoreTm_RecordProj tm fldName) =
    (case core_term_type env ghost tm of
      Some (CoreTy_Record fieldTypes) \<Rightarrow> map_of fieldTypes fldName
    | _ \<Rightarrow> None)"

  (* Array projection (indexing) *)
| "core_term_type env ghost (CoreTm_ArrayProj arr idxTms) =
    (case core_term_type env ghost arr of
      Some (CoreTy_Array elemTy dims) \<Rightarrow>
        if length idxTms = length dims
        \<and> list_all (\<lambda>tm. core_term_type env ghost tm
                          = Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms
        then Some elemTy
        else None
    | _ \<Rightarrow> None)"

  (* Variant projection (extract payload) - constructor name must match *)
| "core_term_type env ghost (CoreTm_VariantProj tm ctorName) =
    (case core_term_type env ghost tm of
      Some (CoreTy_Datatype dtName tyArgs) \<Rightarrow>
        (case fmlookup (TE_DataCtors env) ctorName of
          Some (dtName2, tyvars, payloadTy) \<Rightarrow>
            if dtName = dtName2 \<and> length tyArgs = length tyvars
            then Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)
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

  (* Get size of an array *)
| "core_term_type env ghost (CoreTm_Sizeof tm) =
    (case core_term_type env ghost tm of
      Some (CoreTy_Array _ dims) \<Rightarrow>
        if list_ex (\<lambda>d. d = CoreDim_Allocatable) dims \<and> \<not> is_lvalue tm \<and> ghost = NotGhost
        then None
        else Some (sizeof_type dims)
    | _ \<Rightarrow> None)"

  (* Allocated: Ghost only, parameter can be any type, result is bool *)
| "core_term_type env NotGhost (CoreTm_Allocated _) = None"
| "core_term_type env Ghost (CoreTm_Allocated tm) =
    (case core_term_type env Ghost tm of
      Some _ \<Rightarrow> Some CoreTy_Bool
    | None \<Rightarrow> None)"

  (* Old: Ghost only *)
| "core_term_type env NotGhost (CoreTm_Old _) = None"
| "core_term_type env Ghost (CoreTm_Old tm) = core_term_type env Ghost tm"

  by pat_completeness auto

termination
proof (relation "measure (\<lambda>(env, ghost, tm). size tm)")
  \<comment> \<open>Well-foundedness\<close>
  show "wf (measure (\<lambda>(env, ghost, tm). size tm))" by simp
next
  \<comment> \<open>CoreTm_LitArray - elements are smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix elemTy :: CoreType
  fix tms :: "CoreTerm list"
  fix z :: CoreTerm
  assume "z \<in> set tms"
  hence "size z < Suc (size_list size tms)"
    using size_list_estimation
    by (metis less_not_refl not_less_eq)
  thus "((env, ghost, z), env, ghost, CoreTm_LitArray elemTy tms)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Cast - operand is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix targetTy operand
  show "((env, ghost, operand), env, ghost, CoreTm_Cast targetTy operand)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Unop - operand is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix op operand
  show "((env, ghost, operand), env, ghost, CoreTm_Unop op operand)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Binop - lhs is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix op lhs rhs
  show "((env, ghost, lhs), env, ghost, CoreTm_Binop op lhs rhs)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Binop - rhs is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix op lhs rhs
  show "((env, ghost, rhs), env, ghost, CoreTm_Binop op lhs rhs)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_FunctionCall - elements of tmArgs are smaller\<close>
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
  \<comment> \<open>CoreTm_VariantCtor - payload is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix ctorName tyArgs payload
  show "((env, ghost, payload), env, ghost, CoreTm_VariantCtor ctorName tyArgs payload)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Record - field terms are smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix flds :: "(string \<times> CoreTerm) list"
  fix x :: "string \<times> CoreTerm"
  fix xa :: string
  fix y :: CoreTerm
  assume "x \<in> set flds" and "(xa, y) = x"
  hence "(xa, y) \<in> set flds" by simp
  hence "size_prod (\<lambda>_::string. 0) size (xa, y) \<le>
         size_list (size_prod (\<lambda>_. 0) size) flds"
    by (simp add: size_list_estimation')
  thus "((env, ghost, y), env, ghost, CoreTm_Record flds)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Match - scrutinee is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix scrut arms
  show "((env, ghost, scrut), env, ghost, CoreTm_Match scrut arms)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Match - first arm body is smaller\<close>
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
  \<comment> \<open>CoreTm_Match - tail arm bodies are smaller\<close>
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
  \<comment> \<open>CoreTm_Allocated - tm is smaller\<close>
  fix env :: CoreTyEnv
  fix tm
  show "((env, Ghost, tm), env, Ghost, CoreTm_Allocated tm)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Let - rhs is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix var rhs body
  show "((env, ghost, rhs), env, ghost, CoreTm_Let var rhs body)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Quantifier - body is smaller (with extended env)\<close>
  fix env :: CoreTyEnv
  fix quant var varTy body x
  assume "x = env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                     TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>"
  show "((x, Ghost, body), env, Ghost, CoreTm_Quantifier quant var varTy body)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Let - body is smaller (with extended env)\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix var rhs body x2 x
  assume "core_term_type env ghost rhs = Some x2"
    and "x = env \<lparr> TE_LocalVars := fmupd var x2 (TE_LocalVars env),
                    TE_GhostLocals := if ghost = Ghost then finsert var (TE_GhostLocals env)
                                    else fminus (TE_GhostLocals env) {|var|},
                    TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  show "((x, ghost, body), env, ghost, CoreTm_Let var rhs body)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_RecordProj - tm is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix tm fldName
  show "((env, ghost, tm), env, ghost, CoreTm_RecordProj tm fldName)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_ArrayProj - arr is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix arr idxTms
  show "((env, ghost, arr), env, ghost, CoreTm_ArrayProj arr idxTms)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_ArrayProj - elements of idxTms are smaller\<close>
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
  \<comment> \<open>CoreTm_VariantProj - tm is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix tm ctorName
  show "((env, ghost, tm), env, ghost, CoreTm_VariantProj tm ctorName)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Sizeof - tm is smaller\<close>
  fix env :: CoreTyEnv
  fix ghost :: GhostOrNot
  fix tm :: CoreTerm
  show "((env, ghost, tm), env, ghost, CoreTm_Sizeof tm)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
next
  \<comment> \<open>CoreTm_Old - tm is smaller\<close>
  fix env :: CoreTyEnv
  fix tm :: CoreTerm
  show "((env, Ghost, tm), env, Ghost, CoreTm_Old tm)
        \<in> measure (\<lambda>(env, ghost, tm). size tm)"
    by simp
qed


(* ========================================================================== *)
(* Properties of core_term_type *)
(* ========================================================================== *)

(* Helper lemmas: pattern functions don't depend on TE_ConstLocals *)
lemma pattern_compatible_TE_ConstLocals_irrelevant [simp]:
  "pattern_compatible (env \<lparr> TE_ConstLocals := c \<rparr>) p ty =
   pattern_compatible env p ty"
  by (cases p) (auto split: option.splits)

lemma patterns_exhaustive_TE_ConstLocals_irrelevant [simp]:
  "patterns_exhaustive (env \<lparr> TE_ConstLocals := c \<rparr>) ty ps =
   patterns_exhaustive env ty ps"
  by (auto split: option.splits CoreType.splits)

(* core_term_type does not depend on TE_ConstLocals *)
lemma core_term_type_TE_ConstLocals_irrelevant:
  "core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm =
   core_term_type env ghost tm"
proof (induction tm arbitrary: env ghost c)
  case (CoreTm_Let var rhs body)
  have rhs_eq: "core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost rhs =
                core_term_type env ghost rhs"
    using CoreTm_Let.IH(1) .
  show ?case
  proof (cases "core_term_type env ghost rhs")
    case None
    then show ?thesis using rhs_eq by (simp add: Let_def)
  next
    case (Some rhsTy)
    let ?env' = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                       TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                        else fminus (TE_GhostLocals env) {|var|}),
                       TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
    have body_eq: "\<And>env' ghost c.
            core_term_type (env' \<lparr> TE_ConstLocals := c \<rparr>) ghost body =
            core_term_type env' ghost body"
      using CoreTm_Let.IH(2) .
    then show ?thesis using Some rhs_eq by (simp add: Let_def)
  qed
next
  case (CoreTm_LitArray ty tms)
  have wk_eq: "is_well_kinded (env \<lparr> TE_ConstLocals := c \<rparr>) ty = is_well_kinded env ty" for c
    using is_well_kinded_cong_env[of "env \<lparr> TE_ConstLocals := c \<rparr>" env] by simp
  have rt_eq: "is_runtime_type (env \<lparr> TE_ConstLocals := c \<rparr>) ty = is_runtime_type env ty" for c
    using is_runtime_type_cong_env[of "env \<lparr> TE_ConstLocals := c \<rparr>" env] by simp
  have IH: "\<And>tm. tm \<in> set tms \<Longrightarrow>
    core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm = core_term_type env ghost tm"
    using CoreTm_LitArray.IH by blast
  hence la_eq: "list_all (\<lambda>tm. core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm = Some ty) tms =
                list_all (\<lambda>tm. core_term_type env ghost tm = Some ty) tms"
    by (induction tms) auto
  show ?case using wk_eq rt_eq la_eq by simp
next
  case (CoreTm_Var name)
  then show ?case by (simp split: option.splits)
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  have wk_eq: "\<And>ty. is_well_kinded (env \<lparr> TE_ConstLocals := c \<rparr>) ty = is_well_kinded env ty"
    using is_well_kinded_cong_env[of "env \<lparr> TE_ConstLocals := c \<rparr>" env] by simp
  have rt_eq: "\<And>ty. is_runtime_type (env \<lparr> TE_ConstLocals := c \<rparr>) ty = is_runtime_type env ty"
    using is_runtime_type_cong_env[of "env \<lparr> TE_ConstLocals := c \<rparr>" env] by simp
  have IH: "\<And>tm. tm \<in> set args \<Longrightarrow>
    core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm = core_term_type env ghost tm"
    using CoreTm_FunctionCall.IH by blast
  have la2_eq: "\<And>ys. list_all2 (\<lambda>tm expectedTy.
        case core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm of
          None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy) args ys =
      list_all2 (\<lambda>tm expectedTy.
        case core_term_type env ghost tm of
          None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy) args ys"
  proof (intro iffI)
    fix ys
    assume "list_all2 (\<lambda>tm expectedTy.
        case core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm of
          None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy) args ys"
    then show "list_all2 (\<lambda>tm expectedTy.
        case core_term_type env ghost tm of
          None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy) args ys"
      using IH list.rel_mono_strong by force
  next
    fix ys
    assume "list_all2 (\<lambda>tm expectedTy.
        case core_term_type env ghost tm of
          None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy) args ys"
    then show "list_all2 (\<lambda>tm expectedTy.
        case core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm of
          None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy) args ys"
      by (simp add: IH list.rel_mono_strong)
  qed
  have la_wk: "list_all (is_well_kinded (env \<lparr> TE_ConstLocals := c \<rparr>)) tyArgs =
               list_all (is_well_kinded env) tyArgs"
    by (simp add: list_all_iff wk_eq)
  have la_rt: "list_all (is_runtime_type (env \<lparr> TE_ConstLocals := c \<rparr>)) tyArgs =
               list_all (is_runtime_type env) tyArgs"
    by (simp add: list_all_iff rt_eq)
  show ?case by (auto simp add: la_wk la_rt la2_eq split: option.splits if_splits)
next
  case (CoreTm_VariantCtor ctorName tyArgs arg)
  have wk_eq: "\<And>ty. is_well_kinded (env \<lparr> TE_ConstLocals := c \<rparr>) ty = is_well_kinded env ty"
    using is_well_kinded_cong_env[of "env \<lparr> TE_ConstLocals := c \<rparr>" env] by simp
  have rt_eq: "\<And>ty. is_runtime_type (env \<lparr> TE_ConstLocals := c \<rparr>) ty = is_runtime_type env ty"
    using is_runtime_type_cong_env[of "env \<lparr> TE_ConstLocals := c \<rparr>" env] by simp
  then show ?case using CoreTm_VariantCtor
    by (auto simp: wk_eq rt_eq list_all_iff split: option.splits if_splits)
next
  case (CoreTm_Record flds)
  have IH: "\<And>nm tm. (nm, tm) \<in> set flds \<Longrightarrow>
    core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm = core_term_type env ghost tm"
    using CoreTm_Record.IH by (auto simp: image_iff)
  have map_eq: "map (\<lambda>(name, y). core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost y) flds =
                map (\<lambda>(name, y). core_term_type env ghost y) flds"
    by (rule map_cong, simp, auto simp: IH)
  show ?case by (simp add: map_eq)
next
  case (CoreTm_Match scrut arms)
  have scrut_eq: "core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost scrut =
                  core_term_type env ghost scrut"
    using CoreTm_Match.IH(1) by blast
  have bodies_eq: "\<And>body. body \<in> snd ` set arms \<Longrightarrow>
    core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost body = core_term_type env ghost body"
    using CoreTm_Match.IH(2) by fastforce
  have hd_eq: "arms \<noteq> [] \<Longrightarrow>
    core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost (snd (hd arms)) =
    core_term_type env ghost (snd (hd arms))"
    using bodies_eq by (cases arms) auto
  have tl_eq: "\<And>ty. list_all (\<lambda>body. core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost body = Some ty)
                              (tl (map snd arms)) =
               list_all (\<lambda>body. core_term_type env ghost body = Some ty)
                              (tl (map snd arms))"
  proof -
    fix ty
    have "\<And>body. body \<in> set (tl (map snd arms)) \<Longrightarrow> body \<in> snd ` set arms"
      by (cases arms) auto
    then show "?thesis ty" using bodies_eq by (auto simp: list_all_iff)
  qed
  show ?case
  proof (cases "core_term_type env ghost scrut")
    case None then show ?thesis using scrut_eq by simp
  next
    case (Some scrutTy)
    show ?thesis
    proof (cases "arms = []")
      case True then show ?thesis using Some scrut_eq by simp
    next
      case False
      have "core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost (snd (hd arms)) =
            core_term_type env ghost (snd (hd arms))"
        using hd_eq False .
      then show ?thesis using Some False scrut_eq tl_eq by (auto split: if_splits CoreType.splits option.splits simp: Let_def)
    qed
  qed
next
  case (CoreTm_Quantifier quant var varTy body)
  have body_eq: "\<And>env' ghost c.
    core_term_type (env' \<lparr> TE_ConstLocals := c \<rparr>) ghost body = core_term_type env' ghost body"
    using CoreTm_Quantifier.IH .
  have env_reorder: "env \<lparr> TE_ConstLocals := c,
                           TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                           TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr> =
                     (env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                           TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>) \<lparr> TE_ConstLocals := c \<rparr>"
    by simp
  show ?case by (cases ghost) (simp_all add: body_eq env_reorder Let_def
                                        split: option.splits CoreType.splits)
next
  case (CoreTm_ArrayProj tm idxTms)
  have IH_tm: "core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm = core_term_type env ghost tm"
    using CoreTm_ArrayProj.IH(1) .
  have IH_idx: "\<And>idx. idx \<in> set idxTms \<Longrightarrow>
    core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost idx = core_term_type env ghost idx"
    using CoreTm_ArrayProj.IH(2) by blast
  have la_eq: "\<And>ty. list_all (\<lambda>tm. core_term_type (env \<lparr> TE_ConstLocals := c \<rparr>) ghost tm = Some ty) idxTms =
                    list_all (\<lambda>tm. core_term_type env ghost tm = Some ty) idxTms"
    using IH_idx by (auto simp: list_all_iff)
  show ?case using IH_tm la_eq by (simp split: option.splits CoreType.splits if_splits)
next
  case (CoreTm_Cast targetTy tm)
  then show ?case by (simp split: option.splits if_splits)
next
  case (CoreTm_VariantProj tm ctorName)
  then show ?case by (simp split: option.splits CoreType.splits)
next
  case (CoreTm_Allocated tm)
  then show ?case
    by (metis GhostOrNot.exhaust core_term_type.simps(19,20))
next
  case (CoreTm_Old tm)
  then show ?case
    by (metis GhostOrNot.exhaust core_term_type.simps(21,22))
qed simp_all


(* Weakening/irrelevance: adding a variable to the environment that is not free
   in the term does not affect typing. The ghost vars set may be arbitrarily
   modified at x (to allow for both ghost and non-ghost bindings), as long as
   all other variables' ghost status is preserved. *)
lemma core_term_type_irrelevant_var:
  assumes "x \<notin> core_term_free_vars tm"
    and "core_term_type env ghost tm = Some ty"
    and "\<forall>y. y \<noteq> x \<longrightarrow> (y |\<in>| gv' \<longleftrightarrow> y |\<in>| TE_GhostLocals env)"
  shows "core_term_type
           (env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                  TE_GhostLocals := gv' \<rparr>)
           ghost tm = Some ty"
using assms proof (induction tm arbitrary: env ghost ty gv')
  case (CoreTm_Var name)
  hence "name \<noteq> x" by simp
  (* tyenv_lookup_var is unchanged at name *)
  hence lookup_eq: "tyenv_lookup_var (env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                                            TE_GhostLocals := gv' \<rparr>) name =
                    tyenv_lookup_var env name"
    unfolding tyenv_lookup_var_def by (simp split: option.splits)
  (* tyenv_var_ghost is unchanged at name *)
  from \<open>name \<noteq> x\<close> CoreTm_Var.prems(3)
  have ghost_eq: "tyenv_var_ghost (env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                                         TE_GhostLocals := gv' \<rparr>) name =
                  tyenv_var_ghost env name"
    unfolding tyenv_var_ghost_def by (simp split: option.splits)
  from CoreTm_Var.prems(2) show ?case
    by (simp add: lookup_eq ghost_eq split: option.splits if_splits)
next
  case (CoreTm_Let var rhs body)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  from CoreTm_Let.prems(1) have x_not_free_rhs: "x \<notin> core_term_free_vars rhs" by simp
  from CoreTm_Let.prems(2) obtain rhsTy where
    rhs_ty: "core_term_type env ghost rhs = Some rhsTy" and
    body_ty: "core_term_type
      (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
             TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                 else fminus (TE_GhostLocals env) {|var|}),
             TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
      ghost body = Some ty"
    by (auto simp: Let_def split: option.splits)
  (* Apply IH to rhs *)
  from CoreTm_Let.IH(1)[OF x_not_free_rhs rhs_ty CoreTm_Let.prems(3)]
  have rhs_ty': "core_term_type ?env_x ghost rhs = Some rhsTy" .
  show ?case
  proof (cases "var = x")
    case True
    (* var = x: the inner Let binds x, so the outer fmupd is overwritten *)
    let ?inner_env = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                           TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                               else fminus (TE_GhostLocals env) {|var|}),
                           TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
    let ?inner_env_x = "?env_x \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars ?env_x),
                                  TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals ?env_x)
                                                      else fminus (TE_GhostLocals ?env_x) {|var|}),
                                  TE_ConstLocals := finsert var (TE_ConstLocals ?env_x) \<rparr>"
    (* The two inner environments are the same because fmupd var overwrites fmupd x (since var = x),
       and the GhostLocals updates (finsert/fminus at var) make gv' and TE_GhostLocals env agree *)
    have gv_eq_insert: "finsert x gv' = finsert x (TE_GhostLocals env)"
      using CoreTm_Let.prems(3) by (auto simp: fset_eqI)
    have gv_eq_minus: "fminus gv' {|x|} = fminus (TE_GhostLocals env) {|x|}"
      using CoreTm_Let.prems(3) by (auto simp: fset_eqI)
    from True have "?inner_env_x = ?inner_env"
      using gv_eq_insert gv_eq_minus by simp
    with body_ty have "core_term_type ?inner_env_x ghost body = Some ty" by simp
    with rhs_ty' show ?thesis by (simp add: Let_def)
  next
    case False
    (* var \<noteq> x: the fmupds commute, apply IH to body *)
    from CoreTm_Let.prems(1) False
    have x_not_free_body: "x \<notin> core_term_free_vars body" by auto
    (* Construct the ghost vars assumption for the body's env *)
    let ?body_gv = "if ghost = Ghost then finsert var gv'
                    else fminus gv' {|var|}"
    let ?body_env = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                          TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                              else fminus (TE_GhostLocals env) {|var|}),
                          TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
    have gv_body: "\<forall>y. y \<noteq> x \<longrightarrow> (y |\<in>| ?body_gv \<longleftrightarrow> y |\<in>| TE_GhostLocals ?body_env)"
      using CoreTm_Let.prems(3) False by auto
    from CoreTm_Let.IH(2)[OF x_not_free_body body_ty gv_body]
    have body_ty': "core_term_type
        (?body_env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars ?body_env),
                     TE_GhostLocals := ?body_gv \<rparr>)
        ghost body = Some ty" .
    (* Now show the two inner environments are equal *)
    (* The two inner environments are equal: the fmupds on TE_LocalVars commute
       (since var \<noteq> x), and the ghost/const fields are straightforward. *)
    from False have fmupd_comm_fact:
        "fmupd x ty' (fmupd var rhsTy (TE_LocalVars env)) =
         fmupd var rhsTy (fmupd x ty' (TE_LocalVars env))"
      by (simp add: fmupd_reorder_neq)
    from False have env_eq: "(?body_env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars ?body_env),
                                          TE_GhostLocals := ?body_gv \<rparr>) =
        (?env_x \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars ?env_x),
                  TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals ?env_x)
                                      else fminus (TE_GhostLocals ?env_x) {|var|}),
                  TE_ConstLocals := finsert var (TE_ConstLocals ?env_x) \<rparr>)"
      using fmupd_comm_fact by simp
    from body_ty' env_eq have "core_term_type
        (?env_x \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars ?env_x),
                  TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals ?env_x)
                                      else fminus (TE_GhostLocals ?env_x) {|var|}),
                  TE_ConstLocals := finsert var (TE_ConstLocals ?env_x) \<rparr>)
        ghost body = Some ty" by simp
    with rhs_ty' show ?thesis by (simp add: Let_def)
  qed
next
  case (CoreTm_Quantifier quant var varTy body)
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Quantifier.prems(2) show ?thesis by simp
  next
    case Ghost
    let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                         TE_GhostLocals := gv' \<rparr>"
    from Ghost CoreTm_Quantifier.prems(2) have wk: "is_well_kinded env varTy"
      by (auto simp: Let_def split: option.splits if_splits CoreType.splits)
    have wk': "is_well_kinded ?env_x varTy"
      using wk is_well_kinded_cong_env[of ?env_x env] by simp
    from Ghost CoreTm_Quantifier.prems(2) obtain bodyTy where
      body_ty: "core_term_type
        (env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
               TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>)
        Ghost body = Some bodyTy"
      and ty_eq: "ty = CoreTy_Bool" and body_bool: "bodyTy = CoreTy_Bool"
      by (auto simp: Let_def split: option.splits if_splits CoreType.splits)
    show ?thesis
    proof (cases "var = x")
      case True
      let ?inner = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                         TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>"
      let ?inner_x = "?env_x \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars ?env_x),
                                TE_GhostLocals := finsert var (TE_GhostLocals ?env_x) \<rparr>"
      have "finsert x gv' = finsert x (TE_GhostLocals env)"
        using CoreTm_Quantifier.prems(3) by (auto simp: fset_eqI)
      from True this have "?inner_x = ?inner" by simp
      with body_ty body_bool ty_eq wk' Ghost show ?thesis by (simp add: Let_def)
    next
      case False
      from CoreTm_Quantifier.prems(1) False
      have x_not_free_body: "x \<notin> core_term_free_vars body" by auto
      let ?body_gv = "finsert var gv'"
      let ?body_env = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                            TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>"
      have gv_body: "\<forall>y. y \<noteq> x \<longrightarrow> (y |\<in>| ?body_gv \<longleftrightarrow> y |\<in>| TE_GhostLocals ?body_env)"
        using CoreTm_Quantifier.prems(3) False by auto
      from CoreTm_Quantifier.IH[OF x_not_free_body body_ty gv_body]
      have body_ty': "core_term_type
          (?body_env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars ?body_env),
                       TE_GhostLocals := ?body_gv \<rparr>)
          Ghost body = Some bodyTy" .
      from False have "fmupd x ty' (fmupd var varTy (TE_LocalVars env)) =
                       fmupd var varTy (fmupd x ty' (TE_LocalVars env))"
        by (simp add: fmupd_reorder_neq)
      hence "(?body_env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars ?body_env),
                          TE_GhostLocals := ?body_gv \<rparr>) =
          (?env_x \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars ?env_x),
                    TE_GhostLocals := finsert var (TE_GhostLocals ?env_x) \<rparr>)"
        by simp
      with body_ty' body_bool ty_eq wk' Ghost show ?thesis by (simp add: Let_def)
    qed
  qed
next
  \<comment> \<open>All other cases: no variable binding, straightforward from IH\<close>
  case (CoreTm_LitBool b) then show ?case by simp
next
  case (CoreTm_LitInt i) then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray elemTy tms)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  have wk_eq: "is_well_kinded ?env_x elemTy = is_well_kinded env elemTy"
    using is_well_kinded_cong_env[of ?env_x env] by simp
  have rt_eq: "is_runtime_type ?env_x elemTy = is_runtime_type env elemTy"
    using is_runtime_type_cong_env[of ?env_x env] by simp
  from CoreTm_LitArray.prems have
    "\<forall>tm \<in> set tms. x \<notin> core_term_free_vars tm" by auto
  with CoreTm_LitArray.IH CoreTm_LitArray.prems(3)
  have "\<forall>tm \<in> set tms. \<forall>ty. core_term_type env ghost tm = Some ty \<longrightarrow>
      core_term_type ?env_x ghost tm = Some ty" by blast
  then show ?case using CoreTm_LitArray.prems(2) wk_eq rt_eq
    by (auto simp: list_all_iff split: if_splits)
next
  case (CoreTm_Cast targetTy tm)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  have rt_eq: "\<And>t. is_runtime_type ?env_x t = is_runtime_type env t"
    using is_runtime_type_cong_env[of ?env_x env] by simp
  from CoreTm_Cast show ?case by (auto simp: rt_eq split: option.splits if_splits)
next
  case (CoreTm_Unop op tm)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  from CoreTm_Unop.prems(2) obtain operandTy where
    op_ty: "core_term_type env ghost tm = Some operandTy"
    by (auto split: option.splits)
  from CoreTm_Unop.IH[OF _ op_ty CoreTm_Unop.prems(3)] CoreTm_Unop.prems(1)
  have op_ty': "core_term_type ?env_x ghost tm = Some operandTy" by simp
  from CoreTm_Unop.prems(2) show ?case using op_ty op_ty'
    by (auto split: option.splits)
next
  case (CoreTm_Binop op lhs rhs)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  from CoreTm_Binop.prems(1) have "x \<notin> core_term_free_vars lhs" "x \<notin> core_term_free_vars rhs" by auto
  from CoreTm_Binop.prems(2) obtain lhsTy rhsTy where
    lhs_ty: "core_term_type env ghost lhs = Some lhsTy" and
    rhs_ty: "core_term_type env ghost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)
  from CoreTm_Binop.IH(1)[OF \<open>x \<notin> core_term_free_vars lhs\<close> lhs_ty CoreTm_Binop.prems(3)]
  have lhs_ty': "core_term_type ?env_x ghost lhs = Some lhsTy" .
  from CoreTm_Binop.IH(2)[OF \<open>x \<notin> core_term_free_vars rhs\<close> rhs_ty CoreTm_Binop.prems(3)]
  have rhs_ty': "core_term_type ?env_x ghost rhs = Some rhsTy" .
  from CoreTm_Binop.prems(2) show ?case using lhs_ty lhs_ty' rhs_ty rhs_ty'
    by (auto split: option.splits if_splits)
next
  case (CoreTm_FunctionCall fnName tyArgs tmArgs)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  have wk_eq: "\<And>t. is_well_kinded ?env_x t = is_well_kinded env t"
    using is_well_kinded_cong_env[of ?env_x env] by simp
  have rt_eq: "\<And>t. is_runtime_type ?env_x t = is_runtime_type env t"
    using is_runtime_type_cong_env[of ?env_x env] by simp
  from CoreTm_FunctionCall.prems(1)
  have "\<forall>tm \<in> set tmArgs. x \<notin> core_term_free_vars tm" by auto
  with CoreTm_FunctionCall.IH CoreTm_FunctionCall.prems(3)
  have IH: "\<forall>tm \<in> set tmArgs. \<forall>ty. core_term_type env ghost tm = Some ty \<longrightarrow>
      core_term_type ?env_x ghost tm = Some ty" by blast
  from CoreTm_FunctionCall.prems(2) obtain funInfo where
    fn_lookup: "fmlookup (TE_Functions env) fnName = Some funInfo" and
    len_tyargs: "length tyArgs = length (FI_TyArgs funInfo)" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    len_tmargs: "length tmArgs = length (FI_TmArgs funInfo)" and
    not_impure: "\<not> FI_Impure funInfo" and
    all_var: "list_all (\<lambda>(_, _, vor). vor = Var) (FI_TmArgs funInfo)" and
    la2: "list_all2 (\<lambda>tm expectedTy.
        case core_term_type env ghost tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
        tmArgs (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                    (FI_TmArgs funInfo))" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) (FI_ReturnType funInfo)"
    by (auto simp: Let_def split: option.splits if_splits)
  have la2': "list_all2 (\<lambda>tm expectedTy.
      case core_term_type ?env_x ghost tm of None \<Rightarrow> False | Some actualTy \<Rightarrow> actualTy = expectedTy)
      tmArgs (map (\<lambda>(_, ty, _). apply_subst (fmap_of_list (zip (FI_TyArgs funInfo) tyArgs)) ty)
                  (FI_TmArgs funInfo))"
    using la2 IH by (auto simp: list.rel_mono_strong split: option.splits)
  have fn_lookup': "fmlookup (TE_Functions ?env_x) fnName = Some funInfo"
    using fn_lookup by simp
  have tyargs_wk': "list_all (is_well_kinded ?env_x) tyArgs"
    using tyargs_wk by (simp add: list_all_iff wk_eq)
  from CoreTm_FunctionCall.prems(2) show ?case
    using fn_lookup' len_tyargs tyargs_wk' len_tmargs not_impure all_var la2' ty_eq
          wk_eq rt_eq by (auto simp: Let_def list_all_iff split: option.splits if_splits)
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  have wk_eq: "\<And>t. is_well_kinded ?env_x t = is_well_kinded env t"
    using is_well_kinded_cong_env[of ?env_x env] by simp
  have rt_eq: "\<And>t. is_runtime_type ?env_x t = is_runtime_type env t"
    using is_runtime_type_cong_env[of ?env_x env] by simp
  then show ?case using CoreTm_VariantCtor.prems CoreTm_VariantCtor.IH
    by (auto simp: wk_eq rt_eq list_all_iff split: option.splits if_splits)
next
  case (CoreTm_Record flds)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  from CoreTm_Record.prems(2) obtain tys where
    those_eq: "those (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits)
  from those_eq have la2: "list_all2 (\<lambda>x y. x = Some y)
      (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) tys"
    using those_eq_Some by blast
  hence len_eq: "length flds = length tys" by (auto dest: list_all2_lengthD)
  (* Each field typing is preserved *)
  have "\<And>i. i < length flds \<Longrightarrow> core_term_type ?env_x ghost (snd (flds ! i)) =
        core_term_type env ghost (snd (flds ! i))"
  proof -
    fix i assume "i < length flds"
    obtain nm tm where p_eq: "flds ! i = (nm, tm)" by (cases "flds ! i") auto
    from \<open>i < length flds\<close> have "flds ! i \<in> set flds" by simp
    with CoreTm_Record.prems(1) p_eq have nf: "x \<notin> core_term_free_vars tm"
      by (auto simp: image_iff)
    from la2 \<open>i < length flds\<close> len_eq
    have "core_term_type env ghost tm = Some (tys ! i)"
      by (auto dest: list_all2_nthD simp: p_eq)
    from p_eq have "tm \<in> Basic_BNFs.snds (flds ! i)" by simp
    from CoreTm_Record.IH[OF \<open>flds ! i \<in> set flds\<close> this nf
        \<open>core_term_type env ghost tm = Some (tys ! i)\<close> CoreTm_Record.prems(3)]
    have "core_term_type ?env_x ghost tm = Some (tys ! i)" .
    with \<open>core_term_type env ghost tm = Some (tys ! i)\<close>
    show "core_term_type ?env_x ghost (snd (flds ! i)) = core_term_type env ghost (snd (flds ! i))"
      by (simp add: p_eq)
  qed
  hence map_eq: "map (\<lambda>(name, tm). core_term_type ?env_x ghost tm) flds =
                 map (\<lambda>(name, tm). core_term_type env ghost tm) flds"
    by (metis (mono_tags, lifting) map_equality_iff split_beta)
  show ?case by (simp add: map_eq those_eq ty_eq)
next
  case (CoreTm_RecordProj tm fldName) then show ?case
    by (auto split: option.splits CoreType.splits)
next
  case (CoreTm_VariantProj tm ctorName) then show ?case
    by (auto split: option.splits CoreType.splits)
next
  case (CoreTm_ArrayProj arr idxs)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  from CoreTm_ArrayProj.prems(1) have "x \<notin> core_term_free_vars arr"
    and idx_free: "\<forall>tm \<in> set idxs. x \<notin> core_term_free_vars tm" by auto
  from CoreTm_ArrayProj.prems(2) obtain elemTy dims where
    arr_ty: "core_term_type env ghost arr = Some (CoreTy_Array elemTy dims)"
    by (auto split: option.splits CoreType.splits if_splits)
  from CoreTm_ArrayProj.IH(1)[OF \<open>x \<notin> core_term_free_vars arr\<close> arr_ty CoreTm_ArrayProj.prems(3)]
  have arr_ty': "core_term_type ?env_x ghost arr = Some (CoreTy_Array elemTy dims)" .
  have idx_transfer: "\<And>tm. tm \<in> set idxs \<Longrightarrow>
      core_term_type env ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64) \<Longrightarrow>
      core_term_type ?env_x ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
  proof -
    fix tm assume "tm \<in> set idxs" and ty: "core_term_type env ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64)"
    from idx_free \<open>tm \<in> set idxs\<close> have "x \<notin> core_term_free_vars tm" by auto
    from CoreTm_ArrayProj.IH(2)[OF \<open>tm \<in> set idxs\<close> this ty CoreTm_ArrayProj.prems(3)]
    show "core_term_type ?env_x ghost tm = Some (CoreTy_FiniteInt Unsigned IntBits_64)" .
  qed
  from CoreTm_ArrayProj.prems(2) show ?case using arr_ty arr_ty' idx_transfer
    by (auto simp: list_all_iff split: option.splits CoreType.splits if_splits)
next
  case (CoreTm_Match scrut arms)
  let ?env_x = "env \<lparr> TE_LocalVars := fmupd x ty' (TE_LocalVars env),
                       TE_GhostLocals := gv' \<rparr>"
  from CoreTm_Match.prems(1) have scrut_free: "x \<notin> core_term_free_vars scrut"
    and bodies_free: "\<forall>body \<in> snd ` set arms. x \<notin> core_term_free_vars body" by auto
  (* pattern_compatible and patterns_exhaustive only depend on TE_DataCtors etc. *)
  have pc_eq: "\<And>p t. pattern_compatible ?env_x p t = pattern_compatible env p t"
    by (case_tac p) (simp_all split: option.splits)
  have pe_eq: "\<And>t ps. patterns_exhaustive ?env_x t ps = patterns_exhaustive env t ps"
    by (simp split: CoreType.splits option.splits)
  (* Scrutinee typing preserved *)
  from CoreTm_Match.prems(2) obtain scrutTy where
    scrut_ty: "core_term_type env ghost scrut = Some scrutTy"
    by (auto split: option.splits)
  from CoreTm_Match.IH(1)[OF scrut_free scrut_ty CoreTm_Match.prems(3)]
  have scrut_ty': "core_term_type ?env_x ghost scrut = Some scrutTy" .
  (* Head arm body typing preserved *)
  (* All arm body typings preserved *)
  have body_transfer: "\<And>arm body resultTy. arm \<in> set arms \<Longrightarrow> body = snd arm \<Longrightarrow>
      core_term_type env ghost body = Some resultTy \<Longrightarrow>
      core_term_type ?env_x ghost body = Some resultTy"
  proof -
    fix arm body resultTy
    assume "arm \<in> set arms" and "body = snd arm"
      and body_ty: "core_term_type env ghost body = Some resultTy"
    have "body \<in> Basic_BNFs.snds arm"
      using \<open>body = snd arm\<close> by (cases arm) simp
    from bodies_free \<open>arm \<in> set arms\<close> \<open>body = snd arm\<close>
    have "x \<notin> core_term_free_vars body" by auto
    from CoreTm_Match.IH(2)[OF \<open>arm \<in> set arms\<close> \<open>body \<in> Basic_BNFs.snds arm\<close>
        this body_ty CoreTm_Match.prems(3)]
    show "core_term_type ?env_x ghost body = Some resultTy" .
  qed
  have hd_transfer: "arms \<noteq> [] \<Longrightarrow> core_term_type env ghost (snd (hd arms)) = Some resultTy \<Longrightarrow>
      core_term_type ?env_x ghost (snd (hd arms)) = Some resultTy" for resultTy
    using body_transfer[of "hd arms" "snd (hd arms)"] by (cases arms) auto
  have tl_transfer: "\<And>body resultTy. body \<in> set (tl (map snd arms)) \<Longrightarrow>
      core_term_type env ghost body = Some resultTy \<Longrightarrow>
      core_term_type ?env_x ghost body = Some resultTy"
  proof -
    fix body resultTy
    assume "body \<in> set (tl (map snd arms))"
      and body_ty: "core_term_type env ghost body = Some resultTy"
    from \<open>body \<in> set (tl (map snd arms))\<close> obtain arm where
      "arm \<in> set arms" and "body = snd arm" by (cases arms) auto
    from body_transfer[OF this body_ty]
    show "core_term_type ?env_x ghost body = Some resultTy" .
  qed
  from CoreTm_Match.prems(2) show ?case
    using scrut_ty scrut_ty' pc_eq pe_eq hd_transfer tl_transfer
    by (auto simp: list_all_iff Let_def split: option.splits if_splits)
next
  case (CoreTm_Sizeof tm) then show ?case by (auto split: option.splits)
next
  case (CoreTm_Allocated tm)
  then show ?case
    by (cases ghost) (auto split: option.splits)
next
  case (CoreTm_Old tm)
  then show ?case
    by (cases ghost) auto
qed


(* Weakening: extending TE_TypeVars and TE_RuntimeTypeVars does not change what
   core_term_type accepts. The kind and runtime checks embedded in core_term_type
   are monotone under growing these sets, and lookups into TE_LocalVars /
   TE_Functions / TE_Datatypes / TE_DataCtors are unaffected by them. *)
lemma core_term_type_irrelevant_tyvar:
  assumes "core_term_type env ghost tm = Some ty"
  shows "core_term_type
           (env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                  TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>)
           ghost tm = Some ty"
using assms proof (induction tm arbitrary: env ghost ty)
  case (CoreTm_Var name)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  have lookup_eq: "tyenv_lookup_var ?env' name = tyenv_lookup_var env name"
    unfolding tyenv_lookup_var_def by (simp split: option.splits)
  have ghost_eq: "tyenv_var_ghost ?env' name = tyenv_var_ghost env name"
    unfolding tyenv_var_ghost_def by (simp split: option.splits)
  from CoreTm_Var show ?case
    by (simp add: lookup_eq ghost_eq split: option.splits if_splits)
next
  case (CoreTm_LitArray elemTy tms)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_LitArray.prems have
    elemTy_wk: "is_well_kinded env elemTy" and
    elemTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env elemTy" and
    all_tms: "list_all (\<lambda>tm. core_term_type env ghost tm = Some elemTy) tms" and
    len_range: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)
  have elemTy_wk': "is_well_kinded ?env' elemTy"
    using elemTy_wk is_well_kinded_extend_tyvars by fastforce
  have elemTy_rt': "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' elemTy"
    using elemTy_rt is_runtime_type_extend_runtime_tyvars by fastforce
  have all_tms': "list_all (\<lambda>tm. core_term_type ?env' ghost tm = Some elemTy) tms"
    using all_tms CoreTm_LitArray.IH by (induction tms) auto
  show ?case using elemTy_wk' elemTy_rt' all_tms' len_range ty_eq by simp
next
  case (CoreTm_Cast targetTy tm)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_Cast.prems obtain operandTy where
    operand_ty: "core_term_type env ghost tm = Some operandTy" and
    operand_int: "is_integer_type operandTy" and
    target_int: "is_integer_type targetTy" and
    targetTy_rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env targetTy" and
    ty_eq: "ty = targetTy"
    by (auto split: option.splits if_splits)
  have operand_ty': "core_term_type ?env' ghost tm = Some operandTy"
    using CoreTm_Cast.IH operand_ty by blast
  have targetTy_rt': "ghost = NotGhost \<longrightarrow> is_runtime_type ?env' targetTy"
    using targetTy_rt is_runtime_type_extend_runtime_tyvars by fastforce
  show ?case using operand_ty' operand_int target_int targetTy_rt' ty_eq by simp
next
  case (CoreTm_Let var rhs body)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_Let.prems obtain rhsTy where
    rhs_ty: "core_term_type env ghost rhs = Some rhsTy" and
    body_ty: "core_term_type
        (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
               TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                   else fminus (TE_GhostLocals env) {|var|}),
               TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
        ghost body = Some ty"
    by (auto simp: Let_def split: option.splits)
  have rhs_ty': "core_term_type ?env' ghost rhs = Some rhsTy"
    using CoreTm_Let.IH(1) rhs_ty by blast
  let ?body_env = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                         TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                             else fminus (TE_GhostLocals env) {|var|}),
                         TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  have body_env_shape: "?body_env \<lparr> TE_TypeVars := TE_TypeVars ?body_env |\<union>| extraTV,
                                    TE_RuntimeTypeVars := TE_RuntimeTypeVars ?body_env |\<union>| extraRT \<rparr> =
                        ?env' \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars ?env'),
                                TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals ?env')
                                                    else fminus (TE_GhostLocals ?env') {|var|}),
                                TE_ConstLocals := finsert var (TE_ConstLocals ?env') \<rparr>"
    by simp
  have body_ty': "core_term_type
       (?body_env \<lparr> TE_TypeVars := TE_TypeVars ?body_env |\<union>| extraTV,
                    TE_RuntimeTypeVars := TE_RuntimeTypeVars ?body_env |\<union>| extraRT \<rparr>)
       ghost body = Some ty"
    using CoreTm_Let.IH(2)[OF body_ty] .
  show ?case using rhs_ty' body_ty' body_env_shape
    by (metis core_term_type.simps(8) option.simps(5))
next
  case (CoreTm_Quantifier quant var varTy body)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  show ?case
  proof (cases ghost)
    case NotGhost
    with CoreTm_Quantifier.prems show ?thesis by simp
  next
    case Ghost
    from Ghost CoreTm_Quantifier.prems have wk: "is_well_kinded env varTy"
      by (auto simp: Let_def split: option.splits if_splits CoreType.splits)
    have wk': "is_well_kinded ?env' varTy"
      using wk is_well_kinded_extend_tyvars by fastforce
    from Ghost CoreTm_Quantifier.prems obtain bodyTy where
      body_ty: "core_term_type
        (env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
               TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>)
        Ghost body = Some bodyTy"
      and ty_eq: "ty = CoreTy_Bool" and body_bool: "bodyTy = CoreTy_Bool"
      by (auto simp: Let_def split: option.splits if_splits CoreType.splits)
    let ?body_env = "env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                           TE_GhostLocals := finsert var (TE_GhostLocals env) \<rparr>"
    have body_env_shape: "?body_env \<lparr> TE_TypeVars := TE_TypeVars ?body_env |\<union>| extraTV,
                                       TE_RuntimeTypeVars := TE_RuntimeTypeVars ?body_env |\<union>| extraRT \<rparr> =
                          ?env' \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars ?env'),
                                  TE_GhostLocals := finsert var (TE_GhostLocals ?env') \<rparr>"
      by simp
    have body_ty': "core_term_type
         (?body_env \<lparr> TE_TypeVars := TE_TypeVars ?body_env |\<union>| extraTV,
                      TE_RuntimeTypeVars := TE_RuntimeTypeVars ?body_env |\<union>| extraRT \<rparr>)
         Ghost body = Some bodyTy"
      using CoreTm_Quantifier.IH[OF body_ty] .
    from Ghost wk' body_ty' body_env_shape body_bool ty_eq show ?thesis
      by (metis CoreType.simps(63) core_term_type.simps(10) option.simps(5))
  qed
next
  case (CoreTm_FunctionCall fnName tyArgs args)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  have wk_mono: "\<And>t. is_well_kinded env t \<Longrightarrow> is_well_kinded ?env' t"
    using is_well_kinded_extend_tyvars by fastforce
  have rt_mono: "\<And>t. is_runtime_type env t \<Longrightarrow> is_runtime_type ?env' t"
    using is_runtime_type_extend_runtime_tyvars by fastforce
  have la_wk: "list_all (is_well_kinded env) tyArgs \<Longrightarrow> list_all (is_well_kinded ?env') tyArgs"
    using wk_mono by (auto simp: list_all_iff)
  have la_rt: "list_all (is_runtime_type env) tyArgs \<Longrightarrow> list_all (is_runtime_type ?env') tyArgs"
    using rt_mono by (auto simp: list_all_iff)
  have IH: "\<And>tm ty. tm \<in> set args \<Longrightarrow> core_term_type env ghost tm = Some ty \<Longrightarrow>
                     core_term_type ?env' ghost tm = Some ty"
    using CoreTm_FunctionCall.IH by blast
  have la2_mono: "\<And>ys. list_all2 (\<lambda>tm expectedTy.
          (\<exists>y. core_term_type env ghost tm = Some y) \<and>
          (\<forall>x2. core_term_type env ghost tm = Some x2 \<longrightarrow> x2 = expectedTy)) args ys \<Longrightarrow>
        list_all2 (\<lambda>tm expectedTy.
          (\<exists>y. core_term_type ?env' ghost tm = Some y) \<and>
          (\<forall>x2. core_term_type ?env' ghost tm = Some x2 \<longrightarrow> x2 = expectedTy)) args ys"
    using IH by (fastforce simp: list_all2_iff in_set_zip)
  show ?case using CoreTm_FunctionCall.prems la_wk la_rt la2_mono
    by (auto split: option.splits if_splits simp: Let_def)
next
  case (CoreTm_VariantCtor ctorName tyArgs arg)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  have wk_mono: "\<And>t. is_well_kinded env t \<Longrightarrow> is_well_kinded ?env' t"
    using is_well_kinded_extend_tyvars by fastforce
  have rt_mono: "\<And>t. is_runtime_type env t \<Longrightarrow> is_runtime_type ?env' t"
    using is_runtime_type_extend_runtime_tyvars by fastforce
  have la_wk: "list_all (is_well_kinded env) tyArgs \<Longrightarrow> list_all (is_well_kinded ?env') tyArgs"
    using wk_mono by (auto simp: list_all_iff)
  have la_rt: "list_all (is_runtime_type env) tyArgs \<Longrightarrow> list_all (is_runtime_type ?env') tyArgs"
    using rt_mono by (auto simp: list_all_iff)
  show ?case using CoreTm_VariantCtor la_wk la_rt
    by (auto split: option.splits if_splits)
next
  case (CoreTm_Record flds)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_Record.prems obtain tys where
    those_eq: "those (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits)
  have IH: "\<And>nm tm ty'. (nm, tm) \<in> set flds \<Longrightarrow> core_term_type env ghost tm = Some ty' \<Longrightarrow>
                         core_term_type ?env' ghost tm = Some ty'"
    using CoreTm_Record.IH by (auto simp: image_iff)
  \<comment> \<open>those succeeding means every field typed to Some in env\<close>
  from those_eq have la2: "list_all2 (\<lambda>x y. x = Some y)
                                      (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) tys"
    using those_eq_Some by blast
  have all_some: "\<And>nm tm. (nm, tm) \<in> set flds \<Longrightarrow>
                          \<exists>ty'. core_term_type env ghost tm = Some ty'"
  proof -
    fix nm tm assume mem: "(nm, tm) \<in> set flds"
    then obtain i where i_lt: "i < length flds" and fld_i: "flds ! i = (nm, tm)"
      by (auto simp: in_set_conv_nth)
    from la2 i_lt have "map (\<lambda>(name, tm). core_term_type env ghost tm) flds ! i = Some (tys ! i)"
      by (auto simp: list_all2_conv_all_nth)
    thus "\<exists>ty'. core_term_type env ghost tm = Some ty'"
      using i_lt fld_i by simp
  qed
  have map_eq: "map (\<lambda>(name, y). core_term_type ?env' ghost y) flds =
                map (\<lambda>(name, y). core_term_type env ghost y) flds"
  proof (rule map_cong, simp)
    fix p assume p_in: "p \<in> set flds"
    obtain nm tm where p_eq: "p = (nm, tm)" by (cases p)
    from p_in p_eq all_some obtain ty' where
      tm_ty: "core_term_type env ghost tm = Some ty'" by blast
    from IH[OF _ tm_ty] p_in p_eq have
      tm_ty': "core_term_type ?env' ghost tm = Some ty'" by blast
    show "(case p of (name, y) \<Rightarrow> core_term_type ?env' ghost y) =
          (case p of (name, y) \<Rightarrow> core_term_type env ghost y)"
      using p_eq tm_ty tm_ty' by simp
  qed
  from CoreTm_Record.prems show ?case by (simp add: map_eq)
next
  case (CoreTm_Match scrut arms)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_Match.prems obtain scrutTy where
    scrut_ty: "core_term_type env ghost scrut = Some scrutTy"
    by (auto split: option.splits)
  have scrut_ty': "core_term_type ?env' ghost scrut = Some scrutTy"
    using CoreTm_Match.IH(1) scrut_ty by blast
  \<comment> \<open>arms nonempty and pattern checks pass in env\<close>
  from CoreTm_Match.prems scrut_ty have arms_nonempty: "arms \<noteq> []"
    by (auto split: option.splits if_splits)
  let ?pats = "map fst arms"
  from CoreTm_Match.prems scrut_ty arms_nonempty have
    pat_compat: "list_all (\<lambda>p. pattern_compatible env p scrutTy) ?pats" and
    pat_reg: "patterns_regular ?pats" and
    pat_exh: "patterns_exhaustive env scrutTy ?pats"
    by (auto split: option.splits if_splits simp: Let_def)
  \<comment> \<open>These pattern checks don't depend on TE_TypeVars / TE_RuntimeTypeVars\<close>
  have pc_eq: "\<And>p t. pattern_compatible ?env' p t = pattern_compatible env p t"
    by (rule pattern_compatible.induct[where P="\<lambda>e p t. pattern_compatible ?env' p t = pattern_compatible env p t"])
       auto
  have pat_compat': "list_all (\<lambda>p. pattern_compatible ?env' p scrutTy) ?pats"
    using pat_compat by (simp add: list_all_iff pc_eq)
  have pat_exh': "patterns_exhaustive ?env' scrutTy ?pats"
    using pat_exh by (auto split: CoreType.splits option.splits if_splits)
  \<comment> \<open>First body and rest\<close>
  have match_unfold: "core_term_type env ghost (CoreTm_Match scrut arms) =
    (let pats = map fst arms; bodies = map snd arms in
      if arms = [] then None
      else if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
      else if \<not> patterns_regular pats then None
      else if \<not> patterns_exhaustive env scrutTy pats then None
      else (case core_term_type env ghost (snd (hd arms)) of
              None \<Rightarrow> None
            | Some resultTy \<Rightarrow>
                if list_all (\<lambda>body. core_term_type env ghost body = Some resultTy) (tl bodies)
                then Some resultTy
                else None))"
    using scrut_ty by simp
  from CoreTm_Match.prems match_unfold arms_nonempty pat_compat pat_reg pat_exh
  obtain firstBodyTy where
    first_ty: "core_term_type env ghost (snd (hd arms)) = Some firstBodyTy" and
    ty_eq: "ty = firstBodyTy" and
    rest_ty: "list_all (\<lambda>body. core_term_type env ghost body = Some firstBodyTy)
                       (tl (map snd arms))"
    by (auto simp: Let_def split: option.splits if_splits)
  have hd_in: "snd (hd arms) \<in> snd ` set arms"
    using arms_nonempty by (cases arms) auto
  have bodies_IH: "\<And>body ty'. body \<in> snd ` set arms \<Longrightarrow>
                              core_term_type env ghost body = Some ty' \<Longrightarrow>
                              core_term_type ?env' ghost body = Some ty'"
    using CoreTm_Match.IH(2) by fastforce
  have first_ty': "core_term_type ?env' ghost (snd (hd arms)) = Some firstBodyTy"
    using bodies_IH[OF hd_in first_ty] .
  have tl_in: "\<And>body. body \<in> set (tl (map snd arms)) \<Longrightarrow> body \<in> snd ` set arms"
    by (cases arms) auto
  have rest_ty': "list_all (\<lambda>body. core_term_type ?env' ghost body = Some firstBodyTy)
                           (tl (map snd arms))"
    using rest_ty bodies_IH tl_in by (induction "tl (map snd arms)") (auto simp: list_all_iff)
  show ?case
    using scrut_ty' arms_nonempty pat_compat' pat_reg pat_exh' first_ty' rest_ty' ty_eq
    by (simp add: Let_def)
next
  case (CoreTm_ArrayProj tm idxTms)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_ArrayProj.prems obtain elemTy dims where
    tm_ty: "core_term_type env ghost tm = Some (CoreTy_Array elemTy dims)" and
    len_eq: "length idxTms = length dims" and
    idxs_ty: "list_all (\<lambda>tm. core_term_type env ghost tm =
                              Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)
  have tm_ty': "core_term_type ?env' ghost tm = Some (CoreTy_Array elemTy dims)"
    using CoreTm_ArrayProj.IH(1) tm_ty by blast
  have idx_IH: "\<And>idx ty'. idx \<in> set idxTms \<Longrightarrow> core_term_type env ghost idx = Some ty' \<Longrightarrow>
                          core_term_type ?env' ghost idx = Some ty'"
    using CoreTm_ArrayProj.IH(2) by blast
  have idxs_ty': "list_all (\<lambda>tm. core_term_type ?env' ghost tm =
                                  Some (CoreTy_FiniteInt Unsigned IntBits_64)) idxTms"
    using idxs_ty idx_IH by (induction idxTms) (auto simp: list_all_iff)
  show ?case using tm_ty' len_eq idxs_ty' ty_eq by simp
next
  case (CoreTm_Allocated tm)
  then show ?case
    by (cases ghost) (auto split: option.splits)
next
  case (CoreTm_Old tm)
  then show ?case
    by (cases ghost) auto
next
  case (CoreTm_LitBool b) then show ?case by simp
next
  case (CoreTm_LitInt i) then show ?case by (simp split: option.splits)
next
  case (CoreTm_Unop op operand)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_Unop.prems obtain operandTy where
    op_ty: "core_term_type env ghost operand = Some operandTy"
    by (auto split: option.splits)
  have op_ty': "core_term_type ?env' ghost operand = Some operandTy"
    using CoreTm_Unop.IH op_ty by blast
  show ?case using CoreTm_Unop.prems op_ty op_ty'
    by (auto split: option.splits CoreUnop.splits if_splits)
next
  case (CoreTm_Binop op lhs rhs)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_Binop.prems obtain lhsTy rhsTy where
    lhs_ty: "core_term_type env ghost lhs = Some lhsTy" and
    rhs_ty: "core_term_type env ghost rhs = Some rhsTy"
    by (auto split: option.splits)
  have lhs_ty': "core_term_type ?env' ghost lhs = Some lhsTy"
    using CoreTm_Binop.IH(1) lhs_ty by blast
  have rhs_ty': "core_term_type ?env' ghost rhs = Some rhsTy"
    using CoreTm_Binop.IH(2) rhs_ty by blast
  show ?case using CoreTm_Binop.prems lhs_ty lhs_ty' rhs_ty rhs_ty'
    by (auto split: option.splits if_splits)
next
  case (CoreTm_RecordProj tm fldName)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_RecordProj.prems obtain fieldTypes where
    tm_ty: "core_term_type env ghost tm = Some (CoreTy_Record fieldTypes)" and
    ty_eq: "map_of fieldTypes fldName = Some ty"
    by (auto split: option.splits CoreType.splits)
  have tm_ty': "core_term_type ?env' ghost tm = Some (CoreTy_Record fieldTypes)"
    using CoreTm_RecordProj.IH tm_ty by blast
  show ?case using tm_ty' ty_eq by simp
next
  case (CoreTm_VariantProj tm ctorName)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_VariantProj.prems obtain tmTy where
    tm_ty: "core_term_type env ghost tm = Some tmTy"
    by (auto split: option.splits)
  have tm_ty': "core_term_type ?env' ghost tm = Some tmTy"
    using CoreTm_VariantProj.IH tm_ty by blast
  show ?case using CoreTm_VariantProj.prems tm_ty tm_ty'
    by (auto split: option.splits CoreType.splits)
next
  case (CoreTm_Sizeof tm)
  let ?env' = "env \<lparr> TE_TypeVars := TE_TypeVars env |\<union>| extraTV,
                     TE_RuntimeTypeVars := TE_RuntimeTypeVars env |\<union>| extraRT \<rparr>"
  from CoreTm_Sizeof.prems obtain elemTy dims where
    tm_ty: "core_term_type env ghost tm = Some (CoreTy_Array elemTy dims)"
    by (auto split: option.splits CoreType.splits if_splits)
  have tm_ty': "core_term_type ?env' ghost tm = Some (CoreTy_Array elemTy dims)"
    using CoreTm_Sizeof.IH tm_ty by blast
  show ?case using CoreTm_Sizeof.prems tm_ty tm_ty'
    by (auto split: option.splits CoreType.splits if_splits)
qed


(* core_term_type produces well-kinded types, and in NotGhost mode also runtime types.
   These must be proved simultaneously because the CoreTm_Let case
   needs both properties from the IH to show tyenv_well_formed for the extended env. *)
lemma core_term_type_well_kinded_and_runtime:
  assumes "core_term_type env ghost tm = Some ty"
    and "tyenv_well_formed env"
  shows "is_well_kinded env ty \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env ty)"
using assms proof (induction tm arbitrary: env ghost ty)
  case (CoreTm_LitBool b)
  then show ?case by simp
next
  case (CoreTm_LitInt i)
  then show ?case by (auto split: option.splits)
next
  case (CoreTm_LitArray elemTy tms)
  from CoreTm_LitArray.prems(1) have
    wk: "is_well_kinded env elemTy" and
    rt: "ghost = NotGhost \<longrightarrow> is_runtime_type env elemTy" and
    len_ok: "int_in_range (int_range Unsigned IntBits_64) (int (length tms))" and
    ty_eq: "ty = CoreTy_Array elemTy [CoreDim_Fixed (int (length tms))]"
    by (auto split: if_splits)
  have "is_well_kinded env ty" using wk len_ok ty_eq
    by (simp add: array_dims_well_kinded_def)
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type env ty" using rt ty_eq by simp
  ultimately show ?case by blast
next
  case (CoreTm_Var name)
  then obtain varTy where
    lookup: "tyenv_lookup_var env name = Some varTy" and
    ty_eq: "ty = varTy"
    by (auto split: option.splits if_splits)
  have wk: "tyenv_vars_well_kinded env"
    using CoreTm_Var.prems(2) tyenv_well_formed_def by blast
  \<comment> \<open>The variable might be local (well-kinded directly in env) or global
      (well-kinded in env with TE_TypeVars / TE_RuntimeTypeVars cleared). In the
      global case, we lift back to env via is_well_kinded_extend_tyvars: clearing
      then extending by env's own type vars gives env back. \<close>
  have var_wk: "is_well_kinded env ty"
  proof (cases "fmlookup (TE_LocalVars env) name")
    case (Some lty)
    with lookup ty_eq have "fmlookup (TE_LocalVars env) name = Some ty"
      unfolding tyenv_lookup_var_def by simp
    thus ?thesis using wk unfolding tyenv_vars_well_kinded_def by blast
  next
    case None
    with lookup ty_eq have gv_lookup: "fmlookup (TE_GlobalVars env) name = Some ty"
      unfolding tyenv_lookup_var_def by (auto split: option.splits)
    from gv_lookup wk have wk_cleared:
      "is_well_kinded (env \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
      unfolding tyenv_vars_well_kinded_def by blast
    \<comment> \<open>Well-kinded in the cleared env means ty has no type variables, so it is well-kinded
        in any env with the same TE_Datatypes \<close>
    have tyvars_empty: "type_tyvars ty = {}"
      using is_well_kinded_type_tyvars_subset[OF wk_cleared] by simp
    show ?thesis
      using is_well_kinded_transfer[OF wk_cleared] tyvars_empty by simp
  qed
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
  proof
    assume ng: "ghost = NotGhost"
    from CoreTm_Var.prems(1) ng have not_ghost: "\<not> tyenv_var_ghost env name"
      by (auto split: option.splits if_splits)
    have rt: "tyenv_vars_runtime env"
      using CoreTm_Var.prems(2) tyenv_well_formed_def by blast
    show "is_runtime_type env ty"
    proof (cases "fmlookup (TE_LocalVars env) name")
      case (Some lty)
      with lookup ty_eq have lv: "fmlookup (TE_LocalVars env) name = Some ty"
        unfolding tyenv_lookup_var_def by simp
      from not_ghost lv have "name |\<notin>| TE_GhostLocals env"
        unfolding tyenv_var_ghost_def by simp
      with lv rt show ?thesis unfolding tyenv_vars_runtime_def by blast
    next
      case None
      with lookup ty_eq have gv: "fmlookup (TE_GlobalVars env) name = Some ty"
        unfolding tyenv_lookup_var_def by (auto split: option.splits)
      from not_ghost gv None have "name |\<notin>| TE_GhostGlobals env"
        unfolding tyenv_var_ghost_def by (auto split: option.splits)
      with gv rt have rt_cleared:
        "is_runtime_type (env \<lparr> TE_TypeVars := {||}, TE_RuntimeTypeVars := {||} \<rparr>) ty"
        unfolding tyenv_vars_runtime_def by blast
      have tyvars_empty: "type_tyvars ty = {}"
        using is_runtime_type_tyvars_subset[OF rt_cleared] by simp
      show ?thesis
        using is_runtime_type_transfer[OF rt_cleared] tyvars_empty by simp
    qed
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
  have IH: "is_well_kinded env operandTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env operandTy)"
    using CoreTm_Unop.IH operand_typed CoreTm_Unop.prems(2) by blast
  show ?case using CoreTm_Unop.prems(1) operand_typed IH
    by (cases op) (auto split: if_splits)
next
  case (CoreTm_Binop op lhs rhs)
  from CoreTm_Binop.prems(1) obtain lhsTy rhsTy where
    lhs_typed: "core_term_type env ghost lhs = Some lhsTy" and
    rhs_typed: "core_term_type env ghost rhs = Some rhsTy"
    by (auto split: option.splits prod.splits)
  have lhs_IH: "is_well_kinded env lhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env lhsTy)"
    using CoreTm_Binop.IH(1) lhs_typed CoreTm_Binop.prems(2) by blast
  \<comment> \<open>Result is either lhsTy (arithmetic/modulo/bitwise/shift) or CoreTy_Bool (ordering/eq_neq/logical)\<close>
  show ?case using CoreTm_Binop.prems(1) lhs_typed rhs_typed lhs_IH
    by (auto split: if_splits)
next
  case (CoreTm_Let var tm1 tm2)
  from CoreTm_Let.prems(1) obtain rhsTy where
    rhs_typed: "core_term_type env ghost tm1 = Some rhsTy" and
    body_typed: "core_term_type
      (env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
             TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                              else fminus (TE_GhostLocals env) {|var|}),
             TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>)
      ghost tm2 = Some ty"
    by (auto simp: Let_def split: option.splits if_splits)
  let ?env' = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                     TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                      else fminus (TE_GhostLocals env) {|var|}),
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
  have rhs_IH: "is_well_kinded env rhsTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env rhsTy)"
    using CoreTm_Let.IH(1) rhs_typed CoreTm_Let.prems(2) by blast
  hence rhs_wk: "is_well_kinded env rhsTy" by blast
  let ?env_no_cn = "env \<lparr> TE_LocalVars := fmupd var rhsTy (TE_LocalVars env),
                          TE_GhostLocals := (if ghost = Ghost then finsert var (TE_GhostLocals env)
                                           else fminus (TE_GhostLocals env) {|var|}) \<rparr>"
  have wf_no_cn: "tyenv_well_formed ?env_no_cn"
  proof (cases "ghost = Ghost")
    case True
    then show ?thesis
      using tyenv_well_formed_add_ghost_var[OF CoreTm_Let.prems(2) rhs_wk] by simp
  next
    case False
    hence rhs_rt: "is_runtime_type env rhsTy" using rhs_IH GhostOrNot.exhaust by auto
    show ?thesis using False
      tyenv_well_formed_add_var[OF CoreTm_Let.prems(2) rhs_wk rhs_rt] by simp
  qed
  have env'_eq_cn: "?env' = ?env_no_cn \<lparr> TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
    by simp
  have wf_env': "tyenv_well_formed ?env'"
    using wf_no_cn tyenv_well_formed_TE_ConstLocals_irrelevant env'_eq_cn by simp
  have body_IH: "is_well_kinded ?env' ty \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type ?env' ty)"
    using CoreTm_Let.IH(2) body_typed wf_env' by blast
  \<comment> \<open>is_well_kinded only depends on TE_TypeVars and TE_Datatypes\<close>
  have env'_fields: "TE_TypeVars ?env' = TE_TypeVars env"
                     "TE_Datatypes ?env' = TE_Datatypes env"
    by simp_all
  have "is_well_kinded env ty"
    using body_IH is_well_kinded_cong_env[OF env'_fields] by simp
  have gds_eq: "TE_GhostDatatypes ?env' = TE_GhostDatatypes env" by simp
  have rtv_eq: "TE_RuntimeTypeVars ?env' = TE_RuntimeTypeVars env" by simp
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
    using body_IH is_runtime_type_cong_env[OF gds_eq rtv_eq] by blast
  ultimately show ?case
    by (simp add: \<open>is_well_kinded env ty\<close>)
next
  case (CoreTm_Quantifier quant var varTy body)
  from CoreTm_Quantifier.prems(1) have "ghost = Ghost"
    by (cases ghost) (auto simp: Let_def split: option.splits if_splits)
  with CoreTm_Quantifier.prems(1) have "ty = CoreTy_Bool"
    by (auto simp: Let_def split: option.splits CoreType.splits if_splits)
  thus ?case by simp
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
  hence ret_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                                (FI_ReturnType funInfo)"
    using fn_lookup tyenv_fun_types_well_kinded_def by blast
  have wk: "is_well_kinded env ty"
    using apply_subst_specializes_well_kinded len_tyargs ret_wk ty_eq tyargs_wk
    by simp
  \<comment> \<open>Runtime part (NotGhost only)\<close>
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
  proof
    assume ng: "ghost = NotGhost"
    from CoreTm_FunctionCall.prems(1) ng fn_lookup have
      not_ghost_fn: "FI_Ghost funInfo \<noteq> Ghost" and
      tyargs_rt: "list_all (is_runtime_type env) tyArgs"
      by (auto simp: Let_def split: option.splits if_splits)
    have "tyenv_fun_ghost_constraint env"
      using CoreTm_FunctionCall.prems(2) tyenv_well_formed_def by blast
    hence ret_rt: "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list (FI_TyArgs funInfo),
                                           TE_RuntimeTypeVars := fset_of_list (FI_TyArgs funInfo) \<rparr>)
                                   (FI_ReturnType funInfo)"
      using fn_lookup not_ghost_fn tyenv_fun_ghost_constraint_def Let_def
      by (meson GhostOrNot.exhaust)
    show "is_runtime_type env ty"
      using ty_eq apply_subst_specializes_runtime by (simp add: len_tyargs ret_rt tyargs_rt)
  qed
  ultimately show ?case by blast
next
  case (CoreTm_VariantCtor ctorName tyArgs payload)
  from CoreTm_VariantCtor.prems(1) obtain dtName tyvars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName, tyvars, payloadTy)" and
    len_eq: "length tyArgs = length tyvars" and
    tyargs_wk: "list_all (is_well_kinded env) tyArgs" and
    payload_typed: "core_term_type env ghost payload = Some (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)" and
    ty_eq: "ty = CoreTy_Datatype dtName tyArgs"
    by (auto simp: Let_def split: option.splits prod.splits if_splits)
  \<comment> \<open>Well-kinded: CoreTy_Datatype dtName tyArgs requires dtName in TE_Datatypes with matching arity\<close>
  have ctors_consistent: "tyenv_ctors_consistent env"
    using CoreTm_VariantCtor.prems(2) tyenv_well_formed_def by blast
  have dt_lookup: "fmlookup (TE_Datatypes env) dtName = Some (length tyvars)"
    using ctors_consistent ctor_lookup tyenv_ctors_consistent_def by blast
  have wk: "is_well_kinded env ty"
    using ty_eq dt_lookup len_eq tyargs_wk by simp
  \<comment> \<open>Runtime: CoreTy_Datatype dtName tyArgs requires dtName not ghost and list_all runtime tyArgs\<close>
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
  proof
    assume ng: "ghost = NotGhost"
    from CoreTm_VariantCtor.prems(1) ng ctor_lookup len_eq have
      tyargs_rt: "list_all (is_runtime_type env) tyArgs" and
      dt_nonghost: "dtName |\<notin>| TE_GhostDatatypes env"
      by (auto simp: Let_def split: option.splits prod.splits if_splits)
    show "is_runtime_type env ty" using ty_eq tyargs_rt dt_nonghost by simp
  qed
  ultimately show ?case by blast
next
  case (CoreTm_Record flds)
  from CoreTm_Record.prems(1) obtain tys where
    those_ok: "those (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) = Some tys" and
    ty_eq: "ty = CoreTy_Record (zip (map fst flds) tys)"
    by (auto split: option.splits)
  have len_tys: "length tys = length flds"
    using those_ok
    by (metis length_map list_all2_lengthD those_eq_Some)
  have fld_typed: "\<And>i. i < length flds \<Longrightarrow>
      core_term_type env ghost (snd (flds ! i)) = Some (tys ! i)"
  proof -
    fix i assume "i < length flds"
    from those_ok have la: "list_all2 (\<lambda>x y. x = Some y)
        (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) tys"
      by (simp add: those_eq_Some)
    hence len: "length (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) = length tys"
      by (auto dest: list_all2_lengthD)
    obtain a b where ab: "flds ! i = (a, b)" by (cases "flds ! i")
    from la \<open>i < length flds\<close> len
      have "(map (\<lambda>(name, tm). core_term_type env ghost tm) flds) ! i = Some (tys ! i)"
      by (auto simp: list_all2_conv_all_nth)
    with ab \<open>i < length flds\<close> show "core_term_type env ghost (snd (flds ! i)) = Some (tys ! i)"
      by auto
  qed
  have fld_props: "\<And>i. i < length flds \<Longrightarrow>
      is_well_kinded env (tys ! i) \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env (tys ! i))"
  proof -
    fix i assume i_bound: "i < length flds"
    obtain name tm where fld_eq: "flds ! i = (name, tm)" by (cases "flds ! i") auto
    have fld_in: "(name, tm) \<in> set flds" using i_bound fld_eq by (metis nth_mem)
    have "core_term_type env ghost tm = Some (tys ! i)"
      using fld_typed[OF i_bound] fld_eq by simp
    thus "is_well_kinded env (tys ! i) \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env (tys ! i))"
      using CoreTm_Record.IH CoreTm_Record.prems(2) fld_in by auto
  qed
  have wk: "is_well_kinded env ty"
    unfolding ty_eq using fld_props len_tys
    by (auto simp: list_all_iff set_zip in_set_conv_nth)
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
    unfolding ty_eq using fld_props len_tys
    by (auto simp: list_all_iff set_zip in_set_conv_nth)
  ultimately show ?case by blast
next
  case (CoreTm_RecordProj tm fldName)
  from CoreTm_RecordProj.prems(1) obtain flds where
    tm_typed: "core_term_type env ghost tm = Some (CoreTy_Record flds)" and
    fld_lookup: "map_of flds fldName = Some ty"
    by (auto split: option.splits CoreType.splits)
  have IH: "is_well_kinded env (CoreTy_Record flds) \<and>
            (ghost = NotGhost \<longrightarrow> is_runtime_type env (CoreTy_Record flds))"
    using CoreTm_RecordProj.IH tm_typed CoreTm_RecordProj.prems(2) by blast
  have fld_in_set: "ty \<in> snd ` set flds"
    using fld_lookup
    by (metis Range_iff Range_snd map_of_SomeD)
  have wk: "is_well_kinded env ty"
    using IH fld_in_set by (auto simp: list_all_iff)
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
    using IH fld_in_set by (auto simp: list_all_iff)
  ultimately show ?case by blast
next
  case (CoreTm_ArrayProj arr idxs)
  from CoreTm_ArrayProj.prems(1) obtain elemTy dims where
    arr_typed: "core_term_type env ghost arr = Some (CoreTy_Array elemTy dims)" and
    ty_eq: "ty = elemTy"
    by (auto split: option.splits CoreType.splits if_splits)
  have IH: "is_well_kinded env (CoreTy_Array elemTy dims) \<and>
            (ghost = NotGhost \<longrightarrow> is_runtime_type env (CoreTy_Array elemTy dims))"
    using CoreTm_ArrayProj.IH(1) arr_typed CoreTm_ArrayProj.prems(2) by blast
  have wk: "is_well_kinded env ty"
    using IH ty_eq by simp
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
    using IH ty_eq by simp
  ultimately show ?case by blast
next
  case (CoreTm_VariantProj tm ctorName)
  from CoreTm_VariantProj.prems(1) obtain dtName tyArgs where
    tm_typed: "core_term_type env ghost tm = Some (CoreTy_Datatype dtName tyArgs)"
    by (auto split: option.splits CoreType.splits prod.splits if_splits)
  from CoreTm_VariantProj.prems(1) tm_typed obtain dtName2 tyvars payloadTy where
    ctor_lookup: "fmlookup (TE_DataCtors env) ctorName = Some (dtName2, tyvars, payloadTy)" and
    dt_eq: "dtName = dtName2" and
    len_eq: "length tyArgs = length tyvars" and
    ty_eq: "ty = apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy"
    by (auto split: option.splits prod.splits if_splits)
  \<comment> \<open>Well-kinded: apply_subst preserves well-kindedness\<close>
  have payload_wk: "is_well_kinded (env \<lparr> TE_TypeVars := fset_of_list tyvars \<rparr>) payloadTy"
    using CoreTm_VariantProj.prems(2) ctor_lookup tyenv_well_formed_def
      tyenv_payloads_well_kinded_def by blast
  have tm_IH: "is_well_kinded env (CoreTy_Datatype dtName tyArgs) \<and>
               (ghost = NotGhost \<longrightarrow> is_runtime_type env (CoreTy_Datatype dtName tyArgs))"
    using CoreTm_VariantProj.IH tm_typed CoreTm_VariantProj.prems(2) by blast
  hence tyargs_wk: "list_all (is_well_kinded env) tyArgs"
  proof -
    have ctors_consistent: "tyenv_ctors_consistent env"
      using CoreTm_VariantProj.prems(2) tyenv_well_formed_def by blast
    have dt_lookup: "fmlookup (TE_Datatypes env) dtName = Some (length tyvars)"
      using ctors_consistent ctor_lookup dt_eq tyenv_ctors_consistent_def by blast
    from tm_IH show ?thesis using dt_lookup by simp
  qed
  have wk: "is_well_kinded env ty"
    using ty_eq apply_subst_specializes_well_kinded[OF payload_wk tyargs_wk] len_eq by simp
  \<comment> \<open>Runtime: from IH on scrutinee, tyenv_nonghost_payloads_runtime, and apply_subst_preserves_runtime\<close>
  moreover have "ghost = NotGhost \<longrightarrow> is_runtime_type env ty"
  proof
    assume ng: "ghost = NotGhost"
    from tm_IH ng have scrut_rt: "is_runtime_type env (CoreTy_Datatype dtName tyArgs)" by blast
    hence dt_nonghost: "dtName |\<notin>| TE_GhostDatatypes env" by simp
    from scrut_rt have tyargs_rt: "list_all (is_runtime_type env) tyArgs" by simp
    have "tyenv_nonghost_payloads_runtime env"
      using CoreTm_VariantProj.prems(2) tyenv_well_formed_def by blast
    hence payload_rt: "is_runtime_type (env \<lparr> TE_TypeVars := fset_of_list tyvars,
                                               TE_RuntimeTypeVars := fset_of_list tyvars \<rparr>)
                                       payloadTy"
      using ctor_lookup dt_eq dt_nonghost tyenv_nonghost_payloads_runtime_def by blast
    show "is_runtime_type env ty"
      using ty_eq apply_subst_specializes_runtime[OF payload_rt tyargs_rt] len_eq by simp
  qed
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
  have IH: "is_well_kinded env resultTy \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env resultTy)"
    using CoreTm_Match.IH(2) first_body_typed CoreTm_Match.prems(2)
    using arms_nonempty list.set_sel(1) snds.intros by blast
  thus ?case using ty_eq by simp
next
  case (CoreTm_Sizeof tm)
  from CoreTm_Sizeof.prems(1) obtain elemTy dims where
    tm_typed: "core_term_type env ghost tm = Some (CoreTy_Array elemTy dims)" and
    ty_eq: "ty = sizeof_type dims"
    by (auto split: option.splits CoreType.splits if_splits)
  have "is_well_kinded env (sizeof_type dims) \<and> is_runtime_type env (sizeof_type dims)"
    by (cases dims rule: sizeof_type.cases)
       (auto simp: u64_type_def list_all_iff set_zip nth_Cons')
  thus ?case using ty_eq by auto
next
  case (CoreTm_Allocated tm)
  show ?case using CoreTm_Allocated.prems(1)
    by (cases ghost) (auto split: option.splits)
next
  case (CoreTm_Old tm)
  show ?case using CoreTm_Old.prems(1) CoreTm_Old.IH CoreTm_Old.prems(2)
    by (cases ghost) auto
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
  shows "is_runtime_type env ty"
  using core_term_type_well_kinded_and_runtime[OF assms] by blast


end

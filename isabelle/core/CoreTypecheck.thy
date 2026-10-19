theory CoreTypecheck
  imports CoreTyEnvWellFormed CoreFreeVars "../util/NatToString"
begin

(* Definitions for term typechecking. For lemmas, see CoreTypecheckLemmas.thy.
   For statement typechecking, see CoreStmtTypecheck.thy. *)


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
| "pattern_compatible env (CorePat_Int i) ty =
    (case ty of
      \<comment> \<open>For now, CorePat_Int can only match against finite integer scrutinees.
         MathInt scrutinees can only match against CorePat_Wildcard. 
         This might be changed in the future - allowing a MathInt scrutinee to
         match a CorePat_Int pattern might be useful for ghost code.\<close>
       CoreTy_FiniteInt sign bits \<Rightarrow> int_in_range (int_range sign bits) i
     | _ \<Rightarrow> False)"
| "pattern_compatible env (CorePat_Variant ctorName payloadPat) ty =
    (case fmlookup (TE_DataCtors env) ctorName of
      None \<Rightarrow> False
    | Some (dtName, tyvars, payloadTy) \<Rightarrow>
        (case ty of
          CoreTy_Datatype tyName tyArgs \<Rightarrow>
            tyName = dtName
            \<and> length tyArgs = length tyvars
            \<and> pattern_compatible env payloadPat
                (apply_subst (fmap_of_list (zip tyvars tyArgs)) payloadTy)
        | _ \<Rightarrow> False))"
| "pattern_compatible env (CorePat_Record pflds) ty =
    (case ty of
      CoreTy_Record fldTys \<Rightarrow>
        list_all2 (\<lambda>(pn, p) (fn, fty).
                     pn = fn \<and> pattern_compatible env p fty)
                  pflds fldTys
    | _ \<Rightarrow> False)"


(* ========================================================================== *)
(* Valid decreases-term types                                                 *)
(* ========================================================================== *)

fun is_valid_decreases_type :: "CoreType \<Rightarrow> bool" where
  "is_valid_decreases_type CoreTy_Bool = True"
| "is_valid_decreases_type (CoreTy_FiniteInt _ _) = True"
| "is_valid_decreases_type CoreTy_MathInt = True"
| "is_valid_decreases_type (CoreTy_Record flds) =
     (map fst flds = tuple_field_names (length flds) \<and>
      list_all (\<lambda>(_, ty). is_valid_decreases_type ty) flds)"
| "is_valid_decreases_type _ = False"


(* ========================================================================== *)
(* Typechecking rules for casts *)
(* ========================================================================== *)

(* Valid array casts:
    - Widening: T[n] or T[*] \<longrightarrow> T[]
    - Narrowing: T[*] or T[] \<longrightarrow> T[n]  (well-typed, but creates a separate verifier
        obligation: the array must provably have size n at runtime)
    - Casting any array type to itself is also considered valid (but this isn't used
        by the elaborator).  *)
fun dim_cast_ok :: "CoreDimension \<Rightarrow> CoreDimension \<Rightarrow> bool" where
  "dim_cast_ok (CoreDim_Fixed _)      CoreDim_Unknown   = True"     (* widen *)
| "dim_cast_ok CoreDim_Allocatable    CoreDim_Unknown   = True"     (* widen *)
| "dim_cast_ok CoreDim_Unknown        (CoreDim_Fixed _) = True"     (* narrow, checked *)
| "dim_cast_ok CoreDim_Allocatable    (CoreDim_Fixed _) = True"     (* narrow, checked *)
| "dim_cast_ok (CoreDim_Fixed n)      (CoreDim_Fixed m) = (n = m)"  (* identity *)
| "dim_cast_ok CoreDim_Allocatable    CoreDim_Allocatable = True"   (* identity *)
| "dim_cast_ok CoreDim_Unknown        CoreDim_Unknown   = True"     (* identity *)
| "dim_cast_ok CoreDim_Unknown        CoreDim_Allocatable = False"  (* rejected *)
| "dim_cast_ok (CoreDim_Fixed _)      CoreDim_Allocatable = False"  (* rejected *)

(* An array cast is valid if elemTy is unchanged, and the dimension change
   satisfies dim_cast_ok.
   The well-kindedness of the target type is checked separately (see cast_ok). *)
fun array_cast_ok :: "CoreType \<Rightarrow> CoreType \<Rightarrow> bool" where
  "array_cast_ok (CoreTy_Array elemTy dims) (CoreTy_Array elemTy' dims') =
     (elemTy = elemTy' \<and> list_all2 dim_cast_ok dims dims')"
| "array_cast_ok _ _ = False"

(* A general cast can either be an array cast (as described above), or a numeric
   cast (converting any numeric type -- finite int, int or real -- to another). *)
definition cast_ok :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> CoreType \<Rightarrow> bool" where
  "cast_ok env srcTy tgtTy \<equiv>
     is_numeric_type srcTy \<and> is_numeric_type tgtTy
     \<or> array_cast_ok srcTy tgtTy \<and> is_well_kinded env tgtTy"


(* ========================================================================== *)
(* Argument typing for function calls *)
(* ========================================================================== *)

(* The mode in which the actual for a parameter is typechecked, given the
   ambient mode of the call and the parameter's ghost flag. The actual for a
   ghost parameter is always ghost code; otherwise, the ambient mode applies. *)
definition param_mode :: "GhostOrNot \<Rightarrow> GhostOrNot \<Rightarrow> GhostOrNot" where
  "param_mode ghost gh = (if gh = Ghost then Ghost else ghost)"


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

  (* Casts - must satisfy cast_ok, and in NotGhost mode, the target type must
     additionally be runtime. *)
| "core_term_type env ghost (CoreTm_Cast targetTy operand) =
    (case core_term_type env ghost operand of
      None \<Rightarrow> None
    | Some operandTy \<Rightarrow>
        if cast_ok env operandTy targetTy
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

  (* Quantifier - Ghost mode only. The bound variable is a const local, as for Let. *)
| "core_term_type env NotGhost (CoreTm_Quantifier _ _ _ _) = None"
| "core_term_type env Ghost (CoreTm_Quantifier quant var varTy body) =
    (if is_well_kinded env varTy
     then let env' = env \<lparr> TE_LocalVars := fmupd var varTy (TE_LocalVars env),
                           TE_GhostLocals := finsert var (TE_GhostLocals env),
                           TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>
          in (case core_term_type env' Ghost body of
                Some CoreTy_Bool \<Rightarrow> Some CoreTy_Bool
              | _ \<Rightarrow> None)
     else None)"

(* Function call:
   - Function must exist in environment
   - Number of type args must match
   - Type args must be well-kinded and complete
   - In NotGhost mode: type args must be runtime types, and function must not be ghost
   - Term args must be well-typed with types matching expected arg types (after substitution)
      - Ghost args are checked in Ghost mode; others in the ambient mode *)
| "core_term_type env ghost (CoreTm_FunctionCall fnName tyArgs tmArgs) =
    (case fmlookup (TE_Functions env) fnName of
      None \<Rightarrow> None
    | Some funInfo \<Rightarrow>
        \<comment> \<open>Check number of type arguments\<close>
        if length tyArgs \<noteq> length (FI_TyArgs funInfo) then None
        \<comment> \<open>Check type arguments are well-kinded\<close>
        else if \<not> list_all (is_well_kinded env) tyArgs then None
        \<comment> \<open>Check type arguments are complete types\<close>
        else if \<not> list_all is_complete_type tyArgs then None
        \<comment> \<open>In NotGhost mode: check type args are runtime and the called function is not ghost\<close>
        else if ghost = NotGhost \<and> (\<not> list_all (is_runtime_type env) tyArgs \<or> FI_Ghost funInfo = Ghost)
             then None
        \<comment> \<open>Term-level calls must be pure: no Ref arguments, not impure\<close>
        else if \<not> list_all (\<lambda>(_, vor, _). vor = Var) (FI_TmArgs funInfo) then None
        else if FI_Impure funInfo then None
        \<comment> \<open>Check number of term arguments\<close>
        else if length tmArgs \<noteq> length (FI_TmArgs funInfo) then None
        else
          let tySubst = fmap_of_list (zip (FI_TyArgs funInfo) tyArgs);
              expectedArgTypes = map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo);
              argModes = map (\<lambda>(_, _, gh). param_mode ghost gh) (FI_TmArgs funInfo)
          in \<comment> \<open>Check each term argument has the expected type, in the mode
                 determined by its parameter's ghost flag\<close>
             if list_all2 (\<lambda>tm (expectedTy, mode). core_term_type env mode tm = Some expectedTy)
                  tmArgs (zip expectedArgTypes argModes)
             then Some (apply_subst tySubst (FI_ReturnType funInfo))
             else None)"

(* Variant construction:
   - Constructor must exist in TE_DataCtors
   - Number of type arguments must match the constructor's type-vars
   - Type arguments must be well-kinded and complete
   - In NotGhost mode: type arguments must be runtime types
   - Payload must typecheck to the expected payload type (after substitution) *)
| "core_term_type env ghost (CoreTm_VariantCtor ctorName tyArgs payload) =
    (case fmlookup (TE_DataCtors env) ctorName of
      None \<Rightarrow> None
    | Some (dtName, tyvars, payloadTy) \<Rightarrow>
        (if length tyArgs \<noteq> length tyvars then None
        else if \<not> list_all (is_well_kinded env) tyArgs then None
        else if \<not> list_all is_complete_type tyArgs then None
        else if ghost = NotGhost \<and> (\<not> list_all (is_runtime_type env) tyArgs
               \<or> dtName \<in> ghost_datatypes env) then None
        else let tySubst = fmap_of_list (zip tyvars tyArgs)
             in case core_term_type env ghost payload of
                  None \<Rightarrow> None
                | Some actualPayloadTy \<Rightarrow>
                    if actualPayloadTy = apply_subst tySubst payloadTy
                    then Some (CoreTy_Datatype dtName tyArgs)
                    else None))"

  (* Record construction *)
| "core_term_type env ghost (CoreTm_Record flds) =
    (if \<not> distinct (map fst flds) then None
     else case those (map (\<lambda>(name, tm). core_term_type env ghost tm) flds) of
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
   - All arm bodies must have the same type
     (Note: exhaustiveness is NOT checked; a non-exhaustive match that fails to
     find a matching pattern is a runtime error, not a type error.) *)
| "core_term_type env ghost (CoreTm_Match scrut arms) =
    (case core_term_type env ghost scrut of
      None \<Rightarrow> None
    | Some scrutTy \<Rightarrow>
        let pats = map fst arms;
            bodies = map snd arms
        in if arms = [] then None  \<comment> \<open>empty match not allowed\<close>
           else if \<not> list_all (\<lambda>p. pattern_compatible env p scrutTy) pats then None
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

  (* Allocated: Ghost only. The annotation must be exactly the operand's type,
     and must be a complete type; the result is bool. *)
| "core_term_type env NotGhost (CoreTm_Allocated _ _) = None"
| "core_term_type env Ghost (CoreTm_Allocated ty tm) =
    (case core_term_type env Ghost tm of
      Some ty' \<Rightarrow> if ty' = ty \<and> is_complete_type ty then Some CoreTy_Bool else None
    | None \<Rightarrow> None)"

  (* Default value of a type. Type must be well-kinded; in NotGhost mode it
     must additionally be a runtime type. *)
| "core_term_type env ghost (CoreTm_Default ty) =
    (if is_well_kinded env ty \<and> (ghost = NotGhost \<longrightarrow> is_runtime_type env ty)
     then Some ty else None)"

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
  \<comment> \<open>CoreTm_FunctionCall - elements of tmArgs are smaller (whatever mode
      each one is checked in)\<close>
  fix env :: CoreTyEnv
  fix ghost mode :: GhostOrNot
  fix fnName tyArgs tmArgs x2 x xa yb
  fix z :: CoreTerm
  assume "z \<in> set tmArgs"
  hence "size z < Suc (size_list size tmArgs)"
    using size_list_estimation
    by (metis less_not_refl not_less_eq)
  thus "((env, mode, z), env, ghost, CoreTm_FunctionCall fnName tyArgs tmArgs)
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
  fix ty tm
  show "((env, Ghost, tm), env, Ghost, CoreTm_Allocated ty tm)
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
                     TE_GhostLocals := finsert var (TE_GhostLocals env),
                     TE_ConstLocals := finsert var (TE_ConstLocals env) \<rparr>"
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
qed


end

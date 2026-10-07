theory CoreInterp
  imports InterpState "../util/NatToString" "HOL.Bit_Operations"
begin 

(* ========================================================================== *)
(* Types used by the interpreter *)
(* ========================================================================== *)

(* Interpreter errors *)
datatype InterpError = 
  TypeError           (* Type mismatch, e.g. 1 + true, or other compile-time error *)
  | RuntimeError      (* Runtime failure, e.g division by zero, array index out of bounds *)
  | InsufficientFuel  (* Fuel ran out *)

(* Result of executing a statement *)
datatype 'w ExecResult =
  Continue "'w InterpState"
  | Return "'w InterpState" "CoreValue"


(* ========================================================================== *)
(* Integer operations *)
(* ========================================================================== *)

(* Check if a number (finite integer, int or real) is zero *)
fun is_zero :: "CoreValue \<Rightarrow> bool" where
  "is_zero (CV_FiniteInt _ _ i) = (i = 0)"
| "is_zero (CV_Int i) = (i = 0)"
| "is_zero (CV_Real r) = (r = 0)"
| "is_zero _ = False"

(* Check if a shift operation is valid: shift count must be non-negative
   and less than the bit size of the value being shifted *)
fun is_valid_shift :: "CoreValue \<Rightarrow> CoreValue \<Rightarrow> bool" where
  "is_valid_shift (CV_FiniteInt _ b1 _) (CV_FiniteInt _ _ i2) =
    (i2 \<ge> 0 \<and> nat i2 < bit_size b1)"
| "is_valid_shift _ _ = False"

(* Truncated division - rounds towards zero, like C/Java/JavaScript *)
fun tdiv :: "int \<Rightarrow> int \<Rightarrow> int" where
  "tdiv i1 i2 = sgn i1 * sgn i2 * (abs i1 div abs i2)"

(* Truncated modulo - remainder has sign of dividend, like C/Java/JavaScript *)
fun tmod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "tmod i1 i2 = sgn i1 * (abs i1 mod abs i2)"

(* Bitwise complement for finite integers *)
fun int_complement :: "Signedness \<Rightarrow> IntBits \<Rightarrow> int \<Rightarrow> int" where
  "int_complement sign bits i =
    (let (min_val, max_val) = int_range sign bits in
     case sign of
       Signed \<Rightarrow> -i - 1
     | Unsigned \<Rightarrow> max_val - i)"

(* Evaluate a unary operator *)
fun eval_unop :: "CoreUnop \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "eval_unop CoreUnop_Negate val =
    (case val of
      CV_FiniteInt sign bits i \<Rightarrow>
        if int_fits sign bits (-i) then Inr (CV_FiniteInt sign bits (-i))
        else Inl RuntimeError  \<comment> \<open>overflow (negation of largest negative number)\<close>
    | CV_Int i \<Rightarrow> Inr (CV_Int (-i))
    | CV_Real r \<Rightarrow> Inr (CV_Real (-r))
    | _ \<Rightarrow> Inl TypeError)"
| "eval_unop CoreUnop_Complement val =
    (case val of
      CV_FiniteInt sign bits i \<Rightarrow> 
        Inr (CV_FiniteInt sign bits (int_complement sign bits i))  \<comment> \<open>complement always fits\<close>
    | _ \<Rightarrow> Inl TypeError)"
| "eval_unop CoreUnop_Not val =
    (case val of
      CV_Bool b \<Rightarrow> Inr (CV_Bool (\<not>b))
    | _ \<Rightarrow> Inl TypeError)"

(* Evaluate a generic binop int * int \<rightarrow> int *)
(* Checks types and overflow (only CV_FiniteInt accepted) *)
fun generic_finite_int_binop :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "generic_finite_int_binop f (CV_FiniteInt s1 b1 i1) (CV_FiniteInt s2 b2 i2) =
    (if s1 = s2 \<and> b1 = b2 then
      let result = f i1 i2 in
      if int_fits s1 b1 result then Inr (CV_FiniteInt s1 b1 result)
      else Inl RuntimeError  \<comment> \<open>overflow\<close>
     else Inl TypeError)"   \<comment> \<open>mismatched signedness or number of bits\<close>
| "generic_finite_int_binop _ _ _ = Inl TypeError"  \<comment> \<open>mismatched types\<close>

(* Evaluate a generic binop int * int \<rightarrow> bool *)
(* Checks types (only CV_FiniteInt accepted) *)
fun generic_finite_int_cmp_binop :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "generic_finite_int_cmp_binop f (CV_FiniteInt s1 b1 i1) (CV_FiniteInt s2 b2 i2) =
    (if s1 = s2 \<and> b1 = b2 then Inr (CV_Bool (f i1 i2))
      else Inl TypeError)"  \<comment> \<open>mismatched signedness or number of bits\<close>
| "generic_finite_int_cmp_binop _ _ _ = Inl TypeError"  \<comment> \<open>mismatched types\<close>

(* Like generic_finite_int_binop, but also accepts CV_Int *)
fun generic_integer_binop :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "generic_integer_binop f (CV_Int i1) (CV_Int i2) = Inr (CV_Int (f i1 i2))"
| "generic_integer_binop f v1 v2 = generic_finite_int_binop f v1 v2"

(* Like generic_integer_binop, but also accepts CV_Real *)
fun generic_numeric_binop :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> real)
                                \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "generic_numeric_binop fi fr (CV_Real r1) (CV_Real r2) = Inr (CV_Real (fr r1 r2))"
| "generic_numeric_binop fi fr v1 v2 = generic_integer_binop fi v1 v2"

(* Evaluate a generic comparison of two numbers of the same type: ints, reals,
   or finite integers. *)
fun generic_numeric_cmp_binop :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> bool)
                                    \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "generic_numeric_cmp_binop fi fr (CV_Int i1) (CV_Int i2) = Inr (CV_Bool (fi i1 i2))"
| "generic_numeric_cmp_binop fi fr (CV_Real r1) (CV_Real r2) = Inr (CV_Bool (fr r1 r2))"
| "generic_numeric_cmp_binop fi fr v1 v2 = generic_finite_int_cmp_binop fi v1 v2"

(* Evaluate a generic binop bool * bool \<rightarrow> bool *)
(* Checks types *)
fun generic_bool_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "generic_bool_binop f (CV_Bool b1) (CV_Bool b2) = Inr (CV_Bool (f b1 b2))"
| "generic_bool_binop _ _ _ = Inl TypeError"

(* Evaluate a binop *)
(* Arithmetic and ordering work on finite integers, ints and reals; modulo on
   finite integers and ints; the bitwise operators and shifts on finite
   integers only. *)
fun eval_binop :: "CoreBinop \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "eval_binop CoreBinop_Add v1 v2 = generic_numeric_binop (\<lambda>x y. x + y) (\<lambda>x y. x + y) v1 v2"
| "eval_binop CoreBinop_Subtract v1 v2 = generic_numeric_binop (\<lambda>x y. x - y) (\<lambda>x y. x - y) v1 v2"
| "eval_binop CoreBinop_Multiply v1 v2 = generic_numeric_binop (\<lambda>x y. x * y) (\<lambda>x y. x * y) v1 v2"
| "eval_binop CoreBinop_Divide v1 v2 =
    (if is_zero v2 then Inl RuntimeError  \<comment> \<open>division by zero\<close>
    else generic_numeric_binop tdiv (\<lambda>x y. x / y) v1 v2)"
| "eval_binop CoreBinop_Modulo v1 v2 =
    (if is_zero v2 then Inl RuntimeError  \<comment> \<open>division by zero\<close>
    else generic_integer_binop tmod v1 v2)"
| "eval_binop CoreBinop_BitAnd v1 v2 = generic_finite_int_binop (\<lambda>x y. and x y) v1 v2"
| "eval_binop CoreBinop_BitOr v1 v2 = generic_finite_int_binop (\<lambda>x y. or x y) v1 v2"
| "eval_binop CoreBinop_BitXor v1 v2 = generic_finite_int_binop (\<lambda>x y. xor x y) v1 v2"
| "eval_binop CoreBinop_ShiftLeft v1 v2 =
    (if \<not> is_valid_shift v1 v2 then Inl RuntimeError
    else generic_finite_int_binop (\<lambda>x y. push_bit (nat y) x) v1 v2)"
| "eval_binop CoreBinop_ShiftRight v1 v2 =
    (if \<not> is_valid_shift v1 v2 then Inl RuntimeError
    else generic_finite_int_binop (\<lambda>x y. drop_bit (nat y) x) v1 v2)"
  (* Equality and inequality compare any two values *)
| "eval_binop CoreBinop_Equal v1 v2 = Inr (CV_Bool (v1 = v2))"
| "eval_binop CoreBinop_NotEqual v1 v2 = Inr (CV_Bool (v1 \<noteq> v2))"
| "eval_binop CoreBinop_Less v1 v2 =
    generic_numeric_cmp_binop (\<lambda>x y. x < y) (\<lambda>x y. x < y) v1 v2"
| "eval_binop CoreBinop_LessEqual v1 v2 =
    generic_numeric_cmp_binop (\<lambda>x y. x \<le> y) (\<lambda>x y. x \<le> y) v1 v2"
| "eval_binop CoreBinop_Greater v1 v2 =
    generic_numeric_cmp_binop (\<lambda>x y. x > y) (\<lambda>x y. x > y) v1 v2"
| "eval_binop CoreBinop_GreaterEqual v1 v2 =
    generic_numeric_cmp_binop (\<lambda>x y. x \<ge> y) (\<lambda>x y. x \<ge> y) v1 v2"
| "eval_binop CoreBinop_And v1 v2 = generic_bool_binop (\<lambda>x y. x \<and> y) v1 v2"
| "eval_binop CoreBinop_Or v1 v2 = generic_bool_binop (\<lambda>x y. x \<or> y) v1 v2"
| "eval_binop CoreBinop_Implies v1 v2 = generic_bool_binop (\<lambda>x y. x \<longrightarrow> y) v1 v2"

(* Short-circuit evaluation for the logical binops: if the lhs value alone
   determines the result, the rhs is not evaluated. *)
fun short_circuit :: "CoreBinop \<Rightarrow> CoreValue \<Rightarrow> CoreValue option" where
  "short_circuit CoreBinop_And v = (if v = CV_Bool False then Some (CV_Bool False) else None)"
| "short_circuit CoreBinop_Or v = (if v = CV_Bool True then Some (CV_Bool True) else None)"
| "short_circuit CoreBinop_Implies v = (if v = CV_Bool False then Some (CV_Bool True) else None)"
| "short_circuit _ _ = None"


(* ========================================================================== *)
(* Array helpers *)
(* ========================================================================== *)

(* Make a one-dimensional CV_Array of values *)
fun make_1d_array :: "CoreValue list \<Rightarrow> CoreValue" where
  "make_1d_array vals = 
    CV_Array [int (length vals)] 
             (fmap_of_list (zip (map (\<lambda>i.[int i]) [0..<length vals]) vals))"

(* Convert a list of CV_FiniteInt u64 values to a list of ints, or return a type error *)
fun interpret_index_vals :: "CoreValue list \<Rightarrow> InterpError + int list" where
  "interpret_index_vals [] = Inr []"
| "interpret_index_vals (CV_FiniteInt Unsigned IntBits_64 i # rest) =
    (case interpret_index_vals rest of
      Inr restVals \<Rightarrow> Inr (i # restVals)
    | Inl err \<Rightarrow> Inl err)"
| "interpret_index_vals (_ # rest) = Inl TypeError"

(* Convert an array size to a CoreValue: u64 for 1-d, record for 2-d *)
fun array_size_to_value :: "int list \<Rightarrow> CoreValue" where
  "array_size_to_value [n] = CV_FiniteInt Unsigned IntBits_64 n"
| "array_size_to_value sizes =
    CV_Record (zip (tuple_field_names (length sizes))
                   (map (CV_FiniteInt Unsigned IntBits_64) sizes))"


(* ========================================================================== *)
(* Pattern match helpers *)
(* ========================================================================== *)

fun pattern_matches :: "CoreValue \<Rightarrow> CorePattern \<Rightarrow> bool"
and pattern_matches_fields ::
  "(string \<times> CoreValue) list \<Rightarrow> (string \<times> CorePattern) list \<Rightarrow> bool" where
  "pattern_matches (CV_Bool b1) (CorePat_Bool b2) = (b1 = b2)"
| "pattern_matches (CV_FiniteInt _ _ i1) (CorePat_Int i2) = (i1 = i2)"
| "pattern_matches (CV_Variant ctor1 v) (CorePat_Variant ctor2 p) =
    (ctor1 = ctor2 \<and> pattern_matches v p)"
| "pattern_matches (CV_Record vflds) (CorePat_Record pflds) =
    pattern_matches_fields vflds pflds"
| "pattern_matches _ CorePat_Wildcard = True"
| "pattern_matches _ _ = False"
| "pattern_matches_fields [] [] = True"
| "pattern_matches_fields ((vn, v) # vs) ((pn, p) # ps) =
    (vn = pn \<and> pattern_matches v p \<and> pattern_matches_fields vs ps)"
| "pattern_matches_fields _ _ = False"

fun find_matching_arm :: "CoreValue \<Rightarrow> (CorePattern \<times> 'a) list \<Rightarrow> InterpError + 'a" where
  "find_matching_arm _ [] = Inl RuntimeError"  (* no match found *)
| "find_matching_arm val ((pat, rhs) # rest) =
    (if pattern_matches val pat then Inr rhs
    else find_matching_arm val rest)"

(* A matching arm returned by find_matching_arm is one of the arms. *)
lemma find_matching_arm_in_arms:
  "find_matching_arm v arms = Inr rhs \<Longrightarrow> rhs \<in> snd ` set arms"
  by (induction v arms rule: find_matching_arm.induct) (auto split: if_splits)

(* ========================================================================== *)
(* Lvalue path operations *)
(* ========================================================================== *)

(* Get the subvalue at a specific path within a value *)
fun get_value_at_path :: "CoreValue \<Rightarrow> LValuePath list \<Rightarrow> InterpError + CoreValue" where
  "get_value_at_path val [] = Inr val"
| "get_value_at_path (CV_Record flds) (LVPath_RecordProj fldName # rest) =
    (case map_of flds fldName of
      Some val \<Rightarrow> get_value_at_path val rest
    | None \<Rightarrow> Inl TypeError)"  (* field not present in record *)
| "get_value_at_path (CV_Variant ctorName payload) (LVPath_VariantProj expectedCtor # rest) =
    (if ctorName = expectedCtor then get_value_at_path payload rest
    else Inl RuntimeError)"   (* variant projection from wrong ctor *)
| "get_value_at_path (CV_Array _ elementMap) (LVPath_ArrayProj indices # rest) =
    (case fmlookup elementMap indices of
      Some val \<Rightarrow> get_value_at_path val rest
    | None \<Rightarrow> Inl RuntimeError)"    (* array index out of bounds *)
| "get_value_at_path (CV_Array sizes elementMap) (LVPath_ArrayCast dims # rest) =
    (if sizes_match_dims sizes dims then get_value_at_path (CV_Array sizes elementMap) rest
     else Inl RuntimeError)"    (* array's runtime sizes don't match the cast's dims *)
| "get_value_at_path _ _ = Inl TypeError"   (* wrong kind of projection for value *)

(* Update a specific path within a value *)
fun update_value_at_path :: "CoreValue \<Rightarrow> LValuePath list \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "update_value_at_path _ [] new_val = Inr new_val"
| "update_value_at_path (CV_Record flds) (LVPath_RecordProj field # rest) new_val =
    (case map_of flds field of
      Some old_val \<Rightarrow> 
        (case update_value_at_path old_val rest new_val of
          Inr updated_val \<Rightarrow> Inr (CV_Record (AList.update field updated_val flds))
        | Inl err \<Rightarrow> Inl err)
    | None \<Rightarrow> Inl TypeError)"
| "update_value_at_path (CV_Variant ctor_name old_val) (LVPath_VariantProj expected_ctor # rest) new_val =
    (if ctor_name = expected_ctor then
      (case update_value_at_path old_val rest new_val of
        Inr updated_val \<Rightarrow> Inr (CV_Variant ctor_name updated_val)
      | Inl err \<Rightarrow> Inl err)
    else Inl RuntimeError)"  (* ctor name didn't match *)
| "update_value_at_path (CV_Array sizes elementMap) (LVPath_ArrayProj indices # rest) new_val =
    (case fmlookup elementMap indices of
      Some old_val \<Rightarrow>
        (case update_value_at_path old_val rest new_val of
          Inr updated_val \<Rightarrow> Inr (CV_Array sizes (fmupd indices updated_val elementMap))
        | Inl err \<Rightarrow> Inl err)
    | None \<Rightarrow> Inl RuntimeError)"  (* array index out of bounds *)
| "update_value_at_path (CV_Array sizes elementMap) (LVPath_ArrayCast dims # rest) new_val =
    \<comment> \<open>The runtime array size must match the cast's dims, as for reads.
        In addition, writing through an LVPath_ArrayCast is not allowed to change the
        runtime size of the array (e.g., if you have a `T[]` ref to a size-3 array, you
        are not allowed to overwrite it with a size-5 array, because the original array
        might not have been resizable).\<close>
    (if sizes_match_dims sizes dims then
      (case update_value_at_path (CV_Array sizes elementMap) rest new_val of
        Inr updated_val \<Rightarrow>
          (case updated_val of
            CV_Array sizes' elementMap' \<Rightarrow>
              if sizes' = sizes then Inr (CV_Array sizes' elementMap') else Inl RuntimeError
          | _ \<Rightarrow> Inl TypeError)   \<comment> \<open>non-array written through an array cast\<close>
      | Inl err \<Rightarrow> Inl err)
     else Inl RuntimeError)"
| "update_value_at_path _ _ _ = Inl TypeError"  (* path didn't match the found value *)

(* Given a type and an lvalue path, compute the type of the sub-value at that path.
   This mirrors get_value_at_path but operates on types instead of values.
   Returns None if the path is incompatible with the type. *)
fun type_at_path :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> LValuePath list \<Rightarrow> CoreType option" where
  "type_at_path env ty [] = Some ty"
| "type_at_path env (CoreTy_Record fieldTypes) (LVPath_RecordProj field # rest) =
    (case map_of fieldTypes field of
      Some fieldTy \<Rightarrow> type_at_path env fieldTy rest
    | None \<Rightarrow> None)"
| "type_at_path env (CoreTy_Datatype dtName argTypes) (LVPath_VariantProj ctor # rest) =
    (case fmlookup (TE_DataCtors env) ctor of
      Some (dtName2, tyvars, payloadTy) \<Rightarrow>
        if dtName = dtName2 then
          type_at_path env (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy) rest
        else None
    | None \<Rightarrow> None)"
| "type_at_path env (CoreTy_Array elemTy dims) (LVPath_ArrayProj _ # rest) =
    type_at_path env elemTy rest"
  \<comment> \<open>An array cast step retypes the array at the cast's dims (same element
      type). The dims must be well-kinded so that the value is well-typed at
      the new type. (Whether the cast direction is admissible, dim_cast_ok, isn't
      checked here; we rely on the typechecker for that.)\<close>
| "type_at_path env (CoreTy_Array elemTy dims) (LVPath_ArrayCast dims' # rest) =
    (if array_dims_well_kinded dims'
     then type_at_path env (CoreTy_Array elemTy dims') rest
     else None)"
| "type_at_path _ _ (_ # _) = None"

(* Lemma: type_at_path does not depend on TE_ProofGoal. *)
lemma type_at_path_TE_ProofGoal_irrelevant [simp]:
  "type_at_path (env \<lparr> TE_ProofGoal := g \<rparr>) ty p = type_at_path env ty p"
proof (induction p arbitrary: ty)
  case Nil then show ?case by simp
next
  case (Cons step rest)
  show ?case
    by (cases ty; cases step) (simp_all add: Cons.IH split: option.splits)
qed

(* Lemma: type_at_path does not depend on TE_ProofTopLevel. *)
lemma type_at_path_TE_ProofTopLevel_irrelevant [simp]:
  "type_at_path (env \<lparr> TE_ProofTopLevel := b \<rparr>) ty p = type_at_path env ty p"
proof (induction p arbitrary: ty)
  case Nil then show ?case by simp
next
  case (Cons step rest)
  show ?case
    by (cases ty; cases step) (simp_all add: Cons.IH split: option.splits)
qed


(* ========================================================================== *)
(* Store and scope operations *)
(* ========================================================================== *)

(* Allocate a new address in the store and store the given value *)
fun alloc_store :: "'w InterpState \<Rightarrow> CoreValue \<Rightarrow> ('w InterpState \<times> nat)" where
  "alloc_store state val =
    (let addr = length (IS_Store state);
         new_store = IS_Store state @ [val]
    in (state \<lparr> IS_Store := new_store \<rparr>, addr))"

(* Bind a local variable to a value, in a fresh store cell. Whether the name
   counts as a const local is left as it was; the two helpers below settle
   that, and are what the interpreter uses. *)
fun bind_local :: "string \<Rightarrow> CoreValue \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState" where
  "bind_local varName val state =
    (let (state', addr) = alloc_store state val
     in state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state'),
                 IS_Refs := fmdrop varName (IS_Refs state') \<rparr>)"

(* Bind a const local variable to a value, in a fresh store cell. Used for the
   variable of a Let or a Quantifier, a Var parameter, and a Ref declaration
   whose base is read-only (which copies the value). *)
fun bind_const_local :: "string \<Rightarrow> CoreValue \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState" where
  "bind_const_local varName val state =
    (bind_local varName val state)
      \<lparr> IS_ConstLocals := finsert varName (IS_ConstLocals state) \<rparr>"

(* Bind a non-const local variable to a value, in a fresh store cell. Used for
   the variable of a Var declaration (CoreStmt_VarDecl, CoreStmt_VarDeclCall)
   or an Obtain. The name is removed from IS_ConstLocals in case it was
   previously a const local (now shadowed by this fresh non-const binding). *)
fun bind_mutable_local :: "string \<Rightarrow> CoreValue \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState" where
  "bind_mutable_local varName val state =
    (bind_local varName val state)
      \<lparr> IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"

(* Bind a name as a ref to an existing store location (an address and a path
   into the value stored there). Used for a Ref parameter, and a Ref
   declaration whose base is writable (which aliases the base). The name is
   dropped from IS_Locals and IS_ConstLocals so that the new ref properly
   shadows any previous binding with the same name. *)
fun bind_ref :: "string \<Rightarrow> (nat \<times> LValuePath list) \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState" where
  "bind_ref varName addrAndPath state =
    state \<lparr> IS_Locals := fmdrop varName (IS_Locals state),
            IS_Refs := fmupd varName addrAndPath (IS_Refs state),
            IS_ConstLocals := fminus (IS_ConstLocals state) {|varName|} \<rparr>"

(* Restore scope after exiting a block:
   - old_state: the state before entering the scope
   - new_state: the state after executing the inner scope
   Returns: new_state with locals/refs restored and store truncated *)
fun restore_scope :: "'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState" where
  "restore_scope old_state new_state =
    new_state \<lparr> IS_Locals := IS_Locals old_state,
                IS_Refs := IS_Refs old_state,
                IS_ConstLocals := IS_ConstLocals old_state,
                IS_TyArgs := IS_TyArgs old_state,
                IS_Store := take (length (IS_Store old_state)) (IS_Store new_state) \<rparr>"

(* Exchange values at two lvalue locations *)
fun perform_swap :: "'w InterpState \<Rightarrow> (nat \<times> LValuePath list) \<Rightarrow> (nat \<times> LValuePath list) \<Rightarrow> InterpError + 'w InterpState" where
  "perform_swap state (addr1, path1) (addr2, path2) =
    (case get_value_at_path (IS_Store state ! addr1) path1 of
      Inl err \<Rightarrow> Inl err
    | Inr val1 \<Rightarrow>
        (case get_value_at_path (IS_Store state ! addr2) path2 of
          Inl err \<Rightarrow> Inl err
        | Inr val2 \<Rightarrow>
            \<comment> \<open>Perform the first update and continue from the resulting store, so that
                if addr1 = addr2 the second update sees the first update's result.\<close>
            (case update_value_at_path (IS_Store state ! addr1) path1 val2 of
              Inl err \<Rightarrow> Inl err
            | Inr new_val1 \<Rightarrow>
                (let store1 = (IS_Store state)[addr1 := new_val1] in
                case update_value_at_path (store1 ! addr2) path2 val1 of
                  Inl err \<Rightarrow> Inl err
                | Inr new_val2 \<Rightarrow>
                    Inr (state \<lparr> IS_Store := store1[addr2 := new_val2] \<rparr>)))))"


(* ========================================================================== *)
(* Function call helpers *)
(* ========================================================================== *)

(* Get all Inr values from a list, drop Inl values *)
fun rights :: "('a + 'b) list \<Rightarrow> 'b list" where
  "rights [] = []"
| "rights (Inl _ # xs) = rights xs"
| "rights (Inr x # xs) = x # rights xs"

(* Determine whether a given name refers to a pure function (no Ref parameters) *)
fun is_pure_fun :: "'w InterpState \<Rightarrow> string \<Rightarrow> bool" where
  "is_pure_fun state fnName =
    (case fmlookup (IS_Functions state) fnName of
      Some funInfo \<Rightarrow> 
        (\<not> list_ex (\<lambda>(_, vr). vr = Ref) (IF_Args funInfo))
        \<and> (\<not> IF_Impure funInfo)
    | None \<Rightarrow> False)"

(* Add a single function argument to the state. *)
(* Takes: (parameter info, lvalue result, rvalue result) and current state
   Returns: updated state, or error *)
fun process_one_arg :: "((string \<times> VarOrRef)
                        \<times> (InterpError + (nat \<times> LValuePath list))
                        \<times> (InterpError + CoreValue))
                \<Rightarrow> InterpError + 'w InterpState
                \<Rightarrow> InterpError + 'w InterpState" where
  "process_one_arg _ (Inl err) = Inl err"
| "process_one_arg ((name, Var), _, Inr val) (Inr state) =
    Inr (bind_const_local name val state)"
| "process_one_arg ((name, Var), _, Inl err) _ = Inl err"
| "process_one_arg ((name, Ref), Inr (addr, path), Inr _) (Inr state) =
    Inr (bind_ref name (addr, path) state)"
| "process_one_arg ((name, Ref), Inl err, _) _ = Inl err"
| "process_one_arg ((name, Ref), _, Inl err) _ = Inl err"

(* Once an error has occurred, folding further arguments keeps it. *)
lemma fold_process_one_arg_error:
  "fold process_one_arg xs (Inl err) = Inl err"
  by (induct xs) simp_all

(* Apply extern function ref updates back to the store. *)
(* Takes list of ref lvalues and corresponding new values, returns updated state. *)
fun apply_ref_updates :: "'w InterpState \<Rightarrow> (nat \<times> LValuePath list) list \<Rightarrow> CoreValue list 
                            \<Rightarrow> InterpError + 'w InterpState" where
  "apply_ref_updates state [] [] = Inr state"
| "apply_ref_updates state ((addr, path) # rest_lvals) (newVal # rest_vals) =
    (case update_value_at_path (IS_Store state ! addr) path newVal of
      Inr updated_val \<Rightarrow>
        (let state' = state \<lparr> IS_Store := (IS_Store state)[addr := updated_val] \<rparr>
         in apply_ref_updates state' rest_lvals rest_vals)
    | Inl err \<Rightarrow> Inl err)"
| "apply_ref_updates _ _ _ = Inl TypeError"  (* mismatched list lengths *)


(* ========================================================================== *)
(* Default values *)
(* ========================================================================== *)

(* Extract the size of each Fixed dimension as an int list. If the input
   contains any non-Fixed dimension, the result is meaningless (only used in
   the all-Fixed branch of default_value). *)
fun fixed_dim_sizes :: "CoreDimension list \<Rightarrow> int list" where
  "fixed_dim_sizes [] = []"
| "fixed_dim_sizes (CoreDim_Fixed n # ds) = n # fixed_dim_sizes ds"
| "fixed_dim_sizes (_ # ds) = fixed_dim_sizes ds"

(* Compute the default value of a (ground) CoreType. Fuel is required
   because the recursion goes through datatype payload types substituted by
   the datatype's tyArgs, which need not be syntactically smaller than the
   input. Runs out-of-fuel with InsufficientFuel; encounters a CoreTy_Var
   with TypeError (statically impossible for a well-typed, ground input). *)
function default_value :: "nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreType \<Rightarrow> InterpError + CoreValue"
  and default_value_list :: "nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreType list \<Rightarrow> InterpError + CoreValue list"
where
  "default_value 0 _ _ = Inl InsufficientFuel"
| "default_value (Suc _) _ CoreTy_Bool = Inr (CV_Bool False)"
| "default_value (Suc _) _ (CoreTy_FiniteInt sign bits) = Inr (CV_FiniteInt sign bits 0)"
| "default_value (Suc fuel) state (CoreTy_Record flds) =
    (case default_value_list fuel state (map snd flds) of
      Inl err \<Rightarrow> Inl err
    | Inr vals \<Rightarrow> Inr (CV_Record (zip (map fst flds) vals)))"
| "default_value (Suc fuel) state (CoreTy_Datatype dtName tyArgs) =
    (case fmlookup (IS_DataCtorsByType state) dtName of
      Some (ctorName # _) \<Rightarrow>
        (case fmlookup (IS_DataCtors state) ctorName of
          None \<Rightarrow> Inl TypeError
        | Some (_, tyvars, payloadTy) \<Rightarrow>
            if length tyvars = length tyArgs then
              let subst = fmap_of_list (zip tyvars tyArgs);
                  substPayloadTy = apply_subst subst payloadTy in
              (case default_value fuel state substPayloadTy of
                Inl err \<Rightarrow> Inl err
              | Inr v \<Rightarrow> Inr (CV_Variant ctorName v))
            else Inl TypeError)
    | _ \<Rightarrow> Inl TypeError)"
| "default_value (Suc fuel) state (CoreTy_Array elemTy dims) =
    (if list_all (\<lambda>d. dim_category d = DimCat_Fixed) dims then
       let sizes = fixed_dim_sizes dims in
       (case default_value fuel state elemTy of
         Inl err \<Rightarrow> Inl err
       | Inr ev \<Rightarrow>
           Inr (CV_Array sizes (fmap_of_list (map (\<lambda>idx. (idx, ev)) (all_indices sizes)))))
     else
       Inr (CV_Array (replicate (length dims) 0) fmempty))"
| "default_value (Suc _) _ CoreTy_MathInt = Inr (CV_Int 0)"
| "default_value (Suc _) _ CoreTy_MathReal = Inr (CV_Real 0)"
| "default_value (Suc _) _ (CoreTy_Var _) = Inl TypeError"

| "default_value_list 0 _ _ = Inl InsufficientFuel"
| "default_value_list (Suc _) _ [] = Inr []"
| "default_value_list (Suc fuel) state (ty # tys) =
    (case default_value fuel state ty of
      Inl err \<Rightarrow> Inl err
    | Inr v \<Rightarrow>
        (case default_value_list fuel state tys of
          Inl err \<Rightarrow> Inl err
        | Inr vs \<Rightarrow> Inr (v # vs)))"
  by pat_completeness auto
termination by lexicographic_order


(* ========================================================================== *)
(* Allocated *)
(* ========================================================================== *)

(* Combine the results of checking each component: an error if any component
   errored, otherwise true iff any component was true. *)
fun any_allocated :: "(InterpError + bool) list \<Rightarrow> InterpError + bool" where
  "any_allocated [] = Inr False"
| "any_allocated (Inl err # _) = Inl err"
| "any_allocated (Inr b # rest) =
    (case any_allocated rest of
      Inl err \<Rightarrow> Inl err
    | Inr b' \<Rightarrow> Inr (b \<or> b'))"

(* Does a value of the given (ground) type currently hold allocated storage?
   The type is needed because a CoreValue does not record whether an array is
   allocatable or fixed-size: an allocatable array and a fixed-size array of
   the same size are the same CoreValue.
     - An allocatable array is allocated iff all of its sizes are non-zero.
     - Any other array, a record or a variant is allocated iff some component
       (element, field or payload) is.
     - Scalars are never allocated.
   Recursion is on the value, so no fuel is needed. TypeError arises only for
   a type variable or an unknown data constructor, neither of which can happen
   for a well-typed value of a ground type. *)
function is_allocated :: "(string, string \<times> string list \<times> CoreType) fmap
    \<Rightarrow> CoreValue \<Rightarrow> CoreType \<Rightarrow> InterpError + bool" where
  "is_allocated ctors (CV_Bool _) _ = Inr False"
| "is_allocated ctors (CV_FiniteInt _ _ _) _ = Inr False"
| "is_allocated ctors (CV_Int _) _ = Inr False"
| "is_allocated ctors (CV_Real _) _ = Inr False"
| "is_allocated ctors (CV_Record fieldValues) ty =
    (case ty of
      CoreTy_Record fieldTypes \<Rightarrow>
        any_allocated
          (map (\<lambda>p. is_allocated ctors (snd (fst p)) (snd (snd p)))
               (zip fieldValues fieldTypes))
    | _ \<Rightarrow> Inl TypeError)"
| "is_allocated ctors (CV_Variant ctor payload) ty =
    (case ty of
      CoreTy_Datatype _ argTypes \<Rightarrow>
        (case fmlookup ctors ctor of
          Some (_, tyvars, payloadTy) \<Rightarrow>
            if length tyvars = length argTypes then
              is_allocated ctors payload
                (apply_subst (fmap_of_list (zip tyvars argTypes)) payloadTy)
            else Inl TypeError
        | None \<Rightarrow> Inl TypeError)
    | _ \<Rightarrow> Inl TypeError)"
| "is_allocated ctors (CV_Array sizes valuesMap) ty =
    (case ty of
      CoreTy_Array elemTy dims \<Rightarrow>
        if list_ex (\<lambda>d. d = CoreDim_Allocatable) dims
        then Inr (list_all (\<lambda>s. s \<noteq> 0) sizes)
        else any_allocated
               (map (\<lambda>idx. case fmlookup valuesMap idx of
                              Some v \<Rightarrow> is_allocated ctors v elemTy
                            | None \<Rightarrow> Inl TypeError)
                    (all_indices sizes))
    | _ \<Rightarrow> Inl TypeError)"
  by pat_completeness auto

termination is_allocated
proof (relation "measure (\<lambda>(ctors, val, ty). size val)")
  show "wf (measure (\<lambda>(ctors, val, ty). size val))" by simp
next
  \<comment> \<open>Record case: p is a (value, type) pair from the zip, so fst p is a field.\<close>
  fix ctors :: "(string, string \<times> string list \<times> CoreType) fmap"
  fix fieldValues :: "(string \<times> CoreValue) list"
  fix ty :: CoreType
  fix fieldTypes :: "(string \<times> CoreType) list"
  fix p :: "(string \<times> CoreValue) \<times> (string \<times> CoreType)"
  assume "p \<in> set (zip fieldValues fieldTypes)"
  hence "fst p \<in> set fieldValues" by (metis set_zip_leftD prod.collapse)
  hence "(fst (fst p), snd (fst p)) \<in> set fieldValues" by simp
  hence "size (snd (fst p)) < size (CV_Record fieldValues)"
    by (rule size_record_field)
  thus "((ctors, snd (fst p), snd (snd p)), ctors, CV_Record fieldValues, ty)
        \<in> measure (\<lambda>(ctors, val, ty). size val)"
    by simp
next
  \<comment> \<open>Variant case: payload is a direct subterm.\<close>
  fix ctors :: "(string, string \<times> string list \<times> CoreType) fmap"
  fix ctor :: string
  fix payload :: CoreValue
  fix ty :: CoreType
  fix x11 :: string
  fix x12 :: "CoreType list"
  fix x2 x y xa ya
  show "((ctors, payload, apply_subst (fmap_of_list (zip xa x12)) ya),
         ctors, CV_Variant ctor payload, ty) \<in> measure (\<lambda>(ctors, val, ty). size val)"
    by simp
next
  \<comment> \<open>Array case: element found by lookup.\<close>
  fix ctors :: "(string, string \<times> string list \<times> CoreType) fmap"
  fix sizes :: "int list"
  fix valuesMap :: "(int list, CoreValue) fmap"
  fix ty :: CoreType
  fix x71 :: CoreType
  fix x72 :: "CoreDimension list"
  fix x :: "int list"
  fix x2 :: CoreValue
  assume "fmlookup valuesMap x = Some x2"
  hence "size x2 < size (CV_Array sizes valuesMap)"
    by (rule size_array_lookup)
  thus "((ctors, x2, x71), ctors, CV_Array sizes valuesMap, ty)
        \<in> measure (\<lambda>(ctors, val, ty). size val)"
    by simp
qed


(* ========================================================================== *)
(* Casting *)
(* ========================================================================== *)

(* Apply a cast to a value.
    - RuntimeError if the cast fails (overflow for casts to a finite integer type;
      array's runtime size doesn't match for array casts to CoreDim_Fixed).
    - TypeError if the cast itself is invalid (only array or integer targets are allowed).
    - Otherwise: successful cast, returns the new value. *)
fun cast_value :: "CoreType \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "cast_value (CoreTy_FiniteInt sign bits) (CV_FiniteInt _ _ i) =
     (if int_fits sign bits i then Inr (CV_FiniteInt sign bits i)
      else Inl RuntimeError)"
| "cast_value (CoreTy_FiniteInt sign bits) (CV_Int i) =
     (if int_fits sign bits i then Inr (CV_FiniteInt sign bits i)
      else Inl RuntimeError)"
| "cast_value (CoreTy_FiniteInt _ _) _ = Inl TypeError"
| "cast_value CoreTy_MathInt (CV_FiniteInt _ _ i) = Inr (CV_Int i)"
| "cast_value CoreTy_MathInt (CV_Int i) = Inr (CV_Int i)"
| "cast_value CoreTy_MathInt _ = Inl TypeError"
| "cast_value (CoreTy_Array _ dims) (CV_Array sizes elems) =
     (if sizes_match_dims sizes dims then Inr (CV_Array sizes elems)
      else Inl RuntimeError)"
| "cast_value (CoreTy_Array _ _) _ = Inl TypeError"
| "cast_value _ _ = Inl TypeError"

(* Apply an optional cast to a value (used for the return value of an
   impure call on the rhs of VarDeclCall / AssignCall). None passes the value
   through; Some t casts to t as for CoreTm_Cast. *)
fun apply_cast_opt :: "CoreType option \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "apply_cast_opt None v = Inr v"
| "apply_cast_opt (Some t) v = cast_value t v"


(* ========================================================================== *)
(* Helpers for Quantifier and Obtain *)
(* ========================================================================== *)

(* The set of all values of a (ground) type; this is what a quantified variable
   of that type ranges over.
   Whether a value has a ground type depends only on the datatype tables of the
   type environment (value_has_type reads nothing else), so "any environment
   that has the state's tables" picks out a single set. *)
definition values_of_type :: "'w InterpState \<Rightarrow> CoreType \<Rightarrow> CoreValue set" where
  "values_of_type state ty =
    {v. \<exists>env. TE_Datatypes env = IS_Datatypes state
             \<and> TE_DataCtors env = IS_DataCtors state
             \<and> value_has_type env v ty}"

(* The result of f at the least fuel where it is not InsufficientFuel, or
   InsufficientFuel if there is no such fuel. *)
definition converged :: "(nat \<Rightarrow> InterpError + 'a) \<Rightarrow> InterpError + 'a" where
  "converged f =
    (if \<exists>m. f m \<noteq> Inl InsufficientFuel
     then f (LEAST m. f m \<noteq> Inl InsufficientFuel)
     else Inl InsufficientFuel)"

(* Given a set of values, and an "evaluation function", return None if all values
   evaluate to Inr b (with b boolean), or an error otherwise.

   This is used when interpreting a quantifier term, "forall (x:ty) e" or
   "exists (x:ty) e", or for "obtain" statements. The argument "vals" represents all
   values of type "ty", and the function "r" represents evaluating the expression "e"
   with "x" bound to that value.

   The error InsufficientFuel takes priority over all other errors. Otherwise,
   an instance that is still out of fuel could turn into an error at greater depth
   and change the answer, breaking fuel monotonicity.

   After that, TypeError takes priority over RuntimeError. TypeError can result from
   some instance returning Inl TypeError, or some instance returning Inr x where x
   is not CV_Bool.
*)
definition instances_error ::
    "CoreValue set \<Rightarrow> (CoreValue \<Rightarrow> InterpError + CoreValue) \<Rightarrow> InterpError option" where
  "instances_error vals r =
    (if \<exists>v \<in> vals. r v = Inl InsufficientFuel then Some InsufficientFuel
     else if \<exists>v \<in> vals. r v = Inl TypeError \<or> (\<exists>w. r v = Inr w \<and> (\<forall>b. w \<noteq> CV_Bool b))
          then Some TypeError
     else if \<exists>v \<in> vals. r v = Inl RuntimeError then Some RuntimeError
     else None)"

(* Evaluate a quantifier term, "forall x:ty e" or "exists x:ty e", given the set of
   all values of type "ty", and a function that evaluates "e" given a value for "x". *)
definition eval_quantifier ::
    "Quantifier \<Rightarrow> CoreValue set \<Rightarrow> (CoreValue \<Rightarrow> InterpError + CoreValue)
      \<Rightarrow> InterpError + CoreValue" where
  "eval_quantifier quant vals r =
    \<comment> \<open>Check for error using instances_error.\<close>
    (case instances_error vals r of
      Some err \<Rightarrow> Inl err
    | None \<Rightarrow>
        \<comment> \<open>Since instances_error returned None, we know that `r v` is either CV_Bool True
           or CV_False for every v \<in> vals, so we can evaluate the quantifier using a HOL
           \<forall> or \<exists> expression.\<close>
        Inr (CV_Bool (case quant of
               Quant_Forall \<Rightarrow> (\<forall>v \<in> vals. r v = Inr (CV_Bool True))
             | Quant_Exists \<Rightarrow> (\<exists>v \<in> vals. r v = Inr (CV_Bool True)))))"

(* Choose a value satisfying the condition of an Obtain, given the result of
   the condition at each value of the domain. It is a RuntimeError if there is
   no such value.

   TODO: currently this produces the same value whenever the type and condition are
   the same. For example, after "obtain x:i32 x>0" and "obtain y:i32 y>0", it would be
   provable that x==y. I think this is undesirable. I think the correct semantics should be
   that if the *same* obtain statement is run twice (with equivalent conditions) then the
   same value is obtained, but if *different* obtain statements are run, then they might
   give different values. For example, in the above example with x and y, we would then be
   able to prove neither x==y, nor x!=y. However, in an example like "ghost function f(): i32
   { obtain x:i32 x>0; return x; }", f() would still be a pure function - so all calls to f()
   would give the same result - as would be expected for any pure function.

   To implement that, we would need to add some kind of unique tag (the source code location
   would do) to CoreStmt_Obtain, and then use the tag in the SOME, as in:
     SOME (loc,v). v \<in> vals \<and> r v = Inr (CV_Bool True) \<and> loc = (location from the CoreStmt).

   This is left as future work.
*)
definition choose_witness ::
    "CoreValue set \<Rightarrow> (CoreValue \<Rightarrow> InterpError + CoreValue) \<Rightarrow> InterpError + CoreValue" where
  "choose_witness vals r =
    (case instances_error vals r of
      Some err \<Rightarrow> Inl err
    | None \<Rightarrow>
        if \<exists>v \<in> vals. r v = Inr (CV_Bool True)
        then Inr (SOME v. v \<in> vals \<and> r v = Inr (CV_Bool True))
        else Inl RuntimeError)"

(* Given the values of the invariants of a loop, return None if all of them are
   true, or an error otherwise. A false invariant is a RuntimeError, and a
   non-boolean invariant is a TypeError. *)
definition invariants_error :: "CoreValue list \<Rightarrow> InterpError option" where
  "invariants_error vals =
    (if \<exists>v \<in> set vals. \<forall>b. v \<noteq> CV_Bool b then Some TypeError
     else if CV_Bool False \<in> set vals then Some RuntimeError
     else None)"

(* ========================================================================== *)
(* The main intepreter definitions *)
(* ========================================================================== *)

(* The interpreter runs both Ghost and NotGhost code. As a consequence, it is
   not executable.

   The fuel has two levels. The first argument of each function is the
   depth `d`, the second is the ordinary fuel. Every case passes the depth
   through unchanged, except Quantifier and Obtain, which spend one unit of
   depth and in return evaluate each instance of their body at whatever
   fuel that instance needs.

   "The program terminates with result r" is therefore "there are d and fuel at which
   the interpreter returns r". If this exists, it is independent of the precise
   amount of fuel used (so long as it is sufficient); see CoreInterpFuelMono.thy.
*)

function interp_term :: "nat \<Rightarrow> nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreTerm \<Rightarrow> InterpError + CoreValue"
  and interp_term_list :: "nat \<Rightarrow> nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreTerm list \<Rightarrow> InterpError + CoreValue list"
  and interp_writable_lvalue :: "nat \<Rightarrow> nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreTerm \<Rightarrow> InterpError + nat \<times> LValuePath list"
  and interp_statement :: "nat \<Rightarrow> nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreStatement \<Rightarrow> InterpError + 'w ExecResult"
  and interp_statement_list :: "nat \<Rightarrow> nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreStatement list \<Rightarrow> InterpError + 'w ExecResult"
  and interp_function_call :: "nat \<Rightarrow> nat \<Rightarrow> 'w InterpState \<Rightarrow> string \<Rightarrow> CoreType list \<Rightarrow> CoreTerm list \<Rightarrow> InterpError + ('w InterpState \<times> CoreValue)"
where
  (* Interpret a term *)
  "interp_term _ 0 _ _ = Inl InsufficientFuel"

  (* Literals *)
| "interp_term _ (Suc _) _ (CoreTm_LitBool b) = Inr (CV_Bool b)"
| "interp_term _ (Suc _) _ (CoreTm_LitInt i) =
    (case get_type_for_int i of
      Some (sign, bits) \<Rightarrow> Inr (CV_FiniteInt sign bits i)
    | None \<Rightarrow> Inl TypeError)"
| "interp_term d (Suc fuel) state (CoreTm_LitArray _ tms) =
    (case interp_term_list d fuel state tms of
      Inl err \<Rightarrow> Inl err
    | Inr vals \<Rightarrow> Inr (make_1d_array vals))"

  (* Variable lookup (local var or global constant) *)
| "interp_term _ (Suc _) state (CoreTm_Var varName) =
    (case fmlookup (IS_Locals state) varName of
      Some addr \<Rightarrow> Inr (IS_Store state ! addr)
    | None \<Rightarrow>
      (case fmlookup (IS_Refs state) varName of
        Some (addr, path) \<Rightarrow> get_value_at_path (IS_Store state ! addr) path
      | None \<Rightarrow>
        (case fmlookup (IS_Globals state) varName of
          Some val \<Rightarrow> Inr val
        | None \<Rightarrow> Inl TypeError)))"  \<comment> \<open>name not in scope\<close>

  (* Cast (delegates to cast_value) *)
| "interp_term d (Suc fuel) state (CoreTm_Cast targetTy tm) =
    (case interp_term d fuel state tm of
      Inl err \<Rightarrow> Inl err
    | Inr v \<Rightarrow> cast_value targetTy v)"

  (* Unary operator *)
| "interp_term d (Suc fuel) state (CoreTm_Unop op tm) =
    (case interp_term d fuel state tm of
      Inl err \<Rightarrow> Inl err
    | Inr val \<Rightarrow> eval_unop op val)"

  (* Binary operator *)
| "interp_term d (Suc fuel) state (CoreTm_Binop op lhsTm rhsTm) =
    (case interp_term d fuel state lhsTm of
      Inl err \<Rightarrow> Inl err
    | Inr lhsVal \<Rightarrow>
        (case short_circuit op lhsVal of
          Some result \<Rightarrow> Inr result
        | None \<Rightarrow>
            (case interp_term d fuel state rhsTm of
              Inl err \<Rightarrow> Inl err
            | Inr rhsVal \<Rightarrow> eval_binop op lhsVal rhsVal)))"

  (* Let *)
| "interp_term d (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm) =
    (case interp_term d fuel state rhsTm of
      Inl err \<Rightarrow> Inl err
    | Inr rhsVal \<Rightarrow> interp_term d fuel (bind_const_local varName rhsVal state) bodyTm)"

  (* Function call *)
| "interp_term d (Suc fuel) state (CoreTm_FunctionCall fnName argTypes argTms) =
    (if is_pure_fun state fnName then
      (case interp_function_call d fuel state fnName argTypes argTms of
        \<comment> \<open>Pure functions don't change the state, so we can ignore the new state here\<close>
        Inr (newState, retVal) \<Rightarrow> Inr retVal
      | Inl err \<Rightarrow> Inl err)
    else Inl TypeError)"  \<comment> \<open>attempt to call non-pure function in term context\<close>

  (* Variant construction *)
| "interp_term d (Suc fuel) state (CoreTm_VariantCtor ctorName _ payloadTm) =
    (case interp_term d fuel state payloadTm of
      Inl err \<Rightarrow> Inl err
    | Inr payloadValue \<Rightarrow> Inr (CV_Variant ctorName payloadValue))"

  (* Record construction *)
| "interp_term d (Suc fuel) state (CoreTm_Record nameTermPairs) =
    (case interp_term_list d fuel state (map snd nameTermPairs) of
      Inl err \<Rightarrow> Inl err
    | Inr vals \<Rightarrow> Inr (CV_Record (zip (map fst nameTermPairs) vals)))"

  (* Record projection *)
| "interp_term d (Suc fuel) state (CoreTm_RecordProj tm fldName) =
    (case interp_term d fuel state tm of
      Inr (CV_Record nameTmPairs) \<Rightarrow>
        (case map_of nameTmPairs fldName of
          Some val \<Rightarrow> Inr val
        | None \<Rightarrow> Inl TypeError)
    | Inr _ \<Rightarrow> Inl TypeError
    | Inl err \<Rightarrow> Inl err)"

  (* Variant projection (get payload; ctor name must match) *)
| "interp_term d (Suc fuel) state (CoreTm_VariantProj tm expectedCtorName) =
    (case interp_term d fuel state tm of
      Inr (CV_Variant actualCtorName payload) \<Rightarrow>
        (if actualCtorName = expectedCtorName then Inr payload
        else Inl RuntimeError)  \<comment> \<open>constructor name mismatch\<close>
    | Inr _ \<Rightarrow> Inl TypeError  \<comment> \<open>not a variant value\<close>
    | Inl err \<Rightarrow> Inl err)"

  (* Array projection (indexing) *)
| "interp_term d (Suc fuel) state (CoreTm_ArrayProj arrayTm idxTms) =
    (case interp_term d fuel state arrayTm of
      Inr (CV_Array _ elementMap) \<Rightarrow>
        (case interp_term_list d fuel state idxTms of
          Inr indexVals \<Rightarrow>
            (case interpret_index_vals indexVals of
              Inr indices \<Rightarrow>
                (case fmlookup elementMap indices of
                  Some result \<Rightarrow> Inr result
                | None \<Rightarrow> Inl RuntimeError)  \<comment> \<open>array index out of bounds\<close>
            | Inl err \<Rightarrow> Inl err)  \<comment> \<open>index terms not of type u64\<close>
        | Inl err \<Rightarrow> Inl err)  \<comment> \<open>error evaluating index terms\<close>
    | Inr _ \<Rightarrow> Inl TypeError  \<comment> \<open>not an array value\<close>
    | Inl err \<Rightarrow> Inl err)"  \<comment> \<open>error evaluating array term\<close>

  (* Pattern match *)
| "interp_term d (Suc fuel) state (CoreTm_Match scrutTm arms) =
    (case interp_term d fuel state scrutTm of
      Inr scrutVal \<Rightarrow>
        (case find_matching_arm scrutVal arms of
          Inr armTm \<Rightarrow> interp_term d fuel state armTm
        | Inl err \<Rightarrow> Inl err)
    | Inl err \<Rightarrow> Inl err)"

  (* Sizeof *)
| "interp_term d (Suc fuel) state (CoreTm_Sizeof tm) =
    (case interp_term d fuel state tm of
      Inr (CV_Array sizes _) \<Rightarrow> Inr (array_size_to_value sizes)
    | Inr _ \<Rightarrow> Inl TypeError
    | Inl err \<Rightarrow> Inl err)"

  (* Quantifier. This spends one unit of depth. The body is evaluated at every
     value of the variable's type, each at its own converged fuel, and the
     results are combined by eval_quantifier. *)
| "interp_term 0 (Suc _) _ (CoreTm_Quantifier _ _ _ _) = Inl InsufficientFuel"
| "interp_term (Suc d) (Suc _) state (CoreTm_Quantifier quant varName varTy bodyTm) =
    eval_quantifier quant
      (values_of_type state (apply_subst (IS_TyArgs state) varTy))
      (\<lambda>v. converged (\<lambda>m. interp_term d m (bind_const_local varName v state) bodyTm))"

  (* Allocated: evaluate the operand, then inspect the value guided by the
     annotated operand type (with any current-frame tyvars resolved via
     IS_TyArgs, as for Default). *)
| "interp_term d (Suc fuel) state (CoreTm_Allocated ty tm) =
    (case interp_term d fuel state tm of
      Inl err \<Rightarrow> Inl err
    | Inr v \<Rightarrow>
        (case is_allocated (IS_DataCtors state) v (apply_subst (IS_TyArgs state) ty) of
          Inl err \<Rightarrow> Inl err
        | Inr b \<Rightarrow> Inr (CV_Bool b)))"

  (* Old: the identity (Core has no postconditions yet) *)
| "interp_term d (Suc fuel) state (CoreTm_Old tm) = interp_term d fuel state tm"

  (* Default value: resolve any current-frame tyvars via IS_TyArgs, then
     delegate to the recursive default_value helper. *)
| "interp_term _ (Suc fuel) state (CoreTm_Default ty) =
    default_value fuel state (apply_subst (IS_TyArgs state) ty)"

  (* Evaluate a writable lvalue into (addr, path).
     Returns TypeError if the base variable is read-only (in IS_ConstLocals).
     Note: this doesn't check for "bad paths" (e.g. incorrect field name); that happens
     later when the path is used. It does, however, check whether the base variable name
     exists and whether any array indices can be successfully evaluated. *)
| "interp_writable_lvalue _ 0 _ _ = Inl InsufficientFuel"
| "interp_writable_lvalue d (Suc fuel) state tm =
    (case tm of
      CoreTm_Var varName \<Rightarrow>
        if varName |\<in>| IS_ConstLocals state then Inl TypeError  \<comment> \<open>read-only variable\<close>
        else
        (case fmlookup (IS_Locals state) varName of
          Some addr \<Rightarrow> Inr (addr, [])
        | None \<Rightarrow>
            (case fmlookup (IS_Refs state) varName of
              Some (addr, path) \<Rightarrow> Inr (addr, path)
            | None \<Rightarrow> Inl TypeError))
    | CoreTm_RecordProj tm fldName \<Rightarrow>
        (case interp_writable_lvalue d fuel state tm of
          Inr (addr, path) \<Rightarrow> Inr (addr, path @ [LVPath_RecordProj fldName])
        | Inl err \<Rightarrow> Inl err)
    | CoreTm_VariantProj tm ctorName \<Rightarrow>
        (case interp_writable_lvalue d fuel state tm of
          Inr (addr, path) \<Rightarrow> Inr (addr, path @ [LVPath_VariantProj ctorName])
        | Inl err \<Rightarrow> Inl err)
    | CoreTm_ArrayProj tm indexTms \<Rightarrow>
        (case interp_writable_lvalue d fuel state tm of
          Inr (addr, path) \<Rightarrow>
            (case interp_term_list d fuel state indexTms of
              Inr indexVals \<Rightarrow>
                (case interpret_index_vals indexVals of
                  Inr indices \<Rightarrow> Inr (addr, path @ [LVPath_ArrayProj indices])
                | Inl err \<Rightarrow> Inl err)
            | Inl err \<Rightarrow> Inl err)
        | Inl err \<Rightarrow> Inl err)
    | CoreTm_Cast targetTy tm \<Rightarrow>
        \<comment> \<open>An array cast of an lvalue is an lvalue (a view of the same storage);
            record the cast as a path step. Casts to other types are not lvalues.\<close>
        (case targetTy of
          CoreTy_Array _ dims \<Rightarrow>
            (case interp_writable_lvalue d fuel state tm of
              Inr (addr, path) \<Rightarrow> Inr (addr, path @ [LVPath_ArrayCast dims])
            | Inl err \<Rightarrow> Inl err)
        | _ \<Rightarrow> Inl TypeError)
    | _ \<Rightarrow> Inl TypeError)"

  (* Interpret a list of terms *)
| "interp_term_list _ 0 _ _ = Inl InsufficientFuel"
| "interp_term_list _ (Suc _) _ [] = Inr []"
| "interp_term_list d (Suc fuel) state (tm # tms) =
    (case interp_term d fuel state tm of
      Inl err \<Rightarrow> Inl err
    | Inr val \<Rightarrow>
        (case interp_term_list d fuel state tms of
          Inl err \<Rightarrow> Inl err
        | Inr vals \<Rightarrow> Inr (val # vals)))"

  (* Interpret a statement *)
| "interp_statement _ 0 _ _ = Inl InsufficientFuel"

  (* Variable declaration *)
| "interp_statement d (Suc fuel) state (CoreStmt_VarDecl _ varName Var _ initialTm) =
    \<comment> \<open>The initializer is an ordinary (pure) term; impure-call initializers use
        CoreStmt_VarDeclCall. The state is unchanged by evaluating it. \<close>
    (case interp_term d fuel state initialTm of
       Inr initialVal \<Rightarrow> Inr (Continue (bind_mutable_local varName initialVal state))
     | Inl err \<Rightarrow> Inl err)"

| "interp_statement d (Suc fuel) state (CoreStmt_VarDeclCall _ varName _ castOpt fnName argTys argTms) =
    \<comment> \<open>Run the (possibly impure) call, observing its state effect, then apply the
        optional cast to the returned value before binding it.\<close>
    (case interp_function_call d fuel state fnName argTys argTms of
       Inr (newState, retVal) \<Rightarrow>
         (case apply_cast_opt castOpt retVal of
            Inr initialVal \<Rightarrow> Inr (Continue (bind_mutable_local varName initialVal newState))
          | Inl err \<Rightarrow> Inl err)
     | Inl err \<Rightarrow> Inl err)"
| "interp_statement d (Suc fuel) state (CoreStmt_VarDecl _ varName Ref _ lvalueTm) =
    (case lvalue_base_name lvalueTm of
      Some baseName \<Rightarrow>
        \<comment> \<open>Determine whether the base is read-only. The base is read-only iff:
           - it is in IS_ConstLocals (an explicit const local), or
           - it is not in IS_Locals \<union> IS_Refs at all, in which case it must be a
             global (which is implicitly read-only).
           Locals shadow globals, so we must check IS_Locals/IS_Refs first. \<close>
        if baseName |\<in>| IS_ConstLocals state
           \<or> (fmlookup (IS_Locals state) baseName = None
              \<and> fmlookup (IS_Refs state) baseName = None) then
          \<comment> \<open>Base variable is read-only: copy the value instead of aliasing.
             A compiler would likely use a read-only pointer, but copying is
             semantically equivalent since the source is immutable.\<close>
          (case interp_term d fuel state lvalueTm of
            Inl err \<Rightarrow> Inl err
          | Inr val \<Rightarrow> Inr (Continue (bind_const_local varName val state)))
        else
          \<comment> \<open>Base variable is writable: alias via writable lvalue. \<close>
          (case interp_writable_lvalue d fuel state lvalueTm of
            Inr addrAndPath \<Rightarrow> Inr (Continue (bind_ref varName addrAndPath state))
          | Inl err \<Rightarrow> Inl err)
    | None \<Rightarrow> Inl TypeError)"

  (* Assignment *)
| "interp_statement d (Suc fuel) state (CoreStmt_Assign _ lhsLvalue rhsTm) =
    \<comment> \<open>Resolve the lhs to an address and path; the rhs is an ordinary (pure)
        term (impure-call rhs's use CoreStmt_AssignCall). State is unchanged by
        evaluating it.\<close>
    (case interp_writable_lvalue d fuel state lhsLvalue of
      Inr (addr, path) \<Rightarrow>
        (case interp_term d fuel state rhsTm of
          Inr rhsVal \<Rightarrow>
            (let oldVal = IS_Store state ! addr in
            case update_value_at_path oldVal path rhsVal of
              Inr newVal \<Rightarrow>
                Inr (Continue (state \<lparr> IS_Store := (IS_Store state)[addr := newVal] \<rparr>))
            | Inl err \<Rightarrow> Inl err)
        | Inl err \<Rightarrow> Inl err)
    | Inl err \<Rightarrow> Inl err)"

  (* Assignment from an impure call *)
| "interp_statement d (Suc fuel) state (CoreStmt_AssignCall _ lhsLvalue castOpt fnName argTys argTms) =
    \<comment> \<open>Resolve the lhs first, then run the (possibly impure) call observing its
        state effect, apply the optional cast, and store the result.\<close>
    (case interp_writable_lvalue d fuel state lhsLvalue of
      Inr (addr, path) \<Rightarrow>
        (case interp_function_call d fuel state fnName argTys argTms of
          Inr (newState, retVal) \<Rightarrow>
            (case apply_cast_opt castOpt retVal of
              Inr rhsVal \<Rightarrow>
                (let oldVal = IS_Store newState ! addr in
                case update_value_at_path oldVal path rhsVal of
                  Inr newVal \<Rightarrow>
                    Inr (Continue (newState \<lparr> IS_Store := (IS_Store newState)[addr := newVal] \<rparr>))
                | Inl err \<Rightarrow> Inl err)
            | Inl err \<Rightarrow> Inl err)
        | Inl err \<Rightarrow> Inl err)
    | Inl err \<Rightarrow> Inl err)"

  (* Swap *)
| "interp_statement d (Suc fuel) state (CoreStmt_Swap _ lhsTm rhsTm) =
    (case interp_writable_lvalue d fuel state lhsTm of
      Inl err \<Rightarrow> Inl err
    | Inr lhsLvalue \<Rightarrow>
        (case interp_writable_lvalue d fuel state rhsTm of
          Inl err \<Rightarrow> Inl err
        | Inr rhsLvalue \<Rightarrow>
            (case perform_swap state lhsLvalue rhsLvalue of
              Inl err \<Rightarrow> Inl err
            | Inr newState \<Rightarrow> Inr (Continue newState))))"

  (* Return *)
| "interp_statement d (Suc fuel) state (CoreStmt_Return tm) =
    (case interp_term d fuel state tm of
      Inr val \<Rightarrow> Inr (Return state val)
    | Inl err \<Rightarrow> Inl err)"

  (* While. Each time the condition is about to be tested (including the last
     time, when it is false), the invariants are evaluated first, and it is a
     RuntimeError if one of them is false. The decreases-term is not
     evaluated. *)
| "interp_statement d (Suc fuel) state (CoreStmt_While whileGhost condTm invars decr bodyStmts) =
    (case interp_term_list d fuel state invars of
      Inl err \<Rightarrow> Inl err
    | Inr invarVals \<Rightarrow>
        (case invariants_error invarVals of
          Some err \<Rightarrow> Inl err
        | None \<Rightarrow>
            (case interp_term d fuel state condTm of
              Inr (CV_Bool True) \<Rightarrow>
                (case interp_statement_list d fuel state bodyStmts of
                  Inr (Continue state') \<Rightarrow>
                    interp_statement d fuel (restore_scope state state')
                                      (CoreStmt_While whileGhost condTm invars decr bodyStmts)
                | Inr (Return state' retVal) \<Rightarrow> Inr (Return (restore_scope state state') retVal)
                | Inl err \<Rightarrow> Inl err)
            | Inr (CV_Bool False) \<Rightarrow> Inr (Continue state)
            | Inr _ \<Rightarrow> Inl TypeError
            | Inl err \<Rightarrow> Inl err)))"

  (* Pattern match *)
| "interp_statement d (Suc fuel) state (CoreStmt_Match _ scrutTm arms) =
    (case interp_term d fuel state scrutTm of
      Inr scrutVal \<Rightarrow>
        (case find_matching_arm scrutVal arms of
          Inr armStmts \<Rightarrow>
            (case interp_statement_list d fuel state armStmts of
              Inr (Continue state') \<Rightarrow> Inr (Continue (restore_scope state state'))
            | Inr (Return state' retVal) \<Rightarrow> Inr (Return (restore_scope state state') retVal)
            | Inl err \<Rightarrow> Inl err)
        | Inl err \<Rightarrow> Inl err)
    | Inl err \<Rightarrow> Inl err)"

  (* Assert: the condition is evaluated, and it is a RuntimeError if it is
     false. The proof body is not run.
     "assert *" (no condition) only occurs inside a proof body, so it should
     never be executed. *)
| "interp_statement d (Suc fuel) state (CoreStmt_Assert (Some condTm) _) =
    (case interp_term d fuel state condTm of
      Inr (CV_Bool True) \<Rightarrow> Inr (Continue state)
    | Inr (CV_Bool False) \<Rightarrow> Inl RuntimeError  \<comment> \<open>assertion failed\<close>
    | Inr _ \<Rightarrow> Inl TypeError
    | Inl err \<Rightarrow> Inl err)"
| "interp_statement _ (Suc _) _ (CoreStmt_Assert None _) = Inl TypeError"

  (* Assume: a no-op; the condition is not evaluated. (To be revisited later.) *)
| "interp_statement _ (Suc _) state (CoreStmt_Assume _) = Inr (Continue state)"

  (* ShowHide: a no-op. *)
| "interp_statement _ (Suc _) state (CoreStmt_ShowHide _ _) = Inr (Continue state)"

  (* Obtain: brings a new variable into scope, bound to a value of its type
     that satisfies the condition. It is a RuntimeError if there is no such
     value. Like a Quantifier, this spends one unit of depth, and evaluates the
     condition at every value of the type, each at its own converged fuel. *)
| "interp_statement 0 (Suc _) _ (CoreStmt_Obtain _ _ _) = Inl InsufficientFuel"
| "interp_statement (Suc d) (Suc _) state (CoreStmt_Obtain varName varTy condTm) =
    (case choose_witness
            (values_of_type state (apply_subst (IS_TyArgs state) varTy))
            (\<lambda>v. converged (\<lambda>m. interp_term d m (bind_mutable_local varName v state) condTm)) of
      Inr witness \<Rightarrow> Inr (Continue (bind_mutable_local varName witness state))
    | Inl err \<Rightarrow> Inl err)"

  (* Fix, Use - only appear in proofs; should never be executed *)
| "interp_statement _ (Suc _) _ (CoreStmt_Fix _ _) = Inl TypeError"
| "interp_statement _ (Suc _) _ (CoreStmt_Use _) = Inl TypeError"

  (* Block: interpret a list of statements in a fresh scope. *)
| "interp_statement d (Suc fuel) state (CoreStmt_Block body) =
    (case interp_statement_list d fuel state body of
      Inr (Continue state') \<Rightarrow> Inr (Continue (restore_scope state state'))
    | Inr (Return state' retVal) \<Rightarrow> Inr (Return (restore_scope state state') retVal)
    | Inl err \<Rightarrow> Inl err)"

  (* Interpret a list of statements *)
| "interp_statement_list _ 0 _ _ = Inl InsufficientFuel"
| "interp_statement_list _ (Suc _) state [] = Inr (Continue state)"
| "interp_statement_list d (Suc fuel) state (stmt # stmts) =
    (case interp_statement d fuel state stmt of
      Inl err \<Rightarrow> Inl err
    | Inr (Continue state') \<Rightarrow> interp_statement_list d fuel state' stmts
    | Inr (Return state' retVal) \<Rightarrow> Inr (Return state' retVal))"

  (* Interpret a function call *)
| "interp_function_call _ 0 _ _ _ _ = Inl InsufficientFuel"
| "interp_function_call d (Suc fuel) state fnName argTys argTms =
    (case fmlookup (IS_Functions state) fnName of
      Some f \<Rightarrow>
        (if length argTms \<noteq> length (IF_Args f) then Inl TypeError  \<comment> \<open>wrong number of term args\<close>
        else if length argTys \<noteq> length (IF_TyArgs f) then Inl TypeError  \<comment> \<open>wrong number of type args\<close>
        else
            let refResults = map (interp_writable_lvalue d fuel state) argTms;
                valResults = map (interp_term d fuel state) argTms;
                argTuples = zip (IF_Args f) (zip refResults valResults);
                \<comment> \<open>Resolve each argTy against the caller's IS_TyArgs (which is
                    ground by the well-formedness invariant) before binding it.
                    This gives the callee a fully ground IS_TyArgs. \<close>
                calleeTyArgs = fmap_of_list
                  (zip (IF_TyArgs f)
                       (map (apply_subst (IS_TyArgs state)) argTys));
                clearedState = state \<lparr> IS_Locals := fmempty,
                                          IS_Refs := fmempty,
                                          IS_ConstLocals := {||},
                                          IS_TyArgs := calleeTyArgs \<rparr>
            in
              (case fold process_one_arg argTuples (Inr clearedState) of
                Inl err \<Rightarrow> Inl err
              | Inr preCallState \<Rightarrow>
                  (case IF_Body f of
                    Inl bodyStmts \<Rightarrow>
                      (case interp_statement_list d fuel preCallState bodyStmts of
                        Inr (Return postCallState retVal) \<Rightarrow>
                          Inr (restore_scope state postCallState, retVal)
                      | Inr (Continue _) \<Rightarrow>
                          Inl RuntimeError  \<comment> \<open>Reached end of function without return statement\<close>
                      | Inl err \<Rightarrow>
                          Inl err)
                  | Inr externFun \<Rightarrow>
                      (let vals = rights valResults;
                           refs = rights (map (\<lambda>((_, vr), refResult).
                                                  if vr = Ref then refResult else Inl TypeError)
                                              (zip (IF_Args f) refResults));
                           (newWorld, refUpdates, retVal) = externFun (IS_World state) vals;
                           state' = state \<lparr> IS_World := newWorld \<rparr>
                      in case apply_ref_updates state' refs refUpdates of
                        Inr finalState \<Rightarrow> Inr (finalState, retVal)
                      | Inl err \<Rightarrow> Inl err))))
    | None \<Rightarrow> Inl TypeError)"

  by pat_completeness auto

(* Termination: lexicographic order on (depth, fuel). Only the Quantifier and
   Obtain cases decrease the depth; every other recursive call keeps the depth
   and decreases the fuel. *)
termination by (relation "inv_image (less_than <*lex*> less_than) (\<lambda>x. case x of
    Inl (Inl (d, fuel, _)) \<Rightarrow> (d, fuel)
  | Inl (Inr (Inl (d, fuel, _))) \<Rightarrow> (d, fuel)
  | Inl (Inr (Inr (d, fuel, _))) \<Rightarrow> (d, fuel)
  | Inr (Inl (d, fuel, _)) \<Rightarrow> (d, fuel)
  | Inr (Inr (Inl (d, fuel, _))) \<Rightarrow> (d, fuel)
  | Inr (Inr (Inr (d, fuel, _))) \<Rightarrow> (d, fuel)
)", auto)

end

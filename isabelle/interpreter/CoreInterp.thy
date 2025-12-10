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

(* Check if a finite integer is zero *)
fun is_zero :: "CoreValue \<Rightarrow> bool" where
  "is_zero (CV_FiniteInt _ _ i) = (i = 0)"
| "is_zero _ = False"

(* Check if a finite integer is negative *)
fun is_negative :: "CoreValue \<Rightarrow> bool" where
  "is_negative (CV_FiniteInt _ _ i) = (i < 0)"
| "is_negative _ = False"

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
(* Checks types and overflow *)
fun generic_int_binop :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "generic_int_binop f (CV_FiniteInt s1 b1 i1) (CV_FiniteInt s2 b2 i2) =
    (if s1 = s2 \<and> b1 = b2 then
      let result = f i1 i2 in
      if int_fits s1 b1 result then Inr (CV_FiniteInt s1 b1 result)
      else Inl RuntimeError  \<comment> \<open>overflow\<close>
     else Inl TypeError)"   \<comment> \<open>mismatched signedness or number of bits\<close>
| "generic_int_binop _ _ _ = Inl TypeError"  \<comment> \<open>mismatched types\<close>

(* Evaluate a generic binop int * int \<rightarrow> bool *)
(* Checks types *)
fun generic_int_cmp_binop :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "generic_int_cmp_binop f (CV_FiniteInt s1 b1 i1) (CV_FiniteInt s2 b2 i2) =
    (if s1 = s2 \<and> b1 = b2 then Inr (CV_Bool (f i1 i2))
      else Inl TypeError)"  \<comment> \<open>mismatched signedness or number of bits\<close>
| "generic_int_cmp_binop _ _ _ = Inl TypeError"  \<comment> \<open>mismatched types\<close>

(* Evaluate a generic binop bool * bool \<rightarrow> bool *)
(* Checks types *)
fun generic_bool_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "generic_bool_binop f (CV_Bool b1) (CV_Bool b2) = Inr (CV_Bool (f b1 b2))"
| "generic_bool_binop _ _ _ = Inl TypeError"

(* Evaluate a binop *)
fun eval_binop :: "CoreBinop \<Rightarrow> CoreValue \<Rightarrow> CoreValue \<Rightarrow> InterpError + CoreValue" where
  "eval_binop CoreBinop_Add v1 v2 = generic_int_binop (\<lambda>x y. x + y) v1 v2"
| "eval_binop CoreBinop_Subtract v1 v2 = generic_int_binop (\<lambda>x y. x - y) v1 v2"
| "eval_binop CoreBinop_Multiply v1 v2 = generic_int_binop (\<lambda>x y. x * y) v1 v2"
| "eval_binop CoreBinop_Divide v1 v2 =
    (if is_zero v2 then Inl RuntimeError  \<comment> \<open>division by zero\<close>
    else generic_int_binop tdiv v1 v2)"
| "eval_binop CoreBinop_Modulo v1 v2 =
    (if is_zero v2 then Inl RuntimeError  \<comment> \<open>division by zero\<close>
    else generic_int_binop tmod v1 v2)"
| "eval_binop CoreBinop_BitAnd v1 v2 = generic_int_binop (\<lambda>x y. and x y) v1 v2"
| "eval_binop CoreBinop_BitOr v1 v2 = generic_int_binop (\<lambda>x y. or x y) v1 v2"
| "eval_binop CoreBinop_BitXor v1 v2 = generic_int_binop (\<lambda>x y. xor x y) v1 v2"
| "eval_binop CoreBinop_ShiftLeft v1 v2 =
    (if is_negative v2 then Inl RuntimeError  \<comment> \<open>negative shift amount\<close>
    else generic_int_binop (\<lambda>x y. push_bit (nat y) x) v1 v2)"
| "eval_binop CoreBinop_ShiftRight v1 v2 =
    (if is_negative v2 then Inl RuntimeError  \<comment> \<open>negative shift amount\<close>
    else generic_int_binop (\<lambda>x y. drop_bit (nat y) x) v1 v2)"
| "eval_binop CoreBinop_Equal v1 v2 =
    \<comment> \<open>Equality is supported for bools and finite ints only, for now\<close>
    (case (v1, v2) of
      (CV_Bool b1, CV_Bool b2) \<Rightarrow> Inr (CV_Bool (b1 = b2))
    | (CV_FiniteInt _ _ _, CV_FiniteInt _ _ _) \<Rightarrow> generic_int_cmp_binop (\<lambda>x y. x = y) v1 v2
    | _ \<Rightarrow> Inl TypeError)"
| "eval_binop CoreBinop_NotEqual v1 v2 =
    (case (v1, v2) of
      (CV_Bool b1, CV_Bool b2) \<Rightarrow> Inr (CV_Bool (b1 \<noteq> b2))
    | (CV_FiniteInt _ _ _, CV_FiniteInt _ _ _) \<Rightarrow> generic_int_cmp_binop (\<lambda>x y. x \<noteq> y) v1 v2
    | _ \<Rightarrow> Inl TypeError)"
| "eval_binop CoreBinop_Less v1 v2 = generic_int_cmp_binop (\<lambda>x y. x < y) v1 v2"
| "eval_binop CoreBinop_LessEqual v1 v2 = generic_int_cmp_binop (\<lambda>x y. x \<le> y) v1 v2"
| "eval_binop CoreBinop_Greater v1 v2 = generic_int_cmp_binop (\<lambda>x y. x > y) v1 v2"
| "eval_binop CoreBinop_GreaterEqual v1 v2 = generic_int_cmp_binop (\<lambda>x y. x \<ge> y) v1 v2"
| "eval_binop CoreBinop_And v1 v2 = generic_bool_binop (\<lambda>x y. x \<and> y) v1 v2"
| "eval_binop CoreBinop_Or v1 v2 = generic_bool_binop (\<lambda>x y. x \<or> y) v1 v2"
| "eval_binop CoreBinop_Implies v1 v2 = generic_bool_binop (\<lambda>x y. x \<longrightarrow> y) v1 v2"


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

fun pattern_matches :: "CoreValue \<Rightarrow> CorePattern \<Rightarrow> bool" where
  "pattern_matches (CV_Bool b1) (CorePat_Bool b2) = (b1 = b2)"
| "pattern_matches (CV_FiniteInt _ _ i1) (CorePat_Int i2) = (i1 = i2)"
| "pattern_matches (CV_Variant ctor1 _) (CorePat_Variant ctor2) = (ctor1 = ctor2)"
| "pattern_matches _ CorePat_Wildcard = True"
| "pattern_matches _ _ = False"

fun find_matching_arm :: "CoreValue \<Rightarrow> (CorePattern \<times> 'a) list \<Rightarrow> InterpError + 'a" where
  "find_matching_arm _ [] = Inl RuntimeError"  (* no match found *)
| "find_matching_arm val ((pat, rhs) # rest) =
    (if pattern_matches val pat then Inr rhs
    else find_matching_arm val rest)"


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
    (if ctorName = expectedCtor then Inr payload
    else Inl RuntimeError)"   (* variant projection from wrong ctor *)
| "get_value_at_path (CV_Array _ elementMap) (LVPath_ArrayProj indices # rest) =
    (case fmlookup elementMap indices of
      Some val \<Rightarrow> get_value_at_path val rest
    | None \<Rightarrow> Inl RuntimeError)"    (* array index out of bounds *)
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
| "update_value_at_path _ _ _ = Inl TypeError"  (* path didn't match the found value *)


(* ========================================================================== *)
(* Store and scope operations *)
(* ========================================================================== *)

(* Allocate a new address in the store and store the given value *)
fun alloc_store :: "'w InterpState \<Rightarrow> CoreValue \<Rightarrow> ('w InterpState \<times> nat)" where
  "alloc_store state val =
    (let addr = length (IS_Store state);
         new_store = IS_Store state @ [val]
    in (state \<lparr> IS_Store := new_store \<rparr>, addr))"

(* Restore scope after exiting a block:
   - old_state: the state before entering the scope
   - new_state: the state after executing the inner scope
   Returns: new_state with locals/refs restored and store truncated *)
fun restore_scope :: "'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState" where
  "restore_scope old_state new_state =
    new_state \<lparr> IS_Locals := IS_Locals old_state,
                IS_Refs := IS_Refs old_state,
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
            (case update_value_at_path (IS_Store state ! addr1) path1 val2 of
              Inl err \<Rightarrow> Inl err
            | Inr new_val1 \<Rightarrow>
                (case update_value_at_path (IS_Store state ! addr2) path2 val1 of
                  Inl err \<Rightarrow> Inl err
                | Inr new_val2 \<Rightarrow>
                    Inr (state \<lparr> IS_Store := (IS_Store state)[addr1 := new_val1, addr2 := new_val2] \<rparr>)))))"


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
    (let (state', addr) = alloc_store state val
    in Inr (state' \<lparr> IS_Locals := fmupd name addr (IS_Locals state') \<rparr>))"
| "process_one_arg ((name, Var), _, Inl err) _ = Inl err"
| "process_one_arg ((name, Ref), Inr (addr, path), Inr _) (Inr state) =
    Inr (state \<lparr> IS_Refs := fmupd name (addr, path) (IS_Refs state) \<rparr>)"
| "process_one_arg ((name, Ref), Inl err, _) _ = Inl err"
| "process_one_arg ((name, Ref), _, Inl err) _ = Inl err"

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
(* The main intepreter definitions *)
(* ========================================================================== *)

function interp_term :: "nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreTerm \<Rightarrow> InterpError + CoreValue"
  and interp_term_list :: "nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreTerm list \<Rightarrow> InterpError + CoreValue list"
  and interp_lvalue :: "nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreTerm \<Rightarrow> InterpError + nat \<times> LValuePath list"
  and interp_statement :: "nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreStatement \<Rightarrow> InterpError + 'w ExecResult"
  and interp_statement_list :: "nat \<Rightarrow> 'w InterpState \<Rightarrow> CoreStatement list \<Rightarrow> InterpError + 'w ExecResult"
  and interp_function_call :: "nat \<Rightarrow> 'w InterpState \<Rightarrow> string \<Rightarrow> CoreTerm list \<Rightarrow> InterpError + ('w InterpState \<times> CoreValue)"
where
  (* Interpret a term *)
  "interp_term 0 _ _ = Inl InsufficientFuel"

  (* Literals *)
| "interp_term (Suc _) _ (CoreTm_LitBool b) = Inr (CV_Bool b)"
| "interp_term (Suc _) _ (CoreTm_LitInt i) = 
    (case get_type_for_int i of
      Some (sign, bits) \<Rightarrow> Inr (CV_FiniteInt sign bits i)
    | None \<Rightarrow> Inl TypeError)"
| "interp_term (Suc fuel) state (CoreTm_LitArray tms) = 
    (case interp_term_list fuel state tms of
      Inl err \<Rightarrow> Inl err
    | Inr vals \<Rightarrow> Inr (make_1d_array vals))"

  (* Variable lookup (local var or global constant) *)
| "interp_term (Suc _) state (CoreTm_Var varName) =
    (case fmlookup (IS_Locals state) varName of
      Some addr \<Rightarrow> Inr (IS_Store state ! addr)
    | None \<Rightarrow>
      (case fmlookup (IS_Refs state) varName of
        Some (addr, path) \<Rightarrow> get_value_at_path (IS_Store state ! addr) path
      | None \<Rightarrow>
        (case fmlookup (IS_Constants state) varName of
          Some val \<Rightarrow> Inr val
        | None \<Rightarrow> Inl TypeError)))"  \<comment> \<open>name not in scope\<close>

  (* Cast *)
| "interp_term (Suc fuel) state (CoreTm_Cast targetTy tm) =
    (case interp_term fuel state tm of
      Inr (CV_FiniteInt _ _ i) \<Rightarrow>
        (case targetTy of
          CoreTy_FiniteInt sign bits \<Rightarrow>
            if int_fits sign bits i
            then Inr (CV_FiniteInt sign bits i)
            else Inl RuntimeError  \<comment> \<open>overflow\<close>
        | _ \<Rightarrow> Inl TypeError)  \<comment> \<open>cast to non-finite-integer type\<close>
    | Inr _ \<Rightarrow> Inl TypeError   \<comment> \<open>cast from non-finite-integer type\<close>
    | Inl err \<Rightarrow> Inl err)"

  (* Unary operator *)
| "interp_term (Suc fuel) state (CoreTm_Unop op tm) =
    (case interp_term fuel state tm of
      Inl err \<Rightarrow> Inl err
    | Inr val \<Rightarrow> eval_unop op val)"

  (* Binary operator *)
| "interp_term (Suc fuel) state (CoreTm_Binop op lhsTm rhsTm) =
    (case interp_term fuel state lhsTm of
      Inl err \<Rightarrow> Inl err
    | Inr lhsVal \<Rightarrow>
        (case interp_term fuel state rhsTm of
          Inl err \<Rightarrow> Inl err
        | Inr rhsVal \<Rightarrow> eval_binop op lhsVal rhsVal))"

  (* Let *)
| "interp_term (Suc fuel) state (CoreTm_Let varName rhsTm bodyTm) =
    (case interp_term fuel state rhsTm of
      Inl err \<Rightarrow> Inl err
    | Inr rhsVal \<Rightarrow>
        (let (state', addr) = alloc_store state rhsVal;
             state'' = state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state') \<rparr>
        in interp_term fuel state'' bodyTm))"

  (* Function call *)
| "interp_term (Suc fuel) state (CoreTm_FunctionCall fnName argTypes argTms) =
    (if is_pure_fun state fnName then
      (case interp_function_call fuel state fnName argTms of
        \<comment> \<open>Pure functions don't change the state, so we can ignore the new state here\<close>
        Inr (newState, retVal) \<Rightarrow> Inr retVal
      | Inl err \<Rightarrow> Inl err)
    else Inl TypeError)"  \<comment> \<open>attempt to call non-pure function in term context\<close>

  (* Variant construction *)
| "interp_term (Suc fuel) state (CoreTm_VariantCtor ctorName _ payloadTm) =
    (case interp_term fuel state payloadTm of
      Inl err \<Rightarrow> Inl err
    | Inr payloadValue \<Rightarrow> Inr (CV_Variant ctorName payloadValue))"

  (* Record construction *)
| "interp_term (Suc fuel) state (CoreTm_Record nameTermPairs) =
    (case interp_term_list fuel state (map snd nameTermPairs) of
      Inl err \<Rightarrow> Inl err
    | Inr vals \<Rightarrow> Inr (CV_Record (zip (map fst nameTermPairs) vals)))"

  (* Record projection *)
| "interp_term (Suc fuel) state (CoreTm_RecordProj tm fldName) =
    (case interp_term fuel state tm of
      Inr (CV_Record nameTmPairs) \<Rightarrow>
        (case map_of nameTmPairs fldName of
          Some val \<Rightarrow> Inr val
        | None \<Rightarrow> Inl TypeError)
    | Inr _ \<Rightarrow> Inl TypeError
    | Inl err \<Rightarrow> Inl err)"

  (* Variant projection (get payload; ctor name must match) *)
| "interp_term (Suc fuel) state (CoreTm_VariantProj tm expectedCtorName) =
    (case interp_term fuel state tm of
      Inr (CV_Variant actualCtorName payload) \<Rightarrow>
        (if actualCtorName = expectedCtorName then Inr payload
        else Inl RuntimeError)  \<comment> \<open>constructor name mismatch\<close>
    | Inl err \<Rightarrow> Inl err)"

  (* Array projection (indexing) *)
| "interp_term (Suc fuel) state (CoreTm_ArrayProj arrayTm idxTms) =
    (case interp_term fuel state arrayTm of
      Inr (CV_Array _ elementMap) \<Rightarrow>
        (case interp_term_list fuel state idxTms of
          Inr indexVals \<Rightarrow>
            (case interpret_index_vals indexVals of
              Inr indices \<Rightarrow>
                (case fmlookup elementMap indices of
                  Some result \<Rightarrow> Inr result
                | None \<Rightarrow> Inl RuntimeError)  \<comment> \<open>array index out of bounds\<close>
            | Inl err \<Rightarrow> Inl err)  \<comment> \<open>index terms not of type u64\<close>
        | Inl err \<Rightarrow> Inl err)  \<comment> \<open>error evaluating index terms\<close>
    | Inl err \<Rightarrow> Inl err)"  \<comment> \<open>error evaluating array term\<close>

  (* Pattern match *)
| "interp_term (Suc fuel) state (CoreTm_Match scrutTm arms) =
    (case interp_term fuel state scrutTm of
      Inr scrutVal \<Rightarrow>
        (case find_matching_arm scrutVal arms of
          Inr armTm \<Rightarrow> interp_term fuel state armTm
        | Inl err \<Rightarrow> Inl err)
    | Inl err \<Rightarrow> Inl err)"

  (* Sizeof *)
| "interp_term (Suc fuel) state (CoreTm_Sizeof tm) =
    (case interp_term fuel state tm of
      Inr (CV_Array sizes _) \<Rightarrow> Inr (array_size_to_value sizes)
    | Inr _ \<Rightarrow> Inl TypeError
    | Inl err \<Rightarrow> Inl err)"

  (* Quantifier, Allocated, Old - not allowed at runtime *)
| "interp_term (Suc _) state (CoreTm_Quantifier _ _ _ _) = Inl TypeError"
| "interp_term (Suc _) _ (CoreTm_Allocated _) = Inl TypeError"
| "interp_term (Suc _) _ (CoreTm_Old _) = Inl TypeError"

  (* Evaluate an lvalue into (addr, path) *)
  (* Note: this doesn't check for "bad paths" (e.g. incorrect field name); that happens
     later when the path is used. It does, however, check whether the base variable name
     exists and whether any array indices can be successfully evaluated. *)
| "interp_lvalue 0 _ _ = Inl InsufficientFuel"
| "interp_lvalue (Suc fuel) state tm =
    (case tm of
      CoreTm_Var varName \<Rightarrow>
        (case fmlookup (IS_Locals state) varName of
          Some addr \<Rightarrow> Inr (addr, [])
        | None \<Rightarrow>
            (case fmlookup (IS_Refs state) varName of
              Some (addr, path) \<Rightarrow> Inr (addr, path)
            | None \<Rightarrow> Inl TypeError))
    | CoreTm_RecordProj tm fldName \<Rightarrow>
        (case interp_lvalue fuel state tm of
          Inr (addr, path) \<Rightarrow> Inr (addr, path @ [LVPath_RecordProj fldName])
        | Inl err \<Rightarrow> Inl err)
    | CoreTm_VariantProj tm ctorName \<Rightarrow>
        (case interp_lvalue fuel state tm of
          Inr (addr, path) \<Rightarrow> Inr (addr, path @ [LVPath_VariantProj ctorName])
        | Inl err \<Rightarrow> Inl err)
    | CoreTm_ArrayProj tm indexTms \<Rightarrow>
        (case interp_lvalue fuel state tm of
          Inr (addr, path) \<Rightarrow> 
            (case interp_term_list fuel state indexTms of
              Inr indexVals \<Rightarrow>
                (case interpret_index_vals indexVals of
                  Inr indices \<Rightarrow> Inr (addr, path @ [LVPath_ArrayProj indices])
                | Inl err \<Rightarrow> Inl err)
            | Inl err \<Rightarrow> Inl err)
        | Inl err \<Rightarrow> Inl err)
    | _ \<Rightarrow> Inl TypeError)"

  (* Interpret a list of terms *)
| "interp_term_list 0 _ _ = Inl InsufficientFuel"
| "interp_term_list (Suc _) _ [] = Inr []"
| "interp_term_list (Suc fuel) state (tm # tms) =
    (case interp_term fuel state tm of
      Inl err \<Rightarrow> Inl err
    | Inr val \<Rightarrow>
        (case interp_term_list fuel state tms of
          Inl err \<Rightarrow> Inl err
        | Inr vals \<Rightarrow> Inr (val # vals)))"

  (* Interpret a statement *)
| "interp_statement 0 _ _ = Inl InsufficientFuel"

  (* Variable declaration *)
| "interp_statement (Suc _) state (CoreStmt_VarDecl Ghost _ _ _ _) = Inr (Continue state)"
| "interp_statement (Suc fuel) state (CoreStmt_VarDecl NotGhost varName Var _ initialTm) =
    (case interp_term fuel state initialTm of
      Inl err \<Rightarrow> Inl err
    | Inr initialVal \<Rightarrow>
        (let (state', addr) = alloc_store state initialVal
        in Inr (Continue (state' \<lparr> IS_Locals := fmupd varName addr (IS_Locals state') \<rparr>))))"
| "interp_statement (Suc fuel) state (CoreStmt_VarDecl NotGhost varName Ref _ lvalueTm) =
    (case interp_lvalue fuel state lvalueTm of
      Inl err \<Rightarrow> Inl err
    | Inr addrAndPath \<Rightarrow> 
        Inr (Continue (state \<lparr> IS_Refs := fmupd varName addrAndPath (IS_Refs state) \<rparr> )))"

  (* Assignment *)
| "interp_statement (Suc _) state (CoreStmt_Assign Ghost _ _) = Inr (Continue state)"
| "interp_statement (Suc fuel) state (CoreStmt_Assign NotGhost lhsLvalue rhsTm) =
    \<comment> \<open>Resolve the lhs to an address and path\<close>
    (case interp_lvalue fuel state lhsLvalue of
      Inr (addr, path) \<Rightarrow>
        \<comment> \<open>Compute new state (after any function call) and rhs value\<close>
        (case
          (case rhsTm of
            CoreTm_FunctionCall fnName _ argTms \<Rightarrow>
              interp_function_call fuel state fnName argTms
          | _ \<Rightarrow>
              (case interp_term fuel state rhsTm of
                Inr rhsVal \<Rightarrow> Inr (state, rhsVal)
              | Inl err \<Rightarrow> Inl err))
        of
          Inr (newState, rhsVal) \<Rightarrow>
            \<comment> \<open>Perform the assignment\<close>
            (let oldVal = IS_Store newState ! addr in
            case update_value_at_path oldVal path rhsVal of
              Inr newVal \<Rightarrow> 
                Inr (Continue (newState \<lparr> IS_Store := (IS_Store newState)[addr := newVal] \<rparr>))
            | Inl err \<Rightarrow> Inl err)
        | Inl err \<Rightarrow> Inl err)
    | Inl err \<Rightarrow> Inl err)"

  (* Swap *)
| "interp_statement (Suc _) state (CoreStmt_Swap Ghost _ _) = Inr (Continue state)"
| "interp_statement (Suc fuel) state (CoreStmt_Swap NotGhost lhsTm rhsTm) =
    (case interp_lvalue fuel state lhsTm of
      Inl err \<Rightarrow> Inl err
    | Inr lhsLvalue \<Rightarrow>
        (case interp_lvalue fuel state rhsTm of
          Inl err \<Rightarrow> Inl err
        | Inr rhsLvalue \<Rightarrow> 
            (case perform_swap state lhsLvalue rhsLvalue of
              Inl err \<Rightarrow> Inl err
            | Inr newState \<Rightarrow> Inr (Continue newState))))"

  (* Return *)
| "interp_statement (Suc fuel) state (CoreStmt_Return tm) = 
    (case interp_term fuel state tm of
      Inr val \<Rightarrow> Inr (Return state val)
    | Inl err \<Rightarrow> Inl err)"

  (* While *)
| "interp_statement (Suc _) state (CoreStmt_While Ghost _ _ _ _) = Inr (Continue state)"
| "interp_statement (Suc fuel) state (CoreStmt_While NotGhost condTm invars decr bodyStmts) =
    (case interp_term fuel state condTm of
      Inr (CV_Bool True) \<Rightarrow>
        (case interp_statement_list fuel state bodyStmts of
          Inr (Continue state') \<Rightarrow>
            interp_statement fuel (restore_scope state state')
                             (CoreStmt_While NotGhost condTm invars decr bodyStmts)
        | Inr (Return state' retVal) \<Rightarrow> Inr (Return (restore_scope state state') retVal)
        | Inl err \<Rightarrow> Inl err)
    | Inr (CV_Bool False) \<Rightarrow> Inr (Continue state)
    | Inr _ \<Rightarrow> Inl TypeError
    | Inl err \<Rightarrow> Inl err)"

  (* Pattern match *)
| "interp_statement (Suc _) state (CoreStmt_Match Ghost _ _) = Inr (Continue state)"
| "interp_statement (Suc fuel) state (CoreStmt_Match NotGhost scrutTm arms) =
    (case interp_term fuel state scrutTm of
      Inr scrutVal \<Rightarrow>
        (case find_matching_arm scrutVal arms of
          Inr armStmts \<Rightarrow>
            (case interp_statement_list fuel state armStmts of
              Inr (Continue state') \<Rightarrow> Inr (Continue (restore_scope state state'))
            | Inr (Return state' retVal) \<Rightarrow> Inr (Return (restore_scope state state') retVal)
            | Inl err \<Rightarrow> Inl err)
        | Inl err \<Rightarrow> Inl err)
    | Inl err \<Rightarrow> Inl err)"

  (* Assert, Assume, ShowHide - ignored at runtime *)
| "interp_statement (Suc fuel) state (CoreStmt_Assert _ _) = Inr (Continue state)"
| "interp_statement (Suc fuel) state (CoreStmt_Assume _) = Inr (Continue state)"
| "interp_statement (Suc fuel) state (CoreStmt_ShowHide _ _) = Inr (Continue state)"

  (* Fix, Obtain, Use - not allowed at runtime *)
| "interp_statement (Suc fuel) _ (CoreStmt_Fix _ _) = Inl TypeError"
| "interp_statement (Suc fuel) _ (CoreStmt_Obtain _ _ _) = Inl TypeError"
| "interp_statement (Suc fuel) _ (CoreStmt_Use _) = Inl TypeError"

  (* Interpret a list of statements *)
| "interp_statement_list 0 _ _ = Inl InsufficientFuel"
| "interp_statement_list (Suc _) state [] = Inr (Continue state)"
| "interp_statement_list (Suc fuel) state (stmt # stmts) =
    (case interp_statement fuel state stmt of
      Inl err \<Rightarrow> Inl err
    | Inr (Continue state') \<Rightarrow> interp_statement_list fuel state' stmts
    | Inr (Return state' retVal) \<Rightarrow> Inr (Return state' retVal))"

  (* Interpret a function call *)
| "interp_function_call 0 _ _ _ = Inl InsufficientFuel"
| "interp_function_call (Suc fuel) state fnName argTms =
    (case fmlookup (IS_Functions state) fnName of
      Some f \<Rightarrow>
        (if length argTms \<noteq> length (IF_Args f) then Inl TypeError  \<comment> \<open>wrong number of args\<close>
        else 
            let refResults = map (interp_lvalue fuel state) argTms;
                valResults = map (interp_term fuel state) argTms;
                argTuples = zip (IF_Args f) (zip refResults valResults);
                clearedState = state \<lparr> IS_Locals := fmempty, IS_Refs := fmempty \<rparr>
            in
              (case fold process_one_arg argTuples (Inr clearedState) of
                Inl err \<Rightarrow> Inl err
              | Inr preCallState \<Rightarrow>
                  (case IF_Body f of
                    Inl bodyStmts \<Rightarrow>
                      (case interp_statement_list fuel preCallState bodyStmts of
                        Inr (Return postCallState retVal) \<Rightarrow> 
                          Inr (restore_scope state postCallState, retVal)
                      | Inr (Continue _) \<Rightarrow>
                          Inl TypeError  \<comment> \<open>Reached end of function without return statement\<close>
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

termination by (relation "measure (\<lambda>x. case x of
    Inl (Inl (fuel, _, _)) \<Rightarrow> fuel
  | Inl (Inr (Inl (fuel, _, _))) \<Rightarrow> fuel
  | Inl (Inr (Inr (fuel, _, _))) \<Rightarrow> fuel
  | Inr (Inl (fuel, _, _)) \<Rightarrow> fuel
  | Inr (Inr (Inl (fuel, _, _))) \<Rightarrow> fuel
  | Inr (Inr (Inr (fuel, _, _))) \<Rightarrow> fuel
)", auto)

end

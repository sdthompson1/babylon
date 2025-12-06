theory BabInterp
  imports "../base/BabSyntax" "../base/IntRange" "HOL.Bit_Operations" "HOL-Library.List_Lexorder"
begin

(* ========================================================================== *)
(* Types used in the interpreter *)
(* ========================================================================== *)

(* Evaluated values *)
datatype BabValue =
  BV_Bool bool
  | BV_FiniteInt Signedness IntBits int
  | BV_MathInt int
  | BV_Tuple "BabValue list"
  | BV_Record "(string \<times> BabValue) list"
  | BV_Variant string "BabValue option"   (* constructor name, optional payload *)
  | BV_Array "int list" "(int list, BabValue) fmap"  (* size list, map array index \<rightarrow> value *)
  | BV_Abstract nat  (* extern or abstract type, with arbitrary "token" *)

(* LValue paths for assignments, swaps and references *)
datatype LValuePath =
  LVPath_TupleProj nat
  | LVPath_RecordProj string
  | LVPath_ArrayProj "int list"
  | LVPath_VariantProj string

(* Interpreter state *)
record 'world BabState =
  BS_Functions :: "(string, DeclFun) fmap"
  BS_ExternFunctions :: "(string, 'world \<Rightarrow> BabType list \<Rightarrow> BabValue list \<Rightarrow> 'world \<times> BabValue list \<times> BabValue option) fmap"
  BS_Constants :: "(string, BabValue) fmap"  (* global constants *)
  BS_NullaryCtors :: "string fset"  (* names of nullary data constructors *)
  BS_UnaryCtors :: "string fset"  (* names of unary data constructors *)
  BS_World :: 'world
  BS_Store :: "BabValue list"  (* address \<rightarrow> value *)
  BS_Locals :: "(string, nat) fmap"  (* variable name \<rightarrow> address *)
  BS_RefVars :: "(string, nat \<times> LValuePath list) fmap"  (* ref name \<rightarrow> (address, path) *)

(* Result of interpreting a term *)
datatype 'a BabInterpResult =
  BIR_Success 'a
  | BIR_TypeError
  | BIR_RuntimeError
  | BIR_InsufficientFuel

(* Result of executing a statement *)
datatype 'w BabExecResult =
  BER_Continue "'w BabState"
  | BER_Return "'w BabState" "BabValue option"
  | BER_TypeError
  | BER_RuntimeError
  | BER_InsufficientFuel


(* ========================================================================== *)
(* Size lemmas for BabValue *)
(* ========================================================================== *)

(* We use the auto-generated size function for BabValue.
   For arrays, size (BV_Array dims vals) includes the sizes of all values in the fmap. *)

(* Values in an fmap are smaller than the array containing them *)
lemma size_fmap_lookup:
  assumes "fmlookup vals idx = Some v"
  shows "size v < size (BV_Array dims vals)"
proof -
  from assms have mem: "(idx, v) |\<in>| fset_of_fmap vals"
    by transfer auto
  hence mem': "(idx, v) \<in> fset (fset_of_fmap vals)"
    by simp
  let ?f = "\<lambda>x. Suc (case x of (a, x) \<Rightarrow> size x)"
  have "?f (idx, v) \<le> (\<Sum>x\<in>fset (fset_of_fmap vals). ?f x)"
    by (rule member_le_sum[OF mem']) auto
  hence "Suc (size v) \<le> (\<Sum>x\<in>fset (fset_of_fmap vals). Suc (case x of (a, x) \<Rightarrow> size x))"
    by simp
  thus ?thesis
    by simp
qed


(* ========================================================================== *)
(* General helper functions *)
(* ========================================================================== *)

(* Helper functions to convert errors.
   Note: convert_error is only intended to be called on error results, but we define
   the BIR_Success case to return BIR_Success undefined to make the function total
   and preserve the success/failure distinction for reasoning. *)
fun convert_error :: "'a BabInterpResult \<Rightarrow> 'b BabInterpResult" where
  "convert_error (BIR_Success _) = BIR_Success undefined"
| "convert_error BIR_TypeError = BIR_TypeError"
| "convert_error BIR_RuntimeError = BIR_RuntimeError"
| "convert_error BIR_InsufficientFuel = BIR_InsufficientFuel"

fun convert_exec_error :: "'a BabInterpResult \<Rightarrow> 'w BabExecResult" where
  "convert_exec_error (BIR_Success _) = undefined"
| "convert_exec_error BIR_TypeError = BER_TypeError"
| "convert_exec_error BIR_RuntimeError = BER_RuntimeError"
| "convert_exec_error BIR_InsufficientFuel = BER_InsufficientFuel"

(* Truncated division - rounds towards zero, like C/Java/JavaScript *)
fun tdiv :: "int \<Rightarrow> int \<Rightarrow> int" where
  "tdiv i1 i2 = sgn i1 * sgn i2 * (abs i1 div abs i2)"

(* Truncated modulo - remainder has sign of dividend, like C/Java/JavaScript *)
fun tmod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "tmod i1 i2 = sgn i1 * (abs i1 mod abs i2)"

(* Check if an integer fits in a finite integer type *)
fun int_fits :: "Signedness \<Rightarrow> IntBits \<Rightarrow> int \<Rightarrow> bool" where
  "int_fits sign bits i = (let (min_val, max_val) = int_range sign bits in min_val \<le> i \<and> i \<le> max_val)"

(* Bitwise complement for finite integers *)
fun int_complement :: "Signedness \<Rightarrow> IntBits \<Rightarrow> int \<Rightarrow> int" where
  "int_complement sign bits i =
    (let (min_val, max_val) = int_range sign bits in
     case sign of
       Signed \<Rightarrow> -i - 1
     | Unsigned \<Rightarrow> max_val - i)"

(* Try to find the first type (i32, u32, i64, u64) that fits the literal *)
fun infer_literal_type :: "int \<Rightarrow> (Signedness \<times> IntBits) option" where
  "infer_literal_type i =
    (if int_fits Signed IntBits_32 i then Some (Signed, IntBits_32)
     else if int_fits Unsigned IntBits_32 i then Some (Unsigned, IntBits_32)
     else if int_fits Signed IntBits_64 i then Some (Signed, IntBits_64)
     else if int_fits Unsigned IntBits_64 i then Some (Unsigned, IntBits_64)
     else None)"

(* Generic binary operation on finite integers with overflow checking *)
(* Requires both values to be BV_FiniteInt with same signedness and bit width *)
fun eval_finite_int_binop :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> BabValue \<Rightarrow> BabValue \<Rightarrow> BabValue BabInterpResult" where
  "eval_finite_int_binop op (BV_FiniteInt s1 b1 i1) (BV_FiniteInt s2 b2 i2) =
    (if s1 = s2 \<and> b1 = b2 then
      let result = op i1 i2 in
      if int_fits s1 b1 result then BIR_Success (BV_FiniteInt s1 b1 result)
      else BIR_RuntimeError
     else BIR_TypeError)"
| "eval_finite_int_binop _ _ _ = BIR_TypeError"

(* Generic binary comparison on finite integers *)
(* Requires both values to be BV_FiniteInt with same signedness and bit width *)
fun eval_finite_int_comparison :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow> BabValue \<Rightarrow> BabValue \<Rightarrow> BabValue BabInterpResult" where
  "eval_finite_int_comparison cmp (BV_FiniteInt s1 b1 i1) (BV_FiniteInt s2 b2 i2) =
    (if s1 = s2 \<and> b1 = b2 then BIR_Success (BV_Bool (cmp i1 i2))
     else BIR_TypeError)"
| "eval_finite_int_comparison _ _ _ = BIR_TypeError"

(* Make a one-dimensional BV_Array of values *)
fun make_array :: "BabValue list \<Rightarrow> BabValue" where
  "make_array vals = BV_Array [int (length vals)] (fmap_of_list (zip (map (\<lambda>i.[int i]) [0..<length vals]) vals))"

(* Generate all indices for a multi-dimensional array given sizes in each dimension *)
(* For example, [2, 3] generates [[0,0], [0,1], [0,2], [1,0], [1,1], [1,2]] *)
fun generate_array_indices :: "int list \<Rightarrow> (int list) list" where
  "generate_array_indices [] = [[]]"
| "generate_array_indices (d # ds) =
    concat (map (\<lambda>i. map (\<lambda>rest. int i # rest) (generate_array_indices ds)) [0..<nat d])"

(* Create an array with default values at all indices *)
fun make_default_array :: "BabValue \<Rightarrow> int list \<Rightarrow> BabValue" where
  "make_default_array defaultVal dimSizes =
    (let indices = generate_array_indices dimSizes in
     BV_Array dimSizes (fmap_of_list (zip indices (replicate (length indices) defaultVal))))"

(* Convert array size to BabValue: for 1-d arrays return BV_FiniteInt u64, for 2-d+ return BV_Tuple *)
fun array_size_to_value :: "int list \<Rightarrow> BabValue" where
  "array_size_to_value ns = (if length ns = 1
    then BV_FiniteInt Unsigned IntBits_64 (hd ns)
    else BV_Tuple (map (BV_FiniteInt Unsigned IntBits_64) ns))"

(* Convert a list of BV_FiniteInt u64 values to a list of ints, or return a type error *)
fun interpret_index_vals :: "BabValue list \<Rightarrow> (int list) BabInterpResult" where
  "interpret_index_vals [] = BIR_Success []"
| "interpret_index_vals (BV_FiniteInt Unsigned IntBits_64 i # rest) =
    (case interpret_index_vals rest of
      BIR_Success results \<Rightarrow> BIR_Success (i # results)
    | err \<Rightarrow> err)"
| "interpret_index_vals (_ # rest) = BIR_TypeError"

(* Update record fields: replace existing fields with updates, keep others *)
(* Returns None if any update field doesn't exist in base *)
fun update_record_fields :: "(string \<times> BabValue) list \<Rightarrow> (string \<times> BabValue) list \<Rightarrow> (string \<times> BabValue) list option" where
  "update_record_fields baseFields [] = Some baseFields"
| "update_record_fields baseFields ((name, val) # updates) =
    (if map_of baseFields name = None then None
     else update_record_fields (AList.update name val baseFields) updates)"

(* Allocate a new address in the store and store the given value *)
fun alloc_store :: "'w BabState \<Rightarrow> BabValue \<Rightarrow> ('w BabState \<times> nat)" where
  "alloc_store state val =
    (let addr = length (BS_Store state);
         new_store = BS_Store state @ [val]
     in (state \<lparr> BS_Store := new_store \<rparr>, addr))"

(* Get value at a path within a value *)
fun get_value_at_path :: "BabValue \<Rightarrow> LValuePath list \<Rightarrow> BabValue BabInterpResult" where
  "get_value_at_path val [] = BIR_Success val"
| "get_value_at_path (BV_Tuple vals) (LVPath_TupleProj idx # rest) =
    (if idx < length vals then get_value_at_path (vals ! idx) rest
     else BIR_TypeError)"
| "get_value_at_path (BV_Record flds) (LVPath_RecordProj field # rest) =
    (case map_of flds field of
      Some val \<Rightarrow> get_value_at_path val rest
    | None \<Rightarrow> BIR_TypeError)"
| "get_value_at_path (BV_Array _ fmap) (LVPath_ArrayProj indices # rest) =
    (case fmlookup fmap indices of
      Some val \<Rightarrow> get_value_at_path val rest
    | None \<Rightarrow> BIR_RuntimeError)"
| "get_value_at_path (BV_Variant ctor_name (Some val)) (LVPath_VariantProj expected_ctor # rest) =
    (if ctor_name = expected_ctor then get_value_at_path val rest
     else BIR_RuntimeError)"
| "get_value_at_path (BV_Variant _ None) (LVPath_VariantProj _ # rest) = BIR_RuntimeError"
| "get_value_at_path _ _ = BIR_TypeError"

(* Update value at a path within a value *)
fun update_value_at_path :: "BabValue \<Rightarrow> LValuePath list \<Rightarrow> BabValue \<Rightarrow> BabValue BabInterpResult" where
  "update_value_at_path _ [] new_val = BIR_Success new_val"
| "update_value_at_path (BV_Tuple vals) (LVPath_TupleProj idx # rest) new_val =
    (if idx < length vals then
      (case update_value_at_path (vals ! idx) rest new_val of
        BIR_Success updated_elem \<Rightarrow> BIR_Success (BV_Tuple (vals[idx := updated_elem]))
      | err \<Rightarrow> err)
     else BIR_TypeError)"
| "update_value_at_path (BV_Record flds) (LVPath_RecordProj field # rest) new_val =
    (case map_of flds field of
      Some old_val \<Rightarrow>
        (case update_value_at_path old_val rest new_val of
          BIR_Success updated_val \<Rightarrow> BIR_Success (BV_Record (AList.update field updated_val flds))
        | err \<Rightarrow> err)
    | None \<Rightarrow> BIR_TypeError)"
| "update_value_at_path (BV_Array dims fmap) (LVPath_ArrayProj indices # rest) new_val =
    (case fmlookup fmap indices of
      Some old_val \<Rightarrow>
        (case update_value_at_path old_val rest new_val of
          BIR_Success updated_val \<Rightarrow> BIR_Success (BV_Array dims (fmupd indices updated_val fmap))
        | err \<Rightarrow> err)
    | None \<Rightarrow> BIR_RuntimeError)"
| "update_value_at_path (BV_Variant ctor_name (Some old_val)) (LVPath_VariantProj expected_ctor # rest) new_val =
    (if ctor_name = expected_ctor then
      (case update_value_at_path old_val rest new_val of
        BIR_Success updated_val \<Rightarrow> BIR_Success (BV_Variant ctor_name (Some updated_val))
      | err \<Rightarrow> err)
     else BIR_RuntimeError)"
| "update_value_at_path (BV_Variant _ None) (LVPath_VariantProj _ # rest) _ = BIR_RuntimeError"
| "update_value_at_path _ _ _ = BIR_TypeError"

(* Restore scope after exiting a block:
   - old_state: the state before entering the scope
   - new_state: the state after executing the inner scope
   Returns: new_state with locals/refs restored and store truncated *)
fun restore_scope :: "'w BabState \<Rightarrow> 'w BabState \<Rightarrow> 'w BabState" where
  "restore_scope old_state new_state =
    new_state \<lparr> BS_Locals := BS_Locals old_state,
                BS_RefVars := BS_RefVars old_state,
                BS_Store := take (length (BS_Store old_state)) (BS_Store new_state) \<rparr>"

(* Check if a term is a pure function (has no ref parameters, and not marked "impure") *)
fun is_pure_fun_term :: "'w BabState \<Rightarrow> BabTerm \<Rightarrow> bool" where
  "is_pure_fun_term state (BabTm_Name _ fnName _) =
    (case fmlookup (BS_Functions state) fnName of
      Some funDecl \<Rightarrow> (\<not> list_ex (\<lambda>(_, vr, _). vr = Ref) (DF_TmArgs funDecl)) \<and> (\<not> DF_Impure funDecl)
    | None \<Rightarrow> False)"
| "is_pure_fun_term _ _ = False"

(* Helper function to process a single function argument and update the state *)
(* Takes: (parameter info, lvalue result, rvalue result) and current state result *)
(* Returns: updated state, or error *)
fun process_one_arg :: "((string \<times> VarOrRef \<times> BabType)
                        \<times> (nat \<times> LValuePath list) BabInterpResult
                        \<times> BabValue BabInterpResult)
                \<Rightarrow> 'w BabState BabInterpResult
                \<Rightarrow> 'w BabState BabInterpResult" where
  "process_one_arg _ BIR_TypeError = BIR_TypeError"
| "process_one_arg _ BIR_RuntimeError = BIR_RuntimeError"
| "process_one_arg _ BIR_InsufficientFuel = BIR_InsufficientFuel"
| "process_one_arg ((name, Var, _), _, BIR_Success val) (BIR_Success state) =
    (let (state', addr) = alloc_store state val
     in BIR_Success (state' \<lparr> BS_Locals := fmupd name addr (BS_Locals state') \<rparr>))"
| "process_one_arg ((name, Var, _), _, valErr) _ = convert_error valErr"
| "process_one_arg ((name, Ref, _), BIR_Success (addr, path), _) (BIR_Success state) =
    BIR_Success (state \<lparr> BS_RefVars := fmupd name (addr, path) (BS_RefVars state) \<rparr>)"
| "process_one_arg ((name, Ref, _), refErr, _) _ = convert_error refErr"

(* Apply extern function ref updates back to the store *)
(* Takes list of ref lvalues and corresponding new values, returns updated state *)
fun apply_ref_updates :: "'w BabState \<Rightarrow> (nat \<times> LValuePath list) list \<Rightarrow> BabValue list 
                            \<Rightarrow> 'w BabState BabInterpResult" where
  "apply_ref_updates state [] [] = BIR_Success state"
| "apply_ref_updates state ((addr, path) # rest_lvals) (newVal # rest_vals) =
    (case update_value_at_path (BS_Store state ! addr) path newVal of
      BIR_Success updated_val \<Rightarrow>
        (let state' = state \<lparr> BS_Store := (BS_Store state)[addr := updated_val] \<rparr>
         in apply_ref_updates state' rest_lvals rest_vals)
    | err \<Rightarrow> convert_error err)"
| "apply_ref_updates _ _ _ = BIR_TypeError"  (* mismatched list lengths *)

(* Call an extern function and convert result to BabExecResult *)
(* Precondition: all valResults and refResults are BIR_Success (ensured by fold process_one_arg) *)
fun call_extern_function :: "'w BabState \<Rightarrow> string \<Rightarrow> BabType list \<Rightarrow> (string \<times> VarOrRef \<times> BabType) list
                             \<Rightarrow> (nat \<times> LValuePath list) BabInterpResult list
                             \<Rightarrow> BabValue BabInterpResult list \<Rightarrow> 'w BabExecResult" where
  "call_extern_function state fnName tyArgs params refResults valResults =
    (case fmlookup (BS_ExternFunctions state) fnName of
      Some externFn \<Rightarrow>
        (let argVals = map (\<lambda>r. case r of BIR_Success v \<Rightarrow> v) valResults;
             (newWorld, refUpdates, retVal) = externFn (BS_World state) tyArgs argVals;
             refLvals = map (\<lambda>(_, r). case r of BIR_Success lv \<Rightarrow> lv)
                            (filter (\<lambda>((_, vr, _), _). vr = Ref) (zip params refResults));
             state' = state \<lparr> BS_World := newWorld \<rparr>
         in
           case apply_ref_updates state' refLvals refUpdates of
             BIR_Success finalState \<Rightarrow>
               (case retVal of
                 Some val \<Rightarrow> BER_Return finalState (Some val)
               | None \<Rightarrow> BER_Continue finalState)
           | err \<Rightarrow> convert_exec_error err)
    | None \<Rightarrow> BER_TypeError)"

(* Helper to check if second operand is zero for division/modulo *)
fun is_zero :: "BabValue \<Rightarrow> bool" where
  "is_zero (BV_FiniteInt _ _ i) = (i = 0)"
| "is_zero _ = False"

(* Helper to check if shift amount is negative *)
fun is_negative :: "BabValue \<Rightarrow> bool" where
  "is_negative (BV_FiniteInt _ _ i) = (i < 0)"
| "is_negative _ = False"

(* Evaluate a single binary operation on two values *)
fun eval_binop :: "BabBinop \<Rightarrow> BabValue \<Rightarrow> BabValue \<Rightarrow> BabValue BabInterpResult" where
  "eval_binop op v1 v2 = (case op of
      BabBinop_Add \<Rightarrow> eval_finite_int_binop (\<lambda>x y. x + y) v1 v2
    | BabBinop_Subtract \<Rightarrow> eval_finite_int_binop (\<lambda>x y. x - y) v1 v2
    | BabBinop_Multiply \<Rightarrow> eval_finite_int_binop (\<lambda>x y. x * y) v1 v2
    | BabBinop_Divide \<Rightarrow>
        if is_zero v2 then BIR_RuntimeError else eval_finite_int_binop tdiv v1 v2
    | BabBinop_Modulo \<Rightarrow>
        if is_zero v2 then BIR_RuntimeError else eval_finite_int_binop tmod v1 v2

    | BabBinop_BitAnd \<Rightarrow> eval_finite_int_binop (\<lambda>x y. and x y) v1 v2
    | BabBinop_BitOr \<Rightarrow> eval_finite_int_binop (\<lambda>x y. or x y) v1 v2
    | BabBinop_BitXor \<Rightarrow> eval_finite_int_binop (\<lambda>x y. xor x y) v1 v2
    | BabBinop_ShiftLeft \<Rightarrow>
        if is_negative v2 then BIR_RuntimeError
        else eval_finite_int_binop (\<lambda>x y. push_bit (nat y) x) v1 v2
    | BabBinop_ShiftRight \<Rightarrow>
        if is_negative v2 then BIR_RuntimeError
        else eval_finite_int_binop (\<lambda>x y. drop_bit (nat y) x) v1 v2

    | BabBinop_Equal \<Rightarrow>
        (case (v1, v2) of
          (BV_Bool b1, BV_Bool b2) \<Rightarrow> BIR_Success (BV_Bool (b1 = b2))
        | (BV_FiniteInt _ _ _, BV_FiniteInt _ _ _) \<Rightarrow> eval_finite_int_comparison (\<lambda>x y. x = y) v1 v2
        | _ \<Rightarrow> BIR_TypeError)
    | BabBinop_NotEqual \<Rightarrow>
        (case (v1, v2) of
          (BV_Bool b1, BV_Bool b2) \<Rightarrow> BIR_Success (BV_Bool (b1 \<noteq> b2))
        | (BV_FiniteInt _ _ _, BV_FiniteInt _ _ _) \<Rightarrow> eval_finite_int_comparison (\<lambda>x y. x \<noteq> y) v1 v2
        | _ \<Rightarrow> BIR_TypeError)
    | BabBinop_Less \<Rightarrow> eval_finite_int_comparison (\<lambda>x y. x < y) v1 v2
    | BabBinop_LessEqual \<Rightarrow> eval_finite_int_comparison (\<lambda>x y. x \<le> y) v1 v2
    | BabBinop_Greater \<Rightarrow> eval_finite_int_comparison (\<lambda>x y. x > y) v1 v2
    | BabBinop_GreaterEqual \<Rightarrow> eval_finite_int_comparison (\<lambda>x y. x \<ge> y) v1 v2

    | BabBinop_And \<Rightarrow>
        (case (v1, v2) of (BV_Bool b1, BV_Bool b2) \<Rightarrow> BIR_Success (BV_Bool (b1 \<and> b2)) | _ \<Rightarrow> BIR_TypeError)
    | BabBinop_Or \<Rightarrow>
        (case (v1, v2) of (BV_Bool b1, BV_Bool b2) \<Rightarrow> BIR_Success (BV_Bool (b1 \<or> b2)) | _ \<Rightarrow> BIR_TypeError)
    | BabBinop_Implies \<Rightarrow>
        (case (v1, v2) of (BV_Bool b1, BV_Bool b2) \<Rightarrow> BIR_Success (BV_Bool (b1 \<longrightarrow> b2)) | _ \<Rightarrow> BIR_TypeError)
    | BabBinop_ImpliedBy \<Rightarrow>
        (case (v1, v2) of (BV_Bool b1, BV_Bool b2) \<Rightarrow> BIR_Success (BV_Bool (b2 \<longrightarrow> b1)) | _ \<Rightarrow> BIR_TypeError)
    | BabBinop_Iff \<Rightarrow>
        (case (v1, v2) of (BV_Bool b1, BV_Bool b2) \<Rightarrow> BIR_Success (BV_Bool (b1 = b2)) | _ \<Rightarrow> BIR_TypeError))"

(* Perform a swap operation: exchange values at two lvalue locations *)
fun exec_swap :: "'w BabState \<Rightarrow> (nat \<times> LValuePath list) \<Rightarrow> (nat \<times> LValuePath list) \<Rightarrow> 'w BabExecResult" where
  "exec_swap state (addr1, path1) (addr2, path2) =
    (case get_value_at_path (BS_Store state ! addr1) path1 of
      BIR_Success val1 \<Rightarrow>
        (case get_value_at_path (BS_Store state ! addr2) path2 of
          BIR_Success val2 \<Rightarrow>
            (case update_value_at_path (BS_Store state ! addr1) path1 val2 of
              BIR_Success new_val1 \<Rightarrow>
                (case update_value_at_path (BS_Store state ! addr2) path2 val1 of
                  BIR_Success new_val2 \<Rightarrow>
                    BER_Continue (state \<lparr> BS_Store := (BS_Store state)[addr1 := new_val1, addr2 := new_val2] \<rparr>)
                | err \<Rightarrow> convert_exec_error err)
            | err \<Rightarrow> convert_exec_error err)
        | err \<Rightarrow> convert_exec_error err)
    | err \<Rightarrow> convert_exec_error err)"

(* Helper: Prepend a path element to all Ref bindings *)
fun prepend_path_to_bindings :: "LValuePath \<Rightarrow> (string \<times> (BabValue + LValuePath list)) list \<Rightarrow> (string \<times> (BabValue + LValuePath list)) list" where
  "prepend_path_to_bindings path_elem bindings =
    map (\<lambda>(name, binding).
      case binding of
        Inl val \<Rightarrow> (name, Inl val)
      | Inr path \<Rightarrow> (name, Inr (path_elem # path)))
    bindings"

(* Pattern matching: returns bindings as (name, Inl value) for Var or (name, Inr path) for Ref *)
function match_pattern :: "BabPattern \<Rightarrow> BabValue \<Rightarrow> (string \<times> (BabValue + LValuePath list)) list option" where
  "match_pattern pat value = (case (pat, value) of
      (BabPat_Wildcard _, _) \<Rightarrow> Some []
    | (BabPat_Var _ Var name, v) \<Rightarrow> Some [(name, Inl v)]
    | (BabPat_Var _ Ref name, _) \<Rightarrow> Some [(name, Inr [])]
    | (BabPat_Bool _ expected_b, BV_Bool actual_b) \<Rightarrow>
        if expected_b = actual_b then Some [] else None
    | (BabPat_Int _ expected_i, BV_FiniteInt _ _ actual_i) \<Rightarrow>
        if expected_i = actual_i then Some [] else None
    | (BabPat_Tuple _ pats, BV_Tuple vals) \<Rightarrow>
        if length pats = length vals then
          (let pairs = zip pats vals;
               results = map (\<lambda>(p, v). match_pattern p v) pairs in
           if list_ex (\<lambda>r. r = None) results then None
           else
             let bindings_list = map the results;
                 adjusted_bindings = concat (map (\<lambda>(i, bs). prepend_path_to_bindings (LVPath_TupleProj i) bs)
                                             (zip [0..<length bindings_list] bindings_list))
             in Some adjusted_bindings)
        else None
    | (BabPat_Record _ field_pats, BV_Record flds) \<Rightarrow>
        (let field_names = map fst field_pats in
         if list_all (\<lambda>fname. map_of flds fname \<noteq> None) field_names then
           (let results = map (\<lambda>(fname, p). match_pattern p (the (map_of flds fname))) field_pats in
            if list_ex (\<lambda>r. r = None) results then None
            else
              let bindings_list = map the results;
                  adjusted_bindings = concat (map (\<lambda>((fname, _), bs). prepend_path_to_bindings (LVPath_RecordProj fname) bs)
                                              (zip field_pats bindings_list))
              in Some adjusted_bindings)
         else None)
    | (BabPat_Variant _ ctor_pat maybe_pat, BV_Variant ctor_val maybe_val) \<Rightarrow>
        if ctor_pat = ctor_val then
          (case (maybe_pat, maybe_val) of
            (None, None) \<Rightarrow> Some []
          | (Some p, Some v) \<Rightarrow>
              (case match_pattern p v of
                None \<Rightarrow> None
              | Some bindings \<Rightarrow> Some (prepend_path_to_bindings (LVPath_VariantProj ctor_pat) bindings))
          | _ \<Rightarrow> None)
        else None
    | _ \<Rightarrow> None)"
  by pat_completeness auto

termination match_pattern
proof (relation "measure (\<lambda>(pat, _). bab_pattern_size pat)")
  show "wf (measure (\<lambda>(pat, _). bab_pattern_size pat))" by auto
next
  fix pat val orig_pat orig_val loc pats vals pairs pair sub_pat sub_val
  assume "(orig_pat, orig_val) = (pat, val)"
     and "orig_pat = BabPat_Tuple loc pats"
     and "orig_val = BV_Tuple vals"
     and "length pats = length vals"
     and "pairs = zip pats vals"
     and "pair \<in> set pairs"
     and "(sub_pat, sub_val) = pair"
  then have "sub_pat \<in> set pats"
    by (auto simp add: in_set_zip)
  then show "((sub_pat, sub_val), pat, val) \<in> measure (\<lambda>(pat, _). bab_pattern_size pat)"
    using `(orig_pat, orig_val) = (pat, val)` `orig_pat = BabPat_Tuple loc pats`
    by (auto simp add: bab_pattern_smaller_than_list)
next
  fix pat val orig_pat orig_val loc field_pats flds field_names pair fname sub_pat
  assume "(orig_pat, orig_val) = (pat, val)"
     and "orig_pat = BabPat_Record loc field_pats"
     and "orig_val = BV_Record flds"
     and "field_names = map fst field_pats"
     and "list_all (\<lambda>fname. map_of flds fname \<noteq> None) field_names"
     and "pair \<in> set field_pats"
     and "(fname, sub_pat) = pair"
  then show "((sub_pat, the (map_of flds fname)), pat, val) \<in> measure (\<lambda>(pat, _). bab_pattern_size pat)"
    using \<open>(orig_pat, orig_val) = (pat, val)\<close> \<open>orig_pat = BabPat_Record loc field_pats\<close>
    by (auto simp add: bab_pattern_smaller_than_fieldlist)
next
  fix pat val orig_pat orig_val loc ctor_pat maybe_pat ctor_val maybe_val pair1 pair2 sub_pat sub_val
  assume "(orig_pat, orig_val) = (pat, val)"
     and "orig_pat = BabPat_Variant loc ctor_pat maybe_pat"
     and "orig_val = BV_Variant ctor_val maybe_val"
     and "ctor_pat = ctor_val"
     and "(pair1, pair2) = (maybe_pat, maybe_val)"
     and "pair1 = Some sub_pat"
     and "pair2 = Some sub_val"
  then show "((sub_pat, sub_val), pat, val) \<in> measure (\<lambda>(pat, _). bab_pattern_size pat)"
    by auto
qed

(* Apply pattern bindings to state: allocate Var bindings, add Ref bindings *)
fun apply_pattern_bindings :: "'w BabState \<Rightarrow> (nat \<times> LValuePath list) option \<Rightarrow> (string \<times> (BabValue + LValuePath list)) list \<Rightarrow> 'w BabState BabInterpResult" where
  "apply_pattern_bindings state lvalue_info [] = BIR_Success state"
| "apply_pattern_bindings state lvalue_info ((name, Inl value) # rest) =
    (let (state', addr) = alloc_store state value;
         state'' = state' \<lparr> BS_Locals := fmupd name addr (BS_Locals state') \<rparr>
     in apply_pattern_bindings state'' lvalue_info rest)"
| "apply_pattern_bindings state (Some (addr, base_path)) ((name, Inr rel_path) # rest) =
    (let full_path = base_path @ rel_path;
         state' = state \<lparr> BS_RefVars := fmupd name (addr, full_path) (BS_RefVars state) \<rparr>
     in apply_pattern_bindings state' (Some (addr, base_path)) rest)"
| "apply_pattern_bindings state None ((name, Inr rel_path) # rest) = BIR_TypeError"


(* ========================================================================== *)
(* The main interpreter definition *)
(* ========================================================================== *)

function interp_bab_term :: "nat \<Rightarrow> 'w BabState \<Rightarrow> BabTerm \<Rightarrow> BabValue BabInterpResult"
  and interp_bab_term_list :: "nat \<Rightarrow> 'w BabState \<Rightarrow> BabTerm list \<Rightarrow> (BabValue list) BabInterpResult"
  and interp_bab_binop :: "nat \<Rightarrow> 'w BabState \<Rightarrow> BabValue \<Rightarrow> (BabBinop \<times> BabTerm) list \<Rightarrow> BabValue BabInterpResult"
  and interp_bab_statement :: "nat \<Rightarrow> 'w BabState \<Rightarrow> BabStatement \<Rightarrow> 'w BabExecResult"
  and interp_bab_statement_list :: "nat \<Rightarrow> 'w BabState \<Rightarrow> BabStatement list \<Rightarrow> 'w BabExecResult"
  and eval_lvalue :: "nat \<Rightarrow> 'w BabState \<Rightarrow> BabTerm \<Rightarrow> ((nat \<times> LValuePath list) BabInterpResult)"
  and exec_function_call :: "nat \<Rightarrow> 'w BabState \<Rightarrow> BabTerm \<Rightarrow> ('w BabState \<times> BabValue option) BabInterpResult"
  and try_match_term_arms :: "nat \<Rightarrow> 'w BabState \<Rightarrow> BabValue \<Rightarrow> (nat \<times> LValuePath list) option \<Rightarrow> (BabPattern \<times> BabTerm) list \<Rightarrow> BabValue BabInterpResult"
  and try_match_stmt_arms :: "nat \<Rightarrow> 'w BabState \<Rightarrow> BabValue \<Rightarrow> (nat \<times> LValuePath list) option \<Rightarrow> (BabPattern \<times> BabStatement list) list \<Rightarrow> 'w BabExecResult"
where

  (* Literals *)
  "interp_bab_term 0 _ _ = BIR_InsufficientFuel"
| "interp_bab_term (Suc _) _ (BabTm_Literal _ (BabLit_Bool b)) = BIR_Success (BV_Bool b)"
| "interp_bab_term (Suc _) _ (BabTm_Literal _ (BabLit_Int i)) =
    (case infer_literal_type i of
      Some (sign, bits) \<Rightarrow> BIR_Success (BV_FiniteInt sign bits i)
    | None \<Rightarrow> BIR_TypeError)"
| "interp_bab_term (Suc _) _ (BabTm_Literal _ (BabLit_String s)) =
    (let char_codes = map of_char s in
     if list_all (\<lambda>c. 0 \<le> c \<and> c \<le> 255) char_codes
     then BIR_Success (make_array (map (BV_FiniteInt Unsigned IntBits_8) char_codes))
     else BIR_TypeError)"
| "interp_bab_term (Suc fuel) state (BabTm_Literal _ (BabLit_Array tms)) =
    (case interp_bab_term_list fuel state tms of
      BIR_Success vals \<Rightarrow> BIR_Success (make_array vals)
    | err \<Rightarrow> convert_error err)"

  (* Variable or nullary constructor lookup *)
| "interp_bab_term (Suc _) state (BabTm_Name _ name _) =
    (case fmlookup (BS_Locals state) name of
      Some addr \<Rightarrow> BIR_Success (BS_Store state ! addr)
    | None \<Rightarrow>
      (case fmlookup (BS_RefVars state) name of
        Some (addr, path) \<Rightarrow> get_value_at_path (BS_Store state ! addr) path
      | None \<Rightarrow>
        (case fmlookup (BS_Constants state) name of
          Some val \<Rightarrow> BIR_Success val
        | None \<Rightarrow>
          (if name |\<in>| BS_NullaryCtors state
           then BIR_Success (BV_Variant name None)
           else BIR_TypeError))))"

  (* Cast *)
| "interp_bab_term (Suc fuel) state (BabTm_Cast _ targetType tm) =
    (case interp_bab_term fuel state tm of
      BIR_Success (BV_FiniteInt src_sign src_bits i) \<Rightarrow>
        (case targetType of
          BabTy_FiniteInt _ tgt_sign tgt_bits \<Rightarrow>
            if int_fits tgt_sign tgt_bits i
            then BIR_Success (BV_FiniteInt tgt_sign tgt_bits i)
            else BIR_RuntimeError
        | _ \<Rightarrow> BIR_TypeError)
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"

  (* If-then-else *)
| "interp_bab_term (Suc fuel) state (BabTm_If _ cond thenTm elseTm) =
    (case interp_bab_term fuel state cond of
      BIR_Success (BV_Bool True) \<Rightarrow> interp_bab_term fuel state thenTm
    | BIR_Success (BV_Bool False) \<Rightarrow> interp_bab_term fuel state elseTm
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"

  (* Unary operators *)
| "interp_bab_term (Suc fuel) state (BabTm_Unop _ BabUnop_Negate tm) =
    (case interp_bab_term fuel state tm of
      BIR_Success (BV_FiniteInt sign bits i) \<Rightarrow>
        (let result = -i in
         if int_fits sign bits result then BIR_Success (BV_FiniteInt sign bits result)
         else BIR_RuntimeError)
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"
| "interp_bab_term (Suc fuel) state (BabTm_Unop _ BabUnop_Complement tm) =
    (case interp_bab_term fuel state tm of
      BIR_Success (BV_FiniteInt sign bits i) \<Rightarrow>
        BIR_Success (BV_FiniteInt sign bits (int_complement sign bits i))
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"
| "interp_bab_term (Suc fuel) state (BabTm_Unop _ BabUnop_Not tm) =
    (case interp_bab_term fuel state tm of
      BIR_Success (BV_Bool b) \<Rightarrow> BIR_Success (BV_Bool (\<not>b))
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"

  (* Binary operators *)
| "interp_bab_term (Suc fuel) state (BabTm_Binop _ tm1 ops) =
    (case interp_bab_term fuel state tm1 of
      BIR_Success v1 \<Rightarrow> interp_bab_binop fuel state v1 ops
    | err \<Rightarrow> err)"

  (* Let binding *)
| "interp_bab_term (Suc fuel) state (BabTm_Let _ name bindTm bodyTm) =
    (case interp_bab_term fuel state bindTm of
      BIR_Success val \<Rightarrow>
        (let (state', addr) = alloc_store state val;
             state'' = state' \<lparr> BS_Locals := fmupd name addr (BS_Locals state') \<rparr>
         in interp_bab_term fuel state'' bodyTm)
    | err \<Rightarrow> err)"

  (* Quantifier - not executable, return error *)
| "interp_bab_term (Suc _) _ (BabTm_Quantifier _ _ _ _ _) = BIR_TypeError"

  (* Function call *)
  (* Note: Function calls in a term context are not allowed to have ref parameters (this is
     a type error). This means that the new BabState returned from exec_function_call can
     be dropped. *)
| "interp_bab_term (Suc fuel) state (BabTm_Call loc fnTm argTms) =
    (if is_pure_fun_term state fnTm
     then
       case exec_function_call fuel state (BabTm_Call loc fnTm argTms) of
         BIR_Success (_, Some retVal) \<Rightarrow> BIR_Success retVal
       | BIR_Success (_, None) \<Rightarrow> BIR_TypeError
       | err \<Rightarrow> convert_error err
     else BIR_TypeError)"

  (* Tuple construction *)
| "interp_bab_term (Suc fuel) state (BabTm_Tuple _ tms) =
    (case interp_bab_term_list fuel state tms of
      BIR_Success vals \<Rightarrow> BIR_Success (BV_Tuple vals)
    | err \<Rightarrow> convert_error err)"

  (* Record construction *)
| "interp_bab_term (Suc fuel) state (BabTm_Record _ flds) =
    (case interp_bab_term_list fuel state (map snd flds) of
      BIR_Success vals \<Rightarrow> BIR_Success (BV_Record (zip (map fst flds) vals))
    | err \<Rightarrow> convert_error err)"

  (* Record update *)
| "interp_bab_term (Suc fuel) state (BabTm_RecordUpdate _ baseTm updates) =
    (case interp_bab_term fuel state baseTm of
      BIR_Success (BV_Record baseFields) \<Rightarrow>
        (case interp_bab_term_list fuel state (map snd updates) of
          BIR_Success vals \<Rightarrow>
            (case update_record_fields baseFields (zip (map fst updates) vals) of
              Some updatedFields \<Rightarrow> BIR_Success (BV_Record updatedFields)
            | None \<Rightarrow> BIR_TypeError)
        | err \<Rightarrow> convert_error err)
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"

  (* Tuple projection *)
| "interp_bab_term (Suc fuel) state (BabTm_TupleProj _ tm idx) =
    (case interp_bab_term fuel state tm of
      BIR_Success (BV_Tuple vals) \<Rightarrow>
        if idx < length vals then BIR_Success (vals ! idx)
        else BIR_TypeError
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"

  (* Record projection *)
| "interp_bab_term (Suc fuel) state (BabTm_RecordProj _ tm fieldName) =
    (case interp_bab_term fuel state tm of
      BIR_Success (BV_Record flds) \<Rightarrow>
        (case map_of flds fieldName of
          Some val \<Rightarrow> BIR_Success val
        | None \<Rightarrow> BIR_TypeError)
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"

  (* Array projection *)
| "interp_bab_term (Suc fuel) state (BabTm_ArrayProj _ arrTm indices) =
    (case interp_bab_term fuel state arrTm of
      BIR_Success (BV_Array _ fmap) \<Rightarrow>
        (case interp_bab_term_list fuel state indices of
          BIR_Success indexVals \<Rightarrow>
            (case interpret_index_vals indexVals of
              BIR_Success index_ints \<Rightarrow>
                (case fmlookup fmap index_ints of
                   Some val \<Rightarrow> BIR_Success val
                 | None \<Rightarrow> BIR_RuntimeError)
            | err \<Rightarrow> convert_error err)
        | err \<Rightarrow> convert_error err)
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"

  (* Match *)
| "interp_bab_term (Suc fuel) state (BabTm_Match _ scrutTm arms) =
    (case (interp_bab_term fuel state scrutTm, eval_lvalue fuel state scrutTm) of
      (BIR_Success scrutVal, BIR_Success lv) \<Rightarrow>
        try_match_term_arms fuel state scrutVal (Some lv) arms
    | (BIR_Success scrutVal, _) \<Rightarrow>
        try_match_term_arms fuel state scrutVal None arms
    | (err, _) \<Rightarrow> err)"

  (* Sizeof *)
| "interp_bab_term (Suc fuel) state (BabTm_Sizeof _ tm) =
    (case interp_bab_term fuel state tm of
      BIR_Success (BV_Array dims _) \<Rightarrow> BIR_Success (array_size_to_value dims)
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"

  (* Allocated - not executable, error *)
| "interp_bab_term (Suc _) _ (BabTm_Allocated _ _) = BIR_TypeError"

  (* Old - not executable, error *)
| "interp_bab_term (Suc _) _ (BabTm_Old _ _) = BIR_TypeError"

  (* Interpret a list of terms *)
| "interp_bab_term_list 0 _ _ = BIR_InsufficientFuel"
| "interp_bab_term_list (Suc _) _ [] = BIR_Success []"
| "interp_bab_term_list (Suc fuel) state (tm # tms) =
    (case interp_bab_term fuel state tm of
      BIR_Success val \<Rightarrow>
        (case interp_bab_term_list fuel state tms of
          BIR_Success vals \<Rightarrow> BIR_Success (val # vals)
        | err \<Rightarrow> err)
    | err \<Rightarrow> convert_error err)"

  (* Evaluate a binary operator chain *)
| "interp_bab_binop 0 _ _ _ = BIR_InsufficientFuel"
| "interp_bab_binop (Suc _) _ v1 [] = BIR_Success v1"
| "interp_bab_binop (Suc fuel) state v1 ((op, tm2) # rest) =
    (case interp_bab_term fuel state tm2 of
      BIR_Success v2 \<Rightarrow>
        (case eval_binop op v1 v2 of
          BIR_Success result \<Rightarrow> interp_bab_binop fuel state result rest
        | err \<Rightarrow> err)
    | err \<Rightarrow> err)"

  (* Variable declaration statement *)
| "interp_bab_statement 0 _ _ = BER_InsufficientFuel"
| "interp_bab_statement (Suc _) state (BabStmt_VarDecl _ Ghost _ _ _ _) = BER_Continue state"
| "interp_bab_statement (Suc fuel) state (BabStmt_VarDecl _ NotGhost name Var _ (Some tm)) =
    (case interp_bab_term fuel state tm of
      BIR_Success value \<Rightarrow>
        (let (state', addr) = alloc_store state value
         in BER_Continue (state' \<lparr> BS_Locals := fmupd name addr (BS_Locals state') \<rparr>))
    | err \<Rightarrow> convert_exec_error err)"
| "interp_bab_statement (Suc fuel) state (BabStmt_VarDecl _ NotGhost name Ref _ (Some tm)) =
    (case eval_lvalue fuel state tm of
      BIR_Success (addr, path) \<Rightarrow>
        BER_Continue (state \<lparr> BS_RefVars := fmupd name (addr, path) (BS_RefVars state) \<rparr>)
    | err \<Rightarrow> convert_exec_error err)"
| "interp_bab_statement (Suc _) _ (BabStmt_VarDecl _ NotGhost _ _ _ None) =
    BER_TypeError"  (* initializer is required *)

  (* Fix, obtain, use not allowed in executable code *)
| "interp_bab_statement (Suc _) _ (BabStmt_Fix _ _ _) = BER_TypeError"
| "interp_bab_statement (Suc _) _ (BabStmt_Obtain _ _ _ _) = BER_TypeError"
| "interp_bab_statement (Suc _) _ (BabStmt_Use _ _) = BER_TypeError"

  (* Assignment statement *)
| "interp_bab_statement (Suc _) state (BabStmt_Assign _ Ghost _ _) = BER_Continue state"
| "interp_bab_statement (Suc fuel) state (BabStmt_Assign _ NotGhost lhs rhs) =
    (case eval_lvalue fuel state lhs of
      BIR_Success (addr, path) \<Rightarrow>
        (let stateAndVal = (case rhs of
            BabTm_Call loc fnTm argTms \<Rightarrow>
              (case exec_function_call fuel state (BabTm_Call loc fnTm argTms) of
                BIR_Success (newState, Some retVal) \<Rightarrow> BIR_Success (newState, retVal)
              | BIR_Success (_, None) \<Rightarrow> BIR_TypeError
              | err \<Rightarrow> convert_error err)
          | _ \<Rightarrow>
              (case interp_bab_term fuel state rhs of
                BIR_Success rhs_val \<Rightarrow> BIR_Success (state, rhs_val)
              | err \<Rightarrow> convert_error err))
         in case stateAndVal of
           BIR_Success (newState, rhs_val) \<Rightarrow>
             (let old_val = BS_Store newState ! addr in
               case update_value_at_path old_val path rhs_val of
                 BIR_Success new_val \<Rightarrow>
                   BER_Continue (newState \<lparr> BS_Store := (BS_Store newState)[addr := new_val] \<rparr>)
               | err \<Rightarrow> convert_exec_error err)
         | err \<Rightarrow> convert_exec_error err)
    | err \<Rightarrow> convert_exec_error err)"

  (* Swap statement *)
| "interp_bab_statement (Suc _) state (BabStmt_Swap _ Ghost _ _) = BER_Continue state"
| "interp_bab_statement (Suc fuel) state (BabStmt_Swap _ NotGhost lhs1 lhs2) =
    (case eval_lvalue fuel state lhs1 of
      BIR_Success lv1 \<Rightarrow>
        (case eval_lvalue fuel state lhs2 of
          BIR_Success lv2 \<Rightarrow> exec_swap state lv1 lv2
        | err \<Rightarrow> convert_exec_error err)
    | err \<Rightarrow> convert_exec_error err)"

  (* Return statement *)
| "interp_bab_statement (Suc _) _ (BabStmt_Return _ Ghost _) = BER_TypeError"
| "interp_bab_statement (Suc fuel) state (BabStmt_Return _ NotGhost maybeExpr) =
    (case maybeExpr of
      Some expr \<Rightarrow>
        (case interp_bab_term fuel state expr of
          BIR_Success val \<Rightarrow> BER_Return state (Some val)
        | err \<Rightarrow> convert_exec_error err)
    | None \<Rightarrow> BER_Return state None)"

  (* Assert statement - ignored in executable code *)
| "interp_bab_statement (Suc _) state (BabStmt_Assert _ _ _) = BER_Continue state"

  (* Assume statement - ignored in executable code *)
| "interp_bab_statement (Suc _) state (BabStmt_Assume _ _) = BER_Continue state"

  (* If statement *)
| "interp_bab_statement (Suc _) state (BabStmt_If _ Ghost _ _ _) = BER_Continue state"
| "interp_bab_statement (Suc fuel) state (BabStmt_If _ NotGhost cond thenStmts elseStmts) =
    (case interp_bab_term fuel state cond of
      BIR_Success (BV_Bool b) \<Rightarrow>
        (let branch_stmts = if b then thenStmts else elseStmts
         in case interp_bab_statement_list fuel state branch_stmts of
           BER_Continue state' \<Rightarrow> BER_Continue (restore_scope state state')
         | BER_Return state' retVal \<Rightarrow> BER_Return (restore_scope state state') retVal
         | err \<Rightarrow> err)
    | BIR_Success _ \<Rightarrow> BER_TypeError
    | err \<Rightarrow> convert_exec_error err)"

  (* While statement *)
| "interp_bab_statement (Suc _) state (BabStmt_While _ Ghost _ _ _) = BER_Continue state"
| "interp_bab_statement (Suc fuel) state (BabStmt_While loc NotGhost cond attrs bodyStmts) =
    (case interp_bab_term fuel state cond of
      BIR_Success (BV_Bool True) \<Rightarrow>
        (case interp_bab_statement_list fuel state bodyStmts of
          BER_Continue state' \<Rightarrow>
            interp_bab_statement fuel (restore_scope state state') (BabStmt_While loc NotGhost cond attrs bodyStmts)
        | BER_Return state' retVal \<Rightarrow> BER_Return (restore_scope state state') retVal
        | err \<Rightarrow> err)
    | BIR_Success (BV_Bool False) \<Rightarrow> BER_Continue state
    | BIR_Success _ \<Rightarrow> BER_TypeError
    | err \<Rightarrow> convert_exec_error err)"

  (* Call statement *)
  (* This calls a function, updating state, but discarding the return value *)
| "interp_bab_statement (Suc _) state (BabStmt_Call _ Ghost _) = BER_Continue state"
| "interp_bab_statement (Suc fuel) state (BabStmt_Call _ NotGhost callTm) =
    (case exec_function_call fuel state callTm of
      BIR_Success (newState, _) \<Rightarrow> BER_Continue newState
    | err \<Rightarrow> convert_exec_error err)"

  (* Match statement *)
| "interp_bab_statement (Suc _) state (BabStmt_Match _ Ghost _ _) = BER_Continue state"
| "interp_bab_statement (Suc fuel) state (BabStmt_Match _ NotGhost scrutTm arms) =
    (case (interp_bab_term fuel state scrutTm, eval_lvalue fuel state scrutTm) of
      (BIR_Success scrutVal, BIR_Success lv) \<Rightarrow>
        try_match_stmt_arms fuel state scrutVal (Some lv) arms
    | (BIR_Success scrutVal, _) \<Rightarrow>
        try_match_stmt_arms fuel state scrutVal None arms
    | (err, _) \<Rightarrow> convert_exec_error err)"

  (* ShowHide statement - ignored in executable code *)
| "interp_bab_statement (Suc _) state (BabStmt_ShowHide _ _ _) = BER_Continue state"

  (* Interpret a list of statements *)
| "interp_bab_statement_list 0 _ _ = BER_InsufficientFuel"
| "interp_bab_statement_list (Suc _) state [] = BER_Continue state"
| "interp_bab_statement_list (Suc fuel) state (stmt # stmts) =
    (case interp_bab_statement fuel state stmt of
      BER_Continue state1 \<Rightarrow> interp_bab_statement_list fuel state1 stmts
    | BER_Return state1 retVal \<Rightarrow> BER_Return state1 retVal
    | err \<Rightarrow> err)"

  (* Decompose an lvalue into (address, path) *)
| "eval_lvalue 0 _ _ = BIR_InsufficientFuel"
| "eval_lvalue (Suc fuel) state tm =
    (case tm of
      BabTm_Name _ name _ \<Rightarrow>
        (case fmlookup (BS_RefVars state) name of
          Some (addr, path) \<Rightarrow> BIR_Success (addr, path)
        | None \<Rightarrow>
          (case fmlookup (BS_Locals state) name of
            Some addr \<Rightarrow> BIR_Success (addr, [])
          | None \<Rightarrow> BIR_TypeError))
    | BabTm_TupleProj _ tm' idx \<Rightarrow>
        (case eval_lvalue fuel state tm' of
          BIR_Success (addr, path) \<Rightarrow> BIR_Success (addr, path @ [LVPath_TupleProj idx])
        | err \<Rightarrow> err)
    | BabTm_RecordProj _ tm' field \<Rightarrow>
        (case eval_lvalue fuel state tm' of
          BIR_Success (addr, path) \<Rightarrow> BIR_Success (addr, path @ [LVPath_RecordProj field])
        | err \<Rightarrow> err)
    | BabTm_ArrayProj _ tm' index_tms \<Rightarrow>
        (case eval_lvalue fuel state tm' of
          BIR_Success (addr, path) \<Rightarrow>
            (case interp_bab_term_list fuel state index_tms of
              BIR_Success index_vals \<Rightarrow>
                (case interpret_index_vals index_vals of
                  BIR_Success indices \<Rightarrow> BIR_Success (addr, path @ [LVPath_ArrayProj indices])
                | err \<Rightarrow> convert_error err)
            | err \<Rightarrow> convert_error err)
        | err \<Rightarrow> err)
    | _ \<Rightarrow> BIR_TypeError)"

  (* Execute a function call *)
| "exec_function_call 0 _ _ = BIR_InsufficientFuel"
| "exec_function_call (Suc fuel) state callTm =
    (case callTm of
      BabTm_Call _ (BabTm_Name _ fnName tyArgs) argTms \<Rightarrow>
        (case fmlookup (BS_Functions state) fnName of
          Some funDecl \<Rightarrow>
            (if DF_Ghost funDecl = Ghost then BIR_TypeError
             else
               let params = DF_TmArgs funDecl;
                   tyParams = DF_TyArgs funDecl
               in
               if length argTms \<noteq> length params then BIR_TypeError
               else if length tyArgs \<noteq> length tyParams then BIR_TypeError
               else
                 let refResults = map (eval_lvalue fuel state) argTms;
                     valResults = map (interp_bab_term fuel state) argTms;
                     argTriples = zip params (zip refResults valResults);
                     clearedState = state \<lparr> BS_Locals := fmempty,
                                            BS_RefVars := fmempty \<rparr>
                 in
                   case fold process_one_arg argTriples (BIR_Success clearedState) of
                     BIR_Success newState \<Rightarrow>
                       (let execResult =
                         (if DF_Extern funDecl then
                           call_extern_function state fnName tyArgs params refResults valResults
                         else
                           (case DF_Body funDecl of
                             Some stmts \<Rightarrow> interp_bab_statement_list fuel newState stmts
                           | None \<Rightarrow> BER_RuntimeError))
                       in
                         case execResult of
                           BER_Return finalState retVal \<Rightarrow>
                             BIR_Success (restore_scope state finalState, retVal)
                         | BER_Continue finalState \<Rightarrow>
                             BIR_Success (restore_scope state finalState, None)
                         | BER_TypeError \<Rightarrow> BIR_TypeError
                         | BER_RuntimeError \<Rightarrow> BIR_RuntimeError
                         | BER_InsufficientFuel \<Rightarrow> BIR_InsufficientFuel)
                   | err \<Rightarrow> convert_error err)
        | None \<Rightarrow> BIR_TypeError)
    | _ \<Rightarrow> BIR_TypeError)"

  (* Try matching term arms *)
| "try_match_term_arms 0 _ _ _ _ = BIR_InsufficientFuel"
| "try_match_term_arms (Suc _) _ _ _ [] = BIR_RuntimeError"
| "try_match_term_arms (Suc fuel) state scrutVal lvalue_info ((pat, result_tm) # rest) =
    (case match_pattern pat scrutVal of
      None \<Rightarrow> try_match_term_arms fuel state scrutVal lvalue_info rest
    | Some bindings \<Rightarrow>
        (case apply_pattern_bindings state lvalue_info bindings of
          BIR_Success extended_state \<Rightarrow> interp_bab_term fuel extended_state result_tm
        | err \<Rightarrow> convert_error err))"

  (* Try matching statement arms *)
| "try_match_stmt_arms 0 _ _ _ _ = BER_InsufficientFuel"
| "try_match_stmt_arms (Suc _) state _ _ [] = BER_RuntimeError"
| "try_match_stmt_arms (Suc fuel) state scrutVal lvalue_info ((pat, stmts) # rest) =
    (case match_pattern pat scrutVal of
      None \<Rightarrow> try_match_stmt_arms fuel state scrutVal lvalue_info rest
    | Some bindings \<Rightarrow>
        (case apply_pattern_bindings state lvalue_info bindings of
          BIR_Success extended_state \<Rightarrow>
            (case interp_bab_statement_list fuel extended_state stmts of
              BER_Continue state' \<Rightarrow> BER_Continue (restore_scope state state')
            | BER_Return state' retVal \<Rightarrow> BER_Return (restore_scope state state') retVal
            | err \<Rightarrow> err)
        | err \<Rightarrow> convert_exec_error err))"

  by pat_completeness auto

termination by (relation "measure (\<lambda>x. case x of
        Inl (Inl (Inl (fuel, _, _))) \<Rightarrow> fuel
      | Inl (Inl (Inr (fuel, _, _))) \<Rightarrow> fuel
      | Inl (Inr (Inl (fuel, _, _, _))) \<Rightarrow> fuel
      | Inl (Inr (Inr (fuel, _, _))) \<Rightarrow> fuel
      | Inr (Inl (Inl (fuel, _, _))) \<Rightarrow> fuel
      | Inr (Inl (Inr (fuel, _, _))) \<Rightarrow> fuel
      | Inr (Inr (Inl (fuel, _, _))) \<Rightarrow> fuel
      | Inr (Inr (Inr (Inl (fuel, _, _, _, _)))) \<Rightarrow> fuel
      | Inr (Inr (Inr (Inr (fuel, _, _, _, _)))) \<Rightarrow> fuel
      )", auto)

end

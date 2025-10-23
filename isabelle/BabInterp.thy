theory BabInterp
  imports BabSyntax "HOL.Bit_Operations"
begin

datatype BabValue =
  BV_Bool bool
  | BV_Int int
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

record BabState =
  BS_Functions :: "(string, DeclFun) fmap"
  BS_Constants :: "(string, BabValue) fmap"  (* global constants *)
  BS_Typedefs :: "(string, DeclTypedef) fmap"
  BS_Datatypes :: "(string, DeclDatatype) fmap"
  BS_Store :: "BabValue list"  (* address \<rightarrow> value *)
  BS_Locals :: "(string, nat) fmap"  (* variable name \<rightarrow> address *)
  BS_RefVars :: "(string, nat \<times> LValuePath list) fmap"  (* ref name \<rightarrow> (address, path) *)
  BS_LocalTypes :: "(string, BabType) fmap"  (* local tyvar name \<rightarrow> type *)

datatype 'a BabInterpResult =
  BIR_Success 'a
  | BIR_TypeError
  | BIR_RuntimeError
  | BIR_InsufficientFuel

datatype BabExecResult =
  BER_Continue BabState
  | BER_Return BabState "BabValue option"
  | BER_TypeError
  | BER_RuntimeError
  | BER_InsufficientFuel


fun convert_error :: "'a BabInterpResult \<Rightarrow> 'b BabInterpResult" where
  "convert_error (BIR_Success _) = undefined"
| "convert_error BIR_TypeError = BIR_TypeError"
| "convert_error BIR_RuntimeError = BIR_RuntimeError"
| "convert_error BIR_InsufficientFuel = BIR_InsufficientFuel"

fun convert_exec_error :: "'a BabInterpResult \<Rightarrow> BabExecResult" where
  "convert_exec_error (BIR_Success _) = undefined"
| "convert_exec_error BIR_TypeError = BER_TypeError"
| "convert_exec_error BIR_RuntimeError = BER_RuntimeError"
| "convert_exec_error BIR_InsufficientFuel = BER_InsufficientFuel"

fun make_array :: "BabValue list \<Rightarrow> BabValue" where
  "make_array vals = BV_Array [int (length vals)] (fmap_of_list (zip (map (\<lambda>i.[int i]) [0..<length vals]) vals))"

(* Update record fields: replace existing fields with updates, keep others *)
(* Returns None if any update field doesn't exist in base *)
fun update_record_fields :: "(string \<times> BabValue) list \<Rightarrow> (string \<times> BabValue) list \<Rightarrow> (string \<times> BabValue) list option" where
  "update_record_fields baseFields [] = Some baseFields"
| "update_record_fields baseFields ((name, val) # updates) =
    (if map_of baseFields name = None then None
     else update_record_fields (AList.update name val baseFields) updates)"

(* Truncated division - rounds towards zero, like C/Java/JavaScript *)
fun tdiv :: "int \<Rightarrow> int \<Rightarrow> int" where
  "tdiv i1 i2 = sgn i1 * sgn i2 * (abs i1 div abs i2)"

(* Truncated modulo - remainder has sign of dividend, like C/Java/JavaScript *)
fun tmod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "tmod i1 i2 = sgn i1 * (abs i1 mod abs i2)"

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

(* Restore scope after exiting a block:
   - old_state: the state before entering the scope
   - new_state: the state after executing the inner scope
   Returns: new_state with locals/refs restored and store truncated *)
fun restore_scope :: "BabState \<Rightarrow> BabState \<Rightarrow> BabState" where
  "restore_scope old_state new_state =
    new_state \<lparr> BS_Locals := BS_Locals old_state,
                BS_RefVars := BS_RefVars old_state,
                BS_Store := take (length (BS_Store old_state)) (BS_Store new_state) \<rparr>"

(* Allocate a new address in the store and store the given value *)
fun alloc_store :: "BabState \<Rightarrow> BabValue \<Rightarrow> (BabState \<times> nat)" where
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
| "get_value_at_path _ _ = BIR_TypeError"

(* Convert array size to BabValue: for 1-d arrays return BV_Int, for 2-d+ return BV_Tuple *)
fun array_size_to_value :: "int list \<Rightarrow> BabValue" where
  "array_size_to_value ns = (if length ns = 1 then BV_Int (hd ns) else BV_Tuple (map BV_Int ns))"

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
| "update_value_at_path _ _ _ = BIR_TypeError"

(* Check if a term is a pure function (has no ref parameters) *)
fun is_pure_fun_term :: "BabState \<Rightarrow> BabTerm \<Rightarrow> bool" where
  "is_pure_fun_term state (BabTm_Name _ fnName _) =
    (case fmlookup (BS_Functions state) fnName of
      Some funDecl \<Rightarrow> \<not> list_ex (\<lambda>(_, vr, _). vr = Ref) (DF_TmArgs funDecl)
    | None \<Rightarrow> False)"
| "is_pure_fun_term _ _ = False"

(* Convert a list of BV_Int values to a list of ints, or return a type error *)
fun interpret_index_vals :: "BabValue list \<Rightarrow> (int list) BabInterpResult" where
  "interpret_index_vals [] = BIR_Success []"
| "interpret_index_vals (BV_Int i # rest) =
    (case interpret_index_vals rest of
      BIR_Success results \<Rightarrow> BIR_Success (i # results)
    | err \<Rightarrow> err)"
| "interpret_index_vals (nonInteger # rest) = BIR_TypeError"

(* Helper function to process a single argument and update the state *)
(* Takes: ((parameter info, (lvalue result, rvalue result)), current state result) *)
(* Returns: updated state, or error *)
fun process_one_arg :: "((string \<times> VarOrRef \<times> BabType)
                        \<times> (nat \<times> LValuePath list) BabInterpResult
                        \<times> BabValue BabInterpResult)
                \<Rightarrow> BabState BabInterpResult
                \<Rightarrow> BabState BabInterpResult" where
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

(* Main mutually recursive interpreter functions *)
function interp_bab_term :: "nat \<Rightarrow> BabState \<Rightarrow> BabTerm \<Rightarrow> BabValue BabInterpResult"
  and interp_bab_term_list :: "nat \<Rightarrow> BabState \<Rightarrow> BabTerm list \<Rightarrow> (BabValue list) BabInterpResult"
  and interp_bab_binop :: "nat \<Rightarrow> BabState \<Rightarrow> BabValue \<Rightarrow> (BabBinop \<times> BabTerm) list \<Rightarrow> BabValue BabInterpResult"
  and interp_bab_statement :: "nat \<Rightarrow> BabState \<Rightarrow> BabStatement \<Rightarrow> BabExecResult"
  and interp_bab_statement_list :: "nat \<Rightarrow> BabState \<Rightarrow> BabStatement list \<Rightarrow> BabExecResult"
  and interp_bab_initializer :: "nat \<Rightarrow> BabState \<Rightarrow> BabType option \<Rightarrow> BabTerm option \<Rightarrow> BabValue BabInterpResult"
  and make_default_value :: "nat \<Rightarrow> BabState \<Rightarrow> BabType \<Rightarrow> BabValue BabInterpResult"
  and make_default_value_list :: "nat \<Rightarrow> BabState \<Rightarrow> BabType list \<Rightarrow> (BabValue list) BabInterpResult"
  and eval_lvalue :: "nat \<Rightarrow> BabState \<Rightarrow> BabTerm \<Rightarrow> ((nat \<times> LValuePath list) BabInterpResult)"
  and exec_function_call :: "nat \<Rightarrow> BabState \<Rightarrow> BabTerm \<Rightarrow> (BabState \<times> BabValue option) BabInterpResult"
where

  (* Literals *)
  "interp_bab_term 0 _ _ = BIR_InsufficientFuel"
| "interp_bab_term (Suc _) _ (BabTm_Literal _ (BabLit_Bool b)) = BIR_Success (BV_Bool b)"
| "interp_bab_term (Suc _) _ (BabTm_Literal _ (BabLit_Int i)) = BIR_Success (BV_Int i)"
| "interp_bab_term (Suc _) _ (BabTm_Literal _ (BabLit_String s)) =
    BIR_Success (make_array (map (\<lambda>c. BV_Int (of_char c)) s))"
| "interp_bab_term (Suc fuel) state (BabTm_Literal _ (BabLit_Array tms)) =
    (case interp_bab_term_list fuel state tms of
      BIR_Success vals \<Rightarrow> BIR_Success (make_array vals)
    | err \<Rightarrow> convert_error err)"

  (* Variable lookup *)
| "interp_bab_term (Suc _) state (BabTm_Name _ name _) =
    (case fmlookup (BS_Locals state) name of
      Some addr \<Rightarrow> BIR_Success (BS_Store state ! addr)
    | None \<Rightarrow>
      (case fmlookup (BS_RefVars state) name of
        Some (addr, path) \<Rightarrow> get_value_at_path (BS_Store state ! addr) path
      | None \<Rightarrow>
        (case fmlookup (BS_Constants state) name of
          Some val \<Rightarrow> BIR_Success val
        | None \<Rightarrow> BIR_TypeError)))"

  (* Cast *)
| "interp_bab_term (Suc fuel) state (BabTm_Cast _ _ tm) = interp_bab_term fuel state tm"

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
      BIR_Success (BV_Int i) \<Rightarrow> BIR_Success (BV_Int (-i))
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"
| "interp_bab_term (Suc fuel) state (BabTm_Unop _ BabUnop_Complement tm) =
    (case interp_bab_term fuel state tm of
      BIR_Success (BV_Int i) \<Rightarrow> BIR_Success (BV_Int (-i - 1))
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
     a type error). This means the call will NOT make any changes to the BabState, and therefore,
     the new state returned from exec_function_call can be dropped. *)
| "interp_bab_term (Suc fuel) state (BabTm_Call _ fnTm argTms) =
    (if is_pure_fun_term state fnTm
     then
       case exec_function_call fuel state (BabTm_Call undefined fnTm argTms) of
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
            (let indices = map (\<lambda>v. case v of BV_Int i \<Rightarrow> i | _ \<Rightarrow> -1) indexVals in
              (case fmlookup fmap indices of
                 Some val \<Rightarrow> BIR_Success val
               | None \<Rightarrow> BIR_RuntimeError))
        | err \<Rightarrow> convert_error err)
    | BIR_Success _ \<Rightarrow> BIR_TypeError
    | err \<Rightarrow> err)"

  (* Match - not implemented yet *)
| "interp_bab_term (Suc _) _ (BabTm_Match _ _ _) = BIR_RuntimeError"

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
        (case (op, v1, v2) of
          (BabBinop_Add, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Int (i1 + i2)) rest
        | (BabBinop_Subtract, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Int (i1 - i2)) rest
        | (BabBinop_Multiply, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Int (i1 * i2)) rest
        | (BabBinop_Divide, BV_Int i1, BV_Int i2) \<Rightarrow>
            if i2 = 0 then BIR_RuntimeError
            else interp_bab_binop fuel state (BV_Int (tdiv i1 i2)) rest
        | (BabBinop_Modulo, BV_Int i1, BV_Int i2) \<Rightarrow>
            if i2 = 0 then BIR_RuntimeError
            else interp_bab_binop fuel state (BV_Int (tmod i1 i2)) rest

        | (BabBinop_BitAnd, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Int (and i1 i2)) rest
        | (BabBinop_BitOr, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Int (or i1 i2)) rest
        | (BabBinop_BitXor, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Int (xor i1 i2)) rest
        | (BabBinop_ShiftLeft, BV_Int i1, BV_Int i2) \<Rightarrow>
            if i2 < 0 then BIR_RuntimeError
            else interp_bab_binop fuel state (BV_Int (push_bit (nat i2) i1)) rest
        | (BabBinop_ShiftRight, BV_Int i1, BV_Int i2) \<Rightarrow>
            if i2 < 0 then BIR_RuntimeError
            else interp_bab_binop fuel state (BV_Int (drop_bit (nat i2) i1)) rest

        | (BabBinop_Equal, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (i1 = i2)) rest
        | (BabBinop_Equal, BV_Bool b1, BV_Bool b2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (b1 = b2)) rest
        | (BabBinop_NotEqual, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (i1 \<noteq> i2)) rest
        | (BabBinop_NotEqual, BV_Bool b1, BV_Bool b2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (b1 \<noteq> b2)) rest
        | (BabBinop_Less, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (i1 < i2)) rest
        | (BabBinop_LessEqual, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (i1 \<le> i2)) rest
        | (BabBinop_Greater, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (i1 > i2)) rest
        | (BabBinop_GreaterEqual, BV_Int i1, BV_Int i2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (i1 \<ge> i2)) rest

        | (BabBinop_And, BV_Bool b1, BV_Bool b2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (b1 \<and> b2)) rest
        | (BabBinop_Or, BV_Bool b1, BV_Bool b2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (b1 \<or> b2)) rest
        | (BabBinop_Implies, BV_Bool b1, BV_Bool b2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (b1 \<longrightarrow> b2)) rest
        | (BabBinop_ImpliedBy, BV_Bool b1, BV_Bool b2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (b2 \<longrightarrow> b1)) rest
        | (BabBinop_Iff, BV_Bool b1, BV_Bool b2) \<Rightarrow>
            interp_bab_binop fuel state (BV_Bool (b1 = b2)) rest

        | _ \<Rightarrow> BIR_TypeError)
    | err \<Rightarrow> err)"

  (* Variable declaration statement *)
| "interp_bab_statement 0 _ _ = BER_InsufficientFuel"
| "interp_bab_statement (Suc _) state (BabStmt_VarDecl _ Ghost _ _ _ _) = BER_Continue state"
| "interp_bab_statement (Suc fuel) state (BabStmt_VarDecl _ NotGhost name Var maybeType maybeTerm) =
    (case interp_bab_initializer fuel state maybeType maybeTerm of
      BIR_Success value \<Rightarrow>
        (let (state', addr) = alloc_store state value
         in BER_Continue (state' \<lparr> BS_Locals := fmupd name addr (BS_Locals state') \<rparr>))
    | err \<Rightarrow> convert_exec_error err)"
| "interp_bab_statement (Suc fuel) state (BabStmt_VarDecl _ NotGhost name Ref _ (Some tm)) =
    (case eval_lvalue fuel state tm of
      BIR_Success (addr, path) \<Rightarrow>
        BER_Continue (state \<lparr> BS_RefVars := fmupd name (addr, path) (BS_RefVars state) \<rparr>)
    | err \<Rightarrow> convert_exec_error err)"
| "interp_bab_statement (Suc _) _ (BabStmt_VarDecl _ NotGhost _ Ref _ None) =
    BER_TypeError"  (* ref must be initialized *)

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
      BIR_Success (addr1, path1) \<Rightarrow>
        (case eval_lvalue fuel state lhs2 of
          BIR_Success (addr2, path2) \<Rightarrow>
            (case get_value_at_path (BS_Store state ! addr1) path1 of
              BIR_Success val1 \<Rightarrow>
                (case get_value_at_path (BS_Store state ! addr2) path2 of
                  BIR_Success val2 \<Rightarrow>
                    (case update_value_at_path (BS_Store state ! addr1) path1 val2 of
                      BIR_Success new_val1 \<Rightarrow>
                        (case update_value_at_path (BS_Store state ! addr2) path2 val1 of
                          BIR_Success new_val2 \<Rightarrow>
                            BER_Continue (state \<lparr> BS_Store := 
                                (BS_Store state)[addr1 := new_val1, addr2 := new_val2] \<rparr>)
                          | err \<Rightarrow> convert_exec_error err)
                      | err \<Rightarrow> convert_exec_error err)
                  | err \<Rightarrow> convert_exec_error err)
              | err \<Rightarrow> convert_exec_error err)
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

  (* Match statement - not implemented yet *)
| "interp_bab_statement (Suc _) _ (BabStmt_Match _ _ _ _) = BER_RuntimeError"

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

  (* Initializers (e.g. in var decl statement). Note at least one of type, term must be present. *)
| "interp_bab_initializer 0 _ _ _ = BIR_InsufficientFuel"
| "interp_bab_initializer (Suc fuel) state maybeType maybeTerm =
    (case (maybeType, maybeTerm) of
      (_, Some tm) \<Rightarrow>
        interp_bab_term fuel state tm
    | (Some ty, _) \<Rightarrow>
        make_default_value fuel state ty
    | _ \<Rightarrow>
        BIR_RuntimeError)"

  (* Default value of a type *)
| "make_default_value 0 _ _ = BIR_InsufficientFuel"

  (* Default value of BabTy_Name - could be local type, typedef or datatype *)
| "make_default_value (Suc fuel) state (BabTy_Name _ name tyArgs) =
    (case fmlookup (BS_LocalTypes state) name of
      Some localType \<Rightarrow>
        (if tyArgs = [] then make_default_value fuel state localType
         else BIR_TypeError)
    | None \<Rightarrow>
      (case fmlookup (BS_Typedefs state) name of
        Some typedef \<Rightarrow>
          (case DT_Definition typedef of
            None \<Rightarrow> BIR_Success (BV_Abstract 0)
          | Some defType \<Rightarrow>
              (let subst = fmap_of_list (zip (DT_TyArgs typedef) tyArgs);
                   substitutedType = substitute_bab_type subst defType
               in make_default_value fuel state substitutedType))
      | None \<Rightarrow>
        (case fmlookup (BS_Datatypes state) name of
          Some datatype \<Rightarrow>
            (case DD_Ctors datatype of
              [] \<Rightarrow> BIR_TypeError
            | (_, ctorName, maybePayloadType) # _ \<Rightarrow>
                (case maybePayloadType of
                  None \<Rightarrow> BIR_Success (BV_Variant ctorName None)
                | Some payloadType \<Rightarrow>
                    (let subst = fmap_of_list (zip (DD_TyArgs datatype) tyArgs);
                         substitutedPayloadType = substitute_bab_type subst payloadType
                     in case make_default_value fuel state substitutedPayloadType of
                       BIR_Success payloadVal \<Rightarrow> BIR_Success (BV_Variant ctorName (Some payloadVal))
                     | err \<Rightarrow> convert_error err)))
        | None \<Rightarrow> BIR_TypeError)))"

  (* Default values of other types *)
| "make_default_value (Suc _) _ (BabTy_Bool _) = BIR_Success (BV_Bool False)"
| "make_default_value (Suc _) _ (BabTy_FiniteInt _ _ _) = BIR_Success (BV_Int 0)"
| "make_default_value (Suc _) _ (BabTy_MathInt _) = BIR_TypeError"  (* math ints not allowed at runtime *)
| "make_default_value (Suc _) _ (BabTy_MathReal _) = BIR_TypeError" (* reals not allowed at runtime *)

| "make_default_value (Suc fuel) state (BabTy_Tuple _ types) =
    (case make_default_value_list fuel state types of
      BIR_Success vals \<Rightarrow> BIR_Success (BV_Tuple vals)
    | err \<Rightarrow> convert_error err)"

| "make_default_value (Suc fuel) state (BabTy_Record _ fieldTypes) =
    (case make_default_value_list fuel state (map snd fieldTypes) of
      BIR_Success vals \<Rightarrow> BIR_Success (BV_Record (zip (map fst fieldTypes) vals))
    | err \<Rightarrow> convert_error err)"

  (* Default array: must be "complete" type. If allocatable, initial size is zero. *)
| "make_default_value (Suc fuel) state (BabTy_Array _ ty dims) =
    (if list_ex (\<lambda>d. case d of BabDim_Unknown \<Rightarrow> True | _ \<Rightarrow> False) dims then
      BIR_TypeError
    else if list_ex (\<lambda>d. case d of BabDim_Allocatable \<Rightarrow> True | _ \<Rightarrow> False) dims then
      BIR_Success (BV_Array (replicate (length dims) 0) fmempty)
    else
      let dimTerms = map (\<lambda>d. case d of BabDim_Fixed tm \<Rightarrow> tm) dims in
      case interp_bab_term_list fuel state dimTerms of
        BIR_Success dimVals \<Rightarrow>
          (let dimInts = map (\<lambda>v. case v of BV_Int i \<Rightarrow> i | _ \<Rightarrow> -1) dimVals in
            if list_ex (\<lambda>i. i < 0) dimInts then
              BIR_RuntimeError
            else
              case make_default_value fuel state ty of
                BIR_Success defaultVal \<Rightarrow> BIR_Success (make_default_array defaultVal dimInts)
              | err \<Rightarrow> convert_error err)
      | err \<Rightarrow> convert_error err)"

| "make_default_value_list 0 _ _ = BIR_InsufficientFuel"
| "make_default_value_list (Suc _) _ [] = BIR_Success []"
| "make_default_value_list (Suc fuel) state (ty # tys) =
    (case make_default_value fuel state ty of
      BIR_Success val \<Rightarrow>
        (case make_default_value_list fuel state tys of
          BIR_Success vals \<Rightarrow> BIR_Success (val # vals)
        | err \<Rightarrow> err)
    | err \<Rightarrow> convert_error err)"

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
            (if DF_Body funDecl = None then BIR_RuntimeError
             else if DF_Ghost funDecl = Ghost then BIR_TypeError
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
                                            BS_RefVars := fmempty,
                                            BS_LocalTypes := fmap_of_list (zip tyParams tyArgs) \<rparr>
                 in
                   case fold process_one_arg argTriples (BIR_Success clearedState) of
                     BIR_Success newState \<Rightarrow>
                       (case DF_Body funDecl of
                         Some stmts \<Rightarrow>
                           (case interp_bab_statement_list fuel newState stmts of
                             BER_Return finalState retVal \<Rightarrow>
                               BIR_Success (restore_scope state finalState, retVal)
                           | BER_Continue finalState \<Rightarrow>
                               BIR_Success (restore_scope state finalState, None)
                           | BER_TypeError \<Rightarrow> BIR_TypeError
                           | BER_RuntimeError \<Rightarrow> BIR_RuntimeError
                           | BER_InsufficientFuel \<Rightarrow> BIR_InsufficientFuel)
                       | None \<Rightarrow> BIR_RuntimeError)
                   | err \<Rightarrow> convert_error err)
        | None \<Rightarrow> BIR_TypeError)
    | _ \<Rightarrow> BIR_TypeError)"

  by pat_completeness auto

termination by (relation "measure (\<lambda>x. case x of
        Inl (Inl (Inl (fuel, _, _))) \<Rightarrow> fuel
      | Inl (Inl (Inr (fuel, _, _))) \<Rightarrow> fuel
      | Inl (Inr (Inl (fuel, _, _, _))) \<Rightarrow> fuel
      | Inl (Inr (Inr (Inl (fuel, _, _)))) \<Rightarrow> fuel
      | Inl (Inr (Inr (Inr (fuel, _, _)))) \<Rightarrow> fuel
      | Inr (Inl (Inl (fuel, _, _, _))) \<Rightarrow> fuel
      | Inr (Inl (Inr (fuel, _, _))) \<Rightarrow> fuel
      | Inr (Inr (Inl (fuel, _, _))) \<Rightarrow> fuel
      | Inr (Inr (Inr (Inl (fuel, _, _)))) \<Rightarrow> fuel
      | Inr (Inr (Inr (Inr (fuel, _, _)))) \<Rightarrow> fuel)", auto)

end

theory MiniCSemantics
  imports MiniCMemory
begin

(* ========================================================================== *)
(* MiniC: semantics                                                           *)
(* ========================================================================== *)

(* A fuelled interpreter for MiniC, in the style of CoreInterp. Expressions are
   pure and need no fuel (eval_expr returns None for undefined behaviour).
   Statements are executed by a mutually recursive, fuelled family of functions
   whose result distinguishes a normal result (Inr), insufficient fuel
   (Inl MErr_Fuel) and undefined behaviour (Inl MErr_UB). MiniC has no
   defined abnormal termination (no abort()): the generated code never needs
   one (see DESIGN.md, sections 3.2 and 3.3).

   "Undefined behaviour" means anything that a C compiler would be allowed to
   miscompile, plus anything the C standard leaves implementation-defined that
   the design (minic/DESIGN.md) does not explicitly assume, plus anything an
   ill-formed MiniC program might do (calling an unknown function, reading a
   buffer variable as a scalar, ...). The code generator's simulation theorem
   will show that the generated program never reaches MErr_UB.

   See DESIGN.md for the rationale behind each decision. *)


section \<open>Variables, state, externs\<close>

(* A variable binding: a scalar variable of a given C type, or a byte buffer.
   Either way the variable is an object in memory, in the given block (at
   offset 0). *)
datatype MVar =
  MVar_Scalar CTy nat
  | MVar_Buf nat

type_synonym MEnv = "(string, MVar) fmap"

(* The interpreter state.
    - MS_Mem: the memory (stack blocks, heap blocks, globals alike).
    - MS_Globals: the global variables.
    - MS_Locals: the variables visible in the current function and scope
      (parameters and locals). Shadows MS_Globals.
    - MS_Stack: the blocks allocated by declarations in the current scope (and,
      for the outermost scope of a function, its parameters). They are freed
      when the scope is left, making any pointer to them dangling, as in C.
    - MS_World: the external world (the same type as CoreInterp's). *)
record 'w MState =
  MS_Mem     :: MMem
  MS_Globals :: MEnv
  MS_Locals  :: MEnv
  MS_Stack   :: "nat list"
  MS_World   :: 'w

(* The model of an extern function: given the world, the memory and the
   argument values (scalars and pointers; aggregate arguments are passed as
   pointers to their bytes, exactly as in the C calling convention), it returns
   the new world, the new memory and the return value (None for a void
   function), or None if the call is undefined (the model's precondition does
   not hold, e.g. a dangling pointer argument). The model may allocate and
   free blocks of the memory. *)
type_synonym 'w MExtern = "'w \<Rightarrow> MMem \<Rightarrow> MVal list \<Rightarrow> ('w \<times> MMem \<times> MVal option) option"

(* Everything that is fixed for the duration of a run. The extern models are
   keyed by the MiniC function name (not the C name). *)
record 'w MContext =
  MC_Enc     :: MEncoding
  MC_Prog    :: MProgram
  MC_Externs :: "(string, 'w MExtern) fmap"

definition lookup_var :: "'w MState \<Rightarrow> string \<Rightarrow> MVar option" where
  "lookup_var st x =
    (case fmlookup (MS_Locals st) x of
       Some v \<Rightarrow> Some v
     | None \<Rightarrow> fmlookup (MS_Globals st) x)"

(* The block of a variable. *)
fun var_block :: "MVar \<Rightarrow> nat" where
  "var_block (MVar_Scalar _ b) = b"
| "var_block (MVar_Buf b) = b"


section \<open>Integer operations\<close>

(* Truncated division and modulo, as in C99 6.5.5 (and as Core's tdiv/tmod). *)
definition c_tdiv :: "int \<Rightarrow> int \<Rightarrow> int" where
  "c_tdiv i1 i2 = sgn i1 * sgn i2 * (\<bar>i1\<bar> div \<bar>i2\<bar>)"

definition c_tmod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "c_tmod i1 i2 = sgn i1 * (\<bar>i1\<bar> mod \<bar>i2\<bar>)"

(* Bitwise complement at a type: two's complement for signed types, max - i
   for unsigned (as Core's int_complement). *)
definition c_compl :: "Signedness \<Rightarrow> IntBits \<Rightarrow> int \<Rightarrow> int" where
  "c_compl s b i = (case s of Signed \<Rightarrow> - i - 1 | Unsigned \<Rightarrow> snd (int_range s b) - i)"

(* The mathematical result of an arithmetic or bitwise binop on two integers
   of the type (s, b), or None for undefined behaviour (division by zero,
   shift count out of range). The caller checks that the result fits. *)
definition eval_int_binop :: "CBinop \<Rightarrow> Signedness \<Rightarrow> IntBits \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int option" where
  "eval_int_binop op s b i1 i2 =
    (case op of
       CB_Add \<Rightarrow> Some (i1 + i2)
     | CB_Sub \<Rightarrow> Some (i1 - i2)
     | CB_Mul \<Rightarrow> Some (i1 * i2)
     | CB_Div \<Rightarrow> if i2 = 0 then None else Some (c_tdiv i1 i2)
     | CB_Mod \<Rightarrow> if i2 = 0 then None else Some (c_tmod i1 i2)
     | CB_BitAnd \<Rightarrow> Some (and i1 i2)
     | CB_BitOr \<Rightarrow> Some (or i1 i2)
     | CB_BitXor \<Rightarrow> Some (xor i1 i2)
     | CB_Shl \<Rightarrow> if 0 \<le> i2 \<and> nat i2 < bit_size b then Some (push_bit (nat i2) i1) else None
     | CB_Shr \<Rightarrow> if 0 \<le> i2 \<and> nat i2 < bit_size b then Some (drop_bit (nat i2) i1) else None
     | CB_Max \<Rightarrow> Some (max i1 i2)
     | _ \<Rightarrow> None)"

(* The comparisons, which yield a u8 0/1. *)
definition eval_cmp_binop :: "CBinop \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool option" where
  "eval_cmp_binop op i1 i2 =
    (case op of
       CB_Eq \<Rightarrow> Some (i1 = i2)
     | CB_Ne \<Rightarrow> Some (i1 \<noteq> i2)
     | CB_Lt \<Rightarrow> Some (i1 < i2)
     | CB_Le \<Rightarrow> Some (i1 \<le> i2)
     | CB_Gt \<Rightarrow> Some (i1 > i2)
     | CB_Ge \<Rightarrow> Some (i1 \<ge> i2)
     | _ \<Rightarrow> None)"

definition bool_val :: "bool \<Rightarrow> MVal" where
  "bool_val b = MV_U8 (if b then 1 else 0)"

fun is_shift :: "CBinop \<Rightarrow> bool" where
  "is_shift CB_Shl = True"
| "is_shift CB_Shr = True"
| "is_shift _ = False"

(* A binop on two values. Both operands must be integers of the same type,
   except that the count of a shift may have any integer type (as in Core,
   where is_valid_shift only looks at the count's value); the result has the
   left operand's type. There are no pointer comparisons: executable Core has
   no equality at extern types. Arithmetic results must fit the operand
   type. *)
definition eval_binop :: "CBinop \<Rightarrow> MVal \<Rightarrow> MVal \<Rightarrow> MVal option" where
  "eval_binop op v1 v2 =
    (case (v1, v2) of
       (MV_Int s1 b1 i1, MV_Int s2 b2 i2) \<Rightarrow>
         if \<not> is_shift op \<and> (s1 \<noteq> s2 \<or> b1 \<noteq> b2) then None
         else (case eval_cmp_binop op i1 i2 of
                 Some r \<Rightarrow> Some (bool_val r)
               | None \<Rightarrow>
                   (case eval_int_binop op s1 b1 i1 i2 of
                      None \<Rightarrow> None
                    | Some r \<Rightarrow> if int_fits s1 b1 r then Some (MV_Int s1 b1 r) else None))
     | _ \<Rightarrow> None)"

definition eval_unop :: "CUnop \<Rightarrow> MVal \<Rightarrow> MVal option" where
  "eval_unop op v =
    (case v of
       MV_Int s b i \<Rightarrow>
         (case op of
            CU_Neg \<Rightarrow> if int_fits s b (- i) then Some (MV_Int s b (- i)) else None
          | CU_Compl \<Rightarrow> Some (MV_Int s b (c_compl s b i))
          | CU_Not \<Rightarrow> Some (bool_val (i = 0)))
     | _ \<Rightarrow> None)"

(* Conversion to a C type: integer conversions must be in range (an
   out-of-range conversion to a signed type is implementation-defined in C,
   and the generated code never performs one; to keep MiniC simple the same
   rule is applied to unsigned targets, where C would wrap). Pointers convert
   only between the two pointer types. *)
definition eval_cast :: "CTy \<Rightarrow> MVal \<Rightarrow> MVal option" where
  "eval_cast ty v =
    (case (ty, v) of
       (CTy_Int s b, MV_Int _ _ i) \<Rightarrow> if int_fits s b i then Some (MV_Int s b i) else None
     | (CTy_Int _ _, MV_Ptr _) \<Rightarrow> None
     | (_, MV_Ptr p) \<Rightarrow> Some (MV_Ptr p)
     | (_, MV_Int _ _ _) \<Rightarrow> None)"


section \<open>Expressions\<close>

(* Expression evaluation is pure: it reads the state and returns a value, or
   None for undefined behaviour. *)
fun eval_expr :: "MEncoding \<Rightarrow> 'w MState \<Rightarrow> MExpr \<Rightarrow> MVal option" where
  "eval_expr enc st (ME_Int s b i) = (if int_fits s b i then Some (MV_Int s b i) else None)"
| "eval_expr enc st ME_PtrSize = Some (MV_U64 (int (enc_ptr_size enc)))"
| "eval_expr enc st (ME_Var x) =
    (case lookup_var st x of
       Some (MVar_Scalar ty b) \<Rightarrow> mem_load enc (MS_Mem st) ty (MP_Addr b 0)
     | _ \<Rightarrow> None)"
| "eval_expr enc st (ME_AddrOf x) =
    (case lookup_var st x of
       Some v \<Rightarrow> Some (MV_Ptr (MP_Addr (var_block v) 0))
     | None \<Rightarrow> None)"
| "eval_expr enc st (ME_Load ty e) =
    (case eval_expr enc st e of
       Some (MV_Ptr p) \<Rightarrow> mem_load enc (MS_Mem st) ty p
     | _ \<Rightarrow> None)"
| "eval_expr enc st (ME_Unop op e) =
    (case eval_expr enc st e of
       Some v \<Rightarrow> eval_unop op v
     | None \<Rightarrow> None)"
| "eval_expr enc st (ME_Binop op e1 e2) =
    (case eval_expr enc st e1 of
       None \<Rightarrow> None
     | Some v1 \<Rightarrow>
         (case eval_expr enc st e2 of
            None \<Rightarrow> None
          | Some v2 \<Rightarrow> eval_binop op v1 v2))"
| "eval_expr enc st (ME_Cast ty e) =
    (case eval_expr enc st e of
       Some v \<Rightarrow> eval_cast ty v
     | None \<Rightarrow> None)"
| "eval_expr enc st (ME_PtrAdd e1 e2) =
    (case eval_expr enc st e1 of
       Some (MV_Ptr p) \<Rightarrow>
         (case eval_expr enc st e2 of
            Some (MV_Int _ _ i) \<Rightarrow>
              (case ptr_add (MS_Mem st) p i of
                 Some p' \<Rightarrow> Some (MV_Ptr p')
               | None \<Rightarrow> None)
          | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

fun eval_exprs :: "MEncoding \<Rightarrow> 'w MState \<Rightarrow> MExpr list \<Rightarrow> MVal list option" where
  "eval_exprs enc st [] = Some []"
| "eval_exprs enc st (e # es) =
    (case eval_expr enc st e of
       None \<Rightarrow> None
     | Some v \<Rightarrow>
         (case eval_exprs enc st es of
            None \<Rightarrow> None
          | Some vs \<Rightarrow> Some (v # vs)))"

(* Evaluate to an integer (of any type), a non-negative integer, or a pointer. *)
definition eval_int :: "MEncoding \<Rightarrow> 'w MState \<Rightarrow> MExpr \<Rightarrow> int option" where
  "eval_int enc st e = (case eval_expr enc st e of Some (MV_Int _ _ i) \<Rightarrow> Some i | _ \<Rightarrow> None)"

definition eval_size :: "MEncoding \<Rightarrow> 'w MState \<Rightarrow> MExpr \<Rightarrow> nat option" where
  "eval_size enc st e = (case eval_int enc st e of Some i \<Rightarrow> if i \<ge> 0 then Some (nat i) else None | None \<Rightarrow> None)"

definition eval_ptr :: "MEncoding \<Rightarrow> 'w MState \<Rightarrow> MExpr \<Rightarrow> MPtr option" where
  "eval_ptr enc st e = (case eval_expr enc st e of Some (MV_Ptr p) \<Rightarrow> Some p | _ \<Rightarrow> None)"


section \<open>Statements\<close>

datatype MErr = MErr_UB | MErr_Fuel

(* How a statement (list) finished: normally, by `break`, or by `return`
   (with the returned value, if any). *)
datatype MOutcome = MO_Normal | MO_Break | MO_Return "MVal option"

(* Declare a variable: allocate a block of n undefined bytes, bind the name in
   the current scope and record the block in MS_Stack. *)
definition declare_var :: "'w MState \<Rightarrow> string \<Rightarrow> (nat \<Rightarrow> MVar) \<Rightarrow> nat \<Rightarrow> 'w MState" where
  "declare_var st x mk n =
    (let (m', b) = mem_alloc (MS_Mem st) (replicate n MB_Undef)
     in st \<lparr> MS_Mem := m',
             MS_Locals := fmupd x (mk b) (MS_Locals st),
             MS_Stack := b # MS_Stack st \<rparr>)"

(* Leaving a scope: free the blocks declared in the inner scope and restore the
   outer scope's bindings and stack list. None if one of the blocks is no
   longer live (which only a misbehaving extern model could cause). *)
definition scope_exit :: "'w MState \<Rightarrow> 'w MState \<Rightarrow> 'w MState option" where
  "scope_exit outer inner =
    (case mem_free_all (MS_Mem inner) (MS_Stack inner) of
       None \<Rightarrow> None
     | Some m \<Rightarrow> Some (inner \<lparr> MS_Mem := m,
                               MS_Locals := MS_Locals outer,
                               MS_Stack := MS_Stack outer \<rparr>))"

(* Bind the parameters of a function: each gets a fresh block holding its
   argument value. Fails (None) if an argument does not have its parameter's
   type. The resulting locals are only the parameters; the stack list is the
   parameter blocks. *)
fun bind_params :: "MEncoding \<Rightarrow> 'w MState \<Rightarrow> (string \<times> CTy) list \<Rightarrow> MVal list \<Rightarrow> 'w MState option" where
  "bind_params enc st [] [] = Some st"
| "bind_params enc st ((x, ty) # ps) (v # vs) =
    (if val_has_ty v ty then
       (let (m', b) = mem_alloc (MS_Mem st) (encode_val enc v)
        in bind_params enc (st \<lparr> MS_Mem := m',
                                 MS_Locals := fmupd x (MVar_Scalar ty b) (MS_Locals st),
                                 MS_Stack := b # MS_Stack st \<rparr>) ps vs)
     else None)"
| "bind_params enc st _ _ = None"

(* The return value of a function body, checked against the declared return
   type: a void function returns nothing; a non-void function must execute
   `return e` with a value of the right type (falling off the end of a
   non-void function is undefined, as in C when the value is used; `break`
   outside a loop is ill-formed). *)
definition check_return :: "CTy option \<Rightarrow> MOutcome \<Rightarrow> MVal option option" where
  "check_return retTy out =
    (case (retTy, out) of
       (None, MO_Normal) \<Rightarrow> Some None
     | (None, MO_Return None) \<Rightarrow> Some None
     | (Some ty, MO_Return (Some v)) \<Rightarrow> if val_has_ty v ty then Some (Some v) else None
     | _ \<Rightarrow> None)"

(* Store a scalar into a scalar variable. *)
definition assign_var :: "MEncoding \<Rightarrow> 'w MState \<Rightarrow> string \<Rightarrow> MVal \<Rightarrow> 'w MState option" where
  "assign_var enc st x v =
    (case lookup_var st x of
       Some (MVar_Scalar ty b) \<Rightarrow>
         (case mem_store enc (MS_Mem st) ty (MP_Addr b 0) v of
            Some m' \<Rightarrow> Some (st \<lparr> MS_Mem := m' \<rparr>)
          | None \<Rightarrow> None)
     | _ \<Rightarrow> None)"

(* Lift an optional value into the interpreter's result type (None is UB). *)
fun ub_or :: "'a option \<Rightarrow> MErr + 'a" where
  "ub_or None = Inl MErr_UB"
| "ub_or (Some x) = Inr x"

(* The interpreter proper. Every recursive call spends one unit of fuel.
    - exec_stmt / exec_stmts: one statement / a statement list in the current
      scope.
    - exec_scope: a statement list in a fresh scope (a C compound statement):
      the branches of an if, the body of a loop (once per iteration) and a
      block.
    - call_fun: a call to a function of the program, by name, with argument
      values. *)
function exec_stmt :: "nat \<Rightarrow> 'w MContext \<Rightarrow> 'w MState \<Rightarrow> MStmt \<Rightarrow> MErr + ('w MState \<times> MOutcome)"
  and exec_stmts :: "nat \<Rightarrow> 'w MContext \<Rightarrow> 'w MState \<Rightarrow> MStmt list \<Rightarrow> MErr + ('w MState \<times> MOutcome)"
  and exec_scope :: "nat \<Rightarrow> 'w MContext \<Rightarrow> 'w MState \<Rightarrow> MStmt list \<Rightarrow> MErr + ('w MState \<times> MOutcome)"
  and call_fun :: "nat \<Rightarrow> 'w MContext \<Rightarrow> 'w MState \<Rightarrow> string \<Rightarrow> MVal list \<Rightarrow> MErr + ('w MState \<times> MVal option)"
where
  "exec_stmt 0 _ _ _ = Inl MErr_Fuel"

| "exec_stmt (Suc fuel) ctx st (MS_DeclScalar x ty) =
    Inr (declare_var st x (MVar_Scalar ty) (ty_width (MC_Enc ctx) ty), MO_Normal)"

  (* A buffer must have at least one byte (a zero-length array is not allowed
     in C). *)
| "exec_stmt (Suc fuel) ctx st (MS_DeclBuf x e) =
    (case eval_size (MC_Enc ctx) st e of
       Some n \<Rightarrow> if n = 0 then Inl MErr_UB else Inr (declare_var st x MVar_Buf n, MO_Normal)
     | None \<Rightarrow> Inl MErr_UB)"

| "exec_stmt (Suc fuel) ctx st (MS_Assign x e) =
    (case eval_expr (MC_Enc ctx) st e of
       Some v \<Rightarrow> (case assign_var (MC_Enc ctx) st x v of
                   Some st' \<Rightarrow> Inr (st', MO_Normal)
                 | None \<Rightarrow> Inl MErr_UB)
     | None \<Rightarrow> Inl MErr_UB)"

| "exec_stmt (Suc fuel) ctx st (MS_Store ty pe e) =
    (case eval_ptr (MC_Enc ctx) st pe of
       Some p \<Rightarrow>
         (case eval_expr (MC_Enc ctx) st e of
            Some v \<Rightarrow>
              (case mem_store (MC_Enc ctx) (MS_Mem st) ty p v of
                 Some m' \<Rightarrow> Inr (st \<lparr> MS_Mem := m' \<rparr>, MO_Normal)
               | None \<Rightarrow> Inl MErr_UB)
          | None \<Rightarrow> Inl MErr_UB)
     | None \<Rightarrow> Inl MErr_UB)"

  (* memmove: the bytes are read (undefined ones included) before anything is
     written, so overlapping ranges are fine. *)
| "exec_stmt (Suc fuel) ctx st (MS_Copy de se ne) =
    (case eval_ptr (MC_Enc ctx) st de of
       Some d \<Rightarrow>
         (case eval_ptr (MC_Enc ctx) st se of
            Some s \<Rightarrow>
              (case eval_size (MC_Enc ctx) st ne of
                 Some n \<Rightarrow>
                   (case mem_read (MS_Mem st) s n of
                      Some bs \<Rightarrow>
                        (case mem_write (MS_Mem st) d bs of
                           Some m' \<Rightarrow> Inr (st \<lparr> MS_Mem := m' \<rparr>, MO_Normal)
                         | None \<Rightarrow> Inl MErr_UB)
                    | None \<Rightarrow> Inl MErr_UB)
               | None \<Rightarrow> Inl MErr_UB)
          | None \<Rightarrow> Inl MErr_UB)
     | None \<Rightarrow> Inl MErr_UB)"

| "exec_stmt (Suc fuel) ctx st (MS_Zero pe ne) =
    (case eval_ptr (MC_Enc ctx) st pe of
       Some p \<Rightarrow>
         (case eval_size (MC_Enc ctx) st ne of
            Some n \<Rightarrow>
              (case mem_write (MS_Mem st) p (replicate n (MB_Byte 0)) of
                 Some m' \<Rightarrow> Inr (st \<lparr> MS_Mem := m' \<rparr>, MO_Normal)
               | None \<Rightarrow> Inl MErr_UB)
          | None \<Rightarrow> Inl MErr_UB)
     | None \<Rightarrow> Inl MErr_UB)"

| "exec_stmt (Suc fuel) ctx st (MS_If c t e) =
    (case eval_int (MC_Enc ctx) st c of
       Some i \<Rightarrow> if i \<noteq> 0 then exec_scope fuel ctx st t else exec_scope fuel ctx st e
     | None \<Rightarrow> Inl MErr_UB)"

| "exec_stmt (Suc fuel) ctx st (MS_Loop body) =
    (case exec_scope fuel ctx st body of
       Inl err \<Rightarrow> Inl err
     | Inr (st', MO_Normal) \<Rightarrow> exec_stmt fuel ctx st' (MS_Loop body)
     | Inr (st', MO_Break) \<Rightarrow> Inr (st', MO_Normal)
     | Inr (st', MO_Return r) \<Rightarrow> Inr (st', MO_Return r))"

| "exec_stmt (Suc fuel) ctx st MS_Break = Inr (st, MO_Break)"

| "exec_stmt (Suc fuel) ctx st (MS_Block body) = exec_scope fuel ctx st body"

| "exec_stmt (Suc fuel) ctx st (MS_Call xopt f args) =
    (case eval_exprs (MC_Enc ctx) st args of
       None \<Rightarrow> Inl MErr_UB
     | Some vals \<Rightarrow>
         (case call_fun fuel ctx st f vals of
            Inl err \<Rightarrow> Inl err
          | Inr (st', ret) \<Rightarrow>
              (case xopt of
                 None \<Rightarrow> Inr (st', MO_Normal)
               | Some x \<Rightarrow>
                   (case ret of
                      Some v \<Rightarrow>
                        (case assign_var (MC_Enc ctx) st' x v of
                           Some st'' \<Rightarrow> Inr (st'', MO_Normal)
                         | None \<Rightarrow> Inl MErr_UB)
                    | None \<Rightarrow> Inl MErr_UB))))"

| "exec_stmt (Suc fuel) ctx st (MS_Return None) = Inr (st, MO_Return None)"

| "exec_stmt (Suc fuel) ctx st (MS_Return (Some e)) =
    (case eval_expr (MC_Enc ctx) st e of
       Some v \<Rightarrow> Inr (st, MO_Return (Some v))
     | None \<Rightarrow> Inl MErr_UB)"

| "exec_stmts 0 _ _ _ = Inl MErr_Fuel"
| "exec_stmts (Suc fuel) ctx st [] = Inr (st, MO_Normal)"
| "exec_stmts (Suc fuel) ctx st (s # ss) =
    (case exec_stmt fuel ctx st s of
       Inl err \<Rightarrow> Inl err
     | Inr (st', MO_Normal) \<Rightarrow> exec_stmts fuel ctx st' ss
     | Inr (st', out) \<Rightarrow> Inr (st', out))"

| "exec_scope 0 _ _ _ = Inl MErr_Fuel"
| "exec_scope (Suc fuel) ctx st body =
    (case exec_stmts fuel ctx (st \<lparr> MS_Stack := [] \<rparr>) body of
       Inl err \<Rightarrow> Inl err
     | Inr (st', out) \<Rightarrow>
         (case scope_exit st st' of
            Some st'' \<Rightarrow> Inr (st'', out)
          | None \<Rightarrow> Inl MErr_UB))"

| "call_fun 0 _ _ _ _ = Inl MErr_Fuel"
| "call_fun (Suc fuel) ctx st f vals =
    (case lookup_fun (MC_Prog ctx) f of
       None \<Rightarrow> Inl MErr_UB
     | Some fn \<Rightarrow>
         (case MF_Extern fn of
            Some _ \<Rightarrow>
              \<comment> \<open>An extern function: apply its model.\<close>
              (case fmlookup (MC_Externs ctx) f of
                 None \<Rightarrow> Inl MErr_UB
               | Some ext \<Rightarrow>
                   (case ext (MS_World st) (MS_Mem st) vals of
                      None \<Rightarrow> Inl MErr_UB
                    | Some (w', m', ret) \<Rightarrow>
                        Inr (st \<lparr> MS_World := w', MS_Mem := m' \<rparr>, ret)))
          | None \<Rightarrow>
              \<comment> \<open>A MiniC function: bind the parameters in a fresh frame, run the
                  body, check the outcome against the return type, and free
                  the frame.\<close>
              (case bind_params (MC_Enc ctx) (st \<lparr> MS_Locals := fmempty, MS_Stack := [] \<rparr>)
                                (MF_Params fn) vals of
                 None \<Rightarrow> Inl MErr_UB
               | Some st0 \<Rightarrow>
                   (case exec_stmts fuel ctx st0 (MF_Body fn) of
                      Inl err \<Rightarrow> Inl err
                    | Inr (st1, out) \<Rightarrow>
                        (case check_return (MF_Ret fn) out of
                           None \<Rightarrow> Inl MErr_UB
                         | Some ret \<Rightarrow>
                             (case scope_exit st st1 of
                                Some st2 \<Rightarrow> Inr (st2, ret)
                              | None \<Rightarrow> Inl MErr_UB))))))"

  by pat_completeness auto

termination by lexicographic_order


section \<open>Running a program\<close>

(* The state in which the (closed) size expressions of global buffers are
   evaluated: no variables at all. *)
definition closed_state :: "'w \<Rightarrow> 'w MState" where
  "closed_state w = \<lparr> MS_Mem = empty_mem, MS_Globals = fmempty, MS_Locals = fmempty,
                      MS_Stack = [], MS_World = w \<rparr>"

(* Allocate the global variables: static storage, so all bytes are zero. *)
fun alloc_globals :: "MEncoding \<Rightarrow> 'w \<Rightarrow> MMem \<Rightarrow> MEnv \<Rightarrow> (string \<times> MGlobal) list \<Rightarrow> (MMem \<times> MEnv) option" where
  "alloc_globals enc w m env [] = Some (m, env)"
| "alloc_globals enc w m env ((x, MG_Scalar ty) # gs) =
    (let (m', b) = mem_alloc m (replicate (ty_width enc ty) (MB_Byte 0))
     in alloc_globals enc w m' (fmupd x (MVar_Scalar ty b) env) gs)"
| "alloc_globals enc w m env ((x, MG_Buf e) # gs) =
    (case eval_size enc (closed_state w) e of
       Some n \<Rightarrow>
         if n = 0 then None
         else (let (m', b) = mem_alloc m (replicate n (MB_Byte 0))
               in alloc_globals enc w m' (fmupd x (MVar_Buf b) env) gs)
     | None \<Rightarrow> None)"

(* Run a program: allocate the globals, then call `main` with no arguments. The
   result is the final world and memory and main's return value (an int). *)
definition run_program ::
    "nat \<Rightarrow> MEncoding \<Rightarrow> (string, 'w MExtern) fmap \<Rightarrow> MProgram \<Rightarrow> 'w
     \<Rightarrow> MErr + ('w \<times> MMem \<times> MVal)" where
  "run_program fuel enc externs prog w =
    (case alloc_globals enc w empty_mem fmempty (MP_Globals prog) of
       None \<Rightarrow> Inl MErr_UB
     | Some (m, genv) \<Rightarrow>
         (let ctx = \<lparr> MC_Enc = enc, MC_Prog = prog, MC_Externs = externs \<rparr>;
              st = \<lparr> MS_Mem = m, MS_Globals = genv, MS_Locals = fmempty,
                     MS_Stack = [], MS_World = w \<rparr>
          in case call_fun fuel ctx st ''main'' [] of
               Inl err \<Rightarrow> Inl err
             | Inr (st', Some v) \<Rightarrow> Inr (MS_World st', MS_Mem st', v)
             | Inr (_, None) \<Rightarrow> Inl MErr_UB))"

end

theory MiniCExample
  imports MiniCSemantics
begin

(* ========================================================================== *)
(* MiniC: a hand-written example program                                      *)
(* ========================================================================== *)

(* This is the smoke test of the semantics: a MiniC program written by hand,
   in exactly the form the code generator of DESIGN.md (section 3) would
   produce from a Babylon program, together with MiniC-side models of the
   extern functions it calls, evaluated by `value` in the interpreter with the
   little-endian encoding. Stage 3b prints this program to C, compiles it with
   gcc, links it against Test.c, and compares the output with the list
   checked at the end of this theory.

   The Babylon program it corresponds to is roughly:

     type Point = {x: i32, y: i32};
     datatype Shape = Circle(i32) | Rect(Point);
     const K: i32 = 100;
     const greeting: u8[] = "hi";

     function area(s: Shape): i32 {
       match s { case Circle(r) => return 3 * r * r;  case Rect(p) => return p.x * p.y; }
     }
     function sum3(a: i32[3]): i32 { var acc = 0; var i: u64 = 0; while i < 3 { acc = acc + a[i]; i = i + 1; } return acc; }
     function incr(ref r: i32) { r = r + 1; }
     function swap_elems<T>(ref a: T[*], i: u64, j: u64) { swap a[i], a[j]; }   // generic: uses only sizeof(T)
     function main() {
       print_i32(area(Rect{5, 7}));              // 35
       print_i32(area(Circle(3)));               // 27
       print_i32(sum3([1, 2, 3]));               // 6
       var v = 41; incr(v); print_i32(v);        // 42
       var arr: i32[*]; alloc_array(arr, 3);
       arr[0] = 10; arr[1] = 20; arr[2] = 30;
       swap_elems(arr, 0, 2);
       print_i32(arr[0]); print_u64(sizeof(arr)); // 30, 3
       free_array(arr); print_u64(sizeof(arr));   // 0
       print_bool(v > 30 && v == 42);             // true (1)
       print_string(greeting);                    // bytes 104, 105
       print_i32(K + v);                          // 142
     }

   (The generic function is written with an explicit descriptor-free
   interface, `swap_elems(size$T, p, n0, i, j)`, to keep the example short; the
   point is that its body computes every address from the run-time size.) *)


section \<open>Abbreviations\<close>

abbreviation i32 :: "int \<Rightarrow> MExpr" where "i32 n \<equiv> ME_Int Signed IntBits_32 n"
abbreviation u64 :: "int \<Rightarrow> MExpr" where "u64 n \<equiv> ME_Int Unsigned IntBits_64 n"
abbreviation u8 :: "int \<Rightarrow> MExpr" where "u8 n \<equiv> ME_Int Unsigned IntBits_8 n"

abbreviation ld :: "CTy \<Rightarrow> MExpr \<Rightarrow> MExpr" where "ld ty e \<equiv> ME_Load ty e"
abbreviation addr :: "string \<Rightarrow> MExpr" where "addr x \<equiv> ME_AddrOf x"
abbreviation var :: "string \<Rightarrow> MExpr" where "var x \<equiv> ME_Var x"
(* p + n for a constant n (named offp to avoid clashing with bound variables) *)
abbreviation offp :: "MExpr \<Rightarrow> int \<Rightarrow> MExpr" where "offp p n \<equiv> ME_PtrAdd p (u64 n)"
(* the size of an array descriptor with one dimension: pointer size + 8 *)
abbreviation desc1_size :: MExpr where
  "desc1_size \<equiv> ME_Binop CB_Add ME_PtrSize (u64 8)"


section \<open>The functions\<close>

(* area(s: char pointer): int32_t   -- s points to a Shape (9 bytes: u8 tag, then
   the payload: an i32 for Circle, or {x: i32, y: i32} for Rect). *)
definition area_fun :: MFun where
  "area_fun = \<lparr>
     MF_Name = ''area'',
     MF_Params = [(''s'', CTy_CharPtr)],
     MF_Ret = Some CTy_I32,
     MF_Body = [
       MS_DeclScalar ''tag'' CTy_U8,
       MS_Assign ''tag'' (ld CTy_U8 (var ''s'')),
       MS_DeclScalar ''res'' CTy_I32,
       MS_If (ME_Binop CB_Eq (var ''tag'') (u8 0))
         [ MS_DeclScalar ''r'' CTy_I32,
           MS_Assign ''r'' (ld CTy_I32 (offp (var ''s'') 1)),
           MS_Assign ''res'' (ME_Binop CB_Mul (ME_Binop CB_Mul (i32 3) (var ''r'')) (var ''r'')) ]
         [ MS_If (ME_Binop CB_Eq (var ''tag'') (u8 1))
             [ MS_Assign ''res'' (ME_Binop CB_Mul (ld CTy_I32 (offp (var ''s'') 1))
                                                  (ld CTy_I32 (offp (var ''s'') 5))) ]
             [ MS_Trap ] ],
       MS_Return (Some (var ''res'')) ],
     MF_Extern = None \<rparr>"

(* sum3(a: char pointer): int32_t   -- a points to an i32[3] (12 bytes). *)
definition sum3_fun :: MFun where
  "sum3_fun = \<lparr>
     MF_Name = ''sum3'',
     MF_Params = [(''a'', CTy_CharPtr)],
     MF_Ret = Some CTy_I32,
     MF_Body = [
       MS_DeclScalar ''acc'' CTy_I32,
       MS_Assign ''acc'' (i32 0),
       MS_DeclScalar ''i'' CTy_U64,
       MS_Assign ''i'' (u64 0),
       MS_Loop [
         MS_If (ME_Unop CU_Not (ME_Binop CB_Lt (var ''i'') (u64 3))) [MS_Break] [],
         MS_Assign ''acc'' (ME_Binop CB_Add (var ''acc'')
                              (ld CTy_I32 (ME_PtrAdd (var ''a'') (ME_Binop CB_Mul (u64 4) (var ''i''))))),
         MS_Assign ''i'' (ME_Binop CB_Add (var ''i'') (u64 1)) ],
       MS_Return (Some (var ''acc'')) ],
     MF_Extern = None \<rparr>"

(* incr(r: char pointer)   -- a `ref r: i32` parameter: r points to an int32_t. *)
definition incr_fun :: MFun where
  "incr_fun = \<lparr>
     MF_Name = ''incr'',
     MF_Params = [(''r'', CTy_CharPtr)],
     MF_Ret = None,
     MF_Body = [
       MS_Store CTy_I32 (var ''r'') (ME_Binop CB_Add (ld CTy_I32 (var ''r'')) (i32 1)),
       MS_Return None ],
     MF_Extern = None \<rparr>"

(* swap_elems(size$T: uint64_t, p: char pointer, i: uint64_t, j: uint64_t)
   -- generic in T: p points to an array of elements of size$T bytes; swap
   elements i and j through a VLA temporary of size$T bytes. Every address is
   computed from the run-time size, as generic code must. *)
definition swap_elems_fun :: MFun where
  "swap_elems_fun = \<lparr>
     MF_Name = ''swap_elems'',
     MF_Params = [(''szT'', CTy_U64), (''p'', CTy_CharPtr), (''i'', CTy_U64), (''j'', CTy_U64)],
     MF_Ret = None,
     MF_Body = [
       MS_DeclScalar ''pi'' CTy_CharPtr,
       MS_Assign ''pi'' (ME_PtrAdd (var ''p'') (ME_Binop CB_Mul (var ''szT'') (var ''i''))),
       MS_DeclScalar ''pj'' CTy_CharPtr,
       MS_Assign ''pj'' (ME_PtrAdd (var ''p'') (ME_Binop CB_Mul (var ''szT'') (var ''j''))),
       MS_DeclBuf ''tmp'' (ME_Binop CB_Max (u64 1) (var ''szT'')),
       MS_Copy (addr ''tmp'') (var ''pi'') (var ''szT''),
       MS_Copy (var ''pi'') (var ''pj'') (var ''szT''),
       MS_Copy (var ''pj'') (addr ''tmp'') (var ''szT''),
       MS_Return None ],
     MF_Extern = None \<rparr>"

(* The extern functions of Test.c, with the prototypes of docs/c-interface.md:
     void print_i32(int32_t); void print_u64(uint64_t); void print_bool(uint8_t);
     void print_string(char *s);                       -- s: a u8[] descriptor
     void alloc_array(uint64_t size$T, char *arr, uint64_t n);   -- arr: a T[*] descriptor
     void free_array(uint64_t size$T, char *arr); *)
definition extern_fun :: "string \<Rightarrow> (string \<times> CTy) list \<Rightarrow> MFun" where
  "extern_fun name params = \<lparr>
     MF_Name = name, MF_Params = params, MF_Ret = None, MF_Body = [], MF_Extern = Some name \<rparr>"

definition print_i32_fun :: MFun where
  "print_i32_fun = extern_fun ''print_i32'' [(''x'', CTy_I32)]"
definition print_u64_fun :: MFun where
  "print_u64_fun = extern_fun ''print_u64'' [(''x'', CTy_U64)]"
definition print_bool_fun :: MFun where
  "print_bool_fun = extern_fun ''print_bool'' [(''b'', CTy_U8)]"
definition print_string_fun :: MFun where
  "print_string_fun = extern_fun ''print_string'' [(''s'', CTy_CharPtr)]"
definition alloc_array_fun :: MFun where
  "alloc_array_fun = extern_fun ''alloc_array'' [(''szT'', CTy_U64), (''arr'', CTy_CharPtr), (''n'', CTy_U64)]"
definition free_array_fun :: MFun where
  "free_array_fun = extern_fun ''free_array'' [(''szT'', CTy_U64), (''arr'', CTy_CharPtr)]"

(* main: initialise the globals (DESIGN.md 3.7), run the program, return 0. *)
definition main_fun :: MFun where
  "main_fun = \<lparr>
     MF_Name = ''main'',
     MF_Params = [],
     MF_Ret = Some CTy_I32,
     MF_Body = [
       \<comment> \<open>global initialisation: K = 100; greeting = ''hi'' (data bytes 104 105 0,
           then the descriptor: pointer to the data, size 3)\<close>
       MS_Assign ''K'' (i32 100),
       MS_Store CTy_U8 (addr ''greeting_data'') (u8 104),
       MS_Store CTy_U8 (offp (addr ''greeting_data'') 1) (u8 105),
       MS_Store CTy_U8 (offp (addr ''greeting_data'') 2) (u8 0),
       MS_Store CTy_CharPtr (addr ''greeting'') (addr ''greeting_data''),
       MS_Store CTy_U64 (ME_PtrAdd (addr ''greeting'') ME_PtrSize) (u64 3),

       \<comment> \<open>the record {5, 7} (8 bytes) and the variant Rect(rec) (9 bytes)\<close>
       MS_DeclBuf ''rec'' (u64 8),
       MS_Store CTy_I32 (addr ''rec'') (i32 5),
       MS_Store CTy_I32 (offp (addr ''rec'') 4) (i32 7),
       MS_DeclBuf ''sh'' (u64 9),
       MS_Store CTy_U8 (addr ''sh'') (u8 1),
       MS_Copy (offp (addr ''sh'') 1) (addr ''rec'') (u64 8),
       MS_DeclScalar ''a'' CTy_I32,
       MS_Call (Some ''a'') ''area'' [addr ''sh''],
       MS_Call None ''print_i32'' [var ''a''],

       \<comment> \<open>the variant Circle(3): tag 0, payload 3, remaining 4 bytes undefined\<close>
       MS_DeclBuf ''sh2'' (u64 9),
       MS_Store CTy_U8 (addr ''sh2'') (u8 0),
       MS_Store CTy_I32 (offp (addr ''sh2'') 1) (i32 3),
       MS_DeclBuf ''sh3'' (u64 9),
       MS_Copy (addr ''sh3'') (addr ''sh2'') (u64 9),   \<comment> \<open>copies undefined bytes: allowed\<close>
       MS_DeclScalar ''a2'' CTy_I32,
       MS_Call (Some ''a2'') ''area'' [addr ''sh3''],
       MS_Call None ''print_i32'' [var ''a2''],

       \<comment> \<open>the fixed array [1, 2, 3]\<close>
       MS_DeclBuf ''arr3'' (u64 12),
       MS_Store CTy_I32 (addr ''arr3'') (i32 1),
       MS_Store CTy_I32 (offp (addr ''arr3'') 4) (i32 2),
       MS_Store CTy_I32 (offp (addr ''arr3'') 8) (i32 3),
       MS_DeclScalar ''a3'' CTy_I32,
       MS_Call (Some ''a3'') ''sum3'' [addr ''arr3''],
       MS_Call None ''print_i32'' [var ''a3''],

       \<comment> \<open>var v = 41; incr(ref v)\<close>
       MS_DeclScalar ''v'' CTy_I32,
       MS_Assign ''v'' (i32 41),
       MS_Call None ''incr'' [addr ''v''],
       MS_Call None ''print_i32'' [var ''v''],

       \<comment> \<open>var arr: i32[*] (default: a zeroed descriptor); alloc_array(arr, 3)\<close>
       MS_DeclBuf ''arr'' desc1_size,
       MS_Zero (addr ''arr'') desc1_size,
       MS_Call None ''alloc_array'' [u64 4, addr ''arr'', u64 3],
       \<comment> \<open>arr[0] = 10; arr[1] = 20; arr[2] = 30  (data pointer loaded from the descriptor)\<close>
       MS_DeclScalar ''data'' CTy_CharPtr,
       MS_Assign ''data'' (ld CTy_CharPtr (addr ''arr'')),
       MS_Store CTy_I32 (var ''data'') (i32 10),
       MS_Store CTy_I32 (ME_PtrAdd (var ''data'') (ME_Binop CB_Mul (u64 4) (u64 1))) (i32 20),
       MS_Store CTy_I32 (ME_PtrAdd (var ''data'') (ME_Binop CB_Mul (u64 4) (u64 2))) (i32 30),
       \<comment> \<open>swap_elems<i32>(arr, 0, 2)\<close>
       MS_Call None ''swap_elems'' [u64 4, ld CTy_CharPtr (addr ''arr''), u64 0, u64 2],
       MS_Call None ''print_i32'' [ld CTy_I32 (ld CTy_CharPtr (addr ''arr''))],
       MS_Call None ''print_u64'' [ld CTy_U64 (ME_PtrAdd (addr ''arr'') ME_PtrSize)],
       \<comment> \<open>free_array(arr); sizeof(arr) is now 0\<close>
       MS_Call None ''free_array'' [u64 4, addr ''arr''],
       MS_Call None ''print_u64'' [ld CTy_U64 (ME_PtrAdd (addr ''arr'') ME_PtrSize)],

       \<comment> \<open>print_bool(v > 30 && v == 42), with short-circuit evaluation\<close>
       MS_DeclScalar ''t'' CTy_U8,
       MS_Assign ''t'' (ME_Binop CB_Gt (var ''v'') (i32 30)),
       MS_If (var ''t'') [ MS_Assign ''t'' (ME_Binop CB_Eq (var ''v'') (i32 42)) ] [],
       MS_Call None ''print_bool'' [var ''t''],

       \<comment> \<open>print_string(greeting); print_i32(K + v)\<close>
       MS_Call None ''print_string'' [addr ''greeting''],
       MS_Call None ''print_i32'' [ME_Binop CB_Add (var ''K'') (var ''v'')],

       MS_Return (Some (i32 0)) ],
     MF_Extern = None \<rparr>"

definition example_prog :: MProgram where
  "example_prog = \<lparr>
     MP_Globals = [ (''K'', MG_Scalar CTy_I32),
                    (''greeting_data'', MG_Buf (u64 3)),
                    (''greeting'', MG_Buf desc1_size) ],
     MP_Funcs = [ area_fun, sum3_fun, incr_fun, swap_elems_fun,
                  print_i32_fun, print_u64_fun, print_bool_fun, print_string_fun,
                  alloc_array_fun, free_array_fun, main_fun ] \<rparr>"

lemma example_prog_wf: "program_wf example_prog"
  by eval


section \<open>Models of the extern functions\<close>

(* The world is the list of integers printed so far (print_bool prints 0/1,
   print_string prints the byte values of the string). *)
type_synonym World = "int list"

(* print_i32 / print_u64 / print_bool: append the argument. *)
definition print_int_model :: "World MExtern" where
  "print_int_model w m args =
    (case args of
       [MV_Int _ _ i] \<Rightarrow> Some (w @ [i], m, None)
     | _ \<Rightarrow> None)"

(* Read the bytes of a null-terminated string from memory (at most `fuel`
   bytes), as integers. *)
fun read_cstring :: "nat \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> MPtr \<Rightarrow> int list option" where
  "read_cstring 0 enc m p = None"
| "read_cstring (Suc n) enc m p =
    (case mem_load enc m CTy_U8 p of
       Some (MV_Int _ _ c) \<Rightarrow>
         if c = 0 then Some []
         else (case ptr_add m p 1 of
                 Some p' \<Rightarrow> map_option ((#) c) (read_cstring n enc m p')
               | None \<Rightarrow> None)
     | _ \<Rightarrow> None)"

(* print_string(s): s points to a u8[] descriptor; print the bytes of the
   string its data pointer points to, up to the null terminator. *)
definition print_string_model :: "MEncoding \<Rightarrow> World MExtern" where
  "print_string_model enc w m args =
    (case args of
       [MV_Ptr s] \<Rightarrow>
         (case mem_load enc m CTy_CharPtr s of
            Some (MV_Ptr data) \<Rightarrow>
              (case read_cstring 1000 enc m data of
                 Some cs \<Rightarrow> Some (w @ cs, m, None)
               | None \<Rightarrow> None)
          | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

(* alloc_array(size$T, arr, n), the Test.c version (always succeeds): allocate
   a zero-filled block of n * size$T bytes (none if n = 0: the pointer stays
   null, as Test.c does) and write the descriptor (pointer, then n). *)
definition alloc_array_model :: "MEncoding \<Rightarrow> World MExtern" where
  "alloc_array_model enc w m args =
    (case args of
       [MV_Int Unsigned IntBits_64 sz, MV_Ptr arr, MV_Int Unsigned IntBits_64 n] \<Rightarrow>
         (let (m1, p) = (if n = 0 then (m, MP_Null)
                         else (let (m', b) = mem_alloc m (replicate (nat n * nat sz) (MB_Byte 0))
                               in (m', MP_Addr b 0)))
          in case mem_store enc m1 CTy_CharPtr arr (MV_Ptr p) of
               None \<Rightarrow> None
             | Some m2 \<Rightarrow>
                 (case ptr_add m2 arr (int (enc_ptr_size enc)) of
                    None \<Rightarrow> None
                  | Some arr' \<Rightarrow>
                      (case mem_store enc m2 CTy_U64 arr' (MV_U64 n) of
                         None \<Rightarrow> None
                       | Some m3 \<Rightarrow> Some (w, m3, None))))
     | _ \<Rightarrow> None)"

(* free_array(size$T, arr): free the block the descriptor points to (nothing
   if null), then zero the descriptor. *)
definition free_array_model :: "MEncoding \<Rightarrow> World MExtern" where
  "free_array_model enc w m args =
    (case args of
       [MV_Int Unsigned IntBits_64 sz, MV_Ptr arr] \<Rightarrow>
         (case mem_load enc m CTy_CharPtr arr of
            Some (MV_Ptr p) \<Rightarrow>
              (case (case p of MP_Null \<Rightarrow> Some m
                            | MP_Addr b off \<Rightarrow> if off = 0 then mem_free m b else None) of
                 None \<Rightarrow> None
               | Some m1 \<Rightarrow>
                   (case mem_write m1 arr (replicate (enc_ptr_size enc + 8) (MB_Byte 0)) of
                      None \<Rightarrow> None
                    | Some m2 \<Rightarrow> Some (w, m2, None)))
          | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

definition example_externs :: "MEncoding \<Rightarrow> (string, World MExtern) fmap" where
  "example_externs enc = fmap_of_list
     [ (''print_i32'', print_int_model),
       (''print_u64'', print_int_model),
       (''print_bool'', print_int_model),
       (''print_string'', print_string_model enc),
       (''alloc_array'', alloc_array_model enc),
       (''free_array'', free_array_model enc) ]"


section \<open>Running it\<close>

(* The documented result: the program prints
     35   area(Rect{5, 7})
     27   area(Circle(3))
     6    sum3([1, 2, 3])
     42   v after incr
     30   arr[0] after the swap
     3    sizeof(arr)
     0    sizeof(arr) after free
     1    true
     104 105   the bytes of "hi"
     142  K + v
   and returns 0. *)
definition example_expected :: World where
  "example_expected = [35, 27, 6, 42, 30, 3, 0, 1, 104, 105, 142]"

definition example_result :: "MErr + (World \<times> MMem \<times> MVal)" where
  "example_result = run_program 100000 le_encoding (example_externs le_encoding) example_prog []"

lemma example_run:
  "case example_result of
     Inr (w, m, v) \<Rightarrow> w = example_expected \<and> v = MV_Int Signed IntBits_32 0
   | Inl _ \<Rightarrow> False"
  by eval

(* The same, by value, for inspection: *)
value "case example_result of Inr (w, m, v) \<Rightarrow> Some (w, v) | Inl _ \<Rightarrow> None"

end

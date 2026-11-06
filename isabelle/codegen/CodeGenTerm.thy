theory CodeGenTerm
  imports CodeGenEnv
begin

(* ========================================================================== *)
(* The code generator: terms, places, calls, lazy references                  *)
(* (minic/DESIGN.md, sections 3.3 to 3.5)                                     *)
(* ========================================================================== *)

(* lower_term cg tm gives the MiniC statements that compute a Core term and
   its result expression: the value of a scalar-typed term, the place (a
   char * expression) of an aggregate-typed term. lower_addr cg tm gives the
   address of a term of any type: for an lvalue, the address of the Core
   lvalue (through its representation, projections and casts); for a
   non-lvalue aggregate its place; for a non-lvalue scalar the address of a
   temporary holding its value (used to pass an argument to a parameter of
   type-variable type, which the callee reads through a pointer). The two
   are mutually recursive with lower_call, the call of section 3.4. *)


section \<open>Small helpers\<close>

(* Store a value or copy bytes to an address, by the type. *)
definition store_at :: "CGEnv \<Rightarrow> CoreType \<Rightarrow> MExpr \<Rightarrow> MExpr \<Rightarrow> MStmt" where
  "store_at cg ty dst e =
    (case scalar_ty ty of
       Some cty \<Rightarrow> MS_Store cty dst e
     | None \<Rightarrow> MS_Copy dst e (cg_size cg ty))"

(* The value at an address: a load for a scalar type, the address itself
   (a place) for an aggregate. *)
definition load_at :: "CoreType \<Rightarrow> MExpr \<Rightarrow> MExpr" where
  "load_at ty a = (case scalar_ty ty of Some cty \<Rightarrow> ME_Load cty a | None \<Rightarrow> a)"

(* A fresh scalar or buffer temporary for a value of the given type, with
   its declaration. *)
definition temp_for :: "CGEnv \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> (string \<times> MStmt) CG" where
  "temp_for cg hint ty = do {
     tmp \<leftarrow> fresh_name (CG_Fun cg) hint;
     cg_return (tmp, (case scalar_ty ty of
                        Some cty \<Rightarrow> MS_DeclScalar tmp cty
                      | None \<Rightarrow> MS_DeclBuf tmp (buf_size (cg_size cg ty))))
   }"

(* The result expression for a temporary: its value or its place. *)
definition temp_result :: "CoreType \<Rightarrow> string \<Rightarrow> MExpr" where
  "temp_result ty tmp = (case scalar_ty ty of Some _ \<Rightarrow> ME_Var tmp | None \<Rightarrow> ME_AddrOf tmp)"

(* The address of a temporary (scalar or buffer): ME_AddrOf. The statement
   that stores a result into a temporary. *)
definition temp_store :: "CGEnv \<Rightarrow> CoreType \<Rightarrow> string \<Rightarrow> MExpr \<Rightarrow> MStmt" where
  "temp_store cg ty tmp e =
    (case scalar_ty ty of
       Some _ \<Rightarrow> MS_Assign tmp e
     | None \<Rightarrow> MS_Copy (ME_AddrOf tmp) e (cg_size cg ty))"

(* Build a descriptor for a fixed array at place p, cast to the descriptor
   type toTy (section 3.3): a buffer holding the data pointer p and the
   fixed dimensions. *)
definition build_desc :: "CGEnv \<Rightarrow> CoreDimension list \<Rightarrow> CoreType \<Rightarrow> MExpr \<Rightarrow> (MStmt list \<times> MExpr) CG" where
  "build_desc cg dimsF toTy p = do {
     tmp \<leftarrow> fresh_name (CG_Fun cg) ''desc'';
     cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg toTy)),
                 MS_Store CTy_CharPtr (ME_AddrOf tmp) p]
                @ map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (dim_off k))
                                     (u64_lit (dim_size (dimsF ! k))))
                      [0..<length dimsF],
                ME_AddrOf tmp)
   }"

(* An array cast of a place (section 3.3): the identity between dimensions
   of the same category; a descriptor temporary from fixed to descriptor;
   the data pointer from descriptor to fixed. *)
definition cast_place :: "CGEnv \<Rightarrow> CoreType \<Rightarrow> CoreType \<Rightarrow> MExpr \<Rightarrow> (MStmt list \<times> MExpr) CG" where
  "cast_place cg fromTy toTy p =
    (case (fromTy, toTy) of
       (CoreTy_Array _ dimsF, CoreTy_Array _ dimsT) \<Rightarrow>
         if dims_all_fixed dimsF = dims_all_fixed dimsT then cg_return ([], p)
         else if dims_all_fixed dimsF then build_desc cg dimsF toTy p
         else cg_return ([], desc_data p)
     | _ \<Rightarrow> internal cg ''array cast between non-array types'')"

(* A cast of a term's result (value or place) to a type: a numeric cast of
   a value, or an array cast of a place. *)
definition cast_result :: "CGEnv \<Rightarrow> CoreType \<Rightarrow> CoreType \<Rightarrow> MExpr \<Rightarrow> (MStmt list \<times> MExpr) CG" where
  "cast_result cg fromTy toTy e =
    (case scalar_ty toTy of
       Some cty \<Rightarrow> cg_return ([], ME_Cast cty e)
     | None \<Rightarrow> cast_place cg fromTy toTy e)"

fun unop_of :: "CoreUnop \<Rightarrow> CUnop" where
  "unop_of CoreUnop_Negate = CU_Neg"
| "unop_of CoreUnop_Complement = CU_Compl"
| "unop_of CoreUnop_Not = CU_Not"

(* The MiniC operator of a Core binary operator; None for the three
   short-circuit operators, which lower to statements. *)
fun binop_of :: "CoreBinop \<Rightarrow> CBinop option" where
  "binop_of CoreBinop_Add = Some CB_Add"
| "binop_of CoreBinop_Subtract = Some CB_Sub"
| "binop_of CoreBinop_Multiply = Some CB_Mul"
| "binop_of CoreBinop_Divide = Some CB_Div"
| "binop_of CoreBinop_Modulo = Some CB_Mod"
| "binop_of CoreBinop_BitAnd = Some CB_BitAnd"
| "binop_of CoreBinop_BitOr = Some CB_BitOr"
| "binop_of CoreBinop_BitXor = Some CB_BitXor"
| "binop_of CoreBinop_ShiftLeft = Some CB_Shl"
| "binop_of CoreBinop_ShiftRight = Some CB_Shr"
| "binop_of CoreBinop_Equal = Some CB_Eq"
| "binop_of CoreBinop_NotEqual = Some CB_Ne"
| "binop_of CoreBinop_Less = Some CB_Lt"
| "binop_of CoreBinop_LessEqual = Some CB_Le"
| "binop_of CoreBinop_Greater = Some CB_Gt"
| "binop_of CoreBinop_GreaterEqual = Some CB_Ge"
| "binop_of CoreBinop_And = None"
| "binop_of CoreBinop_Or = None"
| "binop_of CoreBinop_Implies = None"


section \<open>Variables and lazy references\<close>

(* The address of a non-lazy representation. *)
fun rep_addr :: "VarRep \<Rightarrow> MExpr option" where
  "rep_addr (VR_Scalar x _) = Some (ME_AddrOf x)"
| "rep_addr (VR_Buf x) = Some (ME_AddrOf x)"
| "rep_addr (VR_Ptr x) = Some (ME_Var x)"
| "rep_addr (VR_Lazy _) = None"

(* The address denoted by a lazy reference, recomputed at each use
   (section 3.5): the base's address, then offsets, element addresses
   (through the descriptor of an allocatable array, which may have been
   reallocated since the declaration) and casts. *)
fun lazy_addr :: "CGEnv \<Rightarrow> LazyLv \<Rightarrow> (MStmt list \<times> MExpr) CG" where
  "lazy_addr cg (LL_Base rep _) =
    (case rep_addr rep of
       Some a \<Rightarrow> cg_return ([], a)
     | None \<Rightarrow> internal cg ''lazy reference with a lazy base'')"
| "lazy_addr cg (LL_Field ll f _) = do {
    (S, p) \<leftarrow> lazy_addr cg ll;
    (case ll_type ll of
       CoreTy_Record flds \<Rightarrow> cg_return (S, ptr_add p (field_off (CG_TyEnv cg) flds f))
     | _ \<Rightarrow> internal cg ''field of a non-record'')
   }"
| "lazy_addr cg (LL_Payload ll c _) = do {
    (S, p) \<leftarrow> lazy_addr cg ll;
    (case ll_type ll of
       CoreTy_Datatype dtName _ \<Rightarrow> cg_return (S, ptr_add p (tag_off (CG_TyEnv cg) dtName))
     | _ \<Rightarrow> internal cg ''payload of a non-variant'')
   }"
| "lazy_addr cg (LL_Index ll vs _) = do {
    (S, p) \<leftarrow> lazy_addr cg ll;
    (case ll_type ll of
       CoreTy_Array elemTy dims \<Rightarrow>
         cg_return (S, elem_addr (CG_TyEnv cg) elemTy dims p (map ME_Var vs))
     | _ \<Rightarrow> internal cg ''index of a non-array'')
   }"
| "lazy_addr cg (LL_Cast ll ty) = do {
    (S, p) \<leftarrow> lazy_addr cg ll;
    (S', p') \<leftarrow> cast_place cg (ll_type ll) ty p;
    cg_return (S @ S', p')
   }"

(* Reading a variable of the given type through its representation. *)
definition read_rep :: "CGEnv \<Rightarrow> VarRep \<Rightarrow> CoreType \<Rightarrow> (MStmt list \<times> MExpr) CG" where
  "read_rep cg rep ty =
    (case rep of
       VR_Scalar x _ \<Rightarrow> cg_return ([], ME_Var x)
     | VR_Buf x \<Rightarrow> cg_return ([], ME_AddrOf x)
     | VR_Ptr x \<Rightarrow> cg_return ([], load_at ty (ME_Var x))
     | VR_Lazy ll \<Rightarrow> do { (S, a) \<leftarrow> lazy_addr cg ll; cg_return (S, load_at ty a) })"

(* The address of a variable through its representation. *)
definition addr_rep :: "CGEnv \<Rightarrow> VarRep \<Rightarrow> (MStmt list \<times> MExpr) CG" where
  "addr_rep cg rep =
    (case rep of
       VR_Lazy ll \<Rightarrow> lazy_addr cg ll
     | _ \<Rightarrow> cg_return ([], the (rep_addr rep)))"

definition lookup_var :: "CGEnv \<Rightarrow> string \<Rightarrow> VarRep CG" where
  "lookup_var cg x = cg_lift (CG_Fun cg) (''unknown variable '' @ x) (fmlookup (CG_Vars cg) x)"


section \<open>Matches\<close>

(* The if chain of a match (section 3.3): each arm but the last is guarded
   by its condition; the last arm is unconditional; a wildcard arm ends the
   chain (Core never reaches the arms after it). Every arm body is a scope. *)
fun if_chain :: "(MExpr option \<times> MStmt list) list \<Rightarrow> MStmt list" where
  "if_chain [] = []"
| "if_chain [(_, S)] = [MS_Block S]"
| "if_chain ((Some c, S) # rest) = [MS_If c S (if_chain rest)]"
| "if_chain ((None, S) # rest) = [MS_Block S]"

(* The value a flat pattern is compared with (None for a wildcard). *)
definition arm_cond :: "CGEnv \<Rightarrow> CoreType \<Rightarrow> MExpr \<Rightarrow> CorePattern \<Rightarrow> MExpr option CG" where
  "arm_cond cg scrutTy tag pat =
    (case pat of
       CorePat_Wildcard \<Rightarrow> cg_return None
     | CorePat_Bool b \<Rightarrow> cg_return (Some (ME_Binop CB_Eq tag (ME_Int Unsigned IntBits_8 (if b then 1 else 0))))
     | CorePat_Int i \<Rightarrow>
         (case scrutTy of
            CoreTy_FiniteInt s b \<Rightarrow> cg_return (Some (ME_Binop CB_Eq tag (ME_Int s b i)))
          | _ \<Rightarrow> internal cg ''integer pattern on a non-integer scrutinee'')
     | CorePat_Variant c p \<Rightarrow>
         if p \<noteq> CorePat_Wildcard then internal cg ''non-flat pattern''
         else (case scrutTy of
                 CoreTy_Datatype dtName _ \<Rightarrow>
                   cg_return (Some (ME_Binop CB_Eq tag (tag_lit (CG_TyEnv cg) dtName c)))
               | _ \<Rightarrow> internal cg ''constructor pattern on a non-variant scrutinee'')
     | CorePat_Record _ \<Rightarrow> internal cg ''non-flat pattern'')"

(* The value the arms are compared against: the tag of a variant scrutinee
   (loaded from its place) or the value of a bool/integer one, held in a
   fresh variable; nothing for any other type (only wildcards can match). *)
definition match_tag :: "CGEnv \<Rightarrow> CoreType \<Rightarrow> MExpr \<Rightarrow> (MStmt list \<times> MExpr) CG" where
  "match_tag cg scrutTy es =
    (case scrutTy of
       CoreTy_Datatype dtName _ \<Rightarrow> do {
         t \<leftarrow> fresh_name (CG_Fun cg) ''tag'';
         cg_return ([MS_DeclScalar t (tag_ty (CG_TyEnv cg) dtName),
                     MS_Assign t (ME_Load (tag_ty (CG_TyEnv cg) dtName) es)], ME_Var t) }
     | CoreTy_Bool \<Rightarrow> do {
         t \<leftarrow> fresh_name (CG_Fun cg) ''tag'';
         cg_return ([MS_DeclScalar t CTy_U8, MS_Assign t es], ME_Var t) }
     | CoreTy_FiniteInt s b \<Rightarrow> do {
         t \<leftarrow> fresh_name (CG_Fun cg) ''tag'';
         cg_return ([MS_DeclScalar t (CTy_Int s b), MS_Assign t es], ME_Var t) }
     | _ \<Rightarrow> cg_return ([], es))"


section \<open>Calls\<close>

(* The result of a call: a scalar value, the place of the return buffer,
   or nothing (a void function). *)
datatype CallRes = CR_Scalar MExpr | CR_Place MExpr | CR_Unit

(* The result of a call at an instantiated return type, as a term's result
   (section 3.4): the value or the place; a result returned through the
   buffer whose instantiated type is scalar (a type variable instantiated
   at a scalar) is loaded. A void result has no place; the caller
   materialises one if it needs it. *)
definition call_result_expr :: "CoreType \<Rightarrow> CallRes \<Rightarrow> MExpr option" where
  "call_result_expr rty res =
    (case res of
       CR_Scalar e \<Rightarrow> Some e
     | CR_Place p \<Rightarrow> Some (load_at rty p)
     | CR_Unit \<Rightarrow> None)"


section \<open>Terms\<close>

function lower_term :: "CGEnv \<Rightarrow> CoreTerm \<Rightarrow> (MStmt list \<times> MExpr) CG"
  and lower_addr :: "CGEnv \<Rightarrow> CoreTerm \<Rightarrow> (MStmt list \<times> MExpr) CG"
  and lower_call :: "CGEnv \<Rightarrow> string \<Rightarrow> CoreType list \<Rightarrow> CoreTerm list \<Rightarrow> (MStmt list \<times> CallRes) CG"
where
  "lower_term cg (CoreTm_LitBool b) =
    cg_return ([], ME_Int Unsigned IntBits_8 (if b then 1 else 0))"

| "lower_term cg (CoreTm_LitInt i) =
    (case get_type_for_int i of
       Some (s, b) \<Rightarrow> cg_return ([], ME_Int s b i)
     | None \<Rightarrow> internal cg ''integer literal out of range'')"

| "lower_term cg (CoreTm_LitArray elemTy tms) = do {
    tmp \<leftarrow> fresh_name (CG_Fun cg) ''arr'';
    rs \<leftarrow> cg_mapM (lower_term cg) tms;
    cg_return ([MS_DeclBuf tmp (buf_size (e_mul (cg_size cg elemTy) (u64_lit (length tms))))]
               @ concat (map fst rs)
               @ map (\<lambda>(k, e). store_at cg elemTy
                                  (ptr_add (ME_AddrOf tmp) (e_mul (cg_size cg elemTy) (u64_lit k))) e)
                     (zip [0..<length tms] (map snd rs)),
               ME_AddrOf tmp)
   }"

| "lower_term cg (CoreTm_Var x) = do {
    ty \<leftarrow> ty_of cg (CoreTm_Var x);
    rep \<leftarrow> lookup_var cg x;
    read_rep cg rep ty
   }"

| "lower_term cg (CoreTm_Cast ty t) = do {
    fromTy \<leftarrow> ty_of cg t;
    (S, e) \<leftarrow> lower_term cg t;
    (S', e') \<leftarrow> cast_result cg fromTy ty e;
    cg_return (S @ S', e')
   }"

| "lower_term cg (CoreTm_Unop op t) = do {
    (S, e) \<leftarrow> lower_term cg t;
    cg_return (S, ME_Unop (unop_of op) e)
   }"

| "lower_term cg (CoreTm_Binop op t1 t2) = do {
    (S1, e1) \<leftarrow> lower_term cg t1;
    (S2, e2) \<leftarrow> lower_term cg t2;
    (case binop_of op of
       Some cop \<Rightarrow> cg_return (S1 @ S2, ME_Binop cop e1 e2)
     | None \<Rightarrow> do {
         \<comment> \<open>short circuit: the right operand's statements run only when needed\<close>
         tmp \<leftarrow> fresh_name (CG_Fun cg) ''sc'';
         cg_return (S1 @ [MS_DeclScalar tmp CTy_U8]
                    @ (if op = CoreBinop_And
                       then [MS_Assign tmp e1, MS_If (ME_Var tmp) (S2 @ [MS_Assign tmp e2]) []]
                       else if op = CoreBinop_Or
                       then [MS_Assign tmp e1, MS_If (ME_Var tmp) [] (S2 @ [MS_Assign tmp e2])]
                       else [MS_Assign tmp (ME_Unop CU_Not e1),
                             MS_If (ME_Var tmp) [] (S2 @ [MS_Assign tmp e2])]),
                    ME_Var tmp) })
   }"

| "lower_term cg (CoreTm_Let x t1 t2) = do {
    ty1 \<leftarrow> ty_of cg t1;
    (S1, e1) \<leftarrow> lower_term cg t1;
    n \<leftarrow> local_name (CG_Fun cg) x;
    let env' = let_env (CG_TyEnv cg) x ty1;
    let (decl, rep) = (case scalar_ty ty1 of
                         Some cty \<Rightarrow> ([MS_DeclScalar n cty, MS_Assign n e1], VR_Scalar n cty)
                       | None \<Rightarrow> ([MS_DeclScalar n CTy_CharPtr, MS_Assign n e1], VR_Ptr n));
    (S2, e2) \<leftarrow> lower_term (cg_bind_var cg env' x rep) t2;
    cg_return (S1 @ decl @ S2, e2)
   }"

| "lower_term cg (CoreTm_Quantifier _ _ _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

| "lower_term cg (CoreTm_FunctionCall f tys args) = do {
    rty \<leftarrow> ty_of cg (CoreTm_FunctionCall f tys args);
    (S, res) \<leftarrow> lower_call cg f tys args;
    (case call_result_expr rty res of
       Some e \<Rightarrow> cg_return (S, e)
     | None \<Rightarrow> do {
         \<comment> \<open>a void call used as a term of the unit type: a dummy place\<close>
         tmp \<leftarrow> fresh_name (CG_Fun cg) ''unit'';
         cg_return ([MS_DeclBuf tmp (u64_lit 1)] @ S, ME_AddrOf tmp) })
   }"

| "lower_term cg (CoreTm_VariantCtor c tys t) = do {
    dtTy \<leftarrow> ty_of cg (CoreTm_VariantCtor c tys t);
    pty \<leftarrow> ty_of cg t;
    (case dtTy of
       CoreTy_Datatype dtName _ \<Rightarrow> do {
         tmp \<leftarrow> fresh_name (CG_Fun cg) ''var'';
         (S, e) \<leftarrow> lower_term cg t;
         cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg dtTy)),
                     MS_Uninit (ME_AddrOf tmp) (cg_size cg dtTy),
                     MS_Store (tag_ty (CG_TyEnv cg) dtName) (ME_AddrOf tmp) (tag_lit (CG_TyEnv cg) dtName c)]
                    @ S
                    @ [store_at cg pty (ptr_add (ME_AddrOf tmp) (tag_off (CG_TyEnv cg) dtName)) e],
                    ME_AddrOf tmp) }
     | _ \<Rightarrow> internal cg ''variant constructor of a non-datatype type'')
   }"

| "lower_term cg (CoreTm_Record flds) = do {
    recTy \<leftarrow> ty_of cg (CoreTm_Record flds);
    (case recTy of
       CoreTy_Record fldTys \<Rightarrow> do {
         tmp \<leftarrow> fresh_name (CG_Fun cg) ''rec'';
         rs \<leftarrow> cg_mapM (\<lambda>(f, t). do {
                  fty \<leftarrow> cg_lift (CG_Fun cg) ''unknown field'' (map_of fldTys f);
                  (S, e) \<leftarrow> lower_term cg t;
                  cg_return (S @ [store_at cg fty (ptr_add (ME_AddrOf tmp) (field_off (CG_TyEnv cg) fldTys f)) e])
                }) flds;
         cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg recTy))] @ concat rs, ME_AddrOf tmp) }
     | _ \<Rightarrow> internal cg ''record of a non-record type'')
   }"

| "lower_term cg (CoreTm_RecordProj t f) = do {
    recTy \<leftarrow> ty_of cg t;
    (case recTy of
       CoreTy_Record fldTys \<Rightarrow> do {
         fty \<leftarrow> cg_lift (CG_Fun cg) ''unknown field'' (map_of fldTys f);
         (S, p) \<leftarrow> lower_addr cg t;
         cg_return (S, load_at fty (ptr_add p (field_off (CG_TyEnv cg) fldTys f))) }
     | _ \<Rightarrow> internal cg ''projection from a non-record'')
   }"

| "lower_term cg (CoreTm_VariantProj t c) = do {
    dtTy \<leftarrow> ty_of cg t;
    pty \<leftarrow> ty_of cg (CoreTm_VariantProj t c);
    (case dtTy of
       CoreTy_Datatype dtName _ \<Rightarrow> do {
         (S, p) \<leftarrow> lower_addr cg t;
         cg_return (S, load_at pty (ptr_add p (tag_off (CG_TyEnv cg) dtName))) }
     | _ \<Rightarrow> internal cg ''payload of a non-variant'')
   }"

| "lower_term cg (CoreTm_ArrayProj t idxs) = do {
    arrTy \<leftarrow> ty_of cg t;
    (case arrTy of
       CoreTy_Array elemTy dims \<Rightarrow> do {
         (S, p) \<leftarrow> lower_addr cg t;
         rs \<leftarrow> cg_mapM (lower_term cg) idxs;
         cg_return (S @ concat (map fst rs),
                    load_at elemTy (elem_addr (CG_TyEnv cg) elemTy dims p (map snd rs))) }
     | _ \<Rightarrow> internal cg ''index of a non-array'')
   }"

| "lower_term cg (CoreTm_Match s arms) = do {
    scrutTy \<leftarrow> ty_of cg s;
    resTy \<leftarrow> ty_of cg (CoreTm_Match s arms);
    (Ss, es) \<leftarrow> lower_term cg s;
    (St, tag) \<leftarrow> match_tag cg scrutTy es;
    (res, decl) \<leftarrow> temp_for cg ''res'' resTy;
    armsL \<leftarrow> cg_mapM (\<lambda>(pat, body). do {
               c \<leftarrow> arm_cond cg scrutTy tag pat;
               (Sb, eb) \<leftarrow> lower_term cg body;
               cg_return (c, Sb @ [temp_store cg resTy res eb])
             }) arms;
    cg_return (Ss @ St @ [decl] @ if_chain armsL, temp_result resTy res)
   }"

| "lower_term cg (CoreTm_Sizeof t) = do {
    arrTy \<leftarrow> ty_of cg t;
    (case arrTy of
       CoreTy_Array _ dims \<Rightarrow>
         if dims_all_fixed dims then
           (case dims of
              [d] \<Rightarrow> cg_return ([], u64_lit (dim_size d))
            | _ \<Rightarrow> do {
                tmp \<leftarrow> fresh_name (CG_Fun cg) ''sz'';
                cg_return ([MS_DeclBuf tmp (u64_lit (8 * length dims))]
                           @ map (\<lambda>k. MS_Store CTy_U64 (ptr_add (ME_AddrOf tmp) (u64_lit (8 * k)))
                                               (u64_lit (dim_size (dims ! k))))
                                 [0..<length dims],
                           ME_AddrOf tmp) })
         else do {
           (S, p) \<leftarrow> lower_term cg t;
           (case dims of
              [_] \<Rightarrow> cg_return (S, ME_Load CTy_U64 (ptr_add p (dim_off 0)))
            | _ \<Rightarrow> do {
                tmp \<leftarrow> fresh_name (CG_Fun cg) ''sz'';
                cg_return (S @ [MS_DeclBuf tmp (u64_lit (8 * length dims)),
                                MS_Copy (ME_AddrOf tmp) (ptr_add p (dim_off 0)) (u64_lit (8 * length dims))],
                           ME_AddrOf tmp) }) }
     | _ \<Rightarrow> internal cg ''sizeof of a non-array'')
   }"

| "lower_term cg (CoreTm_Allocated _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

| "lower_term cg (CoreTm_Default ty) =
    (case scalar_ty ty of
       Some (CTy_Int s b) \<Rightarrow> cg_return ([], ME_Int s b 0)
     | Some _ \<Rightarrow> do {
         \<comment> \<open>a null pointer: a zeroed pointer variable (A3)\<close>
         tmp \<leftarrow> fresh_name (CG_Fun cg) ''null'';
         cg_return ([MS_DeclScalar tmp CTy_VoidPtr, MS_Zero (ME_AddrOf tmp) ME_PtrSize], ME_Var tmp) }
     | None \<Rightarrow> do {
         tmp \<leftarrow> fresh_name (CG_Fun cg) ''def'';
         cg_return ([MS_DeclBuf tmp (buf_size (cg_size cg ty)), MS_Zero (ME_AddrOf tmp) (cg_size cg ty)],
                    ME_AddrOf tmp) })"

  (* The address of a term. *)
| "lower_addr cg (CoreTm_Var x) = do {
    rep \<leftarrow> lookup_var cg x;
    addr_rep cg rep
   }"

| "lower_addr cg (CoreTm_RecordProj t f) = do {
    recTy \<leftarrow> ty_of cg t;
    (case recTy of
       CoreTy_Record fldTys \<Rightarrow> do {
         (S, p) \<leftarrow> lower_addr cg t;
         cg_return (S, ptr_add p (field_off (CG_TyEnv cg) fldTys f)) }
     | _ \<Rightarrow> internal cg ''projection from a non-record'')
   }"

| "lower_addr cg (CoreTm_VariantProj t c) = do {
    dtTy \<leftarrow> ty_of cg t;
    (case dtTy of
       CoreTy_Datatype dtName _ \<Rightarrow> do {
         (S, p) \<leftarrow> lower_addr cg t;
         cg_return (S, ptr_add p (tag_off (CG_TyEnv cg) dtName)) }
     | _ \<Rightarrow> internal cg ''payload of a non-variant'')
   }"

| "lower_addr cg (CoreTm_ArrayProj t idxs) = do {
    arrTy \<leftarrow> ty_of cg t;
    (case arrTy of
       CoreTy_Array elemTy dims \<Rightarrow> do {
         (S, p) \<leftarrow> lower_addr cg t;
         rs \<leftarrow> cg_mapM (lower_term cg) idxs;
         cg_return (S @ concat (map fst rs), elem_addr (CG_TyEnv cg) elemTy dims p (map snd rs)) }
     | _ \<Rightarrow> internal cg ''index of a non-array'')
   }"

| "lower_addr cg (CoreTm_Cast ty t) =
    (if is_array_type ty then do {
       fromTy \<leftarrow> ty_of cg t;
       (S, p) \<leftarrow> lower_addr cg t;
       (S', p') \<leftarrow> cast_place cg fromTy ty p;
       cg_return (S @ S', p')
     } else do {
       \<comment> \<open>a numeric cast is not an lvalue: its value, in a temporary\<close>
       ty' \<leftarrow> ty_of cg (CoreTm_Cast ty t);
       (S, e) \<leftarrow> lower_term cg (CoreTm_Cast ty t);
       (tmp, decl) \<leftarrow> temp_for cg ''tmp'' ty';
       cg_return (S @ [decl, temp_store cg ty' tmp e], ME_AddrOf tmp)
     })"

| "lower_addr cg (CoreTm_LitBool b) = do {
    (S, e) \<leftarrow> lower_term cg (CoreTm_LitBool b);
    (tmp, decl) \<leftarrow> temp_for cg ''tmp'' CoreTy_Bool;
    cg_return (S @ [decl, MS_Assign tmp e], ME_AddrOf tmp) }"
| "lower_addr cg (CoreTm_LitInt i) = do {
    ty \<leftarrow> ty_of cg (CoreTm_LitInt i);
    (S, e) \<leftarrow> lower_term cg (CoreTm_LitInt i);
    (tmp, decl) \<leftarrow> temp_for cg ''tmp'' ty;
    cg_return (S @ [decl, MS_Assign tmp e], ME_AddrOf tmp) }"
| "lower_addr cg (CoreTm_LitArray ety tms) = lower_term cg (CoreTm_LitArray ety tms)"
| "lower_addr cg (CoreTm_Unop op t) = do {
    ty \<leftarrow> ty_of cg (CoreTm_Unop op t);
    (S, e) \<leftarrow> lower_term cg (CoreTm_Unop op t);
    (tmp, decl) \<leftarrow> temp_for cg ''tmp'' ty;
    cg_return (S @ [decl, MS_Assign tmp e], ME_AddrOf tmp) }"
| "lower_addr cg (CoreTm_Binop op t1 t2) = do {
    ty \<leftarrow> ty_of cg (CoreTm_Binop op t1 t2);
    (S, e) \<leftarrow> lower_term cg (CoreTm_Binop op t1 t2);
    (tmp, decl) \<leftarrow> temp_for cg ''tmp'' ty;
    cg_return (S @ [decl, MS_Assign tmp e], ME_AddrOf tmp) }"
| "lower_addr cg (CoreTm_Let x t1 t2) = do {
    ty \<leftarrow> ty_of cg (CoreTm_Let x t1 t2);
    (S, e) \<leftarrow> lower_term cg (CoreTm_Let x t1 t2);
    (if is_scalar ty then do {
       (tmp, decl) \<leftarrow> temp_for cg ''tmp'' ty;
       cg_return (S @ [decl, MS_Assign tmp e], ME_AddrOf tmp) }
     else cg_return (S, e)) }"
| "lower_addr cg (CoreTm_Quantifier q x ty t) = cg_fail (CGE_Ghost (CG_Fun cg))"
| "lower_addr cg (CoreTm_FunctionCall f tys args) = do {
    ty \<leftarrow> ty_of cg (CoreTm_FunctionCall f tys args);
    (S, e) \<leftarrow> lower_term cg (CoreTm_FunctionCall f tys args);
    (if is_scalar ty then do {
       (tmp, decl) \<leftarrow> temp_for cg ''tmp'' ty;
       cg_return (S @ [decl, MS_Assign tmp e], ME_AddrOf tmp) }
     else cg_return (S, e)) }"
| "lower_addr cg (CoreTm_VariantCtor c tys t) = lower_term cg (CoreTm_VariantCtor c tys t)"
| "lower_addr cg (CoreTm_Record flds) = lower_term cg (CoreTm_Record flds)"
| "lower_addr cg (CoreTm_Match s arms) = do {
    ty \<leftarrow> ty_of cg (CoreTm_Match s arms);
    (S, e) \<leftarrow> lower_term cg (CoreTm_Match s arms);
    (if is_scalar ty then do {
       (tmp, decl) \<leftarrow> temp_for cg ''tmp'' ty;
       cg_return (S @ [decl, MS_Assign tmp e], ME_AddrOf tmp) }
     else cg_return (S, e)) }"
| "lower_addr cg (CoreTm_Sizeof t) = do {
    ty \<leftarrow> ty_of cg (CoreTm_Sizeof t);
    (S, e) \<leftarrow> lower_term cg (CoreTm_Sizeof t);
    (if is_scalar ty then do {
       (tmp, decl) \<leftarrow> temp_for cg ''tmp'' ty;
       cg_return (S @ [decl, MS_Assign tmp e], ME_AddrOf tmp) }
     else cg_return (S, e)) }"
| "lower_addr cg (CoreTm_Allocated ty t) = cg_fail (CGE_Ghost (CG_Fun cg))"
| "lower_addr cg (CoreTm_Default ty) = do {
    (S, e) \<leftarrow> lower_term cg (CoreTm_Default ty);
    (if is_scalar ty then do {
       (tmp, decl) \<leftarrow> temp_for cg ''tmp'' ty;
       cg_return (S @ [decl, MS_Assign tmp e], ME_AddrOf tmp) }
     else cg_return (S, e)) }"

  (* A call (section 3.4): the return buffer if the declared return type
     is a non-unit aggregate, the sizes of the type arguments, then the
     arguments: by value for a scalar declared parameter type, else the
     address (the place of an aggregate, the address of the lvalue of a
     ref argument, the address of a temporary for a scalar passed to a
     parameter of type-variable type). *)
| "lower_call cg f tys args = do {
    info \<leftarrow> cg_lift (CG_Fun cg) (''unknown function '' @ f) (fmlookup (TE_Functions (CG_TyEnv cg)) f);
    (if length args \<noteq> length (FI_TmArgs info) \<or> length tys \<noteq> length (FI_TyArgs info)
     then internal cg (''wrong number of arguments in a call of '' @ f) else cg_return ());
    let subst = fmap_of_list (zip (FI_TyArgs info) tys);
    (Sret, retArgs, xopt, res) \<leftarrow>
      (case ret_kind (FI_ReturnType info) of
         RK_Buf \<Rightarrow> do {
           r \<leftarrow> fresh_name (CG_Fun cg) ''ret'';
           cg_return ([MS_DeclBuf r (buf_size (cg_size cg (apply_subst subst (FI_ReturnType info))))],
                      [ME_AddrOf r], None, CR_Place (ME_AddrOf r)) }
       | RK_Unit \<Rightarrow> cg_return ([], [], None, CR_Unit)
       | RK_Scalar cty \<Rightarrow> do {
           x \<leftarrow> fresh_name (CG_Fun cg) ''call'';
           cg_return ([MS_DeclScalar x cty], [], Some x, CR_Scalar (ME_Var x)) });
    argsL \<leftarrow> cg_mapM (\<lambda>(a, (pty, vor, _)).
                if param_by_ptr pty vor then lower_addr cg a else lower_term cg a)
              (zip args (FI_TmArgs info));
    cg_return (Sret @ concat (map fst argsL)
               @ [MS_Call xopt f (retArgs @ map (cg_size cg) tys @ map snd argsL)],
               res)
   }"
  by pat_completeness auto

(* Termination: by the size of the term; lower_addr may call lower_term on
   the same term, and the call lowering is below the call term. *)
lemma size_in_list: "x \<in> set xs \<Longrightarrow> size x \<le> size_list size xs"
  by (simp add: size_list_estimation')

lemma size_snd_in_list: "x \<in> set xs \<Longrightarrow> size (snd x) \<le> size_list (size_prod (\<lambda>_. 0) size) xs"
  by (cases x) (auto simp: size_list_estimation')

lemma size_fst_in_zip: "x \<in> set (zip xs ys) \<Longrightarrow> size (fst x) \<le> size_list size xs"
  by (cases x) (auto simp: size_list_estimation' dest: set_zip_leftD)

termination
  by (relation "measure (\<lambda>x. case x of
       Inl (cg, tm) \<Rightarrow> 3 * size tm
     | Inr (Inl (cg, tm)) \<Rightarrow> 3 * size tm + 1
     | Inr (Inr (cg, f, tys, args)) \<Rightarrow> 3 * size_list size args + 2)")
     (auto dest!: size_in_list size_snd_in_list size_fst_in_zip)

end

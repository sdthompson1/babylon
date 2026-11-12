theory CodeGen
  imports CodeGenTerm
begin

(* ========================================================================== *)
(* The code generator: statements, functions, globals, main, the module       *)
(* (minic/DESIGN.md, sections 3.4 to 3.9)                                     *)
(* ========================================================================== *)


section \<open>Lazy references (section 3.5)\<close>

(* Does a ref to this lvalue need to be lazy? Yes if the lvalue passes
   through a projection of an array with an allocatable dimension (which
   may be reallocated while the ref is live) or through a variable that
   is itself lazy. *)
fun needs_lazy :: "CGEnv \<Rightarrow> CoreTerm \<Rightarrow> bool" where
  "needs_lazy cg (CoreTm_Var x) =
    (case fmlookup (CG_Vars cg) x of Some (VR_Lazy _) \<Rightarrow> True | _ \<Rightarrow> False)"
| "needs_lazy cg (CoreTm_RecordProj t _) = needs_lazy cg t"
| "needs_lazy cg (CoreTm_VariantProj t _) = needs_lazy cg t"
| "needs_lazy cg (CoreTm_ArrayProj t _) =
    ((case core_term_type (CG_TyEnv cg) NotGhost t of Some ty \<Rightarrow> has_alloc_dim ty | None \<Rightarrow> False)
     \<or> needs_lazy cg t)"
| "needs_lazy cg (CoreTm_Cast _ t) = needs_lazy cg t"
| "needs_lazy cg _ = False"

(* Freeze an lvalue: capture the base's representation and evaluate every
   array index, once, into a fresh uint64_t variable (Core evaluates the
   indices once too, when it resolves the lvalue). Used for lazy refs,
   which Core resolves at their declaration. *)
fun freeze_lvalue :: "CGEnv \<Rightarrow> CoreTerm \<Rightarrow> (MStmt list \<times> LazyLv) CG" where
  "freeze_lvalue cg (CoreTm_Var x) = do {
    ty \<leftarrow> ty_of cg (CoreTm_Var x);
    rep \<leftarrow> lookup_var cg x;
    (case rep of
       VR_Lazy ll \<Rightarrow> cg_return ([], ll)
     | _ \<Rightarrow> cg_return ([], LL_Base rep ty))
   }"
| "freeze_lvalue cg (CoreTm_RecordProj t f) = do {
    ty \<leftarrow> ty_of cg (CoreTm_RecordProj t f);
    (S, ll) \<leftarrow> freeze_lvalue cg t;
    cg_return (S, LL_Field ll f ty)
   }"
| "freeze_lvalue cg (CoreTm_VariantProj t c) = do {
    ty \<leftarrow> ty_of cg (CoreTm_VariantProj t c);
    (S, ll) \<leftarrow> freeze_lvalue cg t;
    cg_return (S, LL_Payload ll c ty)
   }"
| "freeze_lvalue cg (CoreTm_ArrayProj t idxs) = do {
    ty \<leftarrow> ty_of cg (CoreTm_ArrayProj t idxs);
    (S, ll) \<leftarrow> freeze_lvalue cg t;
    rs \<leftarrow> cg_mapM (lower_term cg) idxs;
    vs \<leftarrow> cg_mapM (\<lambda>e. do {
            v \<leftarrow> fresh_name (CG_Fun cg) ''idx'';
            cg_return (v, [MS_DeclScalar v CTy_U64, MS_Assign v e]) }) (map snd rs);
    cg_return (S @ concat (map fst rs) @ concat (map snd vs), LL_Index ll (map fst vs) ty)
   }"
| "freeze_lvalue cg (CoreTm_Cast ty t) =
    (if is_array_type ty then do {
       (S, ll) \<leftarrow> freeze_lvalue cg t;
       cg_return (S, LL_Cast ll ty) }
     else internal cg ''numeric cast as an lvalue'')"
| "freeze_lvalue cg _ = internal cg ''not an lvalue''"


section \<open>Stores to lvalues\<close>

(* Store a value (or copy a place) to a Core lvalue of the given type. A
   scalar variable held in a MiniC scalar is assigned directly; everything
   else goes through the address. *)
definition lower_store :: "CGEnv \<Rightarrow> CoreTerm \<Rightarrow> CoreType \<Rightarrow> MExpr \<Rightarrow> MStmt list CG" where
  "lower_store cg lv ty e =
    (case lv of
       CoreTm_Var x \<Rightarrow>
         (case fmlookup (CG_Vars cg) x of
            Some (VR_Scalar n _) \<Rightarrow> cg_return [MS_Assign n e]
          | _ \<Rightarrow> do { (S, a) \<leftarrow> lower_addr cg lv; cg_return (S @ [store_at cg ty a e]) })
     | _ \<Rightarrow> do { (S, a) \<leftarrow> lower_addr cg lv; cg_return (S @ [store_at cg ty a e]) })"

(* Evaluate an address now, into a fresh char * variable. The expression
   that lower_addr returns denotes the address of the lvalue only in the
   state in which it is evaluated (it may read an index variable, or the
   data pointer of a descriptor); the variable keeps denoting it after a
   store. Used for the two operands of a swap, which Core resolves before
   it writes either. *)
definition bind_addr :: "CGEnv \<Rightarrow> MExpr \<Rightarrow> (MStmt list \<times> MExpr) CG" where
  "bind_addr cg a = do {
     p \<leftarrow> fresh_name (CG_Fun cg) ''addr'';
     cg_return ([MS_DeclScalar p CTy_CharPtr, MS_Assign p a], ME_Var p)
   }"

(* The result of a call stored into a variable or lvalue of the given
   (instantiated) type: nothing for a void result. *)
definition call_store :: "CGEnv \<Rightarrow> (MExpr \<Rightarrow> MStmt list CG) \<Rightarrow> CoreType \<Rightarrow> CallRes \<Rightarrow> MStmt list CG" where
  "call_store cg store ty res =
    (case call_result_expr ty res of
       Some e \<Rightarrow> store e
     | None \<Rightarrow> cg_return [])"

(* The optional cast of a call's result (section 3.6): a numeric cast of
   the value, or an array cast of the place. *)
definition cast_call_res :: "CGEnv \<Rightarrow> CoreType \<Rightarrow> CoreType option \<Rightarrow> CallRes \<Rightarrow> (MStmt list \<times> CallRes) CG" where
  "cast_call_res cg retTy castOpt res =
    (case castOpt of
       None \<Rightarrow> cg_return ([], res)
     | Some toTy \<Rightarrow>
         (case call_result_expr retTy res of
            None \<Rightarrow> internal cg ''cast of a void result''
          | Some e \<Rightarrow> do {
              (S, e') \<leftarrow> cast_result cg retTy toTy e;
              cg_return (S, (if is_scalar toTy then CR_Scalar e' else CR_Place e')) }))"

(* The declaration of a Core local of the given type and its representation. *)
definition decl_local :: "CGEnv \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> (MStmt \<times> VarRep) CG" where
  "decl_local cg x ty = do {
     n \<leftarrow> local_name (CG_Fun cg) x;
     cg_return (case scalar_ty ty of
                  Some cty \<Rightarrow> (MS_DeclScalar n cty, VR_Scalar n cty)
                | None \<Rightarrow> (MS_DeclBuf n (buf_size (cg_size cg ty)), VR_Buf n))
   }"

(* The store of a value into a freshly declared local. *)
definition init_local :: "CGEnv \<Rightarrow> VarRep \<Rightarrow> CoreType \<Rightarrow> MExpr \<Rightarrow> MStmt list CG" where
  "init_local cg rep ty e =
    (case rep of
       VR_Scalar n _ \<Rightarrow> cg_return [MS_Assign n e]
     | VR_Buf n \<Rightarrow> cg_return [MS_Copy (ME_AddrOf n) e (cg_size cg ty)]
     | _ \<Rightarrow> internal cg ''initialisation of a non-local'')"

(* The typing context after a statement, as the typechecker computes it. *)
definition env_after :: "CGEnv \<Rightarrow> CoreStatement \<Rightarrow> CoreTyEnv CG" where
  "env_after cg s =
    cg_lift (CG_Fun cg) ''statement does not typecheck'' (core_statement_type (CG_TyEnv cg) NotGhost s)"

definition impure_ret_type :: "CGEnv \<Rightarrow> string \<Rightarrow> CoreType list \<Rightarrow> CoreTerm list \<Rightarrow> CoreType CG" where
  "impure_ret_type cg f tys args =
    cg_lift (CG_Fun cg) ''call does not typecheck'' (core_impure_call_type (CG_TyEnv cg) NotGhost f tys args)"


section \<open>Statements (section 3.6)\<close>

function lower_stmt :: "CGEnv \<Rightarrow> CoreStatement \<Rightarrow> (MStmt list \<times> CGEnv) CG"
  and lower_stmts :: "CGEnv \<Rightarrow> CoreStatement list \<Rightarrow> (MStmt list \<times> CGEnv) CG"
where
  "lower_stmt cg (CoreStmt_VarDecl Ghost _ _ _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

| "lower_stmt cg (CoreStmt_VarDecl NotGhost x Var ty t) = do {
    env' \<leftarrow> env_after cg (CoreStmt_VarDecl NotGhost x Var ty t);
    (S, e) \<leftarrow> lower_term cg t;
    (decl, rep) \<leftarrow> decl_local cg x ty;
    init \<leftarrow> init_local cg rep ty e;
    cg_return (S @ [decl] @ init, cg_bind_var cg env' x rep)
   }"

| "lower_stmt cg (CoreStmt_VarDecl NotGhost x Ref ty lv) = do {
    env' \<leftarrow> env_after cg (CoreStmt_VarDecl NotGhost x Ref ty lv);
    (if needs_lazy cg lv then do {
       (S, ll) \<leftarrow> freeze_lvalue cg lv;
       cg_return (S, cg_bind_var cg env' x (VR_Lazy ll)) }
     else do {
       (S, a) \<leftarrow> lower_addr cg lv;
       n \<leftarrow> local_name (CG_Fun cg) x;
       cg_return (S @ [MS_DeclScalar n CTy_CharPtr, MS_Assign n a], cg_bind_var cg env' x (VR_Ptr n)) })
   }"

| "lower_stmt cg (CoreStmt_VarDeclCall Ghost _ _ _ _ _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

| "lower_stmt cg (CoreStmt_VarDeclCall NotGhost x ty castOpt f tys args) = do {
    env' \<leftarrow> env_after cg (CoreStmt_VarDeclCall NotGhost x ty castOpt f tys args);
    retTy \<leftarrow> impure_ret_type cg f tys args;
    (Sc, res) \<leftarrow> lower_call cg f tys args;
    (Scast, res') \<leftarrow> cast_call_res cg retTy castOpt res;
    (decl, rep) \<leftarrow> decl_local cg x ty;
    init \<leftarrow> call_store cg (init_local cg rep ty) ty res';
    cg_return (Sc @ Scast @ [decl] @ init, cg_bind_var cg env' x rep)
   }"

| "lower_stmt cg (CoreStmt_Assign Ghost _ _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

| "lower_stmt cg (CoreStmt_Assign NotGhost ty lv t) = do {
    (S, e) \<leftarrow> lower_term cg t;
    Ss \<leftarrow> lower_store cg lv ty e;
    cg_return (S @ Ss, cg)
   }"

| "lower_stmt cg (CoreStmt_AssignCall Ghost _ _ _ _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

| "lower_stmt cg (CoreStmt_AssignCall NotGhost lv castOpt f tys args) = do {
    lhsTy \<leftarrow> ty_of cg lv;
    retTy \<leftarrow> impure_ret_type cg f tys args;
    (Sc, res) \<leftarrow> lower_call cg f tys args;
    (Scast, res') \<leftarrow> cast_call_res cg retTy castOpt res;
    Ss \<leftarrow> call_store cg (lower_store cg lv lhsTy) lhsTy res';
    cg_return (Sc @ Scast @ Ss, cg)
   }"

| "lower_stmt cg (CoreStmt_Swap Ghost _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

  (* Swap: both addresses are computed, and held in pointer variables,
     before anything is written, because Core resolves both lvalues in the
     state before the swap (in "swap i, a[i]" the element is the one
     selected by the old value of i). *)
| "lower_stmt cg (CoreStmt_Swap NotGhost lv1 lv2) = do {
    ty \<leftarrow> ty_of cg lv1;
    (S1, a1) \<leftarrow> lower_addr cg lv1;
    (P1, p1) \<leftarrow> bind_addr cg a1;
    (S2, a2) \<leftarrow> lower_addr cg lv2;
    (P2, p2) \<leftarrow> bind_addr cg a2;
    (tmp, decl) \<leftarrow> temp_for cg ''swap'' ty;
    cg_return (S1 @ P1 @ S2 @ P2 @ [decl]
               @ (case scalar_ty ty of
                    Some cty \<Rightarrow> [MS_Assign tmp (ME_Load cty p1),
                                  MS_Store cty p1 (ME_Load cty p2),
                                  MS_Store cty p2 (ME_Var tmp)]
                  | None \<Rightarrow> [MS_Copy (ME_AddrOf tmp) p1 (cg_size cg ty),
                              MS_Copy p1 p2 (cg_size cg ty),
                              MS_Copy p2 (ME_AddrOf tmp) (cg_size cg ty)]),
               cg)
   }"

| "lower_stmt cg (CoreStmt_Return t) =
    (case CG_Ret cg of
       RK_Scalar _ \<Rightarrow> do {
         (S, e) \<leftarrow> lower_term cg t;
         cg_return (S @ [MS_Return (Some e)], cg) }
     | RK_Unit \<Rightarrow>
         if t = CoreTm_Record [] then cg_return ([MS_Return None], cg)
         else do {
           (S, _) \<leftarrow> lower_term cg t;
           cg_return (S @ [MS_Return None], cg) }
     | RK_Buf \<Rightarrow> do {
         (S, p) \<leftarrow> lower_term cg t;
         cg_return (S @ [MS_Copy (ME_Var ret_param) p (cg_size cg (TE_ReturnType (CG_TyEnv cg))),
                         MS_Return None], cg) })"

| "lower_stmt cg (CoreStmt_While Ghost _ _ _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

| "lower_stmt cg (CoreStmt_While NotGhost c _ _ body) = do {
    (Sc, ec) \<leftarrow> lower_term cg c;
    (Sb, _) \<leftarrow> lower_stmts (cg_nested cg) body;
    cg_return ([MS_Loop (Sc @ [MS_If (ME_Unop CU_Not ec) [MS_Break] []] @ Sb)], cg)
   }"

| "lower_stmt cg (CoreStmt_Match Ghost _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

| "lower_stmt cg (CoreStmt_Match NotGhost s arms) = do {
    scrutTy \<leftarrow> ty_of cg s;
    (Ss, es) \<leftarrow> lower_term cg s;
    (St, tag) \<leftarrow> match_tag cg scrutTy es;
    armsL \<leftarrow> cg_mapM (\<lambda>(pat, body). do {
               c \<leftarrow> arm_cond cg scrutTy tag pat;
               (Sb, _) \<leftarrow> lower_stmts (cg_nested cg) body;
               cg_return (c, Sb)
             }) arms;
    cg_return (Ss @ St @ if_chain armsL, cg)
   }"

| "lower_stmt cg (CoreStmt_Block body) = do {
    (S, _) \<leftarrow> lower_stmts (cg_nested cg) body;
    cg_return ([MS_Block S], cg)
   }"

| "lower_stmt cg (CoreStmt_Fix _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"
| "lower_stmt cg (CoreStmt_Obtain _ _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"
| "lower_stmt cg (CoreStmt_Use _) = cg_fail (CGE_Ghost (CG_Fun cg))"
| "lower_stmt cg (CoreStmt_Assert _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"
| "lower_stmt cg (CoreStmt_Assume _) = cg_fail (CGE_Ghost (CG_Fun cg))"
| "lower_stmt cg (CoreStmt_ShowHide _ _) = cg_fail (CGE_Ghost (CG_Fun cg))"

| "lower_stmts cg [] = cg_return ([], cg)"
| "lower_stmts cg (s # ss) = do {
    (S1, cg1) \<leftarrow> lower_stmt cg s;
    (S2, cg2) \<leftarrow> lower_stmts cg1 ss;
    cg_return (S1 @ S2, cg2)
   }"
  by pat_completeness auto

lemma size_stmts_snd_in_list:
  "x \<in> set xs \<Longrightarrow> size_list size (snd x) \<le> size_list (size_prod (\<lambda>_. 0) (size_list size)) xs"
  by (cases x) (auto simp: size_list_estimation')

termination
  by (relation "measure (\<lambda>x. case x of
       Inl (cg, s) \<Rightarrow> size s
     | Inr (cg, ss) \<Rightarrow> size_list size ss)")
     (auto dest!: size_stmts_snd_in_list)


section \<open>Globals (section 3.7)\<close>

(* The MiniC global of a Core global: a scalar, or a buffer of its size
   (at least one byte). The types are closed, so the type-variable map is
   never consulted. *)
definition global_decl :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> MGlobal" where
  "global_decl env ty =
    (case scalar_ty ty of
       Some cty \<Rightarrow> MG_Scalar cty
     | None \<Rightarrow> MG_Buf (buf_size (size_of env ty)))"

definition global_rep :: "string \<Rightarrow> CoreType \<Rightarrow> VarRep" where
  "global_rep g ty = (case scalar_ty ty of Some cty \<Rightarrow> VR_Scalar g cty | None \<Rightarrow> VR_Buf g)"

(* The representations of all globals (the initial CG_Vars of every
   function). *)
definition global_reps :: "CoreTyEnv \<Rightarrow> (string, VarRep) fmap" where
  "global_reps env = fmmap_keys global_rep (TE_GlobalVars env)"

(* The statements that store a compile-time value at an address (the
   scalar leaves at their offsets), plus the extra data-buffer globals it
   needs (one per non-empty array value at a descriptor type). *)
function init_value :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> CoreType \<Rightarrow> CoreValue \<Rightarrow> MExpr
                        \<Rightarrow> ((string \<times> MGlobal) list \<times> MStmt list) CG" where
  "init_value env g ty (CV_Bool b) base =
    cg_return ([], [MS_Store CTy_U8 base (ME_Int Unsigned IntBits_8 (if b then 1 else 0))])"

| "init_value env g ty (CV_FiniteInt s b i) base =
    cg_return ([], [MS_Store (CTy_Int s b) base (ME_Int s b i)])"

| "init_value env g ty (CV_Record fvs) base =
    (case ty of
       CoreTy_Record fldTys \<Rightarrow> do {
         rs \<leftarrow> cg_mapM (\<lambda>(f, v). do {
                  fty \<leftarrow> cg_lift g ''unknown field in a global value'' (map_of fldTys f);
                  init_value env g fty v (ptr_add base (field_off env fldTys f))
                }) fvs;
         cg_return (concat (map fst rs), concat (map snd rs)) }
     | _ \<Rightarrow> cg_fail (CGE_Internal g ''record value at a non-record type''))"

| "init_value env g ty (CV_Variant c p) base =
    (case ty of
       CoreTy_Datatype dtName args \<Rightarrow>
         (case fmlookup (TE_DataCtors env) c of
            Some (_, tyvars, payloadTy) \<Rightarrow>
              \<comment> \<open>the instantiated payload type must fit (its offsets are literals)\<close>
              if \<not> size_fits env 0 (\<lambda>_. 0) (apply_subst (fmap_of_list (zip tyvars args)) payloadTy)
              then cg_fail (CGE_Internal g ''payload of a global value too large'')
              else do {
              (gs, S) \<leftarrow> init_value env g (apply_subst (fmap_of_list (zip tyvars args)) payloadTy) p
                           (ptr_add base (tag_off env dtName));
              cg_return (gs, MS_Store (tag_ty env dtName) base (tag_lit env dtName c) # S) }
          | None \<Rightarrow> cg_fail (CGE_Internal g ''unknown constructor in a global value''))
     | _ \<Rightarrow> cg_fail (CGE_Internal g ''variant value at a non-datatype type''))"

| "init_value env g ty (CV_Array sizes elems) base =
    (case ty of
       CoreTy_Array elemTy dims \<Rightarrow>
         let esz = size_of env elemTy;
             sizeExprs = map (\<lambda>n. u64_lit (nat n)) sizes;
             initElems = (\<lambda>data. cg_mapM (\<lambda>idx.
                 (case fmlookup elems idx of
                    Some v \<Rightarrow> init_value env g elemTy v
                                (ptr_add data (elem_offset_expr esz sizeExprs (map (\<lambda>i. u64_lit (nat i)) idx)))
                  | None \<Rightarrow> cg_fail (CGE_Internal g ''missing array element in a global value'')))
                 (all_indices sizes))
         in if dims_all_fixed dims then do {
              rs \<leftarrow> initElems base;
              cg_return (concat (map fst rs), concat (map snd rs)) }
            else if \<not> (size_fits env 0 (\<lambda>_. 0) elemTy \<and> sizes_count sizes < u64_max
                       \<and> type_size env 0 (\<lambda>_. 0) elemTy * sizes_count sizes < u64_max)
            then \<comment> \<open>the element offsets and the data buffer's size are literals: they must fit\<close>
                 cg_fail (CGE_Internal g ''global array value too large'')
            else do {
              \<comment> \<open>a descriptor: the sizes, and (if there are elements) a data buffer global\<close>
              let dimStores = map (\<lambda>k. MS_Store CTy_U64 (ptr_add base (dim_off k)) (u64_lit (nat (sizes ! k))))
                                  [0..<length sizes];
              (if sizes_count sizes = 0 then cg_return ([], dimStores)
               else do {
                 data \<leftarrow> fresh_name g (g @ [dollar] @ ''data'');
                 rs \<leftarrow> initElems (ME_AddrOf data);
                 cg_return ((data, MG_Buf (buf_size (e_mul esz (u64_lit (sizes_count sizes))))) # concat (map fst rs),
                            MS_Store CTy_CharPtr base (ME_AddrOf data) # dimStores @ concat (map snd rs)) }) }
     | _ \<Rightarrow> cg_fail (CGE_Internal g ''array value at a non-array type''))"

| "init_value env g ty (CV_Int _) base = cg_fail (CGE_Internal g ''math value in a global'')"
| "init_value env g ty (CV_Real _) base = cg_fail (CGE_Internal g ''math value in a global'')"

| "init_value env g ty (CV_Extern _ _ h) base =
    (if h = 0 then cg_return ([], []) else cg_fail (CGE_GlobalHandle g))"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(env, g, ty, v, base). size v)")
     (auto dest!: size_record_field size_array_lookup)

(* The globals of the module: for each entry of CM_GlobalVars, its MiniC
   global (and data buffers) and its initialisation statements. *)
definition lower_globals :: "CoreModule \<Rightarrow> ((string \<times> MGlobal) list \<times> MStmt list) CG" where
  "lower_globals m = do {
     rs \<leftarrow> cg_mapM (\<lambda>(g, v). do {
              ty \<leftarrow> cg_lift g ''global without a declared type'' (fmlookup (TE_GlobalVars (CM_TyEnv m)) g);
              (gs, S) \<leftarrow> init_value (CM_TyEnv m) g ty v (ME_AddrOf g);
              cg_return ((g, global_decl (CM_TyEnv m) ty) # gs, S)
            }) (sorted_list_of_fmap (CM_GlobalVars m));
     cg_return (concat (map fst rs), concat (map snd rs))
   }"


section \<open>Functions (sections 3.4, 3.9)\<close>

(* The first duplicate of a list, if any. *)
fun first_dup :: "string list \<Rightarrow> string option" where
  "first_dup [] = None"
| "first_dup (x # xs) = (if x \<in> set xs then Some x else first_dup xs)"

(* The parameter list of a function: the return buffer, the sizes of the
   type parameters, the parameters. *)
definition fun_params :: "CoreFunction \<Rightarrow> FunInfo \<Rightarrow> (string \<times> CTy) list" where
  "fun_params cf info =
    (case ret_kind (FI_ReturnType info) of RK_Buf \<Rightarrow> [(ret_param, CTy_CharPtr)] | _ \<Rightarrow> [])
    @ map (\<lambda>v. (size_param v, CTy_U64)) (FI_TyArgs info)
    @ map (\<lambda>(x, (ty, vor, _)). (x, param_cty ty vor)) (zip (CF_Args cf) (FI_TmArgs info))"

(* The representation of a parameter. *)
definition param_rep :: "string \<Rightarrow> CoreType \<Rightarrow> VarOrRef \<Rightarrow> VarRep" where
  "param_rep x ty vor = (if param_by_ptr ty vor then VR_Ptr x else VR_Scalar x (the (scalar_ty ty)))"

(* The checks of section 3.9 on a function's names, and the reservation of
   its parameter names. *)
definition check_fun_names :: "string fset \<Rightarrow> string \<Rightarrow> CoreFunction \<Rightarrow> FunInfo \<Rightarrow> unit CG" where
  "check_fun_names funNames f cf info = do {
     (if length (CF_Args cf) \<noteq> length (FI_TmArgs info) then cg_fail (CGE_ParamCount f) else cg_return ());
     (case first_dup (CF_Args cf) of Some x \<Rightarrow> cg_fail (CGE_DuplicateParam f x) | None \<Rightarrow> cg_return ());
     (case find has_dollar (CF_Args cf @ FI_TyArgs info) of Some x \<Rightarrow> cg_fail (CGE_DollarName x) | None \<Rightarrow> cg_return ());
     (case find (\<lambda>x. x |\<in>| funNames) (CF_Args cf) of Some x \<Rightarrow> cg_fail (CGE_NameIsFunction f x) | None \<Rightarrow> cg_return ());
     cg_mapM (\<lambda>(x, _). reserve_name (CGE_Internal f (''parameter '' @ x @ '' clashes with a global'')) x)
             (fun_params cf info);
     cg_return ()
   }"

(* A function: its prototype from the signature, its body lowered in the
   environment of its parameters (an extern function has no body and
   carries its C name). *)
definition lower_function :: "CoreModule \<Rightarrow> (string, string) fmap \<Rightarrow> string fset \<Rightarrow> string fset
                              \<Rightarrow> string \<Rightarrow> CoreFunction \<Rightarrow> CGError + MFun" where
  "lower_function m cnames funNames usedNames f cf =
    (case fmlookup (TE_Functions (CM_TyEnv m)) f of
       None \<Rightarrow> Inl (CGE_Internal f ''function without a signature'')
     | Some info \<Rightarrow>
         (let st0 = \<lparr> CS_Counter = 0, CS_Used = usedNames \<rparr>;
              params = fun_params cf info;
              reps = fold (\<lambda>(x, (ty, vor, _)). fmupd x (param_rep x ty vor)) (zip (CF_Args cf) (FI_TmArgs info))
                          (global_reps (CM_TyEnv m));
              cg = \<lparr> CG_TyEnv = module_body_env_for (CM_TyEnv m) (CF_Args cf) info,
                     CG_Vars = reps,
                     CG_Ret = ret_kind (FI_ReturnType info),
                     CG_Fun = f \<rparr>;
              retTy = (case ret_kind (FI_ReturnType info) of RK_Scalar cty \<Rightarrow> Some cty | _ \<Rightarrow> None)
          in case check_fun_names funNames f cf info st0 of
               Inl err \<Rightarrow> Inl err
             | Inr (_, st1) \<Rightarrow>
                 (case CF_Body cf of
                    None \<Rightarrow>
                      Inr \<lparr> MF_Name = f, MF_Params = params, MF_Ret = retTy, MF_Body = [],
                            MF_Extern = Some (case fmlookup cnames f of Some c \<Rightarrow> c | None \<Rightarrow> unqualified f) \<rparr>
                  | Some body \<Rightarrow>
                      (case lower_stmts cg body st1 of
                         Inl err \<Rightarrow> Inl err
                       | Inr ((S, _), _) \<Rightarrow>
                           Inr \<lparr> MF_Name = f, MF_Params = params, MF_Ret = retTy, MF_Body = S,
                                 MF_Extern = None \<rparr>))))"


section \<open>The generated main and the module (sections 3.8, 3.9)\<close>

(* int main(void) { <global initialisation>; <Core main>(); return 0; } *)
definition main_fun :: "string \<Rightarrow> MStmt list \<Rightarrow> MFun" where
  "main_fun mainName init =
    \<lparr> MF_Name = ''main'', MF_Params = [], MF_Ret = Some CTy_I32,
      MF_Body = init @ [MS_Call None mainName [], MS_Return (Some (ME_Int Signed IntBits_32 0))],
      MF_Extern = None \<rparr>"

(* The Core main must be a function with no type parameters, no
   parameters and the unit return type. *)
definition check_main :: "CoreModule \<Rightarrow> string \<Rightarrow> CGError option" where
  "check_main m mainName =
    (case (fmlookup (CM_Functions m) mainName, fmlookup (TE_Functions (CM_TyEnv m)) mainName) of
       (Some _, Some info) \<Rightarrow>
         if FI_TyArgs info = [] \<and> FI_TmArgs info = [] \<and> FI_ReturnType info = CoreTy_Record []
         then None else Some (CGE_MainWrongType mainName)
     | _ \<Rightarrow> Some (CGE_MainMissing mainName))"

(* The module-level name checks of section 3.9: no function or global
   named main (the generated main); no '$' in a function or global name;
   no global named like a function. (Function names are distinct because
   CM_Functions is a map; parameters and locals are checked per function.) *)
definition check_module_names :: "CoreModule \<Rightarrow> CGError option" where
  "check_module_names m =
    (let funNames = module_fun_names m;
         globNames = map fst (sorted_list_of_fmap (TE_GlobalVars (CM_TyEnv m)))
     in if ''main'' \<in> set funNames \<or> ''main'' \<in> set globNames then Some CGE_FunctionNamedMain
        else case find has_dollar (funNames @ globNames) of
               Some x \<Rightarrow> Some (CGE_DollarName x)
             | None \<Rightarrow>
                 (case find (\<lambda>g. g \<in> set funNames) globNames of
                    Some g \<Rightarrow> Some (CGE_GlobalIsFunction g)
                  | None \<Rightarrow> None))"

(* Lower every function, in name order. *)
fun lower_functions :: "CoreModule \<Rightarrow> (string, string) fmap \<Rightarrow> string fset \<Rightarrow> string fset
                        \<Rightarrow> (string \<times> CoreFunction) list \<Rightarrow> CGError + MFun list" where
  "lower_functions m cnames funNames usedNames [] = Inr []"
| "lower_functions m cnames funNames usedNames ((f, cf) # rest) =
    (case lower_function m cnames funNames usedNames f cf of
       Inl err \<Rightarrow> Inl err
     | Inr mf \<Rightarrow>
         (case lower_functions m cnames funNames usedNames rest of
            Inl err \<Rightarrow> Inl err
          | Inr mfs \<Rightarrow> Inr (mf # mfs)))"

(* The generator. cnames maps the Core name of an extern function to its C
   name; mainName is the Core main. *)
definition codegen_module :: "(string, string) fmap \<Rightarrow> string \<Rightarrow> CoreModule \<Rightarrow> CGError + MProgram" where
  "codegen_module cnames mainName m =
    (case check_module_names m of
       Some err \<Rightarrow> Inl err
     | None \<Rightarrow>
         (case check_main m mainName of
            Some err \<Rightarrow> Inl err
          | None \<Rightarrow>
              (let funNames = fset_of_list (module_fun_names m);
                   globNames = fmdom (TE_GlobalVars (CM_TyEnv m));
                   usedNames = funNames |\<union>| globNames |\<union>| {|''main''|};
                   gst = \<lparr> CS_Counter = 0, CS_Used = usedNames \<rparr>
               in case lower_globals m gst of
                    Inl err \<Rightarrow> Inl err
                  | Inr ((globals, init), gst') \<Rightarrow>
                      (case lower_functions m cnames funNames (CS_Used gst') (sorted_list_of_fmap (CM_Functions m)) of
                         Inl err \<Rightarrow> Inl err
                       | Inr funs \<Rightarrow>
                           Inr \<lparr> MP_Globals = globals, MP_Funcs = funs @ [main_fun mainName init] \<rparr>))))"


end

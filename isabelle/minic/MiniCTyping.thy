theory MiniCTyping
  imports MiniCSemantics
begin

(* ========================================================================== *)
(* MiniC: typing                                                              *)
(* ========================================================================== *)

(* A minimal typing judgement for MiniC programs, as an executable function.
   Its purpose is the typing theorem of the code generator (DESIGN.md,
   section 8): the generated program is well-typed, which is what makes the
   printed C acceptable to a C compiler. So it checks what a C compiler would
   check and the interpreter does not already check at run time:

    - every variable is declared before use, and not declared twice in the
      same scope (C forbids redeclaration in one scope; the interpreter would
      silently rebind);
    - no variable has the name of a function (C has one namespace for
      functions and variables; the interpreter keeps them apart);
    - expressions are typed: integer operands of a binop have the same type
      (except the count of a shift), loads and pointer arithmetic go through
      pointers, casts are integer-to-integer or pointer-to-pointer, literals
      fit their type;
    - assignments, stores, arguments and returns have compatible types, where
      the two pointer types are interchangeable (as in the semantics:
      val_has_ty (MV_Ptr p) ty = is_ptr_ty ty, and as in C, where void * and
      char * convert implicitly);
    - a call names a function of the program with the right number of
      arguments, and the result of a non-void call may be assigned to a scalar
      variable of its type; `return;` only in a void function, `return e;` only
      in a non-void one, with e of the return type.

   The judgement does not check that a non-void function body ends in a
   return (C allows falling off the end; the interpreter treats using the
   result as UB), nor anything about `break` (program_wf does).

   The printer (MiniCPrint.thy) uses expr_type to find the type of every
   arithmetic expression, because C's integer promotions would otherwise
   change the type (and, for ~ on a narrow unsigned type, the value) of the
   result. *)


section \<open>Environments\<close>

(* The static type of a variable: a scalar of a C type, or a byte buffer. *)
datatype MVarTy = VT_Scalar CTy | VT_Buf

type_synonym MTyEnv = "(string, MVarTy) fmap"

fun is_int_ty :: "CTy \<Rightarrow> bool" where
  "is_int_ty (CTy_Int _ _) = True"
| "is_int_ty _ = False"

(* Compatibility for assignment, argument passing and return: the same type,
   or both pointer types. *)
definition ty_compat :: "CTy \<Rightarrow> CTy \<Rightarrow> bool" where
  "ty_compat t1 t2 = (t1 = t2 \<or> (is_ptr_ty t1 \<and> is_ptr_ty t2))"

fun is_cmp :: "CBinop \<Rightarrow> bool" where
  "is_cmp CB_Eq = True"
| "is_cmp CB_Ne = True"
| "is_cmp CB_Lt = True"
| "is_cmp CB_Le = True"
| "is_cmp CB_Gt = True"
| "is_cmp CB_Ge = True"
| "is_cmp _ = False"

(* The environment of a program's globals. *)
definition global_var_ty :: "MGlobal \<Rightarrow> MVarTy" where
  "global_var_ty g = (case g of MG_Scalar ty \<Rightarrow> VT_Scalar ty | MG_Buf _ \<Rightarrow> VT_Buf)"

definition globals_env :: "MProgram \<Rightarrow> MTyEnv" where
  "globals_env prog = fmap_of_list (map (\<lambda>(x, g). (x, global_var_ty g)) (MP_Globals prog))"

(* All the names under which a function of the program is visible: its MiniC
   name and, for an extern, its C name. No variable may be called any of these. *)
definition fun_names :: "MProgram \<Rightarrow> string list" where
  "fun_names prog = map MF_Name (MP_Funcs prog) @ List.map_filter MF_Extern (MP_Funcs prog)"


section \<open>Expressions\<close>

fun expr_type :: "MTyEnv \<Rightarrow> MExpr \<Rightarrow> CTy option" where
  "expr_type env (ME_Int s b i) = (if int_fits s b i then Some (CTy_Int s b) else None)"
| "expr_type env ME_PtrSize = Some CTy_U64"
| "expr_type env (ME_Var x) =
    (case fmlookup env x of
       Some (VT_Scalar ty) \<Rightarrow> Some ty
     | _ \<Rightarrow> None)"
| "expr_type env (ME_AddrOf x) =
    (case fmlookup env x of
       Some _ \<Rightarrow> Some CTy_CharPtr
     | None \<Rightarrow> None)"
| "expr_type env (ME_Load ty e) =
    (case expr_type env e of
       Some pty \<Rightarrow> if is_ptr_ty pty then Some ty else None
     | None \<Rightarrow> None)"
| "expr_type env (ME_Unop op e) =
    (case expr_type env e of
       Some (CTy_Int s b) \<Rightarrow> (case op of CU_Not \<Rightarrow> Some CTy_U8 | _ \<Rightarrow> Some (CTy_Int s b))
     | _ \<Rightarrow> None)"
| "expr_type env (ME_Binop op e1 e2) =
    (case (expr_type env e1, expr_type env e2) of
       (Some (CTy_Int s1 b1), Some (CTy_Int s2 b2)) \<Rightarrow>
         if \<not> is_shift op \<and> (s1 \<noteq> s2 \<or> b1 \<noteq> b2) then None
         else if is_cmp op then Some CTy_U8
         else Some (CTy_Int s1 b1)
     | _ \<Rightarrow> None)"
| "expr_type env (ME_Cast ty e) =
    (case expr_type env e of
       Some ty' \<Rightarrow>
         if (is_int_ty ty \<and> is_int_ty ty') \<or> (is_ptr_ty ty \<and> is_ptr_ty ty') then Some ty else None
     | None \<Rightarrow> None)"
| "expr_type env (ME_PtrAdd e1 e2) =
    (case (expr_type env e1, expr_type env e2) of
       (Some pty, Some ity) \<Rightarrow> if is_ptr_ty pty \<and> is_int_ty ity then Some pty else None
     | _ \<Rightarrow> None)"

(* Does e have an integer type / a pointer type / a type compatible with ty? *)
definition expr_is_int :: "MTyEnv \<Rightarrow> MExpr \<Rightarrow> bool" where
  "expr_is_int env e = (case expr_type env e of Some ty \<Rightarrow> is_int_ty ty | None \<Rightarrow> False)"

definition expr_is_ptr :: "MTyEnv \<Rightarrow> MExpr \<Rightarrow> bool" where
  "expr_is_ptr env e = (case expr_type env e of Some ty \<Rightarrow> is_ptr_ty ty | None \<Rightarrow> False)"

definition expr_compat :: "MTyEnv \<Rightarrow> MExpr \<Rightarrow> CTy \<Rightarrow> bool" where
  "expr_compat env e ty = (case expr_type env e of Some ty' \<Rightarrow> ty_compat ty' ty | None \<Rightarrow> False)"


section \<open>Statements\<close>

(* The typing context of a function body: the program (for calls) and the
   declared return type. *)
record MTyCtx =
  TC_Prog :: MProgram
  TC_Ret  :: "CTy option"

(* A scope is the environment plus the names declared in the current (innermost)
   scope, which may not be declared again. *)
type_synonym MScope = "MTyEnv \<times> string list"

(* Declare a variable in a scope: it must not already be declared in the current
   scope, and must not be the name of a function. *)
definition sc_declare :: "MTyCtx \<Rightarrow> MScope \<Rightarrow> string \<Rightarrow> MVarTy \<Rightarrow> MScope option" where
  "sc_declare ctx sc x vty =
    (if x \<in> set (snd sc) \<or> x \<in> set (fun_names (TC_Prog ctx)) then None
     else Some (fmupd x vty (fst sc), x # snd sc))"

(* The arguments of a call are compatible with the parameters, pointwise. *)
fun args_compat :: "MTyEnv \<Rightarrow> MExpr list \<Rightarrow> (string \<times> CTy) list \<Rightarrow> bool" where
  "args_compat env [] [] = True"
| "args_compat env (e # es) ((_, ty) # ps) = (expr_compat env e ty \<and> args_compat env es ps)"
| "args_compat env _ _ = False"

(* stmt_ok returns the scope after the statement (declarations extend it);
   stmts_ok threads it through a list. A nested scope (if branches, loop body,
   block) starts with the current environment and no names of its own, and its
   result is discarded. *)
fun stmt_ok :: "MTyCtx \<Rightarrow> MScope \<Rightarrow> MStmt \<Rightarrow> MScope option"
and stmts_ok :: "MTyCtx \<Rightarrow> MScope \<Rightarrow> MStmt list \<Rightarrow> MScope option" where
  "stmt_ok ctx sc (MS_DeclScalar x ty) = sc_declare ctx sc x (VT_Scalar ty)"
| "stmt_ok ctx sc (MS_DeclBuf x e) =
    (if expr_is_int (fst sc) e then sc_declare ctx sc x VT_Buf else None)"
| "stmt_ok ctx sc (MS_Assign x e) =
    (case fmlookup (fst sc) x of
       Some (VT_Scalar ty) \<Rightarrow> if expr_compat (fst sc) e ty then Some sc else None
     | _ \<Rightarrow> None)"
| "stmt_ok ctx sc (MS_Store ty p e) =
    (if expr_is_ptr (fst sc) p \<and> expr_compat (fst sc) e ty then Some sc else None)"
| "stmt_ok ctx sc (MS_Copy d s n) =
    (if expr_is_ptr (fst sc) d \<and> expr_is_ptr (fst sc) s \<and> expr_is_int (fst sc) n then Some sc else None)"
| "stmt_ok ctx sc (MS_Zero p n) =
    (if expr_is_ptr (fst sc) p \<and> expr_is_int (fst sc) n then Some sc else None)"
| "stmt_ok ctx sc (MS_Uninit p n) =
    (if expr_is_ptr (fst sc) p \<and> expr_is_int (fst sc) n then Some sc else None)"
| "stmt_ok ctx sc (MS_If c t e) =
    (if expr_is_int (fst sc) c
        \<and> stmts_ok ctx (fst sc, []) t \<noteq> None
        \<and> stmts_ok ctx (fst sc, []) e \<noteq> None
     then Some sc else None)"
| "stmt_ok ctx sc (MS_Loop body) =
    (if stmts_ok ctx (fst sc, []) body \<noteq> None then Some sc else None)"
| "stmt_ok ctx sc MS_Break = Some sc"
| "stmt_ok ctx sc (MS_Block body) =
    (if stmts_ok ctx (fst sc, []) body \<noteq> None then Some sc else None)"
| "stmt_ok ctx sc (MS_Call xopt f args) =
    (case lookup_fun (TC_Prog ctx) f of
       None \<Rightarrow> None
     | Some fn \<Rightarrow>
         if \<not> args_compat (fst sc) args (MF_Params fn) then None
         else (case xopt of
                 None \<Rightarrow> Some sc
               | Some x \<Rightarrow>
                   (case (MF_Ret fn, fmlookup (fst sc) x) of
                      (Some rty, Some (VT_Scalar ty)) \<Rightarrow> if ty_compat rty ty then Some sc else None
                    | _ \<Rightarrow> None)))"
| "stmt_ok ctx sc (MS_Return None) = (if TC_Ret ctx = None then Some sc else None)"
| "stmt_ok ctx sc (MS_Return (Some e)) =
    (case TC_Ret ctx of
       Some ty \<Rightarrow> if expr_compat (fst sc) e ty then Some sc else None
     | None \<Rightarrow> None)"

| "stmts_ok ctx sc [] = Some sc"
| "stmts_ok ctx sc (s # ss) =
    (case stmt_ok ctx sc s of
       None \<Rightarrow> None
     | Some sc' \<Rightarrow> stmts_ok ctx sc' ss)"


section \<open>Functions and programs\<close>

(* The parameters of a function are declared, one by one, in the outermost
   scope of its body (so a parameter cannot be redeclared there, as in C). *)
fun declare_params :: "MTyCtx \<Rightarrow> MScope \<Rightarrow> (string \<times> CTy) list \<Rightarrow> MScope option" where
  "declare_params ctx sc [] = Some sc"
| "declare_params ctx sc ((x, ty) # ps) =
    (case sc_declare ctx sc x (VT_Scalar ty) of
       None \<Rightarrow> None
     | Some sc' \<Rightarrow> declare_params ctx sc' ps)"

(* An extern function has no body to check (its parameters are still checked
   against the function names, so that the printed prototype is valid C). *)
definition fun_ok :: "MProgram \<Rightarrow> MFun \<Rightarrow> bool" where
  "fun_ok prog f =
    (let ctx = \<lparr> TC_Prog = prog, TC_Ret = MF_Ret f \<rparr>
     in case declare_params ctx (globals_env prog, []) (MF_Params f) of
          None \<Rightarrow> False
        | Some sc \<Rightarrow> MF_Extern f \<noteq> None \<or> stmts_ok ctx sc (MF_Body f) \<noteq> None)"

(* A global: not named after a function; a buffer's size is a closed integer
   expression. *)
definition global_ok :: "MProgram \<Rightarrow> string \<times> MGlobal \<Rightarrow> bool" where
  "global_ok prog xg =
    (fst xg \<notin> set (fun_names prog)
     \<and> (case snd xg of
          MG_Scalar _ \<Rightarrow> True
        | MG_Buf e \<Rightarrow> expr_is_int fmempty e))"

definition program_well_typed :: "MProgram \<Rightarrow> bool" where
  "program_well_typed prog =
    (list_all (global_ok prog) (MP_Globals prog)
     \<and> list_all (fun_ok prog) (MP_Funcs prog))"


section \<open>Well-typed expressions evaluate to values of their type\<close>

(* The static environment describes the dynamic one: every variable in env is
   bound in the state to a variable of that kind (and type). *)
definition env_matches :: "MTyEnv \<Rightarrow> 'w MState \<Rightarrow> bool" where
  "env_matches env st =
    (\<forall>x vty. fmlookup env x = Some vty \<longrightarrow>
       (case vty of
          VT_Scalar ty \<Rightarrow> (\<exists>b. lookup_var st x = Some (MVar_Scalar ty b))
        | VT_Buf \<Rightarrow> (\<exists>b. lookup_var st x = Some (MVar_Buf b))))"

lemma c_compl_fits:
  assumes "int_fits s b i"
  shows "int_fits s b (c_compl s b i)"
proof (cases s)
  case Signed
  show ?thesis using assms unfolding Signed c_compl_def int_fits_signed by simp
next
  case Unsigned
  have "snd (int_range Unsigned b) = 2 ^ bit_size b - 1" by (cases b) simp_all
  then show ?thesis using assms unfolding Unsigned c_compl_def int_fits_unsigned by auto
qed

lemma eval_cmp_binop_is_cmp:
  "(eval_cmp_binop op i1 i2 = None) \<longleftrightarrow> \<not> is_cmp op"
  by (cases op) (simp_all add: eval_cmp_binop_def)

lemma eval_unop_has_ty:
  assumes "val_has_ty v (CTy_Int s b)" and "eval_unop op v = Some v'"
  shows "val_has_ty v' (if op = CU_Not then CTy_U8 else CTy_Int s b)"
proof -
  from assms(1) obtain i where v: "v = MV_Int s b i" and fits: "int_fits s b i"
    by (cases v) auto
  show ?thesis
    using assms(2) fits c_compl_fits[OF fits]
    by (cases op) (auto simp: v eval_unop_def bool_val_def split: if_splits)
qed

lemma eval_binop_has_ty:
  assumes "val_has_ty v1 (CTy_Int s1 b1)" and "val_has_ty v2 (CTy_Int s2 b2)"
    and "eval_binop op v1 v2 = Some v"
  shows "val_has_ty v (if is_cmp op then CTy_U8 else CTy_Int s1 b1)"
proof -
  from assms(1) obtain i1 where v1: "v1 = MV_Int s1 b1 i1" by (cases v1) auto
  from assms(2) obtain i2 where v2: "v2 = MV_Int s2 b2 i2" by (cases v2) auto
  show ?thesis
    using assms(3) eval_cmp_binop_is_cmp[of op i1 i2]
    by (auto simp: v1 v2 eval_binop_def bool_val_def split: if_splits option.splits)
qed

lemma eval_cast_has_ty:
  assumes "eval_cast ty v = Some v'"
  shows "val_has_ty v' ty"
  using assms by (cases ty; cases v) (auto simp: eval_cast_def split: if_splits)

lemma expr_type_sound:
  assumes "valid_encoding enc" and "env_matches env st"
  shows "expr_type env e = Some ty \<Longrightarrow> eval_expr enc st e = Some v \<Longrightarrow> val_has_ty v ty"
proof (induction e arbitrary: ty v)
  case (ME_Int s b i)
  then show ?case by (auto split: if_splits)
next
  case ME_PtrSize
  then show ?case
    using valid_encoding_ptr_size_fits[OF assms(1)] by auto
next
  case (ME_Var x)
  from ME_Var.prems(1) have lk: "fmlookup env x = Some (VT_Scalar ty)"
    by (auto split: option.splits MVarTy.splits)
  obtain b where "lookup_var st x = Some (MVar_Scalar ty b)"
    using assms(2)[unfolded env_matches_def, rule_format, OF lk] by auto
  with ME_Var.prems(2) have "mem_load enc (MS_Mem st) ty (MP_Addr b 0) = Some v" by simp
  then show ?case using mem_load_has_ty[OF assms(1)] by simp
next
  case (ME_AddrOf x)
  then show ?case by (auto split: option.splits)
next
  case (ME_Load ty' e)
  then show ?case
    using mem_load_has_ty[OF assms(1)]
    by (auto split: option.splits MVal.splits if_splits)
next
  case (ME_Unop op e)
  then obtain s b where ety: "expr_type env e = Some (CTy_Int s b)"
    and ty: "ty = (if op = CU_Not then CTy_U8 else CTy_Int s b)"
    by (auto split: option.splits CTy.splits CUnop.splits)
  from ME_Unop.prems(2) obtain v0 where ev: "eval_expr enc st e = Some v0"
    and un: "eval_unop op v0 = Some v"
    by (auto split: option.splits)
  have "val_has_ty v0 (CTy_Int s b)" using ME_Unop.IH[OF ety ev] .
  then show ?case using eval_unop_has_ty[OF _ un] ty by simp
next
  case (ME_Binop op e1 e2)
  then obtain s1 b1 s2 b2 where ety1: "expr_type env e1 = Some (CTy_Int s1 b1)"
    and ety2: "expr_type env e2 = Some (CTy_Int s2 b2)"
    and ty: "ty = (if is_cmp op then CTy_U8 else CTy_Int s1 b1)"
    by (auto split: option.splits CTy.splits if_splits)
  from ME_Binop.prems(2) obtain v1 v2 where ev1: "eval_expr enc st e1 = Some v1"
    and ev2: "eval_expr enc st e2 = Some v2" and bin: "eval_binop op v1 v2 = Some v"
    by (auto split: option.splits)
  have "val_has_ty v1 (CTy_Int s1 b1)" using ME_Binop.IH(1)[OF ety1 ev1] .
  moreover have "val_has_ty v2 (CTy_Int s2 b2)" using ME_Binop.IH(2)[OF ety2 ev2] .
  ultimately show ?case using eval_binop_has_ty[OF _ _ bin] ty by simp
next
  case (ME_Cast ty' e)
  then show ?case
    using eval_cast_has_ty by (auto split: option.splits if_splits)
next
  case (ME_PtrAdd e1 e2)
  then obtain pty where ety1: "expr_type env e1 = Some pty"
    and ty: "ty = pty" and ptr: "is_ptr_ty pty"
    by (auto split: option.splits if_splits)
  from ME_PtrAdd.prems(2) obtain v1 where ev1: "eval_expr enc st e1 = Some v1"
    and v: "\<exists>p. v = MV_Ptr p"
    by (auto split: option.splits MVal.splits)
  then show ?case using ty ptr by auto
qed

end

theory CodeGenEnv
  imports RepVal SizeBound "HOL-Library.Monad_Syntax"
begin

(* ========================================================================== *)
(* The code generator: errors, state, environment, names                      *)
(* (minic/DESIGN.md, sections 3.1, 3.5 and 3.9)                               *)
(* ========================================================================== *)

(* This theory holds everything the lowering functions of CodeGenTerm.thy
   and CodeGen.thy share: the structured error type, the generator monad (a
   state of fresh-name information, or an error), the representation of
   Core variables (section 3.5), the generator environment CGEnv, and the
   small helpers that build MiniC types, sizes and offsets from Core types.

   The environment is the interface over which stage 6's per-frame state
   relation is written, so it is a plain record of plain data: one
   constructor of VarRep per representation kind, and a lazy reference is
   an explicit syntax tree (LazyLv) rather than a Core term, so that it
   captures the MiniC representation of its base variable rather than the
   base's Core name (a Core name may be shadowed in a nested scope while
   the reference is live; a MiniC name of this generator never is, see
   below). *)


section \<open>Errors\<close>

(* Every failure of the generator is a value of this type, with a message
   in the user's terms (cg_error_to_strings in CodeGen.thy). The CGE_Internal
   cases cannot happen on well-typed, ghost-free, flat input; they are
   reported as internal compiler errors. *)
datatype CGError =
    CGE_MainMissing string                 \<comment> \<open>the main function does not exist\<close>
  | CGE_MainWrongType string               \<comment> \<open>main has type parameters, parameters or a non-unit return type\<close>
  | CGE_FunctionNamedMain                  \<comment> \<open>a Core function or global is named "main"\<close>
  | CGE_DollarName string                  \<comment> \<open>a function, global, parameter, local or type parameter name contains '$'\<close>
  | CGE_NameIsFunction string string       \<comment> \<open>in function f, a parameter or local named like a function\<close>
  | CGE_GlobalIsFunction string            \<comment> \<open>a global named like a function\<close>
  | CGE_DuplicateParam string string       \<comment> \<open>function, parameter declared twice\<close>
  | CGE_ParamCount string                  \<comment> \<open>the parameter names and the signature disagree in number\<close>
  | CGE_GlobalHandle string                \<comment> \<open>a global holds a non-null extern handle\<close>
  | CGE_Ghost string                       \<comment> \<open>function: a ghost construct survived erasure\<close>
  | CGE_Internal string string             \<comment> \<open>function (or global), message\<close>


section \<open>The generator monad\<close>

(* The state: a counter for fresh names and the set of every MiniC name in
   use in the current function (the function and global names of the
   program, the parameters, every local and every temporary declared so
   far). A fresh name is checked against the set, so that freshness is a
   fact the generator established rather than a property of a naming
   scheme; see fresh_name below. *)
record CGState =
  CS_Counter :: nat
  CS_Used    :: "string fset"

type_synonym 'a CG = "CGState \<Rightarrow> CGError + ('a \<times> CGState)"

definition cg_return :: "'a \<Rightarrow> 'a CG" where
  "cg_return x st = Inr (x, st)"

definition cg_fail :: "CGError \<Rightarrow> 'a CG" where
  "cg_fail e st = Inl e"

definition cg_bind :: "'a CG \<Rightarrow> ('a \<Rightarrow> 'b CG) \<Rightarrow> 'b CG" where
  "cg_bind m f st = (case m st of Inl e \<Rightarrow> Inl e | Inr (x, st') \<Rightarrow> f x st')"

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> cg_bind

(* The congruence rule that lets the function package see through a bind:
   the continuation is only called on the result of the first computation. *)
lemma cg_bind_cong [fundef_cong]:
  assumes "m = m'"
    and "\<And>x st st'. m' st = Inr (x, st') \<Longrightarrow> f x st' = f' x st'"
  shows "cg_bind m f = cg_bind m' f'"
proof (rule ext)
  fix st
  show "cg_bind m f st = cg_bind m' f' st"
    using assms unfolding cg_bind_def by (auto split: sum.splits prod.splits)
qed

lemma cg_bind_return [simp]: "cg_bind (cg_return x) f = f x"
  by (rule ext) (simp add: cg_bind_def cg_return_def)

lemma cg_bind_fail [simp]: "cg_bind (cg_fail e) f = cg_fail e"
  by (rule ext) (simp add: cg_bind_def cg_fail_def)

lemma cg_bind_InrE:
  assumes "cg_bind m f st = Inr (y, st'')"
  obtains x st' where "m st = Inr (x, st')" and "f x st' = Inr (y, st'')"
  using assms unfolding cg_bind_def by (auto split: sum.splits prod.splits)

lemma cg_return_Inr [simp]: "cg_return x st = Inr (y, st') \<longleftrightarrow> y = x \<and> st' = st"
  by (auto simp: cg_return_def)

lemma cg_fail_Inr [simp]: "cg_fail e st = Inr r \<longleftrightarrow> False"
  by (simp add: cg_fail_def)

(* Lift an option: None is an internal error with the given message. *)
definition cg_lift :: "string \<Rightarrow> string \<Rightarrow> 'a option \<Rightarrow> 'a CG" where
  "cg_lift f msg opt = (case opt of None \<Rightarrow> cg_fail (CGE_Internal f msg) | Some x \<Rightarrow> cg_return x)"

(* Thread a monadic function through a list. *)
fun cg_mapM :: "('a \<Rightarrow> 'b CG) \<Rightarrow> 'a list \<Rightarrow> 'b list CG" where
  "cg_mapM f [] = cg_return []"
| "cg_mapM f (x # xs) = do { y \<leftarrow> f x; ys \<leftarrow> cg_mapM f xs; cg_return (y # ys) }"

lemma cg_mapM_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "cg_mapM f xs = cg_mapM g ys"
  using assms by (induction ys arbitrary: xs) auto

definition cg_get :: "CGState CG" where
  "cg_get st = Inr (st, st)"

definition cg_put :: "CGState \<Rightarrow> unit CG" where
  "cg_put st' st = Inr ((), st')"


section \<open>Names\<close>

(* Every MiniC name the generator introduces is unique within its function
   (and every global name within the program), which is stronger than the
   per-scope distinctness that C and program_well_typed require. The
   reason is shadowing: Core allows a nested scope (a block, a match arm,
   a Let body) to rebind a name that an outer scope bound, and a lazy
   reference (section 3.5) declared in the outer scope must keep
   addressing the outer variable after the inner one is declared. With
   unique MiniC names a lazy reference may simply mention the MiniC name of
   its base. Moreover, two sibling Lets of the same name
   (test/cases/codegen/Let.b) would otherwise declare one C variable twice
   in one scope.

   The scheme: a Core variable keeps its own name if that name is not yet
   in use in the function, and otherwise gets hint$n with the counter
   value n; temporaries are hint$n. Core names never contain '$' (checked
   before generating, section 3.9), so the two kinds cannot collide, and
   the counter makes the hint$n names distinct from each other; but the
   generator does not rely on either fact: every new name is tested
   against the set of names in use and an (impossible) repetition is an
   internal error. The typing proof therefore only needs "the names in
   scope are among those in use". *)

definition dollar :: char where "dollar = CHR 0x24"

definition has_dollar :: "string \<Rightarrow> bool" where
  "has_dollar s = (dollar \<in> set s)"

definition fresh_name :: "string \<Rightarrow> string \<Rightarrow> string CG" where
  "fresh_name f hint st =
    (let n = hint @ [dollar] @ nat_to_string (CS_Counter st)
     in if n |\<in>| CS_Used st then Inl (CGE_Internal f (''fresh name '' @ n @ '' already in use''))
        else Inr (n, st \<lparr> CS_Counter := Suc (CS_Counter st), CS_Used := finsert n (CS_Used st) \<rparr>))"

(* The MiniC name of a Core local variable: its own name if available,
   else a fresh name with that hint. *)
definition local_name :: "string \<Rightarrow> string \<Rightarrow> string CG" where
  "local_name f x st =
    (if x |\<in>| CS_Used st then fresh_name f x st
     else Inr (x, st \<lparr> CS_Used := finsert x (CS_Used st) \<rparr>))"

(* Reserve a name that must be exactly this (a parameter): an error if it
   is already in use. *)
definition reserve_name :: "CGError \<Rightarrow> string \<Rightarrow> unit CG" where
  "reserve_name err x st =
    (if x |\<in>| CS_Used st then Inl err
     else Inr ((), st \<lparr> CS_Used := finsert x (CS_Used st) \<rparr>))"

lemma fresh_name_Inr:
  assumes "fresh_name f hint st = Inr (n, st')"
  shows "n |\<notin>| CS_Used st" and "CS_Used st' = finsert n (CS_Used st)"
    and "n = hint @ [dollar] @ nat_to_string (CS_Counter st)"
  using assms by (auto simp: fresh_name_def Let_def simp del: nat_to_string.simps split: if_splits)

lemma local_name_Inr:
  assumes "local_name f x st = Inr (n, st')"
  shows "n |\<notin>| CS_Used st" and "CS_Used st' = finsert n (CS_Used st)"
  using assms by (auto simp: local_name_def fresh_name_def Let_def simp del: nat_to_string.simps split: if_splits)

lemma reserve_name_Inr:
  assumes "reserve_name err x st = Inr (u, st')"
  shows "x |\<notin>| CS_Used st" and "CS_Used st' = finsert x (CS_Used st)"
  using assms by (auto simp: reserve_name_def split: if_splits)

(* The size parameter of a type parameter T, and the return buffer
   parameter (section 3.4). *)
definition size_param :: "string \<Rightarrow> string" where
  "size_param v = ''size'' @ [dollar] @ v"

definition ret_param :: string where
  "ret_param = ''ret'' @ [dollar]"

(* The unqualified part of a qualified Core name (after the last '.'), for
   the C name of an extern function that has no explicit one (section 3.9). *)
definition unqualified :: "string \<Rightarrow> string" where
  "unqualified s = rev (takeWhile (\<lambda>c. c \<noteq> CHR ''.'') (rev s))"


section \<open>C types, sizes and offsets of Core types\<close>

(* The C scalar type of a scalar Core type is scalar_ty (RepVal.thy):
   bool is uint8_t, iN/uN are themselves, an extern type is void *. An
   aggregate type has none; its values are byte buffers. *)
abbreviation "is_scalar ty \<equiv> scalar_ty ty \<noteq> None"

(* The type-variable map for size expressions inside a function body: the
   size of T is the parameter size$T. *)
definition size_tv :: "string \<Rightarrow> MExpr" where
  "size_tv v = ME_Var (size_param v)"

(* The size of a Core type as a uint64_t expression (section 3.2). *)
definition size_of :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> MExpr" where
  "size_of env ty = size_expr env size_tv ty"

(* The size of a buffer declaration: at least one byte (C forbids
   zero-length arrays; risk 12). Folded when the size is a literal. *)
definition buf_size :: "MExpr \<Rightarrow> MExpr" where
  "buf_size e = e_max (u64_lit 1) e"

(* p + off, with a zero literal offset folded away. *)
definition ptr_add :: "MExpr \<Rightarrow> MExpr \<Rightarrow> MExpr" where
  "ptr_add p off = (if off = u64_lit 0 then p else ME_PtrAdd p off)"

(* The offset of a field of a record type. *)
definition field_off :: "CoreTyEnv \<Rightarrow> (string \<times> CoreType) list \<Rightarrow> string \<Rightarrow> MExpr" where
  "field_off env flds f = field_offset_expr env size_tv flds f"

(* The payload offset of a variant: the size of its tag, as a literal. *)
definition tag_off :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> MExpr" where
  "tag_off env dtName = u64_lit (tag_size env dtName)"

(* The tag of a constructor as a literal of the tag type. *)
definition tag_lit :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> string \<Rightarrow> MExpr" where
  "tag_lit env dtName ctor = ME_Int Unsigned (tag_bits env dtName) (int (ctor_tag env dtName ctor))"

(* The offset of dimension k of a descriptor: ptrsize + 8k. *)
definition dim_off :: "nat \<Rightarrow> MExpr" where
  "dim_off k = e_add ME_PtrSize (u64_lit (8 * k))"

(* The dimensions of a fixed array as literals. *)
definition fixed_dim_exprs :: "CoreDimension list \<Rightarrow> MExpr list" where
  "fixed_dim_exprs dims = map (\<lambda>d. u64_lit (dim_size d)) dims"

(* The run-time dimensions of a descriptor at place p. *)
definition desc_dim_exprs :: "MExpr \<Rightarrow> nat \<Rightarrow> MExpr list" where
  "desc_dim_exprs p d = map (\<lambda>k. ME_Load CTy_U64 (ptr_add p (dim_off k))) [0..<d]"

(* The data pointer of a descriptor at place p. *)
definition desc_data :: "MExpr \<Rightarrow> MExpr" where
  "desc_data p = ME_Load CTy_CharPtr p"

(* The address of element idx (index expressions) of an array of the
   given element type and dimensions at place p: for fixed dimensions the
   element is inside the bytes at p; for a descriptor it is in the data
   block. The result is a MiniC expression that evaluates p several times
   (once for the data pointer and once per dimension); p is pure. *)
definition elem_addr :: "CoreTyEnv \<Rightarrow> CoreType \<Rightarrow> CoreDimension list \<Rightarrow> MExpr \<Rightarrow> MExpr list \<Rightarrow> MExpr" where
  "elem_addr env elemTy dims p idxs =
    (if dims_all_fixed dims
     then ptr_add p (elem_offset_expr (size_of env elemTy) (fixed_dim_exprs dims) idxs)
     else ME_PtrAdd (desc_data p)
            (elem_offset_expr (size_of env elemTy) (desc_dim_exprs p (length dims)) idxs))"

(* Does an array type have an allocatable dimension? Such an array may be
   reallocated through a ref, so references into it are lazy (section 3.5). *)
definition has_alloc_dim :: "CoreType \<Rightarrow> bool" where
  "has_alloc_dim ty = (case ty of CoreTy_Array _ dims \<Rightarrow> CoreDim_Allocatable \<in> set dims | _ \<Rightarrow> False)"

(* Is a parameter of the given declared type passed as a pointer? Scalars
   go by value, everything else (aggregates, and type variables, whose
   instantiation is unknown to the callee) as char *. Refs are always
   pointers. docs/c-interface.md, "Calling C Functions from Babylon". *)
definition param_by_ptr :: "CoreType \<Rightarrow> VarOrRef \<Rightarrow> bool" where
  "param_by_ptr ty vor = (vor = Ref \<or> \<not> is_scalar ty)"

definition param_cty :: "CoreType \<Rightarrow> VarOrRef \<Rightarrow> CTy" where
  "param_cty ty vor = (if param_by_ptr ty vor then CTy_CharPtr else the (scalar_ty ty))"

(* How a function returns, by its declared return type: a scalar in the
   C return value; the unit type as void; any other aggregate (type
   variables included) through the return buffer parameter. *)
datatype RetKind = RK_Scalar CTy | RK_Unit | RK_Buf

definition ret_kind :: "CoreType \<Rightarrow> RetKind" where
  "ret_kind ty =
    (case scalar_ty ty of
       Some cty \<Rightarrow> RK_Scalar cty
     | None \<Rightarrow> if ty = CoreTy_Record [] then RK_Unit else RK_Buf)"


section \<open>Representations of Core variables\<close>

(* How a Core variable in scope is represented (the table of section 3.5):
    - VR_Scalar x cty: a MiniC scalar variable x of type cty holding the
      value (a mutable local, parameter, Let variable or global of scalar
      type). Read: ME_Var x. Address: ME_AddrOf x.
    - VR_Buf x: a MiniC buffer variable x holding the bytes (a mutable
      local or global of aggregate type). Place and address: ME_AddrOf x.
    - VR_Ptr x: a MiniC char * variable x holding the address of the bytes
      (an aggregate by-value parameter, an aggregate Let variable, a ref
      parameter of any type, a non-lazy ref local). Read: ME_Load cty
      (ME_Var x) if scalar, else the place ME_Var x. Address: ME_Var x.
    - VR_Lazy ll: a lazy ref local; the address is recomputed from ll at
      every use.
   The Core type of the variable is not recorded here; the generator finds
   it by typing the term. *)
datatype VarRep =
    VR_Scalar string CTy
  | VR_Buf string
  | VR_Ptr string
  | VR_Lazy LazyLv

(* A lazy reference: the lvalue it was declared with, with its base
   variable's representation captured (never VR_Lazy: a lazy base is
   inlined) and each array index evaluated into a fresh uint64_t variable
   at the declaration. Every node carries the Core type of the sub-lvalue
   it denotes, so that offsets can be computed without re-typing. *)
and LazyLv =
    LL_Base VarRep CoreType
  | LL_Field LazyLv string CoreType
  | LL_Payload LazyLv string CoreType
  | LL_Index LazyLv "string list" CoreType
  | LL_Cast LazyLv CoreType

fun ll_type :: "LazyLv \<Rightarrow> CoreType" where
  "ll_type (LL_Base _ ty) = ty"
| "ll_type (LL_Field _ _ ty) = ty"
| "ll_type (LL_Payload _ _ ty) = ty"
| "ll_type (LL_Index _ _ ty) = ty"
| "ll_type (LL_Cast _ ty) = ty"


section \<open>The environment\<close>

(* The generator's environment for a function body:
    - CG_TyEnv: the Core typing context at this point, threaded exactly as
      core_statement_type and core_term_type thread it (the generator
      re-types every term with it);
    - CG_Vars: the representation of every Core variable in scope (globals
      included; locals shadow them);
    - CG_Ret: how the enclosing function returns;
    - CG_Fun: the name of the enclosing function, for error messages. *)
record CGEnv =
  CG_TyEnv :: CoreTyEnv
  CG_Vars  :: "(string, VarRep) fmap"
  CG_Ret   :: RetKind
  CG_Fun   :: string

(* The Core type of a term (the input is well-typed, so this succeeds;
   failure is an internal error). *)
definition ty_of :: "CGEnv \<Rightarrow> CoreTerm \<Rightarrow> CoreType CG" where
  "ty_of cg tm = cg_lift (CG_Fun cg) ''term does not typecheck'' (core_term_type (CG_TyEnv cg) NotGhost tm)"

definition cg_size :: "CGEnv \<Rightarrow> CoreType \<Rightarrow> MExpr" where
  "cg_size cg ty = size_of (CG_TyEnv cg) ty"

definition internal :: "CGEnv \<Rightarrow> string \<Rightarrow> 'a CG" where
  "internal cg msg = cg_fail (CGE_Internal (CG_Fun cg) msg)"

(* Bind a Core variable to a representation, extending the typing context
   as the typechecker does for the binder (the caller passes the new
   context). *)
definition cg_bind_var :: "CGEnv \<Rightarrow> CoreTyEnv \<Rightarrow> string \<Rightarrow> VarRep \<Rightarrow> CGEnv" where
  "cg_bind_var cg env' x rep = cg \<lparr> CG_TyEnv := env', CG_Vars := fmupd x rep (CG_Vars cg) \<rparr>"

(* The context inside a nested statement scope (the typechecker clears the
   proof-top-level flag; nothing else changes). *)
definition cg_nested :: "CGEnv \<Rightarrow> CGEnv" where
  "cg_nested cg = cg \<lparr> CG_TyEnv := (CG_TyEnv cg) \<lparr> TE_ProofTopLevel := False \<rparr> \<rparr>"

end

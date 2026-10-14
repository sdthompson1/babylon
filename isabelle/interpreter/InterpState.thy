theory InterpState
  imports "../core/CoreValue"
begin

(* Lvalue path component *)
datatype LValuePath =
  LVPath_RecordProj string
  | LVPath_VariantProj string
  | LVPath_ArrayProj "int list"
  | LVPath_ArrayCast "CoreDimension list"


(* Externally defined functions *)
(* The function is passed a "world" and the arguments, and returns new world, new
   values of any ref arguments, and return value *)
type_synonym 'w ExternFunc = "'w \<Rightarrow> CoreValue list \<Rightarrow> 'w \<times> CoreValue list \<times> CoreValue"


(* Function info for the interpreter *)
record 'w InterpFun =
  (* Type arguments *)
  IF_TyArgs :: "string list"

  (* Term arguments (name, and whether passed by value or reference) *)
  IF_Args :: "(string \<times> VarOrRef) list"

  (* The function body: Inl for a Babylon body (list of statements), or
     Inr for an external function. *)
  IF_Body :: "CoreStatement list + 'w ExternFunc"

  (* Whether the function is marked "impure" (i.e. is allowed to read or
     write to the external world). *)
  IF_Impure :: bool

  (* The function's contract, as in FI_Requires / FI_Ensures. These refer to the
     parameters by the positional names of ContractNames.thy. *)
  IF_Requires :: "CoreTerm list"
  IF_Ensures :: "CoreTerm list"


(* Interpreter state *)
record 'world InterpState =

  (* Global constants: map to their value *)
  IS_Globals :: "(string, CoreValue) fmap"

  (* Local variables: map to address in the store *)
  IS_Locals :: "(string, nat) fmap"

  (* Ref variables: map to address and path in the store *)
  IS_Refs :: "(string, nat \<times> LValuePath list) fmap"

  (* Store: maps address to value *)
  IS_Store :: "CoreValue list"

  (* Names of read-only variables (constants).
     The interpreter will produce a TypeError if an attempt is made to
     assign to or swap any of these names. This is a subset of the local
     names appearing in IS_Locals \<union> IS_Refs; globals (IS_Globals) are
     implicitly read-only and do not need to be listed here. *)
  IS_ConstLocals :: "string fset"

  (* Runtime type-variable bindings for the current function frame.
     Maps each type parameter (by name) to a ground CoreType. *)
  IS_TyArgs :: "(string, CoreType) fmap"

  (* The datatypes of the program (name to number of type parameters), their
     data constructors (constructor name to datatype name, type parameters and
     payload type), and each datatype's constructors in declaration order.
     These are copies of the type environment's TE_Datatypes, TE_DataCtors
     and TE_DataCtorsByType tables. The first constructor in a datatype's
     list is the one used to evaluate CoreTm_Default at that datatype. *)
  IS_Datatypes :: "(string, nat) fmap"
  IS_DataCtors :: "(string, string \<times> string list \<times> CoreType) fmap"
  IS_DataCtorsByType :: "(string, string list) fmap"

  (* Available functions (only includes non-ghost functions) *)
  IS_Functions :: "(string, 'world InterpFun) fmap"

  (* Current "world state" for extern functions *)
  IS_World :: 'world

  (* Allocation oracle for extern types. Given an extern type (identified by
     its name and alloc level) and a handle, this determines whether that handle
     counts as "allocated". This is a question that is decided by the external
     environment, not the interpreter itself.

     Note that the interpreter does not consult IS_ExternAlloc n l h when
     l = CoreAlloc_IfNotDefault and h = 0, or at all when l = CoreAlloc_Never;
     this means that an oracle cannot "override" the built-in assumptions about
     allocated-ness of CoreAlloc_IfNotDefault or CoreAlloc_Never types. *)
  IS_ExternAlloc :: "string \<Rightarrow> CoreAllocLevel \<Rightarrow> nat \<Rightarrow> bool"

end

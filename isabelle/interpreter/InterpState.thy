theory InterpState
  imports CoreValue
begin

(* Lvalue path component *)
datatype LValuePath =
  LVPath_RecordProj string
  | LVPath_VariantProj string
  | LVPath_ArrayProj "int list"

(* Externally defined functions *)
(* The function is passed a "world" and the arguments, and returns new world, new
   values of any ref arguments, and return value *)
type_synonym 'w ExternFunc = "'w \<Rightarrow> CoreValue list \<Rightarrow> 'w \<times> CoreValue list \<times> CoreValue"

(* Function info for the interpreter *)
record 'w InterpFun =
  IF_Args :: "(string \<times> VarOrRef) list"
  IF_Body :: "CoreStatement list + 'w ExternFunc"
  IF_Impure :: bool

(* Interpreter state *)
record 'world InterpState =

  (* Local variables: map to address in the store *)
  IS_Locals :: "(string, nat) fmap"

  (* Ref variables: map to address and path in the store *)
  IS_Refs :: "(string, nat \<times> LValuePath list) fmap"

  (* Store: maps address to value *)
  IS_Store :: "CoreValue list"

  (* Global constants: map to their value *)
  IS_Constants :: "(string, CoreValue) fmap"

  (* Available functions (only includes non-ghost functions) *)
  IS_Functions :: "(string, 'world InterpFun) fmap"

  (* Current "world state" for extern functions *)
  IS_World :: 'world


end

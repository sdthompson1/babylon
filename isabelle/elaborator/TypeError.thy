theory TypeError
  imports "../bab/Location" "../bab/BabSyntax" "../core/CoreSyntax"
begin

(* Possible errors returned by the elaborator *)

(* TODO: Review these. Also, we probably should not be including core types here?? *)

datatype TypeError =
  TyErr_OutOfFuel Location
  | TyErr_IntLiteralOutOfRange Location
  | TyErr_InvalidCast Location
  | TyErr_NegateRequiresSigned Location
  | TyErr_ComplementRequiresFiniteInt Location
  | TyErr_NotRequiresBool Location
  | TyErr_UnknownName Location string
  | TyErr_GhostVariableInNonGhost Location string
  | TyErr_WrongNumberOfTypeArgs Location string nat nat  (* name, expected, actual *)
  | TyErr_DataCtorHasPayload Location string  (* For non-nullary constructors used without args *)
  | TyErr_NonRuntimeTypeArg Location
  | TyErr_TypeMismatch Location CoreType CoreType  (* loc, type1, type2 *)
  | TyErr_ConditionNotBool Location CoreType       (* loc, actual condition type *)
  | TyErr_MetavariableInInput                      (* metavariable found in input type *)
  | TyErr_UnknownTypeName Location string
  | TyErr_WrongTypeArity Location string nat nat   (* name, expected, actual *)
  | TyErr_InvalidArrayDimension Location
  (* Function call errors *)
  | TyErr_UnknownFunction Location string
  | TyErr_CalleeNotFunction Location
  | TyErr_ImpureFunctionInTermContext Location string
  | TyErr_RefArgInTermContext Location string
  | TyErr_GhostFunctionInNonGhost Location string
  | TyErr_WrongNumberOfArgs Location string nat nat  (* name, expected, actual *)
  | TyErr_FunctionNoReturnType Location string
  | TyErr_ArgTypeMismatch Location nat CoreType CoreType  (* loc, arg index, expected, actual *)

end

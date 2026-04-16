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
  | TyErr_NonRuntimeType Location
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
  (* Binary operator errors *)
  | TyErr_BinopRequiresNumeric Location BabBinop
  | TyErr_BinopRequiresInteger Location BabBinop
  | TyErr_BinopRequiresFiniteInteger Location BabBinop
  | TyErr_BinopRequiresBool Location BabBinop
  | TyErr_BinopCannotCombineTypes Location BabBinop CoreType CoreType
  | TyErr_EqualityRequiresBoolOrNumeric Location
  (* Chain errors *)
  | TyErr_MixedOperatorsInChain Location
  | TyErr_MixedDirectionsInChain Location
  | TyErr_InternalError_UnexpectedChainVar Location
  (* Type inference errors *)
  | TyErr_CannotInferType Location
  (* Record errors *)
  | TyErr_DuplicateFieldName Location string
  | TyErr_NotARecordType Location CoreType
  | TyErr_FieldNotFound Location string CoreType  (* field name, record type *)
  | TyErr_TupleIndexOutOfRange Location nat CoreType  (* index, tuple type *)
  | TyErr_RequiresGhostContext Location
  | TyErr_NotAnArrayType Location CoreType
  | TyErr_SizeofRequiresLvalue Location
  | TyErr_QuantifierBodyNotBool Location CoreType
  | TyErr_UpdateFieldNotFound Location string CoreType  (* field name, record type *)
  | TyErr_UpdateFieldTypeMismatch Location string CoreType CoreType  (* field, expected, actual *)

end

theory TypeError
  imports "../bab/Location" "../bab/BabSyntax" "../core/CoreSyntax"
begin

(* Possible errors returned by the elaborator *)

datatype TypeError =
  (* Miscellaneous errors *)
  TyErr_OutOfFuel Location
  | TyErr_IntLiteralOutOfRange Location
  | TyErr_InvalidCast Location
  (* Ghost errors *)
  | TyErr_RequiresGhostContext Location
  | TyErr_GhostVariableInNonGhost Location string
  | TyErr_GhostFunctionInNonGhost Location string
  | TyErr_GhostTypeInNonGhost Location
  (* Type mismatch errors *)
  | TyErr_TypeMismatch Location CoreType CoreType  (* loc, type1, type2 *)
  | TyErr_SignedTypeRequired Location CoreType
  | TyErr_NumericTypeRequired Location CoreType
  | TyErr_IntegerTypeRequired Location CoreType
  | TyErr_FiniteIntegerTypeRequired Location CoreType
  (* Kind errors (wrong number of type args) *)
  | TyErr_WrongNumberOfTypeArgs Location string nat nat  (* name, expected, actual *)
  (* Function/data-constructor call errors *)
  | TyErr_CalleeNotFunction Location
  | TyErr_ImpureFunctionInTermContext Location string
  | TyErr_RefArgInTermContext Location string
  | TyErr_WrongNumberOfArgs Location string nat nat  (* name, expected, actual *)
  | TyErr_FunctionNoReturnType Location string
  | TyErr_DataCtorHasPayload Location string  (* For non-nullary constructors used without args *)
  (* Binary operator errors *)
  | TyErr_BinopCannotCombineTypes Location BabBinop CoreType CoreType
  | TyErr_EqualityRequiresBoolOrNumeric Location
  (* Chain errors *)
  | TyErr_MixedOperatorsInChain Location
  | TyErr_MixedDirectionsInChain Location
  (* Type inference errors *)
  | TyErr_CannotInferType Location
  (* Record/tuple errors *)
  | TyErr_DuplicateFieldName Location string
  | TyErr_NotARecordType Location CoreType
  | TyErr_FieldNotFound Location string CoreType  (* field name, record type *)
  | TyErr_TupleIndexOutOfRange Location nat CoreType  (* index, tuple type *)
  (* Sizeof errors *)
  | TyErr_SizeofRequiresLvalue Location
  (* Array errors *)
  | TyErr_NotAnArrayType Location CoreType
  | TyErr_WrongNumberOfIndices Location nat nat  (* expected (= num dims), actual *)
  | TyErr_InvalidArrayDimension Location
  (* Pattern errors *)
  | TyErr_DuplicateVarInPattern Location string  (* variable name bound twice in one pattern *)
  | TyErr_RefPatternInTermContext Location string  (* `ref` binding used in a term-context match *)
  | TyErr_EmptyMatch Location  (* match expression with zero arms *)
  (* Internal errors *)
  | TyErr_InternalError_NameNotFound Location string  (* should have been caught by the renamer *)
  | TyErr_InternalError_UnexpectedChainVar Location

end

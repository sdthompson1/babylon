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
  | TyErr_GhostFunctionInNonGhost Location string  (* executable code tried to call a ghost function *)
  | TyErr_GhostTypeInNonGhost Location
  | TyErr_WriteToNonGhostFromGhost Location  (* ghost code attempting to write a non-ghost variable (assignment, swap, or ref argument) *)
  | TyErr_GhostRefNeedsGhostVar Location string  (* a ref declared in ghost code must refer to a ghost variable; string = ref/pattern var name *)
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
  (* Variable declaration errors *)
  | TyErr_VarDeclNeedsTypeOrValue Location  (* `var x;` with neither type annotation nor initializer *)
  | TyErr_RefDeclNeedsValue Location  (* `ref x;` with no initializer *)
  | TyErr_RefDeclNeedsLvalue Location  (* `ref x = e;` where e is not an lvalue *)
  (* Assignment errors *)
  | TyErr_NotWritableLvalue Location  (* assignment lhs is not a writable lvalue *)
  (* Return errors *)
  | TyErr_VoidReturnWithValue Location  (* `return e;` in a void function *)
  | TyErr_NonVoidReturnNeedsValue Location  (* `return;` in a non-void function *)
  | TyErr_ReturnInGhostContext Location  (* `return` in a ghost block of an executable function *)
  (* Assert errors *)
  | TyErr_AssertStarNoGoal Location  (* `assert *` with no enclosing proof goal *)
  (* Fix errors *)
  | TyErr_FixNoForallGoal Location  (* `fix x` with no enclosing universally-quantified proof goal *)
  | TyErr_FixNotAtProofTopLevel Location  (* `fix x` nested inside a match/while in a proof body *)
  (* Use errors *)
  | TyErr_UseNoExistsGoal Location  (* `use e` with no enclosing existentially-quantified proof goal *)
  (* While errors *)
  | TyErr_InvalidWhileAttribute Location  (* a while attribute other than `invariant` or `decreases` *)
  | TyErr_WhileNeedsOneDecreases Location  (* a while loop without exactly one `decreases` attribute *)
  | TyErr_InvalidDecreasesType Location CoreType  (* `decreases e` where e's type is not a valid decreases type *)
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
  | TyErr_RefPatternNeedsLvalue Location string  (* `ref` binding in a match statement whose scrutinee is not an lvalue *)
  | TyErr_EmptyMatch Location  (* match expression with zero arms *)
  (* Internal errors *)
  | TyErr_InternalError_NameNotFound Location string  (* should have been caught by the renamer *)
  | TyErr_InternalError_UnexpectedChainVar Location
  | TyErr_InternalError_FreshnameClash Location string  (* synthesised match@@n name collided with a free var or pattern var *)
  | TyErr_InternalError_IllKindedProofGoal Location  (* a stored proof goal contained an ill-kinded quantifier type — impossible, as goals come from elaborated (well-typed) Asserts *)

end

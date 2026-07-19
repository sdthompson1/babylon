theory TypeError
  imports "../bab/Location" "../bab/BabSyntax" "../core/CoreSyntax"
    "../interpreter/CoreInterp"  (* for InterpError *)
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
  | TyErr_DataCtorNotCallable Location string  (* For payload-less constructors used with call syntax *)
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
  | TyErr_UseNotAtProofTopLevel Location  (* `use e` nested inside a match/while in a proof body *)
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

  (* Declaration/Module level errors *)
  | TyErr_DuplicateName Location string  (* declaration name (or constructor / type parameter) already in scope *)
  | TyErr_AlreadyDefined Location string  (* second definition of a declared constant or function *)
  | TyErr_ConstDeclNeedsType Location string  (* `const x;` with neither type annotation nor value *)
  | TyErr_FunctionSignatureMismatch Location string  (* a function definition's signature differs from its earlier declaration *)
  | TyErr_NotCompileTimeConstant Location  (* a non-ghost global initializer contains a function call *)
  | TyErr_ConstValueNotVisible Location string  (* a constant initializer references a constant with no visible value (e.g. an opaque imported constant) *)
  | TyErr_ConstEvalError Location InterpError  (* compile-time evaluation of a constant initializer failed (e.g. overflow, match failure, array index out of bounds) *)
  | TyErr_ConstAbstractType Location  (* a constant initializer mentions an abstract (unrealized) type, so it cannot be evaluated at compile time (e.g. an empty array literal at an opaque imported element type) *)
  | TyErr_ExternFunctionWithBody Location string  (* an extern function may not also have a body *)
  | TyErr_InvalidFunctionAttribute Location  (* an attribute other than requires/ensures/decreases on a function *)
  | TyErr_EmptyDatatype Location string  (* datatype with no constructors *)
  | TyErr_TypeArgsNotAllowed Location string  (* type arguments on an abstract type declaration or realization *)
  | TyErr_CannotRealizeImportedType Location string  (* giving a definition to an abstract type this module did not declare *)
  | TyErr_GhostRealizationOfRuntimeType Location string  (* a non-ghost abstract type realized by a non-runtime type *)
  | TyErr_SelfReferentialType Location string  (* a realization's target mentions the name being realized *)
  | TyErr_TypeVarCapture Location string  (* a type parameter collides with an abstract type or type substitution *)
  | TyErr_ExternTypeNotImplemented Location  (* `extern type` is not currently supported *)

  | TyErr_DeclarationOnlyInImplementation Location string  (* a declaration without a definition in an implementation *)
  | TyErr_DeclaredButNotDefined Location string  (* a declared constant or function that the module never defines *)
  | TyErr_AbstractTypeNotRealized Location string  (* an abstract type the implementation never realizes *)
  | TyErr_RecursiveDeclarations Location "string list"  (* a declaration referencing itself, or a cycle of declarations *)

  (* Internal errors *)
  | TyErr_InternalError_NameNotFound Location string  (* should have been caught by the renamer *)
  | TyErr_InternalError_DependencyAnalysis Location  (* declaration dependency analysis failed; cannot happen (duplicates are pre-checked, dependencies are filtered to declared names) *)
  | TyErr_InternalError_UnexpectedChainVar Location
  | TyErr_InternalError_FreshnameClash Location string  (* synthesised match@@n name collided with a free var or pattern var *)
  | TyErr_InternalError_IllKindedProofGoal Location  (* a stored proof goal contained an ill-kinded quantifier type — impossible, as goals come from elaborated (well-typed) Asserts *)
  | TyErr_InternalError_InvalidTypeVarName Location string  (* a declaration binds a type variable whose name begins with '?' (reserved for metavariables); the parser cannot produce such a name *)

end

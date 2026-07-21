theory TypeError
  imports "../bab/Location" "../bab/BabSyntax" "../core/CoreSyntax"
    "../interpreter/CoreInterp"  (* for InterpError *)
begin

(* Possible errors returned by the elaborator *)

datatype (plugins del: size "quickcheck" transfer lifting) TypeError =
  (* Out of fuel *)
  TyErr_OutOfFuel Location

  (* Kind mismatches (wrong number of type args) *)
  | TyErr_WrongNumberOfTypeArgs Location string nat nat  (* name, expected, actual *)

  (* Type mismatches *)
  | TyErr_TypeMismatch Location CoreType CoreType  (* loc, type1, type2 *)
  | TyErr_SignedTypeRequired Location CoreType
  | TyErr_NumericTypeRequired Location CoreType
  | TyErr_IntegerTypeRequired Location CoreType
  | TyErr_FiniteIntegerTypeRequired Location CoreType

  (* Binary operator errors *)
  | TyErr_BinopCannotCombineTypes Location BabBinop CoreType CoreType
  | TyErr_EqualityRequiresBoolOrNumeric Location
  | TyErr_MixedOperatorsInChain Location
  | TyErr_MixedDirectionsInChain Location

  (* Function/data-constructor call errors *)
  | TyErr_CalleeNotFunction Location
  | TyErr_ImpureFunctionInTermContext Location string
  | TyErr_RefArgInTermContext Location string
  | TyErr_WrongNumberOfArgs Location string nat nat  (* name, expected, actual *)
  | TyErr_FunctionNoReturnType Location string
  | TyErr_DataCtorHasPayload Location string  (* For non-nullary constructors used without args *)
  | TyErr_DataCtorNotCallable Location string  (* For payload-less constructors used with call syntax *)

  (* Record/tuple errors *)
  | TyErr_DuplicateFieldName Location string
  | TyErr_NotARecordType Location CoreType
  | TyErr_FieldNotFound Location string CoreType  (* field name, record type *)
  | TyErr_TupleIndexOutOfRange Location nat CoreType  (* index, tuple type *)

  (* Sizeof and Array errors *)
  | TyErr_SizeofRequiresLvalue Location
  | TyErr_NotAnArrayType Location CoreType
  | TyErr_WrongNumberOfIndices Location nat nat  (* expected (= num dims), actual *)
  | TyErr_InvalidArrayDimension Location

  (* Other type errors *)
  | TyErr_IntLiteralOutOfRange Location
  | TyErr_InvalidCast Location

  (* Type inference failure *)
  | TyErr_CannotInferType Location

  (* Incorrect ghost usage *)
  | TyErr_RequiresGhostContext Location
  | TyErr_GhostVariableInNonGhost Location string
  | TyErr_GhostFunctionInNonGhost Location string  (* executable code tried to call a ghost function *)
  | TyErr_GhostTypeInNonGhost Location
  | TyErr_WriteToNonGhostFromGhost Location  (* ghost code attempting to write a non-ghost variable (assignment, swap, or ref argument) *)
  | TyErr_GhostRefNeedsGhostVar Location string  (* a ref declared in ghost code must refer to a ghost variable; string = ref/pattern var name *)

  (* Statement errors *)
  | TyErr_VarDeclNeedsTypeOrValue Location  (* `var x;` with neither type annotation nor initializer *)
  | TyErr_RefDeclNeedsValue Location  (* `ref x;` with no initializer *)
  | TyErr_RefDeclNeedsLvalue Location  (* `ref x = e;` where e is not an lvalue *)
  | TyErr_NotWritableLvalue Location  (* assignment lhs is not a writable lvalue *)
  | TyErr_VoidReturnWithValue Location  (* `return e;` in a void function *)
  | TyErr_NonVoidReturnNeedsValue Location  (* `return;` in a non-void function *)
  | TyErr_ReturnInGhostContext Location  (* `return` in a ghost block of an executable function *)
  | TyErr_InvalidWhileAttribute Location  (* a while attribute other than `invariant` or `decreases` *)
  | TyErr_WhileNeedsOneDecreases Location  (* a while loop without exactly one `decreases` attribute *)
  | TyErr_InvalidDecreasesType Location CoreType  (* `decreases e` where e's type is not a valid decreases type *)
  | TyErr_AssertStarNoGoal Location  (* `assert *` with no enclosing proof goal *)
  | TyErr_FixNoForallGoal Location  (* `fix x` with no enclosing universally-quantified proof goal *)
  | TyErr_FixNotAtProofTopLevel Location  (* `fix x` nested inside a match/while in a proof body *)
  | TyErr_UseNoExistsGoal Location  (* `use e` with no enclosing existentially-quantified proof goal *)
  | TyErr_UseNotAtProofTopLevel Location  (* `use e` nested inside a match/while in a proof body *)

  (* Pattern errors *)
  | TyErr_DuplicateVarInPattern Location string  (* variable name bound twice in one pattern *)
  | TyErr_RefPatternInTermContext Location string  (* `ref` binding used in a term-context match *)
  | TyErr_RefPatternNeedsLvalue Location string  (* `ref` binding in a match statement whose scrutinee is not an lvalue *)
  | TyErr_EmptyMatch Location  (* match expression with zero arms *)
  | TyErr_IntPatternOutOfRange Location CoreType  (* integer literal pattern out of range for the (finite integer) scrutinee type *)

  (* Declaration/Module level errors *)
  | TyErr_DuplicateName Location string  (* a constant, function, constructor, parameter, etc., was defined twice *)
  | TyErr_ConstDeclNeedsType Location string  (* `const x;` with neither type annotation nor value *)
  | TyErr_NotCompileTimeConstant Location  (* a non-ghost global initializer contains a function call *)
  | TyErr_ConstValueNotVisible Location string  (* a constant initializer references a constant with no visible value (e.g. an opaque imported constant) *)
  | TyErr_ConstEvalError Location InterpError  (* compile-time evaluation of a constant initializer failed (e.g. overflow, match failure, array index out of bounds) *)
  | TyErr_ConstAbstractType Location  (* a constant initializer mentions an abstract (unrealized) type, so it cannot be evaluated at compile time (e.g. an empty array literal at an opaque imported element type) *)
  | TyErr_InvalidFunctionAttribute Location  (* an attribute other than requires/ensures/decreases on a function *)
  | TyErr_FunctionSignatureMismatch Location string  (* a function definition's signature differs from its earlier declaration *)
  | TyErr_ConstGhostnessMismatch Location string  (* a const definition's ghostness differs from an earlier declaration of the same name *)
  | TyErr_ExternFunctionWithBody Location string  (* an extern function may not also have a body *)
  | TyErr_EmptyDatatype Location string  (* datatype with no constructors *)
  | TyErr_TypeArgsNotAllowed Location string  (* type arguments on an abstract type declaration or realization *)
  | TyErr_CannotRealizeImportedType Location string  (* giving a definition to an abstract type
        not declared by this module face's own interface: either an imported type (impossible on
        renamer output) or, reachably, an interface realizing its own abstract type (realizations
        belong in the implementation) *)
  | TyErr_GhostRealizationOfRuntimeType Location string  (* a non-ghost abstract type realized by a ghost-only type *)
  | TyErr_SelfReferentialType Location string  (* a realization's target mentions the name being realized *)
  | TyErr_TypeVarCapture Location string  (* a type parameter collides with an abstract type or type substitution (impossible in renamer output) *)
  | TyErr_ExternTypeNotImplemented Location  (* `extern type` is not currently supported *)
  | TyErr_DeclarationOnlyInImplementation Location string  (* a declaration without definition in an implementation section *)
  | TyErr_DeclaredButNotDefined Location string  (* a declared constant or function that the module never defines *)
  | TyErr_AbstractTypeNotRealized Location string  (* an abstract type the implementation never realizes *)
  | TyErr_RecursiveDeclarations Location "string list"  (* a declaration referencing itself, or a cycle of declarations *)

  (* Naming errors (should be impossible) *)
  | TyErr_NameNotFound Location string  (* name not found, should have been caught by renamer *)
  | TyErr_UnexpectedNameClash Location  (* chain@@, match@@ or ? name in input, parser should have rejected *)

  (* Other unexpected errors *)
  | TyErr_DependencyAnalysisUnexpectedFailure Location  (* dependency sorter failed *)
  | TyErr_IllKindedProofGoal Location  (* stored proof goal contained ill-kinded type — impossible, as goals come from elaborated (well-typed) Asserts *)

end

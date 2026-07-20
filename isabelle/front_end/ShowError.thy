(* ShowError converts the various compiler error types into human-readable strings.

   This is used by CodeExport.thy to report errors back to the driver program
   (Main.hs). The exact message wording is unimportant (and in particular does not
   have to match the C implementation of the compiler); the messages just need to
   be reasonable for a human to read.
*)

theory ShowError
  imports
    FrontEnd
    "../elaborator/ElabProgram"
    "../util/NatToString"
begin

(*-----------------------------------------------------------------------------*)
(* Basic string helpers *)
(*-----------------------------------------------------------------------------*)

(* Join a list of strings using a separator *)
fun intercalate :: "string \<Rightarrow> string list \<Rightarrow> string" where
  "intercalate sep [] = ''''"
| "intercalate sep [x] = x"
| "intercalate sep (x # xs) = x @ sep @ intercalate sep xs"

(* Wrap a string in single-quotes *)
definition quote :: "string \<Rightarrow> string" where
  "quote s = CHR 39 # s @ [CHR 39]"

(* Convert an int to a string in decimal notation *)
definition int_to_string :: "int \<Rightarrow> string" where
  "int_to_string i =
     (if i < 0 then CHR ''-'' # nat_to_string (nat (- i))
      else nat_to_string (nat i))"

(* Render a location as "filename:line:col" (using the start of the location) *)
fun location_to_string :: "Location \<Rightarrow> string" where
  "location_to_string (Location filename line1 col1 _ _) =
     filename @ '':'' @ int_to_string line1 @ '':'' @ int_to_string col1"

(* Standard "location: " prefix for error messages *)
definition loc_prefix :: "Location \<Rightarrow> string" where
  "loc_prefix loc = location_to_string loc @ '': ''"


(*-----------------------------------------------------------------------------*)
(* Types *)
(*-----------------------------------------------------------------------------*)

definition finite_int_name :: "Signedness \<Rightarrow> IntBits \<Rightarrow> string" where
  "finite_int_name sgnd nbits =
     (case sgnd of Signed \<Rightarrow> ''i'' | Unsigned \<Rightarrow> ''u'') @
     (case nbits of
        IntBits_8 \<Rightarrow> ''8''
      | IntBits_16 \<Rightarrow> ''16''
      | IntBits_32 \<Rightarrow> ''32''
      | IntBits_64 \<Rightarrow> ''64'')"

fun core_dimension_to_string :: "CoreDimension \<Rightarrow> string" where
  "core_dimension_to_string CoreDim_Unknown = ''''"
| "core_dimension_to_string CoreDim_Allocatable = ''*''"
| "core_dimension_to_string (CoreDim_Fixed n) = int_to_string n"

(* Render a CoreType using (approximately) Babylon source syntax.
   A record whose field names are ''0'', ''1'', ... is shown as a tuple. *)
fun core_type_to_string :: "CoreType \<Rightarrow> string" where
  "core_type_to_string (CoreTy_Datatype name tyArgs) =
     name @ (if tyArgs = [] then ''''
             else ''<'' @ intercalate '', '' (map core_type_to_string tyArgs) @ ''>'')"
| "core_type_to_string CoreTy_Bool = ''bool''"
| "core_type_to_string (CoreTy_FiniteInt sgnd nbits) = finite_int_name sgnd nbits"
| "core_type_to_string CoreTy_MathInt = ''int''"
| "core_type_to_string CoreTy_MathReal = ''real''"
| "core_type_to_string (CoreTy_Record flds) =
     (if map fst flds = tuple_field_names (length flds)
      then ''{'' @ intercalate '', '' (map (core_type_to_string \<circ> snd) flds) @ ''}''
      else ''{'' @ intercalate '', ''
                     (map (\<lambda>f. fst f @ '': '' @ core_type_to_string (snd f)) flds) @ ''}'')"
| "core_type_to_string (CoreTy_Array elemTy dims) =
     core_type_to_string elemTy
       @ ''['' @ intercalate '','' (map core_dimension_to_string dims) @ '']''"
| "core_type_to_string (CoreTy_Var name) = name"

(* Quoted type, for use within error messages *)
definition quote_type :: "CoreType \<Rightarrow> string" where
  "quote_type ty = quote (core_type_to_string ty)"


(*-----------------------------------------------------------------------------*)
(* Operators *)
(*-----------------------------------------------------------------------------*)

fun binop_to_string :: "BabBinop \<Rightarrow> string" where
  "binop_to_string BabBinop_Add = ''+''"
| "binop_to_string BabBinop_Subtract = ''-''"
| "binop_to_string BabBinop_Multiply = ''*''"
| "binop_to_string BabBinop_Divide = ''/''"
| "binop_to_string BabBinop_Modulo = ''%''"
| "binop_to_string BabBinop_BitAnd = ''&''"
| "binop_to_string BabBinop_BitOr = ''|''"
| "binop_to_string BabBinop_BitXor = ''^''"
| "binop_to_string BabBinop_ShiftLeft = ''<<''"
| "binop_to_string BabBinop_ShiftRight = ''>>''"
| "binop_to_string BabBinop_Equal = ''==''"
| "binop_to_string BabBinop_NotEqual = ''!=''"
| "binop_to_string BabBinop_Less = ''<''"
| "binop_to_string BabBinop_LessEqual = ''<=''"
| "binop_to_string BabBinop_Greater = ''>''"
| "binop_to_string BabBinop_GreaterEqual = ''>=''"
| "binop_to_string BabBinop_And = ''&&''"
| "binop_to_string BabBinop_Or = ''||''"
| "binop_to_string BabBinop_Implies = ''==>''"
| "binop_to_string BabBinop_ImpliedBy = ''<==''"
| "binop_to_string BabBinop_Iff = ''<==>''"


(*-----------------------------------------------------------------------------*)
(* Front-end (loader and renamer) errors *)
(*-----------------------------------------------------------------------------*)

fun post_parse_error_to_string :: "PostParseError \<Rightarrow> string" where
  "post_parse_error_to_string PPE_MixedArrayDimension =
     ''array dimensions must be all fixed, all unsized, or all allocatable''"
| "post_parse_error_to_string PPE_OldOutsidePostcondition =
     quote ''old'' @ '' used outside a postcondition''"
| "post_parse_error_to_string PPE_OldUsedWithReturn =
     quote ''old'' @ '' cannot be applied to '' @ quote ''return''"
| "post_parse_error_to_string PPE_DataCtorWrongCase =
     ''data constructor name has incorrect case''"

fun loader_error_to_string :: "LoaderError \<Rightarrow> string" where
  "loader_error_to_string (LoaderError_RootModuleNotFound pkgName modName) =
     ''root module '' @ quote modName @ '' not found in package '' @ quote pkgName"
| "loader_error_to_string (LoaderError_BadDependency pkgName depName) =
     ''package '' @ quote pkgName @ '' depends on unknown package '' @ quote depName"
| "loader_error_to_string (LoaderError_BadExportedModule pkgName modName) =
     ''package '' @ quote pkgName @ '' exports unknown module '' @ quote modName"
| "loader_error_to_string (LoaderError_WrongModuleName expected actual) =
     ''module name mismatch: expected '' @ quote expected
       @ '' but the file declares '' @ quote actual"
| "loader_error_to_string (LoaderError_LexError loc) =
     loc_prefix loc @ ''lexical error''"
| "loader_error_to_string (LoaderError_ParseError loc) =
     loc_prefix loc @ ''parse error''"
| "loader_error_to_string (LoaderError_PostParseError loc err) =
     loc_prefix loc @ post_parse_error_to_string err"
| "loader_error_to_string (LoaderError_ImportNotFound loc modName) =
     loc_prefix loc @ ''imported module '' @ quote modName @ '' not found''"
| "loader_error_to_string (LoaderError_AmbiguousImport loc modName pkgNames) =
     loc_prefix loc @ ''import of module '' @ quote modName
       @ '' is ambiguous: found in packages ''
       @ intercalate '', '' (map quote pkgNames)"

fun rename_error_to_string :: "RenameError \<Rightarrow> string" where
  "rename_error_to_string (RenameError_NotInScopeTerm loc name) =
     loc_prefix loc @ ''not in scope: '' @ quote name"
| "rename_error_to_string (RenameError_NotInScopeType loc name) =
     loc_prefix loc @ ''not in scope: type '' @ quote name"
| "rename_error_to_string (RenameError_AmbiguousTerm loc name candidates) =
     loc_prefix loc @ ''name '' @ quote name @ '' is ambiguous: could be ''
       @ intercalate '', '' (map quote candidates)"
| "rename_error_to_string (RenameError_AmbiguousType loc name candidates) =
     loc_prefix loc @ ''type name '' @ quote name @ '' is ambiguous: could be ''
       @ intercalate '', '' (map quote candidates)"
| "rename_error_to_string (RenameError_ModuleNotFound loc name) =
     loc_prefix loc @ ''module not found: '' @ quote name"
| "rename_error_to_string (RenameError_DuplicateAlias loc name) =
     loc_prefix loc @ ''multiple imports of module '' @ quote name"
| "rename_error_to_string (RenameError_DuplicateDefinition loc name) =
     loc_prefix loc @ quote name @ '' is already defined in this scope''"
| "rename_error_to_string (RenameError_ReturnVarOutsidePostcond loc) =
     loc_prefix loc @ quote ''return'' @ '' used as a variable outside a postcondition''"
| "rename_error_to_string (RenameError_ReturnVarVoidFunction loc) =
     loc_prefix loc @ quote ''return''
       @ '' used as a variable in the postcondition of a function with no return value''"

fun frontend_error_to_string :: "FrontEndError \<Rightarrow> string" where
  "frontend_error_to_string (FrontEndError_Loader err) = loader_error_to_string err"
| "frontend_error_to_string (FrontEndError_Renamer err) = rename_error_to_string err"


(*-----------------------------------------------------------------------------*)
(* Dependency and link errors *)
(*-----------------------------------------------------------------------------*)

fun dependency_error_to_string :: "DependencyError \<Rightarrow> string" where
  "dependency_error_to_string (DepErr_DuplicateName name) =
     ''duplicate name '' @ quote name"
| "dependency_error_to_string (DepErr_DependencyNotFound depender dependee) =
     quote depender @ '' depends on '' @ quote dependee @ '', which was not found''"

fun bab_dependency_error_to_string :: "BabDependencyError \<Rightarrow> string" where
  "bab_dependency_error_to_string (BabDepErr_CircularDependency loc names) =
     loc_prefix loc @ ''circular dependency between modules: ''
       @ intercalate '', '' (map quote names)"
| "bab_dependency_error_to_string (BabDepErr_SelfImport loc name) =
     loc_prefix loc @ ''module '' @ quote name @ '' imports itself''"
| "bab_dependency_error_to_string (BabDepErr_Other err) =
     dependency_error_to_string err"

fun link_error_to_string :: "LinkError \<Rightarrow> string" where
  "link_error_to_string (LinkConflict names) =
     ''multiple definitions of: '' @ intercalate '', '' (map quote names)"
| "link_error_to_string (LinkCycle names) =
     ''cyclic type definitions involving: '' @ intercalate '', '' (map quote names)"
| "link_error_to_string (LinkCapture names) =
     ''type variable capture involving: '' @ intercalate '', '' (map quote names)"
| "link_error_to_string (LinkGhostResolution names) =
     ''non-ghost abstract type realized by ghost type: ''
       @ intercalate '', '' (map quote names)"


(*-----------------------------------------------------------------------------*)
(* Interpreter errors (arising from compile-time evaluation of constants) *)
(*-----------------------------------------------------------------------------*)

definition interp_error_to_string :: "InterpError \<Rightarrow> string" where
  "interp_error_to_string err =
     (case err of
        TypeError \<Rightarrow> ''type error''
      | RuntimeError \<Rightarrow>
          ''runtime error (such as overflow, division by zero, or an array index out of bounds)''
      | InsufficientFuel \<Rightarrow> ''evaluation did not terminate within the fuel limit'')"


(*-----------------------------------------------------------------------------*)
(* Type errors *)
(*-----------------------------------------------------------------------------*)

(* Note: this is written as a "definition" using a case expression, rather than a
   "fun", because the function package is slow when processing a function with this
   many cases. *)
definition type_error_to_string :: "TypeError \<Rightarrow> string" where
  "type_error_to_string err =
    (case err of
      TyErr_OutOfFuel loc \<Rightarrow>
        loc_prefix loc @ ''elaboration ran out of fuel''
    | TyErr_WrongNumberOfTypeArgs loc name expected actual \<Rightarrow>
        loc_prefix loc @ quote name @ '' expects '' @ nat_to_string expected
          @ '' type argument(s) but '' @ nat_to_string actual @ '' were given''
    | TyErr_TypeMismatch loc expectedTy actualTy \<Rightarrow>
        loc_prefix loc @ ''type mismatch: expected '' @ quote_type expectedTy
          @ '' but found '' @ quote_type actualTy
    | TyErr_SignedTypeRequired loc ty \<Rightarrow>
        loc_prefix loc @ ''signed integer type required, but found '' @ quote_type ty
    | TyErr_NumericTypeRequired loc ty \<Rightarrow>
        loc_prefix loc @ ''numeric type required, but found '' @ quote_type ty
    | TyErr_IntegerTypeRequired loc ty \<Rightarrow>
        loc_prefix loc @ ''integer type required, but found '' @ quote_type ty
    | TyErr_FiniteIntegerTypeRequired loc ty \<Rightarrow>
        loc_prefix loc @ ''finite integer type required, but found '' @ quote_type ty
    | TyErr_BinopCannotCombineTypes loc binop ty1 ty2 \<Rightarrow>
        loc_prefix loc @ ''operator '' @ quote (binop_to_string binop)
          @ '' cannot be applied to '' @ quote_type ty1 @ '' and '' @ quote_type ty2
    | TyErr_EqualityRequiresBoolOrNumeric loc \<Rightarrow>
        loc_prefix loc @ ''equality comparison requires boolean or numeric operands''
    | TyErr_MixedOperatorsInChain loc \<Rightarrow>
        loc_prefix loc @ ''cannot mix equality and ordering operators in an operator chain''
    | TyErr_MixedDirectionsInChain loc \<Rightarrow>
        loc_prefix loc @ ''cannot mix comparison directions in an operator chain''
    | TyErr_CalleeNotFunction loc \<Rightarrow>
        loc_prefix loc @ ''this is not a function, so it cannot be called''
    | TyErr_ImpureFunctionInTermContext loc name \<Rightarrow>
        loc_prefix loc @ ''impure function '' @ quote name
          @ '' cannot be called in an expression context''
    | TyErr_RefArgInTermContext loc name \<Rightarrow>
        loc_prefix loc @ ''function '' @ quote name @ '' takes '' @ quote ''ref''
          @ '' arguments, so it cannot be called in an expression context''
    | TyErr_WrongNumberOfArgs loc name expected actual \<Rightarrow>
        loc_prefix loc @ quote name @ '' expects '' @ nat_to_string expected
          @ '' argument(s) but '' @ nat_to_string actual @ '' were given''
    | TyErr_FunctionNoReturnType loc name \<Rightarrow>
        loc_prefix loc @ ''function '' @ quote name @ '' does not return a value''
    | TyErr_DataCtorHasPayload loc name \<Rightarrow>
        loc_prefix loc @ ''data constructor '' @ quote name @ '' requires a payload''
    | TyErr_DataCtorNotCallable loc name \<Rightarrow>
        loc_prefix loc @ ''data constructor '' @ quote name @ '' does not take a payload''
    | TyErr_DuplicateFieldName loc name \<Rightarrow>
        loc_prefix loc @ ''duplicate field name '' @ quote name
    | TyErr_NotARecordType loc ty \<Rightarrow>
        loc_prefix loc @ ''record or tuple type required, but found '' @ quote_type ty
    | TyErr_FieldNotFound loc name ty \<Rightarrow>
        loc_prefix loc @ ''field '' @ quote name @ '' not found in type '' @ quote_type ty
    | TyErr_TupleIndexOutOfRange loc idx ty \<Rightarrow>
        loc_prefix loc @ ''tuple index '' @ nat_to_string idx
          @ '' is out of range for type '' @ quote_type ty
    | TyErr_SizeofRequiresLvalue loc \<Rightarrow>
        loc_prefix loc @ quote ''sizeof'' @ '' requires an lvalue argument''
    | TyErr_NotAnArrayType loc ty \<Rightarrow>
        loc_prefix loc @ ''array type required, but found '' @ quote_type ty
    | TyErr_WrongNumberOfIndices loc expected actual \<Rightarrow>
        loc_prefix loc @ ''wrong number of array indices: expected ''
          @ nat_to_string expected @ '' but found '' @ nat_to_string actual
    | TyErr_InvalidArrayDimension loc \<Rightarrow>
        loc_prefix loc @ ''invalid array dimension''
    | TyErr_IntLiteralOutOfRange loc \<Rightarrow>
        loc_prefix loc @ ''integer literal out of range''
    | TyErr_InvalidCast loc \<Rightarrow>
        loc_prefix loc @ ''invalid cast''
    | TyErr_CannotInferType loc \<Rightarrow>
        loc_prefix loc @ ''unable to infer type''
    | TyErr_RequiresGhostContext loc \<Rightarrow>
        loc_prefix loc @ ''this construct is only allowed in ghost code''
    | TyErr_GhostVariableInNonGhost loc name \<Rightarrow>
        loc_prefix loc @ ''ghost variable '' @ quote name @ '' used in executable code''
    | TyErr_GhostFunctionInNonGhost loc name \<Rightarrow>
        loc_prefix loc @ ''ghost function '' @ quote name @ '' called from executable code''
    | TyErr_GhostTypeInNonGhost loc \<Rightarrow>
        loc_prefix loc @ ''ghost type used in executable code''
    | TyErr_WriteToNonGhostFromGhost loc \<Rightarrow>
        loc_prefix loc @ ''ghost code cannot write to a non-ghost variable''
    | TyErr_GhostRefNeedsGhostVar loc name \<Rightarrow>
        loc_prefix loc @ ''ref '' @ quote name
          @ '' is declared in ghost code, so it must refer to a ghost variable''
    | TyErr_VarDeclNeedsTypeOrValue loc \<Rightarrow>
        loc_prefix loc @ ''variable declaration requires a type or an initial value''
    | TyErr_RefDeclNeedsValue loc \<Rightarrow>
        loc_prefix loc @ ''ref declaration requires an initial value''
    | TyErr_RefDeclNeedsLvalue loc \<Rightarrow>
        loc_prefix loc @ ''ref declaration requires an lvalue initializer''
    | TyErr_NotWritableLvalue loc \<Rightarrow>
        loc_prefix loc @ ''left-hand side of assignment is not a writable lvalue''
    | TyErr_VoidReturnWithValue loc \<Rightarrow>
        loc_prefix loc @ ''cannot return a value from a function with no return type''
    | TyErr_NonVoidReturnNeedsValue loc \<Rightarrow>
        loc_prefix loc @ quote ''return'' @ '' requires a value in this function''
    | TyErr_ReturnInGhostContext loc \<Rightarrow>
        loc_prefix loc @ quote ''return''
          @ '' is not allowed in a ghost block of an executable function''
    | TyErr_InvalidWhileAttribute loc \<Rightarrow>
        loc_prefix loc @ ''invalid attribute on '' @ quote ''while'' @ '' loop: only ''
          @ quote ''invariant'' @ '' and '' @ quote ''decreases'' @ '' are allowed''
    | TyErr_WhileNeedsOneDecreases loc \<Rightarrow>
        loc_prefix loc @ quote ''while'' @ '' loop must have exactly one ''
          @ quote ''decreases'' @ '' attribute''
    | TyErr_InvalidDecreasesType loc ty \<Rightarrow>
        loc_prefix loc @ ''invalid type for '' @ quote ''decreases'' @ '': '' @ quote_type ty
    | TyErr_AssertStarNoGoal loc \<Rightarrow>
        loc_prefix loc @ quote ''assert *'' @ '' used with no enclosing proof goal''
    | TyErr_FixNoForallGoal loc \<Rightarrow>
        loc_prefix loc @ quote ''fix'' @ '' requires an enclosing ''
          @ quote ''forall'' @ '' proof goal''
    | TyErr_FixNotAtProofTopLevel loc \<Rightarrow>
        loc_prefix loc @ quote ''fix'' @ '' must appear at the top level of a proof''
    | TyErr_UseNoExistsGoal loc \<Rightarrow>
        loc_prefix loc @ quote ''use'' @ '' requires an enclosing ''
          @ quote ''exists'' @ '' proof goal''
    | TyErr_UseNotAtProofTopLevel loc \<Rightarrow>
        loc_prefix loc @ quote ''use'' @ '' must appear at the top level of a proof''
    | TyErr_DuplicateVarInPattern loc name \<Rightarrow>
        loc_prefix loc @ ''variable '' @ quote name @ '' is bound more than once in this pattern''
    | TyErr_RefPatternInTermContext loc name \<Rightarrow>
        loc_prefix loc @ quote ''ref'' @ '' pattern binding '' @ quote name
          @ '' is not allowed in an expression context''
    | TyErr_RefPatternNeedsLvalue loc name \<Rightarrow>
        loc_prefix loc @ quote ''ref'' @ '' pattern binding '' @ quote name
          @ '' requires the matched value to be an lvalue''
    | TyErr_EmptyMatch loc \<Rightarrow>
        loc_prefix loc @ ''match must have at least one arm''
    | TyErr_DuplicateName loc name \<Rightarrow>
        loc_prefix loc @ ''duplicate definition of '' @ quote name
    | TyErr_ConstDeclNeedsType loc name \<Rightarrow>
        loc_prefix loc @ ''constant '' @ quote name @ '' requires a type or a value''
    | TyErr_NotCompileTimeConstant loc \<Rightarrow>
        loc_prefix loc @ ''initializer is not a compile-time constant''
    | TyErr_ConstValueNotVisible loc name \<Rightarrow>
        loc_prefix loc @ ''the value of constant '' @ quote name @ '' is not visible here''
    | TyErr_ConstEvalError loc err2 \<Rightarrow>
        loc_prefix loc @ ''compile-time evaluation of constant failed: ''
          @ interp_error_to_string err2
    | TyErr_ConstAbstractType loc \<Rightarrow>
        loc_prefix loc
          @ ''constant initializer mentions an abstract type, so it cannot be evaluated at compile time''
    | TyErr_InvalidFunctionAttribute loc \<Rightarrow>
        loc_prefix loc @ ''invalid function attribute: only '' @ quote ''requires''
          @ '', '' @ quote ''ensures'' @ '' and '' @ quote ''decreases'' @ '' are allowed''
    | TyErr_FunctionSignatureMismatch loc name \<Rightarrow>
        loc_prefix loc @ ''definition of function '' @ quote name
          @ '' does not match its earlier declaration''
    | TyErr_ConstGhostnessMismatch loc name \<Rightarrow>
        loc_prefix loc @ ''definition of constant '' @ quote name
          @ '' does not match the ghostness of its earlier declaration''
    | TyErr_ExternFunctionWithBody loc name \<Rightarrow>
        loc_prefix loc @ ''extern function '' @ quote name @ '' cannot have a body''
    | TyErr_EmptyDatatype loc name \<Rightarrow>
        loc_prefix loc @ ''datatype '' @ quote name @ '' has no constructors''
    | TyErr_TypeArgsNotAllowed loc name \<Rightarrow>
        loc_prefix loc @ ''type arguments are not allowed on abstract type '' @ quote name
    | TyErr_CannotRealizeImportedType loc name \<Rightarrow>
        loc_prefix loc @ ''cannot realize abstract type '' @ quote name
          @ '' here: it is not declared by this module''
    | TyErr_GhostRealizationOfRuntimeType loc name \<Rightarrow>
        loc_prefix loc @ ''abstract type '' @ quote name
          @ '' is non-ghost, so it cannot be realized by a ghost-only type''
    | TyErr_SelfReferentialType loc name \<Rightarrow>
        loc_prefix loc @ ''type '' @ quote name @ '' refers to itself''
    | TyErr_TypeVarCapture loc name \<Rightarrow>
        loc_prefix loc @ ''type parameter '' @ quote name
          @ '' collides with a type of the same name''
    | TyErr_ExternTypeNotImplemented loc \<Rightarrow>
        loc_prefix loc @ quote ''extern type'' @ '' is not currently supported''
    | TyErr_DeclarationOnlyInImplementation loc name \<Rightarrow>
        loc_prefix loc @ quote name
          @ '' is declared without a definition; this is only allowed in an interface''
    | TyErr_DeclaredButNotDefined loc name \<Rightarrow>
        loc_prefix loc @ quote name @ '' is declared but never defined''
    | TyErr_AbstractTypeNotRealized loc name \<Rightarrow>
        loc_prefix loc @ ''abstract type '' @ quote name @ '' is never realized''
    | TyErr_RecursiveDeclarations loc names \<Rightarrow>
        loc_prefix loc @ ''recursive declarations: '' @ intercalate '', '' (map quote names)
    | TyErr_NameNotFound loc name \<Rightarrow>
        loc_prefix loc @ ''internal compiler error: name '' @ quote name @ '' not found''
    | TyErr_UnexpectedNameClash loc \<Rightarrow>
        loc_prefix loc @ ''internal compiler error: unexpected reserved name''
    | TyErr_DependencyAnalysisUnexpectedFailure loc \<Rightarrow>
        loc_prefix loc @ ''internal compiler error: dependency analysis failed''
    | TyErr_IllKindedProofGoal loc \<Rightarrow>
        loc_prefix loc @ ''internal compiler error: ill-kinded proof goal'')"


(*-----------------------------------------------------------------------------*)
(* Pipeline (whole-program elaboration) errors *)
(*-----------------------------------------------------------------------------*)

(* An ElabModuleError may contain several type errors, so this returns a list of
   strings (one per error). The module name is included in the link-error case,
   because link errors carry no location. *)
fun elab_module_error_to_strings :: "string \<Rightarrow> ElabModuleError \<Rightarrow> string list" where
  "elab_module_error_to_strings modName (EM_LinkError err) =
     [''module '' @ quote modName @ '': internal link error: '' @ link_error_to_string err]"
| "elab_module_error_to_strings modName (EM_TypeErrors errs) =
     map type_error_to_string errs"

fun pipeline_error_to_strings :: "PipelineError \<Rightarrow> string list" where
  "pipeline_error_to_strings (PE_DependencyError err) =
     [bab_dependency_error_to_string err]"
| "pipeline_error_to_strings (PE_MissingModule name) =
     [''internal compiler error: module '' @ quote name @ '' missing from pipeline'']"
| "pipeline_error_to_strings (PE_ElabError modName err) =
     elab_module_error_to_strings modName err"

end

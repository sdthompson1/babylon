theory CoreTyEnv
  imports CoreSyntax "HOL-Library.Finite_Map"
begin

record FunInfo =
  (* Type arguments: type variable names *)
  FI_TyArgs :: "string list"

  (* Term arguments: type, whether it is passed by value (Var) or reference (Ref), and
     whether it is a ghost argument (erased at runtime) *)
  FI_TmArgs :: "(CoreType \<times> VarOrRef \<times> GhostOrNot) list"

  (* Return type *)
  FI_ReturnType :: CoreType

  (* Ghost flag - Ghost functions can only be used in ghost contexts *)
  FI_Ghost :: GhostOrNot

  (* Impure flag - impure functions may modify the world state *)
  FI_Impure :: bool


record CoreTyEnv =
  (* Local variable bindings (mutable or const-local, e.g. let-bindings, function params).
     These correspond to IS_Locals and IS_Refs in the interpreter state. *)
  TE_LocalVars :: "(string, CoreType) fmap"

  (* Global variable bindings (always constant / read-only).
     These correspond to IS_Globals in the interpreter state.
     Globals are implicitly constant and do not appear in TE_ConstLocals. *)
  TE_GlobalVars :: "(string, CoreType) fmap"

  (* Ghost local variables - subset of TE_LocalVars keys *)
  TE_GhostLocals :: "string fset"

  (* Constant local names - subset of TE_LocalVars keys; these are not assignable.
     Globals are implicitly constant and do not need to appear here. *)
  TE_ConstLocals :: "string fset"

  (* In-scope type variables (for polymorphic functions) *)
  TE_TypeVars :: "string fset"

  (* Type variables that are known to be bound to runtime types - subset of TE_TypeVars *)
  TE_RuntimeTypeVars :: "string fset"

  (* Type variables representing abstract types ("type T;" in a module interface).
     - Always a subset of TE_TypeVars.
     - Variables in TE_AbstractTypes can be thought of as global type variables; other
       type variables are local to the current function.
     - In the interpreter, TE_AbstractTypes is always empty, since the interpreter only
       runs fully-linked programs. But in other contexts, where we are separately compiling
       individual modules, TE_AbstractTypes can be non-empty. *)
  TE_AbstractTypes :: "string fset"

  (* Expected return type of the enclosing function *)
  TE_ReturnType :: CoreType

  (* Ghost-ness of the enclosing function. *)
  TE_FunctionGhost :: GhostOrNot

  (* True if the enclosing function is impure (it may modify the world state). *)
  TE_FunctionImpure :: bool

  (* The remaining goal of the immediately-enclosing assert proof (if applicable).
     Note: Fix and Use strip quantifiers from the TE_ProofGoal, without renaming or
     substituting into the body correctly, so this might not be a well-typed term.
     This does not matter for typechecking, because the proof goal is only consumed
     structurally. *)
  TE_ProofGoal :: "CoreTerm option"

  (* True if we are at the *top level* (not inside a nested Match or While) in an
     assert proof. *)
  TE_ProofTopLevel :: bool

  (* Function signatures *)
  TE_Functions :: "(string, FunInfo) fmap"

  (* Datatypes: maps datatype name to number of type arguments *)
  TE_Datatypes :: "(string, nat) fmap"

  (* Data constructors: maps constructor name to (datatype name, type variables, payload type) *)
  (* The number of type variables should be consistent with TE_Datatypes *)
  TE_DataCtors :: "(string, string \<times> string list \<times> CoreType) fmap"

  (* Reverse mapping: datatype name to list of its constructor names *)
  (* Should be consistent with TE_DataCtors *)
  TE_DataCtorsByType :: "(string, string list) fmap"

  (* Ghost datatypes: datatypes whose constructors have non-runtime payload types.
     These cannot be represented in memory (e.g. as tagged unions) because the payload
     sizes are not known. A datatype is ghost if any of its constructor payloads
     contains MathInt, MathReal, or another ghost datatype. *)
  TE_GhostDatatypes :: "string fset"


(* This is true if a function has no ghost parameter. *)
definition no_ghost_params :: "FunInfo \<Rightarrow> bool" where
  "no_ghost_params info = list_all (\<lambda>(_, _, gh). gh = NotGhost) (FI_TmArgs info)"

(* The ghost flags of a function's parameters, in order. *)
definition param_ghost_flags :: "FunInfo \<Rightarrow> GhostOrNot list" where
  "param_ghost_flags info = map (\<lambda>(_, _, gh). gh) (FI_TmArgs info)"

(* The ghost flags of a function's Ref parameters, in order. *)
definition ref_param_ghost_flags :: "FunInfo \<Rightarrow> GhostOrNot list" where
  "ref_param_ghost_flags info =
    map (\<lambda>(_, _, gh). gh) (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs info))"

(* Keep the elements of a list whose flag is NotGhost. Ghost erasure uses this
   to remove the ghost arguments of a call, and the contract of an extern
   function says what the function does when called without them. *)
definition drop_ghost :: "GhostOrNot list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "drop_ghost flags xs = map snd (filter (\<lambda>(gh, _). gh = NotGhost) (zip flags xs))"

lemma drop_ghost_Nil [simp]:
  "drop_ghost [] xs = []"
  "drop_ghost flags [] = []"
  by (simp_all add: drop_ghost_def)

lemma drop_ghost_Cons [simp]:
  "drop_ghost (NotGhost # flags) (x # xs) = x # drop_ghost flags xs"
  "drop_ghost (Ghost # flags) (x # xs) = drop_ghost flags xs"
  by (simp_all add: drop_ghost_def)

lemma drop_ghost_map:
  "drop_ghost flags (map f xs) = map f (drop_ghost flags xs)"
proof (induction flags arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons gh flags)
  show ?case by (cases xs; cases gh) (simp_all add: Cons.IH)
qed

(* Dropping from two lists with the same flags, then pairing them up, is
   pairing them up and then dropping. *)
lemma zip_drop_ghost:
  "zip (drop_ghost flags xs) (drop_ghost flags ys) = drop_ghost flags (zip xs ys)"
proof (induction flags arbitrary: xs ys)
  case Nil
  show ?case by simp
next
  case (Cons gh flags)
  note IH = Cons.IH
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case xs_eq: (Cons x xs')
    show ?thesis
    proof (cases ys)
      case Nil
      then show ?thesis by (cases gh) (simp_all add: xs_eq)
    next
      case ys_eq: (Cons y ys')
      show ?thesis by (cases gh) (simp_all add: xs_eq ys_eq IH)
    qed
  qed
qed

lemma set_drop_ghost_subset:
  "set (drop_ghost flags xs) \<subseteq> set xs"
  unfolding drop_ghost_def by (auto dest: set_zip_rightD)

lemma distinct_drop_ghost:
  "distinct xs \<Longrightarrow> distinct (drop_ghost flags xs)"
proof (induction flags arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons gh flags)
  note IH = Cons.IH and dist = Cons.prems
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x xs')
    have d: "distinct xs'" and nin: "x \<notin> set xs'"
      using dist Cons by simp_all
    have tl: "distinct (drop_ghost flags xs')" by (rule IH[OF d])
    have "x \<notin> set (drop_ghost flags xs')"
      using nin set_drop_ghost_subset[of flags xs'] by blast
    with tl show ?thesis by (cases gh) (simp_all add: Cons)
  qed
qed

(* The number of elements kept is the number of NotGhost parameters. *)
lemma length_drop_ghost_params:
  assumes "length xs = length params"
  shows "length (drop_ghost (map (\<lambda>(_, _, gh). gh) params) xs)
           = length (filter (\<lambda>(_, _, gh). gh = NotGhost) params)"
  using assms
proof (induction xs params rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons x xs p params)
  obtain ty vor gh where p: "p = (ty, vor, gh)" by (cases p)
  show ?case using Cons.IH by (cases gh) (simp_all add: p)
qed

(* Dropping the ghost parameters from the parameter list itself is filtering
   it by the flag. *)
lemma drop_ghost_params:
  "drop_ghost (map (\<lambda>(_, _, gh). gh) params) params
     = filter (\<lambda>(_, _, gh). gh = NotGhost) params"
proof (induction params)
  case Nil
  show ?case by simp
next
  case (Cons p params)
  obtain ty vor gh where p: "p = (ty, vor, gh)" by (cases p)
  show ?case by (cases gh) (simp_all add: p Cons.IH)
qed

(* Is a variable ghost? For locals, check TE_GhostLocals; globals are never
   ghost (in Core).
   Note that locals shadow globals, so if a name is both local and global, the
   TE_GhostLocals status wins. *)
definition tyenv_var_ghost :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> bool" where
  "tyenv_var_ghost env name =
    (fmlookup (TE_LocalVars env) name \<noteq> None \<and> name |\<in>| TE_GhostLocals env)"

(* Look up a term variable: locals shadow globals *)
definition tyenv_lookup_var :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> CoreType option" where
  "tyenv_lookup_var env name =
    (case fmlookup (TE_LocalVars env) name of
      Some ty \<Rightarrow> Some ty
    | None \<Rightarrow> fmlookup (TE_GlobalVars env) name)"

(* A term variable is writable if it is a non-const local.
   Globals are implicitly constant and never writable. *)
definition tyenv_var_writable :: "CoreTyEnv \<Rightarrow> string \<Rightarrow> bool" where
  "tyenv_var_writable env name =
    (fmlookup (TE_LocalVars env) name \<noteq> None \<and> name |\<notin>| TE_ConstLocals env)"

(* tyenv_fixed_eq env1 env2: the "fixed" fields of env1 and env2 are identical.
   These are the fields that do not change during statement execution:
   globals, return type, function ghost-ness and impurity, functions, datatypes, etc.
   This is used in the Return case of sound_statement_result to transfer
   value_has_type and TE_ReturnType across environments. *)
definition tyenv_fixed_eq :: "CoreTyEnv \<Rightarrow> CoreTyEnv \<Rightarrow> bool" where
  "tyenv_fixed_eq env1 env2 \<equiv>
    TE_GlobalVars env1 = TE_GlobalVars env2 \<and>
    TE_ReturnType env1 = TE_ReturnType env2 \<and>
    TE_FunctionGhost env1 = TE_FunctionGhost env2 \<and>
    TE_FunctionImpure env1 = TE_FunctionImpure env2 \<and>
    TE_Functions env1 = TE_Functions env2 \<and>
    TE_Datatypes env1 = TE_Datatypes env2 \<and>
    TE_DataCtors env1 = TE_DataCtors env2 \<and>
    TE_DataCtorsByType env1 = TE_DataCtorsByType env2 \<and>
    TE_GhostDatatypes env1 = TE_GhostDatatypes env2 \<and>
    TE_TypeVars env1 = TE_TypeVars env2 \<and>
    TE_RuntimeTypeVars env1 = TE_RuntimeTypeVars env2"

lemma tyenv_fixed_eq_refl: "tyenv_fixed_eq env env"
  unfolding tyenv_fixed_eq_def by simp

lemma tyenv_fixed_eq_trans:
  assumes "tyenv_fixed_eq env1 env2" and "tyenv_fixed_eq env2 env3"
  shows "tyenv_fixed_eq env1 env3"
  using assms unfolding tyenv_fixed_eq_def by simp

lemma tyenv_fixed_eq_sym:
  assumes "tyenv_fixed_eq env1 env2"
  shows "tyenv_fixed_eq env2 env1"
  using assms unfolding tyenv_fixed_eq_def by simp

(* tyenv_fixed_eq does not constrain TE_ProofGoal (it is a mutable scoping
   field, deliberately omitted from the definition above). *)
lemma tyenv_fixed_eq_TE_ProofGoal_left [simp]:
  "tyenv_fixed_eq (env1 \<lparr> TE_ProofGoal := g \<rparr>) env2 = tyenv_fixed_eq env1 env2"
  unfolding tyenv_fixed_eq_def by simp

lemma tyenv_fixed_eq_TE_ProofGoal_right [simp]:
  "tyenv_fixed_eq env1 (env2 \<lparr> TE_ProofGoal := g \<rparr>) = tyenv_fixed_eq env1 env2"
  unfolding tyenv_fixed_eq_def by simp

lemma tyenv_fixed_eq_TE_ProofTopLevel_left [simp]:
  "tyenv_fixed_eq (env1 \<lparr> TE_ProofTopLevel := g \<rparr>) env2 = tyenv_fixed_eq env1 env2"
  unfolding tyenv_fixed_eq_def by simp

lemma tyenv_fixed_eq_TE_ProofTopLevel_right [simp]:
  "tyenv_fixed_eq env1 (env2 \<lparr> TE_ProofTopLevel := g \<rparr>) = tyenv_fixed_eq env1 env2"
  unfolding tyenv_fixed_eq_def by simp

lemma tyenv_lookup_var_local [simp]:
  "fmlookup (TE_LocalVars env) name = Some ty \<Longrightarrow> tyenv_lookup_var env name = Some ty"
  unfolding tyenv_lookup_var_def by simp

lemma tyenv_lookup_var_global:
  "fmlookup (TE_LocalVars env) name = None \<Longrightarrow>
   tyenv_lookup_var env name = fmlookup (TE_GlobalVars env) name"
  unfolding tyenv_lookup_var_def by simp

lemma tyenv_lookup_var_TE_ConstLocals_irrelevant [simp]:
  "tyenv_lookup_var (env \<lparr> TE_ConstLocals := c \<rparr>) name = tyenv_lookup_var env name"
  unfolding tyenv_lookup_var_def by (simp split: option.splits)

lemma tyenv_var_ghost_TE_ConstLocals_irrelevant [simp]:
  "tyenv_var_ghost (env \<lparr> TE_ConstLocals := c \<rparr>) name = tyenv_var_ghost env name"
  unfolding tyenv_var_ghost_def by (simp split: option.splits)

end

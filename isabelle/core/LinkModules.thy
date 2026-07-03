theory LinkModules
  imports CoreModule MergeAllSubsts
begin

(* The **link_modules** function merges a list of CoreModules into a single
   CoreModule. This is the linking step of separate compilation: each module
   carries its own declarations (CM_TyEnv), definitions (CM_GlobalVars,
   CM_Functions) and abstract-type resolutions (CM_TypeSubst), and linking
   combines them all, in one pass over the whole list.

   The semantics is "multiple definition is an error": it is a LinkConflict
   for the same name to be declared/defined by two of the input modules. This
   is decided on map domains alone (no entry comparison) - the renamer
   guarantees globally-unique top-level names, so a shared key signals a
   genuine upstream problem. Concretely:

   - CM_TypeSubst: the inputs' substitutions are combined by merge_all_substs
     (MergeAllSubsts.thy), which fails with LinkConflict if an abstract type
     is defined by two inputs, or LinkCycle if the combined definitions are
     cyclic; on success it returns the idempotent closure of their union.

   - The seven finite-map declaration/definition families (TE_GlobalVars,
     TE_Functions, TE_Datatypes, TE_DataCtors, TE_DataCtorsByType on the
     type environment; CM_GlobalVars, CM_Functions on the module) are each
     combined by disjoint union across the inputs (fmdisjoint_list /
     fmlist_union, util/FmapDisjointUnion.thy), failing with LinkConflict on
     a shared key.

   - The ghost fsets (TE_GhostGlobals, TE_GhostDatatypes) are combined by
     plain union: each is a subset of its parent map's keys (TE_GlobalVars /
     TE_Datatypes) in a well-formed env, so their disjointness is implied by
     the parent check.

   - The type-variable fields (TE_TypeVars, TE_RuntimeTypeVars,
     TE_AbstractTypes) are combined by union, minus the domain of the merged
     substitution: an abstract type that has been given a definition is
     recorded in the substitution and removed from the in-scope type
     variables. (Linking performs NO substitution into types or terms; that
     is normalize_module's job, applied to the linked result later.)

   - The "current scope" fields of the result's type environment are inert,
     holding the module-level conventional values (no locals, no proof goal,
     return type CoreTy_Record [], non-ghost). Well-typed modules carry
     exactly these values, so nothing is lost on such inputs.

   Additionally, linking checks capture-avoidance (LinkCapture on failure):
   no name TOUCHED by any input's CM_TypeSubst - a domain entry, or a type
   variable occurring in a resolution (subst_names, TypeSubst.thy) - may
   coincide with a bound type parameter (an FI_TyArgs entry or a data
   constructor's type-variable list) of any input.

   Linking also checks the runtime-resolution condition (LinkGhostResolution on
   failure): once the merged substitution \<sigma> is known, every resolved name that
   some input declared as a runtime abstract type (n |\<in>| TE_RuntimeTypeVars)
   must be resolved to a runtime type.

   link_modules is **executable**. Its behaviour on success is specified by:

     link_modules_Inr_iff:
       link_modules ms = Inr m \<longleftrightarrow>
         link_fields_disjoint ms
         \<and> link_capture_ok ms
         \<and> (\<exists>\<sigma>. merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>
               \<and> link_runtime_ok ms \<sigma>
               \<and> m = link_result ms \<sigma>)

   (and link_modules_Inr_iff_closure, the same statement with merge_all_substs
   replaced by its own declarative characterization). We also prove:

    - link_modules_idempotent_subst, link_modules_capture_avoiding: a successful
      link's result satisfies the CoreModule invariants: idempotent CM_TypeSubst
      and capture_avoiding).

    - link_modules_perm: the result is insensitive to the order of the input list
      (both orderings succeed with the same module, or both fail) - permutation-
      invariance, NOT de-duplication: link_modules [m, m] is a multiple-definition
      error for any non-empty m.

    - link_modules_singleton: link_modules [m] = Inr m, under the standard module 
      invariants.

   Note the raw result of link_modules is generally NOT independently
   well-kinded - its types may still mention abstract names that linking has
   removed from TE_TypeVars. Only normalize_module of the result is. *)


(* ========================================================================== *)
(* The union of a list of finite sets                                         *)
(* ========================================================================== *)

(* Unlike the finite-map case (fmlist_union) there is no disjointness
   requirement here: fset union is unconditionally order-independent. *)
definition funion_list :: "'a fset list \<Rightarrow> 'a fset" where
  "funion_list xs = foldr (|\<union>|) xs {||}"

lemma funion_list_Nil [simp]:
  "funion_list [] = {||}"
  unfolding funion_list_def by simp

lemma funion_list_Cons [simp]:
  "funion_list (x # xs) = x |\<union>| funion_list xs"
  unfolding funion_list_def by simp

(* Membership in the union is membership in some element - a property of the
   set of elements, with no reference to their order. *)
lemma funion_list_member:
  "x |\<in>| funion_list xs \<longleftrightarrow> (\<exists>s \<in> set xs. x |\<in>| s)"
  by (induction xs) auto

lemma funion_list_singleton [simp]:
  "funion_list [x] = x"
proof (rule fset_eqI)
  fix a
  show "a |\<in>| funion_list [x] \<longleftrightarrow> a |\<in>| x"
    by (simp add: funion_list_member)
qed

(* Hence the union depends only on the set of inputs. *)
lemma funion_list_set_cong:
  assumes "set xs = set ys"
  shows "funion_list xs = funion_list ys"
proof (rule fset_eqI)
  fix x
  show "x |\<in>| funion_list xs \<longleftrightarrow> x |\<in>| funion_list ys"
    using funion_list_member assms by metis
qed


(* ========================================================================== *)
(* Multiset/set congruences for mapped lists                                  *)
(*                                                                            *)
(* link_modules operates on per-field projections (map f ms) of the input     *)
(* module list. These lemmas transport a permutation (multiset equality) of   *)
(* the module list to each projection, feeding the mset_cong lemmas of        *)
(* util/FmapDisjointUnion.thy and merge_all_substs_perm.                      *)
(* ========================================================================== *)

lemma mset_map_perm_cong:
  assumes "mset xs = mset ys"
  shows "mset (map f xs) = mset (map f ys)"
  using assms by (metis mset_map)

lemma set_map_perm_cong:
  assumes "mset xs = mset ys"
  shows "set (map f xs) = set (map f ys)"
  using mset_map_perm_cong[OF assms] by (rule mset_eq_setD)

(* Under a permutation, the disjoint union of a projected family is unchanged
   (given disjointness, which makes the union order-immaterial)... *)
lemma fmlist_union_map_cong:
  assumes "mset ms = mset ms'"
      and "fmdisjoint_list (map f ms)"
  shows "fmlist_union (map f ms) = fmlist_union (map f ms')"
  using fmlist_union_mset_cong[OF mset_map_perm_cong[OF assms(1)] assms(2)] .

(* ...and so is the plain fset union of a projected family (unconditionally). *)
lemma funion_list_map_cong:
  assumes "mset ms = mset ms'"
  shows "funion_list (map f ms) = funion_list (map f ms')"
  using funion_list_set_cong[OF set_map_perm_cong[OF assms]] .


(* ========================================================================== *)
(* Disjointness of the declaration/definition families                       *)
(* ========================================================================== *)

(* The seven finite-map families that linking unions across the input modules:
   five declaration maps of the type environment, and the two definition maps
   of the module itself. A name in two inputs' domains is a multiple-definition
   error, decided on names alone.

   (The ghost fsets TE_GhostGlobals / TE_GhostDatatypes are not checked: each
   is a subset of the keys of its parent map in a well-formed env, so their
   disjointness is implied by the parent's.) *)
definition link_fields_disjoint :: "CoreModule list \<Rightarrow> bool" where
  "link_fields_disjoint ms \<equiv>
       fmdisjoint_list (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) ms)
     \<and> fmdisjoint_list (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)
     \<and> fmdisjoint_list (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)
     \<and> fmdisjoint_list (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)
     \<and> fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)
     \<and> fmdisjoint_list (map CM_GlobalVars ms)
     \<and> fmdisjoint_list (map CM_Functions ms)"

(* Disjointness of every family depends only on the multiset of inputs. *)
lemma link_fields_disjoint_mset_cong:
  assumes m: "mset ms = mset ms'"
  shows "link_fields_disjoint ms = link_fields_disjoint ms'"
  unfolding link_fields_disjoint_def
  by (simp add: fmdisjoint_list_mset_cong[OF mset_map_perm_cong[OF m]])

(* The multiply-defined names, for the LinkConflict payload: the duplicate keys
   of each family, concatenated. Purely diagnostic (no theorem depends on its
   value). remdups because the same name can conflict in more than one family
   (e.g. a global constant defined by two modules conflicts in both
   TE_GlobalVars and CM_GlobalVars). *)
definition link_conflict_names :: "CoreModule list \<Rightarrow> string list" where
  "link_conflict_names ms =
     remdups
       (fmdup_keys (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) ms)
      @ fmdup_keys (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)
      @ fmdup_keys (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)
      @ fmdup_keys (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)
      @ fmdup_keys (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)
      @ fmdup_keys (map CM_GlobalVars ms)
      @ fmdup_keys (map CM_Functions ms))"


(* ========================================================================== *)
(* The capture-avoidance check                                                *)
(* ========================================================================== *)

(* The union's domain is the union of the domains (no disjointness needed). *)
lemma fmdom_fmlist_union:
  "fmdom (fmlist_union ss) = funion_list (map fmdom ss)"
  by (induction ss) (simp_all add: fmlist_union_Cons)

(* The bound type-parameter names of a module: the FI_TyArgs of every declared
   function and the type-variable list of every data constructor. These names
   are binders - they appear in no linked map's domain, so the
   multiple-definition check never sees them. *)
definition module_bound_tyvars :: "CoreModule \<Rightarrow> string fset" where
  "module_bound_tyvars x =
     ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info)) |`| fmran (TE_Functions (CM_TyEnv x)))
     |\<union>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars) |`| fmran (TE_DataCtors (CM_TyEnv x)))"

lemma module_bound_tyvars_fun:
  assumes lk: "fmlookup (TE_Functions (CM_TyEnv x)) name = Some info"
      and n_in: "n \<in> set (FI_TyArgs info)"
  shows "n |\<in>| module_bound_tyvars x"
proof -
  have "info |\<in>| fmran (TE_Functions (CM_TyEnv x))"
    using lk by (rule fmranI)
  then have "fset_of_list (FI_TyArgs info)
               |\<in>| (\<lambda>info. fset_of_list (FI_TyArgs info)) |`| fmran (TE_Functions (CM_TyEnv x))"
    by (rule fimageI)
  moreover have "n |\<in>| fset_of_list (FI_TyArgs info)"
    using n_in by (simp add: fset_of_list_elem)
  ultimately show ?thesis
    unfolding module_bound_tyvars_def
    using fmember_ffUnion_iff by force
qed

lemma module_bound_tyvars_ctor:
  assumes lk: "fmlookup (TE_DataCtors (CM_TyEnv x)) ctorName = Some (dtName, tyVars, payload)"
      and n_in: "n \<in> set tyVars"
  shows "n |\<in>| module_bound_tyvars x"
proof -
  have "(dtName, tyVars, payload) |\<in>| fmran (TE_DataCtors (CM_TyEnv x))"
    using lk by (rule fmranI)
  then have "fset_of_list tyVars
               |\<in>| (\<lambda>(_, tyVars, _). fset_of_list tyVars) |`| fmran (TE_DataCtors (CM_TyEnv x))"
    using fimageI[of "(dtName, tyVars, payload)" _ "\<lambda>(_, tyVars, _). fset_of_list tyVars"]
    by simp
  moreover have "n |\<in>| fset_of_list tyVars"
    using n_in by (simp add: fset_of_list_elem)
  ultimately show ?thesis
    unfolding module_bound_tyvars_def
    using fmember_ffUnion_iff by force
qed

(* Elimination form: a bound tyvar comes from some function's FI_TyArgs or
   some constructor's type-variable list. *)
lemma module_bound_tyvars_E:
  assumes "n |\<in>| module_bound_tyvars x"
  shows "(\<exists>name info. fmlookup (TE_Functions (CM_TyEnv x)) name = Some info
                      \<and> n \<in> set (FI_TyArgs info))
       \<or> (\<exists>ctorName dtName tyVars payload.
            fmlookup (TE_DataCtors (CM_TyEnv x)) ctorName = Some (dtName, tyVars, payload)
            \<and> n \<in> set tyVars)"
proof -
  from assms consider
      (fn) "n |\<in>| ffUnion ((\<lambda>info. fset_of_list (FI_TyArgs info))
                            |`| fmran (TE_Functions (CM_TyEnv x)))"
    | (ct) "n |\<in>| ffUnion ((\<lambda>(_, tyVars, _). fset_of_list tyVars)
                            |`| fmran (TE_DataCtors (CM_TyEnv x)))"
    unfolding module_bound_tyvars_def by auto
  then show ?thesis
  proof cases
    case fn
    then obtain X where
      X_in: "X |\<in>| (\<lambda>info. fset_of_list (FI_TyArgs info)) |`| fmran (TE_Functions (CM_TyEnv x))" and
      n_X: "n |\<in>| X"
      using fmember_ffUnion_iff by (metis (no_types, lifting))
    from X_in obtain info where
      info_ran: "info |\<in>| fmran (TE_Functions (CM_TyEnv x))" and
      X_eq: "X = fset_of_list (FI_TyArgs info)"
      by auto
    from info_ran obtain name where
      "fmlookup (TE_Functions (CM_TyEnv x)) name = Some info"
      by (metis fmranE)
    moreover have "n \<in> set (FI_TyArgs info)"
      using n_X X_eq by (simp add: fset_of_list_elem)
    ultimately show ?thesis by blast
  next
    case ct
    then obtain X where
      X_in: "X |\<in>| (\<lambda>(_, tyVars, _). fset_of_list tyVars) |`| fmran (TE_DataCtors (CM_TyEnv x))" and
      n_X: "n |\<in>| X"
      using fmember_ffUnion_iff by (metis (no_types, lifting))
    from X_in obtain entry where
      entry_ran: "entry |\<in>| fmran (TE_DataCtors (CM_TyEnv x))" and
      X_eq: "X = (case entry of (_, tyVars, _) \<Rightarrow> fset_of_list tyVars)"
      by auto
    obtain dtName tyVars payload where entry_eq: "entry = (dtName, tyVars, payload)"
      by (cases entry) auto
    from entry_ran obtain ctorName where
      "fmlookup (TE_DataCtors (CM_TyEnv x)) ctorName = Some (dtName, tyVars, payload)"
      using entry_eq by (metis fmranE)
    moreover have "n \<in> set tyVars"
      using n_X X_eq entry_eq by (simp add: fset_of_list_elem)
    ultimately show ?thesis by blast
  qed
qed

(* The check: no name TOUCHED by any input's substitution (resolved by it, or
   occurring in one of its resolutions - subst_names, TypeSubst.thy) is a
   bound type parameter of any input. Phrased over the unions, so it depends
   only on the set of inputs. *)
definition link_capture_ok :: "CoreModule list \<Rightarrow> bool" where
  "link_capture_ok ms =
     (funion_list (map (\<lambda>x. subst_names (CM_TypeSubst x)) ms)
      |\<inter>| funion_list (map module_bound_tyvars ms) = {||})"

(* The colliding names, for the LinkCapture payload. Purely diagnostic. *)
definition link_capture_names :: "CoreModule list \<Rightarrow> string list" where
  "link_capture_names ms =
     sorted_list_of_fset
       (funion_list (map (\<lambda>x. subst_names (CM_TypeSubst x)) ms)
        |\<inter>| funion_list (map module_bound_tyvars ms))"

(* The check depends only on the multiset of inputs. *)
lemma link_capture_ok_mset_cong:
  assumes m: "mset ms = mset ms'"
  shows "link_capture_ok ms = link_capture_ok ms'"
  unfolding link_capture_ok_def
  by (simp add: funion_list_map_cong[OF m])


(* ========================================================================== *)
(* The linked module                                                          *)
(* ========================================================================== *)

(* The linked module, given the input list ms and the merged type substitution
   \<sigma> (the result of merge_all_substs on the inputs' CM_TypeSubsts):

   - every declaration/definition map is the (disjoint) union across the
     inputs, and the ghost fsets are plain unions;
   - the three type-variable fields lose the abstract types the merged
     substitution resolves (fmdom \<sigma> is the union of the inputs' CM_TypeSubst
     domains, by is_subst_closure);
   - the "current scope" fields are inert, holding the module-level
     conventional values;
   - CM_TypeSubst is \<sigma> itself; no substitution is applied to any type or term
     (normalize_module does that later).

   TE_AbstractTypes gets the same union-minus-resolved treatment as
   TE_TypeVars: this preserves TE_AbstractTypes |\<subseteq>| TE_TypeVars, and on
   module-level inputs (where TE_AbstractTypes = TE_TypeVars, every in-scope
   type variable being a module-level abstract type) it keeps that equation
   for the result. *)
definition link_result :: "CoreModule list \<Rightarrow> TypeSubst \<Rightarrow> CoreModule" where
  "link_result ms \<sigma> =
     \<lparr> CM_TyEnv =
         \<lparr> TE_LocalVars = fmempty,
           TE_GlobalVars = fmlist_union (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) ms),
           TE_GhostLocals = {||},
           TE_GhostGlobals = funion_list (map (\<lambda>x. TE_GhostGlobals (CM_TyEnv x)) ms),
           TE_ConstLocals = {||},
           TE_TypeVars =
             funion_list (map (\<lambda>x. TE_TypeVars (CM_TyEnv x)) ms) |-| fmdom \<sigma>,
           TE_RuntimeTypeVars =
             funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms) |-| fmdom \<sigma>,
           TE_AbstractTypes =
             funion_list (map (\<lambda>x. TE_AbstractTypes (CM_TyEnv x)) ms) |-| fmdom \<sigma>,
           TE_ReturnType = CoreTy_Record [],
           TE_FunctionGhost = NotGhost,
           TE_ProofGoal = None,
           TE_ProofTopLevel = False,
           TE_Functions = fmlist_union (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms),
           TE_Datatypes = fmlist_union (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms),
           TE_DataCtors = fmlist_union (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms),
           TE_DataCtorsByType = fmlist_union (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms),
           TE_GhostDatatypes = funion_list (map (\<lambda>x. TE_GhostDatatypes (CM_TyEnv x)) ms) \<rparr>,
       CM_TypeSubst = \<sigma>,
       CM_GlobalVars = fmlist_union (map CM_GlobalVars ms),
       CM_Functions = fmlist_union (map CM_Functions ms) \<rparr>"

(* On a permutation of the inputs, the linked module is unchanged (given
   disjointness of the map families, which makes their unions
   order-immaterial; the fset unions are unconditionally so). *)
lemma link_result_mset_cong:
  assumes m: "mset ms = mset ms'"
      and disj: "link_fields_disjoint ms"
  shows "link_result ms \<sigma> = link_result ms' \<sigma>"
proof -
  have d1: "fmdisjoint_list (map (\<lambda>x. TE_GlobalVars (CM_TyEnv x)) ms)"
   and d2: "fmdisjoint_list (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)"
   and d3: "fmdisjoint_list (map (\<lambda>x. TE_Datatypes (CM_TyEnv x)) ms)"
   and d4: "fmdisjoint_list (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)"
   and d5: "fmdisjoint_list (map (\<lambda>x. TE_DataCtorsByType (CM_TyEnv x)) ms)"
   and d6: "fmdisjoint_list (map CM_GlobalVars ms)"
   and d7: "fmdisjoint_list (map CM_Functions ms)"
    using disj by (auto simp: link_fields_disjoint_def)
  show ?thesis
    unfolding link_result_def
    by (simp add: funion_list_map_cong[OF m]
                  fmlist_union_map_cong[OF m d1] fmlist_union_map_cong[OF m d2]
                  fmlist_union_map_cong[OF m d3] fmlist_union_map_cong[OF m d4]
                  fmlist_union_map_cong[OF m d5] fmlist_union_map_cong[OF m d6]
                  fmlist_union_map_cong[OF m d7])
qed


(* ========================================================================== *)
(* The runtime-resolution check                                               *)
(* ========================================================================== *)

(* After merge_all_substs succeeds with \<sigma>, every resolved name that SOME input
   lists in its TE_RuntimeTypeVars (i.e. declared as a runtime abstract type)
   must be resolved to an is_runtime_type in the linked result's env. A runtime
   abstract type resolved by a ghost type falsifies the whole-program linking
   (Target) theorem, and the mismatch is invisible to any per-module predicate:
   the declarer records the runtime-ness, the resolver has forgotten the name;
   they first meet at link time. Resolving a ghost abstract type by a ghost
   type remains legal (the check is keyed on the declarer's TE_RuntimeTypeVars).
   Depends on both ms and \<sigma>, so it is gated inside the Inr \<sigma> branch of
   link_modules (unlike link_capture_ok, which depends on ms alone). *)
definition link_runtime_ok :: "CoreModule list \<Rightarrow> TypeSubst \<Rightarrow> bool" where
  "link_runtime_ok ms \<sigma> =
     (\<forall>n. n |\<in>| fmdom \<sigma>
             |\<inter>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms)
          \<longrightarrow> is_runtime_type (CM_TyEnv (link_result ms \<sigma>)) (the (fmlookup \<sigma> n)))"

(* The offending names, for the LinkGhostResolution payload. Purely
   diagnostic. *)
definition link_ghost_resolution_names :: "CoreModule list \<Rightarrow> TypeSubst \<Rightarrow> string list" where
  "link_ghost_resolution_names ms \<sigma> =
     sorted_list_of_fset
       (ffilter (\<lambda>n. \<not> is_runtime_type (CM_TyEnv (link_result ms \<sigma>)) (the (fmlookup \<sigma> n)))
          (fmdom \<sigma>
           |\<inter>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) ms)))"

(* The check depends only on the multiset of inputs (with a fixed \<sigma>): the
   TE_RuntimeTypeVars union and the linked env are both permutation-invariant
   (link_result_mset_cong needs the field-disjointness that a successful link
   supplies). *)
lemma link_runtime_ok_mset_cong:
  assumes m: "mset ms = mset ms'"
      and disj: "link_fields_disjoint ms"
  shows "link_runtime_ok ms \<sigma> = link_runtime_ok ms' \<sigma>"
  unfolding link_runtime_ok_def
  by (simp add: funion_list_map_cong[OF m] link_result_mset_cong[OF m disj])


(* ========================================================================== *)
(* Definition of link_modules                                                 *)
(* ========================================================================== *)

(* Executable link_modules function.

   First check that no name is declared/defined by two of the inputs
   (LinkConflict otherwise, with the offending names as payload); then check
   capture-avoidance (LinkCapture otherwise); then merge the abstract-type
   substitutions (a LinkConflict or LinkCycle from merge_all_substs propagates);
   then, with the merged \<sigma> in hand, check that no runtime (non-ghost) abstract
   type resolves to a ghost type (LinkGhostResolution otherwise); on success,
   assemble the field-wise union. *)
definition link_modules :: "CoreModule list \<Rightarrow> (LinkError, CoreModule) sum" where
  "link_modules ms =
     (if \<not> link_fields_disjoint ms
      then Inl (LinkConflict (link_conflict_names ms))
      else if \<not> link_capture_ok ms
      then Inl (LinkCapture (link_capture_names ms))
      else case merge_all_substs (map CM_TypeSubst ms) of
             Inl e \<Rightarrow> Inl e
           | Inr \<sigma> \<Rightarrow>
               if link_runtime_ok ms \<sigma>
               then Inr (link_result ms \<sigma>)
               else Inl (LinkGhostResolution (link_ghost_resolution_names ms \<sigma>)))"


(* ========================================================================== *)
(* The success characterization                                               *)
(* ========================================================================== *)

(* link_modules succeeds with result m exactly when the declaration/definition
   families are pairwise domain-disjoint, the capture check passes, the
   substitution merge succeeds (with some \<sigma>), and m is the field-wise union
   with that \<sigma> and the type-variable subtraction. *)
theorem link_modules_Inr_iff:
  "link_modules ms = Inr m \<longleftrightarrow>
     link_fields_disjoint ms
     \<and> link_capture_ok ms
     \<and> (\<exists>\<sigma>. merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>
           \<and> link_runtime_ok ms \<sigma>
           \<and> m = link_result ms \<sigma>)"
proof (cases "link_fields_disjoint ms")
  case False
  then have "link_modules ms = Inl (LinkConflict (link_conflict_names ms))"
    unfolding link_modules_def by simp
  then show ?thesis using False by simp
next
  case disj: True
  show ?thesis
  proof (cases "link_capture_ok ms")
    case False
    then have "link_modules ms = Inl (LinkCapture (link_capture_names ms))"
      unfolding link_modules_def using disj by simp
    then show ?thesis using False by simp
  next
    case cap: True
    show ?thesis
    proof (cases "merge_all_substs (map CM_TypeSubst ms)")
      case (Inl e)
      then have "link_modules ms = Inl e"
        unfolding link_modules_def using disj cap by simp
      then show ?thesis using Inl by auto
    next
      case (Inr \<sigma>)
      show ?thesis
      proof (cases "link_runtime_ok ms \<sigma>")
        case rok: True
        then have lhs: "link_modules ms = Inr (link_result ms \<sigma>)"
          unfolding link_modules_def using disj cap Inr by simp
        show ?thesis
        proof
          assume "link_modules ms = Inr m"
          then have "m = link_result ms \<sigma>" using lhs by simp
          then show "link_fields_disjoint ms
                     \<and> link_capture_ok ms
                     \<and> (\<exists>\<sigma>'. merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>'
                            \<and> link_runtime_ok ms \<sigma>'
                            \<and> m = link_result ms \<sigma>')"
            using disj cap Inr rok by blast
        next
          assume "link_fields_disjoint ms
                  \<and> link_capture_ok ms
                  \<and> (\<exists>\<sigma>'. merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>'
                         \<and> link_runtime_ok ms \<sigma>'
                         \<and> m = link_result ms \<sigma>')"
          then obtain \<sigma>' where "merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>'"
                           and "m = link_result ms \<sigma>'" by blast
          then have "m = link_result ms \<sigma>" using Inr by simp
          then show "link_modules ms = Inr m" using lhs by simp
        qed
      next
        case rok: False
        then have lhs: "link_modules ms = Inl (LinkGhostResolution (link_ghost_resolution_names ms \<sigma>))"
          unfolding link_modules_def using disj cap Inr by simp
        show ?thesis
        proof
          assume "link_modules ms = Inr m"
          then show "link_fields_disjoint ms
                     \<and> link_capture_ok ms
                     \<and> (\<exists>\<sigma>'. merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>'
                            \<and> link_runtime_ok ms \<sigma>'
                            \<and> m = link_result ms \<sigma>')"
            using lhs by simp
        next
          assume "link_fields_disjoint ms
                  \<and> link_capture_ok ms
                  \<and> (\<exists>\<sigma>'. merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>'
                         \<and> link_runtime_ok ms \<sigma>'
                         \<and> m = link_result ms \<sigma>')"
          then obtain \<sigma>' where "merge_all_substs (map CM_TypeSubst ms) = Inr \<sigma>'"
                           and "link_runtime_ok ms \<sigma>'" by blast
          then have "link_runtime_ok ms \<sigma>" using Inr by simp
          with rok show "link_modules ms = Inr m" by simp
        qed
      qed
    qed
  qed
qed

(* The same, with merge_all_substs replaced by its own declarative
   characterization: the substitution part succeeds exactly when the inputs'
   substitutions are pairwise disjoint and the union's dependency relation is
   acyclic, and \<sigma> is the idempotent closure of that union. Every conjunct
   depends only on the (multi)set of inputs. *)
corollary link_modules_Inr_iff_closure:
  "link_modules ms = Inr m \<longleftrightarrow>
     link_fields_disjoint ms
     \<and> link_capture_ok ms
     \<and> fmdisjoint_list (map CM_TypeSubst ms)
     \<and> acyclic_subst_deps (fmlist_union (map CM_TypeSubst ms))
     \<and> (\<exists>\<sigma>. is_subst_closure (fmlist_union (map CM_TypeSubst ms)) \<sigma>
           \<and> link_runtime_ok ms \<sigma>
           \<and> m = link_result ms \<sigma>)"
  unfolding link_modules_Inr_iff merge_all_substs_Inr_iff by blast

(* The merged substitution of a successful link is idempotent: linking
   preserves the CoreModule invariant on CM_TypeSubst. (Immediate from the
   characterization - the result's substitution is the idempotent closure of
   the union of the inputs' substitutions.) *)
lemma link_modules_idempotent_subst:
  assumes "link_modules ms = Inr m"
  shows "idempotent_subst (CM_TypeSubst m)"
proof -
  obtain \<sigma> where clos: "is_subst_closure (fmlist_union (map CM_TypeSubst ms)) \<sigma>"
             and meq: "m = link_result ms \<sigma>"
    using assms link_modules_Inr_iff_closure by blast
  have "idempotent_subst \<sigma>"
    using clos unfolding is_subst_closure_def by blast
  moreover have "CM_TypeSubst m = \<sigma>"
    using meq by (simp add: link_result_def)
  ultimately show ?thesis by simp
qed


(* ========================================================================== *)
(* Permutation-invariance                                                     *)
(* ========================================================================== *)

(* link_modules is invariant under permuting its input list, directly off the
   success characterization - every conjunct of link_modules_Inr_iff depends
   only on the multiset of inputs. Both orderings succeed with the same linked
   module, or both fail. (Stated over Inr: we do NOT claim the same LinkError
   on failure - a different ordering may surface a different error first.)

   This is a sanity check on the definition, not machinery anything downstream
   consumes. Note it is invariance under REORDERING, not de-duplication:
   link_modules [m, m] is a LinkConflict for any non-empty m. *)
theorem link_modules_perm:
  assumes perm: "mset ms = mset ms'"
  shows "link_modules ms = Inr m \<longleftrightarrow> link_modules ms' = Inr m"
proof -
  have one: "link_modules ys = Inr m"
    if ok: "link_modules xs = Inr m" and eq: "mset xs = mset ys" for xs ys
  proof -
    obtain \<sigma> where disj: "link_fields_disjoint xs"
        and cap: "link_capture_ok xs"
        and mer: "merge_all_substs (map CM_TypeSubst xs) = Inr \<sigma>"
        and rok: "link_runtime_ok xs \<sigma>"
        and meq: "m = link_result xs \<sigma>"
      using ok link_modules_Inr_iff[of xs m] by blast
    have disj': "link_fields_disjoint ys"
      using link_fields_disjoint_mset_cong[OF eq] disj by simp
    have cap': "link_capture_ok ys"
      using link_capture_ok_mset_cong[OF eq] cap by simp
    have mer': "merge_all_substs (map CM_TypeSubst ys) = Inr \<sigma>"
      using merge_all_substs_perm[OF mset_map_perm_cong[OF eq]] mer by blast
    have rok': "link_runtime_ok ys \<sigma>"
      using link_runtime_ok_mset_cong[OF eq disj] rok by simp
    have meq': "m = link_result ys \<sigma>"
      using meq link_result_mset_cong[OF eq disj] by simp
    show ?thesis
      using disj' cap' mer' rok' meq' link_modules_Inr_iff[of ys m] by blast
  qed
  show ?thesis using one[OF _ perm] one[OF _ perm[symmetric]] by blast
qed

(* Failure-agreement form: two orderings of the same inputs either both
   succeed (necessarily with the same result, by link_modules_perm) or both
   fail. *)
corollary link_modules_perm_fails:
  assumes "mset ms = mset ms'"
  shows "(\<exists>m. link_modules ms = Inr m) \<longleftrightarrow> (\<exists>m. link_modules ms' = Inr m)"
  using link_modules_perm[OF assms] by blast


(* ========================================================================== *)
(* Singleton input                                                            *)
(* ========================================================================== *)

(* Linking a single module returns it unchanged, under the standard module
   invariants:
   - CM_TypeSubst is idempotent (a CoreModule requirement), so merging the
     one-element substitution list returns it as-is;
   - the module is capture-avoiding (a CoreModule requirement), so the
     capture check passes;
   - the substitution's domain avoids the module's own type variables (a
     resolved abstract type is recorded in the substitution and removed from
     TE_TypeVars), so the type-variable subtraction is the identity;
   - the "current scope" fields hold their inert module-level values. *)
lemma link_modules_singleton:
  assumes idem: "idempotent_subst (CM_TypeSubst m)"
      and cap:  "capture_avoiding m"
      and tv:   "fmdom (CM_TypeSubst m) |\<inter>| TE_TypeVars (CM_TyEnv m) = {||}"
      and rtv:  "TE_RuntimeTypeVars (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
      and abst: "TE_AbstractTypes (CM_TyEnv m) |\<subseteq>| TE_TypeVars (CM_TyEnv m)"
      and inert:
        "TE_LocalVars (CM_TyEnv m) = fmempty"
        "TE_GhostLocals (CM_TyEnv m) = {||}"
        "TE_ConstLocals (CM_TyEnv m) = {||}"
        "TE_ReturnType (CM_TyEnv m) = CoreTy_Record []"
        "TE_FunctionGhost (CM_TyEnv m) = NotGhost"
        "TE_ProofGoal (CM_TyEnv m) = None"
        "TE_ProofTopLevel (CM_TyEnv m) = False"
  shows "link_modules [m] = Inr m"
proof -
  \<comment> \<open>Any fset of in-scope type variables is untouched by the subtraction of
     the substitution's domain.\<close>
  have notin: "x |\<notin>| fmdom (CM_TypeSubst m)" if "x |\<in>| TE_TypeVars (CM_TyEnv m)" for x
    using tv that by auto
  have sub_id: "A |-| fmdom (CM_TypeSubst m) = A"
    if sub: "A |\<subseteq>| TE_TypeVars (CM_TyEnv m)" for A
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| A |-| fmdom (CM_TypeSubst m) \<longleftrightarrow> x |\<in>| A"
      using notin sub by (auto dest: fsubsetD)
  qed
  have tv_sub: "TE_TypeVars (CM_TyEnv m) |-| fmdom (CM_TypeSubst m)
                  = TE_TypeVars (CM_TyEnv m)"
    by (rule sub_id) simp
  have rtv_sub: "TE_RuntimeTypeVars (CM_TyEnv m) |-| fmdom (CM_TypeSubst m)
                   = TE_RuntimeTypeVars (CM_TyEnv m)"
    using sub_id[OF rtv] .
  have abs_sub: "TE_AbstractTypes (CM_TyEnv m) |-| fmdom (CM_TypeSubst m)
                   = TE_AbstractTypes (CM_TyEnv m)"
    using sub_id[OF abst] .

  \<comment> \<open>The one-element substitution merge returns the substitution itself.\<close>
  have merge: "merge_all_substs (map CM_TypeSubst [m]) = Inr (CM_TypeSubst m)"
    using merge_all_substs_singleton[OF idem] by simp

  \<comment> \<open>The assembled module is m itself, field by field.\<close>
  have env_eq: "CM_TyEnv (link_result [m] (CM_TypeSubst m)) = CM_TyEnv m"
    by (rule CoreTyEnv.equality)
       (simp_all add: link_result_def inert tv_sub rtv_sub abs_sub)
  have mod_eq: "link_result [m] (CM_TypeSubst m) = m"
  proof (rule CoreModule.equality)
    show "CM_TyEnv (link_result [m] (CM_TypeSubst m)) = CM_TyEnv m"
      using env_eq .
    show "CM_TypeSubst (link_result [m] (CM_TypeSubst m)) = CM_TypeSubst m"
      by (simp add: link_result_def)
    show "CM_GlobalVars (link_result [m] (CM_TypeSubst m)) = CM_GlobalVars m"
      by (simp add: link_result_def)
    show "CM_Functions (link_result [m] (CM_TypeSubst m)) = CM_Functions m"
      by (simp add: link_result_def)
    show "CoreModule.more (link_result [m] (CM_TypeSubst m)) = CoreModule.more m"
      by (simp add: link_result_def)
  qed

  have disj: "link_fields_disjoint [m]"
    unfolding link_fields_disjoint_def by simp

  \<comment> \<open>The capture check on a single module is exactly its own capture-avoidance.\<close>
  have cap_ok: "link_capture_ok [m]"
  proof -
    have "subst_names (CM_TypeSubst m) |\<inter>| module_bound_tyvars m = {||}"
    proof (rule fset_eqI)
      fix n
      show "n |\<in>| subst_names (CM_TypeSubst m) |\<inter>| module_bound_tyvars m \<longleftrightarrow> n |\<in>| {||}"
      proof
        assume "n |\<in>| subst_names (CM_TypeSubst m) |\<inter>| module_bound_tyvars m"
        then have nd: "n |\<in>| subst_names (CM_TypeSubst m)"
              and nb: "n |\<in>| module_bound_tyvars m" by auto
        from module_bound_tyvars_E[OF nb] show "n |\<in>| {||}"
        proof
          assume "\<exists>name info. fmlookup (TE_Functions (CM_TyEnv m)) name = Some info
                              \<and> n \<in> set (FI_TyArgs info)"
          then obtain name info where
            lk: "fmlookup (TE_Functions (CM_TyEnv m)) name = Some info" and
            n_in: "n \<in> set (FI_TyArgs info)" by blast
          have "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
            using cap lk unfolding capture_avoiding_def by blast
          then show "n |\<in>| {||}"
            using nd n_in by (auto simp: fset_of_list_elem)
        next
          assume "\<exists>ctorName dtName tyVars payload.
                    fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName
                      = Some (dtName, tyVars, payload) \<and> n \<in> set tyVars"
          then obtain ctorName dtName tyVars payload where
            lk: "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName = Some (dtName, tyVars, payload)" and
            n_in: "n \<in> set tyVars" by blast
          have "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
            using cap lk unfolding capture_avoiding_def by blast
          then show "n |\<in>| {||}"
            using nd n_in by (auto simp: fset_of_list_elem)
        qed
      qed simp
    qed
    then show ?thesis unfolding link_capture_ok_def by simp
  qed

  \<comment> \<open>The runtime-resolution check is vacuous on a single module: the
     substitution's domain avoids TE_TypeVars (hypothesis tv), and
     TE_RuntimeTypeVars is contained in TE_TypeVars (hypothesis rtv), so no
     resolved name is a runtime type variable to begin with.\<close>
  have runtime_ok: "link_runtime_ok [m] (CM_TypeSubst m)"
    unfolding link_runtime_ok_def
  proof (intro allI impI)
    fix n
    assume "n |\<in>| fmdom (CM_TypeSubst m)
              |\<inter>| funion_list (map (\<lambda>x. TE_RuntimeTypeVars (CM_TyEnv x)) [m])"
    then have nd: "n |\<in>| fmdom (CM_TypeSubst m)"
          and nr: "n |\<in>| TE_RuntimeTypeVars (CM_TyEnv m)" by auto
    from nr rtv have "n |\<in>| TE_TypeVars (CM_TyEnv m)" by (auto dest: fsubsetD)
    with nd have "n |\<in>| fmdom (CM_TypeSubst m) |\<inter>| TE_TypeVars (CM_TyEnv m)" by simp
    with tv have False by simp
    then show
      "is_runtime_type (CM_TyEnv (link_result [m] (CM_TypeSubst m))) (the (fmlookup (CM_TypeSubst m) n))"
      by simp
  qed

  show ?thesis
    using disj cap_ok merge runtime_ok mod_eq link_modules_Inr_iff by simp
qed


(* ========================================================================== *)
(* A successful link is capture-avoiding                                      *)
(* ========================================================================== *)

(* The point of the capture check: a successful link's result satisfies
   capture_avoiding - against the MERGED substitution's whole name set
   (subst_names): its domain is the union of the inputs' domains, and its
   range's type variables are leftover names of the raw union
   (is_subst_closure_range_tyvars, MergeSubstsPrelims.thy), so both sides are
   covered by the input-side check. Downstream (the whole-program
   well-typedness theorem) this discharges normalize_module's
   capture-avoidance precondition from link success alone. *)
theorem link_modules_capture_avoiding:
  assumes ok: "link_modules ms = Inr m"
  shows "capture_avoiding m"
proof -
  obtain \<sigma> where
    disj: "link_fields_disjoint ms" and
    cap: "link_capture_ok ms" and
    sdisj: "fmdisjoint_list (map CM_TypeSubst ms)" and
    acyc: "acyclic_subst_deps (fmlist_union (map CM_TypeSubst ms))" and
    clos: "is_subst_closure (fmlist_union (map CM_TypeSubst ms)) \<sigma>" and
    meq: "m = link_result ms \<sigma>"
    using ok link_modules_Inr_iff_closure by blast
  have subst_eq: "CM_TypeSubst m = \<sigma>"
    using meq by (simp add: link_result_def)
  let ?u = "fmlist_union (map CM_TypeSubst ms)"
  \<comment> \<open>Every name the merged substitution touches is touched by some input's
      substitution: the closure's domain IS the union of the inputs' domains,
      and the closure's range tyvars are leftover names of the raw union.\<close>
  have names_sub: "\<exists>x \<in> set ms. n |\<in>| subst_names (CM_TypeSubst x)"
    if n_in: "n |\<in>| subst_names \<sigma>" for n
  proof -
    from n_in consider (dom) "n |\<in>| fmdom \<sigma>" | (rng) "n \<in> subst_range_tyvars \<sigma>"
      using subst_names_member by auto
    then show ?thesis
    proof cases
      case dom
      then have "n |\<in>| fmdom ?u"
        using clos unfolding is_subst_closure_def by simp
      then obtain ty where "fmlookup ?u n = Some ty"
        by (auto simp: fmlookup_dom_iff)
      then obtain s where s_in: "s \<in> set (map CM_TypeSubst ms)"
                      and s_lk: "fmlookup s n = Some ty"
        using fmlist_union_lookup[OF sdisj] by blast
      have "n |\<in>| fmdom s" using s_lk by (rule fmdomI)
      then show ?thesis
        using s_in by (auto simp: subst_names_member)
    next
      case rng
      then have "n \<in> subst_range_tyvars ?u"
        using is_subst_closure_range_tyvars[OF acyc clos] by auto
      then obtain ty where "ty \<in> fmran' ?u" and n_ty: "n \<in> type_tyvars ty"
        unfolding subst_range_tyvars_def by auto
      then obtain k where "fmlookup ?u k = Some ty"
        by (auto simp: fmlookup_ran'_iff)
      then obtain s where s_in: "s \<in> set (map CM_TypeSubst ms)"
                      and s_lk: "fmlookup s k = Some ty"
        using fmlist_union_lookup[OF sdisj] by blast
      have "ty \<in> fmran' s" using s_lk by (rule fmran'I)
      then have "n \<in> subst_range_tyvars s"
        using n_ty unfolding subst_range_tyvars_def by auto
      then show ?thesis
        using s_in by (auto simp: subst_names_member)
    qed
  qed
  \<comment> \<open>From the check: no bound tyvar of any input is touched by the merged
      substitution.\<close>
  have nocap: "\<And>n x. x \<in> set ms \<Longrightarrow> n |\<in>| module_bound_tyvars x
                 \<Longrightarrow> n |\<in>| subst_names \<sigma> \<Longrightarrow> False"
  proof -
    fix n x assume x_in: "x \<in> set ms" and nb: "n |\<in>| module_bound_tyvars x"
      and nd: "n |\<in>| subst_names \<sigma>"
    obtain y where y_in: "y \<in> set ms" and ny: "n |\<in>| subst_names (CM_TypeSubst y)"
      using names_sub[OF nd] by blast
    have "n |\<in>| funion_list (map module_bound_tyvars ms)"
      using x_in nb funion_list_member by fastforce
    moreover have "n |\<in>| funion_list (map (\<lambda>x. subst_names (CM_TypeSubst x)) ms)"
      using y_in ny funion_list_member by fastforce
    ultimately have "n |\<in>| funion_list (map (\<lambda>x. subst_names (CM_TypeSubst x)) ms)
                          |\<inter>| funion_list (map module_bound_tyvars ms)"
      by simp
    then show False using cap unfolding link_capture_ok_def by auto
  qed
  have djF: "fmdisjoint_list (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)"
    and djC: "fmdisjoint_list (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)"
    using disj unfolding link_fields_disjoint_def by blast+
  show ?thesis
    unfolding capture_avoiding_def
  proof (rule conjI)
    show "\<forall>funName info.
            fmlookup (TE_Functions (CM_TyEnv m)) funName = Some info \<longrightarrow>
            subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
    proof (intro allI impI)
      fix funName info
      assume lk: "fmlookup (TE_Functions (CM_TyEnv m)) funName = Some info"
      have "TE_Functions (CM_TyEnv m)
              = fmlist_union (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms)"
        using meq by (simp add: link_result_def)
      with lk have "\<exists>f \<in> set (map (\<lambda>x. TE_Functions (CM_TyEnv x)) ms).
                      fmlookup f funName = Some info"
        using fmlist_union_lookup[OF djF] by simp
      then obtain x where x_in: "x \<in> set ms"
          and x_lk: "fmlookup (TE_Functions (CM_TyEnv x)) funName = Some info"
        by auto
      show "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info) = {||}"
      proof (rule fset_eqI)
        fix n
        show "n |\<in>| subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info)
                \<longleftrightarrow> n |\<in>| {||}"
        proof
          assume "n |\<in>| subst_names (CM_TypeSubst m) |\<inter>| fset_of_list (FI_TyArgs info)"
          then have nd: "n |\<in>| subst_names \<sigma>" and n_in: "n \<in> set (FI_TyArgs info)"
            using subst_eq by (auto simp: fset_of_list_elem)
          have "n |\<in>| module_bound_tyvars x"
            using module_bound_tyvars_fun[OF x_lk n_in] .
          then show "n |\<in>| {||}"
            using nocap[OF x_in _ nd] by blast
        qed simp
      qed
    qed
  next
    show "\<forall>ctorName dtName tyVars payload.
            fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName = Some (dtName, tyVars, payload)
            \<longrightarrow> subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
    proof (intro allI impI)
      fix ctorName dtName tyVars payload
      assume lk: "fmlookup (TE_DataCtors (CM_TyEnv m)) ctorName
                    = Some (dtName, tyVars, payload)"
      have "TE_DataCtors (CM_TyEnv m)
              = fmlist_union (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms)"
        using meq by (simp add: link_result_def)
      with lk have "\<exists>f \<in> set (map (\<lambda>x. TE_DataCtors (CM_TyEnv x)) ms).
                      fmlookup f ctorName = Some (dtName, tyVars, payload)"
        using fmlist_union_lookup[OF djC] by simp
      then obtain x where x_in: "x \<in> set ms"
          and x_lk: "fmlookup (TE_DataCtors (CM_TyEnv x)) ctorName
                       = Some (dtName, tyVars, payload)"
        by auto
      show "subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars = {||}"
      proof (rule fset_eqI)
        fix n
        show "n |\<in>| subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars \<longleftrightarrow> n |\<in>| {||}"
        proof
          assume "n |\<in>| subst_names (CM_TypeSubst m) |\<inter>| fset_of_list tyVars"
          then have nd: "n |\<in>| subst_names \<sigma>" and n_in: "n \<in> set tyVars"
            using subst_eq by (auto simp: fset_of_list_elem)
          have "n |\<in>| module_bound_tyvars x"
            using module_bound_tyvars_ctor[OF x_lk n_in] .
          then show "n |\<in>| {||}"
            using nocap[OF x_in _ nd] by blast
        qed simp
      qed
    qed
  qed
qed

end

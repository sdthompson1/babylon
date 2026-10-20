theory ExternContract
  imports InterpState
begin

(* This file defines the obligations that all extern functions are expected to satisfy.
   Discharging these is the responsibility of whoever provides the extern functions. *)

(* Typing: for every valid input (type args, term args, world), the extern
   function returns a valid return value of the (substituted) return type, together
   with a valid list of ref updates (one per Ref parameter) at the (substituted)
   Ref-parameter types.
   "Valid input" means that the type args are ground, well-kinded types (but not
   necessarily runtime types; extern functions can be called from ghost code), and
   that the term args (values) have the substituted parameter types. *)
definition extern_fun_well_typed :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> 'w ExternFunc \<Rightarrow> bool" where
  "extern_fun_well_typed env funInfo externFun =
   (\<forall>tySubst world vals.
       \<comment> \<open>tySubst maps exactly the callee's type arguments to ground,
           well-kinded types in the caller's env.\<close>
       fmdom tySubst = fset_of_list (FI_TyArgs funInfo) \<and>
       (\<forall>ty' \<in> fmran' tySubst. type_tyvars ty' = {}
                              \<and> is_well_kinded env ty') \<and>
       \<comment> \<open>Term arguments (vals) have the substituted parameter types.\<close>
       list_all2 (value_has_type env)
                 vals
                 (map (\<lambda>(ty, _). apply_subst tySubst ty) (FI_TmArgs funInfo))
       \<longrightarrow>
       (case externFun world vals of (newWorld, refUpdates, retVal) \<Rightarrow>
          \<comment> \<open>Return value has the substituted return type.\<close>
          value_has_type env retVal (apply_subst tySubst (FI_ReturnType funInfo)) \<and>
          \<comment> \<open>One ref update per Ref parameter, in IF_Args order, at the substituted type.\<close>
          list_all2 (value_has_type env)
                    refUpdates
                    (map (\<lambda>(ty, _). apply_subst tySubst ty)
                         (filter (\<lambda>(_, vor, _). vor = Ref) (FI_TmArgs funInfo)))))"

(* An extern function marked "pure" always returns the same world that was
   passed into it. (This holds for all inputs, not just well-typed ones.) *)
definition extern_fun_respects_purity :: "FunInfo \<Rightarrow> 'w ExternFunc \<Rightarrow> bool" where
  "extern_fun_respects_purity funInfo externFun =
   (\<not> FI_Impure funInfo \<longrightarrow> (\<forall>world vals. fst (externFun world vals) = world))"

(* Ghost independence: this says that the result of an extern function is unchanged
   by ghost erasure. Specifically, if an extern function is called with all its
   "ghost" arguments omitted, then it returns the same results, except that the
   ghost ref-updates are omitted. (This holds for all inputs of the correct length,
   not just well-typed ones.) *)
definition extern_fun_ghost_independent :: "FunInfo \<Rightarrow> 'w ExternFunc \<Rightarrow> bool" where
  "extern_fun_ghost_independent funInfo externFun =
   (\<forall>world vals. length vals = length (FI_TmArgs funInfo) \<longrightarrow>
      (case externFun world vals of (newWorld, refUpdates, retVal) \<Rightarrow>
         externFun world (drop_ghost (param_ghost_flags funInfo) vals)
           = (newWorld, drop_ghost (ref_param_ghost_flags funInfo) refUpdates, retVal)))"

(* The extern fun contract itself is the conjunction of the above clauses. *)
definition extern_fun_contract :: "CoreTyEnv \<Rightarrow> FunInfo \<Rightarrow> 'w ExternFunc \<Rightarrow> bool" where
  "extern_fun_contract env funInfo externFun =
   (extern_fun_well_typed env funInfo externFun \<and>
    extern_fun_respects_purity funInfo externFun \<and>
    extern_fun_ghost_independent funInfo externFun)"

(* A pure extern function returns the world it was given. *)
lemma extern_fun_contract_pure_world:
  assumes "extern_fun_contract env funInfo externFun" and "\<not> FI_Impure funInfo"
  shows "fst (externFun world vals) = world"
  using assms unfolding extern_fun_contract_def extern_fun_respects_purity_def by simp

(* An extern function called without its ghost arguments returns the same
   world and value, and the ref updates of the parameters that are not
   ghost. *)
lemma extern_fun_ghost_independentD:
  assumes "extern_fun_ghost_independent funInfo externFun"
    and "length vals = length (FI_TmArgs funInfo)"
    and "externFun world vals = (newWorld, refUpdates, retVal)"
  shows "externFun world (drop_ghost (param_ghost_flags funInfo) vals)
           = (newWorld, drop_ghost (ref_param_ghost_flags funInfo) refUpdates, retVal)"
proof -
  note inst = assms(1)[unfolded extern_fun_ghost_independent_def,
                       THEN spec[where x = world], THEN spec[where x = vals]]
  from inst assms(2) show ?thesis by (simp add: assms(3))
qed

end

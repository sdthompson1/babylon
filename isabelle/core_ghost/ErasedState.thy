theory ErasedState
  imports EraseGhost "../interpreter/CoreInterp" "../interpreter/StateMatchesEnv"
begin

(* This file defines the relation between two interpreter states:

    - `full`, a state of the run of a program with its ghost code; and
    - `erased`, the corresponding state of the run of the erased program.

   The erased state is the full state restricted to what is not ghost. The
   relation is taken with respect to the type environment `env` of the current
   program point (of the full program), which says which locals are ghost
   (tyenv_var_ghost).

   The two runs do not use the same addresses, because the full run also
   allocates store cells for ghost variables. The relation therefore takes an
   embedding `emb` of erased addresses into full addresses: the erased address
   i corresponds to the full address (emb ! i). The full addresses outside the
   range of emb are the ghost cells.

   Values contain no addresses, so corresponding cells hold equal values. *)


(* ========================================================================== *)
(* Function tables *)
(* ========================================================================== *)

(* Erase a function: drop its ghost parameters, and erase the ghost code from
   its body. The function signatures funInfos say which arguments of the calls
   in the body are ghost. *)
definition erase_ghost_interp_fun ::
    "(string, FunInfo) fmap \<Rightarrow> 'w InterpFun \<Rightarrow> 'w InterpFun" where
  "erase_ghost_interp_fun funInfos f =
    f \<lparr> IF_Args := filter (\<lambda>(_, _, gh). gh = NotGhost) (IF_Args f),
        IF_Body := map_sum (erase_ghost_statement_list funInfos) id (IF_Body f) \<rparr>"

(* Each non-ghost function is, in the erased state, the erased function. (Ghost
   functions are never called by the erased program, so nothing is said about
   them.) *)
definition funs_erased :: "CoreTyEnv \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "funs_erased env full erased \<equiv>
    \<forall>name info. fmlookup (TE_Functions env) name = Some info \<and> FI_Ghost info = NotGhost \<longrightarrow>
      fmlookup (IS_Functions erased) name
        = map_option (erase_ghost_interp_fun (TE_Functions env))
                     (fmlookup (IS_Functions full) name)"


(* ========================================================================== *)
(* Store *)
(* ========================================================================== *)

(* emb maps the addresses of the erased store, one-to-one, to addresses of the
   full store that hold the same values. *)
definition store_erased :: "nat list \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "store_erased emb full erased \<equiv>
    length emb = length (IS_Store erased) \<and>
    distinct emb \<and>
    (\<forall>i < length emb. emb ! i < length (IS_Store full)
                      \<and> IS_Store erased ! i = IS_Store full ! (emb ! i))"


(* ========================================================================== *)
(* Local variables *)
(* ========================================================================== *)

(* A name that is not a ghost local has corresponding bindings in the two
   states: the same kind of binding (local, ref or neither), at corresponding
   addresses, with the same path and the same const-ness. *)
definition locals_erased ::
    "CoreTyEnv \<Rightarrow> nat list \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "locals_erased env emb full erased \<equiv>
    \<forall>name. \<not> tyenv_var_ghost env name \<longrightarrow>
      rel_option (\<lambda>i addr. i < length emb \<and> addr = emb ! i)
                 (fmlookup (IS_Locals erased) name) (fmlookup (IS_Locals full) name) \<and>
      rel_option (\<lambda>(i, path) (addr, path'). i < length emb \<and> addr = emb ! i \<and> path = path')
                 (fmlookup (IS_Refs erased) name) (fmlookup (IS_Refs full) name) \<and>
      (name |\<in>| IS_ConstLocals erased \<longleftrightarrow> name |\<in>| IS_ConstLocals full)"

(* A ghost local of the full state lives in a ghost cell: a valid address that
   does not correspond to any erased address. (Nothing is said about what the
   same name is bound to in the erased state. It may still have the binding
   that the ghost declaration shadowed, which executable code cannot refer
   to.) *)
definition ghost_locals_separate ::
    "CoreTyEnv \<Rightarrow> nat list \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "ghost_locals_separate env emb full \<equiv>
    \<forall>name. tyenv_var_ghost env name \<longrightarrow>
      (\<forall>addr. fmlookup (IS_Locals full) name = Some addr \<longrightarrow>
         addr < length (IS_Store full) \<and> addr \<notin> set emb) \<and>
      (\<forall>addr path. fmlookup (IS_Refs full) name = Some (addr, path) \<longrightarrow>
         addr < length (IS_Store full) \<and> addr \<notin> set emb)"


(* ========================================================================== *)
(* The state relation *)
(* ========================================================================== *)

(* The part of the relation that does not involve the current function's
   frame: globals, world, function tables and store. This is what relates the
   two states after a Return, when the frame is about to be discarded. *)
definition heap_erased ::
    "CoreTyEnv \<Rightarrow> nat list \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "heap_erased env emb full erased \<equiv>
    IS_Globals erased = IS_Globals full \<and>
    IS_DefaultCtors erased = IS_DefaultCtors full \<and>
    IS_World erased = IS_World full \<and>
    funs_erased env full erased \<and>
    store_erased emb full erased"

(* The whole relation. *)
definition state_erased ::
    "CoreTyEnv \<Rightarrow> nat list \<Rightarrow> 'w InterpState \<Rightarrow> 'w InterpState \<Rightarrow> bool" where
  "state_erased env emb full erased \<equiv>
    heap_erased env emb full erased \<and>
    IS_TyArgs erased = IS_TyArgs full \<and>
    locals_erased env emb full erased \<and>
    ghost_locals_separate env emb full"

(* The relation between the results of running a statement list and its
   erasure, starting from states related by emb. The two results are of the
   same kind, a Return carries the same value, and the final states are related
   by an embedding that extends emb (running the statements may have allocated
   new cells in both stores). The environment is that of the program point
   after the statement list. *)
fun result_erased ::
    "CoreTyEnv \<Rightarrow> nat list \<Rightarrow> 'w ExecResult \<Rightarrow> 'w ExecResult \<Rightarrow> bool" where
  "result_erased env emb (Continue full) (Continue erased) =
    (\<exists>extra. state_erased env (emb @ extra) full erased)"
| "result_erased env emb (Return full fullVal) (Return erased erasedVal) =
    (erasedVal = fullVal \<and> (\<exists>extra. heap_erased env (emb @ extra) full erased))"
| "result_erased _ _ _ _ = False"


(* The simulation theorem, which says that running a statement list and running
   its erasure from related states gives related results, is
   erase_ghost_simulation in EraseGhostSimulation.thy. *)

end

theory StateRep
  imports RepValPath "../interpreter/ExternContract" "../minic/MiniCExample"
begin

(* ========================================================================== *)
(* The store-level representation relation, ownership, and extern_rep         *)
(* (minic/DESIGN.md, sections 4 and 6.2)                                      *)
(* ========================================================================== *)

(* This theory defines the part of the state relation of section 4 that does
   not involve the generator's environment: a region per cell of IS_Store
   whose bytes represent the cell's value, the globals in their blocks, the
   ownership condition with its sharing exception, and equal worlds. The
   per-frame part (IS_Locals, IS_Refs, IS_TyArgs to MiniC variables and lazy
   terms) is stage 6's; it takes the facts defined here as parameters.
   extern_rep is the hypothesis on the models of extern functions (section
   6.2); print_i32's model is shown to satisfy it. *)


section \<open>Regions and cells\<close>

(* A region: a block and an offset in it. *)
type_synonym Region = "nat \<times> nat"

definition region_ptr :: "Region \<Rightarrow> MPtr" where
  "region_ptr r = MP_Addr (fst r) (snd r)"

(* Two byte ranges (region, length) that do not overlap. *)
definition regions_disjoint :: "Region \<Rightarrow> nat \<Rightarrow> Region \<Rightarrow> nat \<Rightarrow> bool" where
  "regions_disjoint r1 n1 r2 n2 =
    (fst r1 \<noteq> fst r2 \<or> snd r1 + n1 \<le> snd r2 \<or> snd r2 + n2 \<le> snd r1)"

(* The bytes of a region of the size of a type. *)
definition region_bytes :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> Region \<Rightarrow> MByte list option" where
  "region_bytes env enc mem ty r = mem_read mem (region_ptr r) (gsz env enc ty)"

(* A cell: the value v of type ty is represented by the bytes of region r. *)
definition cell_rep :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (nat \<Rightarrow> MPtr) \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> CoreValue \<Rightarrow> Region \<Rightarrow> bool" where
  "cell_rep env enc hmap mem ty v r =
    (\<exists>bs. region_bytes env enc mem ty r = Some bs \<and> rep_val env enc hmap mem ty v bs)"

(* The heap blocks reachable from a cell. *)
definition cell_reach :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> CoreValue \<Rightarrow> Region \<Rightarrow> nat set" where
  "cell_reach env enc mem ty v r =
    (case region_bytes env enc mem ty r of
       Some bs \<Rightarrow> reach_blocks env enc mem ty v bs
     | None \<Rightarrow> {})"

(* A cell whose blocks form a tree (section 4). *)
definition cell_owned :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> CoreValue \<Rightarrow> Region \<Rightarrow> bool" where
  "cell_owned env enc mem ty v r =
    (case region_bytes env enc mem ty r of
       Some bs \<Rightarrow> val_owned env enc mem ty v bs \<and> fst r \<notin> reach_blocks env enc mem ty v bs
     | None \<Rightarrow> False)"

lemma cell_rep_bytes:
  assumes "cell_rep env enc hmap mem ty v r"
  obtains bs where "mem_read mem (region_ptr r) (gsz env enc ty) = Some bs" and "rep_val env enc hmap mem ty v bs"
  using assms unfolding cell_rep_def region_bytes_def by blast


section \<open>The store and the globals\<close>

(* Every cell of the store (IS_Store, typed by storeTyping as in
   state_matches_env) has a region whose bytes represent it. *)
definition store_rep :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (nat \<Rightarrow> MPtr) \<Rightarrow> MMem
                         \<Rightarrow> CoreValue list \<Rightarrow> CoreType list \<Rightarrow> Region list \<Rightarrow> bool" where
  "store_rep env enc hmap mem store storeTyping regions =
    (length regions = length store \<and> length storeTyping = length store
     \<and> (\<forall>i < length store. cell_rep env enc hmap mem (storeTyping ! i) (store ! i) (regions ! i)))"

(* Every global is represented in its region (the generator gives each
   global its own block, section 3.7). *)
definition globals_rep :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (nat \<Rightarrow> MPtr) \<Rightarrow> MMem
                           \<Rightarrow> (string, CoreValue) fmap \<Rightarrow> (string \<Rightarrow> Region) \<Rightarrow> bool" where
  "globals_rep env enc hmap mem globals gregion =
    (\<forall>g v. fmlookup globals g = Some v \<longrightarrow>
       (\<exists>ty. fmlookup (TE_GlobalVars env) g = Some ty \<and> cell_rep env enc hmap mem ty v (gregion g)))"


section \<open>Ownership and sharing\<close>

(* Sharing (section 4): a cell created by bind_const_local (a by-value
   parameter, a Let variable, a ref to a read-only base) may share its
   region and heap blocks with the cell it was copied from. The origin map
   gives every cell its root: the cell it is (transitively) a copy of, or
   itself. Cells with different roots are disjoint; cells with the same root
   may share. *)
definition store_owned :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem
                           \<Rightarrow> CoreValue list \<Rightarrow> CoreType list \<Rightarrow> Region list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "store_owned env enc mem store storeTyping regions root =
    ((\<forall>i < length store. cell_owned env enc mem (storeTyping ! i) (store ! i) (regions ! i))
     \<and> (\<forall>i j. i < length store \<longrightarrow> j < length store \<longrightarrow> i \<noteq> j \<longrightarrow> root i \<noteq> root j \<longrightarrow>
          regions_disjoint (regions ! i) (gsz env enc (storeTyping ! i)) (regions ! j) (gsz env enc (storeTyping ! j))
          \<and> cell_reach env enc mem (storeTyping ! i) (store ! i) (regions ! i)
            \<inter> cell_reach env enc mem (storeTyping ! j) (store ! j) (regions ! j) = {}))"

(* The globals have their own blocks, distinct from each other and from
   every cell's region and heap blocks. *)
definition globals_owned :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> MMem \<Rightarrow> (string, CoreValue) fmap \<Rightarrow> (string \<Rightarrow> Region)
                             \<Rightarrow> CoreValue list \<Rightarrow> CoreType list \<Rightarrow> Region list \<Rightarrow> bool" where
  "globals_owned env enc mem globals gregion store storeTyping regions =
    ((\<forall>g v. fmlookup globals g = Some v \<longrightarrow> snd (gregion g) = 0
        \<and> (\<forall>g' v'. fmlookup globals g' = Some v' \<longrightarrow> g' \<noteq> g \<longrightarrow> fst (gregion g') \<noteq> fst (gregion g))
        \<and> (\<forall>i < length store. fst (regions ! i) \<noteq> fst (gregion g)
             \<and> fst (gregion g) \<notin> cell_reach env enc mem (storeTyping ! i) (store ! i) (regions ! i)))
     \<and> (\<forall>g v ty. fmlookup globals g = Some v \<longrightarrow> fmlookup (TE_GlobalVars env) g = Some ty \<longrightarrow>
          cell_owned env enc mem ty v (gregion g)))"

(* The invariant the simulation maintains (section 4): every location
   writable from the current frame (the set W of writable cells: its mutable
   cells and its ref targets) is referenced by no other live cell. Nothing
   is proved about it in this stage. *)
definition writable_unshared :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> bool" where
  "writable_unshared root W n = (\<forall>i \<in> W. root i = i \<and> (\<forall>j < n. j \<noteq> i \<longrightarrow> root j \<noteq> i))"

(* The store-level relation: equal worlds, the store and the globals
   represented, ownership. The per-frame facts (how IS_Locals, IS_Refs and
   IS_TyArgs map to MiniC variables, and which cells are writable) are
   stage 6's parameters. *)
definition state_rep_store :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (nat \<Rightarrow> MPtr) \<Rightarrow> 'w InterpState \<Rightarrow> CoreType list
                               \<Rightarrow> 'w MState \<Rightarrow> Region list \<Rightarrow> (string \<Rightarrow> Region) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "state_rep_store env enc hmap st storeTyping ms regions gregion root =
    (IS_World st = MS_World ms
     \<and> store_rep env enc hmap (MS_Mem ms) (IS_Store st) storeTyping regions
     \<and> globals_rep env enc hmap (MS_Mem ms) (IS_Globals st) gregion
     \<and> store_owned env enc (MS_Mem ms) (IS_Store st) storeTyping regions root
     \<and> globals_owned env enc (MS_Mem ms) (IS_Globals st) gregion (IS_Store st) storeTyping regions)"


section \<open>The extern hypothesis\<close>

(* The argument correspondence of section 6.2. A parameter (ty, vor) of the
   instantiated type ty is passed: by value, as its MiniC scalar value if ty
   is scalar, else as a pointer to a region holding its bytes; by ref, as a
   pointer to a region holding its bytes (which the extern may write). *)
definition arg_rep :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (nat \<Rightarrow> MPtr) \<Rightarrow> MMem \<Rightarrow> CoreType \<Rightarrow> VarOrRef \<Rightarrow> CoreValue \<Rightarrow> MVal \<Rightarrow> bool" where
  "arg_rep env enc hmap mem ty vor v a =
    (if vor = Var \<and> scalar_ty ty \<noteq> None then scalar_val hmap v = Some a
     else (\<exists>p bs. a = MV_Ptr p \<and> mem_read mem p (gsz env enc ty) = Some bs \<and> rep_val env enc hmap mem ty v bs))"

(* The region (pointer and size) of a pointer argument, if any. *)
definition arg_region :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> CoreType \<Rightarrow> VarOrRef \<Rightarrow> MVal \<Rightarrow> (MPtr \<times> nat) option" where
  "arg_region env enc ty vor a =
    (if vor = Var \<and> scalar_ty ty \<noteq> None then None
     else (case a of MV_Ptr p \<Rightarrow> Some (p, gsz env enc ty) | _ \<Rightarrow> None))"

(* Two pointer regions do not overlap. *)
definition ptr_regions_disjoint :: "MPtr \<times> nat \<Rightarrow> MPtr \<times> nat \<Rightarrow> bool" where
  "ptr_regions_disjoint r1 r2 =
    (case (fst r1, fst r2) of
       (MP_Addr b1 o1, MP_Addr b2 o2) \<Rightarrow> b1 \<noteq> b2 \<or> o1 + snd r1 \<le> o2 \<or> o2 + snd r2 \<le> o1
     | _ \<Rightarrow> True)"

definition pairwise_disjoint :: "(MPtr \<times> nat) list \<Rightarrow> bool" where
  "pairwise_disjoint rs = (\<forall>i j. i < length rs \<longrightarrow> j < length rs \<longrightarrow> i \<noteq> j \<longrightarrow> ptr_regions_disjoint (rs ! i) (rs ! j))"

(* Whether the return value is passed through a buffer: a non-unit aggregate. *)
definition ret_by_buffer :: "CoreType \<Rightarrow> bool" where
  "ret_by_buffer rty = (scalar_ty rty = None \<and> rty \<noteq> CoreTy_Record [])"

(* The instantiated parameter and return types of a call of f at tys. *)
definition inst_param_types :: "FunInfo \<Rightarrow> CoreType list \<Rightarrow> (CoreType \<times> VarOrRef) list" where
  "inst_param_types info tys =
    map (\<lambda>(ty, vor, _). (apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) ty, vor)) (FI_TmArgs info)"

definition inst_ret_type :: "FunInfo \<Rightarrow> CoreType list \<Rightarrow> CoreType" where
  "inst_ret_type info tys = apply_subst (fmap_of_list (zip (FI_TyArgs info) tys)) (FI_ReturnType info)"

(* The MiniC argument list of a call (section 3.4): the return buffer if any,
   the sizes of the type arguments, then the arguments. *)
definition args_rep :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (nat \<Rightarrow> MPtr) \<Rightarrow> FunInfo \<Rightarrow> CoreType list \<Rightarrow> CoreValue list
                        \<Rightarrow> MMem \<Rightarrow> MVal list \<Rightarrow> bool" where
  "args_rep env enc hmap info tys vs mem as =
    (let ptys = inst_param_types info tys; rty = inst_ret_type info tys
     in length tys = length (FI_TyArgs info) \<and> length vs = length ptys
        \<and> (\<exists>retArgs argVals.
             as = retArgs @ map (\<lambda>ty. MV_U64 (int (gsz env enc ty))) tys @ argVals
             \<and> length argVals = length vs
             \<and> (\<forall>i < length vs. arg_rep env enc hmap mem (fst (ptys ! i)) (snd (ptys ! i)) (vs ! i) (argVals ! i))
             \<and> (if ret_by_buffer rty
                then (\<exists>p. retArgs = [MV_Ptr p] \<and> ptr_range_ok mem p (gsz env enc rty))
                else retArgs = [])
             \<and> pairwise_disjoint
                 ((case retArgs of [MV_Ptr p] \<Rightarrow> [(p, gsz env enc rty)] | _ \<Rightarrow> [])
                  @ List.map_filter (\<lambda>(pt, a). arg_region env enc (fst pt) (snd pt) a) (zip ptys argVals))))"

(* The memory after the call agrees with the memory before it on every byte
   outside the regions R (the ref regions and the return region), and keeps
   every block that is not in X (the heap blocks the call may free or
   reallocate: those reachable from the ref arguments). New blocks may
   appear. *)
definition mem_agrees_outside :: "MMem \<Rightarrow> MMem \<Rightarrow> (MPtr \<times> nat) list \<Rightarrow> nat set \<Rightarrow> bool" where
  "mem_agrees_outside mem mem' R X =
    (\<forall>b data. fmlookup (MM_Blocks mem) b = Some data \<longrightarrow> b \<notin> X \<longrightarrow>
       (\<exists>data'. fmlookup (MM_Blocks mem') b = Some data' \<and> length data' = length data
          \<and> (\<forall>k < length data. (\<forall>r \<in> set R. \<forall>ofs. fst r = MP_Addr b ofs \<longrightarrow> \<not> (ofs \<le> k \<and> k < ofs + snd r))
               \<longrightarrow> data' ! k = data ! k)))"

(* The ref regions of a call, in IF_Args order, with the ref updates'
   types: the pointer arguments of the Ref parameters. *)
definition ref_args :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (CoreType \<times> VarOrRef) list \<Rightarrow> MVal list \<Rightarrow> (CoreType \<times> MPtr) list" where
  "ref_args env enc ptys argVals =
    List.map_filter (\<lambda>(pt, a). if snd pt = Ref then (case a of MV_Ptr p \<Rightarrow> Some (fst pt, p) | _ \<Rightarrow> None) else None)
                    (zip ptys argVals)"

(* The results: the ref updates are represented in the ref regions, the
   return value in the return region or as the returned scalar (None for
   the unit type); the results own their blocks (val_owned, pairwise
   disjoint reachable blocks), and every block they reach is either one the
   corresponding argument reached before the call or a block that was not
   live before (an allocation). *)
definition results_rep :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (nat \<Rightarrow> MPtr) \<Rightarrow> MMem \<Rightarrow> MMem \<Rightarrow> CoreType
                           \<Rightarrow> (CoreType \<times> MPtr) list \<Rightarrow> CoreValue list \<Rightarrow> MVal list \<Rightarrow> CoreValue \<Rightarrow> MVal option \<Rightarrow> bool" where
  "results_rep env enc hmap mem mem' rty refs refUpds retArgs ret r =
    (length refUpds = length refs
     \<and> (\<forall>i < length refs. \<exists>bs. mem_read mem' (snd (refs ! i)) (gsz env enc (fst (refs ! i))) = Some bs
          \<and> rep_val env enc hmap mem' (fst (refs ! i)) (refUpds ! i) bs
          \<and> val_owned env enc mem' (fst (refs ! i)) (refUpds ! i) bs
          \<and> (\<forall>b \<in> reach_blocks env enc mem' (fst (refs ! i)) (refUpds ! i) bs.
               fmlookup (MM_Blocks mem) b = None
               \<or> (\<exists>bs0. mem_read mem (snd (refs ! i)) (gsz env enc (fst (refs ! i))) = Some bs0
                       \<and> b \<in> (\<Union>v. reach_blocks env enc mem (fst (refs ! i)) v bs0))))
     \<and> (if ret_by_buffer rty
        then (\<exists>p bs. retArgs = [MV_Ptr p] \<and> r = None \<and> mem_read mem' p (gsz env enc rty) = Some bs
                \<and> rep_val env enc hmap mem' rty ret bs \<and> val_owned env enc mem' rty ret bs
                \<and> (\<forall>b \<in> reach_blocks env enc mem' rty ret bs. fmlookup (MM_Blocks mem) b = None))
        else if rty = CoreTy_Record [] then r = None \<and> ret = CV_Record []
        else (\<exists>mv. r = Some mv \<and> scalar_val hmap ret = Some mv \<and> rep_val env enc hmap mem' rty ret (encode_val enc mv))))"

(* extern_rep (section 6.2): for every world, instantiation, Core arguments
   of the instantiated parameter types, memory and MiniC arguments that
   represent them (with pairwise disjoint regions), the MiniC model returns
   the world the Core function returns, a memory that agrees with the old
   one outside the ref and return regions and the blocks reachable from the
   ref arguments, and results that represent the Core results. *)
definition extern_rep :: "CoreTyEnv \<Rightarrow> MEncoding \<Rightarrow> (nat \<Rightarrow> MPtr) \<Rightarrow> FunInfo \<Rightarrow> 'w ExternFunc \<Rightarrow> 'w MExtern \<Rightarrow> bool" where
  "extern_rep env enc hmap info E M =
    (\<forall>w tys vs mem as.
       args_rep env enc hmap info tys vs mem as
       \<longrightarrow> list_all2 (value_has_type env) vs (map fst (inst_param_types info tys))
       \<longrightarrow> (let ptys = inst_param_types info tys; rty = inst_ret_type info tys;
               retArgs = take (length as - length tys - length vs) as;
               argVals = drop (length as - length vs) as;
               refs = ref_args env enc ptys argVals
           in case E w vs of (w', refUpds, ret) \<Rightarrow>
                (\<exists>mem' r. M w mem as = Some (w', mem', r)
                   \<and> mem_agrees_outside mem mem'
                       (map (\<lambda>(ty, p). (p, gsz env enc ty)) refs
                        @ (case retArgs of [MV_Ptr p] \<Rightarrow> [(p, gsz env enc rty)] | _ \<Rightarrow> []))
                       (\<Union>(ty, p) \<in> set refs. \<Union>bs v. {b. mem_read mem p (gsz env enc ty) = Some bs
                                                          \<and> b \<in> reach_blocks env enc mem ty v bs})
                   \<and> results_rep env enc hmap mem mem' rty refs refUpds retArgs ret r)))"


section \<open>print_i32 satisfies extern_rep\<close>

(* The Core side of print_i32 (Test.b): one by-value i32 argument, unit
   result, the world extended by the printed line. *)
definition print_i32_info :: FunInfo where
  "print_i32_info = \<lparr> FI_TyArgs = [], FI_TmArgs = [(CoreTy_FiniteInt Signed IntBits_32, Var, NotGhost)],
                      FI_ReturnType = CoreTy_Record [], FI_Ghost = NotGhost, FI_Impure = True,
                      FI_Requires = [], FI_Ensures = [] \<rparr>"

definition print_i32_core :: "World ExternFunc" where
  "print_i32_core w vs =
    (case vs of [CV_FiniteInt _ _ i] \<Rightarrow> (w @ int_to_string i @ newline, [], CV_Record [])
     | _ \<Rightarrow> (w, [], CV_Record []))"

lemma print_i32_extern_rep:
  "extern_rep env enc hmap print_i32_info print_i32_core print_int_model"
proof -
  have ptys: "inst_param_types print_i32_info tys = [(CoreTy_FiniteInt Signed IntBits_32, Var)]" for tys
    by (simp add: inst_param_types_def print_i32_info_def)
  have rty: "inst_ret_type print_i32_info tys = CoreTy_Record []" for tys
    by (simp add: inst_ret_type_def print_i32_info_def)
  show ?thesis
    unfolding extern_rep_def
  proof (intro allI impI)
    fix w tys vs mem "as"
    assume A: "args_rep env enc hmap print_i32_info tys vs mem as"
      and T: "list_all2 (value_has_type env) vs (map fst (inst_param_types print_i32_info tys))"
    from A have tys: "tys = []" by (simp add: args_rep_def Let_def print_i32_info_def)
    from A obtain v a where vs: "vs = [v]" and as: "as = [a]"
      and ar: "arg_rep env enc hmap mem (CoreTy_FiniteInt Signed IntBits_32) Var v a"
      unfolding args_rep_def ptys rty tys
      by (auto simp: Let_def ret_by_buffer_def length_Suc_conv)
    from T obtain i where v: "v = CV_FiniteInt Signed IntBits_32 i"
      unfolding vs ptys by (cases v) auto
    from ar have a: "a = MV_Int Signed IntBits_32 i" unfolding arg_rep_def v by simp
    have E: "print_i32_core w vs = (w @ int_to_string i @ newline, [], CV_Record [])"
      unfolding print_i32_core_def vs v by simp
    have M: "print_int_model w mem as = Some (w @ int_to_string i @ newline, mem, None)"
      unfolding print_int_model_def as a by simp
    have refs: "ref_args env enc (inst_param_types print_i32_info tys) (drop (length as - length vs) as) = []"
      unfolding ptys as vs by (simp add: ref_args_def List.map_filter_def)
    have retArgs: "take (length as - length tys - length vs) as = []" unfolding as vs tys by simp
    show "let ptys = inst_param_types print_i32_info tys; rty = inst_ret_type print_i32_info tys;
              retArgs = take (length as - length tys - length vs) as;
              argVals = drop (length as - length vs) as;
              refs = ref_args env enc ptys argVals
          in case print_i32_core w vs of (w', refUpds, ret) \<Rightarrow>
               (\<exists>mem' r. print_int_model w mem as = Some (w', mem', r)
                  \<and> mem_agrees_outside mem mem'
                      (map (\<lambda>(ty, p). (p, gsz env enc ty)) refs
                       @ (case retArgs of [MV_Ptr p] \<Rightarrow> [(p, gsz env enc rty)] | _ \<Rightarrow> []))
                      (\<Union>(ty, p) \<in> set refs. \<Union>bs v. {b. mem_read mem p (gsz env enc ty) = Some bs
                                                         \<and> b \<in> reach_blocks env enc mem ty v bs})
                  \<and> results_rep env enc hmap mem mem' rty refs refUpds retArgs ret r)"
      unfolding Let_def refs retArgs rty E prod.case
    proof (intro exI[where x = mem] exI[where x = None] conjI)
      show "print_int_model w mem as = Some (w @ int_to_string i @ newline, mem, None)" by (rule M)
      show "mem_agrees_outside mem mem (map (\<lambda>(ty, p). (p, gsz env enc ty)) [] @ (case [] of [MV_Ptr p] \<Rightarrow> [(p, gsz env enc (CoreTy_Record []))] | _ \<Rightarrow> []))
              (\<Union>(ty, p) \<in> set []. \<Union>bs v. {b. mem_read mem p (gsz env enc ty) = Some bs \<and> b \<in> reach_blocks env enc mem ty v bs})"
        by (simp add: mem_agrees_outside_def)
      show "results_rep env enc hmap mem mem (CoreTy_Record []) [] [] [] (CV_Record []) None"
        by (simp add: results_rep_def ret_by_buffer_def)
    qed
  qed
qed

end

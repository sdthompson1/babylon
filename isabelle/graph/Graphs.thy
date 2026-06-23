theory Graphs
  imports Main "HOL-Library.Finite_Map"
begin

(* Graph theory definitions, reachability, SCCs, graph transposition. *)


(*-----------------------------------------------------------------------------*)
(* Graph Theory Definitions *)
(*-----------------------------------------------------------------------------*)

(* We represent graphs as an adjacency list. *)
(* Note: we will require 'a to have linorder, for efficient code generation. *)
type_synonym 'a Graph = "('a, 'a list) fmap"

(* Predicate for whether the graph contains a vertex v. *)
fun has_vertex :: "('a::linorder) Graph \<Rightarrow> 'a \<Rightarrow> bool" where
  "has_vertex graph v \<longleftrightarrow> v |\<in>| fmdom graph"

(* Predicate for whether a graph contains an edge from v to w. *)
fun has_edge :: "('a::linorder) Graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "has_edge graph v w \<longleftrightarrow>
    (case fmlookup graph v of
      None \<Rightarrow> False
    | Some neighbors \<Rightarrow> List.member neighbors w)"

(* Lemma: If v is a vertex, then has_edge is equivalent to membership in neighbor list *)
lemma has_edge_member_conv:
  assumes "has_vertex graph v"
  shows "has_edge graph v w \<longleftrightarrow> List.member (the (fmlookup graph v)) w"
  using assms by (auto split: option.splits)

(* A graph is valid if whenever v is a valid vertex and (v,w) is an edge,
   then w is a valid vertex. *)
fun valid_graph :: "('a::linorder) Graph \<Rightarrow> bool" where
  "valid_graph graph \<longleftrightarrow>
    (\<forall>v. has_vertex graph v \<longrightarrow> (\<forall>w. has_edge graph v w \<longrightarrow> 
      has_vertex graph w))"

(* Lemma: In a valid graph, an edge from a to b implies that a and b are vertices *)
lemma edge_implies_vertices:
  assumes "valid_graph graph"
    and "has_edge graph a b"
  shows "has_vertex graph a"
    and "has_vertex graph b"
proof -
  show "has_vertex graph a"
  proof -
    have "fmlookup graph a \<noteq> None"
      using assms(2) by (cases "fmlookup graph a") auto
    then show ?thesis
      using fmdom_notD by force 
  qed
  show "has_vertex graph b"
    using assms(1) \<open>has_vertex graph a\<close> assms(2) by auto
qed

(* Define reachability in a graph. *)
inductive reachable :: "('a::linorder) Graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for graph where
  reachable_refl: "has_vertex graph v \<Longrightarrow> reachable graph v v"
| reachable_step: "(reachable graph v w \<and> has_edge graph w u)
                    \<Longrightarrow> reachable graph v u"

(* Lemma: Reachability is transitive *)
lemma reachable_trans:
  assumes "reachable graph v u"
    and "reachable graph u w"
  shows "reachable graph v w"
  using assms(2) assms(1)
proof (induction arbitrary: v)
  case (reachable_refl u)
  (* We have reachable graph u u, so u = w *)
  (* We need to show reachable graph v w = reachable graph v u *)
  (* Which is just our assumption: reachable graph v u *)
  then show ?case by simp
next
  case (reachable_step u x w)
  (* We have:
     - reachable graph u x (from the inductive predicate)
     - has_edge graph x w (from the inductive predicate)
     - reachable graph v u (given as arbitrary parameter)
     - IH: \<forall>v. reachable graph v u \<rightarrow> reachable graph v x
  *)
  (* We need: reachable graph v w *)

  (* Apply IH with v to get reachable graph v x *)
  have "reachable graph v x"
    using reachable_step.IH reachable_step.prems by auto

  (* Now extend with edge x \<rightarrow> w *)
  then show ?case
    using reachable.reachable_step reachable_step.IH by blast
qed

(* Lemma: In a valid graph, if a reaches b then a and b are vertices *)
lemma reachable_implies_vertices:
  assumes "valid_graph graph"
    and "reachable graph a b"
  shows "has_vertex graph a"
    and "has_vertex graph b"
  using assms(2,1)
proof (induction rule: reachable.induct)
  case (reachable_refl v)
  then show "has_vertex graph v" by simp
  then show "has_vertex graph v" by simp
next
  case (reachable_step v w u)
  (* We have: reachable graph v w and has_edge graph w u *)
  (* IH gives us: has_vertex graph v and has_vertex graph w *)

  show "has_vertex graph v"
    using reachable_step.IH
    using assms(1) by blast 

  show "has_vertex graph u"
    using assms(1) edge_implies_vertices(2) local.reachable_step by blast
qed

(* Lemma: If v reaches w and v \<noteq> w, then there's a first step *)
lemma reachable_first_step:
  assumes "valid_graph graph"
    and "reachable graph v w"
    and "v \<noteq> w"
  shows "\<exists>x. has_edge graph v x \<and> reachable graph x w"
  using assms(2,3,1)
proof (induction)
  case (reachable_refl v)
  (* v = w, contradicts assumption v \<noteq> w *)
  then show ?case by simp
next
  case (reachable_step v' w' u)
  (* We have: reachable graph v' w' and has_edge graph w' u *)
  (* We need to show: \<exists>x. has_edge graph v x \<and> reachable graph x w *)
  (* where v = v' and w = u *)
  show ?case
  proof (cases "v' = w'")
    case True
    (* v' = w', so v reaches w' in zero steps, and we have edge w' -> u *)
    (* So v = v' = w', and there's an edge v -> u, and u reaches u *)
    have "has_edge graph v' u" using reachable_step True by auto
    moreover have "reachable graph u u"
      using reachable_step reachable_refl fmdom_notD
      by (metis has_edge.elims(1) has_vertex.simps option.case_eq_if
          valid_graph.elims(2)) 
    ultimately show ?thesis using True by auto
  next
    case False
    (* v' \<noteq> w', so by IH there exists x such that v' -> x and x reaches w' *)
    (* Then v' -> x and by transitivity x reaches u *)
    have "\<exists>x. has_edge graph v' x \<and> reachable graph x w'"
      using reachable_step.IH False
      using reachable_step.prems(2) by blast 
    then obtain x where "has_edge graph v' x" and "reachable graph x w'"
      by auto
    (* Now x reaches w' and w' -> u, so x reaches u *)
    have "reachable graph x u"
      using \<open>reachable graph x w'\<close> reachable_step
      using reachable.reachable_step by blast
    then show ?thesis using \<open>has_edge graph v' x\<close> by auto
  qed
qed

(*-----------------------------------------------------------------------------*)
(* Explicit Path Representation *)
(*-----------------------------------------------------------------------------*)

(* A list represents a valid path in the graph.
   The list contains all vertices on the path, including start and end.
   - [] is not a valid path
   - [v] is a valid path (from v to itself) if v is a vertex
   - [u, v, w, ...] is valid if there are edges u->v, v->w, etc.
  Note: we *don't* require path elements to be distinct.
*)
fun valid_path :: "('a::linorder) Graph \<Rightarrow> 'a list \<Rightarrow> bool" where
  "valid_path graph [] = False"
| "valid_path graph [v] = has_vertex graph v"
| "valid_path graph (u # v # rest) =
    (has_edge graph u v \<and> valid_path graph (v # rest))"

(* Extract the start vertex from a path *)
fun path_start :: "'a list \<Rightarrow> 'a" where
  "path_start [] = undefined"
| "path_start (v # _) = v"

(* Extract the end vertex from a path *)
fun path_end :: "'a list \<Rightarrow> 'a" where
  "path_end [] = undefined"
| "path_end [v] = v"
| "path_end (_ # rest) = path_end rest"

(* Lemma: The end vertex of a non-empty path is a member of the path *)
lemma path_end_in_path:
  assumes "path \<noteq> []"
  shows "List.member path (path_end path)"
  using assms
proof (induction path rule: path_end.induct)
  case 1
  then show ?case by simp
next
  case (2 v)
  then show ?case by (simp add: member_rec(1))
next
  case (3 v va list)
  then have "List.member (va # list) (path_end (va # list))"
    by simp
  then show ?case
    by (simp add: member_rec(1))
qed

(* Lemma: If a path contains vertex v and ends at a different vertex,
   then there exists an edge from v to some next vertex, and a valid
   path from next to the end that doesn't contain v.
   This is proven by finding the last occurrence of v in the path.
   Additionally, all vertices in the suffix are in the original path. *)
lemma path_through_v_has_next:
  assumes "valid_path graph path"
    and "path_end path = target"
    and "List.member path v"
    and "target \<noteq> v"
  shows "\<exists>next suffix.
         has_edge graph v next \<and>
         valid_path graph (next # suffix) \<and>
         path_end (next # suffix) = target \<and>
         \<not>List.member (next # suffix) v \<and>
         (\<forall>u. List.member (next # suffix) u \<longrightarrow> List.member path u)"
  using assms
proof (induction path arbitrary: target rule: valid_path.induct)
  case (1 graph)
  (* path = [], contradicts valid_path *)
  then show ?case by simp
next
  case (2 graph w)
  (* path = [w], so target = w, but we have target \<noteq> v and v \<in> path,
     so w = v and target = v, contradiction *)
  then show ?case by (simp add: member_rec)
next
  case (3 graph u w rest)
  (* path = u # w # rest *)
  then have "target = path_end (w # rest)"
    by simp
  then show ?case
  proof (cases "u = v")
    case True
    (* u = v, so we found v at the head *)
    then show ?thesis
    proof (cases "List.member (w # rest) v")
      case True
      (* v appears later in the path too, so recurse *)
      have "valid_path graph (w # rest)"
        using 3 by simp
      moreover have "path_end (w # rest) = target"
        using \<open>target = path_end (w # rest)\<close> by simp
      moreover have "List.member (w # rest) v"
        using True by simp
      moreover have "target \<noteq> v"
        using 3 by simp
      ultimately obtain nxt suffix where
        nxt_edge: "has_edge graph v nxt"
        and suffix_valid: "valid_path graph (nxt # suffix)"
        and suffix_end: "path_end (nxt # suffix) = target"
        and suffix_no_v: "\<not>List.member (nxt # suffix) v"
        and suffix_in_rest: "(\<forall>u. List.member (nxt # suffix) u \<longrightarrow> List.member (w # rest) u)"
        using 3(1) by blast
      have suffix_in_path: "(\<forall>ua. List.member (nxt # suffix) ua \<longrightarrow> List.member (u # w # rest) ua)"
        using suffix_in_rest by (simp add: member_rec)
      show ?thesis
        using nxt_edge suffix_valid suffix_end suffix_no_v suffix_in_path
        by (intro exI[where x=nxt] exI[where x=suffix]) simp 
    next
      case False
      (* v doesn't appear in w # rest, so this is the last v *)
      have "has_edge graph v w"
        using 3 \<open>u = v\<close> by simp
      moreover have "valid_path graph (w # rest)"
        using 3 by simp
      moreover have "path_end (w # rest) = target"
        using \<open>target = path_end (w # rest)\<close> by simp
      moreover have "\<not>List.member (w # rest) v"
        using False by simp
      moreover have "(\<forall>ua. List.member (w # rest) ua \<longrightarrow> List.member (u # w # rest) ua)"
        by (simp add: member_rec)
      ultimately show ?thesis
        by (intro exI[where x=w] exI[where x=rest]) simp 
    qed
  next
    case False
    (* u \<noteq> v, so v must be in w # rest *)
    have "List.member (w # rest) v"
      using 3(4) False by (simp add: member_rec)
    have "valid_path graph (w # rest)"
      using 3 by simp
    moreover have "path_end (w # rest) = target"
      using \<open>target = path_end (w # rest)\<close> by simp
    moreover have "target \<noteq> v"
      using 3 by simp
    ultimately obtain nxt suffix where
      nxt_edge: "has_edge graph v nxt"
      and suffix_valid: "valid_path graph (nxt # suffix)"
      and suffix_end: "path_end (nxt # suffix) = target"
      and suffix_no_v: "\<not>List.member (nxt # suffix) v"
      and suffix_in_rest: "(\<forall>u. List.member (nxt # suffix) u \<longrightarrow> List.member (w # rest) u)"
      using 3(1) \<open>List.member (w # rest) v\<close> by blast
    have suffix_in_path: "(\<forall>ua. List.member (nxt # suffix) ua \<longrightarrow> List.member (u # w # rest) ua)"
      using suffix_in_rest by (simp add: member_rec)
    show ?thesis
      using nxt_edge suffix_valid suffix_end suffix_no_v suffix_in_path
      by (intro exI[where x=nxt] exI[where x=suffix]) simp 
  qed
qed

(* Lemma: A valid path implies reachability *)
lemma valid_path_implies_reachable:
  assumes "valid_graph graph"
    and "valid_path graph path"
    and "path_start path = start"
    and "path_end path = target"
  shows "reachable graph start target"
  using assms
proof (induction path arbitrary: start rule: valid_path.induct)
  case (1 graph)
  (* path = [], contradicts valid_path *)
  then show ?case by simp
next
  case (2 graph v)
  (* path = [v], so start = v and target = v *)
  then have "start = v" by simp
  moreover have "target = v" using 2 by simp
  moreover have "has_vertex graph v" using 2 by simp
  ultimately show ?case using reachable_refl by simp
next
  case (3 graph u w rest)
  (* path = u # w # rest *)
  then have "start = u" by simp
  have "has_edge graph u w" using 3 by simp
  have "path_start (w # rest) = w" by simp
  moreover have "path_end (w # rest) = target" using 3 by simp
  moreover have "valid_path graph (w # rest)" using 3 by simp
  ultimately have "reachable graph w target"
    using 3(1)
    using "3.prems"(1) by blast 
  then have "reachable graph u w \<and> has_edge graph w target \<or>
             reachable graph u target"
  proof (cases "w = target")
    case True
    then have "reachable graph u w"
      using \<open>has_edge graph u w\<close> reachable.intros
      by (metis fmdom_notD has_edge.elims(1) has_vertex.simps
          option.case_eq_if)
    then show ?thesis using True by simp
  next
    case False
    (* w \<noteq> target, so we can use reachability transitivity *)
    have "has_vertex graph u"
      using \<open>has_edge graph u w\<close>
      using fmdom_notD by fastforce
    then have "reachable graph u u" using reachable_refl by simp
    then have "reachable graph u w"
      using \<open>has_edge graph u w\<close> reachable.reachable_step by blast
    then have "reachable graph u target"
      using \<open>reachable graph w target\<close> reachable_trans by blast
    then show ?thesis by simp
  qed
  then show ?case using \<open>start = u\<close>
    using reachable_step by blast 
qed

(* Lemma: Reachability implies existence of a valid path *)
lemma reachable_implies_valid_path:
  assumes "valid_graph graph"
    and "reachable graph start target"
  shows "\<exists>path. valid_path graph path \<and>
               path_start path = start \<and>
               path_end path = target"
  using assms(2,1)
proof (induction rule: reachable.induct)
  case (reachable_refl v)
  (* start = target = v *)
  show ?case
    by (meson path_end.simps(2) path_start.simps(2) reachable_refl.hyps
        valid_path.simps(2))
next
  case (reachable_step v w u)
  (* We have reachable graph v w and has_edge graph w u *)
  (* By IH, there exists a path from v to w *)
  obtain pth where
    pth_valid: "valid_path graph pth"
    and pth_start: "path_start pth = v"
    and pth_end: "path_end pth = w"
    using reachable_step.IH
    using reachable_step.prems by blast 

  (* Extend the path with u *)
  define extended where "extended = pth @ [u]"

  have edge_wu: "has_edge graph w u"
    using reachable_step.IH by blast
  have valid_g: "valid_graph graph"
    using reachable_step.prems by simp

  have "valid_path graph extended"
    unfolding extended_def
    using pth_valid pth_end edge_wu valid_g
  proof (induction pth arbitrary: w rule: valid_path.induct)
    case (1 graph)
    then show ?case by simp
  next
    case (2 graph x)
    then have "w = x" by simp
    then have "has_edge graph x u" using 2 by simp
    then have "has_vertex graph u"
      by (meson "2.prems"(1,4) valid_graph.elims(2)
          valid_path.simps(2))
    then show ?case
      using \<open>has_edge graph x u\<close>
      by simp
  next
    case (3 graph x y rest)
    then have "path_end (y # rest) = w" by simp
    then have "valid_path graph ((y # rest) @ [u])"
      using 3 by simp
    then show ?case
      using 3(2) by simp
  qed

  moreover have "path_start extended = v"
    unfolding extended_def using pth_start pth_valid
    by (metis append_Cons path_start.cases path_start.simps(2)
        valid_path.simps(1))

  moreover have "path_end extended = u"
    unfolding extended_def using pth_valid
    by (induction pth rule: valid_path.induct) auto

  ultimately show ?case by blast
qed

(* Lemma: If v is on a path from x to z, then x reaches v and v reaches z *)
lemma vertex_on_path_reachable:
  assumes "valid_graph graph"
    and "valid_path graph path"
    and "path_start path = x"
    and "path_end path = z"
    and "v \<in> set path"
  shows "reachable graph x v \<and> reachable graph v z"
proof -
  have "reachable graph x v"
    using assms(1,2) \<open>v \<in> set path\<close> \<open>path_start path = x\<close>
  proof (induction path arbitrary: x rule: valid_path.induct)
    case (1 graph)
    then show ?case by simp
  next
    case (2 graph u)
    then show ?case by (simp add: reachable.reachable_refl)
  next
    case (3 graph u v' rest)
    then show ?case
      by (metis fmdom_notD has_edge.elims(1) has_vertex.simps
          option.case_eq_if path_start.simps(2) reachable.simps reachable_trans
          set_ConsD valid_path.simps(3))
  qed

  moreover have "reachable graph v z"
    using assms(1,2) \<open>v \<in> set path\<close> \<open>path_end path = z\<close>
  proof (induction path arbitrary: z rule: valid_path.induct)
    case (1 graph)
    then show ?case by simp
  next
    case (2 graph u)
    then show ?case by (simp add: reachable.reachable_refl)
  next
    case (3 graph u v' rest)
    then show ?case
      by (metis path_end.simps(3) path_start.simps(2) set_ConsD
          valid_path.simps(3) valid_path_implies_reachable)
  qed

  ultimately show ?thesis by simp
qed

(* Lemma: From any reachable vertex, we can find a path where the start vertex
   doesn't appear in the rest of the path *)
lemma reachable_implies_path_without_revisit:
  assumes "valid_graph graph"
    and "reachable graph x z"
    and "x \<noteq> z"
  shows "\<exists>path. valid_path graph path \<and> path_start path = x \<and> path_end path = z \<and>
               (\<forall>v. v \<in> set (tl path) \<longrightarrow> v \<noteq> x)"
proof -
  (* Get any valid path from x to z *)
  obtain path where path_props: "valid_path graph path" "path_start path = x" "path_end path = z"
    using assms reachable_implies_valid_path
    by blast 

  (* x is a member of path since it's the start *)
  have "List.member path x"
    using path_props
    by (metis member_rec(1) path_start.elims valid_path.simps(1)) 

  (* Apply path_through_v_has_next to get a suffix from some neighbor of x to z without x *)
  obtain nxt suffix where suffix_props:
    "has_edge graph x nxt"
    "valid_path graph (nxt # suffix)"
    "path_end (nxt # suffix) = z"
    "\<not>List.member (nxt # suffix) x"
    using path_through_v_has_next
    using \<open>List.member path x\<close> assms(3) path_props(1,3) by blast 

  (* Construct the path x # next # suffix *)
  define new_path where "new_path = x # nxt # suffix"

  have "valid_path graph new_path"
    using suffix_props(1) suffix_props(2) new_path_def by auto

  moreover have "path_start new_path = x"
    using new_path_def by simp

  moreover have "path_end new_path = z"
    using suffix_props(3) new_path_def by simp

  moreover have "\<forall>v. v \<in> set (tl new_path) \<longrightarrow> v \<noteq> x"
    using suffix_props(4) new_path_def
    by (metis in_set_member list.sel(3)) 

  ultimately show ?thesis by blast
qed

(* Lemma: Concatenating two valid paths with an edge between them makes a valid path *)
lemma path_concat_with_edge:
  assumes "valid_graph graph"
    and "valid_path graph path1"
    and "valid_path graph path2"
    and "path_end path1 = u"
    and "path_start path2 = v"
    and "has_edge graph u v"
  shows "valid_path graph (path1 @ path2)"
    and "path_start (path1 @ path2) = path_start path1"
    and "path_end (path1 @ path2) = path_end path2"
proof -
  show "valid_path graph (path1 @ path2)"
    using assms
  proof (induction path1 rule: valid_path.induct)
    case (1 graph)
    then show ?case by simp
  next
    case (2 graph w)
    then have "w = u" by simp
    moreover have "hd path2 = v"
      using "2.prems"(3,4)
      by (metis assms(5) list.sel(1) path_start.elims
          valid_path.simps(1)) 
    ultimately show ?case
      using "2.prems"(2,5)
      by (metis "2.prems"(3,6) append_Cons append_Nil2 append_eq_append_conv2
          path_start.elims same_append_eq valid_path.simps(3))
  next
    case (3 graph w1 w2 rest)
    then have edge: "has_edge graph w1 w2" by simp
    have rest_path: "valid_path graph (w2 # rest)" using "3.prems"(2) by auto
    have "path_end (w2 # rest) = u"
      using "3.prems"(4) by auto
    then have "valid_path graph ((w2 # rest) @ path2)"
      using "3.IH" "3.prems"(1,3,6) assms(5) rest_path by blast
    then show ?case
      using edge by simp
  qed
next
  show "path_start (path1 @ path2) = path_start path1"
    using assms(2,3,5)
    by (metis append_Cons neq_Nil_conv path_start.simps(2) valid_path.simps(1))
next
  show "path_end (path1 @ path2) = path_end path2"
    using assms(2,3)
  proof (induction path1 rule: valid_path.induct)
    case (1 graph)
    then show ?case by simp
  next
    case (2 graph w)
    then show ?case
      by (metis append_Cons append_Nil path_end.simps(3) path_start.elims
          valid_path.simps(1))
  next
    case (3 graph w1 w2 rest)
    then show ?case by simp
  qed
qed


(*-----------------------------------------------------------------------------*)
(* Strongly connected components (SCCs) *)
(*-----------------------------------------------------------------------------*)

(* Two vertices are in the same SCC if they're mutually reachable *)
fun in_same_scc :: "('a::linorder) Graph \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "in_same_scc graph v w \<longleftrightarrow> reachable graph v w \<and> reachable graph w v"

(* Lemma: in_same_scc is reflexive *)
lemma in_same_scc_refl:
  assumes "has_vertex graph v"
  shows "in_same_scc graph v v"
  using assms reachable.reachable_refl by simp

(* Lemma: in_same_scc is symmetric *)
lemma in_same_scc_sym:
  assumes "in_same_scc graph v w"
  shows "in_same_scc graph w v"
  using assms by simp

(* Lemma: in_same_scc is transitive *)
lemma in_same_scc_trans:
  assumes "in_same_scc graph v u"
    and "in_same_scc graph u w"
  shows "in_same_scc graph v w"
  using assms reachable_trans by auto

(* Two SCCs are either disjoint or equal *)
lemma scc_disjoint_or_equal:
  assumes "valid_graph graph"
    and "\<exists>v1 \<in> scc1. scc1 = {w. has_vertex graph w \<and> in_same_scc graph w v1}"
    and "\<exists>v2 \<in> scc2. scc2 = {w. has_vertex graph w \<and> in_same_scc graph w v2}"
  shows "scc1 = scc2 \<or> scc1 \<inter> scc2 = {}"
proof -
  (* Extract representatives from the assumptions *)
  obtain v1 where v1_def: "v1 \<in> scc1" "scc1 = {w. has_vertex graph w \<and> in_same_scc graph w v1}"
    using assms(2) by blast
  obtain v2 where v2_def: "v2 \<in> scc2" "scc2 = {w. has_vertex graph w \<and> in_same_scc graph w v2}"
    using assms(3) by blast

  (* Show that either the SCCs are equal or disjoint *)
  show ?thesis
  proof (cases "scc1 \<inter> scc2 = {}")
    case True
    then show ?thesis by simp
  next
    case False
    (* scc1 and scc2 have a common element, so they must be equal *)
    then obtain x where x_in_both: "x \<in> scc1" "x \<in> scc2" by blast

    (* From x \<in> scc1, we have x is in same SCC as v1 *)
    have "in_same_scc graph x v1"
      using x_in_both(1) v1_def(2) by auto

    (* From x \<in> scc2, we have x is in same SCC as v2 *)
    have "in_same_scc graph x v2"
      using x_in_both(2) v2_def(2) by auto

    (* By transitivity, v1 and v2 are in the same SCC *)
    have "in_same_scc graph v1 v2"
      using in_same_scc_sym in_same_scc_trans
      by (meson \<open>in_same_scc graph x v1\<close> \<open>in_same_scc graph x v2\<close>)

    (* Therefore, scc1 = scc2 *)
    have "scc1 = scc2"
    proof (rule set_eqI)
      fix w
      show "w \<in> scc1 \<longleftrightarrow> w \<in> scc2"
      proof
        assume "w \<in> scc1"
        then have "has_vertex graph w" "in_same_scc graph w v1"
          using v1_def(2) by auto
        then have "in_same_scc graph w v2"
          using in_same_scc_trans \<open>in_same_scc graph v1 v2\<close> by blast
        then show "w \<in> scc2"
          using \<open>has_vertex graph w\<close> v2_def(2) by auto
      next
        assume "w \<in> scc2"
        then have "has_vertex graph w" "in_same_scc graph w v2"
          using v2_def(2) by auto
        then have "in_same_scc graph w v1"
          using in_same_scc_sym in_same_scc_trans \<open>in_same_scc graph v1 v2\<close> by blast
        then show "w \<in> scc1"
          using \<open>has_vertex graph w\<close> v1_def(2) by auto
      qed
    qed

    then show ?thesis by simp
  qed
qed

(* Lemma: If start and end of a path are in the same SCC,
   then every vertex on the path is in that SCC *)
lemma path_in_scc_all_in_scc:
  assumes "valid_graph graph"
    and "valid_path graph path"
    and "in_same_scc graph (path_start path) (path_end path)"
  shows "\<forall>v. v \<in> set path \<longrightarrow> in_same_scc graph v (path_start path)"
proof (intro allI impI)
  fix v
  assume "v \<in> set path"

  obtain x z where "path_start path = x" "path_end path = z"
    by auto

  (* x and z are in the same SCC *)
  have "in_same_scc graph x z"
    using assms(3) \<open>path_start path = x\<close> \<open>path_end path = z\<close> by simp

  (* v is on the path, so x reaches v and v reaches z *)
  have "reachable graph x v \<and> reachable graph v z"
    using vertex_on_path_reachable[OF assms(1) assms(2) \<open>path_start path = x\<close> \<open>path_end path = z\<close> \<open>v \<in> set path\<close>]
    by simp
  then have "reachable graph x v" "reachable graph v z" by simp_all

  (* Since x and z are in same SCC, z reaches x *)
  have "reachable graph z x"
    using \<open>in_same_scc graph x z\<close> by simp

  (* Therefore v reaches x (via v \<rightarrow> z \<rightarrow> x) and x reaches v, so they're in same SCC *)
  have "reachable graph v x"
    using \<open>reachable graph v z\<close> \<open>reachable graph z x\<close>
    by (rule reachable_trans)

  then show "in_same_scc graph v (path_start path)"
    using \<open>reachable graph x v\<close> \<open>path_start path = x\<close>
    by simp
qed

(* Lemma: In an SCC with distinct vertices, there's always a path that avoids a given vertex *)
lemma scc_path_avoiding_vertex:
  assumes "valid_graph graph"
    and "in_same_scc graph x q"
    and "x \<noteq> q"
  shows "\<exists>p. has_edge graph x p \<and>
             in_same_scc graph p x \<and>
             (\<exists>path. valid_path graph path \<and>
                     path_start path = p \<and>
                     path_end path = q \<and>
                     \<not>List.member path x)"
proof -
  (* x reaches q, so there's a path from x to q *)
  have x_reaches_q: "reachable graph x q"
    using assms(2) by simp

  (* Get a path from x to q without revisiting x *)
  obtain path_xq where path_xq_props:
    "valid_path graph path_xq"
    "path_start path_xq = x"
    "path_end path_xq = q"
    "\<forall>v. v \<in> set (tl path_xq) \<longrightarrow> v \<noteq> x"
    using reachable_implies_path_without_revisit[OF assms(1) x_reaches_q assms(3)]
    by blast

  (* path_xq must have at least 2 elements since x \<noteq> q *)
  have "path_xq \<noteq> []"
    using path_xq_props(1) by (cases path_xq) auto

  (* Extract the first edge: path_xq = x # p # rest *)
  obtain p path_rest where decomp: "path_xq = x # p # path_rest"
    using path_xq_props assms(3)
    by (metis \<open>path_xq \<noteq> []\<close> list.exhaust_sel path_end.simps(2) path_start.simps(2))

  (* We have edge x -> p *)
  have edge_xp: "has_edge graph x p"
    using path_xq_props(1) decomp by auto

  (* p is in the same SCC as x *)
  have "in_same_scc graph p x"
  proof -
    (* p is on the path from x to q, and x and q are in same SCC *)
    have "p \<in> set path_xq"
      using decomp by simp
    then have "in_same_scc graph p x"
      using path_in_scc_all_in_scc[OF assms(1) path_xq_props(1)] assms(2)
      using path_xq_props(2,3)
      by blast 
    then show ?thesis by simp
  qed

  (* Build the path from p to q: it's just (p # path_rest) *)
  define path_pq where "path_pq = p # path_rest"

  have "valid_path graph path_pq"
    using path_xq_props(1) decomp path_pq_def by auto

  moreover have "path_start path_pq = p"
    using path_pq_def by simp

  moreover have "path_end path_pq = q"
    using path_xq_props(3) decomp path_pq_def
    by (metis path_end.simps(3))

  moreover have "\<not>List.member path_pq x"
    using path_xq_props(4) decomp path_pq_def
    by (metis in_set_member list.sel(3))

  ultimately show ?thesis
    using edge_xp \<open>in_same_scc graph p x\<close>
    by blast
qed


(*-----------------------------------------------------------------------------*)
(* Transposing a graph *)
(*-----------------------------------------------------------------------------*)

(* Helper function 1 *)
(* Given a vertex v and its neighbors (from the original graph), add the reversed
   edges to the new graph *)
fun add_reverse_edges :: "('a::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a Graph \<Rightarrow> 'a Graph" where
  "add_reverse_edges v neighbors reverseGraph =
     foldr (\<lambda>w g'.
       let old_list = (case fmlookup g' w of None \<Rightarrow> [] | Some l \<Rightarrow> l)
       in fmupd w (v # old_list) g'
     ) neighbors reverseGraph"

(* Lemma: add_reverse_edges preserves existing vertices *)
lemma add_reverse_edges_preserves_vertices:
  assumes "has_vertex reverseGraph v"
  shows "has_vertex (add_reverse_edges u neighbors reverseGraph) v"
  using assms
proof (induction neighbors arbitrary: reverseGraph)
  case Nil
  then show ?case by simp
next
  case (Cons w rest)
  have "has_vertex (add_reverse_edges u rest reverseGraph) v"
    using Cons.IH Cons.prems by simp
  moreover have "add_reverse_edges u (w # rest) reverseGraph =
                 (let old_list = (case fmlookup (add_reverse_edges u rest reverseGraph) w of None \<Rightarrow> [] | Some l \<Rightarrow> l)
                  in fmupd w (u # old_list) (add_reverse_edges u rest reverseGraph))"
    by simp
  ultimately show ?case
    by (auto simp: Let_def)
qed

(* Lemma: add_reverse_edges adds vertices for each neighbor *)
lemma add_reverse_edges_adds_neighbor_vertices:
  assumes "List.member neighbors w"
  shows "has_vertex (add_reverse_edges v neighbors reverseGraph) w"
  using assms
proof (induction neighbors arbitrary: reverseGraph)
  case Nil
  then show ?case by (simp add: member_rec(2))
next
  case (Cons n rest)
  show ?case
  proof (cases "n = w")
    case True
    (* w is the first neighbor, so we do fmupd w ... *)
    have "add_reverse_edges v (w # rest) reverseGraph =
          (let old_list = (case fmlookup (add_reverse_edges v rest reverseGraph) w of None \<Rightarrow> [] | Some l \<Rightarrow> l)
           in fmupd w (v # old_list) (add_reverse_edges v rest reverseGraph))"
      by simp
    then show ?thesis
      by (simp add: True)
  next
    case False
    (* w is in rest *)
    then have "List.member rest w"
      using Cons.prems by (simp add: member_rec(1))
    then have "has_vertex (add_reverse_edges v rest reverseGraph) w"
      using Cons.IH by simp
    moreover have "add_reverse_edges v (n # rest) reverseGraph =
                   (let old_list = (case fmlookup (add_reverse_edges v rest reverseGraph) n of None \<Rightarrow> [] | Some l \<Rightarrow> l)
                    in fmupd n (v # old_list) (add_reverse_edges v rest reverseGraph))"
      by simp
    ultimately show ?thesis
      using False by (auto simp: Let_def)
  qed
qed

(* Lemma: add_reverse_edges only adds vertices that are in neighbors *)
lemma add_reverse_edges_vertices_only_from_neighbors:
  assumes "has_vertex (add_reverse_edges v neighbors reverseGraph) w"
  shows "has_vertex reverseGraph w \<or> List.member neighbors w"
  using assms
proof (induction neighbors arbitrary: reverseGraph)
  case Nil
  then show ?case by simp
next
  case (Cons n rest)
  have "add_reverse_edges v (n # rest) reverseGraph =
        (let old_list = (case fmlookup (add_reverse_edges v rest reverseGraph) n of None \<Rightarrow> [] | Some l \<Rightarrow> l)
         in fmupd n (v # old_list) (add_reverse_edges v rest reverseGraph))"
    by simp
  then have unfold: "add_reverse_edges v (n # rest) reverseGraph =
                     fmupd n (v # (case fmlookup (add_reverse_edges v rest reverseGraph) n of None \<Rightarrow> [] | Some l \<Rightarrow> l))
                           (add_reverse_edges v rest reverseGraph)"
    by (simp add: Let_def)

  show ?case
  proof (cases "w = n")
    case True
    then show ?thesis by (simp add: member_rec(1))
  next
    case False
    then have "has_vertex (add_reverse_edges v rest reverseGraph) w"
      using Cons.prems unfold by auto
    then have "has_vertex reverseGraph w \<or> List.member rest w"
      using Cons.IH by simp
    then show ?thesis
      by (auto simp: member_rec(1))
  qed
qed

(* Lemma: add_reverse_edges only adds edges, never removes them *)
lemma add_reverse_edges_adds_edges:
  fixes x :: "'a::linorder"
  assumes "has_edge reverseGraph x y"
  shows "has_edge (add_reverse_edges v neighbors reverseGraph) x y"
  using assms
proof (induction neighbors arbitrary: reverseGraph)
  case Nil
  then show ?case by simp

next
  case (Cons w rest)

  define func :: "'a \<Rightarrow> 'a Graph \<Rightarrow> 'a Graph" where 
    "func = (\<lambda>w g'.
       let old_list = (case fmlookup g' w of None \<Rightarrow> [] | Some l \<Rightarrow> l)
       in fmupd w (v # old_list) g')"

  have 1: "add_reverse_edges v (w # rest) reverseGraph =
          foldr func (w # rest) reverseGraph" using func_def by simp

  have 2: "... = func w (foldr func rest reverseGraph)"
    by simp

  have ind_hyp: "has_edge (foldr func rest reverseGraph) x y"
    using Cons.IH Cons.prems func_def by auto

  have "has_edge (func w (foldr func rest reverseGraph)) x y"
  proof (cases "fmlookup (foldr func rest reverseGraph) w")
    case None
    then show ?thesis
      using ind_hyp func_def
      by auto
  next
    case (Some a)
    show ?thesis
    proof (cases "x = w")
      case True
      (* x = w, so we're updating x's adjacency list by prepending v *)
      have "func w (foldr func rest reverseGraph) =
            fmupd w (v # a) (foldr func rest reverseGraph)"
        using Some func_def by (simp add: Let_def)
      then have "fmlookup (func w (foldr func rest reverseGraph)) x = Some (v # a)"
        using True by simp
      moreover have "List.member a y"
        using ind_hyp Some True by auto
      ultimately show ?thesis
        by (simp add: member_rec(1))
    next
      case False
      (* x \<noteq> w, so x's adjacency list is unchanged *)
      have "func w (foldr func rest reverseGraph) =
            fmupd w (v # a) (foldr func rest reverseGraph)"
        using Some func_def by (simp add: Let_def)
      then have "fmlookup (func w (foldr func rest reverseGraph)) x =
                 fmlookup (foldr func rest reverseGraph) x"
        using False by simp
      then show ?thesis
        using ind_hyp by simp
    qed
  qed

  thus ?case
    using 1 2 by auto
qed

(* Lemma: add_reverse_edges adds the reverse edge for each neighbor *)
lemma add_reverse_edges_creates_reverse:
  assumes "List.member neighbors w"
  shows "has_edge (add_reverse_edges v neighbors reverseGraph) w v"
  using assms
proof (induction neighbors arbitrary: reverseGraph)
  case Nil
  then show ?case
    by (simp add: member_rec(2))
next
  case (Cons u rest)
  show ?case
  proof (cases "u = w")
    case True
    (* w is the first neighbor, so we add edge (w,v) *)
    have "add_reverse_edges v (w # rest) reverseGraph =
          foldr (\<lambda>u g'. let old_list = (case fmlookup g' u of None \<Rightarrow> [] | Some l \<Rightarrow> l)
                        in fmupd u (v # old_list) g') (w # rest) reverseGraph"
      by simp
    also have "... = (let old_list = (case fmlookup (add_reverse_edges v rest reverseGraph) w of None \<Rightarrow> [] | Some l \<Rightarrow> l)
                      in fmupd w (v # old_list) (add_reverse_edges v rest reverseGraph))"
      by simp
    finally have eq: "add_reverse_edges v (w # rest) reverseGraph =
                      fmupd w (v # (case fmlookup (add_reverse_edges v rest reverseGraph) w of None \<Rightarrow> [] | Some l \<Rightarrow> l))
                            (add_reverse_edges v rest reverseGraph)"
      by (simp add: Let_def)

    have "fmlookup (add_reverse_edges v (w # rest) reverseGraph) w =
          Some (v # (case fmlookup (add_reverse_edges v rest reverseGraph) w of None \<Rightarrow> [] | Some l \<Rightarrow> l))"
      using eq by simp
    then show ?thesis
      using True by (auto simp: member_rec(1))
  next
    case False
    (* w is somewhere in rest *)
    then have "List.member rest w"
      using Cons.prems by (simp add: member_rec(1))
    then have "has_edge (add_reverse_edges v rest reverseGraph) w v"
      using Cons.IH by simp
    moreover have "add_reverse_edges v (u # rest) reverseGraph =
                   (let old_list = (case fmlookup (add_reverse_edges v rest reverseGraph) u of None \<Rightarrow> [] | Some l \<Rightarrow> l)
                    in fmupd u (v # old_list) (add_reverse_edges v rest reverseGraph))"
      by simp
    ultimately show ?thesis
      using False add_reverse_edges_adds_edges by (auto simp: Let_def)
  qed
qed

(* Lemma: Edges in result of add_reverse_edges either came from reverseGraph
   or were added as reverse edges *)
lemma add_reverse_edges_origin:
  assumes "has_edge (add_reverse_edges v neighbors reverseGraph) w u"
  shows "has_edge reverseGraph w u \<or> (u = v \<and> List.member neighbors w)"
  using assms
proof (induction neighbors arbitrary: reverseGraph)
  case Nil
  then show ?case by simp
next
  case (Cons n rest)

  (* After processing n, we have processed rest first *)
  define g' where "g' = add_reverse_edges v rest reverseGraph"

  (* Then we update n's adjacency list *)
  have "add_reverse_edges v (n # rest) reverseGraph =
        (let old_list = (case fmlookup g' n of None \<Rightarrow> [] | Some l \<Rightarrow> l)
         in fmupd n (v # old_list) g')"
    unfolding g'_def by simp

  then have result_def: "add_reverse_edges v (n # rest) reverseGraph =
                         fmupd n (v # (case fmlookup g' n of None \<Rightarrow> [] | Some l \<Rightarrow> l)) g'"
    by (simp add: Let_def)

  (* Now analyze where edge (w,u) came from *)
  show ?case
  proof (cases "w = n")
    case True
    (* w = n, so we updated w's adjacency list *)
    have "fmlookup (add_reverse_edges v (n # rest) reverseGraph) w =
          Some (v # (case fmlookup g' w of None \<Rightarrow> [] | Some l \<Rightarrow> l))"
      using result_def True by simp

    then have "List.member (v # (case fmlookup g' w of None \<Rightarrow> [] | Some l \<Rightarrow> l)) u"
      using Cons.prems by (auto split: option.splits)

    then show ?thesis
    proof (cases "u = v")
      case True
      then show ?thesis using `w = n` by (simp add: member_rec(1))
    next
      case False
      (* u is in the old list *)
      then have "List.member (case fmlookup g' w of None \<Rightarrow> [] | Some l \<Rightarrow> l) u"
        using `List.member (v # (case fmlookup g' w of None \<Rightarrow> [] | Some l \<Rightarrow> l)) u`
        by (simp add: member_rec(1))
      then have "has_edge g' w u"
        by (metis has_edge.elims(1) member_rec(2) option.case_eq_if)
      then have "has_edge reverseGraph w u \<or> (u = v \<and> List.member rest w)"
        using Cons.IH unfolding g'_def by simp
      then show ?thesis
        using `w = n` by (auto simp: member_rec(1))
    qed
  next
    case False
    (* w \<noteq> n, so w's adjacency list is unchanged from g' *)
    have "fmlookup (add_reverse_edges v (n # rest) reverseGraph) w = fmlookup g' w"
      using result_def False by simp
    then have "has_edge g' w u"
      using Cons.prems by simp
    then have "has_edge reverseGraph w u \<or> (u = v \<and> List.member rest w)"
      using Cons.IH unfolding g'_def by simp
    then show ?thesis
      by (auto simp: member_rec(1))
  qed
qed

(* Helper function 2 *)
(* Given the original graph and a vertex, add all reverse edges of that vertex
   to the reverseGraph. Note the given vertex must be in the graph. *)
fun transpose_step :: "('a::linorder) Graph \<Rightarrow> 'a \<Rightarrow> ('a::linorder) Graph 
                          \<Rightarrow> ('a::linorder) Graph" where
  "transpose_step graph v reverseGraph =
    add_reverse_edges v (the (fmlookup graph v)) reverseGraph"

(* Lemma: transpose_step preserves existing vertices *)
lemma transpose_step_preserves_vertices:
  assumes "has_vertex reverseGraph w"
  shows "has_vertex (transpose_step graph v reverseGraph) w"
  using assms add_reverse_edges_preserves_vertices by simp

(* Lemma: foldr transpose_step preserves existing vertices *)
lemma foldr_transpose_step_preserves_vertices:
  assumes "has_vertex reverseGraph w"
  shows "has_vertex (foldr (transpose_step graph) vertices reverseGraph) w"
  using assms
proof (induction vertices arbitrary: reverseGraph)
  case Nil
  then show ?case by simp
next
  case (Cons v rest)
  have "has_vertex (foldr (transpose_step graph) rest reverseGraph) w"
    using Cons.IH Cons.prems
    by blast 
  then show ?case
    using transpose_step_preserves_vertices
    by (metis (mono_tags, lifting) comp_apply foldr_Cons) 
qed

(* Lemma: transpose_step adds vertices for each neighbor of v *)
lemma transpose_step_adds_neighbor_vertices:
  assumes "has_vertex graph v"
    and "has_edge graph v w"
  shows "has_vertex (transpose_step graph v reverseGraph) w"
  using assms add_reverse_edges_adds_neighbor_vertices has_edge_member_conv
  by (metis transpose_step.simps)

(* Lemma: foldr transpose_step adds vertices for neighbors in the graph *)
lemma foldr_transpose_step_adds_neighbor_vertices:
  assumes "has_edge graph v w"
    and "List.member vertices v"
    and "\<forall>u. List.member vertices u \<longrightarrow> has_vertex graph u"
  shows "has_vertex (foldr (transpose_step graph) vertices reverseGraph) w"
  using assms
proof (induction vertices arbitrary: reverseGraph)
  case Nil
  then show ?case by (simp add: member_rec(2))
next
  case (Cons u rest)
  show ?case
  proof (cases "u = v")
    case True
    (* v is first, so transpose_step adds w as a vertex *)
    have "has_vertex graph v"
      using Cons.prems(3)
      by (simp add: Cons.prems(2)) 
    then have "has_vertex (transpose_step graph v reverseGraph) w"
      using transpose_step_adds_neighbor_vertices Cons.prems(1) by simp
    then show ?thesis
      using True 
      by (metis (mono_tags, lifting) \<open>has_vertex graph v\<close> assms(1) comp_apply
          foldr_Cons transpose_step_adds_neighbor_vertices) 
  next
    case False
    (* v is in rest *)
    then have "List.member rest v"
      using Cons.prems(2) by (simp add: member_rec(1))
    have "\<forall>x. List.member rest x \<longrightarrow> has_vertex graph x"
      using Cons.prems(3) by (simp add: member_rec(1))
    then have "has_vertex (foldr (transpose_step graph) rest reverseGraph) w"
      using Cons.IH[OF Cons.prems(1) \<open>List.member rest v\<close>]
      by blast 
    then show ?thesis
      using transpose_step_preserves_vertices
      by (metis (mono_tags, lifting) comp_apply foldr_Cons) 
  qed
qed

(* Lemma: transpose_step only adds vertices that are neighbors of v *)
lemma transpose_step_vertices_only_from_neighbors:
  assumes "has_vertex graph v"
    and "has_vertex (transpose_step graph v reverseGraph) w"
  shows "has_vertex reverseGraph w \<or> has_edge graph v w"
  using assms add_reverse_edges_vertices_only_from_neighbors has_edge_member_conv
  by (metis transpose_step.simps)

(* Lemma: foldr transpose_step only adds vertices that are in the graph *)
lemma foldr_transpose_step_vertices_only_from_graph:
  assumes "has_vertex (foldr (transpose_step graph) vertices reverseGraph) w"
    and "\<forall>v. List.member vertices v \<longrightarrow> has_vertex graph v"
    and "valid_graph graph"
  shows "has_vertex reverseGraph w \<or> has_vertex graph w"
  using assms
proof (induction vertices arbitrary: reverseGraph)
  case Nil
  then show ?case by simp
next
  case (Cons v rest)
  have v_in_graph: "has_vertex graph v"
    using Cons.prems(2) by (simp add: member_rec(1))

  have rest_valid: "\<forall>u. List.member rest u \<longrightarrow> has_vertex graph u"
    using Cons.prems(2) by (simp add: member_rec(1))

  (* Unfold the foldr *)
  have "foldr (transpose_step graph) (v # rest) reverseGraph =
        transpose_step graph v (foldr (transpose_step graph) rest reverseGraph)"
    by simp

  then have "has_vertex (transpose_step graph v (foldr (transpose_step graph) rest reverseGraph)) w"
    using Cons.prems(1)
    by presburger 

  (* Apply transpose_step_vertices_only_from_neighbors *)
  then have "has_vertex (foldr (transpose_step graph) rest reverseGraph) w \<or> has_edge graph v w"
    using transpose_step_vertices_only_from_neighbors[OF v_in_graph] by simp

  then show ?case
  proof
    assume "has_vertex (foldr (transpose_step graph) rest reverseGraph) w"
    then have "has_vertex reverseGraph w \<or> has_vertex graph w"
      using Cons.IH[OF _ rest_valid Cons.prems(3)]
      by blast 
    then show ?thesis by simp
  next
    assume "has_edge graph v w"
    then have "has_vertex graph w"
      using Cons.prems(3) v_in_graph by (meson valid_graph.elims(2))
    then show ?thesis by simp
  qed
qed

(* Lemma: transpose_step only adds new edges to the reverseGraph,
   never removes them *)
lemma transpose_step_adds_edges:
  assumes "has_edge reverseGraph x y"
  shows "has_edge (transpose_step graph v reverseGraph) x y"
  using assms add_reverse_edges_adds_edges by simp

(* Lemma: If (v,w) in graph, then transpose_step graph v adds
   (w,v) to reverseGraph *)
lemma transpose_step_creates_reverse:
  assumes "has_edge graph v w"
  shows "has_edge (transpose_step graph v reverseGraph) w v"
  using assms add_reverse_edges_creates_reverse
  by (metis has_edge.elims(1) option.case_eq_if
      transpose_step.simps)

(* Lemma: If (v,w) in graph, and v in vertices, then folding transpose_step
   over vertices adds (w,v) to reverseGraph *)
lemma foldr_transpose_step_creates_reverse:
  assumes "has_edge graph v w"
    and "List.member vertices v"
  shows "has_edge (foldr (transpose_step graph) vertices reverseGraph) w v"
  using assms
proof (induction vertices arbitrary: reverseGraph)
  case Nil
  then show ?case using assms(2)
    by (simp add: member_rec(2)) 
next
  case (Cons u rest)

  show ?case
  proof (cases "u = v")
    case True
    (* v is the first vertex, so transpose_step creates the edge (w,v) *)
    have "has_edge (transpose_step graph v reverseGraph) w v"
      using transpose_step_creates_reverse[OF Cons.prems(1)] by simp
    thus ?thesis
      using True transpose_step_creates_reverse assms(1) by simp
  next
    case False
    (* v is somewhere in rest *)
    then have "List.member rest v"
      using Cons.prems(2) by (simp add: member_rec(1))
    then have "has_edge (foldr (transpose_step graph) rest reverseGraph) w v"
      using Cons.IH
      using assms(1) by blast 
    then show ?thesis
      by (metis (mono_tags, lifting) comp_apply foldr_Cons transpose_step_adds_edges) 
  qed
qed

(* Lemma: Edges in result of transpose_step either came from reverseGraph
   or were added as reverse edges *)
lemma transpose_step_origin:
  assumes "has_vertex graph v"
    and "has_edge (transpose_step graph v reverseGraph) w u"
  shows "has_edge reverseGraph w u \<or> (has_edge graph v w \<and> u = v)"
proof -
  have "has_edge (add_reverse_edges v (the (fmlookup graph v)) reverseGraph) w u"
    using assms(2) by simp
  then have "has_edge reverseGraph w u \<or> (u = v \<and> List.member (the (fmlookup graph v)) w)"
    using add_reverse_edges_origin by blast
  then show ?thesis
    using has_edge_member_conv[OF assms(1)] by auto
qed

(* Lemma: Edges in result of foldr transpose_step either came from reverseGraph
   or were created by processing some vertex in the list *)
lemma foldr_transpose_step_origin:
  assumes "has_edge (foldr (transpose_step graph) vertices reverseGraph) w u"
    and "\<forall>v. List.member vertices v \<longrightarrow> has_vertex graph v"
  shows "has_edge reverseGraph w u \<or> (List.member vertices u \<and> has_edge graph u w)"
  using assms
proof (induction vertices arbitrary: reverseGraph)
  case Nil
  then show ?case by simp
next
  case (Cons v rest)

  (* foldr processes right to left: foldr f (v # rest) acc = f v (foldr f rest acc) *)
  have unfold: "foldr (transpose_step graph) (v # rest) reverseGraph =
        transpose_step graph v (foldr (transpose_step graph) rest reverseGraph)"
    by simp

  (* Apply IH to the result of processing rest first *)
  define g' where "g' = foldr (transpose_step graph) rest reverseGraph"

  have "\<forall>x. List.member rest x \<longrightarrow> has_vertex graph x"
    using Cons.prems(2) by (simp add: member_rec(1))

  (* The edge is in transpose_step graph v g' *)
  have "has_edge (transpose_step graph v g') w u"
    using Cons.prems(1) g'_def unfold by argo

  (* Use transpose_step_origin *)
  have "has_vertex graph v"
    using Cons.prems(2) by (simp add: member_rec(1))

  then have "has_edge g' w u \<or> (has_edge graph v w \<and> u = v)"
    using transpose_step_origin[OF _ `has_edge (transpose_step graph v g') w u`] by simp

  then show ?case
  proof
    assume "has_edge g' w u"
    (* Apply IH to g' *)
    then have "has_edge reverseGraph w u \<or> (List.member rest u \<and> has_edge graph u w)"
      using Cons.IH[OF _ `\<forall>x. List.member rest x \<longrightarrow> has_vertex graph x`] g'_def
      by blast
    then show ?thesis
      by (auto simp: member_rec(1))
  next
    assume "has_edge graph v w \<and> u = v"
    then show ?thesis
      by (auto simp: member_rec(1))
  qed
qed

(* Helper function 3 *)
(* Initialize a graph with all vertices but no edges *)
fun init_empty_graph :: "'a::linorder list \<Rightarrow> 'a Graph" where
  "init_empty_graph vertices = foldr (\<lambda>v g. fmupd v [] g) vertices fmempty"

(* Lemma: init_empty_graph has exactly the vertices in the list *)
lemma init_empty_graph_vertices:
  "has_vertex (init_empty_graph vertices) v \<longleftrightarrow> List.member vertices v"
proof (induction vertices)
  case Nil
  then show ?case
    by (simp add: member_rec(2)) 
next
  case (Cons u rest)
  have "init_empty_graph (u # rest) = fmupd u [] (init_empty_graph rest)"
    by simp
  then show ?case
    using Cons.IH by (auto simp: member_rec(1))
qed

(* Lemma: init_empty_graph has no edges *)
lemma init_empty_graph_no_edges:
  "\<not> has_edge (init_empty_graph vertices) v w"
proof (induction vertices)
  case Nil
  then show ?case by simp
next
  case (Cons u rest)
  have "init_empty_graph (u # rest) = fmupd u [] (init_empty_graph rest)"
    by simp
  then show ?case
    using Cons.IH by (auto simp: member_rec(2))
qed

(* Main function to transpose a graph *)
fun transpose_graph :: "(('a::linorder, 'a list) fmap) \<Rightarrow> (('a, 'a list) fmap)" where
  "transpose_graph graph =
    (let vertices = sorted_list_of_fset (fmdom graph) in
     foldr (transpose_step graph) vertices (init_empty_graph vertices))"

(* Lemma: Transposed graph has the same vertices as the original *)
lemma transpose_same_vertices:
  assumes "valid_graph graph"
  shows "\<forall>v. has_vertex graph v \<longleftrightarrow> has_vertex (transpose_graph graph) v"
proof
  fix v
  show "has_vertex graph v \<longleftrightarrow> has_vertex (transpose_graph graph) v"
  proof
    (* Forward direction: graph v \<rightarrow> transpose_graph v *)
    assume "has_vertex graph v"
    then have "v |\<in>| fmdom graph" by simp
    then have v_in_list: "List.member (sorted_list_of_fset (fmdom graph)) v"
      by (simp add: member_def)

    define vertices where "vertices = sorted_list_of_fset (fmdom graph)"
    have "transpose_graph graph = foldr (transpose_step graph) vertices (init_empty_graph vertices)"
      unfolding vertices_def by (simp add: Let_def)

    (* init_empty_graph has v *)
    have "has_vertex (init_empty_graph vertices) v"
      using v_in_list init_empty_graph_vertices vertices_def
      by blast 

    (* foldr preserves v *)
    then have "has_vertex (foldr (transpose_step graph) vertices (init_empty_graph vertices)) v"
      using foldr_transpose_step_preserves_vertices by simp

    then show "has_vertex (transpose_graph graph) v"
      using \<open>transpose_graph graph = foldr (transpose_step graph) vertices (init_empty_graph vertices)\<close>
      by simp

  next
    (* Reverse direction: transpose_graph v \<rightarrow> graph v *)
    assume "has_vertex (transpose_graph graph) v"

    define vertices where "vertices = sorted_list_of_fset (fmdom graph)"
    have "transpose_graph graph = foldr (transpose_step graph) vertices (init_empty_graph vertices)"
      unfolding vertices_def by (simp add: Let_def)

    then have "has_vertex (foldr (transpose_step graph) vertices (init_empty_graph vertices)) v"
      using \<open>has_vertex (transpose_graph graph) v\<close> by simp

    (* All vertices in the list are valid vertices in graph *)
    have "\<forall>u. List.member vertices u \<longrightarrow> has_vertex graph u"
      unfolding vertices_def by (simp add: member_def)

    (* Apply foldr_transpose_step_vertices_only_from_graph *)
    then have "has_vertex (init_empty_graph vertices) v \<or> has_vertex graph v"
      using foldr_transpose_step_vertices_only_from_graph[OF \<open>has_vertex (foldr (transpose_step graph) vertices (init_empty_graph vertices)) v\<close> _ assms]
      by simp

    then show "has_vertex graph v"
    proof
      assume "has_vertex (init_empty_graph vertices) v"
      then have "List.member vertices v"
        using init_empty_graph_vertices
        by auto 
      then show "has_vertex graph v"
        unfolding vertices_def by (simp add: member_def)
    next
      assume "has_vertex graph v"
      then show "has_vertex graph v" by simp
    qed
  qed
qed

(* Lemma: Edges in transposed graph are exactly the "backward" edges in the original graph *)
lemma transpose_edge_correspondence:
  assumes "valid_graph graph"
  shows "has_edge graph v w \<longleftrightarrow> has_edge (transpose_graph graph) w v"
proof
  (* Forward implication *)
  assume edge_vw: "has_edge graph v w"

  (* v must be in the graph's domain *)
  have "v |\<in>| fmdom graph"
    using edge_vw fmdom_notD by fastforce

  (* v is in the sorted list of vertices *)
  then have "List.member (sorted_list_of_fset (fmdom graph)) v"
    by (simp add: member_def)

  (* Apply the foldr lemma *)
  then show "has_edge (transpose_graph graph) w v"
    using foldr_transpose_step_creates_reverse
    by (metis Graphs.transpose_graph.simps edge_vw)

next
  (* Reverse implication *)
  assume "has_edge (transpose_graph graph) w v"

  (* Unfold transpose_graph definition *)
  define vertices where "vertices = sorted_list_of_fset (fmdom graph)"
  then have "has_edge (foldr (transpose_step graph) vertices (init_empty_graph vertices)) w v"
    using `has_edge (transpose_graph graph) w v` by (simp add: Let_def)

  (* All vertices in the list are valid vertices *)
  have "\<forall>u. List.member vertices u \<longrightarrow> has_vertex graph u"
    unfolding vertices_def by (simp add: member_def)

  (* Apply foldr_transpose_step_origin *)
  then have "has_edge (init_empty_graph vertices) w v \<or> (List.member vertices v \<and> has_edge graph v w)"
    using foldr_transpose_step_origin[OF `has_edge (foldr (transpose_step graph) vertices (init_empty_graph vertices)) w v`]
    by simp

  (* init_empty_graph has no edges *)
  moreover have "\<not> has_edge (init_empty_graph vertices) w v"
    using init_empty_graph_no_edges by simp

  ultimately show "has_edge graph v w"
    by simp
qed

(* Lemma: Transposing a valid graph produces a valid graph *)
lemma transpose_valid:
  assumes "valid_graph graph"
  shows "valid_graph (transpose_graph graph)"
proof -
  have "\<forall>v. has_vertex (transpose_graph graph) v \<longrightarrow>
           (\<forall>w. has_edge (transpose_graph graph) v w \<longrightarrow>
            has_vertex (transpose_graph graph) w)"
  proof (intro allI impI)
    fix v w
    assume "has_vertex (transpose_graph graph) v"
    assume "has_edge (transpose_graph graph) v w"

    (* By transpose_edge_correspondence, has_edge (transpose_graph graph) v w
       means has_edge graph w v *)
    then have "has_edge graph w v"
      using transpose_edge_correspondence[OF assms] by simp

    (* Since graph is valid and w has an edge to v, w must be a vertex *)
    then have "has_vertex graph w"
      using fmdom_notD by fastforce
      
    (* By transpose_same_vertices, w is also in the transposed graph *)
    then show "has_vertex (transpose_graph graph) w"
      using transpose_same_vertices[OF assms] by simp
  qed

  then show ?thesis by simp
qed

(* Double transpose has the same edges as the original *)
lemma transpose_double_edges:
  assumes "valid_graph graph"
  shows "has_edge (transpose_graph (transpose_graph graph)) v w \<longleftrightarrow> has_edge graph v w"
  using assms transpose_edge_correspondence transpose_valid by blast

(* Reachability in transposed graph means reverse reachability in original *)
lemma transpose_reachability:
  assumes "valid_graph graph"
  assumes "transposed = transpose_graph graph"
  assumes "reachable transposed v w"
  shows "reachable graph w v"
  using assms(3)
proof (induction rule: reachable.induct)
  case (reachable_refl v)
  (* v is a vertex in transposed, so it's a vertex in graph by transpose_same_vertices *)
  have "has_vertex graph v"
    using reachable_refl.hyps assms(1) assms(2) transpose_same_vertices by metis
  then show ?case
    using reachable.reachable_refl by simp
next
  case (reachable_step v u w)
  (* We have: reachable transposed v u and has_edge transposed u w *)
  (* IH gives us: reachable graph u v *)
  (* We need to show: reachable graph w v *)

  (* has_edge transposed u w means has_edge graph w u by transpose_edge_correspondence *)
  have "has_edge graph w u"
    using reachable_step assms(1) assms(2) transpose_edge_correspondence by metis

  (* Now we can build the path: w \<rightarrow> u \<rightarrow>* v *)
  (* First, get a single-step reachability w \<rightarrow> u *)
  have "has_vertex graph w"
    using \<open>has_edge graph w u\<close> assms(1)
    by (metis fmdom_notD has_edge.elims(1) has_vertex.simps
        option.case_eq_if)
  then have "reachable graph w w"
    using reachable.reachable_refl by simp
  then have "reachable graph w u"
    using reachable.reachable_step \<open>has_edge graph w u\<close>
    by blast

  (* Now use transitivity: w \<rightarrow>* u and u \<rightarrow>* v gives w \<rightarrow>* v *)
  have "reachable graph u v"
    using reachable_step.IH by simp
  then show ?case
    using reachable_trans[OF \<open>reachable graph w u\<close>] by simp
qed

(* Conversely, reachability in original means reachability in transposed graph *)
lemma transpose_reachability_converse:
  assumes "valid_graph graph"
  assumes "transposed = transpose_graph graph"
  assumes "reachable graph v w"
  shows "reachable transposed w v"
  using assms(3)
proof (induction rule: reachable.induct)
  case (reachable_refl v)
  (* v is a vertex in graph, so it's a vertex in transposed by transpose_same_vertices *)
  have "has_vertex transposed v"
    using reachable_refl.hyps assms(1) assms(2) transpose_same_vertices by metis
  then show ?case
    using reachable.reachable_refl by simp
next
  case (reachable_step v u w)
  (* We have: reachable graph v u and has_edge graph u w *)
  (* IH gives us: reachable transposed u v *)
  (* We need to show: reachable transposed w v *)

  (* has_edge graph u w means has_edge transposed w u by transpose_edge_correspondence *)
  have "has_edge transposed w u"
    using reachable_step assms(1) assms(2) transpose_edge_correspondence by metis

  (* Now we can build the path: w \<rightarrow> u \<rightarrow>* v in transposed *)
  (* First, get a single-step reachability w \<rightarrow> u in transposed *)
  have "has_vertex transposed w"
    using \<open>has_edge transposed w u\<close>
    by (metis fmdom_notD has_edge.elims(1) has_vertex.simps
        option.case_eq_if)
  then have "reachable transposed w w"
    using reachable.reachable_refl by simp
  then have "reachable transposed w u"
    using reachable.reachable_step \<open>has_edge transposed w u\<close>
    by blast

  (* Now use transitivity: w \<rightarrow>* u and u \<rightarrow>* v gives w \<rightarrow>* v in transposed *)
  have "reachable transposed u v"
    using reachable_step.IH by simp
  then show ?case
    using reachable_trans[OF \<open>reachable transposed w u\<close>] by simp
qed

(* in_same_scc on the transpose graph is same as original graph *)
lemma transpose_same_scc:
  assumes "valid_graph graph"
  assumes "transposed = transpose_graph graph"
  shows "in_same_scc transposed u v \<longleftrightarrow> in_same_scc graph u v"
proof
  assume "in_same_scc transposed u v"
  then have "reachable transposed u v" "reachable transposed v u" by simp_all
  then have "reachable graph v u" "reachable graph u v"
    using transpose_reachability[OF assms(1)] assms(2) by auto
  then show "in_same_scc graph u v" by simp
next
  assume "in_same_scc graph u v"
  then have reach_orig: "reachable graph u v" "reachable graph v u" by simp_all

  (* Use transpose_reachability_converse to show reachability in transposed graph *)
  have "reachable transposed v u"
    using transpose_reachability_converse[OF assms(1) assms(2) reach_orig(1)] by simp
  moreover have "reachable transposed u v"
    using transpose_reachability_converse[OF assms(1) assms(2) reach_orig(2)] by simp
  ultimately show "in_same_scc transposed u v" by simp
qed

end

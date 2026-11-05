theory MiniCMemoryLemmas
  imports "../minic/MiniCMemory"
begin

(* ========================================================================== *)
(* Byte slices, and sub-ranges of memory regions                              *)
(* ========================================================================== *)

(* The lemmas about mem_read / mem_write / mem_load / mem_store on
   sub-ranges that the representation relation (RepVal.thy) needs. Nothing
   here changes the memory model. *)


section \<open>Slices of lists\<close>

(* The n elements from position off. *)
definition slice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "slice off n xs = take n (drop off xs)"

lemma length_slice [simp]: "length (slice off n xs) = min n (length xs - off)"
  by (simp add: slice_def)

lemma length_slice_le: "off + n \<le> length xs \<Longrightarrow> length (slice off n xs) = n"
  by (simp add: slice_def)

lemma slice_all [simp]: "slice 0 (length xs) xs = xs"
  by (simp add: slice_def)

lemma slice_0: "slice 0 n xs = take n xs"
  by (simp add: slice_def)

lemma slice_slice: "off' + n' \<le> n \<Longrightarrow> slice off' n' (slice off n xs) = slice (off + off') n' xs"
  by (simp add: slice_def drop_take add.commute)

lemma slice_nth: "i < n \<Longrightarrow> off + n \<le> length xs \<Longrightarrow> slice off n xs ! i = xs ! (off + i)"
  by (simp add: slice_def)

lemma slice_append_left: "off + n \<le> length xs \<Longrightarrow> slice off n (xs @ ys) = slice off n xs"
  by (simp add: slice_def)

lemma slice_append_right: "length xs \<le> off \<Longrightarrow> slice off n (xs @ ys) = slice (off - length xs) n ys"
  by (simp add: slice_def)

lemma slice_replicate: "off + n \<le> k \<Longrightarrow> slice off n (replicate k x) = replicate n x"
  by (simp add: slice_def)

lemma take_slice: "take k (slice off n xs) = slice off (min k n) xs"
  by (simp add: slice_def)

lemma slice_map: "slice off n (map f xs) = map f (slice off n xs)"
  by (simp add: slice_def take_map drop_map)

(* Replacing the elements from position off by new. *)
definition splice :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "splice off new xs = take off xs @ new @ drop (off + length new) xs"

lemma length_splice: "off + length new \<le> length xs \<Longrightarrow> length (splice off new xs) = length xs"
  by (simp add: splice_def)

lemma slice_splice_same:
  "off + length new \<le> length xs \<Longrightarrow> slice off (length new) (splice off new xs) = new"
  by (simp add: splice_def slice_def)

(* A slice disjoint from the replaced range is unchanged. *)
lemma slice_splice_before:
  assumes "off' + n' \<le> off" and "off \<le> length xs"
  shows "slice off' n' (splice off new xs) = slice off' n' xs"
proof -
  have lenA: "length (take off xs) = off" using assms(2) by simp
  have "drop off' (splice off new xs) = drop off' (take off xs) @ new @ drop (off + length new) xs"
    unfolding splice_def using assms(1) lenA by simp
  hence "take n' (drop off' (splice off new xs)) = take n' (drop off' (take off xs))"
    using assms(1) lenA by simp
  also have "\<dots> = take n' (drop off' xs)"
    using assms(1) by (simp add: drop_take min_def)
  finally show ?thesis by (simp add: slice_def)
qed

lemma slice_splice_after:
  "off + length new \<le> off' \<Longrightarrow> off + length new \<le> length xs
   \<Longrightarrow> slice off' n' (splice off new xs) = slice off' n' xs"
proof -
  assume a: "off + length new \<le> off'" and b: "off + length new \<le> length xs"
  have "drop off' (splice off new xs) = drop off' xs"
    unfolding splice_def using a b by simp
  thus ?thesis by (simp add: slice_def)
qed

lemma slice_splice_disjoint:
  "off' + n' \<le> off \<or> off + length new \<le> off' \<Longrightarrow> off + length new \<le> length xs
   \<Longrightarrow> slice off' n' (splice off new xs) = slice off' n' xs"
  using slice_splice_before[of off' n' off xs new] slice_splice_after[of off new off' xs n'] by auto

lemma take_splice_before: "k \<le> off \<Longrightarrow> off \<le> length xs \<Longrightarrow> take k (splice off new xs) = take k xs"
  by (simp add: splice_def min_def)

(* A slice that contains the replaced range is the slice with the range
   replaced. *)
lemma slice_splice_inside:
  assumes "off' \<le> off" and "off + length new \<le> off' + n'" and "off' + n' \<le> length xs"
  shows "slice off' n' (splice off new xs) = splice (off - off') new (slice off' n' xs)"
proof -
  let ?A = "take off xs" and ?C = "drop (off + length new) xs" and ?S = "slice off' n' xs"
  have le: "off \<le> length xs" using assms by simp
  have lenA: "length ?A = off" using le by simp
  have 1: "drop off' (splice off new xs) = drop off' ?A @ new @ ?C"
    unfolding splice_def using assms(1) lenA by simp
  have 2: "take n' (drop off' ?A @ new @ ?C) = drop off' ?A @ new @ take (n' - (off - off') - length new) ?C"
    using assms lenA by simp
  have 3: "drop off' ?A = take (off - off') ?S"
    unfolding slice_def using assms by (simp add: drop_take min_def)
  have 4: "take (n' - (off - off') - length new) ?C = drop (off - off' + length new) ?S"
    unfolding slice_def using assms by (simp add: drop_take)
  show ?thesis
    unfolding slice_def[of off' n' "splice off new xs"] 1
    unfolding 2
    unfolding 3 4 splice_def[of "off - off'"] ..
qed

(* Splicing the whole list. *)
lemma splice_all: "length new = length xs \<Longrightarrow> splice 0 new xs = new"
  by (simp add: splice_def)


section \<open>Pointers and offsets\<close>

(* The pointer off bytes further on (null stays null). *)
fun ptr_off :: "MPtr \<Rightarrow> nat \<Rightarrow> MPtr" where
  "ptr_off MP_Null off = MP_Null"
| "ptr_off (MP_Addr b ofs) off = MP_Addr b (ofs + off)"

lemma ptr_off_0 [simp]: "ptr_off p 0 = p"
  by (cases p) simp_all

lemma ptr_off_add: "ptr_off (ptr_off p a) b = ptr_off p (a + b)"
  by (cases p) (simp_all add: add.assoc)

(* Reading a sub-range of a readable range. *)
lemma mem_read_sub:
  assumes "mem_read m p n = Some bs" and "off + n' \<le> n"
  shows "mem_read m (ptr_off p off) n' = Some (slice off n' bs)"
proof -
  from assms(1) obtain b ofs data where p: "p = MP_Addr b ofs" and lk: "fmlookup (MM_Blocks m) b = Some data"
    and le: "ofs + n \<le> length data" and bs: "bs = take n (drop ofs data)"
    by (auto simp: mem_read_def split: MPtr.splits option.splits if_splits)
  have "take n' (drop (ofs + off) data) = slice off n' bs"
    unfolding bs slice_def using assms(2) by (simp add: drop_take add.commute)
  with p lk le assms(2) show ?thesis by (simp add: mem_read_def)
qed

(* The bytes of a block. *)
lemma mem_read_block:
  assumes "fmlookup (MM_Blocks m) b = Some data" and "off + n \<le> length data"
  shows "mem_read m (MP_Addr b off) n = Some (slice off n data)"
  using assms by (simp add: mem_read_def slice_def)

lemma mem_read_Some_block:
  assumes "mem_read m p n = Some bs"
  shows "\<exists>b off data. p = MP_Addr b off \<and> fmlookup (MM_Blocks m) b = Some data
         \<and> off + n \<le> length data \<and> bs = slice off n data"
  using assms by (auto simp: mem_read_def slice_def split: MPtr.splits option.splits if_splits)

lemma mem_read_ptr_range_ok:
  "mem_read m p n = Some bs \<Longrightarrow> ptr_range_ok m p n"
  by (auto simp: mem_read_def ptr_range_ok_def split: MPtr.splits option.splits if_splits)

lemma ptr_range_ok_read:
  "ptr_range_ok m p n \<Longrightarrow> \<exists>bs. mem_read m p n = Some bs"
  by (auto simp: mem_read_def ptr_range_ok_def split: MPtr.splits option.splits)

(* Pointer arithmetic inside a readable range stays defined. *)
lemma ptr_add_off:
  assumes "mem_read m p n = Some bs" and "off \<le> n"
  shows "ptr_add m p (int off) = Some (ptr_off p off)"
proof -
  from assms(1) obtain b ofs data where p: "p = MP_Addr b ofs" and lk: "fmlookup (MM_Blocks m) b = Some data"
    and le: "ofs + n \<le> length data"
    by (auto simp: mem_read_def split: MPtr.splits option.splits if_splits)
  with assms(2) show ?thesis by (simp add: ptr_add_def)
qed

(* Writing a sub-range of a readable range. *)
lemma mem_write_sub:
  assumes "mem_read m p n = Some bs" and "off + length new \<le> n"
  shows "\<exists>m'. mem_write m (ptr_off p off) new = Some m'"
proof -
  from assms(1) obtain b ofs data where p: "p = MP_Addr b ofs" and lk: "fmlookup (MM_Blocks m) b = Some data"
    and le: "ofs + n \<le> length data"
    by (auto simp: mem_read_def split: MPtr.splits option.splits if_splits)
  with assms(2) show ?thesis by (simp add: mem_write_def)
qed

(* After a write inside a range, the range reads back with the sub-range
   replaced. *)
lemma mem_read_after_write_sub:
  assumes "mem_read m p n = Some bs" and "off + length new \<le> n"
    and "mem_write m (ptr_off p off) new = Some m'"
  shows "mem_read m' p n = Some (splice off new bs)"
proof -
  from assms(1) obtain b ofs data where p: "p = MP_Addr b ofs" and lk: "fmlookup (MM_Blocks m) b = Some data"
    and le: "ofs + n \<le> length data" and bs: "bs = take n (drop ofs data)"
    by (auto simp: mem_read_def split: MPtr.splits option.splits if_splits)
  have lk': "fmlookup (MM_Blocks m') b = Some (take (ofs + off) data @ new @ drop (ofs + off + length new) data)"
    using mem_write_lookup_same[OF assms(3)[unfolded p ptr_off.simps]] lk by simp
  have len: "length (take (ofs + off) data @ new @ drop (ofs + off + length new) data) = length data"
    using le assms(2) by simp
  let ?D = "drop ofs data"
  have lenA: "length (take (ofs + off) data) = ofs + off" using le assms(2) by simp
  have 1: "drop ofs (take (ofs + off) data @ new @ drop (ofs + off + length new) data)
           = take off ?D @ new @ drop (off + length new) ?D"
    using lenA by (simp add: drop_take ac_simps)
  have 2: "take n (take off ?D @ new @ drop (off + length new) ?D)
           = take off ?D @ new @ take (n - off - length new) (drop (off + length new) ?D)"
    using le assms(2) by simp
  have 3: "take off ?D = take off bs" unfolding bs using assms(2) by simp
  have 4: "take (n - off - length new) (drop (off + length new) ?D) = drop (off + length new) bs"
    unfolding bs by (simp add: drop_take)
  have "take n (drop ofs (take (ofs + off) data @ new @ drop (ofs + off + length new) data)) = splice off new bs"
    unfolding 1
    unfolding 2
    unfolding 3 4 splice_def ..
  with lk' len le p show ?thesis by (simp add: mem_read_def)
qed

(* A write to one block leaves the reads of every other block unchanged. *)
lemma mem_read_write_other_block:
  assumes "mem_write m (MP_Addr b off) new = Some m'" and "b' \<noteq> b"
  shows "mem_read m' (MP_Addr b' ofs) n = mem_read m (MP_Addr b' ofs) n"
  using mem_write_lookup_other[OF assms] by (simp add: mem_read_def)

lemma mem_write_block_live:
  assumes "mem_write m p new = Some m'"
  shows "fmlookup (MM_Blocks m') b = None \<longleftrightarrow> fmlookup (MM_Blocks m) b = None"
  using assms by (auto simp: mem_write_def split: MPtr.splits option.splits if_splits)

lemma mem_write_dom:
  assumes "mem_write m p new = Some m'"
  shows "fmdom (MM_Blocks m') = fmdom (MM_Blocks m)"
  using assms by (auto simp: mem_write_def split: MPtr.splits option.splits if_splits)
     (metis fmdomI)

(* The block of a write, before and after: same length. *)
lemma mem_write_block_length:
  assumes "mem_write m (MP_Addr b off) new = Some m'"
    and "fmlookup (MM_Blocks m) b = Some data"
  shows "\<exists>data'. fmlookup (MM_Blocks m') b = Some data' \<and> length data' = length data
         \<and> data' = splice off new data"
  using mem_write_lookup_same[OF assms(1)] assms by (auto simp: mem_write_def splice_def split: if_splits)


section \<open>Loads and stores\<close>

lemma mem_load_of_read:
  assumes "mem_read m p (ty_width enc ty) = Some bs" and "decode_val enc ty bs = Some v"
  shows "mem_load enc m ty p = Some v"
  using assms by (simp add: mem_load_def)

lemma mem_load_read:
  assumes "mem_load enc m ty p = Some v"
  shows "\<exists>bs. mem_read m p (ty_width enc ty) = Some bs \<and> decode_val enc ty bs = Some v"
  using assms by (auto simp: mem_load_def split: option.splits)

lemma mem_store_of_read:
  assumes "valid_encoding enc" and "mem_read m p (ty_width enc ty) = Some bs" and "val_has_ty v ty"
  shows "\<exists>m'. mem_store enc m ty p v = Some m' \<and> mem_write m p (encode_val enc v) = Some m'"
proof -
  have len: "length (encode_val enc v) = ty_width enc ty" by (rule length_encode_val[OF assms(1,3)])
  from mem_write_sub[OF assms(2), of 0 "encode_val enc v"] len obtain m' where
    "mem_write m p (encode_val enc v) = Some m'" by auto
  thus ?thesis using assms(3) by (simp add: mem_store_def)
qed

end

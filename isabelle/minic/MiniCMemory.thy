theory MiniCMemory
  imports MiniCSyntax "HOL-Library.Finite_Map"
begin

(* ========================================================================== *)
(* MiniC: values, bytes and memory                                            *)
(* ========================================================================== *)

(* Memory is a set of live blocks, each a list of bytes, addressed by a block
   number and a byte offset (the CompCert-style block/offset model). A byte is
   either undefined (never written), a concrete byte 0..255, or one fragment of
   a stored pointer. Pointers are never converted to or from integers.

   Integers are encoded abstractly: the encoding is a parameter (MEncoding)
   that satisfies the laws in valid_encoding. The little-endian instance
   le_encoding is supplied so that the interpreter can be run, but nothing is
   proved about it beyond valid_encoding. *)


section \<open>Pointers, bytes, values\<close>

(* A pointer is null, or (block, offset). The offset is a byte offset within
   the block; it may equal the block's size ("one past the end"), but never
   exceed it. *)
datatype MPtr =
  MP_Null
  | MP_Addr nat nat

(* MB_Frag b off i is fragment number i (0 \<le> i < pointer size) of the stored
   pointer MP_Addr b off. A pointer can be read back only from a complete,
   in-order run of its fragments. The null pointer is stored as all-zero
   bytes, and all-zero bytes read back as the null pointer. *)
datatype MByte =
  MB_Undef
  | MB_Byte nat
  | MB_Frag nat nat nat

datatype MVal =
  MV_Int Signedness IntBits int
  | MV_Ptr MPtr

(* Does a value have a (scalar) C type? Integers must be in range. *)
fun val_has_ty :: "MVal \<Rightarrow> CTy \<Rightarrow> bool" where
  "val_has_ty (MV_Int s b i) (CTy_Int s' b') = (s = s' \<and> b = b' \<and> int_fits s b i)"
| "val_has_ty (MV_Ptr _) ty = is_ptr_ty ty"
| "val_has_ty _ _ = False"

abbreviation "MV_U64 n \<equiv> MV_Int Unsigned IntBits_64 n"
abbreviation "MV_U8 n \<equiv> MV_Int Unsigned IntBits_8 n"


section \<open>Integer encoding\<close>

(* Number of bytes of an integer type (CHAR_BIT = 8 is assumed, see DESIGN.md). *)
fun byte_width :: "IntBits \<Rightarrow> nat" where
  "byte_width IntBits_8 = 1"
| "byte_width IntBits_16 = 2"
| "byte_width IntBits_32 = 4"
| "byte_width IntBits_64 = 8"

lemma bit_size_byte_width: "bit_size b = 8 * byte_width b"
  by (cases b) simp_all

lemma byte_width_pos: "byte_width b > 0"
  by (cases b) simp_all

(* The encoding parameters: the pointer size in bytes, and the encoding and
   decoding of integers of each type as byte lists (bytes are nats 0..255). *)
record MEncoding =
  enc_ptr_size :: nat
  enc_encode   :: "Signedness \<Rightarrow> IntBits \<Rightarrow> int \<Rightarrow> nat list"
  enc_decode   :: "Signedness \<Rightarrow> IntBits \<Rightarrow> nat list \<Rightarrow> int"

(* The laws the proofs rely on:
    - the pointer size is positive;
    - an in-range integer encodes to exactly byte_width bytes, each < 256,
      and decodes back to itself (round trip; injectivity follows);
    - decoding any byte_width bytes gives an in-range integer (no trap
      representations: C99 7.18.1.1 for the exact-width types);
    - zero encodes as all-zero bytes (calloc / static zero-fill produce the
      Core default value). *)
definition valid_encoding :: "MEncoding \<Rightarrow> bool" where
  "valid_encoding enc =
    (enc_ptr_size enc > 0
     \<and> (\<forall>s b i. int_fits s b i \<longrightarrow>
          length (enc_encode enc s b i) = byte_width b
          \<and> (\<forall>x \<in> set (enc_encode enc s b i). x < 256)
          \<and> enc_decode enc s b (enc_encode enc s b i) = i)
     \<and> (\<forall>s b bs. length bs = byte_width b \<and> (\<forall>x \<in> set bs. x < 256)
          \<longrightarrow> int_fits s b (enc_decode enc s b bs))
     \<and> (\<forall>s b. enc_encode enc s b 0 = replicate (byte_width b) 0))"

lemma valid_encoding_ptr_size_pos: "valid_encoding enc \<Longrightarrow> enc_ptr_size enc > 0"
  by (simp add: valid_encoding_def)

lemma valid_encoding_length:
  "valid_encoding enc \<Longrightarrow> int_fits s b i \<Longrightarrow> length (enc_encode enc s b i) = byte_width b"
  by (simp add: valid_encoding_def)

lemma valid_encoding_bytes:
  "valid_encoding enc \<Longrightarrow> int_fits s b i \<Longrightarrow> x \<in> set (enc_encode enc s b i) \<Longrightarrow> x < 256"
  by (simp add: valid_encoding_def)

lemma valid_encoding_round_trip:
  "valid_encoding enc \<Longrightarrow> int_fits s b i \<Longrightarrow> enc_decode enc s b (enc_encode enc s b i) = i"
  by (simp add: valid_encoding_def)

lemma valid_encoding_decode_fits:
  "valid_encoding enc \<Longrightarrow> length bs = byte_width b \<Longrightarrow> \<forall>x \<in> set bs. x < 256
   \<Longrightarrow> int_fits s b (enc_decode enc s b bs)"
  by (simp add: valid_encoding_def)

lemma valid_encoding_zero:
  "valid_encoding enc \<Longrightarrow> enc_encode enc s b 0 = replicate (byte_width b) 0"
  by (simp add: valid_encoding_def)

(* Injectivity is a consequence of the round trip. *)
lemma valid_encoding_injective:
  assumes "valid_encoding enc" and "int_fits s b i" and "int_fits s b j"
    and "enc_encode enc s b i = enc_encode enc s b j"
  shows "i = j"
proof -
  have "i = enc_decode enc s b (enc_encode enc s b i)"
    using valid_encoding_round_trip[OF assms(1,2)] by simp
  also have "\<dots> = enc_decode enc s b (enc_encode enc s b j)" using assms(4) by simp
  also have "\<dots> = j" using valid_encoding_round_trip[OF assms(1,3)] .
  finally show ?thesis .
qed


subsection \<open>The ranges of the integer types as powers of two\<close>

lemma int_fits_pow2:
  "int_fits s b i \<longleftrightarrow>
     (case s of
        Unsigned \<Rightarrow> 0 \<le> i \<and> i < 2 ^ bit_size b
      | Signed \<Rightarrow> - (2 ^ (bit_size b - 1)) \<le> i \<and> i < 2 ^ (bit_size b - 1))"
  by (cases s; cases b; simp; presburger)

lemma int_fits_unsigned:
  "int_fits Unsigned b i \<longleftrightarrow> 0 \<le> i \<and> i < 2 ^ bit_size b"
  using int_fits_pow2[of Unsigned b i] by simp

lemma int_fits_signed:
  "int_fits Signed b i \<longleftrightarrow> - (2 ^ (bit_size b - 1)) \<le> i \<and> i < 2 ^ (bit_size b - 1)"
  using int_fits_pow2[of Signed b i] by simp


subsection \<open>Little-endian instance\<close>

(* n bytes of the natural number v, least significant first (v mod 256^n). *)
fun le_bytes :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "le_bytes 0 v = []"
| "le_bytes (Suc n) v = (v mod 256) # le_bytes n (v div 256)"

fun le_value :: "nat list \<Rightarrow> nat" where
  "le_value [] = 0"
| "le_value (x # xs) = x + 256 * le_value xs"

lemma length_le_bytes [simp]: "length (le_bytes n v) = n"
  by (induction n arbitrary: v) simp_all

lemma le_bytes_lt_256: "x \<in> set (le_bytes n v) \<Longrightarrow> x < 256"
  by (induction n arbitrary: v) auto

lemma le_value_le_bytes: "le_value (le_bytes n v) = v mod 256 ^ n"
proof (induction n arbitrary: v)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "le_value (le_bytes (Suc n) v) = v mod 256 + 256 * (v div 256 mod 256 ^ n)"
    by (simp add: Suc.IH)
  also have "\<dots> = v mod (256 * 256 ^ n)"
    by (simp add: mod_mult2_eq)
  finally show ?case by simp
qed

lemma le_value_lt: "(\<forall>x \<in> set bs. x < 256) \<Longrightarrow> le_value bs < 256 ^ length bs"
proof (induction bs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then have "x < 256" and "le_value xs < 256 ^ length xs" by auto
  then have "x + 256 * le_value xs < 256 + 256 * le_value xs" by simp
  also have "\<dots> = 256 * (le_value xs + 1)" by simp
  also have "\<dots> \<le> 256 * 256 ^ length xs"
    using \<open>le_value xs < 256 ^ length xs\<close> by simp
  finally show ?case by simp
qed

lemma le_bytes_zero: "le_bytes n 0 = replicate n 0"
  by (induction n) simp_all

(* The encoding of an integer i of type (s, b) is the little-endian encoding of
   i mod 2^N (N the bit size), which for an in-range i is i itself (unsigned)
   or i + 2^N for negative i (two's complement). *)
definition le_encode :: "Signedness \<Rightarrow> IntBits \<Rightarrow> int \<Rightarrow> nat list" where
  "le_encode s b i = le_bytes (byte_width b) (nat (i mod 2 ^ bit_size b))"

definition le_decode :: "Signedness \<Rightarrow> IntBits \<Rightarrow> nat list \<Rightarrow> int" where
  "le_decode s b bs =
    (let v = int (le_value bs) in
     case s of
       Unsigned \<Rightarrow> v
     | Signed \<Rightarrow> if v \<ge> 2 ^ (bit_size b - 1) then v - 2 ^ bit_size b else v)"

definition le_encoding :: "MEncoding" where
  "le_encoding = \<lparr> enc_ptr_size = 8, enc_encode = le_encode, enc_decode = le_decode \<rparr>"

lemma pow_256_byte_width: "(256::nat) ^ byte_width b = 2 ^ bit_size b"
  by (cases b) simp_all

lemma pow_256_byte_width_int: "(256::int) ^ byte_width b = 2 ^ bit_size b"
  by (cases b) simp_all

lemma bit_size_pos: "bit_size b > 0"
  by (cases b) simp_all

lemma le_round_trip:
  assumes "int_fits s b i"
  shows "le_decode s b (le_encode s b i) = i"
proof -
  let ?N = "bit_size b"
  have N: "?N = 8 * byte_width b" by (rule bit_size_byte_width)
  have modpos: "0 \<le> i mod 2 ^ ?N" by simp
  have val: "int (le_value (le_encode s b i)) = i mod 2 ^ ?N"
  proof -
    have "le_value (le_encode s b i) = nat (i mod 2 ^ ?N) mod 256 ^ byte_width b"
      by (simp add: le_encode_def le_value_le_bytes)
    also have "\<dots> = nat (i mod 2 ^ ?N)"
      by (simp add: pow_256_byte_width nat_less_iff[symmetric])
    finally show ?thesis using modpos by simp
  qed
  show ?thesis
  proof (cases s)
    case Unsigned
    with assms have "0 \<le> i" "i < 2 ^ ?N" unfolding Unsigned int_fits_unsigned by simp_all
    then have "i mod 2 ^ ?N = i" by simp
    with val Unsigned show ?thesis by (simp add: le_decode_def)
  next
    case Signed
    with assms have lo: "- (2 ^ (?N - 1)) \<le> i" and hi: "i < 2 ^ (?N - 1)"
      unfolding Signed int_fits_signed by simp_all
    have split: "(2::int) ^ ?N = 2 * 2 ^ (?N - 1)"
      using bit_size_pos[of b] by (cases ?N) simp_all
    show ?thesis
    proof (cases "i \<ge> 0")
      case True
      with hi split have "i mod 2 ^ ?N = i" by simp
      with val Signed hi show ?thesis by (simp add: le_decode_def)
    next
      case False
      then have "i < 0" by simp
      have "i mod 2 ^ ?N = (i + 2 ^ ?N) mod 2 ^ ?N" by simp
      also have "\<dots> = i + 2 ^ ?N"
        using lo split \<open>i < 0\<close> by (intro mod_pos_pos_trivial) linarith+
      finally have "i mod 2 ^ ?N = i + 2 ^ ?N" .
      with val Signed lo split \<open>i < 0\<close> show ?thesis by (simp add: le_decode_def)
    qed
  qed
qed

lemma le_decode_fits:
  assumes "length bs = byte_width b" and "\<forall>x \<in> set bs. x < 256"
  shows "int_fits s b (le_decode s b bs)"
proof -
  let ?N = "bit_size b"
  have "le_value bs < 256 ^ byte_width b" using le_value_lt[OF assms(2)] assms(1) by simp
  then have v_lt: "int (le_value bs) < 2 ^ ?N"
    by (simp add: pow_256_byte_width)
  have split: "(2::int) ^ ?N = 2 * 2 ^ (?N - 1)"
    using bit_size_pos[of b] by (cases ?N) simp_all
  show ?thesis
  proof (cases s)
    case Unsigned
    show ?thesis unfolding Unsigned int_fits_unsigned le_decode_def using v_lt by simp
  next
    case Signed
    have nonneg: "0 \<le> int (le_value bs)" by simp
    show ?thesis
      unfolding Signed int_fits_signed le_decode_def Let_def
      using v_lt split nonneg by (simp split: Signedness.split; linarith)
  qed
qed

lemma valid_le_encoding: "valid_encoding le_encoding"
proof -
  have enc_len: "\<And>s b i. length (le_encode s b i) = byte_width b"
    by (simp add: le_encode_def)
  have enc_bytes: "\<And>s b i x. x \<in> set (le_encode s b i) \<Longrightarrow> x < 256"
    by (simp add: le_encode_def le_bytes_lt_256)
  have enc_zero: "\<And>s b. le_encode s b 0 = replicate (byte_width b) 0"
    by (simp add: le_encode_def le_bytes_zero)
  show ?thesis
    unfolding valid_encoding_def le_encoding_def
    using enc_len enc_bytes enc_zero le_round_trip le_decode_fits by auto
qed


section \<open>Encoding values as bytes\<close>

(* Width in bytes of a scalar C type. *)
fun ty_width :: "MEncoding \<Rightarrow> CTy \<Rightarrow> nat" where
  "ty_width enc (CTy_Int s b) = byte_width b"
| "ty_width enc CTy_CharPtr = enc_ptr_size enc"
| "ty_width enc CTy_VoidPtr = enc_ptr_size enc"

fun encode_ptr :: "MEncoding \<Rightarrow> MPtr \<Rightarrow> MByte list" where
  "encode_ptr enc MP_Null = replicate (enc_ptr_size enc) (MB_Byte 0)"
| "encode_ptr enc (MP_Addr b off) = map (MB_Frag b off) [0..<enc_ptr_size enc]"

(* Decode a pointer: all-zero bytes are null; a complete in-order run of
   fragments of one pointer is that pointer; anything else is undefined. *)
definition decode_ptr :: "MEncoding \<Rightarrow> MByte list \<Rightarrow> MPtr option" where
  "decode_ptr enc bs =
    (if bs = replicate (enc_ptr_size enc) (MB_Byte 0) then Some MP_Null
     else case bs of
       MB_Frag b off 0 # _ \<Rightarrow>
         if bs = map (MB_Frag b off) [0..<enc_ptr_size enc] then Some (MP_Addr b off) else None
     | _ \<Rightarrow> None)"

(* The defined bytes of a byte list, if all of them are defined concrete bytes. *)
fun defined_bytes :: "MByte list \<Rightarrow> nat list option" where
  "defined_bytes [] = Some []"
| "defined_bytes (MB_Byte x # bs) = map_option ((#) x) (defined_bytes bs)"
| "defined_bytes (_ # bs) = None"

lemma defined_bytes_map [simp]: "defined_bytes (map MB_Byte xs) = Some xs"
  by (induction xs) simp_all

lemma defined_bytes_Some:
  "defined_bytes bs = Some xs \<Longrightarrow> bs = map MB_Byte xs"
proof (induction bs arbitrary: xs)
  case Nil then show ?case by simp
next
  case (Cons b bs)
  then show ?case by (cases b) auto
qed

lemma defined_bytes_Some_length:
  "defined_bytes bs = Some xs \<Longrightarrow> length xs = length bs"
  by (drule defined_bytes_Some) simp

definition decode_int :: "MEncoding \<Rightarrow> Signedness \<Rightarrow> IntBits \<Rightarrow> MByte list \<Rightarrow> int option" where
  "decode_int enc s b bs =
    (case defined_bytes bs of
       None \<Rightarrow> None
     | Some xs \<Rightarrow>
         if length xs = byte_width b \<and> (\<forall>x \<in> set xs. x < 256)
         then Some (enc_decode enc s b xs) else None)"

fun encode_val :: "MEncoding \<Rightarrow> MVal \<Rightarrow> MByte list" where
  "encode_val enc (MV_Int s b i) = map MB_Byte (enc_encode enc s b i)"
| "encode_val enc (MV_Ptr p) = encode_ptr enc p"

fun decode_val :: "MEncoding \<Rightarrow> CTy \<Rightarrow> MByte list \<Rightarrow> MVal option" where
  "decode_val enc (CTy_Int s b) bs = map_option (MV_Int s b) (decode_int enc s b bs)"
| "decode_val enc _ bs = map_option MV_Ptr (decode_ptr enc bs)"

lemma length_encode_ptr [simp]: "length (encode_ptr enc p) = enc_ptr_size enc"
  by (cases p) simp_all

lemma length_encode_val:
  "valid_encoding enc \<Longrightarrow> val_has_ty v ty \<Longrightarrow> length (encode_val enc v) = ty_width enc ty"
  by (cases v; cases ty) (auto simp: valid_encoding_length)

lemma decode_ptr_encode_ptr:
  assumes "valid_encoding enc"
  shows "decode_ptr enc (encode_ptr enc p) = Some p"
proof (cases p)
  case MP_Null
  then show ?thesis by (simp add: decode_ptr_def)
next
  case (MP_Addr b off)
  have pos: "enc_ptr_size enc > 0" using assms by (rule valid_encoding_ptr_size_pos)
  have upt: "[0..<enc_ptr_size enc] = 0 # [1..<enc_ptr_size enc]"
    using pos by (simp add: upt_conv_Cons)
  have neq: "map (MB_Frag b off) [0..<enc_ptr_size enc] \<noteq> replicate (enc_ptr_size enc) (MB_Byte 0)"
  proof
    assume eq: "map (MB_Frag b off) [0..<enc_ptr_size enc] = replicate (enc_ptr_size enc) (MB_Byte 0)"
    have "hd (map (MB_Frag b off) [0..<enc_ptr_size enc]) = MB_Frag b off 0"
      by (simp add: upt)
    moreover have "hd (replicate (enc_ptr_size enc) (MB_Byte 0)) = MB_Byte 0"
      using pos by (simp add: hd_replicate)
    ultimately show False using eq by simp
  qed
  show ?thesis using MP_Addr neq by (simp add: decode_ptr_def upt)
qed

(* Round trip for values: a stored value of type ty reads back as itself. *)
lemma decode_val_encode_val:
  assumes "valid_encoding enc" and "val_has_ty v ty"
  shows "decode_val enc ty (encode_val enc v) = Some v"
proof (cases v)
  case (MV_Int s b i)
  with assms(2) obtain s' b' where ty: "ty = CTy_Int s' b'" and eq: "s = s'" "b = b'"
    and fits: "int_fits s b i"
    by (cases ty) auto
  show ?thesis
    using MV_Int ty eq fits assms(1)
    by (simp add: decode_int_def valid_encoding_length valid_encoding_round_trip
                  valid_encoding_bytes)
next
  case (MV_Ptr p)
  with assms(2) have "is_ptr_ty ty" by simp
  then show ?thesis
    using MV_Ptr decode_ptr_encode_ptr[OF assms(1)] by (cases ty) simp_all
qed

(* A successful decode produces a value of the requested type. *)
lemma decode_val_has_ty:
  assumes "valid_encoding enc" and "decode_val enc ty bs = Some v"
  shows "val_has_ty v ty"
proof (cases ty)
  case (CTy_Int s b)
  with assms(2) obtain xs where
    "defined_bytes bs = Some xs" "length xs = byte_width b" "\<forall>x \<in> set xs. x < 256"
    "v = MV_Int s b (enc_decode enc s b xs)"
    by (auto simp: decode_int_def split: option.splits if_splits)
  with CTy_Int show ?thesis
    using valid_encoding_decode_fits[OF assms(1), of xs b s] by simp
next
  case CTy_CharPtr
  with assms(2) show ?thesis by (cases "decode_ptr enc bs") auto
next
  case CTy_VoidPtr
  with assms(2) show ?thesis by (cases "decode_ptr enc bs") auto
qed


section \<open>Memory\<close>

(* The live blocks, and the next block number to allocate. Block numbers are
   never reused: a freed block disappears from MM_Blocks and any pointer into
   it is dangling forever, so that a use after free is always detected. *)
record MMem =
  MM_Blocks :: "(nat, MByte list) fmap"
  MM_Next   :: nat

definition empty_mem :: MMem where
  "empty_mem = \<lparr> MM_Blocks = fmempty, MM_Next = 0 \<rparr>"

(* Allocate a fresh block with the given contents; returns the block number. *)
definition mem_alloc :: "MMem \<Rightarrow> MByte list \<Rightarrow> MMem \<times> nat" where
  "mem_alloc m bs =
    (\<lparr> MM_Blocks = fmupd (MM_Next m) bs (MM_Blocks m), MM_Next = Suc (MM_Next m) \<rparr>,
     MM_Next m)"

(* Free a block (None if it is not live). *)
definition mem_free :: "MMem \<Rightarrow> nat \<Rightarrow> MMem option" where
  "mem_free m b =
    (if b |\<in>| fmdom (MM_Blocks m)
     then Some (m \<lparr> MM_Blocks := fmdrop b (MM_Blocks m) \<rparr>)
     else None)"

(* Free a list of blocks, all of which must be live. *)
fun mem_free_all :: "MMem \<Rightarrow> nat list \<Rightarrow> MMem option" where
  "mem_free_all m [] = Some m"
| "mem_free_all m (b # bs) =
    (case mem_free m b of
       None \<Rightarrow> None
     | Some m' \<Rightarrow> mem_free_all m' bs)"

(* Is the byte range [off, off + n) (or the position off, when n = 0) inside a live
   block? *)
definition ptr_range_ok :: "MMem \<Rightarrow> MPtr \<Rightarrow> nat \<Rightarrow> bool" where
  "ptr_range_ok m p n =
    (case p of
       MP_Null \<Rightarrow> False
     | MP_Addr b off \<Rightarrow>
         (case fmlookup (MM_Blocks m) b of
            None \<Rightarrow> False
          | Some bs \<Rightarrow> off + n \<le> length bs))"

(* Read n bytes (None if the range is not valid). Undefined bytes are read as
   such; only decoding them is an error. *)
definition mem_read :: "MMem \<Rightarrow> MPtr \<Rightarrow> nat \<Rightarrow> MByte list option" where
  "mem_read m p n =
    (case p of
       MP_Null \<Rightarrow> None
     | MP_Addr b off \<Rightarrow>
         (case fmlookup (MM_Blocks m) b of
            None \<Rightarrow> None
          | Some bs \<Rightarrow> if off + n \<le> length bs then Some (take n (drop off bs)) else None))"

(* Write a list of bytes at a pointer (None if the range is not valid). *)
definition mem_write :: "MMem \<Rightarrow> MPtr \<Rightarrow> MByte list \<Rightarrow> MMem option" where
  "mem_write m p new =
    (case p of
       MP_Null \<Rightarrow> None
     | MP_Addr b off \<Rightarrow>
         (case fmlookup (MM_Blocks m) b of
            None \<Rightarrow> None
          | Some bs \<Rightarrow>
              if off + length new \<le> length bs
              then Some (m \<lparr> MM_Blocks :=
                              fmupd b (take off bs @ new @ drop (off + length new) bs) (MM_Blocks m) \<rparr>)
              else None))"

(* Pointer arithmetic: p + i must stay within [0, size] of p's block, which
   must be live. Otherwise undefined (as in C). *)
definition ptr_add :: "MMem \<Rightarrow> MPtr \<Rightarrow> int \<Rightarrow> MPtr option" where
  "ptr_add m p i =
    (case p of
       MP_Null \<Rightarrow> None
     | MP_Addr b off \<Rightarrow>
         (case fmlookup (MM_Blocks m) b of
            None \<Rightarrow> None
          | Some bs \<Rightarrow>
              if 0 \<le> int off + i \<and> int off + i \<le> int (length bs)
              then Some (MP_Addr b (nat (int off + i))) else None))"

(* Load / store a scalar of a given type. *)
definition mem_load :: "MEncoding \<Rightarrow> MMem \<Rightarrow> CTy \<Rightarrow> MPtr \<Rightarrow> MVal option" where
  "mem_load enc m ty p =
    (case mem_read m p (ty_width enc ty) of
       None \<Rightarrow> None
     | Some bs \<Rightarrow> decode_val enc ty bs)"

definition mem_store :: "MEncoding \<Rightarrow> MMem \<Rightarrow> CTy \<Rightarrow> MPtr \<Rightarrow> MVal \<Rightarrow> MMem option" where
  "mem_store enc m ty p v =
    (if val_has_ty v ty then mem_write m p (encode_val enc v) else None)"


subsection \<open>Basic facts about memory operations\<close>

lemma mem_read_length: "mem_read m p n = Some bs \<Longrightarrow> length bs = n"
  by (auto simp: mem_read_def split: MPtr.splits option.splits if_splits)

lemma mem_write_lookup_same:
  assumes "mem_write m (MP_Addr b off) new = Some m'"
  shows "fmlookup (MM_Blocks m') b = (case fmlookup (MM_Blocks m) b of
            Some bs \<Rightarrow> Some (take off bs @ new @ drop (off + length new) bs))"
  using assms by (auto simp: mem_write_def split: option.splits if_splits)

lemma mem_write_lookup_other:
  assumes "mem_write m (MP_Addr b off) new = Some m'" and "b' \<noteq> b"
  shows "fmlookup (MM_Blocks m') b' = fmlookup (MM_Blocks m) b'"
  using assms by (auto simp: mem_write_def split: option.splits if_splits)

lemma mem_write_next: "mem_write m p new = Some m' \<Longrightarrow> MM_Next m' = MM_Next m"
  by (auto simp: mem_write_def split: MPtr.splits option.splits if_splits)

(* Reading back what was just written. *)
lemma mem_read_mem_write:
  assumes "mem_write m (MP_Addr b off) new = Some m'"
  shows "mem_read m' (MP_Addr b off) (length new) = Some new"
proof -
  from assms obtain bs where lk: "fmlookup (MM_Blocks m) b = Some bs"
    and le: "off + length new \<le> length bs"
    by (auto simp: mem_write_def split: option.splits if_splits)
  have "fmlookup (MM_Blocks m') b = Some (take off bs @ new @ drop (off + length new) bs)"
    using mem_write_lookup_same[OF assms] lk by simp
  moreover have "length (take off bs @ new @ drop (off + length new) bs) = length bs"
    using le by simp
  ultimately show ?thesis using le by (simp add: mem_read_def)
qed

(* Store then load gives the value back. *)
lemma mem_load_mem_store:
  assumes "valid_encoding enc" and "mem_store enc m ty (MP_Addr b off) v = Some m'"
  shows "mem_load enc m' ty (MP_Addr b off) = Some v"
proof -
  from assms(2) have hty: "val_has_ty v ty"
    and w: "mem_write m (MP_Addr b off) (encode_val enc v) = Some m'"
    by (auto simp: mem_store_def split: if_splits)
  have len: "length (encode_val enc v) = ty_width enc ty"
    by (rule length_encode_val[OF assms(1) hty])
  show ?thesis
    using mem_read_mem_write[OF w] len decode_val_encode_val[OF assms(1) hty]
    by (simp add: mem_load_def)
qed

(* A loaded value has the type it was loaded at. *)
lemma mem_load_has_ty:
  "valid_encoding enc \<Longrightarrow> mem_load enc m ty p = Some v \<Longrightarrow> val_has_ty v ty"
  by (auto simp: mem_load_def decode_val_has_ty split: option.splits)

end

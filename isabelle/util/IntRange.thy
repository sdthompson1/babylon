theory IntRange
  imports Main
begin

datatype Signedness = Signed | Unsigned
datatype IntBits = IntBits_8 | IntBits_16 | IntBits_32 | IntBits_64

(* Get the range of a finite integer type *)
fun int_range :: "Signedness \<Rightarrow> IntBits \<Rightarrow> (int \<times> int)" where
  "int_range Signed IntBits_8 = (-128, 127)"
| "int_range Signed IntBits_16 = (-32768, 32767)"
| "int_range Signed IntBits_32 = (-2147483648, 2147483647)"
| "int_range Signed IntBits_64 = (-9223372036854775808, 9223372036854775807)"
| "int_range Unsigned IntBits_8 = (0, 255)"
| "int_range Unsigned IntBits_16 = (0, 65535)"
| "int_range Unsigned IntBits_32 = (0, 4294967295)"
| "int_range Unsigned IntBits_64 = (0, 18446744073709551615)"

(* Check if an int is within a given range *)
fun int_in_range :: "(int \<times> int) \<Rightarrow> int \<Rightarrow> bool" where
  "int_in_range (a, b) x = (x \<ge> a \<and> x \<le> b)"

(* Check if an int fits a given type *)
fun int_fits :: "Signedness \<Rightarrow> IntBits \<Rightarrow> int \<Rightarrow> bool" where
  "int_fits sign bits i = int_in_range (int_range sign bits) i"

(* Helper to get the maximum of two bit widths *)
fun max_bits :: "IntBits \<Rightarrow> IntBits \<Rightarrow> IntBits" where
  "max_bits IntBits_8 b = b"
| "max_bits IntBits_16 IntBits_8 = IntBits_16"
| "max_bits IntBits_16 b = b"
| "max_bits IntBits_32 IntBits_64 = IntBits_64"
| "max_bits IntBits_32 _ = IntBits_32"
| "max_bits IntBits_64 _ = IntBits_64"

(* Helper to get the next larger bit width, or None if already at maximum *)
fun next_bits :: "IntBits \<Rightarrow> IntBits option" where
  "next_bits IntBits_8 = Some IntBits_16"
| "next_bits IntBits_16 = Some IntBits_32"
| "next_bits IntBits_32 = Some IntBits_64"
| "next_bits IntBits_64 = None"

(* Determine the smallest type that can contain a value of both given types,
   or return None if this is not possible. *)
fun combine_int_types :: "Signedness \<Rightarrow> IntBits \<Rightarrow> Signedness \<Rightarrow> IntBits \<Rightarrow> (Signedness \<times> IntBits) option" where
  "combine_int_types Signed b1 Signed b2 = Some (Signed, max_bits b1 b2)"
| "combine_int_types Unsigned b1 Unsigned b2 = Some (Unsigned, max_bits b1 b2)"
| "combine_int_types Signed sb Unsigned ub = (
    case next_bits ub of
      None \<Rightarrow> None
    | Some ub_promoted \<Rightarrow> Some (Signed, max_bits sb ub_promoted)
  )"
| "combine_int_types Unsigned ub Signed sb = (
    case next_bits ub of
      None \<Rightarrow> None
    | Some ub_promoted \<Rightarrow> Some (Signed, max_bits ub_promoted sb)
  )"

(* Determine the bits and signedness of an integer literal. *)
(* Int literals use i32, u32, i64, u64 in that order of preference. *)
(* Integer literals have type i32, u32, i64, u64 in that order of preference *)
fun get_type_for_int :: "int \<Rightarrow> (Signedness \<times> IntBits) option" where
  "get_type_for_int i =
    (if int_in_range (int_range Signed IntBits_32) i then Some (Signed, IntBits_32)
    else if int_in_range (int_range Unsigned IntBits_32) i then Some (Unsigned, IntBits_32)
    else if int_in_range (int_range Signed IntBits_64) i then Some (Signed, IntBits_64)
    else if int_in_range (int_range Unsigned IntBits_64) i then Some (Unsigned, IntBits_64)
    else None)"

end

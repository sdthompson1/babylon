theory ExternNames
  imports "../bab/BabSyntax" "HOL-Library.Finite_Map"
begin

(* ========================================================================== *)
(* The C names of extern functions (minic/DESIGN.md, section 3.9)            *)
(* ========================================================================== *)

(* The elaborator sees DF_ExternName and drops it, and nothing in Core
   records the C name of an extern function. The map from the qualified
   Core name of each extern function to its C name is computed here,
   directly from the renamed Babylon modules that elab_program receives:
   the renamer has already replaced DF_Name by the qualified name
   (fullModName @ "." @ name, rename_declaration in BabRenamer.thy), which
   is exactly the key that elab_function_decl (ElabDecl.thy) uses for
   TE_Functions and CM_Functions, so the map agrees with the elaborator's
   naming without touching the elaborator or any of its theorems. The
   string hoisting that elab_program applies first does not rename
   functions. The C name is DF_ExternName if given, otherwise the
   unqualified Babylon name (get_extern_name in src/codegen.c).

   Also here: the check that an explicit C name is a valid C identifier
   (non-empty, alphanumeric or underscore, starting with a letter), as
   is_valid_extern_name in src/typechecker.c does. It is a check in the
   sense of section 3.9 (a property of the input that the printed C needs
   and that no theorem is about). *)

(* The unqualified part of a qualified name: after the last '.'. *)
definition unqualify :: "string \<Rightarrow> string" where
  "unqualify s = rev (takeWhile (\<lambda>c. c \<noteq> CHR ''.'') (rev s))"

(* The extern functions declared in a module, with their C names. *)
fun decl_extern_name :: "BabDeclaration \<Rightarrow> (string \<times> string) list" where
  "decl_extern_name (BabDecl_Function df) =
    (if DF_Extern df
     then [(DF_Name df, (case DF_ExternName df of Some n \<Rightarrow> n | None \<Rightarrow> unqualify (DF_Name df)))]
     else [])"
| "decl_extern_name _ = []"

definition module_extern_names :: "BabModule \<Rightarrow> (string \<times> string) list" where
  "module_extern_names m = concat (map decl_extern_name (Mod_Interface m @ Mod_Implementation m))"

(* The map for a whole program. A function declared in both the interface
   and the implementation has the same C name in both (the implementation
   repeats the declaration), so the order of the entries is irrelevant. *)
definition extern_name_map :: "BabModule list \<Rightarrow> (string, string) fmap" where
  "extern_name_map mods = fmap_of_list (concat (map module_extern_names mods))"

(* Validity of an explicit C name. *)
definition is_c_alpha :: "char \<Rightarrow> bool" where
  "is_c_alpha c = ((CHR ''a'' \<le> c \<and> c \<le> CHR ''z'') \<or> (CHR ''A'' \<le> c \<and> c \<le> CHR ''Z''))"

definition is_c_digit :: "char \<Rightarrow> bool" where
  "is_c_digit c = (CHR ''0'' \<le> c \<and> c \<le> CHR ''9'')"

definition is_valid_extern_name :: "string \<Rightarrow> bool" where
  "is_valid_extern_name s =
    (case s of
       [] \<Rightarrow> False
     | c # cs \<Rightarrow> is_c_alpha c \<and> list_all (\<lambda>c. is_c_alpha c \<or> is_c_digit c \<or> c = CHR ''_'') cs)"

(* The declarations with an invalid explicit C name: their locations. *)
fun decl_invalid_extern_name :: "BabDeclaration \<Rightarrow> Location list" where
  "decl_invalid_extern_name (BabDecl_Function df) =
    (case DF_ExternName df of
       Some n \<Rightarrow> if is_valid_extern_name n then [] else [DF_Location df]
     | None \<Rightarrow> [])"
| "decl_invalid_extern_name _ = []"

definition invalid_extern_names :: "BabModule list \<Rightarrow> Location list" where
  "invalid_extern_names mods =
    concat (map (\<lambda>m. concat (map decl_invalid_extern_name (Mod_Interface m @ Mod_Implementation m))) mods)"

end

/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef ERROR_H
#define ERROR_H

#include "ast.h"
#include "location.h"

#include <stdnoreturn.h>

struct NameList;

// returns newly allocated string
char * sanitise_name(const char *var_name);


// Loader / compiler "front-end" errors
void report_circular_dependency(struct Location location, const char *module_name);
void report_module_not_found(struct Location location, const char *module_name, const char *filename);
void report_module_name_mismatch_filename(struct Location location, const char *module_name);
void report_failed_to_open_c_file(const char *filename);
void report_mkdir_failed(const char *filename);

// Lexer errors
void report_lexical_error(struct Location location);
void report_unclosed_block_comment(struct Location location);

// Parser errors
void report_syntax_error(struct Location location, const char *detail);

// Renamer errors
void report_not_in_scope(struct Location location, const char *name);
void report_incorrect_use_as_module(struct Location location, const char *name);
void report_ambiguity(struct Location location, const char *name, struct NameList *names);
void report_duplicate_definition(const char *name, struct Location location);  // Note: This is also a typechecker error
void report_duplicate_import(struct Import *import);           // two imports have same alias-name
void report_import_clash_with_current(struct Import *import);  // import alias-name equals current module name

// Typechecker errors
void report_type_mismatch(struct Type *expected_type, struct Term *term);
void report_type_mismatch_explicit(struct Type *expected, struct Type *actual, struct Location location);
void report_type_mismatch_string(const char *expected_type, struct Term *term);
void report_type_mismatch_pattern(struct Type *scrut_type, struct Location location);
void report_invalid_decreases_type(struct Location location);
void report_int_pattern_out_of_range(struct Type *scrut_type, struct Location location);
void report_pattern_wrong_number_of_fields(struct Location location);
void report_match_with_no_arms(struct Location location);
void report_function_variable_not_allowed(struct Location loc);
void report_invalid_cast(struct Term *term);
void report_return_var_outside_postcondition(struct Term *var_term);
void report_return_var_void_function(struct Term *var_term);
void report_int_literal_too_big(struct Location location);
void report_incomplete_definition(struct Location location);
void report_interface_mismatch_impl(struct Decl *interface);
void report_double_impl(struct Decl *interface);
void report_missing_impl(struct Decl *interface);
void report_illegal_recursion(struct Decl *decl);
void report_abstract_type_with_tyvars(struct Location loc);
void report_cannot_assign(struct Term *term);
void report_cannot_assign_to_readonly(struct Term *term);
void report_cannot_swap(struct Term *term);
void report_cannot_swap_readonly(struct Term *term);
void report_cannot_take_ref(struct Location location);
void report_cannot_take_ref_to_readonly(struct Location location);
void report_cannot_take_ref_to_resizable_array_element(struct Location location);
void report_cannot_take_sizeof(struct Term *term);
void report_incomplete_array_type(struct Location loc);
void report_unexpected_return_value(struct Term *term);
void report_missing_return_value(struct Statement *stmt);
void report_call_of_non_function(struct Term *term);
void report_updating_non_record(struct Location loc);
void report_wrong_number_of_arguments(struct Term *term);
void report_wrong_number_of_type_arguments(struct Location loc, int num_expected, int num_actual);
void report_type_arguments_not_expected_here(struct Location loc);
void report_function_does_not_return_a_value(struct Term *term);
void report_function_return_value_ignored(struct Term *term);
void report_requires_after_ensures(struct Attribute *attr);
void report_attribute_not_allowed_here(struct Attribute *attr);
void report_duplicate_decreases(struct Attribute *attr);
void report_missing_decreases(struct Location loc);
void report_executable_quantifier(struct Term *term);
void report_executable_allocated(struct Term *term);
void report_access_ghost_var_from_executable_code(struct Term *term);
void report_access_impure_fun_from_ghost_code(struct Term *term);
void report_access_impure_fun_from_pure_code(struct Term *term);
void report_writing_nonghost_from_ghost_code(struct Location loc);
void report_cant_return_in_ghost_code(struct Statement *stmt);
void report_fix_outside_proof(struct Statement *stmt);
void report_use_outside_proof(struct Statement *stmt);
void report_fix_at_wrong_scope(struct Statement *stmt);
void report_use_at_wrong_scope(struct Statement *stmt);
void report_fix_no_forall_variable(struct Statement *stmt, struct Term *assert_term);
void report_use_no_exists_variable(struct Statement *stmt, struct Term *assert_term);
void report_fix_wrong_type(struct Statement *stmt, struct Term *assert_term);
void report_cannot_access_fields_in(struct Term *term);
void report_field_not_found(struct Location loc, const char *field_name);
void report_mixed_positional_and_named_fields(struct Location loc);
void report_field_name_missing(struct Location location);
void report_duplicate_field_name(struct Location location, const char *name);
void report_ref_arg_not_allowed(struct Location location);
void report_no_ref_in_postcondition(struct Location location);
void report_cannot_index(struct Term *term);
void report_wrong_number_of_indexes(struct Term *term);
void report_main_not_found(const char *module_name);
void report_main_wrong_type(const char *module_name);
void report_both_body_and_extern(struct Location location);
void report_impure_cannot_be_ghost(struct Decl *decl);
void report_extern_cannot_be_ghost(struct Decl *decl);
void report_non_compile_time_constant(struct Location location);
void report_compile_time_overflow(struct Location location);
void report_compile_time_division_by_zero(struct Location location);
void report_compile_time_invalid_shift_amount(struct Location location);
void report_compile_time_match_failure(struct Location location);
void report_int_real_not_allowed(struct Location location);
void report_can_only_show_hide_functions(struct Location location);
void report_chaining_direction_error(struct Location location);
void report_implies_direction_error(struct Location location);
void report_const_out_of_bounds(struct Location location);  // array index out of bounds, during const evaluation

// Verifier errors - these allocate a new string and return it
char * err_msg_operator_precondition_fail(struct Term *term);
char * err_msg_function_precondition_fail(struct Term *term, struct Location precond_loc);
char * err_msg_function_postcondition_fail(struct Location return_loc, struct Location postcond_loc);
char * err_msg_end_of_function_reached(struct Location loc);
char * err_msg_assert_failure(struct Statement *stmt);
char * err_msg_inconsistent_preconds(struct Decl *decl);
char * err_msg_inconsistent_postconds(struct Decl *decl);
char * err_msg_invariant_violated_on_entry(struct Attribute *attr);
char * err_msg_invariant_violated_on_exit(struct Attribute *attr);
char * err_msg_decreases_might_not_decrease(struct Attribute *attr);
char * err_msg_decreases_not_bounded_below(struct Attribute *attr);
char * err_msg_obtain_doesnt_exist(const struct Statement *stmt);
char * err_msg_nonexhaustive_match(struct Location loc);
char * err_msg_out_of_bounds(struct Location loc);  // array index out of bounds, during verification
char * err_msg_aliasing_violation(struct Location location, int n1, int n2);
char * err_msg_possible_aliasing_violation(struct Location location, int n1, int n2);
char * err_msg_assign_to_allocated(struct Location loc);
char * err_msg_assign_from_allocated(struct Location loc);
char * err_msg_return_allocated(struct Location loc);
char * err_msg_var_still_allocated(const char *name, struct Location loc);
char * err_msg_var_still_allocated_at_return(const char *name, struct Location loc);
char * err_msg_ref_invalid_variant_change(struct Location location);
char * err_msg_array_wrong_size(struct Term *term);

// Fatal errors (not expected in normal operation)
#define fatal_error(err) fatal_error_impl(err, __FILE__, __LINE__)
noreturn void fatal_error_impl(const char *err, const char *file, int line);


#endif

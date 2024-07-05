/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "fol.h"
#include "op_name.h"
#include "stringbuf.h"
#include "util.h"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

char * sanitise_name(const char *var_name)
{
    char * new_name = alloc(strlen(var_name) + 1);
    char * p = new_name;
    while (*var_name != 0 && *var_name != '@') {
        if (*var_name != '^') {
            *p++ = *var_name;
        }
        ++var_name;
    }
    *p = 0;
    return new_name;
}

static const char *attribute_name(enum AttrTag tag)
{
    switch (tag) {
    case ATTR_REQUIRES: return "requires";
    case ATTR_ENSURES: return "ensures";
    case ATTR_INVARIANT: return "invariant";
    case ATTR_DECREASES: return "decreases";
    }
    return "???";
}

static void print_error(const char *format, ...)
{
    va_list args;
    va_start(args, format);
    vfprintf(stderr, format, args);
    va_end(args);
}

static void print_location_no_colon(struct Location location)
{
    char buf[512];
    format_location(&location, false, true, buf, sizeof(buf));
    print_error("%s", buf);
}

static void print_location(struct Location location)
{
    wait_fol_complete();

    if (location.filename == NULL && location.begin_line_num == 0) {
        return;
    }

    print_location_no_colon(location);
    print_error(": ");
}

void report_circular_dependency(struct Location location, const char *module_name)
{
    print_location(location);
    print_error("Circular dependency on '%s'\n", module_name);
}

void report_module_not_found(struct Location location, const char *module_name, const char *filename)
{
    print_location(location);
    print_error("Module '%s' ('%s') not found\n", module_name, filename);
}

void report_module_name_mismatch_filename(struct Location location, const char *module_name)
{
    print_location(location);
    print_error("Module name '%s' does not match filename\n", module_name);
}

void report_failed_to_open_c_file(const char *filename)
{
    print_error("Failed to open output file '%s'\n", filename);
}

void report_mkdir_failed(const char *filename)
{
    print_error("Failed to create directory '%s'\n", filename);
}

void report_lexical_error(struct Location location)
{
    print_location(location);
    print_error("Lexical error\n");
}

void report_unclosed_block_comment(struct Location location)
{
    print_location(location);
    print_error("Unclosed '/*' comment\n");
}

void report_syntax_error(struct Location location, const char *detail)
{
    print_location(location);
    print_error("Syntax error");
    if (detail) {
        print_error(" (%s)", detail);
    }
    print_error("\n");
}

void report_chaining_direction_error(struct Location location)
{
    print_location(location);
    print_error("Incorrect chaining of <, <=, > or >= operators (all operators in chain must point in same direction)\n");
}

void report_implies_direction_error(struct Location location)
{
    print_location(location);
    print_error("Ambiguity between <== and ==> operators (consider using parentheses to disambiguate)\n");
}

void report_const_out_of_bounds(struct Location location)
{
    print_location(location);
    print_error("Array index out of bounds\n");
}

void report_not_in_scope(struct Location location, const char *name)
{
    print_location(location);
    char *new_name = sanitise_name(name);
    print_error("Not in scope: '%s'\n", new_name);
    free(new_name);
}

void report_incorrect_use_as_module(struct Location location, const char *name)
{
    print_location(location);
    char *new_name = sanitise_name(name);
    print_error("Incorrect use of '%s' as module name\n", new_name);
    free(new_name);
}

void report_ambiguity(struct Location location, const char *name, struct NameList *names)
{
    print_location(location);
    char *new_name = sanitise_name(name);
    print_error("Name '%s' is ambiguous: could refer to", new_name);
    free(new_name);

    for (struct NameList *n = names; n; n = n->next) {
        if (n != names) print_error(" or");
        new_name = sanitise_name(n->name);
        print_error(" '%s'", new_name);
        free(new_name);
    }

    print_error("\n");
}

void report_duplicate_definition(const char *name, struct Location location)
{
    print_location(location);
    char *new_name = sanitise_name(name);
    print_error("Duplicate definition of '%s'\n", new_name);
    free(new_name);
}

void report_duplicate_import(struct Import *import)
{
    print_location(import->location);
    print_error("Multiple imports of module '%s'\n", import->alias_name);
}

void report_import_clash_with_current(struct Import *import)
{
    print_location(import->location);
    print_error("Can't import as '%s', would clash with current module name\n", import->alias_name);
}

void report_duplicate_field_name(struct Location location, const char *name)
{
    print_location(location);
    print_error("Duplicate field name '%s'\n", name);
}

void report_ref_arg_not_allowed(struct Location location)
{
    print_location(location);
    print_error("Cannot pass ref arg here\n");
}

void report_no_ref_in_postcondition(struct Location location)
{
    print_location(location);
    print_error("'match ref' not allowed in postconditions\n");
}

void report_cannot_index(struct Term *term)
{
    print_location(term->location);
    print_error("Cannot index this term\n");
}

void report_wrong_number_of_indexes(struct Term *term)
{
    print_location(term->location);
    print_error("Wrong number of array indices (expected %d)\n",
                term->array_proj.lhs->type->array_data.ndim);
}

void report_main_not_found(const char *module_name)
{
    print_error("'main' function not found (check interface for module '%s')\n", module_name);
}

void report_main_wrong_type(const char *module_name)
{
    print_error("'%s.main' has the wrong type - expected a non-ghost function with no arguments and no return value\n", module_name);
}

void report_both_body_and_extern(struct Location location)
{
    print_location(location);
    print_error("Function body provided for 'extern' function\n");
}

void report_impure_cannot_be_ghost(struct Decl *decl)
{
    print_location(decl->location);
    print_error("'impure' function cannot be 'ghost'\n");
}

void report_extern_cannot_be_ghost(struct Decl *decl)
{
    print_location(decl->location);
    print_error("'extern' function cannot be 'ghost'\n");
}

void report_non_compile_time_constant(struct Location location)
{
    print_location(location);
    print_error("Value is not a compile-time constant\n");
}

void report_compile_time_overflow(struct Location location)
{
    print_location(location);
    print_error("Overflow in compile-time constant\n");
}

void report_compile_time_division_by_zero(struct Location location)
{
    print_location(location);
    print_error("Division by zero in compile-time constant\n");
}

void report_compile_time_invalid_shift_amount(struct Location location)
{
    print_location(location);
    print_error("Invalid shift amount in compile-time constant\n");
}

void report_compile_time_match_failure(struct Location location)
{
    print_location(location);
    print_error("Pattern match failure in compile-time constant\n");
}

void report_int_real_not_allowed(struct Location location)
{
    print_location(location);
    print_error("'int' or 'real' types not allowed in executable code\n");
}

void report_can_only_show_hide_functions(struct Location location)
{
    print_location(location);
    print_error("Attempting to show or hide non-function value\n");
}

void report_type_mismatch(struct Type *expected_type, struct Type *actual_type, struct Location loc)
{
    print_location(loc);
    print_error("Type mismatch\n");
    // TODO: Print actual and expected type
}

void report_type_mismatch_string(const char *expected_type, struct Term *term)
{
    print_location(term->location);
    print_error("Type mismatch (expected %s)\n", expected_type);
    // TODO: Print actual term type
}

void report_type_mismatch_pattern(struct Type *scrut_type, struct Location location)
{
    // todo: print the scrut_type, and perhaps the actual pattern type should be passed
    // in and reported also
    print_location(location);
    print_error("Type mismatch in pattern\n");
}

void report_invalid_decreases_type(struct Location location)
{
    print_location(location);
    print_error("Invalid type for 'decreases' (must be integer, bool, or tuple of the above)\n");
}

void report_pattern_wrong_number_of_fields(struct Location location)
{
    print_location(location);
    print_error("Pattern has wrong number of fields\n");
}

void report_int_pattern_out_of_range(struct Type *scrut_type, struct Location location)
{
    print_location(location);
    print_error("Case value is out of range for the type\n");
}

void report_match_with_no_arms(struct Location location)
{
    print_location(location);
    print_error("Match with no cases\n");
}

void report_function_variable_not_allowed(struct Location loc)
{
    print_location(loc);
    print_error("Can't use function as a value\n");
}

void report_invalid_cast(struct Term *term)
{
    print_location(term->location);
    print_error("Invalid cast\n");
}

void report_return_var_outside_postcondition(struct Term *var_term)
{
    print_location(var_term->location);
    print_error("'return' cannot be used as a variable in this context\n");
}

void report_return_var_void_function(struct Term *var_term)
{
    print_location(var_term->location);
    print_error("'return' used as variable, but this function does not return a value\n");
}

void report_int_literal_too_big(struct Location location)
{
    print_location(location);
    print_error("Integer literal too big\n");
}

void report_incomplete_definition(struct Location location)
{
    print_location(location);
    print_error("Incomplete definition\n");
}

void report_interface_mismatch_impl(struct Decl *interface)
{
    print_location(interface->location);
    char *new_name = sanitise_name(interface->name);
    print_error("Interface for '%s' doesn't match implementation\n", new_name);
    free(new_name);
}

void report_double_impl(struct Decl *interface)
{
    print_location(interface->location);
    char *new_name = sanitise_name(interface->name);
    print_error("Multiple implementations of '%s'\n", new_name);
    free(new_name);
}

void report_ghost_mismatch(struct Decl *interface)
{
    print_location(interface->location);
    char *new_name = sanitise_name(interface->name);
    print_error("'%s': interface and implementation do not agree on whether they are 'ghost'\n", new_name);
    free(new_name);
}

void report_impurity_mismatch(struct Decl *interface)
{
    print_location(interface->location);
    char *new_name = sanitise_name(interface->name);
    print_error("'%s' has pure interface but impure implementation\n", new_name);
    free(new_name);
}

void report_missing_impl(struct Decl *interface)
{
    print_location(interface->location);
    char *new_name = sanitise_name(interface->name);
    print_error("No implementation found for '%s'\n", new_name);
    free(new_name);
}

void report_illegal_recursion(struct Decl *decl)
{
    print_location(decl->location);
    char *new_name = sanitise_name(decl->name);
    print_error("Illegal recursive definition of '%s'\n", new_name);
    free(new_name);
}

void report_abstract_type_with_tyvars(struct Location location)
{
    print_location(location);
    print_error("Abstract or 'extern' type declarations cannot (currently) have type variables\n");
}

void report_abstract_type_in_impl(struct Location location)
{
    print_location(location);
    print_error("Abstract type declarations must be in the module interface, not implementation\n");
}

void report_cannot_assign(struct Term *term)
{
    print_location(term->location);
    print_error("Can't assign (left-hand-side is not an lvalue)\n");
}

void report_cannot_assign_to_readonly(struct Term *term)
{
    print_location(term->location);
    print_error("Can't assign (left-hand-side is read-only)\n");
}

void report_cannot_swap(struct Term *term)
{
    print_location(term->location);
    print_error("Can't swap (not an lvalue)\n");
}

void report_cannot_swap_readonly(struct Term *term)
{
    print_location(term->location);
    print_error("Can't swap (readonly value)\n");
}

void report_cannot_take_ref(struct Location location)
{
    print_location(location);
    print_error("Can't take reference (expression is not an lvalue)\n");
}

void report_cannot_take_ref_to_readonly(struct Location location)
{
    print_location(location);
    print_error("Can't take reference (expression is read-only)\n");
}

void report_cannot_take_ref_to_resizable_array_element(struct Location location)
{
    print_location(location);
    print_error("Can't take reference to element of resizable array\n");
}

void report_cannot_take_sizeof(struct Term *term)
{
    print_location(term->location);
    print_error("Can't use sizeof on this expression (not an lvalue)\n");
}

void report_incomplete_array_type(struct Location loc)
{
    print_location(loc);
    print_error("Can't use an incomplete array type here\n");
}

void report_unexpected_return_value(struct Term *term)
{
    print_location(term->location);
    print_error("Return value not expected\n");
}

void report_missing_return_value(struct Statement *stmt)
{
    print_location(stmt->location);
    print_error("Return value expected\n");
}

void report_call_of_non_function(struct Term *term)
{
    print_location(term->location);
    print_error("Value is not a callable function\n");
}

void report_updating_non_record(struct Location loc)
{
    print_location(loc);
    print_error("Record update applied to non-record value\n");
}

void report_wrong_number_of_arguments(struct Term *term)
{
    print_location(term->location);
    print_error("Wrong number of arguments passed to function\n");
}

void report_wrong_number_of_type_arguments(struct Location loc, int expected_num, int actual_num)
{
    print_location(loc);
    print_error("Wrong number of type arguments (expected: %d, actual: %d)\n", expected_num, actual_num);
}

void report_type_arguments_not_expected_here(struct Location loc)
{
    print_location(loc);
    print_error("Type arguments not expected here\n");
}

void report_function_does_not_return_a_value(struct Term *term)
{
    print_location(term->location);
    print_error("Function does not return a value\n");
}

void report_function_return_value_ignored(struct Term *term)
{
    print_location(term->location);
    print_error("Function return value is being ignored\n");
}

void report_requires_after_ensures(struct Attribute *attr)
{
    print_location(attr->location);
    print_error("'requires' must come before 'ensures'\n");
}

void report_attribute_not_allowed_here(struct Attribute *attr)
{
    print_location(attr->location);
    print_error("'%s' not allowed here\n", attribute_name(attr->tag));
}

void report_duplicate_decreases(struct Attribute *attr)
{
    print_location(attr->location);
    print_error("Duplicate 'decreases' clause\n");
}

void report_missing_decreases(struct Location loc)
{
    print_location(loc);
    print_error("A 'decreases' clause is required\n");
}

void report_executable_quantifier(struct Term *term)
{
    print_location(term->location);
    print_error("Quantifiers cannot be used in executable code\n");
}

void report_executable_allocated(struct Term *term)
{
    print_location(term->location);
    print_error("'allocated' cannot be used in executable code\n");
}

void report_access_ghost_var_from_executable_code(struct Term *term)
{
    print_location(term->location);
    print_error("Can't access a ghost variable or function from executable code\n");
}

void report_access_impure_fun_from_ghost_code(struct Term *term)
{
    print_location(term->location);
    print_error("Can't call an impure function from ghost code\n");
}

void report_access_impure_fun_from_pure_code(struct Term *term)
{
    print_location(term->location);
    print_error("Can't call an impure function from pure code\n");
}

void report_writing_nonghost_from_ghost_code(struct Location loc)
{
    print_location(loc);
    print_error("Can't write to a non-ghost variable from ghost code\n");
}

void report_cant_return_in_ghost_code(struct Statement *stmt)
{
    print_location(stmt->location);
    print_error("Can't return from ghost code (in an executable function)\n");
}

void report_fix_outside_proof(struct Statement *stmt)
{
    print_location(stmt->location);
    print_error("'fix' not allowed outside of a proof\n");
}

void report_use_outside_proof(struct Statement *stmt)
{
    print_location(stmt->location);
    print_error("'use' not allowed outside of a proof\n");
}

void report_fix_at_wrong_scope(struct Statement *stmt)
{
    print_location(stmt->location);
    print_error("'fix' within a sub-block of a proof is not currently supported\n");
}

void report_use_at_wrong_scope(struct Statement *stmt)
{
    print_location(stmt->location);
    print_error("'use' within a sub-block of a proof is not currently supported\n");
}

void report_fix_no_forall_variable(struct Statement *stmt, struct Term *assert_term)
{
    print_location(stmt->location);
    print_error("'fix' not valid; the assert at ");
    print_location_no_colon(assert_term->location);
    print_error(" doesn't have a corresponding forall-variable\n");
}

void report_use_no_exists_variable(struct Statement *stmt, struct Term *assert_term)
{
    print_location(stmt->location);
    print_error("'use' not valid; the assert at ");
    print_location_no_colon(assert_term->location);
    print_error(" doesn't have a corresponding exists-variable\n");
}

void report_fix_wrong_type(struct Statement *stmt, struct Term *assert_term)
{
    print_location(stmt->location);
    print_error("'fix' not valid; the type doesn't match the forall-variable at ");
    print_location_no_colon(assert_term->location);
    print_error("\n");
}

void report_cannot_access_fields_in(struct Term *term)
{
    print_location(term->location);
    print_error("Cannot access fields in this expression\n");
}

void report_field_not_found(struct Location loc, const char *field_name)
{
    print_location(loc);
    print_error("Field '%s' not found\n", field_name);
}

void report_mixed_positional_and_named_fields(struct Location loc)
{
    print_location(loc);
    print_error("Mixture of named and unnamed fields\n");
}

void report_field_name_missing(struct Location loc)
{
    print_location(loc);
    print_error("A field name is required\n");
}


//
// Verifier errors
//

static char * err_msg(struct Location loc, const char *msg)
{
    if (loc.filename != NULL || loc.begin_line_num != 0) {
        char buf[512];
        format_location(&loc, false, true, buf, sizeof(buf));
        return copy_string_3(buf, ": ", msg);
    } else {
        return copy_string(msg);
    }
}

static char * err_msg_2(struct Location loc1, const char *msg1,
                        struct Location loc2, const char *msg2)
{
    char buf[512];
    format_location(&loc2, false, true, buf, sizeof(buf));
    char *msg = copy_string_3(msg1, buf, msg2);
    char *result = err_msg(loc1, msg);
    free(msg);
    return result;
}

char * err_msg_operator_precondition_fail(struct Term *term)
{
    return err_msg(term->location, "Operator precondition might not be met\n");
}

char * err_msg_function_precondition_fail(struct Term *term, struct Location loc)
{
    return err_msg_2(term->location, "Precondition at ", loc, " might not be met\n");
}

char * err_msg_function_postcondition_fail(struct Location return_loc, struct Location postcond_loc)
{
    return err_msg_2(return_loc, "Postcondition at ", postcond_loc, " might not hold\n");
}

char * err_msg_end_of_function_reached(struct Location loc)
{
    return err_msg(loc, "Control might reach end of function without returning a value\n");
}

char * err_msg_assert_failure(struct Statement *stmt)
{
    return err_msg(stmt->location, "Assert might not hold\n");
}

char * err_msg_inconsistent_preconds(struct Decl *decl)
{
    return err_msg(decl->location,
                   "Implementation preconditions are not implied by the interface preconditions\n");
}

char * err_msg_inconsistent_postconds(struct Decl *decl)
{
    return err_msg(decl->location,
                   "Implementation postconditions don't imply the interface postconditions\n");
}

char * err_msg_invariant_violated_on_entry(struct Attribute *attr)
{
    return err_msg(attr->location,
                   "Invariant might not hold on entry to loop\n");
}

char * err_msg_invariant_violated_on_exit(struct Attribute *attr)
{
    return err_msg(attr->location,
                   "Invariant might not hold on exit from loop\n");
}

char * err_msg_decreases_might_not_decrease(struct Attribute *attr)
{
    return err_msg(attr->location,
                   "'decreases' value might not decrease\n");
}

char * err_msg_decreases_not_bounded_below(struct Attribute *attr)
{
    return err_msg(attr->location,
                   "'decreases' value (of type 'int') might not be bounded below by zero\n");
}

char * err_msg_obtain_doesnt_exist(const struct Statement *stmt)
{
    return err_msg(stmt->location,
                   "A value with the given property might not exist\n");
}

char * err_msg_nonexhaustive_match(struct Location loc)
{
    return err_msg(loc, "Match might not be exhaustive\n");
}

char * err_msg_out_of_bounds(struct Location loc)
{
    return err_msg(loc, "Array index might be out of bounds\n");
}

char * err_msg_aliasing_violation(struct Location location, int n1, int n2)
{
    char buf[200];
    sprintf(buf, "Aliasing rules violated: argument %d aliases argument %d\n", n1, n2);
    return err_msg(location, buf);
}


char * err_msg_possible_aliasing_violation(struct Location location, int n1, int n2)
{
    char buf[200];
    sprintf(buf, "Aliasing rules violated: argument %d might alias argument %d\n", n1, n2);
    return err_msg(location, buf);
}

char * err_msg_assign_to_allocated(struct Location loc)
{
    return err_msg(loc, "Can't assign, left-hand-side might be allocated\n");
}

char * err_msg_assign_from_allocated(struct Location loc)
{
    return err_msg(loc, "Can't assign, right-hand-side might be allocated\n");
}

char * err_msg_return_allocated(struct Location loc)
{
    return err_msg(loc, "Return value might be allocated\n");
}

char * err_msg_var_still_allocated(const char *name, struct Location loc)
{
    char *new_name = sanitise_name(name);
    char *msg = copy_string_3("'", new_name, "' might still be allocated when it goes out of scope\n");
    free(new_name);
    char *result = err_msg(loc, msg);
    free(msg);
    return result;
}

char * err_msg_var_still_allocated_at_return(const char *name, struct Location loc)
{
    char *new_name = sanitise_name(name);
    char *msg = copy_string_3("'", new_name, "' might still be allocated at return statement\n");
    free(new_name);
    char *result = err_msg(loc, msg);
    free(msg);
    return result;
}

char * err_msg_ref_invalid_variant_change(struct Location location)
{
    return err_msg(location,
                   "Reference may have become invalid due to change in datatype variant\n");
}

char * err_msg_array_wrong_size(struct Term *term)
{
    return err_msg(term->location,
                   "Array might have the wrong size\n");
}


//
// Internal compiler errors
//

noreturn void fatal_error_impl(const char *msg, const char *file, int line)
{
    fprintf(stderr, "Internal compiler error (%s:%d: %s)\n", file, line, msg);
    exit(1);
}

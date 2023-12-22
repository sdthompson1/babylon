/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


// Pattern match compiler. We loosely follow the algorithm described
// in "How to compile pattern matching" by Jules Jacobs, 2021.

// TODO: We might want to look at "When Do Match-Compilation
// Heuristics Matter?" by Scott & Ramsey (2000) instead.

#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "hash_table.h"
#include "match_compiler.h"
#include "renamer.h"
#include "util.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


//---------------------------------------------------------------------
// Data structures
//---------------------------------------------------------------------

struct MC_Let {
    const char *name;
    struct Term *rhs;
    bool ref;
    struct MC_Let *next;
};

struct MC_Test {
    struct Term *scrutinee;
    struct Pattern *pattern;
    struct MC_Test *next;
};

struct MC_Clause {
    struct MC_Test *tests;
    struct MC_Let *lets;
    void *rhs;
    struct MC_Clause *next;
};


enum MC_OutputTag {
    MC_MATCH,
    MC_IF,
    MC_RHS
};

struct MC_Output {
    enum MC_OutputTag tag;
    union {
        struct {
            // MC_MATCH
            struct Term *scrutinee;
            struct Arm *arms;  // The rhs void* ptrs point to MC_Output
        };
        struct {
            // MC_IF
            struct Term *cond;
            struct MC_Output *then_branch;
            struct MC_Output *else_branch;
        };
        struct {
            // MC_RHS
            struct MC_Let *lets;
            void *rhs;
        };
    };
};


static struct MC_Let * copy_let(struct MC_Let *let)
{
    struct MC_Let *result = NULL;
    struct MC_Let **tail = &result;

    while (let) {
        *tail = alloc(sizeof(struct MC_Let));
        (*tail)->name = copy_string(let->name);
        (*tail)->rhs = copy_term(let->rhs);
        (*tail)->ref = let->ref;
        (*tail)->next = NULL;
        tail = &(*tail)->next;
        let = let->next;
    }

    return result;
}

static void free_let(struct MC_Let *let)
{
    while (let) {
        free((void*)let->name);
        free_term(let->rhs);
        struct MC_Let *next = let->next;
        free(let);
        let = next;
    }
}

static struct MC_Test * copy_test(struct MC_Test *test)
{
    struct MC_Test *result = NULL;
    struct MC_Test **tail = &result;

    while (test) {
        *tail = alloc(sizeof(struct MC_Test));
        (*tail)->scrutinee = copy_term(test->scrutinee);
        (*tail)->pattern = copy_pattern(test->pattern);
        (*tail)->next = NULL;
        tail = &(*tail)->next;
        test = test->next;
    }

    return result;
}

static void free_test(struct MC_Test *test)
{
    while (test) {
        free_term(test->scrutinee);
        free_pattern(test->pattern);
        struct MC_Test *next = test->next;
        free(test);
        test = next;
    }
}

static struct MC_Clause * make_clause(struct MC_Test *tests,  // handed over
                                      struct MC_Let *lets,    // handed over
                                      void *rhs)              // handed over
{
    struct MC_Clause *node = alloc(sizeof(struct MC_Clause));
    node->tests = tests;
    node->lets = lets;
    node->rhs = rhs;
    node->next = NULL;
    return node;
}

static struct MC_Clause * copy_clause(struct MC_Clause *clause,
                                      void* (*copy_rhs)(void*))
{
    struct MC_Clause *result = NULL;
    struct MC_Clause **tail = &result;
    while (clause) {
        *tail = make_clause(copy_test(clause->tests),
                            copy_let(clause->lets),
                            copy_rhs(clause->rhs));
        tail = &(*tail)->next;
        clause = clause->next;
    }
    return result;
}

static void free_clause(struct MC_Clause *clause, void (*free_rhs)(void*))
{
    while (clause) {
        free_test(clause->tests);
        free_let(clause->lets);
        free_rhs(clause->rhs);

        struct MC_Clause *next = clause->next;
        free(clause);
        clause = next;
    }
}

static void free_output(struct MC_Output *output,
                        void (*free_rhs)(void*))
{
    if (!output) return;

    switch (output->tag) {
    case MC_MATCH:
        free_term(output->scrutinee);
        while (output->arms) {
            free_pattern(output->arms->pattern);
            free_output(output->arms->rhs, free_rhs);
            struct Arm *next = output->arms->next;
            free(output->arms);
            output->arms = next;
        }
        break;

    case MC_IF:
        free_term(output->cond);
        free_output(output->then_branch, free_rhs);
        free_output(output->else_branch, free_rhs);
        break;

    case MC_RHS:
        free_let(output->lets);
        free_rhs(output->rhs);
        break;
    }

    free(output);
}

//---------------------------------------------------------------------
// Pre-processing
//---------------------------------------------------------------------

// Remove any PAT_VAR test(s); replace with let(s).
// Remove any clauses *after* the first clause with no tests as they will never match
static void tidy_clauses(struct MC_Clause *match, void (*free_rhs)())
{
    for (struct MC_Clause *c = match; c; c = c->next) {
        struct MC_Test ** t = &c->tests;
        while (*t) {
            if ((*t)->pattern->tag == PAT_VAR) {
                struct MC_Let *let = alloc(sizeof(struct MC_Let));
                let->name = (*t)->pattern->var.name;
                let->ref = (*t)->pattern->var.ref;
                free((*t)->pattern);
                let->rhs = (*t)->scrutinee;

                let->next = c->lets;
                c->lets = let;

                struct MC_Test *next = (*t)->next;
                free(*t);
                *t = next;

            } else {
                t = &(*t)->next;
            }
        }

        if (c->tests == NULL) {
            // Any further clauses are redundant
            while (c->next) {
                struct MC_Clause *next = c->next->next;
                c->next->next = NULL;
                free_clause(c->next, free_rhs);
                c->next = next;
            }
        }
    }
}


//---------------------------------------------------------------------
// Heuristic for deciding what to match first
//---------------------------------------------------------------------

// Helper function - returns new string
const char * scrutinee_term_to_string(struct Term *term)
{
    switch (term->tag) {
    case TM_FIELD_PROJ:
        {
            const char *lhs_name = scrutinee_term_to_string(term->field_proj.lhs);
            const char *result = copy_string_3(lhs_name, ".", term->field_proj.field_name);
            free((void*)lhs_name);
            return result;
        }

    case TM_VAR:
        return copy_string(term->var.name);

    default:
        fatal_error("scrutinee_term_to_string: wrong tag");
    }
}


struct TermInfo {
    struct Term *term;
    int count;
};

// Heuristic to decide which variable/constructor to test
static void choose_test(struct MC_Clause *match,
                        struct Term **chosen_scrutinee,
                        const char **chosen_ctor,
                        struct Location *chosen_location)
{
    // Count how many times each scrutinee appears
    struct HashTable *counts = new_hash_table();

    for (struct MC_Clause *c = match; c; c = c->next) {
        for (struct MC_Test *t = c->tests; t; t = t->next) {
            const char * name = scrutinee_term_to_string(t->scrutinee);

            struct TermInfo *info = hash_table_lookup(counts, name);
            if (info) {
                free((void*)name);
                info->count++;
            } else {
                info = alloc(sizeof(struct TermInfo));
                info->term = t->scrutinee;  // no need to copy here
                info->count = 1;
                hash_table_insert(counts, name, info);
            }
        }
    }

    // Search all tests in the first clause. Find the one whose
    // scrutinee has the highest count.
    struct MC_Test *best_test = NULL;
    int best_count = 0;
    for (struct MC_Test *t = match->tests; t; t = t->next) {
        const char *name = scrutinee_term_to_string(t->scrutinee);
        struct TermInfo *info = hash_table_lookup(counts, name);
        free((void*)name);
        if (info->count > best_count) {
            best_count = info->count;
            best_test = t;
            *chosen_location = t->pattern->location;
        }
    }

    // Free the table
    hash_table_for_each(counts, ht_free_key_and_value, NULL);
    free_hash_table(counts);

    // The chosen scrutinee and chosen ctor can now be extracted.
    *chosen_scrutinee = copy_term(best_test->scrutinee);
    switch (best_test->pattern->tag) {
    case PAT_BOOL:
        if (best_test->pattern->bool_data.value) {
            *chosen_ctor = copy_string("");
        } else {
            *chosen_ctor = NULL;
        }
        break;

    case PAT_INT:
        *chosen_ctor = copy_string(best_test->pattern->int_data.data);
        break;

    case PAT_RECORD:
        *chosen_ctor = NULL;
        break;

    case PAT_VARIANT:
        *chosen_ctor = copy_string(best_test->pattern->variant.variant_name);
        break;

    default:
        fatal_error("choose_test: wrong pattern type");
    }
}


//---------------------------------------------------------------------
// The core algorithm; splitting a match into sub-matches
//---------------------------------------------------------------------

// True if the pattern's ctor matches "ctor"
static bool same_ctor(struct Pattern *p, const char *ctor)
{
    switch (p->tag) {
    case PAT_BOOL:
        if (ctor == NULL) {
            return !p->bool_data.value;
        } else {
            return p->bool_data.value;
        }
        break;

    case PAT_INT:
        return strcmp(p->int_data.data, ctor) == 0;

    case PAT_RECORD:
        return true;

    case PAT_VARIANT:
        return strcmp(p->variant.variant_name, ctor) == 0;

    default:
        fatal_error("same_ctor: wrong pattern type");
    }
}

// True if two terms are syntactically equal. Only works on
// TM_FIELD_PROJ and TM_VAR.
static bool same_term(struct Term *a, struct Term *b)
{
    if (a->tag != b->tag) {
        return false;
    }

    switch (a->tag) {
    case TM_VAR:
        return strcmp(a->var.name, b->var.name) == 0;

    case TM_FIELD_PROJ:
        return same_term(a->field_proj.lhs, b->field_proj.lhs)
            && strcmp(a->field_proj.field_name, b->field_proj.field_name) == 0;

    default:
        fatal_error("same_term: wrong term tag");
    }
}

// Look for a test matching the given scrutinee.
// If found, remove it from the list and return it.
// Otherwise return NULL.
static struct MC_Test * extract_test(struct MC_Test **tests,
                                     struct Term *wanted_scrutinee)
{
    while (*tests) {
        if (same_term((*tests)->scrutinee, wanted_scrutinee)) {
            struct MC_Test *result = *tests;
            *tests = (*tests)->next;
            result->next = NULL;
            return result;
        }
        tests = &(*tests)->next;
    }
    return NULL;
}

static struct MC_Test * make_tests_for_name_pattern_list(
    struct Term *scrutinee,   // shared. assumed TY_RECORD
    struct NamePatternList *list,  // handed over
    struct MC_Test *other_tests)   // handed over
{
    struct MC_Test *result = other_tests;
    struct NameTypeList *field_types = scrutinee->type->record_data.fields;

    while (list) {
        if (list->pattern->tag != PAT_WILDCARD) {
            struct Term *proj = make_term(scrutinee->location, TM_FIELD_PROJ);
            proj->field_proj.lhs = copy_term(scrutinee);
            proj->field_proj.field_name = list->name;

            for (struct NameTypeList *fld = field_types; fld; fld = fld->next) {
                if (strcmp(fld->name, list->name) == 0) {
                    proj->type = copy_type(fld->type);
                    break;
                }
            }

            struct MC_Test *test = alloc(sizeof(struct MC_Test));
            test->scrutinee = proj;
            test->pattern = list->pattern;
            test->next = result;
            result = test;
        } else {
            free((char*)list->name);
            free_pattern(list->pattern);
        }

        struct NamePatternList *next = list->next;
        free(list);
        list = next;
    }

    return result;
}


// Turn a test like "a is Foo(P)" into "payload is P" (where payload
//   is the supplied payload_name).
// "a is Foo" (with no payload) or "a is Foo(_)" (wildcard payload) are just deleted.
// "a is {P1,P2}" becomes "a.0 is P1, a.1 is P2".
// Int and bool tests are just removed.
// Return the new test(s) if any, followed by other_tests.
static struct MC_Test * explode_test(
    struct MC_Test *test,         // handed over. test->next should be NULL.
    const char *payload_name,     // shared.
    struct MC_Test *other_tests,  // handed over
    bool *payload_name_was_used)  // set to true if we used payload_name in the created test(s)
{
    struct MC_Test *result = NULL;

    switch (test->pattern->tag) {
    case PAT_VARIANT:
        {
            if (test->pattern->variant.payload
            && test->pattern->variant.payload->tag != PAT_WILDCARD) {
                struct Term *payload_term = make_var_term(test->pattern->location, payload_name);
                *payload_name_was_used = true;

                for (struct NameTypeList *v = test->scrutinee->type->variant_data.variants; v; v = v->next) {
                    if (strcmp(v->name, test->pattern->variant.variant_name) == 0) {
                        payload_term->type = copy_type(v->type);
                        break;
                    }
                }
                struct Pattern *payload_pattern = test->pattern->variant.payload;

                result = alloc(sizeof(struct MC_Test));
                result->scrutinee = payload_term;
                result->pattern = payload_pattern;
                result->next = other_tests;

            } else {
                result = other_tests;
                free_pattern(test->pattern->variant.payload);
            }

            free((void*)test->pattern->variant.variant_name);
        }
        break;

    case PAT_RECORD:
        result = make_tests_for_name_pattern_list(
            test->scrutinee,                // shared
            test->pattern->record.fields,   // handed over
            other_tests);                   // handed over
        break;

    case PAT_INT:
        free((void*)test->pattern->int_data.data);
        result = other_tests;
        break;

    case PAT_BOOL:
        result = other_tests;
        break;

    default:
        fatal_error("explode_test: wrong pattern tag");
    }

    free(test->pattern);
    free_term(test->scrutinee);
    free(test);

    return result;
}

static struct MC_Output * make_match_output(
    struct Term *scrutinee,   // handed over
    struct Pattern *pattern,  // handed over
    struct MC_Output *result_a,  // handed over
    struct MC_Output *result_b)  // handed over
{
    struct MC_Output *result = alloc(sizeof(struct MC_Output));

    result->tag = MC_MATCH;
    result->scrutinee = scrutinee;

    result->arms = alloc(sizeof(struct Arm));
    result->arms->location = pattern->location;
    result->arms->pattern = pattern;
    result->arms->rhs = result_a;

    result->arms->next = alloc(sizeof(struct Arm));
    result->arms->next->location = pattern->location;
    result->arms->next->pattern = make_pattern(pattern->location, PAT_WILDCARD);
    result->arms->next->rhs = result_b;
    result->arms->next->next = NULL;

    return result;
}

static struct MC_Output * make_if_output(
    struct Term *cond_term,   // handed over
    struct MC_Output *result_then,  // handed over
    struct MC_Output *result_else)  // handed over
{
    struct MC_Output *result = alloc(sizeof(struct MC_Output));
    result->tag = MC_IF;
    result->cond = cond_term;
    result->then_branch = result_then;
    result->else_branch = result_else;
    return result;
}


// forward declaration
static struct MC_Output * compile_clauses(
    struct MC_Clause *input,   // handed over
    uint64_t *name_counter,
    void (*free_rhs)(void*),
    void* (*copy_rhs)(void*));


// The main part of the algorithm. Converts a "tidied" clause into an MC_Output
// in which the Arm void* pointers point to further MC_Outputs.
static struct MC_Output * split_up_match(
    struct MC_Clause *clause,    // handed over
    struct Term *chosen_scrutinee,  // handed over
    const char *chosen_ctor,   // handed over
    struct Location chosen_location,
    uint64_t *name_counter,    // shared
    void (*free_rhs)(void*),
    void* (*copy_rhs)(void*))
{
    // For variant patterns we will need to make up a name for the payload variable
    const char *payload_name = NULL;
    if (chosen_scrutinee->type->tag == TY_VARIANT) {
        char buf[40];
        sprintf(buf, "p@@%" PRIu64, (*name_counter)++);
        payload_name = copy_string(buf);
    }

    bool payload_needed = false;

    // Build two new lists of clauses, corresponding to "[A]" and "[B]" in Jacobs' note.
    struct MC_Clause *list_a = NULL, *list_b = NULL;
    struct MC_Clause **tail_a = &list_a, **tail_b = &list_b;

    while (clause) {
        struct MC_Test *test = extract_test(&clause->tests, chosen_scrutinee);

        if (test != NULL) {
            if (same_ctor(test->pattern, chosen_ctor)) {
                // Explode the matching test, and leave the others unchanged
                test = explode_test(test, payload_name, clause->tests, &payload_needed);

                // Add these tests as a new clause in list_a
                *tail_a = make_clause(test, clause->lets, clause->rhs);
                tail_a = &(*tail_a)->next;

            } else {
                // Leave all tests unchanged (i.e. put the matching one back in the list)
                test->next = clause->tests;

                // Add these tests as a new clause in list_b
                *tail_b = make_clause(test, clause->lets, clause->rhs);
                tail_b = &(*tail_b)->next;
            }

            // Having taken all the pointers out of this clause, we can now free it
            // and move on to the next one.
            struct MC_Clause *next = clause->next;
            free(clause);
            clause = next;

        } else {
            // Add these tests to both lists
            struct MC_Clause *next = clause->next;
            clause->next = NULL;

            *tail_a = copy_clause(clause, copy_rhs);
            *tail_b = clause;
            tail_a = &(*tail_a)->next;
            tail_b = &(*tail_b)->next;

            // Move on to next clause.
            clause = next;
        }
    }

    // We now have two new clause lists, we can process those recursively.
    struct MC_Output *result_a = compile_clauses(list_a, name_counter, free_rhs, copy_rhs);
    struct MC_Output *result_b = compile_clauses(list_b, name_counter, free_rhs, copy_rhs);

    // Now make the result
    switch (chosen_scrutinee->type->tag) {
    case TY_VARIANT:
        {
            struct Pattern *pattern = make_pattern(chosen_location, PAT_VARIANT);
            pattern->variant.variant_name = chosen_ctor;

            if (payload_needed) {
                pattern->variant.payload = make_pattern(chosen_location, PAT_VAR);
                pattern->variant.payload->var.name = payload_name;
                pattern->variant.payload->var.ref = true;
            } else {
                pattern->variant.payload = make_pattern(chosen_location, PAT_WILDCARD);
                free((char*)payload_name);
            }
            return make_match_output(chosen_scrutinee, pattern, result_a, result_b);
        }

    case TY_RECORD:
        // We don't need a pattern match in this case, we can just
        // directly return result_a and discard result_b.
        free_output(result_b, free_rhs);
        free_term(chosen_scrutinee);
        free((void*)chosen_ctor);
        return result_a;

    case TY_FINITE_INT:
        {
            struct Term *cond_term = make_term(chosen_location, TM_BINOP);
            cond_term->type = make_type(g_no_location, TY_BOOL);
            cond_term->binop.lhs = chosen_scrutinee;
            cond_term->binop.list = alloc(sizeof(struct OpTermList));
            cond_term->binop.list->operator = BINOP_EQUAL;
            cond_term->binop.list->rhs = make_int_literal_term(chosen_location, chosen_ctor);
            cond_term->binop.list->rhs->type = copy_type(chosen_scrutinee->type);
            cond_term->binop.list->next = NULL;
            free((void*)chosen_ctor);
            return make_if_output(cond_term, result_a, result_b);
        }

    case TY_BOOL:
        {
            struct Term *cond_term = chosen_scrutinee;
            if (!chosen_ctor) {
                struct Term *not_term = make_term(cond_term->location, TM_UNOP);
                not_term->type = make_type(g_no_location, TY_BOOL);
                not_term->unop.operator = UNOP_NOT;
                not_term->unop.operand = cond_term;
                cond_term = not_term;
            }
            free((void*)chosen_ctor);
            return make_if_output(cond_term, result_a, result_b);
        }

    default:
        fatal_error("split_up_match: bad type");
    }
}


//---------------------------------------------------------------------
// Post-processing
//---------------------------------------------------------------------

static bool all_ctors_found(struct HashTable *ctors_found, struct Type *type)
{
    if (type->tag != TY_VARIANT) {
        fatal_error("all_ctors_found: wrong type");
    }
    for (struct NameTypeList *ctor = type->variant_data.variants; ctor; ctor = ctor->next) {
        if (!hash_table_contains_key(ctors_found, ctor->name)) {
            return false;
        }
    }
    return true;
}

static void post_process(struct MC_Output *match, void (*free_rhs)(void*))
{
    if (!match) return;

    switch (match->tag) {
    case MC_MATCH:
        {
            // Post-process each arm's rhs

            // Also, we can look for:

            // match s with
            //   ...
            //   default =>
            //     match s with (ARMS)

            // and replace with:

            // match s with
            //   ...
            //   (ARMS)

            // Also, remove a WILDCARD pattern if all constructors
            // have already been covered.

            struct HashTable *ctors_found = new_hash_table();

            struct Arm **arm = &match->arms;
            while (*arm) {

                // If it's a variant pattern, make a note of the constructor
                if ((*arm)->pattern->tag == PAT_VARIANT) {
                    if (hash_table_contains_key(ctors_found, (*arm)->pattern->variant.variant_name)) {
                        fatal_error("Bug in pattern match compiler, it has added two cases for the same constructor");
                    }
                    hash_table_insert(ctors_found, (*arm)->pattern->variant.variant_name, NULL);
                }

                // If it's a wildcard, it should be the last one
                if ((*arm)->pattern->tag == PAT_WILDCARD && (*arm)->next) {
                    fatal_error("wasn't expecting a next arm after wildcard");
                }

                // Check if we can optimise away this arm
                if ((*arm)->pattern->tag == PAT_WILDCARD
                && all_ctors_found(ctors_found, match->scrutinee->type)) {
                    // We can remove this arm because it is a wildcard
                    // after all ctors

                    free_pattern((*arm)->pattern);
                    free_output((*arm)->rhs, free_rhs);
                    free(*arm);
                    *arm = NULL;
                
                } else if ((*arm)->rhs
                && (*arm)->pattern->tag == PAT_WILDCARD
                && ((struct MC_Output*)(*arm)->rhs)->tag == MC_MATCH
                && same_term(((struct MC_Output*)(*arm)->rhs)->scrutinee, match->scrutinee)) {
                    // We can remove this arm, hoisting up its
                    // "sub-arms" to the current level

                    if ((*arm)->next) {
                        fatal_error("wasn't expecting a next arm after wildcard");
                    }

                    free_pattern((*arm)->pattern);
                    struct MC_Output *rhs = (*arm)->rhs;
                    free(*arm);

                    *arm = rhs->arms;
                    free_term(rhs->scrutinee);
                    free(rhs);

                } else {
                    // We are keeping this arm, so post-process it and
                    // move on.
                    post_process((*arm)->rhs, free_rhs);
                    arm = &(*arm)->next;
                }
            }

            free_hash_table(ctors_found);
        }
        break;

    case MC_IF:
        // No optimisations to be done; just post-process both
        // children
        post_process(match->then_branch, free_rhs);
        post_process(match->else_branch, free_rhs);
        break;

    case MC_RHS:
        // Nothing to do
        break;
    }
}


//---------------------------------------------------------------------
// Top-level "compile" function
//---------------------------------------------------------------------

// Compile a list of clauses into an MC_Output.
static struct MC_Output * compile_clauses(struct MC_Clause *input,   // handed over
                                          uint64_t *name_counter,
                                          void (*free_rhs)(void*),
                                          void* (*copy_rhs)(void*))
{
    if (input == NULL) {
        // There are no arms, this is a "match failure"
        return NULL;
    }

    // Pre-process the clause.
    // (Convert variable patterns into lets, and remove guaranteed-unmatchable clauses.)
    tidy_clauses(input, free_rhs);

    // If there is just one clause, with no tests, then no match is required,
    // we can generate the rhs directly.
    if (input->tests == NULL) {
        struct MC_Output *result = alloc(sizeof(struct MC_Output));
        result->tag = MC_RHS;
        // (input->test == NULL)
        result->lets = input->lets;
        result->rhs = input->rhs;
        // (we know input->next == NULL, because of tidy_clauses)
        free(input);
        return result;
    }

    // Otherwise, we have a genuine match statement to compile.
    // Apply the heuristic to determine which constructor to look at first.
    struct Term *chosen_scrutinee;
    const char *chosen_ctor;
    struct Location chosen_location;
    choose_test(input, &chosen_scrutinee, &chosen_ctor, &chosen_location);

    // Run the main algorithm to generate the output.
    return split_up_match(input, chosen_scrutinee, chosen_ctor, chosen_location,
                          name_counter, free_rhs, copy_rhs);
}


//---------------------------------------------------------------------
// Converting to/from Terms and Statements
//---------------------------------------------------------------------

static void initialise_mc(uint64_t *name_counter,
                          struct Term *original_scrutinee,
                          struct Arm *arms,
                          void * (*copy_rhs)(void*),
                          struct MC_Clause **clauses_out,
                          const char **scrut_temp_name_out)

{
    // Replace the scrutinee with a variable if necessary
    const char *scrut_temp_name = NULL;
    if (original_scrutinee->tag != TM_VAR) {
        char buf[40];
        sprintf(buf, "match@@%" PRIu64, (*name_counter)++);
        scrut_temp_name = copy_string(buf);
    }

    struct Term * scrut_term;
    if (scrut_temp_name) {
        scrut_term = make_var_term(original_scrutinee->location, scrut_temp_name);
        scrut_term->type = copy_type(original_scrutinee->type);
    } else {
        scrut_term = copy_term(original_scrutinee);
    }

    // Construct the initial MC_Clause list
    struct MC_Clause *list = NULL;
    struct MC_Clause **tail = &list;

    for (struct Arm *arm = arms; arm; arm = arm->next) {

        struct MC_Clause *clause = alloc(sizeof(struct MC_Clause));
        clause->tests = NULL;
        clause->lets = NULL;
        clause->rhs = copy_rhs(arm->rhs);
        clause->next = NULL;

        if (arm->pattern->tag != PAT_WILDCARD) {
            clause->tests = alloc(sizeof(struct MC_Test));
            clause->tests->scrutinee = copy_term(scrut_term);
            clause->tests->pattern = copy_pattern(arm->pattern);
            clause->tests->next = NULL;
        }

        *tail = clause;
        tail = &(*tail)->next;
    }

    free_term(scrut_term);

    *clauses_out = list;
    *scrut_temp_name_out = scrut_temp_name;
}

static struct Term * output_to_term(struct MC_Output *output,   // handed over
                                    const struct Location *failure_location,
                                    struct Type *result_type)   // shared
{
    if (output == NULL) {
        struct Term *result = make_term(*failure_location, TM_MATCH_FAILURE);
        result->type = copy_type(result_type);
        return result;
    }

    switch (output->tag) {
    case MC_MATCH:
        {
            // process the arms
            struct Arm * arm = output->arms;
            while (arm) {
                arm->rhs = output_to_term(arm->rhs, failure_location, result_type);
                arm = arm->next;
            }

            // create output
            struct Term *result = make_term(output->scrutinee->location, TM_MATCH);
            result->type = copy_type(result_type);
            result->match.scrutinee = output->scrutinee;
            result->match.arms = output->arms;
            free(output);
            return result;
        }
        break;

    case MC_IF:
        {
            struct Term *then_term = output_to_term(output->then_branch, failure_location, result_type);
            struct Term *else_term = output_to_term(output->else_branch, failure_location, result_type);

            struct Term *result = make_term(output->cond->location, TM_IF);
            result->type = copy_type(result_type);
            result->if_data.cond = output->cond;
            result->if_data.then_branch = then_term;
            result->if_data.else_branch = else_term;
            free(output);
            return result;
        }
        break;

    case MC_RHS:
        {
            struct Term *result = output->rhs;

            while (output->lets) {
                struct Term *let = make_term(result->location, TM_LET);
                let->type = copy_type(result_type);
                let->let.name = output->lets->name;
                let->let.rhs = output->lets->rhs;
                let->let.body = result;
                result = let;

                struct MC_Let *next = output->lets->next;
                free(output->lets);
                output->lets = next;
            }

            free(output);
            return result;
        }
    }

    fatal_error("output_to_term: bad tag");
}

static struct Statement * output_to_statement(struct MC_Output *output,   // handed over
                                              const struct Location *failure_location,
                                              bool ghost)
{
    if (output == NULL) {
        struct Statement *result = make_statement(*failure_location, ST_MATCH_FAILURE);
        result->ghost = ghost;
        return result;
    }

    switch (output->tag) {
    case MC_MATCH:
        {
            // process the arms
            struct Arm * arm = output->arms;
            while (arm) {
                arm->rhs = output_to_statement(arm->rhs, failure_location, ghost);
                arm = arm->next;
            }

            // create output
            struct Statement *result = make_statement(output->scrutinee->location, ST_MATCH);
            result->next = NULL;
            result->match.scrutinee = output->scrutinee;
            result->match.arms = output->arms;
            result->ghost = ghost;
            free(output);
            return result;
        }
        break;

    case MC_IF:
        {
            struct Statement *then_stmt = output_to_statement(output->then_branch, failure_location, ghost);
            struct Statement *else_stmt = output_to_statement(output->else_branch, failure_location, ghost);

            struct Statement *result = make_statement(output->cond->location, ST_IF);
            result->next = NULL;
            result->if_data.condition = output->cond;
            result->if_data.then_block = then_stmt;
            result->if_data.else_block = else_stmt;
            result->ghost = ghost;
            free(output);
            return result;
        }
        break;

    case MC_RHS:
        {
            struct Statement *result = output->rhs;

            while (output->lets) {
                struct Statement *vardecl = make_statement(result ? result->location : *failure_location, ST_VAR_DECL);
                vardecl->next = result;
                vardecl->var_decl.name = output->lets->name;
                vardecl->var_decl.rhs = output->lets->rhs;
                vardecl->var_decl.type = copy_type(vardecl->var_decl.rhs->type);
                vardecl->var_decl.ref = output->lets->ref;
                vardecl->ghost = ghost;
                result = vardecl;

                struct MC_Let *next = output->lets->next;
                free(output->lets);
                output->lets = next;
            }

            free(output);
            return result;
        }
    }

    fatal_error("output_to_statement: bad tag");
}


//---------------------------------------------------------------------
// Top-level fns for compiling an individual match term or statement
//---------------------------------------------------------------------

static void free_term_aux(void* term)
{
    free_term(term);
}

static void* copy_term_aux(void *term)
{
    return copy_term(term);
}

static bool can_make_ref_for(struct Term *term)
{
    switch (term->tag) {
    case TM_VAR:
        return true;

    case TM_FIELD_PROJ:
        return can_make_ref_for(term->field_proj.lhs);

    case TM_ARRAY_PROJ:
        return can_make_ref_for(term->array_proj.lhs);

    default:
        return false;
    }
}

static struct Term * compile_match_term(uint64_t *name_counter, struct Term *term)
{
    const char *scrut_temp_name;
    struct MC_Clause *clauses;
    initialise_mc(name_counter,
                  term->match.scrutinee,
                  term->match.arms,
                  copy_term_aux,
                  &clauses,
                  &scrut_temp_name);

    struct MC_Output *output = compile_clauses(clauses, name_counter, free_term_aux, copy_term_aux);
    post_process(output, free_term_aux);

    struct Term *result = output_to_term(output, &term->location, term->type);
    result->location = term->location;

    if (scrut_temp_name) {
        struct Term *let = make_term(result->location, TM_LET);
        let->type = copy_type(result->type);
        let->let.name = scrut_temp_name;
        let->let.rhs = copy_term(term->match.scrutinee);
        let->let.body = result;
        result = let;
    }

    // Alpha-convert to remove any duplicate names
    // (these can happen if any of the match arm rhs's were duplicated,
    // which unfortunately is necessary sometimes)
    rename_term_for_match_compiler(result, name_counter);

    return result;
}

static void free_statement_aux(void *stmt)
{
    free_statement(stmt);
}

static void* copy_statement_aux(void *stmt)
{
    return copy_statement(stmt);
}

static struct Statement * compile_match_statement(uint64_t *name_counter, struct Statement *stmt)
{
    const char *scrut_temp_name;
    struct MC_Clause *clauses;
    initialise_mc(name_counter,
                  stmt->match.scrutinee,
                  stmt->match.arms,
                  copy_statement_aux,
                  &clauses,
                  &scrut_temp_name);

    struct MC_Output *output = compile_clauses(clauses, name_counter, free_statement_aux, copy_statement_aux);
    post_process(output, free_statement_aux);

    struct Statement *result = output_to_statement(output, &stmt->location, stmt->ghost);
    struct Location loc = stmt->location;
    if (result) result->location = loc;

    if (scrut_temp_name) {
        struct Statement *vardecl = make_statement(loc, ST_VAR_DECL);
        vardecl->next = result;
        vardecl->var_decl.name = scrut_temp_name;
        vardecl->var_decl.type = copy_type(stmt->match.scrutinee->type);
        vardecl->var_decl.rhs = copy_term(stmt->match.scrutinee);
        vardecl->var_decl.ref = can_make_ref_for(stmt->match.scrutinee);
        vardecl->ghost = stmt->ghost;
        result = vardecl;
    }

    // Alpha-convert to remove any duplicate names
    rename_statement_for_match_compiler(result, name_counter);

    return result;
}


//---------------------------------------------------------------------
// Front-end
//---------------------------------------------------------------------

static void * tr_match_term(void *context, struct Term *term, void *type_result, void *scrut_result, void *arm_result)
{
    struct Term *new_term = compile_match_term(context, term);

    // copy the result to the term
    free_type(term->type);
    free_term(term->match.scrutinee);
    while (term->match.arms) {
        free_pattern(term->match.arms->pattern);
        free_term(term->match.arms->rhs);
            struct Arm *next = term->match.arms->next;
            free(term->match.arms);
            term->match.arms = next;
    }
    *term = *new_term;
    free(new_term);

    return NULL;
}

void match_compiler_term(uint64_t *name_counter, struct Term *term)
{
    struct TermTransform tr = {0};
    tr.transform_match = tr_match_term;
    transform_term(&tr, name_counter, term);
}

void match_compiler_attributes(uint64_t *name_counter, struct Attribute *attr)
{
    for (; attr; attr = attr->next) {
        if (attr->tag == ATTR_INVARIANT || attr->tag == ATTR_DECREASES
        || attr->tag == ATTR_REQUIRES || attr->tag == ATTR_ENSURES) {
            match_compiler_term(name_counter, attr->term);
        } else {
            fatal_error("unexpected attribute");
        }
    }
}

void match_compiler_statements(uint64_t *name_counter, struct Statement *statements)
{
    // we don't currently have a "transform_statement" framework, so
    // have to do the recursion manually

    for (struct Statement *stmt = statements; stmt; stmt = stmt->next) {
        switch (stmt->tag) {
        case ST_VAR_DECL:
            match_compiler_term(name_counter, stmt->var_decl.rhs);
            break;

        case ST_FIX:
            break;

        case ST_OBTAIN:
            match_compiler_term(name_counter, stmt->obtain.condition);
            break;

        case ST_USE:
            match_compiler_term(name_counter, stmt->use.term);
            break;

        case ST_ASSIGN:
            // lhs cannot contain matches, but rhs can
            match_compiler_term(name_counter, stmt->assign.rhs);
            break;

        case ST_SWAP:
            // neither term in a swap-stmt can contain matches
            break;

        case ST_RETURN:
            match_compiler_term(name_counter, stmt->ret.value);
            break;

        case ST_ASSERT:
            match_compiler_term(name_counter, stmt->assert_data.condition);
            match_compiler_statements(name_counter, stmt->assert_data.proof);
            break;

        case ST_ASSUME:
            match_compiler_term(name_counter, stmt->assume.condition);
            break;

        case ST_IF:
            match_compiler_term(name_counter, stmt->if_data.condition);
            match_compiler_statements(name_counter, stmt->if_data.then_block);
            match_compiler_statements(name_counter, stmt->if_data.else_block);
            break;

        case ST_WHILE:
            match_compiler_term(name_counter, stmt->while_data.condition);
            match_compiler_attributes(name_counter, stmt->while_data.attributes);
            match_compiler_statements(name_counter, stmt->while_data.body);
            break;

        case ST_CALL:
            match_compiler_term(name_counter, stmt->call.term);
            break;

        case ST_MATCH:
            match_compiler_term(name_counter, stmt->match.scrutinee);
            for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {
                match_compiler_statements(name_counter, arm->rhs);
            }

            {
                // detach next statement temporarily
                struct Statement *next = stmt->next;
                stmt->next = NULL;

                // run the pattern match compiler
                struct Statement *new_stmt = compile_match_statement(name_counter, stmt);

                // copy the result to the statement
                free_term(stmt->match.scrutinee);
                while (stmt->match.arms) {
                    free_pattern(stmt->match.arms->pattern);
                    free_statement(stmt->match.arms->rhs);
                    struct Arm *next = stmt->match.arms->next;
                    free(stmt->match.arms);
                    stmt->match.arms = next;
                }
                *stmt = *new_stmt;
                free(new_stmt);

                // reattach next statement
                struct Statement **ptr = &stmt->next;
                while (*ptr) ptr = &(*ptr)->next;
                *ptr = next;
            }
            break;

        case ST_MATCH_FAILURE:
            break;

        case ST_SHOW_HIDE:
            break;
        }
    }
}

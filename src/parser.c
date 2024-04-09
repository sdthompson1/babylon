/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "ast.h"
#include "error.h"
#include "lexer.h"
#include "parser.h"
#include "util.h"

#include <ctype.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

// -----------------------------------------------------------------------------

#define MAX_PRECEDENCE 7

struct OpData {
    enum BinOp operator;
    int precedence;
};

struct OpData operators[] = {
    // note: if changing this table, also update MAX_PRECEDENCE if required
    // also update debug_print.c
    [TOK_TIMES] = { BINOP_TIMES, 7 },
    [TOK_DIVIDE] = { BINOP_DIVIDE, 7 },
    [TOK_MODULO] = { BINOP_MODULO, 7 },
    [TOK_AND] = { BINOP_BITAND, 7 },
    [TOK_LESS_LESS] = { BINOP_SHIFTLEFT, 7 },
    [TOK_GREATER_GREATER] = { BINOP_SHIFTRIGHT, 7 },

    [TOK_PLUS] = { BINOP_PLUS, 6 },
    [TOK_MINUS] = { BINOP_MINUS, 6 },
    [TOK_BAR] = { BINOP_BITOR, 6 },
    [TOK_HAT] = { BINOP_BITXOR, 6 },

    [TOK_GREATER] = { BINOP_GREATER, 5 },
    [TOK_GREATER_EQUAL] = { BINOP_GREATER_EQUAL, 5 },
    [TOK_LESS] = { BINOP_LESS, 5 },
    [TOK_LESS_EQUAL] = { BINOP_LESS_EQUAL, 5 },
    [TOK_EQUAL_EQUAL] = { BINOP_EQUAL, 5 },
    [TOK_EXCLAM_EQUAL] = { BINOP_NOT_EQUAL, 5 },

    [TOK_AND_AND] = { BINOP_AND, 4 },

    [TOK_BAR_BAR] = { BINOP_OR, 3 },

    [TOK_EQUAL_EQUAL_GREATER] = { BINOP_IMPLIES, 2 },
    [TOK_LESS_EQUAL_EQUAL] = { BINOP_IMPLIED_BY, 2 },

    [TOK_LESS_EQUAL_EQUAL_GREATER] = { BINOP_IFF, 1 },

    [TOK_EOF] = {0}
};


// -----------------------------------------------------------------------------

struct ParserState {
    const struct Token *token;
    bool error;

    // context for "old" parsing
    bool postcondition;
    bool old;

    // checksumming
    struct SHA256_CTX sha256_module;
    struct SHA256_CTX sha256_decl;
};

static void advance(struct ParserState *state)
{
    if (state->token->type != TOK_EOF) {
        sha256_add_token(&state->sha256_module, state->token);
        sha256_add_token(&state->sha256_decl, state->token);
        state->token = state->token->next;
    }
}

static void report_error(struct ParserState *state, struct Location loc, const char *detail)
{
    if (!state->error) {
        report_syntax_error(loc, detail);
    }
    state->error = true;

    // don't attempt error recovery yet. just fast-forward to EOF
    while (state->token->type != TOK_EOF) {
        advance(state);
    }
}

static const struct Token * expect(struct ParserState *state, enum TokenType type, const char *msg)
{
    if (state->token->type != type) {
        char buf[256];
        sprintf(buf, "expected %s", msg);
        report_error(state, state->token->location, buf);
        return NULL;
    } else {
        const struct Token *tok = state->token;
        advance(state);
        return tok;
    }
}


// -----------------------------------------------------------------------------

//
// Type Parsing
//

static struct Type * parse_type(struct ParserState *state, bool report_errors);

static struct Term * parse_term(struct ParserState *state, bool allow_lbrace);

// Assumption: current token is '<'.
// The list is closed by '>'.
// End of "loc_out" is set to end of list.
static bool parse_type_list(struct ParserState *state,
                            bool report_errors,
                            struct TypeList **output,
                            struct Location *loc_out)
{
    advance(state);

    struct TypeList *types = NULL;
    struct TypeList **tail = &types;

    bool success = true;

    while (state->token->type != TOK_GREATER) {
        if (types != NULL) {
            // not the first type in the list, so we need a comma
            if (state->token->type == TOK_COMMA) {
                advance(state);
            } else {
                if (report_errors) {
                    // report an "expected" error
                    expect(state, TOK_COMMA, "',' or '>'");
                }
                success = false;
                break;
            }
        }

        struct Type *type = parse_type(state, report_errors);
        if (!type) {
            success = false;
            break;
        }

        struct TypeList *node = alloc(sizeof(struct TypeList));
        node->type = type;
        node->next = NULL;

        *tail = node;
        tail = &node->next;
    }

    if (success) {
        set_location_end(loc_out, &state->token->location);
        advance(state);
        *output = types;
        return true;
    } else {
        free_type_list(types);
        return false;
    }
}

// Parse a NameTypeList. The names are optional and will be set to NULL if omitted.
// Current token is assumed to be '{', and list is closed by '}'.
// The end of 'loc' is set to the end of the list.
// (If 'error' is non-NULL, sets *error to true on error - this is needed when
// report_errors = false, as NULL is a valid return value if the list is empty)
static struct NameTypeList *parse_name_type_list(struct ParserState *state,
                                                 bool report_errors,
                                                 struct Location *loc,
                                                 bool *error)
{
    advance(state);

    struct NameTypeList *list = NULL;
    struct NameTypeList **tail = &list;

    while (state->token->type != TOK_RBRACE) {

        // If this is not the first item, we need to see a comma
        if (list != NULL) {
            if (state->token->type != TOK_COMMA) {
                if (report_errors) expect(state, TOK_COMMA, "',' or '}'");
                free_name_type_list(list);
                if (error) *error = true;
                return NULL;
            }
            advance(state);
        }

        // See if there is a field name
        const char *field_name = NULL;

        if (state->token->type == TOK_NAME
        && state->token->next
        && state->token->next->type == TOK_COLON) {
            field_name = copy_string(state->token->data);
            advance(state);
            advance(state);
        }

        // Parse the type
        struct Type *type = parse_type(state, report_errors);
        if (!type) {
            free((char*)field_name);
            free_name_type_list(list);
            if (error) *error = true;
            return NULL;
        }

        struct NameTypeList *node = alloc(sizeof(struct NameTypeList));
        node->name = field_name;
        node->type = type;
        node->next = NULL;

        *tail = node;
        tail = &node->next;
    }

    set_location_end(loc, &state->token->location);
    advance(state);

    return list;
}

static struct Type * parse_type(struct ParserState *state, bool report_errors)
{
    struct Location loc = state->token->location;
    enum TokenType tag = state->token->type;
    const char *data = state->token->data;

    struct Type *result = NULL;

    switch (tag) {
    case TOK_LPAREN:
        advance(state);
        result = parse_type(state, report_errors);
        if (state->token->type == TOK_RPAREN) {
            advance(state);
        } else {
            free_type(result);
            result = NULL;
            if (report_errors) {
                expect(state, TOK_RPAREN, "')'");
            }
        }
        break;

    case TOK_NAME:
        {
            const char *name = NULL;

            advance(state);
            if (state->token->type == TOK_DOT) {
                advance(state);
                if (state->token->type == TOK_NAME) {
                    name = copy_string_3(data, ".", state->token->data);
                    advance(state);
                } else {
                    if (report_errors) {
                        expect(state, TOK_NAME, "type name");  // report error
                    }
                    break;
                }
            } else {
                name = copy_string(data);
            }

            struct TypeList *tyargs = NULL;
            bool success = true;

            if (state->token->type == TOK_LESS) {
                success = parse_type_list(state, report_errors, &tyargs, &loc);
            }

            if (success) {
                struct Type *ty = make_type(loc, TY_VAR);
                ty->var_data.name = name;

                if (tyargs) {
                    struct Type *ty2 = make_type(loc, TY_APP);
                    ty2->app_data.lhs = ty;
                    ty2->app_data.tyargs = tyargs;
                    ty = ty2;
                }

                result = ty;
            } else {
                free_type_list(tyargs);
                free((char*)name);
            }
        }
        break;

    case TOK_KW_BOOL:
        advance(state);
        result = make_type(loc, TY_BOOL);
        break;

    case TOK_KW_U8:
        advance(state);
        result = make_int_type(loc, false, 8);
        break;

    case TOK_KW_U16:
        advance(state);
        result = make_int_type(loc, false, 16);
        break;

    case TOK_KW_U32:
        advance(state);
        result = make_int_type(loc, false, 32);
        break;

    case TOK_KW_U64:
        advance(state);
        result = make_int_type(loc, false, 64);
        break;

    case TOK_KW_I8:
        advance(state);
        result = make_int_type(loc, true, 8);
        break;

    case TOK_KW_I16:
        advance(state);
        result = make_int_type(loc, true, 16);
        break;

    case TOK_KW_I32:
        advance(state);
        result = make_int_type(loc, true, 32);
        break;

    case TOK_KW_I64:
        advance(state);
        result = make_int_type(loc, true, 64);
        break;

    case TOK_KW_INT:
        advance(state);
        result = make_type(loc, TY_MATH_INT);
        break;

    case TOK_KW_REAL:
        advance(state);
        result = make_type(loc, TY_MATH_REAL);
        break;

    case TOK_LBRACE:
        {
            bool error = false;
            struct NameTypeList *fields = parse_name_type_list(state, report_errors, &loc, &error);
            if (!error) {
                result = make_type(loc, TY_RECORD);
                result->record_data.fields = fields;
            }
        }
        break;

    default:
        if (report_errors) {
            report_error(state, loc, "expected type");
        }
        break;
    }

    struct Type *final_result = NULL;
    struct Type **tail_ptr = &final_result;

    while (result && state->token->type == TOK_LBRACKET) {
        advance(state);

        struct OpTermList *dim_terms = NULL;
        struct OpTermList **dim_terms_tail = &dim_terms;
        bool first = true;

        bool found_size = false;
        bool found_star = false;
        bool found_empty = false;
        int ndim = 0;

        do {
            struct Term *term = NULL;

            // need a comma before each dimension other than the first
            if (!first) {
                if (state->token->type == TOK_COMMA) {
                    advance(state);
                } else {
                    free_op_term_list(dim_terms);
                    free_type(result);
                    if (report_errors) {
                        report_error(state, state->token->location, "expected ',' or ']'");
                    }
                    return NULL;
                }
            }

            first = false;

            // There might be a size-term next. If so it will start
            // with a token which is neither ',' nor ']'.
            // Alternatively there might be a '*' next.
            if (state->token->type == TOK_TIMES) {
                found_star = true;
                advance(state);
            } else if (state->token->type != TOK_COMMA && state->token->type != TOK_RBRACKET) {
                // Note: technically we should not report errors while
                // parsing the array-size term (if report_errors is false).
                // But we don't have a report_errors option in parse_term
                // (yet). This is relatively harmless, it just means errors
                // might get reported twice e.g. in a term like f<a[**]>
                // (where ** is a parse error).
                found_size = true;
                term = parse_term(state, true);
                if (term == NULL) {
                    free_op_term_list(dim_terms);
                    free_type(result);
                    return NULL;
                }
            } else {
                found_empty = true;
            }

            // Count total number of dimensions found.
            ++ndim;

            // Record the size-term if there is one.
            struct OpTermList *node = alloc(sizeof(struct OpTermList));
            node->operator = BINOP_PLUS;  // dummy value
            node->rhs = term;
            node->next = NULL;
            *dim_terms_tail = node;
            dim_terms_tail = &node->next;

        } while (state->token->type != TOK_RBRACKET);

        if ((int)found_size + (int)found_empty + (int)found_star != 1) {
            if (report_errors) {
                report_error(state, loc, "invalid array specification");
            }
            free_op_term_list(dim_terms);
            free_type(result);
            return NULL;
        }

        set_location_end(&loc, &state->token->location);
        advance(state);

        struct Type *array_type = make_type(loc, TY_ARRAY);
        array_type->array_data.element_type = NULL;
        array_type->array_data.ndim = ndim;
        array_type->array_data.resizable = found_star;
        if (found_size) {
            array_type->array_data.sizes = alloc(sizeof(struct Term*) * ndim);
            int i = 0;
            for (struct OpTermList *node = dim_terms; node; node = node->next) {
                array_type->array_data.sizes[i++] = node->rhs;
                node->rhs = NULL;
            }
        } else {
            array_type->array_data.sizes = NULL;
        }
        *tail_ptr = array_type;
        tail_ptr = &array_type->array_data.element_type;

        free_op_term_list(dim_terms);
    }

    *tail_ptr = result;
    return final_result;
}


// -----------------------------------------------------------------------------

//
// Pattern Parsing
//

static struct Pattern * parse_pattern(struct ParserState *state);

// Assumption: current token is '{'. parses upto and including '}'.
// The end of 'loc' is updated to be the end of the final '}' token.
static struct NamePatternList * parse_name_pattern_list(struct ParserState *state,
                                                        struct Location *loc)
{
    advance(state);

    struct NamePatternList *list = NULL;
    struct NamePatternList **tail = &list;

    while (state->token->type != TOK_RBRACE) {

        if (list != NULL) {
            expect(state, TOK_COMMA, "',' or '}'");
        }

        const char *field_name = NULL;

        if (state->token->type == TOK_NAME
        && state->token->next
        && state->token->next->type == TOK_EQUAL) {

            field_name = copy_string(state->token->data);

            advance(state);
            advance(state);
        }

        struct Pattern *p = parse_pattern(state);

        if (!p) {
            // parse error
            free((void*)field_name);
            break;
        }

        *tail = alloc(sizeof(struct NamePatternList));
        (*tail)->name = field_name;
        (*tail)->pattern = p;
        (*tail)->next = NULL;
        tail = &(*tail)->next;
    }

    set_location_end(loc, &state->token->location);
    advance(state);

    return list;
}

static struct Pattern * parse_pattern(struct ParserState *state)
{
    struct Location loc = state->token->location;
    bool negative = false;
    bool ref = false;

    switch (state->token->type) {
    case TOK_KW_REF:
        advance(state);
        if (state->token->type != TOK_NAME) {
            report_error(state, state->token->location, "expected variable name");
            return NULL;
        }
        set_location_end(&loc, &state->token->location);
        ref = true;
        // Fall through

    case TOK_NAME:
        {
            const char *name = copy_string(state->token->data);
            struct Location name_loc = state->token->location;
            advance(state);

            if (isupper(name[0])) {
                // variant pattern

                if (ref) {
                    report_error(state, name_loc, "expected variable name");
                    free((char*)name);
                    return NULL;
                }

                if (state->token->type == TOK_DOT) {
                    advance(state);
                    const struct Token *new_tok = expect(state, TOK_NAME, "variant name");
                    if (new_tok == NULL) {
                        free((char*)name);
                        return NULL;
                    }
                    const char *new_name = copy_string_3(name, ".", new_tok->data);
                    free((char*)name);
                    name = new_name;
                }

                struct TypeList *tyargs = NULL;
                if (state->token->type == TOK_LESS) {
                    parse_type_list(state, true, &tyargs, &loc);
                }
                free_type_list(tyargs);  // tyargs are ignored for the moment

                bool have_payload = false;
                bool paren = false;
                if (state->token->type == TOK_LBRACE) {
                    have_payload = true;
                } else if (state->token->type == TOK_LPAREN) {
                    have_payload = true;
                    paren = true;
                    advance(state);
                }

                struct Pattern *payload = have_payload ? parse_pattern(state) : NULL;

                if (paren) {
                    expect(state, TOK_RPAREN, "')'");
                }

                struct Pattern *p = make_pattern(loc, PAT_VARIANT);
                p->variant.variant_name = name;
                p->variant.payload = payload;
                return p;

            } else {
                // variable pattern
                struct Pattern *p = make_pattern(loc, PAT_VAR);
                p->var.name = name;
                p->var.ref = ref;
                return p;
            }
        }
        break;

    case TOK_UNDERSCORE:
        advance(state);
        return make_pattern(loc, PAT_WILDCARD);

    case TOK_KW_TRUE:
    case TOK_KW_FALSE:
        {
            struct Pattern *p = make_pattern(loc, PAT_BOOL);
            p->bool_data.value = (state->token->type == TOK_KW_TRUE);
            advance(state);
            return p;
        }
        break;

    case TOK_MINUS:
        advance(state);
        if (state->token->type != TOK_INT_LITERAL) {
            report_error(state, loc, "expected pattern");
            return NULL;
        }
        set_location_end(&loc, &state->token->location);
        negative = true;
        // Fall through

    case TOK_INT_LITERAL:
        {
            struct Pattern *p = make_pattern(loc, PAT_INT);
            p->int_data.data =
                negative ? copy_string_2("-", state->token->data)
                         : copy_string(state->token->data);
            advance(state);
            return p;
        }
        break;

    case TOK_LBRACE:
        {
            // Record or tuple pattern
            struct NamePatternList *list = parse_name_pattern_list(state, &loc);
            struct Pattern *p = make_pattern(loc, PAT_RECORD);
            p->record.fields = list;
            return p;
        }
        break;

    default:
        report_error(state, loc, "expected pattern");
        return NULL;
    }
}

static struct Arm * make_arm(struct Pattern *p, void *r,
                             const struct Location *r_loc,
                             const struct Location *case_loc)
{
    struct Arm *arm = alloc(sizeof(struct Arm));
    arm->location = *case_loc;
    if (r_loc) {
        set_location_end(&arm->location, r_loc);
    } else if (p) {
        set_location_end(&arm->location, &p->location);
    }
    arm->pattern = p;
    arm->rhs = r;
    arm->next = NULL;
    return arm;
}


// -----------------------------------------------------------------------------

//
// Term Parsing
//

static struct Term * parse_tyarg_suffix(struct ParserState *state, struct Term *base_term)
{
    // Parse type arguments, if any

    if (state->token->type == TOK_LESS) {
        // We need some backtracking here, because of ambiguity, e.g.
        //
        //   f(a<b,c>(d))
        //
        // This could be a function "f" of one argument, namely a
        // function "a" applied to type arguments "b" and "c" and a
        // term argument "d";
        //
        // or it could be a function "f" applied to two term
        // arguments "a<b" and "c>(d)".

        // We prefer the type-argument interpretation if it is possible.
        // Otherwise we backtrack to the current token and carry on.

        const struct Token * backtrack_token = state->token;

        struct TypeList *tyargs;
        struct Location loc = base_term->location;
        if (parse_type_list(state, false, &tyargs, &loc)) {
            if (tyargs == NULL) {
                // empty list <>, ignore it
                return base_term;
            } else {
                struct Term *tyapp = make_term(loc, TM_TYAPP);
                tyapp->tyapp.lhs = base_term;
                tyapp->tyapp.tyargs = tyargs;
                return tyapp;
            }
        } else {
            // no luck, backtrack
            state->token = backtrack_token;
            return base_term;
        }

    } else {
        return base_term;
    }
}

// Assumption: current token is '{'.
// Parses { term with name=term, term, name=term, ... }
// (the "with" is optional).
// Returns the parsed NameTermList, sets end of loc,
// and writes the term appearing before "with" (if any) into *with
// (which should be NULL initially).
static struct NameTermList * parse_name_term_list(struct ParserState *state,
                                                  struct Location *loc,
                                                  struct Term **with)
{
    advance(state);

    struct NameTermList *list = NULL;
    struct NameTermList **next_ptr = &list;

    while (state->token->type != TOK_RBRACE) {

        if (list != NULL) {
            expect(state, TOK_COMMA, "',' or '}'");
        }

        struct Location field_loc = state->token->location;
        const char *field_name = NULL;

        if (state->token->type == TOK_NAME
        && state->token->next
        && state->token->next->type == TOK_EQUAL) {

            field_name = copy_string(state->token->data);

            advance(state);
            advance(state);
        }

        struct Term *initialiser = parse_term(state, true);

        if (initialiser == NULL) {
            // parse error
            free((void*)field_name);
            break;
        }

        set_location_end(&field_loc, &initialiser->location);

        if (state->token->type == TOK_KW_WITH) {
            if (list != NULL || field_name != NULL || *with) {
                // parse error, "with" not expected here
                report_error(state, state->token->location, "incorrect use of 'with'");
                free_term(initialiser);
                free((void*)field_name);
                break;
            }
            *with = initialiser;
            advance(state);
            continue;
        }

        
        struct NameTermList *node = alloc(sizeof(struct NameTermList));
        node->location = field_loc;
        node->name = field_name;
        node->term = initialiser;
        node->next = NULL;

        *next_ptr = node;
        next_ptr = &node->next;
    }

    set_location_end(loc, &state->token->location);
    advance(state);

    return list;
}

// assumption: current token is '(' or '['
// returns the parsed OpTermList (setting operator to BINOP_PLUS) and also
// sets end of loc
static struct OpTermList * parse_term_list(struct ParserState *state, struct Location *loc)
{
    enum TokenType ending_token = TOK_RPAREN;
    const char *msg = "',' or ')'";
    if (state->token->type == TOK_LBRACKET) {
        ending_token = TOK_RBRACKET;
        msg = "',' or ']'";
    }

    advance(state);

    struct OpTermList *list = NULL;
    struct OpTermList **next_ptr = &list;

    while (state->token->type != ending_token) {

        if (list != NULL) {
            expect(state, TOK_COMMA, msg);
        }

        struct Term *term = parse_term(state, true);

        if (term == NULL) {
            break;
        }

        struct OpTermList *node = alloc(sizeof(struct OpTermList));
        node->operator = BINOP_PLUS;   // dummy value
        node->rhs = term;
        node->next = NULL;
        *next_ptr = node;
        next_ptr = &node->next;
    }

    set_location_end(loc, &state->token->location);
    advance(state);

    return list;
}

static struct Term * parse_paren_term(struct ParserState *state)
{
    struct Location loc = state->token->location;
    expect(state, TOK_LPAREN, "'('");

    struct Term * term = parse_term(state, true);
    if (!term) {
        return NULL;
    }

    const struct Token * rparen_tok = expect(state, TOK_RPAREN, "')'");
    term->location = loc;
    if (rparen_tok) {
        set_location_end(&term->location, &rparen_tok->location);
    }
    return term;
}

static struct Term * parse_atomic_expr(struct ParserState *state, bool allow_lbrace)
{
    enum TokenType tag = state->token->type;
    struct Location loc = state->token->location;

    switch (tag) {

    case TOK_KW_IF:
        {
            advance(state);
            struct Term *new_term = make_term(loc, TM_IF);

            new_term->if_data.cond = parse_term(state, true);
            expect(state, TOK_KW_THEN, "'then'");
            new_term->if_data.then_branch = parse_term(state, true);
            expect(state, TOK_KW_ELSE, "'else'");
            new_term->if_data.else_branch = parse_term(state, allow_lbrace);

            if (new_term->if_data.else_branch) {
                set_location_end(&new_term->location, &new_term->if_data.else_branch->location);
            }
            return new_term;
        }

    case TOK_KW_MATCH:
        {
            advance(state);
            struct Term *new_term = make_term(loc, TM_MATCH);

            new_term->match.scrutinee = parse_term(state, false);
            expect(state, TOK_LBRACE, "'{'");

            new_term->match.arms = NULL;
            struct Arm **tail = &new_term->match.arms;

            while (state->token->type == TOK_KW_CASE) {
                const struct Location *case_loc = &state->token->location;
                advance(state);
                struct Pattern *p = parse_pattern(state);
                expect(state, TOK_EQUAL_GREATER, "'=>'");
                struct Term *rhs = parse_term(state, true);
                *tail = make_arm(p, rhs, rhs ? &rhs->location : NULL, case_loc);
                tail = &(*tail)->next;
            }

            set_location_end(&new_term->location, &state->token->location);
            expect(state, TOK_RBRACE, "'case' or '}'");

            return new_term;
        }
        break;

    case TOK_KW_LET:
        {
            advance(state);

            const struct Token * name_tok = expect(state, TOK_NAME, "variable name");
            if (!name_tok) {
                return NULL;
            }

            struct Term *new_term = make_term(loc, TM_LET);
            new_term->let.name = copy_string(name_tok->data);
            expect(state, TOK_EQUAL, "'='");
            new_term->let.rhs = parse_term(state, true);
            expect(state, TOK_KW_IN, "'in'");
            new_term->let.body = parse_term(state, allow_lbrace);

            if (new_term->let.body) {
                set_location_end(&new_term->location, &new_term->let.body->location);
            }
            return new_term;
        }

    case TOK_KW_FORALL:
    case TOK_KW_EXISTS:
        {
            advance(state);
            expect(state, TOK_LPAREN, "'('");

            const struct Token *name_tok = expect(state, TOK_NAME, "variable name");
            if (!name_tok) {
                return NULL;
            }

            expect(state, TOK_COLON, "':'");

            struct Type *type = parse_type(state, true);

            expect(state, TOK_RPAREN, "')'");

            struct Term *term = parse_term(state, allow_lbrace);

            struct Term *new_term = make_term(loc, TM_QUANTIFIER);
            new_term->quant.quant = (tag == TOK_KW_FORALL ? QUANT_FORALL : QUANT_EXISTS);
            new_term->quant.name = copy_string(name_tok->data);
            new_term->quant.type = type;
            new_term->quant.body = term;

            if (term) {
                set_location_end(&new_term->location, &term->location);
            }
            return new_term;
        }

    case TOK_INT_LITERAL:
        {
            const char *data = state->token->data;
            advance(state);
            return make_int_literal_term(loc, data);
        }

    case TOK_STRING_LITERAL:
        {
            const uint8_t *data = (const uint8_t*) state->token->data;
            uint32_t length = state->token->length;
            advance(state);
            return make_string_literal_term(loc, data, length);
        }

    case TOK_KW_I8:
    case TOK_KW_I16:
    case TOK_KW_I32:
    case TOK_KW_I64:
    case TOK_KW_U8:
    case TOK_KW_U16:
    case TOK_KW_U32:
    case TOK_KW_U64:
    case TOK_KW_INT:
    case TOK_KW_REAL:
        {
            struct Type *type = parse_type(state, true);  // will succeed
            struct Term *operand = parse_paren_term(state);

            struct Term *result = make_term(loc, TM_CAST);
            result->cast.target_type = type;
            result->cast.operand = operand;

            if (operand) {
                set_location_end(&result->location, &operand->location);
            }
            return result;
        }
        break;

    case TOK_KW_FALSE:
        advance(state);
        return make_bool_literal_term(loc, false);

    case TOK_KW_TRUE:
        advance(state);
        return make_bool_literal_term(loc, true);

    case TOK_NAME:
        {
            const char *data = state->token->data;
            advance(state);
            struct Term *term = make_var_term(loc, data);
            term->var.postcond_new = state->postcondition && !state->old;
            return parse_tyarg_suffix(state, term);
        }

    case TOK_KW_RETURN:
        {
            if (state->old) {
                report_error(state, loc, "cannot use 'old' with 'return'");
                return NULL;
            }
            advance(state);
            struct Term *term = make_var_term(loc, "return");
            term->var.postcond_new = true;
            return term;
        }

    case TOK_KW_OLD:
        {
            if (!state->postcondition) {
                report_error(state, loc, "'old' only allowed in postconditions");
                return NULL;
            }
            advance(state);
            state->old = true;
            struct Term *term = parse_paren_term(state);
            state->old = false;
            return term;
        }

    case TOK_LPAREN:
        return parse_paren_term(state);

    case TOK_LBRACE:
        {
            struct Term *with = NULL;
            struct NameTermList *fields = parse_name_term_list(state, &loc, &with);

            struct Term *result;

            if (with) {
                result = make_term(loc, TM_RECORD_UPDATE);
                result->record_update.lhs = with;
                result->record_update.fields = fields;
            } else {
                result = make_term(loc, TM_RECORD);
                result->record.fields = fields;
            }

            return result;
        }

    case TOK_LBRACKET:
        {
            struct OpTermList *terms = parse_term_list(state, &loc);
            struct Term *result = make_term(loc, TM_ARRAY_LITERAL);
            result->array_literal.terms = terms;
            return result;
        }
        break;

    case TOK_KW_SIZEOF:
        {
            advance(state);
            struct Term *term = parse_paren_term(state);
            set_location_end(&loc, &term->location);
            struct Term *result = make_term(loc, TM_SIZEOF);
            result->sizeof_data.rhs = term;
            return result;
        }

    case TOK_KW_ALLOCATED:
        {
            advance(state);
            struct Term *term = parse_paren_term(state);
            set_location_end(&loc, &term->location);
            struct Term *result = make_term(loc, TM_ALLOCATED);
            result->allocated.rhs = term;
            return result;
        }

    default:
        {
            // failed to parse term
            report_error(state, loc, "expected term");
            return NULL;
        }
    }
}

static struct Term * parse_call_or_proj_expr(struct ParserState *state, bool allow_lbrace)
{
    struct Term *term = parse_atomic_expr(state, allow_lbrace);

    if (!term) {
        return NULL;
    }

    while (true) {
        if (state->token->type == TOK_LPAREN) {
            // Function call

            struct Term *call = make_term(term->location, TM_CALL);
            call->call.func = term;
            call->call.args = parse_term_list(state, &call->location);
            term = call;

        } else if (state->token->type == TOK_LBRACE && allow_lbrace) {

            // f{1,2,3} is parsed as a function call with one tuple
            // argument, like in Lua.

            // This is particularly useful with datatype construction
            // expressions, e.g. it is nice to be able to write
            // Foo { a=1, b=2 } instead of Foo ({ a=1, b=2 }).

            struct Location loc = term->location;
            struct Term * argument = parse_atomic_expr(state, true);
            set_location_end(&loc, &argument->location);

            struct Term *call = make_term(loc, TM_CALL);
            call->call.func = term;
            call->call.args = alloc(sizeof(struct OpTermList));
            call->call.args->operator = BINOP_PLUS;  // dummy value
            call->call.args->rhs = argument;
            call->call.args->next = NULL;

            term = call;

        } else if (state->token->type == TOK_DOT) {
            // Field projection
            advance(state);

            if (state->token->type != TOK_NAME && state->token->type != TOK_INT_LITERAL) {
                report_error(state, state->token->location, "expected name");
                free_term(term);
                return NULL;
            }

            struct Term *new_term = make_term(term->location, TM_FIELD_PROJ);
            set_location_end(&new_term->location, &state->token->location);
            new_term->field_proj.lhs = term;
            new_term->field_proj.field_name = copy_string(state->token->data);

            advance(state);

            term = parse_tyarg_suffix(state, new_term);

        } else if (state->token->type == TOK_LBRACKET) {
            // Array projection

            struct Term * proj = make_term(term->location, TM_ARRAY_PROJ);
            proj->array_proj.lhs = term;
            proj->array_proj.indexes = parse_term_list(state, &proj->location);
            term = proj;

        } else {
            break;
        }
    }

    return term;
}

static struct Term * parse_unop_expr(struct ParserState *state, bool allow_lbrace)
{
    enum TokenType tok = state->token->type;
    struct Location loc = state->token->location;

    if (tok == TOK_MINUS || tok == TOK_TILDE || tok == TOK_EXCLAM) {
        advance(state);
        struct Term *rhs = parse_unop_expr(state, allow_lbrace);
        if (rhs) {
            set_location_end(&loc, &rhs->location);

            if (tok == TOK_MINUS && rhs->tag == TM_INT_LITERAL && rhs->int_literal.data[0] != '-') {
                // Optimise unary minus applied to an int literal.
                // (The alternative is to keep the term as a TM_UNOP
                // applied to a TM_INT_LITERAL, but this causes
                // problems when trying to write the most negative
                // integer as a literal.)
                char *new_data = copy_string_2("-", rhs->int_literal.data);
                free((char*)rhs->int_literal.data);
                rhs->int_literal.data = new_data;
                rhs->location = loc;
                return rhs;
            }
        }

        // Make a TM_UNOP term.
        struct Term *result = make_term(loc, TM_UNOP);
        switch (tok) {
        case TOK_MINUS: result->unop.operator = UNOP_NEGATE; break;
        case TOK_TILDE: result->unop.operator = UNOP_COMPLEMENT; break;
        default: result->unop.operator = UNOP_NOT; break;
        }
        result->unop.operand = rhs;
        return result;

    } else {
        return parse_call_or_proj_expr(state, allow_lbrace);
    }
}

static bool can_chain(struct OpTermList *end_of_chain, enum BinOp new_op)
{
    if (end_of_chain == NULL) {
        return false;
    }

    switch (end_of_chain->operator) {
    case BINOP_LESS:
    case BINOP_LESS_EQUAL:
    case BINOP_EQUAL:
    case BINOP_NOT_EQUAL:
    case BINOP_GREATER:
    case BINOP_GREATER_EQUAL:
        return new_op == BINOP_LESS
            || new_op == BINOP_LESS_EQUAL
            || new_op == BINOP_GREATER
            || new_op == BINOP_GREATER_EQUAL
            || new_op == BINOP_EQUAL
            || new_op == BINOP_NOT_EQUAL;

    case BINOP_IMPLIES:
    case BINOP_IMPLIED_BY:
        // ==> and <== do not chain (they associate) but it is convenient to parse
        // them as if they chain, and then we can remove the chaining again in the
        // typechecker. (The typechecker will also check whether the "direction" is
        // consistent, e.g. A <== B ==> C is disallowed.)
        return new_op == BINOP_IMPLIES
            || new_op == BINOP_IMPLIED_BY;

    default:
        return false;
    }
}

static struct Term * parse_operators(struct ParserState *state, int precedence, bool allow_lbrace)
{
    if (precedence > MAX_PRECEDENCE) {
        // base case
        return parse_unop_expr(state, allow_lbrace);
    }

    // normal binary operator

    struct Term * term = parse_operators(state, precedence + 1, allow_lbrace);
    struct OpTermList * end_of_chain = NULL;

    while (1) {
        // see if we found an operator at this precedence level
        struct OpData * op_data = &operators[state->token->type];

        if (op_data->precedence == precedence) {

            advance(state);

            // parse the rhs expression. using precedence + 1 gives left associativity.
            struct Term *rhs_term = parse_operators(state, precedence + 1, allow_lbrace);

            if (can_chain(end_of_chain, op_data->operator)) {
                struct OpTermList *new_list = alloc(sizeof(struct OpTermList));
                new_list->operator = op_data->operator;
                new_list->rhs = rhs_term;
                new_list->next = NULL;
                end_of_chain->next = new_list;
                end_of_chain = new_list;

            } else {
                struct Term *new_term = alloc(sizeof(struct Term));
                new_term->location = term ? term->location : g_no_location;
                new_term->type = NULL;
                new_term->tag = TM_BINOP;
                new_term->binop.lhs = term;
                new_term->binop.list = alloc(sizeof(struct OpTermList));
                new_term->binop.list->operator = op_data->operator;
                new_term->binop.list->rhs = rhs_term;
                new_term->binop.list->next = NULL;
                term = new_term;
                end_of_chain = new_term->binop.list;
            }

            if (rhs_term) {
                set_location_end(&term->location, &rhs_term->location);
            }

            // Continue searching as there could be further operators/terms
            // at this precedence level (e.g. 1 + 2 + 3 + 4)

        } else {
            // No further operators found; break out of loop.
            break;
        }
    }

    return term;
}

static struct Term * parse_term(struct ParserState *state, bool allow_lbrace)
{
    return parse_operators(state, 1, allow_lbrace);
}


// -----------------------------------------------------------------------------

//
// Attribute Parsing
//

static struct Attribute * parse_attributes(struct ParserState *state)
{
    struct Attribute *result = NULL;
    struct Attribute **next_ptr = &result;

    while (true) {
        switch (state->token->type) {
        case TOK_KW_REQUIRES:
        case TOK_KW_ENSURES:
        case TOK_KW_INVARIANT:
        case TOK_KW_DECREASES:
            {
                struct Attribute *attr = alloc(sizeof(struct Attribute));
                attr->location = state->token->location;

                switch (state->token->type) {
                case TOK_KW_REQUIRES:
                    attr->tag = ATTR_REQUIRES;
                    break;

                case TOK_KW_ENSURES:
                    attr->tag = ATTR_ENSURES;
                    state->postcondition = true;
                    break;

                case TOK_KW_INVARIANT:
                    attr->tag = ATTR_INVARIANT;
                    break;

                case TOK_KW_DECREASES:
                    attr->tag = ATTR_DECREASES;
                    break;

                default:
                    // impossible
                    break;
                }

                attr->next = NULL;

                advance(state);
                attr->term = parse_term(state, true);
                if (attr->term) {
                    set_location_end(&attr->location, &attr->term->location);
                }

                expect(state, TOK_SEMICOLON, "';'");

                state->postcondition = false;

                *next_ptr = attr;
                next_ptr = &attr->next;
            }
            break;

        default:
            // Reached the end of the attribute list
            return result;
        }
    }
}


// -----------------------------------------------------------------------------

//
// Statement Parsing
//

static struct Statement * parse_statements(struct ParserState *state);

static struct Statement * parse_var_decl_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    bool ref = (state->token->type == TOK_KW_REF);
    advance(state);

    const struct Token * name_tok = expect(state, TOK_NAME, "variable name");
    if (!name_tok) {
        return NULL;
    }

    struct Type *type = NULL;
    if (state->token->type == TOK_COLON) {
        advance(state);
        type = parse_type(state, true);
        if (type) {
            set_location_end(&loc, &type->location);
        }
    }

    struct Term *rhs = NULL;

    if (state->token->type == TOK_EQUAL) {
        advance(state);
        rhs = parse_term(state, true);
        if (rhs) {
            set_location_end(&loc, &rhs->location);
        }
    } else if (ref) {
        report_error(state, state->token->location, "expected '='");
        free_type(type);
        return NULL;
    }

    expect(state, TOK_SEMICOLON, "';'");

    struct Statement *stmt = make_statement(loc, ST_VAR_DECL);
    stmt->var_decl.name = copy_string(name_tok->data);
    stmt->var_decl.type = type;
    stmt->var_decl.rhs = rhs;
    stmt->var_decl.ref = ref;
    return stmt;
}

static struct Statement * parse_fix_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);

    const struct Token * name_tok = expect(state, TOK_NAME, "variable name");
    if (!name_tok) {
        return NULL;
    }

    expect(state, TOK_COLON, "':'");
    struct Type *type = parse_type(state, true);
    if (type) {
        set_location_end(&loc, &type->location);
    }

    expect(state, TOK_SEMICOLON, "';'");

    struct Statement *stmt = make_statement(loc, ST_FIX);
    stmt->fix.name = copy_string(name_tok->data);
    stmt->fix.type = type;
    return stmt;
}

static struct Statement * parse_obtain_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);

    expect(state, TOK_LPAREN, "'('");

    const struct Token * name_tok = expect(state, TOK_NAME, "variable name");
    if (!name_tok) {
        return NULL;
    }

    expect(state, TOK_COLON, "':'");
    struct Type *type = parse_type(state, true);

    expect(state, TOK_RPAREN, "')'");

    struct Term *cond = parse_term(state, true);
    if (cond) {
        set_location_end(&loc, &cond->location);
    }

    expect(state, TOK_SEMICOLON, "';'");

    struct Statement *stmt = make_statement(loc, ST_OBTAIN);
    stmt->obtain.name = copy_string(name_tok->data);
    stmt->obtain.type = type;
    stmt->obtain.condition = cond;
    return stmt;
}

static struct Statement * parse_use_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);
    struct Term *term = parse_term(state, true);
    if (term) {
        set_location_end(&loc, &term->location);
    }
    expect(state, TOK_SEMICOLON, "';'");

    struct Statement *stmt = make_statement(loc, ST_USE);
    stmt->use.term = term;
    return stmt;
}

static struct Statement * parse_swap_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);

    struct Term *lhs = parse_term(state, true);
    expect(state, TOK_COMMA, "','");

    struct Term *rhs = parse_term(state, true);
    if (rhs) {
        set_location_end(&loc, &rhs->location);
    }
    expect(state, TOK_SEMICOLON, "';'");

    struct Statement *stmt = make_statement(loc, ST_SWAP);
    stmt->swap.lhs = lhs;
    stmt->swap.rhs = rhs;
    return stmt;
}

static struct Statement * parse_return_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);

    struct Term *term = NULL;
    if (state->token->type != TOK_SEMICOLON) {
        term = parse_term(state, true);
        if (term) {
            set_location_end(&loc, &term->location);
        }
    }

    expect(state, TOK_SEMICOLON, "';'");

    struct Statement *stmt = make_statement(loc, ST_RETURN);
    stmt->ret.value = term;
    return stmt;
}

static struct Statement * parse_assignment_or_call_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;

    // a function-call or assignment must start with one of the following
    if (state->token->type != TOK_NAME && state->token->type != TOK_LPAREN) {
        report_error(state, loc, "expected statement");
        return NULL;
    }

    struct Term * lhs = parse_term(state, true);

    if (state->token->type == TOK_EQUAL) {
        advance(state);
        struct Term * rhs = parse_term(state, true);
        expect(state, TOK_SEMICOLON, "';'");
        struct Statement *stmt = make_statement(loc, ST_ASSIGN);
        if (rhs) {
            set_location_end(&stmt->location, &rhs->location);
        }
        stmt->assign.lhs = lhs;
        stmt->assign.rhs = rhs;
        return stmt;

    } else if (lhs && lhs->tag == TM_CALL) {
        expect(state, TOK_SEMICOLON, "';'");
        struct Statement *stmt = make_statement(loc, ST_CALL);
        stmt->call.term = lhs;
        return stmt;

    } else if (lhs) {
        report_error(state, loc, "expected statement");
        free_term(lhs);
        return NULL;

    } else {
        return NULL;
    }
}

static struct Statement * parse_assert_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);
    struct Term *term = parse_term(state, false);
    if (term) {
        set_location_end(&loc, &term->location);
    }

    struct Statement *proof = NULL;
    if (state->token->type == TOK_LBRACE) {
        advance(state);
        proof = parse_statements(state);
        const struct Token *tok_end = expect(state, TOK_RBRACE, "statement or '}'");
        if (tok_end) {
            set_location_end(&loc, &tok_end->location);
        }
    } else {
        expect(state, TOK_SEMICOLON, "';'");
    }

    struct Statement *stmt = make_statement(loc, ST_ASSERT);
    stmt->assert_data.condition = term;
    stmt->assert_data.proof = proof;
    return stmt;
}

static struct Statement * parse_assume_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);
    struct Term *term = parse_term(state, true);
    if (term) {
        set_location_end(&loc, &term->location);
    }

    struct Statement *stmt = make_statement(loc, ST_ASSUME);
    stmt->assume.condition = term;
    return stmt;
}

static struct Statement * parse_if_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);
    struct Term *term = parse_term(state, false);

    expect(state, TOK_LBRACE, "'{'");
    struct Statement *then_block = parse_statements(state);
    const struct Token *tok_end = expect(state, TOK_RBRACE, "statement or '}'");
    if (tok_end) set_location_end(&loc, &tok_end->location);

    struct Statement *else_block = NULL;
    if (state->token->type == TOK_KW_ELSE) {
        advance(state);

        if (state->token->type == TOK_KW_IF) {
            else_block = parse_if_stmt(state);
            if (else_block) set_location_end(&loc, &else_block->location);
        } else {
            expect(state, TOK_LBRACE, "'{'");
            else_block = parse_statements(state);
            tok_end = expect(state, TOK_RBRACE, "statement or '}'");
            if (tok_end) set_location_end(&loc, &tok_end->location);
        }
    }

    struct Statement *stmt = make_statement(loc, ST_IF);
    stmt->if_data.condition = term;
    stmt->if_data.then_block = then_block;
    stmt->if_data.else_block = else_block;
    return stmt;
}

static struct Statement * parse_while_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);
    struct Term *term = parse_term(state, false);

    struct Attribute *attributes = parse_attributes(state);

    expect(state, TOK_LBRACE, "'{'");
    struct Statement *body = parse_statements(state);

    const struct Token *tok_end = expect(state, TOK_RBRACE, "'}'");
    if (tok_end) {
        set_location_end(&loc, &tok_end->location);
    }

    struct Statement *stmt = make_statement(loc, ST_WHILE);
    stmt->while_data.condition = term;
    stmt->while_data.attributes = attributes;
    stmt->while_data.body = body;
    return stmt;
}

static struct Statement * parse_match_stmt(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);

    struct Statement *new_stmt = make_statement(loc, ST_MATCH);

    new_stmt->match.scrutinee = parse_term(state, false);
    expect(state, TOK_LBRACE, "'{'");

    new_stmt->match.arms = NULL;
    struct Arm **tail = &new_stmt->match.arms;

    while (state->token->type == TOK_KW_CASE) {
        const struct Location *case_loc = &state->token->location;
        advance(state);
        struct Pattern *p = parse_pattern(state);
        expect(state, TOK_EQUAL_GREATER, "'=>'");
        struct Statement *rhs = parse_statements(state);
        *tail = make_arm(p, rhs, rhs ? &rhs->location : NULL, case_loc);
        tail = &(*tail)->next;
    }

    set_location_end(&new_stmt->location, &state->token->location);
    expect(state, TOK_RBRACE, "'case' or '}'");

    return new_stmt;
}

static struct Statement * parse_show_hide_stmt(struct ParserState *state)
{
    bool show = (state->token->type == TOK_KW_SHOW);

    struct Location loc = state->token->location;
    advance(state);

    const struct Token *tok_name = expect(state, TOK_NAME, "name");
    if (!tok_name) return NULL;

    // allow dotted names
    const struct Token *tok_name_2 = NULL;
    if (state->token->type == TOK_DOT) {
        advance(state);
        tok_name_2 = expect(state, TOK_NAME, "name");
    }

    expect(state, TOK_SEMICOLON, "';'");

    struct Statement *new_stmt = make_statement(loc, ST_SHOW_HIDE);
    if (tok_name_2) {
        new_stmt->show_hide.name = copy_string_3(tok_name->data, ".", tok_name_2->data);
    } else {
        new_stmt->show_hide.name = copy_string(tok_name->data);
    }
    new_stmt->show_hide.show = show;

    return new_stmt;
}

static struct Statement * parse_statement(struct ParserState *state)
{
    bool ghost = false;
    if (state->token->type == TOK_KW_GHOST) {
        ghost = true;
        advance(state);
    }

    struct Statement *stmt = NULL;

    switch (state->token->type) {
    case TOK_KW_VAR:
    case TOK_KW_REF:
        stmt = parse_var_decl_stmt(state);
        break;

    case TOK_KW_FIX:
        stmt = parse_fix_stmt(state);
        break;

    case TOK_KW_OBTAIN:
        stmt = parse_obtain_stmt(state);
        break;

    case TOK_KW_USE:
        stmt = parse_use_stmt(state);
        break;

    case TOK_KW_SWAP:
        stmt = parse_swap_stmt(state);
        break;

    case TOK_KW_RETURN:
        stmt = parse_return_stmt(state);
        break;

    case TOK_KW_ASSERT:
        stmt = parse_assert_stmt(state);
        break;

    case TOK_KW_ASSUME:
        stmt = parse_assume_stmt(state);
        break;

    case TOK_KW_IF:
        stmt = parse_if_stmt(state);
        break;

    case TOK_KW_WHILE:
        stmt = parse_while_stmt(state);
        break;

    case TOK_KW_MATCH:
        stmt = parse_match_stmt(state);
        break;

    case TOK_KW_SHOW:
    case TOK_KW_HIDE:
        stmt = parse_show_hide_stmt(state);
        break;

    default:
        stmt = parse_assignment_or_call_stmt(state);
        break;
    }

    if (stmt) {
        stmt->ghost = ghost;
    }

    return stmt;
}

static struct Statement * parse_statements(struct ParserState *state)
{
    struct Statement * result = NULL;
    struct Statement ** next_ptr = &result;

    while (state->token->type != TOK_RBRACE && state->token->type != TOK_KW_CASE) {

        if (state->token->type == TOK_SEMICOLON) {
            advance(state);
            continue;
        }

        struct Statement *stmt = parse_statement(state);
        if (stmt == NULL) {
            break;
        }
        *next_ptr = stmt;
        next_ptr = &stmt->next;
    }

    return result;
}


// -----------------------------------------------------------------------------

//
// Declaration Parsing
//

static struct Decl * parse_const_decl(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);

    const struct Token *name_tok = expect(state, TOK_NAME, "constant name");
    if (!name_tok) {
        return NULL;
    }

    char *name = copy_string(name_tok->data);
    set_location_end(&loc, &name_tok->location);

    struct Type *type = NULL;

    if (state->token->type == TOK_COLON) {
        advance(state);
        type = parse_type(state, true);
        if (type) {
            set_location_end(&loc, &type->location);
        }
    }

    struct Term *rhs = NULL;

    if (state->token->type == TOK_EQUAL) {
        advance(state);
        rhs = parse_term(state, true);
        if (rhs) {
            set_location_end(&loc, &rhs->location);
        }
    }

    expect(state, TOK_SEMICOLON, "';'");

    struct Decl *result = alloc(sizeof(struct Decl));
    result->location = loc;
    result->name = name;
    result->tag = DECL_CONST;
    result->const_data.type = type;
    result->const_data.rhs = rhs;
    result->const_data.value = NULL;
    result->attributes = NULL;
    result->next = NULL;
    result->recursive = false;

    return result;
}

static struct TyVarList *parse_tyvar_list(struct ParserState *state)
{
    if (state->token->type != TOK_LESS) {
        return NULL;
    }
    advance(state);

    struct TyVarList * result = NULL;
    struct TyVarList ** next_ptr = &result;
    bool first = true;

    while (true) {
        if (state->token->type == TOK_GREATER) {
            advance(state);
            break;
        }

        if (!first) {
            expect(state, TOK_COMMA, "',' or '>'");
        }

        const struct Token *name_tok = expect(state, TOK_NAME, "type variable name");
        if (!name_tok) {
            break;
        }

        struct TyVarList * tyvar = alloc(sizeof(struct TyVarList));
        tyvar->name = copy_string(name_tok->data);
        tyvar->next = NULL;
        *next_ptr = tyvar;
        next_ptr = &tyvar->next;
        first = false;
    }

    return result;
}

static struct FunArg * parse_fun_args_and_rparen(struct ParserState *state, struct Location *loc)
{
    struct FunArg * result = NULL;
    struct FunArg ** next_ptr = &result;
    bool first = true;

    while (true) {
        if (state->token->type == TOK_RPAREN) {
            set_location_end(loc, &state->token->location);
            advance(state);
            break;
        }

        if (!first) {
            expect(state, TOK_COMMA, "',' or ')'");
        }

        bool ref = false;
        if (state->token->type == TOK_KW_REF) {
            ref = true;
            advance(state);
        }

        const struct Token *name_tok = expect(state, TOK_NAME, "argument name");
        if (!name_tok) {
            break;
        }

        expect(state, TOK_COLON, "':'");

        struct Type *type = parse_type(state, true);

        struct FunArg * funarg = alloc(sizeof(struct FunArg));
        funarg->name = copy_string(name_tok->data);
        funarg->type = type;
        funarg->ref = ref;
        funarg->next = NULL;
        *next_ptr = funarg;
        next_ptr = &funarg->next;
        first = false;
    }

    return result;
}

static struct Decl * parse_function_decl(struct ParserState *state, bool is_extern)
{
    struct Location loc = state->token->location;
    advance(state);

    const struct Token *name_tok = expect(state, TOK_NAME, "name");
    if (!name_tok) {
        return NULL;
    }

    struct TyVarList *tyvars = parse_tyvar_list(state);

    expect(state, TOK_LPAREN, "'('");

    struct FunArg *args = parse_fun_args_and_rparen(state, &loc);

    struct Type *return_type = NULL;
    if (state->token->type == TOK_COLON) {
        advance(state);
        return_type = parse_type(state, true);
        if (return_type) {
            set_location_end(&loc, &return_type->location);
        }
    }

    // optional semicolon after the return type (even if there are
    // attributes or a body)
    if (state->token->type == TOK_SEMICOLON) {
        advance(state);
    }

    struct Attribute *attrs = parse_attributes(state);

    struct Statement *body = NULL;
    bool body_specified = false;
    struct Location end_loc = g_no_location;
    if (state->token->type == TOK_LBRACE) {
        advance(state);
        body = parse_statements(state);
        body_specified = true;
        const struct Token *end_tok = expect(state, TOK_RBRACE, "statement or '}'");
        if (end_tok) {
            set_location_end(&loc, &end_tok->location);
            end_loc = end_tok->location;
        }
    }

    struct Decl * result = alloc(sizeof(struct Decl));
    result->location = loc;
    result->name = copy_string(name_tok->data);
    result->tag = DECL_FUNCTION;
    result->function_data.tyvars = tyvars;
    result->function_data.args = args;
    result->function_data.return_type = return_type;
    result->function_data.body = body;
    result->function_data.body_specified = body_specified;
    result->function_data.end_loc = end_loc;
    result->function_data.is_extern = is_extern;
    result->attributes = attrs;
    result->next = NULL;
    result->recursive = false;

    return result;
}

static struct DataCtor * parse_data_ctors(struct ParserState *state,
                                          struct Location *loc)
{
    struct DataCtor * result = NULL;
    struct DataCtor ** tail_ptr = &result;

    while (true) {

        const struct Token * name_tok = expect(state, TOK_NAME, "data constructor name");
        if (name_tok) {
            struct Location ctor_loc = name_tok->location;
            set_location_end(loc, &ctor_loc);

            if (!isupper(name_tok->data[0])) {
                report_error(state, name_tok->location, "data constructor names must begin with an uppercase letter");
            }

            struct Type *payload = NULL;

            bool paren = false;
            bool have_payload = false;
            if (state->token->type == TOK_LPAREN) {
                have_payload = paren = true;
                advance(state);
            } else if (state->token->type == TOK_LBRACE) {
                have_payload = true;
            }

            if (have_payload) {
                payload = parse_type(state, true);
                if (payload) set_location_end(&ctor_loc, &payload->location);
            }

            if (paren) {
                expect(state, TOK_RPAREN, "')'");
            }

            struct DataCtor *ctor = alloc(sizeof(struct DataCtor));
            ctor->location = ctor_loc;
            ctor->name = copy_string(name_tok->data);
            ctor->payload = payload;
            ctor->next = NULL;

            *tail_ptr = ctor;
            tail_ptr = &ctor->next;
        }

        if (state->token->type == TOK_BAR) {
            advance(state);
        } else {
            break;
        }
    }

    return result;
}

static struct Decl * parse_datatype_decl(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);

    const struct Token *name_tok = expect(state, TOK_NAME, "name");
    if (!name_tok) {
        return NULL;
    }

    struct TyVarList *tyvars = parse_tyvar_list(state);

    expect(state, TOK_EQUAL, "'='");

    struct DataCtor * ctors = parse_data_ctors(state, &loc);

    expect(state, TOK_SEMICOLON, "';'");

    struct Decl * result = alloc(sizeof(struct Decl));
    result->location = loc;
    result->name = copy_string(name_tok->data);
    result->tag = DECL_DATATYPE;
    result->datatype_data.tyvars = tyvars;
    result->datatype_data.ctors = ctors;
    result->attributes = NULL;
    result->next = NULL;
    result->recursive = false;

    return result;
}

static struct Decl * parse_typedef_decl(struct ParserState *state)
{
    struct Location loc = state->token->location;
    advance(state);

    const struct Token *name_tok = expect(state, TOK_NAME, "name");
    if (!name_tok) {
        return NULL;
    }

    struct TyVarList *tyvars = parse_tyvar_list(state);

    struct Type *rhs = NULL;
    bool allocated = false;
    if (state->token->type == TOK_EQUAL) {
        advance(state);
        rhs = parse_type(state, true);

    } else if (state->token->type == TOK_LPAREN) {
        allocated = true;
        advance(state);
        expect(state, TOK_KW_ALLOCATED, "'allocated'");
        expect(state, TOK_RPAREN, "')'");
    }

    expect(state, TOK_SEMICOLON, "';'");

    struct Decl * result = alloc(sizeof(struct Decl));
    result->location = loc;
    result->name = copy_string(name_tok->data);
    result->tag = DECL_TYPEDEF;
    result->typedef_data.tyvars = tyvars;
    result->typedef_data.rhs = rhs;
    result->typedef_data.allocated = allocated;
    result->attributes = NULL;
    result->next = NULL;
    result->recursive = false;

    return result;
}

static struct Decl * parse_decl(struct ParserState *state)
{
    bool ghost = false;
    if (state->token->type == TOK_KW_GHOST) {
        ghost = true;
        advance(state);
    }

    bool extern_function = false;

    struct Decl *decl = NULL;

    switch (state->token->type) {
    case TOK_KW_CONST:
        decl = parse_const_decl(state);
        break;

    case TOK_KW_EXTERN:
        // currently "extern" can only precede "function"
        advance(state);
        if (state->token->type != TOK_KW_FUNCTION) {
            expect(state, TOK_KW_FUNCTION, "'function'");  // print error message
            return NULL;
        }
        extern_function = true;
        // Fall through

    case TOK_KW_FUNCTION:
        decl = parse_function_decl(state, extern_function);
        break;

    case TOK_KW_DATATYPE:
        decl = parse_datatype_decl(state);
        break;

    case TOK_KW_TYPE:
        decl = parse_typedef_decl(state);
        break;

    default:
        break;
    };

    if (decl) {
        decl->ghost = ghost;
    }

    return decl;
}

static struct DeclGroup * parse_decls(struct ParserState *state)
{
    struct DeclGroup * result = alloc(sizeof(struct DeclGroup));
    result->decl = NULL;
    result->next = NULL;
    struct Decl ** tail_link = &result->decl;

    while (true) {

        sha256_init(&state->sha256_decl);
        const char *decl_string = "DECL";
        sha256_add_bytes(&state->sha256_decl, (const uint8_t*)decl_string, strlen(decl_string)+1);

        struct Decl * decl = parse_decl(state);

        if (decl == NULL) {
            break;
        } else {
            sha256_final(&state->sha256_decl, decl->checksum);
            decl->dependency_names = NULL;
            *tail_link = decl;
            tail_link = &decl->next;
        }
    }

    if (result->decl == NULL) {
        free_decl_group(result);
        return NULL;
    } else {
        return result;
    }
}


// -----------------------------------------------------------------------------

//
// Import Parsing
//

static struct Import * parse_imports(struct ParserState *state)
{
    struct Import *list = NULL;
    struct Import **tail_ptr = &list;

    while (state->token->type == TOK_KW_IMPORT) {

        struct Location loc = state->token->location;
        advance(state);

        const struct Token *name_tok = expect(state, TOK_NAME, "module name or 'qualified'");
        if (!name_tok) {
            return NULL;
        }

        // 'qualified' is not a keyword, it is just a name that has a
        // special meaning in this context (only)
        bool qualified = false;
        if (strcmp(name_tok->data, "qualified") == 0) {
            qualified = true;
            name_tok = expect(state, TOK_NAME, "module name");
            if (!name_tok) {
                return NULL;
            }
        }

        set_location_end(&loc, &name_tok->location);
        const char * name = copy_string(name_tok->data);
        const char * alias_name = NULL;

        if (state->token->type == TOK_KW_AS) {
            advance(state);
            const struct Token *alias_tok = expect(state, TOK_NAME, "module alias name");
            if (alias_tok) {
                alias_name = copy_string(alias_tok->data);
                set_location_end(&loc, &alias_tok->location);
            }
        } else {
            alias_name = copy_string(name);
        }

        expect(state, TOK_SEMICOLON, "';'");

        struct Import *import = alloc(sizeof(struct Import));
        import->location = loc;
        import->module_name = name;
        import->alias_name = alias_name;
        import->qualified = qualified;
        import->next = NULL;
        *tail_ptr = import;
        tail_ptr = &import->next;
    }

    return list;
}


// -----------------------------------------------------------------------------

//
// Module Parsing
//

struct Module * parse_module(const struct Token *first_token, bool interface_only)
{
    struct ParserState state;
    state.token = first_token;
    state.error = false;
    state.postcondition = false;
    state.old = false;
    sha256_init(&state.sha256_decl);
    sha256_init(&state.sha256_module);
    const char *mod_int = "MOD-INT";
    sha256_add_bytes(&state.sha256_module, (const uint8_t*)mod_int, strlen(mod_int)+1);

    struct Module * result = alloc(sizeof(struct Module));

    // 'module'
    expect(&state, TOK_KW_MODULE, "'module'");

    // module-name
    const struct Token *name_tok = expect(&state, TOK_NAME, "module name");
    if (name_tok) {
        result->name = copy_string(name_tok->data);
    } else {
        result->name = NULL;
    }

    // interface imports (zero or more)
    result->interface_imports = parse_imports(&state);

    // 'interface' '{'
    // (could technically be optional, but a module with no interface is useless, so
    // we might as well require it)
    expect(&state, TOK_KW_INTERFACE, "'interface'");
    expect(&state, TOK_LBRACE, "'{'");

    // interface decl-list (zero or more decls)
    result->interface = parse_decls(&state);

    // '}'
    expect(&state, TOK_RBRACE, "'}'");

    // pull out interface checksum
    sha256_final(&state.sha256_module, result->interface_checksum);

    // now for the implementation
    result->implementation_imports = NULL;
    result->implementation = NULL;

    bool done = false;

    if (interface_only) {
        // We've been asked to parse only the interface, so we can stop here
        memset(result->implementation_checksum, 0, SHA256_HASH_LENGTH);
        done = true;

    } else {
        // Keep going...

        sha256_init(&state.sha256_module);
        const char *mod_impl = "MOD-IMPL";
        sha256_add_bytes(&state.sha256_module, (const uint8_t*)mod_impl, strlen(mod_impl)+1);

        // imports - zero or more
        result->implementation_imports = parse_imports(&state);

        // main definitions - zero or more
        result->implementation = parse_decls(&state);

        sha256_final(&state.sha256_module, result->implementation_checksum);
    }

    // We should now be at eof (unless 'done' was set above)
    if (!done && state.token->type != TOK_EOF) {
        report_error(&state, state.token->location, NULL);
    }

    if (state.error) {
        free_module(result);
        return NULL;
    } else {
        return result;
    }
}

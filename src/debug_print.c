/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "ast.h"
#include "debug_print.h"
#include "error.h"
#include "op_name.h"

#include <ctype.h>

static void print_term(bool postcond, FILE *file, struct Term *term);

static void print_name_type_list(FILE *file, struct NameTypeList *list)
{
    while (list) {
        fprintf(file, "%s: ", list->name);
        print_type(file, list->type);
        if (list->next) {
            fprintf(file, ", ");
        }
        list = list->next;
    }
}

static void print_bracketed_tyvar_list(FILE *file, struct TyVarList *tyvar)
{
    if (tyvar) {
        fprintf(file, "<");
        while (tyvar) {
            fprintf(file, "%s", tyvar->name);
            if (tyvar->next) {
                fprintf(file, ", ");
            }
            tyvar = tyvar->next;
        }
        fprintf(file, ">");
    }
}

void print_type(FILE *file, struct Type *type)
{
    switch (type->tag) {
    case TY_UNIVAR:
        fprintf(file, "<UNIVAR:%p = ", (void*)type->univar_data.node);
        if (type->univar_data.node->type) {
            print_type(file, type->univar_data.node->type);
        } else {
            fprintf(file, "NULL");
        }
        fprintf(file, ">");
        break;

    case TY_VAR:
        fprintf(file, "%s", type->var_data.name);
        break;

    case TY_BOOL:
        fprintf(file, "bool");
        break;

    case TY_FINITE_INT:
        fprintf(file, "%s%d",
                type->int_data.is_signed ? "i" : "u",
                type->int_data.num_bits);
        break;

    case TY_MATH_INT:
        fprintf(file, "int");
        break;

    case TY_MATH_REAL:
        fprintf(file, "real");
        break;

    case TY_RECORD:
        fprintf(file, "{");
        print_name_type_list(file, type->record_data.fields);
        fprintf(file, "}");
        break;

    case TY_VARIANT:
        fprintf(file, "<");
        print_name_type_list(file, type->variant_data.variants);
        fprintf(file, ">");
        break;

    case TY_ARRAY:
        print_type(file, type->array_data.element_type);
        fprintf(file, "[");
        for (int i = 0; i < type->array_data.ndim; ++i) {
            if (type->array_data.sizes) {
                print_term(false, file, type->array_data.sizes[i]);
            } else if (type->array_data.resizable) {
                fprintf(file, "*");
            }
            if (i < type->array_data.ndim - 1) {
                fprintf(file, ", ");
            }
        }
        fprintf(file, "]");
        break;

    case TY_FUNCTION:
        fprintf(file, "fun(");
        {
            for (struct FunArg *arg = type->function_data.args; arg; arg = arg->next) {
                if (arg->ref) {
                    fprintf(file, "ref ");
                }
                print_type(file, arg->type);
                if (arg->next) {
                    fprintf(file, ", ");
                }
            }
        }
        fprintf(file, ")");
        if (type->function_data.return_type) {
            fprintf(file, "->");
            print_type(file, type->function_data.return_type);
        }
        break;

    case TY_FORALL:
        fprintf(file, "forall");
        print_bracketed_tyvar_list(file, type->forall_data.tyvars);
        fprintf(file, " ");
        print_type(file, type->forall_data.type);
        break;

    case TY_LAMBDA:
        fprintf(file, "lambda");
        print_bracketed_tyvar_list(file, type->forall_data.tyvars);
        fprintf(file, " ");
        print_type(file, type->forall_data.type);
        break;

    case TY_APP:
        print_type(file, type->app_data.lhs);
        fprintf(file, "<");
        {
            for (struct TypeList *arg = type->app_data.tyargs; arg; arg = arg->next) {
                print_type(file, arg->type);
                if (arg->next) {
                    fprintf(file, ", ");
                }
            }
        }
        fprintf(file, ">");
        break;
    }
}

static void print_pattern(FILE *file, struct Pattern *pattern)
{
    switch (pattern->tag) {
    case PAT_VAR:
        fprintf(file, "%s%s",
                pattern->var.ref ? "ref " : "",
                pattern->var.name);
        break;

    case PAT_BOOL:
        fprintf(file, "%s", pattern->bool_data.value ? "true" : "false");
        break;

    case PAT_INT:
        fprintf(file, "%s", pattern->int_data.data);
        break;

    case PAT_RECORD:
        // note: this shouldn't appear post-typechecking
        fprintf(file, "TODO_record_pattern");
        break;

    case PAT_VARIANT:
        fprintf(file, "<%s: ", pattern->variant.variant_name);
        print_pattern(file, pattern->variant.payload);
        fprintf(file, ">");
        break;

    case PAT_WILDCARD:
        fprintf(file, "_");
        break;
    }
}

static int precedence(struct Term *term)
{
    switch (term->tag) {
    case TM_VAR:
    case TM_DEFAULT:
    case TM_BOOL_LITERAL:
    case TM_INT_LITERAL:
    case TM_STRING_LITERAL:
    case TM_ARRAY_LITERAL:
    case TM_CAST:
    case TM_CALL:
    case TM_TYAPP:
    case TM_RECORD:
    case TM_RECORD_UPDATE:
    case TM_FIELD_PROJ:
    case TM_VARIANT:
    case TM_MATCH_FAILURE:
    case TM_SIZEOF:
    case TM_ALLOCATED:
    case TM_ARRAY_PROJ:
        return 20;

    case TM_IF:
    case TM_LET:
    case TM_QUANTIFIER:
    case TM_MATCH:
        return 0;

    case TM_UNOP:
        return 10;

    case TM_BINOP:
        switch (term->binop.list->operator) {
        case BINOP_TIMES:
        case BINOP_DIVIDE:
        case BINOP_MODULO:
        case BINOP_BITAND:
        case BINOP_SHIFTLEFT:
        case BINOP_SHIFTRIGHT:
            return 7;

        case BINOP_PLUS:
        case BINOP_MINUS:
        case BINOP_BITOR:
        case BINOP_BITXOR:
            return 6;

        case BINOP_GREATER:
        case BINOP_GREATER_EQUAL:
        case BINOP_LESS:
        case BINOP_LESS_EQUAL:
        case BINOP_EQUAL:
        case BINOP_NOT_EQUAL:
            return 5;

        case BINOP_AND:
            return 4;

        case BINOP_OR:
            return 3;

        case BINOP_IMPLIES:
        case BINOP_IMPLIED_BY:
            return 2;

        case BINOP_IFF:
            return 1;
        }
        break;
    }

    fatal_error("could not calculate precedence");
}

static void print_paren_term(bool postcond, FILE *file, struct Term *term, bool use_paren)
{
    if (use_paren) {
        fprintf(file, "(");
    }

    print_term(postcond, file, term);

    if (use_paren) {
        fprintf(file, ")");
    }
}

static void print_name_term_list(bool postcond, FILE *file, struct NameTermList *node)
{
    while (node) {
        fprintf(file, "%s: ", node->name);
        print_term(postcond, file, node->term);
        if (node->next) {
            fprintf(file, ", ");
        }
        node = node->next;
    }
}

static void print_string_literal(FILE *file, const uint8_t *data, uint32_t length)
{
    fputc('"', file);
    while (length > 0) {
        if (isprint(*data)) {
            fputc(*data, file);
        } else {
            fprintf(file, "\\x%02x", *data);
        }
        ++data;
        --length;
    }
    fputc('"', file);
}

static void print_array_literal(bool postcond, FILE *file, struct OpTermList *terms)
{
    fputc('[', file);
    while (terms) {
        print_term(postcond, file, terms->rhs);
        if (terms->next) {
            fprintf(file, ", ");
        }
        terms = terms->next;
    }
    fputc(']', file);
}

static void print_unop(bool postcond, FILE *file, struct Term *term)
{
    fprintf(file, "%s", unop_name(term->unop.operator));

    bool use_paren = precedence(term) > precedence(term->unop.operand);
    print_paren_term(postcond, file, term->unop.operand, use_paren);
}

static void print_binop(bool postcond, FILE *file, struct Term *term)
{
    int op_prec = precedence(term);
    bool right_assoc = (term->binop.list->operator == BINOP_IMPLIES);

    struct Term *lhs = term->binop.lhs;
    for (struct OpTermList *node = term->binop.list; node; node = node->next) {
        struct Term *rhs = node->rhs;

        int lhs_prec = precedence(lhs);
        int rhs_prec = precedence(rhs);

        bool use_left_paren =
            op_prec > lhs_prec ||
            (right_assoc && op_prec == lhs_prec);

        bool use_right_paren =
            op_prec > rhs_prec ||
            (!right_assoc && op_prec == rhs_prec);

        print_paren_term(postcond, file, lhs, use_left_paren);
        fprintf(file, " %s ", binop_name(node->operator));
        print_paren_term(postcond, file, rhs, use_right_paren);

        lhs = rhs;
    }
}

static void print_if(bool postcond, FILE *file, struct Term *term)
{
    int if_prec = precedence(term);

    fprintf(file, "if ");
    bool cond_paren = if_prec >= precedence(term->if_data.cond);
    print_paren_term(postcond, file, term->if_data.cond, cond_paren);

    fprintf(file, " then ");
    bool then_paren = if_prec >= precedence(term->if_data.then_branch);
    print_paren_term(postcond, file, term->if_data.then_branch, then_paren);

    fprintf(file, " else ");
    bool else_paren = if_prec >= precedence(term->if_data.else_branch);
    print_paren_term(postcond, file, term->if_data.else_branch, else_paren);
}

static void print_let(bool postcond, FILE *file, struct Term *term)
{
    fprintf(file, "let %s = ", term->let.name);

    bool use_paren = precedence(term) >= precedence(term->let.rhs);
    print_paren_term(postcond, file, term->let.rhs, use_paren);

    fprintf(file, " in ");

    print_term(postcond, file, term->let.body);
}

static void print_call(bool postcond, FILE *file, struct Term *term)
{
    bool use_paren = precedence(term) > precedence(term->call.func);
    print_paren_term(postcond, file, term->call.func, use_paren);

    fprintf(file, "(");
    for (struct OpTermList *arg = term->call.args; arg; arg = arg->next) {
        print_term(postcond, file, arg->rhs);
        if (arg->next) {
            fprintf(file, ", ");
        }
    }
    fprintf(file, ")");
}

static void print_term(bool postcond, FILE *file, struct Term *term)
{
    switch (term->tag) {
    case TM_VAR:
        if (postcond && !term->var.postcond_new) {
            fprintf(file, "old(%s)", term->var.name);
        } else {
            fprintf(file, "%s", term->var.name);
        }
        break;

    case TM_DEFAULT:
        fprintf(file, "#default ");
        print_type(file, term->type);
        break;

    case TM_BOOL_LITERAL:
        fprintf(file, "%s", term->bool_literal.value ? "true" : "false");
        break;

    case TM_INT_LITERAL:
        fprintf(file, "%s", term->int_literal.data);
        break;

    case TM_STRING_LITERAL:
        print_string_literal(file, term->string_literal.data, term->string_literal.length);
        break;

    case TM_ARRAY_LITERAL:
        print_array_literal(postcond, file, term->array_literal.terms);
        break;

    case TM_CAST:
        print_type(file, term->cast.target_type);
        print_paren_term(postcond, file, term->cast.operand, true);
        break;

    case TM_IF:
        print_if(postcond, file, term);
        break;

    case TM_UNOP:
        print_unop(postcond, file, term);
        break;

    case TM_BINOP:
        print_binop(postcond, file, term);
        break;

    case TM_LET:
        print_let(postcond, file, term);
        break;

    case TM_QUANTIFIER:
        {
            const char *q = "??";
            switch (term->quant.quant) {
            case QUANT_FORALL: q = "forall"; break;
            case QUANT_EXISTS: q = "exists"; break;
            }
            fprintf(file, "%s (%s: ", q, term->quant.name);
            print_type(file, term->quant.type);
            fprintf(file, ") ");
            print_term(false, file, term->quant.body);
        }
        break;

    case TM_CALL:
        print_call(postcond, file, term);
        break;

    case TM_TYAPP:
        print_term(postcond, file, term->tyapp.lhs);
        fprintf(file, "<");
        for (struct TypeList *tyarg = term->tyapp.tyargs; tyarg; tyarg = tyarg->next) {
            if (tyarg != term->tyapp.tyargs) fprintf(file, ", ");
            print_type(file, tyarg->type);
        }
        fprintf(file, ">");
        break;

    case TM_RECORD:
        fprintf(file, "{");
        print_name_term_list(postcond, file, term->record.fields);
        fprintf(file, "}");
        break;

    case TM_RECORD_UPDATE:
        fprintf(file, "TODO_record_update");
        break;

    case TM_FIELD_PROJ:
        {
            bool use_paren = precedence(term) > precedence(term->field_proj.lhs);
            print_paren_term(postcond, file, term->field_proj.lhs, use_paren);
            fprintf(file, ".%s", term->field_proj.field_name);
        }
        break;

    case TM_VARIANT:
        fprintf(file, "<%s: ", term->variant.variant_name);
        print_term(postcond, file, term->variant.payload);
        fprintf(file, ">");
        break;

    case TM_MATCH:
        fprintf(file, "match ");
        print_paren_term(postcond, file, term->match.scrutinee, true);
        fprintf(file, " {");
        {
            for (struct Arm *arm = term->match.arms; arm; arm = arm->next) {
                fprintf(file, " case ");
                print_pattern(file, arm->pattern);
                fprintf(file, " => ");
                print_term(postcond, file, arm->rhs);
            }
        }
        fprintf(file, " }");
        break;

    case TM_MATCH_FAILURE:
        fprintf(file, "#match_fail_term");
        break;

    case TM_SIZEOF:
        fprintf(file, "sizeof");
        print_paren_term(postcond, file, term->sizeof_data.rhs, true);
        break;

    case TM_ALLOCATED:
        fprintf(file, "allocated");
        print_paren_term(postcond, file, term->allocated.rhs, true);
        break;

    case TM_ARRAY_PROJ:
        print_term(postcond, file, term->array_proj.lhs);
        fprintf(file, "[");
        for (struct OpTermList *node = term->array_proj.indexes; node; node = node->next) {
            if (node != term->array_proj.indexes) fprintf(file, ", ");
            print_term(postcond, file, node->rhs);
        }
        fprintf(file, "]");
        break;
    }
}

static void print_spaces(FILE *file, int indent_level)
{
    for (int i = 0; i < 4 * indent_level; ++i) {
        fprintf(file, " ");
    }
}

static const char * attr_name(enum AttrTag tag)
{
    switch (tag) {
    case ATTR_REQUIRES: return "requires";
    case ATTR_ENSURES: return "ensures";
    case ATTR_INVARIANT: return "invariant";
    case ATTR_DECREASES: return "decreases";
    }
    return "???";
}

static void print_attributes(int indent_level, FILE *file, struct Attribute *attr)
{
    while (attr) {
        print_spaces(file, indent_level);
        fprintf(file, "%s ", attr_name(attr->tag));
        switch (attr->tag) {
        case ATTR_REQUIRES:
        case ATTR_ENSURES:
        case ATTR_INVARIANT:
        case ATTR_DECREASES:
            print_term(attr->tag == ATTR_ENSURES, file, attr->term);
            break;
        }
        fprintf(file, ";\n");
        attr = attr->next;
    }
}

static void print_statements(int indent_level, FILE *file, struct Statement *stmt)
{
    while (stmt) {

        print_spaces(file, indent_level);

        switch (stmt->tag) {
        case ST_VAR_DECL:
            fprintf(file, "%s %s: ",
                    stmt->var_decl.ref ? "ref" : "var",
                    stmt->var_decl.name);
            print_type(file, stmt->var_decl.type);
            fprintf(file, " = ");
            print_term(false, file, stmt->var_decl.rhs);
            fprintf(file, ";\n");
            break;

        case ST_FIX:
            fprintf(file, "fix %s: ", stmt->fix.name);
            print_type(file, stmt->fix.type);
            fprintf(file, ";\n");
            break;

        case ST_OBTAIN:
            fprintf(file, "obtain (%s: ", stmt->obtain.name);
            print_type(file, stmt->obtain.type);
            fprintf(file, ") ");
            print_term(false, file, stmt->obtain.condition);
            fprintf(file, ";\n");
            break;

        case ST_USE:
            fprintf(file, "use ");
            print_term(false, file, stmt->use.term);
            fprintf(file, ";\n");
            break;

        case ST_ASSIGN:
            print_term(false, file, stmt->assign.lhs);
            fprintf(file, " = ");
            print_term(false, file, stmt->assign.rhs);
            fprintf(file, ";\n");
            break;

        case ST_SWAP:
            fprintf(file, "swap ");
            print_term(false, file, stmt->swap.lhs);
            fprintf(file, ", ");
            print_term(false, file, stmt->swap.rhs);
            fprintf(file, ";\n");
            break;

        case ST_RETURN:
            fprintf(file, "return");
            if (stmt->ret.value) {
                fprintf(file, " ");
                print_term(false, file, stmt->ret.value);
            }
            fprintf(file, ";\n");
            break;

        case ST_ASSERT:
            fprintf(file, "assert ");
            print_paren_term(false, file, stmt->assert_data.condition, true);
            if (stmt->assert_data.proof) {
                fprintf(file, " {\n");
                print_statements(indent_level + 1, file, stmt->assert_data.proof);
                print_spaces(file, indent_level);
                fprintf(file, "}\n");
            } else {
                fprintf(file, ";\n");
            }
            break;

        case ST_ASSUME:
            fprintf(file, "assume ");
            print_term(false, file, stmt->assume.condition);
            fprintf(file, ";\n");
            break;

        case ST_IF:
            fprintf(file, "if ");
            print_paren_term(false, file, stmt->if_data.condition, true);
            fprintf(file, " {\n");
            print_statements(indent_level + 1, file, stmt->if_data.then_block);
            if (stmt->if_data.else_block) {
                print_spaces(file, indent_level);
                fprintf(file, "} else {\n");
                print_statements(indent_level + 1, file, stmt->if_data.else_block);
            }
            print_spaces(file, indent_level);
            fprintf(file, "}\n");
            break;

        case ST_WHILE:
            fprintf(file, "while ");
            print_paren_term(false, file, stmt->while_data.condition, true);
            fprintf(file, "\n");
            print_attributes(indent_level + 1, file, stmt->while_data.attributes);
            print_spaces(file, indent_level);
            fprintf(file, "{\n");
            print_statements(indent_level + 1, file, stmt->while_data.body);
            print_spaces(file, indent_level);
            fprintf(file, "}\n");
            break;

        case ST_CALL:
            print_term(false, file, stmt->call.term);
            fprintf(file, ";\n");
            break;

        case ST_MATCH:
            fprintf(file, "match ");
            print_paren_term(false, file, stmt->match.scrutinee, true);
            fprintf(file, " {\n");
            {
                for (struct Arm *arm = stmt->match.arms; arm; arm = arm->next) {
                    print_spaces(file, indent_level);
                    fprintf(file, "case ");
                    print_pattern(file, arm->pattern);
                    fprintf(file, " =>\n");
                    print_statements(indent_level + 1, file, arm->rhs);
                }
            }
            print_spaces(file, indent_level);
            fprintf(file, "}\n");
            break;

        case ST_MATCH_FAILURE:
            fprintf(file, "#match_fail_stmt;\n");
            break;

        case ST_SHOW_HIDE:
            fprintf(file, "%s %s;\n",
                    stmt->show_hide.show ? "show" : "hide",
                    stmt->show_hide.name);
            break;
        }

        stmt = stmt->next;
    }
}

static void print_function(int indent_level, FILE *file, struct Decl *decl)
{
    if (decl->function_data.is_extern) {
        fprintf(file, "extern ");
    }

    if (decl->function_data.impure) {
        fprintf(file, "impure ");
    }

    fprintf(file, "function %s", decl->name);
    print_bracketed_tyvar_list(file, decl->function_data.tyvars);

    fprintf(file, "(");
    for (struct FunArg *arg = decl->function_data.args; arg; arg = arg->next) {
        if (arg->ref) {
            fprintf(file, "ref ");
        }
        fprintf(file, "%s: ", arg->name);
        print_type(file, arg->type);
        if (arg->next) {
            fprintf(file, ", ");
        }
    }
    fprintf(file, ")");

    if (decl->function_data.return_type) {
        fprintf(file, ": ");
        print_type(file, decl->function_data.return_type);
    }

    if (decl->attributes || decl->function_data.body_specified) {
        fprintf(file, "\n");

        print_attributes(indent_level + 1, file, decl->attributes);

        if (decl->function_data.body_specified) {
            print_spaces(file, indent_level);
            fprintf(file, "{\n");
            print_statements(indent_level + 1, file, decl->function_data.body);
            print_spaces(file, indent_level);
            fprintf(file, "}\n");
        }

    } else {
        fprintf(file, ";\n");
    }
}

static void print_datatype(int indent_level, FILE *file, struct Decl *decl)
{
    fprintf(file, "datatype %s", decl->name);
    print_bracketed_tyvar_list(file, decl->datatype_data.tyvars);
    fprintf(file, " =");

    bool first = true;

    for (struct DataCtor *ctor = decl->datatype_data.ctors; ctor; ctor = ctor->next) {
        fprintf(file, "\n");
        print_spaces(file, indent_level);
        if (first) {
            fprintf(file, "    ");
        } else {
            fprintf(file, "  | ");
        }

        fprintf(file, "%s", ctor->name);

        if (ctor->payload) {
            fprintf(file, " ");
            if (ctor->payload->tag == TY_RECORD || ctor->payload->tag == TY_VARIANT) {
                print_type(file, ctor->payload);
            } else {
                fprintf(file, "(");
                print_type(file, ctor->payload);
                fprintf(file, ")");
            }
        }

        first = false;
    }

    fprintf(file, ";\n");
}

static void print_decls(int indent_level, FILE *file, struct Decl *decl)
{
    while (decl) {
        fprintf(file, "\n");

        print_spaces(file, indent_level);

        if (decl->ghost) {
            fprintf(file, "ghost ");
        }

        switch (decl->tag) {
        case DECL_CONST:
            fprintf(file, "const %s: ", decl->name);
            print_type(file, decl->const_data.type);
            if (decl->const_data.rhs) {
                fprintf(file, " = ");
                print_term(false, file, decl->const_data.rhs);
            }
            fprintf(file, ";\n");
            break;

        case DECL_FUNCTION:
            print_function(indent_level, file, decl);
            break;

        case DECL_DATATYPE:
            print_datatype(indent_level, file, decl);
            break;

        case DECL_TYPEDEF:
            fprintf(file, "type %s", decl->name);
            print_bracketed_tyvar_list(file, decl->typedef_data.tyvars);
            if (decl->typedef_data.rhs) {
                fprintf(file, " = ");
                print_type(file, decl->typedef_data.rhs);
            } else if (decl->typedef_data.alloc_level != ALLOC_NEVER) {
                fprintf(file, " (");
                if (decl->typedef_data.alloc_level == ALLOC_ALWAYS) {
                    fprintf(file, "allocated");
                } else if (decl->typedef_data.alloc_level == ALLOC_IF_NOT_DEFAULT) {
                    fprintf(file, "allocated_if_not_default");
                } else {
                    fprintf(file, "????");
                }
                fprintf(file, ")");
            }
            fprintf(file, ";\n");
            break;
        }

        decl = decl->next;
    }
}

static void print_decl_groups(int indent_level, FILE *file, struct DeclGroup *group)
{
    while (group) {
        print_decls(indent_level, file, group->decl);
        group = group->next;
    }
}

static void print_imports(FILE *file, struct Import *import)
{
    if (import) {
        fprintf(file, "\n");
    }

    while (import) {
        fprintf(file, "import %s", import->module_name);
        if (import->alias_name) {
            fprintf(file, " as %s", import->alias_name);
        }
        fprintf(file, ";\n");
        import = import->next;
    }
}

void print_module(FILE *file, struct Module *module)
{
    fprintf(file, "module %s\n", module->name);

    print_imports(file, module->interface_imports);

    fprintf(file, "\ninterface {\n");
    print_decl_groups(1, file, module->interface);
    fprintf(file, "}\n");

    print_imports(file, module->implementation_imports);

    print_decl_groups(0, file, module->implementation);
}

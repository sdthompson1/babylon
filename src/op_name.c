/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "op_name.h"

const char * unop_name(enum UnOp op)
{
    switch (op) {
    case UNOP_NEGATE: return "-";
    case UNOP_COMPLEMENT: return "~";
    case UNOP_NOT: return "!";
    }
    return "???";
}

const char * binop_name(enum BinOp op)
{
    switch (op) {
    case BINOP_PLUS: return "+";
    case BINOP_MINUS: return "-";
    case BINOP_TIMES: return "*";
    case BINOP_DIVIDE: return "/";
    case BINOP_MODULO: return "%";
    case BINOP_BITAND: return "&";
    case BINOP_BITOR: return "|";
    case BINOP_BITXOR: return "^";
    case BINOP_SHIFTLEFT: return "<<";
    case BINOP_SHIFTRIGHT: return ">>";
    case BINOP_EQUAL: return "==";
    case BINOP_NOT_EQUAL: return "!=";
    case BINOP_LESS: return "<";
    case BINOP_LESS_EQUAL: return "<=";
    case BINOP_GREATER: return ">";
    case BINOP_GREATER_EQUAL: return ">=";
    case BINOP_AND: return "&&";
    case BINOP_OR: return "||";
    case BINOP_IMPLIES: return "==>";
    case BINOP_IMPLIED_BY: return "<==";
    case BINOP_IFF: return "<==>";
    }
    return "???";
}

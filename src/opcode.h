/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef OPCODE_H
#define OPCODE_H

// Enum for available ALU operations. Used by stack_machine.h and asm_gen.h.

#include <stdbool.h>

enum Opcode {

    OP_NEG,     // negate
    OP_ADD,
    OP_SUB,
    OP_MUL,
    OP_UDIV,    // unsigned divide
    OP_UREM,    // unsigned remainder
    OP_SDIV,    // signed divide
    OP_SREM,    // signed remainder

    OP_NOT,     // complement all bits
    OP_AND,
    OP_OR,
    OP_XOR,
    OP_XOR_1,   // complement least significant bit only
    OP_SHL,     // shift left
    OP_ASR,     // arithmetic shift right
    OP_LSR,     // logical shift right

    OP_EQ,      // equal (result is 1 if operands equal, 0 otherwise).
    OP_NE,      // not equal
    OP_SLT,     // signed less-than
    OP_SLE,     // signed less-than-or-equal
    OP_SGT,     // signed greater-than
    OP_SGE,     // signed greater-than-or-equal
    OP_ULT,     // unsigned versions
    OP_ULE,
    OP_UGT,
    OP_UGE
};

bool is_unary_opcode(enum Opcode op);

#endif

/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "opcode.h"

bool is_unary_opcode(enum Opcode op)
{
    return op == OP_NEG || op == OP_NOT || op == OP_XOR_1;
}

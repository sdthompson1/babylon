/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef OP_NAME_H
#define OP_NAME_H

#include "ast.h"

const char * unop_name(enum UnOp op);

const char * binop_name(enum BinOp op);

#endif

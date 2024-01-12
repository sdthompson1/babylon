/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef CONVERT_FOL_TO_SMT_H
#define CONVERT_FOL_TO_SMT_H

struct Sexpr;

// fol_problem is handed over
struct Sexpr * convert_fol_to_smt(struct Sexpr * fol_problem);

#endif

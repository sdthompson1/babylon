/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef DEPENDENCY_H
#define DEPENDENCY_H

struct Module;

// The parser creates one big DeclGroup (actually one for interface
// and one for implementation).

// The dependency resolver will organise these into separate groups
// based on the dependencies between the decls.

void resolve_dependencies(struct Module *module);

#endif

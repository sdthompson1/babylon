/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef TYPECHECKER_H
#define TYPECHECKER_H

struct Term;
struct Decl;
struct Module;


//
// Type environment
//

// A type_env is a HashTable from a symbol name to a TypeEnvEntry.

struct TypeEnvEntry {
    struct Type *type;   // Type of the term, or target type of a datatype/typedef (NULL for tyvars).
                         // Kind-checked, but not necessarily kind *.

    struct Term *value;  // For global constants - normal-form value of this constant, if known.

    bool ghost;
    bool read_only;
    bool constructor;
};

void add_to_type_env(struct HashTable *env,
                     const char *name,    // copied
                     struct Type *type,   // handed over
                     bool ghost,
                     bool read_only,
                     bool constructor);

void free_type_env(struct HashTable *type_env);


//
// Typecheck a module.
//

// Returns true on success.

// Fills in any type information (e.g. 'type' field in struct Term.)
// Also adds entries to the type_env.

// If interface_only is true, only the interface section will be
// typechecked, otherwise both interface and implementation will be
// checked.

// If keep_all is true, then both exported and non-exported names are
// kept in the type_env. Otherwise, only exported names are kept.

bool typecheck_module(struct HashTable *type_env,
                      struct Module *module,
                      bool interface_only,
                      bool keep_all);


// Confirm that a "main" function of a suitable type exists in the
// given module. If so, returns true; otherwise prints error
// message(s) and returns false.

bool typecheck_main_function(struct HashTable *type_env, const char *root_module_name);

#endif

/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

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

// A type_env is a StackedHashTable from a symbol name to a TypeEnvEntry.
typedef struct StackedHashTable TypeEnv;

struct TypeEnvEntry {
    struct Type *type;   // Type of the term, or target type of a datatype/typedef (NULL for tyvars).
                         // Kind-checked, but not necessarily kind *.

    struct TraitList *traits;  // If type==NULL this specifies the traits that the tyvar is
                               // guaranteed to have (if any).

    struct Term *value;  // For global constants - normal-form value of this constant, if known.

    bool ghost;
    bool read_only;
    bool constructor;
    bool impure;

    enum AllocLevel alloc_level;  // for tyvars
};

// Create a new type env, with one (empty) layer.
TypeEnv * new_type_env();

// Push a new (empty) layer onto a type env.
TypeEnv * push_type_env(TypeEnv *env);

// Pop the topmost layer of a type env, destroying it.
TypeEnv * pop_type_env(TypeEnv *env);

// Collapse the topmost layer of a type env into the layer below. Any names in the
// topmost layer will be "moved" down one layer. If this clashes with an entry in the
// below layer, then the existing entry in the below layer is removed/destroyed.
// ("env" is itself freed, but the layer below is returned.)
TypeEnv * collapse_type_env(TypeEnv *env);

// Adds a name to the top "layer" of the hash table.
void add_to_type_env(TypeEnv *env,
                     const char *name,    // copied
                     struct Type *type,   // handed over. NULL for tyvars.
                     struct TraitList *traits,  // handed over. only valid when type==NULL.
                     bool ghost,
                     bool read_only,
                     bool constructor,
                     bool impure,
                     enum AllocLevel alloc_level); // only relevant for abstract or extern types

// Lookup an entry in a type env.
struct TypeEnvEntry * type_env_lookup(const TypeEnv *env, const char *name);

void free_type_env(struct StackedHashTable *type_env);


//
// Typecheck a module.
//

// Returns true on success.

// Fills in any type information (e.g. 'type' field in struct Term.)
// Also adds entries to the (top "layer" of the) type_env.

// If interface_only is true, only the interface section will be
// typechecked, otherwise both interface and implementation will be
// checked.

bool typecheck_module(TypeEnv *type_env,
                      struct Module *module,
                      bool interface_only);


// Confirm that a "main" function of a suitable type exists in the
// given module. If so, returns true; otherwise prints error
// message(s) and returns false.

bool typecheck_main_function(TypeEnv *type_env, const char *root_module_name);

#endif

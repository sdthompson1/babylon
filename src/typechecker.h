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

enum TypeFlag {
    FLAG_GHOST       = (1 << 0),    // ghost term variable
    FLAG_READ_ONLY   = (1 << 1),    // read-only variable (e.g. a function argument)
    FLAG_DATA_CTOR   = (1 << 2),    // data constructor name
    FLAG_IMPURE      = (1 << 3),    // impure function
    FLAG_REF         = (1 << 4),    // variable is a reference to something else
    FLAG_PARTIAL_REF = (1 << 5),    // variable is a reference to only part of the mentioned "root_name"
    FLAG_EMPTY       = (1 << 6),    // variable has been "moved out of"
};

struct TypeEnvEntry {
    struct Type *type;   // Type of the term, or target type of a datatype/typedef (NULL for tyvars).
                         // Kind-checked, but not necessarily kind *.

    struct TraitList *traits;  // If type==NULL this specifies the traits that the tyvar is
                               // guaranteed to have (if any).

    const char *root_name;     // For references, names the "root variable" of the reference.

    struct Term *value;  // For global constants - normal-form value of this constant, if known.

    struct Location created_location;  // Where was the variable created.
    struct Location *moved_location;   // If FLAG_EMPTY is set, indicates where moved. Allocated.

    uint8_t flags;   // Bitmask of TypeFlag
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
struct TypeEnvEntry *
    add_to_type_env(TypeEnv *env,
                    const char *name,    // copied
                    struct Type *type,   // handed over. NULL for tyvars.
                    struct TraitList *traits,  // handed over. only valid when type==NULL.
                    uint8_t flags,
                    struct Location location); // location the variable/entity was created

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

/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef RENAMER_H
#define RENAMER_H

struct HashTable;
struct Module;
struct PackageLoader;
struct Statement;
struct Term;


void free_renamer_env(struct HashTable *env);


// Rename symbols in the module to ensure:
//
//  - All global symbols are fully qualified
//      ("package-name/ModuleName.name" instead of "name")
//      (Note we use "/" to separate the package-name from the module-name
//       internally. In error messages, the "/" is converted to a ":".)
//
//  - Local symbols do not shadow each other
//      (shadowed names will have "@" and a number appended,
//       e.g. "x@1" instead of "x")
//
//  - Type names have "^" prepended
//      e.g. "pkg/Main.^Color" instead of "pkg/Main.Color" for a datatype,
//      or "^a" instead of "a" for a type variable.
//      (This is how we ensure the separation between the
//       type and term "namespaces")
//
//  - The module itself will be renamed to "package-name/ModuleName".
//
// The module is modified in place.
//
// The renamer_env contains names exported from previously loaded
// modules. It will be updated in place.
//
// If interface_only is true, then only the "interface" part of the
// module is processed, otherwise the whole module is processed.
//
bool rename_module(struct HashTable *renamer_env,
                   struct PackageLoader *package_loader,
                   const char *package_name,
                   struct Module *module,
                   bool interface_only);


// These are used by the pattern match compiler in order to clean up
// any duplicate names it may have inadvertently created.
void rename_term_for_match_compiler(struct Term *term, uint64_t *name_counter);
void rename_statement_for_match_compiler(struct Statement *stmt, uint64_t *name_counter);


#endif

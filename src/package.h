/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#ifndef PACKAGE_H
#define PACKAGE_H

#include "util.h"

#include <stdbool.h>

struct PackageLoader;

struct PackageLoader * alloc_package_loader();
void free_package_loader(struct PackageLoader *loader);

// Load the root package from prefix+"package.toml",
// and also search for and validate any dependencies.
// On success, returns true.
// On failure, prints error messages and returns false.
bool load_root_package_and_dependencies(struct PackageLoader *loader,
                                        const char *prefix,
                                        struct NameList *search_path);

// These return pointers to internal parts of the PackageLoader, so the
// returned pointers do not need to be freed by the caller
const char * get_root_package_name(struct PackageLoader *loader);
struct NameList * get_root_exported_modules(struct PackageLoader *loader); // can be NULL
const char * get_root_main_module(struct PackageLoader *loader); // can be NULL
const char * get_root_main_function(struct PackageLoader *loader);  // can be NULL

struct ModulePathInfo {
    char *package_name;     // package name that the module was found in
    char *b_filename;       // path to .b file
    char *c_filename;       // path to .c file if it exists
};

// Look for a given module relative to a given "importer" package.
// Returns a pointer to a "cached" ModulePathInfo object (so the
// caller should not free it); or returns NULL if the module was not
// found.
struct ModulePathInfo * find_module(struct PackageLoader *loader,
                                    const char *importer_package,
                                    const char *module_name);

#endif

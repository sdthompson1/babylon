/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/

#define _POSIX_C_SOURCE 200809L   // required by toml-c.h

#include "alloc.h"
#include "dep_list.h"
#include "error.h"
#include "hash_table.h"
#include "package.h"
#include "system_packages.h"

#include "toml-c.h"

#include <stdlib.h>
#include <string.h>


#define PACKAGE_TOML_NAME "package.toml"


struct Package;

struct Package {
    // Package name
    char *name;

    // Package version. Should be a Semantic Version string (or at least a dot separated
    // string of some sort!).
    char *version;

    // Babylon packages that this package depends on.
    struct DepList *deps;

    // cflags (from system packages)
    struct NameList *cflags;

    // Path prefix for the package.toml file. Ends in slash, or is "".
    char *prefix;

    // Only modules on the exported_modules list can be "imported" by other packages.
    // All exported_modules will be used as "roots" for build or verify jobs.
    struct NameList *exported_modules;

    // main_module is used as a root for build/verify jobs.
    // Also, if main_module is non-NULL, we compile and link an executable.
    //  - If main_function is NULL, it is assumed that the C "main" function
    //    is defined externally somewhere.
    //  - Otherwise, the compiler generates a C "main" function that calls
    //    the given main_function in the main_module. The main_function must
    //    take no arguments and return no value.
    char *main_module;
    char *main_function;
};

struct PackageLoader {
    // Key = package name (points to a field of the Package*).
    // Value = Package* (allocated).
    struct HashTable * packages;

    // Key = importing-package-name ">" module-name (allocated).
    // Value = cached ModulePathInfo for that module (allocated), or NULL if not found.
    struct HashTable * path_infos;

    // Points to one of the entries in the packages hash table.
    struct Package * root_package;

    // Our copy of the pkg_config_cmd
    char *pkg_config_cmd;

    // Key = system_package name (allocated).
    // Value = min version required (allocated).
    // This is freed after "libs" is constructed.
    struct HashTable *all_system_packages;

    // All "libs" from all system packages.
    struct NameList *libs;
};


static struct DepList * copy_dep_list(struct DepList *deps)
{
    struct DepList *result = NULL;
    struct DepList **tail = &result;

    while (deps) {
        struct DepList *node = alloc(sizeof(struct DepList));
        node->name = copy_string(deps->name);
        node->min_version = copy_string(deps->min_version);
        node->next = NULL;
        *tail = node;
        tail = &node->next;
        deps = deps->next;
    }

    return result;
}

static void free_path_info(struct ModulePathInfo *info)
{
    if (info) {
        free(info->package_name);
        free(info->b_filename);
        free(info->c_filename);
        free(info);
    }
}

static void free_dep_list(struct DepList *deps)
{
    while (deps) {
        struct DepList *next = deps->next;
        free(deps->name);
        free(deps->min_version);
        free(deps);
        deps = next;
    }
}

static void free_package(struct Package *package)
{
    free(package->name);
    free(package->version);
    free_dep_list(package->deps);
    free_name_list(package->cflags);
    free(package->prefix);
    free_name_list(package->exported_modules);
    free(package->main_module);
    free(package->main_function);
    free(package);
}


// Replacement for toml_table_array that prints an error (as well as
// returning NULL) if the value is present but not actually an array.
static toml_array_t* toml_table_array_ext(const char *filename,
                                          const toml_table_t *table,
                                          const char *key,
                                          bool *error)
{
    if (error) *error = false;

    toml_array_t * arr = toml_table_array(table, key);
    if (arr != NULL) {
        return arr;
    }

    // toml_table_array returns NULL if either the key is not found
    // or the key has non-array type. We have to figure out which it is.
    int len = toml_table_len(table);
    for (int i = 0; i < len; ++i) {
        int keylen;
        if (strcmp(toml_table_key(table, i, &keylen), key) == 0) {
            // Found the key as a non-array key
            fprintf(stderr, "%s: '%s' has incorrect type (should be array)\n", filename, key);
            if (error) *error = true;
            break;
        }
    }

    // Either way, we return NULL
    return NULL;
}


// Helper function used by numeric_compare.
static bool all_digits(const char *a)
{
    while (*a) {
        if (!isdigit(*a)) {
            return false;
        }
        ++a;
    }
    return true;
}

// Helper function used by version_compare.
static int numeric_compare(const char *a, const char *b)
{
    if (all_digits(a) && all_digits(b)) {
        long ai = strtol(a, NULL, 10);
        long bi = strtol(b, NULL, 10);
        if (ai < bi) {
            return -1;
        } else if (ai > bi) {
            return 1;
        } else {
            return 0;
        }
    } else {
        return strcmp(a, b);
    }
}

// Returns -1 if a < b, 0 if equal, 1 if a > b.
// Uses "semver" rules: version components (separated by dots) are compared from
// left to right. Any purely numeric components are compared as numbers, otherwise
// they are compared as strings using strcmp.
// Note: This may modify the strings in place but it reverts them back before returning!
static int version_compare(char *a, char *b)
{
    // Base case - either string is empty
    if (*a == 0) {
        if (*b == 0) {
            return 0;
        } else {
            return -1;  // a < b
        }
    } else if (*b == 0) {
        return 1;  // a > b
    }

    // Isolate the first "dotted" component (which might be the whole string)
    char *dot_a = strchr(a, '.');
    if (dot_a) {
        *dot_a = 0;
    }

    char *dot_b = strchr(b, '.');
    if (dot_b) {
        *dot_b = 0;
    }

    int r = numeric_compare(a, b);
    if (r == 0) {
        if (dot_a) {
            if (dot_b) {
                // Compare the next dotted component in each case
                r = version_compare(dot_a + 1, dot_b + 1);
            } else {
                // a > b (example: 1.2 and 1)
                r = 1;
            }
        } else if (dot_b) {
            // a < b (example: 1 and 1.2)
            r = -1;
        }
    }

    // Restore the strings
    if (dot_a) *dot_a = '.';
    if (dot_b) *dot_b = '.';

    return r;
}


// Given a list of system_packages,
// update "all_system_packages" hashtable,
// and fill in "cflags" for this package.
// Returns false if the pkg-config command fails.
static bool resolve_system_packages(const char *pkg_config_cmd,
                                    struct DepList *system_packages,
                                    struct NameList **cflags,
                                    struct HashTable *all_system_packages)
{
    // Call pkg-config to get the cflags
    bool result = system_package_cflags(pkg_config_cmd, system_packages, cflags);

    // Add the min versions to 'all_system_packages'
    // (updating existing entries if required)
    for (struct DepList *node = system_packages; node; node = node->next) {
        const char *key;
        void *value;
        hash_table_lookup_2(all_system_packages, node->name, &key, &value);
        if (key && version_compare(node->min_version, value) > 0) {
            hash_table_remove(all_system_packages, key);
            free((char*)key);
            free(value);
            key = NULL;
            value = NULL;
        }
        if (!key) {
            hash_table_insert(all_system_packages,
                              copy_string(node->name),
                              copy_string(node->min_version));
        }
    }

    // Return success or failure status
    return result;
}

static bool resolve_libs(const char *pkg_config_cmd,
                         struct HashTable **all_system_packages,
                         struct NameList **libs)
{
    struct DepList *pkgs = NULL;
    struct DepList **tail = &pkgs;

    struct HashIterator *iter = new_hash_iterator(*all_system_packages);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        struct DepList *node = alloc(sizeof(struct DepList));
        node->name = (char*)key;
        node->min_version = value;
        node->next = NULL;
        *tail = node;
        tail = &node->next;
    }
    free_hash_iterator(iter);

    bool success = system_package_libs(pkg_config_cmd, pkgs, libs);

    while (pkgs) {
        struct DepList *next = pkgs->next;
        free(pkgs);
        pkgs = next;
    }

    hash_table_for_each(*all_system_packages, ht_free_key_and_value, NULL);
    free_hash_table(*all_system_packages);
    *all_system_packages = NULL;

    return success;
}


// Reads a string from a toml table. Returns newly allocated string.
// If key not present, or not a string:
//   - if 'dflt' is NULL, prints error and returns NULL;
//   - otherwise, returns a copy of dflt.
// 'filename' is for error messages.
static char* read_string(const char *filename,
                         const toml_table_t *table,
                         const char *key,
                         const char *dflt)
{
    toml_value_t val = toml_table_string(table, key);
    if (val.ok) {
        return val.u.s;  // caller must free this
    } else if (dflt) {
        return copy_string(dflt);
    } else {
        fprintf(stderr, "%s: '%s' missing or invalid\n", filename, key);
        return NULL;
    }
}

// Read a list of strings
static struct NameList *read_string_list(const char *filename,
                                         const toml_array_t *array,
                                         bool *error)
{
    struct NameList *result = NULL;
    struct NameList **tail = &result;
    *error = false;

    int len = toml_array_len(array);
    for (int i = 0; i < len; ++i) {
        toml_value_t str = toml_array_string(array, i);
        if (str.ok) {
            struct NameList *node = alloc(sizeof(struct NameList));
            node->name = str.u.s;
            node->next = NULL;
            *tail = node;
            tail = &node->next;
        } else {
            fprintf(stderr, "%s: invalid string found in array\n", filename);
            *error = true;
            free_name_list(result);
            return NULL;
        }
    }

    return result;
}

// Read the [dependencies] or [system_packages] table.
static struct DepList *read_deps(const char *filename,
                                 const toml_table_t *table,
                                 bool *error)
{
    struct DepList *result = NULL;
    struct DepList **tail = &result;
    *error = false;

    int len = toml_table_len(table);
    for (int i = 0; i < len; ++i) {
        int keylen;
        const char *dep_name = toml_table_key(table, i, &keylen);
        char *version = read_string(filename, table, dep_name, NULL);
        if (version == NULL) {
            fprintf(stderr, "%s: invalid version string found for '%s'\n", filename, dep_name);
            *error = true;
            free_dep_list(result);
            return NULL;
        }

        struct DepList *dep = alloc(sizeof(struct DepList));
        dep->name = copy_string(dep_name);
        dep->min_version = version;
        version = NULL;
        dep->next = NULL;

        *tail = dep;
        tail = &dep->next;
    }

    return result;
}

static bool valid_package_name(const char *name)
{
    for (const char *p = name; *p; p++) {
        if (!isalnum((unsigned char)*p) && *p != '_' && *p != '-') {
            return false;
        }
    }
    return true;
}

// Load a package.
//  - On success, sets *error = false and returns a new Package struct.
//  - If package not found at the given prefix, sets *error = false and returns NULL.
//  - On error (e.g. toml parsing error), sets *error = true and returns NULL.
static struct Package *
    load_package(const char *pkg_config_cmd,
                 struct HashTable *all_system_packages,
                 const char *prefix,   // ends in '/' or is ""
                 const char *filename,  // equals prefix + "package.toml"
                 const char *requested_name,  // NULL means "anything"
                 const char *requested_version,  // NULL means "anything"
                 bool *error)
{
    FILE *file = NULL;
    toml_table_t *conf = NULL;
    char *name = NULL;
    char *version = NULL;
    struct NameList *exported_modules = NULL;
    char *main_module = NULL;
    char *main_function = NULL;
    struct DepList *deps = NULL;
    struct DepList *system_packages = NULL;
    struct NameList *cflags = NULL;
    struct Package *package = NULL;
    *error = true;


    // Open and parse the file
    file = fopen(filename, "r");
    if (file == NULL) {
        if (errno == ENOENT) {
            // If file-not-found then silently ignore the error so that we can move on to
            // the next path.
            *error = false;
        } else {
            // On any other error (e.g. permissions problems), print error message, so
            // that the user can fix it.
            fprintf(stderr, "Failed to open: %s\n", filename);
        }
        goto end;
    }

    char errbuf[200];
    conf = toml_parse_file(file, errbuf, sizeof(errbuf));

    if (!conf) {
        fprintf(stderr, "Error while parsing %s: %s\n", filename, errbuf);
        goto end;
    }


    // Read "package" table
    toml_table_t *package_tbl = toml_table_table(conf, "package");
    if (!package_tbl) {
        fprintf(stderr, "%s: missing [package]\n", filename);
        goto end;
    }

    name = read_string(filename, package_tbl, "name", NULL);
    if (name == NULL) goto end;
    if (!valid_package_name(name)) {
        fprintf(stderr, "%s: invalid package name '%s'\n", filename, name);
        goto end;
    }

    version = read_string(filename, package_tbl, "version", "");

    // If name and version don't match the requested, then this counts as "not found"
    // i.e. we move on to the next component in the search path.
    if (requested_name != NULL && strcmp(name, requested_name) != 0) {
        *error = false;
        goto end;
    }
    if (requested_version != NULL && strcmp(version, requested_version) != 0) {
        *error = false;
        goto end;
    }


    // Read "modules" table
    toml_table_t *modules_tbl = toml_table_table(conf, "modules");
    if (!modules_tbl) {
        fprintf(stderr, "%s: missing [modules]\n", filename);
        goto end;
    }

    main_module = read_string(filename, modules_tbl, "main-module", "");
    if (main_module[0] == 0) {
        free(main_module);
        main_module = NULL;
    }

    main_function = read_string(filename, modules_tbl, "main-function", "");
    if (main_function[0] == 0) {
        free(main_function);
        main_function = NULL;
    }

    bool exports_array_error = false;
    toml_array_t *exports_array =
        toml_table_array_ext(filename,
                             modules_tbl,
                             "exported-modules",
                             &exports_array_error);
    if (exports_array_error) goto end;
    if (exports_array) {
        bool error;
        exported_modules = read_string_list(filename, exports_array, &error);
        if (error) goto end;
    }


    // Read "dependencies" and "system_packages" tables
    toml_table_t *dependencies_tbl = toml_table_table(conf, "dependencies");
    if (dependencies_tbl) {
        bool deps_error;
        deps = read_deps(filename, dependencies_tbl, &deps_error);
        if (deps_error) goto end;
    }

    toml_table_t *system_packages_tbl = toml_table_table(conf, "system-packages");
    if (system_packages_tbl) {
        bool system_packages_error;
        system_packages = read_deps(filename, system_packages_tbl, &system_packages_error);
        if (system_packages_error) goto end;
    }


    // Resolve system packages to cflags.
    // TODO: introduce some caching in case several packages use the same system_package?
    if (!resolve_system_packages(pkg_config_cmd, system_packages, &cflags, all_system_packages)) {
        goto end;
    }

    // Success. Create the Package struct.
    *error = false;
    package = alloc(sizeof(struct Package));
    package->name = name; name = NULL;
    package->version = version; version = NULL;
    package->deps = deps; deps = NULL;
    package->cflags = cflags; cflags = NULL;
    package->prefix = copy_string(prefix);
    package->exported_modules = exported_modules; exported_modules = NULL;
    package->main_module = main_module; main_module = NULL;
    package->main_function = main_function; main_function = NULL;

    // Fall through to "end"

  end:
    if (file) fclose(file);
    toml_free(conf);
    free(name);
    free(version);
    free(main_module);
    free(main_function);
    free_name_list(exported_modules);
    free_dep_list(deps);
    free_dep_list(system_packages);
    free_name_list(cflags);
    return package;
}

static bool does_file_exist(const char *name)
{
    FILE *f = fopen(name, "r");
    if (f) {
        fclose(f);
        return true;
    } else if (errno == ENOENT) {
        return false;
    } else {
        // We'll assume that this means the file exists, but cannot be read for some
        // reason!
        return true;
    }
}

// returns newly allocated ModulePathInfo (or NULL).
static struct ModulePathInfo * find_module_in_package(struct Package *package,
                                                      const char *module_name)
{
    // Look up .b file
    char *name = replace_dots_with_slashes(module_name);
    char *name2 = copy_string_4(package->prefix, "src/", name, ".b");
    free(name);
    name = NULL;

    if (does_file_exist(name2)) {

        struct ModulePathInfo *info = alloc(sizeof(struct ModulePathInfo));
        info->package_name = copy_string(package->name);
        info->b_filename = name2;
        info->c_filename = NULL;
        name2 = NULL;

        // Look up .c file
        char *name3 = copy_string(info->b_filename);
        name3[strlen(name3) - 1] = 'c';  // replace 'b' with 'c'
        if (does_file_exist(name3)) {
            info->c_filename = name3;
        } else {
            free(name3);
        }
        name3 = NULL;

        // Done
        return info;

    } else {
        // The module doesn't exist in this package
        free(name2);
        return NULL;
    }
}

static char * make_cache_key(const char * importer_package, const char * module_name)
{
    return copy_string_3(importer_package, ">", module_name);
}

static bool preload_module(const char *filename,
                           struct PackageLoader *loader,
                           struct Package *package,
                           const char *module_name)
{
    char *cache_key = make_cache_key(package->name, module_name);
    if (hash_table_contains_key(loader->path_infos, cache_key)) {
        free(cache_key);
        return true;
    }

    struct ModulePathInfo *info = find_module_in_package(package, module_name);
    if (info == NULL) {
        fprintf(stderr, "%s: Module '%s' not found in this package\n", filename, module_name);
        free(cache_key);
        return false;
    }

    hash_table_insert(loader->path_infos, cache_key, info);
    cache_key = NULL;
    return true;
}

static bool preload_exported_and_main_modules(const char *filename,
                                              struct PackageLoader *loader,
                                              struct Package *package)
{
    if (package->exported_modules == NULL && package->main_module == NULL) {
        fprintf(stderr, "%s: Package has no exported-modules or main-module\n", filename);
        return false;
    }
    for (struct NameList *name = package->exported_modules; name; name = name->next) {
        if (!preload_module(filename, loader, package, name->name)) {
            return false;
        }
    }
    if (package->main_module) {
        if (!preload_module(filename, loader, package, package->main_module)) {
            return false;
        }
    }
    return true;
}

static struct Package * load_dependencies(struct PackageLoader *loader,
                                          struct NameList *search_path,
                                          struct Package *package);

// If the package already exists (at same or higher version) then return it.
// Otherwise, load it from disk, add it to the loader, and return it.
// Each entry in "search_path" is either "" or ends in a slash.
// Each package is searched for in either $PKGNAME-$VERSION/package.toml
// or $PKGNAME/package.toml under each entry of the search path.
// If loading fails, prints error message and returns NULL.
static struct Package *
    find_package(struct PackageLoader *loader,
                 struct NameList *search_path,
                 char *requested_name,     // must be non-null
                 char *requested_version)  // must be non-null
{
    struct Package *package = NULL;
    char *filename = NULL;

    struct Package *existing_package = hash_table_lookup(loader->packages, requested_name);
    if (existing_package != NULL) {
        if (version_compare(existing_package->version, requested_version) >= 0) {
            // We already have that version or higher, so give them the existing package.
            package = existing_package;
        } else {
            // The existing package is no good, so remove it from the hash table.
            hash_table_remove(loader->packages, requested_name);
            free_package(existing_package);
            existing_package = NULL;
        }
    }

    for (struct NameList *node = search_path; !package && node; node = node->next) {

        // First search dir
        char *path = copy_string_3(node->name, requested_name, "/");
        free(filename);
        filename = copy_string_2(path, PACKAGE_TOML_NAME);
        bool error;
        package = load_package(loader->pkg_config_cmd,
                               loader->all_system_packages,
                               path,
                               filename,
                               requested_name,
                               requested_version,
                               &error);
        free(path);
        if (package == NULL && error) {
            free(filename);
            return NULL;
        }

        if (package == NULL) {
            // Second search dir
            path = copy_string_5(node->name, requested_name, "-", requested_version, "/");
            free(filename);
            filename = copy_string_2(path, PACKAGE_TOML_NAME);
            package = load_package(loader->pkg_config_cmd,
                                   loader->all_system_packages,
                                   path,
                                   filename,
                                   requested_name,
                                   requested_version,
                                   &error);
            free(path);
            if (package == NULL && error) {
                free(filename);
                return NULL;
            }
        }
    }

    if (package == NULL) {
        fprintf(stderr, "Package '%s' (version '%s') not found on search path\n", requested_name, requested_version);
        free(filename);
        return NULL;
    }

    // If we get here, loading was successful.

    if (existing_package == NULL) {
        // Add it to the hash table of all known packages
        hash_table_insert(loader->packages, package->name, package);

        // Preload all the exported_modules and main_module into the ModulePathInfo cache
        // (so that we can be sure that these modules do indeed exist on disk, before continuing).
        if (!preload_exported_and_main_modules(filename, loader, package)) {
            free(filename);
            return NULL;
        }
    }

    free(filename);

    return load_dependencies(loader, search_path, package);
}

static struct Package * load_dependencies(struct PackageLoader *loader,
                                          struct NameList *search_path,
                                          struct Package *package)
{
    struct DepList *deps = copy_dep_list(package->deps);
    char * package_name = copy_string(package->name);
    char * original_version = copy_string(package->version);

    while (deps) {
        // Load this dependency
        struct Package *dep_pkg = find_package(loader, search_path, deps->name, deps->min_version);
        if (dep_pkg == NULL) {
            // Propagate the error
            package = NULL;
            break;
        }

        // Update 'package' (it might have been upgraded to a later version)
        package = hash_table_lookup(loader->packages, package_name);
        if (package == NULL) {
            fatal_error("unexpected: package was removed without replacing it");
        }
        if (strcmp(package->version, original_version) != 0) {
            // We have a newer version of the package; return that
            break;
        }

        // Move on to next dependency
        struct DepList *next = deps->next;
        free(deps->name);
        free(deps->min_version);
        free(deps);
        deps = next;
    }

    free(original_version);
    free(package_name);
    free_dep_list(deps);
    return package;
}

struct PackageLoader * alloc_package_loader(const char *pkg_config_cmd)
{
    struct PackageLoader * loader = alloc(sizeof(struct PackageLoader));
    loader->packages = new_hash_table();
    loader->path_infos = new_hash_table();
    loader->root_package = NULL;
    loader->pkg_config_cmd = copy_string(pkg_config_cmd);
    loader->all_system_packages = new_hash_table();
    loader->libs = NULL;
    return loader;
}

void free_package_loader(struct PackageLoader *loader)
{
    const char *key;
    void *value;
    struct HashIterator *iter = new_hash_iterator(loader->packages);
    while (hash_iterator_next(iter, &key, &value)) {
        free_package(value);
    }
    free_hash_iterator(iter);
    free_hash_table(loader->packages);

    iter = new_hash_iterator(loader->path_infos);
    while (hash_iterator_next(iter, &key, &value)) {
        free((char*)key);
        free_path_info(value);
    }
    free_hash_iterator(iter);
    free_hash_table(loader->path_infos);

    free(loader->pkg_config_cmd);

    if (loader->all_system_packages) {
        hash_table_for_each(loader->all_system_packages, ht_free_key_and_value, NULL);
        free_hash_table(loader->all_system_packages);
    }

    free_name_list(loader->libs);

    free(loader);
}

bool load_root_package_and_dependencies(struct PackageLoader *loader,
                                        const char *prefix,
                                        struct NameList *search_path)
{
    // Load root package (filename = prefix + "package.toml")
    char *filename = copy_string_2(prefix, PACKAGE_TOML_NAME);
    bool error;
    struct Package *package = load_package(loader->pkg_config_cmd,
                                           loader->all_system_packages,
                                           prefix,
                                           filename,
                                           NULL,
                                           NULL,
                                           &error);
    if (package == NULL && !error) {
        fprintf(stderr, "File not found: %s\n", filename);
    }
    if (package == NULL) {
        free(filename);
        return false;
    }

    // Insert into the hash table
    hash_table_insert(loader->packages, package->name, package);

    // Preload exported & main modules
    if (!preload_exported_and_main_modules(filename, loader, package)) {
        free(filename);
        return false;
    }

    free(filename);
    filename = NULL;

    // Backup version, in case some dependency tries to replace the root with
    // another package!
    char *original_version = copy_string(package->version);

    // Load dependencies of the root
    package = load_dependencies(loader, search_path, package);

    // Propagate loading errors
    if (package == NULL) {
        free(original_version);
        return false;
    }

    // Was it replaced?
    if (strcmp(original_version, package->version) != 0) {
        fprintf(stderr,
                "Root package (version '%s') was replaced with newer version ('%s') by a dependency!\n",
                original_version,
                package->version);
        free(original_version);
        return false;
    }

    loader->root_package = package;
    free(original_version);

    // Call pkg-config to fill in libs.
    return resolve_libs(loader->pkg_config_cmd, &loader->all_system_packages, &loader->libs);
}

const char * get_root_package_name(struct PackageLoader *loader)
{
    return loader->root_package->name;
}

struct NameList * get_root_exported_modules(struct PackageLoader *loader)
{
    return loader->root_package->exported_modules;
}

const char * get_root_main_module(struct PackageLoader *loader)
{
    return loader->root_package->main_module;
}

const char * get_root_main_function(struct PackageLoader *loader)
{
    return loader->root_package->main_function;
}

struct ModulePathInfo * find_module(struct PackageLoader *loader,
                                    const char *importer_package,
                                    const char *module_name)
{
    // Check cache.
    char *cache_key = make_cache_key(importer_package, module_name);

    const char *key;
    void *value;
    hash_table_lookup_2(loader->path_infos, cache_key, &key, &value);
    if (key != NULL) {
        free(cache_key);
        return value;
    }

    // Check the importer package itself - this "shadows" the same module name
    // in any of the dependencies.
    struct Package *package = hash_table_lookup(loader->packages, importer_package);
    struct ModulePathInfo *info = find_module_in_package(package, module_name);

    if (info == NULL) {

        // If it is not found in the main package then see if any of the dependencies
        // export this module.
        for (struct DepList *dep = package->deps; dep; dep = dep->next) {
            struct Package *dep_package = hash_table_lookup(loader->packages, dep->name);

            bool found = false;
            for (struct NameList *node = dep_package->exported_modules; node; node = node->next) {
                if (strcmp(node->name, module_name) == 0) {
                    found = true;
                    break;
                }
            }
            if (found) {
                struct ModulePathInfo *new_info = find_module_in_package(dep_package, module_name);
                if (new_info) {
                    if (info) {
                        fprintf(stderr, "Clash of module names: module '%s' (imported in package '%s') is exported by multiple dependencies: '%s' and '%s'",
                                module_name,
                                importer_package,
                                info->package_name,
                                new_info->package_name);
                        free_path_info(info);
                        free_path_info(new_info);
                        return NULL;
                    } else {
                        info = new_info;
                    }
                }
            }
        }
    }

    // Add to cache and return.
    hash_table_insert(loader->path_infos, cache_key, info);
    return info;
}

struct NameList * get_package_cflags(struct PackageLoader *loader,
                                     const char *package_name)
{
    struct Package *pkg = hash_table_lookup(loader->packages, package_name);
    if (pkg == NULL) {
        fatal_error("get_package_cflags: package not found");
    }
    return pkg->cflags;
}

struct NameList * get_package_libs(struct PackageLoader *loader)
{
    return loader->libs;
}

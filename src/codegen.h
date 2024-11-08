/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef CODEGEN_H
#define CODEGEN_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

struct HashTable;
struct Module;

// Codegen a module. Writes C code to "c_output_file"
// and header code to "h_output_file".
// Also writes metadata into the codegen_env.

void codegen_module(FILE *c_output_file,
                    FILE *h_output_file,
                    struct HashTable *codegen_env,
                    struct Module *module);


// Write out a C 'main' function that calls the given Babylon function.

void codegen_main_function(FILE *c_output_file,
                           struct Module *module,
                           const char *function_name);


// Access the codegen_env

struct HashTable *new_codegen_env();
void free_codegen_env(struct HashTable *codegen_env);

#endif

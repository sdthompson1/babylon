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

// Codegen a module. Writes assembly code to the given FILE*.
// Also writes metadata into the codegen_env.

void codegen_module(FILE *asm_output_file,
                    struct HashTable *codegen_env,
                    struct Module *module,
                    bool root,   // Is this the root module?
                    bool generate_main);  // Should 'main' be generated? (relevant only if root==true)


// Access the codegen_env

struct HashTable *new_codegen_env();
void free_codegen_env(struct HashTable *codegen_env);

#endif

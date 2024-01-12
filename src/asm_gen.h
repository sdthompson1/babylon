/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef ASM_GEN_H
#define ASM_GEN_H

// Module for generating assembly code.

// For simplicity we only support a subset of what the x86 instruction
// set can do. E.g. no fancy indexed addressing modes; no memory
// operands in ALU instructions; only 64-bit ALU operations supported.

// This does mean the code we generate is fairly poor quality, but at
// least it keeps the code generator simple. Perhaps later we can add
// more optimised code generation (or, more likely, support a mode
// where we compile to C, and get a C compiler to do the hard work!).

#include "opcode.h"

#include <stdint.h>
#include <stdio.h>

#define LABEL_LEN 40   // Includes null terminator

struct AsmGen;

// TODO: Support other targets. For now we assume x86-64, Linux, and the GNU assembler.
struct AsmGen *new_asm_gen(FILE *output_asm_file);
void free_asm_gen(struct AsmGen *gen);

int asm_get_num_regs(struct AsmGen *gen);
uint64_t asm_get_guard_page_size(struct AsmGen *gen);


// Move instructions

void asm_mov_reg_reg(struct AsmGen *gen, int dest_reg_num, int src_reg_num);

void asm_swap_regs(struct AsmGen *gen, int reg_num_1, int reg_num_2);

void asm_mov_reg_imm(struct AsmGen *gen, int dest_reg_num, uint64_t value);


// ALU operations
// (For unary operations, src_reg should equal dest_reg)

void asm_alu_reg_reg(struct AsmGen *gen, enum Opcode op, int dest_reg_num, int src_reg_num);
void asm_alu_reg_imm(struct AsmGen *gen, enum Opcode op, int dest_reg_num, uint64_t src_immediate);  // only ADD, AND, SUB supported for the moment!


// Load and store instructions

// e.g. movzx eax, word ptr [rbp+offset]
void asm_load_from_frame(struct AsmGen *gen,
                         int dest_reg_num, int64_t frame_offset,
                         bool sign_extend, int size_in_bytes);

// e.g. movsx rax, dword ptr [rcx+offset]
void asm_load_from_reg_address(struct AsmGen *gen,
                               int dest_reg_num, int64_t offset, int addr_reg_num,
                               bool sign_extend, int size_in_bytes);

// e.g. mov [rbp+offset], cl
void asm_store_to_frame(struct AsmGen *gen,
                        int64_t frame_offset, int src_reg_num,
                        int size_in_bytes);
void asm_store_to_stack(struct AsmGen *gen,
                        int64_t stack_offset, int src_reg_num,
                        int size_in_bytes);

// e.g. mov [rcx+offset], eax
void asm_store_to_reg_address(struct AsmGen *gen,
                              int64_t offset, int addr_reg_num, int src_reg_num,
                              int size_in_bytes);

// e.g. lea rax, [rbp+offset]
void asm_lea_frame_slot(struct AsmGen *gen, int dest_reg_num, int64_t frame_offset);
void asm_lea_stack_slot(struct AsmGen *gen, int dest_reg_num, int64_t sp_offset);

// Globals - creation
void asm_begin_global_constant(struct AsmGen *gen, const char *name,
                               bool may_include_addrs, bool exported);
void asm_insert_byte(struct AsmGen *gen, uint8_t x);
void asm_insert_wyde(struct AsmGen *gen, uint16_t x);
void asm_insert_tetra(struct AsmGen *gen, uint32_t x);
void asm_insert_octa(struct AsmGen *gen, uint64_t x);
void asm_insert_global_addr(struct AsmGen *gen, const char *label);
void asm_end_global_constant(struct AsmGen *gen);

// Globals - access
void asm_load_global(struct AsmGen *gen,
                     int dest_reg_num, const char *label,
                     bool sign_extend, int size_in_bytes);

void asm_lea_global(struct AsmGen *gen, int dest_reg_num, const char *label);


// Branches and jumps
// (For now, it may be assumed that a previous ALU instruction has set the
// flags, so that e.g. asm_branch_if_zero may be used after an OP_SUB.)

void asm_make_local_label(struct AsmGen *gen, uint64_t number, char label[LABEL_LEN]);
void asm_label(struct AsmGen *gen, const char *label);
void asm_local_jump(struct AsmGen *gen, const char *label);
void asm_test(struct AsmGen *gen, int reg_num, int num_bytes);  // num_bytes = 1 or 8
void asm_branch_if_zero(struct AsmGen *gen, const char *label);
void asm_branch_if_nonzero(struct AsmGen *gen, const char *label);
void asm_branch_if_above(struct AsmGen *gen, const char *label);


// Calls, returns, stack-pointer operations, pushing and popping registers

void asm_call(struct AsmGen *gen, const char *name);
void asm_enter(struct AsmGen *gen, uint64_t delta);  // push fp; move sp to fp; subtract delta from sp
void asm_leave(struct AsmGen *gen);  // move fp to sp; pop fp
void asm_ret(struct AsmGen *gen);

void asm_mov_reg_sp(struct AsmGen *gen, int dest_reg_num);
void asm_sub_reg_from_sp(struct AsmGen *gen, int reg_num);
void asm_add_imm_to_sp(struct AsmGen *gen, uint64_t amount);
void asm_sub_imm_from_sp(struct AsmGen *gen, uint64_t amount);

void asm_push_reg(struct AsmGen *gen, int src_reg_num);
void asm_pop_reg(struct AsmGen *gen, int dest_reg_num);
void asm_pop_sp(struct AsmGen *gen);     // load sp from (sp)

void asm_probe_sp(struct AsmGen *gen);


// Calling convention information

int asm_num_register_args(struct AsmGen *gen);
int asm_arg_num_to_reg_num(struct AsmGen *gen, int arg_num);
int asm_get_return_reg_num(struct AsmGen *gen);
bool asm_is_caller_save(struct AsmGen *gen, int reg_num); // note args and return are considered caller-save
unsigned int asm_get_stack_alignment(struct AsmGen *gen);  // stack must have this alignment at a call instruction


// Function management

void asm_new_function(struct AsmGen *gen);
void asm_rewind_to_prologue(struct AsmGen *gen, const char *function_name);
void asm_end_function(struct AsmGen *gen);

#endif

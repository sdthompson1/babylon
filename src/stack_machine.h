/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef STACK_MACHINE_H
#define STACK_MACHINE_H

// A stack machine abstraction. This API consumes code for a
// hypothetical "stack machine" and outputs corresponding assembly
// code.

#include "opcode.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

struct StackMachine;


//---------------------------------------------------------------------------
// Construction and destruction
//---------------------------------------------------------------------------

// The caller should open the output_asm_file before calling stk_create,
// and close it after calling stk_destroy. Functions will be written to the
// output file as they are created.
struct StackMachine * stk_create(FILE *output_asm_file);
void stk_destroy(struct StackMachine *mc);


//---------------------------------------------------------------------------
// Pushing and popping stack values
//---------------------------------------------------------------------------

// The stack machine maintains a stack of 64-bit integers (or
// pointers). The following functions will push a constant, push a new
// copy of any stack value, swap two stack values, or pop the top
// value (discarding it).

void stk_const(struct StackMachine *mc, uint64_t value);
void stk_dup(struct StackMachine *mc, int n);  //n=0 for top of stack, 1 for just below, etc.
void stk_swap(struct StackMachine *mc, int n1, int n2);
void stk_pop(struct StackMachine *mc);


//---------------------------------------------------------------------------
// ALU operations
//---------------------------------------------------------------------------

// This will pop one or two values from the stack, do one of the
// operations from opcode.h, and push the result.

// For binary operations, the "RHS" operand is on top of stack, and
// the "LHS" below.

// Note that the comparison operations (OP_EQ, etc.) are only
// guaranteed to set the lowest byte of the resulting stack value (to
// 0 or 1). The other 7 bytes will contain garbage.

void stk_alu(struct StackMachine *mc, enum Opcode op);


//---------------------------------------------------------------------------
// Local variables
//---------------------------------------------------------------------------

// Local variables can be created and destroyed at any time. A local
// can be 1, 2, 4 or 8 bytes in size (pointers are assumed to be 8
// bytes).

// (Note the variable might end up being allocated to an 8-byte
// register, so the size should be viewed as a minimum.)

// Using "stk_set_local" will pop a value from the stack and store it
// into the given local. "stk_get_local" will do the reverse, pushing
// a local's value onto the stack.

// Any locals created before "stk_finish_arguments" are considered
// formal parameters of the current function.

// A "mem block" is a special type of local representing a region of
// memory on the machine stack. Using "get_local" on a mem_block will
// push a pointer. (Using "set_local" on a mem_block is not allowed.)

// Fixed sized mem blocks can be created and destroyed in any order,
// but variable sized blocks must be destroyed in reverse order of
// creation. Also, variable size blocks created inside the scope of a
// "then", "else" or "loop" must be destroyed before that scope ends.

// When creating a variable sized block, the size will be popped from
// the stack.

// The name strings in the below functions are copied (not handed
// over).

void stk_create_local(struct StackMachine *mc, const char *name, bool is_signed, int num_bytes);
void stk_create_mem_block_fixed_size(struct StackMachine *mc, const char *name, uint64_t size);
void stk_create_mem_block_variable_size(struct StackMachine *mc, const char *name);

void stk_destroy_local(struct StackMachine *mc, const char *name);

void stk_finish_arguments(struct StackMachine *mc);

void stk_get_local(struct StackMachine *mc, const char *name);
void stk_set_local(struct StackMachine *mc, const char *name);


//---------------------------------------------------------------------------
// Global variables
//---------------------------------------------------------------------------

// Global constants - creation
void stk_begin_global_constant(struct StackMachine *mc, const char *name,
                               bool may_include_addrs, bool exported);
void stk_insert_byte(struct StackMachine *mc, uint8_t x);
void stk_insert_wyde(struct StackMachine *mc, uint16_t x);
void stk_insert_tetra(struct StackMachine *mc, uint32_t x);
void stk_insert_octa(struct StackMachine *mc, uint64_t x);
void stk_insert_global_addr(struct StackMachine *mc, const char *name);
void stk_end_global_constant(struct StackMachine *mc);

// Global constants - access
void stk_push_global_addr(struct StackMachine *mc, const char *name);
void stk_push_global_value(struct StackMachine *mc, const char *name,
                           bool is_signed, int size_in_bytes);


//---------------------------------------------------------------------------
// Memory operations
//---------------------------------------------------------------------------

// Note: currently we completely ignore alignment, taking advantage of
// x86's ability to do unaligned memory operations. This does lead to
// some loss of speed (although apparently, nowadays, not as much as
// it used to be) but it simplifies the code generator.

// Pop a pointer, push the value loaded from that address.
// num_bytes must be 1, 2, 4 or 8.
// The value is either zero- or sign-extended to an 8-byte stack value.
void stk_load(struct StackMachine *mc, bool is_signed, int num_bytes);

// Pop a value (top of stack) and address (just below) and write the
// value to the address.
// num_bytes must be 1, 2, 4 or 8.
void stk_store(struct StackMachine *mc, int num_bytes);

// Pop a source pointer (top of stack) and dest pointer (just below)
// and do a memcpy from source to destination.
void stk_memcpy_fixed_size(struct StackMachine *mc, uint64_t size);

// Same but the size is also on the stack (above the two pointers).
void stk_memcpy_variable_size(struct StackMachine *mc);

// Clear a block of memory to zero. Pops pointer from the stack.
// In the variable size case, size is also on the stack (above the pointer).
void stk_memclear_fixed_size(struct StackMachine *mc, uint64_t size);
void stk_memclear_variable_size(struct StackMachine *mc);


//---------------------------------------------------------------------------
// Loops and conditionals
//---------------------------------------------------------------------------

void stk_cond_if_zero(struct StackMachine *mc, int num_bytes);  // num_bytes = 1 or 8
void stk_cond_if_nonzero(struct StackMachine *mc, int num_bytes);
void stk_cond_else(struct StackMachine *mc);
void stk_cond_endif(struct StackMachine *mc);

void stk_loop_begin(struct StackMachine *mc);
void stk_loop_end(struct StackMachine *mc);
void stk_loop_goto_beginning(struct StackMachine *mc);
void stk_loop_goto_end(struct StackMachine *mc);

// This returns true if the current position is reachable (i.e.
// haven't passed a loop_goto_begin, loop_goto_end, or
// return_from_function)
bool stk_is_reachable(struct StackMachine *mc);


//---------------------------------------------------------------------------
// Function calls and returns
//---------------------------------------------------------------------------

// Begin the process of calling a function.
// Note: No variable sized memory blocks may be created until after
// "stk_emit_function_call".
void stk_prepare_function_call(struct StackMachine *mc, int num_args);

// Pop the topmost value from the stack and pass it to the function as
// an argument. (Arguments should be pass in right-to-left order, for
// compatibility with C.)
void stk_load_function_argument(struct StackMachine *mc);

// Once all arguments are "loaded", call this to make the function
// call. The function return value (if any) will be pushed onto the
// stack. (function_name is copied.)
void stk_emit_function_call(struct StackMachine *mc, const char *function_name,
                            bool returns_value);

// Return from the current function. The stack should have either 0 or
// 1 value. In the latter case, the value on the stack is the return
// value from the function.
void stk_return_from_function(struct StackMachine *mc);


//---------------------------------------------------------------------------
// Function management
//---------------------------------------------------------------------------

// Begin a new function.
void stk_begin_function(struct StackMachine *mc, const char *function_name);

// Finish the current function.
void stk_end_function(struct StackMachine *mc);

// RTS functions should be added to the root module (only)
void stk_make_rts_functions(struct StackMachine *mc);


#endif

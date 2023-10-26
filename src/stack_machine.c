/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "asm_check_stack.h"
#include "asm_gen.h"
#include "error.h"
#include "hash_table.h"
#include "stack_machine.h"
#include "stack_machine_env.h"
#include "util.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct ControlNode {
    struct MachineEnv *saved_env;
    uint32_t saved_stack_depth;
    char label[LABEL_LEN];       // "else" or "endif" or loop end
    char loop_begin[LABEL_LEN];  // loop begin
    bool is_loop;
    struct ControlNode *next;
};

struct FunCallNode {
    int num_args;
    int args_done;
    struct FunCallNode *next;
};

struct StackMachine {
    struct AsmGen *asm_gen;

    struct MachineEnv *current_env;

    struct ControlNode *control_stack;
    struct FunCallNode *fun_call_stack;

    struct HashTable *fixed_size_mem_block_names;
    struct NameList *var_size_mem_block_names;

    // Current number of items on the abstract machine's stack
    uint32_t stack_depth;

    struct ArgInfo *args;
    struct ArgInfo **args_tail;  // only non-NULL when ready to accept args.

    uint64_t frame_size;
    uint32_t used_regs;

    uint64_t next_label_num;

    char epilogue_label[LABEL_LEN];

    const char *function_name;  // allocated
};


static void stk_new_label(struct StackMachine *mc, char label[LABEL_LEN])
{
    asm_make_local_label(mc->asm_gen, mc->next_label_num++, label);
}

struct StackMachine *stk_create(FILE *output_asm_file)
{
    struct StackMachine *mc = alloc(sizeof(struct StackMachine));

    mc->asm_gen = new_asm_gen(output_asm_file);

    mc->current_env = NULL;

    mc->control_stack = NULL;
    mc->fun_call_stack = NULL;

    mc->fixed_size_mem_block_names = new_hash_table();
    mc->var_size_mem_block_names = NULL;

    mc->stack_depth = 0;

    mc->args = NULL;
    mc->args_tail = NULL;

    mc->frame_size = 0;
    mc->used_regs = 0;

    mc->next_label_num = 0;
    mc->epilogue_label[0] = 0;

    mc->function_name = NULL;

    return mc;
}

void stk_destroy(struct StackMachine *mc)
{
    if (mc->current_env != NULL || mc->control_stack != NULL
        || mc->fun_call_stack != NULL || mc->var_size_mem_block_names != NULL
        || mc->args != NULL || mc->args_tail != NULL || mc->function_name != NULL) {
        fatal_error("stk_destroy: invalid state");
    }

    free_asm_gen(mc->asm_gen);
    free_hash_table(mc->fixed_size_mem_block_names);
    free(mc);
}


// Some simple wrappers around the functions in stack_machine_env.h:

static void add_var(struct StackMachine *mc, const char *name,
                    bool is_signed, uint64_t num_bytes,
                    bool lockable)
{
    add_variable(mc->current_env, mc->asm_gen, name, is_signed, num_bytes, lockable);
}

static void remove_var(struct StackMachine *mc, const char *name)
{
    remove_variable(mc->current_env, name);
}

static int lock_var(struct StackMachine *mc, const char *name, bool preserve_value)
{
    return lock_variable(mc->current_env, mc->asm_gen, name, preserve_value);
}

static void unlock_var(struct StackMachine *mc, const char *name)
{
    unlock_variable(mc->current_env, name);
}


static void update_frame_size_and_used_regs(struct StackMachine *mc, struct MachineEnv *env)
{
    if (env) {
        uint64_t frame_size = get_frame_size(env);
        uint16_t used_regs = get_used_regs(env);
        if (frame_size > mc->frame_size) {
            mc->frame_size = frame_size;
        }
        mc->used_regs |= used_regs;
    }
}

static void reconcile(struct StackMachine *mc, struct ControlNode *node)
{
    if (mc->stack_depth != node->saved_stack_depth) {
        fatal_error("reconcile failed, stack depths are different");
    }

    if (mc->current_env == NULL) {
        if (node->saved_env != NULL) {
            mc->current_env = copy_machine_env(node->saved_env);
        }
    } else if (node->saved_env != NULL) {
        reconcile_envs(mc->current_env, node->saved_env, mc->asm_gen);
        update_frame_size_and_used_regs(mc, mc->current_env);
        free_machine_env(mc->current_env);
        mc->current_env = copy_machine_env(node->saved_env);
    }
}

static void kill_current_block(struct StackMachine *mc)
{
    update_frame_size_and_used_regs(mc, mc->current_env);
    free_machine_env(mc->current_env);
    mc->current_env = NULL;
}


#define VAR_LEN 20
#define MAX_STACK_DEPTH 1000000

// Return the variable name corresponding to a particular stack position.
// level=0 means top of stack, level=1 means just below top, etc.
static void stk_var_name(struct StackMachine *mc, uint32_t level, char buf[VAR_LEN])
{
    if (level >= mc->stack_depth) {
        fatal_error("stack_var_name: level is below base of stack");
    }
    sprintf(buf, "stk:%" PRIu32, mc->stack_depth - 1 - level);
}

// Add a new (8-byte) item to the stack. Write the name of the new variable to 'name'.
static void stk_push(struct StackMachine *mc, char name[VAR_LEN])
{
    if (mc->stack_depth >= MAX_STACK_DEPTH) {
        fatal_error("stack too deep");
    }
    ++ mc->stack_depth;
    stk_var_name(mc, 0, name);
    add_var(mc, name, false, 8, true);
}

// Pop the topmost item from the stack
void stk_pop(struct StackMachine *mc)
{
    if (mc->stack_depth == 0) {
        fatal_error("stack is empty");
    }

    char name[VAR_LEN];
    stk_var_name(mc, 0, name);
    remove_var(mc, name);

    mc->stack_depth --;
}

void stk_const(struct StackMachine *mc, uint64_t value)
{
    // create a new stack value, put it in a register
    char name[VAR_LEN];
    stk_push(mc, name);
    int reg = lock_var(mc, name, false);

    // set the register to the desired value
    asm_mov_reg_imm(mc->asm_gen, reg, value);

    // unlock
    unlock_var(mc, name);
}

void stk_dup(struct StackMachine *mc, int n)
{
    char src_name[VAR_LEN];
    stk_var_name(mc, n, src_name);
    int src_reg = lock_var(mc, src_name, true);

    char dest_name[VAR_LEN];
    stk_push(mc, dest_name);
    int dest_reg = lock_var(mc, dest_name, false);

    asm_mov_reg_reg(mc->asm_gen, dest_reg, src_reg);

    unlock_var(mc, dest_name);
    unlock_var(mc, src_name);
}

void stk_swap(struct StackMachine *mc, int n0, int n1)
{
    char name0[VAR_LEN];
    char name1[VAR_LEN];
    stk_var_name(mc, n0, name0);
    stk_var_name(mc, n1, name1);
    swap_variables(mc->current_env, name0, name1);
}

void stk_alu(struct StackMachine *mc, enum Opcode op)
{
    if (is_unary_opcode(op)) {
        // lock top of stack into a register
        char tos_name[VAR_LEN];
        stk_var_name(mc, 0, tos_name);
        int tos_reg = lock_var(mc, tos_name, true);

        // do the operation in-place
        asm_alu_reg_reg(mc->asm_gen, op, tos_reg, tos_reg);

        // unlock
        unlock_var(mc, tos_name);

    } else {
        // lock top 2 elements into registers
        char rhs_name[VAR_LEN];
        stk_var_name(mc, 0, rhs_name);
        int rhs_reg = lock_var(mc, rhs_name, true);

        char lhs_name[VAR_LEN];
        stk_var_name(mc, 1, lhs_name);
        int lhs_reg = lock_var(mc, lhs_name, true);

        // do the operation (computing result into the lhs)
        asm_alu_reg_reg(mc->asm_gen, op, lhs_reg, rhs_reg);

        // unlock
        unlock_var(mc, lhs_name);
        unlock_var(mc, rhs_name);

        // pop the rhs
        stk_pop(mc);
    }
}

void stk_create_local(struct StackMachine *mc, const char *name, bool is_signed, int num_bytes)
{
    if (mc->args_tail == NULL) {
        // Locals just become variables in the MachineEnv.
        add_var(mc, name, is_signed, num_bytes, true);
    } else {
        // Args are saved until the stk_finish_arguments call
        struct ArgInfo *info = alloc(sizeof(struct ArgInfo));
        info->name = copy_string(name);
        info->is_signed = is_signed;
        info->size = num_bytes;
        info->next = NULL;
        *(mc->args_tail) = info;
        mc->args_tail = &(info->next);
    }
}

void stk_create_mem_block_fixed_size(struct StackMachine *mc, const char *name, uint64_t size)
{
    // Fixed-sized memory blocks become (non-lockable) variables in the MachineEnv.
    add_var(mc, name, false, size, false);

    // Also remember the names of all fixed-size memory blocks in a hash table.
    hash_table_insert(mc->fixed_size_mem_block_names, copy_string(name), NULL);
}

void stk_create_mem_block_variable_size(struct StackMachine *mc, const char *name)
{
    // Get the size (top of stack) into a register
    char size_name[VAR_LEN];
    stk_var_name(mc, 0, size_name);
    int size_reg = lock_var(mc, size_name, true);

    // Round size up to a multiple of the stack alignment,
    // also adding another 8 bytes for our pushed pointer
    uint64_t stack_align = asm_get_stack_alignment(mc->asm_gen);
    asm_alu_reg_imm(mc->asm_gen, OP_ADD, size_reg, stack_align - 1u + 8u);
    asm_alu_reg_imm(mc->asm_gen, OP_AND, size_reg, ~ (stack_align - 1u));

    // Create a new variable to hold a pointer to the memory block
    add_var(mc, name, false, 8, true);
    int ptr_reg = lock_var(mc, name, false);

    // Create a temp variable
    const char *temp_name = ":tmp:";
    add_var(mc, temp_name, false, 8, true);
    int temp_reg = lock_var(mc, temp_name, false);


    // First of all do a check_stack. This is always needed because we don't know
    // anything about the location of sp at this point, and also we don't know how
    // big the allocation is.
    asm_mov_reg_reg(mc->asm_gen, temp_reg, 0);    // save r0
    asm_mov_reg_reg(mc->asm_gen, 0, size_reg);    // put size in r0
    asm_call(mc->asm_gen, "rts_check_stack");
    asm_mov_reg_reg(mc->asm_gen, 0, temp_reg);    // restore r0

    // Now back up sp to the temp_reg
    asm_mov_reg_sp(mc->asm_gen, temp_reg);

    // Deduct size from sp. Use the newly created space
    // (plus 8 bytes) as the pointer to the memory block.
    asm_sub_reg_from_sp(mc->asm_gen, size_reg);
    asm_lea_stack_slot(mc->asm_gen, ptr_reg, 8);

    // Store the backed up sp value
    asm_store_to_stack(mc->asm_gen, 0, temp_reg, 8);

    // Unlock, and pop the size from the stack.
    unlock_var(mc, name);
    unlock_var(mc, size_name);
    stk_pop(mc);
    unlock_var(mc, temp_name);
    remove_var(mc, temp_name);

    // Finally, remember the name of this varsize block, so that we
    // can free it later.
    struct NameList *node = alloc(sizeof(struct NameList));
    node->name = copy_string(name);
    node->next = mc->var_size_mem_block_names;
    mc->var_size_mem_block_names = node;
}

void stk_destroy_local(struct StackMachine *mc, const char *name)
{
    struct NameList *node = mc->var_size_mem_block_names;

    if (node && strcmp(node->name, name) == 0) {
        // We are destroying the topmost var sized mem block.

        // Restore the saved sp value from the stack.
        if (mc->current_env != NULL) {
            asm_pop_sp(mc->asm_gen);
        }

        // Get rid of the node from our list.
        mc->var_size_mem_block_names = node->next;
        free((char*)node->name);
        free(node);
    }

    // If it was a fixed-size mem block then remove it
    const char *key;
    hash_table_lookup_2(mc->fixed_size_mem_block_names, name, &key, NULL);
    if (key) {
        hash_table_remove(mc->fixed_size_mem_block_names, name);
        free((char*)key);
    }

    // We don't need the local in the env any more.
    if (mc->current_env != NULL) {
        remove_var(mc, name);
    }
}

void stk_finish_arguments(struct StackMachine *mc)
{
    add_arg_variables(mc->current_env, mc->asm_gen, mc->args);
    mc->args_tail = NULL;

    while (mc->args) {
        free((char*)mc->args->name);
        struct ArgInfo *to_free = mc->args;
        mc->args = mc->args->next;
        free(to_free);
    }
}

void stk_get_local(struct StackMachine *mc, const char *name)
{
    // If the local is a fixed size mem block, then we want its
    // address.

    // Otherwise, we want the value (this includes the var size mem
    // block case, because var size mem blocks are represented as
    // pointer variables).

    char tos_name[VAR_LEN];
    stk_push(mc, tos_name);
    int tos_reg = lock_var(mc, tos_name, false);

    if (hash_table_contains_key(mc->fixed_size_mem_block_names, name)) {
        // compute fp + fp_offset into tos_reg
        asm_lea_frame_slot(mc->asm_gen, tos_reg, get_variable_fp_offset(mc->current_env, name));
        unlock_var(mc, tos_name);

    } else {
        // move the variable directly into tos_reg
        int var_reg = lock_var(mc, name, true);
        asm_mov_reg_reg(mc->asm_gen, tos_reg, var_reg);
        unlock_var(mc, name);
        unlock_var(mc, tos_name);
    }
}

void stk_set_local(struct StackMachine *mc, const char *name)
{
    char tos_name[VAR_LEN];
    stk_var_name(mc, 0, tos_name);
    int tos_reg = lock_var(mc, tos_name, true);

    int var_reg = lock_var(mc, name, false);

    asm_mov_reg_reg(mc->asm_gen, var_reg, tos_reg);

    unlock_var(mc, name);
    unlock_var(mc, tos_name);

    stk_pop(mc);
}

void stk_begin_global_constant(struct StackMachine *mc, const char *name,
                               bool may_include_addrs, bool exported)
{
    asm_begin_global_constant(mc->asm_gen, name, may_include_addrs, exported);
}

void stk_insert_byte(struct StackMachine *mc, uint8_t x)
{
    asm_insert_byte(mc->asm_gen, x);
}

void stk_insert_wyde(struct StackMachine *mc, uint16_t x)
{
    asm_insert_wyde(mc->asm_gen, x);
}

void stk_insert_tetra(struct StackMachine *mc, uint32_t x)
{
    asm_insert_tetra(mc->asm_gen, x);
}

void stk_insert_octa(struct StackMachine *mc, uint64_t x)
{
    asm_insert_octa(mc->asm_gen, x);
}

void stk_insert_global_addr(struct StackMachine *mc, const char *name)
{
    asm_insert_global_addr(mc->asm_gen, name);
}

void stk_end_global_constant(struct StackMachine *mc)
{
    asm_end_global_constant(mc->asm_gen);
}

void stk_push_global_addr(struct StackMachine *mc, const char *name)
{
    char tos_name[VAR_LEN];
    stk_push(mc, tos_name);
    int reg_num = lock_var(mc, tos_name, false);
    asm_lea_global(mc->asm_gen, reg_num, name);
    unlock_var(mc, tos_name);
}

void stk_push_global_value(struct StackMachine *mc, const char *name, bool is_signed, int size_in_bytes)
{
    char tos_name[VAR_LEN];
    stk_push(mc, tos_name);
    int reg_num = lock_var(mc, tos_name, false);
    asm_load_global(mc->asm_gen, reg_num, name, is_signed, size_in_bytes);
    unlock_var(mc, tos_name);
}

void stk_load(struct StackMachine *mc, bool is_signed, int num_bytes)
{
    char addr_name[VAR_LEN];
    stk_var_name(mc, 0, addr_name);
    int addr_reg = lock_var(mc, addr_name, true);

    asm_load_from_reg_address(mc->asm_gen, addr_reg, 0, addr_reg, is_signed, num_bytes);

    unlock_var(mc, addr_name);
}

void stk_store(struct StackMachine *mc, int num_bytes)
{
    char src_name[VAR_LEN];
    stk_var_name(mc, 0, src_name);
    int src_reg = lock_var(mc, src_name, true);

    char addr_name[VAR_LEN];
    stk_var_name(mc, 1, addr_name);
    int addr_reg = lock_var(mc, addr_name, true);

    asm_store_to_reg_address(mc->asm_gen, 0, addr_reg, src_reg, num_bytes);

    unlock_var(mc, src_name);
    stk_pop(mc);
    unlock_var(mc, addr_name);
    stk_pop(mc);
}

void stk_memcpy_fixed_size(struct StackMachine *mc, uint64_t size)
{
    // for large copies use memcpy_var_size
    if (size >= 128) {
        stk_const(mc, size);
        stk_memcpy_variable_size(mc);
        return;
    }

    char src_name[VAR_LEN];
    stk_var_name(mc, 0, src_name);
    int src_reg = lock_var(mc, src_name, true);

    char dest_name[VAR_LEN];
    stk_var_name(mc, 1, dest_name);
    int dest_reg = lock_var(mc, dest_name, true);

    const char *tmp_name = ":tmp:";
    add_var(mc, tmp_name, false, 8, true);
    int tmp_reg = lock_var(mc, tmp_name, false);

    int32_t offset = 0;

    while (size > 0) {
        int32_t amount;

        if (size >= 8) {
            amount = 8;
        } else if (size >= 4) {
            amount = 4;
        } else if (size >= 2) {
            amount = 2;
        } else {
            amount = 1;
        }

        asm_load_from_reg_address(mc->asm_gen, tmp_reg, offset, src_reg, false, amount);
        asm_store_to_reg_address(mc->asm_gen, offset, dest_reg, tmp_reg, amount);

        offset += amount;
        size -= amount;
    }

    unlock_var(mc, tmp_name);
    remove_var(mc, tmp_name);

    unlock_var(mc, dest_name);
    unlock_var(mc, src_name);

    stk_pop(mc);
    stk_pop(mc);
}

void stk_memcpy_variable_size(struct StackMachine *mc)
{
    // slow method - copy one byte at a time (and do some fairly
    // long-winded register shuffling while we are about it.)

    // (It might be useful if asm_gen had a "memcpy" operation, this
    // could compile to rep movsb on x86...)

    char count_name[VAR_LEN];
    stk_var_name(mc, 0, count_name);
    int count_reg = lock_var(mc, count_name, true);

    char src_name[VAR_LEN];
    stk_var_name(mc, 1, src_name);
    int src_reg = lock_var(mc, src_name, true);

    char dest_name[VAR_LEN];
    stk_var_name(mc, 2, dest_name);
    int dest_reg = lock_var(mc, dest_name, true);

    const char *tmp_name = ":tmp:";
    add_var(mc, tmp_name, false, 8, true);
    int tmp_reg = lock_var(mc, tmp_name, false);

    const char *one_name = ":one:";
    add_var(mc, one_name, false, 8, true);
    int one_reg = lock_var(mc, one_name, false);
    asm_mov_reg_imm(mc->asm_gen, one_reg, 1);

    // test count for first iteration
    asm_test(mc->asm_gen, count_reg, 8);

    // jump to end of loop
    char end_label[LABEL_LEN];
    stk_new_label(mc, end_label);
    asm_local_jump(mc->asm_gen, end_label);

    // start of loop
    char start_label[LABEL_LEN];
    stk_new_label(mc, start_label);
    asm_label(mc->asm_gen, start_label);

    // copy src to dest
    asm_load_from_reg_address(mc->asm_gen, tmp_reg, 0, src_reg, false, 1);
    asm_store_to_reg_address(mc->asm_gen, 0, dest_reg, tmp_reg, 1);

    // add one to src, and one to dest
    asm_alu_reg_reg(mc->asm_gen, OP_ADD, src_reg, one_reg);
    asm_alu_reg_reg(mc->asm_gen, OP_ADD, dest_reg, one_reg);

    // subtract one from count
    asm_alu_reg_reg(mc->asm_gen, OP_SUB, count_reg, one_reg);

    // if count is not zero, loop
    asm_label(mc->asm_gen, end_label);
    asm_branch_if_nonzero(mc->asm_gen, start_label);

    // done.
    unlock_var(mc, one_name);
    remove_var(mc, one_name);
    unlock_var(mc, tmp_name);
    remove_var(mc, tmp_name);

    unlock_var(mc, dest_name);
    unlock_var(mc, src_name);
    unlock_var(mc, count_name);

    stk_pop(mc);
    stk_pop(mc);
    stk_pop(mc);
}

void stk_memclear_fixed_size(struct StackMachine *mc, uint64_t size)
{
    // for large clears use memclear_var_size
    if (size >= 128) {
        stk_const(mc, size);
        stk_memclear_variable_size(mc);
        return;
    }

    char dest_name[VAR_LEN];
    stk_var_name(mc, 0, dest_name);
    int dest_reg = lock_var(mc, dest_name, true);

    const char *zero_name = ":zero:";
    add_var(mc, zero_name, false, 8, true);
    int zero_reg = lock_var(mc, zero_name, false);

    asm_mov_reg_imm(mc->asm_gen, zero_reg, 0);  // asm_gen should optimise this to xor reg, reg

    int32_t offset = 0;

    while (size > 0) {
        int32_t amount;

        if (size >= 8) {
            amount = 8;

        } else if (size >= 4) {
            amount = 4;

        } else if (size >= 2) {
            amount = 2;

        } else {
            amount = 1;
        }

        asm_store_to_reg_address(mc->asm_gen, offset, dest_reg, zero_reg, amount);

        offset += amount;
        size -= amount;
    }

    unlock_var(mc, zero_name);
    remove_var(mc, zero_name);

    unlock_var(mc, dest_name);
    stk_pop(mc);
}

void stk_memclear_variable_size(struct StackMachine *mc)
{
    // Similarly to stk_memcpy_variable_size, this is a bit slow; a
    // "memclear" or "rep stosb" operation in asm_gen might be useful.

    char count_name[VAR_LEN];
    stk_var_name(mc, 0, count_name);
    int count_reg = lock_var(mc, count_name, true);

    char dest_name[VAR_LEN];
    stk_var_name(mc, 1, dest_name);
    int dest_reg = lock_var(mc, dest_name, true);

    const char *zero_name = ":zero:";
    add_var(mc, zero_name, false, 8, true);
    int zero_reg = lock_var(mc, zero_name, false);

    const char *one_name = ":one:";
    add_var(mc, one_name, false, 8, true);
    int one_reg = lock_var(mc, one_name, false);

    // put 0 in the zero_reg, 1 in the one_reg
    asm_mov_reg_imm(mc->asm_gen, zero_reg, 0);
    asm_mov_reg_imm(mc->asm_gen, one_reg, 1);

    // test count for first iteration
    asm_test(mc->asm_gen, count_reg, 8);

    // jump to end of loop
    char end_label[LABEL_LEN];
    stk_new_label(mc, end_label);
    asm_local_jump(mc->asm_gen, end_label);

    // start of loop
    char start_label[LABEL_LEN];
    stk_new_label(mc, start_label);
    asm_label(mc->asm_gen, start_label);

    // write zero to dest
    asm_store_to_reg_address(mc->asm_gen, 0, dest_reg, zero_reg, 1);

    // add one to dest
    asm_alu_reg_reg(mc->asm_gen, OP_ADD, dest_reg, one_reg);

    // subtract one from count
    asm_alu_reg_reg(mc->asm_gen, OP_SUB, count_reg, one_reg);

    // if count is not zero, loop
    asm_label(mc->asm_gen, end_label);
    asm_branch_if_nonzero(mc->asm_gen, start_label);

    // done.
    unlock_var(mc, one_name);
    remove_var(mc, one_name);
    unlock_var(mc, zero_name);
    remove_var(mc, zero_name);

    unlock_var(mc, dest_name);
    unlock_var(mc, count_name);

    stk_pop(mc);
    stk_pop(mc);
}


static void pop_control_stack(struct StackMachine *mc)
{
    update_frame_size_and_used_regs(mc, mc->control_stack->saved_env);
    free_machine_env(mc->control_stack->saved_env);

    struct ControlNode *to_free = mc->control_stack;
    mc->control_stack = to_free->next;
    free(to_free);
}

static void stk_cond_if(struct StackMachine *mc, bool if_nonzero, int num_bytes)
{
#ifdef DEBUG_RECONCILE
    printf("stk_cond_if\n");
    print_env(mc->current_env);
    printf("\n");
#endif

    // label for the "else" or "endif"
    char label[LABEL_LEN];
    stk_new_label(mc, label);

    char tos_name[VAR_LEN];
    stk_var_name(mc, 0, tos_name);
    int tos_reg = lock_var(mc, tos_name, true);
    asm_test(mc->asm_gen, tos_reg, num_bytes);
    if (if_nonzero) {
        // "if_nonzero" means the *else* branch (which the branch is
        // going to) is the *zero* case.
        asm_branch_if_zero(mc->asm_gen, label);
    } else {
        asm_branch_if_nonzero(mc->asm_gen, label);
    }
    unlock_var(mc, tos_name);
    stk_pop(mc);

    struct ControlNode *node = alloc(sizeof(struct ControlNode));
    node->saved_env = copy_machine_env(mc->current_env);
    node->saved_stack_depth = mc->stack_depth;
    strcpy(node->label, label);
    node->is_loop = false;
    node->next = mc->control_stack;
    mc->control_stack = node;
}

void stk_cond_if_zero(struct StackMachine *mc, int num_bytes)
{
    stk_cond_if(mc, false, num_bytes);
}

void stk_cond_if_nonzero(struct StackMachine *mc, int num_bytes)
{
    stk_cond_if(mc, true, num_bytes);
}

void stk_cond_else(struct StackMachine *mc)
{
#ifdef DEBUG_RECONCILE
    printf("stk_cond_else\n");
    print_env(mc->current_env);
    printf("\n");
#endif

    // label for the "endif"
    char label[LABEL_LEN];
    stk_new_label(mc, label);

    // emit jump to endif
    if (mc->current_env != NULL) {
        asm_local_jump(mc->asm_gen, label);
    }

    // emit "else" label
    asm_label(mc->asm_gen, mc->control_stack->label);

    // update stored label to the "endif" label
    strcpy(mc->control_stack->label, label);

    // swap back to the env as it was at the original "if"-statement.
    struct MachineEnv *tmp = mc->control_stack->saved_env;
    mc->control_stack->saved_env = mc->current_env;
    mc->current_env = tmp;

    uint32_t tmp_s = mc->control_stack->saved_stack_depth;
    mc->control_stack->saved_stack_depth = mc->stack_depth;
    mc->stack_depth = tmp_s;
}

void stk_cond_endif(struct StackMachine *mc)
{
#ifdef DEBUG_RECONCILE
    printf("stk_cond_endif\n");
    print_env(mc->current_env);
    printf("\n");
#endif
    reconcile(mc, mc->control_stack);

    // emit "endif" label
    asm_label(mc->asm_gen, mc->control_stack->label);

    pop_control_stack(mc);
}

void stk_loop_begin(struct StackMachine *mc)
{
#ifdef DEBUG_RECONCILE
    printf("stk_loop_begin\n");
    print_env(mc->current_env);
    printf("\n");
#endif

    struct ControlNode *node = alloc(sizeof(struct ControlNode));
    node->saved_env = copy_machine_env(mc->current_env);
    node->saved_stack_depth = mc->stack_depth;
    stk_new_label(mc, node->label);
    stk_new_label(mc, node->loop_begin);
    node->is_loop = true;
    node->next = mc->control_stack;
    mc->control_stack = node;

    asm_label(mc->asm_gen, node->loop_begin);
}

void stk_loop_end(struct StackMachine *mc)
{
#ifdef DEBUG_RECONCILE
    printf("stk_loop_end -> ");
#endif
    // as it happens, this does exactly the same thing as stk_cond_endif
    // (but don't tell our callers that!)
    stk_cond_endif(mc);
}

static struct ControlNode * find_loop_node(struct StackMachine *mc)
{
    struct ControlNode *node = mc->control_stack;
    while (!node->is_loop) {
        node = node->next;
        if (node == NULL) {
            fatal_error("couldn't find loop node");
        }
    }
    return node;
}

void stk_loop_goto_beginning(struct StackMachine *mc)
{
#ifdef DEBUG_RECONCILE
    printf("stk_loop_goto_beginning\n");
#endif
    struct ControlNode *loop_begin_node = find_loop_node(mc);

    reconcile(mc, loop_begin_node);

    asm_local_jump(mc->asm_gen, loop_begin_node->loop_begin);

    kill_current_block(mc);
}

void stk_loop_goto_end(struct StackMachine *mc)
{
#ifdef DEBUG_RECONCILE
    printf("stk_loop_goto_end\n");
#endif
    struct ControlNode *loop_begin_node = find_loop_node(mc);

    reconcile(mc, loop_begin_node);

    asm_local_jump(mc->asm_gen, loop_begin_node->label);

    kill_current_block(mc);
}

bool stk_is_reachable(struct StackMachine *mc)
{
    return mc->current_env != NULL;
}


static void reserve_arg_registers(struct StackMachine *mc, int num_args)
{
    int max_reg_args = asm_num_register_args(mc->asm_gen);
    for (int arg_num = 0; arg_num < max_reg_args && arg_num < num_args; ++arg_num) {
        int reg_num = asm_arg_num_to_reg_num(mc->asm_gen, arg_num);
        reserve_register(mc->current_env, mc->asm_gen, reg_num);
    }
}

static void push_arg_registers(struct StackMachine *mc)
{
    struct FunCallNode *node = mc->fun_call_stack;

    int max_reg_args = asm_num_register_args(mc->asm_gen);
    int leftmost_done_arg = node->num_args - node->args_done;

    for ( int arg_num = leftmost_done_arg;
          arg_num < max_reg_args && arg_num < node->num_args;
          ++arg_num ) {
        int reg_num = asm_arg_num_to_reg_num(mc->asm_gen, arg_num);
        asm_push_reg(mc->asm_gen, reg_num);
        unreserve_register(mc->current_env, mc->asm_gen, reg_num);
    }
}

static void pop_arg_registers(struct StackMachine *mc)
{
    struct FunCallNode *node = mc->fun_call_stack;

    int max_reg_args = asm_num_register_args(mc->asm_gen);
    int leftmost_done_arg = node->num_args - node->args_done;

    int arg_num = max_reg_args - 1;
    if (arg_num >= node->num_args) {
        arg_num = node->num_args - 1;
    }
    for (; arg_num >= leftmost_done_arg; --arg_num) {
        int reg_num = asm_arg_num_to_reg_num(mc->asm_gen, arg_num);
        reserve_register(mc->current_env, mc->asm_gen, reg_num);
        asm_pop_reg(mc->asm_gen, reg_num);
    }

    // Ensure that all arg registers are still reserved
    reserve_arg_registers(mc, node->num_args);
}

static unsigned int stack_offset_for_call(struct StackMachine *mc)
{
    // how many bytes will we push to the stack?
    // (each reg arg, beyond asm_num_register_args, counts for 8 bytes)
    int num_bytes_pushed =
        (mc->fun_call_stack->num_args - asm_num_register_args(mc->asm_gen)) * 8;

    if (num_bytes_pushed < 0) {
        num_bytes_pushed = 0;
    }

    // round this up to the stack alignment.
    unsigned int num_bytes_needed = num_bytes_pushed;
    unsigned int stack_align = asm_get_stack_alignment(mc->asm_gen);
    num_bytes_needed += (stack_align - 1u);
    num_bytes_needed &= ~(stack_align - 1u);

    // the difference gives the stack offset required
    return num_bytes_needed - (unsigned int) num_bytes_pushed;
}

void stk_prepare_function_call(struct StackMachine *mc, int num_args)
{
    if (mc->fun_call_stack) {
        // if we are in the middle of preparing another function call,
        // then push all our work to the stack
        push_arg_registers(mc);
    }

    // Create a new FunCallNode
    struct FunCallNode *node = alloc(sizeof(struct FunCallNode));
    node->num_args = num_args;
    node->args_done = 0;
    node->next = mc->fun_call_stack;
    mc->fun_call_stack = node;

    // Reserve all the arg registers that we will need for this call
    reserve_arg_registers(mc, num_args);

    // Properly align the stack
    unsigned int offset = stack_offset_for_call(mc);
    if (offset != 0) {
        asm_sub_imm_from_sp(mc->asm_gen, offset);
    }
}

void stk_load_function_argument(struct StackMachine *mc)
{
    struct FunCallNode *node = mc->fun_call_stack;

    // let's get the argument into a register
    char name[VAR_LEN];
    stk_var_name(mc, 0, name);
    int reg = lock_var(mc, name, true);

    // figure out the arg number (args are loaded from right to left)
    node->args_done ++;
    int arg_num = node->num_args - node->args_done;
    int max_reg_args = asm_num_register_args(mc->asm_gen);

    if (arg_num >= max_reg_args) {
        // push the argument onto the stack (as 8-bytes...)
        asm_push_reg(mc->asm_gen, reg);
    } else {
        // copy it to the correct arg register
        asm_mov_reg_reg(mc->asm_gen, asm_arg_num_to_reg_num(mc->asm_gen, arg_num), reg);
    }

    // now pop the stack
    unlock_var(mc, name);
    stk_pop(mc);
}

void stk_emit_function_call(struct StackMachine *mc, const char *function_name,
                            bool returns_value)
{
    int num_regs = asm_get_num_regs(mc->asm_gen);
    int max_reg_args = asm_num_register_args(mc->asm_gen);
    int return_reg = asm_get_return_reg_num(mc->asm_gen);

    // "Reserve" all caller-save registers (or all the ones that are
    // not already reserved, at least). This will make sure we don't
    // have any important data in them before the call.
    for (int reg_num = 0; reg_num < num_regs; ++reg_num) {
        if (asm_is_caller_save(mc->asm_gen, reg_num)) {
            reserve_register(mc->current_env, mc->asm_gen, reg_num);
        }
    }

    // Call the function.
    asm_call(mc->asm_gen, function_name);

    // Undo any stack offset
    unsigned int offset = stack_offset_for_call(mc);
    if (offset != 0) {
        asm_add_imm_to_sp(mc->asm_gen, offset);
    }

    // Unreserve all caller-saved regs, except the return-register for the moment.
    for (int reg_num = 0; reg_num < num_regs; ++reg_num) {
        if (asm_is_caller_save(mc->asm_gen, reg_num) && reg_num != return_reg) {
            unreserve_register(mc->current_env, mc->asm_gen, reg_num);
        }
    }

    // If there was a return value, push it to the abstract machine's stack.
    if (returns_value) {
        char name[VAR_LEN];
        stk_push(mc, name);
        int reg = lock_var(mc, name, false);

        asm_mov_reg_reg(mc->asm_gen, reg, return_reg);

        unlock_var(mc, name);
    }

    // Now we can unreserve the return-reg as well.
    unreserve_register(mc->current_env, mc->asm_gen, return_reg);

    // Fix up the stack pointer.
    int num_args_to_pop = mc->fun_call_stack->num_args - max_reg_args;
    if (num_args_to_pop > 0) {
        asm_add_imm_to_sp(mc->asm_gen, num_args_to_pop * 8);
    }

    // Remove the fun call node.
    struct FunCallNode *to_free = mc->fun_call_stack;
    mc->fun_call_stack = mc->fun_call_stack->next;
    free(to_free);

    // We can now restore the previous function's argument registers,
    // if applicable.
    if (mc->fun_call_stack) {
        pop_arg_registers(mc);
    } else {
        // If this is the last fun call, there should no longer be any
        // reserved regs.
        check_no_reserved_regs(mc->current_env, mc->asm_gen);
    }
}

void stk_return_from_function(struct StackMachine *mc)
{
    if (mc->stack_depth > 1) {
        fatal_error("return with more than 1 item on stack");
    }

    if (mc->stack_depth == 1) {
        // Move the topmost stack item to the return-register
        char name[VAR_LEN];
        stk_var_name(mc, 0, name);
        int reg_num = lock_var(mc, name, true);

        int return_reg_num = asm_get_return_reg_num(mc->asm_gen);

        if (reg_num != return_reg_num) {
            asm_mov_reg_reg(mc->asm_gen, return_reg_num, reg_num);
        }

        unlock_var(mc, name);
        stk_pop(mc);
    }

    // We need to pop all varsized blocks, so that rsp is in the right place
    // for the epilogue.
    for (struct NameList *node = mc->var_size_mem_block_names; node; node = node->next) {
        asm_pop_sp(mc->asm_gen);
    }

    // Jump down to the epilogue
    asm_local_jump(mc->asm_gen, mc->epilogue_label);

    kill_current_block(mc);
}

void stk_begin_function(struct StackMachine *mc, const char *function_name)
{
    if (mc->current_env != NULL || mc->control_stack != NULL
        || mc->fun_call_stack != NULL || mc->var_size_mem_block_names != NULL
        || mc->args != NULL || mc->args_tail != NULL || mc->function_name != NULL) {
        fatal_error("stk_begin_function: invalid state");
    }

    asm_new_function(mc->asm_gen);

    mc->current_env = new_machine_env();

    stk_new_label(mc, mc->epilogue_label);

    mc->function_name = copy_string(function_name);

    mc->args_tail = &mc->args;
}

void stk_end_function(struct StackMachine *mc)
{
    // Machine should now be in a "clean" state
    if (mc->control_stack) {
        fatal_error("control stack is not empty");
    }
    if (mc->fun_call_stack) {
        fatal_error("fun call stack is not empty");
    }
    if (hash_table_size(mc->fixed_size_mem_block_names) != 0) {
        fatal_error("fixed-size mem blocks still exist");
    }
    if (mc->var_size_mem_block_names != NULL) {
        fatal_error("var-size mem blocks still exist");
    }
    if (mc->stack_depth != 0) {
        fatal_error("evaluation stack is not empty");
    }
    if (mc->args) {
        fatal_error("args exist");
    }

    if (mc->current_env) {
        check_no_reserved_regs(mc->current_env, mc->asm_gen);
    }


    int num_regs = asm_get_num_regs(mc->asm_gen);
    uint64_t guard_page_size = asm_get_guard_page_size(mc->asm_gen);

    update_frame_size_and_used_regs(mc, mc->current_env);


    // Count how many regs need to be pushed/popped
    int num_regs_push = 0;
    for (int i = num_regs - 1; i >= 0; --i) {
        if (mc->used_regs & (1 << i)) {
            if (!asm_is_caller_save(mc->asm_gen, i)) {
                ++num_regs_push;
            }
        }
    }


    // Write the function epilogue:
    asm_label(mc->asm_gen, mc->epilogue_label);

    // Pop callee-save regs in reverse order
    for (int i = num_regs - 1; i >= 0; --i) {
        if (mc->used_regs & (1 << i)) {
            if (!asm_is_caller_save(mc->asm_gen, i)) {
                asm_pop_reg(mc->asm_gen, i);
            }
        }
    }

    // Return from function
    asm_leave(mc->asm_gen);
    asm_ret(mc->asm_gen);


    // Write the function prologue:
    asm_rewind_to_prologue(mc->asm_gen, mc->function_name);

    // temporarily add pushed regs to frame size.
    mc->frame_size += num_regs_push * 8;

    // Round up frame size to multiple of the stack alignment
    unsigned int stack_align = asm_get_stack_alignment(mc->asm_gen);
    mc->frame_size += (stack_align - 1u);
    mc->frame_size &= ~(stack_align - 1u);

    // subtract the pushed regs again.
    mc->frame_size -= num_regs_push * 8;


    // Insert stack probe if required
    if (mc->frame_size > guard_page_size - 8u) {

        // The stack pointer address is mapped (because the return
        // addr from the previous call is there). In the worst case,
        // it is the lowest address on the page, so there are
        // guard_page_size bytes available below it. We need to leave
        // at least 8 of those (for a future call to check_stack to be
        // safe), so the max size we can allocate without a
        // check_stack is guard_page_size - 8.

        // We also save/restore reg 0 around this call, which isn't
        // strictly necessary (at least on x86), but it might be needed
        // on other targets so we save it just to make sure.

        asm_push_reg(mc->asm_gen, 0);
        asm_mov_reg_imm(mc->asm_gen, 0, mc->frame_size);
        asm_call(mc->asm_gen, "rts_check_stack");
        asm_pop_reg(mc->asm_gen, 0);
    }

    // Open a stack frame
    asm_enter(mc->asm_gen, mc->frame_size);

    // Push callee-save registers
    for (int i = 0; i < num_regs; ++i) {
        if (mc->used_regs & (1 << i)) {
            if (!asm_is_caller_save(mc->asm_gen, i)) {
                asm_push_reg(mc->asm_gen, i);
            }
        }
    }


    // Reset StackMachine state back to "idle".
    free_machine_env(mc->current_env);
    mc->current_env = NULL;

    mc->args_tail = NULL;

    mc->frame_size = 0;
    mc->used_regs = 0;

    mc->epilogue_label[0] = 0;

    free((char*)mc->function_name);
    mc->function_name = NULL;


    // Done!
    asm_end_function(mc->asm_gen);
}

void stk_make_rts_functions(struct StackMachine *mc)
{
    make_check_stack_function(mc->asm_gen, &mc->next_label_num);
}

/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef STACK_MACHINE_ENV_H
#define STACK_MACHINE_ENV_H

// Helper for the stack_machine. Implements a mapping from abstract
// "variables" to registers or stack slots.

#include <stdbool.h>

// define for debugging
//#define DEBUG_RECONCILE


struct AsmGen;
struct MachineEnv;

struct ArgInfo {
    const char *name;
    bool is_signed;
    int size;   // 1,2,4 or 8
    struct ArgInfo *next;
};


struct MachineEnv *new_machine_env();
void free_machine_env(struct MachineEnv *);
struct MachineEnv *copy_machine_env(struct MachineEnv *);


// Add a new local variable to the machine env.
// lockable vars must be 1,2,4 or 8 bytes. Unlockable can be any size.
// is_signed only relevant for lockable variables.
void add_variable(struct MachineEnv *env, struct AsmGen *asm_gen,
                  const char *name, bool is_signed, uint64_t num_bytes, bool lockable);

// Add (lockable) variables representing function arguments.
// Call at most once per function.
// Args are in right-to-left order in the list.
void add_arg_variables(struct MachineEnv *env, struct AsmGen *gen,
                       const struct ArgInfo *args);

// Remove a local variable from the machine env.
void remove_variable(struct MachineEnv *env, const char *name);


// Swap two variables (this doesn't emit any code, just remaps which
// register or stack-slot the variables refer to).
void swap_variables(struct MachineEnv *env, const char *name1, const char *name2);


// Lock a variable into a register. It will stay in that register until unlocked.
// The var must have been created as "lockable".
int lock_variable(struct MachineEnv *env, struct AsmGen *asm_gen,
                  const char *var_name, bool preserve_value);

// "Unlock" a variable so that its register can be re-used.
void unlock_variable(struct MachineEnv *env, const char *var_name);


// Register reservation. Used for function calls (and possibly insns
// like division that require fixed registers).
void reserve_register(struct MachineEnv *env, struct AsmGen *gen, int reg_num);
void unreserve_register(struct MachineEnv *env, struct AsmGen *gen, int reg_num);
void check_no_reserved_regs(struct MachineEnv *env, struct AsmGen *gen);


// Get the frame-pointer-offset of a variable.
// The var must be "unlockable".
// Note: if the var has size zero, this returns zero as the variable doesn't
// actually "exist" anywhere.
int64_t get_variable_fp_offset(struct MachineEnv *env, const char *var_name);


// Get frame size and regs used
uint64_t get_frame_size(struct MachineEnv *env);
uint32_t get_used_regs(struct MachineEnv *env);


// "Reconcile" the current env with a desired_env. This makes sure
// that all values are in the same places (registers or stack slots)
// as the desired_env. Emits move instructions as required.
// NB. this might increase the size of the stack frame.
void reconcile_envs(struct MachineEnv *current_env, struct MachineEnv *desired_env,
                    struct AsmGen *asm_gen);


#ifdef DEBUG_RECONCILE
void print_env(struct MachineEnv *env);
#endif

#endif

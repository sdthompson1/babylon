/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "asm_gen.h"
#include "error.h"
#include "hash_table.h"
#include "stack_machine_env.h"
#include "util.h"

#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct VarLoc {
    int reg_num;          // -1 for "not in reg"
    int64_t fp_offset;    // 0 for "no stack slot allocated"

    uint64_t size;
    uint64_t access_time;
    bool locked;
    bool is_signed;  // true if sign extension required when loading from frame
};

struct Interval {
    int64_t low;  // inclusive
    int64_t high; // inclusive
    struct Interval *next;
};

struct MachineEnv {
    struct HashTable *var_locs;
    struct Interval *occupied_intervals;  // in order high to low
    uint64_t timestamp;
    uint64_t frame_size;  // amount to subtract from rsp (after pushing frame pointer)
    uint32_t used_regs;   // bit set if corresponding register was ever locked
};

#define MAX_VARS 10000000
#define MAX_REGS 32  // currently limited to 32 because "used_regs" is uint32_t (both here and in stack_machine.c)

struct MachineEnv *new_machine_env()
{
    struct MachineEnv *result = alloc(sizeof(struct MachineEnv));
    result->var_locs = new_hash_table();
    result->occupied_intervals = NULL;
    result->timestamp = 0;
    result->frame_size = 0;
    result->used_regs = 0;
    return result;
}

void free_machine_env(struct MachineEnv *env)
{
    if (!env) return;

    hash_table_for_each(env->var_locs, ht_free_key_and_value, NULL);
    free_hash_table(env->var_locs);

    struct Interval *i = env->occupied_intervals;
    while (i) {
        struct Interval *next = i->next;
        free(i);
        i = next;
    }

    free(env);
}

static void copy_var_loc(void *context, const char *key, void *value)
{
    struct HashTable *var_locs = context;

    struct VarLoc *new_var_loc = alloc(sizeof(struct VarLoc));
    *new_var_loc = *(struct VarLoc *)value;

    hash_table_insert(var_locs, copy_string(key), new_var_loc);
}

struct MachineEnv *copy_machine_env(struct MachineEnv *env)
{
    struct MachineEnv *copy = alloc(sizeof(struct MachineEnv));

    copy->var_locs = new_hash_table();
    hash_table_for_each(env->var_locs, copy_var_loc, copy->var_locs);

    struct Interval ** to = &copy->occupied_intervals;
    for (struct Interval *from = env->occupied_intervals; from; from = from->next) {
        *to = alloc(sizeof(struct Interval));
        (*to)->low = from->low;
        (*to)->high = from->high;
        to = &(*to)->next;
    }
    *to = NULL;

    copy->timestamp = env->timestamp;
    copy->frame_size = env->frame_size;
    copy->used_regs = env->used_regs;

    return copy;
}


// Try to insert the interval [low,high] into env->occupied_intervals,
// but only if that doesn't exist any existing interval.
// If successful return true.
// (Also increase env->frame_size if required.)
static bool try_insert_interval(struct MachineEnv *env, int64_t low, int64_t high)
{
    struct Interval *interval_above = NULL;
    struct Interval *interval_below = env->occupied_intervals;
    while (interval_below) {
        if (low > interval_below->high) {
            // Trial interval is above this interval (and below all the previous ones),
            // so it fits.
            break;
        }
        if (high >= interval_below->low) {
            // Trial interval intersects this interval - insertion fails.
            return false;
        }
        // Trial interval is below this interval, so move on to
        // consider the next one(s).
        interval_above = interval_below;
        interval_below = interval_above->next;
    }

    bool touching_above = (interval_above != NULL
                           && high + 1 == interval_above->low);
    bool touching_below = (interval_below != NULL
                           && interval_below->high + 1 == low);

    if (touching_above) {
        // Merge with the interval_above
        interval_above->low = low;

        if (touching_below) {
            // Also merge with the interval below, and delete the interval below
            interval_above->low = interval_below->low;
            interval_above->next = interval_below->next;
            free(interval_below);
        }

    } else if (touching_below) {
        // Just merge with interval_below
        interval_below->high = high;

    } else {
        // Make a whole new interval, in between the two
        struct Interval *new_interval = alloc(sizeof(struct Interval));
        new_interval->high = high;
        new_interval->low = low;
        new_interval->next = interval_below;
        if (interval_above) {
            interval_above->next = new_interval;
        } else {
            env->occupied_intervals = new_interval;
        }
    }

    uint64_t space_required = -low;
    if (space_required > env->frame_size) {
        env->frame_size = space_required;
    }

    return true;
}

// Find a free frame slot of the given size, not in either env's occupied_intervals
// (either env can be NULL).
static int64_t find_free_frame_slot(struct MachineEnv *env1,
                                    struct MachineEnv *env2,
                                    uint64_t size)
{
    // Setup trial interval at [-size, -1] which is the highest
    // possible address range it can occupy.
    int64_t low = - size;
    int64_t high = - 1;

    struct Interval *ival1 = env1 ? env1->occupied_intervals : NULL;
    struct Interval *ival2 = env2 ? env2->occupied_intervals : NULL;

    // During this loop, the trial interval will always be below all
    // previously passed Intervals. Recall that the intervals are in
    // descending order of address.
    while (ival1 || ival2) {
        if (ival1 && low <= ival1->high) {
            // We are intersecting ival1, or below it.
            // Move downwards, if necessary, to get clear of it.
            if (high >= ival1->low) {
                high = ival1->low - 1;
                low = high - size + 1;
            }
            // We're now definitely below ival1, so we can move on past ival1.
            ival1 = ival1->next;

        } else if (ival2 && low <= ival2->high) {
            // Same logic for ival2.
            if (high >= ival2->low) {
                high = ival2->low - 1;
                low = high - size + 1;
            }
            ival2 = ival2->next;

        } else {
            // We are below all the passed intervals and above the
            // current ival1 and ival2. This means we are done.
            break;
        }
    }

    return low;
}


// Find a free frame slot of the given size
// Add it to env->occupied_intervals, and update env->frame_size if required
// Return the "low" address of the new slot
static int64_t create_frame_slot(struct MachineEnv *env, uint64_t size)
{
    int64_t low = find_free_frame_slot(env, NULL, size);

    if (!try_insert_interval(env, low, low + size - 1)) {
        fatal_error("failed to insert into free interval!");
    }

    return low;
}


// Remove the interval [low,high] from env->occupied_intervals
static void remove_frame_slot(struct MachineEnv *env, int64_t low, int64_t high)
{
    struct Interval **interval = &env->occupied_intervals;
    while (*interval) {
        if (low >= (*interval)->low && high <= (*interval)->high) {
            if (low == (*interval)->low) {
                if (high == (*interval)->high) {
                    // remove this interval
                    struct Interval *to_free = *interval;
                    *interval = (*interval)->next;
                    free(to_free);
                } else {
                    (*interval)->low = high + 1;
                }
            } else {
                if (high == (*interval)->high) {
                    (*interval)->high = low - 1;
                } else {
                    // split the interval
                    struct Interval *i = alloc(sizeof(struct Interval));
                    i->next = (*interval)->next;
                    (*interval)->next = i;

                    i->high = low - 1;
                    i->low = (*interval)->low;
                    (*interval)->low = high + 1;
                }
            }
            break;
        }
        interval = &(*interval)->next;
    }
}


static void populate_reg_locs(struct MachineEnv *env, struct VarLoc *reg_loc[MAX_REGS])
{
    for (int i = 0; i < MAX_REGS; ++i) {
        reg_loc[i] = NULL;
    }

    struct HashIterator *iter = new_hash_iterator(env->var_locs);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        struct VarLoc *v = value;
        if (v->reg_num >= 0) {
            reg_loc[v->reg_num] = v;
        }
    }
    free_hash_iterator(iter);
}

static void evict_register_to_stack(struct MachineEnv *env, struct AsmGen *gen, struct VarLoc *loc)
{
    uint64_t size = loc->size;

    int64_t fp_offset = loc->fp_offset;
    if (fp_offset == 0) {
        fp_offset = loc->fp_offset = create_frame_slot(env, size);
    }
    asm_store_to_frame(gen, fp_offset, loc->reg_num, size);
    loc->reg_num = -1;
}

static int find_free_register(struct MachineEnv *env, struct AsmGen *gen)
{
    // Figure out what is in each register currently
    struct VarLoc *reg_loc[MAX_REGS];
    populate_reg_locs(env, reg_loc);

    int num_regs = asm_get_num_regs(gen);
    if (num_regs > MAX_REGS) {
        fatal_error("too many regs");
    }

    // Find first free register
    for (int r = 0; r < num_regs; ++r) {
        if (reg_loc[r] == NULL) {
            return r;
        }
    }

    // No free reg found
    // Pick the oldest unlocked register to evict
    uint64_t oldest_time = (uint64_t)-1;
    int oldest_reg = -1;
    for (int i = 0; i < num_regs; ++i) {
        if (!reg_loc[i]->locked && reg_loc[i]->access_time < oldest_time) {
            oldest_time = reg_loc[i]->access_time;
            oldest_reg = i;
        }
    }

    if (oldest_reg == -1) {
        fatal_error("all registers are locked");
    }

    // Evict it to the stack
    evict_register_to_stack(env, gen, reg_loc[oldest_reg]);
    return oldest_reg;
}


void add_variable(struct MachineEnv *env, struct AsmGen *gen,
                  const char *name, bool is_signed, uint64_t size, bool lockable)
{
    if (hash_table_size(env->var_locs) >= MAX_VARS) {
        fatal_error("too many variables");
    }
    if (hash_table_contains_key(env->var_locs, name)) {
        fatal_error("add_variable: a var with this name already exists");
    }
    if (size == 0) {
        fatal_error("add_variable: invalid size");
    }

    struct VarLoc *loc = alloc(sizeof(struct VarLoc));
    loc->reg_num = -1;
    loc->fp_offset = 0;
    loc->size = size;
    loc->access_time = env->timestamp++;
    loc->locked = false;
    loc->is_signed = is_signed;

    // lockable variables start in a register; unlockable on the stack.
    if (lockable) {
        loc->reg_num = find_free_register(env, gen);
    } else {
        loc->fp_offset = create_frame_slot(env, size);
    }

    hash_table_insert(env->var_locs, copy_string(name), loc);
}

void add_arg_variables(struct MachineEnv *env, struct AsmGen *gen,
                       const struct ArgInfo *args)
{
    // Saved FP is at (fp) and return addr at 8(fp).

    // The first N args go in registers according to asm_num_register_args.

    // Subsequent arguments are on the stack in order at 16(fp), 24(fp), etc.

    int arg_num = 0;
    int num_reg_args = asm_num_register_args(gen);

    while (args) {
        const char *name = args->name;
        uint64_t size = args->size;

        if (hash_table_size(env->var_locs) >= MAX_VARS) {
            fatal_error("too many variables");
        }
        if (hash_table_contains_key(env->var_locs, name)) {
            fatal_error("add_arg_variables: a var with this name already exists");
        }
        if (size != 1 && size != 2 && size != 4 && size != 8) {
            fatal_error("add_arg_variables: invalid size");
        }

        struct VarLoc *loc = alloc(sizeof(struct VarLoc));

        if (arg_num < num_reg_args) {
            loc->reg_num = asm_arg_num_to_reg_num(gen, arg_num);
            loc->fp_offset = 0;
        } else {
            loc->reg_num = -1;
            loc->fp_offset = (uint64_t)(arg_num - num_reg_args) * 8u + 16u;
        }
        loc->size = size;
        loc->access_time = env->timestamp++;
        loc->locked = false;
        loc->is_signed = args->is_signed;

        hash_table_insert(env->var_locs, copy_string(name), loc);

        args = args->next;
        arg_num ++;
    }
}

void remove_variable(struct MachineEnv *env, const char *name)
{
    const char *key;
    void *value;
    hash_table_lookup_2(env->var_locs, name, &key, &value);

    if (key == NULL) {
        fatal_error("remove_variable: not found");
    }

    struct VarLoc *loc = value;

    if (loc->locked) {
        fatal_error("remove_variable: var is locked");
    }

    if (loc->fp_offset != 0) {
        // remove this interval from the occupied intervals
        int64_t low = loc->fp_offset;
        int64_t high = low + loc->size - 1;
        remove_frame_slot(env, low, high);
    }

    // remove the variable from var_locs.
    hash_table_remove(env->var_locs, name);
    free((char*)key);
    free(value);
}

void swap_variables(struct MachineEnv *env, const char *name1, const char *name2)
{
    struct VarLoc *v1 = hash_table_lookup(env->var_locs, name1);
    struct VarLoc *v2 = hash_table_lookup(env->var_locs, name2);

    if (v1 == NULL || v2 == NULL) {
        fatal_error("swapping variable that doesn't exist");
    }

    if (v1->locked || v2->locked) {
        fatal_error("swapping locked variable");
    }

    struct VarLoc tmp = *v1;
    *v1 = *v2;
    *v2 = tmp;

    v1->access_time = env->timestamp++;
    v2->access_time = env->timestamp++;
}


int lock_variable(struct MachineEnv *env,
                  struct AsmGen *gen,
                  const char *name,
                  bool preserve_value)
{
    struct VarLoc *var_loc = hash_table_lookup(env->var_locs, name);
    if (var_loc == NULL) {
        fatal_error("lock_variable: not found");
    }
    if (var_loc->locked) {
        fatal_error("lock_variable: already locked");
    }

    var_loc->access_time = env->timestamp++;
    var_loc->locked = true;

    if (var_loc->reg_num >= 0) {
        // It's already in a register
        env->used_regs |= (1 << var_loc->reg_num);
        return var_loc->reg_num;
    }

    // Free up a register
    int reg_num = find_free_register(env, gen);

    // Load our variable from the frame
    if (preserve_value) {
        asm_load_from_frame(gen, reg_num, var_loc->fp_offset, var_loc->is_signed, var_loc->size);
    }

    // Our variable is now in this register
    var_loc->reg_num = reg_num;

    env->used_regs |= (1u << reg_num);
    return reg_num;
}

void unlock_variable(struct MachineEnv *env, const char *name)
{
    struct VarLoc *var_loc = hash_table_lookup(env->var_locs, name);
    if (var_loc == NULL) {
        fatal_error("unlock_variable: not found");
    }
    if (!var_loc->locked) {
        fatal_error("unlock_variable: not locked");
    }

    var_loc->locked = false;
}

int64_t get_variable_fp_offset(struct MachineEnv *env, const char *name)
{
    struct VarLoc *var_loc = hash_table_lookup(env->var_locs, name);
    if (var_loc == NULL) {
        fatal_error("get_variable_fp_offset: not found");
    }
    if (var_loc->reg_num >= 0) {
        // this shouldn't happen provided the var was created with lockable=false
        // and wasn't locked during its lifetime
        fatal_error("get_variable_fp_offset: var is in register");
    }
    return var_loc->fp_offset;
}

uint64_t get_frame_size(struct MachineEnv *env)
{
    return env->frame_size;
}

uint32_t get_used_regs(struct MachineEnv *env)
{
    return env->used_regs;
}

#define RESERVE_LEN 25
#define RESERVE_PREFIX "#RESERVED#"

void reserve_register(struct MachineEnv *env, struct AsmGen *gen, int reg_num)
{
    char res_name[RESERVE_LEN];
    sprintf(res_name, RESERVE_PREFIX "%d", reg_num);

    if (hash_table_contains_key(env->var_locs, res_name)) {
        // register already reserved, no need to do anything
        return;
    }

    // find out if any variable occupies this register
    struct HashIterator *iter = new_hash_iterator(env->var_locs);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        struct VarLoc *v = value;
        if (v->reg_num == reg_num) {
            // a variable is occupying the register. move it to the stack.
            evict_register_to_stack(env, gen, v);
            break;
        }
    }
    free_hash_iterator(iter);

    // now we know the desired register is free, so we can make a
    // "fake" variable to occupy it.
    struct VarLoc *loc = alloc(sizeof(struct VarLoc));
    loc->reg_num = reg_num;
    loc->fp_offset = 0;
    loc->size = 8;
    loc->access_time = 0;
    loc->locked = true;
    loc->is_signed = false;
    hash_table_insert(env->var_locs, copy_string(res_name), loc);
}

void unreserve_register(struct MachineEnv *env, struct AsmGen *gen, int reg_num)
{
    char res_name[RESERVE_LEN];
    sprintf(res_name, RESERVE_PREFIX "%d", reg_num);

    // if we just "unlock" then "remove" our fake variable, it will do the right thing
    if (hash_table_contains_key(env->var_locs, res_name)) {
        unlock_variable(env, res_name);
        remove_variable(env, res_name);
    }
}

void check_no_reserved_regs(struct MachineEnv *env, struct AsmGen *gen)
{
    char res_name[RESERVE_LEN];
    for (int i = 0; i < asm_get_num_regs(gen); ++i) {
        sprintf(res_name, RESERVE_PREFIX "%d", i);
        if (hash_table_contains_key(env->var_locs, res_name)) {
            fatal_error("reserved register detected");
        }
    }
}


//------------------------------------------------------------------------------
// Reconciliation
//------------------------------------------------------------------------------

#ifdef DEBUG_RECONCILE
static int my_strcmp(const void *a, const void *b)
{
    const char **lhs = (const char**)a;
    const char **rhs = (const char**)b;
    return strcmp(*lhs, *rhs);
}

void print_env(struct MachineEnv *env)
{
    if (env == NULL) {
        printf("null\n");
        return;
    }

    size_t sz = hash_table_size(env->var_locs);
    const char **names = malloc(sizeof(char*) * sz);
    struct HashIterator *iter = new_hash_iterator(env->var_locs);
    const char *key;
    void *value;
    size_t i = 0;
    while (hash_iterator_next(iter, &key, &value)) {
        names[i] = key;
        ++i;
    }
    free_hash_iterator(iter);

    qsort(names, sz, sizeof(char*), my_strcmp);

    for (i = 0; i < sz; ++i) {
        struct VarLoc *loc = hash_table_lookup(env->var_locs, names[i]);
        if ((i % 8) == 0 && i != 0) {
            printf("\n");
        }
        printf("%s:", names[i]);
        if (loc->reg_num != -1) {
            printf("r%d", loc->reg_num);
        } else {
            printf("%" PRIi64 "(fp)", loc->fp_offset);
        }
        printf("\t");
    }

    printf("\n");

    free(names);
}
#endif

static struct VarLoc * find_occupier(struct MachineEnv *env, int64_t low, int64_t high)
{
    struct HashIterator *iter = new_hash_iterator(env->var_locs);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        struct VarLoc *loc = value;
        if (loc->fp_offset != 0 && loc->fp_offset <= high && loc->fp_offset + (int64_t)loc->size - 1 >= low) {
            free_hash_iterator(iter);
            return loc;
        }
    }
    free_hash_iterator(iter);
    return NULL;
}

static void reconcile_mem_to_mem(struct MachineEnv *current_env,
                                 struct MachineEnv *desired_env,
                                 struct AsmGen *gen)
{
    struct HashIterator *iter = new_hash_iterator(current_env->var_locs);
    const char *key;
    void *value;

    // First let's see if we have any variables in the wrong memory location
    bool found = false;
    while (hash_iterator_next(iter, &key, &value)) {
        struct VarLoc *from = value;
        struct VarLoc *to = hash_table_lookup(desired_env->var_locs, key);

        // NOTE: we assume to != NULL, this is justified because we
        // expect current_env and desired_env to contain the same set
        // of variables (if they don't, this probably means that a
        // scope wasn't closed properly, and a variable is therefore
        // being kept alive longer than it should be).

        if (from->reg_num < 0 && to->reg_num < 0 && from->fp_offset != to->fp_offset) {
            found = true;
            break;
        }
    }
    free_hash_iterator(iter);

    if (!found) return;

    // OK so we are going to need a temporary register.
    int tmp_reg = find_free_register(current_env, gen);

    // Now loop through again.
    iter = new_hash_iterator(current_env->var_locs);
    while (hash_iterator_next(iter, &key, &value)) {
        struct VarLoc *from = value;
        struct VarLoc *to = hash_table_lookup(desired_env->var_locs, key);
        if (from->reg_num < 0 && to->reg_num < 0 && from->fp_offset != to->fp_offset) {

            if (from->size > 8 || from->size != to->size) {
                // We assume that the vars requiring moving will
                // be able to fit into a register, and have the
                // same size in both envs.
                fatal_error("reconcile_mem_to_mem assumption violated");
            }

            // OK so "from" is in memory in the wrong place, we need to move it
            // from from->fp_offset to to->fp_offset.

            // But to->fp_offset might already be occupied, let's find out...

            int64_t new_low = to->fp_offset;
            int64_t new_high = to->fp_offset + to->size - 1;

            if (!try_insert_interval(current_env, new_low, new_high)) {
                // The to-slot was indeed already occupied.

                // Find out who is occupying the slot.
                struct VarLoc *occupier;
                while ((occupier = find_occupier(current_env, new_low, new_high)) != NULL) {
                    if (occupier->reg_num >= 0) {
                        // The occupier is currently in a register although it has a
                        // "home slot" on the stack. We can just remove the home slot.
                        remove_frame_slot(current_env, occupier->fp_offset, occupier->fp_offset + occupier->size - 1);
                        occupier->fp_offset = 0;

                    } else {
                        // The occupier is on the stack.
                        // Find another (temporary) home, that is currently unoccupied in both envs.
                        int64_t occupier_new_low = find_free_frame_slot(current_env, desired_env, occupier->size);
                        int64_t occupier_new_high = occupier_new_low + occupier->size - 1;

#ifdef DEBUG_RECONCILE
                        printf(". Move occupier %" PRIi64 "(fp) to %" PRIi64 "(fp)\n", occupier->fp_offset, occupier_new_low);
#endif

                        // Mark the new position as occupied
                        if (!try_insert_interval(current_env, occupier_new_low, occupier_new_high)) {
                            // This should be impossible, because we found the slot using
                            // find_free_frame_slot.
                            fatal_error("failed to insert temporary interval");
                        }

                        // Mark the occupier's old position as no longer occupied
                        remove_frame_slot(current_env, occupier->fp_offset, occupier->fp_offset + occupier->size - 1);

                        // Physically move the occupier, using our tmp_reg
                        asm_load_from_frame(gen, tmp_reg, occupier->fp_offset, occupier->is_signed, occupier->size);
                        asm_store_to_frame(gen, occupier_new_low, tmp_reg, occupier->size);

                        // Update the recorded location for the occupier.
                        occupier->fp_offset = occupier_new_low;
                    }
                }

                // The to-slot should now be available!
                if (!try_insert_interval(current_env, new_low, new_high)) {
#ifdef DEBUG_RECONCILE
                    printf("Failed: Moving %" PRIi64 "(fp) to %" PRIi64 "(fp)\n", from->fp_offset, new_low);
#endif
                    fatal_error("failed to insert interval, even after removing occupiers");
                }
            }

#ifdef DEBUG_RECONCILE
            printf(". Move %" PRIi64 "(fp) to %" PRIi64 "(fp)\n", from->fp_offset, new_low);
#endif

            // Mark the old interval as "unoccupied".
            remove_frame_slot(current_env, from->fp_offset, from->fp_offset + from->size - 1);

            // Physically move the value, using our tmp_reg.
            asm_load_from_frame(gen, tmp_reg, from->fp_offset, from->is_signed, from->size);
            asm_store_to_frame(gen, new_low, tmp_reg, from->size);

            // Update the recorded location for this variable.
            from->fp_offset = new_low;
        }
    }

    free_hash_iterator(iter);
}

static void reconcile_reg_to_mem(struct MachineEnv *current_env,
                                 struct MachineEnv *desired_env,
                                 struct AsmGen *gen)
{
    // Move regs out to memory
    struct HashIterator *iter = new_hash_iterator(current_env->var_locs);
    const char *key;
    void *value;
    while (hash_iterator_next(iter, &key, &value)) {
        struct VarLoc *from = value;
        struct VarLoc *to = hash_table_lookup(desired_env->var_locs, key);
        if (from->reg_num >= 0 && to->reg_num < 0) {
#ifdef DEBUG_RECONCILE
            printf(". Move r%d to %" PRIi64 "(fp)\n", from->reg_num, to->fp_offset);
#endif
            asm_store_to_frame(gen, to->fp_offset, from->reg_num, to->size);
            from->reg_num = -1;
            from->fp_offset = to->fp_offset;
        }
    }
    free_hash_iterator(iter);
}

static void reconcile_reg_to_reg(struct MachineEnv *current_env,
                                 struct MachineEnv *desired_env,
                                 struct AsmGen *gen,
                                 struct VarLoc *reg_loc[MAX_REGS])
{
    struct HashIterator *iter = new_hash_iterator(current_env->var_locs);
    const char *key;
    void *value;

    // Move or swap regs with other regs.
    // Also try to do moves first before resorting to swapping
    // (as xchg is presumably a bit slower than a plain mov).
    bool allow_swap = false;
    while (true) {

        bool problem = false;   // set if a swap was prevented
        bool progress = false;  // set if we moved or swapped anything

        while (hash_iterator_next(iter, &key, &value)) {
            struct VarLoc *from = value;
            struct VarLoc *to = hash_table_lookup(desired_env->var_locs, key);
            if (from->reg_num >= 0 && to->reg_num >= 0 && from->reg_num != to->reg_num) {

                // we want to move from->reg_num to to->reg_num, but if
                // to->reg_num is occupied, then swap instead.
                if (reg_loc[to->reg_num]) {
                    if (allow_swap) {
#ifdef DEBUG_RECONCILE
                        printf(". Swap r%d and r%d\n", from->reg_num, to->reg_num);
#endif
                        asm_swap_regs(gen, from->reg_num, to->reg_num);

                        int tmp = from->reg_num;
                        from->reg_num = to->reg_num;
                        reg_loc[to->reg_num]->reg_num = tmp;

                        progress = true;
                    } else {
                        problem = true;
                    }

                } else {
#ifdef DEBUG_RECONCILE
                    printf(". Move r%d to r%d\n", from->reg_num, to->reg_num);
#endif
                    asm_mov_reg_reg(gen, to->reg_num, from->reg_num);

                    reg_loc[to->reg_num] = from;
                    reg_loc[from->reg_num] = NULL;

                    from->reg_num = to->reg_num;

                    progress = true;
                }
            }
        }

        if (progress) {
            allow_swap = false;
        } else if (problem) {
            allow_swap = true;
        } else {
            break;
        }
    }

    free_hash_iterator(iter);
}

static void reconcile_mem_to_reg(struct MachineEnv *current_env,
                                 struct MachineEnv *desired_env,
                                 struct AsmGen *gen,
                                 struct VarLoc *reg_loc[MAX_REGS])
{
    struct HashIterator *iter = new_hash_iterator(current_env->var_locs);
    const char *key;
    void *value;

    // Now move memory into registers.
    while (hash_iterator_next(iter, &key, &value)) {
        struct VarLoc *from = value;
        struct VarLoc *to = hash_table_lookup(desired_env->var_locs, key);
        if (from->reg_num < 0 && to->reg_num >= 0) {
            if (reg_loc[to->reg_num]) {
                fatal_error("register unexpectedly occupied");
            }

#ifdef DEBUG_RECONCILE
            printf(". Move %" PRIi64 "(fp) to r%d\n", from->fp_offset, to->reg_num);
#endif
            asm_load_from_frame(gen, to->reg_num, from->fp_offset, from->is_signed, from->size);
            from->reg_num = to->reg_num;
        }
    }

    free_hash_iterator(iter);
}

void reconcile_envs(struct MachineEnv *current_env, struct MachineEnv *desired_env,
                    struct AsmGen *gen)
{
#ifdef DEBUG_RECONCILE
    printf("RECONCILE\n");
    print_env(current_env);
    printf("TO:\n");
    print_env(desired_env);
    printf("\n");
#endif

    reconcile_mem_to_mem(current_env, desired_env, gen);

    reconcile_reg_to_mem(current_env, desired_env, gen);

    struct VarLoc *reg_loc[MAX_REGS];
    populate_reg_locs(current_env, reg_loc);

    reconcile_reg_to_reg(current_env, desired_env, gen, reg_loc);

    reconcile_mem_to_reg(current_env, desired_env, gen, reg_loc);
}

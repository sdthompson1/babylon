/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#include "asm_gen.h"

void make_check_stack_function(struct AsmGen *gen, uint64_t *label_num)
{
    uint64_t page_size = asm_get_guard_page_size(gen);

    asm_new_function(gen);

    // reg 0 = count of bytes below RSP that we would like to be accessible.
    // reg 0 will be corrupted by this routine, as will the flags.
    // All other regs preserved.

    // Labels required
    char probe_label[LABEL_LEN];
    char subtract_label[LABEL_LEN];
    asm_make_local_label(gen, (*label_num)++, probe_label);
    asm_make_local_label(gen, (*label_num)++, subtract_label);

    // Setup a frame (as we will be moving the stack pointer)
    asm_enter(gen, 0);

    asm_local_jump(gen, subtract_label);

    asm_label(gen, probe_label);
    asm_probe_sp(gen);

    asm_label(gen, subtract_label);
    asm_sub_imm_from_sp(gen, page_size);
    asm_alu_reg_imm(gen, OP_SUB, 0, page_size);
    asm_branch_if_above(gen, probe_label);

    asm_sub_reg_from_sp(gen, 0);
    asm_probe_sp(gen);

    asm_leave(gen);
    asm_ret(gen);

    asm_rewind_to_prologue(gen, "rts_check_stack");
    asm_end_function(gen);
}

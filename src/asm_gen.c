/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


// Currently this file is specialised for x86-64, on Linux, using the GNU assembler.

#include "alloc.h"
#include "asm_gen.h"
#include "error.h"
#include "stringbuf.h"
#include "util.h"

#include <inttypes.h>
#include <stdlib.h>
#include <string.h>

enum Section {
    SEC_NONE,
    SEC_TEXT,
    SEC_RODATA,
    SEC_DATA_REL_RO_LOCAL
};

struct AsmGen {
    struct StringBuf *buf;       // points to one of the two below bufs
    struct StringBuf prologue_buf;
    struct StringBuf fun_body_buf;
    FILE *output;
    enum Section current_section;
};

#define INSN_FORMAT "        %-7s "

struct AsmGen *new_asm_gen(FILE *output)
{
    struct AsmGen *gen = alloc(sizeof(struct AsmGen));

    gen->buf = NULL;
    stringbuf_init(&gen->prologue_buf);
    stringbuf_init(&gen->fun_body_buf);
    gen->output = output;

    gen->current_section = SEC_NONE;

    return gen;
}

void free_asm_gen(struct AsmGen *gen)
{
    if (gen->buf != NULL) {
        fatal_error("still generating a function");
    }

    stringbuf_free(&gen->fun_body_buf);
    stringbuf_free(&gen->prologue_buf);
    free(gen);

    // note: FILE *output is deliberately not closed; that is up to the caller.
}


static const char * x86_64bit_reg_names[] = {
    "%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi",
    "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15"
};

static const char * x86_32bit_reg_names[] = {
    "%eax", "%ebx", "%ecx", "%edx", "%esi", "%edi",
    "%r8d", "%r9d", "%r10d", "%r11d", "%r12d", "%r13d", "%r14d", "%r15d"
};

static const char * x86_16bit_reg_names[] = {
    "%ax", "%bx", "%cx", "%dx", "%si", "%di",
    "%r8w", "%r9w", "%r10w", "%r11w", "%r12w", "%r13w", "%r14w", "%r15w"
};

static const char * x86_8bit_reg_names[] = {
    "%al", "%bl", "%cl", "%dl", "%sil", "%dil",
    "%r8b", "%r9b", "%r10b", "%r11b", "%r12b", "%r13b", "%r14b", "%r15b"
};

static const bool x86_caller_save[] = {
    true,  // RAX
    false,
    true,  // RCX
    true,  // RDX
    true,  // RSI
    true,  // RDI
    true, true, true, true,  // R8-11
    false, false, false, false    // R12-15
};

enum {
    REG_NUM_RAX = 0, REG_NUM_RBX = 1, REG_NUM_RCX = 2, REG_NUM_RDX = 3,
    REG_NUM_RSI = 4, REG_NUM_RDI = 5,
    REG_NUM_R8 = 6, REG_NUM_R9 = 7
};

static const char * reg_name(int reg_num, int num_bytes)
{
    switch (num_bytes) {
    case 1: return x86_8bit_reg_names[reg_num];
    case 2: return x86_16bit_reg_names[reg_num];
    case 4: return x86_32bit_reg_names[reg_num];
    case 8: return x86_64bit_reg_names[reg_num];
    default: fatal_error("bad reg size");
    }
}


int asm_get_num_regs(struct AsmGen *gen)
{
    return sizeof(x86_64bit_reg_names) / sizeof(x86_64bit_reg_names[0]);
}

uint64_t asm_get_guard_page_size(struct AsmGen *gen)
{
    return 4096;
}


// helpers for common cases (insn reg64; insn reg64,reg64; and insn reg64,imm)
static void print_insn_reg(struct AsmGen *gen, const char *insn, int reg_num)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s\n", insn, reg_name(reg_num, 8));
}

static void print_insn_reg_reg(struct AsmGen *gen, const char *insn,
                               int dest_reg_num, int src_reg_num)
{
    // GNU syntax puts src first, then dest
    stringbuf_printf(gen->buf, INSN_FORMAT "%s, %s\n", insn,
                     reg_name(src_reg_num, 8), reg_name(dest_reg_num, 8));
}

static void print_insn_reg_imm(struct AsmGen *gen, const char *insn,
                               int dest_reg_num, uint64_t value)
{
    // printing as int64 will probably look better than uint64
    int64_t signed_value;
    memcpy(&signed_value, &value, sizeof(int64_t));
    stringbuf_printf(gen->buf, INSN_FORMAT "$%" PRIi64 ", %s\n", insn,
                     signed_value, reg_name(dest_reg_num, 8));
}


void asm_mov_reg_reg(struct AsmGen *gen, int dest_reg_num, int src_reg_num)
{
    if (dest_reg_num != src_reg_num) {
        print_insn_reg_reg(gen, "mov", dest_reg_num, src_reg_num);
    }
}

void asm_swap_regs(struct AsmGen *gen, int reg_num_1, int reg_num_2)
{
    if (reg_num_1 != reg_num_2) {
        print_insn_reg_reg(gen, "xchg", reg_num_1, reg_num_2);
    }
}

void asm_mov_reg_imm(struct AsmGen *gen, int dest_reg_num, uint64_t value)
{
    if (value == 0) {
        // optimisation: use xor, instead of mov, to zero a register
        stringbuf_printf(gen->buf, INSN_FORMAT "%s, %s\n", "xor",
                         reg_name(dest_reg_num, 4), reg_name(dest_reg_num, 4));
    } else {
        print_insn_reg_imm(gen, "mov", dest_reg_num, value);
    }
}

static void handle_division(struct AsmGen *gen, enum Opcode op, int dest_reg_num, int src_reg_num)
{
    bool is_unsigned = (op == OP_UDIV || op == OP_UREM);
    bool is_remainder = (op == OP_SREM || op == OP_UREM);

    // Save RAX and RDX to the stack
    // Exception: if the destination is RAX or RDX then they don't need to be saved.
    if (dest_reg_num != REG_NUM_RAX) {
        asm_push_reg(gen, REG_NUM_RAX);
    }
    if (dest_reg_num != REG_NUM_RDX) {
        asm_push_reg(gen, REG_NUM_RDX);
    }

    // If the src_reg is RAX or RDX then we have a problem.
    // We will use either RCX or RBX as the src_reg in that case.
    // (The chosen reg will then need saving.)
    int real_src_reg = src_reg_num;
    if (src_reg_num == REG_NUM_RAX || src_reg_num == REG_NUM_RDX) {
        if (dest_reg_num == REG_NUM_RCX) {
            real_src_reg = REG_NUM_RBX;
        } else {
            real_src_reg = REG_NUM_RCX;
        }
        asm_push_reg(gen, real_src_reg);
        asm_mov_reg_reg(gen, real_src_reg, src_reg_num);
    }

    // Move the dest_reg (dividend) into RAX - unless it is there already.
    if (dest_reg_num != REG_NUM_RAX) {
        asm_mov_reg_reg(gen, REG_NUM_RAX, dest_reg_num);
    }

    // Load the "top half" of the dividend into RDX
    if (is_unsigned) {
        stringbuf_printf(gen->buf, INSN_FORMAT "%%edx, %%edx\n", "xor");
    } else {
        stringbuf_printf(gen->buf, INSN_FORMAT "\n", "cqto");
    }

    // Divide by the src_reg (or by RBX or RCX if applicable)
    print_insn_reg(gen, is_unsigned ? "div" : "idiv", real_src_reg);

    // Result is now in RDX (remainder) or RAX (quotient).
    // Move it to the dest_reg - if it is not there already.
    int wanted_reg = is_remainder ? REG_NUM_RDX : REG_NUM_RAX;
    if (dest_reg_num != wanted_reg) {
        asm_mov_reg_reg(gen, dest_reg_num, wanted_reg);
    }

    // Restore all the saved registers.
    if (real_src_reg != src_reg_num) {
        asm_pop_reg(gen, real_src_reg);
    }
    if (dest_reg_num != REG_NUM_RDX) {
        asm_pop_reg(gen, REG_NUM_RDX);
    }
    if (dest_reg_num != REG_NUM_RAX) {
        asm_pop_reg(gen, REG_NUM_RAX);
    }
}

static void handle_shift(struct AsmGen *gen, const char *insn, int dest_reg_num, int src_reg_num)
{
    int real_dest_reg = dest_reg_num;
    if (src_reg_num != REG_NUM_RCX) {
        // Temporarily swap the src reg into RCX
        asm_swap_regs(gen, REG_NUM_RCX, src_reg_num);

        if (dest_reg_num == REG_NUM_RCX) {
            real_dest_reg = src_reg_num;
        }
    }

    // Do the shift
    stringbuf_printf(gen->buf, INSN_FORMAT "%%cl, %s\n", insn, reg_name(real_dest_reg, 8));

    if (src_reg_num != REG_NUM_RCX) {
        // Swap the regs back again
        asm_swap_regs(gen, REG_NUM_RCX, src_reg_num);
    }
}

static void handle_cmp(struct AsmGen *gen, const char *insn, int dest_reg_num, int src_reg_num)
{
    print_insn_reg_reg(gen, "cmp", dest_reg_num, src_reg_num);
    stringbuf_printf(gen->buf, INSN_FORMAT "%s\n", insn, reg_name(dest_reg_num, 1));
}

void asm_alu_reg_reg(struct AsmGen *gen, enum Opcode op, int dest_reg_num, int src_reg_num)
{
    switch (op) {
    case OP_NEG:
        print_insn_reg(gen, "neg", dest_reg_num);
        break;

    case OP_ADD:
        print_insn_reg_reg(gen, "add", dest_reg_num, src_reg_num);
        break;

    case OP_SUB:
        print_insn_reg_reg(gen, "sub", dest_reg_num, src_reg_num);
        break;

    case OP_MUL:
        print_insn_reg_reg(gen, "imul", dest_reg_num, src_reg_num);
        break;

    case OP_UDIV:
    case OP_UREM:
    case OP_SDIV:
    case OP_SREM:
        handle_division(gen, op, dest_reg_num, src_reg_num);
        break;

    case OP_NOT:
        print_insn_reg(gen, "not", dest_reg_num);
        break;

    case OP_AND:
        print_insn_reg_reg(gen, "and", dest_reg_num, src_reg_num);
        break;

    case OP_OR:
        print_insn_reg_reg(gen, "or", dest_reg_num, src_reg_num);
        break;

    case OP_XOR:
        print_insn_reg_reg(gen, "xor", dest_reg_num, src_reg_num);
        break;

    case OP_XOR_1:
        print_insn_reg_imm(gen, "xor", dest_reg_num, 1);
        break;

    case OP_SHL:
        handle_shift(gen, "shl", dest_reg_num, src_reg_num);
        break;

    case OP_ASR:
        handle_shift(gen, "sar", dest_reg_num, src_reg_num);
        break;

    case OP_LSR:
        handle_shift(gen, "shr", dest_reg_num, src_reg_num);
        break;

    case OP_EQ:
        handle_cmp(gen, "sete", dest_reg_num, src_reg_num);
        break;

    case OP_NE:
        handle_cmp(gen, "setne", dest_reg_num, src_reg_num);
        break;

    case OP_SLT:
        handle_cmp(gen, "setl", dest_reg_num, src_reg_num);
        break;

    case OP_SLE:
        handle_cmp(gen, "setle", dest_reg_num, src_reg_num);
        break;

    case OP_SGT:
        handle_cmp(gen, "setg", dest_reg_num, src_reg_num);
        break;

    case OP_SGE:
        handle_cmp(gen, "setge", dest_reg_num, src_reg_num);
        break;

    case OP_ULT:
        handle_cmp(gen, "setb", dest_reg_num, src_reg_num);
        break;

    case OP_ULE:
        handle_cmp(gen, "setbe", dest_reg_num, src_reg_num);
        break;

    case OP_UGT:
        handle_cmp(gen, "seta", dest_reg_num, src_reg_num);
        break;

    case OP_UGE:
        handle_cmp(gen, "setae", dest_reg_num, src_reg_num);
        break;
    }
}

void asm_alu_reg_imm(struct AsmGen *gen, enum Opcode op, int dest_reg_num, uint64_t src_immediate)
{
    switch (op) {
    case OP_ADD:
        print_insn_reg_imm(gen, "add", dest_reg_num, src_immediate);
        break;

    case OP_AND:
        print_insn_reg_imm(gen, "and", dest_reg_num, src_immediate);
        break;

    case OP_SUB:
        print_insn_reg_imm(gen, "sub", dest_reg_num, src_immediate);
        break;

    default:
        fatal_error("asm_alu_reg_imm unsupported opcode");
    }
}

static void choose_insn_for_load(bool sign_extend, int size_in_bytes,
                                 const char **insn, int *dest_size)
{
    if (size_in_bytes == 8) {
        *insn = "mov";
        *dest_size = 8;

    } else if (size_in_bytes == 4) {
        *insn = sign_extend ? "movslq" : "mov";
        *dest_size = sign_extend ? 8 : 4;

    } else if (size_in_bytes == 2) {
        *insn = sign_extend ? "movswq" : "movzwl";
        *dest_size = sign_extend ? 8 : 4;

    } else if (size_in_bytes == 1) {
        *insn = sign_extend ? "movsbq" : "movzbl";
        *dest_size = sign_extend ? 8 : 4;

    } else {
        fatal_error("invalid size");
    }
}

void asm_load_from_frame(struct AsmGen *gen, int dest_reg_num, int64_t frame_offset,
                         bool sign_extend, int size_in_bytes)
{
    const char *insn = NULL;
    int dest_size = 0;
    choose_insn_for_load(sign_extend, size_in_bytes, &insn, &dest_size);
    stringbuf_printf(gen->buf, INSN_FORMAT "%.0" PRIi64 "(%%rbp), %s\n",
                     insn, frame_offset, reg_name(dest_reg_num, dest_size));
}

void asm_load_from_reg_address(struct AsmGen *gen, int dest_reg_num, int64_t offset,
                               int addr_reg_num, bool sign_extend, int size_in_bytes)
{
    const char *insn = NULL;
    int dest_size = 0;
    choose_insn_for_load(sign_extend, size_in_bytes, &insn, &dest_size);
    stringbuf_printf(gen->buf, INSN_FORMAT "%.0" PRIi64 "(%s), %s\n",
                     insn, offset,
                     reg_name(addr_reg_num, 8),
                     reg_name(dest_reg_num, dest_size));
}

void asm_store_to_frame(struct AsmGen *gen, int64_t frame_offset,
                        int src_reg_num, int size_in_bytes)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s, %.0" PRIi64 "(%%rbp)\n",
                     "mov", reg_name(src_reg_num, size_in_bytes), frame_offset);
}

void asm_store_to_stack(struct AsmGen *gen, int64_t frame_offset,
                        int src_reg_num, int size_in_bytes)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s, %.0" PRIi64 "(%%rsp)\n",
                     "mov", reg_name(src_reg_num, size_in_bytes), frame_offset);
}

void asm_store_to_reg_address(struct AsmGen *gen, int64_t offset, int addr_reg_num,
                              int src_reg_num, int size_in_bytes)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s, %.0" PRIi64 "(%s)\n",
                     "mov", reg_name(src_reg_num, size_in_bytes),
                     offset, reg_name(addr_reg_num, 8));
}

void asm_lea_frame_slot(struct AsmGen *gen, int dest_reg_num, int64_t frame_offset)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%.0" PRIi64 "(%%rbp), %s\n",
                     "lea", frame_offset, reg_name(dest_reg_num, 8));
}

void asm_lea_stack_slot(struct AsmGen *gen, int dest_reg_num, int64_t frame_offset)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%.0" PRIi64 "(%%rsp), %s\n",
                     "lea", frame_offset, reg_name(dest_reg_num, 8));
}

void asm_begin_global_constant(struct AsmGen *gen, const char *name,
                               bool may_include_addrs, bool exported)
{
    if (gen->buf) {
        fatal_error("in function");
    }

    fprintf(gen->output, "\n");

    enum Section sec = may_include_addrs ? SEC_DATA_REL_RO_LOCAL : SEC_RODATA;
    if (gen->current_section != sec) {
        fprintf(gen->output, INSN_FORMAT "%s\n", ".section",
                may_include_addrs ? ".data.rel.ro.local" : ".rodata");
        gen->current_section = sec;
    }

    if (exported) {
        fprintf(gen->output, INSN_FORMAT "%s\n", ".globl", name);
    }

    fprintf(gen->output, "%s:\n", name);
}

void asm_insert_byte(struct AsmGen *gen, uint8_t x)
{
    fprintf(gen->output, INSN_FORMAT "%" PRIu8 "\n", ".byte", x);
}

void asm_insert_wyde(struct AsmGen *gen, uint16_t x)
{
    fprintf(gen->output, INSN_FORMAT "%" PRIu16 "\n", ".short", x);
}

void asm_insert_tetra(struct AsmGen *gen, uint32_t x)
{
    fprintf(gen->output, INSN_FORMAT "%" PRIu32 "\n", ".long", x);
}

void asm_insert_octa(struct AsmGen *gen, uint64_t x)
{
    fprintf(gen->output, INSN_FORMAT "%" PRIu64 "\n", ".quad", x);
}

void asm_insert_global_addr(struct AsmGen *gen, const char *label)
{
    fprintf(gen->output, INSN_FORMAT "%s\n", ".quad", label);
}

void asm_end_global_constant(struct AsmGen *gen)
{
}

void asm_load_global(struct AsmGen *gen, int dest_reg_num, const char *name,
                     bool sign_extend, int size_in_bytes)
{
    const char *insn = NULL;
    int dest_size = 0;
    choose_insn_for_load(sign_extend, size_in_bytes, &insn, &dest_size);
    stringbuf_printf(gen->buf, INSN_FORMAT "%s(%%rip), %s\n",
                     insn, name, reg_name(dest_reg_num, dest_size));
}

void asm_lea_global(struct AsmGen *gen, int dest_reg_num, const char *name)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s(%%rip), %s\n",
                     "lea", name, reg_name(dest_reg_num, 8));
}

void asm_make_local_label(struct AsmGen *gen, uint64_t number, char label[LABEL_LEN])
{
    // In GNU as, ".L" indicates a local symbol (as in, local to this .s file)
    snprintf(label, LABEL_LEN, ".L%" PRIu64, number);
}

void asm_label(struct AsmGen *gen, const char *label)
{
    stringbuf_printf(gen->buf, "%s:\n", label);
}

void asm_local_jump(struct AsmGen *gen, const char *label)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s\n", "jmp", label);
}

void asm_test(struct AsmGen *gen, int reg_num, int num_bytes)
{
    const char *name = reg_name(reg_num, num_bytes);
    stringbuf_printf(gen->buf, INSN_FORMAT "%s, %s\n", "test", name, name);
}

void asm_branch_if_zero(struct AsmGen *gen, const char *label)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s\n", "je", label);
}

void asm_branch_if_nonzero(struct AsmGen *gen, const char *label)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s\n", "jne", label);
}

void asm_branch_if_above(struct AsmGen *gen, const char *label)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s\n", "ja", label);
}

void asm_call(struct AsmGen *gen, const char *label)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s\n", "call", label);
}

void asm_enter(struct AsmGen *gen, uint64_t delta)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%%rbp\n", "push");
    stringbuf_printf(gen->buf, INSN_FORMAT "%%rsp, %%rbp\n", "mov");

    if (delta != 0) {
        asm_sub_imm_from_sp(gen, delta);
    }
}

void asm_leave(struct AsmGen *gen)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "\n", "leave");
}

void asm_ret(struct AsmGen *gen)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "\n", "ret");
}

void asm_mov_reg_sp(struct AsmGen *gen, int dest_reg_num)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%%rsp, %s\n", "mov", reg_name(dest_reg_num, 8));
}

void asm_sub_reg_from_sp(struct AsmGen *gen, int reg_num)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "%s, %%rsp\n",
                     "sub", reg_name(reg_num, 8));
}

void asm_add_imm_to_sp(struct AsmGen *gen, uint64_t amount)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "$%" PRIu64 ", %%rsp\n",
                     "add", amount);
}

void asm_sub_imm_from_sp(struct AsmGen *gen, uint64_t amount)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "$%" PRIu64 ", %%rsp\n",
                     "sub", amount);
}

void asm_push_reg(struct AsmGen *gen, int src_reg_num)
{
    print_insn_reg(gen, "push", src_reg_num);
}

void asm_pop_reg(struct AsmGen *gen, int dest_reg_num)
{
    print_insn_reg(gen, "pop", dest_reg_num);
}

void asm_pop_sp(struct AsmGen *gen)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "(%%rsp), %%rsp\n", "mov");
}

void asm_probe_sp(struct AsmGen *gen)
{
    stringbuf_printf(gen->buf, INSN_FORMAT "$0, (%%rsp)\n", "orb");
}

int asm_num_register_args(struct AsmGen *gen)
{
    return 6;
}

int asm_arg_num_to_reg_num(struct AsmGen *gen, int arg_num)
{
    switch (arg_num) {
    case 0: return REG_NUM_RDI;
    case 1: return REG_NUM_RSI;
    case 2: return REG_NUM_RDX;
    case 3: return REG_NUM_RCX;
    case 4: return REG_NUM_R8;
    case 5: return REG_NUM_R9;
    default: fatal_error("arg_num out of range");
    }
}

int asm_get_return_reg_num(struct AsmGen *gen)
{
    return REG_NUM_RAX;
}

bool asm_is_caller_save(struct AsmGen *gen, int reg_num)
{
    return x86_caller_save[reg_num];
}

unsigned int asm_get_stack_alignment(struct AsmGen *gen)
{
    return 16;
}

void asm_new_function(struct AsmGen *gen)
{
    if (gen->buf) {
        fatal_error("already in function");
    }
    gen->buf = &gen->fun_body_buf;

    fprintf(gen->output, "\n");
    if (gen->current_section != SEC_TEXT) {
        fprintf(gen->output, INSN_FORMAT "\n", ".text");
        gen->current_section = SEC_TEXT;
    }
}

void asm_rewind_to_prologue(struct AsmGen *gen, const char *function_name)
{
    gen->buf = &gen->prologue_buf;

    stringbuf_printf(gen->buf, INSN_FORMAT "%s\n", ".globl", function_name);
    stringbuf_printf(gen->buf, "%s:\n", function_name);
}

void asm_end_function(struct AsmGen *gen)
{
    if (gen->buf != &gen->prologue_buf) {
        fatal_error("not in function, or rewind_to_prologue was not called");
    }
    if (gen->fun_body_buf.length == 0) {
        fatal_error("empty fun body");
    }
    // (note prologue_buf cannot be empty, as rewind_to_prologue writes to it)

    fputs(gen->prologue_buf.data, gen->output);
    stringbuf_clear(&gen->prologue_buf);

    fputs(gen->fun_body_buf.data, gen->output);
    stringbuf_clear(&gen->fun_body_buf);

    gen->buf = NULL;
}

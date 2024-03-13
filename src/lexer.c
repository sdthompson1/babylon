/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "error.h"
#include "lexer.h"
#include "sha256.h"

#include <ctype.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

// Maximum length of name that the lexer can handle
#define MAX_NAME_LEN  200

struct LexerState {
    // only one of these will be set
    FILE *file;
    const unsigned char *char_data;

    struct Location location;
    struct Token *head;
    struct Token *tail;
    int next_char;

    bool error;
    bool interface_only;
    bool done;
};


static int peek_next_char(struct LexerState *state)
{
    if (state->next_char == EOF) {
        if (state->file) {
            state->next_char = fgetc(state->file);
        } else {
            if (*(state->char_data)) {
                state->next_char = *(state->char_data)++;
            } else {
                state->next_char = EOF;
            }
        }
    }
    return state->next_char;
}

static int read_next_char(struct LexerState *state)
{
    int ch = peek_next_char(state);

    state->next_char = EOF;

    if (ch != EOF) {
        state->location.end_column_num ++;
        if (ch == '\n') {
            state->location.end_column_num = 1;
            state->location.end_line_num ++;
        }
    }

    return ch;
}

static void reset_location(struct LexerState *state)
{
    state->location.begin_line_num = state->location.end_line_num;
    state->location.begin_column_num = state->location.end_column_num;
}

static void skip_rest_of_line(struct LexerState *state)
{
    while (true) {
        int ch = read_next_char(state);
        if (ch == EOF || ch == '\n') {
            break;
        }
    }
}

static void skip_block_comment(struct LexerState *state, struct Location start_loc)
{
    // Allow nested /* */ comments
    int level = 1;

    while (true) {
        int ch = read_next_char(state);
        if (ch == '*') {
            ch = peek_next_char(state);
            if (ch == '/') {
                read_next_char(state);
                --level;
                if (level == 0) {
                    break;
                }
            }
        } else if (ch == '/') {
            ch = peek_next_char(state);
            if (ch == '*') {
                read_next_char(state);
                ++level;
            }
        } else if (ch == EOF) {
            report_unclosed_block_comment(start_loc);
            state->error = true;
            reset_location(state);
            break;
        }
    }
}

static void report_error(struct LexerState *state)
{
    report_lexical_error(state->location);

    state->error = true;

    // Move on to next whitespace char, we should be safe on a whitespace char.
    while (true) {
        int ch = read_next_char(state);
        if (isspace(ch) || ch == EOF) {
            break;
        }
    }

    reset_location(state);
}

// data will be malloc-copied (unless it is NULL)
static void add_token(struct LexerState *state, enum TokenType type, char *data, uint32_t length)
{
    struct Token *new_token = alloc(sizeof(struct Token));

    new_token->next = NULL;
    new_token->location = state->location;
    new_token->type = type;

    if (data) {
        new_token->data = alloc(length);
        memcpy(new_token->data, data, length);
    } else {
        new_token->data = NULL;
    }

    new_token->length = length;

    if (state->tail) {
        state->tail->next = new_token;
        state->tail = new_token;
    } else {
        state->head = state->tail = new_token;
    }

    reset_location(state);
}

static void add_simple_token(struct LexerState *state, enum TokenType type)
{
    add_token(state, type, NULL, 0);
}

static void lex_int_literal(struct LexerState *state)
{
    // Allocate plenty of space, this means that (most) over-sized literals will get the "integer literal too big"
    // type error, rather than a lexical error (from this buffer filling up).
    char buf[1000];
    unsigned int index = 0;
    int ch;

    while (1) {
        // Keep consuming digits until no more are available
        ch = peek_next_char(state);
        if (!isdigit(ch)) {
            break;
        }
        read_next_char(state);

        if (index >= sizeof(buf) - 1) {
            // Integer literal too long
            report_error(state);
            return;
        }

        // Do not add leading zeroes
        if (index != 0 || ch != '0') {
            buf[index++] = ch;
        }
    }

    if (index == 0) {
        // Must have been zero
        buf[index++] = '0';
    }

    buf[index] = 0;

    add_token(state, TOK_INT_LITERAL, buf, strlen(buf) + 1);
}

static int read_hex_digit(struct LexerState *state)
{
    int ch = read_next_char(state);
    if (ch >= '0' && ch <= '9') {
        return ch - '0';
    } else if (ch >= 'a' && ch <= 'f') {
        return ch - 'a' + 10;
    } else if (ch >= 'A' && ch <= 'F') {
        return ch - 'A' + 10;
    } else {
        return -1;
    }
}

static int lex_escape_sequence(struct LexerState *state)
{
    struct Location loc = state->location;
    loc.begin_line_num = loc.end_line_num;
    loc.begin_column_num = loc.end_column_num;

    int ch = read_next_char(state);
    int output = -1;

    switch (ch) {
    case 't':
        // '\t' = tab (ascii 9)
        output = 9;
        break;

    case 'n':
        // '\n' = newline (ascii 10)
        output = 10;
        break;

    case '"':
        // '\"' = double quote (ascii 34)
        output = 34;
        break;

    case 'x':
        // '\x00' = two-digit hex value
        {
            loc = state->location;
            int ch1 = read_hex_digit(state);
            if (ch1 >= 0) {
                loc = state->location;
                int ch2 = read_hex_digit(state);
                if (ch2 >= 0) {
                    output = 16 * ch1 + ch2;
                }
            }
        }
        break;
    }

    if (output < 0) {
        state->location = loc;
        reset_location(state);
        report_lexical_error(state->location);
        state->error = true;
    }

    return output;
}

static void lex_string_literal(struct LexerState *state)
{
    uint8_t * buf = NULL;
    uint32_t len = 0;
    uint32_t capacity = 0;
    const uint32_t MAX_STRING_LEN = 10000000u;

    bool end = false;

    while (!end) {
        struct Location ch_loc = state->location;
        int ch = read_next_char(state);

        if (ch == '\"') {
            // end of string
            end = true;
            ch = 0;  // add null terminator

        } else if (ch == '\n' || ch == EOF) {
            // EOF or newline during string - error
            state->location = ch_loc;
            reset_location(state);
            report_error(state);
            break;

        } else if (ch == '\\') {
            ch = lex_escape_sequence(state);
        }

        // expand the buffer if necessary
        if (len == capacity) {
            if (capacity == 0) {
                capacity = 100;
            } else {
                capacity *= 2;
            }
            if (capacity > MAX_STRING_LEN) {
                // unexpectedly big string... something has probably gone wrong somewhere
                report_error(state);
                break;
            }
            uint8_t * new_buf = alloc(capacity);
            if (buf) {
                memcpy(new_buf, buf, len);
                free(buf);
            }
            buf = new_buf;
        }

        buf[len] = (uint8_t)ch;
        ++len;
    }

    add_token(state, TOK_STRING_LITERAL, (char*)buf, len);
    free(buf);
}

static void lex_keyword_or_name(struct LexerState *state)
{
    char buf[MAX_NAME_LEN + 1];
    unsigned int index = 0;
    int ch;

    while (1) {
        ch = peek_next_char(state);
        if (!isalnum(ch) && ch != '_') {
            break;
        }
        read_next_char(state);

        if (index >= sizeof(buf) - 1) {
            // Name too long
            report_error(state);
            return;
        }

        buf[index++] = ch;
    }

    buf[index] = 0;

    struct Token * old_tail = state->tail;

    switch (buf[0]) {
    case 'a':
        if (strcmp(&buf[1], "llocated") == 0) {
            add_simple_token(state, TOK_KW_ALLOCATED);
        } else if (strcmp(&buf[1], "s") == 0) {
            add_simple_token(state, TOK_KW_AS);
        } else if (strcmp(&buf[1], "ssert") == 0) {
            add_simple_token(state, TOK_KW_ASSERT);
        } else if (strcmp(&buf[1], "ssume") == 0) {
            add_simple_token(state, TOK_KW_ASSUME);
        }
        break;

    case 'b':
        if (strcmp(&buf[1], "ool") == 0) {
            add_simple_token(state, TOK_KW_BOOL);
        }
        break;

    case 'c':
        if (strcmp(&buf[1], "ase") == 0) {
            add_simple_token(state, TOK_KW_CASE);
        } else if (strcmp(&buf[1], "onst") == 0) {
            add_simple_token(state, TOK_KW_CONST);
        }
        break;

    case 'd':
        if (strcmp(&buf[1], "atatype") == 0) {
            add_simple_token(state, TOK_KW_DATATYPE);
        } else if (strcmp(&buf[1], "ecreases") == 0) {
            add_simple_token(state, TOK_KW_DECREASES);
        }
        break;

    case 'e':
        if (strcmp(&buf[1], "lse") == 0) {
            add_simple_token(state, TOK_KW_ELSE);
        } else if (strcmp(&buf[1], "nsures") == 0) {
            add_simple_token(state, TOK_KW_ENSURES);
        } else if (strcmp(&buf[1], "xists") == 0) {
            add_simple_token(state, TOK_KW_EXISTS);
        } else if (strcmp(&buf[1], "xtern") == 0) {
            add_simple_token(state, TOK_KW_EXTERN);
        }
        break;

    case 'f':
        if (strcmp(&buf[1], "alse") == 0) {
            add_simple_token(state, TOK_KW_FALSE);
        } else if (strcmp(&buf[1], "ix") == 0) {
            add_simple_token(state, TOK_KW_FIX);
        } else if (strcmp(&buf[1], "orall") == 0) {
            add_simple_token(state, TOK_KW_FORALL);
        } else if (strcmp(&buf[1], "unction") == 0) {
            add_simple_token(state, TOK_KW_FUNCTION);
        }
        break;

    case 'g':
        if (strcmp(&buf[1], "host") == 0) {
            add_simple_token(state, TOK_KW_GHOST);
        }
        break;

    case 'h':
        if (strcmp(&buf[1], "ide") == 0) {
            add_simple_token(state, TOK_KW_HIDE);
        }
        break;

    case 'i':
        switch (buf[1]) {
        case '8':
            if (buf[2] == 0) {
                add_simple_token(state, TOK_KW_I8);
            }
            break;

        case '1':
            if (strcmp(&buf[2], "6") == 0) {
                add_simple_token(state, TOK_KW_I16);
            }
            break;

        case '3':
            if (strcmp(&buf[2], "2") == 0) {
                add_simple_token(state, TOK_KW_I32);
            }
            break;

        case '6':
            if (strcmp(&buf[2], "4") == 0) {
                add_simple_token(state, TOK_KW_I64);
            }
            break;

        case 'f':
            if (buf[2] == 0) {
                add_simple_token(state, TOK_KW_IF);
            }
            break;

        case 'm':
            if (strcmp(&buf[2], "port") == 0) {
                add_simple_token(state, TOK_KW_IMPORT);
            }
            break;

        case 'n':
            if (buf[2] == 0) {
                add_simple_token(state, TOK_KW_IN);
            } else if (strcmp(&buf[2], "t") == 0) {
                add_simple_token(state, TOK_KW_INT);
            } else if (strcmp(&buf[2], "terface") == 0) {
                add_simple_token(state, TOK_KW_INTERFACE);
            } else if (strcmp(&buf[2], "variant") == 0) {
                add_simple_token(state, TOK_KW_INVARIANT);
            }
            break;
        }
        break;

    case 'l':
        if (strcmp(&buf[1], "et") == 0) {
            add_simple_token(state, TOK_KW_LET);
        }
        break;

    case 'm':
        if (strcmp(&buf[1], "atch") == 0) {
            add_simple_token(state, TOK_KW_MATCH);
        } else if (strcmp(&buf[1], "odule") == 0) {
            add_simple_token(state, TOK_KW_MODULE);
        }
        break;

    case 'o':
        if (strcmp(&buf[1], "btain") == 0) {
            add_simple_token(state, TOK_KW_OBTAIN);
        } else if (strcmp(&buf[1], "ld") == 0) {
            add_simple_token(state, TOK_KW_OLD);
        }
        break;

    case 'r':
        if (strcmp(&buf[1], "eal") == 0) {
            add_simple_token(state, TOK_KW_REAL);
        } else if (strcmp(&buf[1], "ef") == 0) {
            add_simple_token(state, TOK_KW_REF);
        } else if (strcmp(&buf[1], "equires") == 0) {
            add_simple_token(state, TOK_KW_REQUIRES);
        } else if (strcmp(&buf[1], "eturn") == 0) {
            add_simple_token(state, TOK_KW_RETURN);
        }
        break;

    case 's':
        if (strcmp(&buf[1], "how") == 0) {
            add_simple_token(state, TOK_KW_SHOW);
        } else if (strcmp(&buf[1], "izeof") == 0) {
            add_simple_token(state, TOK_KW_SIZEOF);
        } else if (strcmp(&buf[1], "wap") == 0) {
            add_simple_token(state, TOK_KW_SWAP);
        }
        break;

    case 't':
        if (strcmp(&buf[1], "hen") == 0) {
            add_simple_token(state, TOK_KW_THEN);
        } else if (strcmp(&buf[1], "rue") == 0) {
            add_simple_token(state, TOK_KW_TRUE);
        } else if (strcmp(&buf[1], "ype") == 0) {
            add_simple_token(state, TOK_KW_TYPE);
        }
        break;

    case 'u':
        if (strcmp(&buf[1], "8") == 0) {
            add_simple_token(state, TOK_KW_U8);
        } else if (strcmp(&buf[1], "16") == 0) {
            add_simple_token(state, TOK_KW_U16);
        } else if (strcmp(&buf[1], "32") == 0) {
            add_simple_token(state, TOK_KW_U32);
        } else if (strcmp(&buf[1], "64") == 0) {
            add_simple_token(state, TOK_KW_U64);
        } else if (strcmp(&buf[1], "se") == 0) {
            add_simple_token(state, TOK_KW_USE);
        }
        break;

    case 'v':
        if (strcmp(&buf[1], "ar") == 0) {
            add_simple_token(state, TOK_KW_VAR);
        }
        break;

    case 'w':
        if (strcmp(&buf[1], "hile") == 0) {
            add_simple_token(state, TOK_KW_WHILE);
        } else if (strcmp(&buf[1], "ith") == 0) {
            add_simple_token(state, TOK_KW_WITH);
        }
        break;

    case '_':
        if (buf[1] == 0) {
            add_simple_token(state, TOK_UNDERSCORE);
        }
    }

    if (old_tail == state->tail) {
        add_token(state, TOK_NAME, buf, strlen(buf) + 1);
    }
}


static void lex_token(struct LexerState *state, int ch)
{
    if (isalpha(ch) || ch == '_') {
        lex_keyword_or_name(state);

    } else if (isdigit(ch)) {
        lex_int_literal(state);

    } else {
        read_next_char(state);

        switch (ch) {
        case '\"':
            lex_string_literal(state);
            break;

        case '-':
            add_simple_token(state, TOK_MINUS);
            break;

        case '+':
            add_simple_token(state, TOK_PLUS);
            break;

        case '*':
            add_simple_token(state, TOK_TIMES);
            break;

        case '/':
            ch = peek_next_char(state);
            if (ch == '/') {
                // line comment
                skip_rest_of_line(state);
                reset_location(state);
            } else if (ch == '*') {
                // block comment
                struct Location loc = state->location;  // location of the '/'
                read_next_char(state);
                skip_block_comment(state, loc);
            } else {
                add_simple_token(state, TOK_DIVIDE);
            }
            break;

        case '%':
            add_simple_token(state, TOK_MODULO);
            break;

        case '&':
            ch = peek_next_char(state);
            if (ch == '&') {
                read_next_char(state);
                add_simple_token(state, TOK_AND_AND);
            } else {
                add_simple_token(state, TOK_AND);
            }
            break;

        case '|':
            ch = peek_next_char(state);
            if (ch == '|') {
                read_next_char(state);
                add_simple_token(state, TOK_BAR_BAR);
            } else {
                add_simple_token(state, TOK_BAR);
            }
            break;

        case '^':
            add_simple_token(state, TOK_HAT);
            break;

        case '!':
            ch = peek_next_char(state);
            if (ch == '=') {
                read_next_char(state);
                add_simple_token(state, TOK_EXCLAM_EQUAL);
            } else {
                add_simple_token(state, TOK_EXCLAM);
            }
            break;

        case '~':
            add_simple_token(state, TOK_TILDE);
            break;

        case ':':
            add_simple_token(state, TOK_COLON);
            break;

        case ';':
            add_simple_token(state, TOK_SEMICOLON);
            break;

        case ',':
            add_simple_token(state, TOK_COMMA);
            break;

        case '=':
            ch = peek_next_char(state);
            if (ch == '=') {
                read_next_char(state);
                ch = peek_next_char(state);
                if (ch == '>') {
                    read_next_char(state);
                    add_simple_token(state, TOK_EQUAL_EQUAL_GREATER);
                } else {
                    add_simple_token(state, TOK_EQUAL_EQUAL);
                }
            } else if (ch == '>') {
                read_next_char(state);
                add_simple_token(state, TOK_EQUAL_GREATER);
            } else {
                add_simple_token(state, TOK_EQUAL);
            }
            break;

        case '.':
            add_simple_token(state, TOK_DOT);
            break;

        case '(':
            add_simple_token(state, TOK_LPAREN);
            break;

        case ')':
            add_simple_token(state, TOK_RPAREN);
            break;

        case '{':
            add_simple_token(state, TOK_LBRACE);
            break;

        case '}':
            add_simple_token(state, TOK_RBRACE);
            break;

        case '[':
            add_simple_token(state, TOK_LBRACKET);
            break;

        case ']':
            add_simple_token(state, TOK_RBRACKET);
            break;

        case '<':
            ch = peek_next_char(state);
            if (ch == '=') {
                read_next_char(state);
                ch = peek_next_char(state);
                if (ch == '=') {
                    read_next_char(state);
                    ch = peek_next_char(state);
                    if (ch == '>') {
                        read_next_char(state);
                        add_simple_token(state, TOK_LESS_EQUAL_EQUAL_GREATER);
                    } else {
                        add_simple_token(state, TOK_LESS_EQUAL_EQUAL);
                    }
                } else {
                    add_simple_token(state, TOK_LESS_EQUAL);
                }
            } else if (ch == '<') {
                read_next_char(state);
                add_simple_token(state, TOK_LESS_LESS);
            } else {
                add_simple_token(state, TOK_LESS);
            }
            break;

        case '>':
            ch = peek_next_char(state);
            if (ch == '=') {
                read_next_char(state);
                add_simple_token(state, TOK_GREATER_EQUAL);
            } else if (ch == '>') {
                read_next_char(state);
                add_simple_token(state, TOK_GREATER_GREATER);
            } else {
                add_simple_token(state, TOK_GREATER);
            }
            break;

        default:
            // Invalid character
            report_error(state);
            break;
        }
    }
}

static struct Token * run_lexer(const char *filename,
                                FILE *file, const unsigned char *char_data,
                                bool interface_only)
{
    struct LexerState state;
    int ch;

    state.file = file;
    state.char_data = char_data;
    state.location.filename = filename;
    state.location.begin_line_num = state.location.begin_column_num = 1;
    state.location.end_line_num = state.location.end_column_num = 1;
    state.head = state.tail = NULL;
    state.next_char = EOF;
    state.error = false;
    state.interface_only = interface_only;
    state.done = false;

    // Loop until done
    while (!state.done) {

        // Get rid of any whitespace
        while (1) {
            ch = peek_next_char(&state);
            if (ch == EOF || !isspace(ch)) {
                break;
            }
            read_next_char(&state);
            reset_location(&state);
        }

        // Have we reached EOF?
        if (ch == EOF) {
            add_simple_token(&state, TOK_EOF);
            break;
        }

        // If not, then get the next token
        lex_token(&state, ch);
    }

    if (state.error) {
        free_token(state.head);
        return NULL;
    } else {
        return state.head;
    }
}

struct Token * lex(const char *filename, FILE *file, bool interface_only)
{
    return run_lexer(filename, file, NULL, interface_only);
}

struct Token * lex_from_char_data(const char *filename, const char *char_data, bool interface_only)
{
    return run_lexer(filename, NULL, (const unsigned char *)char_data, interface_only);
}

void free_token(struct Token *token)
{
    if (token != NULL) {
        free_token(token->next);
        free(token->data);
        free(token);
    }
}


static void complex_token(struct SHA256_CTX *ctx, const struct Token *token, const char *str)
{
    // add the string including terminating null
    sha256_add_bytes(ctx, (uint8_t*)str, strlen(str)+1);

    // add the argument, with its length
    sha256_add_bytes(ctx, (uint8_t*)&token->length, sizeof(token->length));
    sha256_add_bytes(ctx, (uint8_t*)token->data, token->length);
}

static void simple_token(struct SHA256_CTX *ctx, const char *str)
{
    // add the string including terminating null
    sha256_add_bytes(ctx, (uint8_t*)str, strlen(str)+1);
}

void sha256_add_token(struct SHA256_CTX *ctx, const struct Token *token)
{
    // each token must have a unique identifying string

    switch (token->type) {
    case TOK_INT_LITERAL: complex_token(ctx, token, "INTLIT"); break;
    case TOK_STRING_LITERAL: complex_token(ctx, token, "STRLIT"); break;
    case TOK_NAME: complex_token(ctx, token, "VARNAM"); break;

    case TOK_KW_ALLOCATED: simple_token(ctx, "allocated"); break;
    case TOK_KW_AS: simple_token(ctx, "as"); break;
    case TOK_KW_ASSERT: simple_token(ctx, "assert"); break;
    case TOK_KW_ASSUME: simple_token(ctx, "assume"); break;
    case TOK_KW_BOOL: simple_token(ctx, "bool"); break;
    case TOK_KW_CASE: simple_token(ctx, "case"); break;
    case TOK_KW_CONST: simple_token(ctx, "const"); break;
    case TOK_KW_DATATYPE: simple_token(ctx, "datatype"); break;
    case TOK_KW_DECREASES: simple_token(ctx, "decreases"); break;
    case TOK_KW_ELSE: simple_token(ctx, "else"); break;
    case TOK_KW_ENSURES: simple_token(ctx, "ensures"); break;
    case TOK_KW_EXISTS: simple_token(ctx, "exists"); break;
    case TOK_KW_EXTERN: simple_token(ctx, "extern"); break;
    case TOK_KW_FALSE: simple_token(ctx, "false"); break;
    case TOK_KW_FIX: simple_token(ctx, "fix"); break;
    case TOK_KW_FORALL: simple_token(ctx, "forall"); break;
    case TOK_KW_FUNCTION: simple_token(ctx, "function"); break;
    case TOK_KW_GHOST: simple_token(ctx, "ghost"); break;
    case TOK_KW_HIDE: simple_token(ctx, "hide"); break;
    case TOK_KW_I8: simple_token(ctx, "i8"); break;
    case TOK_KW_I16: simple_token(ctx, "i16"); break;
    case TOK_KW_I32: simple_token(ctx, "i32"); break;
    case TOK_KW_I64: simple_token(ctx, "i64"); break;
    case TOK_KW_IF: simple_token(ctx, "if"); break;
    case TOK_KW_IMPORT: simple_token(ctx, "import"); break;
    case TOK_KW_IN: simple_token(ctx, "in"); break;
    case TOK_KW_INT: simple_token(ctx, "int"); break;
    case TOK_KW_INTERFACE: simple_token(ctx, "interface"); break;
    case TOK_KW_INVARIANT: simple_token(ctx, "invariant"); break;
    case TOK_KW_LET: simple_token(ctx, "let"); break;
    case TOK_KW_MATCH: simple_token(ctx, "match"); break;
    case TOK_KW_MODULE: simple_token(ctx, "module"); break;
    case TOK_KW_OBTAIN: simple_token(ctx, "obtain"); break;
    case TOK_KW_OLD: simple_token(ctx, "old"); break;
    case TOK_KW_REAL: simple_token(ctx, "real"); break;
    case TOK_KW_REF: simple_token(ctx, "ref"); break;
    case TOK_KW_REQUIRES: simple_token(ctx, "requires"); break;
    case TOK_KW_RETURN: simple_token(ctx, "return"); break;
    case TOK_KW_SHOW: simple_token(ctx, "show"); break;
    case TOK_KW_SIZEOF: simple_token(ctx, "sizeof"); break;
    case TOK_KW_SWAP: simple_token(ctx, "swap"); break;
    case TOK_KW_THEN: simple_token(ctx, "then"); break;
    case TOK_KW_TRUE: simple_token(ctx, "true"); break;
    case TOK_KW_TYPE: simple_token(ctx, "type"); break;
    case TOK_KW_U8: simple_token(ctx, "u8"); break;
    case TOK_KW_U16: simple_token(ctx, "u16"); break;
    case TOK_KW_U32: simple_token(ctx, "u32"); break;
    case TOK_KW_U64: simple_token(ctx, "u64"); break;
    case TOK_KW_USE: simple_token(ctx, "use"); break;
    case TOK_KW_VAR: simple_token(ctx, "var"); break;
    case TOK_KW_WHILE: simple_token(ctx, "while"); break;
    case TOK_KW_WITH: simple_token(ctx, "with"); break;

    case TOK_PLUS: simple_token(ctx, "+"); break;
    case TOK_MINUS: simple_token(ctx, "-"); break;
    case TOK_TIMES: simple_token(ctx, "*"); break;
    case TOK_DIVIDE: simple_token(ctx, "/"); break;
    case TOK_MODULO: simple_token(ctx, "%"); break;

    case TOK_AND: simple_token(ctx, "&"); break;
    case TOK_AND_AND: simple_token(ctx, "&&"); break;
    case TOK_BAR: simple_token(ctx, "|"); break;
    case TOK_BAR_BAR: simple_token(ctx, "||"); break;
    case TOK_HAT: simple_token(ctx, "^"); break;
    case TOK_EXCLAM: simple_token(ctx, "!"); break;
    case TOK_TILDE: simple_token(ctx, "~"); break;

    case TOK_LESS: simple_token(ctx, "<"); break;
    case TOK_LESS_LESS: simple_token(ctx, "<<"); break;
    case TOK_LESS_EQUAL: simple_token(ctx, "<="); break;
    case TOK_LESS_EQUAL_EQUAL: simple_token(ctx, "<=="); break;
    case TOK_LESS_EQUAL_EQUAL_GREATER: simple_token(ctx, "<==>"); break;

    case TOK_GREATER: simple_token(ctx, ">"); break;
    case TOK_GREATER_GREATER: simple_token(ctx, ">>"); break;
    case TOK_GREATER_EQUAL: simple_token(ctx, ">="); break;

    case TOK_EQUAL: simple_token(ctx, "="); break;
    case TOK_EQUAL_GREATER: simple_token(ctx, "=>"); break;
    case TOK_EQUAL_EQUAL: simple_token(ctx, "=="); break;
    case TOK_EQUAL_EQUAL_GREATER: simple_token(ctx, "==>"); break;
    case TOK_EXCLAM_EQUAL: simple_token(ctx, "!="); break;

    case TOK_COLON: simple_token(ctx, ":"); break;
    case TOK_SEMICOLON: simple_token(ctx, ";"); break;
    case TOK_COMMA: simple_token(ctx, ","); break;
    case TOK_DOT: simple_token(ctx, "."); break;

    case TOK_LPAREN: simple_token(ctx, "("); break;
    case TOK_RPAREN: simple_token(ctx, ")"); break;
    case TOK_LBRACE: simple_token(ctx, "{"); break;
    case TOK_RBRACE: simple_token(ctx, "}"); break;
    case TOK_LBRACKET: simple_token(ctx, "["); break;
    case TOK_RBRACKET: simple_token(ctx, "]"); break;

    case TOK_UNDERSCORE: simple_token(ctx, "_"); break;

    case TOK_EOF: simple_token(ctx, "EOF"); break;
    }
}

/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#include "alloc.h"
#include "error.h"
#include "lexer.h"

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
    case '0':
        // '\0' = null character (ascii 0)
        output = 0;
        break;

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

    while (1) {
        struct Location ch_loc = state->location;
        int ch = read_next_char(state);

        if (ch == '\"') {
            // end of string
            break;

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
        if (strcmp(&buf[1], "ef") == 0) {
            add_simple_token(state, TOK_KW_REF);
        } else if (strcmp(&buf[1], "equires") == 0) {
            add_simple_token(state, TOK_KW_REQUIRES);
        } else if (strcmp(&buf[1], "eturn") == 0) {
            add_simple_token(state, TOK_KW_RETURN);
        }
        break;

    case 's':
        if (strcmp(&buf[1], "izeof") == 0) {
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

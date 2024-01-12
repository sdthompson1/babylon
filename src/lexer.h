/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/



#ifndef LEXER_H
#define LEXER_H

#include "location.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

enum TokenType {
    TOK_INT_LITERAL,
    TOK_STRING_LITERAL,
    TOK_NAME,

    TOK_KW_ALLOCATED,
    TOK_KW_AS,
    TOK_KW_ASSERT,
    TOK_KW_ASSUME,
    TOK_KW_BOOL,
    TOK_KW_CASE,
    TOK_KW_CONST,
    TOK_KW_DATATYPE,
    TOK_KW_DECREASES,
    TOK_KW_ELSE,
    TOK_KW_ENSURES,
    TOK_KW_EXISTS,
    TOK_KW_EXTERN,
    TOK_KW_FALSE,
    TOK_KW_FIX,
    TOK_KW_FORALL,
    TOK_KW_FUNCTION,
    TOK_KW_GHOST,
    TOK_KW_HIDE,
    TOK_KW_I8,
    TOK_KW_I16,
    TOK_KW_I32,
    TOK_KW_I64,
    TOK_KW_IF,
    TOK_KW_IMPORT,
    TOK_KW_IN,
    TOK_KW_INT,
    TOK_KW_INTERFACE,
    TOK_KW_INVARIANT,
    TOK_KW_LET,
    TOK_KW_MATCH,
    TOK_KW_MODULE,
    TOK_KW_OBTAIN,
    TOK_KW_OLD,
    TOK_KW_REAL,
    TOK_KW_REF,
    TOK_KW_REQUIRES,
    TOK_KW_RETURN,
    TOK_KW_SHOW,
    TOK_KW_SIZEOF,
    TOK_KW_SWAP,
    TOK_KW_THEN,
    TOK_KW_TRUE,
    TOK_KW_TYPE,
    TOK_KW_U8,
    TOK_KW_U16,
    TOK_KW_U32,
    TOK_KW_U64,
    TOK_KW_USE,
    TOK_KW_VAR,
    TOK_KW_WHILE,
    TOK_KW_WITH,

    TOK_PLUS,
    TOK_MINUS,
    TOK_TIMES,
    TOK_DIVIDE,
    TOK_MODULO,

    TOK_AND,
    TOK_AND_AND,
    TOK_BAR,
    TOK_BAR_BAR,
    TOK_HAT,
    TOK_EXCLAM,
    TOK_TILDE,

    TOK_LESS,
    TOK_LESS_LESS,
    TOK_LESS_EQUAL,
    TOK_LESS_EQUAL_EQUAL,
    TOK_LESS_EQUAL_EQUAL_GREATER,

    TOK_GREATER,
    TOK_GREATER_GREATER,
    TOK_GREATER_EQUAL,

    TOK_EQUAL,
    TOK_EQUAL_GREATER,
    TOK_EQUAL_EQUAL,
    TOK_EQUAL_EQUAL_GREATER,

    TOK_EXCLAM_EQUAL,

    TOK_COLON,
    TOK_SEMICOLON,
    TOK_COMMA,
    TOK_DOT,

    TOK_LPAREN,
    TOK_RPAREN,
    TOK_LBRACE,
    TOK_RBRACE,
    TOK_LBRACKET,
    TOK_RBRACKET,

    TOK_UNDERSCORE,

    TOK_EOF   // always last
};

struct Token {
    struct Token *next;
    struct Location location;
    enum TokenType type;
    char *data;
    uint32_t length;
};

// Note: filename is NOT copied, make sure it is somewhere permanent.
// Free the resulting Token* using free_token.
struct Token * lex(const char *filename, FILE *file,
                   bool interface_only);

struct Token * lex_from_char_data(const char *filename, const char *file_contents,
                                  bool interface_only);

void free_token(struct Token *token);

struct SHA256_CTX;
void sha256_add_token(struct SHA256_CTX *ctx, const struct Token *token);

#endif

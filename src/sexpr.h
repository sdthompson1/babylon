/*
This file is part of the Babylon compiler.

Copyright (C) Stephen Thompson, 2023--2024.

For licensing information please see LICENCE.txt at the root of the
repository.
*/


#ifndef SEXPR_H
#define SEXPR_H

struct StringBuf;

enum SexprType {
    S_STRING,
    S_PAIR
    // note: "NULL" is also a valid sexpr
};

// note: "string", "left" and "right" are assumed to be results of
// malloc calls (and therefore can and should be freed in free_sexpr).
// also: Strings are expected to follow the syntax rules of SMT-LIB
// (e.g. quoting with "|" characters if required).
struct Sexpr {
    enum SexprType type;
    union {
        const char *string;
        struct {
            struct Sexpr *left;
            struct Sexpr *right;
        };
    };
};

// Allocate string sexpr. Copies the char* data.
struct Sexpr * make_string_sexpr(const char *data);

// Allocate string sexpr. Hands over ownership of the char* data.
struct Sexpr * make_string_sexpr_handover(const char *data);

// Allocate pair sexpr. Does NOT copy the two input sexprs.
struct Sexpr * make_pair_sexpr(struct Sexpr *left, struct Sexpr *right);


// Apply a bottom-up "transform" to an Sexpr.
struct SexprTransform {
    void * (*transform_string) (void *context, struct Sexpr *sexpr);
    void * (*transform_pair) (void *context, struct Sexpr *sexpr, void *left, void *right);
};
void* transform_sexpr(struct SexprTransform *transform, void *context, struct Sexpr *sexpr);

// Deep-copy an sexpr.
struct Sexpr * copy_sexpr(struct Sexpr *sexpr);

// Free a sexpr and all its children.
void free_sexpr(struct Sexpr *sexpr);


// List making functions.
struct Sexpr * make_list1_sexpr(struct Sexpr *s1);
struct Sexpr * make_list2_sexpr(struct Sexpr *s1, struct Sexpr *s2);
struct Sexpr * make_list3_sexpr(struct Sexpr *s1, struct Sexpr *s2, struct Sexpr *s3);
struct Sexpr * make_list4_sexpr(struct Sexpr *s1, struct Sexpr *s2, struct Sexpr *s3, struct Sexpr *s4);
struct Sexpr * make_list5_sexpr(struct Sexpr *s1, struct Sexpr *s2, struct Sexpr *s3, struct Sexpr *s4, struct Sexpr *s5);


// Get length of sexpr list. Returns 0 if it is NULL, or -1 if
// not a proper list.
int get_sexpr_list_length(const struct Sexpr *s);


// Append a string representation of a sexpr to a StringBuf.
void format_sexpr(struct StringBuf *buf, const struct Sexpr *expr);

// For debugging - print sexpr to stderr
void print_sexpr(const struct Sexpr *expr);

// Check if two sexprs are equal
bool sexpr_equal(const struct Sexpr *left, const struct Sexpr *right);

// True if the sexpr is a string and equal to the given string
bool sexpr_equal_string(const struct Sexpr *left, const char *right);


// Substitute strings for sexprs in a sexpr
// Copies the input expr (making changes as it goes), also copies any values substituted in.
struct Sexpr * substitute_in_sexpr(const struct Sexpr *keys,    // list of strings
                                   const struct Sexpr *values,  // list of sexprs
                                   const struct Sexpr *expr);


// Returns true if the given string is found (as a complete S_STRING) anywhere
// in the given sexpr.
bool sexpr_contains_string(const struct Sexpr *sexpr, const char *find);

#endif

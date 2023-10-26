#ifndef COMMON_TYPES_H
#define COMMON_TYPES_H

// Types needed by both game_engine.c and load_png.c.

#include <stdint.h>

// type String = u8[]
// Arrays are represented by a pointer to the data, followed by a 64-bit length.
struct String {
    char *data;
    uint64_t length;
};

// These will make valid C strings containing a NUL terminator
// (the NUL is counted as part of the length in the result).
struct String make_string(const char *string);
struct String make_string_3(const char *string1, const char *string2, const char *string3);


// type RGBA = {r:u8, g:u8, b:u8, a:u8}
struct RGBA {
    uint8_t r;
    uint8_t g;
    uint8_t b;
    uint8_t a;
};


// datatype Result = Error(u8[]) | Ok(T)
// A datatype is represented as a tag byte, followed by the payload type.
enum ResultTag {
    RESULT_OK,
    RESULT_ERROR
};

// Note: The compiler does not (currently) add the correct alignment-padding to structs,
// so we have to use __attribute__((__packed__)) on the C side.
struct __attribute__((__packed__)) Result {
    uint8_t tag;
    union {
        struct String error_string;

        // we allow for different "T"s of different sizes
        uint8_t value_8;
        uint32_t value_32;
        uint64_t value_64;
    };
};


// generic array types
struct Array1 {
    void *data;
    uint64_t num_elements;
};

struct Array2 {
    void *data;
    uint64_t num_elements_0;
    uint64_t num_elements_1;
};

// datatype Maybe<T> = Nothing | Just(T)
enum MaybeTag {
    MAYBE_NOTHING,
    MAYBE_JUST
};

#endif

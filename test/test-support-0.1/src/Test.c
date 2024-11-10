#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void print_i8(int8_t i)
{
    printf("%" PRIi8 "\n", i);
}

void print_i16(int16_t i)
{
    printf("%" PRIi16 "\n", i);
}

void print_i32(int32_t i)
{
    printf("%" PRIi32 "\n", i);
}

void print_i64(int64_t i)
{
    printf("%" PRIi64 "\n", i);
}

void print_u8(uint8_t i)
{
    printf("%" PRIu8 "\n", i);
}

void print_u16(uint16_t i)
{
    printf("%" PRIu16 "\n", i);
}

void print_u32(uint32_t i)
{
    printf("%" PRIu32 "\n", i);
}

void print_u64(uint64_t i)
{
    printf("%" PRIu64 "\n", i);
}

void print_bool(bool b)
{
    puts(b ? "true" : "false");
}

void print_string(void *str)
{
    char *data;
    memcpy(&data, str, sizeof(data));
    printf("%s", data);
}

void alloc_array(uint64_t elt_size, char *array, uint64_t dim)
{
    // Note: we assume (in this function, and in free_array) that
    // size_t is 64-bit, and that NULL is represented as a zero
    // bit-pattern.

    // Allocate some new space. Use calloc to ensure the new
    // elements are zero-initialized.
    // Note: Ensure we use NULL, rather than some calloc-produced
    // dummy memory block, when the dim is zero (because the language
    // doesn't count zero-sized arrays as allocated and will not
    // free them).
    void *p = NULL;
    if (dim != 0) {
        p = calloc(dim, elt_size);
        if (p == NULL) {
            // We are out of memory, abort program.
            abort();
        }
    }

    // Write the pointer and size into the descriptor.
    memcpy(array, &p, sizeof(void*));
    memcpy(array + sizeof(void*), &dim, 8);
}

void free_array(uint64_t elt_size, char *array)
{
    // Read the pointer out of the descriptor.
    void *p;
    memcpy(&p, array, sizeof(void*));

    // Free the pointer.
    // Note: freeing NULL is acceptable in C, so if the array
    // was already empty, then this will do nothing, which is fine.
    free(p);

    // Write NULL, and the new size (0), back to the descriptor.
    memset(array, 0, sizeof(void*) + 8);
}

void alloc_2d_array(uint64_t elt_size, char *array, uint64_t dim0, uint64_t dim1)
{
    void *p = NULL;
    if (dim0 != 0 && dim1 != 0) {  // both dimensions have to be nonzero to allocate anything
        // Note: Multiplying the dimensions is guaranteed safe by the function precondition
        uint64_t dim = dim0 * dim1;
        p = calloc(dim, elt_size);
        if (p == NULL) {
            abort();
        }
    }

    memcpy(array, &p, sizeof(void*));
    memcpy(array + sizeof(void*), &dim0, 8);
    memcpy(array + sizeof(void*) + 8, &dim1, 8);
}

void free_2d_array(uint64_t elt_size, char *array)
{
    void *p;
    memcpy(&p, array, sizeof(void*));
    free(p);
    memset(array, 0, sizeof(void*) + 16);
}

void alloc_3d_array(uint64_t elt_size, char *array, uint64_t dim0, uint64_t dim1, uint64_t dim2)
{
    void *p = NULL;
    if (dim0 != 0 && dim1 != 0 && dim2 != 0) {
        uint64_t dim = dim0 * dim1 * dim2;
        p = calloc(dim, elt_size);
        if (p == NULL) {
            abort();
        }
    }

    memcpy(array, &p, sizeof(void*));
    memcpy(array + sizeof(void*), &dim0, 8);
    memcpy(array + sizeof(void*) + 8, &dim1, 8);
    memcpy(array + sizeof(void*) + 16, &dim2, 8);
}

void free_3d_array(uint64_t elt_size, char *array)
{
    void *p;
    memcpy(&p, array, sizeof(void*));
    free(p);
    memset(array, 0, sizeof(void*) + 24);
}


void allocate_alloc_test(char *maybe)
{
    uint8_t tag;
    uint64_t value;
    memcpy(&tag, maybe, 1);
    memcpy(&value, maybe + 1, 8);

    if (tag != 0 || value != 0) {
        printf("Precondition violated!\n");
        abort();
    }

    tag = 1;
    value = 999;

    memcpy(maybe, &tag, 1);
    memcpy(maybe + 1, &value, 8);
}

void free_alloc_test(char *maybe)
{
    uint8_t tag;
    uint64_t value;
    memcpy(&tag, maybe, 1);
    memcpy(&value, maybe + 1, 8);

    if (tag != 1 || value != 999) {
        printf("Precondition violated!\n");
        abort();
    }

    tag = 0;
    value = 0;

    memcpy(maybe, &tag, 1);
    memcpy(maybe + 1, &value, 8);
}

// Used in test ExternInImpl.b
int32_t c_test_fun()
{
    return 42;
}

// Used in codegen/ExternName.b
void c_function_with_custom_name()
{
    printf("Hello from c_function_with_custom_name!\n");
}

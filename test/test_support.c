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

void alloc_array(char *arr, uint64_t elt_size, uint64_t dim)
{
    void *ptr = calloc(dim, elt_size);
    if (ptr == NULL) {
        abort();
    }
    memcpy(arr, &ptr, sizeof(void*));
    memcpy(arr + sizeof(void*), &dim, 8);
}

void free_array(uint64_t elt_size, char *arr)
{
    void *ptr;
    memcpy(&ptr, arr, sizeof(void*));
    free(ptr);
}

void alloc_2d_array(char *arr, uint64_t elt_size, uint64_t dim0, uint64_t dim1)
{
    void *ptr = calloc(dim0 * dim1, elt_size);
    if (ptr == NULL) {
        abort();
    }
    memcpy(arr, &ptr, sizeof(void*));
    memcpy(arr + sizeof(void*), &dim0, 8);
    memcpy(arr + sizeof(void*) + 8, &dim1, 8);
}

void free_2d_array(uint64_t elt_size, char *arr)
{
    void *ptr;
    memcpy(&ptr, arr, sizeof(void*));
    free(ptr);
}

void alloc_3d_array(char *arr, uint64_t elt_size, uint64_t dim0, uint64_t dim1, uint64_t dim2)
{
    void *ptr = calloc(dim0 * dim1 * dim2, elt_size);
    if (ptr == NULL) {
        abort();
    }
    memcpy(arr, &ptr, sizeof(void*));
    memcpy(arr + sizeof(void*), &dim0, 8);
    memcpy(arr + sizeof(void*) + 8, &dim1, 8);
    memcpy(arr + sizeof(void*) + 16, &dim2, 8);
}

void free_3d_array(uint64_t elt_size, char *arr)
{
    void *ptr;
    memcpy(&ptr, arr, sizeof(void*));
    free(ptr);
}

// Used in test ExternInImpl.b
int32_t c_test_fun()
{
    return 42;
}

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static void* get_array_ptr(char *array)
{
    void *result;
    memcpy(&result, array, sizeof(void*));
    return result;
}

static void write_array_1d(char *array, void *ptr, uint64_t size)
{
    memcpy(array, &ptr, sizeof(void*));
    memcpy(array + sizeof(void*), &size, 8);
}

static void write_array_2d(char *array, void *ptr, uint64_t size0, uint64_t size1)
{
    memcpy(array, &ptr, sizeof(void*));
    memcpy(array + sizeof(void*), &size0, 8);
    memcpy(array + sizeof(void*) + 8, &size1, 8);
}

static void write_array_3d(char *array, void *ptr, uint64_t size0, uint64_t size1, uint64_t size2)
{
    memcpy(array, &ptr, sizeof(void*));
    memcpy(array + sizeof(void*), &size0, 8);
    memcpy(array + sizeof(void*) + 8, &size1, 8);
    memcpy(array + sizeof(void*) + 16, &size2, 8);
}

bool alloc_array(uint64_t elem_size,
                 char *array,
                 uint64_t new_dim)
{
    // precondition: array size is zero
    // precondition: new_dim is non-zero
    // postcondition: return = true ==> array size is new_dim and all elements are zero
    // postcondition: return = false ==> array is unchanged

    if (new_dim > SIZE_MAX) {
        // calloc can only allocate upto SIZE_MAX elements
        return false;
    }

    void *ptr = calloc(new_dim, elem_size);

    if (ptr != NULL) {
        write_array_1d(array, ptr, new_dim);
        return true;
    } else {
        return false;
    }
}

void free_array(uint64_t elem_size,
                char *array)
{
    // precondition: none
    // postcondition: array size is zero

    free(get_array_ptr(array));
    write_array_1d(array, NULL, 0);
}

bool alloc_2d_array(uint64_t elem_size,
                    char *array,
                    uint64_t new_dim_0,
                    uint64_t new_dim_1)
{
    // pre/post conditions: as alloc_array, but also, product of dims does not
    // overflow a u64 (and is at least 1)
    uint64_t total_dim = new_dim_0 * new_dim_1;

    if (total_dim > SIZE_MAX) {
        return false;
    }

    void *ptr = calloc(total_dim, elem_size);

    if (ptr != NULL) {
        write_array_2d(array, ptr, new_dim_0, new_dim_1);
        return true;
    } else {
        return false;
    }
}

void free_2d_array(uint64_t elem_size,
                   char *array)
{
    free(get_array_ptr(array));
    write_array_2d(array, NULL, 0, 0);
}

bool alloc_3d_array(uint64_t elem_size,
                    char *array,
                    uint64_t new_dim_0,
                    uint64_t new_dim_1,
                    uint64_t new_dim_2)
{
    uint64_t total_dim = new_dim_0 * new_dim_1 * new_dim_2;

    if (total_dim > SIZE_MAX) {
        return false;
    }

    void *ptr = calloc(total_dim, elem_size);

    if (ptr != NULL) {
        write_array_3d(array, ptr, new_dim_0, new_dim_1, new_dim_2);
        return true;
    } else {
        return false;
    }
}

void free_3d_array(uint64_t elem_size,
                   char *array)
{
    free(get_array_ptr(array));
    write_array_3d(array, NULL, 0, 0, 0);
}

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

void resize_array(uint64_t elt_size, char *array, uint64_t new_dim)
{
    // Note: we assume size_t is 64-bit, and that reallocarray is available.

    // This will resize the array. Elements at positions less than both
    // new_dim and old_dim will be preserved. Elements above old_dim,
    // but below new_dim, will be zero-initialised.

    void *old_data;
    memcpy(&old_data, array, sizeof(void*));
    uint64_t old_dim;
    memcpy(&old_dim, array + sizeof(void*), 8);

    bool freeing = (new_dim == 0 || elt_size == 0);

    if (freeing) {
        // To avoid confusion, let's explicitly call free, rather than realloc with a zero size
        free(old_data);

        void *new_data = NULL;
        memcpy(array, &new_data, sizeof(void*));
        memcpy(array + sizeof(void*), &new_dim, 8);

    } else {
        // Call reallocarray with non-zero size(s).
        void *p = reallocarray(old_data, new_dim, elt_size);

        if (p == NULL) {
            // We are out of memory, abort program.
            abort();
        }

        // reallocarray will have preserved any existing array data, so
        // now we just have to zero out any new bytes (between old_dim and
        // new_dim).
        if (new_dim > old_dim) {
            memset((char*)p + old_dim * elt_size,
                   0,
                   (new_dim - old_dim) * elt_size);
        }

        memcpy(array, &p, sizeof(void*));
        memcpy(array + sizeof(void*), &new_dim, 8);
    }
}

void resize_2d_array(uint64_t elt_size, char *array, uint64_t new_dim1, uint64_t new_dim2)
{
    // This is the 2d equivalent of resize_array.

    // We can't use realloc as we have to not only copy the existing
    // data, but "reformat" it (if dim2 has changed).

    // To keep things simple we will just calloc a new buffer, then copy the
    // old data to it (row by row), then free the old buffer.

    void *old_data;
    uint64_t old_dim1, old_dim2;
    memcpy(&old_data, array, sizeof(void*));
    memcpy(&old_dim1, array + sizeof(void*), 8);
    memcpy(&old_dim2, array + sizeof(void*) + 8, 8);

    bool freeing = (new_dim1 == 0 || new_dim2 == 0 || elt_size == 0);

    if (freeing) {
        free(old_data);

        void *new_data = NULL;
        memcpy(array, &new_data, sizeof(void*));
        memcpy(array + sizeof(void*), &new_dim1, 8);
        memcpy(array + sizeof(void*) + 8, &new_dim2, 8);

    } else {
        // Note: multiplication of new_dim1 and new_dim2 is guaranteed not to overflow
        // because of the precondition in Test.b.
        // calloc will take care of the case where the multiplication by elt_size overflows.
        // calloc will also zero out any "new" bytes, as required.
        void *p = calloc(new_dim1 * new_dim2, elt_size);

        if (p == NULL) {
            abort();
        }

        // Copy old elements to the correct positions in new array.
        // (We can memcpy entire rows at once.)
        uint64_t copy_width = old_dim2 < new_dim2 ? old_dim2 : new_dim2;
        for (uint64_t i = old_dim1; i < old_dim1 && i < new_dim1; ++i) {
            memcpy((char*)p + i * new_dim2 * elt_size,
                   (char*)old_data + i * old_dim2 * elt_size,
                   copy_width * elt_size);
        }

        memcpy(array, &p, sizeof(void*));
        memcpy(array + sizeof(void*), &new_dim1, 8);
        memcpy(array + sizeof(void*) + 8, &new_dim2, 8);
    }
}

void resize_3d_array(uint64_t elt_size, char *array,
                     uint64_t new_dim1, uint64_t new_dim2, uint64_t new_dim3)
{
    // This is similar to resize_2d_array except that we use a simplified implementation
    // where the existing contents of the array are lost.

    void *old_data;
    uint64_t old_dim1, old_dim2, old_dim3;
    memcpy(&old_data, array, sizeof(void*));
    memcpy(&old_dim1, array + sizeof(void*), 8);
    memcpy(&old_dim2, array + sizeof(void*) + 8, 8);
    memcpy(&old_dim3, array + sizeof(void*) + 16, 8);

    free(old_data);

    if (new_dim1 != 0 && new_dim2 != 0 && new_dim3 != 0 && elt_size != 0) {
        void *new_data = calloc(new_dim1 * new_dim2 * new_dim3, elt_size);
        if (new_data == NULL) abort();
        memcpy(array, &new_data, sizeof(void*));
    } else {
        void *new_data = NULL;
        memcpy(array, &new_data, sizeof(void*));
    }

    memcpy(array + sizeof(void*), &new_dim1, 8);
    memcpy(array + sizeof(void*) + 8, &new_dim2, 8);
    memcpy(array + sizeof(void*) + 16, &new_dim3, 8);
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

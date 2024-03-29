// This implements the interface defined in ExampleLib.b.

#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Strings in the language are represented as a little struct containing
// the string data (which is NOT null-terminated) and the length, as
// follows:

struct String {
    char *data;
    uint64_t length;
};

void print_string(const struct String *string)
{
    printf("%s", string->data);
}

void print_i32(int32_t x)
{
    printf("%" PRIi32, x);
}

void print_u32(uint32_t x)
{
    printf("%" PRIu32, x);
}

void print_i64(int64_t x)
{
    printf("%" PRIi64, x);
}

void print_u64(uint64_t x)
{
    printf("%" PRIu64, x);
}


// Array resizing functions

struct Array1d {
    void *data;
    uint64_t dim;
};

struct Array2d {
    void *data;
    uint64_t dim1;
    uint64_t dim2;
};

void resize_array(uint64_t elt_size, struct Array1d *array, uint64_t new_dim)
{
    // Note: we assume size_t is 64-bit, and that reallocarray is available.

    // This will resize the array. Elements at positions less than both
    // new_dim and old_dim will be preserved. Elements above old_dim,
    // but below new_dim, will be zero-initialised.

    uint64_t old_dim = array->dim;
    bool freeing = (new_dim == 0 || elt_size == 0);

    if (freeing) {
        // To avoid confusion, let's explicitly call free, rather than realloc with a zero size
        free(array->data);
        array->data = NULL;
        array->dim = new_dim;

    } else {
        // Call reallocarray with non-zero size(s).
        void *p = reallocarray(array->data, new_dim, elt_size);

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

        array->data = p;
        array->dim = new_dim;
    }
}

void resize_2d_array(uint64_t elt_size, struct Array2d *array, uint64_t new_dim1, uint64_t new_dim2)
{
    // This is the 2d equivalent of resize_array.

    // We can't use realloc as we have to not only copy the existing
    // data, but "reformat" it (if dim2 has changed).

    // To keep things simple we will just calloc a new buffer, then copy the
    // old data to it (row by row), then free the old buffer.

    uint64_t old_dim1 = array->dim1;
    uint64_t old_dim2 = array->dim2;
    bool freeing = (new_dim1 == 0 || new_dim2 == 0 || elt_size == 0);

    if (freeing) {
        free(array->data);
        array->data = NULL;
        array->dim1 = new_dim1;
        array->dim2 = new_dim2;

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
                   (char*)array->data + i * old_dim2 * elt_size,
                   copy_width * elt_size);
        }

        array->data = p;
        array->dim1 = new_dim1;
        array->dim2 = new_dim2;
    }
}

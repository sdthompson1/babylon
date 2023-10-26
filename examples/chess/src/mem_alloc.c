// Memory allocation functions from MemAlloc.b.

#include "common_types.h"

#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

// note: polymorphic functions like alloc<T> accept the sizeof(T) as a
// hidden parameter.
bool resize_array(uint64_t elem_size,
                  void *mem,
                  struct Array1 *array,
                  uint64_t new_dim)
{
    // Note: we assume size_t is 64-bit, and that reallocarray is available.

    // This will resize the array. Elements at positions less than both
    // new_dim and old_dim will be preserved. Elements above old_dim,
    // but below new_dim, will be zero-initialised.

    uint64_t old_dim = array->num_elements;
    bool freeing = (new_dim == 0 || elem_size == 0);

    if (freeing) {
        // To avoid confusion, let's explicitly call free, rather than
        // realloc with a zero size.
        free(array->data);
        array->data = NULL;
        array->num_elements = new_dim;
        return true;

    } else {
        // Call reallocarray with non-zero size(s).
        void *p = reallocarray(array->data, new_dim, elem_size);

        if (p == NULL) {
            // Reallocation failed. Leave the array unchanged.
            return false;
        }

        // Success.
        // reallocarray will have preserved any existing array data, so
        // now we just have to zero out any new bytes (between old_dim and
        // new_dim).
        if (new_dim > old_dim) {
            memset((char*)p + old_dim * elem_size,
                   0,
                   (new_dim - old_dim) * elem_size);
        }

        array->data = p;
        array->num_elements = new_dim;
        return true;
    }
}

bool resize_2d_array(uint64_t elem_size,
                     void *mem,
                     struct Array2 *array,
                     uint64_t new_dim_0,
                     uint64_t new_dim_1)
{
    // This is the 2d equivalent of resize_array.

    // We can't use realloc as we have to not only copy the existing
    // data, but "reformat" it (if dim2 has changed).

    // To keep things simple we will just calloc a new buffer, then copy the
    // old data to it (row by row), then free the old buffer.

    uint64_t old_dim_0 = array->num_elements_0;
    uint64_t old_dim_1 = array->num_elements_1;
    bool freeing = (new_dim_0 == 0 || new_dim_1 == 0 || elem_size == 0);

    if (freeing) {
        free(array->data);
        array->data = NULL;
        array->num_elements_0 = new_dim_0;
        array->num_elements_1 = new_dim_1;
        return true;

    } else {
        // Note: multiplication of new_dim_0 and new_dim_1 should not overflow
        // because of the precondition in Test.b.
        // calloc will take care of the case where the multiplication by elem_size overflows.
        // calloc will also zero out any "new" bytes, as required.
        void *p = calloc(new_dim_0 * new_dim_1, elem_size);

        if (p == NULL) {
            return false;
        }

        // Copy old elements to the correct positions in new array.
        // (We can memcpy entire rows at once.)
        uint64_t copy_width = old_dim_1 < new_dim_1 ? old_dim_1 : new_dim_1;
        for (uint64_t i = old_dim_0; i < old_dim_0 && i < new_dim_0; ++i) {
            memcpy((char*)p + i * new_dim_1 * elem_size,
                   (char*)array->data + i * old_dim_1 * elem_size,
                   copy_width * elem_size);
        }

        array->data = p;
        array->num_elements_0 = new_dim_0;
        array->num_elements_1 = new_dim_1;
        return true;
    }
}

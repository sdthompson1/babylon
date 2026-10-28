#include "zlib.h"

#include <stdio.h>

int main()
{
    // Check that zlib was linked correctly, without printing its version
    // (which varies between systems). Per the zlib documentation, a
    // differing first character means the library is incompatible with
    // the header.
    if (zlibVersion()[0] == ZLIB_VERSION[0]) {
        printf("zlib version OK\n");
    } else {
        printf("zlib version mismatch\n");
    }
}

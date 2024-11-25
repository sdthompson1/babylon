#define STB_IMAGE_IMPLEMENTATION
#define STBI_ONLY_PNG
#define STBI_FAILURE_USERMSG
#include "stb_image.h"   // Obtained from https://github.com/nothings/stb/blob/master/stb_image.h

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void load_png(const char *filename,
              char *result)
{
    // filename points to {filename_data, filename_size}
    const char *filename_str;
    memcpy(&filename_str, filename, sizeof(char*));

    // Load the PNG file
    int width, height, depth;
    unsigned char *data = stbi_load(filename_str, &width, &height, &depth, 4);

    // Check for errors
    if (data == NULL) {
        // Build error message string
        uint64_t len = strlen(stbi_failure_reason()) + 1;
        char *str = malloc(len);
        if (str) {
            strcpy(str, stbi_failure_reason());
            // result points to {0, string, size} in error case
            result[0] = 0;
            memcpy(result + 1, &str, sizeof(char *));
            memcpy(result + 1 + sizeof(char *), &len, 8);
        }
        return;
    }

    // result points to {1, data, height, width} in success case
    uint64_t h = height;
    uint64_t w = width;
    result[0] = 1;
    memcpy(result + 1, &data, sizeof(char*));
    memcpy(result + 1 + sizeof(char*), &h, 8);
    memcpy(result + 9 + sizeof(char*), &w, 8);
}

#define STB_IMAGE_IMPLEMENTATION
#define STBI_ONLY_PNG
//#define STBI_FAILURE_USERMSG
#include "stb_image.h"   // Obtained from https://github.com/nothings/stb/blob/master/stb_image.h

#include "common_types.h"

#include <stdlib.h>
#include <string.h>

void load_png(void *io,
              const struct String *filename,
              struct Array2 *pixels,
              struct Result *result)
{
    int width, height, depth;
    unsigned char *data = stbi_load(filename->data, &width, &height, &depth, 4);

    if (data == NULL) {
        result->tag = RESULT_ERROR;
        result->error_string = make_string_3("stbi_load failed: ", stbi_failure_reason(), NULL);
        return;
    }

    result->tag = RESULT_OK;
    pixels->data = data;
    pixels->num_elements_0 = height;
    pixels->num_elements_1 = width;
}

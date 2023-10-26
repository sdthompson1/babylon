#include "common_types.h"

#include <stdlib.h>
#include <string.h>

struct String make_string(const char *string)
{
    return make_string_3(string, NULL, NULL);
}

struct String make_string_3(const char *string1, const char *string2, const char *string3)
{
    size_t len1 = string1 ? strlen(string1) : 0;
    size_t len2 = string2 ? strlen(string2) : 0;
    size_t len3 = string3 ? strlen(string3) : 0;

    size_t len = len1 + len2 + len3 + 1;

    struct String msg;
    msg.data = malloc(len);

    if (msg.data == NULL) {
        // in the unlikely event that we cannot allocate memory for the error
        // string, just set it to an empty string.
        msg.length = 0;

    } else {
        msg.length = len;
        if (string1) memcpy(msg.data, string1, len1);
        if (string2) memcpy(msg.data + len1, string2, len2);
        if (string3) memcpy(msg.data + len1 + len2, string3, len3);
        msg.data[len - 1] = 0;
    }

    return msg;
}

#include <sys/random.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

void get_random_seed(char *bytes)
{
    // Currently this is only implemented for Linux.

    // We first attempt to get some random bytes using getrandom(2).

    // We use GRND_NONBLOCK to prevent unbounded delays -- if there is not
    // enough entropy the call will just fail, rather than block for an
    // unknown length of time.

    // We do NOT use GRND_RANDOM, because we are not interested in
    // cryptography, and we want to maximise the chances that the call
    // will succeed.

    // If the call does fail, we fall back to time(2) which gives the
    // number of seconds since the Epoch.

    char *byte_buf;
    uint64_t num_bytes;
    memcpy(&byte_buf, bytes, sizeof(char*));
    memcpy(&num_bytes, bytes + sizeof(char*), 8);

    ssize_t i = getrandom(byte_buf, num_bytes, GRND_NONBLOCK);

    if (i < (ssize_t)num_bytes) {
        // If i < 0 this means the call failed completely. If 0 < i < num_bytes
        // this means that only i bytes were filled. We fill any remaining
        // bytes with the value of time(NULL), padding with zeroes if we
        // need more bytes than sizeof(time_t).
        if (i < 0) i = 0;
        uint64_t t = (uint64_t) time(NULL);

        while (i < num_bytes) {
            byte_buf[i] = (uint8_t) t;
            t >>= 8;
            i = i + 1u;
        }
    }
}

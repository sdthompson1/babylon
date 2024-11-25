#include <errno.h>
#include <stdint.h>
#include <time.h>

#define SEC_TO_NANO ((int64_t)1000000000)
#define MILLI_TO_NANO ((int64_t)1000000)

int64_t Timer_get_nanosecond_count()
{
    // Query the CLOCK_MONOTONIC.
    struct timespec ts;
    int error = clock_gettime(CLOCK_MONOTONIC, &ts);

    // Convert to int64_t. We assume that overflows will not occur here.
    return (int64_t)ts.tv_sec * SEC_TO_NANO + (int64_t)ts.tv_nsec;
}

void Timer_sleep_nanoseconds(int64_t ns)
{
    int64_t sec = ns / SEC_TO_NANO;
    int64_t nano = ns % SEC_TO_NANO;

    // There is an outside chance that we are on a (very old) system
    // with a (signed) 32-bit time_t, in which case, having sec above
    // INT32_MAX will not work. We will solve that simply by capping
    // sec at INT32_MAX. Since that corresponds to a sleep of over 60
    // years, this should not cause any serious problems!

    if (sec > INT32_MAX) {
        sec = INT32_MAX;
    }

    struct timespec ts;
    ts.tv_sec = sec;
    ts.tv_nsec = nano;

    while (nanosleep(&ts, &ts) == -1) {
        if (errno != EINTR) {
            // We just ignore errors as there is not much else we can do.
            return;
        }
        // If interrupted, nanosleep updates 'ts' with the remaining sleep time.
    }
}

void Timer_sleep_milliseconds(int64_t ms)
{
    // Our strategy here is to convert ms to ns and then use
    // Timer_sleep_nanoseconds.

    // If ms*1000 exceeds INT64_MAX, then that will not work, but
    // Timer_sleep_nanoseconds can't sleep that long anyway (see
    // above). We solve this simply by capping the computed ns value
    // at INT64_MAX if necessary.

    int64_t ns;
    if (ms >= INT64_MAX / MILLI_TO_NANO) {
        // ns capped out at INT64_MAX.
        ns = INT64_MAX;
    } else {
        // Convert ns to ms by multiplying by 1000.
        // (This does not overflow, thanks to the above check.)
        ns = ms * MILLI_TO_NANO;
    }
    Timer_sleep_nanoseconds(ns);
}

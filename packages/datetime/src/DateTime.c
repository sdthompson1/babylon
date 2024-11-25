// For now this is implemented for POSIX systems only. In particular
// we assume that clock_gettime and nanosleep are available.

#include <stdint.h>
#include <string.h>
#include <time.h>

#define DATETIME_SIZE 9

static void write_datetime(char *p,
                           int32_t year, int8_t month, int8_t day,
                           int8_t hour, int8_t minute, int8_t second)
{
    memcpy(p, &year, 4);
    memcpy(p + 4, &month, 1);
    memcpy(p + 5, &day, 1);
    memcpy(p + 6, &hour, 1);
    memcpy(p + 7, &minute, 1);
    memcpy(p + 8, &second, 1);
}

static void write_time_results(char *ret, const struct tm *tm, int32_t nsec)
{
    if (tm == NULL) {
        // There was an error getting the time. This shouldn't really happen, but
        // we handle it by passing an implausible date/time back to the caller.
        write_datetime(ret, 1900, 1, 1, 0, 0, 0);
        int32_t zero = 0;
        memcpy(ret + DATETIME_SIZE, &zero, 4);

    } else {
        // We successfully got the time. Pass it back to the caller.
        write_datetime(ret, tm->tm_year + 1900, tm->tm_mon + 1, tm->tm_mday,
                       tm->tm_hour, tm->tm_min, tm->tm_sec);
        memcpy(ret + DATETIME_SIZE, &nsec, 4);
    }
}

void DateTime_utc_time_now(char *ret)
{
    // Query the CLOCK_REALTIME.
    struct timespec ts;
    int error = clock_gettime(CLOCK_REALTIME, &ts);

    // If successful, convert to UTC ("gmtime"), else set time_result to NULL.
    struct tm tm;
    struct tm *time_result = error ? NULL : gmtime_r(&ts.tv_sec, &tm);

    // Write results back to caller.
    write_time_results(ret, time_result, ts.tv_nsec);
}

void DateTime_local_time_now(char *ret)
{
    // Query the CLOCK_REALTIME.
    struct timespec ts;
    int error = clock_gettime(CLOCK_REALTIME, &ts);

    // If successful, convert to local time, else set time_result to NULL.
    struct tm tm;
    struct tm *time_result = error ? NULL : localtime_r(&ts.tv_sec, &tm);

    // Write results back to the caller.
    write_time_results(ret, time_result, ts.tv_nsec);
}

module Timer

// Functions to access a "monotonic timer" and to sleep for
// a given amount of time.

interface {
    // Get a "monotonic" time, in nanoseconds from some arbitrary reference point.
    // (Returns an i64, so range is approx 290 years. The return value is
    // guaranteed to be positive.)
    extern impure function get_nanosecond_count(): i64 = "Timer_get_nanosecond_count";
        ensures return >= 0;

    // Some callers might prefer milliseconds instead of nanoseconds.
    impure function get_millisecond_count(): i64
        ensures return >= 0;
    {
        return get_nanosecond_count() / 1000000;
    }

    // Sleep for a given number of nanoseconds (or milliseconds).
    extern function sleep_nanoseconds(ns: i64) = "Timer_sleep_nanoseconds";
        requires ns >= 0;

    extern function sleep_milliseconds(ms: i64) = "Timer_sleep_milliseconds";
        requires ms >= 0;
}

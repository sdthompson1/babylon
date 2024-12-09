/*

A simple DateTime module.

This module implements an "idealized" calendar/clock where there are
exactly 86400 seconds in one day, the dates follow the Gregorian
calendar rules (both forwards and backwards indefinitely from the
present), and there are no time zones, DST changes, leap seconds, or
anything like that. We also assume that a year zero exists. (See also
https://en.wikipedia.org/wiki/Proleptic_Gregorian_calendar.)

Dates and times are represented by a record containing year/month/day/
hour/minute/second, but conversion to and from an "epoch seconds"
value (i.e. number of seconds since 00:00:00 1-Jan-1970 in the
idealized calendar) is also provided, as this may be useful for some
applications.

*/

module DateTime

import Int;
import IntDivision;
import IntSaturate;
import Ord;

interface {

    // Types.

    type DateTime = {
        year: i32,
        month: i8,
        day: i8,
        hour: i8,
        minute: i8,
        second: i8
    };


    // Constants.

    const DATE_TIME_MIN: DateTime = {year = I32_MIN, month = i8(1), day = i8(1),
                                     hour = i8(0), minute = i8(0), second = i8(0)};
                                     
    const DATE_TIME_MAX: DateTime = {year = I32_MAX, month = i8(12), day = i8(31),
                                     hour = i8(23), minute = i8(59), second = i8(59)};
    
    const EPOCH: DateTime = {year = 1970, month = i8(1), day = i8(1),
                             hour = i8(0), minute = i8(0), second = i8(0)};

    const EPOCH_WEEKDAY: i8 = 4;   // Thursday

    const EPOCH_SECOND_MIN: i64 = -67768100567971200;
    const EPOCH_SECOND_MAX: i64 =  67767976233532799;

    const SECONDS_PER_MINUTE: i32 = 60;
    const SECONDS_PER_HOUR: i32 = 60 * SECONDS_PER_MINUTE;
    const SECONDS_PER_DAY: i32 = 24 * SECONDS_PER_HOUR;
    const SECONDS_PER_WEEK: i32 = 7 * SECONDS_PER_DAY;


    // Constructor functions.
    
    function ymd(y: i32, m: i8, d: i8): DateTime
    {
        return { year = y, month = m, day = d, hour = i8(0), minute = i8(0), second = i8(0) };
    }
    
    function ymdhms(y: i32, m: i8, d: i8, hr: i8, min: i8, sec: i8): DateTime
    {
        return { year = y, month = m, day = d, hour = hr, minute = min, second = sec };
    }


    // Leap year and last-day-of-month calculations.

    function is_leap_year(year: i32): bool
    {
        return year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
    }

    function last_day_of_month_common_year(month: i8): i8
        requires 1 <= month <= 12;
        ensures 28 <= return <= 31;
    {
        if month == 2 {
            return 28;
        } else if month == 9 || month == 4 || month == 6 || month == 11 {
            return 30;
        } else {
            return 31;
        }
    }

    function last_day_of_month_leap_year(month: i8): i8
        requires 1 <= month <= 12;
        ensures 29 <= return <= 31;
    {
        if month == 2 {
            return 29;
        } else {
            return last_day_of_month_common_year(month);
        }
    }

    function last_day_of_month(year: i32, month: i8): i8
        requires 1 <= month <= 12;
        ensures 28 <= return <= 31;
    {
        if is_leap_year(year) {
            return last_day_of_month_leap_year(month);
        } else {
            return last_day_of_month_common_year(month);
        }
    }


    // Validity function.

    function valid_date_time(dt: DateTime): bool
    {
        // (Any i32 year is allowed)
        return 1 <= dt.month <= 12
            && 1 <= dt.day <= last_day_of_month(dt.year, dt.month)
            && 0 <= dt.hour <= 23
            && 0 <= dt.minute <= 59
            && 0 <= dt.second <= 59;
    }


    // Conversion to/from epoch seconds
    // (i.e. the number of seconds since 00:00:00 on 1-Jan-1970).

    function date_time_to_epoch_second(dt: DateTime): i64
        requires valid_date_time(dt);
        ensures EPOCH_SECOND_MIN <= return <= EPOCH_SECOND_MAX;
        ensures dt == DATE_TIME_MIN ==> return == EPOCH_SECOND_MIN;
        ensures dt == DATE_TIME_MAX ==> return == EPOCH_SECOND_MAX;
        ensures dt == EPOCH ==> return == 0;

    function epoch_second_to_date_time(s: i64): DateTime
        requires EPOCH_SECOND_MIN <= s <= EPOCH_SECOND_MAX;
        ensures valid_date_time(return);
        ensures s == EPOCH_SECOND_MIN ==> return == DATE_TIME_MIN;
        ensures s == EPOCH_SECOND_MAX ==> return == DATE_TIME_MAX;
        ensures s == 0 ==> return == EPOCH;

    // Lemma: the above functions are inverses
    ghost function date_time_to_epoch_second_and_back(dt: DateTime)
        requires valid_date_time(dt);
        ensures epoch_second_to_date_time(date_time_to_epoch_second(dt)) == dt;
        
    ghost function epoch_second_to_date_time_and_back(s: i64)
        requires EPOCH_SECOND_MIN <= s <= EPOCH_SECOND_MAX;
        ensures date_time_to_epoch_second(epoch_second_to_date_time(s)) == s;


    // Adding seconds, hours, minutes, days or weeks to a DateTime.

    // If the result overflows, these will return the min or max allowed DateTime
    // (but this is unlikely to happen except with crazy inputs).

    ghost function clamp_epoch_second(s: int): int
    {
        return int_clamp(s, int(EPOCH_SECOND_MIN), int(EPOCH_SECOND_MAX));
    }

    function add_seconds(dt: DateTime, secs: i64): DateTime
        requires valid_date_time(dt);
        ensures valid_date_time(return);
        ensures int(date_time_to_epoch_second(return)) ==
            clamp_epoch_second(int(date_time_to_epoch_second(dt)) + int(secs));

    function add_minutes(dt: DateTime, mins: i32): DateTime
        requires valid_date_time(dt);
        ensures valid_date_time(return);
        ensures int(date_time_to_epoch_second(return)) ==
            clamp_epoch_second(int(date_time_to_epoch_second(dt))
                + int(mins) * int(SECONDS_PER_MINUTE));

    function add_hours(dt: DateTime, hrs: i32): DateTime
        requires valid_date_time(dt);
        ensures valid_date_time(return);
        ensures int(date_time_to_epoch_second(return)) ==
            clamp_epoch_second(int(date_time_to_epoch_second(dt))
                + int(hrs) * int(SECONDS_PER_HOUR));

    function add_days(dt: DateTime, days: i32): DateTime
        requires valid_date_time(dt);
        ensures valid_date_time(return);
        ensures int(date_time_to_epoch_second(return)) ==
            clamp_epoch_second(int(date_time_to_epoch_second(dt))
                + int(days) * int(SECONDS_PER_DAY));

    function add_weeks(dt: DateTime, weeks: i32): DateTime
        requires valid_date_time(dt);
        ensures valid_date_time(return);
        ensures int(date_time_to_epoch_second(return)) ==
            clamp_epoch_second(int(date_time_to_epoch_second(dt))
                + int(weeks) * int(SECONDS_PER_WEEK));


    // Adding months or years to a DateTime.

    // This works in calendar months or years, e.g. adding one month to
    // 1-Jan-2024 yields 1-Feb-2024.

    // If the addition results in a date that does not exist, then the last
    // day of the month is substituted instead, e.g. adding one month to
    // 31-Jan-2024 yields 29-Feb-2024, and adding one year to 29-Feb-2024
    // yields 28-Feb-2025.

    // First let's write some specifications.

    function clamp_to_last_day_of_month(dt: DateTime): DateTime
        requires 1 <= dt.month <= 12;
        requires 1 <= dt.day;
        requires 0 <= dt.hour <= 23;
        requires 0 <= dt.minute <= 59;
        requires 0 <= dt.second <= 59;
        ensures valid_date_time(return);
    {
        return { dt with day = i64_min(last_day_of_month(dt.year, dt.month), dt.day) };
    }

    ghost function add_years_spec(dt: DateTime, years: i32): DateTime
        requires 1 <= dt.month <= 12;
        requires 1 <= dt.day;
        requires 0 <= dt.hour <= 23;
        requires 0 <= dt.minute <= 59;
        requires 0 <= dt.second <= 59;
        ensures valid_date_time(return);
    {
        return clamp_to_last_day_of_month{ dt with year = i32_sat_add(dt.year, years) };
    }

    ghost function add_months_spec(dt: DateTime, months: i32): DateTime
        requires valid_date_time(dt);
        ensures valid_date_time(return);
    {
        var new_month_raw: int = int(dt.month) + int(months);

        // Bring new_month_raw back into the 1-12 range, and work out how
        // many years must be added to compensate.
        var d = int_floor_div(new_month_raw - int(1), int(12));
        var year_adjust: int = d.quot;
        var new_month: int = d.rem + int(1);

        // Use add_years_spec to add the years, and correct the day if necessary.
        return add_years_spec({dt with month = i8(new_month)}, i32(year_adjust));
    }

    // Now for the actual functions:

    function add_months(dt: DateTime, months: i32): DateTime
        requires valid_date_time(dt);
        ensures valid_date_time(return);
        ensures return == add_months_spec(dt, months);

    function add_years(dt: DateTime, years: i32): DateTime
        requires valid_date_time(dt);
        ensures valid_date_time(return);
        ensures return == add_years_spec(dt, years);


    // Calculate the number of seconds between two DateTimes.

    function date_time_diff_seconds(lhs: DateTime, rhs: DateTime): i64
        requires valid_date_time(lhs);
        requires valid_date_time(rhs);
    {
        return date_time_to_epoch_second(lhs) - date_time_to_epoch_second(rhs);
    }


    // Comparisons.

    function date_time_equal(lhs: DateTime, rhs: DateTime): bool
        requires valid_date_time(lhs);
        requires valid_date_time(rhs);
        ensures return <==> lhs == rhs;

    function date_time_compare(lhs: DateTime, rhs: DateTime): Ordering
        requires valid_date_time(lhs);
        requires valid_date_time(rhs);
    {
        if lhs.year < rhs.year { return LT; }
        if lhs.year > rhs.year { return GT; }
        if lhs.month < rhs.month { return LT; }
        if lhs.month > rhs.month { return GT; }
        if lhs.day < rhs.day { return LT; }
        if lhs.day > rhs.day { return GT; }
        if lhs.hour < rhs.hour { return LT; }
        if lhs.hour > rhs.hour { return GT; }
        if lhs.minute < rhs.minute { return LT; }
        if lhs.minute > rhs.minute { return GT; }
        if lhs.second < rhs.second { return LT; }
        if lhs.second > rhs.second { return GT; }
        return EQ;
    }

    // Lemma: date_time_compare agrees with the epoch second order.
    ghost function date_time_compare_agrees(lhs: DateTime, rhs: DateTime)
        requires valid_date_time(lhs);
        requires valid_date_time(rhs);
        ensures date_time_compare(lhs, rhs) == LT <==>
            date_time_to_epoch_second(lhs) < date_time_to_epoch_second(rhs);
        ensures date_time_compare(lhs, rhs) == GT <==>
            date_time_to_epoch_second(lhs) > date_time_to_epoch_second(rhs);
        ensures date_time_compare(lhs, rhs) == EQ <==> lhs == rhs;


    // Get the day-of-the-week for a given DateTime.

    // This returns a number between 0 and 6 where 0 is Sunday and 6 is Saturday.

    function day_of_week(dt: DateTime): i8
        requires valid_date_time(dt);
        ensures 0 <= return <= 6;
        ensures int(return) ==
            int_mod(int_floor_div(int(date_time_to_epoch_second(dt)),
                                  int(SECONDS_PER_DAY)).quot
                        + int(EPOCH_WEEKDAY),
                    int(7));

    // Lemma: Adding N days to a date causes the weekday to increase by N (mod 7).
    // (This is assuming the result of the addition did not clip to DATE_TIME_MIN
    // or DATE_TIME_MAX.)
    ghost function day_of_week_add_days(dt: DateTime, days: i32)
        requires valid_date_time(dt);
        requires add_days(dt, days) != DATE_TIME_MIN;
        requires add_days(dt, days) != DATE_TIME_MAX;
        ensures day_of_week(add_days(dt, days)) == i64_mod(day_of_week(dt) + i64(days), 7);


    // Interacting with the system clock.

    // Get the current UTC time. Returns DateTime plus nanoseconds.
    extern impure function utc_time_now(): {DateTime, i32} = "DateTime_utc_time_now";
        ensures valid_date_time(return.0);
        ensures 0 <= return.1 <= 999999999;

    // Get the current time in the local timezone. Returns DateTime plus nanoseconds.
    extern impure function local_time_now(): {DateTime, i32} = "DateTime_local_time_now";
        ensures valid_date_time(return.0);
        ensures 0 <= return.1 <= 999999999;

}


// We start by defining functions that can convert a date (year/month/day)
// to and from an "Epoch day number". These will be needed later for the
// date_time_to_epoch_second and epoch_second_to_date_time functions.

// For more info on the algorithm used, see:
// https://howardhinnant.github.io/date_algorithms.html.

ghost function ymd_only(y: i32, m: i8, d: i8): {year: i32, month: i8, day: i8}
{
    return { year = y, month = m, day = d };
}

const EPOCH_DAY_MIN: i64 = -784353015833;
const EPOCH_DAY_MAX: i64 = 784351576776;

function date_to_epoch_day(date: {year: i32, month: i8, day: i8}): i64
    requires 1 <= date.month <= 12;
    requires 1 <= date.day <= last_day_of_month(date.year, date.month);
    ensures EPOCH_DAY_MIN <= return <= EPOCH_DAY_MAX;
{
    var y: i64 = date.year;
    var m: i64 = date.month;
    var d: i64 = date.day;

    if m <= 2 {
        m = m + 9;
        y = y - 1;
    } else {
        m = m - 3;
    }

    var era = (if y >= 0 then y else y-399) / 400;

    var yoe = (y - era*400);
    assert 0 <= yoe <= 399;

    var doy = (153*m + 2) / 5 + d - 1;
    assert 0 <= doy <= 365;

    var doe = yoe*365 + yoe/4 - yoe/100 + doy;
    assert 0 <= doe <= 146096;

    return era*146097 + doe - 719468;
}

function epoch_day_to_date(epoch_day: i64): {year: i32, month: i8, day: i8}
    requires EPOCH_DAY_MIN <= epoch_day <= EPOCH_DAY_MAX;
    ensures 1 <= return.month <= 12;
    ensures 1 <= return.day <= last_day_of_month(return.year, return.month);
{
    var z = epoch_day + 719468;

    var era = (if z >= 0 then z else z - 146096) / 146097;

    var doe = z - era*146097;
    assert 0 <= doe <= 146096;

    var yoe = (doe - doe/1460 + doe/36524 - doe/146096) / 365;
    assert 0 <= yoe <= 399;

    var y = yoe + era*400;
    
    var doy = doe - (365*yoe + yoe/4 - yoe/100);
    assert 0 <= doy <= 365;

    var mp = (5*doy + 2) / 153;
    assert 0 <= mp <= 11;

    var d = doy - (153*mp + 2)/5 + 1;
    assert 1 <= d <= 31;

    var m = if mp < 10 then mp+3 else mp-9;
    assert 1 <= m <= 12;

    if m <= 2 {
        y = y + 1;
    }

    return {year=i32(y), month=i8(m), day=i8(d)};
}

// Test cases:
ghost function date_to_epoch_day_test_cases()
    ensures date_to_epoch_day(ymd_only(2024, 11, 12)) == 20039;
    ensures date_to_epoch_day(ymd_only(-100, 2, 10)) == -756012;
    ensures date_to_epoch_day(ymd_only(I32_MIN, 1, 1)) == EPOCH_DAY_MIN;
    ensures date_to_epoch_day(ymd_only(I32_MAX, 12, 31)) == EPOCH_DAY_MAX;
    ensures date_to_epoch_day(ymd_only(1970, 1, 1)) == 0;
{}

ghost function epoch_day_to_date_test_cases()
    ensures epoch_day_to_date(20039)         == ymd_only(2024, 11, 12);
    ensures epoch_day_to_date(-756012)       == ymd_only(-100, 2, 10);
    ensures epoch_day_to_date(EPOCH_DAY_MIN) == ymd_only(I32_MIN, 1, 1);
    ensures epoch_day_to_date(EPOCH_DAY_MAX) == ymd_only(I32_MAX, 12, 31);
    ensures epoch_day_to_date(0)             == ymd_only(1970, 1, 1);
{}

// Theorem: The two epoch_day functions are inverses of each other:
ghost function date_to_epoch_day_and_back(date: {year: i32, month: i8, day: i8})
    requires 1 <= date.month <= 12;
    requires 1 <= date.day <= last_day_of_month(date.year, date.month);
    ensures epoch_day_to_date(date_to_epoch_day(date)) == date;
{
    var y: i64 = date.year;
    var m: i64 = date.month;
    var d: i64 = date.day;
    
    if m <= 2 {
        y = y - 1;
    }

    var era = (if y >= 0 then y else y-399) / 400;
    var yoe = y - era*400;
    var doy = (153 * (if m <= 2 then m+9 else m-3) + 2) / 5 + d - 1;
    var doe = yoe * 365 + yoe/4 - yoe/100 + doy;
    
    var z = i64(era) * 146097 + doe;
    assert z == date_to_epoch_day(date) + 719468;

    var era2 = (if z >= 0 then z else z - 146096) / 146097;
    assert era2 == era;

    var doe2 = z - era2 * 146097;
    assert doe2 == doe;

    var yoe2 = (doe2 - doe2/1460 + doe2/36524 - doe2/146096) / 365;
    assert yoe2 == yoe;

    var y2 = yoe + era*400;
    assert y2 == y;

    var doy2 = doe2 - (365*yoe2 + yoe2/4 - yoe2/100);
    assert doy2 == doy;

    var mp2 = (5*doy2 + 2) / 153;
    var d2 = doy - (153*mp2 + 2)/5 + 1;
    assert d2 == d;

    var m2 = if mp2 < 10 then mp2 + 3 else mp2 - 9;
    assert m2 == m;

    var result = {year = i32(if m2 <= 2 then y2+1 else y2), month = i8(m2), day = i8(d2)};
    assert result == epoch_day_to_date(date_to_epoch_day(date));
}

ghost function epoch_day_to_date_and_back(epoch_day: i64)
    requires EPOCH_DAY_MIN <= epoch_day <= EPOCH_DAY_MAX;
    ensures date_to_epoch_day(epoch_day_to_date(epoch_day)) == epoch_day;
{
    var z = epoch_day + 719468;
    var era = (if z >= 0 then z else z - 146096) / 146097;
    var doe = z - era*146097;
    var yoe = (doe - doe/1460 + doe/36524 - doe/146096) / 365;
    var y = yoe + era*400;
    var doy = doe - (365*yoe + yoe/4 - yoe/100);
    var mp = (5*doy + 2) / 153;
    var d = doy - (153*mp + 2)/5 + 1;
    var m = if mp < 10 then mp+3 else mp-9;
    if m <= 2 {
        y = y + 1;
    }
    
    var date = {year = i32(y), month = i8(m), day = i8(d)};
    assert date == epoch_day_to_date(epoch_day);

    var y2 = if m <= 2 then y - 1 else y;
    var era2 = (if y2 >= 0 then y2 else y2-399) / 400;
    assert era2 == era;
    var yoe2 = y2 - era*400;
    assert yoe2 == yoe;
    var doy2 = (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + d - 1;
    assert doy2 == doy;
    var doe2 = yoe2 * 365 + yoe2/4 - yoe2/100 + doy2;
    assert doe2 == doe;
}


// Given the above, we can easily write the date_time_to_epoch_second and
// epoch_second_to_date_time functions.

function date_time_to_epoch_second(dt: DateTime): i64
    requires valid_date_time(dt);
    ensures EPOCH_SECOND_MIN <= return <= EPOCH_SECOND_MAX;
    ensures dt == DATE_TIME_MIN ==> return == EPOCH_SECOND_MIN;
    ensures dt == DATE_TIME_MAX ==> return == EPOCH_SECOND_MAX;
    ensures dt == EPOCH ==> return == 0;
{
    return i64(SECONDS_PER_DAY) * date_to_epoch_day{year = dt.year, month = dt.month, day = dt.day}
        + i64(SECONDS_PER_HOUR) * dt.hour
        + i64(SECONDS_PER_MINUTE) * dt.minute
        + dt.second;
}

function epoch_second_to_date_time(s: i64): DateTime
    requires EPOCH_SECOND_MIN <= s <= EPOCH_SECOND_MAX;
    ensures valid_date_time(return);
    ensures s == EPOCH_SECOND_MIN ==> return == DATE_TIME_MIN;
    ensures s == EPOCH_SECOND_MAX ==> return == DATE_TIME_MAX;
    ensures s == 0 ==> return == EPOCH;    
{
    var epoch_day: i64 = (if s >= 0 then s else s - 86399) / 86400;
    var date: {year: i32, month: i8, day: i8} = epoch_day_to_date(epoch_day);

    var second_of_day = s - epoch_day * 86400;
    assert 0 <= second_of_day <= 86399;

    var hour_of_day = second_of_day / 3600;
    assert 0 <= hour_of_day <= 23;
    
    var second_of_hour = second_of_day % 3600;
    assert 0 <= second_of_hour <= 3599;
    
    var minute_of_hour   = second_of_hour / 60;
    assert 0 <= minute_of_hour <= 59;
    
    var second_of_minute = second_of_hour % 60;
    assert 0 <= second_of_minute <= 59;

    return {year = date.year, month = date.month, day = date.day,
            hour = i8(hour_of_day), minute = i8(minute_of_hour),
            second = i8(second_of_minute)};
}

// Test cases:
ghost function date_time_to_epoch_second_testcases()
    ensures date_time_to_epoch_second(ymdhms(2024, 11, 12, 10, 33, 4)) == 1731407584;
    ensures date_time_to_epoch_second(ymdhms(-100, 2, 10, 20, 30, 40)) == -65319362960;
{}

ghost function epoch_second_to_date_time_testcases()
    ensures epoch_second_to_date_time(1731407584) == ymdhms(2024, 11, 12, 10, 33, 4);
    ensures epoch_second_to_date_time(-65319362960) == ymdhms(-100, 2, 10, 20, 30, 40);
{}

// Inverse theorems:
ghost function date_time_to_epoch_second_and_back(dt: DateTime)
    requires valid_date_time(dt);
    ensures epoch_second_to_date_time(date_time_to_epoch_second(dt)) == dt;
{
    hide date_to_epoch_day;
    hide epoch_day_to_date;
    date_to_epoch_day_and_back{year = dt.year, month = dt.month, day = dt.day};
}

ghost function epoch_second_to_date_time_and_back(s: i64)
    requires EPOCH_SECOND_MIN <= s <= EPOCH_SECOND_MAX;
    ensures date_time_to_epoch_second(epoch_second_to_date_time(s)) == s;
{
    hide date_to_epoch_day;
    hide epoch_day_to_date;
    epoch_day_to_date_and_back((if s >= 0 then s else s - 86399) / 86400);
}



// Adding seconds, minutes, etc. to a DateTime.

function add_seconds(dt: DateTime, secs: i64): DateTime
    requires valid_date_time(dt);
    ensures valid_date_time(return);
    ensures int(date_time_to_epoch_second(return)) ==
        int_clamp(int(date_time_to_epoch_second(dt)) + int(secs),
                  int(EPOCH_SECOND_MIN),
                  int(EPOCH_SECOND_MAX));
{
    var z = date_time_to_epoch_second(dt);

    // If secs >= 0 and z + secs > EPOCH_SECOND_MAX, clamp at DATE_TIME_MAX
    if secs >= 0 && z > EPOCH_SECOND_MAX - secs {
        return DATE_TIME_MAX;

    // Else if secs < 0 and z + secs < EPOCH_SECOND_MIN, clamp at DATE_TIME_MIN
    } else if secs < 0 && z < EPOCH_SECOND_MIN - secs {
        return DATE_TIME_MIN;

    // Else do full calculation
    } else {
        ghost epoch_second_to_date_time_and_back(z + secs);
        return epoch_second_to_date_time(z + secs);
    }
}

function add_minutes(dt: DateTime, mins: i32): DateTime
    requires valid_date_time(dt);
    ensures valid_date_time(return);
    ensures int(date_time_to_epoch_second(return)) ==
        clamp_epoch_second(int(date_time_to_epoch_second(dt)) + int(mins) * int(SECONDS_PER_MINUTE));
{
    return add_seconds(dt, i64(mins) * SECONDS_PER_MINUTE);
}

function add_hours(dt: DateTime, hrs: i32): DateTime
    requires valid_date_time(dt);
    ensures valid_date_time(return);
    ensures int(date_time_to_epoch_second(return)) ==
        clamp_epoch_second(int(date_time_to_epoch_second(dt)) + int(hrs) * int(SECONDS_PER_HOUR));
{
    return add_seconds(dt, i64(hrs) * SECONDS_PER_HOUR);
}

function add_days(dt: DateTime, days: i32): DateTime
    requires valid_date_time(dt);
    ensures valid_date_time(return);
    ensures int(date_time_to_epoch_second(return)) ==
        clamp_epoch_second(int(date_time_to_epoch_second(dt)) + int(days) * int(SECONDS_PER_DAY));
{
    return add_seconds(dt, i64(days) * SECONDS_PER_DAY);
}

function add_weeks(dt: DateTime, weeks: i32): DateTime
    requires valid_date_time(dt);
    ensures valid_date_time(return);
    ensures int(date_time_to_epoch_second(return)) ==
        clamp_epoch_second(int(date_time_to_epoch_second(dt)) + int(weeks) * int(SECONDS_PER_WEEK));
{
    return add_seconds(dt, i64(weeks) * SECONDS_PER_WEEK);
}


// Adding years and months to a DateTime.

function add_months(dt: DateTime, months: i32): DateTime
    requires valid_date_time(dt);
    ensures valid_date_time(return);
    ensures return == add_months_spec(dt, months);
{
    var new_month_raw: i64 = i64(dt.month) + months;
    var d = i64_floor_div(new_month_raw - 1, 12);
    var year_adjust: i64 = d.quot;
    var new_month: i8 = d.rem + 1;
    return clamp_to_last_day_of_month{dt with year = i32_sat_add(dt.year, year_adjust),
        month = new_month};
}

function add_years(dt: DateTime, years: i32): DateTime
    requires valid_date_time(dt);
    ensures valid_date_time(return);
    ensures return == add_years_spec(dt, years);
{
    var new_year = i32_sat_add(dt.year, years);
    if dt.month == 2 && dt.day == 29 && !is_leap_year(new_year) {
        return { dt with year = new_year, day = 28 };
    } else {
        return { dt with year = new_year };
    }
}

// Some quick test cases for add_months and add_years:
ghost function add_months_test_cases()
    ensures add_months(ymd(2000, 1, 1), 3) == ymd(2000, 4, 1);
    ensures add_months(ymd(2000, 1, 31), 3) == ymd(2000, 4, 30);
    ensures add_months(ymdhms(2023, 12, 30, 12, 34, 56), 2) == ymdhms(2024, 2, 29, 12, 34, 56);
    ensures add_months(ymdhms(2024, 12, 30,  1,  2,  3), 2) == ymdhms(2025, 2, 28,  1,  2,  3);
{}

ghost function add_years_test_cases()
    ensures add_years(ymd(2000, 8, 16), 99) == ymd(2099, 8, 16);
    ensures add_years(ymd(1992, 2, 29), 4) == ymd(1996, 2, 29);
    ensures add_years(ymd(1992, 2, 29), 5) == ymd(1997, 2, 28);
    ensures add_years(ymdhms(2020, 2, 28, 1, 2, 3), 10) == ymdhms(2030, 2, 28, 1, 2, 3);
{}



// Some properties of date_time_diff_seconds:

// Subtracting two DateTimes, then adding the result back on to the first DateTime,
// should produce the second DateTime.
ghost function diff_and_add_again(lhs: DateTime, rhs: DateTime)
    requires valid_date_time(lhs);
    requires valid_date_time(rhs);
    ensures add_seconds(lhs, date_time_diff_seconds(rhs, lhs)) == rhs;
{
    var x = date_time_to_epoch_second(lhs);
    var y = date_time_to_epoch_second(rhs);
    var d = date_time_diff_seconds(rhs, lhs);
    assert d == y - x;
    var result = add_seconds(lhs, d);
    date_time_to_epoch_second_and_back(result);
    date_time_to_epoch_second_and_back(rhs);
}

// If the dates are equal, then the difference can be computed by looking at
// the times only.
ghost function diff_same_date(lhs: DateTime, rhs: DateTime)
    requires valid_date_time(lhs);
    requires valid_date_time(rhs);
    requires lhs.year == rhs.year;
    requires lhs.month == rhs.month;
    requires lhs.day == rhs.day;
    ensures date_time_diff_seconds(lhs, rhs) ==
        SECONDS_PER_HOUR * i64(lhs.hour - rhs.hour)
        + SECONDS_PER_MINUTE * i64(lhs.minute - rhs.minute)
        + i64(lhs.second - rhs.second);
{}

// Some quick test cases for date_time_diff_seconds:
ghost function diff_seconds_test_cases()
    ensures date_time_diff_seconds(ymd(2024, 11, 14), ymd(2024, 12, 25)) == -41 * SECONDS_PER_DAY;
    ensures date_time_diff_seconds(ymdhms(1999, 4, 1, 10, 11, 33),
                                   ymdhms(1999, 3, 31, 9, 9, 22)) == 90131;
{}



// Comparisons.

function date_time_equal(lhs: DateTime, rhs: DateTime): bool
    requires valid_date_time(lhs);
    requires valid_date_time(rhs);
    ensures return <==> lhs == rhs;
{
    return lhs.year == rhs.year
        && lhs.month == rhs.month
        && lhs.day == rhs.day
        && lhs.hour == rhs.hour
        && lhs.minute == rhs.minute
        && lhs.second == rhs.second;
}

ghost function date_time_compare_agrees(lhs: DateTime, rhs: DateTime)
    requires valid_date_time(lhs);
    requires valid_date_time(rhs);
    ensures date_time_compare(lhs, rhs) == LT <==>
        date_time_to_epoch_second(lhs) < date_time_to_epoch_second(rhs);
    ensures date_time_compare(lhs, rhs) == GT <==>
        date_time_to_epoch_second(lhs) > date_time_to_epoch_second(rhs);
    ensures date_time_compare(lhs, rhs) == EQ <==> lhs == rhs;
{}

// Some test cases for date_time_equal and date_time_compare:
ghost function date_time_comparison_tests()
    ensures date_time_equal(ymdhms(1, 2, 3, 4, 5, 6), ymdhms(1, 2, 3, 4, 5, 6));
    ensures date_time_compare(ymdhms(1, 2, 3, 4, 5, 6), ymdhms(1, 2, 3, 4, 5, 6)) == EQ;
    ensures date_time_compare(ymd(2024, 1, 1), ymd(2025, 1, 1)) == LT;
    ensures date_time_compare(ymd(2025, 1, 1), ymd(2024, 1, 1)) == GT;
    ensures date_time_compare(ymd(2024, 2, 15), ymd(2024, 3, 1)) == LT;
    ensures date_time_compare(ymd(2024, 3, 1), ymd(2024, 2, 15)) == GT;
    ensures date_time_compare(ymdhms(2024, 1, 1, 20, 15, 0), ymdhms(2024, 1, 1, 21, 8, 39)) == LT;
    ensures date_time_compare(ymdhms(2024, 1, 1, 21, 8, 39), ymdhms(2024, 1, 1, 20, 15, 0)) == GT;
{}



// Day of week function.

function day_of_week(dt: DateTime): i8
    requires valid_date_time(dt);
    ensures 0 <= return <= 6;
    ensures int(return) ==
        int_mod(int_floor_div(int(date_time_to_epoch_second(dt)),
                              int(SECONDS_PER_DAY)).quot
                    + int(EPOCH_WEEKDAY),
                int(7));
{
    var s: i64 = date_to_epoch_day{year = dt.year, month = dt.month, day = dt.day};
    return i64_mod(s + EPOCH_WEEKDAY, 7);
}

// Test cases.
ghost function day_of_week_tests()
    ensures day_of_week(ymd(2024, 11, 13)) == 3;
    ensures day_of_week(ymdhms(1969, 7, 20, 20, 17, 40)) == 0;
{}


// Day of week addition property.

ghost function day_of_week_add_days(dt: DateTime, days: i32)
    requires valid_date_time(dt);
    requires add_days(dt, days) != DATE_TIME_MIN;
    requires add_days(dt, days) != DATE_TIME_MAX;
    ensures day_of_week(add_days(dt, days)) == i64_mod(day_of_week(dt) + i64(days), 7);
{
    hide date_to_epoch_day;

    var d = int(date_to_epoch_day{year=dt.year, month=dt.month, day=dt.day});
    assert d == int_floor_div(int(date_time_to_epoch_second(dt)), int(SECONDS_PER_DAY)).quot;

    var add = add_days(dt, days);
    var a = int(date_to_epoch_day{year=add.year, month=add.month, day = add.day});
    assert a == d + int(days);  // this relies on the preconditions (i.e. 'add' was not clamped at DATE_TIME_MIN or DATE_TIME_MAX)

    var w = int(EPOCH_WEEKDAY);
    assert int(day_of_week(dt)) == int_mod(d + w, int(7));
    assert int(day_of_week(add_days(dt, days))) == int_mod(d + int(days) + w, int(7));

    mod_add(d + w, int(days), int(7));
}

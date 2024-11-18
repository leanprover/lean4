// Lean compiler output
// Module: Std.Time.Zoned.DateTime
// Imports: Std.Time.DateTime Std.Time.Zoned.TimeZone Std.Internal
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday(lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object*);
lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__5(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_addWeeks___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_withMilliseconds___closed__2;
static lean_object* l_Std_Time_instInhabitedDateTime___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_addMinutes___closed__1;
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_instInhabitedDateTime___lambda__1___closed__2;
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___rarg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instBEqDateTime___rarg(lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__1(lean_object*);
lean_object* l_Std_Time_PlainTime_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object*);
static lean_object* l_Std_Time_DateTime_withMilliseconds___closed__1;
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__6(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___rarg(lean_object*);
static lean_object* l_Std_Time_DateTime_addHours___closed__1;
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_addYearsRollOver___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__3(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___rarg(lean_object*);
lean_object* l_Std_Time_PlainTime_addMilliseconds(lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___rarg___boxed(lean_object*);
static lean_object* l_Std_Time_instInhabitedDateTime___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object*);
static lean_object* l_Std_Time_DateTime_addMilliseconds___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__3(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
static lean_object* l_Std_Time_instInhabitedDateTime___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Std_Time_DateTime_Timestamp_0__Std_Time_beqTimestamp____x40_Std_Time_DateTime_Timestamp___hyg_56_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___rarg___boxed(lean_object*);
lean_object* l_Std_Time_PlainTime_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___rarg___boxed(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
static lean_object* l_Std_Time_instInhabitedDateTime___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___rarg(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_instInhabitedDateTime___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___rarg___boxed(lean_object*);
static lean_object* l_Std_Time_instInhabitedDateTime___closed__2;
static lean_object* l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instBEqDateTime___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Std_Time_DateTime_Timestamp_0__Std_Time_beqTimestamp____x40_Std_Time_DateTime_Timestamp___hyg_56_(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_instBEqDateTime___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_instBEqDateTime___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instBEqDateTime(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(30u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(23u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(59u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_4 = l_Std_Time_instInhabitedDateTime___lambda__1___closed__1;
x_5 = lean_int_add(x_1, x_4);
x_6 = lean_int_sub(x_5, x_1);
lean_dec(x_5);
x_7 = lean_int_add(x_6, x_1);
lean_dec(x_6);
x_8 = lean_int_sub(x_1, x_1);
x_9 = lean_int_emod(x_8, x_7);
x_10 = lean_int_add(x_9, x_7);
lean_dec(x_9);
x_11 = lean_int_emod(x_10, x_7);
lean_dec(x_7);
lean_dec(x_10);
x_12 = lean_int_add(x_11, x_1);
lean_dec(x_11);
x_13 = l_Std_Time_instInhabitedDateTime___lambda__1___closed__2;
x_14 = lean_int_add(x_1, x_13);
x_15 = lean_int_sub(x_14, x_1);
lean_dec(x_14);
x_16 = lean_int_add(x_15, x_1);
lean_dec(x_15);
x_17 = lean_int_emod(x_8, x_16);
lean_dec(x_8);
x_18 = lean_int_add(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_emod(x_18, x_16);
lean_dec(x_16);
lean_dec(x_18);
x_20 = lean_int_add(x_19, x_1);
lean_dec(x_19);
lean_inc(x_2);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Std_Time_instInhabitedDateTime___lambda__1___closed__3;
x_23 = lean_int_add(x_2, x_22);
x_24 = lean_int_sub(x_23, x_2);
lean_dec(x_23);
x_25 = lean_int_add(x_24, x_1);
lean_dec(x_24);
x_26 = lean_int_sub(x_2, x_2);
x_27 = lean_int_emod(x_26, x_25);
x_28 = lean_int_add(x_27, x_25);
lean_dec(x_27);
x_29 = lean_int_emod(x_28, x_25);
lean_dec(x_25);
lean_dec(x_28);
x_30 = lean_int_add(x_29, x_2);
lean_dec(x_29);
x_31 = l_Std_Time_instInhabitedDateTime___lambda__1___closed__4;
x_32 = lean_int_add(x_2, x_31);
x_33 = lean_int_sub(x_32, x_2);
lean_dec(x_32);
x_34 = lean_int_add(x_33, x_1);
lean_dec(x_33);
x_35 = lean_int_emod(x_26, x_34);
lean_dec(x_26);
x_36 = lean_int_add(x_35, x_34);
lean_dec(x_35);
x_37 = lean_int_emod(x_36, x_34);
lean_dec(x_34);
lean_dec(x_36);
x_38 = lean_int_add(x_37, x_2);
lean_dec(x_37);
x_39 = 0;
x_40 = lean_box(x_39);
lean_inc(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_2);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Time_instInhabitedDateTime___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Std_Time_instInhabitedDateTime___closed__1;
x_3 = l_Std_Time_instInhabitedDateTime___closed__2;
x_4 = lean_alloc_closure((void*)(l_Std_Time_instInhabitedDateTime___lambda__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_mk_thunk(x_4);
x_6 = l_Std_Time_instInhabitedDateTime___closed__3;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_instInhabitedDateTime___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instInhabitedDateTime(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(86400u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = l_Std_Time_PlainTime_toSeconds(x_6);
x_8 = lean_int_add(x_7, x_5);
lean_dec(x_7);
x_9 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_10 = lean_int_ediv(x_8, x_9);
lean_dec(x_8);
x_11 = l_Std_Time_PlainTime_toNanoseconds(x_6);
lean_dec(x_6);
x_12 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_13 = lean_int_mul(x_5, x_12);
x_14 = lean_int_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_15 = l_Std_Time_PlainTime_ofNanoseconds(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_16);
x_18 = lean_int_add(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_19 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestamp___lambda__1___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_mk_thunk(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_ofTimestamp___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_toDaysSinceUNIXEpoch___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toDaysSinceUNIXEpoch___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toDaysSinceUNIXEpoch(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_toTimestamp___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toTimestamp___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toTimestamp(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestamp___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_mk_thunk(x_6);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestamp___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_mk_thunk(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_convertTimeZone(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = l_Std_Time_PlainTime_toSeconds(x_5);
x_7 = lean_int_add(x_6, x_4);
lean_dec(x_6);
x_8 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_9 = lean_int_ediv(x_7, x_8);
lean_dec(x_7);
x_10 = l_Std_Time_PlainTime_toNanoseconds(x_5);
lean_dec(x_5);
x_11 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_12 = lean_int_mul(x_4, x_11);
x_13 = lean_int_add(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = l_Std_Time_PlainTime_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_15);
x_17 = lean_int_add(x_16, x_9);
lean_dec(x_9);
lean_dec(x_16);
x_18 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lambda__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_1);
x_5 = lean_mk_thunk(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_int_neg(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l_Std_Time_PlainTime_toSeconds(x_5);
x_7 = lean_int_add(x_6, x_4);
lean_dec(x_6);
x_8 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_9 = lean_int_ediv(x_7, x_8);
lean_dec(x_7);
x_10 = l_Std_Time_PlainTime_toNanoseconds(x_5);
lean_dec(x_5);
x_11 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_12 = lean_int_mul(x_4, x_11);
lean_dec(x_4);
x_13 = lean_int_add(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = l_Std_Time_PlainTime_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_15);
x_17 = lean_int_add(x_16, x_9);
lean_dec(x_9);
lean_dec(x_16);
x_18 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
x_20 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_19);
x_21 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_1);
x_22 = lean_mk_thunk(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_ofPlainDateTime___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_ofPlainDateTime(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Std_Time_PlainTime_toSeconds(x_6);
x_8 = l_Std_Time_DateTime_addHours___closed__1;
x_9 = lean_int_mul(x_3, x_8);
x_10 = lean_int_add(x_7, x_9);
lean_dec(x_7);
x_11 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_12 = lean_int_ediv(x_10, x_11);
lean_dec(x_10);
x_13 = l_Std_Time_PlainTime_toNanoseconds(x_6);
lean_dec(x_6);
x_14 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_15 = lean_int_mul(x_9, x_14);
lean_dec(x_9);
x_16 = lean_int_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = l_Std_Time_PlainTime_ofNanoseconds(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_18);
x_20 = lean_int_add(x_19, x_12);
lean_dec(x_12);
lean_dec(x_19);
x_21 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_20);
lean_dec(x_20);
lean_inc(x_17);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_int_neg(x_23);
x_25 = l_Std_Time_PlainTime_toSeconds(x_17);
x_26 = lean_int_add(x_25, x_24);
lean_dec(x_25);
x_27 = lean_int_ediv(x_26, x_11);
lean_dec(x_26);
x_28 = l_Std_Time_PlainTime_toNanoseconds(x_17);
lean_dec(x_17);
x_29 = lean_int_mul(x_24, x_14);
lean_dec(x_24);
x_30 = lean_int_add(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = l_Std_Time_PlainTime_ofNanoseconds(x_30);
lean_dec(x_30);
x_32 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_21);
x_33 = lean_int_add(x_32, x_27);
lean_dec(x_27);
lean_dec(x_32);
x_34 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
x_36 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_35);
x_37 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_37, 0, x_22);
x_38 = lean_mk_thunk(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addHours(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_int_neg(x_3);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_Std_Time_PlainTime_toSeconds(x_7);
x_9 = l_Std_Time_DateTime_addHours___closed__1;
x_10 = lean_int_mul(x_6, x_9);
lean_dec(x_6);
x_11 = lean_int_add(x_8, x_10);
lean_dec(x_8);
x_12 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_13 = lean_int_ediv(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_PlainTime_toNanoseconds(x_7);
lean_dec(x_7);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_16 = lean_int_mul(x_10, x_15);
lean_dec(x_10);
x_17 = lean_int_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = l_Std_Time_PlainTime_ofNanoseconds(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_19);
x_21 = lean_int_add(x_20, x_13);
lean_dec(x_13);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_21);
lean_dec(x_21);
lean_inc(x_18);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_int_neg(x_24);
x_26 = l_Std_Time_PlainTime_toSeconds(x_18);
x_27 = lean_int_add(x_26, x_25);
lean_dec(x_26);
x_28 = lean_int_ediv(x_27, x_12);
lean_dec(x_27);
x_29 = l_Std_Time_PlainTime_toNanoseconds(x_18);
lean_dec(x_18);
x_30 = lean_int_mul(x_25, x_15);
lean_dec(x_25);
x_31 = lean_int_add(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_32 = l_Std_Time_PlainTime_ofNanoseconds(x_31);
lean_dec(x_31);
x_33 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_22);
x_34 = lean_int_add(x_33, x_28);
lean_dec(x_28);
lean_dec(x_33);
x_35 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_36);
x_38 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_38, 0, x_23);
x_39 = lean_mk_thunk(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subHours(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(60u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Std_Time_PlainTime_toSeconds(x_6);
x_8 = l_Std_Time_DateTime_addMinutes___closed__1;
x_9 = lean_int_mul(x_3, x_8);
x_10 = lean_int_add(x_7, x_9);
lean_dec(x_7);
x_11 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_12 = lean_int_ediv(x_10, x_11);
lean_dec(x_10);
x_13 = l_Std_Time_PlainTime_toNanoseconds(x_6);
lean_dec(x_6);
x_14 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_15 = lean_int_mul(x_9, x_14);
lean_dec(x_9);
x_16 = lean_int_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = l_Std_Time_PlainTime_ofNanoseconds(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
lean_dec(x_5);
x_19 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_18);
x_20 = lean_int_add(x_19, x_12);
lean_dec(x_12);
lean_dec(x_19);
x_21 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_20);
lean_dec(x_20);
lean_inc(x_17);
lean_inc(x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_int_neg(x_23);
x_25 = l_Std_Time_PlainTime_toSeconds(x_17);
x_26 = lean_int_add(x_25, x_24);
lean_dec(x_25);
x_27 = lean_int_ediv(x_26, x_11);
lean_dec(x_26);
x_28 = l_Std_Time_PlainTime_toNanoseconds(x_17);
lean_dec(x_17);
x_29 = lean_int_mul(x_24, x_14);
lean_dec(x_24);
x_30 = lean_int_add(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = l_Std_Time_PlainTime_ofNanoseconds(x_30);
lean_dec(x_30);
x_32 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_21);
x_33 = lean_int_add(x_32, x_27);
lean_dec(x_27);
lean_dec(x_32);
x_34 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
x_36 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_35);
x_37 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_37, 0, x_22);
x_38 = lean_mk_thunk(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addMinutes(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_int_neg(x_3);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_Std_Time_PlainTime_toSeconds(x_7);
x_9 = l_Std_Time_DateTime_addMinutes___closed__1;
x_10 = lean_int_mul(x_6, x_9);
lean_dec(x_6);
x_11 = lean_int_add(x_8, x_10);
lean_dec(x_8);
x_12 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_13 = lean_int_ediv(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_PlainTime_toNanoseconds(x_7);
lean_dec(x_7);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_16 = lean_int_mul(x_10, x_15);
lean_dec(x_10);
x_17 = lean_int_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = l_Std_Time_PlainTime_ofNanoseconds(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
lean_dec(x_5);
x_20 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_19);
x_21 = lean_int_add(x_20, x_13);
lean_dec(x_13);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_21);
lean_dec(x_21);
lean_inc(x_18);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_int_neg(x_24);
x_26 = l_Std_Time_PlainTime_toSeconds(x_18);
x_27 = lean_int_add(x_26, x_25);
lean_dec(x_26);
x_28 = lean_int_ediv(x_27, x_12);
lean_dec(x_27);
x_29 = l_Std_Time_PlainTime_toNanoseconds(x_18);
lean_dec(x_18);
x_30 = lean_int_mul(x_25, x_15);
lean_dec(x_25);
x_31 = lean_int_add(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
x_32 = l_Std_Time_PlainTime_ofNanoseconds(x_31);
lean_dec(x_31);
x_33 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_22);
x_34 = lean_int_add(x_33, x_28);
lean_dec(x_28);
lean_dec(x_33);
x_35 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_36);
x_38 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_38, 0, x_23);
x_39 = lean_mk_thunk(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subMinutes(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Std_Time_PlainTime_toSeconds(x_6);
x_8 = lean_int_add(x_7, x_3);
lean_dec(x_7);
x_9 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_10 = lean_int_ediv(x_8, x_9);
lean_dec(x_8);
x_11 = l_Std_Time_PlainTime_toNanoseconds(x_6);
lean_dec(x_6);
x_12 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_13 = lean_int_mul(x_3, x_12);
x_14 = lean_int_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_15 = l_Std_Time_PlainTime_ofNanoseconds(x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_16);
x_18 = lean_int_add(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_19 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_18);
lean_dec(x_18);
lean_inc(x_15);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_int_neg(x_21);
x_23 = l_Std_Time_PlainTime_toSeconds(x_15);
x_24 = lean_int_add(x_23, x_22);
lean_dec(x_23);
x_25 = lean_int_ediv(x_24, x_9);
lean_dec(x_24);
x_26 = l_Std_Time_PlainTime_toNanoseconds(x_15);
lean_dec(x_15);
x_27 = lean_int_mul(x_22, x_12);
lean_dec(x_22);
x_28 = lean_int_add(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = l_Std_Time_PlainTime_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_19);
x_31 = lean_int_add(x_30, x_25);
lean_dec(x_25);
lean_dec(x_30);
x_32 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_33);
x_35 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_35, 0, x_20);
x_36 = lean_mk_thunk(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addSeconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_int_neg(x_3);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_Std_Time_PlainTime_toSeconds(x_7);
x_9 = lean_int_add(x_8, x_6);
lean_dec(x_8);
x_10 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_11 = lean_int_ediv(x_9, x_10);
lean_dec(x_9);
x_12 = l_Std_Time_PlainTime_toNanoseconds(x_7);
lean_dec(x_7);
x_13 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_14 = lean_int_mul(x_6, x_13);
lean_dec(x_6);
x_15 = lean_int_add(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_Std_Time_PlainTime_ofNanoseconds(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_17);
x_19 = lean_int_add(x_18, x_11);
lean_dec(x_11);
lean_dec(x_18);
x_20 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_19);
lean_dec(x_19);
lean_inc(x_16);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_int_neg(x_22);
x_24 = l_Std_Time_PlainTime_toSeconds(x_16);
x_25 = lean_int_add(x_24, x_23);
lean_dec(x_24);
x_26 = lean_int_ediv(x_25, x_10);
lean_dec(x_25);
x_27 = l_Std_Time_PlainTime_toNanoseconds(x_16);
lean_dec(x_16);
x_28 = lean_int_mul(x_23, x_13);
lean_dec(x_23);
x_29 = lean_int_add(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
x_30 = l_Std_Time_PlainTime_ofNanoseconds(x_29);
lean_dec(x_29);
x_31 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_20);
x_32 = lean_int_add(x_31, x_26);
lean_dec(x_26);
lean_dec(x_31);
x_33 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_34);
x_36 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_21);
x_37 = lean_mk_thunk(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subSeconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMilliseconds___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(86400000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = l_Std_Time_PlainTime_toMilliseconds(x_6);
x_8 = lean_int_add(x_7, x_3);
lean_dec(x_7);
x_9 = l_Std_Time_DateTime_addMilliseconds___closed__1;
x_10 = lean_int_ediv(x_8, x_9);
lean_dec(x_8);
x_11 = l_Std_Time_PlainTime_addMilliseconds(x_6, x_3);
lean_dec(x_6);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_12);
x_14 = lean_int_add(x_13, x_10);
lean_dec(x_10);
lean_dec(x_13);
x_15 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_14);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_int_neg(x_17);
x_19 = l_Std_Time_PlainTime_toSeconds(x_11);
x_20 = lean_int_add(x_19, x_18);
lean_dec(x_19);
x_21 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_22 = lean_int_ediv(x_20, x_21);
lean_dec(x_20);
x_23 = l_Std_Time_PlainTime_toNanoseconds(x_11);
lean_dec(x_11);
x_24 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_25 = lean_int_mul(x_18, x_24);
lean_dec(x_18);
x_26 = lean_int_add(x_23, x_25);
lean_dec(x_25);
lean_dec(x_23);
x_27 = l_Std_Time_PlainTime_ofNanoseconds(x_26);
lean_dec(x_26);
x_28 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_15);
x_29 = lean_int_add(x_28, x_22);
lean_dec(x_22);
lean_dec(x_28);
x_30 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
x_32 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_31);
x_33 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_33, 0, x_16);
x_34 = lean_mk_thunk(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addMilliseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_int_neg(x_3);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_Std_Time_PlainTime_toMilliseconds(x_7);
x_9 = lean_int_add(x_8, x_6);
lean_dec(x_8);
x_10 = l_Std_Time_DateTime_addMilliseconds___closed__1;
x_11 = lean_int_ediv(x_9, x_10);
lean_dec(x_9);
x_12 = l_Std_Time_PlainTime_addMilliseconds(x_7, x_6);
lean_dec(x_6);
lean_dec(x_7);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_13);
x_15 = lean_int_add(x_14, x_11);
lean_dec(x_11);
lean_dec(x_14);
x_16 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_15);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_int_neg(x_18);
x_20 = l_Std_Time_PlainTime_toSeconds(x_12);
x_21 = lean_int_add(x_20, x_19);
lean_dec(x_20);
x_22 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_23 = lean_int_ediv(x_21, x_22);
lean_dec(x_21);
x_24 = l_Std_Time_PlainTime_toNanoseconds(x_12);
lean_dec(x_12);
x_25 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_26 = lean_int_mul(x_19, x_25);
lean_dec(x_19);
x_27 = lean_int_add(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Std_Time_PlainTime_ofNanoseconds(x_27);
lean_dec(x_27);
x_29 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_16);
x_30 = lean_int_add(x_29, x_23);
lean_dec(x_23);
lean_dec(x_29);
x_31 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_32);
x_34 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_34, 0, x_17);
x_35 = lean_mk_thunk(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subMilliseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
x_10 = lean_int_add(x_9, x_3);
lean_dec(x_9);
x_11 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_12 = lean_int_ediv(x_10, x_11);
x_13 = lean_int_emod(x_10, x_11);
lean_dec(x_10);
x_14 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_15 = lean_int_mul(x_12, x_11);
lean_dec(x_12);
x_16 = lean_int_add(x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_17 = l_Std_Time_PlainTime_ofNanoseconds(x_16);
lean_dec(x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_19 = lean_ctor_get(x_17, 3);
lean_dec(x_19);
lean_ctor_set(x_17, 3, x_13);
lean_inc(x_17);
lean_inc(x_7);
lean_ctor_set(x_5, 1, x_17);
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_int_neg(x_20);
x_22 = l_Std_Time_PlainTime_toSeconds(x_17);
x_23 = lean_int_add(x_22, x_21);
lean_dec(x_22);
x_24 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_25 = lean_int_ediv(x_23, x_24);
lean_dec(x_23);
x_26 = l_Std_Time_PlainTime_toNanoseconds(x_17);
lean_dec(x_17);
x_27 = lean_int_mul(x_21, x_11);
lean_dec(x_21);
x_28 = lean_int_add(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_29 = l_Std_Time_PlainTime_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_7);
x_31 = lean_int_add(x_30, x_25);
lean_dec(x_25);
lean_dec(x_30);
x_32 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_33);
x_35 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_35, 0, x_5);
x_36 = lean_mk_thunk(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
x_40 = lean_ctor_get(x_17, 2);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_13);
lean_inc(x_41);
lean_inc(x_7);
lean_ctor_set(x_5, 1, x_41);
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_int_neg(x_42);
x_44 = l_Std_Time_PlainTime_toSeconds(x_41);
x_45 = lean_int_add(x_44, x_43);
lean_dec(x_44);
x_46 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_47 = lean_int_ediv(x_45, x_46);
lean_dec(x_45);
x_48 = l_Std_Time_PlainTime_toNanoseconds(x_41);
lean_dec(x_41);
x_49 = lean_int_mul(x_43, x_11);
lean_dec(x_43);
x_50 = lean_int_add(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
x_51 = l_Std_Time_PlainTime_ofNanoseconds(x_50);
lean_dec(x_50);
x_52 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_7);
x_53 = lean_int_add(x_52, x_47);
lean_dec(x_47);
lean_dec(x_52);
x_54 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
x_56 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_55);
x_57 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_57, 0, x_5);
x_58 = lean_mk_thunk(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_60 = lean_ctor_get(x_5, 0);
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_5);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
x_63 = lean_int_add(x_62, x_3);
lean_dec(x_62);
x_64 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_65 = lean_int_ediv(x_63, x_64);
x_66 = lean_int_emod(x_63, x_64);
lean_dec(x_63);
x_67 = l_Std_Time_PlainTime_toNanoseconds(x_61);
lean_dec(x_61);
x_68 = lean_int_mul(x_65, x_64);
lean_dec(x_65);
x_69 = lean_int_add(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
x_70 = l_Std_Time_PlainTime_ofNanoseconds(x_69);
lean_dec(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 2);
lean_inc(x_73);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 lean_ctor_release(x_70, 2);
 lean_ctor_release(x_70, 3);
 x_74 = x_70;
} else {
 lean_dec_ref(x_70);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(0, 4, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set(x_75, 2, x_73);
lean_ctor_set(x_75, 3, x_66);
lean_inc(x_75);
lean_inc(x_60);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_60);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_ctor_get(x_1, 0);
x_78 = lean_int_neg(x_77);
x_79 = l_Std_Time_PlainTime_toSeconds(x_75);
x_80 = lean_int_add(x_79, x_78);
lean_dec(x_79);
x_81 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_82 = lean_int_ediv(x_80, x_81);
lean_dec(x_80);
x_83 = l_Std_Time_PlainTime_toNanoseconds(x_75);
lean_dec(x_75);
x_84 = lean_int_mul(x_78, x_64);
lean_dec(x_78);
x_85 = lean_int_add(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
x_86 = l_Std_Time_PlainTime_ofNanoseconds(x_85);
lean_dec(x_85);
x_87 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_60);
x_88 = lean_int_add(x_87, x_82);
lean_dec(x_82);
lean_dec(x_87);
x_89 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_88);
lean_dec(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
x_91 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_90);
x_92 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_92, 0, x_76);
x_93 = lean_mk_thunk(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addNanoseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_int_neg(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = lean_int_add(x_10, x_6);
lean_dec(x_6);
lean_dec(x_10);
x_12 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_13 = lean_int_ediv(x_11, x_12);
x_14 = lean_int_emod(x_11, x_12);
lean_dec(x_11);
x_15 = l_Std_Time_PlainTime_toNanoseconds(x_9);
lean_dec(x_9);
x_16 = lean_int_mul(x_13, x_12);
lean_dec(x_13);
x_17 = lean_int_add(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = l_Std_Time_PlainTime_ofNanoseconds(x_17);
lean_dec(x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_20 = lean_ctor_get(x_18, 3);
lean_dec(x_20);
lean_ctor_set(x_18, 3, x_14);
lean_inc(x_18);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_18);
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_int_neg(x_21);
x_23 = l_Std_Time_PlainTime_toSeconds(x_18);
x_24 = lean_int_add(x_23, x_22);
lean_dec(x_23);
x_25 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_26 = lean_int_ediv(x_24, x_25);
lean_dec(x_24);
x_27 = l_Std_Time_PlainTime_toNanoseconds(x_18);
lean_dec(x_18);
x_28 = lean_int_mul(x_22, x_12);
lean_dec(x_22);
x_29 = lean_int_add(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
x_30 = l_Std_Time_PlainTime_ofNanoseconds(x_29);
lean_dec(x_29);
x_31 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_32 = lean_int_add(x_31, x_26);
lean_dec(x_26);
lean_dec(x_31);
x_33 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_30);
x_35 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_34);
x_36 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_5);
x_37 = lean_mk_thunk(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
x_41 = lean_ctor_get(x_18, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_14);
lean_inc(x_42);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_42);
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_int_neg(x_43);
x_45 = l_Std_Time_PlainTime_toSeconds(x_42);
x_46 = lean_int_add(x_45, x_44);
lean_dec(x_45);
x_47 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_48 = lean_int_ediv(x_46, x_47);
lean_dec(x_46);
x_49 = l_Std_Time_PlainTime_toNanoseconds(x_42);
lean_dec(x_42);
x_50 = lean_int_mul(x_44, x_12);
lean_dec(x_44);
x_51 = lean_int_add(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
x_52 = l_Std_Time_PlainTime_ofNanoseconds(x_51);
lean_dec(x_51);
x_53 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_54 = lean_int_add(x_53, x_48);
lean_dec(x_48);
lean_dec(x_53);
x_55 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
x_57 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_56);
x_58 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_58, 0, x_5);
x_59 = lean_mk_thunk(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_61 = lean_ctor_get(x_5, 0);
x_62 = lean_ctor_get(x_5, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_5);
x_63 = lean_ctor_get(x_62, 3);
lean_inc(x_63);
x_64 = lean_int_add(x_63, x_6);
lean_dec(x_6);
lean_dec(x_63);
x_65 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_66 = lean_int_ediv(x_64, x_65);
x_67 = lean_int_emod(x_64, x_65);
lean_dec(x_64);
x_68 = l_Std_Time_PlainTime_toNanoseconds(x_62);
lean_dec(x_62);
x_69 = lean_int_mul(x_66, x_65);
lean_dec(x_66);
x_70 = lean_int_add(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
x_71 = l_Std_Time_PlainTime_ofNanoseconds(x_70);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 2);
lean_inc(x_74);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 lean_ctor_release(x_71, 3);
 x_75 = x_71;
} else {
 lean_dec_ref(x_71);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 4, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_73);
lean_ctor_set(x_76, 2, x_74);
lean_ctor_set(x_76, 3, x_67);
lean_inc(x_76);
lean_inc(x_61);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_61);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_ctor_get(x_1, 0);
x_79 = lean_int_neg(x_78);
x_80 = l_Std_Time_PlainTime_toSeconds(x_76);
x_81 = lean_int_add(x_80, x_79);
lean_dec(x_80);
x_82 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_83 = lean_int_ediv(x_81, x_82);
lean_dec(x_81);
x_84 = l_Std_Time_PlainTime_toNanoseconds(x_76);
lean_dec(x_76);
x_85 = lean_int_mul(x_79, x_65);
lean_dec(x_79);
x_86 = lean_int_add(x_84, x_85);
lean_dec(x_85);
lean_dec(x_84);
x_87 = l_Std_Time_PlainTime_ofNanoseconds(x_86);
lean_dec(x_86);
x_88 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_61);
x_89 = lean_int_add(x_88, x_83);
lean_dec(x_83);
lean_dec(x_88);
x_90 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_87);
x_92 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_91);
x_93 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_93, 0, x_77);
x_94 = lean_mk_thunk(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subNanoseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_7);
x_10 = lean_int_add(x_9, x_3);
lean_dec(x_9);
x_11 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_ctor_set(x_5, 0, x_11);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_int_neg(x_12);
x_14 = l_Std_Time_PlainTime_toSeconds(x_8);
x_15 = lean_int_add(x_14, x_13);
lean_dec(x_14);
x_16 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_17 = lean_int_ediv(x_15, x_16);
lean_dec(x_15);
x_18 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_20 = lean_int_mul(x_13, x_19);
lean_dec(x_13);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_PlainTime_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_11);
x_24 = lean_int_add(x_23, x_17);
lean_dec(x_17);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_28, 0, x_5);
x_29 = lean_mk_thunk(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_31);
x_34 = lean_int_add(x_33, x_3);
lean_dec(x_33);
x_35 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_34);
lean_dec(x_34);
lean_inc(x_32);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_int_neg(x_37);
x_39 = l_Std_Time_PlainTime_toSeconds(x_32);
x_40 = lean_int_add(x_39, x_38);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_42 = lean_int_ediv(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_PlainTime_toNanoseconds(x_32);
lean_dec(x_32);
x_44 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_45 = lean_int_mul(x_38, x_44);
lean_dec(x_38);
x_46 = lean_int_add(x_43, x_45);
lean_dec(x_45);
lean_dec(x_43);
x_47 = l_Std_Time_PlainTime_ofNanoseconds(x_46);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_35);
x_49 = lean_int_add(x_48, x_42);
lean_dec(x_42);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_51);
x_53 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_53, 0, x_36);
x_54 = lean_mk_thunk(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addDays(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_int_neg(x_3);
x_10 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_7);
x_11 = lean_int_add(x_10, x_9);
lean_dec(x_9);
lean_dec(x_10);
x_12 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_11);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_12);
lean_ctor_set(x_5, 0, x_12);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_int_neg(x_13);
x_15 = l_Std_Time_PlainTime_toSeconds(x_8);
x_16 = lean_int_add(x_15, x_14);
lean_dec(x_15);
x_17 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_18 = lean_int_ediv(x_16, x_17);
lean_dec(x_16);
x_19 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_20 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_21 = lean_int_mul(x_14, x_20);
lean_dec(x_14);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_PlainTime_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_12);
x_25 = lean_int_add(x_24, x_18);
lean_dec(x_18);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_27);
x_29 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_29, 0, x_5);
x_30 = lean_mk_thunk(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = lean_int_neg(x_3);
x_35 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_32);
x_36 = lean_int_add(x_35, x_34);
lean_dec(x_34);
lean_dec(x_35);
x_37 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_36);
lean_dec(x_36);
lean_inc(x_33);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_int_neg(x_39);
x_41 = l_Std_Time_PlainTime_toSeconds(x_33);
x_42 = lean_int_add(x_41, x_40);
lean_dec(x_41);
x_43 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_44 = lean_int_ediv(x_42, x_43);
lean_dec(x_42);
x_45 = l_Std_Time_PlainTime_toNanoseconds(x_33);
lean_dec(x_33);
x_46 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_47 = lean_int_mul(x_40, x_46);
lean_dec(x_40);
x_48 = lean_int_add(x_45, x_47);
lean_dec(x_47);
lean_dec(x_45);
x_49 = l_Std_Time_PlainTime_ofNanoseconds(x_48);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_37);
x_51 = lean_int_add(x_50, x_44);
lean_dec(x_44);
lean_dec(x_50);
x_52 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
x_54 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_53);
x_55 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_55, 0, x_38);
x_56 = lean_mk_thunk(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subDays(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_7);
x_10 = l_Std_Time_DateTime_addWeeks___closed__1;
x_11 = lean_int_mul(x_3, x_10);
x_12 = lean_int_add(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
x_13 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_12);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_13);
lean_ctor_set(x_5, 0, x_13);
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_int_neg(x_14);
x_16 = l_Std_Time_PlainTime_toSeconds(x_8);
x_17 = lean_int_add(x_16, x_15);
lean_dec(x_16);
x_18 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_19 = lean_int_ediv(x_17, x_18);
lean_dec(x_17);
x_20 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_21 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_22 = lean_int_mul(x_15, x_21);
lean_dec(x_15);
x_23 = lean_int_add(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
x_24 = l_Std_Time_PlainTime_ofNanoseconds(x_23);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_13);
x_26 = lean_int_add(x_25, x_19);
lean_dec(x_19);
lean_dec(x_25);
x_27 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
x_29 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_28);
x_30 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_30, 0, x_5);
x_31 = lean_mk_thunk(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_35 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_33);
x_36 = l_Std_Time_DateTime_addWeeks___closed__1;
x_37 = lean_int_mul(x_3, x_36);
x_38 = lean_int_add(x_35, x_37);
lean_dec(x_37);
lean_dec(x_35);
x_39 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_38);
lean_dec(x_38);
lean_inc(x_34);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_34);
x_41 = lean_ctor_get(x_1, 0);
x_42 = lean_int_neg(x_41);
x_43 = l_Std_Time_PlainTime_toSeconds(x_34);
x_44 = lean_int_add(x_43, x_42);
lean_dec(x_43);
x_45 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_46 = lean_int_ediv(x_44, x_45);
lean_dec(x_44);
x_47 = l_Std_Time_PlainTime_toNanoseconds(x_34);
lean_dec(x_34);
x_48 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_49 = lean_int_mul(x_42, x_48);
lean_dec(x_42);
x_50 = lean_int_add(x_47, x_49);
lean_dec(x_49);
lean_dec(x_47);
x_51 = l_Std_Time_PlainTime_ofNanoseconds(x_50);
lean_dec(x_50);
x_52 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_39);
x_53 = lean_int_add(x_52, x_46);
lean_dec(x_46);
lean_dec(x_52);
x_54 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
x_56 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_55);
x_57 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_57, 0, x_40);
x_58 = lean_mk_thunk(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addWeeks(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_int_neg(x_3);
x_10 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_7);
x_11 = l_Std_Time_DateTime_addWeeks___closed__1;
x_12 = lean_int_mul(x_9, x_11);
lean_dec(x_9);
x_13 = lean_int_add(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_13);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_14);
lean_ctor_set(x_5, 0, x_14);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_int_neg(x_15);
x_17 = l_Std_Time_PlainTime_toSeconds(x_8);
x_18 = lean_int_add(x_17, x_16);
lean_dec(x_17);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_20 = lean_int_ediv(x_18, x_19);
lean_dec(x_18);
x_21 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_22 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_23 = lean_int_mul(x_16, x_22);
lean_dec(x_16);
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_Time_PlainTime_ofNanoseconds(x_24);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_14);
x_27 = lean_int_add(x_26, x_20);
lean_dec(x_20);
lean_dec(x_26);
x_28 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
x_30 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_29);
x_31 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_5);
x_32 = lean_mk_thunk(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_34 = lean_ctor_get(x_5, 0);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_5);
x_36 = lean_int_neg(x_3);
x_37 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_34);
x_38 = l_Std_Time_DateTime_addWeeks___closed__1;
x_39 = lean_int_mul(x_36, x_38);
lean_dec(x_36);
x_40 = lean_int_add(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
x_41 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_40);
lean_dec(x_40);
lean_inc(x_35);
lean_inc(x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_int_neg(x_43);
x_45 = l_Std_Time_PlainTime_toSeconds(x_35);
x_46 = lean_int_add(x_45, x_44);
lean_dec(x_45);
x_47 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_48 = lean_int_ediv(x_46, x_47);
lean_dec(x_46);
x_49 = l_Std_Time_PlainTime_toNanoseconds(x_35);
lean_dec(x_35);
x_50 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_51 = lean_int_mul(x_44, x_50);
lean_dec(x_44);
x_52 = lean_int_add(x_49, x_51);
lean_dec(x_51);
lean_dec(x_49);
x_53 = l_Std_Time_PlainTime_ofNanoseconds(x_52);
lean_dec(x_52);
x_54 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_41);
x_55 = lean_int_add(x_54, x_48);
lean_dec(x_48);
lean_dec(x_54);
x_56 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
x_58 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_57);
x_59 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_59, 0, x_42);
x_60 = lean_mk_thunk(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subWeeks(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
lean_inc(x_5);
x_6 = l_Std_Time_PlainDateTime_addMonthsClip(x_5, x_3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_int_neg(x_7);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Std_Time_PlainTime_toSeconds(x_9);
x_11 = lean_int_add(x_10, x_8);
lean_dec(x_10);
x_12 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_13 = lean_int_ediv(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_PlainTime_toNanoseconds(x_9);
lean_dec(x_9);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_16 = lean_int_mul(x_8, x_15);
lean_dec(x_8);
x_17 = lean_int_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = l_Std_Time_PlainTime_ofNanoseconds(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_19);
x_21 = lean_int_add(x_20, x_13);
lean_dec(x_13);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_23);
x_25 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_6);
x_26 = lean_mk_thunk(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addMonthsClip(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_int_neg(x_3);
x_10 = l_Std_Time_PlainDate_addMonthsClip(x_7, x_9);
lean_dec(x_9);
lean_inc(x_8);
lean_inc(x_10);
lean_ctor_set(x_5, 0, x_10);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_int_neg(x_11);
x_13 = l_Std_Time_PlainTime_toSeconds(x_8);
x_14 = lean_int_add(x_13, x_12);
lean_dec(x_13);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_16 = lean_int_ediv(x_14, x_15);
lean_dec(x_14);
x_17 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_18 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_19 = lean_int_mul(x_12, x_18);
lean_dec(x_12);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_PlainTime_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_10);
x_23 = lean_int_add(x_22, x_16);
lean_dec(x_16);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_25);
x_27 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_5);
x_28 = lean_mk_thunk(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_int_neg(x_3);
x_33 = l_Std_Time_PlainDate_addMonthsClip(x_30, x_32);
lean_dec(x_32);
lean_inc(x_31);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_int_neg(x_35);
x_37 = l_Std_Time_PlainTime_toSeconds(x_31);
x_38 = lean_int_add(x_37, x_36);
lean_dec(x_37);
x_39 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_40 = lean_int_ediv(x_38, x_39);
lean_dec(x_38);
x_41 = l_Std_Time_PlainTime_toNanoseconds(x_31);
lean_dec(x_31);
x_42 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_43 = lean_int_mul(x_36, x_42);
lean_dec(x_36);
x_44 = lean_int_add(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
x_45 = l_Std_Time_PlainTime_ofNanoseconds(x_44);
lean_dec(x_44);
x_46 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_33);
x_47 = lean_int_add(x_46, x_40);
lean_dec(x_40);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_51, 0, x_34);
x_52 = lean_mk_thunk(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subMonthsClip(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
lean_inc(x_5);
x_6 = l_Std_Time_PlainDateTime_addMonthsRollOver(x_5, x_3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_int_neg(x_7);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Std_Time_PlainTime_toSeconds(x_9);
x_11 = lean_int_add(x_10, x_8);
lean_dec(x_10);
x_12 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_13 = lean_int_ediv(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_PlainTime_toNanoseconds(x_9);
lean_dec(x_9);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_16 = lean_int_mul(x_8, x_15);
lean_dec(x_8);
x_17 = lean_int_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = l_Std_Time_PlainTime_ofNanoseconds(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_19);
x_21 = lean_int_add(x_20, x_13);
lean_dec(x_13);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_23);
x_25 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_6);
x_26 = lean_mk_thunk(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addMonthsRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_int_neg(x_3);
x_10 = l_Std_Time_PlainDate_addMonthsRollOver(x_7, x_9);
lean_dec(x_9);
lean_inc(x_8);
lean_inc(x_10);
lean_ctor_set(x_5, 0, x_10);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_int_neg(x_11);
x_13 = l_Std_Time_PlainTime_toSeconds(x_8);
x_14 = lean_int_add(x_13, x_12);
lean_dec(x_13);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_16 = lean_int_ediv(x_14, x_15);
lean_dec(x_14);
x_17 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_18 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_19 = lean_int_mul(x_12, x_18);
lean_dec(x_12);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_PlainTime_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_10);
x_23 = lean_int_add(x_22, x_16);
lean_dec(x_16);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_25);
x_27 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_5);
x_28 = lean_mk_thunk(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_int_neg(x_3);
x_33 = l_Std_Time_PlainDate_addMonthsRollOver(x_30, x_32);
lean_dec(x_32);
lean_inc(x_31);
lean_inc(x_33);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_int_neg(x_35);
x_37 = l_Std_Time_PlainTime_toSeconds(x_31);
x_38 = lean_int_add(x_37, x_36);
lean_dec(x_37);
x_39 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_40 = lean_int_ediv(x_38, x_39);
lean_dec(x_38);
x_41 = l_Std_Time_PlainTime_toNanoseconds(x_31);
lean_dec(x_31);
x_42 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_43 = lean_int_mul(x_36, x_42);
lean_dec(x_36);
x_44 = lean_int_add(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
x_45 = l_Std_Time_PlainTime_ofNanoseconds(x_44);
lean_dec(x_44);
x_46 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_33);
x_47 = lean_int_add(x_46, x_40);
lean_dec(x_40);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_51, 0, x_34);
x_52 = lean_mk_thunk(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subMonthsRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Std_Time_DateTime_addYearsRollOver___closed__1;
x_10 = lean_int_mul(x_3, x_9);
x_11 = l_Std_Time_PlainDate_addMonthsRollOver(x_7, x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_ctor_set(x_5, 0, x_11);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_int_neg(x_12);
x_14 = l_Std_Time_PlainTime_toSeconds(x_8);
x_15 = lean_int_add(x_14, x_13);
lean_dec(x_14);
x_16 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_17 = lean_int_ediv(x_15, x_16);
lean_dec(x_15);
x_18 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_20 = lean_int_mul(x_13, x_19);
lean_dec(x_13);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_PlainTime_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_11);
x_24 = lean_int_add(x_23, x_17);
lean_dec(x_17);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_28, 0, x_5);
x_29 = lean_mk_thunk(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = l_Std_Time_DateTime_addYearsRollOver___closed__1;
x_34 = lean_int_mul(x_3, x_33);
x_35 = l_Std_Time_PlainDate_addMonthsRollOver(x_31, x_34);
lean_dec(x_34);
lean_inc(x_32);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_int_neg(x_37);
x_39 = l_Std_Time_PlainTime_toSeconds(x_32);
x_40 = lean_int_add(x_39, x_38);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_42 = lean_int_ediv(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_PlainTime_toNanoseconds(x_32);
lean_dec(x_32);
x_44 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_45 = lean_int_mul(x_38, x_44);
lean_dec(x_38);
x_46 = lean_int_add(x_43, x_45);
lean_dec(x_45);
lean_dec(x_43);
x_47 = l_Std_Time_PlainTime_ofNanoseconds(x_46);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_35);
x_49 = lean_int_add(x_48, x_42);
lean_dec(x_42);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_51);
x_53 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_53, 0, x_36);
x_54 = lean_mk_thunk(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addYearsRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Std_Time_DateTime_addYearsRollOver___closed__1;
x_10 = lean_int_mul(x_3, x_9);
x_11 = l_Std_Time_PlainDate_addMonthsClip(x_7, x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_ctor_set(x_5, 0, x_11);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_int_neg(x_12);
x_14 = l_Std_Time_PlainTime_toSeconds(x_8);
x_15 = lean_int_add(x_14, x_13);
lean_dec(x_14);
x_16 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_17 = lean_int_ediv(x_15, x_16);
lean_dec(x_15);
x_18 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_20 = lean_int_mul(x_13, x_19);
lean_dec(x_13);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_PlainTime_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_11);
x_24 = lean_int_add(x_23, x_17);
lean_dec(x_17);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_28, 0, x_5);
x_29 = lean_mk_thunk(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = l_Std_Time_DateTime_addYearsRollOver___closed__1;
x_34 = lean_int_mul(x_3, x_33);
x_35 = l_Std_Time_PlainDate_addMonthsClip(x_31, x_34);
lean_dec(x_34);
lean_inc(x_32);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_int_neg(x_37);
x_39 = l_Std_Time_PlainTime_toSeconds(x_32);
x_40 = lean_int_add(x_39, x_38);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_42 = lean_int_ediv(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_PlainTime_toNanoseconds(x_32);
lean_dec(x_32);
x_44 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_45 = lean_int_mul(x_38, x_44);
lean_dec(x_38);
x_46 = lean_int_add(x_43, x_45);
lean_dec(x_45);
lean_dec(x_43);
x_47 = l_Std_Time_PlainTime_ofNanoseconds(x_46);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_35);
x_49 = lean_int_add(x_48, x_42);
lean_dec(x_42);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_51);
x_53 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_53, 0, x_36);
x_54 = lean_mk_thunk(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addYearsClip(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Std_Time_DateTime_addYearsRollOver___closed__1;
x_10 = lean_int_mul(x_3, x_9);
x_11 = lean_int_neg(x_10);
lean_dec(x_10);
x_12 = l_Std_Time_PlainDate_addMonthsRollOver(x_7, x_11);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_12);
lean_ctor_set(x_5, 0, x_12);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_int_neg(x_13);
x_15 = l_Std_Time_PlainTime_toSeconds(x_8);
x_16 = lean_int_add(x_15, x_14);
lean_dec(x_15);
x_17 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_18 = lean_int_ediv(x_16, x_17);
lean_dec(x_16);
x_19 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_20 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_21 = lean_int_mul(x_14, x_20);
lean_dec(x_14);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_PlainTime_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_12);
x_25 = lean_int_add(x_24, x_18);
lean_dec(x_18);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_27);
x_29 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_29, 0, x_5);
x_30 = lean_mk_thunk(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = l_Std_Time_DateTime_addYearsRollOver___closed__1;
x_35 = lean_int_mul(x_3, x_34);
x_36 = lean_int_neg(x_35);
lean_dec(x_35);
x_37 = l_Std_Time_PlainDate_addMonthsRollOver(x_32, x_36);
lean_dec(x_36);
lean_inc(x_33);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_int_neg(x_39);
x_41 = l_Std_Time_PlainTime_toSeconds(x_33);
x_42 = lean_int_add(x_41, x_40);
lean_dec(x_41);
x_43 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_44 = lean_int_ediv(x_42, x_43);
lean_dec(x_42);
x_45 = l_Std_Time_PlainTime_toNanoseconds(x_33);
lean_dec(x_33);
x_46 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_47 = lean_int_mul(x_40, x_46);
lean_dec(x_40);
x_48 = lean_int_add(x_45, x_47);
lean_dec(x_47);
lean_dec(x_45);
x_49 = l_Std_Time_PlainTime_ofNanoseconds(x_48);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_37);
x_51 = lean_int_add(x_50, x_44);
lean_dec(x_44);
lean_dec(x_50);
x_52 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
x_54 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_53);
x_55 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_55, 0, x_38);
x_56 = lean_mk_thunk(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subYearsRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Std_Time_DateTime_addYearsRollOver___closed__1;
x_10 = lean_int_mul(x_3, x_9);
x_11 = lean_int_neg(x_10);
lean_dec(x_10);
x_12 = l_Std_Time_PlainDate_addMonthsClip(x_7, x_11);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_12);
lean_ctor_set(x_5, 0, x_12);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_int_neg(x_13);
x_15 = l_Std_Time_PlainTime_toSeconds(x_8);
x_16 = lean_int_add(x_15, x_14);
lean_dec(x_15);
x_17 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_18 = lean_int_ediv(x_16, x_17);
lean_dec(x_16);
x_19 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_20 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_21 = lean_int_mul(x_14, x_20);
lean_dec(x_14);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_PlainTime_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_12);
x_25 = lean_int_add(x_24, x_18);
lean_dec(x_18);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_27);
x_29 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_29, 0, x_5);
x_30 = lean_mk_thunk(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = l_Std_Time_DateTime_addYearsRollOver___closed__1;
x_35 = lean_int_mul(x_3, x_34);
x_36 = lean_int_neg(x_35);
lean_dec(x_35);
x_37 = l_Std_Time_PlainDate_addMonthsClip(x_32, x_36);
lean_dec(x_36);
lean_inc(x_33);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_int_neg(x_39);
x_41 = l_Std_Time_PlainTime_toSeconds(x_33);
x_42 = lean_int_add(x_41, x_40);
lean_dec(x_41);
x_43 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_44 = lean_int_ediv(x_42, x_43);
lean_dec(x_42);
x_45 = l_Std_Time_PlainTime_toNanoseconds(x_33);
lean_dec(x_33);
x_46 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_47 = lean_int_mul(x_40, x_46);
lean_dec(x_40);
x_48 = lean_int_add(x_45, x_47);
lean_dec(x_47);
lean_dec(x_45);
x_49 = l_Std_Time_PlainTime_ofNanoseconds(x_48);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_37);
x_51 = lean_int_add(x_50, x_44);
lean_dec(x_44);
lean_dec(x_50);
x_52 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
x_54 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_53);
x_55 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_55, 0, x_38);
x_56 = lean_mk_thunk(x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subYearsClip(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(100u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(400u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 2);
lean_dec(x_12);
x_13 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_14 = lean_int_mod(x_10, x_13);
x_15 = l_Std_Time_instInhabitedDateTime___closed__2;
x_16 = lean_int_dec_eq(x_14, x_15);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_int_neg(x_17);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_20 = lean_int_mul(x_18, x_19);
if (x_16 == 0)
{
uint8_t x_40; lean_object* x_41; uint8_t x_42; 
x_40 = 0;
x_41 = l_Std_Time_Month_Ordinal_days(x_40, x_11);
x_42 = lean_int_dec_lt(x_41, x_3);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
lean_ctor_set(x_6, 2, x_3);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_7);
x_21 = x_43;
goto block_39;
}
else
{
lean_object* x_44; 
lean_dec(x_3);
lean_ctor_set(x_6, 2, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_7);
x_21 = x_44;
goto block_39;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_46 = lean_int_mod(x_10, x_45);
x_47 = lean_int_dec_eq(x_46, x_15);
lean_dec(x_46);
x_48 = l_instDecidableNot___rarg(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_50 = lean_int_mod(x_10, x_49);
x_51 = lean_int_dec_eq(x_50, x_15);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; lean_object* x_53; uint8_t x_54; 
x_52 = 0;
x_53 = l_Std_Time_Month_Ordinal_days(x_52, x_11);
x_54 = lean_int_dec_lt(x_53, x_3);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_ctor_set(x_6, 2, x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_7);
x_21 = x_55;
goto block_39;
}
else
{
lean_object* x_56; 
lean_dec(x_3);
lean_ctor_set(x_6, 2, x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_7);
x_21 = x_56;
goto block_39;
}
}
else
{
uint8_t x_57; lean_object* x_58; uint8_t x_59; 
x_57 = 1;
x_58 = l_Std_Time_Month_Ordinal_days(x_57, x_11);
x_59 = lean_int_dec_lt(x_58, x_3);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_58);
lean_ctor_set(x_6, 2, x_3);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_7);
x_21 = x_60;
goto block_39;
}
else
{
lean_object* x_61; 
lean_dec(x_3);
lean_ctor_set(x_6, 2, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_6);
lean_ctor_set(x_61, 1, x_7);
x_21 = x_61;
goto block_39;
}
}
}
else
{
uint8_t x_62; lean_object* x_63; uint8_t x_64; 
x_62 = 1;
x_63 = l_Std_Time_Month_Ordinal_days(x_62, x_11);
x_64 = lean_int_dec_lt(x_63, x_3);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_63);
lean_ctor_set(x_6, 2, x_3);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_7);
x_21 = x_65;
goto block_39;
}
else
{
lean_object* x_66; 
lean_dec(x_3);
lean_ctor_set(x_6, 2, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_6);
lean_ctor_set(x_66, 1, x_7);
x_21 = x_66;
goto block_39;
}
}
}
block_39:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = l_Std_Time_PlainTime_toSeconds(x_22);
x_24 = lean_int_add(x_23, x_18);
lean_dec(x_18);
lean_dec(x_23);
x_25 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_26 = lean_int_ediv(x_24, x_25);
lean_dec(x_24);
x_27 = l_Std_Time_PlainTime_toNanoseconds(x_22);
lean_dec(x_22);
x_28 = lean_int_add(x_27, x_20);
lean_dec(x_20);
lean_dec(x_27);
x_29 = l_Std_Time_PlainTime_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
x_31 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_30);
x_32 = lean_int_add(x_31, x_26);
lean_dec(x_26);
lean_dec(x_31);
x_33 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_32);
lean_dec(x_32);
if (lean_is_scalar(x_8)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_8;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_34);
x_36 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_21);
x_37 = lean_mk_thunk(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_6, 0);
x_68 = lean_ctor_get(x_6, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_6);
x_69 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_70 = lean_int_mod(x_67, x_69);
x_71 = l_Std_Time_instInhabitedDateTime___closed__2;
x_72 = lean_int_dec_eq(x_70, x_71);
lean_dec(x_70);
x_73 = lean_ctor_get(x_1, 0);
x_74 = lean_int_neg(x_73);
x_75 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_76 = lean_int_mul(x_74, x_75);
if (x_72 == 0)
{
uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_96 = 0;
x_97 = l_Std_Time_Month_Ordinal_days(x_96, x_68);
x_98 = lean_int_dec_lt(x_97, x_3);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_97);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_67);
lean_ctor_set(x_99, 1, x_68);
lean_ctor_set(x_99, 2, x_3);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_7);
x_77 = x_100;
goto block_95;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_3);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_67);
lean_ctor_set(x_101, 1, x_68);
lean_ctor_set(x_101, 2, x_97);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_7);
x_77 = x_102;
goto block_95;
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; 
x_103 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_104 = lean_int_mod(x_67, x_103);
x_105 = lean_int_dec_eq(x_104, x_71);
lean_dec(x_104);
x_106 = l_instDecidableNot___rarg(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_108 = lean_int_mod(x_67, x_107);
x_109 = lean_int_dec_eq(x_108, x_71);
lean_dec(x_108);
if (x_109 == 0)
{
uint8_t x_110; lean_object* x_111; uint8_t x_112; 
x_110 = 0;
x_111 = l_Std_Time_Month_Ordinal_days(x_110, x_68);
x_112 = lean_int_dec_lt(x_111, x_3);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_111);
x_113 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_113, 0, x_67);
lean_ctor_set(x_113, 1, x_68);
lean_ctor_set(x_113, 2, x_3);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_7);
x_77 = x_114;
goto block_95;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_3);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_67);
lean_ctor_set(x_115, 1, x_68);
lean_ctor_set(x_115, 2, x_111);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_7);
x_77 = x_116;
goto block_95;
}
}
else
{
uint8_t x_117; lean_object* x_118; uint8_t x_119; 
x_117 = 1;
x_118 = l_Std_Time_Month_Ordinal_days(x_117, x_68);
x_119 = lean_int_dec_lt(x_118, x_3);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_118);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_67);
lean_ctor_set(x_120, 1, x_68);
lean_ctor_set(x_120, 2, x_3);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_7);
x_77 = x_121;
goto block_95;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_3);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_67);
lean_ctor_set(x_122, 1, x_68);
lean_ctor_set(x_122, 2, x_118);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_7);
x_77 = x_123;
goto block_95;
}
}
}
else
{
uint8_t x_124; lean_object* x_125; uint8_t x_126; 
x_124 = 1;
x_125 = l_Std_Time_Month_Ordinal_days(x_124, x_68);
x_126 = lean_int_dec_lt(x_125, x_3);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_67);
lean_ctor_set(x_127, 1, x_68);
lean_ctor_set(x_127, 2, x_3);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_7);
x_77 = x_128;
goto block_95;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_3);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_67);
lean_ctor_set(x_129, 1, x_68);
lean_ctor_set(x_129, 2, x_125);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
x_77 = x_130;
goto block_95;
}
}
}
block_95:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = l_Std_Time_PlainTime_toSeconds(x_78);
x_80 = lean_int_add(x_79, x_74);
lean_dec(x_74);
lean_dec(x_79);
x_81 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_82 = lean_int_ediv(x_80, x_81);
lean_dec(x_80);
x_83 = l_Std_Time_PlainTime_toNanoseconds(x_78);
lean_dec(x_78);
x_84 = lean_int_add(x_83, x_76);
lean_dec(x_76);
lean_dec(x_83);
x_85 = l_Std_Time_PlainTime_ofNanoseconds(x_84);
lean_dec(x_84);
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
x_87 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_86);
x_88 = lean_int_add(x_87, x_82);
lean_dec(x_82);
lean_dec(x_87);
x_89 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_88);
lean_dec(x_88);
if (lean_is_scalar(x_8)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_8;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
x_91 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_90);
x_92 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_92, 0, x_77);
x_93 = lean_mk_thunk(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withDaysClip(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Std_Time_PlainDate_rollOver(x_9, x_10, x_3);
lean_inc(x_8);
lean_inc(x_11);
lean_ctor_set(x_5, 0, x_11);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_int_neg(x_12);
x_14 = l_Std_Time_PlainTime_toSeconds(x_8);
x_15 = lean_int_add(x_14, x_13);
lean_dec(x_14);
x_16 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_17 = lean_int_ediv(x_15, x_16);
lean_dec(x_15);
x_18 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_20 = lean_int_mul(x_13, x_19);
lean_dec(x_13);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_PlainTime_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_11);
x_24 = lean_int_add(x_23, x_17);
lean_dec(x_17);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_28, 0, x_5);
x_29 = lean_mk_thunk(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Std_Time_PlainDate_rollOver(x_33, x_34, x_3);
lean_inc(x_32);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_int_neg(x_37);
x_39 = l_Std_Time_PlainTime_toSeconds(x_32);
x_40 = lean_int_add(x_39, x_38);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_42 = lean_int_ediv(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_PlainTime_toNanoseconds(x_32);
lean_dec(x_32);
x_44 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_45 = lean_int_mul(x_38, x_44);
lean_dec(x_38);
x_46 = lean_int_add(x_43, x_45);
lean_dec(x_45);
lean_dec(x_43);
x_47 = l_Std_Time_PlainTime_ofNanoseconds(x_46);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_35);
x_49 = lean_int_add(x_48, x_42);
lean_dec(x_42);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_51);
x_53 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_53, 0, x_36);
x_54 = lean_mk_thunk(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withDaysRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 2);
x_12 = lean_ctor_get(x_6, 1);
lean_dec(x_12);
x_13 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_14 = lean_int_mod(x_10, x_13);
x_15 = l_Std_Time_instInhabitedDateTime___closed__2;
x_16 = lean_int_dec_eq(x_14, x_15);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_int_neg(x_17);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_20 = lean_int_mul(x_18, x_19);
if (x_16 == 0)
{
uint8_t x_40; lean_object* x_41; uint8_t x_42; 
x_40 = 0;
x_41 = l_Std_Time_Month_Ordinal_days(x_40, x_3);
x_42 = lean_int_dec_lt(x_41, x_11);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
lean_ctor_set(x_6, 1, x_3);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_7);
x_21 = x_43;
goto block_39;
}
else
{
lean_object* x_44; 
lean_dec(x_11);
lean_ctor_set(x_6, 2, x_41);
lean_ctor_set(x_6, 1, x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_7);
x_21 = x_44;
goto block_39;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_46 = lean_int_mod(x_10, x_45);
x_47 = lean_int_dec_eq(x_46, x_15);
lean_dec(x_46);
x_48 = l_instDecidableNot___rarg(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_50 = lean_int_mod(x_10, x_49);
x_51 = lean_int_dec_eq(x_50, x_15);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; lean_object* x_53; uint8_t x_54; 
x_52 = 0;
x_53 = l_Std_Time_Month_Ordinal_days(x_52, x_3);
x_54 = lean_int_dec_lt(x_53, x_11);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_ctor_set(x_6, 1, x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_7);
x_21 = x_55;
goto block_39;
}
else
{
lean_object* x_56; 
lean_dec(x_11);
lean_ctor_set(x_6, 2, x_53);
lean_ctor_set(x_6, 1, x_3);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_7);
x_21 = x_56;
goto block_39;
}
}
else
{
uint8_t x_57; lean_object* x_58; uint8_t x_59; 
x_57 = 1;
x_58 = l_Std_Time_Month_Ordinal_days(x_57, x_3);
x_59 = lean_int_dec_lt(x_58, x_11);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_58);
lean_ctor_set(x_6, 1, x_3);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_7);
x_21 = x_60;
goto block_39;
}
else
{
lean_object* x_61; 
lean_dec(x_11);
lean_ctor_set(x_6, 2, x_58);
lean_ctor_set(x_6, 1, x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_6);
lean_ctor_set(x_61, 1, x_7);
x_21 = x_61;
goto block_39;
}
}
}
else
{
uint8_t x_62; lean_object* x_63; uint8_t x_64; 
x_62 = 1;
x_63 = l_Std_Time_Month_Ordinal_days(x_62, x_3);
x_64 = lean_int_dec_lt(x_63, x_11);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_63);
lean_ctor_set(x_6, 1, x_3);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_7);
x_21 = x_65;
goto block_39;
}
else
{
lean_object* x_66; 
lean_dec(x_11);
lean_ctor_set(x_6, 2, x_63);
lean_ctor_set(x_6, 1, x_3);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_6);
lean_ctor_set(x_66, 1, x_7);
x_21 = x_66;
goto block_39;
}
}
}
block_39:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = l_Std_Time_PlainTime_toSeconds(x_22);
x_24 = lean_int_add(x_23, x_18);
lean_dec(x_18);
lean_dec(x_23);
x_25 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_26 = lean_int_ediv(x_24, x_25);
lean_dec(x_24);
x_27 = l_Std_Time_PlainTime_toNanoseconds(x_22);
lean_dec(x_22);
x_28 = lean_int_add(x_27, x_20);
lean_dec(x_20);
lean_dec(x_27);
x_29 = l_Std_Time_PlainTime_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
x_31 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_30);
x_32 = lean_int_add(x_31, x_26);
lean_dec(x_26);
lean_dec(x_31);
x_33 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_32);
lean_dec(x_32);
if (lean_is_scalar(x_8)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_8;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_34);
x_36 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_21);
x_37 = lean_mk_thunk(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_6, 0);
x_68 = lean_ctor_get(x_6, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_6);
x_69 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_70 = lean_int_mod(x_67, x_69);
x_71 = l_Std_Time_instInhabitedDateTime___closed__2;
x_72 = lean_int_dec_eq(x_70, x_71);
lean_dec(x_70);
x_73 = lean_ctor_get(x_1, 0);
x_74 = lean_int_neg(x_73);
x_75 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_76 = lean_int_mul(x_74, x_75);
if (x_72 == 0)
{
uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_96 = 0;
x_97 = l_Std_Time_Month_Ordinal_days(x_96, x_3);
x_98 = lean_int_dec_lt(x_97, x_68);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_97);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_67);
lean_ctor_set(x_99, 1, x_3);
lean_ctor_set(x_99, 2, x_68);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_7);
x_77 = x_100;
goto block_95;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_68);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_67);
lean_ctor_set(x_101, 1, x_3);
lean_ctor_set(x_101, 2, x_97);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_7);
x_77 = x_102;
goto block_95;
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; 
x_103 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_104 = lean_int_mod(x_67, x_103);
x_105 = lean_int_dec_eq(x_104, x_71);
lean_dec(x_104);
x_106 = l_instDecidableNot___rarg(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_108 = lean_int_mod(x_67, x_107);
x_109 = lean_int_dec_eq(x_108, x_71);
lean_dec(x_108);
if (x_109 == 0)
{
uint8_t x_110; lean_object* x_111; uint8_t x_112; 
x_110 = 0;
x_111 = l_Std_Time_Month_Ordinal_days(x_110, x_3);
x_112 = lean_int_dec_lt(x_111, x_68);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_111);
x_113 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_113, 0, x_67);
lean_ctor_set(x_113, 1, x_3);
lean_ctor_set(x_113, 2, x_68);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_7);
x_77 = x_114;
goto block_95;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_68);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_67);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_115, 2, x_111);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_7);
x_77 = x_116;
goto block_95;
}
}
else
{
uint8_t x_117; lean_object* x_118; uint8_t x_119; 
x_117 = 1;
x_118 = l_Std_Time_Month_Ordinal_days(x_117, x_3);
x_119 = lean_int_dec_lt(x_118, x_68);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_118);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_67);
lean_ctor_set(x_120, 1, x_3);
lean_ctor_set(x_120, 2, x_68);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_7);
x_77 = x_121;
goto block_95;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_68);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_67);
lean_ctor_set(x_122, 1, x_3);
lean_ctor_set(x_122, 2, x_118);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_7);
x_77 = x_123;
goto block_95;
}
}
}
else
{
uint8_t x_124; lean_object* x_125; uint8_t x_126; 
x_124 = 1;
x_125 = l_Std_Time_Month_Ordinal_days(x_124, x_3);
x_126 = lean_int_dec_lt(x_125, x_68);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_67);
lean_ctor_set(x_127, 1, x_3);
lean_ctor_set(x_127, 2, x_68);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_7);
x_77 = x_128;
goto block_95;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_68);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_67);
lean_ctor_set(x_129, 1, x_3);
lean_ctor_set(x_129, 2, x_125);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
x_77 = x_130;
goto block_95;
}
}
}
block_95:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = l_Std_Time_PlainTime_toSeconds(x_78);
x_80 = lean_int_add(x_79, x_74);
lean_dec(x_74);
lean_dec(x_79);
x_81 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_82 = lean_int_ediv(x_80, x_81);
lean_dec(x_80);
x_83 = l_Std_Time_PlainTime_toNanoseconds(x_78);
lean_dec(x_78);
x_84 = lean_int_add(x_83, x_76);
lean_dec(x_76);
lean_dec(x_83);
x_85 = l_Std_Time_PlainTime_ofNanoseconds(x_84);
lean_dec(x_84);
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
x_87 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_86);
x_88 = lean_int_add(x_87, x_82);
lean_dec(x_82);
lean_dec(x_87);
x_89 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_88);
lean_dec(x_88);
if (lean_is_scalar(x_8)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_8;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
x_91 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_90);
x_92 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_92, 0, x_77);
x_93 = lean_mk_thunk(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withMonthClip(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Std_Time_PlainDate_rollOver(x_9, x_3, x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_ctor_set(x_5, 0, x_11);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_int_neg(x_12);
x_14 = l_Std_Time_PlainTime_toSeconds(x_8);
x_15 = lean_int_add(x_14, x_13);
lean_dec(x_14);
x_16 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_17 = lean_int_ediv(x_15, x_16);
lean_dec(x_15);
x_18 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_20 = lean_int_mul(x_13, x_19);
lean_dec(x_13);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_PlainTime_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_11);
x_24 = lean_int_add(x_23, x_17);
lean_dec(x_17);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_28, 0, x_5);
x_29 = lean_mk_thunk(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Std_Time_PlainDate_rollOver(x_33, x_3, x_34);
lean_dec(x_34);
lean_inc(x_32);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_int_neg(x_37);
x_39 = l_Std_Time_PlainTime_toSeconds(x_32);
x_40 = lean_int_add(x_39, x_38);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_42 = lean_int_ediv(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_PlainTime_toNanoseconds(x_32);
lean_dec(x_32);
x_44 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_45 = lean_int_mul(x_38, x_44);
lean_dec(x_38);
x_46 = lean_int_add(x_43, x_45);
lean_dec(x_45);
lean_dec(x_43);
x_47 = l_Std_Time_PlainTime_ofNanoseconds(x_46);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_35);
x_49 = lean_int_add(x_48, x_42);
lean_dec(x_42);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_51);
x_53 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_53, 0, x_36);
x_54 = lean_mk_thunk(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withMonthRollOver(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 2);
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
x_13 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_14 = lean_int_mod(x_3, x_13);
x_15 = l_Std_Time_instInhabitedDateTime___closed__2;
x_16 = lean_int_dec_eq(x_14, x_15);
lean_dec(x_14);
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_int_neg(x_17);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_20 = lean_int_mul(x_18, x_19);
if (x_16 == 0)
{
uint8_t x_40; lean_object* x_41; uint8_t x_42; 
x_40 = 0;
x_41 = l_Std_Time_Month_Ordinal_days(x_40, x_10);
x_42 = lean_int_dec_lt(x_41, x_11);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
lean_ctor_set(x_6, 0, x_3);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_7);
x_21 = x_43;
goto block_39;
}
else
{
lean_object* x_44; 
lean_dec(x_11);
lean_ctor_set(x_6, 2, x_41);
lean_ctor_set(x_6, 0, x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_7);
x_21 = x_44;
goto block_39;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; 
x_45 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_46 = lean_int_mod(x_3, x_45);
x_47 = lean_int_dec_eq(x_46, x_15);
lean_dec(x_46);
x_48 = l_instDecidableNot___rarg(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_50 = lean_int_mod(x_3, x_49);
x_51 = lean_int_dec_eq(x_50, x_15);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; lean_object* x_53; uint8_t x_54; 
x_52 = 0;
x_53 = l_Std_Time_Month_Ordinal_days(x_52, x_10);
x_54 = lean_int_dec_lt(x_53, x_11);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_ctor_set(x_6, 0, x_3);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_7);
x_21 = x_55;
goto block_39;
}
else
{
lean_object* x_56; 
lean_dec(x_11);
lean_ctor_set(x_6, 2, x_53);
lean_ctor_set(x_6, 0, x_3);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_7);
x_21 = x_56;
goto block_39;
}
}
else
{
uint8_t x_57; lean_object* x_58; uint8_t x_59; 
x_57 = 1;
x_58 = l_Std_Time_Month_Ordinal_days(x_57, x_10);
x_59 = lean_int_dec_lt(x_58, x_11);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_58);
lean_ctor_set(x_6, 0, x_3);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_6);
lean_ctor_set(x_60, 1, x_7);
x_21 = x_60;
goto block_39;
}
else
{
lean_object* x_61; 
lean_dec(x_11);
lean_ctor_set(x_6, 2, x_58);
lean_ctor_set(x_6, 0, x_3);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_6);
lean_ctor_set(x_61, 1, x_7);
x_21 = x_61;
goto block_39;
}
}
}
else
{
uint8_t x_62; lean_object* x_63; uint8_t x_64; 
x_62 = 1;
x_63 = l_Std_Time_Month_Ordinal_days(x_62, x_10);
x_64 = lean_int_dec_lt(x_63, x_11);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_63);
lean_ctor_set(x_6, 0, x_3);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_7);
x_21 = x_65;
goto block_39;
}
else
{
lean_object* x_66; 
lean_dec(x_11);
lean_ctor_set(x_6, 2, x_63);
lean_ctor_set(x_6, 0, x_3);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_6);
lean_ctor_set(x_66, 1, x_7);
x_21 = x_66;
goto block_39;
}
}
}
block_39:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = l_Std_Time_PlainTime_toSeconds(x_22);
x_24 = lean_int_add(x_23, x_18);
lean_dec(x_18);
lean_dec(x_23);
x_25 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_26 = lean_int_ediv(x_24, x_25);
lean_dec(x_24);
x_27 = l_Std_Time_PlainTime_toNanoseconds(x_22);
lean_dec(x_22);
x_28 = lean_int_add(x_27, x_20);
lean_dec(x_20);
lean_dec(x_27);
x_29 = l_Std_Time_PlainTime_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
x_31 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_30);
x_32 = lean_int_add(x_31, x_26);
lean_dec(x_26);
lean_dec(x_31);
x_33 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_32);
lean_dec(x_32);
if (lean_is_scalar(x_8)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_8;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
x_35 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_34);
x_36 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_21);
x_37 = lean_mk_thunk(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_67 = lean_ctor_get(x_6, 1);
x_68 = lean_ctor_get(x_6, 2);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_6);
x_69 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_70 = lean_int_mod(x_3, x_69);
x_71 = l_Std_Time_instInhabitedDateTime___closed__2;
x_72 = lean_int_dec_eq(x_70, x_71);
lean_dec(x_70);
x_73 = lean_ctor_get(x_1, 0);
x_74 = lean_int_neg(x_73);
x_75 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_76 = lean_int_mul(x_74, x_75);
if (x_72 == 0)
{
uint8_t x_96; lean_object* x_97; uint8_t x_98; 
x_96 = 0;
x_97 = l_Std_Time_Month_Ordinal_days(x_96, x_67);
x_98 = lean_int_dec_lt(x_97, x_68);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_97);
x_99 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_99, 0, x_3);
lean_ctor_set(x_99, 1, x_67);
lean_ctor_set(x_99, 2, x_68);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_7);
x_77 = x_100;
goto block_95;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_68);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_3);
lean_ctor_set(x_101, 1, x_67);
lean_ctor_set(x_101, 2, x_97);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_7);
x_77 = x_102;
goto block_95;
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; 
x_103 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_104 = lean_int_mod(x_3, x_103);
x_105 = lean_int_dec_eq(x_104, x_71);
lean_dec(x_104);
x_106 = l_instDecidableNot___rarg(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_108 = lean_int_mod(x_3, x_107);
x_109 = lean_int_dec_eq(x_108, x_71);
lean_dec(x_108);
if (x_109 == 0)
{
uint8_t x_110; lean_object* x_111; uint8_t x_112; 
x_110 = 0;
x_111 = l_Std_Time_Month_Ordinal_days(x_110, x_67);
x_112 = lean_int_dec_lt(x_111, x_68);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_111);
x_113 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_113, 0, x_3);
lean_ctor_set(x_113, 1, x_67);
lean_ctor_set(x_113, 2, x_68);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_7);
x_77 = x_114;
goto block_95;
}
else
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_68);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_3);
lean_ctor_set(x_115, 1, x_67);
lean_ctor_set(x_115, 2, x_111);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_7);
x_77 = x_116;
goto block_95;
}
}
else
{
uint8_t x_117; lean_object* x_118; uint8_t x_119; 
x_117 = 1;
x_118 = l_Std_Time_Month_Ordinal_days(x_117, x_67);
x_119 = lean_int_dec_lt(x_118, x_68);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_118);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_3);
lean_ctor_set(x_120, 1, x_67);
lean_ctor_set(x_120, 2, x_68);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_7);
x_77 = x_121;
goto block_95;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_68);
x_122 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_122, 0, x_3);
lean_ctor_set(x_122, 1, x_67);
lean_ctor_set(x_122, 2, x_118);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_7);
x_77 = x_123;
goto block_95;
}
}
}
else
{
uint8_t x_124; lean_object* x_125; uint8_t x_126; 
x_124 = 1;
x_125 = l_Std_Time_Month_Ordinal_days(x_124, x_67);
x_126 = lean_int_dec_lt(x_125, x_68);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_125);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_3);
lean_ctor_set(x_127, 1, x_67);
lean_ctor_set(x_127, 2, x_68);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_7);
x_77 = x_128;
goto block_95;
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_68);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_3);
lean_ctor_set(x_129, 1, x_67);
lean_ctor_set(x_129, 2, x_125);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_7);
x_77 = x_130;
goto block_95;
}
}
}
block_95:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = l_Std_Time_PlainTime_toSeconds(x_78);
x_80 = lean_int_add(x_79, x_74);
lean_dec(x_74);
lean_dec(x_79);
x_81 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_82 = lean_int_ediv(x_80, x_81);
lean_dec(x_80);
x_83 = l_Std_Time_PlainTime_toNanoseconds(x_78);
lean_dec(x_78);
x_84 = lean_int_add(x_83, x_76);
lean_dec(x_76);
lean_dec(x_83);
x_85 = l_Std_Time_PlainTime_ofNanoseconds(x_84);
lean_dec(x_84);
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
x_87 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_86);
x_88 = lean_int_add(x_87, x_82);
lean_dec(x_82);
lean_dec(x_87);
x_89 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_88);
lean_dec(x_88);
if (lean_is_scalar(x_8)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_8;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_85);
x_91 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_90);
x_92 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_92, 0, x_77);
x_93 = lean_mk_thunk(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withYearClip(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Std_Time_PlainDate_rollOver(x_3, x_9, x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_11);
lean_ctor_set(x_5, 0, x_11);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_int_neg(x_12);
x_14 = l_Std_Time_PlainTime_toSeconds(x_8);
x_15 = lean_int_add(x_14, x_13);
lean_dec(x_14);
x_16 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_17 = lean_int_ediv(x_15, x_16);
lean_dec(x_15);
x_18 = l_Std_Time_PlainTime_toNanoseconds(x_8);
lean_dec(x_8);
x_19 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_20 = lean_int_mul(x_13, x_19);
lean_dec(x_13);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_PlainTime_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_11);
x_24 = lean_int_add(x_23, x_17);
lean_dec(x_17);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_28, 0, x_5);
x_29 = lean_mk_thunk(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 2);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Std_Time_PlainDate_rollOver(x_3, x_33, x_34);
lean_dec(x_34);
lean_inc(x_32);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_int_neg(x_37);
x_39 = l_Std_Time_PlainTime_toSeconds(x_32);
x_40 = lean_int_add(x_39, x_38);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_42 = lean_int_ediv(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_PlainTime_toNanoseconds(x_32);
lean_dec(x_32);
x_44 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_45 = lean_int_mul(x_38, x_44);
lean_dec(x_38);
x_46 = lean_int_add(x_43, x_45);
lean_dec(x_45);
lean_dec(x_43);
x_47 = l_Std_Time_PlainTime_ofNanoseconds(x_46);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_35);
x_49 = lean_int_add(x_48, x_42);
lean_dec(x_42);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
x_52 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_51);
x_53 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_53, 0, x_36);
x_54 = lean_mk_thunk(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withYearRollOver(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_3);
lean_inc(x_7);
lean_inc(x_9);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_int_neg(x_11);
x_13 = l_Std_Time_PlainTime_toSeconds(x_7);
x_14 = lean_int_add(x_13, x_12);
lean_dec(x_13);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_16 = lean_int_ediv(x_14, x_15);
lean_dec(x_14);
x_17 = l_Std_Time_PlainTime_toNanoseconds(x_7);
lean_dec(x_7);
x_18 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_19 = lean_int_mul(x_12, x_18);
lean_dec(x_12);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_PlainTime_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_9);
x_23 = lean_int_add(x_22, x_16);
lean_dec(x_16);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_25);
x_27 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_5);
x_28 = lean_mk_thunk(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_7, 1);
x_32 = lean_ctor_get(x_7, 2);
x_33 = lean_ctor_get(x_7, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_34);
lean_inc(x_30);
lean_ctor_set(x_5, 1, x_34);
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_int_neg(x_35);
x_37 = l_Std_Time_PlainTime_toSeconds(x_34);
x_38 = lean_int_add(x_37, x_36);
lean_dec(x_37);
x_39 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_40 = lean_int_ediv(x_38, x_39);
lean_dec(x_38);
x_41 = l_Std_Time_PlainTime_toNanoseconds(x_34);
lean_dec(x_34);
x_42 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_43 = lean_int_mul(x_36, x_42);
lean_dec(x_36);
x_44 = lean_int_add(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
x_45 = l_Std_Time_PlainTime_ofNanoseconds(x_44);
lean_dec(x_44);
x_46 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_30);
x_47 = lean_int_add(x_46, x_40);
lean_dec(x_40);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_51, 0, x_5);
x_52 = lean_mk_thunk(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_54 = lean_ctor_get(x_5, 1);
x_55 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
lean_inc(x_55);
lean_dec(x_5);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 3);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 4, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_58);
lean_inc(x_60);
lean_inc(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_int_neg(x_62);
x_64 = l_Std_Time_PlainTime_toSeconds(x_60);
x_65 = lean_int_add(x_64, x_63);
lean_dec(x_64);
x_66 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_67 = lean_int_ediv(x_65, x_66);
lean_dec(x_65);
x_68 = l_Std_Time_PlainTime_toNanoseconds(x_60);
lean_dec(x_60);
x_69 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_70 = lean_int_mul(x_63, x_69);
lean_dec(x_63);
x_71 = lean_int_add(x_68, x_70);
lean_dec(x_70);
lean_dec(x_68);
x_72 = l_Std_Time_PlainTime_ofNanoseconds(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_55);
x_74 = lean_int_add(x_73, x_67);
lean_dec(x_67);
lean_dec(x_73);
x_75 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
x_77 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_76);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_78, 0, x_61);
x_79 = lean_mk_thunk(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withHours(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
lean_ctor_set(x_7, 1, x_3);
lean_inc(x_7);
lean_inc(x_9);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_int_neg(x_11);
x_13 = l_Std_Time_PlainTime_toSeconds(x_7);
x_14 = lean_int_add(x_13, x_12);
lean_dec(x_13);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_16 = lean_int_ediv(x_14, x_15);
lean_dec(x_14);
x_17 = l_Std_Time_PlainTime_toNanoseconds(x_7);
lean_dec(x_7);
x_18 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_19 = lean_int_mul(x_12, x_18);
lean_dec(x_12);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_PlainTime_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_9);
x_23 = lean_int_add(x_22, x_16);
lean_dec(x_16);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_25);
x_27 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_5);
x_28 = lean_mk_thunk(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 2);
x_33 = lean_ctor_get(x_7, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_3);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_34);
lean_inc(x_30);
lean_ctor_set(x_5, 1, x_34);
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_int_neg(x_35);
x_37 = l_Std_Time_PlainTime_toSeconds(x_34);
x_38 = lean_int_add(x_37, x_36);
lean_dec(x_37);
x_39 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_40 = lean_int_ediv(x_38, x_39);
lean_dec(x_38);
x_41 = l_Std_Time_PlainTime_toNanoseconds(x_34);
lean_dec(x_34);
x_42 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_43 = lean_int_mul(x_36, x_42);
lean_dec(x_36);
x_44 = lean_int_add(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
x_45 = l_Std_Time_PlainTime_ofNanoseconds(x_44);
lean_dec(x_44);
x_46 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_30);
x_47 = lean_int_add(x_46, x_40);
lean_dec(x_40);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_51, 0, x_5);
x_52 = lean_mk_thunk(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_54 = lean_ctor_get(x_5, 1);
x_55 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
lean_inc(x_55);
lean_dec(x_5);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 3);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 4, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_3);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_58);
lean_inc(x_60);
lean_inc(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_int_neg(x_62);
x_64 = l_Std_Time_PlainTime_toSeconds(x_60);
x_65 = lean_int_add(x_64, x_63);
lean_dec(x_64);
x_66 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_67 = lean_int_ediv(x_65, x_66);
lean_dec(x_65);
x_68 = l_Std_Time_PlainTime_toNanoseconds(x_60);
lean_dec(x_60);
x_69 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_70 = lean_int_mul(x_63, x_69);
lean_dec(x_63);
x_71 = lean_int_add(x_68, x_70);
lean_dec(x_70);
lean_dec(x_68);
x_72 = l_Std_Time_PlainTime_ofNanoseconds(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_55);
x_74 = lean_int_add(x_73, x_67);
lean_dec(x_67);
lean_dec(x_73);
x_75 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
x_77 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_76);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_78, 0, x_61);
x_79 = lean_mk_thunk(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withMinutes(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_7, 2);
lean_dec(x_10);
lean_ctor_set(x_7, 2, x_3);
lean_inc(x_7);
lean_inc(x_9);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_int_neg(x_11);
x_13 = l_Std_Time_PlainTime_toSeconds(x_7);
x_14 = lean_int_add(x_13, x_12);
lean_dec(x_13);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_16 = lean_int_ediv(x_14, x_15);
lean_dec(x_14);
x_17 = l_Std_Time_PlainTime_toNanoseconds(x_7);
lean_dec(x_7);
x_18 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_19 = lean_int_mul(x_12, x_18);
lean_dec(x_12);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_PlainTime_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_9);
x_23 = lean_int_add(x_22, x_16);
lean_dec(x_16);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_25);
x_27 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_5);
x_28 = lean_mk_thunk(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
x_33 = lean_ctor_get(x_7, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_3);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_34);
lean_inc(x_30);
lean_ctor_set(x_5, 1, x_34);
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_int_neg(x_35);
x_37 = l_Std_Time_PlainTime_toSeconds(x_34);
x_38 = lean_int_add(x_37, x_36);
lean_dec(x_37);
x_39 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_40 = lean_int_ediv(x_38, x_39);
lean_dec(x_38);
x_41 = l_Std_Time_PlainTime_toNanoseconds(x_34);
lean_dec(x_34);
x_42 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_43 = lean_int_mul(x_36, x_42);
lean_dec(x_36);
x_44 = lean_int_add(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
x_45 = l_Std_Time_PlainTime_ofNanoseconds(x_44);
lean_dec(x_44);
x_46 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_30);
x_47 = lean_int_add(x_46, x_40);
lean_dec(x_40);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_51, 0, x_5);
x_52 = lean_mk_thunk(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_54 = lean_ctor_get(x_5, 1);
x_55 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
lean_inc(x_55);
lean_dec(x_5);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 3);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 4, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_3);
lean_ctor_set(x_60, 3, x_58);
lean_inc(x_60);
lean_inc(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_int_neg(x_62);
x_64 = l_Std_Time_PlainTime_toSeconds(x_60);
x_65 = lean_int_add(x_64, x_63);
lean_dec(x_64);
x_66 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_67 = lean_int_ediv(x_65, x_66);
lean_dec(x_65);
x_68 = l_Std_Time_PlainTime_toNanoseconds(x_60);
lean_dec(x_60);
x_69 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_70 = lean_int_mul(x_63, x_69);
lean_dec(x_63);
x_71 = lean_int_add(x_68, x_70);
lean_dec(x_70);
lean_dec(x_68);
x_72 = l_Std_Time_PlainTime_ofNanoseconds(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_55);
x_74 = lean_int_add(x_73, x_67);
lean_dec(x_67);
lean_dec(x_73);
x_75 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
x_77 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_76);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_78, 0, x_61);
x_79 = lean_mk_thunk(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withSeconds(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_7, 3);
lean_dec(x_10);
lean_ctor_set(x_7, 3, x_3);
lean_inc(x_7);
lean_inc(x_9);
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_int_neg(x_11);
x_13 = l_Std_Time_PlainTime_toSeconds(x_7);
x_14 = lean_int_add(x_13, x_12);
lean_dec(x_13);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_16 = lean_int_ediv(x_14, x_15);
lean_dec(x_14);
x_17 = l_Std_Time_PlainTime_toNanoseconds(x_7);
lean_dec(x_7);
x_18 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_19 = lean_int_mul(x_12, x_18);
lean_dec(x_12);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_PlainTime_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_9);
x_23 = lean_int_add(x_22, x_16);
lean_dec(x_16);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_25);
x_27 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_5);
x_28 = lean_mk_thunk(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
x_33 = lean_ctor_get(x_7, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set(x_34, 3, x_3);
lean_inc(x_34);
lean_inc(x_30);
lean_ctor_set(x_5, 1, x_34);
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_int_neg(x_35);
x_37 = l_Std_Time_PlainTime_toSeconds(x_34);
x_38 = lean_int_add(x_37, x_36);
lean_dec(x_37);
x_39 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_40 = lean_int_ediv(x_38, x_39);
lean_dec(x_38);
x_41 = l_Std_Time_PlainTime_toNanoseconds(x_34);
lean_dec(x_34);
x_42 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_43 = lean_int_mul(x_36, x_42);
lean_dec(x_36);
x_44 = lean_int_add(x_41, x_43);
lean_dec(x_43);
lean_dec(x_41);
x_45 = l_Std_Time_PlainTime_ofNanoseconds(x_44);
lean_dec(x_44);
x_46 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_30);
x_47 = lean_int_add(x_46, x_40);
lean_dec(x_40);
lean_dec(x_46);
x_48 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_51, 0, x_5);
x_52 = lean_mk_thunk(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_54 = lean_ctor_get(x_5, 1);
x_55 = lean_ctor_get(x_5, 0);
lean_inc(x_54);
lean_inc(x_55);
lean_dec(x_5);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 2);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 lean_ctor_release(x_54, 3);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 4, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_3);
lean_inc(x_60);
lean_inc(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_ctor_get(x_1, 0);
x_63 = lean_int_neg(x_62);
x_64 = l_Std_Time_PlainTime_toSeconds(x_60);
x_65 = lean_int_add(x_64, x_63);
lean_dec(x_64);
x_66 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_67 = lean_int_ediv(x_65, x_66);
lean_dec(x_65);
x_68 = l_Std_Time_PlainTime_toNanoseconds(x_60);
lean_dec(x_60);
x_69 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_70 = lean_int_mul(x_63, x_69);
lean_dec(x_63);
x_71 = lean_int_add(x_68, x_70);
lean_dec(x_70);
lean_dec(x_68);
x_72 = l_Std_Time_PlainTime_ofNanoseconds(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_55);
x_74 = lean_int_add(x_73, x_67);
lean_dec(x_67);
lean_dec(x_73);
x_75 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
x_77 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_76);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_78, 0, x_61);
x_79 = lean_mk_thunk(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withNanoseconds(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_withMilliseconds___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_withMilliseconds___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_7, 3);
x_11 = l_Std_Time_DateTime_withMilliseconds___closed__1;
x_12 = lean_int_emod(x_10, x_11);
lean_dec(x_10);
x_13 = l_Std_Time_DateTime_withMilliseconds___closed__2;
x_14 = lean_int_mul(x_3, x_13);
x_15 = lean_int_add(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
lean_ctor_set(x_7, 3, x_15);
lean_inc(x_7);
lean_inc(x_9);
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_int_neg(x_16);
x_18 = l_Std_Time_PlainTime_toSeconds(x_7);
x_19 = lean_int_add(x_18, x_17);
lean_dec(x_18);
x_20 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_21 = lean_int_ediv(x_19, x_20);
lean_dec(x_19);
x_22 = l_Std_Time_PlainTime_toNanoseconds(x_7);
lean_dec(x_7);
x_23 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_24 = lean_int_mul(x_17, x_23);
lean_dec(x_17);
x_25 = lean_int_add(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
x_26 = l_Std_Time_PlainTime_ofNanoseconds(x_25);
lean_dec(x_25);
x_27 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_9);
x_28 = lean_int_add(x_27, x_21);
lean_dec(x_21);
lean_dec(x_27);
x_29 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
x_31 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_30);
x_32 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_5);
x_33 = lean_mk_thunk(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_35 = lean_ctor_get(x_5, 0);
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
x_38 = lean_ctor_get(x_7, 2);
x_39 = lean_ctor_get(x_7, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_40 = l_Std_Time_DateTime_withMilliseconds___closed__1;
x_41 = lean_int_emod(x_39, x_40);
lean_dec(x_39);
x_42 = l_Std_Time_DateTime_withMilliseconds___closed__2;
x_43 = lean_int_mul(x_3, x_42);
x_44 = lean_int_add(x_43, x_41);
lean_dec(x_41);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_38);
lean_ctor_set(x_45, 3, x_44);
lean_inc(x_45);
lean_inc(x_35);
lean_ctor_set(x_5, 1, x_45);
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_int_neg(x_46);
x_48 = l_Std_Time_PlainTime_toSeconds(x_45);
x_49 = lean_int_add(x_48, x_47);
lean_dec(x_48);
x_50 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_51 = lean_int_ediv(x_49, x_50);
lean_dec(x_49);
x_52 = l_Std_Time_PlainTime_toNanoseconds(x_45);
lean_dec(x_45);
x_53 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_54 = lean_int_mul(x_47, x_53);
lean_dec(x_47);
x_55 = lean_int_add(x_52, x_54);
lean_dec(x_54);
lean_dec(x_52);
x_56 = l_Std_Time_PlainTime_ofNanoseconds(x_55);
lean_dec(x_55);
x_57 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_35);
x_58 = lean_int_add(x_57, x_51);
lean_dec(x_51);
lean_dec(x_57);
x_59 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
x_61 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_60);
x_62 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_62, 0, x_5);
x_63 = lean_mk_thunk(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_65 = lean_ctor_get(x_5, 1);
x_66 = lean_ctor_get(x_5, 0);
lean_inc(x_65);
lean_inc(x_66);
lean_dec(x_5);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc(x_70);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 x_71 = x_65;
} else {
 lean_dec_ref(x_65);
 x_71 = lean_box(0);
}
x_72 = l_Std_Time_DateTime_withMilliseconds___closed__1;
x_73 = lean_int_emod(x_70, x_72);
lean_dec(x_70);
x_74 = l_Std_Time_DateTime_withMilliseconds___closed__2;
x_75 = lean_int_mul(x_3, x_74);
x_76 = lean_int_add(x_75, x_73);
lean_dec(x_73);
lean_dec(x_75);
if (lean_is_scalar(x_71)) {
 x_77 = lean_alloc_ctor(0, 4, 0);
} else {
 x_77 = x_71;
}
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_69);
lean_ctor_set(x_77, 3, x_76);
lean_inc(x_77);
lean_inc(x_66);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_66);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_ctor_get(x_1, 0);
x_80 = lean_int_neg(x_79);
x_81 = l_Std_Time_PlainTime_toSeconds(x_77);
x_82 = lean_int_add(x_81, x_80);
lean_dec(x_81);
x_83 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_84 = lean_int_ediv(x_82, x_83);
lean_dec(x_82);
x_85 = l_Std_Time_PlainTime_toNanoseconds(x_77);
lean_dec(x_77);
x_86 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_87 = lean_int_mul(x_80, x_86);
lean_dec(x_80);
x_88 = lean_int_add(x_85, x_87);
lean_dec(x_87);
lean_dec(x_85);
x_89 = l_Std_Time_PlainTime_ofNanoseconds(x_88);
lean_dec(x_88);
x_90 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_66);
x_91 = lean_int_add(x_90, x_84);
lean_dec(x_84);
lean_dec(x_90);
x_92 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
x_94 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_93);
x_95 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_95, 0, x_78);
x_96 = lean_mk_thunk(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withMilliseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_toPlainDateTime___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toPlainDateTime___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toPlainDateTime(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_year___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_year___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_year(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_month___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_month___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_month(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_day___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_day___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_day(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_hour___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_hour___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_hour(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_minute___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_minute___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_minute(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_second___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_second___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_second(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_Time_DateTime_withMilliseconds___closed__1;
x_7 = lean_int_emod(x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_millisecond___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_millisecond___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_millisecond(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_nanosecond___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_nanosecond___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_nanosecond(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_weekday(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_weekday___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_DateTime_weekday___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_weekday(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_Time_Year_Offset_era(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_era___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_DateTime_era___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_era(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_thunk_get_own(x_4);
lean_inc(x_5);
x_6 = l_Std_Time_PlainDateTime_withWeekday(x_5, x_3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_int_neg(x_7);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = l_Std_Time_PlainTime_toSeconds(x_9);
x_11 = lean_int_add(x_10, x_8);
lean_dec(x_10);
x_12 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_13 = lean_int_ediv(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_PlainTime_toNanoseconds(x_9);
lean_dec(x_9);
x_15 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_16 = lean_int_mul(x_8, x_15);
lean_dec(x_8);
x_17 = lean_int_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = l_Std_Time_PlainTime_ofNanoseconds(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_19);
x_21 = lean_int_add(x_20, x_13);
lean_dec(x_13);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
x_24 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_23);
x_25 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_6);
x_26 = lean_mk_thunk(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Std_Time_DateTime_withWeekday(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_7 = lean_int_mod(x_5, x_6);
x_8 = l_Std_Time_instInhabitedDateTime___closed__2;
x_9 = lean_int_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_11 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_12 = lean_int_mod(x_5, x_11);
x_13 = lean_int_dec_eq(x_12, x_8);
lean_dec(x_12);
x_14 = l_instDecidableNot___rarg(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_16 = lean_int_mod(x_5, x_15);
lean_dec(x_5);
x_17 = lean_int_dec_eq(x_16, x_8);
lean_dec(x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
x_18 = 1;
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_inLeapYear___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_DateTime_inLeapYear___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_inLeapYear(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_7 = lean_int_mod(x_5, x_6);
x_8 = l_Std_Time_instInhabitedDateTime___closed__2;
x_9 = lean_int_dec_eq(x_7, x_8);
lean_dec(x_7);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
if (x_9 == 0)
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_5);
x_13 = 0;
x_14 = l_Std_Time_ValidDate_dayOfYear(x_13, x_12);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_15 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_16 = lean_int_mod(x_5, x_15);
x_17 = lean_int_dec_eq(x_16, x_8);
lean_dec(x_16);
x_18 = l_instDecidableNot___rarg(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_20 = lean_int_mod(x_5, x_19);
lean_dec(x_5);
x_21 = lean_int_dec_eq(x_20, x_8);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; lean_object* x_23; 
x_22 = 0;
x_23 = l_Std_Time_ValidDate_dayOfYear(x_22, x_12);
lean_dec(x_12);
return x_23;
}
else
{
uint8_t x_24; lean_object* x_25; 
x_24 = 1;
x_25 = l_Std_Time_ValidDate_dayOfYear(x_24, x_12);
lean_dec(x_12);
return x_25;
}
}
else
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_5);
x_26 = 1;
x_27 = l_Std_Time_ValidDate_dayOfYear(x_26, x_12);
lean_dec(x_12);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_dayOfYear___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_dayOfYear___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_dayOfYear(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_weekOfYear(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_weekOfYear___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_weekOfYear___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_weekOfYear(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = l_Std_Time_PlainDateTime_weekOfMonth(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_weekOfMonth___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_weekOfMonth___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_weekOfMonth(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_alignedWeekOfMonth(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_alignedWeekOfMonth___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_alignedWeekOfMonth___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_alignedWeekOfMonth(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_quarter(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_quarter___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_quarter___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_quarter(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_time___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_time___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_time(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_4 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_1);
lean_inc(x_2);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_int_neg(x_6);
x_8 = l_Std_Time_PlainTime_toSeconds(x_2);
x_9 = lean_int_add(x_8, x_7);
lean_dec(x_8);
x_10 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_11 = lean_int_ediv(x_9, x_10);
lean_dec(x_9);
x_12 = l_Std_Time_PlainTime_toNanoseconds(x_2);
lean_dec(x_2);
x_13 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_14 = lean_int_mul(x_7, x_13);
lean_dec(x_7);
x_15 = lean_int_add(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_Std_Time_PlainTime_ofNanoseconds(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_4);
x_18 = lean_int_add(x_17, x_11);
lean_dec(x_11);
lean_dec(x_17);
x_19 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
x_21 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_20);
x_22 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_22, 0, x_5);
x_23 = lean_mk_thunk(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_ofDaysSinceUNIXEpoch(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_subDays___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addWeeks___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_subWeeks___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_subHours___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMinutes___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_subMinutes___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addSeconds___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_subSeconds___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_subMilliseconds___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addNanoseconds___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_subNanoseconds___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_int_neg(x_5);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_int_neg(x_7);
x_9 = lean_ctor_get(x_3, 0);
x_10 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_11 = lean_int_mul(x_9, x_10);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_int_add(x_11, x_12);
lean_dec(x_11);
x_14 = lean_int_mul(x_6, x_10);
lean_dec(x_6);
x_15 = lean_int_add(x_14, x_8);
lean_dec(x_8);
lean_dec(x_14);
x_16 = lean_int_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_16);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHSubDuration___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_instHSubDuration___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_instHSubDuration(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_6 = lean_int_mul(x_4, x_5);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_int_add(x_6, x_7);
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_thunk_get_own(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_int_add(x_14, x_8);
lean_dec(x_8);
lean_dec(x_14);
x_16 = lean_int_ediv(x_15, x_5);
x_17 = lean_int_emod(x_15, x_5);
lean_dec(x_15);
x_18 = l_Std_Time_PlainTime_toNanoseconds(x_13);
lean_dec(x_13);
x_19 = lean_int_mul(x_16, x_5);
lean_dec(x_16);
x_20 = lean_int_add(x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
x_21 = l_Std_Time_PlainTime_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_21, 3);
lean_dec(x_23);
lean_ctor_set(x_21, 3, x_17);
lean_inc(x_21);
lean_inc(x_12);
lean_ctor_set(x_10, 1, x_21);
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_int_neg(x_24);
x_26 = l_Std_Time_PlainTime_toSeconds(x_21);
x_27 = lean_int_add(x_26, x_25);
lean_dec(x_26);
x_28 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_29 = lean_int_ediv(x_27, x_28);
lean_dec(x_27);
x_30 = l_Std_Time_PlainTime_toNanoseconds(x_21);
lean_dec(x_21);
x_31 = lean_int_mul(x_25, x_5);
lean_dec(x_25);
x_32 = lean_int_add(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
x_33 = l_Std_Time_PlainTime_ofNanoseconds(x_32);
lean_dec(x_32);
x_34 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_12);
x_35 = lean_int_add(x_34, x_29);
lean_dec(x_29);
lean_dec(x_34);
x_36 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
x_38 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_37);
x_39 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_39, 0, x_10);
x_40 = lean_mk_thunk(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_21, 1);
x_44 = lean_ctor_get(x_21, 2);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_21);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_17);
lean_inc(x_45);
lean_inc(x_12);
lean_ctor_set(x_10, 1, x_45);
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_int_neg(x_46);
x_48 = l_Std_Time_PlainTime_toSeconds(x_45);
x_49 = lean_int_add(x_48, x_47);
lean_dec(x_48);
x_50 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_51 = lean_int_ediv(x_49, x_50);
lean_dec(x_49);
x_52 = l_Std_Time_PlainTime_toNanoseconds(x_45);
lean_dec(x_45);
x_53 = lean_int_mul(x_47, x_5);
lean_dec(x_47);
x_54 = lean_int_add(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
x_55 = l_Std_Time_PlainTime_ofNanoseconds(x_54);
lean_dec(x_54);
x_56 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_12);
x_57 = lean_int_add(x_56, x_51);
lean_dec(x_51);
lean_dec(x_56);
x_58 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
x_60 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_59);
x_61 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_61, 0, x_10);
x_62 = lean_mk_thunk(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_64 = lean_ctor_get(x_10, 0);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_10);
x_66 = lean_ctor_get(x_65, 3);
lean_inc(x_66);
x_67 = lean_int_add(x_66, x_8);
lean_dec(x_8);
lean_dec(x_66);
x_68 = lean_int_ediv(x_67, x_5);
x_69 = lean_int_emod(x_67, x_5);
lean_dec(x_67);
x_70 = l_Std_Time_PlainTime_toNanoseconds(x_65);
lean_dec(x_65);
x_71 = lean_int_mul(x_68, x_5);
lean_dec(x_68);
x_72 = lean_int_add(x_70, x_71);
lean_dec(x_71);
lean_dec(x_70);
x_73 = l_Std_Time_PlainTime_ofNanoseconds(x_72);
lean_dec(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 2);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 lean_ctor_release(x_73, 2);
 lean_ctor_release(x_73, 3);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 4, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_76);
lean_ctor_set(x_78, 3, x_69);
lean_inc(x_78);
lean_inc(x_64);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_64);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_ctor_get(x_1, 0);
x_81 = lean_int_neg(x_80);
x_82 = l_Std_Time_PlainTime_toSeconds(x_78);
x_83 = lean_int_add(x_82, x_81);
lean_dec(x_82);
x_84 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_85 = lean_int_ediv(x_83, x_84);
lean_dec(x_83);
x_86 = l_Std_Time_PlainTime_toNanoseconds(x_78);
lean_dec(x_78);
x_87 = lean_int_mul(x_81, x_5);
lean_dec(x_81);
x_88 = lean_int_add(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
x_89 = l_Std_Time_PlainTime_ofNanoseconds(x_88);
lean_dec(x_88);
x_90 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_64);
x_91 = lean_int_add(x_90, x_85);
lean_dec(x_85);
lean_dec(x_90);
x_92 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
x_94 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_93);
x_95 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_95, 0, x_79);
x_96 = lean_mk_thunk(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_instHAddDuration(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2;
x_6 = lean_int_mul(x_4, x_5);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_int_add(x_6, x_7);
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_thunk_get_own(x_9);
x_11 = lean_int_neg(x_8);
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_int_add(x_15, x_11);
lean_dec(x_11);
lean_dec(x_15);
x_17 = lean_int_ediv(x_16, x_5);
x_18 = lean_int_emod(x_16, x_5);
lean_dec(x_16);
x_19 = l_Std_Time_PlainTime_toNanoseconds(x_14);
lean_dec(x_14);
x_20 = lean_int_mul(x_17, x_5);
lean_dec(x_17);
x_21 = lean_int_add(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = l_Std_Time_PlainTime_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = lean_ctor_get(x_22, 3);
lean_dec(x_24);
lean_ctor_set(x_22, 3, x_18);
lean_inc(x_22);
lean_inc(x_13);
lean_ctor_set(x_10, 1, x_22);
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_int_neg(x_25);
x_27 = l_Std_Time_PlainTime_toSeconds(x_22);
x_28 = lean_int_add(x_27, x_26);
lean_dec(x_27);
x_29 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_30 = lean_int_ediv(x_28, x_29);
lean_dec(x_28);
x_31 = l_Std_Time_PlainTime_toNanoseconds(x_22);
lean_dec(x_22);
x_32 = lean_int_mul(x_26, x_5);
lean_dec(x_26);
x_33 = lean_int_add(x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_34 = l_Std_Time_PlainTime_ofNanoseconds(x_33);
lean_dec(x_33);
x_35 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_13);
x_36 = lean_int_add(x_35, x_30);
lean_dec(x_30);
lean_dec(x_35);
x_37 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
x_39 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_38);
x_40 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_40, 0, x_10);
x_41 = lean_mk_thunk(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
x_45 = lean_ctor_get(x_22, 2);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_18);
lean_inc(x_46);
lean_inc(x_13);
lean_ctor_set(x_10, 1, x_46);
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_int_neg(x_47);
x_49 = l_Std_Time_PlainTime_toSeconds(x_46);
x_50 = lean_int_add(x_49, x_48);
lean_dec(x_49);
x_51 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_52 = lean_int_ediv(x_50, x_51);
lean_dec(x_50);
x_53 = l_Std_Time_PlainTime_toNanoseconds(x_46);
lean_dec(x_46);
x_54 = lean_int_mul(x_48, x_5);
lean_dec(x_48);
x_55 = lean_int_add(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
x_56 = l_Std_Time_PlainTime_ofNanoseconds(x_55);
lean_dec(x_55);
x_57 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_13);
x_58 = lean_int_add(x_57, x_52);
lean_dec(x_52);
lean_dec(x_57);
x_59 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
x_61 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_60);
x_62 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_62, 0, x_10);
x_63 = lean_mk_thunk(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_65 = lean_ctor_get(x_10, 0);
x_66 = lean_ctor_get(x_10, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_10);
x_67 = lean_ctor_get(x_66, 3);
lean_inc(x_67);
x_68 = lean_int_add(x_67, x_11);
lean_dec(x_11);
lean_dec(x_67);
x_69 = lean_int_ediv(x_68, x_5);
x_70 = lean_int_emod(x_68, x_5);
lean_dec(x_68);
x_71 = l_Std_Time_PlainTime_toNanoseconds(x_66);
lean_dec(x_66);
x_72 = lean_int_mul(x_69, x_5);
lean_dec(x_69);
x_73 = lean_int_add(x_71, x_72);
lean_dec(x_72);
lean_dec(x_71);
x_74 = l_Std_Time_PlainTime_ofNanoseconds(x_73);
lean_dec(x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 2);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 lean_ctor_release(x_74, 2);
 lean_ctor_release(x_74, 3);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 4, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_77);
lean_ctor_set(x_79, 3, x_70);
lean_inc(x_79);
lean_inc(x_65);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_ctor_get(x_1, 0);
x_82 = lean_int_neg(x_81);
x_83 = l_Std_Time_PlainTime_toSeconds(x_79);
x_84 = lean_int_add(x_83, x_82);
lean_dec(x_83);
x_85 = l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1;
x_86 = lean_int_ediv(x_84, x_85);
lean_dec(x_84);
x_87 = l_Std_Time_PlainTime_toNanoseconds(x_79);
lean_dec(x_79);
x_88 = lean_int_mul(x_82, x_5);
lean_dec(x_82);
x_89 = lean_int_add(x_87, x_88);
lean_dec(x_88);
lean_dec(x_87);
x_90 = l_Std_Time_PlainTime_ofNanoseconds(x_89);
lean_dec(x_89);
x_91 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_65);
x_92 = lean_int_add(x_91, x_86);
lean_dec(x_86);
lean_dec(x_91);
x_93 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_92);
lean_dec(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
x_95 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_94);
x_96 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lambda__1___boxed), 2, 1);
lean_closure_set(x_96, 0, x_80);
x_97 = lean_mk_thunk(x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_instHSubDuration__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Std_Time_DateTime(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_DateTime(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_DateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_TimeZone(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedDateTime___lambda__1___closed__1 = _init_l_Std_Time_instInhabitedDateTime___lambda__1___closed__1();
lean_mark_persistent(l_Std_Time_instInhabitedDateTime___lambda__1___closed__1);
l_Std_Time_instInhabitedDateTime___lambda__1___closed__2 = _init_l_Std_Time_instInhabitedDateTime___lambda__1___closed__2();
lean_mark_persistent(l_Std_Time_instInhabitedDateTime___lambda__1___closed__2);
l_Std_Time_instInhabitedDateTime___lambda__1___closed__3 = _init_l_Std_Time_instInhabitedDateTime___lambda__1___closed__3();
lean_mark_persistent(l_Std_Time_instInhabitedDateTime___lambda__1___closed__3);
l_Std_Time_instInhabitedDateTime___lambda__1___closed__4 = _init_l_Std_Time_instInhabitedDateTime___lambda__1___closed__4();
lean_mark_persistent(l_Std_Time_instInhabitedDateTime___lambda__1___closed__4);
l_Std_Time_instInhabitedDateTime___closed__1 = _init_l_Std_Time_instInhabitedDateTime___closed__1();
lean_mark_persistent(l_Std_Time_instInhabitedDateTime___closed__1);
l_Std_Time_instInhabitedDateTime___closed__2 = _init_l_Std_Time_instInhabitedDateTime___closed__2();
lean_mark_persistent(l_Std_Time_instInhabitedDateTime___closed__2);
l_Std_Time_instInhabitedDateTime___closed__3 = _init_l_Std_Time_instInhabitedDateTime___closed__3();
lean_mark_persistent(l_Std_Time_instInhabitedDateTime___closed__3);
l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1 = _init_l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1();
lean_mark_persistent(l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__1);
l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2 = _init_l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2();
lean_mark_persistent(l_Std_Time_DateTime_ofTimestamp___lambda__1___closed__2);
l_Std_Time_DateTime_addHours___closed__1 = _init_l_Std_Time_DateTime_addHours___closed__1();
lean_mark_persistent(l_Std_Time_DateTime_addHours___closed__1);
l_Std_Time_DateTime_addMinutes___closed__1 = _init_l_Std_Time_DateTime_addMinutes___closed__1();
lean_mark_persistent(l_Std_Time_DateTime_addMinutes___closed__1);
l_Std_Time_DateTime_addMilliseconds___closed__1 = _init_l_Std_Time_DateTime_addMilliseconds___closed__1();
lean_mark_persistent(l_Std_Time_DateTime_addMilliseconds___closed__1);
l_Std_Time_DateTime_addWeeks___closed__1 = _init_l_Std_Time_DateTime_addWeeks___closed__1();
lean_mark_persistent(l_Std_Time_DateTime_addWeeks___closed__1);
l_Std_Time_DateTime_addYearsRollOver___closed__1 = _init_l_Std_Time_DateTime_addYearsRollOver___closed__1();
lean_mark_persistent(l_Std_Time_DateTime_addYearsRollOver___closed__1);
l_Std_Time_DateTime_withDaysClip___closed__1 = _init_l_Std_Time_DateTime_withDaysClip___closed__1();
lean_mark_persistent(l_Std_Time_DateTime_withDaysClip___closed__1);
l_Std_Time_DateTime_withDaysClip___closed__2 = _init_l_Std_Time_DateTime_withDaysClip___closed__2();
lean_mark_persistent(l_Std_Time_DateTime_withDaysClip___closed__2);
l_Std_Time_DateTime_withDaysClip___closed__3 = _init_l_Std_Time_DateTime_withDaysClip___closed__3();
lean_mark_persistent(l_Std_Time_DateTime_withDaysClip___closed__3);
l_Std_Time_DateTime_withMilliseconds___closed__1 = _init_l_Std_Time_DateTime_withMilliseconds___closed__1();
lean_mark_persistent(l_Std_Time_DateTime_withMilliseconds___closed__1);
l_Std_Time_DateTime_withMilliseconds___closed__2 = _init_l_Std_Time_DateTime_withMilliseconds___closed__2();
lean_mark_persistent(l_Std_Time_DateTime_withMilliseconds___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Std.Time.Zoned.DateTime
// Imports: Std.Time.DateTime Std.Time.Zoned.TimeZone Std.Time.Date.Unit.Month Std.Time.Date.Unit.Year Std.Time.DateTime.PlainDateTime
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
LEAN_EXPORT uint8_t l_Std_Time_instBEqDateTime___lam__0(lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___redArg___boxed(lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instNeg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__5(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg(lean_object*);
static lean_object* l_Std_Time_DateTime_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg___boxed(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg___boxed(lean_object*);
extern lean_object* l_Std_Time_instOrdTimestamp;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg___boxed(lean_object*);
static lean_object* l_Std_Time_DateTime_withMilliseconds___closed__0;
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday___redArg(lean_object*);
uint8_t l_Std_Time_decEqDuration____x40_Std_Time_Duration_4137264884____hygCtx___hyg_300_(lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_addYearsRollOver___closed__0;
static lean_object* l_Std_Time_DateTime_addWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_addMinutes___closed__0;
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__6(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg___boxed(lean_object*);
static lean_object* l_Std_Time_DateTime_addMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
extern lean_object* l_Std_Time_defaultTimestamp____x40_Std_Time_DateTime_Timestamp_1067989854____hygCtx___hyg_203_;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__3(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_addHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__3(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instBEqDateTime___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Std_Time_decEqDuration____x40_Std_Time_Duration_4137264884____hygCtx___hyg_300_(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_instBEqDateTime___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_instBEqDateTime___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instBEqDateTime(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_instOrdDateTime___lam__0___boxed), 1, 0);
x_3 = l_Std_Time_instOrdTimestamp;
x_4 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_3);
lean_closure_set(x_4, 3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instOrdDateTime___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instOrdDateTime(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_5 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Time_TimeZone_toSeconds(x_2);
x_9 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_10 = lean_int_mul(x_8, x_9);
lean_dec(x_8);
x_11 = l_Std_Time_Duration_ofNanoseconds(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_int_mul(x_6, x_9);
lean_dec(x_6);
x_15 = lean_int_add(x_14, x_7);
lean_dec(x_7);
lean_dec(x_14);
x_16 = lean_int_mul(x_12, x_9);
lean_dec(x_12);
x_17 = lean_int_add(x_16, x_13);
lean_dec(x_13);
lean_dec(x_16);
x_18 = lean_int_add(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
x_19 = l_Std_Time_Duration_ofNanoseconds(x_18);
lean_dec(x_18);
x_20 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestamp___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = lean_mk_thunk(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_ofTimestamp___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_5 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Time_TimeZone_toSeconds(x_2);
x_9 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_10 = lean_int_mul(x_8, x_9);
lean_dec(x_8);
x_11 = l_Std_Time_Duration_ofNanoseconds(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_int_mul(x_6, x_9);
lean_dec(x_6);
x_15 = lean_int_add(x_14, x_7);
lean_dec(x_7);
lean_dec(x_14);
x_16 = lean_int_mul(x_12, x_9);
lean_dec(x_12);
x_17 = lean_int_add(x_16, x_13);
lean_dec(x_13);
lean_dec(x_16);
x_18 = lean_int_add(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
x_19 = l_Std_Time_Duration_ofNanoseconds(x_18);
lean_dec(x_18);
x_20 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_19);
return x_20;
}
}
static lean_object* _init_l_Std_Time_DateTime_instInhabited___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Time_defaultTimestamp____x40_Std_Time_DateTime_Timestamp_1067989854____hygCtx___hyg_203_;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Std_Time_DateTime_instInhabited___closed__0;
x_3 = lean_alloc_closure((void*)(l_Std_Time_DateTime_instInhabited___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lean_mk_thunk(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_instInhabited___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_toDaysSinceUNIXEpoch(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toTimestamp___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_toTimestamp(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_4 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_5 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Time_TimeZone_toSeconds(x_2);
x_9 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_10 = lean_int_mul(x_8, x_9);
lean_dec(x_8);
x_11 = l_Std_Time_Duration_ofNanoseconds(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_int_mul(x_6, x_9);
lean_dec(x_6);
x_15 = lean_int_add(x_14, x_7);
lean_dec(x_7);
lean_dec(x_14);
x_16 = lean_int_mul(x_12, x_9);
lean_dec(x_12);
x_17 = lean_int_add(x_16, x_13);
lean_dec(x_13);
lean_dec(x_16);
x_18 = lean_int_add(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
x_19 = l_Std_Time_Duration_ofNanoseconds(x_18);
lean_dec(x_18);
x_20 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_inc_ref(x_4);
x_6 = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
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
lean_inc_ref(x_8);
x_9 = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_dec(x_6);
lean_inc_ref(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_mk_thunk(x_7);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
lean_inc_ref(x_9);
x_10 = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_3);
x_11 = lean_mk_thunk(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_convertTimeZone(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Std_Time_TimeZone_toSeconds(x_2);
x_8 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_9 = lean_int_mul(x_7, x_8);
lean_dec(x_7);
x_10 = l_Std_Time_Duration_ofNanoseconds(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_int_mul(x_5, x_8);
lean_dec(x_5);
x_14 = lean_int_add(x_13, x_6);
lean_dec(x_6);
lean_dec(x_13);
x_15 = lean_int_mul(x_11, x_8);
lean_dec(x_11);
x_16 = lean_int_add(x_15, x_12);
lean_dec(x_12);
lean_dec(x_15);
x_17 = lean_int_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = l_Std_Time_Duration_ofNanoseconds(x_17);
lean_dec(x_17);
x_19 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_1);
x_3 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_5 = lean_mk_thunk(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_1);
x_3 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Std_Time_TimeZone_toSeconds(x_2);
x_7 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_6);
lean_dec(x_6);
x_8 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_9 = lean_int_mul(x_7, x_8);
lean_dec(x_7);
x_10 = l_Std_Time_Duration_ofNanoseconds(x_9);
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed), 2, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_int_mul(x_4, x_8);
lean_dec(x_4);
x_16 = lean_int_add(x_15, x_5);
lean_dec(x_5);
lean_dec(x_15);
x_17 = lean_int_mul(x_12, x_8);
lean_dec(x_12);
x_18 = lean_int_add(x_17, x_13);
lean_dec(x_13);
lean_dec(x_17);
x_19 = lean_int_add(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_20);
x_22 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_21);
x_23 = lean_mk_thunk(x_14);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_1);
x_27 = lean_int_mul(x_4, x_8);
lean_dec(x_4);
x_28 = lean_int_add(x_27, x_5);
lean_dec(x_5);
lean_dec(x_27);
x_29 = lean_int_mul(x_24, x_8);
lean_dec(x_24);
x_30 = lean_int_add(x_29, x_25);
lean_dec(x_25);
lean_dec(x_29);
x_31 = lean_int_add(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_32 = l_Std_Time_Duration_ofNanoseconds(x_31);
lean_dec(x_31);
x_33 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_32);
x_34 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_33);
x_35 = lean_mk_thunk(x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_ofPlainDateTime___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_ofPlainDateTime(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_cstr_to_nat("3600000000000");
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_DateTime_addHours___closed__0;
x_12 = lean_int_mul(x_3, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_17 = lean_int_mul(x_9, x_16);
lean_dec(x_9);
x_18 = lean_int_add(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_19 = lean_int_mul(x_14, x_16);
lean_dec(x_14);
x_20 = lean_int_add(x_19, x_15);
lean_dec(x_15);
lean_dec(x_19);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_Duration_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_22);
lean_inc_ref(x_23);
x_24 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Std_Time_TimeZone_toSeconds(x_1);
x_28 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_27);
lean_dec(x_27);
x_29 = lean_int_mul(x_28, x_16);
lean_dec(x_28);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_33, 0, x_23);
x_34 = lean_int_mul(x_25, x_16);
lean_dec(x_25);
x_35 = lean_int_add(x_34, x_26);
lean_dec(x_26);
lean_dec(x_34);
x_36 = lean_int_mul(x_31, x_16);
lean_dec(x_31);
x_37 = lean_int_add(x_36, x_32);
lean_dec(x_32);
lean_dec(x_36);
x_38 = lean_int_add(x_35, x_37);
lean_dec(x_37);
lean_dec(x_35);
x_39 = l_Std_Time_Duration_ofNanoseconds(x_38);
lean_dec(x_38);
x_40 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_39);
x_41 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_40);
x_42 = lean_mk_thunk(x_33);
lean_ctor_set(x_2, 1, x_42);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_thunk_get_own(x_43);
lean_dec_ref(x_43);
x_45 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Std_Time_DateTime_addHours___closed__0;
x_49 = lean_int_mul(x_3, x_48);
x_50 = l_Std_Time_Duration_ofNanoseconds(x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_54 = lean_int_mul(x_46, x_53);
lean_dec(x_46);
x_55 = lean_int_add(x_54, x_47);
lean_dec(x_47);
lean_dec(x_54);
x_56 = lean_int_mul(x_51, x_53);
lean_dec(x_51);
x_57 = lean_int_add(x_56, x_52);
lean_dec(x_52);
lean_dec(x_56);
x_58 = lean_int_add(x_55, x_57);
lean_dec(x_57);
lean_dec(x_55);
x_59 = l_Std_Time_Duration_ofNanoseconds(x_58);
lean_dec(x_58);
x_60 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_59);
lean_inc_ref(x_60);
x_61 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = l_Std_Time_TimeZone_toSeconds(x_1);
x_65 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_64);
lean_dec(x_64);
x_66 = lean_int_mul(x_65, x_53);
lean_dec(x_65);
x_67 = l_Std_Time_Duration_ofNanoseconds(x_66);
lean_dec(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_70, 0, x_60);
x_71 = lean_int_mul(x_62, x_53);
lean_dec(x_62);
x_72 = lean_int_add(x_71, x_63);
lean_dec(x_63);
lean_dec(x_71);
x_73 = lean_int_mul(x_68, x_53);
lean_dec(x_68);
x_74 = lean_int_add(x_73, x_69);
lean_dec(x_69);
lean_dec(x_73);
x_75 = lean_int_add(x_72, x_74);
lean_dec(x_74);
lean_dec(x_72);
x_76 = l_Std_Time_Duration_ofNanoseconds(x_75);
lean_dec(x_75);
x_77 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_76);
x_78 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_77);
x_79 = lean_mk_thunk(x_70);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_addHours___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addHours(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_12 = l_Std_Time_DateTime_addHours___closed__0;
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_18 = lean_int_mul(x_9, x_17);
lean_dec(x_9);
x_19 = lean_int_add(x_18, x_10);
lean_dec(x_10);
lean_dec(x_18);
x_20 = lean_int_mul(x_15, x_17);
lean_dec(x_15);
x_21 = lean_int_add(x_20, x_16);
lean_dec(x_16);
lean_dec(x_20);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_Duration_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_23);
lean_inc_ref(x_24);
x_25 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Std_Time_TimeZone_toSeconds(x_1);
x_29 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_28);
lean_dec(x_28);
x_30 = lean_int_mul(x_29, x_17);
lean_dec(x_29);
x_31 = l_Std_Time_Duration_ofNanoseconds(x_30);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_34, 0, x_24);
x_35 = lean_int_mul(x_26, x_17);
lean_dec(x_26);
x_36 = lean_int_add(x_35, x_27);
lean_dec(x_27);
lean_dec(x_35);
x_37 = lean_int_mul(x_32, x_17);
lean_dec(x_32);
x_38 = lean_int_add(x_37, x_33);
lean_dec(x_33);
lean_dec(x_37);
x_39 = lean_int_add(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
x_40 = l_Std_Time_Duration_ofNanoseconds(x_39);
lean_dec(x_39);
x_41 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_40);
x_42 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_41);
x_43 = lean_mk_thunk(x_34);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_42);
return x_2;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_thunk_get_own(x_44);
lean_dec_ref(x_44);
x_46 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_50 = l_Std_Time_DateTime_addHours___closed__0;
x_51 = lean_int_mul(x_49, x_50);
lean_dec(x_49);
x_52 = l_Std_Time_Duration_ofNanoseconds(x_51);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_56 = lean_int_mul(x_47, x_55);
lean_dec(x_47);
x_57 = lean_int_add(x_56, x_48);
lean_dec(x_48);
lean_dec(x_56);
x_58 = lean_int_mul(x_53, x_55);
lean_dec(x_53);
x_59 = lean_int_add(x_58, x_54);
lean_dec(x_54);
lean_dec(x_58);
x_60 = lean_int_add(x_57, x_59);
lean_dec(x_59);
lean_dec(x_57);
x_61 = l_Std_Time_Duration_ofNanoseconds(x_60);
lean_dec(x_60);
x_62 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_61);
lean_inc_ref(x_62);
x_63 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = l_Std_Time_TimeZone_toSeconds(x_1);
x_67 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_66);
lean_dec(x_66);
x_68 = lean_int_mul(x_67, x_55);
lean_dec(x_67);
x_69 = l_Std_Time_Duration_ofNanoseconds(x_68);
lean_dec(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_72, 0, x_62);
x_73 = lean_int_mul(x_64, x_55);
lean_dec(x_64);
x_74 = lean_int_add(x_73, x_65);
lean_dec(x_65);
lean_dec(x_73);
x_75 = lean_int_mul(x_70, x_55);
lean_dec(x_70);
x_76 = lean_int_add(x_75, x_71);
lean_dec(x_71);
lean_dec(x_75);
x_77 = lean_int_add(x_74, x_76);
lean_dec(x_76);
lean_dec(x_74);
x_78 = l_Std_Time_Duration_ofNanoseconds(x_77);
lean_dec(x_77);
x_79 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_78);
x_80 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_79);
x_81 = lean_mk_thunk(x_72);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subHours(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_cstr_to_nat("60000000000");
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_DateTime_addMinutes___closed__0;
x_12 = lean_int_mul(x_3, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_17 = lean_int_mul(x_9, x_16);
lean_dec(x_9);
x_18 = lean_int_add(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_19 = lean_int_mul(x_14, x_16);
lean_dec(x_14);
x_20 = lean_int_add(x_19, x_15);
lean_dec(x_15);
lean_dec(x_19);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_Duration_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_22);
lean_inc_ref(x_23);
x_24 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Std_Time_TimeZone_toSeconds(x_1);
x_28 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_27);
lean_dec(x_27);
x_29 = lean_int_mul(x_28, x_16);
lean_dec(x_28);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_33, 0, x_23);
x_34 = lean_int_mul(x_25, x_16);
lean_dec(x_25);
x_35 = lean_int_add(x_34, x_26);
lean_dec(x_26);
lean_dec(x_34);
x_36 = lean_int_mul(x_31, x_16);
lean_dec(x_31);
x_37 = lean_int_add(x_36, x_32);
lean_dec(x_32);
lean_dec(x_36);
x_38 = lean_int_add(x_35, x_37);
lean_dec(x_37);
lean_dec(x_35);
x_39 = l_Std_Time_Duration_ofNanoseconds(x_38);
lean_dec(x_38);
x_40 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_39);
x_41 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_40);
x_42 = lean_mk_thunk(x_33);
lean_ctor_set(x_2, 1, x_42);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_thunk_get_own(x_43);
lean_dec_ref(x_43);
x_45 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Std_Time_DateTime_addMinutes___closed__0;
x_49 = lean_int_mul(x_3, x_48);
x_50 = l_Std_Time_Duration_ofNanoseconds(x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_54 = lean_int_mul(x_46, x_53);
lean_dec(x_46);
x_55 = lean_int_add(x_54, x_47);
lean_dec(x_47);
lean_dec(x_54);
x_56 = lean_int_mul(x_51, x_53);
lean_dec(x_51);
x_57 = lean_int_add(x_56, x_52);
lean_dec(x_52);
lean_dec(x_56);
x_58 = lean_int_add(x_55, x_57);
lean_dec(x_57);
lean_dec(x_55);
x_59 = l_Std_Time_Duration_ofNanoseconds(x_58);
lean_dec(x_58);
x_60 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_59);
lean_inc_ref(x_60);
x_61 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = l_Std_Time_TimeZone_toSeconds(x_1);
x_65 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_64);
lean_dec(x_64);
x_66 = lean_int_mul(x_65, x_53);
lean_dec(x_65);
x_67 = l_Std_Time_Duration_ofNanoseconds(x_66);
lean_dec(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_70, 0, x_60);
x_71 = lean_int_mul(x_62, x_53);
lean_dec(x_62);
x_72 = lean_int_add(x_71, x_63);
lean_dec(x_63);
lean_dec(x_71);
x_73 = lean_int_mul(x_68, x_53);
lean_dec(x_68);
x_74 = lean_int_add(x_73, x_69);
lean_dec(x_69);
lean_dec(x_73);
x_75 = lean_int_add(x_72, x_74);
lean_dec(x_74);
lean_dec(x_72);
x_76 = l_Std_Time_Duration_ofNanoseconds(x_75);
lean_dec(x_75);
x_77 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_76);
x_78 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_77);
x_79 = lean_mk_thunk(x_70);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addMinutes(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_12 = l_Std_Time_DateTime_addMinutes___closed__0;
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_18 = lean_int_mul(x_9, x_17);
lean_dec(x_9);
x_19 = lean_int_add(x_18, x_10);
lean_dec(x_10);
lean_dec(x_18);
x_20 = lean_int_mul(x_15, x_17);
lean_dec(x_15);
x_21 = lean_int_add(x_20, x_16);
lean_dec(x_16);
lean_dec(x_20);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_Duration_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_23);
lean_inc_ref(x_24);
x_25 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Std_Time_TimeZone_toSeconds(x_1);
x_29 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_28);
lean_dec(x_28);
x_30 = lean_int_mul(x_29, x_17);
lean_dec(x_29);
x_31 = l_Std_Time_Duration_ofNanoseconds(x_30);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_34, 0, x_24);
x_35 = lean_int_mul(x_26, x_17);
lean_dec(x_26);
x_36 = lean_int_add(x_35, x_27);
lean_dec(x_27);
lean_dec(x_35);
x_37 = lean_int_mul(x_32, x_17);
lean_dec(x_32);
x_38 = lean_int_add(x_37, x_33);
lean_dec(x_33);
lean_dec(x_37);
x_39 = lean_int_add(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
x_40 = l_Std_Time_Duration_ofNanoseconds(x_39);
lean_dec(x_39);
x_41 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_40);
x_42 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_41);
x_43 = lean_mk_thunk(x_34);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_42);
return x_2;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_thunk_get_own(x_44);
lean_dec_ref(x_44);
x_46 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_50 = l_Std_Time_DateTime_addMinutes___closed__0;
x_51 = lean_int_mul(x_49, x_50);
lean_dec(x_49);
x_52 = l_Std_Time_Duration_ofNanoseconds(x_51);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_56 = lean_int_mul(x_47, x_55);
lean_dec(x_47);
x_57 = lean_int_add(x_56, x_48);
lean_dec(x_48);
lean_dec(x_56);
x_58 = lean_int_mul(x_53, x_55);
lean_dec(x_53);
x_59 = lean_int_add(x_58, x_54);
lean_dec(x_54);
lean_dec(x_58);
x_60 = lean_int_add(x_57, x_59);
lean_dec(x_59);
lean_dec(x_57);
x_61 = l_Std_Time_Duration_ofNanoseconds(x_60);
lean_dec(x_60);
x_62 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_61);
lean_inc_ref(x_62);
x_63 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = l_Std_Time_TimeZone_toSeconds(x_1);
x_67 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_66);
lean_dec(x_66);
x_68 = lean_int_mul(x_67, x_55);
lean_dec(x_67);
x_69 = l_Std_Time_Duration_ofNanoseconds(x_68);
lean_dec(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_72, 0, x_62);
x_73 = lean_int_mul(x_64, x_55);
lean_dec(x_64);
x_74 = lean_int_add(x_73, x_65);
lean_dec(x_65);
lean_dec(x_73);
x_75 = lean_int_mul(x_70, x_55);
lean_dec(x_70);
x_76 = lean_int_add(x_75, x_71);
lean_dec(x_71);
lean_dec(x_75);
x_77 = lean_int_add(x_74, x_76);
lean_dec(x_76);
lean_dec(x_74);
x_78 = l_Std_Time_Duration_ofNanoseconds(x_77);
lean_dec(x_77);
x_79 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_78);
x_80 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_79);
x_81 = lean_mk_thunk(x_72);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subMinutes(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_12 = lean_int_mul(x_3, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_int_mul(x_9, x_11);
lean_dec(x_9);
x_17 = lean_int_add(x_16, x_10);
lean_dec(x_10);
lean_dec(x_16);
x_18 = lean_int_mul(x_14, x_11);
lean_dec(x_14);
x_19 = lean_int_add(x_18, x_15);
lean_dec(x_15);
lean_dec(x_18);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_Duration_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_21);
lean_inc_ref(x_22);
x_23 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Std_Time_TimeZone_toSeconds(x_1);
x_27 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_26);
lean_dec(x_26);
x_28 = lean_int_mul(x_27, x_11);
lean_dec(x_27);
x_29 = l_Std_Time_Duration_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_32, 0, x_22);
x_33 = lean_int_mul(x_24, x_11);
lean_dec(x_24);
x_34 = lean_int_add(x_33, x_25);
lean_dec(x_25);
lean_dec(x_33);
x_35 = lean_int_mul(x_30, x_11);
lean_dec(x_30);
x_36 = lean_int_add(x_35, x_31);
lean_dec(x_31);
lean_dec(x_35);
x_37 = lean_int_add(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
x_38 = l_Std_Time_Duration_ofNanoseconds(x_37);
lean_dec(x_37);
x_39 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_38);
x_40 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_39);
x_41 = lean_mk_thunk(x_32);
lean_ctor_set(x_2, 1, x_41);
lean_ctor_set(x_2, 0, x_40);
return x_2;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_thunk_get_own(x_42);
lean_dec_ref(x_42);
x_44 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_48 = lean_int_mul(x_3, x_47);
x_49 = l_Std_Time_Duration_ofNanoseconds(x_48);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_int_mul(x_45, x_47);
lean_dec(x_45);
x_53 = lean_int_add(x_52, x_46);
lean_dec(x_46);
lean_dec(x_52);
x_54 = lean_int_mul(x_50, x_47);
lean_dec(x_50);
x_55 = lean_int_add(x_54, x_51);
lean_dec(x_51);
lean_dec(x_54);
x_56 = lean_int_add(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
x_57 = l_Std_Time_Duration_ofNanoseconds(x_56);
lean_dec(x_56);
x_58 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_57);
lean_inc_ref(x_58);
x_59 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = l_Std_Time_TimeZone_toSeconds(x_1);
x_63 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_62);
lean_dec(x_62);
x_64 = lean_int_mul(x_63, x_47);
lean_dec(x_63);
x_65 = l_Std_Time_Duration_ofNanoseconds(x_64);
lean_dec(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_68, 0, x_58);
x_69 = lean_int_mul(x_60, x_47);
lean_dec(x_60);
x_70 = lean_int_add(x_69, x_61);
lean_dec(x_61);
lean_dec(x_69);
x_71 = lean_int_mul(x_66, x_47);
lean_dec(x_66);
x_72 = lean_int_add(x_71, x_67);
lean_dec(x_67);
lean_dec(x_71);
x_73 = lean_int_add(x_70, x_72);
lean_dec(x_72);
lean_dec(x_70);
x_74 = l_Std_Time_Duration_ofNanoseconds(x_73);
lean_dec(x_73);
x_75 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_74);
x_76 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_75);
x_77 = lean_mk_thunk(x_68);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addSeconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_12 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_int_mul(x_9, x_12);
lean_dec(x_9);
x_18 = lean_int_add(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_19 = lean_int_mul(x_15, x_12);
lean_dec(x_15);
x_20 = lean_int_add(x_19, x_16);
lean_dec(x_16);
lean_dec(x_19);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_Duration_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_22);
lean_inc_ref(x_23);
x_24 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Std_Time_TimeZone_toSeconds(x_1);
x_28 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_27);
lean_dec(x_27);
x_29 = lean_int_mul(x_28, x_12);
lean_dec(x_28);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_33, 0, x_23);
x_34 = lean_int_mul(x_25, x_12);
lean_dec(x_25);
x_35 = lean_int_add(x_34, x_26);
lean_dec(x_26);
lean_dec(x_34);
x_36 = lean_int_mul(x_31, x_12);
lean_dec(x_31);
x_37 = lean_int_add(x_36, x_32);
lean_dec(x_32);
lean_dec(x_36);
x_38 = lean_int_add(x_35, x_37);
lean_dec(x_37);
lean_dec(x_35);
x_39 = l_Std_Time_Duration_ofNanoseconds(x_38);
lean_dec(x_38);
x_40 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_39);
x_41 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_40);
x_42 = lean_mk_thunk(x_33);
lean_ctor_set(x_2, 1, x_42);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_thunk_get_own(x_43);
lean_dec_ref(x_43);
x_45 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_49 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_50 = lean_int_mul(x_48, x_49);
lean_dec(x_48);
x_51 = l_Std_Time_Duration_ofNanoseconds(x_50);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_int_mul(x_46, x_49);
lean_dec(x_46);
x_55 = lean_int_add(x_54, x_47);
lean_dec(x_47);
lean_dec(x_54);
x_56 = lean_int_mul(x_52, x_49);
lean_dec(x_52);
x_57 = lean_int_add(x_56, x_53);
lean_dec(x_53);
lean_dec(x_56);
x_58 = lean_int_add(x_55, x_57);
lean_dec(x_57);
lean_dec(x_55);
x_59 = l_Std_Time_Duration_ofNanoseconds(x_58);
lean_dec(x_58);
x_60 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_59);
lean_inc_ref(x_60);
x_61 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = l_Std_Time_TimeZone_toSeconds(x_1);
x_65 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_64);
lean_dec(x_64);
x_66 = lean_int_mul(x_65, x_49);
lean_dec(x_65);
x_67 = l_Std_Time_Duration_ofNanoseconds(x_66);
lean_dec(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_70, 0, x_60);
x_71 = lean_int_mul(x_62, x_49);
lean_dec(x_62);
x_72 = lean_int_add(x_71, x_63);
lean_dec(x_63);
lean_dec(x_71);
x_73 = lean_int_mul(x_68, x_49);
lean_dec(x_68);
x_74 = lean_int_add(x_73, x_69);
lean_dec(x_69);
lean_dec(x_73);
x_75 = lean_int_add(x_72, x_74);
lean_dec(x_74);
lean_dec(x_72);
x_76 = l_Std_Time_Duration_ofNanoseconds(x_75);
lean_dec(x_75);
x_77 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_76);
x_78 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_77);
x_79 = lean_mk_thunk(x_70);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subSeconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMilliseconds___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_DateTime_addMilliseconds___closed__0;
x_12 = lean_int_mul(x_3, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_17 = lean_int_mul(x_9, x_16);
lean_dec(x_9);
x_18 = lean_int_add(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_19 = lean_int_mul(x_14, x_16);
lean_dec(x_14);
x_20 = lean_int_add(x_19, x_15);
lean_dec(x_15);
lean_dec(x_19);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_Duration_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_22);
lean_inc_ref(x_23);
x_24 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Std_Time_TimeZone_toSeconds(x_1);
x_28 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_27);
lean_dec(x_27);
x_29 = lean_int_mul(x_28, x_16);
lean_dec(x_28);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_33, 0, x_23);
x_34 = lean_int_mul(x_25, x_16);
lean_dec(x_25);
x_35 = lean_int_add(x_34, x_26);
lean_dec(x_26);
lean_dec(x_34);
x_36 = lean_int_mul(x_31, x_16);
lean_dec(x_31);
x_37 = lean_int_add(x_36, x_32);
lean_dec(x_32);
lean_dec(x_36);
x_38 = lean_int_add(x_35, x_37);
lean_dec(x_37);
lean_dec(x_35);
x_39 = l_Std_Time_Duration_ofNanoseconds(x_38);
lean_dec(x_38);
x_40 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_39);
x_41 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_40);
x_42 = lean_mk_thunk(x_33);
lean_ctor_set(x_2, 1, x_42);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_thunk_get_own(x_43);
lean_dec_ref(x_43);
x_45 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Std_Time_DateTime_addMilliseconds___closed__0;
x_49 = lean_int_mul(x_3, x_48);
x_50 = l_Std_Time_Duration_ofNanoseconds(x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_54 = lean_int_mul(x_46, x_53);
lean_dec(x_46);
x_55 = lean_int_add(x_54, x_47);
lean_dec(x_47);
lean_dec(x_54);
x_56 = lean_int_mul(x_51, x_53);
lean_dec(x_51);
x_57 = lean_int_add(x_56, x_52);
lean_dec(x_52);
lean_dec(x_56);
x_58 = lean_int_add(x_55, x_57);
lean_dec(x_57);
lean_dec(x_55);
x_59 = l_Std_Time_Duration_ofNanoseconds(x_58);
lean_dec(x_58);
x_60 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_59);
lean_inc_ref(x_60);
x_61 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = l_Std_Time_TimeZone_toSeconds(x_1);
x_65 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_64);
lean_dec(x_64);
x_66 = lean_int_mul(x_65, x_53);
lean_dec(x_65);
x_67 = l_Std_Time_Duration_ofNanoseconds(x_66);
lean_dec(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_70, 0, x_60);
x_71 = lean_int_mul(x_62, x_53);
lean_dec(x_62);
x_72 = lean_int_add(x_71, x_63);
lean_dec(x_63);
lean_dec(x_71);
x_73 = lean_int_mul(x_68, x_53);
lean_dec(x_68);
x_74 = lean_int_add(x_73, x_69);
lean_dec(x_69);
lean_dec(x_73);
x_75 = lean_int_add(x_72, x_74);
lean_dec(x_74);
lean_dec(x_72);
x_76 = l_Std_Time_Duration_ofNanoseconds(x_75);
lean_dec(x_75);
x_77 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_76);
x_78 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_77);
x_79 = lean_mk_thunk(x_70);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addMilliseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_12 = l_Std_Time_DateTime_addMilliseconds___closed__0;
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_18 = lean_int_mul(x_9, x_17);
lean_dec(x_9);
x_19 = lean_int_add(x_18, x_10);
lean_dec(x_10);
lean_dec(x_18);
x_20 = lean_int_mul(x_15, x_17);
lean_dec(x_15);
x_21 = lean_int_add(x_20, x_16);
lean_dec(x_16);
lean_dec(x_20);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_Duration_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_23);
lean_inc_ref(x_24);
x_25 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Std_Time_TimeZone_toSeconds(x_1);
x_29 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_28);
lean_dec(x_28);
x_30 = lean_int_mul(x_29, x_17);
lean_dec(x_29);
x_31 = l_Std_Time_Duration_ofNanoseconds(x_30);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_34, 0, x_24);
x_35 = lean_int_mul(x_26, x_17);
lean_dec(x_26);
x_36 = lean_int_add(x_35, x_27);
lean_dec(x_27);
lean_dec(x_35);
x_37 = lean_int_mul(x_32, x_17);
lean_dec(x_32);
x_38 = lean_int_add(x_37, x_33);
lean_dec(x_33);
lean_dec(x_37);
x_39 = lean_int_add(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
x_40 = l_Std_Time_Duration_ofNanoseconds(x_39);
lean_dec(x_39);
x_41 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_40);
x_42 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_41);
x_43 = lean_mk_thunk(x_34);
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_42);
return x_2;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_thunk_get_own(x_44);
lean_dec_ref(x_44);
x_46 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_50 = l_Std_Time_DateTime_addMilliseconds___closed__0;
x_51 = lean_int_mul(x_49, x_50);
lean_dec(x_49);
x_52 = l_Std_Time_Duration_ofNanoseconds(x_51);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_56 = lean_int_mul(x_47, x_55);
lean_dec(x_47);
x_57 = lean_int_add(x_56, x_48);
lean_dec(x_48);
lean_dec(x_56);
x_58 = lean_int_mul(x_53, x_55);
lean_dec(x_53);
x_59 = lean_int_add(x_58, x_54);
lean_dec(x_54);
lean_dec(x_58);
x_60 = lean_int_add(x_57, x_59);
lean_dec(x_59);
lean_dec(x_57);
x_61 = l_Std_Time_Duration_ofNanoseconds(x_60);
lean_dec(x_60);
x_62 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_61);
lean_inc_ref(x_62);
x_63 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = l_Std_Time_TimeZone_toSeconds(x_1);
x_67 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_66);
lean_dec(x_66);
x_68 = lean_int_mul(x_67, x_55);
lean_dec(x_67);
x_69 = l_Std_Time_Duration_ofNanoseconds(x_68);
lean_dec(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_72, 0, x_62);
x_73 = lean_int_mul(x_64, x_55);
lean_dec(x_64);
x_74 = lean_int_add(x_73, x_65);
lean_dec(x_65);
lean_dec(x_73);
x_75 = lean_int_mul(x_70, x_55);
lean_dec(x_70);
x_76 = lean_int_add(x_75, x_71);
lean_dec(x_71);
lean_dec(x_75);
x_77 = lean_int_add(x_74, x_76);
lean_dec(x_76);
lean_dec(x_74);
x_78 = l_Std_Time_Duration_ofNanoseconds(x_77);
lean_dec(x_77);
x_79 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_78);
x_80 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_79);
x_81 = lean_mk_thunk(x_72);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subMilliseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_Duration_ofNanoseconds(x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_15 = lean_int_mul(x_9, x_14);
lean_dec(x_9);
x_16 = lean_int_add(x_15, x_10);
lean_dec(x_10);
lean_dec(x_15);
x_17 = lean_int_mul(x_12, x_14);
lean_dec(x_12);
x_18 = lean_int_add(x_17, x_13);
lean_dec(x_13);
lean_dec(x_17);
x_19 = lean_int_add(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_20);
lean_inc_ref(x_21);
x_22 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = l_Std_Time_TimeZone_toSeconds(x_1);
x_26 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_25);
lean_dec(x_25);
x_27 = lean_int_mul(x_26, x_14);
lean_dec(x_26);
x_28 = l_Std_Time_Duration_ofNanoseconds(x_27);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_31, 0, x_21);
x_32 = lean_int_mul(x_23, x_14);
lean_dec(x_23);
x_33 = lean_int_add(x_32, x_24);
lean_dec(x_24);
lean_dec(x_32);
x_34 = lean_int_mul(x_29, x_14);
lean_dec(x_29);
x_35 = lean_int_add(x_34, x_30);
lean_dec(x_30);
lean_dec(x_34);
x_36 = lean_int_add(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
x_37 = l_Std_Time_Duration_ofNanoseconds(x_36);
lean_dec(x_36);
x_38 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_37);
x_39 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_38);
x_40 = lean_mk_thunk(x_31);
lean_ctor_set(x_2, 1, x_40);
lean_ctor_set(x_2, 0, x_39);
return x_2;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_thunk_get_own(x_41);
lean_dec_ref(x_41);
x_43 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Std_Time_Duration_ofNanoseconds(x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_50 = lean_int_mul(x_44, x_49);
lean_dec(x_44);
x_51 = lean_int_add(x_50, x_45);
lean_dec(x_45);
lean_dec(x_50);
x_52 = lean_int_mul(x_47, x_49);
lean_dec(x_47);
x_53 = lean_int_add(x_52, x_48);
lean_dec(x_48);
lean_dec(x_52);
x_54 = lean_int_add(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
x_55 = l_Std_Time_Duration_ofNanoseconds(x_54);
lean_dec(x_54);
x_56 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_55);
lean_inc_ref(x_56);
x_57 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = l_Std_Time_TimeZone_toSeconds(x_1);
x_61 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_60);
lean_dec(x_60);
x_62 = lean_int_mul(x_61, x_49);
lean_dec(x_61);
x_63 = l_Std_Time_Duration_ofNanoseconds(x_62);
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_66, 0, x_56);
x_67 = lean_int_mul(x_58, x_49);
lean_dec(x_58);
x_68 = lean_int_add(x_67, x_59);
lean_dec(x_59);
lean_dec(x_67);
x_69 = lean_int_mul(x_64, x_49);
lean_dec(x_64);
x_70 = lean_int_add(x_69, x_65);
lean_dec(x_65);
lean_dec(x_69);
x_71 = lean_int_add(x_68, x_70);
lean_dec(x_70);
lean_dec(x_68);
x_72 = l_Std_Time_Duration_ofNanoseconds(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_72);
x_74 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_73);
x_75 = lean_mk_thunk(x_66);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addNanoseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_12 = l_Std_Time_Duration_ofNanoseconds(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_16 = lean_int_mul(x_9, x_15);
lean_dec(x_9);
x_17 = lean_int_add(x_16, x_10);
lean_dec(x_10);
lean_dec(x_16);
x_18 = lean_int_mul(x_13, x_15);
lean_dec(x_13);
x_19 = lean_int_add(x_18, x_14);
lean_dec(x_14);
lean_dec(x_18);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_Duration_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_21);
lean_inc_ref(x_22);
x_23 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Std_Time_TimeZone_toSeconds(x_1);
x_27 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_26);
lean_dec(x_26);
x_28 = lean_int_mul(x_27, x_15);
lean_dec(x_27);
x_29 = l_Std_Time_Duration_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_32, 0, x_22);
x_33 = lean_int_mul(x_24, x_15);
lean_dec(x_24);
x_34 = lean_int_add(x_33, x_25);
lean_dec(x_25);
lean_dec(x_33);
x_35 = lean_int_mul(x_30, x_15);
lean_dec(x_30);
x_36 = lean_int_add(x_35, x_31);
lean_dec(x_31);
lean_dec(x_35);
x_37 = lean_int_add(x_34, x_36);
lean_dec(x_36);
lean_dec(x_34);
x_38 = l_Std_Time_Duration_ofNanoseconds(x_37);
lean_dec(x_37);
x_39 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_38);
x_40 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_39);
x_41 = lean_mk_thunk(x_32);
lean_ctor_set(x_2, 1, x_41);
lean_ctor_set(x_2, 0, x_40);
return x_2;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_thunk_get_own(x_42);
lean_dec_ref(x_42);
x_44 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_48 = l_Std_Time_Duration_ofNanoseconds(x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_52 = lean_int_mul(x_45, x_51);
lean_dec(x_45);
x_53 = lean_int_add(x_52, x_46);
lean_dec(x_46);
lean_dec(x_52);
x_54 = lean_int_mul(x_49, x_51);
lean_dec(x_49);
x_55 = lean_int_add(x_54, x_50);
lean_dec(x_50);
lean_dec(x_54);
x_56 = lean_int_add(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
x_57 = l_Std_Time_Duration_ofNanoseconds(x_56);
lean_dec(x_56);
x_58 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_57);
lean_inc_ref(x_58);
x_59 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = l_Std_Time_TimeZone_toSeconds(x_1);
x_63 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_62);
lean_dec(x_62);
x_64 = lean_int_mul(x_63, x_51);
lean_dec(x_63);
x_65 = l_Std_Time_Duration_ofNanoseconds(x_64);
lean_dec(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_68, 0, x_58);
x_69 = lean_int_mul(x_60, x_51);
lean_dec(x_60);
x_70 = lean_int_add(x_69, x_61);
lean_dec(x_61);
lean_dec(x_69);
x_71 = lean_int_mul(x_66, x_51);
lean_dec(x_66);
x_72 = lean_int_add(x_71, x_67);
lean_dec(x_67);
lean_dec(x_71);
x_73 = lean_int_add(x_70, x_72);
lean_dec(x_72);
lean_dec(x_70);
x_74 = l_Std_Time_Duration_ofNanoseconds(x_73);
lean_dec(x_73);
x_75 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_74);
x_76 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_75);
x_77 = lean_mk_thunk(x_68);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subNanoseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_9);
x_11 = lean_int_add(x_10, x_3);
lean_dec(x_10);
x_12 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_12);
lean_inc_ref(x_7);
x_13 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_TimeZone_toSeconds(x_1);
x_17 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_16);
lean_dec(x_16);
x_18 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_19 = lean_int_mul(x_17, x_18);
lean_dec(x_17);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_7);
x_24 = lean_int_mul(x_14, x_18);
lean_dec(x_14);
x_25 = lean_int_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_26 = lean_int_mul(x_21, x_18);
lean_dec(x_21);
x_27 = lean_int_add(x_26, x_22);
lean_dec(x_22);
lean_dec(x_26);
x_28 = lean_int_add(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_29 = l_Std_Time_Duration_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_29);
x_31 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_30);
x_32 = lean_mk_thunk(x_23);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_33);
x_36 = lean_int_add(x_35, x_3);
lean_dec(x_35);
x_37 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
lean_inc_ref(x_38);
x_39 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Std_Time_TimeZone_toSeconds(x_1);
x_43 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_42);
lean_dec(x_42);
x_44 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_45 = lean_int_mul(x_43, x_44);
lean_dec(x_43);
x_46 = l_Std_Time_Duration_ofNanoseconds(x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_38);
x_50 = lean_int_mul(x_40, x_44);
lean_dec(x_40);
x_51 = lean_int_add(x_50, x_41);
lean_dec(x_41);
lean_dec(x_50);
x_52 = lean_int_mul(x_47, x_44);
lean_dec(x_47);
x_53 = lean_int_add(x_52, x_48);
lean_dec(x_48);
lean_dec(x_52);
x_54 = lean_int_add(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
x_55 = l_Std_Time_Duration_ofNanoseconds(x_54);
lean_dec(x_54);
x_56 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_55);
x_57 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_56);
x_58 = lean_mk_thunk(x_49);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_57);
return x_2;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_thunk_get_own(x_59);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_61);
x_65 = lean_int_add(x_64, x_3);
lean_dec(x_64);
x_66 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_65);
lean_dec(x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
lean_inc_ref(x_67);
x_68 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Std_Time_TimeZone_toSeconds(x_1);
x_72 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_74 = lean_int_mul(x_72, x_73);
lean_dec(x_72);
x_75 = l_Std_Time_Duration_ofNanoseconds(x_74);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_78, 0, x_67);
x_79 = lean_int_mul(x_69, x_73);
lean_dec(x_69);
x_80 = lean_int_add(x_79, x_70);
lean_dec(x_70);
lean_dec(x_79);
x_81 = lean_int_mul(x_76, x_73);
lean_dec(x_76);
x_82 = lean_int_add(x_81, x_77);
lean_dec(x_77);
lean_dec(x_81);
x_83 = lean_int_add(x_80, x_82);
lean_dec(x_82);
lean_dec(x_80);
x_84 = l_Std_Time_Duration_ofNanoseconds(x_83);
lean_dec(x_83);
x_85 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_84);
x_86 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_85);
x_87 = lean_mk_thunk(x_78);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addDays(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_11 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_9);
x_12 = lean_int_add(x_11, x_10);
lean_dec(x_10);
lean_dec(x_11);
x_13 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_12);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_13);
lean_inc_ref(x_7);
x_14 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Std_Time_TimeZone_toSeconds(x_1);
x_18 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_17);
lean_dec(x_17);
x_19 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_20 = lean_int_mul(x_18, x_19);
lean_dec(x_18);
x_21 = l_Std_Time_Duration_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_24, 0, x_7);
x_25 = lean_int_mul(x_15, x_19);
lean_dec(x_15);
x_26 = lean_int_add(x_25, x_16);
lean_dec(x_16);
lean_dec(x_25);
x_27 = lean_int_mul(x_22, x_19);
lean_dec(x_22);
x_28 = lean_int_add(x_27, x_23);
lean_dec(x_23);
lean_dec(x_27);
x_29 = lean_int_add(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
x_31 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_30);
x_32 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_31);
x_33 = lean_mk_thunk(x_24);
lean_ctor_set(x_2, 1, x_33);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_37 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_34);
x_38 = lean_int_add(x_37, x_36);
lean_dec(x_36);
lean_dec(x_37);
x_39 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
lean_inc_ref(x_40);
x_41 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Std_Time_TimeZone_toSeconds(x_1);
x_45 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_44);
lean_dec(x_44);
x_46 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_47 = lean_int_mul(x_45, x_46);
lean_dec(x_45);
x_48 = l_Std_Time_Duration_ofNanoseconds(x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_51, 0, x_40);
x_52 = lean_int_mul(x_42, x_46);
lean_dec(x_42);
x_53 = lean_int_add(x_52, x_43);
lean_dec(x_43);
lean_dec(x_52);
x_54 = lean_int_mul(x_49, x_46);
lean_dec(x_49);
x_55 = lean_int_add(x_54, x_50);
lean_dec(x_50);
lean_dec(x_54);
x_56 = lean_int_add(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
x_57 = l_Std_Time_Duration_ofNanoseconds(x_56);
lean_dec(x_56);
x_58 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_57);
x_59 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_58);
x_60 = lean_mk_thunk(x_51);
lean_ctor_set(x_2, 1, x_60);
lean_ctor_set(x_2, 0, x_59);
return x_2;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_61 = lean_ctor_get(x_2, 1);
lean_inc(x_61);
lean_dec(x_2);
x_62 = lean_thunk_get_own(x_61);
lean_dec_ref(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_67 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_63);
x_68 = lean_int_add(x_67, x_66);
lean_dec(x_66);
lean_dec(x_67);
x_69 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_68);
lean_dec(x_68);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
lean_inc_ref(x_70);
x_71 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Std_Time_TimeZone_toSeconds(x_1);
x_75 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_74);
lean_dec(x_74);
x_76 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_77 = lean_int_mul(x_75, x_76);
lean_dec(x_75);
x_78 = l_Std_Time_Duration_ofNanoseconds(x_77);
lean_dec(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_81, 0, x_70);
x_82 = lean_int_mul(x_72, x_76);
lean_dec(x_72);
x_83 = lean_int_add(x_82, x_73);
lean_dec(x_73);
lean_dec(x_82);
x_84 = lean_int_mul(x_79, x_76);
lean_dec(x_79);
x_85 = lean_int_add(x_84, x_80);
lean_dec(x_80);
lean_dec(x_84);
x_86 = lean_int_add(x_83, x_85);
lean_dec(x_85);
lean_dec(x_83);
x_87 = l_Std_Time_Duration_ofNanoseconds(x_86);
lean_dec(x_86);
x_88 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_87);
x_89 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_88);
x_90 = lean_mk_thunk(x_81);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subDays(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__0() {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_9);
x_11 = l_Std_Time_DateTime_addWeeks___closed__0;
x_12 = lean_int_mul(x_3, x_11);
x_13 = lean_int_add(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_13);
lean_dec(x_13);
lean_ctor_set(x_7, 0, x_14);
lean_inc_ref(x_7);
x_15 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Std_Time_TimeZone_toSeconds(x_1);
x_19 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_18);
lean_dec(x_18);
x_20 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_21 = lean_int_mul(x_19, x_20);
lean_dec(x_19);
x_22 = l_Std_Time_Duration_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_25, 0, x_7);
x_26 = lean_int_mul(x_16, x_20);
lean_dec(x_16);
x_27 = lean_int_add(x_26, x_17);
lean_dec(x_17);
lean_dec(x_26);
x_28 = lean_int_mul(x_23, x_20);
lean_dec(x_23);
x_29 = lean_int_add(x_28, x_24);
lean_dec(x_24);
lean_dec(x_28);
x_30 = lean_int_add(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
x_31 = l_Std_Time_Duration_ofNanoseconds(x_30);
lean_dec(x_30);
x_32 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_31);
x_33 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_32);
x_34 = lean_mk_thunk(x_25);
lean_ctor_set(x_2, 1, x_34);
lean_ctor_set(x_2, 0, x_33);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_35 = lean_ctor_get(x_7, 0);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_7);
x_37 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_35);
x_38 = l_Std_Time_DateTime_addWeeks___closed__0;
x_39 = lean_int_mul(x_3, x_38);
x_40 = lean_int_add(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
x_41 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
lean_inc_ref(x_42);
x_43 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = l_Std_Time_TimeZone_toSeconds(x_1);
x_47 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_46);
lean_dec(x_46);
x_48 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_49 = lean_int_mul(x_47, x_48);
lean_dec(x_47);
x_50 = l_Std_Time_Duration_ofNanoseconds(x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_53, 0, x_42);
x_54 = lean_int_mul(x_44, x_48);
lean_dec(x_44);
x_55 = lean_int_add(x_54, x_45);
lean_dec(x_45);
lean_dec(x_54);
x_56 = lean_int_mul(x_51, x_48);
lean_dec(x_51);
x_57 = lean_int_add(x_56, x_52);
lean_dec(x_52);
lean_dec(x_56);
x_58 = lean_int_add(x_55, x_57);
lean_dec(x_57);
lean_dec(x_55);
x_59 = l_Std_Time_Duration_ofNanoseconds(x_58);
lean_dec(x_58);
x_60 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_59);
x_61 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_60);
x_62 = lean_mk_thunk(x_53);
lean_ctor_set(x_2, 1, x_62);
lean_ctor_set(x_2, 0, x_61);
return x_2;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_dec(x_2);
x_64 = lean_thunk_get_own(x_63);
lean_dec_ref(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_65);
x_69 = l_Std_Time_DateTime_addWeeks___closed__0;
x_70 = lean_int_mul(x_3, x_69);
x_71 = lean_int_add(x_68, x_70);
lean_dec(x_70);
lean_dec(x_68);
x_72 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_71);
lean_dec(x_71);
if (lean_is_scalar(x_67)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_67;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
lean_inc_ref(x_73);
x_74 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_73);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = l_Std_Time_TimeZone_toSeconds(x_1);
x_78 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_77);
lean_dec(x_77);
x_79 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_80 = lean_int_mul(x_78, x_79);
lean_dec(x_78);
x_81 = l_Std_Time_Duration_ofNanoseconds(x_80);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_84, 0, x_73);
x_85 = lean_int_mul(x_75, x_79);
lean_dec(x_75);
x_86 = lean_int_add(x_85, x_76);
lean_dec(x_76);
lean_dec(x_85);
x_87 = lean_int_mul(x_82, x_79);
lean_dec(x_82);
x_88 = lean_int_add(x_87, x_83);
lean_dec(x_83);
lean_dec(x_87);
x_89 = lean_int_add(x_86, x_88);
lean_dec(x_88);
lean_dec(x_86);
x_90 = l_Std_Time_Duration_ofNanoseconds(x_89);
lean_dec(x_89);
x_91 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_90);
x_92 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_91);
x_93 = lean_mk_thunk(x_84);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addWeeks(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_11 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_9);
x_12 = l_Std_Time_DateTime_addWeeks___closed__0;
x_13 = lean_int_mul(x_10, x_12);
lean_dec(x_10);
x_14 = lean_int_add(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
x_15 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_14);
lean_dec(x_14);
lean_ctor_set(x_7, 0, x_15);
lean_inc_ref(x_7);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Std_Time_TimeZone_toSeconds(x_1);
x_20 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_19);
lean_dec(x_19);
x_21 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_22 = lean_int_mul(x_20, x_21);
lean_dec(x_20);
x_23 = l_Std_Time_Duration_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_7);
x_27 = lean_int_mul(x_17, x_21);
lean_dec(x_17);
x_28 = lean_int_add(x_27, x_18);
lean_dec(x_18);
lean_dec(x_27);
x_29 = lean_int_mul(x_24, x_21);
lean_dec(x_24);
x_30 = lean_int_add(x_29, x_25);
lean_dec(x_25);
lean_dec(x_29);
x_31 = lean_int_add(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
x_32 = l_Std_Time_Duration_ofNanoseconds(x_31);
lean_dec(x_31);
x_33 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_32);
x_34 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_33);
x_35 = lean_mk_thunk(x_26);
lean_ctor_set(x_2, 1, x_35);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_36 = lean_ctor_get(x_7, 0);
x_37 = lean_ctor_get(x_7, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_7);
x_38 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_39 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_36);
x_40 = l_Std_Time_DateTime_addWeeks___closed__0;
x_41 = lean_int_mul(x_38, x_40);
lean_dec(x_38);
x_42 = lean_int_add(x_39, x_41);
lean_dec(x_41);
lean_dec(x_39);
x_43 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
lean_inc_ref(x_44);
x_45 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = l_Std_Time_TimeZone_toSeconds(x_1);
x_49 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_48);
lean_dec(x_48);
x_50 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_51 = lean_int_mul(x_49, x_50);
lean_dec(x_49);
x_52 = l_Std_Time_Duration_ofNanoseconds(x_51);
lean_dec(x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_55, 0, x_44);
x_56 = lean_int_mul(x_46, x_50);
lean_dec(x_46);
x_57 = lean_int_add(x_56, x_47);
lean_dec(x_47);
lean_dec(x_56);
x_58 = lean_int_mul(x_53, x_50);
lean_dec(x_53);
x_59 = lean_int_add(x_58, x_54);
lean_dec(x_54);
lean_dec(x_58);
x_60 = lean_int_add(x_57, x_59);
lean_dec(x_59);
lean_dec(x_57);
x_61 = l_Std_Time_Duration_ofNanoseconds(x_60);
lean_dec(x_60);
x_62 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_61);
x_63 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_62);
x_64 = lean_mk_thunk(x_55);
lean_ctor_set(x_2, 1, x_64);
lean_ctor_set(x_2, 0, x_63);
return x_2;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_thunk_get_own(x_65);
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc_ref(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_3);
x_71 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_67);
x_72 = l_Std_Time_DateTime_addWeeks___closed__0;
x_73 = lean_int_mul(x_70, x_72);
lean_dec(x_70);
x_74 = lean_int_add(x_71, x_73);
lean_dec(x_73);
lean_dec(x_71);
x_75 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_74);
lean_dec(x_74);
if (lean_is_scalar(x_69)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_69;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_68);
lean_inc_ref(x_76);
x_77 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = l_Std_Time_TimeZone_toSeconds(x_1);
x_81 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_80);
lean_dec(x_80);
x_82 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_83 = lean_int_mul(x_81, x_82);
lean_dec(x_81);
x_84 = l_Std_Time_Duration_ofNanoseconds(x_83);
lean_dec(x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_87, 0, x_76);
x_88 = lean_int_mul(x_78, x_82);
lean_dec(x_78);
x_89 = lean_int_add(x_88, x_79);
lean_dec(x_79);
lean_dec(x_88);
x_90 = lean_int_mul(x_85, x_82);
lean_dec(x_85);
x_91 = lean_int_add(x_90, x_86);
lean_dec(x_86);
lean_dec(x_90);
x_92 = lean_int_add(x_89, x_91);
lean_dec(x_91);
lean_dec(x_89);
x_93 = l_Std_Time_Duration_ofNanoseconds(x_92);
lean_dec(x_92);
x_94 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_93);
x_95 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_94);
x_96 = lean_mk_thunk(x_87);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subWeeks(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_addMonthsClip(x_7, x_3);
lean_inc_ref(x_8);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Time_TimeZone_toSeconds(x_1);
x_13 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_12);
lean_dec(x_12);
x_14 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_15 = lean_int_mul(x_13, x_14);
lean_dec(x_13);
x_16 = l_Std_Time_Duration_ofNanoseconds(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_8);
x_20 = lean_int_mul(x_10, x_14);
lean_dec(x_10);
x_21 = lean_int_add(x_20, x_11);
lean_dec(x_11);
lean_dec(x_20);
x_22 = lean_int_mul(x_17, x_14);
lean_dec(x_17);
x_23 = lean_int_add(x_22, x_18);
lean_dec(x_18);
lean_dec(x_22);
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_Time_Duration_ofNanoseconds(x_24);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_25);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_mk_thunk(x_19);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_thunk_get_own(x_29);
lean_dec_ref(x_29);
x_31 = l_Std_Time_PlainDateTime_addMonthsClip(x_30, x_3);
lean_inc_ref(x_31);
x_32 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = l_Std_Time_TimeZone_toSeconds(x_1);
x_36 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_35);
lean_dec(x_35);
x_37 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_38 = lean_int_mul(x_36, x_37);
lean_dec(x_36);
x_39 = l_Std_Time_Duration_ofNanoseconds(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_42, 0, x_31);
x_43 = lean_int_mul(x_33, x_37);
lean_dec(x_33);
x_44 = lean_int_add(x_43, x_34);
lean_dec(x_34);
lean_dec(x_43);
x_45 = lean_int_mul(x_40, x_37);
lean_dec(x_40);
x_46 = lean_int_add(x_45, x_41);
lean_dec(x_41);
lean_dec(x_45);
x_47 = lean_int_add(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
x_48 = l_Std_Time_Duration_ofNanoseconds(x_47);
lean_dec(x_47);
x_49 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_48);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_mk_thunk(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addMonthsClip(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_int_neg(x_3);
x_11 = l_Std_Time_PlainDate_addMonthsClip(x_9, x_10);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_11);
lean_inc_ref(x_7);
x_12 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Std_Time_TimeZone_toSeconds(x_1);
x_16 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_18 = lean_int_mul(x_16, x_17);
lean_dec(x_16);
x_19 = l_Std_Time_Duration_ofNanoseconds(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_7);
x_23 = lean_int_mul(x_13, x_17);
lean_dec(x_13);
x_24 = lean_int_add(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
x_25 = lean_int_mul(x_20, x_17);
lean_dec(x_20);
x_26 = lean_int_add(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
x_27 = lean_int_add(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Std_Time_Duration_ofNanoseconds(x_27);
lean_dec(x_27);
x_29 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_28);
x_30 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_29);
x_31 = lean_mk_thunk(x_22);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_int_neg(x_3);
x_35 = l_Std_Time_PlainDate_addMonthsClip(x_32, x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_inc_ref(x_36);
x_37 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = l_Std_Time_TimeZone_toSeconds(x_1);
x_41 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_40);
lean_dec(x_40);
x_42 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_43 = lean_int_mul(x_41, x_42);
lean_dec(x_41);
x_44 = l_Std_Time_Duration_ofNanoseconds(x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_47, 0, x_36);
x_48 = lean_int_mul(x_38, x_42);
lean_dec(x_38);
x_49 = lean_int_add(x_48, x_39);
lean_dec(x_39);
lean_dec(x_48);
x_50 = lean_int_mul(x_45, x_42);
lean_dec(x_45);
x_51 = lean_int_add(x_50, x_46);
lean_dec(x_46);
lean_dec(x_50);
x_52 = lean_int_add(x_49, x_51);
lean_dec(x_51);
lean_dec(x_49);
x_53 = l_Std_Time_Duration_ofNanoseconds(x_52);
lean_dec(x_52);
x_54 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_53);
x_55 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_54);
x_56 = lean_mk_thunk(x_47);
lean_ctor_set(x_2, 1, x_56);
lean_ctor_set(x_2, 0, x_55);
return x_2;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
lean_dec(x_2);
x_58 = lean_thunk_get_own(x_57);
lean_dec_ref(x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_int_neg(x_3);
x_63 = l_Std_Time_PlainDate_addMonthsClip(x_59, x_62);
lean_dec(x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
lean_inc_ref(x_64);
x_65 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = l_Std_Time_TimeZone_toSeconds(x_1);
x_69 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_68);
lean_dec(x_68);
x_70 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_71 = lean_int_mul(x_69, x_70);
lean_dec(x_69);
x_72 = l_Std_Time_Duration_ofNanoseconds(x_71);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_75, 0, x_64);
x_76 = lean_int_mul(x_66, x_70);
lean_dec(x_66);
x_77 = lean_int_add(x_76, x_67);
lean_dec(x_67);
lean_dec(x_76);
x_78 = lean_int_mul(x_73, x_70);
lean_dec(x_73);
x_79 = lean_int_add(x_78, x_74);
lean_dec(x_74);
lean_dec(x_78);
x_80 = lean_int_add(x_77, x_79);
lean_dec(x_79);
lean_dec(x_77);
x_81 = l_Std_Time_Duration_ofNanoseconds(x_80);
lean_dec(x_80);
x_82 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_81);
x_83 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_82);
x_84 = lean_mk_thunk(x_75);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subMonthsClip(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_addMonthsRollOver(x_7, x_3);
lean_inc_ref(x_8);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Time_TimeZone_toSeconds(x_1);
x_13 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_12);
lean_dec(x_12);
x_14 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_15 = lean_int_mul(x_13, x_14);
lean_dec(x_13);
x_16 = l_Std_Time_Duration_ofNanoseconds(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_8);
x_20 = lean_int_mul(x_10, x_14);
lean_dec(x_10);
x_21 = lean_int_add(x_20, x_11);
lean_dec(x_11);
lean_dec(x_20);
x_22 = lean_int_mul(x_17, x_14);
lean_dec(x_17);
x_23 = lean_int_add(x_22, x_18);
lean_dec(x_18);
lean_dec(x_22);
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_Time_Duration_ofNanoseconds(x_24);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_25);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_mk_thunk(x_19);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_thunk_get_own(x_29);
lean_dec_ref(x_29);
x_31 = l_Std_Time_PlainDateTime_addMonthsRollOver(x_30, x_3);
lean_inc_ref(x_31);
x_32 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = l_Std_Time_TimeZone_toSeconds(x_1);
x_36 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_35);
lean_dec(x_35);
x_37 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_38 = lean_int_mul(x_36, x_37);
lean_dec(x_36);
x_39 = l_Std_Time_Duration_ofNanoseconds(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_42, 0, x_31);
x_43 = lean_int_mul(x_33, x_37);
lean_dec(x_33);
x_44 = lean_int_add(x_43, x_34);
lean_dec(x_34);
lean_dec(x_43);
x_45 = lean_int_mul(x_40, x_37);
lean_dec(x_40);
x_46 = lean_int_add(x_45, x_41);
lean_dec(x_41);
lean_dec(x_45);
x_47 = lean_int_add(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
x_48 = l_Std_Time_Duration_ofNanoseconds(x_47);
lean_dec(x_47);
x_49 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_48);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_mk_thunk(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addMonthsRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_int_neg(x_3);
x_11 = l_Std_Time_PlainDate_addMonthsRollOver(x_9, x_10);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_11);
lean_inc_ref(x_7);
x_12 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Std_Time_TimeZone_toSeconds(x_1);
x_16 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_18 = lean_int_mul(x_16, x_17);
lean_dec(x_16);
x_19 = l_Std_Time_Duration_ofNanoseconds(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_7);
x_23 = lean_int_mul(x_13, x_17);
lean_dec(x_13);
x_24 = lean_int_add(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
x_25 = lean_int_mul(x_20, x_17);
lean_dec(x_20);
x_26 = lean_int_add(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
x_27 = lean_int_add(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Std_Time_Duration_ofNanoseconds(x_27);
lean_dec(x_27);
x_29 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_28);
x_30 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_29);
x_31 = lean_mk_thunk(x_22);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_int_neg(x_3);
x_35 = l_Std_Time_PlainDate_addMonthsRollOver(x_32, x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
lean_inc_ref(x_36);
x_37 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = l_Std_Time_TimeZone_toSeconds(x_1);
x_41 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_40);
lean_dec(x_40);
x_42 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_43 = lean_int_mul(x_41, x_42);
lean_dec(x_41);
x_44 = l_Std_Time_Duration_ofNanoseconds(x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_47, 0, x_36);
x_48 = lean_int_mul(x_38, x_42);
lean_dec(x_38);
x_49 = lean_int_add(x_48, x_39);
lean_dec(x_39);
lean_dec(x_48);
x_50 = lean_int_mul(x_45, x_42);
lean_dec(x_45);
x_51 = lean_int_add(x_50, x_46);
lean_dec(x_46);
lean_dec(x_50);
x_52 = lean_int_add(x_49, x_51);
lean_dec(x_51);
lean_dec(x_49);
x_53 = l_Std_Time_Duration_ofNanoseconds(x_52);
lean_dec(x_52);
x_54 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_53);
x_55 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_54);
x_56 = lean_mk_thunk(x_47);
lean_ctor_set(x_2, 1, x_56);
lean_ctor_set(x_2, 0, x_55);
return x_2;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_57 = lean_ctor_get(x_2, 1);
lean_inc(x_57);
lean_dec(x_2);
x_58 = lean_thunk_get_own(x_57);
lean_dec_ref(x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_int_neg(x_3);
x_63 = l_Std_Time_PlainDate_addMonthsRollOver(x_59, x_62);
lean_dec(x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
lean_inc_ref(x_64);
x_65 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = l_Std_Time_TimeZone_toSeconds(x_1);
x_69 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_68);
lean_dec(x_68);
x_70 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_71 = lean_int_mul(x_69, x_70);
lean_dec(x_69);
x_72 = l_Std_Time_Duration_ofNanoseconds(x_71);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec_ref(x_72);
x_75 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_75, 0, x_64);
x_76 = lean_int_mul(x_66, x_70);
lean_dec(x_66);
x_77 = lean_int_add(x_76, x_67);
lean_dec(x_67);
lean_dec(x_76);
x_78 = lean_int_mul(x_73, x_70);
lean_dec(x_73);
x_79 = lean_int_add(x_78, x_74);
lean_dec(x_74);
lean_dec(x_78);
x_80 = lean_int_add(x_77, x_79);
lean_dec(x_79);
lean_dec(x_77);
x_81 = l_Std_Time_Duration_ofNanoseconds(x_80);
lean_dec(x_80);
x_82 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_81);
x_83 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_82);
x_84 = lean_mk_thunk(x_75);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subMonthsRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__0() {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_11 = lean_int_mul(x_3, x_10);
x_12 = l_Std_Time_PlainDate_addMonthsRollOver(x_9, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_12);
lean_inc_ref(x_7);
x_13 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_TimeZone_toSeconds(x_1);
x_17 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_16);
lean_dec(x_16);
x_18 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_19 = lean_int_mul(x_17, x_18);
lean_dec(x_17);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_7);
x_24 = lean_int_mul(x_14, x_18);
lean_dec(x_14);
x_25 = lean_int_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_26 = lean_int_mul(x_21, x_18);
lean_dec(x_21);
x_27 = lean_int_add(x_26, x_22);
lean_dec(x_22);
lean_dec(x_26);
x_28 = lean_int_add(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_29 = l_Std_Time_Duration_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_29);
x_31 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_30);
x_32 = lean_mk_thunk(x_23);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_36 = lean_int_mul(x_3, x_35);
x_37 = l_Std_Time_PlainDate_addMonthsRollOver(x_33, x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
lean_inc_ref(x_38);
x_39 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Std_Time_TimeZone_toSeconds(x_1);
x_43 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_42);
lean_dec(x_42);
x_44 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_45 = lean_int_mul(x_43, x_44);
lean_dec(x_43);
x_46 = l_Std_Time_Duration_ofNanoseconds(x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_38);
x_50 = lean_int_mul(x_40, x_44);
lean_dec(x_40);
x_51 = lean_int_add(x_50, x_41);
lean_dec(x_41);
lean_dec(x_50);
x_52 = lean_int_mul(x_47, x_44);
lean_dec(x_47);
x_53 = lean_int_add(x_52, x_48);
lean_dec(x_48);
lean_dec(x_52);
x_54 = lean_int_add(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
x_55 = l_Std_Time_Duration_ofNanoseconds(x_54);
lean_dec(x_54);
x_56 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_55);
x_57 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_56);
x_58 = lean_mk_thunk(x_49);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_57);
return x_2;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_thunk_get_own(x_59);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_65 = lean_int_mul(x_3, x_64);
x_66 = l_Std_Time_PlainDate_addMonthsRollOver(x_61, x_65);
lean_dec(x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
lean_inc_ref(x_67);
x_68 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Std_Time_TimeZone_toSeconds(x_1);
x_72 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_74 = lean_int_mul(x_72, x_73);
lean_dec(x_72);
x_75 = l_Std_Time_Duration_ofNanoseconds(x_74);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_78, 0, x_67);
x_79 = lean_int_mul(x_69, x_73);
lean_dec(x_69);
x_80 = lean_int_add(x_79, x_70);
lean_dec(x_70);
lean_dec(x_79);
x_81 = lean_int_mul(x_76, x_73);
lean_dec(x_76);
x_82 = lean_int_add(x_81, x_77);
lean_dec(x_77);
lean_dec(x_81);
x_83 = lean_int_add(x_80, x_82);
lean_dec(x_82);
lean_dec(x_80);
x_84 = l_Std_Time_Duration_ofNanoseconds(x_83);
lean_dec(x_83);
x_85 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_84);
x_86 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_85);
x_87 = lean_mk_thunk(x_78);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addYearsRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_11 = lean_int_mul(x_3, x_10);
x_12 = l_Std_Time_PlainDate_addMonthsClip(x_9, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_12);
lean_inc_ref(x_7);
x_13 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_TimeZone_toSeconds(x_1);
x_17 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_16);
lean_dec(x_16);
x_18 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_19 = lean_int_mul(x_17, x_18);
lean_dec(x_17);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_7);
x_24 = lean_int_mul(x_14, x_18);
lean_dec(x_14);
x_25 = lean_int_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_26 = lean_int_mul(x_21, x_18);
lean_dec(x_21);
x_27 = lean_int_add(x_26, x_22);
lean_dec(x_22);
lean_dec(x_26);
x_28 = lean_int_add(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_29 = l_Std_Time_Duration_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_29);
x_31 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_30);
x_32 = lean_mk_thunk(x_23);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_36 = lean_int_mul(x_3, x_35);
x_37 = l_Std_Time_PlainDate_addMonthsClip(x_33, x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
lean_inc_ref(x_38);
x_39 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Std_Time_TimeZone_toSeconds(x_1);
x_43 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_42);
lean_dec(x_42);
x_44 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_45 = lean_int_mul(x_43, x_44);
lean_dec(x_43);
x_46 = l_Std_Time_Duration_ofNanoseconds(x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_38);
x_50 = lean_int_mul(x_40, x_44);
lean_dec(x_40);
x_51 = lean_int_add(x_50, x_41);
lean_dec(x_41);
lean_dec(x_50);
x_52 = lean_int_mul(x_47, x_44);
lean_dec(x_47);
x_53 = lean_int_add(x_52, x_48);
lean_dec(x_48);
lean_dec(x_52);
x_54 = lean_int_add(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
x_55 = l_Std_Time_Duration_ofNanoseconds(x_54);
lean_dec(x_54);
x_56 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_55);
x_57 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_56);
x_58 = lean_mk_thunk(x_49);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_57);
return x_2;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_thunk_get_own(x_59);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_65 = lean_int_mul(x_3, x_64);
x_66 = l_Std_Time_PlainDate_addMonthsClip(x_61, x_65);
lean_dec(x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
lean_inc_ref(x_67);
x_68 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Std_Time_TimeZone_toSeconds(x_1);
x_72 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_74 = lean_int_mul(x_72, x_73);
lean_dec(x_72);
x_75 = l_Std_Time_Duration_ofNanoseconds(x_74);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_78, 0, x_67);
x_79 = lean_int_mul(x_69, x_73);
lean_dec(x_69);
x_80 = lean_int_add(x_79, x_70);
lean_dec(x_70);
lean_dec(x_79);
x_81 = lean_int_mul(x_76, x_73);
lean_dec(x_76);
x_82 = lean_int_add(x_81, x_77);
lean_dec(x_77);
lean_dec(x_81);
x_83 = lean_int_add(x_80, x_82);
lean_dec(x_82);
lean_dec(x_80);
x_84 = l_Std_Time_Duration_ofNanoseconds(x_83);
lean_dec(x_83);
x_85 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_84);
x_86 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_85);
x_87 = lean_mk_thunk(x_78);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_addYearsClip(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_11 = lean_int_mul(x_3, x_10);
x_12 = lean_int_neg(x_11);
lean_dec(x_11);
x_13 = l_Std_Time_PlainDate_addMonthsRollOver(x_9, x_12);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_13);
lean_inc_ref(x_7);
x_14 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Std_Time_TimeZone_toSeconds(x_1);
x_18 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_17);
lean_dec(x_17);
x_19 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_20 = lean_int_mul(x_18, x_19);
lean_dec(x_18);
x_21 = l_Std_Time_Duration_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_24, 0, x_7);
x_25 = lean_int_mul(x_15, x_19);
lean_dec(x_15);
x_26 = lean_int_add(x_25, x_16);
lean_dec(x_16);
lean_dec(x_25);
x_27 = lean_int_mul(x_22, x_19);
lean_dec(x_22);
x_28 = lean_int_add(x_27, x_23);
lean_dec(x_23);
lean_dec(x_27);
x_29 = lean_int_add(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
x_31 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_30);
x_32 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_31);
x_33 = lean_mk_thunk(x_24);
lean_ctor_set(x_2, 1, x_33);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_37 = lean_int_mul(x_3, x_36);
x_38 = lean_int_neg(x_37);
lean_dec(x_37);
x_39 = l_Std_Time_PlainDate_addMonthsRollOver(x_34, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
lean_inc_ref(x_40);
x_41 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Std_Time_TimeZone_toSeconds(x_1);
x_45 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_44);
lean_dec(x_44);
x_46 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_47 = lean_int_mul(x_45, x_46);
lean_dec(x_45);
x_48 = l_Std_Time_Duration_ofNanoseconds(x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_51, 0, x_40);
x_52 = lean_int_mul(x_42, x_46);
lean_dec(x_42);
x_53 = lean_int_add(x_52, x_43);
lean_dec(x_43);
lean_dec(x_52);
x_54 = lean_int_mul(x_49, x_46);
lean_dec(x_49);
x_55 = lean_int_add(x_54, x_50);
lean_dec(x_50);
lean_dec(x_54);
x_56 = lean_int_add(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
x_57 = l_Std_Time_Duration_ofNanoseconds(x_56);
lean_dec(x_56);
x_58 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_57);
x_59 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_58);
x_60 = lean_mk_thunk(x_51);
lean_ctor_set(x_2, 1, x_60);
lean_ctor_set(x_2, 0, x_59);
return x_2;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_61 = lean_ctor_get(x_2, 1);
lean_inc(x_61);
lean_dec(x_2);
x_62 = lean_thunk_get_own(x_61);
lean_dec_ref(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_67 = lean_int_mul(x_3, x_66);
x_68 = lean_int_neg(x_67);
lean_dec(x_67);
x_69 = l_Std_Time_PlainDate_addMonthsRollOver(x_63, x_68);
lean_dec(x_68);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
lean_inc_ref(x_70);
x_71 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Std_Time_TimeZone_toSeconds(x_1);
x_75 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_74);
lean_dec(x_74);
x_76 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_77 = lean_int_mul(x_75, x_76);
lean_dec(x_75);
x_78 = l_Std_Time_Duration_ofNanoseconds(x_77);
lean_dec(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_81, 0, x_70);
x_82 = lean_int_mul(x_72, x_76);
lean_dec(x_72);
x_83 = lean_int_add(x_82, x_73);
lean_dec(x_73);
lean_dec(x_82);
x_84 = lean_int_mul(x_79, x_76);
lean_dec(x_79);
x_85 = lean_int_add(x_84, x_80);
lean_dec(x_80);
lean_dec(x_84);
x_86 = lean_int_add(x_83, x_85);
lean_dec(x_85);
lean_dec(x_83);
x_87 = l_Std_Time_Duration_ofNanoseconds(x_86);
lean_dec(x_86);
x_88 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_87);
x_89 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_88);
x_90 = lean_mk_thunk(x_81);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subYearsRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_11 = lean_int_mul(x_3, x_10);
x_12 = lean_int_neg(x_11);
lean_dec(x_11);
x_13 = l_Std_Time_PlainDate_addMonthsClip(x_9, x_12);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_13);
lean_inc_ref(x_7);
x_14 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Std_Time_TimeZone_toSeconds(x_1);
x_18 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_17);
lean_dec(x_17);
x_19 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_20 = lean_int_mul(x_18, x_19);
lean_dec(x_18);
x_21 = l_Std_Time_Duration_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_24, 0, x_7);
x_25 = lean_int_mul(x_15, x_19);
lean_dec(x_15);
x_26 = lean_int_add(x_25, x_16);
lean_dec(x_16);
lean_dec(x_25);
x_27 = lean_int_mul(x_22, x_19);
lean_dec(x_22);
x_28 = lean_int_add(x_27, x_23);
lean_dec(x_23);
lean_dec(x_27);
x_29 = lean_int_add(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
x_31 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_30);
x_32 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_31);
x_33 = lean_mk_thunk(x_24);
lean_ctor_set(x_2, 1, x_33);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_34 = lean_ctor_get(x_7, 0);
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_7);
x_36 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_37 = lean_int_mul(x_3, x_36);
x_38 = lean_int_neg(x_37);
lean_dec(x_37);
x_39 = l_Std_Time_PlainDate_addMonthsClip(x_34, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
lean_inc_ref(x_40);
x_41 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec_ref(x_41);
x_44 = l_Std_Time_TimeZone_toSeconds(x_1);
x_45 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_44);
lean_dec(x_44);
x_46 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_47 = lean_int_mul(x_45, x_46);
lean_dec(x_45);
x_48 = l_Std_Time_Duration_ofNanoseconds(x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_51, 0, x_40);
x_52 = lean_int_mul(x_42, x_46);
lean_dec(x_42);
x_53 = lean_int_add(x_52, x_43);
lean_dec(x_43);
lean_dec(x_52);
x_54 = lean_int_mul(x_49, x_46);
lean_dec(x_49);
x_55 = lean_int_add(x_54, x_50);
lean_dec(x_50);
lean_dec(x_54);
x_56 = lean_int_add(x_53, x_55);
lean_dec(x_55);
lean_dec(x_53);
x_57 = l_Std_Time_Duration_ofNanoseconds(x_56);
lean_dec(x_56);
x_58 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_57);
x_59 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_58);
x_60 = lean_mk_thunk(x_51);
lean_ctor_set(x_2, 1, x_60);
lean_ctor_set(x_2, 0, x_59);
return x_2;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_61 = lean_ctor_get(x_2, 1);
lean_inc(x_61);
lean_dec(x_2);
x_62 = lean_thunk_get_own(x_61);
lean_dec_ref(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = l_Std_Time_DateTime_addYearsRollOver___closed__0;
x_67 = lean_int_mul(x_3, x_66);
x_68 = lean_int_neg(x_67);
lean_dec(x_67);
x_69 = l_Std_Time_PlainDate_addMonthsClip(x_63, x_68);
lean_dec(x_68);
if (lean_is_scalar(x_65)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_65;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
lean_inc_ref(x_70);
x_71 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = l_Std_Time_TimeZone_toSeconds(x_1);
x_75 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_74);
lean_dec(x_74);
x_76 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_77 = lean_int_mul(x_75, x_76);
lean_dec(x_75);
x_78 = l_Std_Time_Duration_ofNanoseconds(x_77);
lean_dec(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_81, 0, x_70);
x_82 = lean_int_mul(x_72, x_76);
lean_dec(x_72);
x_83 = lean_int_add(x_82, x_73);
lean_dec(x_73);
lean_dec(x_82);
x_84 = lean_int_mul(x_79, x_76);
lean_dec(x_79);
x_85 = lean_int_add(x_84, x_80);
lean_dec(x_80);
lean_dec(x_84);
x_86 = lean_int_add(x_83, x_85);
lean_dec(x_85);
lean_dec(x_83);
x_87 = l_Std_Time_Duration_ofNanoseconds(x_86);
lean_dec(x_86);
x_88 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_87);
x_89 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_88);
x_90 = lean_mk_thunk(x_81);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_subYearsClip(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_5 = x_2;
} else {
 lean_dec_ref(x_2);
 x_5 = lean_box(0);
}
x_6 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_55 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_65 = l_Std_Time_DateTime_withDaysClip___closed__0;
x_66 = lean_int_mod(x_56, x_65);
x_67 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_68 = lean_int_dec_eq(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
x_59 = x_68;
goto block_64;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; 
x_69 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_70 = lean_int_mod(x_56, x_69);
x_71 = lean_int_dec_eq(x_70, x_67);
lean_dec(x_70);
x_72 = l_instDecidableNot___redArg(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_74 = lean_int_mod(x_56, x_73);
x_75 = lean_int_dec_eq(x_74, x_67);
lean_dec(x_74);
x_59 = x_75;
goto block_64;
}
else
{
x_59 = x_72;
goto block_64;
}
}
block_54:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_7);
lean_inc_ref(x_6);
x_10 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Time_TimeZone_toSeconds(x_1);
x_14 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_13);
lean_dec(x_13);
x_15 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_16 = lean_int_mul(x_14, x_15);
lean_dec(x_14);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_20, 0, x_6);
x_21 = lean_int_mul(x_11, x_15);
lean_dec(x_11);
x_22 = lean_int_add(x_21, x_12);
lean_dec(x_12);
lean_dec(x_21);
x_23 = lean_int_mul(x_18, x_15);
lean_dec(x_18);
x_24 = lean_int_add(x_23, x_19);
lean_dec(x_19);
lean_dec(x_23);
x_25 = lean_int_add(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
x_26 = l_Std_Time_Duration_ofNanoseconds(x_25);
lean_dec(x_25);
x_27 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_26);
x_28 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_27);
x_29 = lean_mk_thunk(x_20);
if (lean_is_scalar(x_5)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_5;
}
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_inc_ref(x_32);
x_33 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Std_Time_TimeZone_toSeconds(x_1);
x_37 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_36);
lean_dec(x_36);
x_38 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_39 = lean_int_mul(x_37, x_38);
lean_dec(x_37);
x_40 = l_Std_Time_Duration_ofNanoseconds(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_43, 0, x_32);
x_44 = lean_int_mul(x_34, x_38);
lean_dec(x_34);
x_45 = lean_int_add(x_44, x_35);
lean_dec(x_35);
lean_dec(x_44);
x_46 = lean_int_mul(x_41, x_38);
lean_dec(x_41);
x_47 = lean_int_add(x_46, x_42);
lean_dec(x_42);
lean_dec(x_46);
x_48 = lean_int_add(x_45, x_47);
lean_dec(x_47);
lean_dec(x_45);
x_49 = l_Std_Time_Duration_ofNanoseconds(x_48);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_49);
x_51 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_50);
x_52 = lean_mk_thunk(x_43);
if (lean_is_scalar(x_5)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_5;
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
block_64:
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Std_Time_Month_Ordinal_days(x_59, x_57);
x_61 = lean_int_dec_lt(x_60, x_3);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 3, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_57);
lean_ctor_set(x_62, 2, x_3);
x_7 = x_62;
goto block_54;
}
else
{
lean_object* x_63; 
lean_dec(x_3);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 3, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_63, 2, x_60);
x_7 = x_63;
goto block_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withDaysClip(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Time_PlainDate_rollOver(x_10, x_11, x_3);
lean_ctor_set(x_7, 0, x_12);
lean_inc_ref(x_7);
x_13 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_TimeZone_toSeconds(x_1);
x_17 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_16);
lean_dec(x_16);
x_18 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_19 = lean_int_mul(x_17, x_18);
lean_dec(x_17);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_7);
x_24 = lean_int_mul(x_14, x_18);
lean_dec(x_14);
x_25 = lean_int_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_26 = lean_int_mul(x_21, x_18);
lean_dec(x_21);
x_27 = lean_int_add(x_26, x_22);
lean_dec(x_22);
lean_dec(x_26);
x_28 = lean_int_add(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_29 = l_Std_Time_Duration_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_29);
x_31 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_30);
x_32 = lean_mk_thunk(x_23);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = l_Std_Time_PlainDate_rollOver(x_35, x_36, x_3);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
lean_inc_ref(x_38);
x_39 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Std_Time_TimeZone_toSeconds(x_1);
x_43 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_42);
lean_dec(x_42);
x_44 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_45 = lean_int_mul(x_43, x_44);
lean_dec(x_43);
x_46 = l_Std_Time_Duration_ofNanoseconds(x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_38);
x_50 = lean_int_mul(x_40, x_44);
lean_dec(x_40);
x_51 = lean_int_add(x_50, x_41);
lean_dec(x_41);
lean_dec(x_50);
x_52 = lean_int_mul(x_47, x_44);
lean_dec(x_47);
x_53 = lean_int_add(x_52, x_48);
lean_dec(x_48);
lean_dec(x_52);
x_54 = lean_int_add(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
x_55 = l_Std_Time_Duration_ofNanoseconds(x_54);
lean_dec(x_54);
x_56 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_55);
x_57 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_56);
x_58 = lean_mk_thunk(x_49);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_57);
return x_2;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_thunk_get_own(x_59);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec_ref(x_61);
x_66 = l_Std_Time_PlainDate_rollOver(x_64, x_65, x_3);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
lean_inc_ref(x_67);
x_68 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Std_Time_TimeZone_toSeconds(x_1);
x_72 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_74 = lean_int_mul(x_72, x_73);
lean_dec(x_72);
x_75 = l_Std_Time_Duration_ofNanoseconds(x_74);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_78, 0, x_67);
x_79 = lean_int_mul(x_69, x_73);
lean_dec(x_69);
x_80 = lean_int_add(x_79, x_70);
lean_dec(x_70);
lean_dec(x_79);
x_81 = lean_int_mul(x_76, x_73);
lean_dec(x_76);
x_82 = lean_int_add(x_81, x_77);
lean_dec(x_77);
lean_dec(x_81);
x_83 = lean_int_add(x_80, x_82);
lean_dec(x_82);
lean_dec(x_80);
x_84 = l_Std_Time_Duration_ofNanoseconds(x_83);
lean_dec(x_83);
x_85 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_84);
x_86 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_85);
x_87 = lean_mk_thunk(x_78);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withDaysRollOver(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_5 = x_2;
} else {
 lean_dec_ref(x_2);
 x_5 = lean_box(0);
}
x_6 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_55 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 2);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_65 = l_Std_Time_DateTime_withDaysClip___closed__0;
x_66 = lean_int_mod(x_56, x_65);
x_67 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_68 = lean_int_dec_eq(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
x_59 = x_68;
goto block_64;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; 
x_69 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_70 = lean_int_mod(x_56, x_69);
x_71 = lean_int_dec_eq(x_70, x_67);
lean_dec(x_70);
x_72 = l_instDecidableNot___redArg(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_74 = lean_int_mod(x_56, x_73);
x_75 = lean_int_dec_eq(x_74, x_67);
lean_dec(x_74);
x_59 = x_75;
goto block_64;
}
else
{
x_59 = x_72;
goto block_64;
}
}
block_54:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_7);
lean_inc_ref(x_6);
x_10 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Time_TimeZone_toSeconds(x_1);
x_14 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_13);
lean_dec(x_13);
x_15 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_16 = lean_int_mul(x_14, x_15);
lean_dec(x_14);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_20, 0, x_6);
x_21 = lean_int_mul(x_11, x_15);
lean_dec(x_11);
x_22 = lean_int_add(x_21, x_12);
lean_dec(x_12);
lean_dec(x_21);
x_23 = lean_int_mul(x_18, x_15);
lean_dec(x_18);
x_24 = lean_int_add(x_23, x_19);
lean_dec(x_19);
lean_dec(x_23);
x_25 = lean_int_add(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
x_26 = l_Std_Time_Duration_ofNanoseconds(x_25);
lean_dec(x_25);
x_27 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_26);
x_28 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_27);
x_29 = lean_mk_thunk(x_20);
if (lean_is_scalar(x_5)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_5;
}
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_inc_ref(x_32);
x_33 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Std_Time_TimeZone_toSeconds(x_1);
x_37 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_36);
lean_dec(x_36);
x_38 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_39 = lean_int_mul(x_37, x_38);
lean_dec(x_37);
x_40 = l_Std_Time_Duration_ofNanoseconds(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_43, 0, x_32);
x_44 = lean_int_mul(x_34, x_38);
lean_dec(x_34);
x_45 = lean_int_add(x_44, x_35);
lean_dec(x_35);
lean_dec(x_44);
x_46 = lean_int_mul(x_41, x_38);
lean_dec(x_41);
x_47 = lean_int_add(x_46, x_42);
lean_dec(x_42);
lean_dec(x_46);
x_48 = lean_int_add(x_45, x_47);
lean_dec(x_47);
lean_dec(x_45);
x_49 = l_Std_Time_Duration_ofNanoseconds(x_48);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_49);
x_51 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_50);
x_52 = lean_mk_thunk(x_43);
if (lean_is_scalar(x_5)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_5;
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
block_64:
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Std_Time_Month_Ordinal_days(x_59, x_3);
x_61 = lean_int_dec_lt(x_60, x_57);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 3, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_3);
lean_ctor_set(x_62, 2, x_57);
x_7 = x_62;
goto block_54;
}
else
{
lean_object* x_63; 
lean_dec(x_57);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 3, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_3);
lean_ctor_set(x_63, 2, x_60);
x_7 = x_63;
goto block_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withMonthClip(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Time_PlainDate_rollOver(x_10, x_3, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_12);
lean_inc_ref(x_7);
x_13 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_TimeZone_toSeconds(x_1);
x_17 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_16);
lean_dec(x_16);
x_18 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_19 = lean_int_mul(x_17, x_18);
lean_dec(x_17);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_7);
x_24 = lean_int_mul(x_14, x_18);
lean_dec(x_14);
x_25 = lean_int_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_26 = lean_int_mul(x_21, x_18);
lean_dec(x_21);
x_27 = lean_int_add(x_26, x_22);
lean_dec(x_22);
lean_dec(x_26);
x_28 = lean_int_add(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_29 = l_Std_Time_Duration_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_29);
x_31 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_30);
x_32 = lean_mk_thunk(x_23);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 2);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = l_Std_Time_PlainDate_rollOver(x_35, x_3, x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
lean_inc_ref(x_38);
x_39 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Std_Time_TimeZone_toSeconds(x_1);
x_43 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_42);
lean_dec(x_42);
x_44 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_45 = lean_int_mul(x_43, x_44);
lean_dec(x_43);
x_46 = l_Std_Time_Duration_ofNanoseconds(x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_38);
x_50 = lean_int_mul(x_40, x_44);
lean_dec(x_40);
x_51 = lean_int_add(x_50, x_41);
lean_dec(x_41);
lean_dec(x_50);
x_52 = lean_int_mul(x_47, x_44);
lean_dec(x_47);
x_53 = lean_int_add(x_52, x_48);
lean_dec(x_48);
lean_dec(x_52);
x_54 = lean_int_add(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
x_55 = l_Std_Time_Duration_ofNanoseconds(x_54);
lean_dec(x_54);
x_56 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_55);
x_57 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_56);
x_58 = lean_mk_thunk(x_49);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_57);
return x_2;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_thunk_get_own(x_59);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
lean_dec_ref(x_61);
x_66 = l_Std_Time_PlainDate_rollOver(x_64, x_3, x_65);
lean_dec(x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
lean_inc_ref(x_67);
x_68 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Std_Time_TimeZone_toSeconds(x_1);
x_72 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_74 = lean_int_mul(x_72, x_73);
lean_dec(x_72);
x_75 = l_Std_Time_Duration_ofNanoseconds(x_74);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_78, 0, x_67);
x_79 = lean_int_mul(x_69, x_73);
lean_dec(x_69);
x_80 = lean_int_add(x_79, x_70);
lean_dec(x_70);
lean_dec(x_79);
x_81 = lean_int_mul(x_76, x_73);
lean_dec(x_76);
x_82 = lean_int_add(x_81, x_77);
lean_dec(x_77);
lean_dec(x_81);
x_83 = lean_int_add(x_80, x_82);
lean_dec(x_82);
lean_dec(x_80);
x_84 = l_Std_Time_Duration_ofNanoseconds(x_83);
lean_dec(x_83);
x_85 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_84);
x_86 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_85);
x_87 = lean_mk_thunk(x_78);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withMonthRollOver(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_5 = x_2;
} else {
 lean_dec_ref(x_2);
 x_5 = lean_box(0);
}
x_6 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_55 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 2);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
x_65 = l_Std_Time_DateTime_withDaysClip___closed__0;
x_66 = lean_int_mod(x_3, x_65);
x_67 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_68 = lean_int_dec_eq(x_66, x_67);
lean_dec(x_66);
if (x_68 == 0)
{
x_59 = x_68;
goto block_64;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; 
x_69 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_70 = lean_int_mod(x_3, x_69);
x_71 = lean_int_dec_eq(x_70, x_67);
lean_dec(x_70);
x_72 = l_instDecidableNot___redArg(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_74 = lean_int_mod(x_3, x_73);
x_75 = lean_int_dec_eq(x_74, x_67);
lean_dec(x_74);
x_59 = x_75;
goto block_64;
}
else
{
x_59 = x_72;
goto block_64;
}
}
block_54:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_7);
lean_inc_ref(x_6);
x_10 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Time_TimeZone_toSeconds(x_1);
x_14 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_13);
lean_dec(x_13);
x_15 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_16 = lean_int_mul(x_14, x_15);
lean_dec(x_14);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_20, 0, x_6);
x_21 = lean_int_mul(x_11, x_15);
lean_dec(x_11);
x_22 = lean_int_add(x_21, x_12);
lean_dec(x_12);
lean_dec(x_21);
x_23 = lean_int_mul(x_18, x_15);
lean_dec(x_18);
x_24 = lean_int_add(x_23, x_19);
lean_dec(x_19);
lean_dec(x_23);
x_25 = lean_int_add(x_22, x_24);
lean_dec(x_24);
lean_dec(x_22);
x_26 = l_Std_Time_Duration_ofNanoseconds(x_25);
lean_dec(x_25);
x_27 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_26);
x_28 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_27);
x_29 = lean_mk_thunk(x_20);
if (lean_is_scalar(x_5)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_5;
}
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_31);
lean_inc_ref(x_32);
x_33 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = l_Std_Time_TimeZone_toSeconds(x_1);
x_37 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_36);
lean_dec(x_36);
x_38 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_39 = lean_int_mul(x_37, x_38);
lean_dec(x_37);
x_40 = l_Std_Time_Duration_ofNanoseconds(x_39);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_43, 0, x_32);
x_44 = lean_int_mul(x_34, x_38);
lean_dec(x_34);
x_45 = lean_int_add(x_44, x_35);
lean_dec(x_35);
lean_dec(x_44);
x_46 = lean_int_mul(x_41, x_38);
lean_dec(x_41);
x_47 = lean_int_add(x_46, x_42);
lean_dec(x_42);
lean_dec(x_46);
x_48 = lean_int_add(x_45, x_47);
lean_dec(x_47);
lean_dec(x_45);
x_49 = l_Std_Time_Duration_ofNanoseconds(x_48);
lean_dec(x_48);
x_50 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_49);
x_51 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_50);
x_52 = lean_mk_thunk(x_43);
if (lean_is_scalar(x_5)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_5;
}
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
block_64:
{
lean_object* x_60; uint8_t x_61; 
x_60 = l_Std_Time_Month_Ordinal_days(x_59, x_56);
x_61 = lean_int_dec_lt(x_60, x_57);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 3, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_3);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_62, 2, x_57);
x_7 = x_62;
goto block_54;
}
else
{
lean_object* x_63; 
lean_dec(x_57);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 3, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_56);
lean_ctor_set(x_63, 2, x_60);
x_7 = x_63;
goto block_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withYearClip(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Time_PlainDate_rollOver(x_3, x_10, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 0, x_12);
lean_inc_ref(x_7);
x_13 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_TimeZone_toSeconds(x_1);
x_17 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_16);
lean_dec(x_16);
x_18 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_19 = lean_int_mul(x_17, x_18);
lean_dec(x_17);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_23, 0, x_7);
x_24 = lean_int_mul(x_14, x_18);
lean_dec(x_14);
x_25 = lean_int_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_26 = lean_int_mul(x_21, x_18);
lean_dec(x_21);
x_27 = lean_int_add(x_26, x_22);
lean_dec(x_22);
lean_dec(x_26);
x_28 = lean_int_add(x_25, x_27);
lean_dec(x_27);
lean_dec(x_25);
x_29 = l_Std_Time_Duration_ofNanoseconds(x_28);
lean_dec(x_28);
x_30 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_29);
x_31 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_30);
x_32 = lean_mk_thunk(x_23);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 2);
lean_inc(x_36);
lean_dec_ref(x_33);
x_37 = l_Std_Time_PlainDate_rollOver(x_3, x_35, x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
lean_inc_ref(x_38);
x_39 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = l_Std_Time_TimeZone_toSeconds(x_1);
x_43 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_42);
lean_dec(x_42);
x_44 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_45 = lean_int_mul(x_43, x_44);
lean_dec(x_43);
x_46 = l_Std_Time_Duration_ofNanoseconds(x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_49, 0, x_38);
x_50 = lean_int_mul(x_40, x_44);
lean_dec(x_40);
x_51 = lean_int_add(x_50, x_41);
lean_dec(x_41);
lean_dec(x_50);
x_52 = lean_int_mul(x_47, x_44);
lean_dec(x_47);
x_53 = lean_int_add(x_52, x_48);
lean_dec(x_48);
lean_dec(x_52);
x_54 = lean_int_add(x_51, x_53);
lean_dec(x_53);
lean_dec(x_51);
x_55 = l_Std_Time_Duration_ofNanoseconds(x_54);
lean_dec(x_54);
x_56 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_55);
x_57 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_56);
x_58 = lean_mk_thunk(x_49);
lean_ctor_set(x_2, 1, x_58);
lean_ctor_set(x_2, 0, x_57);
return x_2;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_59 = lean_ctor_get(x_2, 1);
lean_inc(x_59);
lean_dec(x_2);
x_60 = lean_thunk_get_own(x_59);
lean_dec_ref(x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 2);
lean_inc(x_65);
lean_dec_ref(x_61);
x_66 = l_Std_Time_PlainDate_rollOver(x_3, x_64, x_65);
lean_dec(x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
lean_inc_ref(x_67);
x_68 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Std_Time_TimeZone_toSeconds(x_1);
x_72 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_71);
lean_dec(x_71);
x_73 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_74 = lean_int_mul(x_72, x_73);
lean_dec(x_72);
x_75 = l_Std_Time_Duration_ofNanoseconds(x_74);
lean_dec(x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_78, 0, x_67);
x_79 = lean_int_mul(x_69, x_73);
lean_dec(x_69);
x_80 = lean_int_add(x_79, x_70);
lean_dec(x_70);
lean_dec(x_79);
x_81 = lean_int_mul(x_76, x_73);
lean_dec(x_76);
x_82 = lean_int_add(x_81, x_77);
lean_dec(x_77);
lean_dec(x_81);
x_83 = lean_int_add(x_80, x_82);
lean_dec(x_82);
lean_dec(x_80);
x_84 = l_Std_Time_Duration_ofNanoseconds(x_83);
lean_dec(x_83);
x_85 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_84);
x_86 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_85);
x_87 = lean_mk_thunk(x_78);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withYearRollOver(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_3);
lean_inc_ref(x_7);
x_12 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Std_Time_TimeZone_toSeconds(x_1);
x_16 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_18 = lean_int_mul(x_16, x_17);
lean_dec(x_16);
x_19 = l_Std_Time_Duration_ofNanoseconds(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_7);
x_23 = lean_int_mul(x_13, x_17);
lean_dec(x_13);
x_24 = lean_int_add(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
x_25 = lean_int_mul(x_20, x_17);
lean_dec(x_20);
x_26 = lean_int_add(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
x_27 = lean_int_add(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Std_Time_Duration_ofNanoseconds(x_27);
lean_dec(x_27);
x_29 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_28);
x_30 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_29);
x_31 = lean_mk_thunk(x_22);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_32 = lean_ctor_get(x_9, 1);
x_33 = lean_ctor_get(x_9, 2);
x_34 = lean_ctor_get(x_9, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_7, 1, x_35);
lean_inc_ref(x_7);
x_36 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Std_Time_TimeZone_toSeconds(x_1);
x_40 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_39);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_42 = lean_int_mul(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_Duration_ofNanoseconds(x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_46, 0, x_7);
x_47 = lean_int_mul(x_37, x_41);
lean_dec(x_37);
x_48 = lean_int_add(x_47, x_38);
lean_dec(x_38);
lean_dec(x_47);
x_49 = lean_int_mul(x_44, x_41);
lean_dec(x_44);
x_50 = lean_int_add(x_49, x_45);
lean_dec(x_45);
lean_dec(x_49);
x_51 = lean_int_add(x_48, x_50);
lean_dec(x_50);
lean_dec(x_48);
x_52 = l_Std_Time_Duration_ofNanoseconds(x_51);
lean_dec(x_51);
x_53 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_52);
x_54 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_53);
x_55 = lean_mk_thunk(x_46);
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_54);
return x_2;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_56 = lean_ctor_get(x_7, 1);
x_57 = lean_ctor_get(x_7, 0);
lean_inc(x_56);
lean_inc(x_57);
lean_dec(x_7);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 3);
lean_inc(x_60);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 x_61 = x_56;
} else {
 lean_dec_ref(x_56);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 4, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_3);
lean_ctor_set(x_62, 1, x_58);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
lean_inc_ref(x_63);
x_64 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = l_Std_Time_TimeZone_toSeconds(x_1);
x_68 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_67);
lean_dec(x_67);
x_69 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_70 = lean_int_mul(x_68, x_69);
lean_dec(x_68);
x_71 = l_Std_Time_Duration_ofNanoseconds(x_70);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_74, 0, x_63);
x_75 = lean_int_mul(x_65, x_69);
lean_dec(x_65);
x_76 = lean_int_add(x_75, x_66);
lean_dec(x_66);
lean_dec(x_75);
x_77 = lean_int_mul(x_72, x_69);
lean_dec(x_72);
x_78 = lean_int_add(x_77, x_73);
lean_dec(x_73);
lean_dec(x_77);
x_79 = lean_int_add(x_76, x_78);
lean_dec(x_78);
lean_dec(x_76);
x_80 = l_Std_Time_Duration_ofNanoseconds(x_79);
lean_dec(x_79);
x_81 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_80);
x_82 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_81);
x_83 = lean_mk_thunk(x_74);
lean_ctor_set(x_2, 1, x_83);
lean_ctor_set(x_2, 0, x_82);
return x_2;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
lean_dec(x_2);
x_85 = lean_thunk_get_own(x_84);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_85, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 3);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 4, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_3);
lean_ctor_set(x_93, 1, x_89);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_91);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_88;
}
lean_ctor_set(x_94, 0, x_87);
lean_ctor_set(x_94, 1, x_93);
lean_inc_ref(x_94);
x_95 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = l_Std_Time_TimeZone_toSeconds(x_1);
x_99 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_98);
lean_dec(x_98);
x_100 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_101 = lean_int_mul(x_99, x_100);
lean_dec(x_99);
x_102 = l_Std_Time_Duration_ofNanoseconds(x_101);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_105, 0, x_94);
x_106 = lean_int_mul(x_96, x_100);
lean_dec(x_96);
x_107 = lean_int_add(x_106, x_97);
lean_dec(x_97);
lean_dec(x_106);
x_108 = lean_int_mul(x_103, x_100);
lean_dec(x_103);
x_109 = lean_int_add(x_108, x_104);
lean_dec(x_104);
lean_dec(x_108);
x_110 = lean_int_add(x_107, x_109);
lean_dec(x_109);
lean_dec(x_107);
x_111 = l_Std_Time_Duration_ofNanoseconds(x_110);
lean_dec(x_110);
x_112 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_111);
x_113 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_112);
x_114 = lean_mk_thunk(x_105);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withHours(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_9, 1);
lean_dec(x_11);
lean_ctor_set(x_9, 1, x_3);
lean_inc_ref(x_7);
x_12 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Std_Time_TimeZone_toSeconds(x_1);
x_16 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_18 = lean_int_mul(x_16, x_17);
lean_dec(x_16);
x_19 = l_Std_Time_Duration_ofNanoseconds(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_7);
x_23 = lean_int_mul(x_13, x_17);
lean_dec(x_13);
x_24 = lean_int_add(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
x_25 = lean_int_mul(x_20, x_17);
lean_dec(x_20);
x_26 = lean_int_add(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
x_27 = lean_int_add(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Std_Time_Duration_ofNanoseconds(x_27);
lean_dec(x_27);
x_29 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_28);
x_30 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_29);
x_31 = lean_mk_thunk(x_22);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 2);
x_34 = lean_ctor_get(x_9, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_35, 2, x_33);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_7, 1, x_35);
lean_inc_ref(x_7);
x_36 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Std_Time_TimeZone_toSeconds(x_1);
x_40 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_39);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_42 = lean_int_mul(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_Duration_ofNanoseconds(x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_46, 0, x_7);
x_47 = lean_int_mul(x_37, x_41);
lean_dec(x_37);
x_48 = lean_int_add(x_47, x_38);
lean_dec(x_38);
lean_dec(x_47);
x_49 = lean_int_mul(x_44, x_41);
lean_dec(x_44);
x_50 = lean_int_add(x_49, x_45);
lean_dec(x_45);
lean_dec(x_49);
x_51 = lean_int_add(x_48, x_50);
lean_dec(x_50);
lean_dec(x_48);
x_52 = l_Std_Time_Duration_ofNanoseconds(x_51);
lean_dec(x_51);
x_53 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_52);
x_54 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_53);
x_55 = lean_mk_thunk(x_46);
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_54);
return x_2;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_56 = lean_ctor_get(x_7, 1);
x_57 = lean_ctor_get(x_7, 0);
lean_inc(x_56);
lean_inc(x_57);
lean_dec(x_7);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 3);
lean_inc(x_60);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 x_61 = x_56;
} else {
 lean_dec_ref(x_56);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 4, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_3);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
lean_inc_ref(x_63);
x_64 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = l_Std_Time_TimeZone_toSeconds(x_1);
x_68 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_67);
lean_dec(x_67);
x_69 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_70 = lean_int_mul(x_68, x_69);
lean_dec(x_68);
x_71 = l_Std_Time_Duration_ofNanoseconds(x_70);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_74, 0, x_63);
x_75 = lean_int_mul(x_65, x_69);
lean_dec(x_65);
x_76 = lean_int_add(x_75, x_66);
lean_dec(x_66);
lean_dec(x_75);
x_77 = lean_int_mul(x_72, x_69);
lean_dec(x_72);
x_78 = lean_int_add(x_77, x_73);
lean_dec(x_73);
lean_dec(x_77);
x_79 = lean_int_add(x_76, x_78);
lean_dec(x_78);
lean_dec(x_76);
x_80 = l_Std_Time_Duration_ofNanoseconds(x_79);
lean_dec(x_79);
x_81 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_80);
x_82 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_81);
x_83 = lean_mk_thunk(x_74);
lean_ctor_set(x_2, 1, x_83);
lean_ctor_set(x_2, 0, x_82);
return x_2;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
lean_dec(x_2);
x_85 = lean_thunk_get_own(x_84);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_85, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 3);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 4, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_3);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_91);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_88;
}
lean_ctor_set(x_94, 0, x_87);
lean_ctor_set(x_94, 1, x_93);
lean_inc_ref(x_94);
x_95 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = l_Std_Time_TimeZone_toSeconds(x_1);
x_99 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_98);
lean_dec(x_98);
x_100 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_101 = lean_int_mul(x_99, x_100);
lean_dec(x_99);
x_102 = l_Std_Time_Duration_ofNanoseconds(x_101);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_105, 0, x_94);
x_106 = lean_int_mul(x_96, x_100);
lean_dec(x_96);
x_107 = lean_int_add(x_106, x_97);
lean_dec(x_97);
lean_dec(x_106);
x_108 = lean_int_mul(x_103, x_100);
lean_dec(x_103);
x_109 = lean_int_add(x_108, x_104);
lean_dec(x_104);
lean_dec(x_108);
x_110 = lean_int_add(x_107, x_109);
lean_dec(x_109);
lean_dec(x_107);
x_111 = l_Std_Time_Duration_ofNanoseconds(x_110);
lean_dec(x_110);
x_112 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_111);
x_113 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_112);
x_114 = lean_mk_thunk(x_105);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withMinutes(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_9, 2);
lean_dec(x_11);
lean_ctor_set(x_9, 2, x_3);
lean_inc_ref(x_7);
x_12 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Std_Time_TimeZone_toSeconds(x_1);
x_16 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_18 = lean_int_mul(x_16, x_17);
lean_dec(x_16);
x_19 = l_Std_Time_Duration_ofNanoseconds(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_7);
x_23 = lean_int_mul(x_13, x_17);
lean_dec(x_13);
x_24 = lean_int_add(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
x_25 = lean_int_mul(x_20, x_17);
lean_dec(x_20);
x_26 = lean_int_add(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
x_27 = lean_int_add(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Std_Time_Duration_ofNanoseconds(x_27);
lean_dec(x_27);
x_29 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_28);
x_30 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_29);
x_31 = lean_mk_thunk(x_22);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
x_34 = lean_ctor_get(x_9, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_3);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_7, 1, x_35);
lean_inc_ref(x_7);
x_36 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Std_Time_TimeZone_toSeconds(x_1);
x_40 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_39);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_42 = lean_int_mul(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_Duration_ofNanoseconds(x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_46, 0, x_7);
x_47 = lean_int_mul(x_37, x_41);
lean_dec(x_37);
x_48 = lean_int_add(x_47, x_38);
lean_dec(x_38);
lean_dec(x_47);
x_49 = lean_int_mul(x_44, x_41);
lean_dec(x_44);
x_50 = lean_int_add(x_49, x_45);
lean_dec(x_45);
lean_dec(x_49);
x_51 = lean_int_add(x_48, x_50);
lean_dec(x_50);
lean_dec(x_48);
x_52 = l_Std_Time_Duration_ofNanoseconds(x_51);
lean_dec(x_51);
x_53 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_52);
x_54 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_53);
x_55 = lean_mk_thunk(x_46);
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_54);
return x_2;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_56 = lean_ctor_get(x_7, 1);
x_57 = lean_ctor_get(x_7, 0);
lean_inc(x_56);
lean_inc(x_57);
lean_dec(x_7);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 3);
lean_inc(x_60);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 x_61 = x_56;
} else {
 lean_dec_ref(x_56);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 4, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_3);
lean_ctor_set(x_62, 3, x_60);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
lean_inc_ref(x_63);
x_64 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = l_Std_Time_TimeZone_toSeconds(x_1);
x_68 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_67);
lean_dec(x_67);
x_69 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_70 = lean_int_mul(x_68, x_69);
lean_dec(x_68);
x_71 = l_Std_Time_Duration_ofNanoseconds(x_70);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_74, 0, x_63);
x_75 = lean_int_mul(x_65, x_69);
lean_dec(x_65);
x_76 = lean_int_add(x_75, x_66);
lean_dec(x_66);
lean_dec(x_75);
x_77 = lean_int_mul(x_72, x_69);
lean_dec(x_72);
x_78 = lean_int_add(x_77, x_73);
lean_dec(x_73);
lean_dec(x_77);
x_79 = lean_int_add(x_76, x_78);
lean_dec(x_78);
lean_dec(x_76);
x_80 = l_Std_Time_Duration_ofNanoseconds(x_79);
lean_dec(x_79);
x_81 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_80);
x_82 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_81);
x_83 = lean_mk_thunk(x_74);
lean_ctor_set(x_2, 1, x_83);
lean_ctor_set(x_2, 0, x_82);
return x_2;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
lean_dec(x_2);
x_85 = lean_thunk_get_own(x_84);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_85, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 3);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 4, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_3);
lean_ctor_set(x_93, 3, x_91);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_88;
}
lean_ctor_set(x_94, 0, x_87);
lean_ctor_set(x_94, 1, x_93);
lean_inc_ref(x_94);
x_95 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = l_Std_Time_TimeZone_toSeconds(x_1);
x_99 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_98);
lean_dec(x_98);
x_100 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_101 = lean_int_mul(x_99, x_100);
lean_dec(x_99);
x_102 = l_Std_Time_Duration_ofNanoseconds(x_101);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_105, 0, x_94);
x_106 = lean_int_mul(x_96, x_100);
lean_dec(x_96);
x_107 = lean_int_add(x_106, x_97);
lean_dec(x_97);
lean_dec(x_106);
x_108 = lean_int_mul(x_103, x_100);
lean_dec(x_103);
x_109 = lean_int_add(x_108, x_104);
lean_dec(x_104);
lean_dec(x_108);
x_110 = lean_int_add(x_107, x_109);
lean_dec(x_109);
lean_dec(x_107);
x_111 = l_Std_Time_Duration_ofNanoseconds(x_110);
lean_dec(x_110);
x_112 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_111);
x_113 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_112);
x_114 = lean_mk_thunk(x_105);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withSeconds(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_9, 3);
lean_dec(x_11);
lean_ctor_set(x_9, 3, x_3);
lean_inc_ref(x_7);
x_12 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Std_Time_TimeZone_toSeconds(x_1);
x_16 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_18 = lean_int_mul(x_16, x_17);
lean_dec(x_16);
x_19 = l_Std_Time_Duration_ofNanoseconds(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_22, 0, x_7);
x_23 = lean_int_mul(x_13, x_17);
lean_dec(x_13);
x_24 = lean_int_add(x_23, x_14);
lean_dec(x_14);
lean_dec(x_23);
x_25 = lean_int_mul(x_20, x_17);
lean_dec(x_20);
x_26 = lean_int_add(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
x_27 = lean_int_add(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Std_Time_Duration_ofNanoseconds(x_27);
lean_dec(x_27);
x_29 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_28);
x_30 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_29);
x_31 = lean_mk_thunk(x_22);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
x_34 = lean_ctor_get(x_9, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_3);
lean_ctor_set(x_7, 1, x_35);
lean_inc_ref(x_7);
x_36 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Std_Time_TimeZone_toSeconds(x_1);
x_40 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_39);
lean_dec(x_39);
x_41 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_42 = lean_int_mul(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_Duration_ofNanoseconds(x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_46, 0, x_7);
x_47 = lean_int_mul(x_37, x_41);
lean_dec(x_37);
x_48 = lean_int_add(x_47, x_38);
lean_dec(x_38);
lean_dec(x_47);
x_49 = lean_int_mul(x_44, x_41);
lean_dec(x_44);
x_50 = lean_int_add(x_49, x_45);
lean_dec(x_45);
lean_dec(x_49);
x_51 = lean_int_add(x_48, x_50);
lean_dec(x_50);
lean_dec(x_48);
x_52 = l_Std_Time_Duration_ofNanoseconds(x_51);
lean_dec(x_51);
x_53 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_52);
x_54 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_53);
x_55 = lean_mk_thunk(x_46);
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_54);
return x_2;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_56 = lean_ctor_get(x_7, 1);
x_57 = lean_ctor_get(x_7, 0);
lean_inc(x_56);
lean_inc(x_57);
lean_dec(x_7);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc(x_60);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 x_61 = x_56;
} else {
 lean_dec_ref(x_56);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 4, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set(x_62, 3, x_3);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
lean_inc_ref(x_63);
x_64 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_63);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = l_Std_Time_TimeZone_toSeconds(x_1);
x_68 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_67);
lean_dec(x_67);
x_69 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_70 = lean_int_mul(x_68, x_69);
lean_dec(x_68);
x_71 = l_Std_Time_Duration_ofNanoseconds(x_70);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_74, 0, x_63);
x_75 = lean_int_mul(x_65, x_69);
lean_dec(x_65);
x_76 = lean_int_add(x_75, x_66);
lean_dec(x_66);
lean_dec(x_75);
x_77 = lean_int_mul(x_72, x_69);
lean_dec(x_72);
x_78 = lean_int_add(x_77, x_73);
lean_dec(x_73);
lean_dec(x_77);
x_79 = lean_int_add(x_76, x_78);
lean_dec(x_78);
lean_dec(x_76);
x_80 = l_Std_Time_Duration_ofNanoseconds(x_79);
lean_dec(x_79);
x_81 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_80);
x_82 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_81);
x_83 = lean_mk_thunk(x_74);
lean_ctor_set(x_2, 1, x_83);
lean_ctor_set(x_2, 0, x_82);
return x_2;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_84 = lean_ctor_get(x_2, 1);
lean_inc(x_84);
lean_dec(x_2);
x_85 = lean_thunk_get_own(x_84);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_85, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 2);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 lean_ctor_release(x_86, 2);
 lean_ctor_release(x_86, 3);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 4, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_89);
lean_ctor_set(x_93, 1, x_90);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_3);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_88;
}
lean_ctor_set(x_94, 0, x_87);
lean_ctor_set(x_94, 1, x_93);
lean_inc_ref(x_94);
x_95 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = l_Std_Time_TimeZone_toSeconds(x_1);
x_99 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_98);
lean_dec(x_98);
x_100 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_101 = lean_int_mul(x_99, x_100);
lean_dec(x_99);
x_102 = l_Std_Time_Duration_ofNanoseconds(x_101);
lean_dec(x_101);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_105, 0, x_94);
x_106 = lean_int_mul(x_96, x_100);
lean_dec(x_96);
x_107 = lean_int_add(x_106, x_97);
lean_dec(x_97);
lean_dec(x_106);
x_108 = lean_int_mul(x_103, x_100);
lean_dec(x_103);
x_109 = lean_int_add(x_108, x_104);
lean_dec(x_104);
lean_dec(x_108);
x_110 = lean_int_add(x_107, x_109);
lean_dec(x_109);
lean_dec(x_107);
x_111 = l_Std_Time_Duration_ofNanoseconds(x_110);
lean_dec(x_110);
x_112 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_111);
x_113 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_112);
x_114 = lean_mk_thunk(x_105);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withNanoseconds(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Time_DateTime_withMilliseconds___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_11 = lean_ctor_get(x_9, 3);
x_12 = l_Std_Time_DateTime_withMilliseconds___closed__0;
x_13 = lean_int_emod(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_DateTime_addMilliseconds___closed__0;
x_15 = lean_int_mul(x_3, x_14);
x_16 = lean_int_add(x_15, x_13);
lean_dec(x_13);
lean_dec(x_15);
lean_ctor_set(x_9, 3, x_16);
lean_inc_ref(x_7);
x_17 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Std_Time_TimeZone_toSeconds(x_1);
x_21 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_23 = lean_int_mul(x_21, x_22);
lean_dec(x_21);
x_24 = l_Std_Time_Duration_ofNanoseconds(x_23);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_27, 0, x_7);
x_28 = lean_int_mul(x_18, x_22);
lean_dec(x_18);
x_29 = lean_int_add(x_28, x_19);
lean_dec(x_19);
lean_dec(x_28);
x_30 = lean_int_mul(x_25, x_22);
lean_dec(x_25);
x_31 = lean_int_add(x_30, x_26);
lean_dec(x_26);
lean_dec(x_30);
x_32 = lean_int_add(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_33 = l_Std_Time_Duration_ofNanoseconds(x_32);
lean_dec(x_32);
x_34 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_33);
x_35 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_34);
x_36 = lean_mk_thunk(x_27);
lean_ctor_set(x_2, 1, x_36);
lean_ctor_set(x_2, 0, x_35);
return x_2;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
x_39 = lean_ctor_get(x_9, 2);
x_40 = lean_ctor_get(x_9, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_41 = l_Std_Time_DateTime_withMilliseconds___closed__0;
x_42 = lean_int_emod(x_40, x_41);
lean_dec(x_40);
x_43 = l_Std_Time_DateTime_addMilliseconds___closed__0;
x_44 = lean_int_mul(x_3, x_43);
x_45 = lean_int_add(x_44, x_42);
lean_dec(x_42);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_39);
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_7, 1, x_46);
lean_inc_ref(x_7);
x_47 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = l_Std_Time_TimeZone_toSeconds(x_1);
x_51 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_50);
lean_dec(x_50);
x_52 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_53 = lean_int_mul(x_51, x_52);
lean_dec(x_51);
x_54 = l_Std_Time_Duration_ofNanoseconds(x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_57, 0, x_7);
x_58 = lean_int_mul(x_48, x_52);
lean_dec(x_48);
x_59 = lean_int_add(x_58, x_49);
lean_dec(x_49);
lean_dec(x_58);
x_60 = lean_int_mul(x_55, x_52);
lean_dec(x_55);
x_61 = lean_int_add(x_60, x_56);
lean_dec(x_56);
lean_dec(x_60);
x_62 = lean_int_add(x_59, x_61);
lean_dec(x_61);
lean_dec(x_59);
x_63 = l_Std_Time_Duration_ofNanoseconds(x_62);
lean_dec(x_62);
x_64 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_63);
x_65 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_64);
x_66 = lean_mk_thunk(x_57);
lean_ctor_set(x_2, 1, x_66);
lean_ctor_set(x_2, 0, x_65);
return x_2;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_67 = lean_ctor_get(x_7, 1);
x_68 = lean_ctor_get(x_7, 0);
lean_inc(x_67);
lean_inc(x_68);
lean_dec(x_7);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 3);
lean_inc(x_72);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 lean_ctor_release(x_67, 3);
 x_73 = x_67;
} else {
 lean_dec_ref(x_67);
 x_73 = lean_box(0);
}
x_74 = l_Std_Time_DateTime_withMilliseconds___closed__0;
x_75 = lean_int_emod(x_72, x_74);
lean_dec(x_72);
x_76 = l_Std_Time_DateTime_addMilliseconds___closed__0;
x_77 = lean_int_mul(x_3, x_76);
x_78 = lean_int_add(x_77, x_75);
lean_dec(x_75);
lean_dec(x_77);
if (lean_is_scalar(x_73)) {
 x_79 = lean_alloc_ctor(0, 4, 0);
} else {
 x_79 = x_73;
}
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_70);
lean_ctor_set(x_79, 2, x_71);
lean_ctor_set(x_79, 3, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_68);
lean_ctor_set(x_80, 1, x_79);
lean_inc_ref(x_80);
x_81 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = l_Std_Time_TimeZone_toSeconds(x_1);
x_85 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_84);
lean_dec(x_84);
x_86 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_87 = lean_int_mul(x_85, x_86);
lean_dec(x_85);
x_88 = l_Std_Time_Duration_ofNanoseconds(x_87);
lean_dec(x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_91, 0, x_80);
x_92 = lean_int_mul(x_82, x_86);
lean_dec(x_82);
x_93 = lean_int_add(x_92, x_83);
lean_dec(x_83);
lean_dec(x_92);
x_94 = lean_int_mul(x_89, x_86);
lean_dec(x_89);
x_95 = lean_int_add(x_94, x_90);
lean_dec(x_90);
lean_dec(x_94);
x_96 = lean_int_add(x_93, x_95);
lean_dec(x_95);
lean_dec(x_93);
x_97 = l_Std_Time_Duration_ofNanoseconds(x_96);
lean_dec(x_96);
x_98 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_97);
x_99 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_98);
x_100 = lean_mk_thunk(x_91);
lean_ctor_set(x_2, 1, x_100);
lean_ctor_set(x_2, 0, x_99);
return x_2;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
lean_dec(x_2);
x_102 = lean_thunk_get_own(x_101);
lean_dec_ref(x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc_ref(x_103);
x_104 = lean_ctor_get(x_102, 0);
lean_inc_ref(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 3);
lean_inc(x_109);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 lean_ctor_release(x_103, 2);
 lean_ctor_release(x_103, 3);
 x_110 = x_103;
} else {
 lean_dec_ref(x_103);
 x_110 = lean_box(0);
}
x_111 = l_Std_Time_DateTime_withMilliseconds___closed__0;
x_112 = lean_int_emod(x_109, x_111);
lean_dec(x_109);
x_113 = l_Std_Time_DateTime_addMilliseconds___closed__0;
x_114 = lean_int_mul(x_3, x_113);
x_115 = lean_int_add(x_114, x_112);
lean_dec(x_112);
lean_dec(x_114);
if (lean_is_scalar(x_110)) {
 x_116 = lean_alloc_ctor(0, 4, 0);
} else {
 x_116 = x_110;
}
lean_ctor_set(x_116, 0, x_106);
lean_ctor_set(x_116, 1, x_107);
lean_ctor_set(x_116, 2, x_108);
lean_ctor_set(x_116, 3, x_115);
if (lean_is_scalar(x_105)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_105;
}
lean_ctor_set(x_117, 0, x_104);
lean_ctor_set(x_117, 1, x_116);
lean_inc_ref(x_117);
x_118 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec_ref(x_118);
x_121 = l_Std_Time_TimeZone_toSeconds(x_1);
x_122 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_121);
lean_dec(x_121);
x_123 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_124 = lean_int_mul(x_122, x_123);
lean_dec(x_122);
x_125 = l_Std_Time_Duration_ofNanoseconds(x_124);
lean_dec(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_128, 0, x_117);
x_129 = lean_int_mul(x_119, x_123);
lean_dec(x_119);
x_130 = lean_int_add(x_129, x_120);
lean_dec(x_120);
lean_dec(x_129);
x_131 = lean_int_mul(x_126, x_123);
lean_dec(x_126);
x_132 = lean_int_add(x_131, x_127);
lean_dec(x_127);
lean_dec(x_131);
x_133 = lean_int_add(x_130, x_132);
lean_dec(x_132);
lean_dec(x_130);
x_134 = l_Std_Time_Duration_ofNanoseconds(x_133);
lean_dec(x_133);
x_135 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_134);
x_136 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_135);
x_137 = lean_mk_thunk(x_128);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_withMilliseconds(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toPlainDateTime___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_toPlainDateTime(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_year___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_year(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_month___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_month(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_day___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_day(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_hour___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_hour(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_minute___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_minute(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_second___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_second(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_DateTime_withMilliseconds___closed__0;
x_7 = lean_int_emod(x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Std_Time_DateTime_withMilliseconds___closed__0;
x_8 = lean_int_emod(x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_millisecond___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_millisecond(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_nanosecond___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_nanosecond(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Std_Time_PlainDate_weekday(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_PlainDate_weekday(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_DateTime_weekday___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_DateTime_weekday(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_Year_Offset_era(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Time_DateTime_era___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_DateTime_era___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_DateTime_era(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_dec(x_6);
x_7 = lean_thunk_get_own(x_5);
lean_dec_ref(x_5);
x_8 = l_Std_Time_PlainDateTime_withWeekday(x_7, x_3);
lean_inc_ref(x_8);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Time_TimeZone_toSeconds(x_1);
x_13 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_12);
lean_dec(x_12);
x_14 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_15 = lean_int_mul(x_13, x_14);
lean_dec(x_13);
x_16 = l_Std_Time_Duration_ofNanoseconds(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_19, 0, x_8);
x_20 = lean_int_mul(x_10, x_14);
lean_dec(x_10);
x_21 = lean_int_add(x_20, x_11);
lean_dec(x_11);
lean_dec(x_20);
x_22 = lean_int_mul(x_17, x_14);
lean_dec(x_17);
x_23 = lean_int_add(x_22, x_18);
lean_dec(x_18);
lean_dec(x_22);
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_Time_Duration_ofNanoseconds(x_24);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_25);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_mk_thunk(x_19);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_thunk_get_own(x_29);
lean_dec_ref(x_29);
x_31 = l_Std_Time_PlainDateTime_withWeekday(x_30, x_3);
lean_inc_ref(x_31);
x_32 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = l_Std_Time_TimeZone_toSeconds(x_1);
x_36 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_35);
lean_dec(x_35);
x_37 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_38 = lean_int_mul(x_36, x_37);
lean_dec(x_36);
x_39 = l_Std_Time_Duration_ofNanoseconds(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_42, 0, x_31);
x_43 = lean_int_mul(x_33, x_37);
lean_dec(x_33);
x_44 = lean_int_add(x_43, x_34);
lean_dec(x_34);
lean_dec(x_43);
x_45 = lean_int_mul(x_40, x_37);
lean_dec(x_40);
x_46 = lean_int_add(x_45, x_41);
lean_dec(x_41);
lean_dec(x_45);
x_47 = lean_int_add(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
x_48 = l_Std_Time_Duration_ofNanoseconds(x_47);
lean_dec(x_47);
x_49 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_48);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_mk_thunk(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Std_Time_DateTime_withWeekday(x_1, x_2, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_DateTime_withDaysClip___closed__0;
x_7 = lean_int_mod(x_5, x_6);
x_8 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_9 = lean_int_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_11 = lean_int_mod(x_5, x_10);
x_12 = lean_int_dec_eq(x_11, x_8);
lean_dec(x_11);
x_13 = l_instDecidableNot___redArg(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_15 = lean_int_mod(x_5, x_14);
lean_dec(x_5);
x_16 = lean_int_dec_eq(x_15, x_8);
lean_dec(x_15);
return x_16;
}
else
{
lean_dec(x_5);
return x_13;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Time_DateTime_inLeapYear___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_DateTime_inLeapYear___redArg(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_DateTime_inLeapYear(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_2 = lean_ctor_get(x_1, 1);
x_17 = lean_thunk_get_own(x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Std_Time_DateTime_withDaysClip___closed__0;
x_21 = lean_int_mod(x_19, x_20);
x_22 = l_Std_Time_DateTime_withDaysClip___closed__1;
x_23 = lean_int_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_dec(x_19);
x_3 = x_23;
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_24 = l_Std_Time_DateTime_withDaysClip___closed__2;
x_25 = lean_int_mod(x_19, x_24);
x_26 = lean_int_dec_eq(x_25, x_22);
lean_dec(x_25);
x_27 = l_instDecidableNot___redArg(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Std_Time_DateTime_withDaysClip___closed__3;
x_29 = lean_int_mod(x_19, x_28);
lean_dec(x_19);
x_30 = lean_int_dec_eq(x_29, x_22);
lean_dec(x_29);
x_3 = x_30;
goto block_16;
}
else
{
lean_dec(x_19);
x_3 = x_27;
goto block_16;
}
}
block_16:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_thunk_get_own(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
lean_dec_ref(x_6);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_8);
x_10 = l_Std_Time_ValidDate_dayOfYear(x_3, x_4);
lean_dec_ref(x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Std_Time_ValidDate_dayOfYear(x_3, x_14);
lean_dec_ref(x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_dayOfYear___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_dayOfYear___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_dayOfYear(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Std_Time_PlainDate_weekOfYear(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_PlainDate_weekOfYear(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_weekOfYear___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_weekOfYear(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = l_Std_Time_PlainDateTime_weekOfMonth(x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_weekOfMonth___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_weekOfMonth___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_weekOfMonth(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Std_Time_PlainDate_alignedWeekOfMonth(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_PlainDate_alignedWeekOfMonth(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_alignedWeekOfMonth___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_alignedWeekOfMonth(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = l_Std_Time_PlainDate_quarter(x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_PlainDate_quarter(x_5);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_quarter___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_quarter(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_time___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_time(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_4 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_inc_ref(x_5);
x_6 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Std_Time_TimeZone_toSeconds(x_3);
x_10 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_9);
lean_dec(x_9);
x_11 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_12 = lean_int_mul(x_10, x_11);
lean_dec(x_10);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_17, 0, x_5);
x_18 = lean_int_mul(x_7, x_11);
lean_dec(x_7);
x_19 = lean_int_add(x_18, x_8);
lean_dec(x_8);
lean_dec(x_18);
x_20 = lean_int_mul(x_15, x_11);
lean_dec(x_15);
x_21 = lean_int_add(x_20, x_16);
lean_dec(x_16);
lean_dec(x_20);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_Duration_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_23);
x_25 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_24);
x_26 = lean_mk_thunk(x_17);
lean_ctor_set(x_13, 1, x_26);
lean_ctor_set(x_13, 0, x_25);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_5);
x_30 = lean_int_mul(x_7, x_11);
lean_dec(x_7);
x_31 = lean_int_add(x_30, x_8);
lean_dec(x_8);
lean_dec(x_30);
x_32 = lean_int_mul(x_27, x_11);
lean_dec(x_27);
x_33 = lean_int_add(x_32, x_28);
lean_dec(x_28);
lean_dec(x_32);
x_34 = lean_int_add(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
x_35 = l_Std_Time_Duration_ofNanoseconds(x_34);
lean_dec(x_34);
x_36 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_35);
x_37 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_36);
x_38 = lean_mk_thunk(x_29);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_ofDaysSinceUNIXEpoch(x_1, x_2, x_3);
lean_dec_ref(x_3);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_5);
x_10 = lean_int_neg(x_6);
x_11 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_12 = lean_int_mul(x_7, x_11);
x_13 = lean_int_add(x_12, x_8);
lean_dec(x_12);
x_14 = lean_int_mul(x_9, x_11);
lean_dec(x_9);
x_15 = lean_int_add(x_14, x_10);
lean_dec(x_10);
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
x_3 = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHSubDuration___lam__0___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_instHSubDuration___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_instHSubDuration(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
x_9 = lean_thunk_get_own(x_7);
lean_dec_ref(x_7);
x_10 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_14 = lean_int_mul(x_5, x_13);
x_15 = lean_int_add(x_14, x_6);
lean_dec(x_14);
x_16 = l_Std_Time_Duration_ofNanoseconds(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_int_mul(x_11, x_13);
lean_dec(x_11);
x_20 = lean_int_add(x_19, x_12);
lean_dec(x_12);
lean_dec(x_19);
x_21 = lean_int_mul(x_17, x_13);
lean_dec(x_17);
x_22 = lean_int_add(x_21, x_18);
lean_dec(x_18);
lean_dec(x_21);
x_23 = lean_int_add(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
x_24 = l_Std_Time_Duration_ofNanoseconds(x_23);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_24);
lean_inc_ref(x_25);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Std_Time_TimeZone_toSeconds(x_1);
x_30 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_29);
lean_dec(x_29);
x_31 = lean_int_mul(x_30, x_13);
lean_dec(x_30);
x_32 = l_Std_Time_Duration_ofNanoseconds(x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_35, 0, x_25);
x_36 = lean_int_mul(x_27, x_13);
lean_dec(x_27);
x_37 = lean_int_add(x_36, x_28);
lean_dec(x_28);
lean_dec(x_36);
x_38 = lean_int_mul(x_33, x_13);
lean_dec(x_33);
x_39 = lean_int_add(x_38, x_34);
lean_dec(x_34);
lean_dec(x_38);
x_40 = lean_int_add(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
x_41 = l_Std_Time_Duration_ofNanoseconds(x_40);
lean_dec(x_40);
x_42 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_41);
x_43 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_42);
x_44 = lean_mk_thunk(x_35);
lean_ctor_set(x_2, 1, x_44);
lean_ctor_set(x_2, 0, x_43);
return x_2;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
lean_dec(x_2);
x_48 = lean_thunk_get_own(x_47);
lean_dec_ref(x_47);
x_49 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_53 = lean_int_mul(x_45, x_52);
x_54 = lean_int_add(x_53, x_46);
lean_dec(x_53);
x_55 = l_Std_Time_Duration_ofNanoseconds(x_54);
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = lean_int_mul(x_50, x_52);
lean_dec(x_50);
x_59 = lean_int_add(x_58, x_51);
lean_dec(x_51);
lean_dec(x_58);
x_60 = lean_int_mul(x_56, x_52);
lean_dec(x_56);
x_61 = lean_int_add(x_60, x_57);
lean_dec(x_57);
lean_dec(x_60);
x_62 = lean_int_add(x_59, x_61);
lean_dec(x_61);
lean_dec(x_59);
x_63 = l_Std_Time_Duration_ofNanoseconds(x_62);
lean_dec(x_62);
x_64 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_63);
lean_inc_ref(x_64);
x_65 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_64);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = l_Std_Time_TimeZone_toSeconds(x_1);
x_69 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_68);
lean_dec(x_68);
x_70 = lean_int_mul(x_69, x_52);
lean_dec(x_69);
x_71 = l_Std_Time_Duration_ofNanoseconds(x_70);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_74, 0, x_64);
x_75 = lean_int_mul(x_66, x_52);
lean_dec(x_66);
x_76 = lean_int_add(x_75, x_67);
lean_dec(x_67);
lean_dec(x_75);
x_77 = lean_int_mul(x_72, x_52);
lean_dec(x_72);
x_78 = lean_int_add(x_77, x_73);
lean_dec(x_73);
lean_dec(x_77);
x_79 = lean_int_add(x_76, x_78);
lean_dec(x_78);
lean_dec(x_76);
x_80 = l_Std_Time_Duration_ofNanoseconds(x_79);
lean_dec(x_79);
x_81 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_80);
x_82 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_81);
x_83 = lean_mk_thunk(x_74);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHAddDuration___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_instHAddDuration___lam__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
x_9 = lean_thunk_get_own(x_7);
lean_dec_ref(x_7);
x_10 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_14 = lean_int_mul(x_5, x_13);
x_15 = lean_int_add(x_14, x_6);
lean_dec(x_14);
x_16 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_int_mul(x_11, x_13);
lean_dec(x_11);
x_21 = lean_int_add(x_20, x_12);
lean_dec(x_12);
lean_dec(x_20);
x_22 = lean_int_mul(x_18, x_13);
lean_dec(x_18);
x_23 = lean_int_add(x_22, x_19);
lean_dec(x_19);
lean_dec(x_22);
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_Time_Duration_ofNanoseconds(x_24);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_25);
lean_inc_ref(x_26);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Std_Time_TimeZone_toSeconds(x_1);
x_31 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_30);
lean_dec(x_30);
x_32 = lean_int_mul(x_31, x_13);
lean_dec(x_31);
x_33 = l_Std_Time_Duration_ofNanoseconds(x_32);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_36, 0, x_26);
x_37 = lean_int_mul(x_28, x_13);
lean_dec(x_28);
x_38 = lean_int_add(x_37, x_29);
lean_dec(x_29);
lean_dec(x_37);
x_39 = lean_int_mul(x_34, x_13);
lean_dec(x_34);
x_40 = lean_int_add(x_39, x_35);
lean_dec(x_35);
lean_dec(x_39);
x_41 = lean_int_add(x_38, x_40);
lean_dec(x_40);
lean_dec(x_38);
x_42 = l_Std_Time_Duration_ofNanoseconds(x_41);
lean_dec(x_41);
x_43 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_42);
x_44 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_43);
x_45 = lean_mk_thunk(x_36);
lean_ctor_set(x_2, 1, x_45);
lean_ctor_set(x_2, 0, x_44);
return x_2;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_thunk_get_own(x_48);
lean_dec_ref(x_48);
x_50 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
x_54 = lean_int_mul(x_46, x_53);
x_55 = lean_int_add(x_54, x_47);
lean_dec(x_54);
x_56 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_55);
lean_dec(x_55);
x_57 = l_Std_Time_Duration_ofNanoseconds(x_56);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = lean_int_mul(x_51, x_53);
lean_dec(x_51);
x_61 = lean_int_add(x_60, x_52);
lean_dec(x_52);
lean_dec(x_60);
x_62 = lean_int_mul(x_58, x_53);
lean_dec(x_58);
x_63 = lean_int_add(x_62, x_59);
lean_dec(x_59);
lean_dec(x_62);
x_64 = lean_int_add(x_61, x_63);
lean_dec(x_63);
lean_dec(x_61);
x_65 = l_Std_Time_Duration_ofNanoseconds(x_64);
lean_dec(x_64);
x_66 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_65);
lean_inc_ref(x_66);
x_67 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_70 = l_Std_Time_TimeZone_toSeconds(x_1);
x_71 = l_Std_Time_Internal_UnitVal_instNeg___lam__0(x_70);
lean_dec(x_70);
x_72 = lean_int_mul(x_71, x_53);
lean_dec(x_71);
x_73 = l_Std_Time_Duration_ofNanoseconds(x_72);
lean_dec(x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec_ref(x_73);
x_76 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_76, 0, x_66);
x_77 = lean_int_mul(x_68, x_53);
lean_dec(x_68);
x_78 = lean_int_add(x_77, x_69);
lean_dec(x_69);
lean_dec(x_77);
x_79 = lean_int_mul(x_74, x_53);
lean_dec(x_74);
x_80 = lean_int_add(x_79, x_75);
lean_dec(x_75);
lean_dec(x_79);
x_81 = lean_int_add(x_78, x_80);
lean_dec(x_80);
lean_dec(x_78);
x_82 = l_Std_Time_Duration_ofNanoseconds(x_81);
lean_dec(x_81);
x_83 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_82);
x_84 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_83);
x_85 = lean_mk_thunk(x_76);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_instHSubDuration__1___lam__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
lean_object* initialize_Std_Time_DateTime(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Date_Unit_Year(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin, lean_object*);
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
res = initialize_Std_Time_Date_Unit_Month(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Year(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0 = _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0();
lean_mark_persistent(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
l_Std_Time_DateTime_instInhabited___closed__0 = _init_l_Std_Time_DateTime_instInhabited___closed__0();
lean_mark_persistent(l_Std_Time_DateTime_instInhabited___closed__0);
l_Std_Time_DateTime_addHours___closed__0 = _init_l_Std_Time_DateTime_addHours___closed__0();
lean_mark_persistent(l_Std_Time_DateTime_addHours___closed__0);
l_Std_Time_DateTime_addMinutes___closed__0 = _init_l_Std_Time_DateTime_addMinutes___closed__0();
lean_mark_persistent(l_Std_Time_DateTime_addMinutes___closed__0);
l_Std_Time_DateTime_addMilliseconds___closed__0 = _init_l_Std_Time_DateTime_addMilliseconds___closed__0();
lean_mark_persistent(l_Std_Time_DateTime_addMilliseconds___closed__0);
l_Std_Time_DateTime_addWeeks___closed__0 = _init_l_Std_Time_DateTime_addWeeks___closed__0();
lean_mark_persistent(l_Std_Time_DateTime_addWeeks___closed__0);
l_Std_Time_DateTime_addYearsRollOver___closed__0 = _init_l_Std_Time_DateTime_addYearsRollOver___closed__0();
lean_mark_persistent(l_Std_Time_DateTime_addYearsRollOver___closed__0);
l_Std_Time_DateTime_withDaysClip___closed__0 = _init_l_Std_Time_DateTime_withDaysClip___closed__0();
lean_mark_persistent(l_Std_Time_DateTime_withDaysClip___closed__0);
l_Std_Time_DateTime_withDaysClip___closed__1 = _init_l_Std_Time_DateTime_withDaysClip___closed__1();
lean_mark_persistent(l_Std_Time_DateTime_withDaysClip___closed__1);
l_Std_Time_DateTime_withDaysClip___closed__2 = _init_l_Std_Time_DateTime_withDaysClip___closed__2();
lean_mark_persistent(l_Std_Time_DateTime_withDaysClip___closed__2);
l_Std_Time_DateTime_withDaysClip___closed__3 = _init_l_Std_Time_DateTime_withDaysClip___closed__3();
lean_mark_persistent(l_Std_Time_DateTime_withDaysClip___closed__3);
l_Std_Time_DateTime_withMilliseconds___closed__0 = _init_l_Std_Time_DateTime_withMilliseconds___closed__0();
lean_mark_persistent(l_Std_Time_DateTime_withMilliseconds___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

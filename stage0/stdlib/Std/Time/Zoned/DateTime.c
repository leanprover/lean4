// Lean compiler output
// Module: Std.Time.Zoned.DateTime
// Imports: public import Std.Time.DateTime public import Std.Time.Zoned.TimeZone import all Std.Time.Date.Unit.Month import all Std.Time.Date.Unit.Year import all Std.Time.DateTime.PlainDateTime
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
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
extern lean_object* l_Std_Time_instOrdTimestamp;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_instDecidableEqDuration_decEq(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object*, lean_object*);
extern lean_object* l_Std_Time_instInhabitedTimestamp_default;
LEAN_EXPORT uint8_t l_Std_Time_instBEqDateTime___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instBEqDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instBEqDateTime___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instBEqDateTime___closed__0 = (const lean_object*)&l_Std_Time_instBEqDateTime___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instOrdDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdDateTime___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdDateTime___closed__0 = (const lean_object*)&l_Std_Time_instOrdDateTime___closed__0_value;
static lean_once_cell_t l_Std_Time_instOrdDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdDateTime___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addYearsRollOver___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addYearsRollOver___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_withDaysClip___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__0;
static lean_once_cell_t l_Std_Time_DateTime_withDaysClip___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__1;
static lean_once_cell_t l_Std_Time_DateTime_withDaysClip___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__2;
static lean_once_cell_t l_Std_Time_DateTime_withDaysClip___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_withDaysClip___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_withMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_withMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__4(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__6(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_DateTime_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_instHSubDuration___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instBEqDateTime___lam__0(lean_object* v_x_1_, lean_object* v_y_2_){
_start:
{
lean_object* v_timestamp_3_; lean_object* v_timestamp_4_; uint8_t v___x_5_; 
v_timestamp_3_ = lean_ctor_get(v_x_1_, 0);
v_timestamp_4_ = lean_ctor_get(v_y_2_, 0);
v___x_5_ = l_Std_Time_instDecidableEqDuration_decEq(v_timestamp_3_, v_timestamp_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___lam__0___boxed(lean_object* v_x_6_, lean_object* v_y_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Std_Time_instBEqDateTime___lam__0(v_x_6_, v_y_7_);
lean_dec_ref(v_y_7_);
lean_dec_ref(v_x_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime(lean_object* v_tz_11_){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = ((lean_object*)(l_Std_Time_instBEqDateTime___closed__0));
return v___f_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime___boxed(lean_object* v_tz_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_Time_instBEqDateTime(v_tz_13_);
lean_dec_ref(v_tz_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___lam__0(lean_object* v_x_15_){
_start:
{
lean_object* v_timestamp_16_; 
v_timestamp_16_ = lean_ctor_get(v_x_15_, 0);
lean_inc_ref(v_timestamp_16_);
return v_timestamp_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___lam__0___boxed(lean_object* v_x_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Std_Time_instOrdDateTime___lam__0(v_x_17_);
lean_dec_ref(v_x_17_);
return v_res_18_;
}
}
static lean_object* _init_l_Std_Time_instOrdDateTime___closed__1(void){
_start:
{
lean_object* v___f_20_; lean_object* v___x_21_; lean_object* v___x_22_; 
v___f_20_ = ((lean_object*)(l_Std_Time_instOrdDateTime___closed__0));
v___x_21_ = l_Std_Time_instOrdTimestamp;
v___x_22_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_22_, 0, lean_box(0));
lean_closure_set(v___x_22_, 1, lean_box(0));
lean_closure_set(v___x_22_, 2, v___x_21_);
lean_closure_set(v___x_22_, 3, v___f_20_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime(lean_object* v_tz_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Std_Time_instOrdDateTime___closed__1, &l_Std_Time_instOrdDateTime___closed__1_once, _init_l_Std_Time_instOrdDateTime___closed__1);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___boxed(lean_object* v_tz_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Time_instOrdDateTime(v_tz_25_);
lean_dec_ref(v_tz_25_);
return v_res_26_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(1000000000u);
v___x_28_ = lean_nat_to_int(v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object* v_tm_29_, lean_object* v_tz_30_, lean_object* v_x_31_){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v_second_34_; lean_object* v_nano_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v_second_40_; lean_object* v_nano_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_32_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_tm_29_);
v___x_33_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_32_);
v_second_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_second_34_);
v_nano_35_ = lean_ctor_get(v___x_33_, 1);
lean_inc(v_nano_35_);
lean_dec_ref(v___x_33_);
v___x_36_ = l_Std_Time_TimeZone_toSeconds(v_tz_30_);
v___x_37_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_38_ = lean_int_mul(v___x_36_, v___x_37_);
lean_dec(v___x_36_);
v___x_39_ = l_Std_Time_Duration_ofNanoseconds(v___x_38_);
lean_dec(v___x_38_);
v_second_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_second_40_);
v_nano_41_ = lean_ctor_get(v___x_39_, 1);
lean_inc(v_nano_41_);
lean_dec_ref(v___x_39_);
v___x_42_ = lean_int_mul(v_second_34_, v___x_37_);
lean_dec(v_second_34_);
v___x_43_ = lean_int_add(v___x_42_, v_nano_35_);
lean_dec(v_nano_35_);
lean_dec(v___x_42_);
v___x_44_ = lean_int_mul(v_second_40_, v___x_37_);
lean_dec(v_second_40_);
v___x_45_ = lean_int_add(v___x_44_, v_nano_41_);
lean_dec(v_nano_41_);
lean_dec(v___x_44_);
v___x_46_ = lean_int_add(v___x_43_, v___x_45_);
lean_dec(v___x_45_);
lean_dec(v___x_43_);
v___x_47_ = l_Std_Time_Duration_ofNanoseconds(v___x_46_);
lean_dec(v___x_46_);
v___x_48_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object* v_tm_49_, lean_object* v_tz_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Time_DateTime_ofTimestamp___lam__0(v_tm_49_, v_tz_50_, v_x_51_);
lean_dec_ref(v_tz_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object* v_tm_53_, lean_object* v_tz_54_){
_start:
{
lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
lean_inc_ref(v_tm_53_);
v___f_55_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestamp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_55_, 0, v_tm_53_);
lean_closure_set(v___f_55_, 1, v_tz_54_);
v___x_56_ = lean_mk_thunk(v___f_55_);
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v_tm_53_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0(lean_object* v___x_58_, lean_object* v_tz_59_, lean_object* v_x_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_second_63_; lean_object* v_nano_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_second_69_; lean_object* v_nano_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_61_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_58_);
v___x_62_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_61_);
v_second_63_ = lean_ctor_get(v___x_62_, 0);
lean_inc(v_second_63_);
v_nano_64_ = lean_ctor_get(v___x_62_, 1);
lean_inc(v_nano_64_);
lean_dec_ref(v___x_62_);
v___x_65_ = l_Std_Time_TimeZone_toSeconds(v_tz_59_);
v___x_66_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_67_ = lean_int_mul(v___x_65_, v___x_66_);
lean_dec(v___x_65_);
v___x_68_ = l_Std_Time_Duration_ofNanoseconds(v___x_67_);
lean_dec(v___x_67_);
v_second_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_second_69_);
v_nano_70_ = lean_ctor_get(v___x_68_, 1);
lean_inc(v_nano_70_);
lean_dec_ref(v___x_68_);
v___x_71_ = lean_int_mul(v_second_63_, v___x_66_);
lean_dec(v_second_63_);
v___x_72_ = lean_int_add(v___x_71_, v_nano_64_);
lean_dec(v_nano_64_);
lean_dec(v___x_71_);
v___x_73_ = lean_int_mul(v_second_69_, v___x_66_);
lean_dec(v_second_69_);
v___x_74_ = lean_int_add(v___x_73_, v_nano_70_);
lean_dec(v_nano_70_);
lean_dec(v___x_73_);
v___x_75_ = lean_int_add(v___x_72_, v___x_74_);
lean_dec(v___x_74_);
lean_dec(v___x_72_);
v___x_76_ = l_Std_Time_Duration_ofNanoseconds(v___x_75_);
lean_dec(v___x_75_);
v___x_77_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0___boxed(lean_object* v___x_78_, lean_object* v_tz_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Std_Time_DateTime_instInhabited___lam__0(v___x_78_, v_tz_79_, v_x_80_);
lean_dec_ref(v_tz_79_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited(lean_object* v_tz_82_){
_start:
{
lean_object* v___x_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = l_Std_Time_instInhabitedTimestamp_default;
v___f_84_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_instInhabited___lam__0___boxed), 3, 2);
lean_closure_set(v___f_84_, 0, v___x_83_);
lean_closure_set(v___f_84_, 1, v_tz_82_);
v___x_85_ = lean_mk_thunk(v___f_84_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_83_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(lean_object* v_date_87_){
_start:
{
lean_object* v_date_88_; lean_object* v___x_89_; lean_object* v_date_90_; lean_object* v___x_91_; 
v_date_88_ = lean_ctor_get(v_date_87_, 1);
v___x_89_ = lean_thunk_get_own(v_date_88_);
v_date_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc_ref(v_date_90_);
lean_dec(v___x_89_);
v___x_91_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg___boxed(lean_object* v_date_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(v_date_92_);
lean_dec_ref(v_date_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch(lean_object* v_tz_94_, lean_object* v_date_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(v_date_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___boxed(lean_object* v_tz_97_, lean_object* v_date_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_Time_DateTime_toDaysSinceUNIXEpoch(v_tz_97_, v_date_98_);
lean_dec_ref(v_date_98_);
lean_dec_ref(v_tz_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg(lean_object* v_date_100_){
_start:
{
lean_object* v_timestamp_101_; 
v_timestamp_101_ = lean_ctor_get(v_date_100_, 0);
lean_inc_ref(v_timestamp_101_);
return v_timestamp_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg___boxed(lean_object* v_date_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_Time_DateTime_toTimestamp___redArg(v_date_102_);
lean_dec_ref(v_date_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object* v_tz_104_, lean_object* v_date_105_){
_start:
{
lean_object* v_timestamp_106_; 
v_timestamp_106_ = lean_ctor_get(v_date_105_, 0);
lean_inc_ref(v_timestamp_106_);
return v_timestamp_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object* v_tz_107_, lean_object* v_date_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Std_Time_DateTime_toTimestamp(v_tz_107_, v_date_108_);
lean_dec_ref(v_date_108_);
lean_dec_ref(v_tz_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(lean_object* v_timestamp_110_, lean_object* v_tz_u2081_111_, lean_object* v_x_112_){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_second_115_; lean_object* v_nano_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_second_121_; lean_object* v_nano_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_113_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_110_);
v___x_114_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_113_);
v_second_115_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_second_115_);
v_nano_116_ = lean_ctor_get(v___x_114_, 1);
lean_inc(v_nano_116_);
lean_dec_ref(v___x_114_);
v___x_117_ = l_Std_Time_TimeZone_toSeconds(v_tz_u2081_111_);
v___x_118_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_119_ = lean_int_mul(v___x_117_, v___x_118_);
lean_dec(v___x_117_);
v___x_120_ = l_Std_Time_Duration_ofNanoseconds(v___x_119_);
lean_dec(v___x_119_);
v_second_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_second_121_);
v_nano_122_ = lean_ctor_get(v___x_120_, 1);
lean_inc(v_nano_122_);
lean_dec_ref(v___x_120_);
v___x_123_ = lean_int_mul(v_second_115_, v___x_118_);
lean_dec(v_second_115_);
v___x_124_ = lean_int_add(v___x_123_, v_nano_116_);
lean_dec(v_nano_116_);
lean_dec(v___x_123_);
v___x_125_ = lean_int_mul(v_second_121_, v___x_118_);
lean_dec(v_second_121_);
v___x_126_ = lean_int_add(v___x_125_, v_nano_122_);
lean_dec(v_nano_122_);
lean_dec(v___x_125_);
v___x_127_ = lean_int_add(v___x_124_, v___x_126_);
lean_dec(v___x_126_);
lean_dec(v___x_124_);
v___x_128_ = l_Std_Time_Duration_ofNanoseconds(v___x_127_);
lean_dec(v___x_127_);
v___x_129_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed(lean_object* v_timestamp_130_, lean_object* v_tz_u2081_131_, lean_object* v_x_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(v_timestamp_130_, v_tz_u2081_131_, v_x_132_);
lean_dec_ref(v_tz_u2081_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg(lean_object* v_date_134_, lean_object* v_tz_u2081_135_){
_start:
{
lean_object* v_timestamp_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_145_; 
v_timestamp_136_ = lean_ctor_get(v_date_134_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v_date_134_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v_date_134_, 1);
lean_dec(v_unused_146_);
v___x_138_ = v_date_134_;
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_timestamp_136_);
lean_dec(v_date_134_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_145_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
lean_inc_ref(v_timestamp_136_);
v___f_140_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_140_, 0, v_timestamp_136_);
lean_closure_set(v___f_140_, 1, v_tz_u2081_135_);
v___x_141_ = lean_mk_thunk(v___f_140_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_timestamp_136_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_141_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone(lean_object* v_tz_147_, lean_object* v_date_148_, lean_object* v_tz_u2081_149_){
_start:
{
lean_object* v_timestamp_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_159_; 
v_timestamp_150_ = lean_ctor_get(v_date_148_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_date_148_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_date_148_, 1);
lean_dec(v_unused_160_);
v___x_152_ = v_date_148_;
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_timestamp_150_);
lean_dec(v_date_148_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
lean_inc_ref(v_timestamp_150_);
v___f_154_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_154_, 0, v_timestamp_150_);
lean_closure_set(v___f_154_, 1, v_tz_u2081_149_);
v___x_155_ = lean_mk_thunk(v___f_154_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___x_155_);
v___x_157_ = v___x_152_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_timestamp_150_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___boxed(lean_object* v_tz_161_, lean_object* v_date_162_, lean_object* v_tz_u2081_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Std_Time_DateTime_convertTimeZone(v_tz_161_, v_date_162_, v_tz_u2081_163_);
lean_dec_ref(v_tz_161_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0(lean_object* v_date_165_, lean_object* v_tz_166_, lean_object* v_x_167_){
_start:
{
lean_object* v___x_168_; lean_object* v_second_169_; lean_object* v_nano_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v_second_175_; lean_object* v_nano_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_168_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_165_);
v_second_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_second_169_);
v_nano_170_ = lean_ctor_get(v___x_168_, 1);
lean_inc(v_nano_170_);
lean_dec_ref(v___x_168_);
v___x_171_ = l_Std_Time_TimeZone_toSeconds(v_tz_166_);
v___x_172_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_173_ = lean_int_mul(v___x_171_, v___x_172_);
lean_dec(v___x_171_);
v___x_174_ = l_Std_Time_Duration_ofNanoseconds(v___x_173_);
lean_dec(v___x_173_);
v_second_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_second_175_);
v_nano_176_ = lean_ctor_get(v___x_174_, 1);
lean_inc(v_nano_176_);
lean_dec_ref(v___x_174_);
v___x_177_ = lean_int_mul(v_second_169_, v___x_172_);
lean_dec(v_second_169_);
v___x_178_ = lean_int_add(v___x_177_, v_nano_170_);
lean_dec(v_nano_170_);
lean_dec(v___x_177_);
v___x_179_ = lean_int_mul(v_second_175_, v___x_172_);
lean_dec(v_second_175_);
v___x_180_ = lean_int_add(v___x_179_, v_nano_176_);
lean_dec(v_nano_176_);
lean_dec(v___x_179_);
v___x_181_ = lean_int_add(v___x_178_, v___x_180_);
lean_dec(v___x_180_);
lean_dec(v___x_178_);
v___x_182_ = l_Std_Time_Duration_ofNanoseconds(v___x_181_);
lean_dec(v___x_181_);
v___x_183_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed(lean_object* v_date_184_, lean_object* v_tz_185_, lean_object* v_x_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0(v_date_184_, v_tz_185_, v_x_186_);
lean_dec_ref(v_tz_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC(lean_object* v_date_188_, lean_object* v_tz_189_){
_start:
{
lean_object* v___f_190_; lean_object* v_tm_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
lean_inc_ref(v_date_188_);
v___f_190_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_190_, 0, v_date_188_);
lean_closure_set(v___f_190_, 1, v_tz_189_);
v_tm_191_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_188_);
v___x_192_ = lean_mk_thunk(v___f_190_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v_tm_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object* v_date_194_, lean_object* v_x_195_){
_start:
{
lean_inc_ref(v_date_194_);
return v_date_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(lean_object* v_date_196_, lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Time_DateTime_ofPlainDateTime___lam__0(v_date_196_, v_x_197_);
lean_dec_ref(v_date_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object* v_date_199_, lean_object* v_tz_200_){
_start:
{
lean_object* v___x_201_; lean_object* v_second_202_; lean_object* v_nano_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v_second_209_; lean_object* v_nano_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_227_; 
lean_inc_ref(v_date_199_);
v___x_201_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_199_);
v_second_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_second_202_);
v_nano_203_ = lean_ctor_get(v___x_201_, 1);
lean_inc(v_nano_203_);
lean_dec_ref(v___x_201_);
v___x_204_ = l_Std_Time_TimeZone_toSeconds(v_tz_200_);
v___x_205_ = lean_int_neg(v___x_204_);
lean_dec(v___x_204_);
v___x_206_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_207_ = lean_int_mul(v___x_205_, v___x_206_);
lean_dec(v___x_205_);
v___x_208_ = l_Std_Time_Duration_ofNanoseconds(v___x_207_);
lean_dec(v___x_207_);
v_second_209_ = lean_ctor_get(v___x_208_, 0);
v_nano_210_ = lean_ctor_get(v___x_208_, 1);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_227_ == 0)
{
v___x_212_ = v___x_208_;
v_isShared_213_ = v_isSharedCheck_227_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_nano_210_);
lean_inc(v_second_209_);
lean_dec(v___x_208_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_227_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___f_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v_tm_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___f_214_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed), 2, 1);
lean_closure_set(v___f_214_, 0, v_date_199_);
v___x_215_ = lean_int_mul(v_second_202_, v___x_206_);
lean_dec(v_second_202_);
v___x_216_ = lean_int_add(v___x_215_, v_nano_203_);
lean_dec(v_nano_203_);
lean_dec(v___x_215_);
v___x_217_ = lean_int_mul(v_second_209_, v___x_206_);
lean_dec(v_second_209_);
v___x_218_ = lean_int_add(v___x_217_, v_nano_210_);
lean_dec(v_nano_210_);
lean_dec(v___x_217_);
v___x_219_ = lean_int_add(v___x_216_, v___x_218_);
lean_dec(v___x_218_);
lean_dec(v___x_216_);
v___x_220_ = l_Std_Time_Duration_ofNanoseconds(v___x_219_);
lean_dec(v___x_219_);
v_tm_221_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_220_);
v___x_222_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_221_);
v___x_223_ = lean_mk_thunk(v___f_214_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 1, v___x_223_);
lean_ctor_set(v___x_212_, 0, v___x_222_);
v___x_225_ = v___x_212_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___boxed(lean_object* v_date_228_, lean_object* v_tz_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_Time_DateTime_ofPlainDateTime(v_date_228_, v_tz_229_);
lean_dec_ref(v_tz_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0(lean_object* v___x_231_, lean_object* v_x_232_){
_start:
{
lean_inc_ref(v___x_231_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0___boxed(lean_object* v___x_233_, lean_object* v_x_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Time_DateTime_addHours___lam__0(v___x_233_, v_x_234_);
lean_dec_ref(v___x_233_);
return v_res_235_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_cstr_to_nat("3600000000000");
v___x_237_ = lean_nat_to_int(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object* v_tz_238_, lean_object* v_dt_239_, lean_object* v_hours_240_){
_start:
{
lean_object* v_date_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_284_; 
v_date_241_ = lean_ctor_get(v_dt_239_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_dt_239_);
if (v_isSharedCheck_284_ == 0)
{
lean_object* v_unused_285_; 
v_unused_285_ = lean_ctor_get(v_dt_239_, 0);
lean_dec(v_unused_285_);
v___x_243_ = v_dt_239_;
v_isShared_244_ = v_isSharedCheck_284_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_date_241_);
lean_dec(v_dt_239_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_284_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_second_247_; lean_object* v_nano_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_second_252_; lean_object* v_nano_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_second_263_; lean_object* v_nano_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_second_269_; lean_object* v_nano_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_tm_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_245_ = lean_thunk_get_own(v_date_241_);
lean_dec_ref(v_date_241_);
v___x_246_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_245_);
v_second_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_second_247_);
v_nano_248_ = lean_ctor_get(v___x_246_, 1);
lean_inc(v_nano_248_);
lean_dec_ref(v___x_246_);
v___x_249_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_250_ = lean_int_mul(v_hours_240_, v___x_249_);
v___x_251_ = l_Std_Time_Duration_ofNanoseconds(v___x_250_);
lean_dec(v___x_250_);
v_second_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_second_252_);
v_nano_253_ = lean_ctor_get(v___x_251_, 1);
lean_inc(v_nano_253_);
lean_dec_ref(v___x_251_);
v___x_254_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_255_ = lean_int_mul(v_second_247_, v___x_254_);
lean_dec(v_second_247_);
v___x_256_ = lean_int_add(v___x_255_, v_nano_248_);
lean_dec(v_nano_248_);
lean_dec(v___x_255_);
v___x_257_ = lean_int_mul(v_second_252_, v___x_254_);
lean_dec(v_second_252_);
v___x_258_ = lean_int_add(v___x_257_, v_nano_253_);
lean_dec(v_nano_253_);
lean_dec(v___x_257_);
v___x_259_ = lean_int_add(v___x_256_, v___x_258_);
lean_dec(v___x_258_);
lean_dec(v___x_256_);
v___x_260_ = l_Std_Time_Duration_ofNanoseconds(v___x_259_);
lean_dec(v___x_259_);
v___x_261_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_260_);
lean_inc_ref(v___x_261_);
v___x_262_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_261_);
v_second_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_second_263_);
v_nano_264_ = lean_ctor_get(v___x_262_, 1);
lean_inc(v_nano_264_);
lean_dec_ref(v___x_262_);
v___x_265_ = l_Std_Time_TimeZone_toSeconds(v_tz_238_);
v___x_266_ = lean_int_neg(v___x_265_);
lean_dec(v___x_265_);
v___x_267_ = lean_int_mul(v___x_266_, v___x_254_);
lean_dec(v___x_266_);
v___x_268_ = l_Std_Time_Duration_ofNanoseconds(v___x_267_);
lean_dec(v___x_267_);
v_second_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_second_269_);
v_nano_270_ = lean_ctor_get(v___x_268_, 1);
lean_inc(v_nano_270_);
lean_dec_ref(v___x_268_);
v___f_271_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_271_, 0, v___x_261_);
v___x_272_ = lean_int_mul(v_second_263_, v___x_254_);
lean_dec(v_second_263_);
v___x_273_ = lean_int_add(v___x_272_, v_nano_264_);
lean_dec(v_nano_264_);
lean_dec(v___x_272_);
v___x_274_ = lean_int_mul(v_second_269_, v___x_254_);
lean_dec(v_second_269_);
v___x_275_ = lean_int_add(v___x_274_, v_nano_270_);
lean_dec(v_nano_270_);
lean_dec(v___x_274_);
v___x_276_ = lean_int_add(v___x_273_, v___x_275_);
lean_dec(v___x_275_);
lean_dec(v___x_273_);
v___x_277_ = l_Std_Time_Duration_ofNanoseconds(v___x_276_);
lean_dec(v___x_276_);
v_tm_278_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_277_);
v___x_279_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_278_);
v___x_280_ = lean_mk_thunk(v___f_271_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___x_280_);
lean_ctor_set(v___x_243_, 0, v___x_279_);
v___x_282_ = v___x_243_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object* v_tz_286_, lean_object* v_dt_287_, lean_object* v_hours_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_Time_DateTime_addHours(v_tz_286_, v_dt_287_, v_hours_288_);
lean_dec(v_hours_288_);
lean_dec_ref(v_tz_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object* v_tz_290_, lean_object* v_dt_291_, lean_object* v_hours_292_){
_start:
{
lean_object* v_date_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_337_; 
v_date_293_ = lean_ctor_get(v_dt_291_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_dt_291_);
if (v_isSharedCheck_337_ == 0)
{
lean_object* v_unused_338_; 
v_unused_338_ = lean_ctor_get(v_dt_291_, 0);
lean_dec(v_unused_338_);
v___x_295_ = v_dt_291_;
v_isShared_296_ = v_isSharedCheck_337_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_date_293_);
lean_dec(v_dt_291_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_337_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_second_299_; lean_object* v_nano_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_second_305_; lean_object* v_nano_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v_second_316_; lean_object* v_nano_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_second_322_; lean_object* v_nano_323_; lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v_tm_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_297_ = lean_thunk_get_own(v_date_293_);
lean_dec_ref(v_date_293_);
v___x_298_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_297_);
v_second_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_second_299_);
v_nano_300_ = lean_ctor_get(v___x_298_, 1);
lean_inc(v_nano_300_);
lean_dec_ref(v___x_298_);
v___x_301_ = lean_int_neg(v_hours_292_);
v___x_302_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_303_ = lean_int_mul(v___x_301_, v___x_302_);
lean_dec(v___x_301_);
v___x_304_ = l_Std_Time_Duration_ofNanoseconds(v___x_303_);
lean_dec(v___x_303_);
v_second_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_second_305_);
v_nano_306_ = lean_ctor_get(v___x_304_, 1);
lean_inc(v_nano_306_);
lean_dec_ref(v___x_304_);
v___x_307_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_308_ = lean_int_mul(v_second_299_, v___x_307_);
lean_dec(v_second_299_);
v___x_309_ = lean_int_add(v___x_308_, v_nano_300_);
lean_dec(v_nano_300_);
lean_dec(v___x_308_);
v___x_310_ = lean_int_mul(v_second_305_, v___x_307_);
lean_dec(v_second_305_);
v___x_311_ = lean_int_add(v___x_310_, v_nano_306_);
lean_dec(v_nano_306_);
lean_dec(v___x_310_);
v___x_312_ = lean_int_add(v___x_309_, v___x_311_);
lean_dec(v___x_311_);
lean_dec(v___x_309_);
v___x_313_ = l_Std_Time_Duration_ofNanoseconds(v___x_312_);
lean_dec(v___x_312_);
v___x_314_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_313_);
lean_inc_ref(v___x_314_);
v___x_315_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_314_);
v_second_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc(v_second_316_);
v_nano_317_ = lean_ctor_get(v___x_315_, 1);
lean_inc(v_nano_317_);
lean_dec_ref(v___x_315_);
v___x_318_ = l_Std_Time_TimeZone_toSeconds(v_tz_290_);
v___x_319_ = lean_int_neg(v___x_318_);
lean_dec(v___x_318_);
v___x_320_ = lean_int_mul(v___x_319_, v___x_307_);
lean_dec(v___x_319_);
v___x_321_ = l_Std_Time_Duration_ofNanoseconds(v___x_320_);
lean_dec(v___x_320_);
v_second_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_second_322_);
v_nano_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc(v_nano_323_);
lean_dec_ref(v___x_321_);
v___f_324_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_324_, 0, v___x_314_);
v___x_325_ = lean_int_mul(v_second_316_, v___x_307_);
lean_dec(v_second_316_);
v___x_326_ = lean_int_add(v___x_325_, v_nano_317_);
lean_dec(v_nano_317_);
lean_dec(v___x_325_);
v___x_327_ = lean_int_mul(v_second_322_, v___x_307_);
lean_dec(v_second_322_);
v___x_328_ = lean_int_add(v___x_327_, v_nano_323_);
lean_dec(v_nano_323_);
lean_dec(v___x_327_);
v___x_329_ = lean_int_add(v___x_326_, v___x_328_);
lean_dec(v___x_328_);
lean_dec(v___x_326_);
v___x_330_ = l_Std_Time_Duration_ofNanoseconds(v___x_329_);
lean_dec(v___x_329_);
v_tm_331_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_330_);
v___x_332_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_331_);
v___x_333_ = lean_mk_thunk(v___f_324_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_333_);
lean_ctor_set(v___x_295_, 0, v___x_332_);
v___x_335_ = v___x_295_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object* v_tz_339_, lean_object* v_dt_340_, lean_object* v_hours_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Time_DateTime_subHours(v_tz_339_, v_dt_340_, v_hours_341_);
lean_dec(v_hours_341_);
lean_dec_ref(v_tz_339_);
return v_res_342_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_cstr_to_nat("60000000000");
v___x_344_ = lean_nat_to_int(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object* v_tz_345_, lean_object* v_dt_346_, lean_object* v_minutes_347_){
_start:
{
lean_object* v_date_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_391_; 
v_date_348_ = lean_ctor_get(v_dt_346_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_dt_346_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_dt_346_, 0);
lean_dec(v_unused_392_);
v___x_350_ = v_dt_346_;
v_isShared_351_ = v_isSharedCheck_391_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_date_348_);
lean_dec(v_dt_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_391_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v_second_354_; lean_object* v_nano_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v_second_359_; lean_object* v_nano_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_second_370_; lean_object* v_nano_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v_second_376_; lean_object* v_nano_377_; lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v_tm_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_352_ = lean_thunk_get_own(v_date_348_);
lean_dec_ref(v_date_348_);
v___x_353_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_352_);
v_second_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_second_354_);
v_nano_355_ = lean_ctor_get(v___x_353_, 1);
lean_inc(v_nano_355_);
lean_dec_ref(v___x_353_);
v___x_356_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_357_ = lean_int_mul(v_minutes_347_, v___x_356_);
v___x_358_ = l_Std_Time_Duration_ofNanoseconds(v___x_357_);
lean_dec(v___x_357_);
v_second_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_second_359_);
v_nano_360_ = lean_ctor_get(v___x_358_, 1);
lean_inc(v_nano_360_);
lean_dec_ref(v___x_358_);
v___x_361_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_362_ = lean_int_mul(v_second_354_, v___x_361_);
lean_dec(v_second_354_);
v___x_363_ = lean_int_add(v___x_362_, v_nano_355_);
lean_dec(v_nano_355_);
lean_dec(v___x_362_);
v___x_364_ = lean_int_mul(v_second_359_, v___x_361_);
lean_dec(v_second_359_);
v___x_365_ = lean_int_add(v___x_364_, v_nano_360_);
lean_dec(v_nano_360_);
lean_dec(v___x_364_);
v___x_366_ = lean_int_add(v___x_363_, v___x_365_);
lean_dec(v___x_365_);
lean_dec(v___x_363_);
v___x_367_ = l_Std_Time_Duration_ofNanoseconds(v___x_366_);
lean_dec(v___x_366_);
v___x_368_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_367_);
lean_inc_ref(v___x_368_);
v___x_369_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_368_);
v_second_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_second_370_);
v_nano_371_ = lean_ctor_get(v___x_369_, 1);
lean_inc(v_nano_371_);
lean_dec_ref(v___x_369_);
v___x_372_ = l_Std_Time_TimeZone_toSeconds(v_tz_345_);
v___x_373_ = lean_int_neg(v___x_372_);
lean_dec(v___x_372_);
v___x_374_ = lean_int_mul(v___x_373_, v___x_361_);
lean_dec(v___x_373_);
v___x_375_ = l_Std_Time_Duration_ofNanoseconds(v___x_374_);
lean_dec(v___x_374_);
v_second_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_second_376_);
v_nano_377_ = lean_ctor_get(v___x_375_, 1);
lean_inc(v_nano_377_);
lean_dec_ref(v___x_375_);
v___f_378_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_378_, 0, v___x_368_);
v___x_379_ = lean_int_mul(v_second_370_, v___x_361_);
lean_dec(v_second_370_);
v___x_380_ = lean_int_add(v___x_379_, v_nano_371_);
lean_dec(v_nano_371_);
lean_dec(v___x_379_);
v___x_381_ = lean_int_mul(v_second_376_, v___x_361_);
lean_dec(v_second_376_);
v___x_382_ = lean_int_add(v___x_381_, v_nano_377_);
lean_dec(v_nano_377_);
lean_dec(v___x_381_);
v___x_383_ = lean_int_add(v___x_380_, v___x_382_);
lean_dec(v___x_382_);
lean_dec(v___x_380_);
v___x_384_ = l_Std_Time_Duration_ofNanoseconds(v___x_383_);
lean_dec(v___x_383_);
v_tm_385_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_384_);
v___x_386_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_385_);
v___x_387_ = lean_mk_thunk(v___f_378_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_387_);
lean_ctor_set(v___x_350_, 0, v___x_386_);
v___x_389_ = v___x_350_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object* v_tz_393_, lean_object* v_dt_394_, lean_object* v_minutes_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_Time_DateTime_addMinutes(v_tz_393_, v_dt_394_, v_minutes_395_);
lean_dec(v_minutes_395_);
lean_dec_ref(v_tz_393_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object* v_tz_397_, lean_object* v_dt_398_, lean_object* v_minutes_399_){
_start:
{
lean_object* v_date_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_444_; 
v_date_400_ = lean_ctor_get(v_dt_398_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_dt_398_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; 
v_unused_445_ = lean_ctor_get(v_dt_398_, 0);
lean_dec(v_unused_445_);
v___x_402_ = v_dt_398_;
v_isShared_403_ = v_isSharedCheck_444_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_date_400_);
lean_dec(v_dt_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_444_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v_second_406_; lean_object* v_nano_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_second_412_; lean_object* v_nano_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_second_423_; lean_object* v_nano_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_second_429_; lean_object* v_nano_430_; lean_object* v___f_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_tm_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_404_ = lean_thunk_get_own(v_date_400_);
lean_dec_ref(v_date_400_);
v___x_405_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_404_);
v_second_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_second_406_);
v_nano_407_ = lean_ctor_get(v___x_405_, 1);
lean_inc(v_nano_407_);
lean_dec_ref(v___x_405_);
v___x_408_ = lean_int_neg(v_minutes_399_);
v___x_409_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_410_ = lean_int_mul(v___x_408_, v___x_409_);
lean_dec(v___x_408_);
v___x_411_ = l_Std_Time_Duration_ofNanoseconds(v___x_410_);
lean_dec(v___x_410_);
v_second_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_second_412_);
v_nano_413_ = lean_ctor_get(v___x_411_, 1);
lean_inc(v_nano_413_);
lean_dec_ref(v___x_411_);
v___x_414_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_415_ = lean_int_mul(v_second_406_, v___x_414_);
lean_dec(v_second_406_);
v___x_416_ = lean_int_add(v___x_415_, v_nano_407_);
lean_dec(v_nano_407_);
lean_dec(v___x_415_);
v___x_417_ = lean_int_mul(v_second_412_, v___x_414_);
lean_dec(v_second_412_);
v___x_418_ = lean_int_add(v___x_417_, v_nano_413_);
lean_dec(v_nano_413_);
lean_dec(v___x_417_);
v___x_419_ = lean_int_add(v___x_416_, v___x_418_);
lean_dec(v___x_418_);
lean_dec(v___x_416_);
v___x_420_ = l_Std_Time_Duration_ofNanoseconds(v___x_419_);
lean_dec(v___x_419_);
v___x_421_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_420_);
lean_inc_ref(v___x_421_);
v___x_422_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_421_);
v_second_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_second_423_);
v_nano_424_ = lean_ctor_get(v___x_422_, 1);
lean_inc(v_nano_424_);
lean_dec_ref(v___x_422_);
v___x_425_ = l_Std_Time_TimeZone_toSeconds(v_tz_397_);
v___x_426_ = lean_int_neg(v___x_425_);
lean_dec(v___x_425_);
v___x_427_ = lean_int_mul(v___x_426_, v___x_414_);
lean_dec(v___x_426_);
v___x_428_ = l_Std_Time_Duration_ofNanoseconds(v___x_427_);
lean_dec(v___x_427_);
v_second_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_second_429_);
v_nano_430_ = lean_ctor_get(v___x_428_, 1);
lean_inc(v_nano_430_);
lean_dec_ref(v___x_428_);
v___f_431_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_431_, 0, v___x_421_);
v___x_432_ = lean_int_mul(v_second_423_, v___x_414_);
lean_dec(v_second_423_);
v___x_433_ = lean_int_add(v___x_432_, v_nano_424_);
lean_dec(v_nano_424_);
lean_dec(v___x_432_);
v___x_434_ = lean_int_mul(v_second_429_, v___x_414_);
lean_dec(v_second_429_);
v___x_435_ = lean_int_add(v___x_434_, v_nano_430_);
lean_dec(v_nano_430_);
lean_dec(v___x_434_);
v___x_436_ = lean_int_add(v___x_433_, v___x_435_);
lean_dec(v___x_435_);
lean_dec(v___x_433_);
v___x_437_ = l_Std_Time_Duration_ofNanoseconds(v___x_436_);
lean_dec(v___x_436_);
v_tm_438_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_437_);
v___x_439_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_438_);
v___x_440_ = lean_mk_thunk(v___f_431_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 1, v___x_440_);
lean_ctor_set(v___x_402_, 0, v___x_439_);
v___x_442_ = v___x_402_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object* v_tz_446_, lean_object* v_dt_447_, lean_object* v_minutes_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_Time_DateTime_subMinutes(v_tz_446_, v_dt_447_, v_minutes_448_);
lean_dec(v_minutes_448_);
lean_dec_ref(v_tz_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object* v_tz_450_, lean_object* v_dt_451_, lean_object* v_seconds_452_){
_start:
{
lean_object* v_date_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_495_; 
v_date_453_ = lean_ctor_get(v_dt_451_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_dt_451_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v_dt_451_, 0);
lean_dec(v_unused_496_);
v___x_455_ = v_dt_451_;
v_isShared_456_ = v_isSharedCheck_495_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_date_453_);
lean_dec(v_dt_451_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_495_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v_second_459_; lean_object* v_nano_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_second_464_; lean_object* v_nano_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_second_474_; lean_object* v_nano_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v_second_480_; lean_object* v_nano_481_; lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_tm_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_457_ = lean_thunk_get_own(v_date_453_);
lean_dec_ref(v_date_453_);
v___x_458_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_457_);
v_second_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_second_459_);
v_nano_460_ = lean_ctor_get(v___x_458_, 1);
lean_inc(v_nano_460_);
lean_dec_ref(v___x_458_);
v___x_461_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_462_ = lean_int_mul(v_seconds_452_, v___x_461_);
v___x_463_ = l_Std_Time_Duration_ofNanoseconds(v___x_462_);
lean_dec(v___x_462_);
v_second_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_second_464_);
v_nano_465_ = lean_ctor_get(v___x_463_, 1);
lean_inc(v_nano_465_);
lean_dec_ref(v___x_463_);
v___x_466_ = lean_int_mul(v_second_459_, v___x_461_);
lean_dec(v_second_459_);
v___x_467_ = lean_int_add(v___x_466_, v_nano_460_);
lean_dec(v_nano_460_);
lean_dec(v___x_466_);
v___x_468_ = lean_int_mul(v_second_464_, v___x_461_);
lean_dec(v_second_464_);
v___x_469_ = lean_int_add(v___x_468_, v_nano_465_);
lean_dec(v_nano_465_);
lean_dec(v___x_468_);
v___x_470_ = lean_int_add(v___x_467_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v___x_467_);
v___x_471_ = l_Std_Time_Duration_ofNanoseconds(v___x_470_);
lean_dec(v___x_470_);
v___x_472_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_471_);
lean_inc_ref(v___x_472_);
v___x_473_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_472_);
v_second_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_second_474_);
v_nano_475_ = lean_ctor_get(v___x_473_, 1);
lean_inc(v_nano_475_);
lean_dec_ref(v___x_473_);
v___x_476_ = l_Std_Time_TimeZone_toSeconds(v_tz_450_);
v___x_477_ = lean_int_neg(v___x_476_);
lean_dec(v___x_476_);
v___x_478_ = lean_int_mul(v___x_477_, v___x_461_);
lean_dec(v___x_477_);
v___x_479_ = l_Std_Time_Duration_ofNanoseconds(v___x_478_);
lean_dec(v___x_478_);
v_second_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_second_480_);
v_nano_481_ = lean_ctor_get(v___x_479_, 1);
lean_inc(v_nano_481_);
lean_dec_ref(v___x_479_);
v___f_482_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_482_, 0, v___x_472_);
v___x_483_ = lean_int_mul(v_second_474_, v___x_461_);
lean_dec(v_second_474_);
v___x_484_ = lean_int_add(v___x_483_, v_nano_475_);
lean_dec(v_nano_475_);
lean_dec(v___x_483_);
v___x_485_ = lean_int_mul(v_second_480_, v___x_461_);
lean_dec(v_second_480_);
v___x_486_ = lean_int_add(v___x_485_, v_nano_481_);
lean_dec(v_nano_481_);
lean_dec(v___x_485_);
v___x_487_ = lean_int_add(v___x_484_, v___x_486_);
lean_dec(v___x_486_);
lean_dec(v___x_484_);
v___x_488_ = l_Std_Time_Duration_ofNanoseconds(v___x_487_);
lean_dec(v___x_487_);
v_tm_489_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_488_);
v___x_490_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_489_);
v___x_491_ = lean_mk_thunk(v___f_482_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_491_);
lean_ctor_set(v___x_455_, 0, v___x_490_);
v___x_493_ = v___x_455_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object* v_tz_497_, lean_object* v_dt_498_, lean_object* v_seconds_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Time_DateTime_addSeconds(v_tz_497_, v_dt_498_, v_seconds_499_);
lean_dec(v_seconds_499_);
lean_dec_ref(v_tz_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object* v_tz_501_, lean_object* v_dt_502_, lean_object* v_seconds_503_){
_start:
{
lean_object* v_date_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_547_; 
v_date_504_ = lean_ctor_get(v_dt_502_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_dt_502_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; 
v_unused_548_ = lean_ctor_get(v_dt_502_, 0);
lean_dec(v_unused_548_);
v___x_506_ = v_dt_502_;
v_isShared_507_ = v_isSharedCheck_547_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_date_504_);
lean_dec(v_dt_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_547_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_second_510_; lean_object* v_nano_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_second_516_; lean_object* v_nano_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v_second_526_; lean_object* v_nano_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_second_532_; lean_object* v_nano_533_; lean_object* v___f_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_tm_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_508_ = lean_thunk_get_own(v_date_504_);
lean_dec_ref(v_date_504_);
v___x_509_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_508_);
v_second_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_second_510_);
v_nano_511_ = lean_ctor_get(v___x_509_, 1);
lean_inc(v_nano_511_);
lean_dec_ref(v___x_509_);
v___x_512_ = lean_int_neg(v_seconds_503_);
v___x_513_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_514_ = lean_int_mul(v___x_512_, v___x_513_);
lean_dec(v___x_512_);
v___x_515_ = l_Std_Time_Duration_ofNanoseconds(v___x_514_);
lean_dec(v___x_514_);
v_second_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_second_516_);
v_nano_517_ = lean_ctor_get(v___x_515_, 1);
lean_inc(v_nano_517_);
lean_dec_ref(v___x_515_);
v___x_518_ = lean_int_mul(v_second_510_, v___x_513_);
lean_dec(v_second_510_);
v___x_519_ = lean_int_add(v___x_518_, v_nano_511_);
lean_dec(v_nano_511_);
lean_dec(v___x_518_);
v___x_520_ = lean_int_mul(v_second_516_, v___x_513_);
lean_dec(v_second_516_);
v___x_521_ = lean_int_add(v___x_520_, v_nano_517_);
lean_dec(v_nano_517_);
lean_dec(v___x_520_);
v___x_522_ = lean_int_add(v___x_519_, v___x_521_);
lean_dec(v___x_521_);
lean_dec(v___x_519_);
v___x_523_ = l_Std_Time_Duration_ofNanoseconds(v___x_522_);
lean_dec(v___x_522_);
v___x_524_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_523_);
lean_inc_ref(v___x_524_);
v___x_525_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_524_);
v_second_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_second_526_);
v_nano_527_ = lean_ctor_get(v___x_525_, 1);
lean_inc(v_nano_527_);
lean_dec_ref(v___x_525_);
v___x_528_ = l_Std_Time_TimeZone_toSeconds(v_tz_501_);
v___x_529_ = lean_int_neg(v___x_528_);
lean_dec(v___x_528_);
v___x_530_ = lean_int_mul(v___x_529_, v___x_513_);
lean_dec(v___x_529_);
v___x_531_ = l_Std_Time_Duration_ofNanoseconds(v___x_530_);
lean_dec(v___x_530_);
v_second_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_second_532_);
v_nano_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_nano_533_);
lean_dec_ref(v___x_531_);
v___f_534_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_534_, 0, v___x_524_);
v___x_535_ = lean_int_mul(v_second_526_, v___x_513_);
lean_dec(v_second_526_);
v___x_536_ = lean_int_add(v___x_535_, v_nano_527_);
lean_dec(v_nano_527_);
lean_dec(v___x_535_);
v___x_537_ = lean_int_mul(v_second_532_, v___x_513_);
lean_dec(v_second_532_);
v___x_538_ = lean_int_add(v___x_537_, v_nano_533_);
lean_dec(v_nano_533_);
lean_dec(v___x_537_);
v___x_539_ = lean_int_add(v___x_536_, v___x_538_);
lean_dec(v___x_538_);
lean_dec(v___x_536_);
v___x_540_ = l_Std_Time_Duration_ofNanoseconds(v___x_539_);
lean_dec(v___x_539_);
v_tm_541_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_540_);
v___x_542_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_541_);
v___x_543_ = lean_mk_thunk(v___f_534_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v___x_543_);
lean_ctor_set(v___x_506_, 0, v___x_542_);
v___x_545_ = v___x_506_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object* v_tz_549_, lean_object* v_dt_550_, lean_object* v_seconds_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Time_DateTime_subSeconds(v_tz_549_, v_dt_550_, v_seconds_551_);
lean_dec(v_seconds_551_);
lean_dec_ref(v_tz_549_);
return v_res_552_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_unsigned_to_nat(1000000u);
v___x_554_ = lean_nat_to_int(v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object* v_tz_555_, lean_object* v_dt_556_, lean_object* v_milliseconds_557_){
_start:
{
lean_object* v_date_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_601_; 
v_date_558_ = lean_ctor_get(v_dt_556_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_dt_556_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_dt_556_, 0);
lean_dec(v_unused_602_);
v___x_560_ = v_dt_556_;
v_isShared_561_ = v_isSharedCheck_601_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_date_558_);
lean_dec(v_dt_556_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_601_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v_second_564_; lean_object* v_nano_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_second_569_; lean_object* v_nano_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_second_580_; lean_object* v_nano_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_second_586_; lean_object* v_nano_587_; lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_tm_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_562_ = lean_thunk_get_own(v_date_558_);
lean_dec_ref(v_date_558_);
v___x_563_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_562_);
v_second_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_second_564_);
v_nano_565_ = lean_ctor_get(v___x_563_, 1);
lean_inc(v_nano_565_);
lean_dec_ref(v___x_563_);
v___x_566_ = lean_obj_once(&l_Std_Time_DateTime_addMilliseconds___closed__0, &l_Std_Time_DateTime_addMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_addMilliseconds___closed__0);
v___x_567_ = lean_int_mul(v_milliseconds_557_, v___x_566_);
v___x_568_ = l_Std_Time_Duration_ofNanoseconds(v___x_567_);
lean_dec(v___x_567_);
v_second_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_second_569_);
v_nano_570_ = lean_ctor_get(v___x_568_, 1);
lean_inc(v_nano_570_);
lean_dec_ref(v___x_568_);
v___x_571_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_572_ = lean_int_mul(v_second_564_, v___x_571_);
lean_dec(v_second_564_);
v___x_573_ = lean_int_add(v___x_572_, v_nano_565_);
lean_dec(v_nano_565_);
lean_dec(v___x_572_);
v___x_574_ = lean_int_mul(v_second_569_, v___x_571_);
lean_dec(v_second_569_);
v___x_575_ = lean_int_add(v___x_574_, v_nano_570_);
lean_dec(v_nano_570_);
lean_dec(v___x_574_);
v___x_576_ = lean_int_add(v___x_573_, v___x_575_);
lean_dec(v___x_575_);
lean_dec(v___x_573_);
v___x_577_ = l_Std_Time_Duration_ofNanoseconds(v___x_576_);
lean_dec(v___x_576_);
v___x_578_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_577_);
lean_inc_ref(v___x_578_);
v___x_579_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_578_);
v_second_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_second_580_);
v_nano_581_ = lean_ctor_get(v___x_579_, 1);
lean_inc(v_nano_581_);
lean_dec_ref(v___x_579_);
v___x_582_ = l_Std_Time_TimeZone_toSeconds(v_tz_555_);
v___x_583_ = lean_int_neg(v___x_582_);
lean_dec(v___x_582_);
v___x_584_ = lean_int_mul(v___x_583_, v___x_571_);
lean_dec(v___x_583_);
v___x_585_ = l_Std_Time_Duration_ofNanoseconds(v___x_584_);
lean_dec(v___x_584_);
v_second_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_second_586_);
v_nano_587_ = lean_ctor_get(v___x_585_, 1);
lean_inc(v_nano_587_);
lean_dec_ref(v___x_585_);
v___f_588_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_588_, 0, v___x_578_);
v___x_589_ = lean_int_mul(v_second_580_, v___x_571_);
lean_dec(v_second_580_);
v___x_590_ = lean_int_add(v___x_589_, v_nano_581_);
lean_dec(v_nano_581_);
lean_dec(v___x_589_);
v___x_591_ = lean_int_mul(v_second_586_, v___x_571_);
lean_dec(v_second_586_);
v___x_592_ = lean_int_add(v___x_591_, v_nano_587_);
lean_dec(v_nano_587_);
lean_dec(v___x_591_);
v___x_593_ = lean_int_add(v___x_590_, v___x_592_);
lean_dec(v___x_592_);
lean_dec(v___x_590_);
v___x_594_ = l_Std_Time_Duration_ofNanoseconds(v___x_593_);
lean_dec(v___x_593_);
v_tm_595_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_594_);
v___x_596_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_595_);
v___x_597_ = lean_mk_thunk(v___f_588_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_597_);
lean_ctor_set(v___x_560_, 0, v___x_596_);
v___x_599_ = v___x_560_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object* v_tz_603_, lean_object* v_dt_604_, lean_object* v_milliseconds_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_Time_DateTime_addMilliseconds(v_tz_603_, v_dt_604_, v_milliseconds_605_);
lean_dec(v_milliseconds_605_);
lean_dec_ref(v_tz_603_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object* v_tz_607_, lean_object* v_dt_608_, lean_object* v_milliseconds_609_){
_start:
{
lean_object* v_date_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_654_; 
v_date_610_ = lean_ctor_get(v_dt_608_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_dt_608_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_dt_608_, 0);
lean_dec(v_unused_655_);
v___x_612_ = v_dt_608_;
v_isShared_613_ = v_isSharedCheck_654_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_date_610_);
lean_dec(v_dt_608_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_654_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_second_616_; lean_object* v_nano_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_second_622_; lean_object* v_nano_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v_second_633_; lean_object* v_nano_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v_second_639_; lean_object* v_nano_640_; lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_tm_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_614_ = lean_thunk_get_own(v_date_610_);
lean_dec_ref(v_date_610_);
v___x_615_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_614_);
v_second_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_second_616_);
v_nano_617_ = lean_ctor_get(v___x_615_, 1);
lean_inc(v_nano_617_);
lean_dec_ref(v___x_615_);
v___x_618_ = lean_int_neg(v_milliseconds_609_);
v___x_619_ = lean_obj_once(&l_Std_Time_DateTime_addMilliseconds___closed__0, &l_Std_Time_DateTime_addMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_addMilliseconds___closed__0);
v___x_620_ = lean_int_mul(v___x_618_, v___x_619_);
lean_dec(v___x_618_);
v___x_621_ = l_Std_Time_Duration_ofNanoseconds(v___x_620_);
lean_dec(v___x_620_);
v_second_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_second_622_);
v_nano_623_ = lean_ctor_get(v___x_621_, 1);
lean_inc(v_nano_623_);
lean_dec_ref(v___x_621_);
v___x_624_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_625_ = lean_int_mul(v_second_616_, v___x_624_);
lean_dec(v_second_616_);
v___x_626_ = lean_int_add(v___x_625_, v_nano_617_);
lean_dec(v_nano_617_);
lean_dec(v___x_625_);
v___x_627_ = lean_int_mul(v_second_622_, v___x_624_);
lean_dec(v_second_622_);
v___x_628_ = lean_int_add(v___x_627_, v_nano_623_);
lean_dec(v_nano_623_);
lean_dec(v___x_627_);
v___x_629_ = lean_int_add(v___x_626_, v___x_628_);
lean_dec(v___x_628_);
lean_dec(v___x_626_);
v___x_630_ = l_Std_Time_Duration_ofNanoseconds(v___x_629_);
lean_dec(v___x_629_);
v___x_631_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_630_);
lean_inc_ref(v___x_631_);
v___x_632_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_631_);
v_second_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_second_633_);
v_nano_634_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_nano_634_);
lean_dec_ref(v___x_632_);
v___x_635_ = l_Std_Time_TimeZone_toSeconds(v_tz_607_);
v___x_636_ = lean_int_neg(v___x_635_);
lean_dec(v___x_635_);
v___x_637_ = lean_int_mul(v___x_636_, v___x_624_);
lean_dec(v___x_636_);
v___x_638_ = l_Std_Time_Duration_ofNanoseconds(v___x_637_);
lean_dec(v___x_637_);
v_second_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_second_639_);
v_nano_640_ = lean_ctor_get(v___x_638_, 1);
lean_inc(v_nano_640_);
lean_dec_ref(v___x_638_);
v___f_641_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_641_, 0, v___x_631_);
v___x_642_ = lean_int_mul(v_second_633_, v___x_624_);
lean_dec(v_second_633_);
v___x_643_ = lean_int_add(v___x_642_, v_nano_634_);
lean_dec(v_nano_634_);
lean_dec(v___x_642_);
v___x_644_ = lean_int_mul(v_second_639_, v___x_624_);
lean_dec(v_second_639_);
v___x_645_ = lean_int_add(v___x_644_, v_nano_640_);
lean_dec(v_nano_640_);
lean_dec(v___x_644_);
v___x_646_ = lean_int_add(v___x_643_, v___x_645_);
lean_dec(v___x_645_);
lean_dec(v___x_643_);
v___x_647_ = l_Std_Time_Duration_ofNanoseconds(v___x_646_);
lean_dec(v___x_646_);
v_tm_648_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_647_);
v___x_649_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_648_);
v___x_650_ = lean_mk_thunk(v___f_641_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v___x_650_);
lean_ctor_set(v___x_612_, 0, v___x_649_);
v___x_652_ = v___x_612_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object* v_tz_656_, lean_object* v_dt_657_, lean_object* v_milliseconds_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Time_DateTime_subMilliseconds(v_tz_656_, v_dt_657_, v_milliseconds_658_);
lean_dec(v_milliseconds_658_);
lean_dec_ref(v_tz_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object* v_tz_660_, lean_object* v_dt_661_, lean_object* v_nanoseconds_662_){
_start:
{
lean_object* v_date_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_704_; 
v_date_663_ = lean_ctor_get(v_dt_661_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_dt_661_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_dt_661_, 0);
lean_dec(v_unused_705_);
v___x_665_ = v_dt_661_;
v_isShared_666_ = v_isSharedCheck_704_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_date_663_);
lean_dec(v_dt_661_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_704_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_second_669_; lean_object* v_nano_670_; lean_object* v___x_671_; lean_object* v_second_672_; lean_object* v_nano_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v_second_683_; lean_object* v_nano_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v_second_689_; lean_object* v_nano_690_; lean_object* v___f_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_tm_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_667_ = lean_thunk_get_own(v_date_663_);
lean_dec_ref(v_date_663_);
v___x_668_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_667_);
v_second_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_second_669_);
v_nano_670_ = lean_ctor_get(v___x_668_, 1);
lean_inc(v_nano_670_);
lean_dec_ref(v___x_668_);
v___x_671_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_662_);
v_second_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_second_672_);
v_nano_673_ = lean_ctor_get(v___x_671_, 1);
lean_inc(v_nano_673_);
lean_dec_ref(v___x_671_);
v___x_674_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_675_ = lean_int_mul(v_second_669_, v___x_674_);
lean_dec(v_second_669_);
v___x_676_ = lean_int_add(v___x_675_, v_nano_670_);
lean_dec(v_nano_670_);
lean_dec(v___x_675_);
v___x_677_ = lean_int_mul(v_second_672_, v___x_674_);
lean_dec(v_second_672_);
v___x_678_ = lean_int_add(v___x_677_, v_nano_673_);
lean_dec(v_nano_673_);
lean_dec(v___x_677_);
v___x_679_ = lean_int_add(v___x_676_, v___x_678_);
lean_dec(v___x_678_);
lean_dec(v___x_676_);
v___x_680_ = l_Std_Time_Duration_ofNanoseconds(v___x_679_);
lean_dec(v___x_679_);
v___x_681_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_680_);
lean_inc_ref(v___x_681_);
v___x_682_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_681_);
v_second_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_second_683_);
v_nano_684_ = lean_ctor_get(v___x_682_, 1);
lean_inc(v_nano_684_);
lean_dec_ref(v___x_682_);
v___x_685_ = l_Std_Time_TimeZone_toSeconds(v_tz_660_);
v___x_686_ = lean_int_neg(v___x_685_);
lean_dec(v___x_685_);
v___x_687_ = lean_int_mul(v___x_686_, v___x_674_);
lean_dec(v___x_686_);
v___x_688_ = l_Std_Time_Duration_ofNanoseconds(v___x_687_);
lean_dec(v___x_687_);
v_second_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_second_689_);
v_nano_690_ = lean_ctor_get(v___x_688_, 1);
lean_inc(v_nano_690_);
lean_dec_ref(v___x_688_);
v___f_691_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_691_, 0, v___x_681_);
v___x_692_ = lean_int_mul(v_second_683_, v___x_674_);
lean_dec(v_second_683_);
v___x_693_ = lean_int_add(v___x_692_, v_nano_684_);
lean_dec(v_nano_684_);
lean_dec(v___x_692_);
v___x_694_ = lean_int_mul(v_second_689_, v___x_674_);
lean_dec(v_second_689_);
v___x_695_ = lean_int_add(v___x_694_, v_nano_690_);
lean_dec(v_nano_690_);
lean_dec(v___x_694_);
v___x_696_ = lean_int_add(v___x_693_, v___x_695_);
lean_dec(v___x_695_);
lean_dec(v___x_693_);
v___x_697_ = l_Std_Time_Duration_ofNanoseconds(v___x_696_);
lean_dec(v___x_696_);
v_tm_698_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_697_);
v___x_699_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_698_);
v___x_700_ = lean_mk_thunk(v___f_691_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 1, v___x_700_);
lean_ctor_set(v___x_665_, 0, v___x_699_);
v___x_702_ = v___x_665_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object* v_tz_706_, lean_object* v_dt_707_, lean_object* v_nanoseconds_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Std_Time_DateTime_addNanoseconds(v_tz_706_, v_dt_707_, v_nanoseconds_708_);
lean_dec(v_nanoseconds_708_);
lean_dec_ref(v_tz_706_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object* v_tz_710_, lean_object* v_dt_711_, lean_object* v_nanoseconds_712_){
_start:
{
lean_object* v_date_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_755_; 
v_date_713_ = lean_ctor_get(v_dt_711_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_dt_711_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_dt_711_, 0);
lean_dec(v_unused_756_);
v___x_715_ = v_dt_711_;
v_isShared_716_ = v_isSharedCheck_755_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_date_713_);
lean_dec(v_dt_711_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_755_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_second_719_; lean_object* v_nano_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_second_723_; lean_object* v_nano_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v_second_734_; lean_object* v_nano_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_second_740_; lean_object* v_nano_741_; lean_object* v___f_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_tm_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_717_ = lean_thunk_get_own(v_date_713_);
lean_dec_ref(v_date_713_);
v___x_718_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_717_);
v_second_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_second_719_);
v_nano_720_ = lean_ctor_get(v___x_718_, 1);
lean_inc(v_nano_720_);
lean_dec_ref(v___x_718_);
v___x_721_ = lean_int_neg(v_nanoseconds_712_);
v___x_722_ = l_Std_Time_Duration_ofNanoseconds(v___x_721_);
lean_dec(v___x_721_);
v_second_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_second_723_);
v_nano_724_ = lean_ctor_get(v___x_722_, 1);
lean_inc(v_nano_724_);
lean_dec_ref(v___x_722_);
v___x_725_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_726_ = lean_int_mul(v_second_719_, v___x_725_);
lean_dec(v_second_719_);
v___x_727_ = lean_int_add(v___x_726_, v_nano_720_);
lean_dec(v_nano_720_);
lean_dec(v___x_726_);
v___x_728_ = lean_int_mul(v_second_723_, v___x_725_);
lean_dec(v_second_723_);
v___x_729_ = lean_int_add(v___x_728_, v_nano_724_);
lean_dec(v_nano_724_);
lean_dec(v___x_728_);
v___x_730_ = lean_int_add(v___x_727_, v___x_729_);
lean_dec(v___x_729_);
lean_dec(v___x_727_);
v___x_731_ = l_Std_Time_Duration_ofNanoseconds(v___x_730_);
lean_dec(v___x_730_);
v___x_732_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_731_);
lean_inc_ref(v___x_732_);
v___x_733_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_732_);
v_second_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_second_734_);
v_nano_735_ = lean_ctor_get(v___x_733_, 1);
lean_inc(v_nano_735_);
lean_dec_ref(v___x_733_);
v___x_736_ = l_Std_Time_TimeZone_toSeconds(v_tz_710_);
v___x_737_ = lean_int_neg(v___x_736_);
lean_dec(v___x_736_);
v___x_738_ = lean_int_mul(v___x_737_, v___x_725_);
lean_dec(v___x_737_);
v___x_739_ = l_Std_Time_Duration_ofNanoseconds(v___x_738_);
lean_dec(v___x_738_);
v_second_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_second_740_);
v_nano_741_ = lean_ctor_get(v___x_739_, 1);
lean_inc(v_nano_741_);
lean_dec_ref(v___x_739_);
v___f_742_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_742_, 0, v___x_732_);
v___x_743_ = lean_int_mul(v_second_734_, v___x_725_);
lean_dec(v_second_734_);
v___x_744_ = lean_int_add(v___x_743_, v_nano_735_);
lean_dec(v_nano_735_);
lean_dec(v___x_743_);
v___x_745_ = lean_int_mul(v_second_740_, v___x_725_);
lean_dec(v_second_740_);
v___x_746_ = lean_int_add(v___x_745_, v_nano_741_);
lean_dec(v_nano_741_);
lean_dec(v___x_745_);
v___x_747_ = lean_int_add(v___x_744_, v___x_746_);
lean_dec(v___x_746_);
lean_dec(v___x_744_);
v___x_748_ = l_Std_Time_Duration_ofNanoseconds(v___x_747_);
lean_dec(v___x_747_);
v_tm_749_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_748_);
v___x_750_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_749_);
v___x_751_ = lean_mk_thunk(v___f_742_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v___x_751_);
lean_ctor_set(v___x_715_, 0, v___x_750_);
v___x_753_ = v___x_715_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object* v_tz_757_, lean_object* v_dt_758_, lean_object* v_nanoseconds_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_Time_DateTime_subNanoseconds(v_tz_757_, v_dt_758_, v_nanoseconds_759_);
lean_dec(v_nanoseconds_759_);
lean_dec_ref(v_tz_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object* v_tz_761_, lean_object* v_dt_762_, lean_object* v_days_763_){
_start:
{
lean_object* v_date_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_804_; 
v_date_764_ = lean_ctor_get(v_dt_762_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_dt_762_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v_dt_762_, 0);
lean_dec(v_unused_805_);
v___x_766_ = v_dt_762_;
v_isShared_767_ = v_isSharedCheck_804_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_date_764_);
lean_dec(v_dt_762_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_804_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v_date_769_; lean_object* v_time_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_803_; 
v___x_768_ = lean_thunk_get_own(v_date_764_);
lean_dec_ref(v_date_764_);
v_date_769_ = lean_ctor_get(v___x_768_, 0);
v_time_770_ = lean_ctor_get(v___x_768_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_803_ == 0)
{
v___x_772_ = v___x_768_;
v_isShared_773_ = v_isSharedCheck_803_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_time_770_);
lean_inc(v_date_769_);
lean_dec(v___x_768_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_803_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_dateDays_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
v_dateDays_774_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_769_);
v___x_775_ = lean_int_add(v_dateDays_774_, v_days_763_);
lean_dec(v_dateDays_774_);
v___x_776_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_775_);
lean_dec(v___x_775_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_776_);
v___x_778_ = v___x_772_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_time_770_);
v___x_778_ = v_reuseFailAlloc_802_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v_second_780_; lean_object* v_nano_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_second_787_; lean_object* v_nano_788_; lean_object* v___f_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_tm_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_inc_ref(v___x_778_);
v___x_779_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_778_);
v_second_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_second_780_);
v_nano_781_ = lean_ctor_get(v___x_779_, 1);
lean_inc(v_nano_781_);
lean_dec_ref(v___x_779_);
v___x_782_ = l_Std_Time_TimeZone_toSeconds(v_tz_761_);
v___x_783_ = lean_int_neg(v___x_782_);
lean_dec(v___x_782_);
v___x_784_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_785_ = lean_int_mul(v___x_783_, v___x_784_);
lean_dec(v___x_783_);
v___x_786_ = l_Std_Time_Duration_ofNanoseconds(v___x_785_);
lean_dec(v___x_785_);
v_second_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_second_787_);
v_nano_788_ = lean_ctor_get(v___x_786_, 1);
lean_inc(v_nano_788_);
lean_dec_ref(v___x_786_);
v___f_789_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_789_, 0, v___x_778_);
v___x_790_ = lean_int_mul(v_second_780_, v___x_784_);
lean_dec(v_second_780_);
v___x_791_ = lean_int_add(v___x_790_, v_nano_781_);
lean_dec(v_nano_781_);
lean_dec(v___x_790_);
v___x_792_ = lean_int_mul(v_second_787_, v___x_784_);
lean_dec(v_second_787_);
v___x_793_ = lean_int_add(v___x_792_, v_nano_788_);
lean_dec(v_nano_788_);
lean_dec(v___x_792_);
v___x_794_ = lean_int_add(v___x_791_, v___x_793_);
lean_dec(v___x_793_);
lean_dec(v___x_791_);
v___x_795_ = l_Std_Time_Duration_ofNanoseconds(v___x_794_);
lean_dec(v___x_794_);
v_tm_796_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_795_);
v___x_797_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_796_);
v___x_798_ = lean_mk_thunk(v___f_789_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v___x_798_);
lean_ctor_set(v___x_766_, 0, v___x_797_);
v___x_800_ = v___x_766_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object* v_tz_806_, lean_object* v_dt_807_, lean_object* v_days_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Std_Time_DateTime_addDays(v_tz_806_, v_dt_807_, v_days_808_);
lean_dec(v_days_808_);
lean_dec_ref(v_tz_806_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object* v_tz_810_, lean_object* v_dt_811_, lean_object* v_days_812_){
_start:
{
lean_object* v_date_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_854_; 
v_date_813_ = lean_ctor_get(v_dt_811_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v_dt_811_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v_dt_811_, 0);
lean_dec(v_unused_855_);
v___x_815_ = v_dt_811_;
v_isShared_816_ = v_isSharedCheck_854_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_date_813_);
lean_dec(v_dt_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_854_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v_date_818_; lean_object* v_time_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_853_; 
v___x_817_ = lean_thunk_get_own(v_date_813_);
lean_dec_ref(v_date_813_);
v_date_818_ = lean_ctor_get(v___x_817_, 0);
v_time_819_ = lean_ctor_get(v___x_817_, 1);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_853_ == 0)
{
v___x_821_ = v___x_817_;
v_isShared_822_ = v_isSharedCheck_853_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_time_819_);
lean_inc(v_date_818_);
lean_dec(v___x_817_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_853_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v_dateDays_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_823_ = lean_int_neg(v_days_812_);
v_dateDays_824_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_818_);
v___x_825_ = lean_int_add(v_dateDays_824_, v___x_823_);
lean_dec(v___x_823_);
lean_dec(v_dateDays_824_);
v___x_826_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_825_);
lean_dec(v___x_825_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_826_);
v___x_828_ = v___x_821_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_time_819_);
v___x_828_ = v_reuseFailAlloc_852_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v_second_830_; lean_object* v_nano_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v_second_837_; lean_object* v_nano_838_; lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_tm_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_850_; 
lean_inc_ref(v___x_828_);
v___x_829_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_828_);
v_second_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_second_830_);
v_nano_831_ = lean_ctor_get(v___x_829_, 1);
lean_inc(v_nano_831_);
lean_dec_ref(v___x_829_);
v___x_832_ = l_Std_Time_TimeZone_toSeconds(v_tz_810_);
v___x_833_ = lean_int_neg(v___x_832_);
lean_dec(v___x_832_);
v___x_834_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_835_ = lean_int_mul(v___x_833_, v___x_834_);
lean_dec(v___x_833_);
v___x_836_ = l_Std_Time_Duration_ofNanoseconds(v___x_835_);
lean_dec(v___x_835_);
v_second_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_second_837_);
v_nano_838_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_nano_838_);
lean_dec_ref(v___x_836_);
v___f_839_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_839_, 0, v___x_828_);
v___x_840_ = lean_int_mul(v_second_830_, v___x_834_);
lean_dec(v_second_830_);
v___x_841_ = lean_int_add(v___x_840_, v_nano_831_);
lean_dec(v_nano_831_);
lean_dec(v___x_840_);
v___x_842_ = lean_int_mul(v_second_837_, v___x_834_);
lean_dec(v_second_837_);
v___x_843_ = lean_int_add(v___x_842_, v_nano_838_);
lean_dec(v_nano_838_);
lean_dec(v___x_842_);
v___x_844_ = lean_int_add(v___x_841_, v___x_843_);
lean_dec(v___x_843_);
lean_dec(v___x_841_);
v___x_845_ = l_Std_Time_Duration_ofNanoseconds(v___x_844_);
lean_dec(v___x_844_);
v_tm_846_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_845_);
v___x_847_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_846_);
v___x_848_ = lean_mk_thunk(v___f_839_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v___x_848_);
lean_ctor_set(v___x_815_, 0, v___x_847_);
v___x_850_ = v___x_815_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object* v_tz_856_, lean_object* v_dt_857_, lean_object* v_days_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Std_Time_DateTime_subDays(v_tz_856_, v_dt_857_, v_days_858_);
lean_dec(v_days_858_);
lean_dec_ref(v_tz_856_);
return v_res_859_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(7u);
v___x_861_ = lean_nat_to_int(v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object* v_tz_862_, lean_object* v_dt_863_, lean_object* v_weeks_864_){
_start:
{
lean_object* v_date_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_907_; 
v_date_865_ = lean_ctor_get(v_dt_863_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_dt_863_);
if (v_isSharedCheck_907_ == 0)
{
lean_object* v_unused_908_; 
v_unused_908_ = lean_ctor_get(v_dt_863_, 0);
lean_dec(v_unused_908_);
v___x_867_ = v_dt_863_;
v_isShared_868_ = v_isSharedCheck_907_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_date_865_);
lean_dec(v_dt_863_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_907_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v_date_870_; lean_object* v_time_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_906_; 
v___x_869_ = lean_thunk_get_own(v_date_865_);
lean_dec_ref(v_date_865_);
v_date_870_ = lean_ctor_get(v___x_869_, 0);
v_time_871_ = lean_ctor_get(v___x_869_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_906_ == 0)
{
v___x_873_ = v___x_869_;
v_isShared_874_ = v_isSharedCheck_906_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_time_871_);
lean_inc(v_date_870_);
lean_dec(v___x_869_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_906_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_dateDays_875_; lean_object* v___x_876_; lean_object* v_daysToAdd_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v_dateDays_875_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_870_);
v___x_876_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v_daysToAdd_877_ = lean_int_mul(v_weeks_864_, v___x_876_);
v___x_878_ = lean_int_add(v_dateDays_875_, v_daysToAdd_877_);
lean_dec(v_daysToAdd_877_);
lean_dec(v_dateDays_875_);
v___x_879_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_878_);
lean_dec(v___x_878_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_879_);
v___x_881_ = v___x_873_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_time_871_);
v___x_881_ = v_reuseFailAlloc_905_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; lean_object* v_second_883_; lean_object* v_nano_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_second_890_; lean_object* v_nano_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_tm_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
lean_inc_ref(v___x_881_);
v___x_882_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_881_);
v_second_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_second_883_);
v_nano_884_ = lean_ctor_get(v___x_882_, 1);
lean_inc(v_nano_884_);
lean_dec_ref(v___x_882_);
v___x_885_ = l_Std_Time_TimeZone_toSeconds(v_tz_862_);
v___x_886_ = lean_int_neg(v___x_885_);
lean_dec(v___x_885_);
v___x_887_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_888_ = lean_int_mul(v___x_886_, v___x_887_);
lean_dec(v___x_886_);
v___x_889_ = l_Std_Time_Duration_ofNanoseconds(v___x_888_);
lean_dec(v___x_888_);
v_second_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_second_890_);
v_nano_891_ = lean_ctor_get(v___x_889_, 1);
lean_inc(v_nano_891_);
lean_dec_ref(v___x_889_);
v___f_892_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_892_, 0, v___x_881_);
v___x_893_ = lean_int_mul(v_second_883_, v___x_887_);
lean_dec(v_second_883_);
v___x_894_ = lean_int_add(v___x_893_, v_nano_884_);
lean_dec(v_nano_884_);
lean_dec(v___x_893_);
v___x_895_ = lean_int_mul(v_second_890_, v___x_887_);
lean_dec(v_second_890_);
v___x_896_ = lean_int_add(v___x_895_, v_nano_891_);
lean_dec(v_nano_891_);
lean_dec(v___x_895_);
v___x_897_ = lean_int_add(v___x_894_, v___x_896_);
lean_dec(v___x_896_);
lean_dec(v___x_894_);
v___x_898_ = l_Std_Time_Duration_ofNanoseconds(v___x_897_);
lean_dec(v___x_897_);
v_tm_899_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_898_);
v___x_900_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_899_);
v___x_901_ = lean_mk_thunk(v___f_892_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 1, v___x_901_);
lean_ctor_set(v___x_867_, 0, v___x_900_);
v___x_903_ = v___x_867_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_900_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object* v_tz_909_, lean_object* v_dt_910_, lean_object* v_weeks_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Std_Time_DateTime_addWeeks(v_tz_909_, v_dt_910_, v_weeks_911_);
lean_dec(v_weeks_911_);
lean_dec_ref(v_tz_909_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object* v_tz_913_, lean_object* v_dt_914_, lean_object* v_weeks_915_){
_start:
{
lean_object* v_date_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_959_; 
v_date_916_ = lean_ctor_get(v_dt_914_, 1);
v_isSharedCheck_959_ = !lean_is_exclusive(v_dt_914_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v_dt_914_, 0);
lean_dec(v_unused_960_);
v___x_918_ = v_dt_914_;
v_isShared_919_ = v_isSharedCheck_959_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_date_916_);
lean_dec(v_dt_914_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_959_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v_date_921_; lean_object* v_time_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_958_; 
v___x_920_ = lean_thunk_get_own(v_date_916_);
lean_dec_ref(v_date_916_);
v_date_921_ = lean_ctor_get(v___x_920_, 0);
v_time_922_ = lean_ctor_get(v___x_920_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_958_ == 0)
{
v___x_924_ = v___x_920_;
v_isShared_925_ = v_isSharedCheck_958_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_time_922_);
lean_inc(v_date_921_);
lean_dec(v___x_920_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_958_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v_dateDays_927_; lean_object* v___x_928_; lean_object* v_daysToAdd_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_926_ = lean_int_neg(v_weeks_915_);
v_dateDays_927_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_921_);
v___x_928_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v_daysToAdd_929_ = lean_int_mul(v___x_926_, v___x_928_);
lean_dec(v___x_926_);
v___x_930_ = lean_int_add(v_dateDays_927_, v_daysToAdd_929_);
lean_dec(v_daysToAdd_929_);
lean_dec(v_dateDays_927_);
v___x_931_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_930_);
lean_dec(v___x_930_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v___x_931_);
v___x_933_ = v___x_924_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_time_922_);
v___x_933_ = v_reuseFailAlloc_957_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v_second_935_; lean_object* v_nano_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v_second_942_; lean_object* v_nano_943_; lean_object* v___f_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_tm_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
lean_inc_ref(v___x_933_);
v___x_934_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_933_);
v_second_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_second_935_);
v_nano_936_ = lean_ctor_get(v___x_934_, 1);
lean_inc(v_nano_936_);
lean_dec_ref(v___x_934_);
v___x_937_ = l_Std_Time_TimeZone_toSeconds(v_tz_913_);
v___x_938_ = lean_int_neg(v___x_937_);
lean_dec(v___x_937_);
v___x_939_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_940_ = lean_int_mul(v___x_938_, v___x_939_);
lean_dec(v___x_938_);
v___x_941_ = l_Std_Time_Duration_ofNanoseconds(v___x_940_);
lean_dec(v___x_940_);
v_second_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_second_942_);
v_nano_943_ = lean_ctor_get(v___x_941_, 1);
lean_inc(v_nano_943_);
lean_dec_ref(v___x_941_);
v___f_944_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_944_, 0, v___x_933_);
v___x_945_ = lean_int_mul(v_second_935_, v___x_939_);
lean_dec(v_second_935_);
v___x_946_ = lean_int_add(v___x_945_, v_nano_936_);
lean_dec(v_nano_936_);
lean_dec(v___x_945_);
v___x_947_ = lean_int_mul(v_second_942_, v___x_939_);
lean_dec(v_second_942_);
v___x_948_ = lean_int_add(v___x_947_, v_nano_943_);
lean_dec(v_nano_943_);
lean_dec(v___x_947_);
v___x_949_ = lean_int_add(v___x_946_, v___x_948_);
lean_dec(v___x_948_);
lean_dec(v___x_946_);
v___x_950_ = l_Std_Time_Duration_ofNanoseconds(v___x_949_);
lean_dec(v___x_949_);
v_tm_951_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_950_);
v___x_952_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_951_);
v___x_953_ = lean_mk_thunk(v___f_944_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 1, v___x_953_);
lean_ctor_set(v___x_918_, 0, v___x_952_);
v___x_955_ = v___x_918_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object* v_tz_961_, lean_object* v_dt_962_, lean_object* v_weeks_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Std_Time_DateTime_subWeeks(v_tz_961_, v_dt_962_, v_weeks_963_);
lean_dec(v_weeks_963_);
lean_dec_ref(v_tz_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object* v_tz_965_, lean_object* v_dt_966_, lean_object* v_months_967_){
_start:
{
lean_object* v_date_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_997_; 
v_date_968_ = lean_ctor_get(v_dt_966_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_dt_966_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_dt_966_, 0);
lean_dec(v_unused_998_);
v___x_970_ = v_dt_966_;
v_isShared_971_ = v_isSharedCheck_997_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_date_968_);
lean_dec(v_dt_966_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_997_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_second_975_; lean_object* v_nano_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v_second_982_; lean_object* v_nano_983_; lean_object* v___f_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_tm_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_972_ = lean_thunk_get_own(v_date_968_);
lean_dec_ref(v_date_968_);
v___x_973_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_972_, v_months_967_);
lean_inc_ref(v___x_973_);
v___x_974_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_973_);
v_second_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_second_975_);
v_nano_976_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_nano_976_);
lean_dec_ref(v___x_974_);
v___x_977_ = l_Std_Time_TimeZone_toSeconds(v_tz_965_);
v___x_978_ = lean_int_neg(v___x_977_);
lean_dec(v___x_977_);
v___x_979_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_980_ = lean_int_mul(v___x_978_, v___x_979_);
lean_dec(v___x_978_);
v___x_981_ = l_Std_Time_Duration_ofNanoseconds(v___x_980_);
lean_dec(v___x_980_);
v_second_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_second_982_);
v_nano_983_ = lean_ctor_get(v___x_981_, 1);
lean_inc(v_nano_983_);
lean_dec_ref(v___x_981_);
v___f_984_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_984_, 0, v___x_973_);
v___x_985_ = lean_int_mul(v_second_975_, v___x_979_);
lean_dec(v_second_975_);
v___x_986_ = lean_int_add(v___x_985_, v_nano_976_);
lean_dec(v_nano_976_);
lean_dec(v___x_985_);
v___x_987_ = lean_int_mul(v_second_982_, v___x_979_);
lean_dec(v_second_982_);
v___x_988_ = lean_int_add(v___x_987_, v_nano_983_);
lean_dec(v_nano_983_);
lean_dec(v___x_987_);
v___x_989_ = lean_int_add(v___x_986_, v___x_988_);
lean_dec(v___x_988_);
lean_dec(v___x_986_);
v___x_990_ = l_Std_Time_Duration_ofNanoseconds(v___x_989_);
lean_dec(v___x_989_);
v_tm_991_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_990_);
v___x_992_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_991_);
v___x_993_ = lean_mk_thunk(v___f_984_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 1, v___x_993_);
lean_ctor_set(v___x_970_, 0, v___x_992_);
v___x_995_ = v___x_970_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object* v_tz_999_, lean_object* v_dt_1000_, lean_object* v_months_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_Time_DateTime_addMonthsClip(v_tz_999_, v_dt_1000_, v_months_1001_);
lean_dec(v_months_1001_);
lean_dec_ref(v_tz_999_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object* v_tz_1003_, lean_object* v_dt_1004_, lean_object* v_months_1005_){
_start:
{
lean_object* v_date_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1045_; 
v_date_1006_ = lean_ctor_get(v_dt_1004_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_dt_1004_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v_dt_1004_, 0);
lean_dec(v_unused_1046_);
v___x_1008_ = v_dt_1004_;
v_isShared_1009_ = v_isSharedCheck_1045_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_date_1006_);
lean_dec(v_dt_1004_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1045_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v_date_1011_; lean_object* v_time_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1044_; 
v___x_1010_ = lean_thunk_get_own(v_date_1006_);
lean_dec_ref(v_date_1006_);
v_date_1011_ = lean_ctor_get(v___x_1010_, 0);
v_time_1012_ = lean_ctor_get(v___x_1010_, 1);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1014_ = v___x_1010_;
v_isShared_1015_ = v_isSharedCheck_1044_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_time_1012_);
lean_inc(v_date_1011_);
lean_dec(v___x_1010_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1044_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1016_ = lean_int_neg(v_months_1005_);
v___x_1017_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1011_, v___x_1016_);
lean_dec(v___x_1016_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1017_);
v___x_1019_ = v___x_1014_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1017_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_time_1012_);
v___x_1019_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1020_; lean_object* v_second_1021_; lean_object* v_nano_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v_second_1028_; lean_object* v_nano_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_tm_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_inc_ref(v___x_1019_);
v___x_1020_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1019_);
v_second_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_second_1021_);
v_nano_1022_ = lean_ctor_get(v___x_1020_, 1);
lean_inc(v_nano_1022_);
lean_dec_ref(v___x_1020_);
v___x_1023_ = l_Std_Time_TimeZone_toSeconds(v_tz_1003_);
v___x_1024_ = lean_int_neg(v___x_1023_);
lean_dec(v___x_1023_);
v___x_1025_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1026_ = lean_int_mul(v___x_1024_, v___x_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = l_Std_Time_Duration_ofNanoseconds(v___x_1026_);
lean_dec(v___x_1026_);
v_second_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_second_1028_);
v_nano_1029_ = lean_ctor_get(v___x_1027_, 1);
lean_inc(v_nano_1029_);
lean_dec_ref(v___x_1027_);
v___f_1030_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1030_, 0, v___x_1019_);
v___x_1031_ = lean_int_mul(v_second_1021_, v___x_1025_);
lean_dec(v_second_1021_);
v___x_1032_ = lean_int_add(v___x_1031_, v_nano_1022_);
lean_dec(v_nano_1022_);
lean_dec(v___x_1031_);
v___x_1033_ = lean_int_mul(v_second_1028_, v___x_1025_);
lean_dec(v_second_1028_);
v___x_1034_ = lean_int_add(v___x_1033_, v_nano_1029_);
lean_dec(v_nano_1029_);
lean_dec(v___x_1033_);
v___x_1035_ = lean_int_add(v___x_1032_, v___x_1034_);
lean_dec(v___x_1034_);
lean_dec(v___x_1032_);
v___x_1036_ = l_Std_Time_Duration_ofNanoseconds(v___x_1035_);
lean_dec(v___x_1035_);
v_tm_1037_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1036_);
v___x_1038_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1037_);
v___x_1039_ = lean_mk_thunk(v___f_1030_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 1, v___x_1039_);
lean_ctor_set(v___x_1008_, 0, v___x_1038_);
v___x_1041_ = v___x_1008_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object* v_tz_1047_, lean_object* v_dt_1048_, lean_object* v_months_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Std_Time_DateTime_subMonthsClip(v_tz_1047_, v_dt_1048_, v_months_1049_);
lean_dec(v_months_1049_);
lean_dec_ref(v_tz_1047_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object* v_tz_1051_, lean_object* v_dt_1052_, lean_object* v_months_1053_){
_start:
{
lean_object* v_date_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1083_; 
v_date_1054_ = lean_ctor_get(v_dt_1052_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_dt_1052_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_dt_1052_, 0);
lean_dec(v_unused_1084_);
v___x_1056_ = v_dt_1052_;
v_isShared_1057_ = v_isSharedCheck_1083_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_date_1054_);
lean_dec(v_dt_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1083_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_second_1061_; lean_object* v_nano_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_second_1068_; lean_object* v_nano_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v_tm_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1058_ = lean_thunk_get_own(v_date_1054_);
lean_dec_ref(v_date_1054_);
v___x_1059_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_1058_, v_months_1053_);
lean_inc_ref(v___x_1059_);
v___x_1060_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1059_);
v_second_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_second_1061_);
v_nano_1062_ = lean_ctor_get(v___x_1060_, 1);
lean_inc(v_nano_1062_);
lean_dec_ref(v___x_1060_);
v___x_1063_ = l_Std_Time_TimeZone_toSeconds(v_tz_1051_);
v___x_1064_ = lean_int_neg(v___x_1063_);
lean_dec(v___x_1063_);
v___x_1065_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1066_ = lean_int_mul(v___x_1064_, v___x_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = l_Std_Time_Duration_ofNanoseconds(v___x_1066_);
lean_dec(v___x_1066_);
v_second_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_second_1068_);
v_nano_1069_ = lean_ctor_get(v___x_1067_, 1);
lean_inc(v_nano_1069_);
lean_dec_ref(v___x_1067_);
v___f_1070_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1070_, 0, v___x_1059_);
v___x_1071_ = lean_int_mul(v_second_1061_, v___x_1065_);
lean_dec(v_second_1061_);
v___x_1072_ = lean_int_add(v___x_1071_, v_nano_1062_);
lean_dec(v_nano_1062_);
lean_dec(v___x_1071_);
v___x_1073_ = lean_int_mul(v_second_1068_, v___x_1065_);
lean_dec(v_second_1068_);
v___x_1074_ = lean_int_add(v___x_1073_, v_nano_1069_);
lean_dec(v_nano_1069_);
lean_dec(v___x_1073_);
v___x_1075_ = lean_int_add(v___x_1072_, v___x_1074_);
lean_dec(v___x_1074_);
lean_dec(v___x_1072_);
v___x_1076_ = l_Std_Time_Duration_ofNanoseconds(v___x_1075_);
lean_dec(v___x_1075_);
v_tm_1077_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1076_);
v___x_1078_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1077_);
v___x_1079_ = lean_mk_thunk(v___f_1070_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1079_);
lean_ctor_set(v___x_1056_, 0, v___x_1078_);
v___x_1081_ = v___x_1056_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object* v_tz_1085_, lean_object* v_dt_1086_, lean_object* v_months_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Std_Time_DateTime_addMonthsRollOver(v_tz_1085_, v_dt_1086_, v_months_1087_);
lean_dec(v_months_1087_);
lean_dec_ref(v_tz_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object* v_tz_1089_, lean_object* v_dt_1090_, lean_object* v_months_1091_){
_start:
{
lean_object* v_date_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1131_; 
v_date_1092_ = lean_ctor_get(v_dt_1090_, 1);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_dt_1090_);
if (v_isSharedCheck_1131_ == 0)
{
lean_object* v_unused_1132_; 
v_unused_1132_ = lean_ctor_get(v_dt_1090_, 0);
lean_dec(v_unused_1132_);
v___x_1094_ = v_dt_1090_;
v_isShared_1095_ = v_isSharedCheck_1131_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_date_1092_);
lean_dec(v_dt_1090_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1131_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v_date_1097_; lean_object* v_time_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1130_; 
v___x_1096_ = lean_thunk_get_own(v_date_1092_);
lean_dec_ref(v_date_1092_);
v_date_1097_ = lean_ctor_get(v___x_1096_, 0);
v_time_1098_ = lean_ctor_get(v___x_1096_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1100_ = v___x_1096_;
v_isShared_1101_ = v_isSharedCheck_1130_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_time_1098_);
lean_inc(v_date_1097_);
lean_dec(v___x_1096_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1130_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1102_ = lean_int_neg(v_months_1091_);
v___x_1103_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1097_, v___x_1102_);
lean_dec(v___x_1102_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1103_);
v___x_1105_ = v___x_1100_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_time_1098_);
v___x_1105_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v_second_1107_; lean_object* v_nano_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_second_1114_; lean_object* v_nano_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_tm_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_inc_ref(v___x_1105_);
v___x_1106_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1105_);
v_second_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_second_1107_);
v_nano_1108_ = lean_ctor_get(v___x_1106_, 1);
lean_inc(v_nano_1108_);
lean_dec_ref(v___x_1106_);
v___x_1109_ = l_Std_Time_TimeZone_toSeconds(v_tz_1089_);
v___x_1110_ = lean_int_neg(v___x_1109_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1112_ = lean_int_mul(v___x_1110_, v___x_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = l_Std_Time_Duration_ofNanoseconds(v___x_1112_);
lean_dec(v___x_1112_);
v_second_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_second_1114_);
v_nano_1115_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_nano_1115_);
lean_dec_ref(v___x_1113_);
v___f_1116_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1116_, 0, v___x_1105_);
v___x_1117_ = lean_int_mul(v_second_1107_, v___x_1111_);
lean_dec(v_second_1107_);
v___x_1118_ = lean_int_add(v___x_1117_, v_nano_1108_);
lean_dec(v_nano_1108_);
lean_dec(v___x_1117_);
v___x_1119_ = lean_int_mul(v_second_1114_, v___x_1111_);
lean_dec(v_second_1114_);
v___x_1120_ = lean_int_add(v___x_1119_, v_nano_1115_);
lean_dec(v_nano_1115_);
lean_dec(v___x_1119_);
v___x_1121_ = lean_int_add(v___x_1118_, v___x_1120_);
lean_dec(v___x_1120_);
lean_dec(v___x_1118_);
v___x_1122_ = l_Std_Time_Duration_ofNanoseconds(v___x_1121_);
lean_dec(v___x_1121_);
v_tm_1123_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1122_);
v___x_1124_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1123_);
v___x_1125_ = lean_mk_thunk(v___f_1116_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 1, v___x_1125_);
lean_ctor_set(v___x_1094_, 0, v___x_1124_);
v___x_1127_ = v___x_1094_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object* v_tz_1133_, lean_object* v_dt_1134_, lean_object* v_months_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Std_Time_DateTime_subMonthsRollOver(v_tz_1133_, v_dt_1134_, v_months_1135_);
lean_dec(v_months_1135_);
lean_dec_ref(v_tz_1133_);
return v_res_1136_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = lean_unsigned_to_nat(12u);
v___x_1138_ = lean_nat_to_int(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object* v_tz_1139_, lean_object* v_dt_1140_, lean_object* v_years_1141_){
_start:
{
lean_object* v_date_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1182_; 
v_date_1142_ = lean_ctor_get(v_dt_1140_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_dt_1140_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v_dt_1140_, 0);
lean_dec(v_unused_1183_);
v___x_1144_ = v_dt_1140_;
v_isShared_1145_ = v_isSharedCheck_1182_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_date_1142_);
lean_dec(v_dt_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1182_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v_date_1147_; lean_object* v_time_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1181_; 
v___x_1146_ = lean_thunk_get_own(v_date_1142_);
lean_dec_ref(v_date_1142_);
v_date_1147_ = lean_ctor_get(v___x_1146_, 0);
v_time_1148_ = lean_ctor_get(v___x_1146_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1150_ = v___x_1146_;
v_isShared_1151_ = v_isSharedCheck_1181_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_time_1148_);
lean_inc(v_date_1147_);
lean_dec(v___x_1146_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1181_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1152_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_1153_ = lean_int_mul(v_years_1141_, v___x_1152_);
v___x_1154_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1147_, v___x_1153_);
lean_dec(v___x_1153_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1154_);
v___x_1156_ = v___x_1150_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_time_1148_);
v___x_1156_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v_second_1158_; lean_object* v_nano_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_second_1165_; lean_object* v_nano_1166_; lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_tm_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_inc_ref(v___x_1156_);
v___x_1157_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1156_);
v_second_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_second_1158_);
v_nano_1159_ = lean_ctor_get(v___x_1157_, 1);
lean_inc(v_nano_1159_);
lean_dec_ref(v___x_1157_);
v___x_1160_ = l_Std_Time_TimeZone_toSeconds(v_tz_1139_);
v___x_1161_ = lean_int_neg(v___x_1160_);
lean_dec(v___x_1160_);
v___x_1162_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1163_ = lean_int_mul(v___x_1161_, v___x_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = l_Std_Time_Duration_ofNanoseconds(v___x_1163_);
lean_dec(v___x_1163_);
v_second_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_second_1165_);
v_nano_1166_ = lean_ctor_get(v___x_1164_, 1);
lean_inc(v_nano_1166_);
lean_dec_ref(v___x_1164_);
v___f_1167_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1167_, 0, v___x_1156_);
v___x_1168_ = lean_int_mul(v_second_1158_, v___x_1162_);
lean_dec(v_second_1158_);
v___x_1169_ = lean_int_add(v___x_1168_, v_nano_1159_);
lean_dec(v_nano_1159_);
lean_dec(v___x_1168_);
v___x_1170_ = lean_int_mul(v_second_1165_, v___x_1162_);
lean_dec(v_second_1165_);
v___x_1171_ = lean_int_add(v___x_1170_, v_nano_1166_);
lean_dec(v_nano_1166_);
lean_dec(v___x_1170_);
v___x_1172_ = lean_int_add(v___x_1169_, v___x_1171_);
lean_dec(v___x_1171_);
lean_dec(v___x_1169_);
v___x_1173_ = l_Std_Time_Duration_ofNanoseconds(v___x_1172_);
lean_dec(v___x_1172_);
v_tm_1174_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1173_);
v___x_1175_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1174_);
v___x_1176_ = lean_mk_thunk(v___f_1167_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v___x_1176_);
lean_ctor_set(v___x_1144_, 0, v___x_1175_);
v___x_1178_ = v___x_1144_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object* v_tz_1184_, lean_object* v_dt_1185_, lean_object* v_years_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Std_Time_DateTime_addYearsRollOver(v_tz_1184_, v_dt_1185_, v_years_1186_);
lean_dec(v_years_1186_);
lean_dec_ref(v_tz_1184_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object* v_tz_1188_, lean_object* v_dt_1189_, lean_object* v_years_1190_){
_start:
{
lean_object* v_date_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1231_; 
v_date_1191_ = lean_ctor_get(v_dt_1189_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_dt_1189_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v_dt_1189_, 0);
lean_dec(v_unused_1232_);
v___x_1193_ = v_dt_1189_;
v_isShared_1194_ = v_isSharedCheck_1231_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_date_1191_);
lean_dec(v_dt_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1231_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v_date_1196_; lean_object* v_time_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1230_; 
v___x_1195_ = lean_thunk_get_own(v_date_1191_);
lean_dec_ref(v_date_1191_);
v_date_1196_ = lean_ctor_get(v___x_1195_, 0);
v_time_1197_ = lean_ctor_get(v___x_1195_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1199_ = v___x_1195_;
v_isShared_1200_ = v_isSharedCheck_1230_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_time_1197_);
lean_inc(v_date_1196_);
lean_dec(v___x_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1230_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1201_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_1202_ = lean_int_mul(v_years_1190_, v___x_1201_);
v___x_1203_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1196_, v___x_1202_);
lean_dec(v___x_1202_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1203_);
v___x_1205_ = v___x_1199_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_time_1197_);
v___x_1205_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; lean_object* v_second_1207_; lean_object* v_nano_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_second_1214_; lean_object* v_nano_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_tm_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1227_; 
lean_inc_ref(v___x_1205_);
v___x_1206_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1205_);
v_second_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_second_1207_);
v_nano_1208_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_nano_1208_);
lean_dec_ref(v___x_1206_);
v___x_1209_ = l_Std_Time_TimeZone_toSeconds(v_tz_1188_);
v___x_1210_ = lean_int_neg(v___x_1209_);
lean_dec(v___x_1209_);
v___x_1211_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1212_ = lean_int_mul(v___x_1210_, v___x_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = l_Std_Time_Duration_ofNanoseconds(v___x_1212_);
lean_dec(v___x_1212_);
v_second_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_second_1214_);
v_nano_1215_ = lean_ctor_get(v___x_1213_, 1);
lean_inc(v_nano_1215_);
lean_dec_ref(v___x_1213_);
v___f_1216_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1216_, 0, v___x_1205_);
v___x_1217_ = lean_int_mul(v_second_1207_, v___x_1211_);
lean_dec(v_second_1207_);
v___x_1218_ = lean_int_add(v___x_1217_, v_nano_1208_);
lean_dec(v_nano_1208_);
lean_dec(v___x_1217_);
v___x_1219_ = lean_int_mul(v_second_1214_, v___x_1211_);
lean_dec(v_second_1214_);
v___x_1220_ = lean_int_add(v___x_1219_, v_nano_1215_);
lean_dec(v_nano_1215_);
lean_dec(v___x_1219_);
v___x_1221_ = lean_int_add(v___x_1218_, v___x_1220_);
lean_dec(v___x_1220_);
lean_dec(v___x_1218_);
v___x_1222_ = l_Std_Time_Duration_ofNanoseconds(v___x_1221_);
lean_dec(v___x_1221_);
v_tm_1223_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1222_);
v___x_1224_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1223_);
v___x_1225_ = lean_mk_thunk(v___f_1216_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1225_);
lean_ctor_set(v___x_1193_, 0, v___x_1224_);
v___x_1227_ = v___x_1193_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object* v_tz_1233_, lean_object* v_dt_1234_, lean_object* v_years_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_Time_DateTime_addYearsClip(v_tz_1233_, v_dt_1234_, v_years_1235_);
lean_dec(v_years_1235_);
lean_dec_ref(v_tz_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object* v_tz_1237_, lean_object* v_dt_1238_, lean_object* v_years_1239_){
_start:
{
lean_object* v_date_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1281_; 
v_date_1240_ = lean_ctor_get(v_dt_1238_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_dt_1238_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_dt_1238_, 0);
lean_dec(v_unused_1282_);
v___x_1242_ = v_dt_1238_;
v_isShared_1243_ = v_isSharedCheck_1281_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_date_1240_);
lean_dec(v_dt_1238_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1281_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v_date_1245_; lean_object* v_time_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1280_; 
v___x_1244_ = lean_thunk_get_own(v_date_1240_);
lean_dec_ref(v_date_1240_);
v_date_1245_ = lean_ctor_get(v___x_1244_, 0);
v_time_1246_ = lean_ctor_get(v___x_1244_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1248_ = v___x_1244_;
v_isShared_1249_ = v_isSharedCheck_1280_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_time_1246_);
lean_inc(v_date_1245_);
lean_dec(v___x_1244_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1280_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1250_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_1251_ = lean_int_mul(v_years_1239_, v___x_1250_);
v___x_1252_ = lean_int_neg(v___x_1251_);
lean_dec(v___x_1251_);
v___x_1253_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1245_, v___x_1252_);
lean_dec(v___x_1252_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1253_);
v___x_1255_ = v___x_1248_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_time_1246_);
v___x_1255_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v_second_1257_; lean_object* v_nano_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_second_1264_; lean_object* v_nano_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_tm_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
lean_inc_ref(v___x_1255_);
v___x_1256_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1255_);
v_second_1257_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_second_1257_);
v_nano_1258_ = lean_ctor_get(v___x_1256_, 1);
lean_inc(v_nano_1258_);
lean_dec_ref(v___x_1256_);
v___x_1259_ = l_Std_Time_TimeZone_toSeconds(v_tz_1237_);
v___x_1260_ = lean_int_neg(v___x_1259_);
lean_dec(v___x_1259_);
v___x_1261_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1262_ = lean_int_mul(v___x_1260_, v___x_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = l_Std_Time_Duration_ofNanoseconds(v___x_1262_);
lean_dec(v___x_1262_);
v_second_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_second_1264_);
v_nano_1265_ = lean_ctor_get(v___x_1263_, 1);
lean_inc(v_nano_1265_);
lean_dec_ref(v___x_1263_);
v___f_1266_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1266_, 0, v___x_1255_);
v___x_1267_ = lean_int_mul(v_second_1257_, v___x_1261_);
lean_dec(v_second_1257_);
v___x_1268_ = lean_int_add(v___x_1267_, v_nano_1258_);
lean_dec(v_nano_1258_);
lean_dec(v___x_1267_);
v___x_1269_ = lean_int_mul(v_second_1264_, v___x_1261_);
lean_dec(v_second_1264_);
v___x_1270_ = lean_int_add(v___x_1269_, v_nano_1265_);
lean_dec(v_nano_1265_);
lean_dec(v___x_1269_);
v___x_1271_ = lean_int_add(v___x_1268_, v___x_1270_);
lean_dec(v___x_1270_);
lean_dec(v___x_1268_);
v___x_1272_ = l_Std_Time_Duration_ofNanoseconds(v___x_1271_);
lean_dec(v___x_1271_);
v_tm_1273_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1272_);
v___x_1274_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1273_);
v___x_1275_ = lean_mk_thunk(v___f_1266_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1275_);
lean_ctor_set(v___x_1242_, 0, v___x_1274_);
v___x_1277_ = v___x_1242_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object* v_tz_1283_, lean_object* v_dt_1284_, lean_object* v_years_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_Time_DateTime_subYearsRollOver(v_tz_1283_, v_dt_1284_, v_years_1285_);
lean_dec(v_years_1285_);
lean_dec_ref(v_tz_1283_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object* v_tz_1287_, lean_object* v_dt_1288_, lean_object* v_years_1289_){
_start:
{
lean_object* v_date_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1331_; 
v_date_1290_ = lean_ctor_get(v_dt_1288_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_dt_1288_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v_dt_1288_, 0);
lean_dec(v_unused_1332_);
v___x_1292_ = v_dt_1288_;
v_isShared_1293_ = v_isSharedCheck_1331_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_date_1290_);
lean_dec(v_dt_1288_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1331_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; lean_object* v_date_1295_; lean_object* v_time_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1330_; 
v___x_1294_ = lean_thunk_get_own(v_date_1290_);
lean_dec_ref(v_date_1290_);
v_date_1295_ = lean_ctor_get(v___x_1294_, 0);
v_time_1296_ = lean_ctor_get(v___x_1294_, 1);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1298_ = v___x_1294_;
v_isShared_1299_ = v_isSharedCheck_1330_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_time_1296_);
lean_inc(v_date_1295_);
lean_dec(v___x_1294_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1330_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1300_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_1301_ = lean_int_mul(v_years_1289_, v___x_1300_);
v___x_1302_ = lean_int_neg(v___x_1301_);
lean_dec(v___x_1301_);
v___x_1303_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1295_, v___x_1302_);
lean_dec(v___x_1302_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1303_);
v___x_1305_ = v___x_1298_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_time_1296_);
v___x_1305_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; lean_object* v_second_1307_; lean_object* v_nano_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v_second_1314_; lean_object* v_nano_1315_; lean_object* v___f_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v_tm_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
lean_inc_ref(v___x_1305_);
v___x_1306_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1305_);
v_second_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_second_1307_);
v_nano_1308_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_nano_1308_);
lean_dec_ref(v___x_1306_);
v___x_1309_ = l_Std_Time_TimeZone_toSeconds(v_tz_1287_);
v___x_1310_ = lean_int_neg(v___x_1309_);
lean_dec(v___x_1309_);
v___x_1311_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1312_ = lean_int_mul(v___x_1310_, v___x_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = l_Std_Time_Duration_ofNanoseconds(v___x_1312_);
lean_dec(v___x_1312_);
v_second_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_second_1314_);
v_nano_1315_ = lean_ctor_get(v___x_1313_, 1);
lean_inc(v_nano_1315_);
lean_dec_ref(v___x_1313_);
v___f_1316_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1316_, 0, v___x_1305_);
v___x_1317_ = lean_int_mul(v_second_1307_, v___x_1311_);
lean_dec(v_second_1307_);
v___x_1318_ = lean_int_add(v___x_1317_, v_nano_1308_);
lean_dec(v_nano_1308_);
lean_dec(v___x_1317_);
v___x_1319_ = lean_int_mul(v_second_1314_, v___x_1311_);
lean_dec(v_second_1314_);
v___x_1320_ = lean_int_add(v___x_1319_, v_nano_1315_);
lean_dec(v_nano_1315_);
lean_dec(v___x_1319_);
v___x_1321_ = lean_int_add(v___x_1318_, v___x_1320_);
lean_dec(v___x_1320_);
lean_dec(v___x_1318_);
v___x_1322_ = l_Std_Time_Duration_ofNanoseconds(v___x_1321_);
lean_dec(v___x_1321_);
v_tm_1323_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1322_);
v___x_1324_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1323_);
v___x_1325_ = lean_mk_thunk(v___f_1316_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v___x_1325_);
lean_ctor_set(v___x_1292_, 0, v___x_1324_);
v___x_1327_ = v___x_1292_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object* v_tz_1333_, lean_object* v_dt_1334_, lean_object* v_years_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_Time_DateTime_subYearsClip(v_tz_1333_, v_dt_1334_, v_years_1335_);
lean_dec(v_years_1335_);
lean_dec_ref(v_tz_1333_);
return v_res_1336_;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__0(void){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_unsigned_to_nat(4u);
v___x_1338_ = lean_nat_to_int(v___x_1337_);
return v___x_1338_;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__1(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = lean_nat_to_int(v___x_1339_);
return v___x_1340_;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__2(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1341_ = lean_unsigned_to_nat(400u);
v___x_1342_ = lean_nat_to_int(v___x_1341_);
return v___x_1342_;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__3(void){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_unsigned_to_nat(100u);
v___x_1344_ = lean_nat_to_int(v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object* v_tz_1345_, lean_object* v_dt_1346_, lean_object* v_days_1347_){
_start:
{
lean_object* v_date_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1416_; 
v_date_1348_ = lean_ctor_get(v_dt_1346_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_dt_1346_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; 
v_unused_1417_ = lean_ctor_get(v_dt_1346_, 0);
lean_dec(v_unused_1417_);
v___x_1350_ = v_dt_1346_;
v_isShared_1351_ = v_isSharedCheck_1416_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_date_1348_);
lean_dec(v_dt_1346_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1416_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___y_1354_; lean_object* v_date_1387_; lean_object* v_year_1388_; lean_object* v_month_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1414_; 
v___x_1352_ = lean_thunk_get_own(v_date_1348_);
lean_dec_ref(v_date_1348_);
v_date_1387_ = lean_ctor_get(v___x_1352_, 0);
lean_inc_ref(v_date_1387_);
v_year_1388_ = lean_ctor_get(v_date_1387_, 0);
v_month_1389_ = lean_ctor_get(v_date_1387_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_date_1387_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v_date_1387_, 2);
lean_dec(v_unused_1415_);
v___x_1391_ = v_date_1387_;
v_isShared_1392_ = v_isSharedCheck_1414_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_month_1389_);
lean_inc(v_year_1388_);
lean_dec(v_date_1387_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1414_;
goto v_resetjp_1390_;
}
v___jp_1353_:
{
lean_object* v_time_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1385_; 
v_time_1355_ = lean_ctor_get(v___x_1352_, 1);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; 
v_unused_1386_ = lean_ctor_get(v___x_1352_, 0);
lean_dec(v_unused_1386_);
v___x_1357_ = v___x_1352_;
v_isShared_1358_ = v_isSharedCheck_1385_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_time_1355_);
lean_dec(v___x_1352_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1385_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___y_1354_);
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___y_1354_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_time_1355_);
v___x_1360_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; lean_object* v_second_1362_; lean_object* v_nano_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v_second_1369_; lean_object* v_nano_1370_; lean_object* v___f_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_tm_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
lean_inc_ref(v___x_1360_);
v___x_1361_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1360_);
v_second_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_second_1362_);
v_nano_1363_ = lean_ctor_get(v___x_1361_, 1);
lean_inc(v_nano_1363_);
lean_dec_ref(v___x_1361_);
v___x_1364_ = l_Std_Time_TimeZone_toSeconds(v_tz_1345_);
v___x_1365_ = lean_int_neg(v___x_1364_);
lean_dec(v___x_1364_);
v___x_1366_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1367_ = lean_int_mul(v___x_1365_, v___x_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = l_Std_Time_Duration_ofNanoseconds(v___x_1367_);
lean_dec(v___x_1367_);
v_second_1369_ = lean_ctor_get(v___x_1368_, 0);
lean_inc(v_second_1369_);
v_nano_1370_ = lean_ctor_get(v___x_1368_, 1);
lean_inc(v_nano_1370_);
lean_dec_ref(v___x_1368_);
v___f_1371_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1371_, 0, v___x_1360_);
v___x_1372_ = lean_int_mul(v_second_1362_, v___x_1366_);
lean_dec(v_second_1362_);
v___x_1373_ = lean_int_add(v___x_1372_, v_nano_1363_);
lean_dec(v_nano_1363_);
lean_dec(v___x_1372_);
v___x_1374_ = lean_int_mul(v_second_1369_, v___x_1366_);
lean_dec(v_second_1369_);
v___x_1375_ = lean_int_add(v___x_1374_, v_nano_1370_);
lean_dec(v_nano_1370_);
lean_dec(v___x_1374_);
v___x_1376_ = lean_int_add(v___x_1373_, v___x_1375_);
lean_dec(v___x_1375_);
lean_dec(v___x_1373_);
v___x_1377_ = l_Std_Time_Duration_ofNanoseconds(v___x_1376_);
lean_dec(v___x_1376_);
v_tm_1378_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1377_);
v___x_1379_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1378_);
v___x_1380_ = lean_mk_thunk(v___f_1371_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1380_);
lean_ctor_set(v___x_1350_, 0, v___x_1379_);
v___x_1382_ = v___x_1350_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1380_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
v_resetjp_1390_:
{
uint8_t v___y_1394_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1410_; 
v___x_1403_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_1404_ = lean_int_mod(v_year_1388_, v___x_1403_);
v___x_1405_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_1410_ = lean_int_dec_eq(v___x_1404_, v___x_1405_);
lean_dec(v___x_1404_);
if (v___x_1410_ == 0)
{
v___y_1394_ = v___x_1410_;
goto v___jp_1393_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v___x_1411_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
v___x_1412_ = lean_int_mod(v_year_1388_, v___x_1411_);
v___x_1413_ = lean_int_dec_eq(v___x_1412_, v___x_1405_);
lean_dec(v___x_1412_);
if (v___x_1413_ == 0)
{
if (v___x_1410_ == 0)
{
goto v___jp_1406_;
}
else
{
v___y_1394_ = v___x_1410_;
goto v___jp_1393_;
}
}
else
{
goto v___jp_1406_;
}
}
v___jp_1393_:
{
lean_object* v_max_1395_; uint8_t v___x_1396_; 
v_max_1395_ = l_Std_Time_Month_Ordinal_days(v___y_1394_, v_month_1389_);
v___x_1396_ = lean_int_dec_lt(v_max_1395_, v_days_1347_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1398_; 
lean_dec(v_max_1395_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 2, v_days_1347_);
v___x_1398_ = v___x_1391_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_year_1388_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_month_1389_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_days_1347_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
v___y_1354_ = v___x_1398_;
goto v___jp_1353_;
}
}
else
{
lean_object* v___x_1401_; 
lean_dec(v_days_1347_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 2, v_max_1395_);
v___x_1401_ = v___x_1391_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_year_1388_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_month_1389_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_max_1395_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
v___y_1354_ = v___x_1401_;
goto v___jp_1353_;
}
}
}
v___jp_1406_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1407_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_1408_ = lean_int_mod(v_year_1388_, v___x_1407_);
v___x_1409_ = lean_int_dec_eq(v___x_1408_, v___x_1405_);
lean_dec(v___x_1408_);
v___y_1394_ = v___x_1409_;
goto v___jp_1393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip___boxed(lean_object* v_tz_1418_, lean_object* v_dt_1419_, lean_object* v_days_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Std_Time_DateTime_withDaysClip(v_tz_1418_, v_dt_1419_, v_days_1420_);
lean_dec_ref(v_tz_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object* v_tz_1422_, lean_object* v_dt_1423_, lean_object* v_days_1424_){
_start:
{
lean_object* v_date_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1465_; 
v_date_1425_ = lean_ctor_get(v_dt_1423_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_dt_1423_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_dt_1423_, 0);
lean_dec(v_unused_1466_);
v___x_1427_ = v_dt_1423_;
v_isShared_1428_ = v_isSharedCheck_1465_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_date_1425_);
lean_dec(v_dt_1423_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1465_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v_date_1430_; lean_object* v_time_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1464_; 
v___x_1429_ = lean_thunk_get_own(v_date_1425_);
lean_dec_ref(v_date_1425_);
v_date_1430_ = lean_ctor_get(v___x_1429_, 0);
v_time_1431_ = lean_ctor_get(v___x_1429_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1433_ = v___x_1429_;
v_isShared_1434_ = v_isSharedCheck_1464_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_time_1431_);
lean_inc(v_date_1430_);
lean_dec(v___x_1429_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1464_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_year_1435_; lean_object* v_month_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v_year_1435_ = lean_ctor_get(v_date_1430_, 0);
lean_inc(v_year_1435_);
v_month_1436_ = lean_ctor_get(v_date_1430_, 1);
lean_inc(v_month_1436_);
lean_dec_ref(v_date_1430_);
v___x_1437_ = l_Std_Time_PlainDate_rollOver(v_year_1435_, v_month_1436_, v_days_1424_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1437_);
v___x_1439_ = v___x_1433_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_time_1431_);
v___x_1439_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; lean_object* v_second_1441_; lean_object* v_nano_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_second_1448_; lean_object* v_nano_1449_; lean_object* v___f_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v_tm_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_inc_ref(v___x_1439_);
v___x_1440_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1439_);
v_second_1441_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_second_1441_);
v_nano_1442_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_nano_1442_);
lean_dec_ref(v___x_1440_);
v___x_1443_ = l_Std_Time_TimeZone_toSeconds(v_tz_1422_);
v___x_1444_ = lean_int_neg(v___x_1443_);
lean_dec(v___x_1443_);
v___x_1445_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1446_ = lean_int_mul(v___x_1444_, v___x_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = l_Std_Time_Duration_ofNanoseconds(v___x_1446_);
lean_dec(v___x_1446_);
v_second_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_second_1448_);
v_nano_1449_ = lean_ctor_get(v___x_1447_, 1);
lean_inc(v_nano_1449_);
lean_dec_ref(v___x_1447_);
v___f_1450_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1450_, 0, v___x_1439_);
v___x_1451_ = lean_int_mul(v_second_1441_, v___x_1445_);
lean_dec(v_second_1441_);
v___x_1452_ = lean_int_add(v___x_1451_, v_nano_1442_);
lean_dec(v_nano_1442_);
lean_dec(v___x_1451_);
v___x_1453_ = lean_int_mul(v_second_1448_, v___x_1445_);
lean_dec(v_second_1448_);
v___x_1454_ = lean_int_add(v___x_1453_, v_nano_1449_);
lean_dec(v_nano_1449_);
lean_dec(v___x_1453_);
v___x_1455_ = lean_int_add(v___x_1452_, v___x_1454_);
lean_dec(v___x_1454_);
lean_dec(v___x_1452_);
v___x_1456_ = l_Std_Time_Duration_ofNanoseconds(v___x_1455_);
lean_dec(v___x_1455_);
v_tm_1457_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1456_);
v___x_1458_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1457_);
v___x_1459_ = lean_mk_thunk(v___f_1450_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1459_);
lean_ctor_set(v___x_1427_, 0, v___x_1458_);
v___x_1461_ = v___x_1427_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1458_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object* v_tz_1467_, lean_object* v_dt_1468_, lean_object* v_days_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Std_Time_DateTime_withDaysRollOver(v_tz_1467_, v_dt_1468_, v_days_1469_);
lean_dec(v_days_1469_);
lean_dec_ref(v_tz_1467_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object* v_tz_1471_, lean_object* v_dt_1472_, lean_object* v_month_1473_){
_start:
{
lean_object* v_date_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1542_; 
v_date_1474_ = lean_ctor_get(v_dt_1472_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_dt_1472_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v_dt_1472_, 0);
lean_dec(v_unused_1543_);
v___x_1476_ = v_dt_1472_;
v_isShared_1477_ = v_isSharedCheck_1542_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_date_1474_);
lean_dec(v_dt_1472_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1542_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; lean_object* v___y_1480_; lean_object* v_date_1513_; lean_object* v_year_1514_; lean_object* v_day_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1540_; 
v___x_1478_ = lean_thunk_get_own(v_date_1474_);
lean_dec_ref(v_date_1474_);
v_date_1513_ = lean_ctor_get(v___x_1478_, 0);
lean_inc_ref(v_date_1513_);
v_year_1514_ = lean_ctor_get(v_date_1513_, 0);
v_day_1515_ = lean_ctor_get(v_date_1513_, 2);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_date_1513_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; 
v_unused_1541_ = lean_ctor_get(v_date_1513_, 1);
lean_dec(v_unused_1541_);
v___x_1517_ = v_date_1513_;
v_isShared_1518_ = v_isSharedCheck_1540_;
goto v_resetjp_1516_;
}
else
{
lean_inc(v_day_1515_);
lean_inc(v_year_1514_);
lean_dec(v_date_1513_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1540_;
goto v_resetjp_1516_;
}
v___jp_1479_:
{
lean_object* v_time_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1511_; 
v_time_1481_ = lean_ctor_get(v___x_1478_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v___x_1478_, 0);
lean_dec(v_unused_1512_);
v___x_1483_ = v___x_1478_;
v_isShared_1484_ = v_isSharedCheck_1511_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_time_1481_);
lean_dec(v___x_1478_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1511_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___y_1480_);
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___y_1480_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_time_1481_);
v___x_1486_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v_second_1488_; lean_object* v_nano_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_second_1495_; lean_object* v_nano_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v_tm_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
lean_inc_ref(v___x_1486_);
v___x_1487_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1486_);
v_second_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_second_1488_);
v_nano_1489_ = lean_ctor_get(v___x_1487_, 1);
lean_inc(v_nano_1489_);
lean_dec_ref(v___x_1487_);
v___x_1490_ = l_Std_Time_TimeZone_toSeconds(v_tz_1471_);
v___x_1491_ = lean_int_neg(v___x_1490_);
lean_dec(v___x_1490_);
v___x_1492_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1493_ = lean_int_mul(v___x_1491_, v___x_1492_);
lean_dec(v___x_1491_);
v___x_1494_ = l_Std_Time_Duration_ofNanoseconds(v___x_1493_);
lean_dec(v___x_1493_);
v_second_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_second_1495_);
v_nano_1496_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_nano_1496_);
lean_dec_ref(v___x_1494_);
v___f_1497_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1497_, 0, v___x_1486_);
v___x_1498_ = lean_int_mul(v_second_1488_, v___x_1492_);
lean_dec(v_second_1488_);
v___x_1499_ = lean_int_add(v___x_1498_, v_nano_1489_);
lean_dec(v_nano_1489_);
lean_dec(v___x_1498_);
v___x_1500_ = lean_int_mul(v_second_1495_, v___x_1492_);
lean_dec(v_second_1495_);
v___x_1501_ = lean_int_add(v___x_1500_, v_nano_1496_);
lean_dec(v_nano_1496_);
lean_dec(v___x_1500_);
v___x_1502_ = lean_int_add(v___x_1499_, v___x_1501_);
lean_dec(v___x_1501_);
lean_dec(v___x_1499_);
v___x_1503_ = l_Std_Time_Duration_ofNanoseconds(v___x_1502_);
lean_dec(v___x_1502_);
v_tm_1504_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1503_);
v___x_1505_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1504_);
v___x_1506_ = lean_mk_thunk(v___f_1497_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v___x_1506_);
lean_ctor_set(v___x_1476_, 0, v___x_1505_);
v___x_1508_ = v___x_1476_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
v_resetjp_1516_:
{
uint8_t v___y_1520_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1536_; 
v___x_1529_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_1530_ = lean_int_mod(v_year_1514_, v___x_1529_);
v___x_1531_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_1536_ = lean_int_dec_eq(v___x_1530_, v___x_1531_);
lean_dec(v___x_1530_);
if (v___x_1536_ == 0)
{
v___y_1520_ = v___x_1536_;
goto v___jp_1519_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1537_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
v___x_1538_ = lean_int_mod(v_year_1514_, v___x_1537_);
v___x_1539_ = lean_int_dec_eq(v___x_1538_, v___x_1531_);
lean_dec(v___x_1538_);
if (v___x_1539_ == 0)
{
if (v___x_1536_ == 0)
{
goto v___jp_1532_;
}
else
{
v___y_1520_ = v___x_1536_;
goto v___jp_1519_;
}
}
else
{
goto v___jp_1532_;
}
}
v___jp_1519_:
{
lean_object* v_max_1521_; uint8_t v___x_1522_; 
v_max_1521_ = l_Std_Time_Month_Ordinal_days(v___y_1520_, v_month_1473_);
v___x_1522_ = lean_int_dec_lt(v_max_1521_, v_day_1515_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1524_; 
lean_dec(v_max_1521_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 1, v_month_1473_);
v___x_1524_ = v___x_1517_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_year_1514_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_month_1473_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_day_1515_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
v___y_1480_ = v___x_1524_;
goto v___jp_1479_;
}
}
else
{
lean_object* v___x_1527_; 
lean_dec(v_day_1515_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 2, v_max_1521_);
lean_ctor_set(v___x_1517_, 1, v_month_1473_);
v___x_1527_ = v___x_1517_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_year_1514_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_month_1473_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_max_1521_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
v___y_1480_ = v___x_1527_;
goto v___jp_1479_;
}
}
}
v___jp_1532_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1533_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_1534_ = lean_int_mod(v_year_1514_, v___x_1533_);
v___x_1535_ = lean_int_dec_eq(v___x_1534_, v___x_1531_);
lean_dec(v___x_1534_);
v___y_1520_ = v___x_1535_;
goto v___jp_1519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip___boxed(lean_object* v_tz_1544_, lean_object* v_dt_1545_, lean_object* v_month_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Std_Time_DateTime_withMonthClip(v_tz_1544_, v_dt_1545_, v_month_1546_);
lean_dec_ref(v_tz_1544_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object* v_tz_1548_, lean_object* v_dt_1549_, lean_object* v_month_1550_){
_start:
{
lean_object* v_date_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1591_; 
v_date_1551_ = lean_ctor_get(v_dt_1549_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_dt_1549_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_dt_1549_, 0);
lean_dec(v_unused_1592_);
v___x_1553_ = v_dt_1549_;
v_isShared_1554_ = v_isSharedCheck_1591_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_date_1551_);
lean_dec(v_dt_1549_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1591_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v_date_1556_; lean_object* v_time_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1590_; 
v___x_1555_ = lean_thunk_get_own(v_date_1551_);
lean_dec_ref(v_date_1551_);
v_date_1556_ = lean_ctor_get(v___x_1555_, 0);
v_time_1557_ = lean_ctor_get(v___x_1555_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1559_ = v___x_1555_;
v_isShared_1560_ = v_isSharedCheck_1590_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_time_1557_);
lean_inc(v_date_1556_);
lean_dec(v___x_1555_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1590_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_year_1561_; lean_object* v_day_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v_year_1561_ = lean_ctor_get(v_date_1556_, 0);
lean_inc(v_year_1561_);
v_day_1562_ = lean_ctor_get(v_date_1556_, 2);
lean_inc(v_day_1562_);
lean_dec_ref(v_date_1556_);
v___x_1563_ = l_Std_Time_PlainDate_rollOver(v_year_1561_, v_month_1550_, v_day_1562_);
lean_dec(v_day_1562_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 0, v___x_1563_);
v___x_1565_ = v___x_1559_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_time_1557_);
v___x_1565_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1566_; lean_object* v_second_1567_; lean_object* v_nano_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v_second_1574_; lean_object* v_nano_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v_tm_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
lean_inc_ref(v___x_1565_);
v___x_1566_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1565_);
v_second_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_second_1567_);
v_nano_1568_ = lean_ctor_get(v___x_1566_, 1);
lean_inc(v_nano_1568_);
lean_dec_ref(v___x_1566_);
v___x_1569_ = l_Std_Time_TimeZone_toSeconds(v_tz_1548_);
v___x_1570_ = lean_int_neg(v___x_1569_);
lean_dec(v___x_1569_);
v___x_1571_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1572_ = lean_int_mul(v___x_1570_, v___x_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = l_Std_Time_Duration_ofNanoseconds(v___x_1572_);
lean_dec(v___x_1572_);
v_second_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_second_1574_);
v_nano_1575_ = lean_ctor_get(v___x_1573_, 1);
lean_inc(v_nano_1575_);
lean_dec_ref(v___x_1573_);
v___f_1576_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1576_, 0, v___x_1565_);
v___x_1577_ = lean_int_mul(v_second_1567_, v___x_1571_);
lean_dec(v_second_1567_);
v___x_1578_ = lean_int_add(v___x_1577_, v_nano_1568_);
lean_dec(v_nano_1568_);
lean_dec(v___x_1577_);
v___x_1579_ = lean_int_mul(v_second_1574_, v___x_1571_);
lean_dec(v_second_1574_);
v___x_1580_ = lean_int_add(v___x_1579_, v_nano_1575_);
lean_dec(v_nano_1575_);
lean_dec(v___x_1579_);
v___x_1581_ = lean_int_add(v___x_1578_, v___x_1580_);
lean_dec(v___x_1580_);
lean_dec(v___x_1578_);
v___x_1582_ = l_Std_Time_Duration_ofNanoseconds(v___x_1581_);
lean_dec(v___x_1581_);
v_tm_1583_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1582_);
v___x_1584_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1583_);
v___x_1585_ = lean_mk_thunk(v___f_1576_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 1, v___x_1585_);
lean_ctor_set(v___x_1553_, 0, v___x_1584_);
v___x_1587_ = v___x_1553_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver___boxed(lean_object* v_tz_1593_, lean_object* v_dt_1594_, lean_object* v_month_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Std_Time_DateTime_withMonthRollOver(v_tz_1593_, v_dt_1594_, v_month_1595_);
lean_dec_ref(v_tz_1593_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object* v_tz_1597_, lean_object* v_dt_1598_, lean_object* v_year_1599_){
_start:
{
lean_object* v_date_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1668_; 
v_date_1600_ = lean_ctor_get(v_dt_1598_, 1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_dt_1598_);
if (v_isSharedCheck_1668_ == 0)
{
lean_object* v_unused_1669_; 
v_unused_1669_ = lean_ctor_get(v_dt_1598_, 0);
lean_dec(v_unused_1669_);
v___x_1602_ = v_dt_1598_;
v_isShared_1603_ = v_isSharedCheck_1668_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_date_1600_);
lean_dec(v_dt_1598_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1668_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___y_1606_; lean_object* v_date_1639_; lean_object* v_month_1640_; lean_object* v_day_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1666_; 
v___x_1604_ = lean_thunk_get_own(v_date_1600_);
lean_dec_ref(v_date_1600_);
v_date_1639_ = lean_ctor_get(v___x_1604_, 0);
lean_inc_ref(v_date_1639_);
v_month_1640_ = lean_ctor_get(v_date_1639_, 1);
v_day_1641_ = lean_ctor_get(v_date_1639_, 2);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_date_1639_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v_date_1639_, 0);
lean_dec(v_unused_1667_);
v___x_1643_ = v_date_1639_;
v_isShared_1644_ = v_isSharedCheck_1666_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_day_1641_);
lean_inc(v_month_1640_);
lean_dec(v_date_1639_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1666_;
goto v_resetjp_1642_;
}
v___jp_1605_:
{
lean_object* v_time_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1637_; 
v_time_1607_ = lean_ctor_get(v___x_1604_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v___x_1604_, 0);
lean_dec(v_unused_1638_);
v___x_1609_ = v___x_1604_;
v_isShared_1610_ = v_isSharedCheck_1637_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_time_1607_);
lean_dec(v___x_1604_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1637_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___y_1606_);
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___y_1606_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_time_1607_);
v___x_1612_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
lean_object* v___x_1613_; lean_object* v_second_1614_; lean_object* v_nano_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v_second_1621_; lean_object* v_nano_1622_; lean_object* v___f_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v_tm_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
lean_inc_ref(v___x_1612_);
v___x_1613_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1612_);
v_second_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_second_1614_);
v_nano_1615_ = lean_ctor_get(v___x_1613_, 1);
lean_inc(v_nano_1615_);
lean_dec_ref(v___x_1613_);
v___x_1616_ = l_Std_Time_TimeZone_toSeconds(v_tz_1597_);
v___x_1617_ = lean_int_neg(v___x_1616_);
lean_dec(v___x_1616_);
v___x_1618_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1619_ = lean_int_mul(v___x_1617_, v___x_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = l_Std_Time_Duration_ofNanoseconds(v___x_1619_);
lean_dec(v___x_1619_);
v_second_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_second_1621_);
v_nano_1622_ = lean_ctor_get(v___x_1620_, 1);
lean_inc(v_nano_1622_);
lean_dec_ref(v___x_1620_);
v___f_1623_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1623_, 0, v___x_1612_);
v___x_1624_ = lean_int_mul(v_second_1614_, v___x_1618_);
lean_dec(v_second_1614_);
v___x_1625_ = lean_int_add(v___x_1624_, v_nano_1615_);
lean_dec(v_nano_1615_);
lean_dec(v___x_1624_);
v___x_1626_ = lean_int_mul(v_second_1621_, v___x_1618_);
lean_dec(v_second_1621_);
v___x_1627_ = lean_int_add(v___x_1626_, v_nano_1622_);
lean_dec(v_nano_1622_);
lean_dec(v___x_1626_);
v___x_1628_ = lean_int_add(v___x_1625_, v___x_1627_);
lean_dec(v___x_1627_);
lean_dec(v___x_1625_);
v___x_1629_ = l_Std_Time_Duration_ofNanoseconds(v___x_1628_);
lean_dec(v___x_1628_);
v_tm_1630_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1629_);
v___x_1631_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1630_);
v___x_1632_ = lean_mk_thunk(v___f_1623_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v___x_1632_);
lean_ctor_set(v___x_1602_, 0, v___x_1631_);
v___x_1634_ = v___x_1602_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v___x_1632_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
v_resetjp_1642_:
{
uint8_t v___y_1646_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1662_; 
v___x_1655_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_1656_ = lean_int_mod(v_year_1599_, v___x_1655_);
v___x_1657_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_1662_ = lean_int_dec_eq(v___x_1656_, v___x_1657_);
lean_dec(v___x_1656_);
if (v___x_1662_ == 0)
{
v___y_1646_ = v___x_1662_;
goto v___jp_1645_;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1663_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
v___x_1664_ = lean_int_mod(v_year_1599_, v___x_1663_);
v___x_1665_ = lean_int_dec_eq(v___x_1664_, v___x_1657_);
lean_dec(v___x_1664_);
if (v___x_1665_ == 0)
{
if (v___x_1662_ == 0)
{
goto v___jp_1658_;
}
else
{
v___y_1646_ = v___x_1662_;
goto v___jp_1645_;
}
}
else
{
goto v___jp_1658_;
}
}
v___jp_1645_:
{
lean_object* v_max_1647_; uint8_t v___x_1648_; 
v_max_1647_ = l_Std_Time_Month_Ordinal_days(v___y_1646_, v_month_1640_);
v___x_1648_ = lean_int_dec_lt(v_max_1647_, v_day_1641_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1650_; 
lean_dec(v_max_1647_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v_year_1599_);
v___x_1650_ = v___x_1643_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_year_1599_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_month_1640_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_day_1641_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
v___y_1606_ = v___x_1650_;
goto v___jp_1605_;
}
}
else
{
lean_object* v___x_1653_; 
lean_dec(v_day_1641_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 2, v_max_1647_);
lean_ctor_set(v___x_1643_, 0, v_year_1599_);
v___x_1653_ = v___x_1643_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_year_1599_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_month_1640_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_max_1647_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
v___y_1606_ = v___x_1653_;
goto v___jp_1605_;
}
}
}
v___jp_1658_:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v___x_1659_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_1660_ = lean_int_mod(v_year_1599_, v___x_1659_);
v___x_1661_ = lean_int_dec_eq(v___x_1660_, v___x_1657_);
lean_dec(v___x_1660_);
v___y_1646_ = v___x_1661_;
goto v___jp_1645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip___boxed(lean_object* v_tz_1670_, lean_object* v_dt_1671_, lean_object* v_year_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l_Std_Time_DateTime_withYearClip(v_tz_1670_, v_dt_1671_, v_year_1672_);
lean_dec_ref(v_tz_1670_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object* v_tz_1674_, lean_object* v_dt_1675_, lean_object* v_year_1676_){
_start:
{
lean_object* v_date_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1717_; 
v_date_1677_ = lean_ctor_get(v_dt_1675_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_dt_1675_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; 
v_unused_1718_ = lean_ctor_get(v_dt_1675_, 0);
lean_dec(v_unused_1718_);
v___x_1679_ = v_dt_1675_;
v_isShared_1680_ = v_isSharedCheck_1717_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_date_1677_);
lean_dec(v_dt_1675_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1717_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v_date_1682_; lean_object* v_time_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1716_; 
v___x_1681_ = lean_thunk_get_own(v_date_1677_);
lean_dec_ref(v_date_1677_);
v_date_1682_ = lean_ctor_get(v___x_1681_, 0);
v_time_1683_ = lean_ctor_get(v___x_1681_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1685_ = v___x_1681_;
v_isShared_1686_ = v_isSharedCheck_1716_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_time_1683_);
lean_inc(v_date_1682_);
lean_dec(v___x_1681_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1716_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_month_1687_; lean_object* v_day_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v_month_1687_ = lean_ctor_get(v_date_1682_, 1);
lean_inc(v_month_1687_);
v_day_1688_ = lean_ctor_get(v_date_1682_, 2);
lean_inc(v_day_1688_);
lean_dec_ref(v_date_1682_);
v___x_1689_ = l_Std_Time_PlainDate_rollOver(v_year_1676_, v_month_1687_, v_day_1688_);
lean_dec(v_day_1688_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 0, v___x_1689_);
v___x_1691_ = v___x_1685_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_time_1683_);
v___x_1691_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; lean_object* v_second_1693_; lean_object* v_nano_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_second_1700_; lean_object* v_nano_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v_tm_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_inc_ref(v___x_1691_);
v___x_1692_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1691_);
v_second_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_second_1693_);
v_nano_1694_ = lean_ctor_get(v___x_1692_, 1);
lean_inc(v_nano_1694_);
lean_dec_ref(v___x_1692_);
v___x_1695_ = l_Std_Time_TimeZone_toSeconds(v_tz_1674_);
v___x_1696_ = lean_int_neg(v___x_1695_);
lean_dec(v___x_1695_);
v___x_1697_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1698_ = lean_int_mul(v___x_1696_, v___x_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = l_Std_Time_Duration_ofNanoseconds(v___x_1698_);
lean_dec(v___x_1698_);
v_second_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_second_1700_);
v_nano_1701_ = lean_ctor_get(v___x_1699_, 1);
lean_inc(v_nano_1701_);
lean_dec_ref(v___x_1699_);
v___f_1702_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1702_, 0, v___x_1691_);
v___x_1703_ = lean_int_mul(v_second_1693_, v___x_1697_);
lean_dec(v_second_1693_);
v___x_1704_ = lean_int_add(v___x_1703_, v_nano_1694_);
lean_dec(v_nano_1694_);
lean_dec(v___x_1703_);
v___x_1705_ = lean_int_mul(v_second_1700_, v___x_1697_);
lean_dec(v_second_1700_);
v___x_1706_ = lean_int_add(v___x_1705_, v_nano_1701_);
lean_dec(v_nano_1701_);
lean_dec(v___x_1705_);
v___x_1707_ = lean_int_add(v___x_1704_, v___x_1706_);
lean_dec(v___x_1706_);
lean_dec(v___x_1704_);
v___x_1708_ = l_Std_Time_Duration_ofNanoseconds(v___x_1707_);
lean_dec(v___x_1707_);
v_tm_1709_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1708_);
v___x_1710_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1709_);
v___x_1711_ = lean_mk_thunk(v___f_1702_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___x_1711_);
lean_ctor_set(v___x_1679_, 0, v___x_1710_);
v___x_1713_ = v___x_1679_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver___boxed(lean_object* v_tz_1719_, lean_object* v_dt_1720_, lean_object* v_year_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_Time_DateTime_withYearRollOver(v_tz_1719_, v_dt_1720_, v_year_1721_);
lean_dec_ref(v_tz_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object* v_tz_1723_, lean_object* v_dt_1724_, lean_object* v_hour_1725_){
_start:
{
lean_object* v_date_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1774_; 
v_date_1726_ = lean_ctor_get(v_dt_1724_, 1);
v_isSharedCheck_1774_ = !lean_is_exclusive(v_dt_1724_);
if (v_isSharedCheck_1774_ == 0)
{
lean_object* v_unused_1775_; 
v_unused_1775_ = lean_ctor_get(v_dt_1724_, 0);
lean_dec(v_unused_1775_);
v___x_1728_ = v_dt_1724_;
v_isShared_1729_ = v_isSharedCheck_1774_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_date_1726_);
lean_dec(v_dt_1724_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1774_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v_time_1731_; lean_object* v_date_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1773_; 
v___x_1730_ = lean_thunk_get_own(v_date_1726_);
lean_dec_ref(v_date_1726_);
v_time_1731_ = lean_ctor_get(v___x_1730_, 1);
v_date_1732_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1734_ = v___x_1730_;
v_isShared_1735_ = v_isSharedCheck_1773_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_time_1731_);
lean_inc(v_date_1732_);
lean_dec(v___x_1730_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1773_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_minute_1736_; lean_object* v_second_1737_; lean_object* v_nanosecond_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1771_; 
v_minute_1736_ = lean_ctor_get(v_time_1731_, 1);
v_second_1737_ = lean_ctor_get(v_time_1731_, 2);
v_nanosecond_1738_ = lean_ctor_get(v_time_1731_, 3);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_time_1731_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v_time_1731_, 0);
lean_dec(v_unused_1772_);
v___x_1740_ = v_time_1731_;
v_isShared_1741_ = v_isSharedCheck_1771_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_nanosecond_1738_);
lean_inc(v_second_1737_);
lean_inc(v_minute_1736_);
lean_dec(v_time_1731_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1771_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v_hour_1725_);
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_hour_1725_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_minute_1736_);
lean_ctor_set(v_reuseFailAlloc_1770_, 2, v_second_1737_);
lean_ctor_set(v_reuseFailAlloc_1770_, 3, v_nanosecond_1738_);
v___x_1743_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1743_);
v___x_1745_ = v___x_1734_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_date_1732_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; lean_object* v_second_1747_; lean_object* v_nano_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v_second_1754_; lean_object* v_nano_1755_; lean_object* v___f_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v_tm_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
lean_inc_ref(v___x_1745_);
v___x_1746_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1745_);
v_second_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_second_1747_);
v_nano_1748_ = lean_ctor_get(v___x_1746_, 1);
lean_inc(v_nano_1748_);
lean_dec_ref(v___x_1746_);
v___x_1749_ = l_Std_Time_TimeZone_toSeconds(v_tz_1723_);
v___x_1750_ = lean_int_neg(v___x_1749_);
lean_dec(v___x_1749_);
v___x_1751_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1752_ = lean_int_mul(v___x_1750_, v___x_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = l_Std_Time_Duration_ofNanoseconds(v___x_1752_);
lean_dec(v___x_1752_);
v_second_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_second_1754_);
v_nano_1755_ = lean_ctor_get(v___x_1753_, 1);
lean_inc(v_nano_1755_);
lean_dec_ref(v___x_1753_);
v___f_1756_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1756_, 0, v___x_1745_);
v___x_1757_ = lean_int_mul(v_second_1747_, v___x_1751_);
lean_dec(v_second_1747_);
v___x_1758_ = lean_int_add(v___x_1757_, v_nano_1748_);
lean_dec(v_nano_1748_);
lean_dec(v___x_1757_);
v___x_1759_ = lean_int_mul(v_second_1754_, v___x_1751_);
lean_dec(v_second_1754_);
v___x_1760_ = lean_int_add(v___x_1759_, v_nano_1755_);
lean_dec(v_nano_1755_);
lean_dec(v___x_1759_);
v___x_1761_ = lean_int_add(v___x_1758_, v___x_1760_);
lean_dec(v___x_1760_);
lean_dec(v___x_1758_);
v___x_1762_ = l_Std_Time_Duration_ofNanoseconds(v___x_1761_);
lean_dec(v___x_1761_);
v_tm_1763_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1762_);
v___x_1764_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1763_);
v___x_1765_ = lean_mk_thunk(v___f_1756_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v___x_1765_);
lean_ctor_set(v___x_1728_, 0, v___x_1764_);
v___x_1767_ = v___x_1728_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours___boxed(lean_object* v_tz_1776_, lean_object* v_dt_1777_, lean_object* v_hour_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Std_Time_DateTime_withHours(v_tz_1776_, v_dt_1777_, v_hour_1778_);
lean_dec_ref(v_tz_1776_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object* v_tz_1780_, lean_object* v_dt_1781_, lean_object* v_minute_1782_){
_start:
{
lean_object* v_date_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1831_; 
v_date_1783_ = lean_ctor_get(v_dt_1781_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_dt_1781_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v_dt_1781_, 0);
lean_dec(v_unused_1832_);
v___x_1785_ = v_dt_1781_;
v_isShared_1786_ = v_isSharedCheck_1831_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_date_1783_);
lean_dec(v_dt_1781_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1831_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v_time_1788_; lean_object* v_date_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1830_; 
v___x_1787_ = lean_thunk_get_own(v_date_1783_);
lean_dec_ref(v_date_1783_);
v_time_1788_ = lean_ctor_get(v___x_1787_, 1);
v_date_1789_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1791_ = v___x_1787_;
v_isShared_1792_ = v_isSharedCheck_1830_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_time_1788_);
lean_inc(v_date_1789_);
lean_dec(v___x_1787_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1830_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v_hour_1793_; lean_object* v_second_1794_; lean_object* v_nanosecond_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1828_; 
v_hour_1793_ = lean_ctor_get(v_time_1788_, 0);
v_second_1794_ = lean_ctor_get(v_time_1788_, 2);
v_nanosecond_1795_ = lean_ctor_get(v_time_1788_, 3);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_time_1788_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_time_1788_, 1);
lean_dec(v_unused_1829_);
v___x_1797_ = v_time_1788_;
v_isShared_1798_ = v_isSharedCheck_1828_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_nanosecond_1795_);
lean_inc(v_second_1794_);
lean_inc(v_hour_1793_);
lean_dec(v_time_1788_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1828_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 1, v_minute_1782_);
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_hour_1793_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_minute_1782_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_second_1794_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_nanosecond_1795_);
v___x_1800_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1802_; 
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 1, v___x_1800_);
v___x_1802_ = v___x_1791_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_date_1789_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v_second_1804_; lean_object* v_nano_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v_second_1811_; lean_object* v_nano_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v_tm_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1824_; 
lean_inc_ref(v___x_1802_);
v___x_1803_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1802_);
v_second_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_second_1804_);
v_nano_1805_ = lean_ctor_get(v___x_1803_, 1);
lean_inc(v_nano_1805_);
lean_dec_ref(v___x_1803_);
v___x_1806_ = l_Std_Time_TimeZone_toSeconds(v_tz_1780_);
v___x_1807_ = lean_int_neg(v___x_1806_);
lean_dec(v___x_1806_);
v___x_1808_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1809_ = lean_int_mul(v___x_1807_, v___x_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = l_Std_Time_Duration_ofNanoseconds(v___x_1809_);
lean_dec(v___x_1809_);
v_second_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_second_1811_);
v_nano_1812_ = lean_ctor_get(v___x_1810_, 1);
lean_inc(v_nano_1812_);
lean_dec_ref(v___x_1810_);
v___f_1813_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1813_, 0, v___x_1802_);
v___x_1814_ = lean_int_mul(v_second_1804_, v___x_1808_);
lean_dec(v_second_1804_);
v___x_1815_ = lean_int_add(v___x_1814_, v_nano_1805_);
lean_dec(v_nano_1805_);
lean_dec(v___x_1814_);
v___x_1816_ = lean_int_mul(v_second_1811_, v___x_1808_);
lean_dec(v_second_1811_);
v___x_1817_ = lean_int_add(v___x_1816_, v_nano_1812_);
lean_dec(v_nano_1812_);
lean_dec(v___x_1816_);
v___x_1818_ = lean_int_add(v___x_1815_, v___x_1817_);
lean_dec(v___x_1817_);
lean_dec(v___x_1815_);
v___x_1819_ = l_Std_Time_Duration_ofNanoseconds(v___x_1818_);
lean_dec(v___x_1818_);
v_tm_1820_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1819_);
v___x_1821_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1820_);
v___x_1822_ = lean_mk_thunk(v___f_1813_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 1, v___x_1822_);
lean_ctor_set(v___x_1785_, 0, v___x_1821_);
v___x_1824_ = v___x_1785_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes___boxed(lean_object* v_tz_1833_, lean_object* v_dt_1834_, lean_object* v_minute_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Std_Time_DateTime_withMinutes(v_tz_1833_, v_dt_1834_, v_minute_1835_);
lean_dec_ref(v_tz_1833_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object* v_tz_1837_, lean_object* v_dt_1838_, lean_object* v_second_1839_){
_start:
{
lean_object* v_date_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1888_; 
v_date_1840_ = lean_ctor_get(v_dt_1838_, 1);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_dt_1838_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; 
v_unused_1889_ = lean_ctor_get(v_dt_1838_, 0);
lean_dec(v_unused_1889_);
v___x_1842_ = v_dt_1838_;
v_isShared_1843_ = v_isSharedCheck_1888_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_date_1840_);
lean_dec(v_dt_1838_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1888_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v_time_1845_; lean_object* v_date_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1887_; 
v___x_1844_ = lean_thunk_get_own(v_date_1840_);
lean_dec_ref(v_date_1840_);
v_time_1845_ = lean_ctor_get(v___x_1844_, 1);
v_date_1846_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1848_ = v___x_1844_;
v_isShared_1849_ = v_isSharedCheck_1887_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_time_1845_);
lean_inc(v_date_1846_);
lean_dec(v___x_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1887_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v_hour_1850_; lean_object* v_minute_1851_; lean_object* v_nanosecond_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1885_; 
v_hour_1850_ = lean_ctor_get(v_time_1845_, 0);
v_minute_1851_ = lean_ctor_get(v_time_1845_, 1);
v_nanosecond_1852_ = lean_ctor_get(v_time_1845_, 3);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_time_1845_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v_time_1845_, 2);
lean_dec(v_unused_1886_);
v___x_1854_ = v_time_1845_;
v_isShared_1855_ = v_isSharedCheck_1885_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_nanosecond_1852_);
lean_inc(v_minute_1851_);
lean_inc(v_hour_1850_);
lean_dec(v_time_1845_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1885_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 2, v_second_1839_);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_hour_1850_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_minute_1851_);
lean_ctor_set(v_reuseFailAlloc_1884_, 2, v_second_1839_);
lean_ctor_set(v_reuseFailAlloc_1884_, 3, v_nanosecond_1852_);
v___x_1857_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1859_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v___x_1857_);
v___x_1859_ = v___x_1848_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_date_1846_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; lean_object* v_second_1861_; lean_object* v_nano_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v_second_1868_; lean_object* v_nano_1869_; lean_object* v___f_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v_tm_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
lean_inc_ref(v___x_1859_);
v___x_1860_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1859_);
v_second_1861_ = lean_ctor_get(v___x_1860_, 0);
lean_inc(v_second_1861_);
v_nano_1862_ = lean_ctor_get(v___x_1860_, 1);
lean_inc(v_nano_1862_);
lean_dec_ref(v___x_1860_);
v___x_1863_ = l_Std_Time_TimeZone_toSeconds(v_tz_1837_);
v___x_1864_ = lean_int_neg(v___x_1863_);
lean_dec(v___x_1863_);
v___x_1865_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1866_ = lean_int_mul(v___x_1864_, v___x_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = l_Std_Time_Duration_ofNanoseconds(v___x_1866_);
lean_dec(v___x_1866_);
v_second_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_second_1868_);
v_nano_1869_ = lean_ctor_get(v___x_1867_, 1);
lean_inc(v_nano_1869_);
lean_dec_ref(v___x_1867_);
v___f_1870_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1870_, 0, v___x_1859_);
v___x_1871_ = lean_int_mul(v_second_1861_, v___x_1865_);
lean_dec(v_second_1861_);
v___x_1872_ = lean_int_add(v___x_1871_, v_nano_1862_);
lean_dec(v_nano_1862_);
lean_dec(v___x_1871_);
v___x_1873_ = lean_int_mul(v_second_1868_, v___x_1865_);
lean_dec(v_second_1868_);
v___x_1874_ = lean_int_add(v___x_1873_, v_nano_1869_);
lean_dec(v_nano_1869_);
lean_dec(v___x_1873_);
v___x_1875_ = lean_int_add(v___x_1872_, v___x_1874_);
lean_dec(v___x_1874_);
lean_dec(v___x_1872_);
v___x_1876_ = l_Std_Time_Duration_ofNanoseconds(v___x_1875_);
lean_dec(v___x_1875_);
v_tm_1877_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1876_);
v___x_1878_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1877_);
v___x_1879_ = lean_mk_thunk(v___f_1870_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 1, v___x_1879_);
lean_ctor_set(v___x_1842_, 0, v___x_1878_);
v___x_1881_ = v___x_1842_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds___boxed(lean_object* v_tz_1890_, lean_object* v_dt_1891_, lean_object* v_second_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Std_Time_DateTime_withSeconds(v_tz_1890_, v_dt_1891_, v_second_1892_);
lean_dec_ref(v_tz_1890_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object* v_tz_1894_, lean_object* v_dt_1895_, lean_object* v_nano_1896_){
_start:
{
lean_object* v_date_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1945_; 
v_date_1897_ = lean_ctor_get(v_dt_1895_, 1);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_dt_1895_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v_dt_1895_, 0);
lean_dec(v_unused_1946_);
v___x_1899_ = v_dt_1895_;
v_isShared_1900_ = v_isSharedCheck_1945_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_date_1897_);
lean_dec(v_dt_1895_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1945_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v_time_1902_; lean_object* v_date_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1944_; 
v___x_1901_ = lean_thunk_get_own(v_date_1897_);
lean_dec_ref(v_date_1897_);
v_time_1902_ = lean_ctor_get(v___x_1901_, 1);
v_date_1903_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1905_ = v___x_1901_;
v_isShared_1906_ = v_isSharedCheck_1944_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_time_1902_);
lean_inc(v_date_1903_);
lean_dec(v___x_1901_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1944_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_hour_1907_; lean_object* v_minute_1908_; lean_object* v_second_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1942_; 
v_hour_1907_ = lean_ctor_get(v_time_1902_, 0);
v_minute_1908_ = lean_ctor_get(v_time_1902_, 1);
v_second_1909_ = lean_ctor_get(v_time_1902_, 2);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_time_1902_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v_time_1902_, 3);
lean_dec(v_unused_1943_);
v___x_1911_ = v_time_1902_;
v_isShared_1912_ = v_isSharedCheck_1942_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_second_1909_);
lean_inc(v_minute_1908_);
lean_inc(v_hour_1907_);
lean_dec(v_time_1902_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1942_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 3, v_nano_1896_);
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_hour_1907_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_minute_1908_);
lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_second_1909_);
lean_ctor_set(v_reuseFailAlloc_1941_, 3, v_nano_1896_);
v___x_1914_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 1, v___x_1914_);
v___x_1916_ = v___x_1905_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_date_1903_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v_second_1918_; lean_object* v_nano_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v_second_1925_; lean_object* v_nano_1926_; lean_object* v___f_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v_tm_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
lean_inc_ref(v___x_1916_);
v___x_1917_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1916_);
v_second_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_second_1918_);
v_nano_1919_ = lean_ctor_get(v___x_1917_, 1);
lean_inc(v_nano_1919_);
lean_dec_ref(v___x_1917_);
v___x_1920_ = l_Std_Time_TimeZone_toSeconds(v_tz_1894_);
v___x_1921_ = lean_int_neg(v___x_1920_);
lean_dec(v___x_1920_);
v___x_1922_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1923_ = lean_int_mul(v___x_1921_, v___x_1922_);
lean_dec(v___x_1921_);
v___x_1924_ = l_Std_Time_Duration_ofNanoseconds(v___x_1923_);
lean_dec(v___x_1923_);
v_second_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_second_1925_);
v_nano_1926_ = lean_ctor_get(v___x_1924_, 1);
lean_inc(v_nano_1926_);
lean_dec_ref(v___x_1924_);
v___f_1927_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1927_, 0, v___x_1916_);
v___x_1928_ = lean_int_mul(v_second_1918_, v___x_1922_);
lean_dec(v_second_1918_);
v___x_1929_ = lean_int_add(v___x_1928_, v_nano_1919_);
lean_dec(v_nano_1919_);
lean_dec(v___x_1928_);
v___x_1930_ = lean_int_mul(v_second_1925_, v___x_1922_);
lean_dec(v_second_1925_);
v___x_1931_ = lean_int_add(v___x_1930_, v_nano_1926_);
lean_dec(v_nano_1926_);
lean_dec(v___x_1930_);
v___x_1932_ = lean_int_add(v___x_1929_, v___x_1931_);
lean_dec(v___x_1931_);
lean_dec(v___x_1929_);
v___x_1933_ = l_Std_Time_Duration_ofNanoseconds(v___x_1932_);
lean_dec(v___x_1932_);
v_tm_1934_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1933_);
v___x_1935_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1934_);
v___x_1936_ = lean_mk_thunk(v___f_1927_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1936_);
lean_ctor_set(v___x_1899_, 0, v___x_1935_);
v___x_1938_ = v___x_1899_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds___boxed(lean_object* v_tz_1947_, lean_object* v_dt_1948_, lean_object* v_nano_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Std_Time_DateTime_withNanoseconds(v_tz_1947_, v_dt_1948_, v_nano_1949_);
lean_dec_ref(v_tz_1947_);
return v_res_1950_;
}
}
static lean_object* _init_l_Std_Time_DateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_unsigned_to_nat(1000u);
v___x_1952_ = lean_nat_to_int(v___x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object* v_tz_1953_, lean_object* v_dt_1954_, lean_object* v_milli_1955_){
_start:
{
lean_object* v_date_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_2009_; 
v_date_1956_ = lean_ctor_get(v_dt_1954_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_dt_1954_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_dt_1954_, 0);
lean_dec(v_unused_2010_);
v___x_1958_ = v_dt_1954_;
v_isShared_1959_ = v_isSharedCheck_2009_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_date_1956_);
lean_dec(v_dt_1954_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_2009_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v_time_1961_; lean_object* v_date_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_2008_; 
v___x_1960_ = lean_thunk_get_own(v_date_1956_);
lean_dec_ref(v_date_1956_);
v_time_1961_ = lean_ctor_get(v___x_1960_, 1);
v_date_1962_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1964_ = v___x_1960_;
v_isShared_1965_ = v_isSharedCheck_2008_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_time_1961_);
lean_inc(v_date_1962_);
lean_dec(v___x_1960_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_2008_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_hour_1966_; lean_object* v_minute_1967_; lean_object* v_second_1968_; lean_object* v_nanosecond_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2007_; 
v_hour_1966_ = lean_ctor_get(v_time_1961_, 0);
v_minute_1967_ = lean_ctor_get(v_time_1961_, 1);
v_second_1968_ = lean_ctor_get(v_time_1961_, 2);
v_nanosecond_1969_ = lean_ctor_get(v_time_1961_, 3);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_time_1961_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1971_ = v_time_1961_;
v_isShared_1972_ = v_isSharedCheck_2007_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_nanosecond_1969_);
lean_inc(v_second_1968_);
lean_inc(v_minute_1967_);
lean_inc(v_hour_1966_);
lean_dec(v_time_1961_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2007_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1973_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_1974_ = lean_int_emod(v_nanosecond_1969_, v___x_1973_);
lean_dec(v_nanosecond_1969_);
v___x_1975_ = lean_obj_once(&l_Std_Time_DateTime_addMilliseconds___closed__0, &l_Std_Time_DateTime_addMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_addMilliseconds___closed__0);
v___x_1976_ = lean_int_mul(v_milli_1955_, v___x_1975_);
v___x_1977_ = lean_int_add(v___x_1976_, v___x_1974_);
lean_dec(v___x_1974_);
lean_dec(v___x_1976_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 3, v___x_1977_);
v___x_1979_ = v___x_1971_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_hour_1966_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_minute_1967_);
lean_ctor_set(v_reuseFailAlloc_2006_, 2, v_second_1968_);
lean_ctor_set(v_reuseFailAlloc_2006_, 3, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_2006_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 1, v___x_1979_);
v___x_1981_ = v___x_1964_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_date_1962_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v_second_1983_; lean_object* v_nano_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v_second_1990_; lean_object* v_nano_1991_; lean_object* v___f_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v_tm_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
lean_inc_ref(v___x_1981_);
v___x_1982_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1981_);
v_second_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_second_1983_);
v_nano_1984_ = lean_ctor_get(v___x_1982_, 1);
lean_inc(v_nano_1984_);
lean_dec_ref(v___x_1982_);
v___x_1985_ = l_Std_Time_TimeZone_toSeconds(v_tz_1953_);
v___x_1986_ = lean_int_neg(v___x_1985_);
lean_dec(v___x_1985_);
v___x_1987_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1988_ = lean_int_mul(v___x_1986_, v___x_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = l_Std_Time_Duration_ofNanoseconds(v___x_1988_);
lean_dec(v___x_1988_);
v_second_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_second_1990_);
v_nano_1991_ = lean_ctor_get(v___x_1989_, 1);
lean_inc(v_nano_1991_);
lean_dec_ref(v___x_1989_);
v___f_1992_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1992_, 0, v___x_1981_);
v___x_1993_ = lean_int_mul(v_second_1983_, v___x_1987_);
lean_dec(v_second_1983_);
v___x_1994_ = lean_int_add(v___x_1993_, v_nano_1984_);
lean_dec(v_nano_1984_);
lean_dec(v___x_1993_);
v___x_1995_ = lean_int_mul(v_second_1990_, v___x_1987_);
lean_dec(v_second_1990_);
v___x_1996_ = lean_int_add(v___x_1995_, v_nano_1991_);
lean_dec(v_nano_1991_);
lean_dec(v___x_1995_);
v___x_1997_ = lean_int_add(v___x_1994_, v___x_1996_);
lean_dec(v___x_1996_);
lean_dec(v___x_1994_);
v___x_1998_ = l_Std_Time_Duration_ofNanoseconds(v___x_1997_);
lean_dec(v___x_1997_);
v_tm_1999_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1998_);
v___x_2000_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_1999_);
v___x_2001_ = lean_mk_thunk(v___f_1992_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v___x_2001_);
lean_ctor_set(v___x_1958_, 0, v___x_2000_);
v___x_2003_ = v___x_1958_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object* v_tz_2011_, lean_object* v_dt_2012_, lean_object* v_milli_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Std_Time_DateTime_withMilliseconds(v_tz_2011_, v_dt_2012_, v_milli_2013_);
lean_dec(v_milli_2013_);
lean_dec_ref(v_tz_2011_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg(lean_object* v_dt_2015_){
_start:
{
lean_object* v_date_2016_; lean_object* v___x_2017_; 
v_date_2016_ = lean_ctor_get(v_dt_2015_, 1);
v___x_2017_ = lean_thunk_get_own(v_date_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg___boxed(lean_object* v_dt_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Std_Time_DateTime_toPlainDateTime___redArg(v_dt_2018_);
lean_dec_ref(v_dt_2018_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object* v_tz_2020_, lean_object* v_dt_2021_){
_start:
{
lean_object* v_date_2022_; lean_object* v___x_2023_; 
v_date_2022_ = lean_ctor_get(v_dt_2021_, 1);
v___x_2023_ = lean_thunk_get_own(v_date_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object* v_tz_2024_, lean_object* v_dt_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Std_Time_DateTime_toPlainDateTime(v_tz_2024_, v_dt_2025_);
lean_dec_ref(v_dt_2025_);
lean_dec_ref(v_tz_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg(lean_object* v_dt_2027_){
_start:
{
lean_object* v_date_2028_; lean_object* v___x_2029_; lean_object* v_date_2030_; lean_object* v_year_2031_; 
v_date_2028_ = lean_ctor_get(v_dt_2027_, 1);
v___x_2029_ = lean_thunk_get_own(v_date_2028_);
v_date_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc_ref(v_date_2030_);
lean_dec(v___x_2029_);
v_year_2031_ = lean_ctor_get(v_date_2030_, 0);
lean_inc(v_year_2031_);
lean_dec_ref(v_date_2030_);
return v_year_2031_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg___boxed(lean_object* v_dt_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Std_Time_DateTime_year___redArg(v_dt_2032_);
lean_dec_ref(v_dt_2032_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object* v_tz_2034_, lean_object* v_dt_2035_){
_start:
{
lean_object* v_date_2036_; lean_object* v___x_2037_; lean_object* v_date_2038_; lean_object* v_year_2039_; 
v_date_2036_ = lean_ctor_get(v_dt_2035_, 1);
v___x_2037_ = lean_thunk_get_own(v_date_2036_);
v_date_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc_ref(v_date_2038_);
lean_dec(v___x_2037_);
v_year_2039_ = lean_ctor_get(v_date_2038_, 0);
lean_inc(v_year_2039_);
lean_dec_ref(v_date_2038_);
return v_year_2039_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object* v_tz_2040_, lean_object* v_dt_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Std_Time_DateTime_year(v_tz_2040_, v_dt_2041_);
lean_dec_ref(v_dt_2041_);
lean_dec_ref(v_tz_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg(lean_object* v_dt_2043_){
_start:
{
lean_object* v_date_2044_; lean_object* v___x_2045_; lean_object* v_date_2046_; lean_object* v_month_2047_; 
v_date_2044_ = lean_ctor_get(v_dt_2043_, 1);
v___x_2045_ = lean_thunk_get_own(v_date_2044_);
v_date_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_ref(v_date_2046_);
lean_dec(v___x_2045_);
v_month_2047_ = lean_ctor_get(v_date_2046_, 1);
lean_inc(v_month_2047_);
lean_dec_ref(v_date_2046_);
return v_month_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg___boxed(lean_object* v_dt_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Std_Time_DateTime_month___redArg(v_dt_2048_);
lean_dec_ref(v_dt_2048_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object* v_tz_2050_, lean_object* v_dt_2051_){
_start:
{
lean_object* v_date_2052_; lean_object* v___x_2053_; lean_object* v_date_2054_; lean_object* v_month_2055_; 
v_date_2052_ = lean_ctor_get(v_dt_2051_, 1);
v___x_2053_ = lean_thunk_get_own(v_date_2052_);
v_date_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc_ref(v_date_2054_);
lean_dec(v___x_2053_);
v_month_2055_ = lean_ctor_get(v_date_2054_, 1);
lean_inc(v_month_2055_);
lean_dec_ref(v_date_2054_);
return v_month_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object* v_tz_2056_, lean_object* v_dt_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Std_Time_DateTime_month(v_tz_2056_, v_dt_2057_);
lean_dec_ref(v_dt_2057_);
lean_dec_ref(v_tz_2056_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg(lean_object* v_dt_2059_){
_start:
{
lean_object* v_date_2060_; lean_object* v___x_2061_; lean_object* v_date_2062_; lean_object* v_day_2063_; 
v_date_2060_ = lean_ctor_get(v_dt_2059_, 1);
v___x_2061_ = lean_thunk_get_own(v_date_2060_);
v_date_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc_ref(v_date_2062_);
lean_dec(v___x_2061_);
v_day_2063_ = lean_ctor_get(v_date_2062_, 2);
lean_inc(v_day_2063_);
lean_dec_ref(v_date_2062_);
return v_day_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg___boxed(lean_object* v_dt_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_Time_DateTime_day___redArg(v_dt_2064_);
lean_dec_ref(v_dt_2064_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object* v_tz_2066_, lean_object* v_dt_2067_){
_start:
{
lean_object* v_date_2068_; lean_object* v___x_2069_; lean_object* v_date_2070_; lean_object* v_day_2071_; 
v_date_2068_ = lean_ctor_get(v_dt_2067_, 1);
v___x_2069_ = lean_thunk_get_own(v_date_2068_);
v_date_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc_ref(v_date_2070_);
lean_dec(v___x_2069_);
v_day_2071_ = lean_ctor_get(v_date_2070_, 2);
lean_inc(v_day_2071_);
lean_dec_ref(v_date_2070_);
return v_day_2071_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object* v_tz_2072_, lean_object* v_dt_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Std_Time_DateTime_day(v_tz_2072_, v_dt_2073_);
lean_dec_ref(v_dt_2073_);
lean_dec_ref(v_tz_2072_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg(lean_object* v_dt_2075_){
_start:
{
lean_object* v_date_2076_; lean_object* v___x_2077_; lean_object* v_time_2078_; lean_object* v_hour_2079_; 
v_date_2076_ = lean_ctor_get(v_dt_2075_, 1);
v___x_2077_ = lean_thunk_get_own(v_date_2076_);
v_time_2078_ = lean_ctor_get(v___x_2077_, 1);
lean_inc_ref(v_time_2078_);
lean_dec(v___x_2077_);
v_hour_2079_ = lean_ctor_get(v_time_2078_, 0);
lean_inc(v_hour_2079_);
lean_dec_ref(v_time_2078_);
return v_hour_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg___boxed(lean_object* v_dt_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Std_Time_DateTime_hour___redArg(v_dt_2080_);
lean_dec_ref(v_dt_2080_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object* v_tz_2082_, lean_object* v_dt_2083_){
_start:
{
lean_object* v_date_2084_; lean_object* v___x_2085_; lean_object* v_time_2086_; lean_object* v_hour_2087_; 
v_date_2084_ = lean_ctor_get(v_dt_2083_, 1);
v___x_2085_ = lean_thunk_get_own(v_date_2084_);
v_time_2086_ = lean_ctor_get(v___x_2085_, 1);
lean_inc_ref(v_time_2086_);
lean_dec(v___x_2085_);
v_hour_2087_ = lean_ctor_get(v_time_2086_, 0);
lean_inc(v_hour_2087_);
lean_dec_ref(v_time_2086_);
return v_hour_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object* v_tz_2088_, lean_object* v_dt_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_Time_DateTime_hour(v_tz_2088_, v_dt_2089_);
lean_dec_ref(v_dt_2089_);
lean_dec_ref(v_tz_2088_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg(lean_object* v_dt_2091_){
_start:
{
lean_object* v_date_2092_; lean_object* v___x_2093_; lean_object* v_time_2094_; lean_object* v_minute_2095_; 
v_date_2092_ = lean_ctor_get(v_dt_2091_, 1);
v___x_2093_ = lean_thunk_get_own(v_date_2092_);
v_time_2094_ = lean_ctor_get(v___x_2093_, 1);
lean_inc_ref(v_time_2094_);
lean_dec(v___x_2093_);
v_minute_2095_ = lean_ctor_get(v_time_2094_, 1);
lean_inc(v_minute_2095_);
lean_dec_ref(v_time_2094_);
return v_minute_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg___boxed(lean_object* v_dt_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Std_Time_DateTime_minute___redArg(v_dt_2096_);
lean_dec_ref(v_dt_2096_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object* v_tz_2098_, lean_object* v_dt_2099_){
_start:
{
lean_object* v_date_2100_; lean_object* v___x_2101_; lean_object* v_time_2102_; lean_object* v_minute_2103_; 
v_date_2100_ = lean_ctor_get(v_dt_2099_, 1);
v___x_2101_ = lean_thunk_get_own(v_date_2100_);
v_time_2102_ = lean_ctor_get(v___x_2101_, 1);
lean_inc_ref(v_time_2102_);
lean_dec(v___x_2101_);
v_minute_2103_ = lean_ctor_get(v_time_2102_, 1);
lean_inc(v_minute_2103_);
lean_dec_ref(v_time_2102_);
return v_minute_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object* v_tz_2104_, lean_object* v_dt_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Std_Time_DateTime_minute(v_tz_2104_, v_dt_2105_);
lean_dec_ref(v_dt_2105_);
lean_dec_ref(v_tz_2104_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg(lean_object* v_dt_2107_){
_start:
{
lean_object* v_date_2108_; lean_object* v___x_2109_; lean_object* v_time_2110_; lean_object* v_second_2111_; 
v_date_2108_ = lean_ctor_get(v_dt_2107_, 1);
v___x_2109_ = lean_thunk_get_own(v_date_2108_);
v_time_2110_ = lean_ctor_get(v___x_2109_, 1);
lean_inc_ref(v_time_2110_);
lean_dec(v___x_2109_);
v_second_2111_ = lean_ctor_get(v_time_2110_, 2);
lean_inc(v_second_2111_);
lean_dec_ref(v_time_2110_);
return v_second_2111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg___boxed(lean_object* v_dt_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Std_Time_DateTime_second___redArg(v_dt_2112_);
lean_dec_ref(v_dt_2112_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object* v_tz_2114_, lean_object* v_dt_2115_){
_start:
{
lean_object* v_date_2116_; lean_object* v___x_2117_; lean_object* v_time_2118_; lean_object* v_second_2119_; 
v_date_2116_ = lean_ctor_get(v_dt_2115_, 1);
v___x_2117_ = lean_thunk_get_own(v_date_2116_);
v_time_2118_ = lean_ctor_get(v___x_2117_, 1);
lean_inc_ref(v_time_2118_);
lean_dec(v___x_2117_);
v_second_2119_ = lean_ctor_get(v_time_2118_, 2);
lean_inc(v_second_2119_);
lean_dec_ref(v_time_2118_);
return v_second_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object* v_tz_2120_, lean_object* v_dt_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Std_Time_DateTime_second(v_tz_2120_, v_dt_2121_);
lean_dec_ref(v_dt_2121_);
lean_dec_ref(v_tz_2120_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg(lean_object* v_dt_2123_){
_start:
{
lean_object* v_date_2124_; lean_object* v___x_2125_; lean_object* v_time_2126_; lean_object* v_nanosecond_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_date_2124_ = lean_ctor_get(v_dt_2123_, 1);
v___x_2125_ = lean_thunk_get_own(v_date_2124_);
v_time_2126_ = lean_ctor_get(v___x_2125_, 1);
lean_inc_ref(v_time_2126_);
lean_dec(v___x_2125_);
v_nanosecond_2127_ = lean_ctor_get(v_time_2126_, 3);
lean_inc(v_nanosecond_2127_);
lean_dec_ref(v_time_2126_);
v___x_2128_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_2129_ = lean_int_emod(v_nanosecond_2127_, v___x_2128_);
lean_dec(v_nanosecond_2127_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg___boxed(lean_object* v_dt_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Std_Time_DateTime_millisecond___redArg(v_dt_2130_);
lean_dec_ref(v_dt_2130_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object* v_tz_2132_, lean_object* v_dt_2133_){
_start:
{
lean_object* v_date_2134_; lean_object* v___x_2135_; lean_object* v_time_2136_; lean_object* v_nanosecond_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_date_2134_ = lean_ctor_get(v_dt_2133_, 1);
v___x_2135_ = lean_thunk_get_own(v_date_2134_);
v_time_2136_ = lean_ctor_get(v___x_2135_, 1);
lean_inc_ref(v_time_2136_);
lean_dec(v___x_2135_);
v_nanosecond_2137_ = lean_ctor_get(v_time_2136_, 3);
lean_inc(v_nanosecond_2137_);
lean_dec_ref(v_time_2136_);
v___x_2138_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_2139_ = lean_int_emod(v_nanosecond_2137_, v___x_2138_);
lean_dec(v_nanosecond_2137_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object* v_tz_2140_, lean_object* v_dt_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Std_Time_DateTime_millisecond(v_tz_2140_, v_dt_2141_);
lean_dec_ref(v_dt_2141_);
lean_dec_ref(v_tz_2140_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg(lean_object* v_dt_2143_){
_start:
{
lean_object* v_date_2144_; lean_object* v___x_2145_; lean_object* v_time_2146_; lean_object* v_nanosecond_2147_; 
v_date_2144_ = lean_ctor_get(v_dt_2143_, 1);
v___x_2145_ = lean_thunk_get_own(v_date_2144_);
v_time_2146_ = lean_ctor_get(v___x_2145_, 1);
lean_inc_ref(v_time_2146_);
lean_dec(v___x_2145_);
v_nanosecond_2147_ = lean_ctor_get(v_time_2146_, 3);
lean_inc(v_nanosecond_2147_);
lean_dec_ref(v_time_2146_);
return v_nanosecond_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg___boxed(lean_object* v_dt_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Std_Time_DateTime_nanosecond___redArg(v_dt_2148_);
lean_dec_ref(v_dt_2148_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object* v_tz_2150_, lean_object* v_dt_2151_){
_start:
{
lean_object* v_date_2152_; lean_object* v___x_2153_; lean_object* v_time_2154_; lean_object* v_nanosecond_2155_; 
v_date_2152_ = lean_ctor_get(v_dt_2151_, 1);
v___x_2153_ = lean_thunk_get_own(v_date_2152_);
v_time_2154_ = lean_ctor_get(v___x_2153_, 1);
lean_inc_ref(v_time_2154_);
lean_dec(v___x_2153_);
v_nanosecond_2155_ = lean_ctor_get(v_time_2154_, 3);
lean_inc(v_nanosecond_2155_);
lean_dec_ref(v_time_2154_);
return v_nanosecond_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object* v_tz_2156_, lean_object* v_dt_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Std_Time_DateTime_nanosecond(v_tz_2156_, v_dt_2157_);
lean_dec_ref(v_dt_2157_);
lean_dec_ref(v_tz_2156_);
return v_res_2158_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday___redArg(lean_object* v_dt_2159_){
_start:
{
lean_object* v_date_2160_; lean_object* v___x_2161_; lean_object* v_date_2162_; uint8_t v___x_2163_; 
v_date_2160_ = lean_ctor_get(v_dt_2159_, 1);
v___x_2161_ = lean_thunk_get_own(v_date_2160_);
v_date_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc_ref(v_date_2162_);
lean_dec(v___x_2161_);
v___x_2163_ = l_Std_Time_PlainDate_weekday(v_date_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___redArg___boxed(lean_object* v_dt_2164_){
_start:
{
uint8_t v_res_2165_; lean_object* v_r_2166_; 
v_res_2165_ = l_Std_Time_DateTime_weekday___redArg(v_dt_2164_);
lean_dec_ref(v_dt_2164_);
v_r_2166_ = lean_box(v_res_2165_);
return v_r_2166_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object* v_tz_2167_, lean_object* v_dt_2168_){
_start:
{
lean_object* v_date_2169_; lean_object* v___x_2170_; lean_object* v_date_2171_; uint8_t v___x_2172_; 
v_date_2169_ = lean_ctor_get(v_dt_2168_, 1);
v___x_2170_ = lean_thunk_get_own(v_date_2169_);
v_date_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc_ref(v_date_2171_);
lean_dec(v___x_2170_);
v___x_2172_ = l_Std_Time_PlainDate_weekday(v_date_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object* v_tz_2173_, lean_object* v_dt_2174_){
_start:
{
uint8_t v_res_2175_; lean_object* v_r_2176_; 
v_res_2175_ = l_Std_Time_DateTime_weekday(v_tz_2173_, v_dt_2174_);
lean_dec_ref(v_dt_2174_);
lean_dec_ref(v_tz_2173_);
v_r_2176_ = lean_box(v_res_2175_);
return v_r_2176_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era___redArg(lean_object* v_date_2177_){
_start:
{
lean_object* v_date_2178_; lean_object* v___x_2179_; lean_object* v_date_2180_; lean_object* v_year_2181_; uint8_t v___x_2182_; 
v_date_2178_ = lean_ctor_get(v_date_2177_, 1);
v___x_2179_ = lean_thunk_get_own(v_date_2178_);
v_date_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc_ref(v_date_2180_);
lean_dec(v___x_2179_);
v_year_2181_ = lean_ctor_get(v_date_2180_, 0);
lean_inc(v_year_2181_);
lean_dec_ref(v_date_2180_);
v___x_2182_ = l_Std_Time_Year_Offset_era(v_year_2181_);
lean_dec(v_year_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___redArg___boxed(lean_object* v_date_2183_){
_start:
{
uint8_t v_res_2184_; lean_object* v_r_2185_; 
v_res_2184_ = l_Std_Time_DateTime_era___redArg(v_date_2183_);
lean_dec_ref(v_date_2183_);
v_r_2185_ = lean_box(v_res_2184_);
return v_r_2185_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object* v_tz_2186_, lean_object* v_date_2187_){
_start:
{
uint8_t v___x_2188_; 
v___x_2188_ = l_Std_Time_DateTime_era___redArg(v_date_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object* v_tz_2189_, lean_object* v_date_2190_){
_start:
{
uint8_t v_res_2191_; lean_object* v_r_2192_; 
v_res_2191_ = l_Std_Time_DateTime_era(v_tz_2189_, v_date_2190_);
lean_dec_ref(v_date_2190_);
lean_dec_ref(v_tz_2189_);
v_r_2192_ = lean_box(v_res_2191_);
return v_r_2192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object* v_tz_2193_, lean_object* v_dt_2194_, uint8_t v_desiredWeekday_2195_){
_start:
{
lean_object* v_date_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2225_; 
v_date_2196_ = lean_ctor_get(v_dt_2194_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_dt_2194_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v_dt_2194_, 0);
lean_dec(v_unused_2226_);
v___x_2198_ = v_dt_2194_;
v_isShared_2199_ = v_isSharedCheck_2225_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_date_2196_);
lean_dec(v_dt_2194_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2225_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_second_2203_; lean_object* v_nano_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v_second_2210_; lean_object* v_nano_2211_; lean_object* v___f_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_tm_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2200_ = lean_thunk_get_own(v_date_2196_);
lean_dec_ref(v_date_2196_);
v___x_2201_ = l_Std_Time_PlainDateTime_withWeekday(v___x_2200_, v_desiredWeekday_2195_);
lean_inc_ref(v___x_2201_);
v___x_2202_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2201_);
v_second_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_second_2203_);
v_nano_2204_ = lean_ctor_get(v___x_2202_, 1);
lean_inc(v_nano_2204_);
lean_dec_ref(v___x_2202_);
v___x_2205_ = l_Std_Time_TimeZone_toSeconds(v_tz_2193_);
v___x_2206_ = lean_int_neg(v___x_2205_);
lean_dec(v___x_2205_);
v___x_2207_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_2208_ = lean_int_mul(v___x_2206_, v___x_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = l_Std_Time_Duration_ofNanoseconds(v___x_2208_);
lean_dec(v___x_2208_);
v_second_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_second_2210_);
v_nano_2211_ = lean_ctor_get(v___x_2209_, 1);
lean_inc(v_nano_2211_);
lean_dec_ref(v___x_2209_);
v___f_2212_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2212_, 0, v___x_2201_);
v___x_2213_ = lean_int_mul(v_second_2203_, v___x_2207_);
lean_dec(v_second_2203_);
v___x_2214_ = lean_int_add(v___x_2213_, v_nano_2204_);
lean_dec(v_nano_2204_);
lean_dec(v___x_2213_);
v___x_2215_ = lean_int_mul(v_second_2210_, v___x_2207_);
lean_dec(v_second_2210_);
v___x_2216_ = lean_int_add(v___x_2215_, v_nano_2211_);
lean_dec(v_nano_2211_);
lean_dec(v___x_2215_);
v___x_2217_ = lean_int_add(v___x_2214_, v___x_2216_);
lean_dec(v___x_2216_);
lean_dec(v___x_2214_);
v___x_2218_ = l_Std_Time_Duration_ofNanoseconds(v___x_2217_);
lean_dec(v___x_2217_);
v_tm_2219_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_2218_);
v___x_2220_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_2219_);
v___x_2221_ = lean_mk_thunk(v___f_2212_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v___x_2221_);
lean_ctor_set(v___x_2198_, 0, v___x_2220_);
v___x_2223_ = v___x_2198_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v___x_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object* v_tz_2227_, lean_object* v_dt_2228_, lean_object* v_desiredWeekday_2229_){
_start:
{
uint8_t v_desiredWeekday_boxed_2230_; lean_object* v_res_2231_; 
v_desiredWeekday_boxed_2230_ = lean_unbox(v_desiredWeekday_2229_);
v_res_2231_ = l_Std_Time_DateTime_withWeekday(v_tz_2227_, v_dt_2228_, v_desiredWeekday_boxed_2230_);
lean_dec_ref(v_tz_2227_);
return v_res_2231_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear___redArg(lean_object* v_date_2232_){
_start:
{
lean_object* v_date_2233_; lean_object* v___x_2234_; lean_object* v_date_2235_; lean_object* v_year_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2244_; 
v_date_2233_ = lean_ctor_get(v_date_2232_, 1);
v___x_2234_ = lean_thunk_get_own(v_date_2233_);
v_date_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_ref(v_date_2235_);
lean_dec(v___x_2234_);
v_year_2236_ = lean_ctor_get(v_date_2235_, 0);
lean_inc(v_year_2236_);
lean_dec_ref(v_date_2235_);
v___x_2237_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_2238_ = lean_int_mod(v_year_2236_, v___x_2237_);
v___x_2239_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_2244_ = lean_int_dec_eq(v___x_2238_, v___x_2239_);
lean_dec(v___x_2238_);
if (v___x_2244_ == 0)
{
lean_dec(v_year_2236_);
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2246_; uint8_t v___x_2247_; 
v___x_2245_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
v___x_2246_ = lean_int_mod(v_year_2236_, v___x_2245_);
v___x_2247_ = lean_int_dec_eq(v___x_2246_, v___x_2239_);
lean_dec(v___x_2246_);
if (v___x_2247_ == 0)
{
if (v___x_2244_ == 0)
{
goto v___jp_2240_;
}
else
{
lean_dec(v_year_2236_);
return v___x_2244_;
}
}
else
{
goto v___jp_2240_;
}
}
v___jp_2240_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2241_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_2242_ = lean_int_mod(v_year_2236_, v___x_2241_);
lean_dec(v_year_2236_);
v___x_2243_ = lean_int_dec_eq(v___x_2242_, v___x_2239_);
lean_dec(v___x_2242_);
return v___x_2243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___redArg___boxed(lean_object* v_date_2248_){
_start:
{
uint8_t v_res_2249_; lean_object* v_r_2250_; 
v_res_2249_ = l_Std_Time_DateTime_inLeapYear___redArg(v_date_2248_);
lean_dec_ref(v_date_2248_);
v_r_2250_ = lean_box(v_res_2249_);
return v_r_2250_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object* v_tz_2251_, lean_object* v_date_2252_){
_start:
{
uint8_t v___x_2253_; 
v___x_2253_ = l_Std_Time_DateTime_inLeapYear___redArg(v_date_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object* v_tz_2254_, lean_object* v_date_2255_){
_start:
{
uint8_t v_res_2256_; lean_object* v_r_2257_; 
v_res_2256_ = l_Std_Time_DateTime_inLeapYear(v_tz_2254_, v_date_2255_);
lean_dec_ref(v_date_2255_);
lean_dec_ref(v_tz_2254_);
v_r_2257_ = lean_box(v_res_2256_);
return v_r_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg(lean_object* v_date_2258_){
_start:
{
lean_object* v_date_2259_; uint8_t v___y_2261_; lean_object* v___x_2275_; lean_object* v_date_2276_; lean_object* v_year_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2285_; 
v_date_2259_ = lean_ctor_get(v_date_2258_, 1);
v___x_2275_ = lean_thunk_get_own(v_date_2259_);
v_date_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc_ref(v_date_2276_);
lean_dec(v___x_2275_);
v_year_2277_ = lean_ctor_get(v_date_2276_, 0);
lean_inc(v_year_2277_);
lean_dec_ref(v_date_2276_);
v___x_2278_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_2279_ = lean_int_mod(v_year_2277_, v___x_2278_);
v___x_2280_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_2285_ = lean_int_dec_eq(v___x_2279_, v___x_2280_);
lean_dec(v___x_2279_);
if (v___x_2285_ == 0)
{
lean_dec(v_year_2277_);
v___y_2261_ = v___x_2285_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v___x_2286_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
v___x_2287_ = lean_int_mod(v_year_2277_, v___x_2286_);
v___x_2288_ = lean_int_dec_eq(v___x_2287_, v___x_2280_);
lean_dec(v___x_2287_);
if (v___x_2288_ == 0)
{
if (v___x_2285_ == 0)
{
goto v___jp_2281_;
}
else
{
lean_dec(v_year_2277_);
v___y_2261_ = v___x_2285_;
goto v___jp_2260_;
}
}
else
{
goto v___jp_2281_;
}
}
v___jp_2260_:
{
lean_object* v___x_2262_; lean_object* v_date_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2273_; 
v___x_2262_ = lean_thunk_get_own(v_date_2259_);
v_date_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2273_ == 0)
{
lean_object* v_unused_2274_; 
v_unused_2274_ = lean_ctor_get(v___x_2262_, 1);
lean_dec(v_unused_2274_);
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2273_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_date_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2273_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v_month_2267_; lean_object* v_day_2268_; lean_object* v___x_2270_; 
v_month_2267_ = lean_ctor_get(v_date_2263_, 1);
lean_inc(v_month_2267_);
v_day_2268_ = lean_ctor_get(v_date_2263_, 2);
lean_inc(v_day_2268_);
lean_dec_ref(v_date_2263_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 1, v_day_2268_);
lean_ctor_set(v___x_2265_, 0, v_month_2267_);
v___x_2270_ = v___x_2265_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_month_2267_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v_day_2268_);
v___x_2270_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Std_Time_ValidDate_dayOfYear(v___y_2261_, v___x_2270_);
lean_dec_ref(v___x_2270_);
return v___x_2271_;
}
}
}
v___jp_2281_:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2282_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_2283_ = lean_int_mod(v_year_2277_, v___x_2282_);
lean_dec(v_year_2277_);
v___x_2284_ = lean_int_dec_eq(v___x_2283_, v___x_2280_);
lean_dec(v___x_2283_);
v___y_2261_ = v___x_2284_;
goto v___jp_2260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg___boxed(lean_object* v_date_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Std_Time_DateTime_dayOfYear___redArg(v_date_2289_);
lean_dec_ref(v_date_2289_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object* v_tz_2291_, lean_object* v_date_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Std_Time_DateTime_dayOfYear___redArg(v_date_2292_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object* v_tz_2294_, lean_object* v_date_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Std_Time_DateTime_dayOfYear(v_tz_2294_, v_date_2295_);
lean_dec_ref(v_date_2295_);
lean_dec_ref(v_tz_2294_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg(lean_object* v_date_2297_){
_start:
{
lean_object* v_date_2298_; lean_object* v___x_2299_; lean_object* v_date_2300_; lean_object* v___x_2301_; 
v_date_2298_ = lean_ctor_get(v_date_2297_, 1);
v___x_2299_ = lean_thunk_get_own(v_date_2298_);
v_date_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc_ref(v_date_2300_);
lean_dec(v___x_2299_);
v___x_2301_ = l_Std_Time_PlainDate_weekOfYear(v_date_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg___boxed(lean_object* v_date_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Std_Time_DateTime_weekOfYear___redArg(v_date_2302_);
lean_dec_ref(v_date_2302_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* v_tz_2304_, lean_object* v_date_2305_){
_start:
{
lean_object* v_date_2306_; lean_object* v___x_2307_; lean_object* v_date_2308_; lean_object* v___x_2309_; 
v_date_2306_ = lean_ctor_get(v_date_2305_, 1);
v___x_2307_ = lean_thunk_get_own(v_date_2306_);
v_date_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc_ref(v_date_2308_);
lean_dec(v___x_2307_);
v___x_2309_ = l_Std_Time_PlainDate_weekOfYear(v_date_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object* v_tz_2310_, lean_object* v_date_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Std_Time_DateTime_weekOfYear(v_tz_2310_, v_date_2311_);
lean_dec_ref(v_date_2311_);
lean_dec_ref(v_tz_2310_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg(lean_object* v_date_2313_){
_start:
{
lean_object* v_date_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v_date_2314_ = lean_ctor_get(v_date_2313_, 1);
v___x_2315_ = lean_thunk_get_own(v_date_2314_);
v___x_2316_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_2315_);
lean_dec(v___x_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg___boxed(lean_object* v_date_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Std_Time_DateTime_weekOfMonth___redArg(v_date_2317_);
lean_dec_ref(v_date_2317_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* v_tz_2319_, lean_object* v_date_2320_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Std_Time_DateTime_weekOfMonth___redArg(v_date_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object* v_tz_2322_, lean_object* v_date_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Std_Time_DateTime_weekOfMonth(v_tz_2322_, v_date_2323_);
lean_dec_ref(v_date_2323_);
lean_dec_ref(v_tz_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg(lean_object* v_date_2325_){
_start:
{
lean_object* v_date_2326_; lean_object* v___x_2327_; lean_object* v_date_2328_; lean_object* v___x_2329_; 
v_date_2326_ = lean_ctor_get(v_date_2325_, 1);
v___x_2327_ = lean_thunk_get_own(v_date_2326_);
v_date_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc_ref(v_date_2328_);
lean_dec(v___x_2327_);
v___x_2329_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg___boxed(lean_object* v_date_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Std_Time_DateTime_alignedWeekOfMonth___redArg(v_date_2330_);
lean_dec_ref(v_date_2330_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* v_tz_2332_, lean_object* v_date_2333_){
_start:
{
lean_object* v_date_2334_; lean_object* v___x_2335_; lean_object* v_date_2336_; lean_object* v___x_2337_; 
v_date_2334_ = lean_ctor_get(v_date_2333_, 1);
v___x_2335_ = lean_thunk_get_own(v_date_2334_);
v_date_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc_ref(v_date_2336_);
lean_dec(v___x_2335_);
v___x_2337_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object* v_tz_2338_, lean_object* v_date_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_tz_2338_, v_date_2339_);
lean_dec_ref(v_date_2339_);
lean_dec_ref(v_tz_2338_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg(lean_object* v_date_2341_){
_start:
{
lean_object* v_date_2342_; lean_object* v___x_2343_; lean_object* v_date_2344_; lean_object* v___x_2345_; 
v_date_2342_ = lean_ctor_get(v_date_2341_, 1);
v___x_2343_ = lean_thunk_get_own(v_date_2342_);
v_date_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc_ref(v_date_2344_);
lean_dec(v___x_2343_);
v___x_2345_ = l_Std_Time_PlainDate_quarter(v_date_2344_);
lean_dec_ref(v_date_2344_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg___boxed(lean_object* v_date_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Std_Time_DateTime_quarter___redArg(v_date_2346_);
lean_dec_ref(v_date_2346_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* v_tz_2348_, lean_object* v_date_2349_){
_start:
{
lean_object* v_date_2350_; lean_object* v___x_2351_; lean_object* v_date_2352_; lean_object* v___x_2353_; 
v_date_2350_ = lean_ctor_get(v_date_2349_, 1);
v___x_2351_ = lean_thunk_get_own(v_date_2350_);
v_date_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc_ref(v_date_2352_);
lean_dec(v___x_2351_);
v___x_2353_ = l_Std_Time_PlainDate_quarter(v_date_2352_);
lean_dec_ref(v_date_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object* v_tz_2354_, lean_object* v_date_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_Std_Time_DateTime_quarter(v_tz_2354_, v_date_2355_);
lean_dec_ref(v_date_2355_);
lean_dec_ref(v_tz_2354_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg(lean_object* v_zdt_2357_){
_start:
{
lean_object* v_date_2358_; lean_object* v___x_2359_; lean_object* v_time_2360_; 
v_date_2358_ = lean_ctor_get(v_zdt_2357_, 1);
v___x_2359_ = lean_thunk_get_own(v_date_2358_);
v_time_2360_ = lean_ctor_get(v___x_2359_, 1);
lean_inc_ref(v_time_2360_);
lean_dec(v___x_2359_);
return v_time_2360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg___boxed(lean_object* v_zdt_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Std_Time_DateTime_time___redArg(v_zdt_2361_);
lean_dec_ref(v_zdt_2361_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object* v_tz_2363_, lean_object* v_zdt_2364_){
_start:
{
lean_object* v_date_2365_; lean_object* v___x_2366_; lean_object* v_time_2367_; 
v_date_2365_ = lean_ctor_get(v_zdt_2364_, 1);
v___x_2366_ = lean_thunk_get_own(v_date_2365_);
v_time_2367_ = lean_ctor_get(v___x_2366_, 1);
lean_inc_ref(v_time_2367_);
lean_dec(v___x_2366_);
return v_time_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object* v_tz_2368_, lean_object* v_zdt_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Std_Time_DateTime_time(v_tz_2368_, v_zdt_2369_);
lean_dec_ref(v_zdt_2369_);
lean_dec_ref(v_tz_2368_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch(lean_object* v_days_2371_, lean_object* v_time_2372_, lean_object* v_tz_2373_){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_second_2377_; lean_object* v_nano_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v_second_2384_; lean_object* v_nano_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2402_; 
v___x_2374_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v_days_2371_);
v___x_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
lean_ctor_set(v___x_2375_, 1, v_time_2372_);
lean_inc_ref(v___x_2375_);
v___x_2376_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2375_);
v_second_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_second_2377_);
v_nano_2378_ = lean_ctor_get(v___x_2376_, 1);
lean_inc(v_nano_2378_);
lean_dec_ref(v___x_2376_);
v___x_2379_ = l_Std_Time_TimeZone_toSeconds(v_tz_2373_);
v___x_2380_ = lean_int_neg(v___x_2379_);
lean_dec(v___x_2379_);
v___x_2381_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_2382_ = lean_int_mul(v___x_2380_, v___x_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = l_Std_Time_Duration_ofNanoseconds(v___x_2382_);
lean_dec(v___x_2382_);
v_second_2384_ = lean_ctor_get(v___x_2383_, 0);
v_nano_2385_ = lean_ctor_get(v___x_2383_, 1);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2387_ = v___x_2383_;
v_isShared_2388_ = v_isSharedCheck_2402_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_nano_2385_);
lean_inc(v_second_2384_);
lean_dec(v___x_2383_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2402_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___f_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v_tm_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___f_2389_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2389_, 0, v___x_2375_);
v___x_2390_ = lean_int_mul(v_second_2377_, v___x_2381_);
lean_dec(v_second_2377_);
v___x_2391_ = lean_int_add(v___x_2390_, v_nano_2378_);
lean_dec(v_nano_2378_);
lean_dec(v___x_2390_);
v___x_2392_ = lean_int_mul(v_second_2384_, v___x_2381_);
lean_dec(v_second_2384_);
v___x_2393_ = lean_int_add(v___x_2392_, v_nano_2385_);
lean_dec(v_nano_2385_);
lean_dec(v___x_2392_);
v___x_2394_ = lean_int_add(v___x_2391_, v___x_2393_);
lean_dec(v___x_2393_);
lean_dec(v___x_2391_);
v___x_2395_ = l_Std_Time_Duration_ofNanoseconds(v___x_2394_);
lean_dec(v___x_2394_);
v_tm_2396_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_2395_);
v___x_2397_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_2396_);
v___x_2398_ = lean_mk_thunk(v___f_2389_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 1, v___x_2398_);
lean_ctor_set(v___x_2387_, 0, v___x_2397_);
v___x_2400_ = v___x_2387_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofDaysSinceUNIXEpoch___boxed(lean_object* v_days_2403_, lean_object* v_time_2404_, lean_object* v_tz_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Std_Time_DateTime_ofDaysSinceUNIXEpoch(v_days_2403_, v_time_2404_, v_tz_2405_);
lean_dec_ref(v_tz_2405_);
lean_dec(v_days_2403_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset(lean_object* v_tz_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___boxed), 3, 1);
lean_closure_set(v___x_2408_, 0, v_tz_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset(lean_object* v_tz_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subDays___boxed), 3, 1);
lean_closure_set(v___x_2410_, 0, v_tz_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__1(lean_object* v_tz_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addWeeks___boxed), 3, 1);
lean_closure_set(v___x_2412_, 0, v_tz_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__1(lean_object* v_tz_2413_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subWeeks___boxed), 3, 1);
lean_closure_set(v___x_2414_, 0, v_tz_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__2(lean_object* v_tz_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___boxed), 3, 1);
lean_closure_set(v___x_2416_, 0, v_tz_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__2(lean_object* v_tz_2417_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subHours___boxed), 3, 1);
lean_closure_set(v___x_2418_, 0, v_tz_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__3(lean_object* v_tz_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMinutes___boxed), 3, 1);
lean_closure_set(v___x_2420_, 0, v_tz_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__3(lean_object* v_tz_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subMinutes___boxed), 3, 1);
lean_closure_set(v___x_2422_, 0, v_tz_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__4(lean_object* v_tz_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addSeconds___boxed), 3, 1);
lean_closure_set(v___x_2424_, 0, v_tz_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__4(lean_object* v_tz_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subSeconds___boxed), 3, 1);
lean_closure_set(v___x_2426_, 0, v_tz_2425_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__5(lean_object* v_tz_2427_){
_start:
{
lean_object* v___x_2428_; 
v___x_2428_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___boxed), 3, 1);
lean_closure_set(v___x_2428_, 0, v_tz_2427_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__5(lean_object* v_tz_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subMilliseconds___boxed), 3, 1);
lean_closure_set(v___x_2430_, 0, v_tz_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__6(lean_object* v_tz_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addNanoseconds___boxed), 3, 1);
lean_closure_set(v___x_2432_, 0, v_tz_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__6(lean_object* v_tz_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subNanoseconds___boxed), 3, 1);
lean_closure_set(v___x_2434_, 0, v_tz_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object* v_x_2435_, lean_object* v_y_2436_){
_start:
{
lean_object* v_timestamp_2437_; lean_object* v_timestamp_2438_; lean_object* v_second_2439_; lean_object* v_nano_2440_; lean_object* v_second_2441_; lean_object* v_nano_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_timestamp_2437_ = lean_ctor_get(v_y_2436_, 0);
v_timestamp_2438_ = lean_ctor_get(v_x_2435_, 0);
v_second_2439_ = lean_ctor_get(v_timestamp_2437_, 0);
v_nano_2440_ = lean_ctor_get(v_timestamp_2437_, 1);
v_second_2441_ = lean_ctor_get(v_timestamp_2438_, 0);
v_nano_2442_ = lean_ctor_get(v_timestamp_2438_, 1);
v___x_2443_ = lean_int_neg(v_second_2439_);
v___x_2444_ = lean_int_neg(v_nano_2440_);
v___x_2445_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_2446_ = lean_int_mul(v_second_2441_, v___x_2445_);
v___x_2447_ = lean_int_add(v___x_2446_, v_nano_2442_);
lean_dec(v___x_2446_);
v___x_2448_ = lean_int_mul(v___x_2443_, v___x_2445_);
lean_dec(v___x_2443_);
v___x_2449_ = lean_int_add(v___x_2448_, v___x_2444_);
lean_dec(v___x_2444_);
lean_dec(v___x_2448_);
v___x_2450_ = lean_int_add(v___x_2447_, v___x_2449_);
lean_dec(v___x_2449_);
lean_dec(v___x_2447_);
v___x_2451_ = l_Std_Time_Duration_ofNanoseconds(v___x_2450_);
lean_dec(v___x_2450_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object* v_x_2452_, lean_object* v_y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Std_Time_DateTime_instHSubDuration___lam__0(v_x_2452_, v_y_2453_);
lean_dec_ref(v_y_2453_);
lean_dec_ref(v_x_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration(lean_object* v_tz_2456_, lean_object* v_tz_u2081_2457_){
_start:
{
lean_object* v___f_2458_; 
v___f_2458_ = ((lean_object*)(l_Std_Time_DateTime_instHSubDuration___closed__0));
return v___f_2458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___boxed(lean_object* v_tz_2459_, lean_object* v_tz_u2081_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Std_Time_DateTime_instHSubDuration(v_tz_2459_, v_tz_u2081_2460_);
lean_dec_ref(v_tz_u2081_2460_);
lean_dec_ref(v_tz_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1(lean_object* v_tz_2462_, lean_object* v_x_2463_, lean_object* v_y_2464_){
_start:
{
lean_object* v_second_2465_; lean_object* v_nano_2466_; lean_object* v_date_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2510_; 
v_second_2465_ = lean_ctor_get(v_y_2464_, 0);
v_nano_2466_ = lean_ctor_get(v_y_2464_, 1);
v_date_2467_ = lean_ctor_get(v_x_2463_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_x_2463_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; 
v_unused_2511_ = lean_ctor_get(v_x_2463_, 0);
lean_dec(v_unused_2511_);
v___x_2469_ = v_x_2463_;
v_isShared_2470_ = v_isSharedCheck_2510_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_date_2467_);
lean_dec(v_x_2463_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2510_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_second_2473_; lean_object* v_nano_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v_nanos_2477_; lean_object* v___x_2478_; lean_object* v_second_2479_; lean_object* v_nano_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_second_2489_; lean_object* v_nano_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v_second_2495_; lean_object* v_nano_2496_; lean_object* v___f_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v_tm_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2471_ = lean_thunk_get_own(v_date_2467_);
lean_dec_ref(v_date_2467_);
v___x_2472_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2471_);
v_second_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_second_2473_);
v_nano_2474_ = lean_ctor_get(v___x_2472_, 1);
lean_inc(v_nano_2474_);
lean_dec_ref(v___x_2472_);
v___x_2475_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_2476_ = lean_int_mul(v_second_2465_, v___x_2475_);
v_nanos_2477_ = lean_int_add(v___x_2476_, v_nano_2466_);
lean_dec(v___x_2476_);
v___x_2478_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_2477_);
lean_dec(v_nanos_2477_);
v_second_2479_ = lean_ctor_get(v___x_2478_, 0);
lean_inc(v_second_2479_);
v_nano_2480_ = lean_ctor_get(v___x_2478_, 1);
lean_inc(v_nano_2480_);
lean_dec_ref(v___x_2478_);
v___x_2481_ = lean_int_mul(v_second_2473_, v___x_2475_);
lean_dec(v_second_2473_);
v___x_2482_ = lean_int_add(v___x_2481_, v_nano_2474_);
lean_dec(v_nano_2474_);
lean_dec(v___x_2481_);
v___x_2483_ = lean_int_mul(v_second_2479_, v___x_2475_);
lean_dec(v_second_2479_);
v___x_2484_ = lean_int_add(v___x_2483_, v_nano_2480_);
lean_dec(v_nano_2480_);
lean_dec(v___x_2483_);
v___x_2485_ = lean_int_add(v___x_2482_, v___x_2484_);
lean_dec(v___x_2484_);
lean_dec(v___x_2482_);
v___x_2486_ = l_Std_Time_Duration_ofNanoseconds(v___x_2485_);
lean_dec(v___x_2485_);
v___x_2487_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_2486_);
lean_inc_ref(v___x_2487_);
v___x_2488_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2487_);
v_second_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_second_2489_);
v_nano_2490_ = lean_ctor_get(v___x_2488_, 1);
lean_inc(v_nano_2490_);
lean_dec_ref(v___x_2488_);
v___x_2491_ = l_Std_Time_TimeZone_toSeconds(v_tz_2462_);
v___x_2492_ = lean_int_neg(v___x_2491_);
lean_dec(v___x_2491_);
v___x_2493_ = lean_int_mul(v___x_2492_, v___x_2475_);
lean_dec(v___x_2492_);
v___x_2494_ = l_Std_Time_Duration_ofNanoseconds(v___x_2493_);
lean_dec(v___x_2493_);
v_second_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_second_2495_);
v_nano_2496_ = lean_ctor_get(v___x_2494_, 1);
lean_inc(v_nano_2496_);
lean_dec_ref(v___x_2494_);
v___f_2497_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2497_, 0, v___x_2487_);
v___x_2498_ = lean_int_mul(v_second_2489_, v___x_2475_);
lean_dec(v_second_2489_);
v___x_2499_ = lean_int_add(v___x_2498_, v_nano_2490_);
lean_dec(v_nano_2490_);
lean_dec(v___x_2498_);
v___x_2500_ = lean_int_mul(v_second_2495_, v___x_2475_);
lean_dec(v_second_2495_);
v___x_2501_ = lean_int_add(v___x_2500_, v_nano_2496_);
lean_dec(v_nano_2496_);
lean_dec(v___x_2500_);
v___x_2502_ = lean_int_add(v___x_2499_, v___x_2501_);
lean_dec(v___x_2501_);
lean_dec(v___x_2499_);
v___x_2503_ = l_Std_Time_Duration_ofNanoseconds(v___x_2502_);
lean_dec(v___x_2502_);
v_tm_2504_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_2503_);
v___x_2505_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_2504_);
v___x_2506_ = lean_mk_thunk(v___f_2497_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 1, v___x_2506_);
lean_ctor_set(v___x_2469_, 0, v___x_2505_);
v___x_2508_ = v___x_2469_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2505_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v___x_2506_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1___boxed(lean_object* v_tz_2512_, lean_object* v_x_2513_, lean_object* v_y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_Std_Time_DateTime_instHAddDuration___lam__1(v_tz_2512_, v_x_2513_, v_y_2514_);
lean_dec_ref(v_y_2514_);
lean_dec_ref(v_tz_2512_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration(lean_object* v_tz_2516_){
_start:
{
lean_object* v___f_2517_; 
v___f_2517_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHAddDuration___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2517_, 0, v_tz_2516_);
return v___f_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1(lean_object* v_tz_2518_, lean_object* v_x_2519_, lean_object* v_y_2520_){
_start:
{
lean_object* v_second_2521_; lean_object* v_nano_2522_; lean_object* v_date_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2567_; 
v_second_2521_ = lean_ctor_get(v_y_2520_, 0);
v_nano_2522_ = lean_ctor_get(v_y_2520_, 1);
v_date_2523_ = lean_ctor_get(v_x_2519_, 1);
v_isSharedCheck_2567_ = !lean_is_exclusive(v_x_2519_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; 
v_unused_2568_ = lean_ctor_get(v_x_2519_, 0);
lean_dec(v_unused_2568_);
v___x_2525_ = v_x_2519_;
v_isShared_2526_ = v_isSharedCheck_2567_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_date_2523_);
lean_dec(v_x_2519_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2567_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v_second_2529_; lean_object* v_nano_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v_nanos_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_second_2536_; lean_object* v_nano_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v_second_2546_; lean_object* v_nano_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v_second_2552_; lean_object* v_nano_2553_; lean_object* v___f_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v_tm_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2565_; 
v___x_2527_ = lean_thunk_get_own(v_date_2523_);
lean_dec_ref(v_date_2523_);
v___x_2528_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2527_);
v_second_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_second_2529_);
v_nano_2530_ = lean_ctor_get(v___x_2528_, 1);
lean_inc(v_nano_2530_);
lean_dec_ref(v___x_2528_);
v___x_2531_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_2532_ = lean_int_mul(v_second_2521_, v___x_2531_);
v_nanos_2533_ = lean_int_add(v___x_2532_, v_nano_2522_);
lean_dec(v___x_2532_);
v___x_2534_ = lean_int_neg(v_nanos_2533_);
lean_dec(v_nanos_2533_);
v___x_2535_ = l_Std_Time_Duration_ofNanoseconds(v___x_2534_);
lean_dec(v___x_2534_);
v_second_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_second_2536_);
v_nano_2537_ = lean_ctor_get(v___x_2535_, 1);
lean_inc(v_nano_2537_);
lean_dec_ref(v___x_2535_);
v___x_2538_ = lean_int_mul(v_second_2529_, v___x_2531_);
lean_dec(v_second_2529_);
v___x_2539_ = lean_int_add(v___x_2538_, v_nano_2530_);
lean_dec(v_nano_2530_);
lean_dec(v___x_2538_);
v___x_2540_ = lean_int_mul(v_second_2536_, v___x_2531_);
lean_dec(v_second_2536_);
v___x_2541_ = lean_int_add(v___x_2540_, v_nano_2537_);
lean_dec(v_nano_2537_);
lean_dec(v___x_2540_);
v___x_2542_ = lean_int_add(v___x_2539_, v___x_2541_);
lean_dec(v___x_2541_);
lean_dec(v___x_2539_);
v___x_2543_ = l_Std_Time_Duration_ofNanoseconds(v___x_2542_);
lean_dec(v___x_2542_);
v___x_2544_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_2543_);
lean_inc_ref(v___x_2544_);
v___x_2545_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2544_);
v_second_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_second_2546_);
v_nano_2547_ = lean_ctor_get(v___x_2545_, 1);
lean_inc(v_nano_2547_);
lean_dec_ref(v___x_2545_);
v___x_2548_ = l_Std_Time_TimeZone_toSeconds(v_tz_2518_);
v___x_2549_ = lean_int_neg(v___x_2548_);
lean_dec(v___x_2548_);
v___x_2550_ = lean_int_mul(v___x_2549_, v___x_2531_);
lean_dec(v___x_2549_);
v___x_2551_ = l_Std_Time_Duration_ofNanoseconds(v___x_2550_);
lean_dec(v___x_2550_);
v_second_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_second_2552_);
v_nano_2553_ = lean_ctor_get(v___x_2551_, 1);
lean_inc(v_nano_2553_);
lean_dec_ref(v___x_2551_);
v___f_2554_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2554_, 0, v___x_2544_);
v___x_2555_ = lean_int_mul(v_second_2546_, v___x_2531_);
lean_dec(v_second_2546_);
v___x_2556_ = lean_int_add(v___x_2555_, v_nano_2547_);
lean_dec(v_nano_2547_);
lean_dec(v___x_2555_);
v___x_2557_ = lean_int_mul(v_second_2552_, v___x_2531_);
lean_dec(v_second_2552_);
v___x_2558_ = lean_int_add(v___x_2557_, v_nano_2553_);
lean_dec(v_nano_2553_);
lean_dec(v___x_2557_);
v___x_2559_ = lean_int_add(v___x_2556_, v___x_2558_);
lean_dec(v___x_2558_);
lean_dec(v___x_2556_);
v___x_2560_ = l_Std_Time_Duration_ofNanoseconds(v___x_2559_);
lean_dec(v___x_2559_);
v_tm_2561_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_2560_);
v___x_2562_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_2561_);
v___x_2563_ = lean_mk_thunk(v___f_2554_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 1, v___x_2563_);
lean_ctor_set(v___x_2525_, 0, v___x_2562_);
v___x_2565_ = v___x_2525_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2562_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v___x_2563_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed(lean_object* v_tz_2569_, lean_object* v_x_2570_, lean_object* v_y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Std_Time_DateTime_instHSubDuration__1___lam__1(v_tz_2569_, v_x_2570_, v_y_2571_);
lean_dec_ref(v_y_2571_);
lean_dec_ref(v_tz_2569_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1(lean_object* v_tz_2573_){
_start:
{
lean_object* v___f_2574_; 
v___f_2574_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2574_, 0, v_tz_2573_);
return v___f_2574_;
}
}
lean_object* runtime_initialize_Std_Time_DateTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Year(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Year(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_DateTime(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Year(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Month(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Year(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_DateTime(builtin);
}
#ifdef __cplusplus
}
#endif

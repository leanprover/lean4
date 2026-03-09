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
uint8_t l_Std_Time_instDecidableEqDuration_decEq(lean_object*, lean_object*);
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
extern lean_object* l_Std_Time_instOrdTimestamp;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_instOrdDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdDateTime___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Time_instInhabitedTimestamp_default;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
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
lean_object* lean_int_neg(lean_object*);
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
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
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
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
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
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_int_emod(lean_object*, lean_object*);
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
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_instBEqDateTime___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Std_Time_instDecidableEqDuration_decEq(x_3, x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_instBEqDateTime(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_Std_Time_instBEqDateTime___closed__0));
return x_2;
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
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instOrdDateTime___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instOrdDateTime___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Time_instOrdDateTime___closed__0));
x_2 = l_Std_Time_instOrdTimestamp;
x_3 = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_2);
lean_closure_set(x_3, 3, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdDateTime(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Std_Time_instOrdDateTime___closed__1, &l_Std_Time_instOrdDateTime___closed__1_once, _init_l_Std_Time_instOrdDateTime___closed__1);
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
static lean_object* _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0(void) {
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
x_9 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_ofTimestamp___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
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
x_9 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_instInhabited___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Std_Time_instInhabitedTimestamp_default;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDaysSinceUNIXEpoch(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_toDaysSinceUNIXEpoch___redArg(x_2);
return x_3;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toTimestamp___redArg(x_1);
lean_dec_ref(x_1);
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
x_9 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_12; 
x_3 = lean_ctor_get(x_1, 0);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_4 = x_1;
x_5 = x_12;
goto block_11;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_3);
x_6 = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_mk_thunk(x_6);
if (x_5 == 0)
{
lean_ctor_set(x_4, 1, x_7);
x_8 = x_4;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_4);
x_7 = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_3);
x_8 = lean_mk_thunk(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
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
x_8 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_DateTime_ofPlainDateTimeAssumingUTC___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_1);
return x_1;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_29; 
lean_inc_ref(x_1);
x_3 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Std_Time_TimeZone_toSeconds(x_2);
x_7 = lean_int_neg(x_6);
lean_dec(x_6);
x_8 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_9 = lean_int_mul(x_7, x_8);
lean_dec(x_7);
x_10 = l_Std_Time_Duration_ofNanoseconds(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
x_13 = x_10;
x_14 = x_29;
goto block_28;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed), 2, 1);
lean_closure_set(x_15, 0, x_1);
x_16 = lean_int_mul(x_4, x_8);
lean_dec(x_4);
x_17 = lean_int_add(x_16, x_5);
lean_dec(x_5);
lean_dec(x_16);
x_18 = lean_int_mul(x_11, x_8);
lean_dec(x_11);
x_19 = lean_int_add(x_18, x_12);
lean_dec(x_12);
lean_dec(x_18);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_Duration_ofNanoseconds(x_20);
lean_dec(x_20);
x_22 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_21);
x_23 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_22);
x_24 = lean_mk_thunk(x_15);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_24);
lean_ctor_set(x_13, 0, x_23);
x_25 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_addHours___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__0(void) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_47; 
x_4 = lean_ctor_get(x_2, 1);
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_2, 0);
lean_dec(x_48);
x_5 = x_2;
x_6 = x_47;
goto block_46;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
x_12 = lean_int_mul(x_3, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_28 = lean_int_neg(x_27);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_41);
x_43 = x_5;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_48; 
x_4 = lean_ctor_get(x_2, 1);
x_48 = !lean_is_exclusive(x_2);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_2, 0);
lean_dec(x_49);
x_5 = x_2;
x_6 = x_48;
goto block_47;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_3);
x_12 = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_29 = lean_int_neg(x_28);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_43);
lean_ctor_set(x_5, 0, x_42);
x_44 = x_5;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
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
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__0(void) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_47; 
x_4 = lean_ctor_get(x_2, 1);
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_2, 0);
lean_dec(x_48);
x_5 = x_2;
x_6 = x_47;
goto block_46;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
x_12 = lean_int_mul(x_3, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_28 = lean_int_neg(x_27);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_41);
x_43 = x_5;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_48; 
x_4 = lean_ctor_get(x_2, 1);
x_48 = !lean_is_exclusive(x_2);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_2, 0);
lean_dec(x_49);
x_5 = x_2;
x_6 = x_48;
goto block_47;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_3);
x_12 = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_29 = lean_int_neg(x_28);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_43);
lean_ctor_set(x_5, 0, x_42);
x_44 = x_5;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_46; 
x_4 = lean_ctor_get(x_2, 1);
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_2, 0);
lean_dec(x_47);
x_5 = x_2;
x_6 = x_46;
goto block_45;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_27 = lean_int_neg(x_26);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_41);
lean_ctor_set(x_5, 0, x_40);
x_42 = x_5;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_47; 
x_4 = lean_ctor_get(x_2, 1);
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_2, 0);
lean_dec(x_48);
x_5 = x_2;
x_6 = x_47;
goto block_46;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_3);
x_12 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_28 = lean_int_neg(x_27);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_41);
x_43 = x_5;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
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
static lean_object* _init_l_Std_Time_DateTime_addMilliseconds___closed__0(void) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_47; 
x_4 = lean_ctor_get(x_2, 1);
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_2, 0);
lean_dec(x_48);
x_5 = x_2;
x_6 = x_47;
goto block_46;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_obj_once(&l_Std_Time_DateTime_addMilliseconds___closed__0, &l_Std_Time_DateTime_addMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_addMilliseconds___closed__0);
x_12 = lean_int_mul(x_3, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_28 = lean_int_neg(x_27);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_42);
lean_ctor_set(x_5, 0, x_41);
x_43 = x_5;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_48; 
x_4 = lean_ctor_get(x_2, 1);
x_48 = !lean_is_exclusive(x_2);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_2, 0);
lean_dec(x_49);
x_5 = x_2;
x_6 = x_48;
goto block_47;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_3);
x_12 = lean_obj_once(&l_Std_Time_DateTime_addMilliseconds___closed__0, &l_Std_Time_DateTime_addMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_addMilliseconds___closed__0);
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_29 = lean_int_neg(x_28);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_43);
lean_ctor_set(x_5, 0, x_42);
x_44 = x_5;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_45; 
x_4 = lean_ctor_get(x_2, 1);
x_45 = !lean_is_exclusive(x_2);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_2, 0);
lean_dec(x_46);
x_5 = x_2;
x_6 = x_45;
goto block_44;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
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
x_14 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_26 = lean_int_neg(x_25);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_40);
lean_ctor_set(x_5, 0, x_39);
x_41 = x_5;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_46; 
x_4 = lean_ctor_get(x_2, 1);
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_2, 0);
lean_dec(x_47);
x_5 = x_2;
x_6 = x_46;
goto block_45;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_3);
x_12 = l_Std_Time_Duration_ofNanoseconds(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
x_27 = lean_int_neg(x_26);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_41);
lean_ctor_set(x_5, 0, x_40);
x_42 = x_5;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_44; 
x_4 = lean_ctor_get(x_2, 1);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 0);
lean_dec(x_45);
x_5 = x_2;
x_6 = x_44;
goto block_43;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
x_10 = x_7;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_13 = lean_int_add(x_12, x_3);
lean_dec(x_12);
x_14 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_13);
lean_dec(x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_9);
x_15 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_15);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Std_Time_TimeZone_toSeconds(x_1);
x_20 = lean_int_neg(x_19);
lean_dec(x_19);
x_21 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_26, 0, x_15);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_34);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_45; 
x_4 = lean_ctor_get(x_2, 1);
x_45 = !lean_is_exclusive(x_2);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_2, 0);
lean_dec(x_46);
x_5 = x_2;
x_6 = x_45;
goto block_44;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_43; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
x_10 = x_7;
x_11 = x_43;
goto block_42;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_int_neg(x_3);
x_13 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_14 = lean_int_add(x_13, x_12);
lean_dec(x_12);
lean_dec(x_13);
x_15 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_14);
lean_dec(x_14);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_15);
x_16 = x_10;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_9);
x_16 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc_ref(x_16);
x_17 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Std_Time_TimeZone_toSeconds(x_1);
x_21 = lean_int_neg(x_20);
lean_dec(x_20);
x_22 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_27, 0, x_16);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_35);
x_37 = x_5;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
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
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__0(void) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_46; 
x_4 = lean_ctor_get(x_2, 1);
x_46 = !lean_is_exclusive(x_2);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_2, 0);
lean_dec(x_47);
x_5 = x_2;
x_6 = x_46;
goto block_45;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_44; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_44 = !lean_is_exclusive(x_7);
if (x_44 == 0)
{
x_10 = x_7;
x_11 = x_44;
goto block_43;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_13 = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
x_14 = lean_int_mul(x_3, x_13);
x_15 = lean_int_add(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_15);
lean_dec(x_15);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_16);
x_17 = x_10;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_16);
lean_ctor_set(x_42, 1, x_9);
x_17 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc_ref(x_17);
x_18 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Std_Time_TimeZone_toSeconds(x_1);
x_22 = lean_int_neg(x_21);
lean_dec(x_21);
x_23 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_24 = lean_int_mul(x_22, x_23);
lean_dec(x_22);
x_25 = l_Std_Time_Duration_ofNanoseconds(x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_28, 0, x_17);
x_29 = lean_int_mul(x_19, x_23);
lean_dec(x_19);
x_30 = lean_int_add(x_29, x_20);
lean_dec(x_20);
lean_dec(x_29);
x_31 = lean_int_mul(x_26, x_23);
lean_dec(x_26);
x_32 = lean_int_add(x_31, x_27);
lean_dec(x_27);
lean_dec(x_31);
x_33 = lean_int_add(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
x_34 = l_Std_Time_Duration_ofNanoseconds(x_33);
lean_dec(x_33);
x_35 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_34);
x_36 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_35);
x_37 = lean_mk_thunk(x_28);
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_37);
lean_ctor_set(x_5, 0, x_36);
x_38 = x_5;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_47; 
x_4 = lean_ctor_get(x_2, 1);
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_2, 0);
lean_dec(x_48);
x_5 = x_2;
x_6 = x_47;
goto block_46;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_45; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
x_10 = x_7;
x_11 = x_45;
goto block_44;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_int_neg(x_3);
x_13 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_14 = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
x_15 = lean_int_mul(x_12, x_14);
lean_dec(x_12);
x_16 = lean_int_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_16);
lean_dec(x_16);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_17);
x_18 = x_10;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_17);
lean_ctor_set(x_43, 1, x_9);
x_18 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc_ref(x_18);
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Std_Time_TimeZone_toSeconds(x_1);
x_23 = lean_int_neg(x_22);
lean_dec(x_22);
x_24 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_25 = lean_int_mul(x_23, x_24);
lean_dec(x_23);
x_26 = l_Std_Time_Duration_ofNanoseconds(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_18);
x_30 = lean_int_mul(x_20, x_24);
lean_dec(x_20);
x_31 = lean_int_add(x_30, x_21);
lean_dec(x_21);
lean_dec(x_30);
x_32 = lean_int_mul(x_27, x_24);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_37);
x_39 = x_5;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_33; 
x_4 = lean_ctor_get(x_2, 1);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_2, 0);
lean_dec(x_34);
x_5 = x_2;
x_6 = x_33;
goto block_32;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_addMonthsClip(x_7, x_3);
lean_inc_ref(x_8);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Time_TimeZone_toSeconds(x_1);
x_13 = lean_int_neg(x_12);
lean_dec(x_12);
x_14 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_27);
x_29 = x_5;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_43; 
x_4 = lean_ctor_get(x_2, 1);
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_2, 0);
lean_dec(x_44);
x_5 = x_2;
x_6 = x_43;
goto block_42;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_41; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
x_10 = x_7;
x_11 = x_41;
goto block_40;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_int_neg(x_3);
x_13 = l_Std_Time_PlainDate_addMonthsClip(x_8, x_12);
lean_dec(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_9);
x_14 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_14);
x_15 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Std_Time_TimeZone_toSeconds(x_1);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_25, 0, x_14);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_34);
lean_ctor_set(x_5, 0, x_33);
x_35 = x_5;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_33; 
x_4 = lean_ctor_get(x_2, 1);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_2, 0);
lean_dec(x_34);
x_5 = x_2;
x_6 = x_33;
goto block_32;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_addMonthsRollOver(x_7, x_3);
lean_inc_ref(x_8);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Time_TimeZone_toSeconds(x_1);
x_13 = lean_int_neg(x_12);
lean_dec(x_12);
x_14 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_27);
x_29 = x_5;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_43; 
x_4 = lean_ctor_get(x_2, 1);
x_43 = !lean_is_exclusive(x_2);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_2, 0);
lean_dec(x_44);
x_5 = x_2;
x_6 = x_43;
goto block_42;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_41; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_41 = !lean_is_exclusive(x_7);
if (x_41 == 0)
{
x_10 = x_7;
x_11 = x_41;
goto block_40;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_int_neg(x_3);
x_13 = l_Std_Time_PlainDate_addMonthsRollOver(x_8, x_12);
lean_dec(x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_9);
x_14 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_14);
x_15 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
x_18 = l_Std_Time_TimeZone_toSeconds(x_1);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_25, 0, x_14);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_34);
lean_ctor_set(x_5, 0, x_33);
x_35 = x_5;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
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
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__0(void) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_44; 
x_4 = lean_ctor_get(x_2, 1);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 0);
lean_dec(x_45);
x_5 = x_2;
x_6 = x_44;
goto block_43;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
x_10 = x_7;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
x_13 = lean_int_mul(x_3, x_12);
x_14 = l_Std_Time_PlainDate_addMonthsRollOver(x_8, x_13);
lean_dec(x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_9);
x_15 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_15);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Std_Time_TimeZone_toSeconds(x_1);
x_20 = lean_int_neg(x_19);
lean_dec(x_19);
x_21 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_26, 0, x_15);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_34);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_44; 
x_4 = lean_ctor_get(x_2, 1);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 0);
lean_dec(x_45);
x_5 = x_2;
x_6 = x_44;
goto block_43;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
x_10 = x_7;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
x_13 = lean_int_mul(x_3, x_12);
x_14 = l_Std_Time_PlainDate_addMonthsClip(x_8, x_13);
lean_dec(x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_9);
x_15 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_15);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Std_Time_TimeZone_toSeconds(x_1);
x_20 = lean_int_neg(x_19);
lean_dec(x_19);
x_21 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_26, 0, x_15);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_34);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_45; 
x_4 = lean_ctor_get(x_2, 1);
x_45 = !lean_is_exclusive(x_2);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_2, 0);
lean_dec(x_46);
x_5 = x_2;
x_6 = x_45;
goto block_44;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_43; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
x_10 = x_7;
x_11 = x_43;
goto block_42;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
x_13 = lean_int_mul(x_3, x_12);
x_14 = lean_int_neg(x_13);
lean_dec(x_13);
x_15 = l_Std_Time_PlainDate_addMonthsRollOver(x_8, x_14);
lean_dec(x_14);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_15);
x_16 = x_10;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_9);
x_16 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc_ref(x_16);
x_17 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Std_Time_TimeZone_toSeconds(x_1);
x_21 = lean_int_neg(x_20);
lean_dec(x_20);
x_22 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_27, 0, x_16);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_35);
x_37 = x_5;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_45; 
x_4 = lean_ctor_get(x_2, 1);
x_45 = !lean_is_exclusive(x_2);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_2, 0);
lean_dec(x_46);
x_5 = x_2;
x_6 = x_45;
goto block_44;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_43; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
x_10 = x_7;
x_11 = x_43;
goto block_42;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
x_13 = lean_int_mul(x_3, x_12);
x_14 = lean_int_neg(x_13);
lean_dec(x_13);
x_15 = l_Std_Time_PlainDate_addMonthsClip(x_8, x_14);
lean_dec(x_14);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_15);
x_16 = x_10;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_15);
lean_ctor_set(x_41, 1, x_9);
x_16 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_inc_ref(x_16);
x_17 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Std_Time_TimeZone_toSeconds(x_1);
x_21 = lean_int_neg(x_20);
lean_dec(x_20);
x_22 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_27, 0, x_16);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_36);
lean_ctor_set(x_5, 0, x_35);
x_37 = x_5;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
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
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(400u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(100u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_72; 
x_4 = lean_ctor_get(x_2, 1);
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_2, 0);
lean_dec(x_73);
x_5 = x_2;
x_6 = x_72;
goto block_71;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_7; lean_object* x_8; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_69; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_42 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_42, 0);
x_44 = lean_ctor_get(x_42, 1);
x_69 = !lean_is_exclusive(x_42);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_42, 2);
lean_dec(x_70);
x_45 = x_42;
x_46 = x_69;
goto block_68;
}
else
{
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = x_69;
goto block_68;
}
block_41:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_39; 
x_9 = lean_ctor_get(x_7, 1);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_7, 0);
lean_dec(x_40);
x_10 = x_7;
x_11 = x_39;
goto block_38;
}
else
{
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_8);
x_12 = x_10;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_9);
x_12 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc_ref(x_12);
x_13 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_TimeZone_toSeconds(x_1);
x_17 = lean_int_neg(x_16);
lean_dec(x_16);
x_18 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_23, 0, x_12);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_32);
lean_ctor_set(x_5, 0, x_31);
x_33 = x_5;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
block_68:
{
uint8_t x_47; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_64; 
x_57 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
x_58 = lean_int_mod(x_43, x_57);
x_59 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
x_64 = lean_int_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_64 == 0)
{
x_47 = x_64;
goto block_56;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
x_66 = lean_int_mod(x_43, x_65);
x_67 = lean_int_dec_eq(x_66, x_59);
lean_dec(x_66);
if (x_67 == 0)
{
if (x_64 == 0)
{
goto block_63;
}
else
{
x_47 = x_64;
goto block_56;
}
}
else
{
goto block_63;
}
}
block_56:
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Std_Time_Month_Ordinal_days(x_47, x_44);
x_49 = lean_int_dec_lt(x_48, x_3);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
if (x_46 == 0)
{
lean_ctor_set(x_45, 2, x_3);
x_50 = x_45;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_44);
lean_ctor_set(x_52, 2, x_3);
x_50 = x_52;
goto block_51;
}
block_51:
{
x_8 = x_50;
goto block_41;
}
}
else
{
lean_object* x_53; 
lean_dec(x_3);
if (x_46 == 0)
{
lean_ctor_set(x_45, 2, x_48);
x_53 = x_45;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_44);
lean_ctor_set(x_55, 2, x_48);
x_53 = x_55;
goto block_54;
}
block_54:
{
x_8 = x_53;
goto block_41;
}
}
}
block_63:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
x_61 = lean_int_mod(x_43, x_60);
x_62 = lean_int_dec_eq(x_61, x_59);
lean_dec(x_61);
x_47 = x_62;
goto block_56;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_44; 
x_4 = lean_ctor_get(x_2, 1);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 0);
lean_dec(x_45);
x_5 = x_2;
x_6 = x_44;
goto block_43;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
x_10 = x_7;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = l_Std_Time_PlainDate_rollOver(x_12, x_13, x_3);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_9);
x_15 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_15);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Std_Time_TimeZone_toSeconds(x_1);
x_20 = lean_int_neg(x_19);
lean_dec(x_19);
x_21 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_26, 0, x_15);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_34);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_72; 
x_4 = lean_ctor_get(x_2, 1);
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_2, 0);
lean_dec(x_73);
x_5 = x_2;
x_6 = x_72;
goto block_71;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_7; lean_object* x_8; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_69; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_42 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_42, 0);
x_44 = lean_ctor_get(x_42, 2);
x_69 = !lean_is_exclusive(x_42);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_42, 1);
lean_dec(x_70);
x_45 = x_42;
x_46 = x_69;
goto block_68;
}
else
{
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = x_69;
goto block_68;
}
block_41:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_39; 
x_9 = lean_ctor_get(x_7, 1);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_7, 0);
lean_dec(x_40);
x_10 = x_7;
x_11 = x_39;
goto block_38;
}
else
{
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_8);
x_12 = x_10;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_9);
x_12 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc_ref(x_12);
x_13 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_TimeZone_toSeconds(x_1);
x_17 = lean_int_neg(x_16);
lean_dec(x_16);
x_18 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_23, 0, x_12);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_32);
lean_ctor_set(x_5, 0, x_31);
x_33 = x_5;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
block_68:
{
uint8_t x_47; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_64; 
x_57 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
x_58 = lean_int_mod(x_43, x_57);
x_59 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
x_64 = lean_int_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_64 == 0)
{
x_47 = x_64;
goto block_56;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
x_66 = lean_int_mod(x_43, x_65);
x_67 = lean_int_dec_eq(x_66, x_59);
lean_dec(x_66);
if (x_67 == 0)
{
if (x_64 == 0)
{
goto block_63;
}
else
{
x_47 = x_64;
goto block_56;
}
}
else
{
goto block_63;
}
}
block_56:
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Std_Time_Month_Ordinal_days(x_47, x_3);
x_49 = lean_int_dec_lt(x_48, x_44);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
if (x_46 == 0)
{
lean_ctor_set(x_45, 1, x_3);
x_50 = x_45;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 2, x_44);
x_50 = x_52;
goto block_51;
}
block_51:
{
x_8 = x_50;
goto block_41;
}
}
else
{
lean_object* x_53; 
lean_dec(x_44);
if (x_46 == 0)
{
lean_ctor_set(x_45, 2, x_48);
lean_ctor_set(x_45, 1, x_3);
x_53 = x_45;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_48);
x_53 = x_55;
goto block_54;
}
block_54:
{
x_8 = x_53;
goto block_41;
}
}
}
block_63:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
x_61 = lean_int_mod(x_43, x_60);
x_62 = lean_int_dec_eq(x_61, x_59);
lean_dec(x_61);
x_47 = x_62;
goto block_56;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_44; 
x_4 = lean_ctor_get(x_2, 1);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 0);
lean_dec(x_45);
x_5 = x_2;
x_6 = x_44;
goto block_43;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
x_10 = x_7;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = l_Std_Time_PlainDate_rollOver(x_12, x_3, x_13);
lean_dec(x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_9);
x_15 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_15);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Std_Time_TimeZone_toSeconds(x_1);
x_20 = lean_int_neg(x_19);
lean_dec(x_19);
x_21 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_26, 0, x_15);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_34);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_72; 
x_4 = lean_ctor_get(x_2, 1);
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_2, 0);
lean_dec(x_73);
x_5 = x_2;
x_6 = x_72;
goto block_71;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_7; lean_object* x_8; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_69; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_42 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_42, 1);
x_44 = lean_ctor_get(x_42, 2);
x_69 = !lean_is_exclusive(x_42);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_42, 0);
lean_dec(x_70);
x_45 = x_42;
x_46 = x_69;
goto block_68;
}
else
{
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_42);
x_45 = lean_box(0);
x_46 = x_69;
goto block_68;
}
block_41:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_39; 
x_9 = lean_ctor_get(x_7, 1);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_7, 0);
lean_dec(x_40);
x_10 = x_7;
x_11 = x_39;
goto block_38;
}
else
{
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_12; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_8);
x_12 = x_10;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_9);
x_12 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_inc_ref(x_12);
x_13 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Std_Time_TimeZone_toSeconds(x_1);
x_17 = lean_int_neg(x_16);
lean_dec(x_16);
x_18 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_23, 0, x_12);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_32);
lean_ctor_set(x_5, 0, x_31);
x_33 = x_5;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
block_68:
{
uint8_t x_47; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_64; 
x_57 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
x_58 = lean_int_mod(x_3, x_57);
x_59 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
x_64 = lean_int_dec_eq(x_58, x_59);
lean_dec(x_58);
if (x_64 == 0)
{
x_47 = x_64;
goto block_56;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
x_66 = lean_int_mod(x_3, x_65);
x_67 = lean_int_dec_eq(x_66, x_59);
lean_dec(x_66);
if (x_67 == 0)
{
if (x_64 == 0)
{
goto block_63;
}
else
{
x_47 = x_64;
goto block_56;
}
}
else
{
goto block_63;
}
}
block_56:
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Std_Time_Month_Ordinal_days(x_47, x_43);
x_49 = lean_int_dec_lt(x_48, x_44);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
if (x_46 == 0)
{
lean_ctor_set(x_45, 0, x_3);
x_50 = x_45;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_3);
lean_ctor_set(x_52, 1, x_43);
lean_ctor_set(x_52, 2, x_44);
x_50 = x_52;
goto block_51;
}
block_51:
{
x_8 = x_50;
goto block_41;
}
}
else
{
lean_object* x_53; 
lean_dec(x_44);
if (x_46 == 0)
{
lean_ctor_set(x_45, 2, x_48);
lean_ctor_set(x_45, 0, x_3);
x_53 = x_45;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set(x_55, 1, x_43);
lean_ctor_set(x_55, 2, x_48);
x_53 = x_55;
goto block_54;
}
block_54:
{
x_8 = x_53;
goto block_41;
}
}
}
block_63:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
x_61 = lean_int_mod(x_3, x_60);
x_62 = lean_int_dec_eq(x_61, x_59);
lean_dec(x_61);
x_47 = x_62;
goto block_56;
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_44; 
x_4 = lean_ctor_get(x_2, 1);
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 0);
lean_dec(x_45);
x_5 = x_2;
x_6 = x_44;
goto block_43;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_42; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
x_10 = x_7;
x_11 = x_42;
goto block_41;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = l_Std_Time_PlainDate_rollOver(x_3, x_12, x_13);
lean_dec(x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_14);
lean_ctor_set(x_40, 1, x_9);
x_15 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_15);
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Std_Time_TimeZone_toSeconds(x_1);
x_20 = lean_int_neg(x_19);
lean_dec(x_19);
x_21 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
lean_closure_set(x_26, 0, x_15);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_34);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_52; 
x_4 = lean_ctor_get(x_2, 1);
x_52 = !lean_is_exclusive(x_2);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_2, 0);
lean_dec(x_53);
x_5 = x_2;
x_6 = x_52;
goto block_51;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_50; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
x_10 = x_7;
x_11 = x_50;
goto block_49;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_47; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 2);
x_14 = lean_ctor_get(x_8, 3);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_8, 0);
lean_dec(x_48);
x_15 = x_8;
x_16 = x_47;
goto block_46;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_3);
x_17 = x_15;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_12);
lean_ctor_set(x_45, 2, x_13);
lean_ctor_set(x_45, 3, x_14);
x_17 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_18; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_17);
x_18 = x_10;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_17);
x_18 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc_ref(x_18);
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Std_Time_TimeZone_toSeconds(x_1);
x_23 = lean_int_neg(x_22);
lean_dec(x_22);
x_24 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_25 = lean_int_mul(x_23, x_24);
lean_dec(x_23);
x_26 = l_Std_Time_Duration_ofNanoseconds(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_18);
x_30 = lean_int_mul(x_20, x_24);
lean_dec(x_20);
x_31 = lean_int_add(x_30, x_21);
lean_dec(x_21);
lean_dec(x_30);
x_32 = lean_int_mul(x_27, x_24);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_37);
x_39 = x_5;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_52; 
x_4 = lean_ctor_get(x_2, 1);
x_52 = !lean_is_exclusive(x_2);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_2, 0);
lean_dec(x_53);
x_5 = x_2;
x_6 = x_52;
goto block_51;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_50; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
x_10 = x_7;
x_11 = x_50;
goto block_49;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_47; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 2);
x_14 = lean_ctor_get(x_8, 3);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_8, 1);
lean_dec(x_48);
x_15 = x_8;
x_16 = x_47;
goto block_46;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_3);
x_17 = x_15;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set(x_45, 2, x_13);
lean_ctor_set(x_45, 3, x_14);
x_17 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_18; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_17);
x_18 = x_10;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_17);
x_18 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc_ref(x_18);
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Std_Time_TimeZone_toSeconds(x_1);
x_23 = lean_int_neg(x_22);
lean_dec(x_22);
x_24 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_25 = lean_int_mul(x_23, x_24);
lean_dec(x_23);
x_26 = l_Std_Time_Duration_ofNanoseconds(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_18);
x_30 = lean_int_mul(x_20, x_24);
lean_dec(x_20);
x_31 = lean_int_add(x_30, x_21);
lean_dec(x_21);
lean_dec(x_30);
x_32 = lean_int_mul(x_27, x_24);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_37);
x_39 = x_5;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_52; 
x_4 = lean_ctor_get(x_2, 1);
x_52 = !lean_is_exclusive(x_2);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_2, 0);
lean_dec(x_53);
x_5 = x_2;
x_6 = x_52;
goto block_51;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_50; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
x_10 = x_7;
x_11 = x_50;
goto block_49;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_47; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 3);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_8, 2);
lean_dec(x_48);
x_15 = x_8;
x_16 = x_47;
goto block_46;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_3);
x_17 = x_15;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_13);
lean_ctor_set(x_45, 2, x_3);
lean_ctor_set(x_45, 3, x_14);
x_17 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_18; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_17);
x_18 = x_10;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_17);
x_18 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc_ref(x_18);
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Std_Time_TimeZone_toSeconds(x_1);
x_23 = lean_int_neg(x_22);
lean_dec(x_22);
x_24 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_25 = lean_int_mul(x_23, x_24);
lean_dec(x_23);
x_26 = l_Std_Time_Duration_ofNanoseconds(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_18);
x_30 = lean_int_mul(x_20, x_24);
lean_dec(x_20);
x_31 = lean_int_add(x_30, x_21);
lean_dec(x_21);
lean_dec(x_30);
x_32 = lean_int_mul(x_27, x_24);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_37);
x_39 = x_5;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_52; 
x_4 = lean_ctor_get(x_2, 1);
x_52 = !lean_is_exclusive(x_2);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_2, 0);
lean_dec(x_53);
x_5 = x_2;
x_6 = x_52;
goto block_51;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_50; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_50 = !lean_is_exclusive(x_7);
if (x_50 == 0)
{
x_10 = x_7;
x_11 = x_50;
goto block_49;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_47; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_8, 3);
lean_dec(x_48);
x_15 = x_8;
x_16 = x_47;
goto block_46;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 3, x_3);
x_17 = x_15;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_13);
lean_ctor_set(x_45, 2, x_14);
lean_ctor_set(x_45, 3, x_3);
x_17 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_18; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_17);
x_18 = x_10;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_17);
x_18 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_inc_ref(x_18);
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Std_Time_TimeZone_toSeconds(x_1);
x_23 = lean_int_neg(x_22);
lean_dec(x_22);
x_24 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_25 = lean_int_mul(x_23, x_24);
lean_dec(x_23);
x_26 = l_Std_Time_Duration_ofNanoseconds(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_29, 0, x_18);
x_30 = lean_int_mul(x_20, x_24);
lean_dec(x_20);
x_31 = lean_int_add(x_30, x_21);
lean_dec(x_21);
lean_dec(x_30);
x_32 = lean_int_mul(x_27, x_24);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_38);
lean_ctor_set(x_5, 0, x_37);
x_39 = x_5;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
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
static lean_object* _init_l_Std_Time_DateTime_withMilliseconds___closed__0(void) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_57; 
x_4 = lean_ctor_get(x_2, 1);
x_57 = !lean_is_exclusive(x_2);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_2, 0);
lean_dec(x_58);
x_5 = x_2;
x_6 = x_57;
goto block_56;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_55; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_55 = !lean_is_exclusive(x_7);
if (x_55 == 0)
{
x_10 = x_7;
x_11 = x_55;
goto block_54;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_53; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_ctor_get(x_8, 3);
x_53 = !lean_is_exclusive(x_8);
if (x_53 == 0)
{
x_16 = x_8;
x_17 = x_53;
goto block_52;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
x_19 = lean_int_emod(x_15, x_18);
lean_dec(x_15);
x_20 = lean_obj_once(&l_Std_Time_DateTime_addMilliseconds___closed__0, &l_Std_Time_DateTime_addMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_addMilliseconds___closed__0);
x_21 = lean_int_mul(x_3, x_20);
x_22 = lean_int_add(x_21, x_19);
lean_dec(x_19);
lean_dec(x_21);
if (x_17 == 0)
{
lean_ctor_set(x_16, 3, x_22);
x_23 = x_16;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_12);
lean_ctor_set(x_51, 1, x_13);
lean_ctor_set(x_51, 2, x_14);
lean_ctor_set(x_51, 3, x_22);
x_23 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_24; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_23);
x_24 = x_10;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_9);
lean_ctor_set(x_49, 1, x_23);
x_24 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_inc_ref(x_24);
x_25 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_Std_Time_TimeZone_toSeconds(x_1);
x_29 = lean_int_neg(x_28);
lean_dec(x_28);
x_30 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_31 = lean_int_mul(x_29, x_30);
lean_dec(x_29);
x_32 = l_Std_Time_Duration_ofNanoseconds(x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_35, 0, x_24);
x_36 = lean_int_mul(x_26, x_30);
lean_dec(x_26);
x_37 = lean_int_add(x_36, x_27);
lean_dec(x_27);
lean_dec(x_36);
x_38 = lean_int_mul(x_33, x_30);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_44);
lean_ctor_set(x_5, 0, x_43);
x_45 = x_5;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_DateTime_toPlainDateTime___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
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
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
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
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
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
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
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
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
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
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
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
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
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
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
x_7 = lean_int_emod(x_5, x_6);
lean_dec(x_5);
return x_7;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
x_8 = lean_int_emod(x_6, x_7);
lean_dec(x_6);
return x_8;
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
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec_ref(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec_ref(x_5);
return x_6;
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
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_weekday(x_4);
return x_5;
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
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_weekday(x_5);
return x_6;
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
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Std_Time_Year_Offset_era(x_5);
lean_dec(x_5);
return x_6;
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
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Time_DateTime_era___redArg(x_2);
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_33; 
x_4 = lean_ctor_get(x_2, 1);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_2, 0);
lean_dec(x_34);
x_5 = x_2;
x_6 = x_33;
goto block_32;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_thunk_get_own(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_PlainDateTime_withWeekday(x_7, x_3);
lean_inc_ref(x_8);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Std_Time_TimeZone_toSeconds(x_1);
x_13 = lean_int_neg(x_12);
lean_dec(x_12);
x_14 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
if (x_6 == 0)
{
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_27);
x_29 = x_5;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
x_7 = lean_int_mod(x_5, x_6);
x_8 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
x_13 = lean_int_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_13 == 0)
{
lean_dec(x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
x_15 = lean_int_mod(x_5, x_14);
x_16 = lean_int_dec_eq(x_15, x_8);
lean_dec(x_15);
if (x_16 == 0)
{
if (x_13 == 0)
{
goto block_12;
}
else
{
lean_dec(x_5);
return x_13;
}
}
else
{
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
x_10 = lean_int_mod(x_5, x_9);
lean_dec(x_5);
x_11 = lean_int_dec_eq(x_10, x_8);
lean_dec(x_10);
return x_11;
}
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
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Time_DateTime_inLeapYear___redArg(x_2);
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
lean_object* x_2; uint8_t x_3; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_28; 
x_2 = lean_ctor_get(x_1, 1);
x_18 = lean_thunk_get_own(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
x_22 = lean_int_mod(x_20, x_21);
x_23 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
x_28 = lean_int_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_28 == 0)
{
lean_dec(x_20);
x_3 = x_28;
goto block_17;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__3, &l_Std_Time_DateTime_withDaysClip___closed__3_once, _init_l_Std_Time_DateTime_withDaysClip___closed__3);
x_30 = lean_int_mod(x_20, x_29);
x_31 = lean_int_dec_eq(x_30, x_23);
lean_dec(x_30);
if (x_31 == 0)
{
if (x_28 == 0)
{
goto block_27;
}
else
{
lean_dec(x_20);
x_3 = x_28;
goto block_17;
}
}
else
{
goto block_27;
}
}
block_17:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_15; 
x_4 = lean_thunk_get_own(x_2);
x_5 = lean_ctor_get(x_4, 0);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_6 = x_4;
x_7 = x_15;
goto block_14;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
lean_dec_ref(x_5);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_9);
lean_ctor_set(x_6, 0, x_8);
x_10 = x_6;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_9);
x_10 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_11; 
x_11 = l_Std_Time_ValidDate_dayOfYear(x_3, x_10);
lean_dec_ref(x_10);
return x_11;
}
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
x_25 = lean_int_mod(x_20, x_24);
lean_dec(x_20);
x_26 = lean_int_dec_eq(x_25, x_23);
lean_dec(x_25);
x_3 = x_26;
goto block_17;
}
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_dayOfYear___redArg(x_2);
return x_3;
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
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_weekOfYear(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_weekOfYear(x_5);
return x_6;
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
lean_dec(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_DateTime_weekOfMonth___redArg(x_2);
return x_3;
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
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_alignedWeekOfMonth(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_alignedWeekOfMonth(x_5);
return x_6;
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
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_quarter(x_4);
lean_dec_ref(x_4);
return x_5;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Std_Time_PlainDate_quarter(x_5);
lean_dec_ref(x_5);
return x_6;
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
lean_dec(x_3);
return x_4;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_thunk_get_own(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec(x_4);
return x_5;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_32; 
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
x_10 = lean_int_neg(x_9);
lean_dec(x_9);
x_11 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_12 = lean_int_mul(x_10, x_11);
lean_dec(x_10);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_ctor_get(x_13, 1);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
x_16 = x_13;
x_17 = x_32;
goto block_31;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 2, 1);
lean_closure_set(x_18, 0, x_5);
x_19 = lean_int_mul(x_7, x_11);
lean_dec(x_7);
x_20 = lean_int_add(x_19, x_8);
lean_dec(x_8);
lean_dec(x_19);
x_21 = lean_int_mul(x_14, x_11);
lean_dec(x_14);
x_22 = lean_int_add(x_21, x_15);
lean_dec(x_15);
lean_dec(x_21);
x_23 = lean_int_add(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
x_24 = l_Std_Time_Duration_ofNanoseconds(x_23);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_24);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_25);
x_27 = lean_mk_thunk(x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_27);
lean_ctor_set(x_16, 0, x_26);
x_28 = x_16;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
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
x_9 = lean_int_neg(x_5);
x_10 = lean_int_neg(x_6);
x_11 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = ((lean_object*)(l_Std_Time_DateTime_instHSubDuration___closed__0));
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_49; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_2, 1);
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_2, 0);
lean_dec(x_50);
x_7 = x_2;
x_8 = x_49;
goto block_48;
}
else
{
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_9 = lean_thunk_get_own(x_6);
lean_dec_ref(x_6);
x_10 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_14 = lean_int_mul(x_4, x_13);
x_15 = lean_int_add(x_14, x_5);
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
x_30 = lean_int_neg(x_29);
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
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_44);
lean_ctor_set(x_7, 0, x_43);
x_45 = x_7;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHAddDuration___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_50; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_2, 1);
x_50 = !lean_is_exclusive(x_2);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_2, 0);
lean_dec(x_51);
x_7 = x_2;
x_8 = x_50;
goto block_49;
}
else
{
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_9 = lean_thunk_get_own(x_6);
lean_dec_ref(x_6);
x_10 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
x_14 = lean_int_mul(x_4, x_13);
x_15 = lean_int_add(x_14, x_5);
lean_dec(x_14);
x_16 = lean_int_neg(x_15);
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
x_31 = lean_int_neg(x_30);
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
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_45);
lean_ctor_set(x_7, 0, x_44);
x_46 = x_7;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
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
res = runtime_initialize_Std_Time_DateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Month(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Year(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin)
;
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
res = initialize_Std_Time_DateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_TimeZone(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Month(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Year(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_DateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_DateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_DateTime(builtin);
}
#ifdef __cplusplus
}
#endif

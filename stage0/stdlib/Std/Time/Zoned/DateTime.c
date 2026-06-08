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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
extern lean_object* l_Std_Time_instOrdTimestamp;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_instDecidableEqDuration_decEq(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*, uint8_t);
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
static lean_once_cell_t l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_ofPlainDateTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofPlainDateTime___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Time_DateTime_addDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addDays___closed__0;
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay___boxed(lean_object*, lean_object*, lean_object*);
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
v___x_27_ = lean_unsigned_to_nat(0u);
v___x_28_ = lean_nat_to_int(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = lean_unsigned_to_nat(1000000000u);
v___x_30_ = lean_nat_to_int(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object* v_tz_31_, lean_object* v_tm_32_, lean_object* v_x_33_){
_start:
{
lean_object* v_offset_34_; lean_object* v_second_35_; lean_object* v_nano_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_offset_34_ = lean_ctor_get(v_tz_31_, 0);
v_second_35_ = lean_ctor_get(v_tm_32_, 0);
v_nano_36_ = lean_ctor_get(v_tm_32_, 1);
v___x_37_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_38_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_39_ = lean_int_mul(v_second_35_, v___x_38_);
v___x_40_ = lean_int_add(v___x_39_, v_nano_36_);
lean_dec(v___x_39_);
v___x_41_ = lean_int_mul(v_offset_34_, v___x_38_);
v___x_42_ = lean_int_add(v___x_41_, v___x_37_);
lean_dec(v___x_41_);
v___x_43_ = lean_int_add(v___x_40_, v___x_42_);
lean_dec(v___x_42_);
lean_dec(v___x_40_);
v___x_44_ = l_Std_Time_Duration_ofNanoseconds(v___x_43_);
lean_dec(v___x_43_);
v___x_45_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object* v_tz_46_, lean_object* v_tm_47_, lean_object* v_x_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_Time_DateTime_ofTimestamp___lam__0(v_tz_46_, v_tm_47_, v_x_48_);
lean_dec_ref(v_tm_47_);
lean_dec_ref(v_tz_46_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object* v_tm_50_, lean_object* v_tz_51_){
_start:
{
lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
lean_inc_ref(v_tm_50_);
v___f_52_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestamp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_52_, 0, v_tz_51_);
lean_closure_set(v___f_52_, 1, v_tm_50_);
v___x_53_ = lean_mk_thunk(v___f_52_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v_tm_50_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0(lean_object* v_tz_55_, lean_object* v___x_56_, lean_object* v_x_57_){
_start:
{
lean_object* v_offset_58_; lean_object* v_second_59_; lean_object* v_nano_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v_offset_58_ = lean_ctor_get(v_tz_55_, 0);
v_second_59_ = lean_ctor_get(v___x_56_, 0);
v_nano_60_ = lean_ctor_get(v___x_56_, 1);
v___x_61_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_62_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_63_ = lean_int_mul(v_second_59_, v___x_62_);
v___x_64_ = lean_int_add(v___x_63_, v_nano_60_);
lean_dec(v___x_63_);
v___x_65_ = lean_int_mul(v_offset_58_, v___x_62_);
v___x_66_ = lean_int_add(v___x_65_, v___x_61_);
lean_dec(v___x_65_);
v___x_67_ = lean_int_add(v___x_64_, v___x_66_);
lean_dec(v___x_66_);
lean_dec(v___x_64_);
v___x_68_ = l_Std_Time_Duration_ofNanoseconds(v___x_67_);
lean_dec(v___x_67_);
v___x_69_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited___lam__0___boxed(lean_object* v_tz_70_, lean_object* v___x_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Std_Time_DateTime_instInhabited___lam__0(v_tz_70_, v___x_71_, v_x_72_);
lean_dec_ref(v___x_71_);
lean_dec_ref(v_tz_70_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instInhabited(lean_object* v_tz_74_){
_start:
{
lean_object* v___x_75_; lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = l_Std_Time_instInhabitedTimestamp_default;
v___f_76_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_instInhabited___lam__0___boxed), 3, 2);
lean_closure_set(v___f_76_, 0, v_tz_74_);
lean_closure_set(v___f_76_, 1, v___x_75_);
v___x_77_ = lean_mk_thunk(v___f_76_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_75_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___redArg(lean_object* v_date_79_){
_start:
{
lean_object* v_date_80_; lean_object* v___x_81_; lean_object* v_date_82_; lean_object* v___x_83_; 
v_date_80_ = lean_ctor_get(v_date_79_, 1);
v___x_81_ = lean_thunk_get_own(v_date_80_);
v_date_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc_ref(v_date_82_);
lean_dec(v___x_81_);
v___x_83_ = l_Std_Time_PlainDate_toEpochDay(v_date_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___redArg___boxed(lean_object* v_date_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Std_Time_DateTime_toEpochDay___redArg(v_date_84_);
lean_dec_ref(v_date_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay(lean_object* v_tz_86_, lean_object* v_date_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Std_Time_DateTime_toEpochDay___redArg(v_date_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___boxed(lean_object* v_tz_89_, lean_object* v_date_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_Time_DateTime_toEpochDay(v_tz_89_, v_date_90_);
lean_dec_ref(v_date_90_);
lean_dec_ref(v_tz_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg(lean_object* v_date_92_){
_start:
{
lean_object* v_timestamp_93_; 
v_timestamp_93_ = lean_ctor_get(v_date_92_, 0);
lean_inc_ref(v_timestamp_93_);
return v_timestamp_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___redArg___boxed(lean_object* v_date_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_Time_DateTime_toTimestamp___redArg(v_date_94_);
lean_dec_ref(v_date_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object* v_tz_96_, lean_object* v_date_97_){
_start:
{
lean_object* v_timestamp_98_; 
v_timestamp_98_ = lean_ctor_get(v_date_97_, 0);
lean_inc_ref(v_timestamp_98_);
return v_timestamp_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object* v_tz_99_, lean_object* v_date_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Std_Time_DateTime_toTimestamp(v_tz_99_, v_date_100_);
lean_dec_ref(v_date_100_);
lean_dec_ref(v_tz_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(lean_object* v_tz_u2081_102_, lean_object* v_timestamp_103_, lean_object* v_x_104_){
_start:
{
lean_object* v_offset_105_; lean_object* v_second_106_; lean_object* v_nano_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_offset_105_ = lean_ctor_get(v_tz_u2081_102_, 0);
v_second_106_ = lean_ctor_get(v_timestamp_103_, 0);
v_nano_107_ = lean_ctor_get(v_timestamp_103_, 1);
v___x_108_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_109_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_110_ = lean_int_mul(v_second_106_, v___x_109_);
v___x_111_ = lean_int_add(v___x_110_, v_nano_107_);
lean_dec(v___x_110_);
v___x_112_ = lean_int_mul(v_offset_105_, v___x_109_);
v___x_113_ = lean_int_add(v___x_112_, v___x_108_);
lean_dec(v___x_112_);
v___x_114_ = lean_int_add(v___x_111_, v___x_113_);
lean_dec(v___x_113_);
lean_dec(v___x_111_);
v___x_115_ = l_Std_Time_Duration_ofNanoseconds(v___x_114_);
lean_dec(v___x_114_);
v___x_116_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed(lean_object* v_tz_u2081_117_, lean_object* v_timestamp_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(v_tz_u2081_117_, v_timestamp_118_, v_x_119_);
lean_dec_ref(v_timestamp_118_);
lean_dec_ref(v_tz_u2081_117_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___redArg(lean_object* v_date_121_, lean_object* v_tz_u2081_122_){
_start:
{
lean_object* v_timestamp_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_132_; 
v_timestamp_123_ = lean_ctor_get(v_date_121_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_date_121_);
if (v_isSharedCheck_132_ == 0)
{
lean_object* v_unused_133_; 
v_unused_133_ = lean_ctor_get(v_date_121_, 1);
lean_dec(v_unused_133_);
v___x_125_ = v_date_121_;
v_isShared_126_ = v_isSharedCheck_132_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_timestamp_123_);
lean_dec(v_date_121_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_132_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___f_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
lean_inc_ref(v_timestamp_123_);
v___f_127_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_127_, 0, v_tz_u2081_122_);
lean_closure_set(v___f_127_, 1, v_timestamp_123_);
v___x_128_ = lean_mk_thunk(v___f_127_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_128_);
v___x_130_ = v___x_125_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_timestamp_123_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone(lean_object* v_tz_134_, lean_object* v_date_135_, lean_object* v_tz_u2081_136_){
_start:
{
lean_object* v_timestamp_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_146_; 
v_timestamp_137_ = lean_ctor_get(v_date_135_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_date_135_);
if (v_isSharedCheck_146_ == 0)
{
lean_object* v_unused_147_; 
v_unused_147_ = lean_ctor_get(v_date_135_, 1);
lean_dec(v_unused_147_);
v___x_139_ = v_date_135_;
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_timestamp_137_);
lean_dec(v_date_135_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_146_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_144_; 
lean_inc_ref(v_timestamp_137_);
v___f_141_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_141_, 0, v_tz_u2081_136_);
lean_closure_set(v___f_141_, 1, v_timestamp_137_);
v___x_142_ = lean_mk_thunk(v___f_141_);
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 1, v___x_142_);
v___x_144_ = v___x_139_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_timestamp_137_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertTimeZone___boxed(lean_object* v_tz_148_, lean_object* v_date_149_, lean_object* v_tz_u2081_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_Time_DateTime_convertTimeZone(v_tz_148_, v_date_149_, v_tz_u2081_150_);
lean_dec_ref(v_tz_148_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object* v_date_152_, lean_object* v_x_153_){
_start:
{
lean_inc_ref(v_date_152_);
return v_date_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(lean_object* v_date_154_, lean_object* v_x_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Time_DateTime_ofPlainDateTime___lam__0(v_date_154_, v_x_155_);
lean_dec_ref(v_date_154_);
return v_res_156_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_158_ = lean_int_neg(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object* v_date_159_, lean_object* v_tz_160_){
_start:
{
lean_object* v_offset_161_; lean_object* v___x_162_; lean_object* v_second_163_; lean_object* v_nano_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_182_; 
v_offset_161_ = lean_ctor_get(v_tz_160_, 0);
lean_inc_ref(v_date_159_);
v___x_162_ = l_Std_Time_PlainDateTime_toWallTime(v_date_159_);
v_second_163_ = lean_ctor_get(v___x_162_, 0);
v_nano_164_ = lean_ctor_get(v___x_162_, 1);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_182_ == 0)
{
v___x_166_ = v___x_162_;
v_isShared_167_ = v_isSharedCheck_182_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_nano_164_);
lean_inc(v_second_163_);
lean_dec(v___x_162_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_182_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___f_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_tm_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___f_168_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed), 2, 1);
lean_closure_set(v___f_168_, 0, v_date_159_);
v___x_169_ = lean_int_neg(v_offset_161_);
v___x_170_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_171_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_172_ = lean_int_mul(v_second_163_, v___x_171_);
lean_dec(v_second_163_);
v___x_173_ = lean_int_add(v___x_172_, v_nano_164_);
lean_dec(v_nano_164_);
lean_dec(v___x_172_);
v___x_174_ = lean_int_mul(v___x_169_, v___x_171_);
lean_dec(v___x_169_);
v___x_175_ = lean_int_add(v___x_174_, v___x_170_);
lean_dec(v___x_174_);
v___x_176_ = lean_int_add(v___x_173_, v___x_175_);
lean_dec(v___x_175_);
lean_dec(v___x_173_);
v_tm_177_ = l_Std_Time_Duration_ofNanoseconds(v___x_176_);
lean_dec(v___x_176_);
v___x_178_ = lean_mk_thunk(v___f_168_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 1, v___x_178_);
lean_ctor_set(v___x_166_, 0, v_tm_177_);
v___x_180_ = v___x_166_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_tm_177_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___boxed(lean_object* v_date_183_, lean_object* v_tz_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_Time_DateTime_ofPlainDateTime(v_date_183_, v_tz_184_);
lean_dec_ref(v_tz_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0(lean_object* v_tz_186_, lean_object* v___x_187_, lean_object* v___x_188_, lean_object* v___x_189_, lean_object* v_x_190_){
_start:
{
lean_object* v_offset_191_; lean_object* v_second_192_; lean_object* v_nano_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_offset_191_ = lean_ctor_get(v_tz_186_, 0);
v_second_192_ = lean_ctor_get(v___x_187_, 0);
v_nano_193_ = lean_ctor_get(v___x_187_, 1);
v___x_194_ = lean_int_mul(v_second_192_, v___x_188_);
v___x_195_ = lean_int_add(v___x_194_, v_nano_193_);
lean_dec(v___x_194_);
v___x_196_ = lean_int_mul(v_offset_191_, v___x_188_);
v___x_197_ = lean_int_add(v___x_196_, v___x_189_);
lean_dec(v___x_196_);
v___x_198_ = lean_int_add(v___x_195_, v___x_197_);
lean_dec(v___x_197_);
lean_dec(v___x_195_);
v___x_199_ = l_Std_Time_Duration_ofNanoseconds(v___x_198_);
lean_dec(v___x_198_);
v___x_200_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___lam__0___boxed(lean_object* v_tz_201_, lean_object* v___x_202_, lean_object* v___x_203_, lean_object* v___x_204_, lean_object* v_x_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Time_DateTime_addHours___lam__0(v_tz_201_, v___x_202_, v___x_203_, v___x_204_, v_x_205_);
lean_dec(v___x_204_);
lean_dec(v___x_203_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v_tz_201_);
return v_res_206_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(3600u);
v___x_208_ = lean_nat_to_int(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object* v_tz_209_, lean_object* v_dt_210_, lean_object* v_hours_211_){
_start:
{
lean_object* v_timestamp_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_233_; 
v_timestamp_212_ = lean_ctor_get(v_dt_210_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_dt_210_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v_dt_210_, 1);
lean_dec(v_unused_234_);
v___x_214_ = v_dt_210_;
v_isShared_215_ = v_isSharedCheck_233_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_timestamp_212_);
lean_dec(v_dt_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_233_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_second_216_; lean_object* v_nano_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v_second_216_ = lean_ctor_get(v_timestamp_212_, 0);
lean_inc(v_second_216_);
v_nano_217_ = lean_ctor_get(v_timestamp_212_, 1);
lean_inc(v_nano_217_);
lean_dec_ref(v_timestamp_212_);
v___x_218_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_219_ = lean_int_mul(v_hours_211_, v___x_218_);
v___x_220_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_221_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_222_ = lean_int_mul(v_second_216_, v___x_221_);
lean_dec(v_second_216_);
v___x_223_ = lean_int_add(v___x_222_, v_nano_217_);
lean_dec(v_nano_217_);
lean_dec(v___x_222_);
v___x_224_ = lean_int_mul(v___x_219_, v___x_221_);
lean_dec(v___x_219_);
v___x_225_ = lean_int_add(v___x_224_, v___x_220_);
lean_dec(v___x_224_);
v___x_226_ = lean_int_add(v___x_223_, v___x_225_);
lean_dec(v___x_225_);
lean_dec(v___x_223_);
v___x_227_ = l_Std_Time_Duration_ofNanoseconds(v___x_226_);
lean_dec(v___x_226_);
lean_inc_ref(v___x_227_);
v___f_228_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_228_, 0, v_tz_209_);
lean_closure_set(v___f_228_, 1, v___x_227_);
lean_closure_set(v___f_228_, 2, v___x_221_);
lean_closure_set(v___f_228_, 3, v___x_220_);
v___x_229_ = lean_mk_thunk(v___f_228_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_229_);
lean_ctor_set(v___x_214_, 0, v___x_227_);
v___x_231_ = v___x_214_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object* v_tz_235_, lean_object* v_dt_236_, lean_object* v_hours_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_Time_DateTime_addHours(v_tz_235_, v_dt_236_, v_hours_237_);
lean_dec(v_hours_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object* v_tz_239_, lean_object* v_dt_240_, lean_object* v_hours_241_){
_start:
{
lean_object* v_timestamp_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_265_; 
v_timestamp_242_ = lean_ctor_get(v_dt_240_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v_dt_240_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v_dt_240_, 1);
lean_dec(v_unused_266_);
v___x_244_ = v_dt_240_;
v_isShared_245_ = v_isSharedCheck_265_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_timestamp_242_);
lean_dec(v_dt_240_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_265_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_second_246_; lean_object* v_nano_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v_second_246_ = lean_ctor_get(v_timestamp_242_, 0);
lean_inc(v_second_246_);
v_nano_247_ = lean_ctor_get(v_timestamp_242_, 1);
lean_inc(v_nano_247_);
lean_dec_ref(v_timestamp_242_);
v___x_248_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_249_ = lean_int_mul(v_hours_241_, v___x_248_);
v___x_250_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_251_ = lean_int_neg(v___x_249_);
lean_dec(v___x_249_);
v___x_252_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_253_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_254_ = lean_int_mul(v_second_246_, v___x_253_);
lean_dec(v_second_246_);
v___x_255_ = lean_int_add(v___x_254_, v_nano_247_);
lean_dec(v_nano_247_);
lean_dec(v___x_254_);
v___x_256_ = lean_int_mul(v___x_251_, v___x_253_);
lean_dec(v___x_251_);
v___x_257_ = lean_int_add(v___x_256_, v___x_252_);
lean_dec(v___x_256_);
v___x_258_ = lean_int_add(v___x_255_, v___x_257_);
lean_dec(v___x_257_);
lean_dec(v___x_255_);
v___x_259_ = l_Std_Time_Duration_ofNanoseconds(v___x_258_);
lean_dec(v___x_258_);
lean_inc_ref(v___x_259_);
v___f_260_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_260_, 0, v_tz_239_);
lean_closure_set(v___f_260_, 1, v___x_259_);
lean_closure_set(v___f_260_, 2, v___x_253_);
lean_closure_set(v___f_260_, 3, v___x_250_);
v___x_261_ = lean_mk_thunk(v___f_260_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v___x_261_);
lean_ctor_set(v___x_244_, 0, v___x_259_);
v___x_263_ = v___x_244_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object* v_tz_267_, lean_object* v_dt_268_, lean_object* v_hours_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Time_DateTime_subHours(v_tz_267_, v_dt_268_, v_hours_269_);
lean_dec(v_hours_269_);
return v_res_270_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(60u);
v___x_272_ = lean_nat_to_int(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object* v_tz_273_, lean_object* v_dt_274_, lean_object* v_minutes_275_){
_start:
{
lean_object* v_timestamp_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_297_; 
v_timestamp_276_ = lean_ctor_get(v_dt_274_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_dt_274_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v_dt_274_, 1);
lean_dec(v_unused_298_);
v___x_278_ = v_dt_274_;
v_isShared_279_ = v_isSharedCheck_297_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_timestamp_276_);
lean_dec(v_dt_274_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_297_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v_second_280_; lean_object* v_nano_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___f_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v_second_280_ = lean_ctor_get(v_timestamp_276_, 0);
lean_inc(v_second_280_);
v_nano_281_ = lean_ctor_get(v_timestamp_276_, 1);
lean_inc(v_nano_281_);
lean_dec_ref(v_timestamp_276_);
v___x_282_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_283_ = lean_int_mul(v_minutes_275_, v___x_282_);
v___x_284_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_285_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_286_ = lean_int_mul(v_second_280_, v___x_285_);
lean_dec(v_second_280_);
v___x_287_ = lean_int_add(v___x_286_, v_nano_281_);
lean_dec(v_nano_281_);
lean_dec(v___x_286_);
v___x_288_ = lean_int_mul(v___x_283_, v___x_285_);
lean_dec(v___x_283_);
v___x_289_ = lean_int_add(v___x_288_, v___x_284_);
lean_dec(v___x_288_);
v___x_290_ = lean_int_add(v___x_287_, v___x_289_);
lean_dec(v___x_289_);
lean_dec(v___x_287_);
v___x_291_ = l_Std_Time_Duration_ofNanoseconds(v___x_290_);
lean_dec(v___x_290_);
lean_inc_ref(v___x_291_);
v___f_292_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_292_, 0, v_tz_273_);
lean_closure_set(v___f_292_, 1, v___x_291_);
lean_closure_set(v___f_292_, 2, v___x_285_);
lean_closure_set(v___f_292_, 3, v___x_284_);
v___x_293_ = lean_mk_thunk(v___f_292_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v___x_293_);
lean_ctor_set(v___x_278_, 0, v___x_291_);
v___x_295_ = v___x_278_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object* v_tz_299_, lean_object* v_dt_300_, lean_object* v_minutes_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Std_Time_DateTime_addMinutes(v_tz_299_, v_dt_300_, v_minutes_301_);
lean_dec(v_minutes_301_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object* v_tz_303_, lean_object* v_dt_304_, lean_object* v_minutes_305_){
_start:
{
lean_object* v_timestamp_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_329_; 
v_timestamp_306_ = lean_ctor_get(v_dt_304_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_dt_304_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_dt_304_, 1);
lean_dec(v_unused_330_);
v___x_308_ = v_dt_304_;
v_isShared_309_ = v_isSharedCheck_329_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_timestamp_306_);
lean_dec(v_dt_304_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_329_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_second_310_; lean_object* v_nano_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v_second_310_ = lean_ctor_get(v_timestamp_306_, 0);
lean_inc(v_second_310_);
v_nano_311_ = lean_ctor_get(v_timestamp_306_, 1);
lean_inc(v_nano_311_);
lean_dec_ref(v_timestamp_306_);
v___x_312_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_313_ = lean_int_mul(v_minutes_305_, v___x_312_);
v___x_314_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_315_ = lean_int_neg(v___x_313_);
lean_dec(v___x_313_);
v___x_316_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_317_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_318_ = lean_int_mul(v_second_310_, v___x_317_);
lean_dec(v_second_310_);
v___x_319_ = lean_int_add(v___x_318_, v_nano_311_);
lean_dec(v_nano_311_);
lean_dec(v___x_318_);
v___x_320_ = lean_int_mul(v___x_315_, v___x_317_);
lean_dec(v___x_315_);
v___x_321_ = lean_int_add(v___x_320_, v___x_316_);
lean_dec(v___x_320_);
v___x_322_ = lean_int_add(v___x_319_, v___x_321_);
lean_dec(v___x_321_);
lean_dec(v___x_319_);
v___x_323_ = l_Std_Time_Duration_ofNanoseconds(v___x_322_);
lean_dec(v___x_322_);
lean_inc_ref(v___x_323_);
v___f_324_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_324_, 0, v_tz_303_);
lean_closure_set(v___f_324_, 1, v___x_323_);
lean_closure_set(v___f_324_, 2, v___x_317_);
lean_closure_set(v___f_324_, 3, v___x_314_);
v___x_325_ = lean_mk_thunk(v___f_324_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_325_);
lean_ctor_set(v___x_308_, 0, v___x_323_);
v___x_327_ = v___x_308_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object* v_tz_331_, lean_object* v_dt_332_, lean_object* v_minutes_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_Time_DateTime_subMinutes(v_tz_331_, v_dt_332_, v_minutes_333_);
lean_dec(v_minutes_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object* v_tz_335_, lean_object* v_dt_336_, lean_object* v_seconds_337_){
_start:
{
lean_object* v_timestamp_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_357_; 
v_timestamp_338_ = lean_ctor_get(v_dt_336_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v_dt_336_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v_dt_336_, 1);
lean_dec(v_unused_358_);
v___x_340_ = v_dt_336_;
v_isShared_341_ = v_isSharedCheck_357_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_timestamp_338_);
lean_dec(v_dt_336_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_357_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_second_342_; lean_object* v_nano_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___f_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v_second_342_ = lean_ctor_get(v_timestamp_338_, 0);
lean_inc(v_second_342_);
v_nano_343_ = lean_ctor_get(v_timestamp_338_, 1);
lean_inc(v_nano_343_);
lean_dec_ref(v_timestamp_338_);
v___x_344_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_345_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_346_ = lean_int_mul(v_second_342_, v___x_345_);
lean_dec(v_second_342_);
v___x_347_ = lean_int_add(v___x_346_, v_nano_343_);
lean_dec(v_nano_343_);
lean_dec(v___x_346_);
v___x_348_ = lean_int_mul(v_seconds_337_, v___x_345_);
v___x_349_ = lean_int_add(v___x_348_, v___x_344_);
lean_dec(v___x_348_);
v___x_350_ = lean_int_add(v___x_347_, v___x_349_);
lean_dec(v___x_349_);
lean_dec(v___x_347_);
v___x_351_ = l_Std_Time_Duration_ofNanoseconds(v___x_350_);
lean_dec(v___x_350_);
lean_inc_ref(v___x_351_);
v___f_352_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_352_, 0, v_tz_335_);
lean_closure_set(v___f_352_, 1, v___x_351_);
lean_closure_set(v___f_352_, 2, v___x_345_);
lean_closure_set(v___f_352_, 3, v___x_344_);
v___x_353_ = lean_mk_thunk(v___f_352_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 1, v___x_353_);
lean_ctor_set(v___x_340_, 0, v___x_351_);
v___x_355_ = v___x_340_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object* v_tz_359_, lean_object* v_dt_360_, lean_object* v_seconds_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Time_DateTime_addSeconds(v_tz_359_, v_dt_360_, v_seconds_361_);
lean_dec(v_seconds_361_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object* v_tz_363_, lean_object* v_dt_364_, lean_object* v_seconds_365_){
_start:
{
lean_object* v_timestamp_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_387_; 
v_timestamp_366_ = lean_ctor_get(v_dt_364_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_dt_364_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v_dt_364_, 1);
lean_dec(v_unused_388_);
v___x_368_ = v_dt_364_;
v_isShared_369_ = v_isSharedCheck_387_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_timestamp_366_);
lean_dec(v_dt_364_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_387_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_second_370_; lean_object* v_nano_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v_second_370_ = lean_ctor_get(v_timestamp_366_, 0);
lean_inc(v_second_370_);
v_nano_371_ = lean_ctor_get(v_timestamp_366_, 1);
lean_inc(v_nano_371_);
lean_dec_ref(v_timestamp_366_);
v___x_372_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_373_ = lean_int_neg(v_seconds_365_);
v___x_374_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_375_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_376_ = lean_int_mul(v_second_370_, v___x_375_);
lean_dec(v_second_370_);
v___x_377_ = lean_int_add(v___x_376_, v_nano_371_);
lean_dec(v_nano_371_);
lean_dec(v___x_376_);
v___x_378_ = lean_int_mul(v___x_373_, v___x_375_);
lean_dec(v___x_373_);
v___x_379_ = lean_int_add(v___x_378_, v___x_374_);
lean_dec(v___x_378_);
v___x_380_ = lean_int_add(v___x_377_, v___x_379_);
lean_dec(v___x_379_);
lean_dec(v___x_377_);
v___x_381_ = l_Std_Time_Duration_ofNanoseconds(v___x_380_);
lean_dec(v___x_380_);
lean_inc_ref(v___x_381_);
v___f_382_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_382_, 0, v_tz_363_);
lean_closure_set(v___f_382_, 1, v___x_381_);
lean_closure_set(v___f_382_, 2, v___x_375_);
lean_closure_set(v___f_382_, 3, v___x_372_);
v___x_383_ = lean_mk_thunk(v___f_382_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_383_);
lean_ctor_set(v___x_368_, 0, v___x_381_);
v___x_385_ = v___x_368_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object* v_tz_389_, lean_object* v_dt_390_, lean_object* v_seconds_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Time_DateTime_subSeconds(v_tz_389_, v_dt_390_, v_seconds_391_);
lean_dec(v_seconds_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0(lean_object* v_tz_393_, lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v_x_396_){
_start:
{
lean_object* v_offset_397_; lean_object* v_second_398_; lean_object* v_nano_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_offset_397_ = lean_ctor_get(v_tz_393_, 0);
v_second_398_ = lean_ctor_get(v___x_394_, 0);
v_nano_399_ = lean_ctor_get(v___x_394_, 1);
v___x_400_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_401_ = lean_int_mul(v_second_398_, v___x_395_);
v___x_402_ = lean_int_add(v___x_401_, v_nano_399_);
lean_dec(v___x_401_);
v___x_403_ = lean_int_mul(v_offset_397_, v___x_395_);
v___x_404_ = lean_int_add(v___x_403_, v___x_400_);
lean_dec(v___x_403_);
v___x_405_ = lean_int_add(v___x_402_, v___x_404_);
lean_dec(v___x_404_);
lean_dec(v___x_402_);
v___x_406_ = l_Std_Time_Duration_ofNanoseconds(v___x_405_);
lean_dec(v___x_405_);
v___x_407_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(lean_object* v_tz_408_, lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v_x_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_Time_DateTime_addMilliseconds___lam__0(v_tz_408_, v___x_409_, v___x_410_, v_x_411_);
lean_dec(v___x_410_);
lean_dec_ref(v___x_409_);
lean_dec_ref(v_tz_408_);
return v_res_412_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(1000000u);
v___x_414_ = lean_nat_to_int(v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object* v_tz_415_, lean_object* v_dt_416_, lean_object* v_milliseconds_417_){
_start:
{
lean_object* v_timestamp_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_441_; 
v_timestamp_418_ = lean_ctor_get(v_dt_416_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v_dt_416_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; 
v_unused_442_ = lean_ctor_get(v_dt_416_, 1);
lean_dec(v_unused_442_);
v___x_420_ = v_dt_416_;
v_isShared_421_ = v_isSharedCheck_441_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_timestamp_418_);
lean_dec(v_dt_416_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_441_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v_second_422_; lean_object* v_nano_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_second_427_; lean_object* v_nano_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v_second_422_ = lean_ctor_get(v_timestamp_418_, 0);
lean_inc(v_second_422_);
v_nano_423_ = lean_ctor_get(v_timestamp_418_, 1);
lean_inc(v_nano_423_);
lean_dec_ref(v_timestamp_418_);
v___x_424_ = lean_obj_once(&l_Std_Time_DateTime_addMilliseconds___closed__0, &l_Std_Time_DateTime_addMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_addMilliseconds___closed__0);
v___x_425_ = lean_int_mul(v_milliseconds_417_, v___x_424_);
v___x_426_ = l_Std_Time_Duration_ofNanoseconds(v___x_425_);
lean_dec(v___x_425_);
v_second_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_second_427_);
v_nano_428_ = lean_ctor_get(v___x_426_, 1);
lean_inc(v_nano_428_);
lean_dec_ref(v___x_426_);
v___x_429_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_430_ = lean_int_mul(v_second_422_, v___x_429_);
lean_dec(v_second_422_);
v___x_431_ = lean_int_add(v___x_430_, v_nano_423_);
lean_dec(v_nano_423_);
lean_dec(v___x_430_);
v___x_432_ = lean_int_mul(v_second_427_, v___x_429_);
lean_dec(v_second_427_);
v___x_433_ = lean_int_add(v___x_432_, v_nano_428_);
lean_dec(v_nano_428_);
lean_dec(v___x_432_);
v___x_434_ = lean_int_add(v___x_431_, v___x_433_);
lean_dec(v___x_433_);
lean_dec(v___x_431_);
v___x_435_ = l_Std_Time_Duration_ofNanoseconds(v___x_434_);
lean_dec(v___x_434_);
lean_inc_ref(v___x_435_);
v___f_436_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_436_, 0, v_tz_415_);
lean_closure_set(v___f_436_, 1, v___x_435_);
lean_closure_set(v___f_436_, 2, v___x_429_);
v___x_437_ = lean_mk_thunk(v___f_436_);
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 1, v___x_437_);
lean_ctor_set(v___x_420_, 0, v___x_435_);
v___x_439_ = v___x_420_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_435_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object* v_tz_443_, lean_object* v_dt_444_, lean_object* v_milliseconds_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_Time_DateTime_addMilliseconds(v_tz_443_, v_dt_444_, v_milliseconds_445_);
lean_dec(v_milliseconds_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object* v_tz_447_, lean_object* v_dt_448_, lean_object* v_milliseconds_449_){
_start:
{
lean_object* v_timestamp_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_475_; 
v_timestamp_450_ = lean_ctor_get(v_dt_448_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_dt_448_);
if (v_isSharedCheck_475_ == 0)
{
lean_object* v_unused_476_; 
v_unused_476_ = lean_ctor_get(v_dt_448_, 1);
lean_dec(v_unused_476_);
v___x_452_ = v_dt_448_;
v_isShared_453_ = v_isSharedCheck_475_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_timestamp_450_);
lean_dec(v_dt_448_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_475_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_second_457_; lean_object* v_nano_458_; lean_object* v_second_459_; lean_object* v_nano_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_454_ = lean_obj_once(&l_Std_Time_DateTime_addMilliseconds___closed__0, &l_Std_Time_DateTime_addMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_addMilliseconds___closed__0);
v___x_455_ = lean_int_mul(v_milliseconds_449_, v___x_454_);
v___x_456_ = l_Std_Time_Duration_ofNanoseconds(v___x_455_);
lean_dec(v___x_455_);
v_second_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_second_457_);
v_nano_458_ = lean_ctor_get(v___x_456_, 1);
lean_inc(v_nano_458_);
lean_dec_ref(v___x_456_);
v_second_459_ = lean_ctor_get(v_timestamp_450_, 0);
lean_inc(v_second_459_);
v_nano_460_ = lean_ctor_get(v_timestamp_450_, 1);
lean_inc(v_nano_460_);
lean_dec_ref(v_timestamp_450_);
v___x_461_ = lean_int_neg(v_second_457_);
lean_dec(v_second_457_);
v___x_462_ = lean_int_neg(v_nano_458_);
lean_dec(v_nano_458_);
v___x_463_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_464_ = lean_int_mul(v_second_459_, v___x_463_);
lean_dec(v_second_459_);
v___x_465_ = lean_int_add(v___x_464_, v_nano_460_);
lean_dec(v_nano_460_);
lean_dec(v___x_464_);
v___x_466_ = lean_int_mul(v___x_461_, v___x_463_);
lean_dec(v___x_461_);
v___x_467_ = lean_int_add(v___x_466_, v___x_462_);
lean_dec(v___x_462_);
lean_dec(v___x_466_);
v___x_468_ = lean_int_add(v___x_465_, v___x_467_);
lean_dec(v___x_467_);
lean_dec(v___x_465_);
v___x_469_ = l_Std_Time_Duration_ofNanoseconds(v___x_468_);
lean_dec(v___x_468_);
lean_inc_ref(v___x_469_);
v___f_470_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_470_, 0, v_tz_447_);
lean_closure_set(v___f_470_, 1, v___x_469_);
lean_closure_set(v___f_470_, 2, v___x_463_);
v___x_471_ = lean_mk_thunk(v___f_470_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_471_);
lean_ctor_set(v___x_452_, 0, v___x_469_);
v___x_473_ = v___x_452_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object* v_tz_477_, lean_object* v_dt_478_, lean_object* v_milliseconds_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_Time_DateTime_subMilliseconds(v_tz_477_, v_dt_478_, v_milliseconds_479_);
lean_dec(v_milliseconds_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object* v_tz_481_, lean_object* v_dt_482_, lean_object* v_nanoseconds_483_){
_start:
{
lean_object* v_timestamp_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_505_; 
v_timestamp_484_ = lean_ctor_get(v_dt_482_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v_dt_482_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_dt_482_, 1);
lean_dec(v_unused_506_);
v___x_486_ = v_dt_482_;
v_isShared_487_ = v_isSharedCheck_505_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_timestamp_484_);
lean_dec(v_dt_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_505_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v_second_488_; lean_object* v_nano_489_; lean_object* v___x_490_; lean_object* v_second_491_; lean_object* v_nano_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v_second_488_ = lean_ctor_get(v_timestamp_484_, 0);
lean_inc(v_second_488_);
v_nano_489_ = lean_ctor_get(v_timestamp_484_, 1);
lean_inc(v_nano_489_);
lean_dec_ref(v_timestamp_484_);
v___x_490_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_483_);
v_second_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_second_491_);
v_nano_492_ = lean_ctor_get(v___x_490_, 1);
lean_inc(v_nano_492_);
lean_dec_ref(v___x_490_);
v___x_493_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_494_ = lean_int_mul(v_second_488_, v___x_493_);
lean_dec(v_second_488_);
v___x_495_ = lean_int_add(v___x_494_, v_nano_489_);
lean_dec(v_nano_489_);
lean_dec(v___x_494_);
v___x_496_ = lean_int_mul(v_second_491_, v___x_493_);
lean_dec(v_second_491_);
v___x_497_ = lean_int_add(v___x_496_, v_nano_492_);
lean_dec(v_nano_492_);
lean_dec(v___x_496_);
v___x_498_ = lean_int_add(v___x_495_, v___x_497_);
lean_dec(v___x_497_);
lean_dec(v___x_495_);
v___x_499_ = l_Std_Time_Duration_ofNanoseconds(v___x_498_);
lean_dec(v___x_498_);
lean_inc_ref(v___x_499_);
v___f_500_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_500_, 0, v_tz_481_);
lean_closure_set(v___f_500_, 1, v___x_499_);
lean_closure_set(v___f_500_, 2, v___x_493_);
v___x_501_ = lean_mk_thunk(v___f_500_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_501_);
lean_ctor_set(v___x_486_, 0, v___x_499_);
v___x_503_ = v___x_486_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object* v_tz_507_, lean_object* v_dt_508_, lean_object* v_nanoseconds_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_Time_DateTime_addNanoseconds(v_tz_507_, v_dt_508_, v_nanoseconds_509_);
lean_dec(v_nanoseconds_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object* v_tz_511_, lean_object* v_dt_512_, lean_object* v_nanoseconds_513_){
_start:
{
lean_object* v_timestamp_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_537_; 
v_timestamp_514_ = lean_ctor_get(v_dt_512_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v_dt_512_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v_dt_512_, 1);
lean_dec(v_unused_538_);
v___x_516_ = v_dt_512_;
v_isShared_517_ = v_isSharedCheck_537_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_timestamp_514_);
lean_dec(v_dt_512_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_537_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v_second_519_; lean_object* v_nano_520_; lean_object* v_second_521_; lean_object* v_nano_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_518_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_513_);
v_second_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_second_519_);
v_nano_520_ = lean_ctor_get(v___x_518_, 1);
lean_inc(v_nano_520_);
lean_dec_ref(v___x_518_);
v_second_521_ = lean_ctor_get(v_timestamp_514_, 0);
lean_inc(v_second_521_);
v_nano_522_ = lean_ctor_get(v_timestamp_514_, 1);
lean_inc(v_nano_522_);
lean_dec_ref(v_timestamp_514_);
v___x_523_ = lean_int_neg(v_second_519_);
lean_dec(v_second_519_);
v___x_524_ = lean_int_neg(v_nano_520_);
lean_dec(v_nano_520_);
v___x_525_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_526_ = lean_int_mul(v_second_521_, v___x_525_);
lean_dec(v_second_521_);
v___x_527_ = lean_int_add(v___x_526_, v_nano_522_);
lean_dec(v_nano_522_);
lean_dec(v___x_526_);
v___x_528_ = lean_int_mul(v___x_523_, v___x_525_);
lean_dec(v___x_523_);
v___x_529_ = lean_int_add(v___x_528_, v___x_524_);
lean_dec(v___x_524_);
lean_dec(v___x_528_);
v___x_530_ = lean_int_add(v___x_527_, v___x_529_);
lean_dec(v___x_529_);
lean_dec(v___x_527_);
v___x_531_ = l_Std_Time_Duration_ofNanoseconds(v___x_530_);
lean_dec(v___x_530_);
lean_inc_ref(v___x_531_);
v___f_532_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_532_, 0, v_tz_511_);
lean_closure_set(v___f_532_, 1, v___x_531_);
lean_closure_set(v___f_532_, 2, v___x_525_);
v___x_533_ = lean_mk_thunk(v___f_532_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___x_533_);
lean_ctor_set(v___x_516_, 0, v___x_531_);
v___x_535_ = v___x_516_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object* v_tz_539_, lean_object* v_dt_540_, lean_object* v_nanoseconds_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_Time_DateTime_subNanoseconds(v_tz_539_, v_dt_540_, v_nanoseconds_541_);
lean_dec(v_nanoseconds_541_);
return v_res_542_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addDays___closed__0(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_unsigned_to_nat(86400u);
v___x_544_ = lean_nat_to_int(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object* v_tz_545_, lean_object* v_dt_546_, lean_object* v_days_547_){
_start:
{
lean_object* v_timestamp_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_569_; 
v_timestamp_548_ = lean_ctor_get(v_dt_546_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v_dt_546_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v_dt_546_, 1);
lean_dec(v_unused_570_);
v___x_550_ = v_dt_546_;
v_isShared_551_ = v_isSharedCheck_569_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_timestamp_548_);
lean_dec(v_dt_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_569_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_second_552_; lean_object* v_nano_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___f_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v_second_552_ = lean_ctor_get(v_timestamp_548_, 0);
lean_inc(v_second_552_);
v_nano_553_ = lean_ctor_get(v_timestamp_548_, 1);
lean_inc(v_nano_553_);
lean_dec_ref(v_timestamp_548_);
v___x_554_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_555_ = lean_int_mul(v_days_547_, v___x_554_);
v___x_556_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_557_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_558_ = lean_int_mul(v_second_552_, v___x_557_);
lean_dec(v_second_552_);
v___x_559_ = lean_int_add(v___x_558_, v_nano_553_);
lean_dec(v_nano_553_);
lean_dec(v___x_558_);
v___x_560_ = lean_int_mul(v___x_555_, v___x_557_);
lean_dec(v___x_555_);
v___x_561_ = lean_int_add(v___x_560_, v___x_556_);
lean_dec(v___x_560_);
v___x_562_ = lean_int_add(v___x_559_, v___x_561_);
lean_dec(v___x_561_);
lean_dec(v___x_559_);
v___x_563_ = l_Std_Time_Duration_ofNanoseconds(v___x_562_);
lean_dec(v___x_562_);
lean_inc_ref(v___x_563_);
v___f_564_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_564_, 0, v_tz_545_);
lean_closure_set(v___f_564_, 1, v___x_563_);
lean_closure_set(v___f_564_, 2, v___x_557_);
lean_closure_set(v___f_564_, 3, v___x_556_);
v___x_565_ = lean_mk_thunk(v___f_564_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_565_);
lean_ctor_set(v___x_550_, 0, v___x_563_);
v___x_567_ = v___x_550_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object* v_tz_571_, lean_object* v_dt_572_, lean_object* v_days_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Time_DateTime_addDays(v_tz_571_, v_dt_572_, v_days_573_);
lean_dec(v_days_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object* v_tz_575_, lean_object* v_dt_576_, lean_object* v_days_577_){
_start:
{
lean_object* v_timestamp_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_601_; 
v_timestamp_578_ = lean_ctor_get(v_dt_576_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_dt_576_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_dt_576_, 1);
lean_dec(v_unused_602_);
v___x_580_ = v_dt_576_;
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_timestamp_578_);
lean_dec(v_dt_576_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_601_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_second_582_; lean_object* v_nano_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v_second_582_ = lean_ctor_get(v_timestamp_578_, 0);
lean_inc(v_second_582_);
v_nano_583_ = lean_ctor_get(v_timestamp_578_, 1);
lean_inc(v_nano_583_);
lean_dec_ref(v_timestamp_578_);
v___x_584_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_585_ = lean_int_mul(v_days_577_, v___x_584_);
v___x_586_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_587_ = lean_int_neg(v___x_585_);
lean_dec(v___x_585_);
v___x_588_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_589_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_590_ = lean_int_mul(v_second_582_, v___x_589_);
lean_dec(v_second_582_);
v___x_591_ = lean_int_add(v___x_590_, v_nano_583_);
lean_dec(v_nano_583_);
lean_dec(v___x_590_);
v___x_592_ = lean_int_mul(v___x_587_, v___x_589_);
lean_dec(v___x_587_);
v___x_593_ = lean_int_add(v___x_592_, v___x_588_);
lean_dec(v___x_592_);
v___x_594_ = lean_int_add(v___x_591_, v___x_593_);
lean_dec(v___x_593_);
lean_dec(v___x_591_);
v___x_595_ = l_Std_Time_Duration_ofNanoseconds(v___x_594_);
lean_dec(v___x_594_);
lean_inc_ref(v___x_595_);
v___f_596_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_596_, 0, v_tz_575_);
lean_closure_set(v___f_596_, 1, v___x_595_);
lean_closure_set(v___f_596_, 2, v___x_589_);
lean_closure_set(v___f_596_, 3, v___x_586_);
v___x_597_ = lean_mk_thunk(v___f_596_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_597_);
lean_ctor_set(v___x_580_, 0, v___x_595_);
v___x_599_ = v___x_580_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_595_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object* v_tz_603_, lean_object* v_dt_604_, lean_object* v_days_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Std_Time_DateTime_subDays(v_tz_603_, v_dt_604_, v_days_605_);
lean_dec(v_days_605_);
return v_res_606_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(7u);
v___x_608_ = lean_nat_to_int(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object* v_tz_609_, lean_object* v_dt_610_, lean_object* v_weeks_611_){
_start:
{
lean_object* v_timestamp_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_635_; 
v_timestamp_612_ = lean_ctor_get(v_dt_610_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v_dt_610_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_dt_610_, 1);
lean_dec(v_unused_636_);
v___x_614_ = v_dt_610_;
v_isShared_615_ = v_isSharedCheck_635_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_timestamp_612_);
lean_dec(v_dt_610_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_635_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_second_616_; lean_object* v_nano_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v_second_616_ = lean_ctor_get(v_timestamp_612_, 0);
lean_inc(v_second_616_);
v_nano_617_ = lean_ctor_get(v_timestamp_612_, 1);
lean_inc(v_nano_617_);
lean_dec_ref(v_timestamp_612_);
v___x_618_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_619_ = lean_int_mul(v_weeks_611_, v___x_618_);
v___x_620_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_621_ = lean_int_mul(v___x_619_, v___x_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_623_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_624_ = lean_int_mul(v_second_616_, v___x_623_);
lean_dec(v_second_616_);
v___x_625_ = lean_int_add(v___x_624_, v_nano_617_);
lean_dec(v_nano_617_);
lean_dec(v___x_624_);
v___x_626_ = lean_int_mul(v___x_621_, v___x_623_);
lean_dec(v___x_621_);
v___x_627_ = lean_int_add(v___x_626_, v___x_622_);
lean_dec(v___x_626_);
v___x_628_ = lean_int_add(v___x_625_, v___x_627_);
lean_dec(v___x_627_);
lean_dec(v___x_625_);
v___x_629_ = l_Std_Time_Duration_ofNanoseconds(v___x_628_);
lean_dec(v___x_628_);
lean_inc_ref(v___x_629_);
v___f_630_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_630_, 0, v_tz_609_);
lean_closure_set(v___f_630_, 1, v___x_629_);
lean_closure_set(v___f_630_, 2, v___x_623_);
lean_closure_set(v___f_630_, 3, v___x_622_);
v___x_631_ = lean_mk_thunk(v___f_630_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_631_);
lean_ctor_set(v___x_614_, 0, v___x_629_);
v___x_633_ = v___x_614_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object* v_tz_637_, lean_object* v_dt_638_, lean_object* v_weeks_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_Time_DateTime_addWeeks(v_tz_637_, v_dt_638_, v_weeks_639_);
lean_dec(v_weeks_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object* v_tz_641_, lean_object* v_dt_642_, lean_object* v_weeks_643_){
_start:
{
lean_object* v_timestamp_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_669_; 
v_timestamp_644_ = lean_ctor_get(v_dt_642_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v_dt_642_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_dt_642_, 1);
lean_dec(v_unused_670_);
v___x_646_ = v_dt_642_;
v_isShared_647_ = v_isSharedCheck_669_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_timestamp_644_);
lean_dec(v_dt_642_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_669_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_second_648_; lean_object* v_nano_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v_second_648_ = lean_ctor_get(v_timestamp_644_, 0);
lean_inc(v_second_648_);
v_nano_649_ = lean_ctor_get(v_timestamp_644_, 1);
lean_inc(v_nano_649_);
lean_dec_ref(v_timestamp_644_);
v___x_650_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_651_ = lean_int_mul(v_weeks_643_, v___x_650_);
v___x_652_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_653_ = lean_int_mul(v___x_651_, v___x_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_655_ = lean_int_neg(v___x_653_);
lean_dec(v___x_653_);
v___x_656_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_657_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_658_ = lean_int_mul(v_second_648_, v___x_657_);
lean_dec(v_second_648_);
v___x_659_ = lean_int_add(v___x_658_, v_nano_649_);
lean_dec(v_nano_649_);
lean_dec(v___x_658_);
v___x_660_ = lean_int_mul(v___x_655_, v___x_657_);
lean_dec(v___x_655_);
v___x_661_ = lean_int_add(v___x_660_, v___x_656_);
lean_dec(v___x_660_);
v___x_662_ = lean_int_add(v___x_659_, v___x_661_);
lean_dec(v___x_661_);
lean_dec(v___x_659_);
v___x_663_ = l_Std_Time_Duration_ofNanoseconds(v___x_662_);
lean_dec(v___x_662_);
lean_inc_ref(v___x_663_);
v___f_664_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___lam__0___boxed), 5, 4);
lean_closure_set(v___f_664_, 0, v_tz_641_);
lean_closure_set(v___f_664_, 1, v___x_663_);
lean_closure_set(v___f_664_, 2, v___x_657_);
lean_closure_set(v___f_664_, 3, v___x_654_);
v___x_665_ = lean_mk_thunk(v___f_664_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___x_665_);
lean_ctor_set(v___x_646_, 0, v___x_663_);
v___x_667_ = v___x_646_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object* v_tz_671_, lean_object* v_dt_672_, lean_object* v_weeks_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_Time_DateTime_subWeeks(v_tz_671_, v_dt_672_, v_weeks_673_);
lean_dec(v_weeks_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0(lean_object* v___x_675_, lean_object* v_x_676_){
_start:
{
lean_inc_ref(v___x_675_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(lean_object* v___x_677_, lean_object* v_x_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_Time_DateTime_addMonthsClip___lam__0(v___x_677_, v_x_678_);
lean_dec_ref(v___x_677_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object* v_tz_680_, lean_object* v_dt_681_, lean_object* v_months_682_){
_start:
{
lean_object* v_date_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_707_; 
v_date_683_ = lean_ctor_get(v_dt_681_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_dt_681_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_dt_681_, 0);
lean_dec(v_unused_708_);
v___x_685_ = v_dt_681_;
v_isShared_686_ = v_isSharedCheck_707_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_date_683_);
lean_dec(v_dt_681_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_707_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_offset_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v_second_691_; lean_object* v_nano_692_; lean_object* v___f_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v_tm_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v_offset_687_ = lean_ctor_get(v_tz_680_, 0);
v___x_688_ = lean_thunk_get_own(v_date_683_);
lean_dec_ref(v_date_683_);
v___x_689_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_688_, v_months_682_);
lean_inc_ref(v___x_689_);
v___x_690_ = l_Std_Time_PlainDateTime_toWallTime(v___x_689_);
v_second_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_second_691_);
v_nano_692_ = lean_ctor_get(v___x_690_, 1);
lean_inc(v_nano_692_);
lean_dec_ref(v___x_690_);
v___f_693_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_693_, 0, v___x_689_);
v___x_694_ = lean_int_neg(v_offset_687_);
v___x_695_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_696_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_697_ = lean_int_mul(v_second_691_, v___x_696_);
lean_dec(v_second_691_);
v___x_698_ = lean_int_add(v___x_697_, v_nano_692_);
lean_dec(v_nano_692_);
lean_dec(v___x_697_);
v___x_699_ = lean_int_mul(v___x_694_, v___x_696_);
lean_dec(v___x_694_);
v___x_700_ = lean_int_add(v___x_699_, v___x_695_);
lean_dec(v___x_699_);
v___x_701_ = lean_int_add(v___x_698_, v___x_700_);
lean_dec(v___x_700_);
lean_dec(v___x_698_);
v_tm_702_ = l_Std_Time_Duration_ofNanoseconds(v___x_701_);
lean_dec(v___x_701_);
v___x_703_ = lean_mk_thunk(v___f_693_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v___x_703_);
lean_ctor_set(v___x_685_, 0, v_tm_702_);
v___x_705_ = v___x_685_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_tm_702_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object* v_tz_709_, lean_object* v_dt_710_, lean_object* v_months_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_Time_DateTime_addMonthsClip(v_tz_709_, v_dt_710_, v_months_711_);
lean_dec(v_months_711_);
lean_dec_ref(v_tz_709_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object* v_tz_713_, lean_object* v_dt_714_, lean_object* v_months_715_){
_start:
{
lean_object* v_date_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_750_; 
v_date_716_ = lean_ctor_get(v_dt_714_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v_dt_714_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; 
v_unused_751_ = lean_ctor_get(v_dt_714_, 0);
lean_dec(v_unused_751_);
v___x_718_ = v_dt_714_;
v_isShared_719_ = v_isSharedCheck_750_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_date_716_);
lean_dec(v_dt_714_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_750_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v_date_721_; lean_object* v_time_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_749_; 
v___x_720_ = lean_thunk_get_own(v_date_716_);
lean_dec_ref(v_date_716_);
v_date_721_ = lean_ctor_get(v___x_720_, 0);
v_time_722_ = lean_ctor_get(v___x_720_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_749_ == 0)
{
v___x_724_ = v___x_720_;
v_isShared_725_ = v_isSharedCheck_749_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_time_722_);
lean_inc(v_date_721_);
lean_dec(v___x_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_749_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v_offset_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v_offset_726_ = lean_ctor_get(v_tz_713_, 0);
v___x_727_ = lean_int_neg(v_months_715_);
v___x_728_ = l_Std_Time_PlainDate_addMonthsClip(v_date_721_, v___x_727_);
lean_dec(v___x_727_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_728_);
v___x_730_ = v___x_724_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_time_722_);
v___x_730_ = v_reuseFailAlloc_748_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_731_; lean_object* v_second_732_; lean_object* v_nano_733_; lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_tm_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
lean_inc_ref(v___x_730_);
v___x_731_ = l_Std_Time_PlainDateTime_toWallTime(v___x_730_);
v_second_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_second_732_);
v_nano_733_ = lean_ctor_get(v___x_731_, 1);
lean_inc(v_nano_733_);
lean_dec_ref(v___x_731_);
v___f_734_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_734_, 0, v___x_730_);
v___x_735_ = lean_int_neg(v_offset_726_);
v___x_736_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_737_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_738_ = lean_int_mul(v_second_732_, v___x_737_);
lean_dec(v_second_732_);
v___x_739_ = lean_int_add(v___x_738_, v_nano_733_);
lean_dec(v_nano_733_);
lean_dec(v___x_738_);
v___x_740_ = lean_int_mul(v___x_735_, v___x_737_);
lean_dec(v___x_735_);
v___x_741_ = lean_int_add(v___x_740_, v___x_736_);
lean_dec(v___x_740_);
v___x_742_ = lean_int_add(v___x_739_, v___x_741_);
lean_dec(v___x_741_);
lean_dec(v___x_739_);
v_tm_743_ = l_Std_Time_Duration_ofNanoseconds(v___x_742_);
lean_dec(v___x_742_);
v___x_744_ = lean_mk_thunk(v___f_734_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_744_);
lean_ctor_set(v___x_718_, 0, v_tm_743_);
v___x_746_ = v___x_718_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_tm_743_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object* v_tz_752_, lean_object* v_dt_753_, lean_object* v_months_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Std_Time_DateTime_subMonthsClip(v_tz_752_, v_dt_753_, v_months_754_);
lean_dec(v_months_754_);
lean_dec_ref(v_tz_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object* v_tz_756_, lean_object* v_dt_757_, lean_object* v_months_758_){
_start:
{
lean_object* v_date_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_783_; 
v_date_759_ = lean_ctor_get(v_dt_757_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_dt_757_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_dt_757_, 0);
lean_dec(v_unused_784_);
v___x_761_ = v_dt_757_;
v_isShared_762_ = v_isSharedCheck_783_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_date_759_);
lean_dec(v_dt_757_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_783_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v_offset_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_second_767_; lean_object* v_nano_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v_tm_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v_offset_763_ = lean_ctor_get(v_tz_756_, 0);
v___x_764_ = lean_thunk_get_own(v_date_759_);
lean_dec_ref(v_date_759_);
v___x_765_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_764_, v_months_758_);
lean_inc_ref(v___x_765_);
v___x_766_ = l_Std_Time_PlainDateTime_toWallTime(v___x_765_);
v_second_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_second_767_);
v_nano_768_ = lean_ctor_get(v___x_766_, 1);
lean_inc(v_nano_768_);
lean_dec_ref(v___x_766_);
v___f_769_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_769_, 0, v___x_765_);
v___x_770_ = lean_int_neg(v_offset_763_);
v___x_771_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_772_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_773_ = lean_int_mul(v_second_767_, v___x_772_);
lean_dec(v_second_767_);
v___x_774_ = lean_int_add(v___x_773_, v_nano_768_);
lean_dec(v_nano_768_);
lean_dec(v___x_773_);
v___x_775_ = lean_int_mul(v___x_770_, v___x_772_);
lean_dec(v___x_770_);
v___x_776_ = lean_int_add(v___x_775_, v___x_771_);
lean_dec(v___x_775_);
v___x_777_ = lean_int_add(v___x_774_, v___x_776_);
lean_dec(v___x_776_);
lean_dec(v___x_774_);
v_tm_778_ = l_Std_Time_Duration_ofNanoseconds(v___x_777_);
lean_dec(v___x_777_);
v___x_779_ = lean_mk_thunk(v___f_769_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 1, v___x_779_);
lean_ctor_set(v___x_761_, 0, v_tm_778_);
v___x_781_ = v___x_761_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_tm_778_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object* v_tz_785_, lean_object* v_dt_786_, lean_object* v_months_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Std_Time_DateTime_addMonthsRollOver(v_tz_785_, v_dt_786_, v_months_787_);
lean_dec(v_months_787_);
lean_dec_ref(v_tz_785_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object* v_tz_789_, lean_object* v_dt_790_, lean_object* v_months_791_){
_start:
{
lean_object* v_date_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_826_; 
v_date_792_ = lean_ctor_get(v_dt_790_, 1);
v_isSharedCheck_826_ = !lean_is_exclusive(v_dt_790_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_dt_790_, 0);
lean_dec(v_unused_827_);
v___x_794_ = v_dt_790_;
v_isShared_795_ = v_isSharedCheck_826_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_date_792_);
lean_dec(v_dt_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_826_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v_date_797_; lean_object* v_time_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_825_; 
v___x_796_ = lean_thunk_get_own(v_date_792_);
lean_dec_ref(v_date_792_);
v_date_797_ = lean_ctor_get(v___x_796_, 0);
v_time_798_ = lean_ctor_get(v___x_796_, 1);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_825_ == 0)
{
v___x_800_ = v___x_796_;
v_isShared_801_ = v_isSharedCheck_825_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_time_798_);
lean_inc(v_date_797_);
lean_dec(v___x_796_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_825_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_offset_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_806_; 
v_offset_802_ = lean_ctor_get(v_tz_789_, 0);
v___x_803_ = lean_int_neg(v_months_791_);
v___x_804_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_797_, v___x_803_);
lean_dec(v___x_803_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v___x_804_);
v___x_806_ = v___x_800_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v_time_798_);
v___x_806_ = v_reuseFailAlloc_824_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v_second_808_; lean_object* v_nano_809_; lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_tm_819_; lean_object* v___x_820_; lean_object* v___x_822_; 
lean_inc_ref(v___x_806_);
v___x_807_ = l_Std_Time_PlainDateTime_toWallTime(v___x_806_);
v_second_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_second_808_);
v_nano_809_ = lean_ctor_get(v___x_807_, 1);
lean_inc(v_nano_809_);
lean_dec_ref(v___x_807_);
v___f_810_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_810_, 0, v___x_806_);
v___x_811_ = lean_int_neg(v_offset_802_);
v___x_812_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_813_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_814_ = lean_int_mul(v_second_808_, v___x_813_);
lean_dec(v_second_808_);
v___x_815_ = lean_int_add(v___x_814_, v_nano_809_);
lean_dec(v_nano_809_);
lean_dec(v___x_814_);
v___x_816_ = lean_int_mul(v___x_811_, v___x_813_);
lean_dec(v___x_811_);
v___x_817_ = lean_int_add(v___x_816_, v___x_812_);
lean_dec(v___x_816_);
v___x_818_ = lean_int_add(v___x_815_, v___x_817_);
lean_dec(v___x_817_);
lean_dec(v___x_815_);
v_tm_819_ = l_Std_Time_Duration_ofNanoseconds(v___x_818_);
lean_dec(v___x_818_);
v___x_820_ = lean_mk_thunk(v___f_810_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 1, v___x_820_);
lean_ctor_set(v___x_794_, 0, v_tm_819_);
v___x_822_ = v___x_794_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_tm_819_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object* v_tz_828_, lean_object* v_dt_829_, lean_object* v_months_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_Time_DateTime_subMonthsRollOver(v_tz_828_, v_dt_829_, v_months_830_);
lean_dec(v_months_830_);
lean_dec_ref(v_tz_828_);
return v_res_831_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(12u);
v___x_833_ = lean_nat_to_int(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object* v_tz_834_, lean_object* v_dt_835_, lean_object* v_years_836_){
_start:
{
lean_object* v_date_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_872_; 
v_date_837_ = lean_ctor_get(v_dt_835_, 1);
v_isSharedCheck_872_ = !lean_is_exclusive(v_dt_835_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v_dt_835_, 0);
lean_dec(v_unused_873_);
v___x_839_ = v_dt_835_;
v_isShared_840_ = v_isSharedCheck_872_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_date_837_);
lean_dec(v_dt_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_872_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v_date_842_; lean_object* v_time_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_871_; 
v___x_841_ = lean_thunk_get_own(v_date_837_);
lean_dec_ref(v_date_837_);
v_date_842_ = lean_ctor_get(v___x_841_, 0);
v_time_843_ = lean_ctor_get(v___x_841_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_871_ == 0)
{
v___x_845_ = v___x_841_;
v_isShared_846_ = v_isSharedCheck_871_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_time_843_);
lean_inc(v_date_842_);
lean_dec(v___x_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_871_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_offset_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v_offset_847_ = lean_ctor_get(v_tz_834_, 0);
v___x_848_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_849_ = lean_int_mul(v_years_836_, v___x_848_);
v___x_850_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_842_, v___x_849_);
lean_dec(v___x_849_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_850_);
v___x_852_ = v___x_845_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_time_843_);
v___x_852_ = v_reuseFailAlloc_870_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_853_; lean_object* v_second_854_; lean_object* v_nano_855_; lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_tm_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_inc_ref(v___x_852_);
v___x_853_ = l_Std_Time_PlainDateTime_toWallTime(v___x_852_);
v_second_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_second_854_);
v_nano_855_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_nano_855_);
lean_dec_ref(v___x_853_);
v___f_856_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_856_, 0, v___x_852_);
v___x_857_ = lean_int_neg(v_offset_847_);
v___x_858_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_859_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_860_ = lean_int_mul(v_second_854_, v___x_859_);
lean_dec(v_second_854_);
v___x_861_ = lean_int_add(v___x_860_, v_nano_855_);
lean_dec(v_nano_855_);
lean_dec(v___x_860_);
v___x_862_ = lean_int_mul(v___x_857_, v___x_859_);
lean_dec(v___x_857_);
v___x_863_ = lean_int_add(v___x_862_, v___x_858_);
lean_dec(v___x_862_);
v___x_864_ = lean_int_add(v___x_861_, v___x_863_);
lean_dec(v___x_863_);
lean_dec(v___x_861_);
v_tm_865_ = l_Std_Time_Duration_ofNanoseconds(v___x_864_);
lean_dec(v___x_864_);
v___x_866_ = lean_mk_thunk(v___f_856_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_866_);
lean_ctor_set(v___x_839_, 0, v_tm_865_);
v___x_868_ = v___x_839_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_tm_865_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object* v_tz_874_, lean_object* v_dt_875_, lean_object* v_years_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_Time_DateTime_addYearsRollOver(v_tz_874_, v_dt_875_, v_years_876_);
lean_dec(v_years_876_);
lean_dec_ref(v_tz_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object* v_tz_878_, lean_object* v_dt_879_, lean_object* v_years_880_){
_start:
{
lean_object* v_date_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_916_; 
v_date_881_ = lean_ctor_get(v_dt_879_, 1);
v_isSharedCheck_916_ = !lean_is_exclusive(v_dt_879_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v_dt_879_, 0);
lean_dec(v_unused_917_);
v___x_883_ = v_dt_879_;
v_isShared_884_ = v_isSharedCheck_916_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_date_881_);
lean_dec(v_dt_879_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_916_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v_date_886_; lean_object* v_time_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_915_; 
v___x_885_ = lean_thunk_get_own(v_date_881_);
lean_dec_ref(v_date_881_);
v_date_886_ = lean_ctor_get(v___x_885_, 0);
v_time_887_ = lean_ctor_get(v___x_885_, 1);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_915_ == 0)
{
v___x_889_ = v___x_885_;
v_isShared_890_ = v_isSharedCheck_915_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_time_887_);
lean_inc(v_date_886_);
lean_dec(v___x_885_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_915_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_offset_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v_offset_891_ = lean_ctor_get(v_tz_878_, 0);
v___x_892_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_893_ = lean_int_mul(v_years_880_, v___x_892_);
v___x_894_ = l_Std_Time_PlainDate_addMonthsClip(v_date_886_, v___x_893_);
lean_dec(v___x_893_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_894_);
v___x_896_ = v___x_889_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v_time_887_);
v___x_896_ = v_reuseFailAlloc_914_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v_second_898_; lean_object* v_nano_899_; lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v_tm_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
lean_inc_ref(v___x_896_);
v___x_897_ = l_Std_Time_PlainDateTime_toWallTime(v___x_896_);
v_second_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_second_898_);
v_nano_899_ = lean_ctor_get(v___x_897_, 1);
lean_inc(v_nano_899_);
lean_dec_ref(v___x_897_);
v___f_900_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_900_, 0, v___x_896_);
v___x_901_ = lean_int_neg(v_offset_891_);
v___x_902_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_903_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_904_ = lean_int_mul(v_second_898_, v___x_903_);
lean_dec(v_second_898_);
v___x_905_ = lean_int_add(v___x_904_, v_nano_899_);
lean_dec(v_nano_899_);
lean_dec(v___x_904_);
v___x_906_ = lean_int_mul(v___x_901_, v___x_903_);
lean_dec(v___x_901_);
v___x_907_ = lean_int_add(v___x_906_, v___x_902_);
lean_dec(v___x_906_);
v___x_908_ = lean_int_add(v___x_905_, v___x_907_);
lean_dec(v___x_907_);
lean_dec(v___x_905_);
v_tm_909_ = l_Std_Time_Duration_ofNanoseconds(v___x_908_);
lean_dec(v___x_908_);
v___x_910_ = lean_mk_thunk(v___f_900_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v___x_910_);
lean_ctor_set(v___x_883_, 0, v_tm_909_);
v___x_912_ = v___x_883_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_tm_909_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object* v_tz_918_, lean_object* v_dt_919_, lean_object* v_years_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_Time_DateTime_addYearsClip(v_tz_918_, v_dt_919_, v_years_920_);
lean_dec(v_years_920_);
lean_dec_ref(v_tz_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object* v_tz_922_, lean_object* v_dt_923_, lean_object* v_years_924_){
_start:
{
lean_object* v_date_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_961_; 
v_date_925_ = lean_ctor_get(v_dt_923_, 1);
v_isSharedCheck_961_ = !lean_is_exclusive(v_dt_923_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; 
v_unused_962_ = lean_ctor_get(v_dt_923_, 0);
lean_dec(v_unused_962_);
v___x_927_ = v_dt_923_;
v_isShared_928_ = v_isSharedCheck_961_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_date_925_);
lean_dec(v_dt_923_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_961_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v_date_930_; lean_object* v_time_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_960_; 
v___x_929_ = lean_thunk_get_own(v_date_925_);
lean_dec_ref(v_date_925_);
v_date_930_ = lean_ctor_get(v___x_929_, 0);
v_time_931_ = lean_ctor_get(v___x_929_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_960_ == 0)
{
v___x_933_ = v___x_929_;
v_isShared_934_ = v_isSharedCheck_960_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_time_931_);
lean_inc(v_date_930_);
lean_dec(v___x_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_960_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_offset_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v_offset_935_ = lean_ctor_get(v_tz_922_, 0);
v___x_936_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_937_ = lean_int_mul(v_years_924_, v___x_936_);
v___x_938_ = lean_int_neg(v___x_937_);
lean_dec(v___x_937_);
v___x_939_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_930_, v___x_938_);
lean_dec(v___x_938_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_939_);
v___x_941_ = v___x_933_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_time_931_);
v___x_941_ = v_reuseFailAlloc_959_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; lean_object* v_second_943_; lean_object* v_nano_944_; lean_object* v___f_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_tm_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
lean_inc_ref(v___x_941_);
v___x_942_ = l_Std_Time_PlainDateTime_toWallTime(v___x_941_);
v_second_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_second_943_);
v_nano_944_ = lean_ctor_get(v___x_942_, 1);
lean_inc(v_nano_944_);
lean_dec_ref(v___x_942_);
v___f_945_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_945_, 0, v___x_941_);
v___x_946_ = lean_int_neg(v_offset_935_);
v___x_947_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_948_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_949_ = lean_int_mul(v_second_943_, v___x_948_);
lean_dec(v_second_943_);
v___x_950_ = lean_int_add(v___x_949_, v_nano_944_);
lean_dec(v_nano_944_);
lean_dec(v___x_949_);
v___x_951_ = lean_int_mul(v___x_946_, v___x_948_);
lean_dec(v___x_946_);
v___x_952_ = lean_int_add(v___x_951_, v___x_947_);
lean_dec(v___x_951_);
v___x_953_ = lean_int_add(v___x_950_, v___x_952_);
lean_dec(v___x_952_);
lean_dec(v___x_950_);
v_tm_954_ = l_Std_Time_Duration_ofNanoseconds(v___x_953_);
lean_dec(v___x_953_);
v___x_955_ = lean_mk_thunk(v___f_945_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v___x_955_);
lean_ctor_set(v___x_927_, 0, v_tm_954_);
v___x_957_ = v___x_927_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_tm_954_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object* v_tz_963_, lean_object* v_dt_964_, lean_object* v_years_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_Time_DateTime_subYearsRollOver(v_tz_963_, v_dt_964_, v_years_965_);
lean_dec(v_years_965_);
lean_dec_ref(v_tz_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object* v_tz_967_, lean_object* v_dt_968_, lean_object* v_years_969_){
_start:
{
lean_object* v_date_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1006_; 
v_date_970_ = lean_ctor_get(v_dt_968_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_dt_968_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v_dt_968_, 0);
lean_dec(v_unused_1007_);
v___x_972_ = v_dt_968_;
v_isShared_973_ = v_isSharedCheck_1006_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_date_970_);
lean_dec(v_dt_968_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1006_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v_date_975_; lean_object* v_time_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1005_; 
v___x_974_ = lean_thunk_get_own(v_date_970_);
lean_dec_ref(v_date_970_);
v_date_975_ = lean_ctor_get(v___x_974_, 0);
v_time_976_ = lean_ctor_get(v___x_974_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_978_ = v___x_974_;
v_isShared_979_ = v_isSharedCheck_1005_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_time_976_);
lean_inc(v_date_975_);
lean_dec(v___x_974_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1005_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_offset_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
v_offset_980_ = lean_ctor_get(v_tz_967_, 0);
v___x_981_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_982_ = lean_int_mul(v_years_969_, v___x_981_);
v___x_983_ = lean_int_neg(v___x_982_);
lean_dec(v___x_982_);
v___x_984_ = l_Std_Time_PlainDate_addMonthsClip(v_date_975_, v___x_983_);
lean_dec(v___x_983_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_984_);
v___x_986_ = v___x_978_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_984_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_time_976_);
v___x_986_ = v_reuseFailAlloc_1004_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v_second_988_; lean_object* v_nano_989_; lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v_tm_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_inc_ref(v___x_986_);
v___x_987_ = l_Std_Time_PlainDateTime_toWallTime(v___x_986_);
v_second_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_second_988_);
v_nano_989_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_nano_989_);
lean_dec_ref(v___x_987_);
v___f_990_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_990_, 0, v___x_986_);
v___x_991_ = lean_int_neg(v_offset_980_);
v___x_992_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_993_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_994_ = lean_int_mul(v_second_988_, v___x_993_);
lean_dec(v_second_988_);
v___x_995_ = lean_int_add(v___x_994_, v_nano_989_);
lean_dec(v_nano_989_);
lean_dec(v___x_994_);
v___x_996_ = lean_int_mul(v___x_991_, v___x_993_);
lean_dec(v___x_991_);
v___x_997_ = lean_int_add(v___x_996_, v___x_992_);
lean_dec(v___x_996_);
v___x_998_ = lean_int_add(v___x_995_, v___x_997_);
lean_dec(v___x_997_);
lean_dec(v___x_995_);
v_tm_999_ = l_Std_Time_Duration_ofNanoseconds(v___x_998_);
lean_dec(v___x_998_);
v___x_1000_ = lean_mk_thunk(v___f_990_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 1, v___x_1000_);
lean_ctor_set(v___x_972_, 0, v_tm_999_);
v___x_1002_ = v___x_972_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_tm_999_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object* v_tz_1008_, lean_object* v_dt_1009_, lean_object* v_years_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Std_Time_DateTime_subYearsClip(v_tz_1008_, v_dt_1009_, v_years_1010_);
lean_dec(v_years_1010_);
lean_dec_ref(v_tz_1008_);
return v_res_1011_;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__0(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_unsigned_to_nat(4u);
v___x_1013_ = lean_nat_to_int(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__1(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = lean_unsigned_to_nat(400u);
v___x_1015_ = lean_nat_to_int(v___x_1014_);
return v___x_1015_;
}
}
static lean_object* _init_l_Std_Time_DateTime_withDaysClip___closed__2(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_unsigned_to_nat(100u);
v___x_1017_ = lean_nat_to_int(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object* v_tz_1018_, lean_object* v_dt_1019_, lean_object* v_days_1020_){
_start:
{
lean_object* v_date_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1084_; 
v_date_1021_ = lean_ctor_get(v_dt_1019_, 1);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_dt_1019_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_dt_1019_, 0);
lean_dec(v_unused_1085_);
v___x_1023_ = v_dt_1019_;
v_isShared_1024_ = v_isSharedCheck_1084_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_date_1021_);
lean_dec(v_dt_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1084_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1025_; lean_object* v___y_1027_; lean_object* v_date_1055_; lean_object* v_year_1056_; lean_object* v_month_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1082_; 
v___x_1025_ = lean_thunk_get_own(v_date_1021_);
lean_dec_ref(v_date_1021_);
v_date_1055_ = lean_ctor_get(v___x_1025_, 0);
lean_inc_ref(v_date_1055_);
v_year_1056_ = lean_ctor_get(v_date_1055_, 0);
v_month_1057_ = lean_ctor_get(v_date_1055_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_date_1055_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_date_1055_, 2);
lean_dec(v_unused_1083_);
v___x_1059_ = v_date_1055_;
v_isShared_1060_ = v_isSharedCheck_1082_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_month_1057_);
lean_inc(v_year_1056_);
lean_dec(v_date_1055_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1082_;
goto v_resetjp_1058_;
}
v___jp_1026_:
{
lean_object* v_time_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1053_; 
v_time_1028_ = lean_ctor_get(v___x_1025_, 1);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v___x_1025_, 0);
lean_dec(v_unused_1054_);
v___x_1030_ = v___x_1025_;
v_isShared_1031_ = v_isSharedCheck_1053_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_time_1028_);
lean_dec(v___x_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1053_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_offset_1032_; lean_object* v___x_1034_; 
v_offset_1032_ = lean_ctor_get(v_tz_1018_, 0);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 0, v___y_1027_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___y_1027_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_time_1028_);
v___x_1034_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; lean_object* v_second_1036_; lean_object* v_nano_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_tm_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_inc_ref(v___x_1034_);
v___x_1035_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1034_);
v_second_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_second_1036_);
v_nano_1037_ = lean_ctor_get(v___x_1035_, 1);
lean_inc(v_nano_1037_);
lean_dec_ref(v___x_1035_);
v___f_1038_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1038_, 0, v___x_1034_);
v___x_1039_ = lean_int_neg(v_offset_1032_);
v___x_1040_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1041_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1042_ = lean_int_mul(v_second_1036_, v___x_1041_);
lean_dec(v_second_1036_);
v___x_1043_ = lean_int_add(v___x_1042_, v_nano_1037_);
lean_dec(v_nano_1037_);
lean_dec(v___x_1042_);
v___x_1044_ = lean_int_mul(v___x_1039_, v___x_1041_);
lean_dec(v___x_1039_);
v___x_1045_ = lean_int_add(v___x_1044_, v___x_1040_);
lean_dec(v___x_1044_);
v___x_1046_ = lean_int_add(v___x_1043_, v___x_1045_);
lean_dec(v___x_1045_);
lean_dec(v___x_1043_);
v_tm_1047_ = l_Std_Time_Duration_ofNanoseconds(v___x_1046_);
lean_dec(v___x_1046_);
v___x_1048_ = lean_mk_thunk(v___f_1038_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 1, v___x_1048_);
lean_ctor_set(v___x_1023_, 0, v_tm_1047_);
v___x_1050_ = v___x_1023_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_tm_1047_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
v_resetjp_1058_:
{
uint8_t v___y_1062_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1078_; 
v___x_1071_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_1072_ = lean_int_mod(v_year_1056_, v___x_1071_);
v___x_1073_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1078_ = lean_int_dec_eq(v___x_1072_, v___x_1073_);
lean_dec(v___x_1072_);
if (v___x_1078_ == 0)
{
v___y_1062_ = v___x_1078_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1079_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_1080_ = lean_int_mod(v_year_1056_, v___x_1079_);
v___x_1081_ = lean_int_dec_eq(v___x_1080_, v___x_1073_);
lean_dec(v___x_1080_);
if (v___x_1081_ == 0)
{
if (v___x_1078_ == 0)
{
goto v___jp_1074_;
}
else
{
v___y_1062_ = v___x_1078_;
goto v___jp_1061_;
}
}
else
{
goto v___jp_1074_;
}
}
v___jp_1061_:
{
lean_object* v_max_1063_; uint8_t v___x_1064_; 
v_max_1063_ = l_Std_Time_Month_Ordinal_days(v___y_1062_, v_month_1057_);
v___x_1064_ = lean_int_dec_lt(v_max_1063_, v_days_1020_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1066_; 
lean_dec(v_max_1063_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 2, v_days_1020_);
v___x_1066_ = v___x_1059_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_year_1056_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_month_1057_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_days_1020_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
v___y_1027_ = v___x_1066_;
goto v___jp_1026_;
}
}
else
{
lean_object* v___x_1069_; 
lean_dec(v_days_1020_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 2, v_max_1063_);
v___x_1069_ = v___x_1059_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_year_1056_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v_month_1057_);
lean_ctor_set(v_reuseFailAlloc_1070_, 2, v_max_1063_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
v___y_1027_ = v___x_1069_;
goto v___jp_1026_;
}
}
}
v___jp_1074_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1075_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_1076_ = lean_int_mod(v_year_1056_, v___x_1075_);
v___x_1077_ = lean_int_dec_eq(v___x_1076_, v___x_1073_);
lean_dec(v___x_1076_);
v___y_1062_ = v___x_1077_;
goto v___jp_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip___boxed(lean_object* v_tz_1086_, lean_object* v_dt_1087_, lean_object* v_days_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Std_Time_DateTime_withDaysClip(v_tz_1086_, v_dt_1087_, v_days_1088_);
lean_dec_ref(v_tz_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object* v_tz_1090_, lean_object* v_dt_1091_, lean_object* v_days_1092_){
_start:
{
lean_object* v_date_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1128_; 
v_date_1093_ = lean_ctor_get(v_dt_1091_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_dt_1091_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_dt_1091_, 0);
lean_dec(v_unused_1129_);
v___x_1095_ = v_dt_1091_;
v_isShared_1096_ = v_isSharedCheck_1128_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_date_1093_);
lean_dec(v_dt_1091_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1128_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v_date_1098_; lean_object* v_time_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1127_; 
v___x_1097_ = lean_thunk_get_own(v_date_1093_);
lean_dec_ref(v_date_1093_);
v_date_1098_ = lean_ctor_get(v___x_1097_, 0);
v_time_1099_ = lean_ctor_get(v___x_1097_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1101_ = v___x_1097_;
v_isShared_1102_ = v_isSharedCheck_1127_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_time_1099_);
lean_inc(v_date_1098_);
lean_dec(v___x_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1127_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_year_1103_; lean_object* v_month_1104_; lean_object* v_offset_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v_year_1103_ = lean_ctor_get(v_date_1098_, 0);
lean_inc(v_year_1103_);
v_month_1104_ = lean_ctor_get(v_date_1098_, 1);
lean_inc(v_month_1104_);
lean_dec_ref(v_date_1098_);
v_offset_1105_ = lean_ctor_get(v_tz_1090_, 0);
v___x_1106_ = l_Std_Time_PlainDate_rollOver(v_year_1103_, v_month_1104_, v_days_1092_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1106_);
v___x_1108_ = v___x_1101_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_time_1099_);
v___x_1108_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; lean_object* v_second_1110_; lean_object* v_nano_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v_tm_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_inc_ref(v___x_1108_);
v___x_1109_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1108_);
v_second_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_second_1110_);
v_nano_1111_ = lean_ctor_get(v___x_1109_, 1);
lean_inc(v_nano_1111_);
lean_dec_ref(v___x_1109_);
v___f_1112_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1112_, 0, v___x_1108_);
v___x_1113_ = lean_int_neg(v_offset_1105_);
v___x_1114_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1115_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1116_ = lean_int_mul(v_second_1110_, v___x_1115_);
lean_dec(v_second_1110_);
v___x_1117_ = lean_int_add(v___x_1116_, v_nano_1111_);
lean_dec(v_nano_1111_);
lean_dec(v___x_1116_);
v___x_1118_ = lean_int_mul(v___x_1113_, v___x_1115_);
lean_dec(v___x_1113_);
v___x_1119_ = lean_int_add(v___x_1118_, v___x_1114_);
lean_dec(v___x_1118_);
v___x_1120_ = lean_int_add(v___x_1117_, v___x_1119_);
lean_dec(v___x_1119_);
lean_dec(v___x_1117_);
v_tm_1121_ = l_Std_Time_Duration_ofNanoseconds(v___x_1120_);
lean_dec(v___x_1120_);
v___x_1122_ = lean_mk_thunk(v___f_1112_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v___x_1122_);
lean_ctor_set(v___x_1095_, 0, v_tm_1121_);
v___x_1124_ = v___x_1095_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_tm_1121_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object* v_tz_1130_, lean_object* v_dt_1131_, lean_object* v_days_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_Time_DateTime_withDaysRollOver(v_tz_1130_, v_dt_1131_, v_days_1132_);
lean_dec(v_days_1132_);
lean_dec_ref(v_tz_1130_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object* v_tz_1134_, lean_object* v_dt_1135_, lean_object* v_month_1136_){
_start:
{
lean_object* v_date_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1200_; 
v_date_1137_ = lean_ctor_get(v_dt_1135_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_dt_1135_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v_dt_1135_, 0);
lean_dec(v_unused_1201_);
v___x_1139_ = v_dt_1135_;
v_isShared_1140_ = v_isSharedCheck_1200_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_date_1137_);
lean_dec(v_dt_1135_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1200_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___y_1143_; lean_object* v_date_1171_; lean_object* v_year_1172_; lean_object* v_day_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1198_; 
v___x_1141_ = lean_thunk_get_own(v_date_1137_);
lean_dec_ref(v_date_1137_);
v_date_1171_ = lean_ctor_get(v___x_1141_, 0);
lean_inc_ref(v_date_1171_);
v_year_1172_ = lean_ctor_get(v_date_1171_, 0);
v_day_1173_ = lean_ctor_get(v_date_1171_, 2);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_date_1171_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v_date_1171_, 1);
lean_dec(v_unused_1199_);
v___x_1175_ = v_date_1171_;
v_isShared_1176_ = v_isSharedCheck_1198_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_day_1173_);
lean_inc(v_year_1172_);
lean_dec(v_date_1171_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1198_;
goto v_resetjp_1174_;
}
v___jp_1142_:
{
lean_object* v_time_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1169_; 
v_time_1144_ = lean_ctor_get(v___x_1141_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; 
v_unused_1170_ = lean_ctor_get(v___x_1141_, 0);
lean_dec(v_unused_1170_);
v___x_1146_ = v___x_1141_;
v_isShared_1147_ = v_isSharedCheck_1169_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_time_1144_);
lean_dec(v___x_1141_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1169_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_offset_1148_; lean_object* v___x_1150_; 
v_offset_1148_ = lean_ctor_get(v_tz_1134_, 0);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___y_1143_);
v___x_1150_ = v___x_1146_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___y_1143_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_time_1144_);
v___x_1150_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; lean_object* v_second_1152_; lean_object* v_nano_1153_; lean_object* v___f_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_tm_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_inc_ref(v___x_1150_);
v___x_1151_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1150_);
v_second_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_second_1152_);
v_nano_1153_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_nano_1153_);
lean_dec_ref(v___x_1151_);
v___f_1154_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1154_, 0, v___x_1150_);
v___x_1155_ = lean_int_neg(v_offset_1148_);
v___x_1156_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1157_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1158_ = lean_int_mul(v_second_1152_, v___x_1157_);
lean_dec(v_second_1152_);
v___x_1159_ = lean_int_add(v___x_1158_, v_nano_1153_);
lean_dec(v_nano_1153_);
lean_dec(v___x_1158_);
v___x_1160_ = lean_int_mul(v___x_1155_, v___x_1157_);
lean_dec(v___x_1155_);
v___x_1161_ = lean_int_add(v___x_1160_, v___x_1156_);
lean_dec(v___x_1160_);
v___x_1162_ = lean_int_add(v___x_1159_, v___x_1161_);
lean_dec(v___x_1161_);
lean_dec(v___x_1159_);
v_tm_1163_ = l_Std_Time_Duration_ofNanoseconds(v___x_1162_);
lean_dec(v___x_1162_);
v___x_1164_ = lean_mk_thunk(v___f_1154_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1164_);
lean_ctor_set(v___x_1139_, 0, v_tm_1163_);
v___x_1166_ = v___x_1139_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_tm_1163_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
v_resetjp_1174_:
{
uint8_t v___y_1178_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; uint8_t v___x_1194_; 
v___x_1187_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_1188_ = lean_int_mod(v_year_1172_, v___x_1187_);
v___x_1189_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1194_ = lean_int_dec_eq(v___x_1188_, v___x_1189_);
lean_dec(v___x_1188_);
if (v___x_1194_ == 0)
{
v___y_1178_ = v___x_1194_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_1196_ = lean_int_mod(v_year_1172_, v___x_1195_);
v___x_1197_ = lean_int_dec_eq(v___x_1196_, v___x_1189_);
lean_dec(v___x_1196_);
if (v___x_1197_ == 0)
{
if (v___x_1194_ == 0)
{
goto v___jp_1190_;
}
else
{
v___y_1178_ = v___x_1194_;
goto v___jp_1177_;
}
}
else
{
goto v___jp_1190_;
}
}
v___jp_1177_:
{
lean_object* v_max_1179_; uint8_t v___x_1180_; 
v_max_1179_ = l_Std_Time_Month_Ordinal_days(v___y_1178_, v_month_1136_);
v___x_1180_ = lean_int_dec_lt(v_max_1179_, v_day_1173_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1182_; 
lean_dec(v_max_1179_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_month_1136_);
v___x_1182_ = v___x_1175_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_year_1172_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_month_1136_);
lean_ctor_set(v_reuseFailAlloc_1183_, 2, v_day_1173_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
v___y_1143_ = v___x_1182_;
goto v___jp_1142_;
}
}
else
{
lean_object* v___x_1185_; 
lean_dec(v_day_1173_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 2, v_max_1179_);
lean_ctor_set(v___x_1175_, 1, v_month_1136_);
v___x_1185_ = v___x_1175_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_year_1172_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_month_1136_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_max_1179_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
v___y_1143_ = v___x_1185_;
goto v___jp_1142_;
}
}
}
v___jp_1190_:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1191_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_1192_ = lean_int_mod(v_year_1172_, v___x_1191_);
v___x_1193_ = lean_int_dec_eq(v___x_1192_, v___x_1189_);
lean_dec(v___x_1192_);
v___y_1178_ = v___x_1193_;
goto v___jp_1177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip___boxed(lean_object* v_tz_1202_, lean_object* v_dt_1203_, lean_object* v_month_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Std_Time_DateTime_withMonthClip(v_tz_1202_, v_dt_1203_, v_month_1204_);
lean_dec_ref(v_tz_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object* v_tz_1206_, lean_object* v_dt_1207_, lean_object* v_month_1208_){
_start:
{
lean_object* v_date_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1244_; 
v_date_1209_ = lean_ctor_get(v_dt_1207_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_dt_1207_);
if (v_isSharedCheck_1244_ == 0)
{
lean_object* v_unused_1245_; 
v_unused_1245_ = lean_ctor_get(v_dt_1207_, 0);
lean_dec(v_unused_1245_);
v___x_1211_ = v_dt_1207_;
v_isShared_1212_ = v_isSharedCheck_1244_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_date_1209_);
lean_dec(v_dt_1207_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1244_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v_date_1214_; lean_object* v_time_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1243_; 
v___x_1213_ = lean_thunk_get_own(v_date_1209_);
lean_dec_ref(v_date_1209_);
v_date_1214_ = lean_ctor_get(v___x_1213_, 0);
v_time_1215_ = lean_ctor_get(v___x_1213_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1217_ = v___x_1213_;
v_isShared_1218_ = v_isSharedCheck_1243_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_time_1215_);
lean_inc(v_date_1214_);
lean_dec(v___x_1213_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1243_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_year_1219_; lean_object* v_day_1220_; lean_object* v_offset_1221_; lean_object* v___x_1222_; lean_object* v___x_1224_; 
v_year_1219_ = lean_ctor_get(v_date_1214_, 0);
lean_inc(v_year_1219_);
v_day_1220_ = lean_ctor_get(v_date_1214_, 2);
lean_inc(v_day_1220_);
lean_dec_ref(v_date_1214_);
v_offset_1221_ = lean_ctor_get(v_tz_1206_, 0);
v___x_1222_ = l_Std_Time_PlainDate_rollOver(v_year_1219_, v_month_1208_, v_day_1220_);
lean_dec(v_day_1220_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1222_);
v___x_1224_ = v___x_1217_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_time_1215_);
v___x_1224_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v_second_1226_; lean_object* v_nano_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_tm_1237_; lean_object* v___x_1238_; lean_object* v___x_1240_; 
lean_inc_ref(v___x_1224_);
v___x_1225_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1224_);
v_second_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_second_1226_);
v_nano_1227_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_nano_1227_);
lean_dec_ref(v___x_1225_);
v___f_1228_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1228_, 0, v___x_1224_);
v___x_1229_ = lean_int_neg(v_offset_1221_);
v___x_1230_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1231_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1232_ = lean_int_mul(v_second_1226_, v___x_1231_);
lean_dec(v_second_1226_);
v___x_1233_ = lean_int_add(v___x_1232_, v_nano_1227_);
lean_dec(v_nano_1227_);
lean_dec(v___x_1232_);
v___x_1234_ = lean_int_mul(v___x_1229_, v___x_1231_);
lean_dec(v___x_1229_);
v___x_1235_ = lean_int_add(v___x_1234_, v___x_1230_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_int_add(v___x_1233_, v___x_1235_);
lean_dec(v___x_1235_);
lean_dec(v___x_1233_);
v_tm_1237_ = l_Std_Time_Duration_ofNanoseconds(v___x_1236_);
lean_dec(v___x_1236_);
v___x_1238_ = lean_mk_thunk(v___f_1228_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___x_1238_);
lean_ctor_set(v___x_1211_, 0, v_tm_1237_);
v___x_1240_ = v___x_1211_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_tm_1237_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1238_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver___boxed(lean_object* v_tz_1246_, lean_object* v_dt_1247_, lean_object* v_month_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Std_Time_DateTime_withMonthRollOver(v_tz_1246_, v_dt_1247_, v_month_1248_);
lean_dec_ref(v_tz_1246_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object* v_tz_1250_, lean_object* v_dt_1251_, lean_object* v_year_1252_){
_start:
{
lean_object* v_date_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1316_; 
v_date_1253_ = lean_ctor_get(v_dt_1251_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_dt_1251_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v_dt_1251_, 0);
lean_dec(v_unused_1317_);
v___x_1255_ = v_dt_1251_;
v_isShared_1256_ = v_isSharedCheck_1316_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_date_1253_);
lean_dec(v_dt_1251_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1316_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___y_1259_; lean_object* v_date_1287_; lean_object* v_month_1288_; lean_object* v_day_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1314_; 
v___x_1257_ = lean_thunk_get_own(v_date_1253_);
lean_dec_ref(v_date_1253_);
v_date_1287_ = lean_ctor_get(v___x_1257_, 0);
lean_inc_ref(v_date_1287_);
v_month_1288_ = lean_ctor_get(v_date_1287_, 1);
v_day_1289_ = lean_ctor_get(v_date_1287_, 2);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_date_1287_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v_date_1287_, 0);
lean_dec(v_unused_1315_);
v___x_1291_ = v_date_1287_;
v_isShared_1292_ = v_isSharedCheck_1314_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_day_1289_);
lean_inc(v_month_1288_);
lean_dec(v_date_1287_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1314_;
goto v_resetjp_1290_;
}
v___jp_1258_:
{
lean_object* v_time_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1285_; 
v_time_1260_ = lean_ctor_get(v___x_1257_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1286_);
v___x_1262_ = v___x_1257_;
v_isShared_1263_ = v_isSharedCheck_1285_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_time_1260_);
lean_dec(v___x_1257_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1285_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v_offset_1264_; lean_object* v___x_1266_; 
v_offset_1264_ = lean_ctor_get(v_tz_1250_, 0);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v___y_1259_);
v___x_1266_ = v___x_1262_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___y_1259_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_time_1260_);
v___x_1266_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; lean_object* v_second_1268_; lean_object* v_nano_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_tm_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
lean_inc_ref(v___x_1266_);
v___x_1267_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1266_);
v_second_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_second_1268_);
v_nano_1269_ = lean_ctor_get(v___x_1267_, 1);
lean_inc(v_nano_1269_);
lean_dec_ref(v___x_1267_);
v___f_1270_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1270_, 0, v___x_1266_);
v___x_1271_ = lean_int_neg(v_offset_1264_);
v___x_1272_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1273_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1274_ = lean_int_mul(v_second_1268_, v___x_1273_);
lean_dec(v_second_1268_);
v___x_1275_ = lean_int_add(v___x_1274_, v_nano_1269_);
lean_dec(v_nano_1269_);
lean_dec(v___x_1274_);
v___x_1276_ = lean_int_mul(v___x_1271_, v___x_1273_);
lean_dec(v___x_1271_);
v___x_1277_ = lean_int_add(v___x_1276_, v___x_1272_);
lean_dec(v___x_1276_);
v___x_1278_ = lean_int_add(v___x_1275_, v___x_1277_);
lean_dec(v___x_1277_);
lean_dec(v___x_1275_);
v_tm_1279_ = l_Std_Time_Duration_ofNanoseconds(v___x_1278_);
lean_dec(v___x_1278_);
v___x_1280_ = lean_mk_thunk(v___f_1270_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v___x_1280_);
lean_ctor_set(v___x_1255_, 0, v_tm_1279_);
v___x_1282_ = v___x_1255_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_tm_1279_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
v_resetjp_1290_:
{
uint8_t v___y_1294_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1310_; 
v___x_1303_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_1304_ = lean_int_mod(v_year_1252_, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1310_ = lean_int_dec_eq(v___x_1304_, v___x_1305_);
lean_dec(v___x_1304_);
if (v___x_1310_ == 0)
{
v___y_1294_ = v___x_1310_;
goto v___jp_1293_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1311_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_1312_ = lean_int_mod(v_year_1252_, v___x_1311_);
v___x_1313_ = lean_int_dec_eq(v___x_1312_, v___x_1305_);
lean_dec(v___x_1312_);
if (v___x_1313_ == 0)
{
if (v___x_1310_ == 0)
{
goto v___jp_1306_;
}
else
{
v___y_1294_ = v___x_1310_;
goto v___jp_1293_;
}
}
else
{
goto v___jp_1306_;
}
}
v___jp_1293_:
{
lean_object* v_max_1295_; uint8_t v___x_1296_; 
v_max_1295_ = l_Std_Time_Month_Ordinal_days(v___y_1294_, v_month_1288_);
v___x_1296_ = lean_int_dec_lt(v_max_1295_, v_day_1289_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1298_; 
lean_dec(v_max_1295_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v_year_1252_);
v___x_1298_ = v___x_1291_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_year_1252_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_month_1288_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v_day_1289_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
v___y_1259_ = v___x_1298_;
goto v___jp_1258_;
}
}
else
{
lean_object* v___x_1301_; 
lean_dec(v_day_1289_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 2, v_max_1295_);
lean_ctor_set(v___x_1291_, 0, v_year_1252_);
v___x_1301_ = v___x_1291_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_year_1252_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_month_1288_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_max_1295_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
v___y_1259_ = v___x_1301_;
goto v___jp_1258_;
}
}
}
v___jp_1306_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1307_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_1308_ = lean_int_mod(v_year_1252_, v___x_1307_);
v___x_1309_ = lean_int_dec_eq(v___x_1308_, v___x_1305_);
lean_dec(v___x_1308_);
v___y_1294_ = v___x_1309_;
goto v___jp_1293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip___boxed(lean_object* v_tz_1318_, lean_object* v_dt_1319_, lean_object* v_year_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Std_Time_DateTime_withYearClip(v_tz_1318_, v_dt_1319_, v_year_1320_);
lean_dec_ref(v_tz_1318_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object* v_tz_1322_, lean_object* v_dt_1323_, lean_object* v_year_1324_){
_start:
{
lean_object* v_date_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1360_; 
v_date_1325_ = lean_ctor_get(v_dt_1323_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_dt_1323_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v_dt_1323_, 0);
lean_dec(v_unused_1361_);
v___x_1327_ = v_dt_1323_;
v_isShared_1328_ = v_isSharedCheck_1360_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_date_1325_);
lean_dec(v_dt_1323_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1360_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v_date_1330_; lean_object* v_time_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1359_; 
v___x_1329_ = lean_thunk_get_own(v_date_1325_);
lean_dec_ref(v_date_1325_);
v_date_1330_ = lean_ctor_get(v___x_1329_, 0);
v_time_1331_ = lean_ctor_get(v___x_1329_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1333_ = v___x_1329_;
v_isShared_1334_ = v_isSharedCheck_1359_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_time_1331_);
lean_inc(v_date_1330_);
lean_dec(v___x_1329_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1359_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v_month_1335_; lean_object* v_day_1336_; lean_object* v_offset_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
v_month_1335_ = lean_ctor_get(v_date_1330_, 1);
lean_inc(v_month_1335_);
v_day_1336_ = lean_ctor_get(v_date_1330_, 2);
lean_inc(v_day_1336_);
lean_dec_ref(v_date_1330_);
v_offset_1337_ = lean_ctor_get(v_tz_1322_, 0);
v___x_1338_ = l_Std_Time_PlainDate_rollOver(v_year_1324_, v_month_1335_, v_day_1336_);
lean_dec(v_day_1336_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1338_);
v___x_1340_ = v___x_1333_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_time_1331_);
v___x_1340_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v_second_1342_; lean_object* v_nano_1343_; lean_object* v___f_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v_tm_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
lean_inc_ref(v___x_1340_);
v___x_1341_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1340_);
v_second_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_second_1342_);
v_nano_1343_ = lean_ctor_get(v___x_1341_, 1);
lean_inc(v_nano_1343_);
lean_dec_ref(v___x_1341_);
v___f_1344_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1344_, 0, v___x_1340_);
v___x_1345_ = lean_int_neg(v_offset_1337_);
v___x_1346_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1347_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1348_ = lean_int_mul(v_second_1342_, v___x_1347_);
lean_dec(v_second_1342_);
v___x_1349_ = lean_int_add(v___x_1348_, v_nano_1343_);
lean_dec(v_nano_1343_);
lean_dec(v___x_1348_);
v___x_1350_ = lean_int_mul(v___x_1345_, v___x_1347_);
lean_dec(v___x_1345_);
v___x_1351_ = lean_int_add(v___x_1350_, v___x_1346_);
lean_dec(v___x_1350_);
v___x_1352_ = lean_int_add(v___x_1349_, v___x_1351_);
lean_dec(v___x_1351_);
lean_dec(v___x_1349_);
v_tm_1353_ = l_Std_Time_Duration_ofNanoseconds(v___x_1352_);
lean_dec(v___x_1352_);
v___x_1354_ = lean_mk_thunk(v___f_1344_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 1, v___x_1354_);
lean_ctor_set(v___x_1327_, 0, v_tm_1353_);
v___x_1356_ = v___x_1327_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_tm_1353_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver___boxed(lean_object* v_tz_1362_, lean_object* v_dt_1363_, lean_object* v_year_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Std_Time_DateTime_withYearRollOver(v_tz_1362_, v_dt_1363_, v_year_1364_);
lean_dec_ref(v_tz_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object* v_tz_1366_, lean_object* v_dt_1367_, lean_object* v_hour_1368_){
_start:
{
lean_object* v_date_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1412_; 
v_date_1369_ = lean_ctor_get(v_dt_1367_, 1);
v_isSharedCheck_1412_ = !lean_is_exclusive(v_dt_1367_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; 
v_unused_1413_ = lean_ctor_get(v_dt_1367_, 0);
lean_dec(v_unused_1413_);
v___x_1371_ = v_dt_1367_;
v_isShared_1372_ = v_isSharedCheck_1412_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_date_1369_);
lean_dec(v_dt_1367_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1412_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v_time_1374_; lean_object* v_date_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1411_; 
v___x_1373_ = lean_thunk_get_own(v_date_1369_);
lean_dec_ref(v_date_1369_);
v_time_1374_ = lean_ctor_get(v___x_1373_, 1);
v_date_1375_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1377_ = v___x_1373_;
v_isShared_1378_ = v_isSharedCheck_1411_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_time_1374_);
lean_inc(v_date_1375_);
lean_dec(v___x_1373_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1411_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v_minute_1379_; lean_object* v_second_1380_; lean_object* v_nanosecond_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1409_; 
v_minute_1379_ = lean_ctor_get(v_time_1374_, 1);
v_second_1380_ = lean_ctor_get(v_time_1374_, 2);
v_nanosecond_1381_ = lean_ctor_get(v_time_1374_, 3);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_time_1374_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_time_1374_, 0);
lean_dec(v_unused_1410_);
v___x_1383_ = v_time_1374_;
v_isShared_1384_ = v_isSharedCheck_1409_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_nanosecond_1381_);
lean_inc(v_second_1380_);
lean_inc(v_minute_1379_);
lean_dec(v_time_1374_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1409_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v_offset_1385_; lean_object* v___x_1387_; 
v_offset_1385_ = lean_ctor_get(v_tz_1366_, 0);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v_hour_1368_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_hour_1368_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_minute_1379_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_second_1380_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_nanosecond_1381_);
v___x_1387_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1389_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v___x_1387_);
v___x_1389_ = v___x_1377_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_date_1375_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v___x_1387_);
v___x_1389_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v_second_1391_; lean_object* v_nano_1392_; lean_object* v___f_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v_tm_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
lean_inc_ref(v___x_1389_);
v___x_1390_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1389_);
v_second_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_second_1391_);
v_nano_1392_ = lean_ctor_get(v___x_1390_, 1);
lean_inc(v_nano_1392_);
lean_dec_ref(v___x_1390_);
v___f_1393_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1393_, 0, v___x_1389_);
v___x_1394_ = lean_int_neg(v_offset_1385_);
v___x_1395_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1396_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1397_ = lean_int_mul(v_second_1391_, v___x_1396_);
lean_dec(v_second_1391_);
v___x_1398_ = lean_int_add(v___x_1397_, v_nano_1392_);
lean_dec(v_nano_1392_);
lean_dec(v___x_1397_);
v___x_1399_ = lean_int_mul(v___x_1394_, v___x_1396_);
lean_dec(v___x_1394_);
v___x_1400_ = lean_int_add(v___x_1399_, v___x_1395_);
lean_dec(v___x_1399_);
v___x_1401_ = lean_int_add(v___x_1398_, v___x_1400_);
lean_dec(v___x_1400_);
lean_dec(v___x_1398_);
v_tm_1402_ = l_Std_Time_Duration_ofNanoseconds(v___x_1401_);
lean_dec(v___x_1401_);
v___x_1403_ = lean_mk_thunk(v___f_1393_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v___x_1403_);
lean_ctor_set(v___x_1371_, 0, v_tm_1402_);
v___x_1405_ = v___x_1371_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_tm_1402_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours___boxed(lean_object* v_tz_1414_, lean_object* v_dt_1415_, lean_object* v_hour_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Std_Time_DateTime_withHours(v_tz_1414_, v_dt_1415_, v_hour_1416_);
lean_dec_ref(v_tz_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object* v_tz_1418_, lean_object* v_dt_1419_, lean_object* v_minute_1420_){
_start:
{
lean_object* v_date_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1464_; 
v_date_1421_ = lean_ctor_get(v_dt_1419_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_dt_1419_);
if (v_isSharedCheck_1464_ == 0)
{
lean_object* v_unused_1465_; 
v_unused_1465_ = lean_ctor_get(v_dt_1419_, 0);
lean_dec(v_unused_1465_);
v___x_1423_ = v_dt_1419_;
v_isShared_1424_ = v_isSharedCheck_1464_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_date_1421_);
lean_dec(v_dt_1419_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1464_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v_time_1426_; lean_object* v_date_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1463_; 
v___x_1425_ = lean_thunk_get_own(v_date_1421_);
lean_dec_ref(v_date_1421_);
v_time_1426_ = lean_ctor_get(v___x_1425_, 1);
v_date_1427_ = lean_ctor_get(v___x_1425_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1429_ = v___x_1425_;
v_isShared_1430_ = v_isSharedCheck_1463_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_time_1426_);
lean_inc(v_date_1427_);
lean_dec(v___x_1425_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1463_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_hour_1431_; lean_object* v_second_1432_; lean_object* v_nanosecond_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1461_; 
v_hour_1431_ = lean_ctor_get(v_time_1426_, 0);
v_second_1432_ = lean_ctor_get(v_time_1426_, 2);
v_nanosecond_1433_ = lean_ctor_get(v_time_1426_, 3);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_time_1426_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_time_1426_, 1);
lean_dec(v_unused_1462_);
v___x_1435_ = v_time_1426_;
v_isShared_1436_ = v_isSharedCheck_1461_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_nanosecond_1433_);
lean_inc(v_second_1432_);
lean_inc(v_hour_1431_);
lean_dec(v_time_1426_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1461_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v_offset_1437_; lean_object* v___x_1439_; 
v_offset_1437_ = lean_ctor_get(v_tz_1418_, 0);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v_minute_1420_);
v___x_1439_ = v___x_1435_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_hour_1431_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_minute_1420_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_second_1432_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_nanosecond_1433_);
v___x_1439_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1441_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 1, v___x_1439_);
v___x_1441_ = v___x_1429_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_date_1427_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; lean_object* v_second_1443_; lean_object* v_nano_1444_; lean_object* v___f_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_tm_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_inc_ref(v___x_1441_);
v___x_1442_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1441_);
v_second_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_second_1443_);
v_nano_1444_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_nano_1444_);
lean_dec_ref(v___x_1442_);
v___f_1445_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1445_, 0, v___x_1441_);
v___x_1446_ = lean_int_neg(v_offset_1437_);
v___x_1447_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1448_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1449_ = lean_int_mul(v_second_1443_, v___x_1448_);
lean_dec(v_second_1443_);
v___x_1450_ = lean_int_add(v___x_1449_, v_nano_1444_);
lean_dec(v_nano_1444_);
lean_dec(v___x_1449_);
v___x_1451_ = lean_int_mul(v___x_1446_, v___x_1448_);
lean_dec(v___x_1446_);
v___x_1452_ = lean_int_add(v___x_1451_, v___x_1447_);
lean_dec(v___x_1451_);
v___x_1453_ = lean_int_add(v___x_1450_, v___x_1452_);
lean_dec(v___x_1452_);
lean_dec(v___x_1450_);
v_tm_1454_ = l_Std_Time_Duration_ofNanoseconds(v___x_1453_);
lean_dec(v___x_1453_);
v___x_1455_ = lean_mk_thunk(v___f_1445_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1455_);
lean_ctor_set(v___x_1423_, 0, v_tm_1454_);
v___x_1457_ = v___x_1423_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_tm_1454_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes___boxed(lean_object* v_tz_1466_, lean_object* v_dt_1467_, lean_object* v_minute_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_Time_DateTime_withMinutes(v_tz_1466_, v_dt_1467_, v_minute_1468_);
lean_dec_ref(v_tz_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object* v_tz_1470_, lean_object* v_dt_1471_, lean_object* v_second_1472_){
_start:
{
lean_object* v_date_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1516_; 
v_date_1473_ = lean_ctor_get(v_dt_1471_, 1);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_dt_1471_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_dt_1471_, 0);
lean_dec(v_unused_1517_);
v___x_1475_ = v_dt_1471_;
v_isShared_1476_ = v_isSharedCheck_1516_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_date_1473_);
lean_dec(v_dt_1471_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1516_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v_time_1478_; lean_object* v_date_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1515_; 
v___x_1477_ = lean_thunk_get_own(v_date_1473_);
lean_dec_ref(v_date_1473_);
v_time_1478_ = lean_ctor_get(v___x_1477_, 1);
v_date_1479_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1481_ = v___x_1477_;
v_isShared_1482_ = v_isSharedCheck_1515_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_time_1478_);
lean_inc(v_date_1479_);
lean_dec(v___x_1477_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1515_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v_hour_1483_; lean_object* v_minute_1484_; lean_object* v_nanosecond_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1513_; 
v_hour_1483_ = lean_ctor_get(v_time_1478_, 0);
v_minute_1484_ = lean_ctor_get(v_time_1478_, 1);
v_nanosecond_1485_ = lean_ctor_get(v_time_1478_, 3);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_time_1478_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v_time_1478_, 2);
lean_dec(v_unused_1514_);
v___x_1487_ = v_time_1478_;
v_isShared_1488_ = v_isSharedCheck_1513_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_nanosecond_1485_);
lean_inc(v_minute_1484_);
lean_inc(v_hour_1483_);
lean_dec(v_time_1478_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1513_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v_offset_1489_; lean_object* v___x_1491_; 
v_offset_1489_ = lean_ctor_get(v_tz_1470_, 0);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 2, v_second_1472_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_hour_1483_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_minute_1484_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_second_1472_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_nanosecond_1485_);
v___x_1491_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 1, v___x_1491_);
v___x_1493_ = v___x_1481_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_date_1479_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; lean_object* v_second_1495_; lean_object* v_nano_1496_; lean_object* v___f_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_tm_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
lean_inc_ref(v___x_1493_);
v___x_1494_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1493_);
v_second_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_second_1495_);
v_nano_1496_ = lean_ctor_get(v___x_1494_, 1);
lean_inc(v_nano_1496_);
lean_dec_ref(v___x_1494_);
v___f_1497_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1497_, 0, v___x_1493_);
v___x_1498_ = lean_int_neg(v_offset_1489_);
v___x_1499_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1500_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1501_ = lean_int_mul(v_second_1495_, v___x_1500_);
lean_dec(v_second_1495_);
v___x_1502_ = lean_int_add(v___x_1501_, v_nano_1496_);
lean_dec(v_nano_1496_);
lean_dec(v___x_1501_);
v___x_1503_ = lean_int_mul(v___x_1498_, v___x_1500_);
lean_dec(v___x_1498_);
v___x_1504_ = lean_int_add(v___x_1503_, v___x_1499_);
lean_dec(v___x_1503_);
v___x_1505_ = lean_int_add(v___x_1502_, v___x_1504_);
lean_dec(v___x_1504_);
lean_dec(v___x_1502_);
v_tm_1506_ = l_Std_Time_Duration_ofNanoseconds(v___x_1505_);
lean_dec(v___x_1505_);
v___x_1507_ = lean_mk_thunk(v___f_1497_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v___x_1507_);
lean_ctor_set(v___x_1475_, 0, v_tm_1506_);
v___x_1509_ = v___x_1475_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_tm_1506_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds___boxed(lean_object* v_tz_1518_, lean_object* v_dt_1519_, lean_object* v_second_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Std_Time_DateTime_withSeconds(v_tz_1518_, v_dt_1519_, v_second_1520_);
lean_dec_ref(v_tz_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object* v_tz_1522_, lean_object* v_dt_1523_, lean_object* v_nano_1524_){
_start:
{
lean_object* v_date_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1568_; 
v_date_1525_ = lean_ctor_get(v_dt_1523_, 1);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_dt_1523_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_dt_1523_, 0);
lean_dec(v_unused_1569_);
v___x_1527_ = v_dt_1523_;
v_isShared_1528_ = v_isSharedCheck_1568_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_date_1525_);
lean_dec(v_dt_1523_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1568_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1529_; lean_object* v_time_1530_; lean_object* v_date_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1567_; 
v___x_1529_ = lean_thunk_get_own(v_date_1525_);
lean_dec_ref(v_date_1525_);
v_time_1530_ = lean_ctor_get(v___x_1529_, 1);
v_date_1531_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1533_ = v___x_1529_;
v_isShared_1534_ = v_isSharedCheck_1567_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_time_1530_);
lean_inc(v_date_1531_);
lean_dec(v___x_1529_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1567_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v_hour_1535_; lean_object* v_minute_1536_; lean_object* v_second_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1565_; 
v_hour_1535_ = lean_ctor_get(v_time_1530_, 0);
v_minute_1536_ = lean_ctor_get(v_time_1530_, 1);
v_second_1537_ = lean_ctor_get(v_time_1530_, 2);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_time_1530_);
if (v_isSharedCheck_1565_ == 0)
{
lean_object* v_unused_1566_; 
v_unused_1566_ = lean_ctor_get(v_time_1530_, 3);
lean_dec(v_unused_1566_);
v___x_1539_ = v_time_1530_;
v_isShared_1540_ = v_isSharedCheck_1565_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_second_1537_);
lean_inc(v_minute_1536_);
lean_inc(v_hour_1535_);
lean_dec(v_time_1530_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1565_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_offset_1541_; lean_object* v___x_1543_; 
v_offset_1541_ = lean_ctor_get(v_tz_1522_, 0);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 3, v_nano_1524_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_hour_1535_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_minute_1536_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_second_1537_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_nano_1524_);
v___x_1543_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v___x_1543_);
v___x_1545_ = v___x_1533_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_date_1531_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1546_; lean_object* v_second_1547_; lean_object* v_nano_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_tm_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
lean_inc_ref(v___x_1545_);
v___x_1546_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1545_);
v_second_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_second_1547_);
v_nano_1548_ = lean_ctor_get(v___x_1546_, 1);
lean_inc(v_nano_1548_);
lean_dec_ref(v___x_1546_);
v___f_1549_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1549_, 0, v___x_1545_);
v___x_1550_ = lean_int_neg(v_offset_1541_);
v___x_1551_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1552_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1553_ = lean_int_mul(v_second_1547_, v___x_1552_);
lean_dec(v_second_1547_);
v___x_1554_ = lean_int_add(v___x_1553_, v_nano_1548_);
lean_dec(v_nano_1548_);
lean_dec(v___x_1553_);
v___x_1555_ = lean_int_mul(v___x_1550_, v___x_1552_);
lean_dec(v___x_1550_);
v___x_1556_ = lean_int_add(v___x_1555_, v___x_1551_);
lean_dec(v___x_1555_);
v___x_1557_ = lean_int_add(v___x_1554_, v___x_1556_);
lean_dec(v___x_1556_);
lean_dec(v___x_1554_);
v_tm_1558_ = l_Std_Time_Duration_ofNanoseconds(v___x_1557_);
lean_dec(v___x_1557_);
v___x_1559_ = lean_mk_thunk(v___f_1549_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1559_);
lean_ctor_set(v___x_1527_, 0, v_tm_1558_);
v___x_1561_ = v___x_1527_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_tm_1558_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds___boxed(lean_object* v_tz_1570_, lean_object* v_dt_1571_, lean_object* v_nano_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_Std_Time_DateTime_withNanoseconds(v_tz_1570_, v_dt_1571_, v_nano_1572_);
lean_dec_ref(v_tz_1570_);
return v_res_1573_;
}
}
static lean_object* _init_l_Std_Time_DateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_unsigned_to_nat(1000u);
v___x_1575_ = lean_nat_to_int(v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object* v_tz_1576_, lean_object* v_dt_1577_, lean_object* v_milli_1578_){
_start:
{
lean_object* v_date_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1627_; 
v_date_1579_ = lean_ctor_get(v_dt_1577_, 1);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_dt_1577_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v_dt_1577_, 0);
lean_dec(v_unused_1628_);
v___x_1581_ = v_dt_1577_;
v_isShared_1582_ = v_isSharedCheck_1627_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_date_1579_);
lean_dec(v_dt_1577_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1627_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v_time_1584_; lean_object* v_date_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1626_; 
v___x_1583_ = lean_thunk_get_own(v_date_1579_);
lean_dec_ref(v_date_1579_);
v_time_1584_ = lean_ctor_get(v___x_1583_, 1);
v_date_1585_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1587_ = v___x_1583_;
v_isShared_1588_ = v_isSharedCheck_1626_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_time_1584_);
lean_inc(v_date_1585_);
lean_dec(v___x_1583_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1626_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_hour_1589_; lean_object* v_minute_1590_; lean_object* v_second_1591_; lean_object* v_nanosecond_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1625_; 
v_hour_1589_ = lean_ctor_get(v_time_1584_, 0);
v_minute_1590_ = lean_ctor_get(v_time_1584_, 1);
v_second_1591_ = lean_ctor_get(v_time_1584_, 2);
v_nanosecond_1592_ = lean_ctor_get(v_time_1584_, 3);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_time_1584_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1594_ = v_time_1584_;
v_isShared_1595_ = v_isSharedCheck_1625_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_nanosecond_1592_);
lean_inc(v_second_1591_);
lean_inc(v_minute_1590_);
lean_inc(v_hour_1589_);
lean_dec(v_time_1584_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1625_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_offset_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
v_offset_1596_ = lean_ctor_get(v_tz_1576_, 0);
v___x_1597_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_1598_ = lean_int_emod(v_nanosecond_1592_, v___x_1597_);
lean_dec(v_nanosecond_1592_);
v___x_1599_ = lean_obj_once(&l_Std_Time_DateTime_addMilliseconds___closed__0, &l_Std_Time_DateTime_addMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_addMilliseconds___closed__0);
v___x_1600_ = lean_int_mul(v_milli_1578_, v___x_1599_);
v___x_1601_ = lean_int_add(v___x_1600_, v___x_1598_);
lean_dec(v___x_1598_);
lean_dec(v___x_1600_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 3, v___x_1601_);
v___x_1603_ = v___x_1594_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_hour_1589_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_minute_1590_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_second_1591_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1605_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 1, v___x_1603_);
v___x_1605_ = v___x_1587_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_date_1585_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; lean_object* v_second_1607_; lean_object* v_nano_1608_; lean_object* v___f_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v_tm_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_inc_ref(v___x_1605_);
v___x_1606_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1605_);
v_second_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_second_1607_);
v_nano_1608_ = lean_ctor_get(v___x_1606_, 1);
lean_inc(v_nano_1608_);
lean_dec_ref(v___x_1606_);
v___f_1609_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1609_, 0, v___x_1605_);
v___x_1610_ = lean_int_neg(v_offset_1596_);
v___x_1611_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1612_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1613_ = lean_int_mul(v_second_1607_, v___x_1612_);
lean_dec(v_second_1607_);
v___x_1614_ = lean_int_add(v___x_1613_, v_nano_1608_);
lean_dec(v_nano_1608_);
lean_dec(v___x_1613_);
v___x_1615_ = lean_int_mul(v___x_1610_, v___x_1612_);
lean_dec(v___x_1610_);
v___x_1616_ = lean_int_add(v___x_1615_, v___x_1611_);
lean_dec(v___x_1615_);
v___x_1617_ = lean_int_add(v___x_1614_, v___x_1616_);
lean_dec(v___x_1616_);
lean_dec(v___x_1614_);
v_tm_1618_ = l_Std_Time_Duration_ofNanoseconds(v___x_1617_);
lean_dec(v___x_1617_);
v___x_1619_ = lean_mk_thunk(v___f_1609_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1619_);
lean_ctor_set(v___x_1581_, 0, v_tm_1618_);
v___x_1621_ = v___x_1581_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_tm_1618_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object* v_tz_1629_, lean_object* v_dt_1630_, lean_object* v_milli_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Std_Time_DateTime_withMilliseconds(v_tz_1629_, v_dt_1630_, v_milli_1631_);
lean_dec(v_milli_1631_);
lean_dec_ref(v_tz_1629_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg(lean_object* v_dt_1633_){
_start:
{
lean_object* v_date_1634_; lean_object* v___x_1635_; 
v_date_1634_ = lean_ctor_get(v_dt_1633_, 1);
v___x_1635_ = lean_thunk_get_own(v_date_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___redArg___boxed(lean_object* v_dt_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Std_Time_DateTime_toPlainDateTime___redArg(v_dt_1636_);
lean_dec_ref(v_dt_1636_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object* v_tz_1638_, lean_object* v_dt_1639_){
_start:
{
lean_object* v_date_1640_; lean_object* v___x_1641_; 
v_date_1640_ = lean_ctor_get(v_dt_1639_, 1);
v___x_1641_ = lean_thunk_get_own(v_date_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object* v_tz_1642_, lean_object* v_dt_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Std_Time_DateTime_toPlainDateTime(v_tz_1642_, v_dt_1643_);
lean_dec_ref(v_dt_1643_);
lean_dec_ref(v_tz_1642_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg(lean_object* v_dt_1645_){
_start:
{
lean_object* v_date_1646_; lean_object* v___x_1647_; lean_object* v_date_1648_; lean_object* v_year_1649_; 
v_date_1646_ = lean_ctor_get(v_dt_1645_, 1);
v___x_1647_ = lean_thunk_get_own(v_date_1646_);
v_date_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc_ref(v_date_1648_);
lean_dec(v___x_1647_);
v_year_1649_ = lean_ctor_get(v_date_1648_, 0);
lean_inc(v_year_1649_);
lean_dec_ref(v_date_1648_);
return v_year_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___redArg___boxed(lean_object* v_dt_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Std_Time_DateTime_year___redArg(v_dt_1650_);
lean_dec_ref(v_dt_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object* v_tz_1652_, lean_object* v_dt_1653_){
_start:
{
lean_object* v_date_1654_; lean_object* v___x_1655_; lean_object* v_date_1656_; lean_object* v_year_1657_; 
v_date_1654_ = lean_ctor_get(v_dt_1653_, 1);
v___x_1655_ = lean_thunk_get_own(v_date_1654_);
v_date_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc_ref(v_date_1656_);
lean_dec(v___x_1655_);
v_year_1657_ = lean_ctor_get(v_date_1656_, 0);
lean_inc(v_year_1657_);
lean_dec_ref(v_date_1656_);
return v_year_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object* v_tz_1658_, lean_object* v_dt_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Std_Time_DateTime_year(v_tz_1658_, v_dt_1659_);
lean_dec_ref(v_dt_1659_);
lean_dec_ref(v_tz_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg(lean_object* v_dt_1661_){
_start:
{
lean_object* v_date_1662_; lean_object* v___x_1663_; lean_object* v_date_1664_; lean_object* v_month_1665_; 
v_date_1662_ = lean_ctor_get(v_dt_1661_, 1);
v___x_1663_ = lean_thunk_get_own(v_date_1662_);
v_date_1664_ = lean_ctor_get(v___x_1663_, 0);
lean_inc_ref(v_date_1664_);
lean_dec(v___x_1663_);
v_month_1665_ = lean_ctor_get(v_date_1664_, 1);
lean_inc(v_month_1665_);
lean_dec_ref(v_date_1664_);
return v_month_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___redArg___boxed(lean_object* v_dt_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Std_Time_DateTime_month___redArg(v_dt_1666_);
lean_dec_ref(v_dt_1666_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object* v_tz_1668_, lean_object* v_dt_1669_){
_start:
{
lean_object* v_date_1670_; lean_object* v___x_1671_; lean_object* v_date_1672_; lean_object* v_month_1673_; 
v_date_1670_ = lean_ctor_get(v_dt_1669_, 1);
v___x_1671_ = lean_thunk_get_own(v_date_1670_);
v_date_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc_ref(v_date_1672_);
lean_dec(v___x_1671_);
v_month_1673_ = lean_ctor_get(v_date_1672_, 1);
lean_inc(v_month_1673_);
lean_dec_ref(v_date_1672_);
return v_month_1673_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object* v_tz_1674_, lean_object* v_dt_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Std_Time_DateTime_month(v_tz_1674_, v_dt_1675_);
lean_dec_ref(v_dt_1675_);
lean_dec_ref(v_tz_1674_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg(lean_object* v_dt_1677_){
_start:
{
lean_object* v_date_1678_; lean_object* v___x_1679_; lean_object* v_date_1680_; lean_object* v_day_1681_; 
v_date_1678_ = lean_ctor_get(v_dt_1677_, 1);
v___x_1679_ = lean_thunk_get_own(v_date_1678_);
v_date_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc_ref(v_date_1680_);
lean_dec(v___x_1679_);
v_day_1681_ = lean_ctor_get(v_date_1680_, 2);
lean_inc(v_day_1681_);
lean_dec_ref(v_date_1680_);
return v_day_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___redArg___boxed(lean_object* v_dt_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Std_Time_DateTime_day___redArg(v_dt_1682_);
lean_dec_ref(v_dt_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object* v_tz_1684_, lean_object* v_dt_1685_){
_start:
{
lean_object* v_date_1686_; lean_object* v___x_1687_; lean_object* v_date_1688_; lean_object* v_day_1689_; 
v_date_1686_ = lean_ctor_get(v_dt_1685_, 1);
v___x_1687_ = lean_thunk_get_own(v_date_1686_);
v_date_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc_ref(v_date_1688_);
lean_dec(v___x_1687_);
v_day_1689_ = lean_ctor_get(v_date_1688_, 2);
lean_inc(v_day_1689_);
lean_dec_ref(v_date_1688_);
return v_day_1689_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object* v_tz_1690_, lean_object* v_dt_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_Time_DateTime_day(v_tz_1690_, v_dt_1691_);
lean_dec_ref(v_dt_1691_);
lean_dec_ref(v_tz_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg(lean_object* v_dt_1693_){
_start:
{
lean_object* v_date_1694_; lean_object* v___x_1695_; lean_object* v_time_1696_; lean_object* v_hour_1697_; 
v_date_1694_ = lean_ctor_get(v_dt_1693_, 1);
v___x_1695_ = lean_thunk_get_own(v_date_1694_);
v_time_1696_ = lean_ctor_get(v___x_1695_, 1);
lean_inc_ref(v_time_1696_);
lean_dec(v___x_1695_);
v_hour_1697_ = lean_ctor_get(v_time_1696_, 0);
lean_inc(v_hour_1697_);
lean_dec_ref(v_time_1696_);
return v_hour_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___redArg___boxed(lean_object* v_dt_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Std_Time_DateTime_hour___redArg(v_dt_1698_);
lean_dec_ref(v_dt_1698_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object* v_tz_1700_, lean_object* v_dt_1701_){
_start:
{
lean_object* v_date_1702_; lean_object* v___x_1703_; lean_object* v_time_1704_; lean_object* v_hour_1705_; 
v_date_1702_ = lean_ctor_get(v_dt_1701_, 1);
v___x_1703_ = lean_thunk_get_own(v_date_1702_);
v_time_1704_ = lean_ctor_get(v___x_1703_, 1);
lean_inc_ref(v_time_1704_);
lean_dec(v___x_1703_);
v_hour_1705_ = lean_ctor_get(v_time_1704_, 0);
lean_inc(v_hour_1705_);
lean_dec_ref(v_time_1704_);
return v_hour_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object* v_tz_1706_, lean_object* v_dt_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Std_Time_DateTime_hour(v_tz_1706_, v_dt_1707_);
lean_dec_ref(v_dt_1707_);
lean_dec_ref(v_tz_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg(lean_object* v_dt_1709_){
_start:
{
lean_object* v_date_1710_; lean_object* v___x_1711_; lean_object* v_time_1712_; lean_object* v_minute_1713_; 
v_date_1710_ = lean_ctor_get(v_dt_1709_, 1);
v___x_1711_ = lean_thunk_get_own(v_date_1710_);
v_time_1712_ = lean_ctor_get(v___x_1711_, 1);
lean_inc_ref(v_time_1712_);
lean_dec(v___x_1711_);
v_minute_1713_ = lean_ctor_get(v_time_1712_, 1);
lean_inc(v_minute_1713_);
lean_dec_ref(v_time_1712_);
return v_minute_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___redArg___boxed(lean_object* v_dt_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Std_Time_DateTime_minute___redArg(v_dt_1714_);
lean_dec_ref(v_dt_1714_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object* v_tz_1716_, lean_object* v_dt_1717_){
_start:
{
lean_object* v_date_1718_; lean_object* v___x_1719_; lean_object* v_time_1720_; lean_object* v_minute_1721_; 
v_date_1718_ = lean_ctor_get(v_dt_1717_, 1);
v___x_1719_ = lean_thunk_get_own(v_date_1718_);
v_time_1720_ = lean_ctor_get(v___x_1719_, 1);
lean_inc_ref(v_time_1720_);
lean_dec(v___x_1719_);
v_minute_1721_ = lean_ctor_get(v_time_1720_, 1);
lean_inc(v_minute_1721_);
lean_dec_ref(v_time_1720_);
return v_minute_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object* v_tz_1722_, lean_object* v_dt_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_Time_DateTime_minute(v_tz_1722_, v_dt_1723_);
lean_dec_ref(v_dt_1723_);
lean_dec_ref(v_tz_1722_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg(lean_object* v_dt_1725_){
_start:
{
lean_object* v_date_1726_; lean_object* v___x_1727_; lean_object* v_time_1728_; lean_object* v_second_1729_; 
v_date_1726_ = lean_ctor_get(v_dt_1725_, 1);
v___x_1727_ = lean_thunk_get_own(v_date_1726_);
v_time_1728_ = lean_ctor_get(v___x_1727_, 1);
lean_inc_ref(v_time_1728_);
lean_dec(v___x_1727_);
v_second_1729_ = lean_ctor_get(v_time_1728_, 2);
lean_inc(v_second_1729_);
lean_dec_ref(v_time_1728_);
return v_second_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___redArg___boxed(lean_object* v_dt_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Std_Time_DateTime_second___redArg(v_dt_1730_);
lean_dec_ref(v_dt_1730_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object* v_tz_1732_, lean_object* v_dt_1733_){
_start:
{
lean_object* v_date_1734_; lean_object* v___x_1735_; lean_object* v_time_1736_; lean_object* v_second_1737_; 
v_date_1734_ = lean_ctor_get(v_dt_1733_, 1);
v___x_1735_ = lean_thunk_get_own(v_date_1734_);
v_time_1736_ = lean_ctor_get(v___x_1735_, 1);
lean_inc_ref(v_time_1736_);
lean_dec(v___x_1735_);
v_second_1737_ = lean_ctor_get(v_time_1736_, 2);
lean_inc(v_second_1737_);
lean_dec_ref(v_time_1736_);
return v_second_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object* v_tz_1738_, lean_object* v_dt_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Std_Time_DateTime_second(v_tz_1738_, v_dt_1739_);
lean_dec_ref(v_dt_1739_);
lean_dec_ref(v_tz_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg(lean_object* v_dt_1741_){
_start:
{
lean_object* v_date_1742_; lean_object* v___x_1743_; lean_object* v_time_1744_; lean_object* v_nanosecond_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_date_1742_ = lean_ctor_get(v_dt_1741_, 1);
v___x_1743_ = lean_thunk_get_own(v_date_1742_);
v_time_1744_ = lean_ctor_get(v___x_1743_, 1);
lean_inc_ref(v_time_1744_);
lean_dec(v___x_1743_);
v_nanosecond_1745_ = lean_ctor_get(v_time_1744_, 3);
lean_inc(v_nanosecond_1745_);
lean_dec_ref(v_time_1744_);
v___x_1746_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_1747_ = lean_int_emod(v_nanosecond_1745_, v___x_1746_);
lean_dec(v_nanosecond_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___redArg___boxed(lean_object* v_dt_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Std_Time_DateTime_millisecond___redArg(v_dt_1748_);
lean_dec_ref(v_dt_1748_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object* v_tz_1750_, lean_object* v_dt_1751_){
_start:
{
lean_object* v_date_1752_; lean_object* v___x_1753_; lean_object* v_time_1754_; lean_object* v_nanosecond_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_date_1752_ = lean_ctor_get(v_dt_1751_, 1);
v___x_1753_ = lean_thunk_get_own(v_date_1752_);
v_time_1754_ = lean_ctor_get(v___x_1753_, 1);
lean_inc_ref(v_time_1754_);
lean_dec(v___x_1753_);
v_nanosecond_1755_ = lean_ctor_get(v_time_1754_, 3);
lean_inc(v_nanosecond_1755_);
lean_dec_ref(v_time_1754_);
v___x_1756_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_1757_ = lean_int_emod(v_nanosecond_1755_, v___x_1756_);
lean_dec(v_nanosecond_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object* v_tz_1758_, lean_object* v_dt_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Std_Time_DateTime_millisecond(v_tz_1758_, v_dt_1759_);
lean_dec_ref(v_dt_1759_);
lean_dec_ref(v_tz_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg(lean_object* v_dt_1761_){
_start:
{
lean_object* v_date_1762_; lean_object* v___x_1763_; lean_object* v_time_1764_; lean_object* v_nanosecond_1765_; 
v_date_1762_ = lean_ctor_get(v_dt_1761_, 1);
v___x_1763_ = lean_thunk_get_own(v_date_1762_);
v_time_1764_ = lean_ctor_get(v___x_1763_, 1);
lean_inc_ref(v_time_1764_);
lean_dec(v___x_1763_);
v_nanosecond_1765_ = lean_ctor_get(v_time_1764_, 3);
lean_inc(v_nanosecond_1765_);
lean_dec_ref(v_time_1764_);
return v_nanosecond_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___redArg___boxed(lean_object* v_dt_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Std_Time_DateTime_nanosecond___redArg(v_dt_1766_);
lean_dec_ref(v_dt_1766_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object* v_tz_1768_, lean_object* v_dt_1769_){
_start:
{
lean_object* v_date_1770_; lean_object* v___x_1771_; lean_object* v_time_1772_; lean_object* v_nanosecond_1773_; 
v_date_1770_ = lean_ctor_get(v_dt_1769_, 1);
v___x_1771_ = lean_thunk_get_own(v_date_1770_);
v_time_1772_ = lean_ctor_get(v___x_1771_, 1);
lean_inc_ref(v_time_1772_);
lean_dec(v___x_1771_);
v_nanosecond_1773_ = lean_ctor_get(v_time_1772_, 3);
lean_inc(v_nanosecond_1773_);
lean_dec_ref(v_time_1772_);
return v_nanosecond_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object* v_tz_1774_, lean_object* v_dt_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_Time_DateTime_nanosecond(v_tz_1774_, v_dt_1775_);
lean_dec_ref(v_dt_1775_);
lean_dec_ref(v_tz_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday___redArg(lean_object* v_dt_1777_){
_start:
{
lean_object* v_date_1778_; lean_object* v___x_1779_; lean_object* v_date_1780_; uint8_t v___x_1781_; 
v_date_1778_ = lean_ctor_get(v_dt_1777_, 1);
v___x_1779_ = lean_thunk_get_own(v_date_1778_);
v_date_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc_ref(v_date_1780_);
lean_dec(v___x_1779_);
v___x_1781_ = l_Std_Time_PlainDate_weekday(v_date_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___redArg___boxed(lean_object* v_dt_1782_){
_start:
{
uint8_t v_res_1783_; lean_object* v_r_1784_; 
v_res_1783_ = l_Std_Time_DateTime_weekday___redArg(v_dt_1782_);
lean_dec_ref(v_dt_1782_);
v_r_1784_ = lean_box(v_res_1783_);
return v_r_1784_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object* v_tz_1785_, lean_object* v_dt_1786_){
_start:
{
lean_object* v_date_1787_; lean_object* v___x_1788_; lean_object* v_date_1789_; uint8_t v___x_1790_; 
v_date_1787_ = lean_ctor_get(v_dt_1786_, 1);
v___x_1788_ = lean_thunk_get_own(v_date_1787_);
v_date_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc_ref(v_date_1789_);
lean_dec(v___x_1788_);
v___x_1790_ = l_Std_Time_PlainDate_weekday(v_date_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object* v_tz_1791_, lean_object* v_dt_1792_){
_start:
{
uint8_t v_res_1793_; lean_object* v_r_1794_; 
v_res_1793_ = l_Std_Time_DateTime_weekday(v_tz_1791_, v_dt_1792_);
lean_dec_ref(v_dt_1792_);
lean_dec_ref(v_tz_1791_);
v_r_1794_ = lean_box(v_res_1793_);
return v_r_1794_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era___redArg(lean_object* v_date_1795_){
_start:
{
lean_object* v_date_1796_; lean_object* v___x_1797_; lean_object* v_date_1798_; lean_object* v_year_1799_; uint8_t v___x_1800_; 
v_date_1796_ = lean_ctor_get(v_date_1795_, 1);
v___x_1797_ = lean_thunk_get_own(v_date_1796_);
v_date_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc_ref(v_date_1798_);
lean_dec(v___x_1797_);
v_year_1799_ = lean_ctor_get(v_date_1798_, 0);
lean_inc(v_year_1799_);
lean_dec_ref(v_date_1798_);
v___x_1800_ = l_Std_Time_Year_Offset_era(v_year_1799_);
lean_dec(v_year_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___redArg___boxed(lean_object* v_date_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_Std_Time_DateTime_era___redArg(v_date_1801_);
lean_dec_ref(v_date_1801_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object* v_tz_1804_, lean_object* v_date_1805_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = l_Std_Time_DateTime_era___redArg(v_date_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object* v_tz_1807_, lean_object* v_date_1808_){
_start:
{
uint8_t v_res_1809_; lean_object* v_r_1810_; 
v_res_1809_ = l_Std_Time_DateTime_era(v_tz_1807_, v_date_1808_);
lean_dec_ref(v_date_1808_);
lean_dec_ref(v_tz_1807_);
v_r_1810_ = lean_box(v_res_1809_);
return v_r_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object* v_tz_1811_, lean_object* v_dt_1812_, uint8_t v_desiredWeekday_1813_){
_start:
{
lean_object* v_date_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1838_; 
v_date_1814_ = lean_ctor_get(v_dt_1812_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_dt_1812_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v_dt_1812_, 0);
lean_dec(v_unused_1839_);
v___x_1816_ = v_dt_1812_;
v_isShared_1817_ = v_isSharedCheck_1838_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_date_1814_);
lean_dec(v_dt_1812_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1838_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_offset_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v_second_1822_; lean_object* v_nano_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v_tm_1833_; lean_object* v___x_1834_; lean_object* v___x_1836_; 
v_offset_1818_ = lean_ctor_get(v_tz_1811_, 0);
v___x_1819_ = lean_thunk_get_own(v_date_1814_);
lean_dec_ref(v_date_1814_);
v___x_1820_ = l_Std_Time_PlainDateTime_withWeekday(v___x_1819_, v_desiredWeekday_1813_);
lean_inc_ref(v___x_1820_);
v___x_1821_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1820_);
v_second_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_second_1822_);
v_nano_1823_ = lean_ctor_get(v___x_1821_, 1);
lean_inc(v_nano_1823_);
lean_dec_ref(v___x_1821_);
v___f_1824_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1824_, 0, v___x_1820_);
v___x_1825_ = lean_int_neg(v_offset_1818_);
v___x_1826_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1827_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1828_ = lean_int_mul(v_second_1822_, v___x_1827_);
lean_dec(v_second_1822_);
v___x_1829_ = lean_int_add(v___x_1828_, v_nano_1823_);
lean_dec(v_nano_1823_);
lean_dec(v___x_1828_);
v___x_1830_ = lean_int_mul(v___x_1825_, v___x_1827_);
lean_dec(v___x_1825_);
v___x_1831_ = lean_int_add(v___x_1830_, v___x_1826_);
lean_dec(v___x_1830_);
v___x_1832_ = lean_int_add(v___x_1829_, v___x_1831_);
lean_dec(v___x_1831_);
lean_dec(v___x_1829_);
v_tm_1833_ = l_Std_Time_Duration_ofNanoseconds(v___x_1832_);
lean_dec(v___x_1832_);
v___x_1834_ = lean_mk_thunk(v___f_1824_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v___x_1834_);
lean_ctor_set(v___x_1816_, 0, v_tm_1833_);
v___x_1836_ = v___x_1816_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_tm_1833_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object* v_tz_1840_, lean_object* v_dt_1841_, lean_object* v_desiredWeekday_1842_){
_start:
{
uint8_t v_desiredWeekday_boxed_1843_; lean_object* v_res_1844_; 
v_desiredWeekday_boxed_1843_ = lean_unbox(v_desiredWeekday_1842_);
v_res_1844_ = l_Std_Time_DateTime_withWeekday(v_tz_1840_, v_dt_1841_, v_desiredWeekday_boxed_1843_);
lean_dec_ref(v_tz_1840_);
return v_res_1844_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear___redArg(lean_object* v_date_1845_){
_start:
{
lean_object* v_date_1846_; lean_object* v___x_1847_; lean_object* v_date_1848_; lean_object* v_year_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1857_; 
v_date_1846_ = lean_ctor_get(v_date_1845_, 1);
v___x_1847_ = lean_thunk_get_own(v_date_1846_);
v_date_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc_ref(v_date_1848_);
lean_dec(v___x_1847_);
v_year_1849_ = lean_ctor_get(v_date_1848_, 0);
lean_inc(v_year_1849_);
lean_dec_ref(v_date_1848_);
v___x_1850_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_1851_ = lean_int_mod(v_year_1849_, v___x_1850_);
v___x_1852_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1857_ = lean_int_dec_eq(v___x_1851_, v___x_1852_);
lean_dec(v___x_1851_);
if (v___x_1857_ == 0)
{
lean_dec(v_year_1849_);
return v___x_1857_;
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1858_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_1859_ = lean_int_mod(v_year_1849_, v___x_1858_);
v___x_1860_ = lean_int_dec_eq(v___x_1859_, v___x_1852_);
lean_dec(v___x_1859_);
if (v___x_1860_ == 0)
{
if (v___x_1857_ == 0)
{
goto v___jp_1853_;
}
else
{
lean_dec(v_year_1849_);
return v___x_1857_;
}
}
else
{
goto v___jp_1853_;
}
}
v___jp_1853_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_1855_ = lean_int_mod(v_year_1849_, v___x_1854_);
lean_dec(v_year_1849_);
v___x_1856_ = lean_int_dec_eq(v___x_1855_, v___x_1852_);
lean_dec(v___x_1855_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___redArg___boxed(lean_object* v_date_1861_){
_start:
{
uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_res_1862_ = l_Std_Time_DateTime_inLeapYear___redArg(v_date_1861_);
lean_dec_ref(v_date_1861_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object* v_tz_1864_, lean_object* v_date_1865_){
_start:
{
uint8_t v___x_1866_; 
v___x_1866_ = l_Std_Time_DateTime_inLeapYear___redArg(v_date_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object* v_tz_1867_, lean_object* v_date_1868_){
_start:
{
uint8_t v_res_1869_; lean_object* v_r_1870_; 
v_res_1869_ = l_Std_Time_DateTime_inLeapYear(v_tz_1867_, v_date_1868_);
lean_dec_ref(v_date_1868_);
lean_dec_ref(v_tz_1867_);
v_r_1870_ = lean_box(v_res_1869_);
return v_r_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg(lean_object* v_date_1871_){
_start:
{
lean_object* v_date_1872_; uint8_t v___y_1874_; lean_object* v___x_1888_; lean_object* v_date_1889_; lean_object* v_year_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1898_; 
v_date_1872_ = lean_ctor_get(v_date_1871_, 1);
v___x_1888_ = lean_thunk_get_own(v_date_1872_);
v_date_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc_ref(v_date_1889_);
lean_dec(v___x_1888_);
v_year_1890_ = lean_ctor_get(v_date_1889_, 0);
lean_inc(v_year_1890_);
lean_dec_ref(v_date_1889_);
v___x_1891_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__0, &l_Std_Time_DateTime_withDaysClip___closed__0_once, _init_l_Std_Time_DateTime_withDaysClip___closed__0);
v___x_1892_ = lean_int_mod(v_year_1890_, v___x_1891_);
v___x_1893_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1898_ = lean_int_dec_eq(v___x_1892_, v___x_1893_);
lean_dec(v___x_1892_);
if (v___x_1898_ == 0)
{
lean_dec(v_year_1890_);
v___y_1874_ = v___x_1898_;
goto v___jp_1873_;
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v___x_1899_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__2, &l_Std_Time_DateTime_withDaysClip___closed__2_once, _init_l_Std_Time_DateTime_withDaysClip___closed__2);
v___x_1900_ = lean_int_mod(v_year_1890_, v___x_1899_);
v___x_1901_ = lean_int_dec_eq(v___x_1900_, v___x_1893_);
lean_dec(v___x_1900_);
if (v___x_1901_ == 0)
{
if (v___x_1898_ == 0)
{
goto v___jp_1894_;
}
else
{
lean_dec(v_year_1890_);
v___y_1874_ = v___x_1898_;
goto v___jp_1873_;
}
}
else
{
goto v___jp_1894_;
}
}
v___jp_1873_:
{
lean_object* v___x_1875_; lean_object* v_date_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1886_; 
v___x_1875_ = lean_thunk_get_own(v_date_1872_);
v_date_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1886_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1886_ == 0)
{
lean_object* v_unused_1887_; 
v_unused_1887_ = lean_ctor_get(v___x_1875_, 1);
lean_dec(v_unused_1887_);
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_date_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1886_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v_month_1880_; lean_object* v_day_1881_; lean_object* v___x_1883_; 
v_month_1880_ = lean_ctor_get(v_date_1876_, 1);
lean_inc(v_month_1880_);
v_day_1881_ = lean_ctor_get(v_date_1876_, 2);
lean_inc(v_day_1881_);
lean_dec_ref(v_date_1876_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 1, v_day_1881_);
lean_ctor_set(v___x_1878_, 0, v_month_1880_);
v___x_1883_ = v___x_1878_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v_month_1880_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v_day_1881_);
v___x_1883_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_Time_ValidDate_dayOfYear(v___y_1874_, v___x_1883_);
lean_dec_ref(v___x_1883_);
return v___x_1884_;
}
}
}
v___jp_1894_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v___x_1895_ = lean_obj_once(&l_Std_Time_DateTime_withDaysClip___closed__1, &l_Std_Time_DateTime_withDaysClip___closed__1_once, _init_l_Std_Time_DateTime_withDaysClip___closed__1);
v___x_1896_ = lean_int_mod(v_year_1890_, v___x_1895_);
lean_dec(v_year_1890_);
v___x_1897_ = lean_int_dec_eq(v___x_1896_, v___x_1893_);
lean_dec(v___x_1896_);
v___y_1874_ = v___x_1897_;
goto v___jp_1873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___redArg___boxed(lean_object* v_date_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Std_Time_DateTime_dayOfYear___redArg(v_date_1902_);
lean_dec_ref(v_date_1902_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object* v_tz_1904_, lean_object* v_date_1905_){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Std_Time_DateTime_dayOfYear___redArg(v_date_1905_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object* v_tz_1907_, lean_object* v_date_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Std_Time_DateTime_dayOfYear(v_tz_1907_, v_date_1908_);
lean_dec_ref(v_date_1908_);
lean_dec_ref(v_tz_1907_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg(lean_object* v_date_1910_, uint8_t v_firstDay_1911_){
_start:
{
lean_object* v_date_1912_; lean_object* v___x_1913_; lean_object* v_date_1914_; lean_object* v___x_1915_; 
v_date_1912_ = lean_ctor_get(v_date_1910_, 1);
v___x_1913_ = lean_thunk_get_own(v_date_1912_);
v_date_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_ref(v_date_1914_);
lean_dec(v___x_1913_);
v___x_1915_ = l_Std_Time_PlainDate_weekOfYear(v_date_1914_, v_firstDay_1911_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___redArg___boxed(lean_object* v_date_1916_, lean_object* v_firstDay_1917_){
_start:
{
uint8_t v_firstDay_boxed_1918_; lean_object* v_res_1919_; 
v_firstDay_boxed_1918_ = lean_unbox(v_firstDay_1917_);
v_res_1919_ = l_Std_Time_DateTime_weekOfYear___redArg(v_date_1916_, v_firstDay_boxed_1918_);
lean_dec_ref(v_date_1916_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* v_tz_1920_, lean_object* v_date_1921_, uint8_t v_firstDay_1922_){
_start:
{
lean_object* v_date_1923_; lean_object* v___x_1924_; lean_object* v_date_1925_; lean_object* v___x_1926_; 
v_date_1923_ = lean_ctor_get(v_date_1921_, 1);
v___x_1924_ = lean_thunk_get_own(v_date_1923_);
v_date_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc_ref(v_date_1925_);
lean_dec(v___x_1924_);
v___x_1926_ = l_Std_Time_PlainDate_weekOfYear(v_date_1925_, v_firstDay_1922_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object* v_tz_1927_, lean_object* v_date_1928_, lean_object* v_firstDay_1929_){
_start:
{
uint8_t v_firstDay_boxed_1930_; lean_object* v_res_1931_; 
v_firstDay_boxed_1930_ = lean_unbox(v_firstDay_1929_);
v_res_1931_ = l_Std_Time_DateTime_weekOfYear(v_tz_1927_, v_date_1928_, v_firstDay_boxed_1930_);
lean_dec_ref(v_date_1928_);
lean_dec_ref(v_tz_1927_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___redArg(lean_object* v_date_1932_, uint8_t v_firstDay_1933_){
_start:
{
lean_object* v_date_1934_; lean_object* v___x_1935_; lean_object* v_date_1936_; lean_object* v___x_1937_; 
v_date_1934_ = lean_ctor_get(v_date_1932_, 1);
v___x_1935_ = lean_thunk_get_own(v_date_1934_);
v_date_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc_ref(v_date_1936_);
lean_dec(v___x_1935_);
v___x_1937_ = l_Std_Time_PlainDate_weekYear(v_date_1936_, v_firstDay_1933_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___redArg___boxed(lean_object* v_date_1938_, lean_object* v_firstDay_1939_){
_start:
{
uint8_t v_firstDay_boxed_1940_; lean_object* v_res_1941_; 
v_firstDay_boxed_1940_ = lean_unbox(v_firstDay_1939_);
v_res_1941_ = l_Std_Time_DateTime_weekYear___redArg(v_date_1938_, v_firstDay_boxed_1940_);
lean_dec_ref(v_date_1938_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear(lean_object* v_tz_1942_, lean_object* v_date_1943_, uint8_t v_firstDay_1944_){
_start:
{
lean_object* v_date_1945_; lean_object* v___x_1946_; lean_object* v_date_1947_; lean_object* v___x_1948_; 
v_date_1945_ = lean_ctor_get(v_date_1943_, 1);
v___x_1946_ = lean_thunk_get_own(v_date_1945_);
v_date_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc_ref(v_date_1947_);
lean_dec(v___x_1946_);
v___x_1948_ = l_Std_Time_PlainDate_weekYear(v_date_1947_, v_firstDay_1944_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___boxed(lean_object* v_tz_1949_, lean_object* v_date_1950_, lean_object* v_firstDay_1951_){
_start:
{
uint8_t v_firstDay_boxed_1952_; lean_object* v_res_1953_; 
v_firstDay_boxed_1952_ = lean_unbox(v_firstDay_1951_);
v_res_1953_ = l_Std_Time_DateTime_weekYear(v_tz_1949_, v_date_1950_, v_firstDay_boxed_1952_);
lean_dec_ref(v_date_1950_);
lean_dec_ref(v_tz_1949_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg(lean_object* v_date_1954_){
_start:
{
lean_object* v_date_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v_date_1955_ = lean_ctor_get(v_date_1954_, 1);
v___x_1956_ = lean_thunk_get_own(v_date_1955_);
v___x_1957_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_1956_);
lean_dec(v___x_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___redArg___boxed(lean_object* v_date_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Std_Time_DateTime_weekOfMonth___redArg(v_date_1958_);
lean_dec_ref(v_date_1958_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* v_tz_1960_, lean_object* v_date_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Std_Time_DateTime_weekOfMonth___redArg(v_date_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object* v_tz_1963_, lean_object* v_date_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Std_Time_DateTime_weekOfMonth(v_tz_1963_, v_date_1964_);
lean_dec_ref(v_date_1964_);
lean_dec_ref(v_tz_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg(lean_object* v_date_1966_, uint8_t v_firstDay_1967_){
_start:
{
lean_object* v_date_1968_; lean_object* v___x_1969_; lean_object* v_date_1970_; lean_object* v___x_1971_; 
v_date_1968_ = lean_ctor_get(v_date_1966_, 1);
v___x_1969_ = lean_thunk_get_own(v_date_1968_);
v_date_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc_ref(v_date_1970_);
lean_dec(v___x_1969_);
v___x_1971_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1970_, v_firstDay_1967_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___redArg___boxed(lean_object* v_date_1972_, lean_object* v_firstDay_1973_){
_start:
{
uint8_t v_firstDay_boxed_1974_; lean_object* v_res_1975_; 
v_firstDay_boxed_1974_ = lean_unbox(v_firstDay_1973_);
v_res_1975_ = l_Std_Time_DateTime_alignedWeekOfMonth___redArg(v_date_1972_, v_firstDay_boxed_1974_);
lean_dec_ref(v_date_1972_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* v_tz_1976_, lean_object* v_date_1977_, uint8_t v_firstDay_1978_){
_start:
{
lean_object* v_date_1979_; lean_object* v___x_1980_; lean_object* v_date_1981_; lean_object* v___x_1982_; 
v_date_1979_ = lean_ctor_get(v_date_1977_, 1);
v___x_1980_ = lean_thunk_get_own(v_date_1979_);
v_date_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc_ref(v_date_1981_);
lean_dec(v___x_1980_);
v___x_1982_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1981_, v_firstDay_1978_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object* v_tz_1983_, lean_object* v_date_1984_, lean_object* v_firstDay_1985_){
_start:
{
uint8_t v_firstDay_boxed_1986_; lean_object* v_res_1987_; 
v_firstDay_boxed_1986_ = lean_unbox(v_firstDay_1985_);
v_res_1987_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_tz_1983_, v_date_1984_, v_firstDay_boxed_1986_);
lean_dec_ref(v_date_1984_);
lean_dec_ref(v_tz_1983_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg(lean_object* v_date_1988_){
_start:
{
lean_object* v_date_1989_; lean_object* v___x_1990_; lean_object* v_date_1991_; lean_object* v___x_1992_; 
v_date_1989_ = lean_ctor_get(v_date_1988_, 1);
v___x_1990_ = lean_thunk_get_own(v_date_1989_);
v_date_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_ref(v_date_1991_);
lean_dec(v___x_1990_);
v___x_1992_ = l_Std_Time_PlainDate_quarter(v_date_1991_);
lean_dec_ref(v_date_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___redArg___boxed(lean_object* v_date_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Std_Time_DateTime_quarter___redArg(v_date_1993_);
lean_dec_ref(v_date_1993_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* v_tz_1995_, lean_object* v_date_1996_){
_start:
{
lean_object* v_date_1997_; lean_object* v___x_1998_; lean_object* v_date_1999_; lean_object* v___x_2000_; 
v_date_1997_ = lean_ctor_get(v_date_1996_, 1);
v___x_1998_ = lean_thunk_get_own(v_date_1997_);
v_date_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc_ref(v_date_1999_);
lean_dec(v___x_1998_);
v___x_2000_ = l_Std_Time_PlainDate_quarter(v_date_1999_);
lean_dec_ref(v_date_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object* v_tz_2001_, lean_object* v_date_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Std_Time_DateTime_quarter(v_tz_2001_, v_date_2002_);
lean_dec_ref(v_date_2002_);
lean_dec_ref(v_tz_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg(lean_object* v_zdt_2004_){
_start:
{
lean_object* v_date_2005_; lean_object* v___x_2006_; lean_object* v_time_2007_; 
v_date_2005_ = lean_ctor_get(v_zdt_2004_, 1);
v___x_2006_ = lean_thunk_get_own(v_date_2005_);
v_time_2007_ = lean_ctor_get(v___x_2006_, 1);
lean_inc_ref(v_time_2007_);
lean_dec(v___x_2006_);
return v_time_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___redArg___boxed(lean_object* v_zdt_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Std_Time_DateTime_time___redArg(v_zdt_2008_);
lean_dec_ref(v_zdt_2008_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object* v_tz_2010_, lean_object* v_zdt_2011_){
_start:
{
lean_object* v_date_2012_; lean_object* v___x_2013_; lean_object* v_time_2014_; 
v_date_2012_ = lean_ctor_get(v_zdt_2011_, 1);
v___x_2013_ = lean_thunk_get_own(v_date_2012_);
v_time_2014_ = lean_ctor_get(v___x_2013_, 1);
lean_inc_ref(v_time_2014_);
lean_dec(v___x_2013_);
return v_time_2014_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object* v_tz_2015_, lean_object* v_zdt_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Std_Time_DateTime_time(v_tz_2015_, v_zdt_2016_);
lean_dec_ref(v_zdt_2016_);
lean_dec_ref(v_tz_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay(lean_object* v_days_2018_, lean_object* v_time_2019_, lean_object* v_tz_2020_){
_start:
{
lean_object* v_offset_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v_second_2025_; lean_object* v_nano_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2044_; 
v_offset_2021_ = lean_ctor_get(v_tz_2020_, 0);
v___x_2022_ = l_Std_Time_PlainDate_ofEpochDay(v_days_2018_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2022_);
lean_ctor_set(v___x_2023_, 1, v_time_2019_);
lean_inc_ref(v___x_2023_);
v___x_2024_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2023_);
v_second_2025_ = lean_ctor_get(v___x_2024_, 0);
v_nano_2026_ = lean_ctor_get(v___x_2024_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2028_ = v___x_2024_;
v_isShared_2029_ = v_isSharedCheck_2044_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_nano_2026_);
lean_inc(v_second_2025_);
lean_dec(v___x_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2044_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___f_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v_tm_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___f_2030_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2030_, 0, v___x_2023_);
v___x_2031_ = lean_int_neg(v_offset_2021_);
v___x_2032_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_2033_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_2034_ = lean_int_mul(v_second_2025_, v___x_2033_);
lean_dec(v_second_2025_);
v___x_2035_ = lean_int_add(v___x_2034_, v_nano_2026_);
lean_dec(v_nano_2026_);
lean_dec(v___x_2034_);
v___x_2036_ = lean_int_mul(v___x_2031_, v___x_2033_);
lean_dec(v___x_2031_);
v___x_2037_ = lean_int_add(v___x_2036_, v___x_2032_);
lean_dec(v___x_2036_);
v___x_2038_ = lean_int_add(v___x_2035_, v___x_2037_);
lean_dec(v___x_2037_);
lean_dec(v___x_2035_);
v_tm_2039_ = l_Std_Time_Duration_ofNanoseconds(v___x_2038_);
lean_dec(v___x_2038_);
v___x_2040_ = lean_mk_thunk(v___f_2030_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 1, v___x_2040_);
lean_ctor_set(v___x_2028_, 0, v_tm_2039_);
v___x_2042_ = v___x_2028_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_tm_2039_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay___boxed(lean_object* v_days_2045_, lean_object* v_time_2046_, lean_object* v_tz_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Std_Time_DateTime_ofEpochDay(v_days_2045_, v_time_2046_, v_tz_2047_);
lean_dec_ref(v_tz_2047_);
lean_dec(v_days_2045_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset(lean_object* v_tz_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___boxed), 3, 1);
lean_closure_set(v___x_2050_, 0, v_tz_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset(lean_object* v_tz_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subDays___boxed), 3, 1);
lean_closure_set(v___x_2052_, 0, v_tz_2051_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__1(lean_object* v_tz_2053_){
_start:
{
lean_object* v___x_2054_; 
v___x_2054_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addWeeks___boxed), 3, 1);
lean_closure_set(v___x_2054_, 0, v_tz_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__1(lean_object* v_tz_2055_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subWeeks___boxed), 3, 1);
lean_closure_set(v___x_2056_, 0, v_tz_2055_);
return v___x_2056_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__2(lean_object* v_tz_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addHours___boxed), 3, 1);
lean_closure_set(v___x_2058_, 0, v_tz_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__2(lean_object* v_tz_2059_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subHours___boxed), 3, 1);
lean_closure_set(v___x_2060_, 0, v_tz_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__3(lean_object* v_tz_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMinutes___boxed), 3, 1);
lean_closure_set(v___x_2062_, 0, v_tz_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__3(lean_object* v_tz_2063_){
_start:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subMinutes___boxed), 3, 1);
lean_closure_set(v___x_2064_, 0, v_tz_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__4(lean_object* v_tz_2065_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addSeconds___boxed), 3, 1);
lean_closure_set(v___x_2066_, 0, v_tz_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__4(lean_object* v_tz_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subSeconds___boxed), 3, 1);
lean_closure_set(v___x_2068_, 0, v_tz_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__5(lean_object* v_tz_2069_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___boxed), 3, 1);
lean_closure_set(v___x_2070_, 0, v_tz_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__5(lean_object* v_tz_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subMilliseconds___boxed), 3, 1);
lean_closure_set(v___x_2072_, 0, v_tz_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddOffset__6(lean_object* v_tz_2073_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addNanoseconds___boxed), 3, 1);
lean_closure_set(v___x_2074_, 0, v_tz_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubOffset__6(lean_object* v_tz_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_subNanoseconds___boxed), 3, 1);
lean_closure_set(v___x_2076_, 0, v_tz_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object* v_x_2077_, lean_object* v_y_2078_){
_start:
{
lean_object* v_timestamp_2079_; lean_object* v_timestamp_2080_; lean_object* v_second_2081_; lean_object* v_nano_2082_; lean_object* v_second_2083_; lean_object* v_nano_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v_timestamp_2079_ = lean_ctor_get(v_y_2078_, 0);
v_timestamp_2080_ = lean_ctor_get(v_x_2077_, 0);
v_second_2081_ = lean_ctor_get(v_timestamp_2079_, 0);
v_nano_2082_ = lean_ctor_get(v_timestamp_2079_, 1);
v_second_2083_ = lean_ctor_get(v_timestamp_2080_, 0);
v_nano_2084_ = lean_ctor_get(v_timestamp_2080_, 1);
v___x_2085_ = lean_int_neg(v_second_2081_);
v___x_2086_ = lean_int_neg(v_nano_2082_);
v___x_2087_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_2088_ = lean_int_mul(v_second_2083_, v___x_2087_);
v___x_2089_ = lean_int_add(v___x_2088_, v_nano_2084_);
lean_dec(v___x_2088_);
v___x_2090_ = lean_int_mul(v___x_2085_, v___x_2087_);
lean_dec(v___x_2085_);
v___x_2091_ = lean_int_add(v___x_2090_, v___x_2086_);
lean_dec(v___x_2086_);
lean_dec(v___x_2090_);
v___x_2092_ = lean_int_add(v___x_2089_, v___x_2091_);
lean_dec(v___x_2091_);
lean_dec(v___x_2089_);
v___x_2093_ = l_Std_Time_Duration_ofNanoseconds(v___x_2092_);
lean_dec(v___x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object* v_x_2094_, lean_object* v_y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Std_Time_DateTime_instHSubDuration___lam__0(v_x_2094_, v_y_2095_);
lean_dec_ref(v_y_2095_);
lean_dec_ref(v_x_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration(lean_object* v_tz_2098_, lean_object* v_tz_u2081_2099_){
_start:
{
lean_object* v___f_2100_; 
v___f_2100_ = ((lean_object*)(l_Std_Time_DateTime_instHSubDuration___closed__0));
return v___f_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___boxed(lean_object* v_tz_2101_, lean_object* v_tz_u2081_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Std_Time_DateTime_instHSubDuration(v_tz_2101_, v_tz_u2081_2102_);
lean_dec_ref(v_tz_u2081_2102_);
lean_dec_ref(v_tz_2101_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1(lean_object* v_tz_2104_, lean_object* v_x_2105_, lean_object* v_y_2106_){
_start:
{
lean_object* v_timestamp_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2132_; 
v_timestamp_2107_ = lean_ctor_get(v_x_2105_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_x_2105_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v_x_2105_, 1);
lean_dec(v_unused_2133_);
v___x_2109_ = v_x_2105_;
v_isShared_2110_ = v_isSharedCheck_2132_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_timestamp_2107_);
lean_dec(v_x_2105_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2132_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v_second_2111_; lean_object* v_nano_2112_; lean_object* v_second_2113_; lean_object* v_nano_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v_nanos_2117_; lean_object* v___x_2118_; lean_object* v_second_2119_; lean_object* v_nano_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v_second_2111_ = lean_ctor_get(v_y_2106_, 0);
v_nano_2112_ = lean_ctor_get(v_y_2106_, 1);
v_second_2113_ = lean_ctor_get(v_timestamp_2107_, 0);
lean_inc(v_second_2113_);
v_nano_2114_ = lean_ctor_get(v_timestamp_2107_, 1);
lean_inc(v_nano_2114_);
lean_dec_ref(v_timestamp_2107_);
v___x_2115_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_2116_ = lean_int_mul(v_second_2111_, v___x_2115_);
v_nanos_2117_ = lean_int_add(v___x_2116_, v_nano_2112_);
lean_dec(v___x_2116_);
v___x_2118_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_2117_);
lean_dec(v_nanos_2117_);
v_second_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_second_2119_);
v_nano_2120_ = lean_ctor_get(v___x_2118_, 1);
lean_inc(v_nano_2120_);
lean_dec_ref(v___x_2118_);
v___x_2121_ = lean_int_mul(v_second_2113_, v___x_2115_);
lean_dec(v_second_2113_);
v___x_2122_ = lean_int_add(v___x_2121_, v_nano_2114_);
lean_dec(v_nano_2114_);
lean_dec(v___x_2121_);
v___x_2123_ = lean_int_mul(v_second_2119_, v___x_2115_);
lean_dec(v_second_2119_);
v___x_2124_ = lean_int_add(v___x_2123_, v_nano_2120_);
lean_dec(v_nano_2120_);
lean_dec(v___x_2123_);
v___x_2125_ = lean_int_add(v___x_2122_, v___x_2124_);
lean_dec(v___x_2124_);
lean_dec(v___x_2122_);
v___x_2126_ = l_Std_Time_Duration_ofNanoseconds(v___x_2125_);
lean_dec(v___x_2125_);
lean_inc_ref(v___x_2126_);
v___f_2127_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2127_, 0, v_tz_2104_);
lean_closure_set(v___f_2127_, 1, v___x_2126_);
lean_closure_set(v___f_2127_, 2, v___x_2115_);
v___x_2128_ = lean_mk_thunk(v___f_2127_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 1, v___x_2128_);
lean_ctor_set(v___x_2109_, 0, v___x_2126_);
v___x_2130_ = v___x_2109_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2131_, 1, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__1___boxed(lean_object* v_tz_2134_, lean_object* v_x_2135_, lean_object* v_y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Std_Time_DateTime_instHAddDuration___lam__1(v_tz_2134_, v_x_2135_, v_y_2136_);
lean_dec_ref(v_y_2136_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration(lean_object* v_tz_2138_){
_start:
{
lean_object* v___f_2139_; 
v___f_2139_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHAddDuration___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2139_, 0, v_tz_2138_);
return v___f_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1(lean_object* v_tz_2140_, lean_object* v_x_2141_, lean_object* v_y_2142_){
_start:
{
lean_object* v_second_2143_; lean_object* v_nano_2144_; lean_object* v_timestamp_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2170_; 
v_second_2143_ = lean_ctor_get(v_y_2142_, 0);
v_nano_2144_ = lean_ctor_get(v_y_2142_, 1);
v_timestamp_2145_ = lean_ctor_get(v_x_2141_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_x_2141_);
if (v_isSharedCheck_2170_ == 0)
{
lean_object* v_unused_2171_; 
v_unused_2171_ = lean_ctor_get(v_x_2141_, 1);
lean_dec(v_unused_2171_);
v___x_2147_ = v_x_2141_;
v_isShared_2148_ = v_isSharedCheck_2170_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_timestamp_2145_);
lean_dec(v_x_2141_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2170_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v_nanos_2151_; lean_object* v___x_2152_; lean_object* v_second_2153_; lean_object* v_nano_2154_; lean_object* v_second_2155_; lean_object* v_nano_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___f_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2149_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_2150_ = lean_int_mul(v_second_2143_, v___x_2149_);
v_nanos_2151_ = lean_int_add(v___x_2150_, v_nano_2144_);
lean_dec(v___x_2150_);
v___x_2152_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_2151_);
lean_dec(v_nanos_2151_);
v_second_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_second_2153_);
v_nano_2154_ = lean_ctor_get(v___x_2152_, 1);
lean_inc(v_nano_2154_);
lean_dec_ref(v___x_2152_);
v_second_2155_ = lean_ctor_get(v_timestamp_2145_, 0);
lean_inc(v_second_2155_);
v_nano_2156_ = lean_ctor_get(v_timestamp_2145_, 1);
lean_inc(v_nano_2156_);
lean_dec_ref(v_timestamp_2145_);
v___x_2157_ = lean_int_neg(v_second_2153_);
lean_dec(v_second_2153_);
v___x_2158_ = lean_int_neg(v_nano_2154_);
lean_dec(v_nano_2154_);
v___x_2159_ = lean_int_mul(v_second_2155_, v___x_2149_);
lean_dec(v_second_2155_);
v___x_2160_ = lean_int_add(v___x_2159_, v_nano_2156_);
lean_dec(v_nano_2156_);
lean_dec(v___x_2159_);
v___x_2161_ = lean_int_mul(v___x_2157_, v___x_2149_);
lean_dec(v___x_2157_);
v___x_2162_ = lean_int_add(v___x_2161_, v___x_2158_);
lean_dec(v___x_2158_);
lean_dec(v___x_2161_);
v___x_2163_ = lean_int_add(v___x_2160_, v___x_2162_);
lean_dec(v___x_2162_);
lean_dec(v___x_2160_);
v___x_2164_ = l_Std_Time_Duration_ofNanoseconds(v___x_2163_);
lean_dec(v___x_2163_);
lean_inc_ref(v___x_2164_);
v___f_2165_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2165_, 0, v_tz_2140_);
lean_closure_set(v___f_2165_, 1, v___x_2164_);
lean_closure_set(v___f_2165_, 2, v___x_2149_);
v___x_2166_ = lean_mk_thunk(v___f_2165_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 1, v___x_2166_);
lean_ctor_set(v___x_2147_, 0, v___x_2164_);
v___x_2168_ = v___x_2147_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed(lean_object* v_tz_2172_, lean_object* v_x_2173_, lean_object* v_y_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Std_Time_DateTime_instHSubDuration__1___lam__1(v_tz_2172_, v_x_2173_, v_y_2174_);
lean_dec_ref(v_y_2174_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1(lean_object* v_tz_2176_){
_start:
{
lean_object* v___f_2177_; 
v___f_2177_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2177_, 0, v_tz_2176_);
return v___f_2177_;
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

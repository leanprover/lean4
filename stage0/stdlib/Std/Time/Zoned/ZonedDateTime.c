// Lean compiler output
// Module: Std.Time.Zoned.ZonedDateTime
// Imports: public import Std.Time.Zoned.DateTime public import Std.Time.Zoned.ZoneRules import all Std.Time.DateTime.PlainDateTime
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
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t);
extern lean_object* l_Std_Time_instInhabitedTimeZone_default;
extern lean_object* l_Std_Time_TimeZone_instInhabitedZoneRules_default;
extern lean_object* l_Std_Time_instInhabitedTimestamp_default;
extern lean_object* l_Std_Time_instInhabitedPlainDateTime_default;
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0 = (const lean_object*)&l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value;
static lean_once_cell_t l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1;
static lean_once_cell_t l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedZonedDateTime;
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0;
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDateTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_time(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_time___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_year(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_year___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_month(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_month___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_day(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_day___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_hour(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_hour___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_minute(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_minute___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_second(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_second___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_millisecond___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_millisecond___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_weekday(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekday___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_dayOfYear___closed__0;
static lean_once_cell_t l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_dayOfYear___closed__1;
static lean_once_cell_t l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_dayOfYear___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekYear(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_addDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_addDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subDays___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_addWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_addWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsRollOver___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsRollOver___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_addHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_addHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subHours___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_addMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_addMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_era___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMonthClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMonthRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withYearClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withYearRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withSeconds(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_withMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_inLeapYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_inLeapYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toEpochDay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toEpochDay___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofEpochDay(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofEpochDay___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_addDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_subDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_addWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__1 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_subWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__1 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_addHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__2 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_subHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__2 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_addMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__3 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_subMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__3 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_addSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__4 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_subSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__4 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_addMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__5 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_subMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__5 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_addNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHAddOffset__6 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddOffset__6___closed__0_value;
static const lean_closure_object l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_subNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHSubOffset__6 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubOffset__6___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHSubDuration = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHAddDuration___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHAddDuration = (const lean_object*)&l_Std_Time_ZonedDateTime_instHAddDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1 = (const lean_object*)&l_Std_Time_ZonedDateTime_instHSubDuration__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Std_Time_instInhabitedPlainDateTime_default;
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1(void){
_start:
{
lean_object* v___f_4_; lean_object* v___x_5_; 
v___f_4_ = ((lean_object*)(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0));
v___x_5_ = lean_mk_thunk(v___f_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_6_ = l_Std_Time_instInhabitedTimeZone_default;
v___x_7_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
v___x_8_ = l_Std_Time_instInhabitedTimestamp_default;
v___x_9_ = lean_obj_once(&l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1, &l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once, _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1);
v___x_10_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_7_);
lean_ctor_set(v___x_10_, 3, v___x_6_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedZonedDateTime___private__1(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2, &l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once, _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2);
return v___x_11_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedZonedDateTime(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2, &l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once, _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2);
return v___x_12_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_nat_to_int(v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(1000000000u);
v___x_16_ = lean_nat_to_int(v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(lean_object* v___y_17_, lean_object* v_tm_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_offset_20_; lean_object* v_second_21_; lean_object* v_nano_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_offset_20_ = lean_ctor_get(v___y_17_, 0);
v_second_21_ = lean_ctor_get(v_tm_18_, 0);
v_nano_22_ = lean_ctor_get(v_tm_18_, 1);
v___x_23_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_24_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_25_ = lean_int_mul(v_second_21_, v___x_24_);
v___x_26_ = lean_int_add(v___x_25_, v_nano_22_);
lean_dec(v___x_25_);
v___x_27_ = lean_int_mul(v_offset_20_, v___x_24_);
v___x_28_ = lean_int_add(v___x_27_, v___x_23_);
lean_dec(v___x_27_);
v___x_29_ = lean_int_add(v___x_26_, v___x_28_);
lean_dec(v___x_28_);
lean_dec(v___x_26_);
v___x_30_ = l_Std_Time_Duration_ofNanoseconds(v___x_29_);
lean_dec(v___x_29_);
v___x_31_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed(lean_object* v___y_32_, lean_object* v_tm_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(v___y_32_, v_tm_33_, v_x_34_);
lean_dec_ref(v_tm_33_);
lean_dec_ref(v___y_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp(lean_object* v_tm_36_, lean_object* v_rules_37_){
_start:
{
lean_object* v___y_39_; lean_object* v_initialLocalTimeType_43_; lean_object* v_transitions_44_; lean_object* v___x_45_; 
v_initialLocalTimeType_43_ = lean_ctor_get(v_rules_37_, 0);
v_transitions_44_ = lean_ctor_get(v_rules_37_, 1);
v___x_45_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_44_, v_tm_36_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v___x_46_; 
lean_dec_ref_known(v___x_45_, 1);
v___x_46_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_43_);
v___y_39_ = v___x_46_;
goto v___jp_38_;
}
else
{
lean_object* v_a_47_; 
v_a_47_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_45_, 1);
v___y_39_ = v_a_47_;
goto v___jp_38_;
}
v___jp_38_:
{
lean_object* v___f_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
lean_inc_ref(v_tm_36_);
lean_inc_ref(v___y_39_);
v___f_40_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_40_, 0, v___y_39_);
lean_closure_set(v___f_40_, 1, v_tm_36_);
v___x_41_ = lean_mk_thunk(v___f_40_);
v___x_42_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v_tm_36_);
lean_ctor_set(v___x_42_, 2, v_rules_37_);
lean_ctor_set(v___x_42_, 3, v___y_39_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(lean_object* v_pdt_48_, lean_object* v_x_49_){
_start:
{
lean_inc_ref(v_pdt_48_);
return v_pdt_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed(lean_object* v_pdt_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(v_pdt_50_, v_x_51_);
lean_dec_ref(v_pdt_50_);
return v_res_52_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_54_ = lean_int_neg(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime(lean_object* v_pdt_55_, lean_object* v_zr_56_){
_start:
{
lean_object* v_wt_57_; lean_object* v_ltt_58_; lean_object* v_tz_59_; lean_object* v_offset_60_; lean_object* v_second_61_; lean_object* v_nano_62_; lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_inc_ref(v_pdt_55_);
v_wt_57_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_55_);
lean_inc_ref(v_zr_56_);
v_ltt_58_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_56_, v_wt_57_);
v_tz_59_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_58_);
lean_dec_ref(v_ltt_58_);
v_offset_60_ = lean_ctor_get(v_tz_59_, 0);
lean_inc(v_offset_60_);
v_second_61_ = lean_ctor_get(v_wt_57_, 0);
lean_inc(v_second_61_);
v_nano_62_ = lean_ctor_get(v_wt_57_, 1);
lean_inc(v_nano_62_);
lean_dec_ref(v_wt_57_);
v___f_63_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 2, 1);
lean_closure_set(v___f_63_, 0, v_pdt_55_);
v___x_64_ = lean_mk_thunk(v___f_63_);
v___x_65_ = lean_int_neg(v_offset_60_);
lean_dec(v_offset_60_);
v___x_66_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_67_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_68_ = lean_int_mul(v_second_61_, v___x_67_);
lean_dec(v_second_61_);
v___x_69_ = lean_int_add(v___x_68_, v_nano_62_);
lean_dec(v_nano_62_);
lean_dec(v___x_68_);
v___x_70_ = lean_int_mul(v___x_65_, v___x_67_);
lean_dec(v___x_65_);
v___x_71_ = lean_int_add(v___x_70_, v___x_66_);
lean_dec(v___x_70_);
v___x_72_ = lean_int_add(v___x_69_, v___x_71_);
lean_dec(v___x_71_);
lean_dec(v___x_69_);
v___x_73_ = l_Std_Time_Duration_ofNanoseconds(v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_74_, 0, v___x_64_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
lean_ctor_set(v___x_74_, 2, v_zr_56_);
lean_ctor_set(v___x_74_, 3, v_tz_59_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0(lean_object* v___y_75_, lean_object* v_tm_76_, lean_object* v___x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_offset_79_; lean_object* v_second_80_; lean_object* v_nano_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_offset_79_ = lean_ctor_get(v___y_75_, 0);
v_second_80_ = lean_ctor_get(v_tm_76_, 0);
v_nano_81_ = lean_ctor_get(v_tm_76_, 1);
v___x_82_ = lean_nat_to_int(v___x_77_);
v___x_83_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_84_ = lean_int_mul(v_second_80_, v___x_83_);
v___x_85_ = lean_int_add(v___x_84_, v_nano_81_);
lean_dec(v___x_84_);
v___x_86_ = lean_int_mul(v_offset_79_, v___x_83_);
v___x_87_ = lean_int_add(v___x_86_, v___x_82_);
lean_dec(v___x_82_);
lean_dec(v___x_86_);
v___x_88_ = lean_int_add(v___x_85_, v___x_87_);
lean_dec(v___x_87_);
lean_dec(v___x_85_);
v___x_89_ = l_Std_Time_Duration_ofNanoseconds(v___x_88_);
lean_dec(v___x_88_);
v___x_90_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0___boxed(lean_object* v___y_91_, lean_object* v_tm_92_, lean_object* v___x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0(v___y_91_, v_tm_92_, v___x_93_, v_x_94_);
lean_dec_ref(v_tm_92_);
lean_dec_ref(v___y_91_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone(lean_object* v_tm_98_, lean_object* v_tz_99_){
_start:
{
lean_object* v_offset_100_; lean_object* v_name_101_; lean_object* v_abbreviation_102_; uint8_t v_isDST_103_; uint8_t v___x_104_; uint8_t v___x_105_; lean_object* v_ltt_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___y_111_; lean_object* v___x_115_; 
v_offset_100_ = lean_ctor_get(v_tz_99_, 0);
v_name_101_ = lean_ctor_get(v_tz_99_, 1);
v_abbreviation_102_ = lean_ctor_get(v_tz_99_, 2);
v_isDST_103_ = lean_ctor_get_uint8(v_tz_99_, sizeof(void*)*3);
v___x_104_ = 0;
v___x_105_ = 1;
lean_inc_ref(v_name_101_);
lean_inc_ref(v_abbreviation_102_);
lean_inc(v_offset_100_);
v_ltt_106_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_106_, 0, v_offset_100_);
lean_ctor_set(v_ltt_106_, 1, v_abbreviation_102_);
lean_ctor_set(v_ltt_106_, 2, v_name_101_);
lean_ctor_set_uint8(v_ltt_106_, sizeof(void*)*3, v_isDST_103_);
lean_ctor_set_uint8(v_ltt_106_, sizeof(void*)*3 + 1, v___x_104_);
lean_ctor_set_uint8(v_ltt_106_, sizeof(void*)*3 + 2, v___x_105_);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
lean_inc_ref(v_ltt_106_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_ltt_106_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_115_ = l_Std_Time_TimeZone_Transition_timezoneAt(v___x_108_, v_tm_98_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v___x_116_; 
lean_dec_ref_known(v___x_115_, 1);
v___x_116_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_106_);
lean_dec_ref_known(v_ltt_106_, 3);
v___y_111_ = v___x_116_;
goto v___jp_110_;
}
else
{
lean_object* v_a_117_; 
lean_dec_ref_known(v_ltt_106_, 3);
v_a_117_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_115_, 1);
v___y_111_ = v_a_117_;
goto v___jp_110_;
}
v___jp_110_:
{
lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
lean_inc_ref(v_tm_98_);
lean_inc_ref(v___y_111_);
v___f_112_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___lam__0___boxed), 4, 3);
lean_closure_set(v___f_112_, 0, v___y_111_);
lean_closure_set(v___f_112_, 1, v_tm_98_);
lean_closure_set(v___f_112_, 2, v___x_107_);
v___x_113_ = lean_mk_thunk(v___f_112_);
v___x_114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_tm_98_);
lean_ctor_set(v___x_114_, 2, v___x_109_);
lean_ctor_set(v___x_114_, 3, v___y_111_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___boxed(lean_object* v_tm_118_, lean_object* v_tz_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone(v_tm_118_, v_tz_119_);
lean_dec_ref(v_tz_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0(lean_object* v_tm_121_, lean_object* v_x_122_){
_start:
{
lean_inc_ref(v_tm_121_);
return v_tm_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0___boxed(lean_object* v_tm_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0(v_tm_123_, v_x_124_);
lean_dec_ref(v_tm_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(lean_object* v_tm_126_, lean_object* v_tz_127_){
_start:
{
lean_object* v_offset_128_; lean_object* v_name_129_; lean_object* v_abbreviation_130_; uint8_t v_isDST_131_; uint8_t v___x_132_; uint8_t v___x_133_; lean_object* v_ltt_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v_wt_137_; lean_object* v_ltt_138_; lean_object* v_tz_139_; lean_object* v_offset_140_; lean_object* v_second_141_; lean_object* v_nano_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_offset_128_ = lean_ctor_get(v_tz_127_, 0);
v_name_129_ = lean_ctor_get(v_tz_127_, 1);
v_abbreviation_130_ = lean_ctor_get(v_tz_127_, 2);
v_isDST_131_ = lean_ctor_get_uint8(v_tz_127_, sizeof(void*)*3);
v___x_132_ = 0;
v___x_133_ = 1;
lean_inc_ref(v_name_129_);
lean_inc_ref(v_abbreviation_130_);
lean_inc(v_offset_128_);
v_ltt_134_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_134_, 0, v_offset_128_);
lean_ctor_set(v_ltt_134_, 1, v_abbreviation_130_);
lean_ctor_set(v_ltt_134_, 2, v_name_129_);
lean_ctor_set_uint8(v_ltt_134_, sizeof(void*)*3, v_isDST_131_);
lean_ctor_set_uint8(v_ltt_134_, sizeof(void*)*3 + 1, v___x_132_);
lean_ctor_set_uint8(v_ltt_134_, sizeof(void*)*3 + 2, v___x_133_);
v___x_135_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v_ltt_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
lean_inc_ref(v_tm_126_);
v_wt_137_ = l_Std_Time_PlainDateTime_toWallTime(v_tm_126_);
lean_inc_ref(v___x_136_);
v_ltt_138_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_136_, v_wt_137_);
v_tz_139_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_138_);
lean_dec_ref(v_ltt_138_);
v_offset_140_ = lean_ctor_get(v_tz_139_, 0);
lean_inc(v_offset_140_);
v_second_141_ = lean_ctor_get(v_wt_137_, 0);
lean_inc(v_second_141_);
v_nano_142_ = lean_ctor_get(v_wt_137_, 1);
lean_inc(v_nano_142_);
lean_dec_ref(v_wt_137_);
v___f_143_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___lam__0___boxed), 2, 1);
lean_closure_set(v___f_143_, 0, v_tm_126_);
v___x_144_ = lean_mk_thunk(v___f_143_);
v___x_145_ = lean_int_neg(v_offset_140_);
lean_dec(v_offset_140_);
v___x_146_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_147_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_148_ = lean_int_mul(v_second_141_, v___x_147_);
lean_dec(v_second_141_);
v___x_149_ = lean_int_add(v___x_148_, v_nano_142_);
lean_dec(v_nano_142_);
lean_dec(v___x_148_);
v___x_150_ = lean_int_mul(v___x_145_, v___x_147_);
lean_dec(v___x_145_);
v___x_151_ = lean_int_add(v___x_150_, v___x_146_);
lean_dec(v___x_150_);
v___x_152_ = lean_int_add(v___x_149_, v___x_151_);
lean_dec(v___x_151_);
lean_dec(v___x_149_);
v___x_153_ = l_Std_Time_Duration_ofNanoseconds(v___x_152_);
lean_dec(v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_154_, 0, v___x_144_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
lean_ctor_set(v___x_154_, 2, v___x_136_);
lean_ctor_set(v___x_154_, 3, v_tz_139_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___boxed(lean_object* v_tm_155_, lean_object* v_tz_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(v_tm_155_, v_tz_156_);
lean_dec_ref(v_tz_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp(lean_object* v_date_158_){
_start:
{
lean_object* v_timestamp_159_; 
v_timestamp_159_ = lean_ctor_get(v_date_158_, 1);
lean_inc_ref(v_timestamp_159_);
return v_timestamp_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp___boxed(lean_object* v_date_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Time_ZonedDateTime_toTimestamp(v_date_160_);
lean_dec_ref(v_date_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(lean_object* v___y_162_, lean_object* v_timestamp_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_offset_165_; lean_object* v_second_166_; lean_object* v_nano_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_offset_165_ = lean_ctor_get(v___y_162_, 0);
v_second_166_ = lean_ctor_get(v_timestamp_163_, 0);
v_nano_167_ = lean_ctor_get(v_timestamp_163_, 1);
v___x_168_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_169_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_170_ = lean_int_mul(v_second_166_, v___x_169_);
v___x_171_ = lean_int_add(v___x_170_, v_nano_167_);
lean_dec(v___x_170_);
v___x_172_ = lean_int_mul(v_offset_165_, v___x_169_);
v___x_173_ = lean_int_add(v___x_172_, v___x_168_);
lean_dec(v___x_172_);
v___x_174_ = lean_int_add(v___x_171_, v___x_173_);
lean_dec(v___x_173_);
lean_dec(v___x_171_);
v___x_175_ = l_Std_Time_Duration_ofNanoseconds(v___x_174_);
lean_dec(v___x_174_);
v___x_176_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed(lean_object* v___y_177_, lean_object* v_timestamp_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(v___y_177_, v_timestamp_178_, v_x_179_);
lean_dec_ref(v_timestamp_178_);
lean_dec_ref(v___y_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules(lean_object* v_date_181_, lean_object* v_tz_u2081_182_){
_start:
{
lean_object* v_timestamp_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_199_; 
v_timestamp_183_ = lean_ctor_get(v_date_181_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_date_181_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; lean_object* v_unused_201_; lean_object* v_unused_202_; 
v_unused_200_ = lean_ctor_get(v_date_181_, 3);
lean_dec(v_unused_200_);
v_unused_201_ = lean_ctor_get(v_date_181_, 2);
lean_dec(v_unused_201_);
v_unused_202_ = lean_ctor_get(v_date_181_, 0);
lean_dec(v_unused_202_);
v___x_185_ = v_date_181_;
v_isShared_186_ = v_isSharedCheck_199_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_timestamp_183_);
lean_dec(v_date_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_199_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___y_188_; lean_object* v_initialLocalTimeType_194_; lean_object* v_transitions_195_; lean_object* v___x_196_; 
v_initialLocalTimeType_194_ = lean_ctor_get(v_tz_u2081_182_, 0);
v_transitions_195_ = lean_ctor_get(v_tz_u2081_182_, 1);
v___x_196_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_195_, v_timestamp_183_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v___x_197_; 
lean_dec_ref_known(v___x_196_, 1);
v___x_197_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_194_);
v___y_188_ = v___x_197_;
goto v___jp_187_;
}
else
{
lean_object* v_a_198_; 
v_a_198_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_198_);
lean_dec_ref_known(v___x_196_, 1);
v___y_188_ = v_a_198_;
goto v___jp_187_;
}
v___jp_187_:
{
lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
lean_inc_ref(v_timestamp_183_);
lean_inc_ref(v___y_188_);
v___f_189_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed), 3, 2);
lean_closure_set(v___f_189_, 0, v___y_188_);
lean_closure_set(v___f_189_, 1, v_timestamp_183_);
v___x_190_ = lean_mk_thunk(v___f_189_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 3, v___y_188_);
lean_ctor_set(v___x_185_, 2, v_tz_u2081_182_);
lean_ctor_set(v___x_185_, 0, v___x_190_);
v___x_192_ = v___x_185_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_timestamp_183_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_tz_u2081_182_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v___y_188_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDateTime(lean_object* v_dt_203_){
_start:
{
lean_object* v_date_204_; lean_object* v___x_205_; 
v_date_204_ = lean_ctor_get(v_dt_203_, 0);
v___x_205_ = lean_thunk_get_own(v_date_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDateTime___boxed(lean_object* v_dt_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Time_ZonedDateTime_toPlainDateTime(v_dt_206_);
lean_dec_ref(v_dt_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime___lam__0(lean_object* v_timezone_208_, lean_object* v_timestamp_209_, lean_object* v_x_210_){
_start:
{
lean_object* v_offset_211_; lean_object* v_second_212_; lean_object* v_nano_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_offset_211_ = lean_ctor_get(v_timezone_208_, 0);
v_second_212_ = lean_ctor_get(v_timestamp_209_, 0);
v_nano_213_ = lean_ctor_get(v_timestamp_209_, 1);
v___x_214_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_215_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_216_ = lean_int_mul(v_second_212_, v___x_215_);
v___x_217_ = lean_int_add(v___x_216_, v_nano_213_);
lean_dec(v___x_216_);
v___x_218_ = lean_int_mul(v_offset_211_, v___x_215_);
v___x_219_ = lean_int_add(v___x_218_, v___x_214_);
lean_dec(v___x_218_);
v___x_220_ = lean_int_add(v___x_217_, v___x_219_);
lean_dec(v___x_219_);
lean_dec(v___x_217_);
v___x_221_ = l_Std_Time_Duration_ofNanoseconds(v___x_220_);
lean_dec(v___x_220_);
v___x_222_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed(lean_object* v_timezone_223_, lean_object* v_timestamp_224_, lean_object* v_x_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_Time_ZonedDateTime_toDateTime___lam__0(v_timezone_223_, v_timestamp_224_, v_x_225_);
lean_dec_ref(v_timestamp_224_);
lean_dec_ref(v_timezone_223_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime(lean_object* v_dt_227_){
_start:
{
lean_object* v_timestamp_228_; lean_object* v_timezone_229_; lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_timestamp_228_ = lean_ctor_get(v_dt_227_, 1);
lean_inc_ref_n(v_timestamp_228_, 2);
v_timezone_229_ = lean_ctor_get(v_dt_227_, 3);
lean_inc_ref(v_timezone_229_);
lean_dec_ref(v_dt_227_);
v___f_230_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed), 3, 2);
lean_closure_set(v___f_230_, 0, v_timezone_229_);
lean_closure_set(v___f_230_, 1, v_timestamp_228_);
v___x_231_ = lean_mk_thunk(v___f_230_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_timestamp_228_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_time(lean_object* v_zdt_233_){
_start:
{
lean_object* v_date_234_; lean_object* v___x_235_; lean_object* v_time_236_; 
v_date_234_ = lean_ctor_get(v_zdt_233_, 0);
v___x_235_ = lean_thunk_get_own(v_date_234_);
v_time_236_ = lean_ctor_get(v___x_235_, 1);
lean_inc_ref(v_time_236_);
lean_dec(v___x_235_);
return v_time_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_time___boxed(lean_object* v_zdt_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_Time_ZonedDateTime_time(v_zdt_237_);
lean_dec_ref(v_zdt_237_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_year(lean_object* v_zdt_239_){
_start:
{
lean_object* v_date_240_; lean_object* v___x_241_; lean_object* v_date_242_; lean_object* v_year_243_; 
v_date_240_ = lean_ctor_get(v_zdt_239_, 0);
v___x_241_ = lean_thunk_get_own(v_date_240_);
v_date_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc_ref(v_date_242_);
lean_dec(v___x_241_);
v_year_243_ = lean_ctor_get(v_date_242_, 0);
lean_inc(v_year_243_);
lean_dec_ref(v_date_242_);
return v_year_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_year___boxed(lean_object* v_zdt_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Time_ZonedDateTime_year(v_zdt_244_);
lean_dec_ref(v_zdt_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_month(lean_object* v_zdt_246_){
_start:
{
lean_object* v_date_247_; lean_object* v___x_248_; lean_object* v_date_249_; lean_object* v_month_250_; 
v_date_247_ = lean_ctor_get(v_zdt_246_, 0);
v___x_248_ = lean_thunk_get_own(v_date_247_);
v_date_249_ = lean_ctor_get(v___x_248_, 0);
lean_inc_ref(v_date_249_);
lean_dec(v___x_248_);
v_month_250_ = lean_ctor_get(v_date_249_, 1);
lean_inc(v_month_250_);
lean_dec_ref(v_date_249_);
return v_month_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_month___boxed(lean_object* v_zdt_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Time_ZonedDateTime_month(v_zdt_251_);
lean_dec_ref(v_zdt_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_day(lean_object* v_zdt_253_){
_start:
{
lean_object* v_date_254_; lean_object* v___x_255_; lean_object* v_date_256_; lean_object* v_day_257_; 
v_date_254_ = lean_ctor_get(v_zdt_253_, 0);
v___x_255_ = lean_thunk_get_own(v_date_254_);
v_date_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc_ref(v_date_256_);
lean_dec(v___x_255_);
v_day_257_ = lean_ctor_get(v_date_256_, 2);
lean_inc(v_day_257_);
lean_dec_ref(v_date_256_);
return v_day_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_day___boxed(lean_object* v_zdt_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Time_ZonedDateTime_day(v_zdt_258_);
lean_dec_ref(v_zdt_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_hour(lean_object* v_zdt_260_){
_start:
{
lean_object* v_date_261_; lean_object* v___x_262_; lean_object* v_time_263_; lean_object* v_hour_264_; 
v_date_261_ = lean_ctor_get(v_zdt_260_, 0);
v___x_262_ = lean_thunk_get_own(v_date_261_);
v_time_263_ = lean_ctor_get(v___x_262_, 1);
lean_inc_ref(v_time_263_);
lean_dec(v___x_262_);
v_hour_264_ = lean_ctor_get(v_time_263_, 0);
lean_inc(v_hour_264_);
lean_dec_ref(v_time_263_);
return v_hour_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_hour___boxed(lean_object* v_zdt_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_Time_ZonedDateTime_hour(v_zdt_265_);
lean_dec_ref(v_zdt_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_minute(lean_object* v_zdt_267_){
_start:
{
lean_object* v_date_268_; lean_object* v___x_269_; lean_object* v_time_270_; lean_object* v_minute_271_; 
v_date_268_ = lean_ctor_get(v_zdt_267_, 0);
v___x_269_ = lean_thunk_get_own(v_date_268_);
v_time_270_ = lean_ctor_get(v___x_269_, 1);
lean_inc_ref(v_time_270_);
lean_dec(v___x_269_);
v_minute_271_ = lean_ctor_get(v_time_270_, 1);
lean_inc(v_minute_271_);
lean_dec_ref(v_time_270_);
return v_minute_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_minute___boxed(lean_object* v_zdt_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Time_ZonedDateTime_minute(v_zdt_272_);
lean_dec_ref(v_zdt_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_second(lean_object* v_zdt_274_){
_start:
{
lean_object* v_date_275_; lean_object* v___x_276_; lean_object* v_time_277_; lean_object* v_second_278_; 
v_date_275_ = lean_ctor_get(v_zdt_274_, 0);
v___x_276_ = lean_thunk_get_own(v_date_275_);
v_time_277_ = lean_ctor_get(v___x_276_, 1);
lean_inc_ref(v_time_277_);
lean_dec(v___x_276_);
v_second_278_ = lean_ctor_get(v_time_277_, 2);
lean_inc(v_second_278_);
lean_dec_ref(v_time_277_);
return v_second_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_second___boxed(lean_object* v_zdt_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Time_ZonedDateTime_second(v_zdt_279_);
lean_dec_ref(v_zdt_279_);
return v_res_280_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_millisecond___closed__0(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1000000u);
v___x_282_ = lean_nat_to_int(v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond(lean_object* v_dt_283_){
_start:
{
lean_object* v_date_284_; lean_object* v___x_285_; lean_object* v_time_286_; lean_object* v_nanosecond_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_date_284_ = lean_ctor_get(v_dt_283_, 0);
v___x_285_ = lean_thunk_get_own(v_date_284_);
v_time_286_ = lean_ctor_get(v___x_285_, 1);
lean_inc_ref(v_time_286_);
lean_dec(v___x_285_);
v_nanosecond_287_ = lean_ctor_get(v_time_286_, 3);
lean_inc(v_nanosecond_287_);
lean_dec_ref(v_time_286_);
v___x_288_ = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
v___x_289_ = lean_int_ediv(v_nanosecond_287_, v___x_288_);
lean_dec(v_nanosecond_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond___boxed(lean_object* v_dt_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_Time_ZonedDateTime_millisecond(v_dt_290_);
lean_dec_ref(v_dt_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond(lean_object* v_zdt_292_){
_start:
{
lean_object* v_date_293_; lean_object* v___x_294_; lean_object* v_time_295_; lean_object* v_nanosecond_296_; 
v_date_293_ = lean_ctor_get(v_zdt_292_, 0);
v___x_294_ = lean_thunk_get_own(v_date_293_);
v_time_295_ = lean_ctor_get(v___x_294_, 1);
lean_inc_ref(v_time_295_);
lean_dec(v___x_294_);
v_nanosecond_296_ = lean_ctor_get(v_time_295_, 3);
lean_inc(v_nanosecond_296_);
lean_dec_ref(v_time_295_);
return v_nanosecond_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond___boxed(lean_object* v_zdt_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Time_ZonedDateTime_nanosecond(v_zdt_297_);
lean_dec_ref(v_zdt_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset(lean_object* v_zdt_299_){
_start:
{
lean_object* v_timezone_300_; lean_object* v_offset_301_; 
v_timezone_300_ = lean_ctor_get(v_zdt_299_, 3);
v_offset_301_ = lean_ctor_get(v_timezone_300_, 0);
lean_inc(v_offset_301_);
return v_offset_301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset___boxed(lean_object* v_zdt_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Std_Time_ZonedDateTime_offset(v_zdt_302_);
lean_dec_ref(v_zdt_302_);
return v_res_303_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_weekday(lean_object* v_zdt_304_){
_start:
{
lean_object* v_date_305_; lean_object* v___x_306_; lean_object* v_date_307_; uint8_t v___x_308_; 
v_date_305_ = lean_ctor_get(v_zdt_304_, 0);
v___x_306_ = lean_thunk_get_own(v_date_305_);
v_date_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc_ref(v_date_307_);
lean_dec(v___x_306_);
v___x_308_ = l_Std_Time_PlainDate_weekday(v_date_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekday___boxed(lean_object* v_zdt_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Std_Time_ZonedDateTime_weekday(v_zdt_309_);
lean_dec_ref(v_zdt_309_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(4u);
v___x_313_ = lean_nat_to_int(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(400u);
v___x_315_ = lean_nat_to_int(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(100u);
v___x_317_ = lean_nat_to_int(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear(lean_object* v_date_318_){
_start:
{
lean_object* v_date_319_; uint8_t v___y_321_; lean_object* v___x_335_; lean_object* v_date_336_; lean_object* v_year_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_345_; 
v_date_319_ = lean_ctor_get(v_date_318_, 0);
v___x_335_ = lean_thunk_get_own(v_date_319_);
v_date_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc_ref(v_date_336_);
lean_dec(v___x_335_);
v_year_337_ = lean_ctor_get(v_date_336_, 0);
lean_inc(v_year_337_);
lean_dec_ref(v_date_336_);
v___x_338_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_339_ = lean_int_mod(v_year_337_, v___x_338_);
v___x_340_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_345_ = lean_int_dec_eq(v___x_339_, v___x_340_);
lean_dec(v___x_339_);
if (v___x_345_ == 0)
{
lean_dec(v_year_337_);
v___y_321_ = v___x_345_;
goto v___jp_320_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_346_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_347_ = lean_int_mod(v_year_337_, v___x_346_);
v___x_348_ = lean_int_dec_eq(v___x_347_, v___x_340_);
lean_dec(v___x_347_);
if (v___x_348_ == 0)
{
if (v___x_345_ == 0)
{
goto v___jp_341_;
}
else
{
lean_dec(v_year_337_);
v___y_321_ = v___x_345_;
goto v___jp_320_;
}
}
else
{
goto v___jp_341_;
}
}
v___jp_320_:
{
lean_object* v___x_322_; lean_object* v_date_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_333_; 
v___x_322_ = lean_thunk_get_own(v_date_319_);
v_date_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v___x_322_, 1);
lean_dec(v_unused_334_);
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_333_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_date_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_333_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_month_327_; lean_object* v_day_328_; lean_object* v___x_330_; 
v_month_327_ = lean_ctor_get(v_date_323_, 1);
lean_inc(v_month_327_);
v_day_328_ = lean_ctor_get(v_date_323_, 2);
lean_inc(v_day_328_);
lean_dec_ref(v_date_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v_day_328_);
lean_ctor_set(v___x_325_, 0, v_month_327_);
v___x_330_ = v___x_325_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_month_327_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_day_328_);
v___x_330_ = v_reuseFailAlloc_332_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; 
v___x_331_ = l_Std_Time_ValidDate_dayOfYear(v___y_321_, v___x_330_);
lean_dec_ref(v___x_330_);
return v___x_331_;
}
}
}
v___jp_341_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_343_ = lean_int_mod(v_year_337_, v___x_342_);
lean_dec(v_year_337_);
v___x_344_ = lean_int_dec_eq(v___x_343_, v___x_340_);
lean_dec(v___x_343_);
v___y_321_ = v___x_344_;
goto v___jp_320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear___boxed(lean_object* v_date_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Time_ZonedDateTime_dayOfYear(v_date_349_);
lean_dec_ref(v_date_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear(lean_object* v_date_351_, uint8_t v_firstDay_352_){
_start:
{
lean_object* v_date_353_; lean_object* v___x_354_; lean_object* v_date_355_; lean_object* v___x_356_; 
v_date_353_ = lean_ctor_get(v_date_351_, 0);
v___x_354_ = lean_thunk_get_own(v_date_353_);
v_date_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc_ref(v_date_355_);
lean_dec(v___x_354_);
v___x_356_ = l_Std_Time_PlainDate_weekOfYear(v_date_355_, v_firstDay_352_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear___boxed(lean_object* v_date_357_, lean_object* v_firstDay_358_){
_start:
{
uint8_t v_firstDay_boxed_359_; lean_object* v_res_360_; 
v_firstDay_boxed_359_ = lean_unbox(v_firstDay_358_);
v_res_360_ = l_Std_Time_ZonedDateTime_weekOfYear(v_date_357_, v_firstDay_boxed_359_);
lean_dec_ref(v_date_357_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekYear(lean_object* v_date_361_, uint8_t v_firstDay_362_){
_start:
{
lean_object* v_date_363_; lean_object* v___x_364_; lean_object* v_date_365_; lean_object* v___x_366_; 
v_date_363_ = lean_ctor_get(v_date_361_, 0);
v___x_364_ = lean_thunk_get_own(v_date_363_);
v_date_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_date_365_);
lean_dec(v___x_364_);
v___x_366_ = l_Std_Time_PlainDate_weekYear(v_date_365_, v_firstDay_362_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekYear___boxed(lean_object* v_date_367_, lean_object* v_firstDay_368_){
_start:
{
uint8_t v_firstDay_boxed_369_; lean_object* v_res_370_; 
v_firstDay_boxed_369_ = lean_unbox(v_firstDay_368_);
v_res_370_ = l_Std_Time_ZonedDateTime_weekYear(v_date_367_, v_firstDay_boxed_369_);
lean_dec_ref(v_date_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth(lean_object* v_date_371_){
_start:
{
lean_object* v_date_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_date_372_ = lean_ctor_get(v_date_371_, 0);
v___x_373_ = lean_thunk_get_own(v_date_372_);
v___x_374_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_373_);
lean_dec(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth___boxed(lean_object* v_date_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_Time_ZonedDateTime_weekOfMonth(v_date_375_);
lean_dec_ref(v_date_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth(lean_object* v_date_377_, uint8_t v_firstDay_378_){
_start:
{
lean_object* v_date_379_; lean_object* v___x_380_; lean_object* v_date_381_; lean_object* v___x_382_; 
v_date_379_ = lean_ctor_get(v_date_377_, 0);
v___x_380_ = lean_thunk_get_own(v_date_379_);
v_date_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc_ref(v_date_381_);
lean_dec(v___x_380_);
v___x_382_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_381_, v_firstDay_378_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth___boxed(lean_object* v_date_383_, lean_object* v_firstDay_384_){
_start:
{
uint8_t v_firstDay_boxed_385_; lean_object* v_res_386_; 
v_firstDay_boxed_385_ = lean_unbox(v_firstDay_384_);
v_res_386_ = l_Std_Time_ZonedDateTime_alignedWeekOfMonth(v_date_383_, v_firstDay_boxed_385_);
lean_dec_ref(v_date_383_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter(lean_object* v_date_387_){
_start:
{
lean_object* v_date_388_; lean_object* v___x_389_; lean_object* v_date_390_; lean_object* v___x_391_; 
v_date_388_ = lean_ctor_get(v_date_387_, 0);
v___x_389_ = lean_thunk_get_own(v_date_388_);
v_date_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc_ref(v_date_390_);
lean_dec(v___x_389_);
v___x_391_ = l_Std_Time_PlainDate_quarter(v_date_390_);
lean_dec_ref(v_date_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter___boxed(lean_object* v_date_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_Time_ZonedDateTime_quarter(v_date_392_);
lean_dec_ref(v_date_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays___lam__0(lean_object* v___y_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v___x_397_, lean_object* v_x_398_){
_start:
{
lean_object* v_offset_399_; lean_object* v_second_400_; lean_object* v_nano_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v_offset_399_ = lean_ctor_get(v___y_394_, 0);
v_second_400_ = lean_ctor_get(v___x_395_, 0);
v_nano_401_ = lean_ctor_get(v___x_395_, 1);
v___x_402_ = lean_int_mul(v_second_400_, v___x_396_);
v___x_403_ = lean_int_add(v___x_402_, v_nano_401_);
lean_dec(v___x_402_);
v___x_404_ = lean_int_mul(v_offset_399_, v___x_396_);
v___x_405_ = lean_int_add(v___x_404_, v___x_397_);
lean_dec(v___x_404_);
v___x_406_ = lean_int_add(v___x_403_, v___x_405_);
lean_dec(v___x_405_);
lean_dec(v___x_403_);
v___x_407_ = l_Std_Time_Duration_ofNanoseconds(v___x_406_);
lean_dec(v___x_406_);
v___x_408_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays___lam__0___boxed(lean_object* v___y_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v___x_412_, lean_object* v_x_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Time_ZonedDateTime_addDays___lam__0(v___y_409_, v___x_410_, v___x_411_, v___x_412_, v_x_413_);
lean_dec(v___x_412_);
lean_dec(v___x_411_);
lean_dec_ref(v___x_410_);
lean_dec_ref(v___y_409_);
return v_res_414_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addDays___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(86400u);
v___x_416_ = lean_nat_to_int(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays(lean_object* v_dt_417_, lean_object* v_days_418_){
_start:
{
lean_object* v_timestamp_419_; lean_object* v_rules_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_448_; 
v_timestamp_419_ = lean_ctor_get(v_dt_417_, 1);
v_rules_420_ = lean_ctor_get(v_dt_417_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_dt_417_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; lean_object* v_unused_450_; 
v_unused_449_ = lean_ctor_get(v_dt_417_, 3);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_dt_417_, 0);
lean_dec(v_unused_450_);
v___x_422_ = v_dt_417_;
v_isShared_423_ = v_isSharedCheck_448_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_rules_420_);
lean_inc(v_timestamp_419_);
lean_dec(v_dt_417_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_448_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_second_424_; lean_object* v_nano_425_; lean_object* v_initialLocalTimeType_426_; lean_object* v_transitions_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___y_439_; lean_object* v___x_445_; 
v_second_424_ = lean_ctor_get(v_timestamp_419_, 0);
lean_inc(v_second_424_);
v_nano_425_ = lean_ctor_get(v_timestamp_419_, 1);
lean_inc(v_nano_425_);
lean_dec_ref(v_timestamp_419_);
v_initialLocalTimeType_426_ = lean_ctor_get(v_rules_420_, 0);
v_transitions_427_ = lean_ctor_get(v_rules_420_, 1);
v___x_428_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addDays___closed__0, &l_Std_Time_ZonedDateTime_addDays___closed__0_once, _init_l_Std_Time_ZonedDateTime_addDays___closed__0);
v___x_429_ = lean_int_mul(v_days_418_, v___x_428_);
v___x_430_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_431_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_432_ = lean_int_mul(v_second_424_, v___x_431_);
lean_dec(v_second_424_);
v___x_433_ = lean_int_add(v___x_432_, v_nano_425_);
lean_dec(v_nano_425_);
lean_dec(v___x_432_);
v___x_434_ = lean_int_mul(v___x_429_, v___x_431_);
lean_dec(v___x_429_);
v___x_435_ = lean_int_add(v___x_434_, v___x_430_);
lean_dec(v___x_434_);
v___x_436_ = lean_int_add(v___x_433_, v___x_435_);
lean_dec(v___x_435_);
lean_dec(v___x_433_);
v___x_437_ = l_Std_Time_Duration_ofNanoseconds(v___x_436_);
lean_dec(v___x_436_);
v___x_445_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_427_, v___x_437_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; 
lean_dec_ref_known(v___x_445_, 1);
v___x_446_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_426_);
v___y_439_ = v___x_446_;
goto v___jp_438_;
}
else
{
lean_object* v_a_447_; 
v_a_447_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v___x_445_, 1);
v___y_439_ = v_a_447_;
goto v___jp_438_;
}
v___jp_438_:
{
lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
lean_inc_ref(v___x_437_);
lean_inc_ref(v___y_439_);
v___f_440_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_440_, 0, v___y_439_);
lean_closure_set(v___f_440_, 1, v___x_437_);
lean_closure_set(v___f_440_, 2, v___x_431_);
lean_closure_set(v___f_440_, 3, v___x_430_);
v___x_441_ = lean_mk_thunk(v___f_440_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 3, v___y_439_);
lean_ctor_set(v___x_422_, 1, v___x_437_);
lean_ctor_set(v___x_422_, 0, v___x_441_);
v___x_443_ = v___x_422_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_rules_420_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v___y_439_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays___boxed(lean_object* v_dt_451_, lean_object* v_days_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_Time_ZonedDateTime_addDays(v_dt_451_, v_days_452_);
lean_dec(v_days_452_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subDays(lean_object* v_dt_454_, lean_object* v_days_455_){
_start:
{
lean_object* v_timestamp_456_; lean_object* v_rules_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_487_; 
v_timestamp_456_ = lean_ctor_get(v_dt_454_, 1);
v_rules_457_ = lean_ctor_get(v_dt_454_, 2);
v_isSharedCheck_487_ = !lean_is_exclusive(v_dt_454_);
if (v_isSharedCheck_487_ == 0)
{
lean_object* v_unused_488_; lean_object* v_unused_489_; 
v_unused_488_ = lean_ctor_get(v_dt_454_, 3);
lean_dec(v_unused_488_);
v_unused_489_ = lean_ctor_get(v_dt_454_, 0);
lean_dec(v_unused_489_);
v___x_459_ = v_dt_454_;
v_isShared_460_ = v_isSharedCheck_487_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_rules_457_);
lean_inc(v_timestamp_456_);
lean_dec(v_dt_454_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_487_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_second_461_; lean_object* v_nano_462_; lean_object* v_initialLocalTimeType_463_; lean_object* v_transitions_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___y_478_; lean_object* v___x_484_; 
v_second_461_ = lean_ctor_get(v_timestamp_456_, 0);
lean_inc(v_second_461_);
v_nano_462_ = lean_ctor_get(v_timestamp_456_, 1);
lean_inc(v_nano_462_);
lean_dec_ref(v_timestamp_456_);
v_initialLocalTimeType_463_ = lean_ctor_get(v_rules_457_, 0);
v_transitions_464_ = lean_ctor_get(v_rules_457_, 1);
v___x_465_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addDays___closed__0, &l_Std_Time_ZonedDateTime_addDays___closed__0_once, _init_l_Std_Time_ZonedDateTime_addDays___closed__0);
v___x_466_ = lean_int_mul(v_days_455_, v___x_465_);
v___x_467_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_468_ = lean_int_neg(v___x_466_);
lean_dec(v___x_466_);
v___x_469_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_470_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_471_ = lean_int_mul(v_second_461_, v___x_470_);
lean_dec(v_second_461_);
v___x_472_ = lean_int_add(v___x_471_, v_nano_462_);
lean_dec(v_nano_462_);
lean_dec(v___x_471_);
v___x_473_ = lean_int_mul(v___x_468_, v___x_470_);
lean_dec(v___x_468_);
v___x_474_ = lean_int_add(v___x_473_, v___x_469_);
lean_dec(v___x_473_);
v___x_475_ = lean_int_add(v___x_472_, v___x_474_);
lean_dec(v___x_474_);
lean_dec(v___x_472_);
v___x_476_ = l_Std_Time_Duration_ofNanoseconds(v___x_475_);
lean_dec(v___x_475_);
v___x_484_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_464_, v___x_476_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v___x_485_; 
lean_dec_ref_known(v___x_484_, 1);
v___x_485_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_463_);
v___y_478_ = v___x_485_;
goto v___jp_477_;
}
else
{
lean_object* v_a_486_; 
v_a_486_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_486_);
lean_dec_ref_known(v___x_484_, 1);
v___y_478_ = v_a_486_;
goto v___jp_477_;
}
v___jp_477_:
{
lean_object* v___f_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
lean_inc_ref(v___x_476_);
lean_inc_ref(v___y_478_);
v___f_479_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_479_, 0, v___y_478_);
lean_closure_set(v___f_479_, 1, v___x_476_);
lean_closure_set(v___f_479_, 2, v___x_470_);
lean_closure_set(v___f_479_, 3, v___x_467_);
v___x_480_ = lean_mk_thunk(v___f_479_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 3, v___y_478_);
lean_ctor_set(v___x_459_, 1, v___x_476_);
lean_ctor_set(v___x_459_, 0, v___x_480_);
v___x_482_ = v___x_459_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_rules_457_);
lean_ctor_set(v_reuseFailAlloc_483_, 3, v___y_478_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subDays___boxed(lean_object* v_dt_490_, lean_object* v_days_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_Time_ZonedDateTime_subDays(v_dt_490_, v_days_491_);
lean_dec(v_days_491_);
return v_res_492_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(7u);
v___x_494_ = lean_nat_to_int(v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addWeeks(lean_object* v_dt_495_, lean_object* v_weeks_496_){
_start:
{
lean_object* v_timestamp_497_; lean_object* v_rules_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_528_; 
v_timestamp_497_ = lean_ctor_get(v_dt_495_, 1);
v_rules_498_ = lean_ctor_get(v_dt_495_, 2);
v_isSharedCheck_528_ = !lean_is_exclusive(v_dt_495_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; lean_object* v_unused_530_; 
v_unused_529_ = lean_ctor_get(v_dt_495_, 3);
lean_dec(v_unused_529_);
v_unused_530_ = lean_ctor_get(v_dt_495_, 0);
lean_dec(v_unused_530_);
v___x_500_ = v_dt_495_;
v_isShared_501_ = v_isSharedCheck_528_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_rules_498_);
lean_inc(v_timestamp_497_);
lean_dec(v_dt_495_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_528_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_second_502_; lean_object* v_nano_503_; lean_object* v_initialLocalTimeType_504_; lean_object* v_transitions_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___y_519_; lean_object* v___x_525_; 
v_second_502_ = lean_ctor_get(v_timestamp_497_, 0);
lean_inc(v_second_502_);
v_nano_503_ = lean_ctor_get(v_timestamp_497_, 1);
lean_inc(v_nano_503_);
lean_dec_ref(v_timestamp_497_);
v_initialLocalTimeType_504_ = lean_ctor_get(v_rules_498_, 0);
v_transitions_505_ = lean_ctor_get(v_rules_498_, 1);
v___x_506_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addWeeks___closed__0, &l_Std_Time_ZonedDateTime_addWeeks___closed__0_once, _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0);
v___x_507_ = lean_int_mul(v_weeks_496_, v___x_506_);
v___x_508_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addDays___closed__0, &l_Std_Time_ZonedDateTime_addDays___closed__0_once, _init_l_Std_Time_ZonedDateTime_addDays___closed__0);
v___x_509_ = lean_int_mul(v___x_507_, v___x_508_);
lean_dec(v___x_507_);
v___x_510_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_511_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_512_ = lean_int_mul(v_second_502_, v___x_511_);
lean_dec(v_second_502_);
v___x_513_ = lean_int_add(v___x_512_, v_nano_503_);
lean_dec(v_nano_503_);
lean_dec(v___x_512_);
v___x_514_ = lean_int_mul(v___x_509_, v___x_511_);
lean_dec(v___x_509_);
v___x_515_ = lean_int_add(v___x_514_, v___x_510_);
lean_dec(v___x_514_);
v___x_516_ = lean_int_add(v___x_513_, v___x_515_);
lean_dec(v___x_515_);
lean_dec(v___x_513_);
v___x_517_ = l_Std_Time_Duration_ofNanoseconds(v___x_516_);
lean_dec(v___x_516_);
v___x_525_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_505_, v___x_517_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v___x_526_; 
lean_dec_ref_known(v___x_525_, 1);
v___x_526_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_504_);
v___y_519_ = v___x_526_;
goto v___jp_518_;
}
else
{
lean_object* v_a_527_; 
v_a_527_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_525_, 1);
v___y_519_ = v_a_527_;
goto v___jp_518_;
}
v___jp_518_:
{
lean_object* v___f_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
lean_inc_ref(v___x_517_);
lean_inc_ref(v___y_519_);
v___f_520_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_520_, 0, v___y_519_);
lean_closure_set(v___f_520_, 1, v___x_517_);
lean_closure_set(v___f_520_, 2, v___x_511_);
lean_closure_set(v___f_520_, 3, v___x_510_);
v___x_521_ = lean_mk_thunk(v___f_520_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 3, v___y_519_);
lean_ctor_set(v___x_500_, 1, v___x_517_);
lean_ctor_set(v___x_500_, 0, v___x_521_);
v___x_523_ = v___x_500_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_rules_498_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v___y_519_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addWeeks___boxed(lean_object* v_dt_531_, lean_object* v_weeks_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Std_Time_ZonedDateTime_addWeeks(v_dt_531_, v_weeks_532_);
lean_dec(v_weeks_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subWeeks(lean_object* v_dt_534_, lean_object* v_weeks_535_){
_start:
{
lean_object* v_timestamp_536_; lean_object* v_rules_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_569_; 
v_timestamp_536_ = lean_ctor_get(v_dt_534_, 1);
v_rules_537_ = lean_ctor_get(v_dt_534_, 2);
v_isSharedCheck_569_ = !lean_is_exclusive(v_dt_534_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; lean_object* v_unused_571_; 
v_unused_570_ = lean_ctor_get(v_dt_534_, 3);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_dt_534_, 0);
lean_dec(v_unused_571_);
v___x_539_ = v_dt_534_;
v_isShared_540_ = v_isSharedCheck_569_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_rules_537_);
lean_inc(v_timestamp_536_);
lean_dec(v_dt_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_569_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_second_541_; lean_object* v_nano_542_; lean_object* v_initialLocalTimeType_543_; lean_object* v_transitions_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___y_560_; lean_object* v___x_566_; 
v_second_541_ = lean_ctor_get(v_timestamp_536_, 0);
lean_inc(v_second_541_);
v_nano_542_ = lean_ctor_get(v_timestamp_536_, 1);
lean_inc(v_nano_542_);
lean_dec_ref(v_timestamp_536_);
v_initialLocalTimeType_543_ = lean_ctor_get(v_rules_537_, 0);
v_transitions_544_ = lean_ctor_get(v_rules_537_, 1);
v___x_545_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addWeeks___closed__0, &l_Std_Time_ZonedDateTime_addWeeks___closed__0_once, _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0);
v___x_546_ = lean_int_mul(v_weeks_535_, v___x_545_);
v___x_547_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addDays___closed__0, &l_Std_Time_ZonedDateTime_addDays___closed__0_once, _init_l_Std_Time_ZonedDateTime_addDays___closed__0);
v___x_548_ = lean_int_mul(v___x_546_, v___x_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_550_ = lean_int_neg(v___x_548_);
lean_dec(v___x_548_);
v___x_551_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_552_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_553_ = lean_int_mul(v_second_541_, v___x_552_);
lean_dec(v_second_541_);
v___x_554_ = lean_int_add(v___x_553_, v_nano_542_);
lean_dec(v_nano_542_);
lean_dec(v___x_553_);
v___x_555_ = lean_int_mul(v___x_550_, v___x_552_);
lean_dec(v___x_550_);
v___x_556_ = lean_int_add(v___x_555_, v___x_551_);
lean_dec(v___x_555_);
v___x_557_ = lean_int_add(v___x_554_, v___x_556_);
lean_dec(v___x_556_);
lean_dec(v___x_554_);
v___x_558_ = l_Std_Time_Duration_ofNanoseconds(v___x_557_);
lean_dec(v___x_557_);
v___x_566_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_544_, v___x_558_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___x_567_; 
lean_dec_ref_known(v___x_566_, 1);
v___x_567_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_543_);
v___y_560_ = v___x_567_;
goto v___jp_559_;
}
else
{
lean_object* v_a_568_; 
v_a_568_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v___x_566_, 1);
v___y_560_ = v_a_568_;
goto v___jp_559_;
}
v___jp_559_:
{
lean_object* v___f_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
lean_inc_ref(v___x_558_);
lean_inc_ref(v___y_560_);
v___f_561_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_561_, 0, v___y_560_);
lean_closure_set(v___f_561_, 1, v___x_558_);
lean_closure_set(v___f_561_, 2, v___x_552_);
lean_closure_set(v___f_561_, 3, v___x_549_);
v___x_562_ = lean_mk_thunk(v___f_561_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 3, v___y_560_);
lean_ctor_set(v___x_539_, 1, v___x_558_);
lean_ctor_set(v___x_539_, 0, v___x_562_);
v___x_564_ = v___x_539_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_rules_537_);
lean_ctor_set(v_reuseFailAlloc_565_, 3, v___y_560_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subWeeks___boxed(lean_object* v_dt_572_, lean_object* v_weeks_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Time_ZonedDateTime_subWeeks(v_dt_572_, v_weeks_573_);
lean_dec(v_weeks_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip___lam__0(lean_object* v___x_575_, lean_object* v_x_576_){
_start:
{
lean_inc_ref(v___x_575_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed(lean_object* v___x_577_, lean_object* v_x_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Std_Time_ZonedDateTime_addMonthsClip___lam__0(v___x_577_, v_x_578_);
lean_dec_ref(v___x_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip(lean_object* v_dt_580_, lean_object* v_months_581_){
_start:
{
lean_object* v_date_582_; lean_object* v_rules_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_609_; 
v_date_582_ = lean_ctor_get(v_dt_580_, 0);
v_rules_583_ = lean_ctor_get(v_dt_580_, 2);
v_isSharedCheck_609_ = !lean_is_exclusive(v_dt_580_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; lean_object* v_unused_611_; 
v_unused_610_ = lean_ctor_get(v_dt_580_, 3);
lean_dec(v_unused_610_);
v_unused_611_ = lean_ctor_get(v_dt_580_, 1);
lean_dec(v_unused_611_);
v___x_585_ = v_dt_580_;
v_isShared_586_ = v_isSharedCheck_609_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_rules_583_);
lean_inc(v_date_582_);
lean_dec(v_dt_580_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_609_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_wt_589_; lean_object* v_ltt_590_; lean_object* v_tz_591_; lean_object* v_offset_592_; lean_object* v_second_593_; lean_object* v_nano_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_587_ = lean_thunk_get_own(v_date_582_);
lean_dec_ref(v_date_582_);
v___x_588_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_587_, v_months_581_);
lean_inc_ref(v___x_588_);
v_wt_589_ = l_Std_Time_PlainDateTime_toWallTime(v___x_588_);
lean_inc_ref(v_rules_583_);
v_ltt_590_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_583_, v_wt_589_);
v_tz_591_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_590_);
lean_dec_ref(v_ltt_590_);
v_offset_592_ = lean_ctor_get(v_tz_591_, 0);
lean_inc(v_offset_592_);
v_second_593_ = lean_ctor_get(v_wt_589_, 0);
lean_inc(v_second_593_);
v_nano_594_ = lean_ctor_get(v_wt_589_, 1);
lean_inc(v_nano_594_);
lean_dec_ref(v_wt_589_);
v___f_595_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_595_, 0, v___x_588_);
v___x_596_ = lean_mk_thunk(v___f_595_);
v___x_597_ = lean_int_neg(v_offset_592_);
lean_dec(v_offset_592_);
v___x_598_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_599_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_600_ = lean_int_mul(v_second_593_, v___x_599_);
lean_dec(v_second_593_);
v___x_601_ = lean_int_add(v___x_600_, v_nano_594_);
lean_dec(v_nano_594_);
lean_dec(v___x_600_);
v___x_602_ = lean_int_mul(v___x_597_, v___x_599_);
lean_dec(v___x_597_);
v___x_603_ = lean_int_add(v___x_602_, v___x_598_);
lean_dec(v___x_602_);
v___x_604_ = lean_int_add(v___x_601_, v___x_603_);
lean_dec(v___x_603_);
lean_dec(v___x_601_);
v___x_605_ = l_Std_Time_Duration_ofNanoseconds(v___x_604_);
lean_dec(v___x_604_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 3, v_tz_591_);
lean_ctor_set(v___x_585_, 1, v___x_605_);
lean_ctor_set(v___x_585_, 0, v___x_596_);
v___x_607_ = v___x_585_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v_rules_583_);
lean_ctor_set(v_reuseFailAlloc_608_, 3, v_tz_591_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip___boxed(lean_object* v_dt_612_, lean_object* v_months_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Std_Time_ZonedDateTime_addMonthsClip(v_dt_612_, v_months_613_);
lean_dec(v_months_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip(lean_object* v_dt_615_, lean_object* v_months_616_){
_start:
{
lean_object* v_date_617_; lean_object* v_rules_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_654_; 
v_date_617_ = lean_ctor_get(v_dt_615_, 0);
v_rules_618_ = lean_ctor_get(v_dt_615_, 2);
v_isSharedCheck_654_ = !lean_is_exclusive(v_dt_615_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; lean_object* v_unused_656_; 
v_unused_655_ = lean_ctor_get(v_dt_615_, 3);
lean_dec(v_unused_655_);
v_unused_656_ = lean_ctor_get(v_dt_615_, 1);
lean_dec(v_unused_656_);
v___x_620_ = v_dt_615_;
v_isShared_621_ = v_isSharedCheck_654_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_rules_618_);
lean_inc(v_date_617_);
lean_dec(v_dt_615_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_654_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v_date_623_; lean_object* v_time_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_653_; 
v___x_622_ = lean_thunk_get_own(v_date_617_);
lean_dec_ref(v_date_617_);
v_date_623_ = lean_ctor_get(v___x_622_, 0);
v_time_624_ = lean_ctor_get(v___x_622_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_653_ == 0)
{
v___x_626_ = v___x_622_;
v_isShared_627_ = v_isSharedCheck_653_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_time_624_);
lean_inc(v_date_623_);
lean_dec(v___x_622_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_653_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_int_neg(v_months_616_);
v___x_629_ = l_Std_Time_PlainDate_addMonthsClip(v_date_623_, v___x_628_);
lean_dec(v___x_628_);
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_629_);
v___x_631_ = v___x_626_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_time_624_);
v___x_631_ = v_reuseFailAlloc_652_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v_wt_632_; lean_object* v_ltt_633_; lean_object* v_tz_634_; lean_object* v_offset_635_; lean_object* v_second_636_; lean_object* v_nano_637_; lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
lean_inc_ref(v___x_631_);
v_wt_632_ = l_Std_Time_PlainDateTime_toWallTime(v___x_631_);
lean_inc_ref(v_rules_618_);
v_ltt_633_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_618_, v_wt_632_);
v_tz_634_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_633_);
lean_dec_ref(v_ltt_633_);
v_offset_635_ = lean_ctor_get(v_tz_634_, 0);
lean_inc(v_offset_635_);
v_second_636_ = lean_ctor_get(v_wt_632_, 0);
lean_inc(v_second_636_);
v_nano_637_ = lean_ctor_get(v_wt_632_, 1);
lean_inc(v_nano_637_);
lean_dec_ref(v_wt_632_);
v___f_638_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_638_, 0, v___x_631_);
v___x_639_ = lean_mk_thunk(v___f_638_);
v___x_640_ = lean_int_neg(v_offset_635_);
lean_dec(v_offset_635_);
v___x_641_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_642_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_643_ = lean_int_mul(v_second_636_, v___x_642_);
lean_dec(v_second_636_);
v___x_644_ = lean_int_add(v___x_643_, v_nano_637_);
lean_dec(v_nano_637_);
lean_dec(v___x_643_);
v___x_645_ = lean_int_mul(v___x_640_, v___x_642_);
lean_dec(v___x_640_);
v___x_646_ = lean_int_add(v___x_645_, v___x_641_);
lean_dec(v___x_645_);
v___x_647_ = lean_int_add(v___x_644_, v___x_646_);
lean_dec(v___x_646_);
lean_dec(v___x_644_);
v___x_648_ = l_Std_Time_Duration_ofNanoseconds(v___x_647_);
lean_dec(v___x_647_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 3, v_tz_634_);
lean_ctor_set(v___x_620_, 1, v___x_648_);
lean_ctor_set(v___x_620_, 0, v___x_639_);
v___x_650_ = v___x_620_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_rules_618_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_tz_634_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip___boxed(lean_object* v_dt_657_, lean_object* v_months_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Time_ZonedDateTime_subMonthsClip(v_dt_657_, v_months_658_);
lean_dec(v_months_658_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver(lean_object* v_dt_660_, lean_object* v_months_661_){
_start:
{
lean_object* v_date_662_; lean_object* v_rules_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_689_; 
v_date_662_ = lean_ctor_get(v_dt_660_, 0);
v_rules_663_ = lean_ctor_get(v_dt_660_, 2);
v_isSharedCheck_689_ = !lean_is_exclusive(v_dt_660_);
if (v_isSharedCheck_689_ == 0)
{
lean_object* v_unused_690_; lean_object* v_unused_691_; 
v_unused_690_ = lean_ctor_get(v_dt_660_, 3);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_dt_660_, 1);
lean_dec(v_unused_691_);
v___x_665_ = v_dt_660_;
v_isShared_666_ = v_isSharedCheck_689_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_rules_663_);
lean_inc(v_date_662_);
lean_dec(v_dt_660_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_689_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_wt_669_; lean_object* v_ltt_670_; lean_object* v_tz_671_; lean_object* v_offset_672_; lean_object* v_second_673_; lean_object* v_nano_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_687_; 
v___x_667_ = lean_thunk_get_own(v_date_662_);
lean_dec_ref(v_date_662_);
v___x_668_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_667_, v_months_661_);
lean_inc_ref(v___x_668_);
v_wt_669_ = l_Std_Time_PlainDateTime_toWallTime(v___x_668_);
lean_inc_ref(v_rules_663_);
v_ltt_670_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_663_, v_wt_669_);
v_tz_671_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_670_);
lean_dec_ref(v_ltt_670_);
v_offset_672_ = lean_ctor_get(v_tz_671_, 0);
lean_inc(v_offset_672_);
v_second_673_ = lean_ctor_get(v_wt_669_, 0);
lean_inc(v_second_673_);
v_nano_674_ = lean_ctor_get(v_wt_669_, 1);
lean_inc(v_nano_674_);
lean_dec_ref(v_wt_669_);
v___f_675_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_675_, 0, v___x_668_);
v___x_676_ = lean_mk_thunk(v___f_675_);
v___x_677_ = lean_int_neg(v_offset_672_);
lean_dec(v_offset_672_);
v___x_678_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_679_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_680_ = lean_int_mul(v_second_673_, v___x_679_);
lean_dec(v_second_673_);
v___x_681_ = lean_int_add(v___x_680_, v_nano_674_);
lean_dec(v_nano_674_);
lean_dec(v___x_680_);
v___x_682_ = lean_int_mul(v___x_677_, v___x_679_);
lean_dec(v___x_677_);
v___x_683_ = lean_int_add(v___x_682_, v___x_678_);
lean_dec(v___x_682_);
v___x_684_ = lean_int_add(v___x_681_, v___x_683_);
lean_dec(v___x_683_);
lean_dec(v___x_681_);
v___x_685_ = l_Std_Time_Duration_ofNanoseconds(v___x_684_);
lean_dec(v___x_684_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 3, v_tz_671_);
lean_ctor_set(v___x_665_, 1, v___x_685_);
lean_ctor_set(v___x_665_, 0, v___x_676_);
v___x_687_ = v___x_665_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v___x_685_);
lean_ctor_set(v_reuseFailAlloc_688_, 2, v_rules_663_);
lean_ctor_set(v_reuseFailAlloc_688_, 3, v_tz_671_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver___boxed(lean_object* v_dt_692_, lean_object* v_months_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_Time_ZonedDateTime_addMonthsRollOver(v_dt_692_, v_months_693_);
lean_dec(v_months_693_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsRollOver(lean_object* v_dt_695_, lean_object* v_months_696_){
_start:
{
lean_object* v_date_697_; lean_object* v_rules_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_734_; 
v_date_697_ = lean_ctor_get(v_dt_695_, 0);
v_rules_698_ = lean_ctor_get(v_dt_695_, 2);
v_isSharedCheck_734_ = !lean_is_exclusive(v_dt_695_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; lean_object* v_unused_736_; 
v_unused_735_ = lean_ctor_get(v_dt_695_, 3);
lean_dec(v_unused_735_);
v_unused_736_ = lean_ctor_get(v_dt_695_, 1);
lean_dec(v_unused_736_);
v___x_700_ = v_dt_695_;
v_isShared_701_ = v_isSharedCheck_734_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_rules_698_);
lean_inc(v_date_697_);
lean_dec(v_dt_695_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_734_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v_date_703_; lean_object* v_time_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_733_; 
v___x_702_ = lean_thunk_get_own(v_date_697_);
lean_dec_ref(v_date_697_);
v_date_703_ = lean_ctor_get(v___x_702_, 0);
v_time_704_ = lean_ctor_get(v___x_702_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_733_ == 0)
{
v___x_706_ = v___x_702_;
v_isShared_707_ = v_isSharedCheck_733_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_time_704_);
lean_inc(v_date_703_);
lean_dec(v___x_702_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_733_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_708_ = lean_int_neg(v_months_696_);
v___x_709_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_703_, v___x_708_);
lean_dec(v___x_708_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_709_);
v___x_711_ = v___x_706_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_time_704_);
v___x_711_ = v_reuseFailAlloc_732_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v_wt_712_; lean_object* v_ltt_713_; lean_object* v_tz_714_; lean_object* v_offset_715_; lean_object* v_second_716_; lean_object* v_nano_717_; lean_object* v___f_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
lean_inc_ref(v___x_711_);
v_wt_712_ = l_Std_Time_PlainDateTime_toWallTime(v___x_711_);
lean_inc_ref(v_rules_698_);
v_ltt_713_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_698_, v_wt_712_);
v_tz_714_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_713_);
lean_dec_ref(v_ltt_713_);
v_offset_715_ = lean_ctor_get(v_tz_714_, 0);
lean_inc(v_offset_715_);
v_second_716_ = lean_ctor_get(v_wt_712_, 0);
lean_inc(v_second_716_);
v_nano_717_ = lean_ctor_get(v_wt_712_, 1);
lean_inc(v_nano_717_);
lean_dec_ref(v_wt_712_);
v___f_718_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_718_, 0, v___x_711_);
v___x_719_ = lean_mk_thunk(v___f_718_);
v___x_720_ = lean_int_neg(v_offset_715_);
lean_dec(v_offset_715_);
v___x_721_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_722_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_723_ = lean_int_mul(v_second_716_, v___x_722_);
lean_dec(v_second_716_);
v___x_724_ = lean_int_add(v___x_723_, v_nano_717_);
lean_dec(v_nano_717_);
lean_dec(v___x_723_);
v___x_725_ = lean_int_mul(v___x_720_, v___x_722_);
lean_dec(v___x_720_);
v___x_726_ = lean_int_add(v___x_725_, v___x_721_);
lean_dec(v___x_725_);
v___x_727_ = lean_int_add(v___x_724_, v___x_726_);
lean_dec(v___x_726_);
lean_dec(v___x_724_);
v___x_728_ = l_Std_Time_Duration_ofNanoseconds(v___x_727_);
lean_dec(v___x_727_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 3, v_tz_714_);
lean_ctor_set(v___x_700_, 1, v___x_728_);
lean_ctor_set(v___x_700_, 0, v___x_719_);
v___x_730_ = v___x_700_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_731_, 2, v_rules_698_);
lean_ctor_set(v_reuseFailAlloc_731_, 3, v_tz_714_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsRollOver___boxed(lean_object* v_dt_737_, lean_object* v_months_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_Time_ZonedDateTime_subMonthsRollOver(v_dt_737_, v_months_738_);
lean_dec(v_months_738_);
return v_res_739_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(12u);
v___x_741_ = lean_nat_to_int(v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsRollOver(lean_object* v_dt_742_, lean_object* v_years_743_){
_start:
{
lean_object* v_date_744_; lean_object* v_rules_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_782_; 
v_date_744_ = lean_ctor_get(v_dt_742_, 0);
v_rules_745_ = lean_ctor_get(v_dt_742_, 2);
v_isSharedCheck_782_ = !lean_is_exclusive(v_dt_742_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; lean_object* v_unused_784_; 
v_unused_783_ = lean_ctor_get(v_dt_742_, 3);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_dt_742_, 1);
lean_dec(v_unused_784_);
v___x_747_ = v_dt_742_;
v_isShared_748_ = v_isSharedCheck_782_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_rules_745_);
lean_inc(v_date_744_);
lean_dec(v_dt_742_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_782_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v_date_750_; lean_object* v_time_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_781_; 
v___x_749_ = lean_thunk_get_own(v_date_744_);
lean_dec_ref(v_date_744_);
v_date_750_ = lean_ctor_get(v___x_749_, 0);
v_time_751_ = lean_ctor_get(v___x_749_, 1);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_781_ == 0)
{
v___x_753_ = v___x_749_;
v_isShared_754_ = v_isSharedCheck_781_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_time_751_);
lean_inc(v_date_750_);
lean_dec(v___x_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_781_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_755_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
v___x_756_ = lean_int_mul(v_years_743_, v___x_755_);
v___x_757_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_750_, v___x_756_);
lean_dec(v___x_756_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_757_);
v___x_759_ = v___x_753_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_time_751_);
v___x_759_ = v_reuseFailAlloc_780_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v_wt_760_; lean_object* v_ltt_761_; lean_object* v_tz_762_; lean_object* v_offset_763_; lean_object* v_second_764_; lean_object* v_nano_765_; lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_778_; 
lean_inc_ref(v___x_759_);
v_wt_760_ = l_Std_Time_PlainDateTime_toWallTime(v___x_759_);
lean_inc_ref(v_rules_745_);
v_ltt_761_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_745_, v_wt_760_);
v_tz_762_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_761_);
lean_dec_ref(v_ltt_761_);
v_offset_763_ = lean_ctor_get(v_tz_762_, 0);
lean_inc(v_offset_763_);
v_second_764_ = lean_ctor_get(v_wt_760_, 0);
lean_inc(v_second_764_);
v_nano_765_ = lean_ctor_get(v_wt_760_, 1);
lean_inc(v_nano_765_);
lean_dec_ref(v_wt_760_);
v___f_766_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_766_, 0, v___x_759_);
v___x_767_ = lean_mk_thunk(v___f_766_);
v___x_768_ = lean_int_neg(v_offset_763_);
lean_dec(v_offset_763_);
v___x_769_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_770_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_771_ = lean_int_mul(v_second_764_, v___x_770_);
lean_dec(v_second_764_);
v___x_772_ = lean_int_add(v___x_771_, v_nano_765_);
lean_dec(v_nano_765_);
lean_dec(v___x_771_);
v___x_773_ = lean_int_mul(v___x_768_, v___x_770_);
lean_dec(v___x_768_);
v___x_774_ = lean_int_add(v___x_773_, v___x_769_);
lean_dec(v___x_773_);
v___x_775_ = lean_int_add(v___x_772_, v___x_774_);
lean_dec(v___x_774_);
lean_dec(v___x_772_);
v___x_776_ = l_Std_Time_Duration_ofNanoseconds(v___x_775_);
lean_dec(v___x_775_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 3, v_tz_762_);
lean_ctor_set(v___x_747_, 1, v___x_776_);
lean_ctor_set(v___x_747_, 0, v___x_767_);
v___x_778_ = v___x_747_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_rules_745_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_tz_762_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsRollOver___boxed(lean_object* v_dt_785_, lean_object* v_years_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_Time_ZonedDateTime_addYearsRollOver(v_dt_785_, v_years_786_);
lean_dec(v_years_786_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsClip(lean_object* v_dt_788_, lean_object* v_years_789_){
_start:
{
lean_object* v_date_790_; lean_object* v_rules_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_828_; 
v_date_790_ = lean_ctor_get(v_dt_788_, 0);
v_rules_791_ = lean_ctor_get(v_dt_788_, 2);
v_isSharedCheck_828_ = !lean_is_exclusive(v_dt_788_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; lean_object* v_unused_830_; 
v_unused_829_ = lean_ctor_get(v_dt_788_, 3);
lean_dec(v_unused_829_);
v_unused_830_ = lean_ctor_get(v_dt_788_, 1);
lean_dec(v_unused_830_);
v___x_793_ = v_dt_788_;
v_isShared_794_ = v_isSharedCheck_828_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_rules_791_);
lean_inc(v_date_790_);
lean_dec(v_dt_788_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_828_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v_date_796_; lean_object* v_time_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_827_; 
v___x_795_ = lean_thunk_get_own(v_date_790_);
lean_dec_ref(v_date_790_);
v_date_796_ = lean_ctor_get(v___x_795_, 0);
v_time_797_ = lean_ctor_get(v___x_795_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_827_ == 0)
{
v___x_799_ = v___x_795_;
v_isShared_800_ = v_isSharedCheck_827_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_time_797_);
lean_inc(v_date_796_);
lean_dec(v___x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_827_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_801_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
v___x_802_ = lean_int_mul(v_years_789_, v___x_801_);
v___x_803_ = l_Std_Time_PlainDate_addMonthsClip(v_date_796_, v___x_802_);
lean_dec(v___x_802_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_803_);
v___x_805_ = v___x_799_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_time_797_);
v___x_805_ = v_reuseFailAlloc_826_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v_wt_806_; lean_object* v_ltt_807_; lean_object* v_tz_808_; lean_object* v_offset_809_; lean_object* v_second_810_; lean_object* v_nano_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_inc_ref(v___x_805_);
v_wt_806_ = l_Std_Time_PlainDateTime_toWallTime(v___x_805_);
lean_inc_ref(v_rules_791_);
v_ltt_807_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_791_, v_wt_806_);
v_tz_808_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_807_);
lean_dec_ref(v_ltt_807_);
v_offset_809_ = lean_ctor_get(v_tz_808_, 0);
lean_inc(v_offset_809_);
v_second_810_ = lean_ctor_get(v_wt_806_, 0);
lean_inc(v_second_810_);
v_nano_811_ = lean_ctor_get(v_wt_806_, 1);
lean_inc(v_nano_811_);
lean_dec_ref(v_wt_806_);
v___f_812_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_812_, 0, v___x_805_);
v___x_813_ = lean_mk_thunk(v___f_812_);
v___x_814_ = lean_int_neg(v_offset_809_);
lean_dec(v_offset_809_);
v___x_815_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_816_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_817_ = lean_int_mul(v_second_810_, v___x_816_);
lean_dec(v_second_810_);
v___x_818_ = lean_int_add(v___x_817_, v_nano_811_);
lean_dec(v_nano_811_);
lean_dec(v___x_817_);
v___x_819_ = lean_int_mul(v___x_814_, v___x_816_);
lean_dec(v___x_814_);
v___x_820_ = lean_int_add(v___x_819_, v___x_815_);
lean_dec(v___x_819_);
v___x_821_ = lean_int_add(v___x_818_, v___x_820_);
lean_dec(v___x_820_);
lean_dec(v___x_818_);
v___x_822_ = l_Std_Time_Duration_ofNanoseconds(v___x_821_);
lean_dec(v___x_821_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 3, v_tz_808_);
lean_ctor_set(v___x_793_, 1, v___x_822_);
lean_ctor_set(v___x_793_, 0, v___x_813_);
v___x_824_ = v___x_793_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v_rules_791_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v_tz_808_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsClip___boxed(lean_object* v_dt_831_, lean_object* v_years_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_Time_ZonedDateTime_addYearsClip(v_dt_831_, v_years_832_);
lean_dec(v_years_832_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsClip(lean_object* v_dt_834_, lean_object* v_years_835_){
_start:
{
lean_object* v_date_836_; lean_object* v_rules_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_875_; 
v_date_836_ = lean_ctor_get(v_dt_834_, 0);
v_rules_837_ = lean_ctor_get(v_dt_834_, 2);
v_isSharedCheck_875_ = !lean_is_exclusive(v_dt_834_);
if (v_isSharedCheck_875_ == 0)
{
lean_object* v_unused_876_; lean_object* v_unused_877_; 
v_unused_876_ = lean_ctor_get(v_dt_834_, 3);
lean_dec(v_unused_876_);
v_unused_877_ = lean_ctor_get(v_dt_834_, 1);
lean_dec(v_unused_877_);
v___x_839_ = v_dt_834_;
v_isShared_840_ = v_isSharedCheck_875_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_rules_837_);
lean_inc(v_date_836_);
lean_dec(v_dt_834_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_875_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v_date_842_; lean_object* v_time_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_874_; 
v___x_841_ = lean_thunk_get_own(v_date_836_);
lean_dec_ref(v_date_836_);
v_date_842_ = lean_ctor_get(v___x_841_, 0);
v_time_843_ = lean_ctor_get(v___x_841_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_874_ == 0)
{
v___x_845_ = v___x_841_;
v_isShared_846_ = v_isSharedCheck_874_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_time_843_);
lean_inc(v_date_842_);
lean_dec(v___x_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_874_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_847_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
v___x_848_ = lean_int_mul(v_years_835_, v___x_847_);
v___x_849_ = lean_int_neg(v___x_848_);
lean_dec(v___x_848_);
v___x_850_ = l_Std_Time_PlainDate_addMonthsClip(v_date_842_, v___x_849_);
lean_dec(v___x_849_);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v___x_850_);
v___x_852_ = v___x_845_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_850_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_time_843_);
v___x_852_ = v_reuseFailAlloc_873_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v_wt_853_; lean_object* v_ltt_854_; lean_object* v_tz_855_; lean_object* v_offset_856_; lean_object* v_second_857_; lean_object* v_nano_858_; lean_object* v___f_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_inc_ref(v___x_852_);
v_wt_853_ = l_Std_Time_PlainDateTime_toWallTime(v___x_852_);
lean_inc_ref(v_rules_837_);
v_ltt_854_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_837_, v_wt_853_);
v_tz_855_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_854_);
lean_dec_ref(v_ltt_854_);
v_offset_856_ = lean_ctor_get(v_tz_855_, 0);
lean_inc(v_offset_856_);
v_second_857_ = lean_ctor_get(v_wt_853_, 0);
lean_inc(v_second_857_);
v_nano_858_ = lean_ctor_get(v_wt_853_, 1);
lean_inc(v_nano_858_);
lean_dec_ref(v_wt_853_);
v___f_859_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_859_, 0, v___x_852_);
v___x_860_ = lean_mk_thunk(v___f_859_);
v___x_861_ = lean_int_neg(v_offset_856_);
lean_dec(v_offset_856_);
v___x_862_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_863_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_864_ = lean_int_mul(v_second_857_, v___x_863_);
lean_dec(v_second_857_);
v___x_865_ = lean_int_add(v___x_864_, v_nano_858_);
lean_dec(v_nano_858_);
lean_dec(v___x_864_);
v___x_866_ = lean_int_mul(v___x_861_, v___x_863_);
lean_dec(v___x_861_);
v___x_867_ = lean_int_add(v___x_866_, v___x_862_);
lean_dec(v___x_866_);
v___x_868_ = lean_int_add(v___x_865_, v___x_867_);
lean_dec(v___x_867_);
lean_dec(v___x_865_);
v___x_869_ = l_Std_Time_Duration_ofNanoseconds(v___x_868_);
lean_dec(v___x_868_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 3, v_tz_855_);
lean_ctor_set(v___x_839_, 1, v___x_869_);
lean_ctor_set(v___x_839_, 0, v___x_860_);
v___x_871_ = v___x_839_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_860_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_rules_837_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_tz_855_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsClip___boxed(lean_object* v_dt_878_, lean_object* v_years_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_Time_ZonedDateTime_subYearsClip(v_dt_878_, v_years_879_);
lean_dec(v_years_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsRollOver(lean_object* v_dt_881_, lean_object* v_years_882_){
_start:
{
lean_object* v_date_883_; lean_object* v_rules_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_922_; 
v_date_883_ = lean_ctor_get(v_dt_881_, 0);
v_rules_884_ = lean_ctor_get(v_dt_881_, 2);
v_isSharedCheck_922_ = !lean_is_exclusive(v_dt_881_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; lean_object* v_unused_924_; 
v_unused_923_ = lean_ctor_get(v_dt_881_, 3);
lean_dec(v_unused_923_);
v_unused_924_ = lean_ctor_get(v_dt_881_, 1);
lean_dec(v_unused_924_);
v___x_886_ = v_dt_881_;
v_isShared_887_ = v_isSharedCheck_922_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_rules_884_);
lean_inc(v_date_883_);
lean_dec(v_dt_881_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_922_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v_date_889_; lean_object* v_time_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_921_; 
v___x_888_ = lean_thunk_get_own(v_date_883_);
lean_dec_ref(v_date_883_);
v_date_889_ = lean_ctor_get(v___x_888_, 0);
v_time_890_ = lean_ctor_get(v___x_888_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_921_ == 0)
{
v___x_892_ = v___x_888_;
v_isShared_893_ = v_isSharedCheck_921_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_time_890_);
lean_inc(v_date_889_);
lean_dec(v___x_888_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_921_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_894_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
v___x_895_ = lean_int_mul(v_years_882_, v___x_894_);
v___x_896_ = lean_int_neg(v___x_895_);
lean_dec(v___x_895_);
v___x_897_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_889_, v___x_896_);
lean_dec(v___x_896_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_897_);
v___x_899_ = v___x_892_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_time_890_);
v___x_899_ = v_reuseFailAlloc_920_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v_wt_900_; lean_object* v_ltt_901_; lean_object* v_tz_902_; lean_object* v_offset_903_; lean_object* v_second_904_; lean_object* v_nano_905_; lean_object* v___f_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
lean_inc_ref(v___x_899_);
v_wt_900_ = l_Std_Time_PlainDateTime_toWallTime(v___x_899_);
lean_inc_ref(v_rules_884_);
v_ltt_901_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_884_, v_wt_900_);
v_tz_902_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_901_);
lean_dec_ref(v_ltt_901_);
v_offset_903_ = lean_ctor_get(v_tz_902_, 0);
lean_inc(v_offset_903_);
v_second_904_ = lean_ctor_get(v_wt_900_, 0);
lean_inc(v_second_904_);
v_nano_905_ = lean_ctor_get(v_wt_900_, 1);
lean_inc(v_nano_905_);
lean_dec_ref(v_wt_900_);
v___f_906_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_906_, 0, v___x_899_);
v___x_907_ = lean_mk_thunk(v___f_906_);
v___x_908_ = lean_int_neg(v_offset_903_);
lean_dec(v_offset_903_);
v___x_909_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_910_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_911_ = lean_int_mul(v_second_904_, v___x_910_);
lean_dec(v_second_904_);
v___x_912_ = lean_int_add(v___x_911_, v_nano_905_);
lean_dec(v_nano_905_);
lean_dec(v___x_911_);
v___x_913_ = lean_int_mul(v___x_908_, v___x_910_);
lean_dec(v___x_908_);
v___x_914_ = lean_int_add(v___x_913_, v___x_909_);
lean_dec(v___x_913_);
v___x_915_ = lean_int_add(v___x_912_, v___x_914_);
lean_dec(v___x_914_);
lean_dec(v___x_912_);
v___x_916_ = l_Std_Time_Duration_ofNanoseconds(v___x_915_);
lean_dec(v___x_915_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 3, v_tz_902_);
lean_ctor_set(v___x_886_, 1, v___x_916_);
lean_ctor_set(v___x_886_, 0, v___x_907_);
v___x_918_ = v___x_886_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_916_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_rules_884_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_tz_902_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsRollOver___boxed(lean_object* v_dt_925_, lean_object* v_years_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_Time_ZonedDateTime_subYearsRollOver(v_dt_925_, v_years_926_);
lean_dec(v_years_926_);
return v_res_927_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(3600u);
v___x_929_ = lean_nat_to_int(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours(lean_object* v_dt_930_, lean_object* v_hours_931_){
_start:
{
lean_object* v_timestamp_932_; lean_object* v_rules_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_961_; 
v_timestamp_932_ = lean_ctor_get(v_dt_930_, 1);
v_rules_933_ = lean_ctor_get(v_dt_930_, 2);
v_isSharedCheck_961_ = !lean_is_exclusive(v_dt_930_);
if (v_isSharedCheck_961_ == 0)
{
lean_object* v_unused_962_; lean_object* v_unused_963_; 
v_unused_962_ = lean_ctor_get(v_dt_930_, 3);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_dt_930_, 0);
lean_dec(v_unused_963_);
v___x_935_ = v_dt_930_;
v_isShared_936_ = v_isSharedCheck_961_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_rules_933_);
lean_inc(v_timestamp_932_);
lean_dec(v_dt_930_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_961_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_second_937_; lean_object* v_nano_938_; lean_object* v_initialLocalTimeType_939_; lean_object* v_transitions_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___y_952_; lean_object* v___x_958_; 
v_second_937_ = lean_ctor_get(v_timestamp_932_, 0);
lean_inc(v_second_937_);
v_nano_938_ = lean_ctor_get(v_timestamp_932_, 1);
lean_inc(v_nano_938_);
lean_dec_ref(v_timestamp_932_);
v_initialLocalTimeType_939_ = lean_ctor_get(v_rules_933_, 0);
v_transitions_940_ = lean_ctor_get(v_rules_933_, 1);
v___x_941_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addHours___closed__0, &l_Std_Time_ZonedDateTime_addHours___closed__0_once, _init_l_Std_Time_ZonedDateTime_addHours___closed__0);
v___x_942_ = lean_int_mul(v_hours_931_, v___x_941_);
v___x_943_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_944_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_945_ = lean_int_mul(v_second_937_, v___x_944_);
lean_dec(v_second_937_);
v___x_946_ = lean_int_add(v___x_945_, v_nano_938_);
lean_dec(v_nano_938_);
lean_dec(v___x_945_);
v___x_947_ = lean_int_mul(v___x_942_, v___x_944_);
lean_dec(v___x_942_);
v___x_948_ = lean_int_add(v___x_947_, v___x_943_);
lean_dec(v___x_947_);
v___x_949_ = lean_int_add(v___x_946_, v___x_948_);
lean_dec(v___x_948_);
lean_dec(v___x_946_);
v___x_950_ = l_Std_Time_Duration_ofNanoseconds(v___x_949_);
lean_dec(v___x_949_);
v___x_958_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_940_, v___x_950_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; 
lean_dec_ref_known(v___x_958_, 1);
v___x_959_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_939_);
v___y_952_ = v___x_959_;
goto v___jp_951_;
}
else
{
lean_object* v_a_960_; 
v_a_960_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_958_, 1);
v___y_952_ = v_a_960_;
goto v___jp_951_;
}
v___jp_951_:
{
lean_object* v___f_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
lean_inc_ref(v___x_950_);
lean_inc_ref(v___y_952_);
v___f_953_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_953_, 0, v___y_952_);
lean_closure_set(v___f_953_, 1, v___x_950_);
lean_closure_set(v___f_953_, 2, v___x_944_);
lean_closure_set(v___f_953_, 3, v___x_943_);
v___x_954_ = lean_mk_thunk(v___f_953_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 3, v___y_952_);
lean_ctor_set(v___x_935_, 1, v___x_950_);
lean_ctor_set(v___x_935_, 0, v___x_954_);
v___x_956_ = v___x_935_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_rules_933_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v___y_952_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___boxed(lean_object* v_dt_964_, lean_object* v_hours_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Std_Time_ZonedDateTime_addHours(v_dt_964_, v_hours_965_);
lean_dec(v_hours_965_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subHours(lean_object* v_dt_967_, lean_object* v_hours_968_){
_start:
{
lean_object* v_timestamp_969_; lean_object* v_rules_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1000_; 
v_timestamp_969_ = lean_ctor_get(v_dt_967_, 1);
v_rules_970_ = lean_ctor_get(v_dt_967_, 2);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_dt_967_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; lean_object* v_unused_1002_; 
v_unused_1001_ = lean_ctor_get(v_dt_967_, 3);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_dt_967_, 0);
lean_dec(v_unused_1002_);
v___x_972_ = v_dt_967_;
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_rules_970_);
lean_inc(v_timestamp_969_);
lean_dec(v_dt_967_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v_second_974_; lean_object* v_nano_975_; lean_object* v_initialLocalTimeType_976_; lean_object* v_transitions_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___y_991_; lean_object* v___x_997_; 
v_second_974_ = lean_ctor_get(v_timestamp_969_, 0);
lean_inc(v_second_974_);
v_nano_975_ = lean_ctor_get(v_timestamp_969_, 1);
lean_inc(v_nano_975_);
lean_dec_ref(v_timestamp_969_);
v_initialLocalTimeType_976_ = lean_ctor_get(v_rules_970_, 0);
v_transitions_977_ = lean_ctor_get(v_rules_970_, 1);
v___x_978_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addHours___closed__0, &l_Std_Time_ZonedDateTime_addHours___closed__0_once, _init_l_Std_Time_ZonedDateTime_addHours___closed__0);
v___x_979_ = lean_int_mul(v_hours_968_, v___x_978_);
v___x_980_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_981_ = lean_int_neg(v___x_979_);
lean_dec(v___x_979_);
v___x_982_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_983_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_984_ = lean_int_mul(v_second_974_, v___x_983_);
lean_dec(v_second_974_);
v___x_985_ = lean_int_add(v___x_984_, v_nano_975_);
lean_dec(v_nano_975_);
lean_dec(v___x_984_);
v___x_986_ = lean_int_mul(v___x_981_, v___x_983_);
lean_dec(v___x_981_);
v___x_987_ = lean_int_add(v___x_986_, v___x_982_);
lean_dec(v___x_986_);
v___x_988_ = lean_int_add(v___x_985_, v___x_987_);
lean_dec(v___x_987_);
lean_dec(v___x_985_);
v___x_989_ = l_Std_Time_Duration_ofNanoseconds(v___x_988_);
lean_dec(v___x_988_);
v___x_997_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_977_, v___x_989_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v___x_998_; 
lean_dec_ref_known(v___x_997_, 1);
v___x_998_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_976_);
v___y_991_ = v___x_998_;
goto v___jp_990_;
}
else
{
lean_object* v_a_999_; 
v_a_999_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_997_, 1);
v___y_991_ = v_a_999_;
goto v___jp_990_;
}
v___jp_990_:
{
lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
lean_inc_ref(v___x_989_);
lean_inc_ref(v___y_991_);
v___f_992_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_992_, 0, v___y_991_);
lean_closure_set(v___f_992_, 1, v___x_989_);
lean_closure_set(v___f_992_, 2, v___x_983_);
lean_closure_set(v___f_992_, 3, v___x_980_);
v___x_993_ = lean_mk_thunk(v___f_992_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 3, v___y_991_);
lean_ctor_set(v___x_972_, 1, v___x_989_);
lean_ctor_set(v___x_972_, 0, v___x_993_);
v___x_995_ = v___x_972_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_996_, 2, v_rules_970_);
lean_ctor_set(v_reuseFailAlloc_996_, 3, v___y_991_);
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
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subHours___boxed(lean_object* v_dt_1003_, lean_object* v_hours_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_Time_ZonedDateTime_subHours(v_dt_1003_, v_hours_1004_);
lean_dec(v_hours_1004_);
return v_res_1005_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_unsigned_to_nat(60u);
v___x_1007_ = lean_nat_to_int(v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMinutes(lean_object* v_dt_1008_, lean_object* v_minutes_1009_){
_start:
{
lean_object* v_timestamp_1010_; lean_object* v_rules_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1039_; 
v_timestamp_1010_ = lean_ctor_get(v_dt_1008_, 1);
v_rules_1011_ = lean_ctor_get(v_dt_1008_, 2);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_dt_1008_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; lean_object* v_unused_1041_; 
v_unused_1040_ = lean_ctor_get(v_dt_1008_, 3);
lean_dec(v_unused_1040_);
v_unused_1041_ = lean_ctor_get(v_dt_1008_, 0);
lean_dec(v_unused_1041_);
v___x_1013_ = v_dt_1008_;
v_isShared_1014_ = v_isSharedCheck_1039_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_rules_1011_);
lean_inc(v_timestamp_1010_);
lean_dec(v_dt_1008_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1039_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v_second_1015_; lean_object* v_nano_1016_; lean_object* v_initialLocalTimeType_1017_; lean_object* v_transitions_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___y_1030_; lean_object* v___x_1036_; 
v_second_1015_ = lean_ctor_get(v_timestamp_1010_, 0);
lean_inc(v_second_1015_);
v_nano_1016_ = lean_ctor_get(v_timestamp_1010_, 1);
lean_inc(v_nano_1016_);
lean_dec_ref(v_timestamp_1010_);
v_initialLocalTimeType_1017_ = lean_ctor_get(v_rules_1011_, 0);
v_transitions_1018_ = lean_ctor_get(v_rules_1011_, 1);
v___x_1019_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addMinutes___closed__0, &l_Std_Time_ZonedDateTime_addMinutes___closed__0_once, _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0);
v___x_1020_ = lean_int_mul(v_minutes_1009_, v___x_1019_);
v___x_1021_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1022_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1023_ = lean_int_mul(v_second_1015_, v___x_1022_);
lean_dec(v_second_1015_);
v___x_1024_ = lean_int_add(v___x_1023_, v_nano_1016_);
lean_dec(v_nano_1016_);
lean_dec(v___x_1023_);
v___x_1025_ = lean_int_mul(v___x_1020_, v___x_1022_);
lean_dec(v___x_1020_);
v___x_1026_ = lean_int_add(v___x_1025_, v___x_1021_);
lean_dec(v___x_1025_);
v___x_1027_ = lean_int_add(v___x_1024_, v___x_1026_);
lean_dec(v___x_1026_);
lean_dec(v___x_1024_);
v___x_1028_ = l_Std_Time_Duration_ofNanoseconds(v___x_1027_);
lean_dec(v___x_1027_);
v___x_1036_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1018_, v___x_1028_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; 
lean_dec_ref_known(v___x_1036_, 1);
v___x_1037_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1017_);
v___y_1030_ = v___x_1037_;
goto v___jp_1029_;
}
else
{
lean_object* v_a_1038_; 
v_a_1038_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1036_, 1);
v___y_1030_ = v_a_1038_;
goto v___jp_1029_;
}
v___jp_1029_:
{
lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
lean_inc_ref(v___x_1028_);
lean_inc_ref(v___y_1030_);
v___f_1031_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1031_, 0, v___y_1030_);
lean_closure_set(v___f_1031_, 1, v___x_1028_);
lean_closure_set(v___f_1031_, 2, v___x_1022_);
lean_closure_set(v___f_1031_, 3, v___x_1021_);
v___x_1032_ = lean_mk_thunk(v___f_1031_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 3, v___y_1030_);
lean_ctor_set(v___x_1013_, 1, v___x_1028_);
lean_ctor_set(v___x_1013_, 0, v___x_1032_);
v___x_1034_ = v___x_1013_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
lean_ctor_set(v_reuseFailAlloc_1035_, 1, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1035_, 2, v_rules_1011_);
lean_ctor_set(v_reuseFailAlloc_1035_, 3, v___y_1030_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMinutes___boxed(lean_object* v_dt_1042_, lean_object* v_minutes_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_Time_ZonedDateTime_addMinutes(v_dt_1042_, v_minutes_1043_);
lean_dec(v_minutes_1043_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMinutes(lean_object* v_dt_1045_, lean_object* v_minutes_1046_){
_start:
{
lean_object* v_timestamp_1047_; lean_object* v_rules_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1078_; 
v_timestamp_1047_ = lean_ctor_get(v_dt_1045_, 1);
v_rules_1048_ = lean_ctor_get(v_dt_1045_, 2);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_dt_1045_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; lean_object* v_unused_1080_; 
v_unused_1079_ = lean_ctor_get(v_dt_1045_, 3);
lean_dec(v_unused_1079_);
v_unused_1080_ = lean_ctor_get(v_dt_1045_, 0);
lean_dec(v_unused_1080_);
v___x_1050_ = v_dt_1045_;
v_isShared_1051_ = v_isSharedCheck_1078_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_rules_1048_);
lean_inc(v_timestamp_1047_);
lean_dec(v_dt_1045_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1078_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_second_1052_; lean_object* v_nano_1053_; lean_object* v_initialLocalTimeType_1054_; lean_object* v_transitions_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___y_1069_; lean_object* v___x_1075_; 
v_second_1052_ = lean_ctor_get(v_timestamp_1047_, 0);
lean_inc(v_second_1052_);
v_nano_1053_ = lean_ctor_get(v_timestamp_1047_, 1);
lean_inc(v_nano_1053_);
lean_dec_ref(v_timestamp_1047_);
v_initialLocalTimeType_1054_ = lean_ctor_get(v_rules_1048_, 0);
v_transitions_1055_ = lean_ctor_get(v_rules_1048_, 1);
v___x_1056_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addMinutes___closed__0, &l_Std_Time_ZonedDateTime_addMinutes___closed__0_once, _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0);
v___x_1057_ = lean_int_mul(v_minutes_1046_, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1059_ = lean_int_neg(v___x_1057_);
lean_dec(v___x_1057_);
v___x_1060_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1061_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1062_ = lean_int_mul(v_second_1052_, v___x_1061_);
lean_dec(v_second_1052_);
v___x_1063_ = lean_int_add(v___x_1062_, v_nano_1053_);
lean_dec(v_nano_1053_);
lean_dec(v___x_1062_);
v___x_1064_ = lean_int_mul(v___x_1059_, v___x_1061_);
lean_dec(v___x_1059_);
v___x_1065_ = lean_int_add(v___x_1064_, v___x_1060_);
lean_dec(v___x_1064_);
v___x_1066_ = lean_int_add(v___x_1063_, v___x_1065_);
lean_dec(v___x_1065_);
lean_dec(v___x_1063_);
v___x_1067_ = l_Std_Time_Duration_ofNanoseconds(v___x_1066_);
lean_dec(v___x_1066_);
v___x_1075_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1055_, v___x_1067_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v___x_1076_; 
lean_dec_ref_known(v___x_1075_, 1);
v___x_1076_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1054_);
v___y_1069_ = v___x_1076_;
goto v___jp_1068_;
}
else
{
lean_object* v_a_1077_; 
v_a_1077_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1075_, 1);
v___y_1069_ = v_a_1077_;
goto v___jp_1068_;
}
v___jp_1068_:
{
lean_object* v___f_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
lean_inc_ref(v___x_1067_);
lean_inc_ref(v___y_1069_);
v___f_1070_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1070_, 0, v___y_1069_);
lean_closure_set(v___f_1070_, 1, v___x_1067_);
lean_closure_set(v___f_1070_, 2, v___x_1061_);
lean_closure_set(v___f_1070_, 3, v___x_1058_);
v___x_1071_ = lean_mk_thunk(v___f_1070_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 3, v___y_1069_);
lean_ctor_set(v___x_1050_, 1, v___x_1067_);
lean_ctor_set(v___x_1050_, 0, v___x_1071_);
v___x_1073_ = v___x_1050_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_rules_1048_);
lean_ctor_set(v_reuseFailAlloc_1074_, 3, v___y_1069_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMinutes___boxed(lean_object* v_dt_1081_, lean_object* v_minutes_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Std_Time_ZonedDateTime_subMinutes(v_dt_1081_, v_minutes_1082_);
lean_dec(v_minutes_1082_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds___lam__0(lean_object* v___y_1084_, lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v_x_1087_){
_start:
{
lean_object* v_offset_1088_; lean_object* v_second_1089_; lean_object* v_nano_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_offset_1088_ = lean_ctor_get(v___y_1084_, 0);
v_second_1089_ = lean_ctor_get(v___x_1085_, 0);
v_nano_1090_ = lean_ctor_get(v___x_1085_, 1);
v___x_1091_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1092_ = lean_int_mul(v_second_1089_, v___x_1086_);
v___x_1093_ = lean_int_add(v___x_1092_, v_nano_1090_);
lean_dec(v___x_1092_);
v___x_1094_ = lean_int_mul(v_offset_1088_, v___x_1086_);
v___x_1095_ = lean_int_add(v___x_1094_, v___x_1091_);
lean_dec(v___x_1094_);
v___x_1096_ = lean_int_add(v___x_1093_, v___x_1095_);
lean_dec(v___x_1095_);
lean_dec(v___x_1093_);
v___x_1097_ = l_Std_Time_Duration_ofNanoseconds(v___x_1096_);
lean_dec(v___x_1096_);
v___x_1098_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed(lean_object* v___y_1099_, lean_object* v___x_1100_, lean_object* v___x_1101_, lean_object* v_x_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_Time_ZonedDateTime_addMilliseconds___lam__0(v___y_1099_, v___x_1100_, v___x_1101_, v_x_1102_);
lean_dec(v___x_1101_);
lean_dec_ref(v___x_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds(lean_object* v_dt_1104_, lean_object* v_milliseconds_1105_){
_start:
{
lean_object* v_timestamp_1106_; lean_object* v_rules_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1137_; 
v_timestamp_1106_ = lean_ctor_get(v_dt_1104_, 1);
v_rules_1107_ = lean_ctor_get(v_dt_1104_, 2);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_dt_1104_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; lean_object* v_unused_1139_; 
v_unused_1138_ = lean_ctor_get(v_dt_1104_, 3);
lean_dec(v_unused_1138_);
v_unused_1139_ = lean_ctor_get(v_dt_1104_, 0);
lean_dec(v_unused_1139_);
v___x_1109_ = v_dt_1104_;
v_isShared_1110_ = v_isSharedCheck_1137_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_rules_1107_);
lean_inc(v_timestamp_1106_);
lean_dec(v_dt_1104_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1137_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v_second_1111_; lean_object* v_nano_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v_second_1116_; lean_object* v_nano_1117_; lean_object* v_initialLocalTimeType_1118_; lean_object* v_transitions_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___y_1128_; lean_object* v___x_1134_; 
v_second_1111_ = lean_ctor_get(v_timestamp_1106_, 0);
lean_inc(v_second_1111_);
v_nano_1112_ = lean_ctor_get(v_timestamp_1106_, 1);
lean_inc(v_nano_1112_);
lean_dec_ref(v_timestamp_1106_);
v___x_1113_ = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
v___x_1114_ = lean_int_mul(v_milliseconds_1105_, v___x_1113_);
v___x_1115_ = l_Std_Time_Duration_ofNanoseconds(v___x_1114_);
lean_dec(v___x_1114_);
v_second_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_second_1116_);
v_nano_1117_ = lean_ctor_get(v___x_1115_, 1);
lean_inc(v_nano_1117_);
lean_dec_ref(v___x_1115_);
v_initialLocalTimeType_1118_ = lean_ctor_get(v_rules_1107_, 0);
v_transitions_1119_ = lean_ctor_get(v_rules_1107_, 1);
v___x_1120_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1121_ = lean_int_mul(v_second_1111_, v___x_1120_);
lean_dec(v_second_1111_);
v___x_1122_ = lean_int_add(v___x_1121_, v_nano_1112_);
lean_dec(v_nano_1112_);
lean_dec(v___x_1121_);
v___x_1123_ = lean_int_mul(v_second_1116_, v___x_1120_);
lean_dec(v_second_1116_);
v___x_1124_ = lean_int_add(v___x_1123_, v_nano_1117_);
lean_dec(v_nano_1117_);
lean_dec(v___x_1123_);
v___x_1125_ = lean_int_add(v___x_1122_, v___x_1124_);
lean_dec(v___x_1124_);
lean_dec(v___x_1122_);
v___x_1126_ = l_Std_Time_Duration_ofNanoseconds(v___x_1125_);
lean_dec(v___x_1125_);
v___x_1134_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1119_, v___x_1126_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref_known(v___x_1134_, 1);
v___x_1135_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1118_);
v___y_1128_ = v___x_1135_;
goto v___jp_1127_;
}
else
{
lean_object* v_a_1136_; 
v_a_1136_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1134_, 1);
v___y_1128_ = v_a_1136_;
goto v___jp_1127_;
}
v___jp_1127_:
{
lean_object* v___f_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_inc_ref(v___x_1126_);
lean_inc_ref(v___y_1128_);
v___f_1129_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1129_, 0, v___y_1128_);
lean_closure_set(v___f_1129_, 1, v___x_1126_);
lean_closure_set(v___f_1129_, 2, v___x_1120_);
v___x_1130_ = lean_mk_thunk(v___f_1129_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 3, v___y_1128_);
lean_ctor_set(v___x_1109_, 1, v___x_1126_);
lean_ctor_set(v___x_1109_, 0, v___x_1130_);
v___x_1132_ = v___x_1109_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_rules_1107_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v___y_1128_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds___boxed(lean_object* v_dt_1140_, lean_object* v_milliseconds_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_Time_ZonedDateTime_addMilliseconds(v_dt_1140_, v_milliseconds_1141_);
lean_dec(v_milliseconds_1141_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMilliseconds(lean_object* v_dt_1143_, lean_object* v_milliseconds_1144_){
_start:
{
lean_object* v_timestamp_1145_; lean_object* v_rules_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1178_; 
v_timestamp_1145_ = lean_ctor_get(v_dt_1143_, 1);
v_rules_1146_ = lean_ctor_get(v_dt_1143_, 2);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_dt_1143_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; 
v_unused_1179_ = lean_ctor_get(v_dt_1143_, 3);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_dt_1143_, 0);
lean_dec(v_unused_1180_);
v___x_1148_ = v_dt_1143_;
v_isShared_1149_ = v_isSharedCheck_1178_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_rules_1146_);
lean_inc(v_timestamp_1145_);
lean_dec(v_dt_1143_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1178_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_second_1153_; lean_object* v_nano_1154_; lean_object* v_second_1155_; lean_object* v_nano_1156_; lean_object* v_initialLocalTimeType_1157_; lean_object* v_transitions_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___y_1169_; lean_object* v___x_1175_; 
v___x_1150_ = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
v___x_1151_ = lean_int_mul(v_milliseconds_1144_, v___x_1150_);
v___x_1152_ = l_Std_Time_Duration_ofNanoseconds(v___x_1151_);
lean_dec(v___x_1151_);
v_second_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_second_1153_);
v_nano_1154_ = lean_ctor_get(v___x_1152_, 1);
lean_inc(v_nano_1154_);
lean_dec_ref(v___x_1152_);
v_second_1155_ = lean_ctor_get(v_timestamp_1145_, 0);
lean_inc(v_second_1155_);
v_nano_1156_ = lean_ctor_get(v_timestamp_1145_, 1);
lean_inc(v_nano_1156_);
lean_dec_ref(v_timestamp_1145_);
v_initialLocalTimeType_1157_ = lean_ctor_get(v_rules_1146_, 0);
v_transitions_1158_ = lean_ctor_get(v_rules_1146_, 1);
v___x_1159_ = lean_int_neg(v_second_1153_);
lean_dec(v_second_1153_);
v___x_1160_ = lean_int_neg(v_nano_1154_);
lean_dec(v_nano_1154_);
v___x_1161_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1162_ = lean_int_mul(v_second_1155_, v___x_1161_);
lean_dec(v_second_1155_);
v___x_1163_ = lean_int_add(v___x_1162_, v_nano_1156_);
lean_dec(v_nano_1156_);
lean_dec(v___x_1162_);
v___x_1164_ = lean_int_mul(v___x_1159_, v___x_1161_);
lean_dec(v___x_1159_);
v___x_1165_ = lean_int_add(v___x_1164_, v___x_1160_);
lean_dec(v___x_1160_);
lean_dec(v___x_1164_);
v___x_1166_ = lean_int_add(v___x_1163_, v___x_1165_);
lean_dec(v___x_1165_);
lean_dec(v___x_1163_);
v___x_1167_ = l_Std_Time_Duration_ofNanoseconds(v___x_1166_);
lean_dec(v___x_1166_);
v___x_1175_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1158_, v___x_1167_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref_known(v___x_1175_, 1);
v___x_1176_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1157_);
v___y_1169_ = v___x_1176_;
goto v___jp_1168_;
}
else
{
lean_object* v_a_1177_; 
v_a_1177_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1177_);
lean_dec_ref_known(v___x_1175_, 1);
v___y_1169_ = v_a_1177_;
goto v___jp_1168_;
}
v___jp_1168_:
{
lean_object* v___f_1170_; lean_object* v___x_1171_; lean_object* v___x_1173_; 
lean_inc_ref(v___x_1167_);
lean_inc_ref(v___y_1169_);
v___f_1170_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1170_, 0, v___y_1169_);
lean_closure_set(v___f_1170_, 1, v___x_1167_);
lean_closure_set(v___f_1170_, 2, v___x_1161_);
v___x_1171_ = lean_mk_thunk(v___f_1170_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 3, v___y_1169_);
lean_ctor_set(v___x_1148_, 1, v___x_1167_);
lean_ctor_set(v___x_1148_, 0, v___x_1171_);
v___x_1173_ = v___x_1148_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1167_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_rules_1146_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v___y_1169_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMilliseconds___boxed(lean_object* v_dt_1181_, lean_object* v_milliseconds_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Std_Time_ZonedDateTime_subMilliseconds(v_dt_1181_, v_milliseconds_1182_);
lean_dec(v_milliseconds_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addSeconds(lean_object* v_dt_1184_, lean_object* v_seconds_1185_){
_start:
{
lean_object* v_timestamp_1186_; lean_object* v_rules_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1213_; 
v_timestamp_1186_ = lean_ctor_get(v_dt_1184_, 1);
v_rules_1187_ = lean_ctor_get(v_dt_1184_, 2);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_dt_1184_);
if (v_isSharedCheck_1213_ == 0)
{
lean_object* v_unused_1214_; lean_object* v_unused_1215_; 
v_unused_1214_ = lean_ctor_get(v_dt_1184_, 3);
lean_dec(v_unused_1214_);
v_unused_1215_ = lean_ctor_get(v_dt_1184_, 0);
lean_dec(v_unused_1215_);
v___x_1189_ = v_dt_1184_;
v_isShared_1190_ = v_isSharedCheck_1213_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_rules_1187_);
lean_inc(v_timestamp_1186_);
lean_dec(v_dt_1184_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1213_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_second_1191_; lean_object* v_nano_1192_; lean_object* v_initialLocalTimeType_1193_; lean_object* v_transitions_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___y_1204_; lean_object* v___x_1210_; 
v_second_1191_ = lean_ctor_get(v_timestamp_1186_, 0);
lean_inc(v_second_1191_);
v_nano_1192_ = lean_ctor_get(v_timestamp_1186_, 1);
lean_inc(v_nano_1192_);
lean_dec_ref(v_timestamp_1186_);
v_initialLocalTimeType_1193_ = lean_ctor_get(v_rules_1187_, 0);
v_transitions_1194_ = lean_ctor_get(v_rules_1187_, 1);
v___x_1195_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1196_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1197_ = lean_int_mul(v_second_1191_, v___x_1196_);
lean_dec(v_second_1191_);
v___x_1198_ = lean_int_add(v___x_1197_, v_nano_1192_);
lean_dec(v_nano_1192_);
lean_dec(v___x_1197_);
v___x_1199_ = lean_int_mul(v_seconds_1185_, v___x_1196_);
v___x_1200_ = lean_int_add(v___x_1199_, v___x_1195_);
lean_dec(v___x_1199_);
v___x_1201_ = lean_int_add(v___x_1198_, v___x_1200_);
lean_dec(v___x_1200_);
lean_dec(v___x_1198_);
v___x_1202_ = l_Std_Time_Duration_ofNanoseconds(v___x_1201_);
lean_dec(v___x_1201_);
v___x_1210_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1194_, v___x_1202_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1211_; 
lean_dec_ref_known(v___x_1210_, 1);
v___x_1211_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1193_);
v___y_1204_ = v___x_1211_;
goto v___jp_1203_;
}
else
{
lean_object* v_a_1212_; 
v_a_1212_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1210_, 1);
v___y_1204_ = v_a_1212_;
goto v___jp_1203_;
}
v___jp_1203_:
{
lean_object* v___f_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_inc_ref(v___x_1202_);
lean_inc_ref(v___y_1204_);
v___f_1205_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1205_, 0, v___y_1204_);
lean_closure_set(v___f_1205_, 1, v___x_1202_);
lean_closure_set(v___f_1205_, 2, v___x_1196_);
lean_closure_set(v___f_1205_, 3, v___x_1195_);
v___x_1206_ = lean_mk_thunk(v___f_1205_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 3, v___y_1204_);
lean_ctor_set(v___x_1189_, 1, v___x_1202_);
lean_ctor_set(v___x_1189_, 0, v___x_1206_);
v___x_1208_ = v___x_1189_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_rules_1187_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v___y_1204_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addSeconds___boxed(lean_object* v_dt_1216_, lean_object* v_seconds_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_Time_ZonedDateTime_addSeconds(v_dt_1216_, v_seconds_1217_);
lean_dec(v_seconds_1217_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subSeconds(lean_object* v_dt_1219_, lean_object* v_seconds_1220_){
_start:
{
lean_object* v_timestamp_1221_; lean_object* v_rules_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1250_; 
v_timestamp_1221_ = lean_ctor_get(v_dt_1219_, 1);
v_rules_1222_ = lean_ctor_get(v_dt_1219_, 2);
v_isSharedCheck_1250_ = !lean_is_exclusive(v_dt_1219_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; lean_object* v_unused_1252_; 
v_unused_1251_ = lean_ctor_get(v_dt_1219_, 3);
lean_dec(v_unused_1251_);
v_unused_1252_ = lean_ctor_get(v_dt_1219_, 0);
lean_dec(v_unused_1252_);
v___x_1224_ = v_dt_1219_;
v_isShared_1225_ = v_isSharedCheck_1250_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_rules_1222_);
lean_inc(v_timestamp_1221_);
lean_dec(v_dt_1219_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1250_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_second_1226_; lean_object* v_nano_1227_; lean_object* v_initialLocalTimeType_1228_; lean_object* v_transitions_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___y_1241_; lean_object* v___x_1247_; 
v_second_1226_ = lean_ctor_get(v_timestamp_1221_, 0);
lean_inc(v_second_1226_);
v_nano_1227_ = lean_ctor_get(v_timestamp_1221_, 1);
lean_inc(v_nano_1227_);
lean_dec_ref(v_timestamp_1221_);
v_initialLocalTimeType_1228_ = lean_ctor_get(v_rules_1222_, 0);
v_transitions_1229_ = lean_ctor_get(v_rules_1222_, 1);
v___x_1230_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1231_ = lean_int_neg(v_seconds_1220_);
v___x_1232_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1233_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1234_ = lean_int_mul(v_second_1226_, v___x_1233_);
lean_dec(v_second_1226_);
v___x_1235_ = lean_int_add(v___x_1234_, v_nano_1227_);
lean_dec(v_nano_1227_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_int_mul(v___x_1231_, v___x_1233_);
lean_dec(v___x_1231_);
v___x_1237_ = lean_int_add(v___x_1236_, v___x_1232_);
lean_dec(v___x_1236_);
v___x_1238_ = lean_int_add(v___x_1235_, v___x_1237_);
lean_dec(v___x_1237_);
lean_dec(v___x_1235_);
v___x_1239_ = l_Std_Time_Duration_ofNanoseconds(v___x_1238_);
lean_dec(v___x_1238_);
v___x_1247_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1229_, v___x_1239_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1248_; 
lean_dec_ref_known(v___x_1247_, 1);
v___x_1248_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1228_);
v___y_1241_ = v___x_1248_;
goto v___jp_1240_;
}
else
{
lean_object* v_a_1249_; 
v_a_1249_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1247_, 1);
v___y_1241_ = v_a_1249_;
goto v___jp_1240_;
}
v___jp_1240_:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1245_; 
lean_inc_ref(v___x_1239_);
lean_inc_ref(v___y_1241_);
v___f_1242_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1242_, 0, v___y_1241_);
lean_closure_set(v___f_1242_, 1, v___x_1239_);
lean_closure_set(v___f_1242_, 2, v___x_1233_);
lean_closure_set(v___f_1242_, 3, v___x_1230_);
v___x_1243_ = lean_mk_thunk(v___f_1242_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v___y_1241_);
lean_ctor_set(v___x_1224_, 1, v___x_1239_);
lean_ctor_set(v___x_1224_, 0, v___x_1243_);
v___x_1245_ = v___x_1224_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_rules_1222_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v___y_1241_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subSeconds___boxed(lean_object* v_dt_1253_, lean_object* v_seconds_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Std_Time_ZonedDateTime_subSeconds(v_dt_1253_, v_seconds_1254_);
lean_dec(v_seconds_1254_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addNanoseconds(lean_object* v_dt_1256_, lean_object* v_nanoseconds_1257_){
_start:
{
lean_object* v_timestamp_1258_; lean_object* v_rules_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1287_; 
v_timestamp_1258_ = lean_ctor_get(v_dt_1256_, 1);
v_rules_1259_ = lean_ctor_get(v_dt_1256_, 2);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_dt_1256_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; lean_object* v_unused_1289_; 
v_unused_1288_ = lean_ctor_get(v_dt_1256_, 3);
lean_dec(v_unused_1288_);
v_unused_1289_ = lean_ctor_get(v_dt_1256_, 0);
lean_dec(v_unused_1289_);
v___x_1261_ = v_dt_1256_;
v_isShared_1262_ = v_isSharedCheck_1287_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_rules_1259_);
lean_inc(v_timestamp_1258_);
lean_dec(v_dt_1256_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1287_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_second_1263_; lean_object* v_nano_1264_; lean_object* v___x_1265_; lean_object* v_second_1266_; lean_object* v_nano_1267_; lean_object* v_initialLocalTimeType_1268_; lean_object* v_transitions_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___y_1278_; lean_object* v___x_1284_; 
v_second_1263_ = lean_ctor_get(v_timestamp_1258_, 0);
lean_inc(v_second_1263_);
v_nano_1264_ = lean_ctor_get(v_timestamp_1258_, 1);
lean_inc(v_nano_1264_);
lean_dec_ref(v_timestamp_1258_);
v___x_1265_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1257_);
v_second_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_second_1266_);
v_nano_1267_ = lean_ctor_get(v___x_1265_, 1);
lean_inc(v_nano_1267_);
lean_dec_ref(v___x_1265_);
v_initialLocalTimeType_1268_ = lean_ctor_get(v_rules_1259_, 0);
v_transitions_1269_ = lean_ctor_get(v_rules_1259_, 1);
v___x_1270_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1271_ = lean_int_mul(v_second_1263_, v___x_1270_);
lean_dec(v_second_1263_);
v___x_1272_ = lean_int_add(v___x_1271_, v_nano_1264_);
lean_dec(v_nano_1264_);
lean_dec(v___x_1271_);
v___x_1273_ = lean_int_mul(v_second_1266_, v___x_1270_);
lean_dec(v_second_1266_);
v___x_1274_ = lean_int_add(v___x_1273_, v_nano_1267_);
lean_dec(v_nano_1267_);
lean_dec(v___x_1273_);
v___x_1275_ = lean_int_add(v___x_1272_, v___x_1274_);
lean_dec(v___x_1274_);
lean_dec(v___x_1272_);
v___x_1276_ = l_Std_Time_Duration_ofNanoseconds(v___x_1275_);
lean_dec(v___x_1275_);
v___x_1284_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1269_, v___x_1276_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1285_; 
lean_dec_ref_known(v___x_1284_, 1);
v___x_1285_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1268_);
v___y_1278_ = v___x_1285_;
goto v___jp_1277_;
}
else
{
lean_object* v_a_1286_; 
v_a_1286_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1284_, 1);
v___y_1278_ = v_a_1286_;
goto v___jp_1277_;
}
v___jp_1277_:
{
lean_object* v___f_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
lean_inc_ref(v___x_1276_);
lean_inc_ref(v___y_1278_);
v___f_1279_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1279_, 0, v___y_1278_);
lean_closure_set(v___f_1279_, 1, v___x_1276_);
lean_closure_set(v___f_1279_, 2, v___x_1270_);
v___x_1280_ = lean_mk_thunk(v___f_1279_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 3, v___y_1278_);
lean_ctor_set(v___x_1261_, 1, v___x_1276_);
lean_ctor_set(v___x_1261_, 0, v___x_1280_);
v___x_1282_ = v___x_1261_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_rules_1259_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v___y_1278_);
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
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addNanoseconds___boxed(lean_object* v_dt_1290_, lean_object* v_nanoseconds_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_dt_1290_, v_nanoseconds_1291_);
lean_dec(v_nanoseconds_1291_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subNanoseconds(lean_object* v_dt_1293_, lean_object* v_nanoseconds_1294_){
_start:
{
lean_object* v_timestamp_1295_; lean_object* v_rules_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1326_; 
v_timestamp_1295_ = lean_ctor_get(v_dt_1293_, 1);
v_rules_1296_ = lean_ctor_get(v_dt_1293_, 2);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_dt_1293_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; lean_object* v_unused_1328_; 
v_unused_1327_ = lean_ctor_get(v_dt_1293_, 3);
lean_dec(v_unused_1327_);
v_unused_1328_ = lean_ctor_get(v_dt_1293_, 0);
lean_dec(v_unused_1328_);
v___x_1298_ = v_dt_1293_;
v_isShared_1299_ = v_isSharedCheck_1326_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_rules_1296_);
lean_inc(v_timestamp_1295_);
lean_dec(v_dt_1293_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1326_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v_second_1301_; lean_object* v_nano_1302_; lean_object* v_second_1303_; lean_object* v_nano_1304_; lean_object* v_initialLocalTimeType_1305_; lean_object* v_transitions_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___y_1317_; lean_object* v___x_1323_; 
v___x_1300_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1294_);
v_second_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_second_1301_);
v_nano_1302_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_nano_1302_);
lean_dec_ref(v___x_1300_);
v_second_1303_ = lean_ctor_get(v_timestamp_1295_, 0);
lean_inc(v_second_1303_);
v_nano_1304_ = lean_ctor_get(v_timestamp_1295_, 1);
lean_inc(v_nano_1304_);
lean_dec_ref(v_timestamp_1295_);
v_initialLocalTimeType_1305_ = lean_ctor_get(v_rules_1296_, 0);
v_transitions_1306_ = lean_ctor_get(v_rules_1296_, 1);
v___x_1307_ = lean_int_neg(v_second_1301_);
lean_dec(v_second_1301_);
v___x_1308_ = lean_int_neg(v_nano_1302_);
lean_dec(v_nano_1302_);
v___x_1309_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1310_ = lean_int_mul(v_second_1303_, v___x_1309_);
lean_dec(v_second_1303_);
v___x_1311_ = lean_int_add(v___x_1310_, v_nano_1304_);
lean_dec(v_nano_1304_);
lean_dec(v___x_1310_);
v___x_1312_ = lean_int_mul(v___x_1307_, v___x_1309_);
lean_dec(v___x_1307_);
v___x_1313_ = lean_int_add(v___x_1312_, v___x_1308_);
lean_dec(v___x_1308_);
lean_dec(v___x_1312_);
v___x_1314_ = lean_int_add(v___x_1311_, v___x_1313_);
lean_dec(v___x_1313_);
lean_dec(v___x_1311_);
v___x_1315_ = l_Std_Time_Duration_ofNanoseconds(v___x_1314_);
lean_dec(v___x_1314_);
v___x_1323_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1306_, v___x_1315_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref_known(v___x_1323_, 1);
v___x_1324_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1305_);
v___y_1317_ = v___x_1324_;
goto v___jp_1316_;
}
else
{
lean_object* v_a_1325_; 
v_a_1325_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1323_, 1);
v___y_1317_ = v_a_1325_;
goto v___jp_1316_;
}
v___jp_1316_:
{
lean_object* v___f_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
lean_inc_ref(v___x_1315_);
lean_inc_ref(v___y_1317_);
v___f_1318_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1318_, 0, v___y_1317_);
lean_closure_set(v___f_1318_, 1, v___x_1315_);
lean_closure_set(v___f_1318_, 2, v___x_1309_);
v___x_1319_ = lean_mk_thunk(v___f_1318_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 3, v___y_1317_);
lean_ctor_set(v___x_1298_, 1, v___x_1315_);
lean_ctor_set(v___x_1298_, 0, v___x_1319_);
v___x_1321_ = v___x_1298_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1322_, 2, v_rules_1296_);
lean_ctor_set(v_reuseFailAlloc_1322_, 3, v___y_1317_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subNanoseconds___boxed(lean_object* v_dt_1329_, lean_object* v_nanoseconds_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_dt_1329_, v_nanoseconds_1330_);
lean_dec(v_nanoseconds_1330_);
return v_res_1331_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_era(lean_object* v_date_1332_){
_start:
{
lean_object* v_date_1333_; lean_object* v___x_1334_; lean_object* v_date_1335_; lean_object* v_year_1336_; uint8_t v___x_1337_; 
v_date_1333_ = lean_ctor_get(v_date_1332_, 0);
v___x_1334_ = lean_thunk_get_own(v_date_1333_);
v_date_1335_ = lean_ctor_get(v___x_1334_, 0);
lean_inc_ref(v_date_1335_);
lean_dec(v___x_1334_);
v_year_1336_ = lean_ctor_get(v_date_1335_, 0);
lean_inc(v_year_1336_);
lean_dec_ref(v_date_1335_);
v___x_1337_ = l_Std_Time_Year_Offset_era(v_year_1336_);
lean_dec(v_year_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_era___boxed(lean_object* v_date_1338_){
_start:
{
uint8_t v_res_1339_; lean_object* v_r_1340_; 
v_res_1339_ = l_Std_Time_ZonedDateTime_era(v_date_1338_);
lean_dec_ref(v_date_1338_);
v_r_1340_ = lean_box(v_res_1339_);
return v_r_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday(lean_object* v_dt_1341_, uint8_t v_desiredWeekday_1342_){
_start:
{
lean_object* v_date_1343_; lean_object* v_rules_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1370_; 
v_date_1343_ = lean_ctor_get(v_dt_1341_, 0);
v_rules_1344_ = lean_ctor_get(v_dt_1341_, 2);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_dt_1341_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; lean_object* v_unused_1372_; 
v_unused_1371_ = lean_ctor_get(v_dt_1341_, 3);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_dt_1341_, 1);
lean_dec(v_unused_1372_);
v___x_1346_ = v_dt_1341_;
v_isShared_1347_ = v_isSharedCheck_1370_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_rules_1344_);
lean_inc(v_date_1343_);
lean_dec(v_dt_1341_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1370_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v_date_1348_; lean_object* v___x_1349_; lean_object* v_wt_1350_; lean_object* v_ltt_1351_; lean_object* v_tz_1352_; lean_object* v_offset_1353_; lean_object* v_second_1354_; lean_object* v_nano_1355_; lean_object* v___f_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v_date_1348_ = lean_thunk_get_own(v_date_1343_);
lean_dec_ref(v_date_1343_);
v___x_1349_ = l_Std_Time_PlainDateTime_withWeekday(v_date_1348_, v_desiredWeekday_1342_);
lean_inc_ref(v___x_1349_);
v_wt_1350_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1349_);
lean_inc_ref(v_rules_1344_);
v_ltt_1351_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1344_, v_wt_1350_);
v_tz_1352_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1351_);
lean_dec_ref(v_ltt_1351_);
v_offset_1353_ = lean_ctor_get(v_tz_1352_, 0);
lean_inc(v_offset_1353_);
v_second_1354_ = lean_ctor_get(v_wt_1350_, 0);
lean_inc(v_second_1354_);
v_nano_1355_ = lean_ctor_get(v_wt_1350_, 1);
lean_inc(v_nano_1355_);
lean_dec_ref(v_wt_1350_);
v___f_1356_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1356_, 0, v___x_1349_);
v___x_1357_ = lean_mk_thunk(v___f_1356_);
v___x_1358_ = lean_int_neg(v_offset_1353_);
lean_dec(v_offset_1353_);
v___x_1359_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1360_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1361_ = lean_int_mul(v_second_1354_, v___x_1360_);
lean_dec(v_second_1354_);
v___x_1362_ = lean_int_add(v___x_1361_, v_nano_1355_);
lean_dec(v_nano_1355_);
lean_dec(v___x_1361_);
v___x_1363_ = lean_int_mul(v___x_1358_, v___x_1360_);
lean_dec(v___x_1358_);
v___x_1364_ = lean_int_add(v___x_1363_, v___x_1359_);
lean_dec(v___x_1363_);
v___x_1365_ = lean_int_add(v___x_1362_, v___x_1364_);
lean_dec(v___x_1364_);
lean_dec(v___x_1362_);
v___x_1366_ = l_Std_Time_Duration_ofNanoseconds(v___x_1365_);
lean_dec(v___x_1365_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 3, v_tz_1352_);
lean_ctor_set(v___x_1346_, 1, v___x_1366_);
lean_ctor_set(v___x_1346_, 0, v___x_1357_);
v___x_1368_ = v___x_1346_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_rules_1344_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_tz_1352_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday___boxed(lean_object* v_dt_1373_, lean_object* v_desiredWeekday_1374_){
_start:
{
uint8_t v_desiredWeekday_boxed_1375_; lean_object* v_res_1376_; 
v_desiredWeekday_boxed_1375_ = lean_unbox(v_desiredWeekday_1374_);
v_res_1376_ = l_Std_Time_ZonedDateTime_withWeekday(v_dt_1373_, v_desiredWeekday_boxed_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysClip(lean_object* v_dt_1377_, lean_object* v_days_1378_){
_start:
{
lean_object* v_date_1379_; lean_object* v_rules_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1445_; 
v_date_1379_ = lean_ctor_get(v_dt_1377_, 0);
v_rules_1380_ = lean_ctor_get(v_dt_1377_, 2);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_dt_1377_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; lean_object* v_unused_1447_; 
v_unused_1446_ = lean_ctor_get(v_dt_1377_, 3);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_dt_1377_, 1);
lean_dec(v_unused_1447_);
v___x_1382_ = v_dt_1377_;
v_isShared_1383_ = v_isSharedCheck_1445_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_rules_1380_);
lean_inc(v_date_1379_);
lean_dec(v_dt_1377_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1445_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_date_1384_; lean_object* v___y_1386_; lean_object* v_date_1416_; lean_object* v_year_1417_; lean_object* v_month_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1443_; 
v_date_1384_ = lean_thunk_get_own(v_date_1379_);
lean_dec_ref(v_date_1379_);
v_date_1416_ = lean_ctor_get(v_date_1384_, 0);
lean_inc_ref(v_date_1416_);
v_year_1417_ = lean_ctor_get(v_date_1416_, 0);
v_month_1418_ = lean_ctor_get(v_date_1416_, 1);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_date_1416_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; 
v_unused_1444_ = lean_ctor_get(v_date_1416_, 2);
lean_dec(v_unused_1444_);
v___x_1420_ = v_date_1416_;
v_isShared_1421_ = v_isSharedCheck_1443_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_month_1418_);
lean_inc(v_year_1417_);
lean_dec(v_date_1416_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1443_;
goto v_resetjp_1419_;
}
v___jp_1385_:
{
lean_object* v_time_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1414_; 
v_time_1387_ = lean_ctor_get(v_date_1384_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_date_1384_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v_date_1384_, 0);
lean_dec(v_unused_1415_);
v___x_1389_ = v_date_1384_;
v_isShared_1390_ = v_isSharedCheck_1414_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_time_1387_);
lean_dec(v_date_1384_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1414_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___y_1386_);
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___y_1386_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_time_1387_);
v___x_1392_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v_wt_1393_; lean_object* v_ltt_1394_; lean_object* v_tz_1395_; lean_object* v_offset_1396_; lean_object* v_second_1397_; lean_object* v_nano_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
lean_inc_ref(v___x_1392_);
v_wt_1393_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1392_);
lean_inc_ref(v_rules_1380_);
v_ltt_1394_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1380_, v_wt_1393_);
v_tz_1395_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1394_);
lean_dec_ref(v_ltt_1394_);
v_offset_1396_ = lean_ctor_get(v_tz_1395_, 0);
lean_inc(v_offset_1396_);
v_second_1397_ = lean_ctor_get(v_wt_1393_, 0);
lean_inc(v_second_1397_);
v_nano_1398_ = lean_ctor_get(v_wt_1393_, 1);
lean_inc(v_nano_1398_);
lean_dec_ref(v_wt_1393_);
v___f_1399_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1399_, 0, v___x_1392_);
v___x_1400_ = lean_mk_thunk(v___f_1399_);
v___x_1401_ = lean_int_neg(v_offset_1396_);
lean_dec(v_offset_1396_);
v___x_1402_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1403_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1404_ = lean_int_mul(v_second_1397_, v___x_1403_);
lean_dec(v_second_1397_);
v___x_1405_ = lean_int_add(v___x_1404_, v_nano_1398_);
lean_dec(v_nano_1398_);
lean_dec(v___x_1404_);
v___x_1406_ = lean_int_mul(v___x_1401_, v___x_1403_);
lean_dec(v___x_1401_);
v___x_1407_ = lean_int_add(v___x_1406_, v___x_1402_);
lean_dec(v___x_1406_);
v___x_1408_ = lean_int_add(v___x_1405_, v___x_1407_);
lean_dec(v___x_1407_);
lean_dec(v___x_1405_);
v___x_1409_ = l_Std_Time_Duration_ofNanoseconds(v___x_1408_);
lean_dec(v___x_1408_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 3, v_tz_1395_);
lean_ctor_set(v___x_1382_, 1, v___x_1409_);
lean_ctor_set(v___x_1382_, 0, v___x_1400_);
v___x_1411_ = v___x_1382_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_rules_1380_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v_tz_1395_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
v_resetjp_1419_:
{
uint8_t v___y_1423_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; uint8_t v___x_1439_; 
v___x_1432_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_1433_ = lean_int_mod(v_year_1417_, v___x_1432_);
v___x_1434_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1439_ = lean_int_dec_eq(v___x_1433_, v___x_1434_);
lean_dec(v___x_1433_);
if (v___x_1439_ == 0)
{
v___y_1423_ = v___x_1439_;
goto v___jp_1422_;
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v___x_1440_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_1441_ = lean_int_mod(v_year_1417_, v___x_1440_);
v___x_1442_ = lean_int_dec_eq(v___x_1441_, v___x_1434_);
lean_dec(v___x_1441_);
if (v___x_1442_ == 0)
{
if (v___x_1439_ == 0)
{
goto v___jp_1435_;
}
else
{
v___y_1423_ = v___x_1439_;
goto v___jp_1422_;
}
}
else
{
goto v___jp_1435_;
}
}
v___jp_1422_:
{
lean_object* v_max_1424_; uint8_t v___x_1425_; 
v_max_1424_ = l_Std_Time_Month_Ordinal_days(v___y_1423_, v_month_1418_);
v___x_1425_ = lean_int_dec_lt(v_max_1424_, v_days_1378_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1427_; 
lean_dec(v_max_1424_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 2, v_days_1378_);
v___x_1427_ = v___x_1420_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_year_1417_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_month_1418_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_days_1378_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
v___y_1386_ = v___x_1427_;
goto v___jp_1385_;
}
}
else
{
lean_object* v___x_1430_; 
lean_dec(v_days_1378_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 2, v_max_1424_);
v___x_1430_ = v___x_1420_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_year_1417_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_month_1418_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_max_1424_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
v___y_1386_ = v___x_1430_;
goto v___jp_1385_;
}
}
}
v___jp_1435_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_1437_ = lean_int_mod(v_year_1417_, v___x_1436_);
v___x_1438_ = lean_int_dec_eq(v___x_1437_, v___x_1434_);
lean_dec(v___x_1437_);
v___y_1423_ = v___x_1438_;
goto v___jp_1422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysRollOver(lean_object* v_dt_1448_, lean_object* v_days_1449_){
_start:
{
lean_object* v_date_1450_; lean_object* v_rules_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1488_; 
v_date_1450_ = lean_ctor_get(v_dt_1448_, 0);
v_rules_1451_ = lean_ctor_get(v_dt_1448_, 2);
v_isSharedCheck_1488_ = !lean_is_exclusive(v_dt_1448_);
if (v_isSharedCheck_1488_ == 0)
{
lean_object* v_unused_1489_; lean_object* v_unused_1490_; 
v_unused_1489_ = lean_ctor_get(v_dt_1448_, 3);
lean_dec(v_unused_1489_);
v_unused_1490_ = lean_ctor_get(v_dt_1448_, 1);
lean_dec(v_unused_1490_);
v___x_1453_ = v_dt_1448_;
v_isShared_1454_ = v_isSharedCheck_1488_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_rules_1451_);
lean_inc(v_date_1450_);
lean_dec(v_dt_1448_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1488_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v_date_1455_; lean_object* v_date_1456_; lean_object* v_time_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1487_; 
v_date_1455_ = lean_thunk_get_own(v_date_1450_);
lean_dec_ref(v_date_1450_);
v_date_1456_ = lean_ctor_get(v_date_1455_, 0);
v_time_1457_ = lean_ctor_get(v_date_1455_, 1);
v_isSharedCheck_1487_ = !lean_is_exclusive(v_date_1455_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1459_ = v_date_1455_;
v_isShared_1460_ = v_isSharedCheck_1487_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_time_1457_);
lean_inc(v_date_1456_);
lean_dec(v_date_1455_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1487_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v_year_1461_; lean_object* v_month_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v_year_1461_ = lean_ctor_get(v_date_1456_, 0);
lean_inc(v_year_1461_);
v_month_1462_ = lean_ctor_get(v_date_1456_, 1);
lean_inc(v_month_1462_);
lean_dec_ref(v_date_1456_);
v___x_1463_ = l_Std_Time_PlainDate_rollOver(v_year_1461_, v_month_1462_, v_days_1449_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1463_);
v___x_1465_ = v___x_1459_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v_time_1457_);
v___x_1465_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v_wt_1466_; lean_object* v_ltt_1467_; lean_object* v_tz_1468_; lean_object* v_offset_1469_; lean_object* v_second_1470_; lean_object* v_nano_1471_; lean_object* v___f_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1484_; 
lean_inc_ref(v___x_1465_);
v_wt_1466_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1465_);
lean_inc_ref(v_rules_1451_);
v_ltt_1467_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1451_, v_wt_1466_);
v_tz_1468_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1467_);
lean_dec_ref(v_ltt_1467_);
v_offset_1469_ = lean_ctor_get(v_tz_1468_, 0);
lean_inc(v_offset_1469_);
v_second_1470_ = lean_ctor_get(v_wt_1466_, 0);
lean_inc(v_second_1470_);
v_nano_1471_ = lean_ctor_get(v_wt_1466_, 1);
lean_inc(v_nano_1471_);
lean_dec_ref(v_wt_1466_);
v___f_1472_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1472_, 0, v___x_1465_);
v___x_1473_ = lean_mk_thunk(v___f_1472_);
v___x_1474_ = lean_int_neg(v_offset_1469_);
lean_dec(v_offset_1469_);
v___x_1475_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1476_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1477_ = lean_int_mul(v_second_1470_, v___x_1476_);
lean_dec(v_second_1470_);
v___x_1478_ = lean_int_add(v___x_1477_, v_nano_1471_);
lean_dec(v_nano_1471_);
lean_dec(v___x_1477_);
v___x_1479_ = lean_int_mul(v___x_1474_, v___x_1476_);
lean_dec(v___x_1474_);
v___x_1480_ = lean_int_add(v___x_1479_, v___x_1475_);
lean_dec(v___x_1479_);
v___x_1481_ = lean_int_add(v___x_1478_, v___x_1480_);
lean_dec(v___x_1480_);
lean_dec(v___x_1478_);
v___x_1482_ = l_Std_Time_Duration_ofNanoseconds(v___x_1481_);
lean_dec(v___x_1481_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 3, v_tz_1468_);
lean_ctor_set(v___x_1453_, 1, v___x_1482_);
lean_ctor_set(v___x_1453_, 0, v___x_1473_);
v___x_1484_ = v___x_1453_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_rules_1451_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_tz_1468_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysRollOver___boxed(lean_object* v_dt_1491_, lean_object* v_days_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Std_Time_ZonedDateTime_withDaysRollOver(v_dt_1491_, v_days_1492_);
lean_dec(v_days_1492_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMonthClip(lean_object* v_dt_1494_, lean_object* v_month_1495_){
_start:
{
lean_object* v_date_1496_; lean_object* v_rules_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1562_; 
v_date_1496_ = lean_ctor_get(v_dt_1494_, 0);
v_rules_1497_ = lean_ctor_get(v_dt_1494_, 2);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_dt_1494_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; lean_object* v_unused_1564_; 
v_unused_1563_ = lean_ctor_get(v_dt_1494_, 3);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_dt_1494_, 1);
lean_dec(v_unused_1564_);
v___x_1499_ = v_dt_1494_;
v_isShared_1500_ = v_isSharedCheck_1562_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_rules_1497_);
lean_inc(v_date_1496_);
lean_dec(v_dt_1494_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1562_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_date_1501_; lean_object* v___y_1503_; lean_object* v_date_1533_; lean_object* v_year_1534_; lean_object* v_day_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1560_; 
v_date_1501_ = lean_thunk_get_own(v_date_1496_);
lean_dec_ref(v_date_1496_);
v_date_1533_ = lean_ctor_get(v_date_1501_, 0);
lean_inc_ref(v_date_1533_);
v_year_1534_ = lean_ctor_get(v_date_1533_, 0);
v_day_1535_ = lean_ctor_get(v_date_1533_, 2);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_date_1533_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_date_1533_, 1);
lean_dec(v_unused_1561_);
v___x_1537_ = v_date_1533_;
v_isShared_1538_ = v_isSharedCheck_1560_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_day_1535_);
lean_inc(v_year_1534_);
lean_dec(v_date_1533_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1560_;
goto v_resetjp_1536_;
}
v___jp_1502_:
{
lean_object* v_time_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1531_; 
v_time_1504_ = lean_ctor_get(v_date_1501_, 1);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_date_1501_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v_date_1501_, 0);
lean_dec(v_unused_1532_);
v___x_1506_ = v_date_1501_;
v_isShared_1507_ = v_isSharedCheck_1531_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_time_1504_);
lean_dec(v_date_1501_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1531_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v___y_1503_);
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___y_1503_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_time_1504_);
v___x_1509_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v_wt_1510_; lean_object* v_ltt_1511_; lean_object* v_tz_1512_; lean_object* v_offset_1513_; lean_object* v_second_1514_; lean_object* v_nano_1515_; lean_object* v___f_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_inc_ref(v___x_1509_);
v_wt_1510_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1509_);
lean_inc_ref(v_rules_1497_);
v_ltt_1511_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1497_, v_wt_1510_);
v_tz_1512_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1511_);
lean_dec_ref(v_ltt_1511_);
v_offset_1513_ = lean_ctor_get(v_tz_1512_, 0);
lean_inc(v_offset_1513_);
v_second_1514_ = lean_ctor_get(v_wt_1510_, 0);
lean_inc(v_second_1514_);
v_nano_1515_ = lean_ctor_get(v_wt_1510_, 1);
lean_inc(v_nano_1515_);
lean_dec_ref(v_wt_1510_);
v___f_1516_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1516_, 0, v___x_1509_);
v___x_1517_ = lean_mk_thunk(v___f_1516_);
v___x_1518_ = lean_int_neg(v_offset_1513_);
lean_dec(v_offset_1513_);
v___x_1519_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1520_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1521_ = lean_int_mul(v_second_1514_, v___x_1520_);
lean_dec(v_second_1514_);
v___x_1522_ = lean_int_add(v___x_1521_, v_nano_1515_);
lean_dec(v_nano_1515_);
lean_dec(v___x_1521_);
v___x_1523_ = lean_int_mul(v___x_1518_, v___x_1520_);
lean_dec(v___x_1518_);
v___x_1524_ = lean_int_add(v___x_1523_, v___x_1519_);
lean_dec(v___x_1523_);
v___x_1525_ = lean_int_add(v___x_1522_, v___x_1524_);
lean_dec(v___x_1524_);
lean_dec(v___x_1522_);
v___x_1526_ = l_Std_Time_Duration_ofNanoseconds(v___x_1525_);
lean_dec(v___x_1525_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 3, v_tz_1512_);
lean_ctor_set(v___x_1499_, 1, v___x_1526_);
lean_ctor_set(v___x_1499_, 0, v___x_1517_);
v___x_1528_ = v___x_1499_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_rules_1497_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_tz_1512_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
v_resetjp_1536_:
{
uint8_t v___y_1540_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1556_; 
v___x_1549_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_1550_ = lean_int_mod(v_year_1534_, v___x_1549_);
v___x_1551_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1556_ = lean_int_dec_eq(v___x_1550_, v___x_1551_);
lean_dec(v___x_1550_);
if (v___x_1556_ == 0)
{
v___y_1540_ = v___x_1556_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1557_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_1558_ = lean_int_mod(v_year_1534_, v___x_1557_);
v___x_1559_ = lean_int_dec_eq(v___x_1558_, v___x_1551_);
lean_dec(v___x_1558_);
if (v___x_1559_ == 0)
{
if (v___x_1556_ == 0)
{
goto v___jp_1552_;
}
else
{
v___y_1540_ = v___x_1556_;
goto v___jp_1539_;
}
}
else
{
goto v___jp_1552_;
}
}
v___jp_1539_:
{
lean_object* v_max_1541_; uint8_t v___x_1542_; 
v_max_1541_ = l_Std_Time_Month_Ordinal_days(v___y_1540_, v_month_1495_);
v___x_1542_ = lean_int_dec_lt(v_max_1541_, v_day_1535_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1544_; 
lean_dec(v_max_1541_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 1, v_month_1495_);
v___x_1544_ = v___x_1537_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_year_1534_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_month_1495_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_day_1535_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
v___y_1503_ = v___x_1544_;
goto v___jp_1502_;
}
}
else
{
lean_object* v___x_1547_; 
lean_dec(v_day_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 2, v_max_1541_);
lean_ctor_set(v___x_1537_, 1, v_month_1495_);
v___x_1547_ = v___x_1537_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_year_1534_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_month_1495_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_max_1541_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
v___y_1503_ = v___x_1547_;
goto v___jp_1502_;
}
}
}
v___jp_1552_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v___x_1553_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_1554_ = lean_int_mod(v_year_1534_, v___x_1553_);
v___x_1555_ = lean_int_dec_eq(v___x_1554_, v___x_1551_);
lean_dec(v___x_1554_);
v___y_1540_ = v___x_1555_;
goto v___jp_1539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMonthRollOver(lean_object* v_dt_1565_, lean_object* v_month_1566_){
_start:
{
lean_object* v_date_1567_; lean_object* v_rules_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1605_; 
v_date_1567_ = lean_ctor_get(v_dt_1565_, 0);
v_rules_1568_ = lean_ctor_get(v_dt_1565_, 2);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_dt_1565_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; 
v_unused_1606_ = lean_ctor_get(v_dt_1565_, 3);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_dt_1565_, 1);
lean_dec(v_unused_1607_);
v___x_1570_ = v_dt_1565_;
v_isShared_1571_ = v_isSharedCheck_1605_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_rules_1568_);
lean_inc(v_date_1567_);
lean_dec(v_dt_1565_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1605_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v_date_1572_; lean_object* v_date_1573_; lean_object* v_time_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1604_; 
v_date_1572_ = lean_thunk_get_own(v_date_1567_);
lean_dec_ref(v_date_1567_);
v_date_1573_ = lean_ctor_get(v_date_1572_, 0);
v_time_1574_ = lean_ctor_get(v_date_1572_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_date_1572_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1576_ = v_date_1572_;
v_isShared_1577_ = v_isSharedCheck_1604_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_time_1574_);
lean_inc(v_date_1573_);
lean_dec(v_date_1572_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1604_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_year_1578_; lean_object* v_day_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v_year_1578_ = lean_ctor_get(v_date_1573_, 0);
lean_inc(v_year_1578_);
v_day_1579_ = lean_ctor_get(v_date_1573_, 2);
lean_inc(v_day_1579_);
lean_dec_ref(v_date_1573_);
v___x_1580_ = l_Std_Time_PlainDate_rollOver(v_year_1578_, v_month_1566_, v_day_1579_);
lean_dec(v_day_1579_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1580_);
v___x_1582_ = v___x_1576_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1580_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_time_1574_);
v___x_1582_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v_wt_1583_; lean_object* v_ltt_1584_; lean_object* v_tz_1585_; lean_object* v_offset_1586_; lean_object* v_second_1587_; lean_object* v_nano_1588_; lean_object* v___f_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
lean_inc_ref(v___x_1582_);
v_wt_1583_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1582_);
lean_inc_ref(v_rules_1568_);
v_ltt_1584_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1568_, v_wt_1583_);
v_tz_1585_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1584_);
lean_dec_ref(v_ltt_1584_);
v_offset_1586_ = lean_ctor_get(v_tz_1585_, 0);
lean_inc(v_offset_1586_);
v_second_1587_ = lean_ctor_get(v_wt_1583_, 0);
lean_inc(v_second_1587_);
v_nano_1588_ = lean_ctor_get(v_wt_1583_, 1);
lean_inc(v_nano_1588_);
lean_dec_ref(v_wt_1583_);
v___f_1589_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1589_, 0, v___x_1582_);
v___x_1590_ = lean_mk_thunk(v___f_1589_);
v___x_1591_ = lean_int_neg(v_offset_1586_);
lean_dec(v_offset_1586_);
v___x_1592_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1593_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1594_ = lean_int_mul(v_second_1587_, v___x_1593_);
lean_dec(v_second_1587_);
v___x_1595_ = lean_int_add(v___x_1594_, v_nano_1588_);
lean_dec(v_nano_1588_);
lean_dec(v___x_1594_);
v___x_1596_ = lean_int_mul(v___x_1591_, v___x_1593_);
lean_dec(v___x_1591_);
v___x_1597_ = lean_int_add(v___x_1596_, v___x_1592_);
lean_dec(v___x_1596_);
v___x_1598_ = lean_int_add(v___x_1595_, v___x_1597_);
lean_dec(v___x_1597_);
lean_dec(v___x_1595_);
v___x_1599_ = l_Std_Time_Duration_ofNanoseconds(v___x_1598_);
lean_dec(v___x_1598_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 3, v_tz_1585_);
lean_ctor_set(v___x_1570_, 1, v___x_1599_);
lean_ctor_set(v___x_1570_, 0, v___x_1590_);
v___x_1601_ = v___x_1570_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_rules_1568_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_tz_1585_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withYearClip(lean_object* v_dt_1608_, lean_object* v_year_1609_){
_start:
{
lean_object* v_date_1610_; lean_object* v_rules_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1676_; 
v_date_1610_ = lean_ctor_get(v_dt_1608_, 0);
v_rules_1611_ = lean_ctor_get(v_dt_1608_, 2);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_dt_1608_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; lean_object* v_unused_1678_; 
v_unused_1677_ = lean_ctor_get(v_dt_1608_, 3);
lean_dec(v_unused_1677_);
v_unused_1678_ = lean_ctor_get(v_dt_1608_, 1);
lean_dec(v_unused_1678_);
v___x_1613_ = v_dt_1608_;
v_isShared_1614_ = v_isSharedCheck_1676_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_rules_1611_);
lean_inc(v_date_1610_);
lean_dec(v_dt_1608_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1676_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_date_1615_; lean_object* v___y_1617_; lean_object* v_date_1647_; lean_object* v_month_1648_; lean_object* v_day_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1674_; 
v_date_1615_ = lean_thunk_get_own(v_date_1610_);
lean_dec_ref(v_date_1610_);
v_date_1647_ = lean_ctor_get(v_date_1615_, 0);
lean_inc_ref(v_date_1647_);
v_month_1648_ = lean_ctor_get(v_date_1647_, 1);
v_day_1649_ = lean_ctor_get(v_date_1647_, 2);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_date_1647_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v_date_1647_, 0);
lean_dec(v_unused_1675_);
v___x_1651_ = v_date_1647_;
v_isShared_1652_ = v_isSharedCheck_1674_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_day_1649_);
lean_inc(v_month_1648_);
lean_dec(v_date_1647_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1674_;
goto v_resetjp_1650_;
}
v___jp_1616_:
{
lean_object* v_time_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1645_; 
v_time_1618_ = lean_ctor_get(v_date_1615_, 1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_date_1615_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v_date_1615_, 0);
lean_dec(v_unused_1646_);
v___x_1620_ = v_date_1615_;
v_isShared_1621_ = v_isSharedCheck_1645_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_time_1618_);
lean_dec(v_date_1615_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1645_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___y_1617_);
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___y_1617_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_time_1618_);
v___x_1623_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v_wt_1624_; lean_object* v_ltt_1625_; lean_object* v_tz_1626_; lean_object* v_offset_1627_; lean_object* v_second_1628_; lean_object* v_nano_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
lean_inc_ref(v___x_1623_);
v_wt_1624_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1623_);
lean_inc_ref(v_rules_1611_);
v_ltt_1625_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1611_, v_wt_1624_);
v_tz_1626_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1625_);
lean_dec_ref(v_ltt_1625_);
v_offset_1627_ = lean_ctor_get(v_tz_1626_, 0);
lean_inc(v_offset_1627_);
v_second_1628_ = lean_ctor_get(v_wt_1624_, 0);
lean_inc(v_second_1628_);
v_nano_1629_ = lean_ctor_get(v_wt_1624_, 1);
lean_inc(v_nano_1629_);
lean_dec_ref(v_wt_1624_);
v___f_1630_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1630_, 0, v___x_1623_);
v___x_1631_ = lean_mk_thunk(v___f_1630_);
v___x_1632_ = lean_int_neg(v_offset_1627_);
lean_dec(v_offset_1627_);
v___x_1633_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1634_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1635_ = lean_int_mul(v_second_1628_, v___x_1634_);
lean_dec(v_second_1628_);
v___x_1636_ = lean_int_add(v___x_1635_, v_nano_1629_);
lean_dec(v_nano_1629_);
lean_dec(v___x_1635_);
v___x_1637_ = lean_int_mul(v___x_1632_, v___x_1634_);
lean_dec(v___x_1632_);
v___x_1638_ = lean_int_add(v___x_1637_, v___x_1633_);
lean_dec(v___x_1637_);
v___x_1639_ = lean_int_add(v___x_1636_, v___x_1638_);
lean_dec(v___x_1638_);
lean_dec(v___x_1636_);
v___x_1640_ = l_Std_Time_Duration_ofNanoseconds(v___x_1639_);
lean_dec(v___x_1639_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 3, v_tz_1626_);
lean_ctor_set(v___x_1613_, 1, v___x_1640_);
lean_ctor_set(v___x_1613_, 0, v___x_1631_);
v___x_1642_ = v___x_1613_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_rules_1611_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_tz_1626_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
v_resetjp_1650_:
{
uint8_t v___y_1654_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1670_; 
v___x_1663_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_1664_ = lean_int_mod(v_year_1609_, v___x_1663_);
v___x_1665_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1670_ = lean_int_dec_eq(v___x_1664_, v___x_1665_);
lean_dec(v___x_1664_);
if (v___x_1670_ == 0)
{
v___y_1654_ = v___x_1670_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1671_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_1672_ = lean_int_mod(v_year_1609_, v___x_1671_);
v___x_1673_ = lean_int_dec_eq(v___x_1672_, v___x_1665_);
lean_dec(v___x_1672_);
if (v___x_1673_ == 0)
{
if (v___x_1670_ == 0)
{
goto v___jp_1666_;
}
else
{
v___y_1654_ = v___x_1670_;
goto v___jp_1653_;
}
}
else
{
goto v___jp_1666_;
}
}
v___jp_1653_:
{
lean_object* v_max_1655_; uint8_t v___x_1656_; 
v_max_1655_ = l_Std_Time_Month_Ordinal_days(v___y_1654_, v_month_1648_);
v___x_1656_ = lean_int_dec_lt(v_max_1655_, v_day_1649_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1658_; 
lean_dec(v_max_1655_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v_year_1609_);
v___x_1658_ = v___x_1651_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_year_1609_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_month_1648_);
lean_ctor_set(v_reuseFailAlloc_1659_, 2, v_day_1649_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
v___y_1617_ = v___x_1658_;
goto v___jp_1616_;
}
}
else
{
lean_object* v___x_1661_; 
lean_dec(v_day_1649_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 2, v_max_1655_);
lean_ctor_set(v___x_1651_, 0, v_year_1609_);
v___x_1661_ = v___x_1651_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_year_1609_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_month_1648_);
lean_ctor_set(v_reuseFailAlloc_1662_, 2, v_max_1655_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
v___y_1617_ = v___x_1661_;
goto v___jp_1616_;
}
}
}
v___jp_1666_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1667_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_1668_ = lean_int_mod(v_year_1609_, v___x_1667_);
v___x_1669_ = lean_int_dec_eq(v___x_1668_, v___x_1665_);
lean_dec(v___x_1668_);
v___y_1654_ = v___x_1669_;
goto v___jp_1653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withYearRollOver(lean_object* v_dt_1679_, lean_object* v_year_1680_){
_start:
{
lean_object* v_date_1681_; lean_object* v_rules_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1719_; 
v_date_1681_ = lean_ctor_get(v_dt_1679_, 0);
v_rules_1682_ = lean_ctor_get(v_dt_1679_, 2);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_dt_1679_);
if (v_isSharedCheck_1719_ == 0)
{
lean_object* v_unused_1720_; lean_object* v_unused_1721_; 
v_unused_1720_ = lean_ctor_get(v_dt_1679_, 3);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_dt_1679_, 1);
lean_dec(v_unused_1721_);
v___x_1684_ = v_dt_1679_;
v_isShared_1685_ = v_isSharedCheck_1719_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_rules_1682_);
lean_inc(v_date_1681_);
lean_dec(v_dt_1679_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1719_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v_date_1686_; lean_object* v_date_1687_; lean_object* v_time_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1718_; 
v_date_1686_ = lean_thunk_get_own(v_date_1681_);
lean_dec_ref(v_date_1681_);
v_date_1687_ = lean_ctor_get(v_date_1686_, 0);
v_time_1688_ = lean_ctor_get(v_date_1686_, 1);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_date_1686_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1690_ = v_date_1686_;
v_isShared_1691_ = v_isSharedCheck_1718_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_time_1688_);
lean_inc(v_date_1687_);
lean_dec(v_date_1686_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1718_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_month_1692_; lean_object* v_day_1693_; lean_object* v___x_1694_; lean_object* v___x_1696_; 
v_month_1692_ = lean_ctor_get(v_date_1687_, 1);
lean_inc(v_month_1692_);
v_day_1693_ = lean_ctor_get(v_date_1687_, 2);
lean_inc(v_day_1693_);
lean_dec_ref(v_date_1687_);
v___x_1694_ = l_Std_Time_PlainDate_rollOver(v_year_1680_, v_month_1692_, v_day_1693_);
lean_dec(v_day_1693_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1694_);
v___x_1696_ = v___x_1690_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_time_1688_);
v___x_1696_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v_wt_1697_; lean_object* v_ltt_1698_; lean_object* v_tz_1699_; lean_object* v_offset_1700_; lean_object* v_second_1701_; lean_object* v_nano_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_inc_ref(v___x_1696_);
v_wt_1697_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1696_);
lean_inc_ref(v_rules_1682_);
v_ltt_1698_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1682_, v_wt_1697_);
v_tz_1699_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1698_);
lean_dec_ref(v_ltt_1698_);
v_offset_1700_ = lean_ctor_get(v_tz_1699_, 0);
lean_inc(v_offset_1700_);
v_second_1701_ = lean_ctor_get(v_wt_1697_, 0);
lean_inc(v_second_1701_);
v_nano_1702_ = lean_ctor_get(v_wt_1697_, 1);
lean_inc(v_nano_1702_);
lean_dec_ref(v_wt_1697_);
v___f_1703_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1703_, 0, v___x_1696_);
v___x_1704_ = lean_mk_thunk(v___f_1703_);
v___x_1705_ = lean_int_neg(v_offset_1700_);
lean_dec(v_offset_1700_);
v___x_1706_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1707_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1708_ = lean_int_mul(v_second_1701_, v___x_1707_);
lean_dec(v_second_1701_);
v___x_1709_ = lean_int_add(v___x_1708_, v_nano_1702_);
lean_dec(v_nano_1702_);
lean_dec(v___x_1708_);
v___x_1710_ = lean_int_mul(v___x_1705_, v___x_1707_);
lean_dec(v___x_1705_);
v___x_1711_ = lean_int_add(v___x_1710_, v___x_1706_);
lean_dec(v___x_1710_);
v___x_1712_ = lean_int_add(v___x_1709_, v___x_1711_);
lean_dec(v___x_1711_);
lean_dec(v___x_1709_);
v___x_1713_ = l_Std_Time_Duration_ofNanoseconds(v___x_1712_);
lean_dec(v___x_1712_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 3, v_tz_1699_);
lean_ctor_set(v___x_1684_, 1, v___x_1713_);
lean_ctor_set(v___x_1684_, 0, v___x_1704_);
v___x_1715_ = v___x_1684_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_rules_1682_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_tz_1699_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withHours(lean_object* v_dt_1722_, lean_object* v_hour_1723_){
_start:
{
lean_object* v_date_1724_; lean_object* v_rules_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1770_; 
v_date_1724_ = lean_ctor_get(v_dt_1722_, 0);
v_rules_1725_ = lean_ctor_get(v_dt_1722_, 2);
v_isSharedCheck_1770_ = !lean_is_exclusive(v_dt_1722_);
if (v_isSharedCheck_1770_ == 0)
{
lean_object* v_unused_1771_; lean_object* v_unused_1772_; 
v_unused_1771_ = lean_ctor_get(v_dt_1722_, 3);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_dt_1722_, 1);
lean_dec(v_unused_1772_);
v___x_1727_ = v_dt_1722_;
v_isShared_1728_ = v_isSharedCheck_1770_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_rules_1725_);
lean_inc(v_date_1724_);
lean_dec(v_dt_1722_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1770_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_date_1729_; lean_object* v_time_1730_; lean_object* v_date_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1769_; 
v_date_1729_ = lean_thunk_get_own(v_date_1724_);
lean_dec_ref(v_date_1724_);
v_time_1730_ = lean_ctor_get(v_date_1729_, 1);
v_date_1731_ = lean_ctor_get(v_date_1729_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v_date_1729_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1733_ = v_date_1729_;
v_isShared_1734_ = v_isSharedCheck_1769_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_time_1730_);
lean_inc(v_date_1731_);
lean_dec(v_date_1729_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1769_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_minute_1735_; lean_object* v_second_1736_; lean_object* v_nanosecond_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1767_; 
v_minute_1735_ = lean_ctor_get(v_time_1730_, 1);
v_second_1736_ = lean_ctor_get(v_time_1730_, 2);
v_nanosecond_1737_ = lean_ctor_get(v_time_1730_, 3);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_time_1730_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; 
v_unused_1768_ = lean_ctor_get(v_time_1730_, 0);
lean_dec(v_unused_1768_);
v___x_1739_ = v_time_1730_;
v_isShared_1740_ = v_isSharedCheck_1767_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_nanosecond_1737_);
lean_inc(v_second_1736_);
lean_inc(v_minute_1735_);
lean_dec(v_time_1730_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1767_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 0, v_hour_1723_);
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_hour_1723_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_minute_1735_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v_second_1736_);
lean_ctor_set(v_reuseFailAlloc_1766_, 3, v_nanosecond_1737_);
v___x_1742_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1744_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v___x_1742_);
v___x_1744_ = v___x_1733_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_date_1731_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v_wt_1745_; lean_object* v_ltt_1746_; lean_object* v_tz_1747_; lean_object* v_offset_1748_; lean_object* v_second_1749_; lean_object* v_nano_1750_; lean_object* v___f_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1763_; 
lean_inc_ref(v___x_1744_);
v_wt_1745_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1744_);
lean_inc_ref(v_rules_1725_);
v_ltt_1746_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1725_, v_wt_1745_);
v_tz_1747_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1746_);
lean_dec_ref(v_ltt_1746_);
v_offset_1748_ = lean_ctor_get(v_tz_1747_, 0);
lean_inc(v_offset_1748_);
v_second_1749_ = lean_ctor_get(v_wt_1745_, 0);
lean_inc(v_second_1749_);
v_nano_1750_ = lean_ctor_get(v_wt_1745_, 1);
lean_inc(v_nano_1750_);
lean_dec_ref(v_wt_1745_);
v___f_1751_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1751_, 0, v___x_1744_);
v___x_1752_ = lean_mk_thunk(v___f_1751_);
v___x_1753_ = lean_int_neg(v_offset_1748_);
lean_dec(v_offset_1748_);
v___x_1754_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1755_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1756_ = lean_int_mul(v_second_1749_, v___x_1755_);
lean_dec(v_second_1749_);
v___x_1757_ = lean_int_add(v___x_1756_, v_nano_1750_);
lean_dec(v_nano_1750_);
lean_dec(v___x_1756_);
v___x_1758_ = lean_int_mul(v___x_1753_, v___x_1755_);
lean_dec(v___x_1753_);
v___x_1759_ = lean_int_add(v___x_1758_, v___x_1754_);
lean_dec(v___x_1758_);
v___x_1760_ = lean_int_add(v___x_1757_, v___x_1759_);
lean_dec(v___x_1759_);
lean_dec(v___x_1757_);
v___x_1761_ = l_Std_Time_Duration_ofNanoseconds(v___x_1760_);
lean_dec(v___x_1760_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 3, v_tz_1747_);
lean_ctor_set(v___x_1727_, 1, v___x_1761_);
lean_ctor_set(v___x_1727_, 0, v___x_1752_);
v___x_1763_ = v___x_1727_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1752_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_rules_1725_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_tz_1747_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMinutes(lean_object* v_dt_1773_, lean_object* v_minute_1774_){
_start:
{
lean_object* v_date_1775_; lean_object* v_rules_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1821_; 
v_date_1775_ = lean_ctor_get(v_dt_1773_, 0);
v_rules_1776_ = lean_ctor_get(v_dt_1773_, 2);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_dt_1773_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; lean_object* v_unused_1823_; 
v_unused_1822_ = lean_ctor_get(v_dt_1773_, 3);
lean_dec(v_unused_1822_);
v_unused_1823_ = lean_ctor_get(v_dt_1773_, 1);
lean_dec(v_unused_1823_);
v___x_1778_ = v_dt_1773_;
v_isShared_1779_ = v_isSharedCheck_1821_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_rules_1776_);
lean_inc(v_date_1775_);
lean_dec(v_dt_1773_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1821_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_date_1780_; lean_object* v_time_1781_; lean_object* v_date_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1820_; 
v_date_1780_ = lean_thunk_get_own(v_date_1775_);
lean_dec_ref(v_date_1775_);
v_time_1781_ = lean_ctor_get(v_date_1780_, 1);
v_date_1782_ = lean_ctor_get(v_date_1780_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_date_1780_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1784_ = v_date_1780_;
v_isShared_1785_ = v_isSharedCheck_1820_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_time_1781_);
lean_inc(v_date_1782_);
lean_dec(v_date_1780_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1820_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v_hour_1786_; lean_object* v_second_1787_; lean_object* v_nanosecond_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1818_; 
v_hour_1786_ = lean_ctor_get(v_time_1781_, 0);
v_second_1787_ = lean_ctor_get(v_time_1781_, 2);
v_nanosecond_1788_ = lean_ctor_get(v_time_1781_, 3);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_time_1781_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v_time_1781_, 1);
lean_dec(v_unused_1819_);
v___x_1790_ = v_time_1781_;
v_isShared_1791_ = v_isSharedCheck_1818_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_nanosecond_1788_);
lean_inc(v_second_1787_);
lean_inc(v_hour_1786_);
lean_dec(v_time_1781_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1818_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v_minute_1774_);
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_hour_1786_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_minute_1774_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_second_1787_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_nanosecond_1788_);
v___x_1793_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 1, v___x_1793_);
v___x_1795_ = v___x_1784_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_date_1782_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v_wt_1796_; lean_object* v_ltt_1797_; lean_object* v_tz_1798_; lean_object* v_offset_1799_; lean_object* v_second_1800_; lean_object* v_nano_1801_; lean_object* v___f_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
lean_inc_ref(v___x_1795_);
v_wt_1796_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1795_);
lean_inc_ref(v_rules_1776_);
v_ltt_1797_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1776_, v_wt_1796_);
v_tz_1798_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1797_);
lean_dec_ref(v_ltt_1797_);
v_offset_1799_ = lean_ctor_get(v_tz_1798_, 0);
lean_inc(v_offset_1799_);
v_second_1800_ = lean_ctor_get(v_wt_1796_, 0);
lean_inc(v_second_1800_);
v_nano_1801_ = lean_ctor_get(v_wt_1796_, 1);
lean_inc(v_nano_1801_);
lean_dec_ref(v_wt_1796_);
v___f_1802_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1802_, 0, v___x_1795_);
v___x_1803_ = lean_mk_thunk(v___f_1802_);
v___x_1804_ = lean_int_neg(v_offset_1799_);
lean_dec(v_offset_1799_);
v___x_1805_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1806_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1807_ = lean_int_mul(v_second_1800_, v___x_1806_);
lean_dec(v_second_1800_);
v___x_1808_ = lean_int_add(v___x_1807_, v_nano_1801_);
lean_dec(v_nano_1801_);
lean_dec(v___x_1807_);
v___x_1809_ = lean_int_mul(v___x_1804_, v___x_1806_);
lean_dec(v___x_1804_);
v___x_1810_ = lean_int_add(v___x_1809_, v___x_1805_);
lean_dec(v___x_1809_);
v___x_1811_ = lean_int_add(v___x_1808_, v___x_1810_);
lean_dec(v___x_1810_);
lean_dec(v___x_1808_);
v___x_1812_ = l_Std_Time_Duration_ofNanoseconds(v___x_1811_);
lean_dec(v___x_1811_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 3, v_tz_1798_);
lean_ctor_set(v___x_1778_, 1, v___x_1812_);
lean_ctor_set(v___x_1778_, 0, v___x_1803_);
v___x_1814_ = v___x_1778_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v_rules_1776_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v_tz_1798_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withSeconds(lean_object* v_dt_1824_, lean_object* v_second_1825_){
_start:
{
lean_object* v_date_1826_; lean_object* v_rules_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1872_; 
v_date_1826_ = lean_ctor_get(v_dt_1824_, 0);
v_rules_1827_ = lean_ctor_get(v_dt_1824_, 2);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_dt_1824_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; lean_object* v_unused_1874_; 
v_unused_1873_ = lean_ctor_get(v_dt_1824_, 3);
lean_dec(v_unused_1873_);
v_unused_1874_ = lean_ctor_get(v_dt_1824_, 1);
lean_dec(v_unused_1874_);
v___x_1829_ = v_dt_1824_;
v_isShared_1830_ = v_isSharedCheck_1872_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_rules_1827_);
lean_inc(v_date_1826_);
lean_dec(v_dt_1824_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1872_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_date_1831_; lean_object* v_time_1832_; lean_object* v_date_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1871_; 
v_date_1831_ = lean_thunk_get_own(v_date_1826_);
lean_dec_ref(v_date_1826_);
v_time_1832_ = lean_ctor_get(v_date_1831_, 1);
v_date_1833_ = lean_ctor_get(v_date_1831_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_date_1831_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1835_ = v_date_1831_;
v_isShared_1836_ = v_isSharedCheck_1871_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_time_1832_);
lean_inc(v_date_1833_);
lean_dec(v_date_1831_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1871_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_hour_1837_; lean_object* v_minute_1838_; lean_object* v_nanosecond_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1869_; 
v_hour_1837_ = lean_ctor_get(v_time_1832_, 0);
v_minute_1838_ = lean_ctor_get(v_time_1832_, 1);
v_nanosecond_1839_ = lean_ctor_get(v_time_1832_, 3);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_time_1832_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; 
v_unused_1870_ = lean_ctor_get(v_time_1832_, 2);
lean_dec(v_unused_1870_);
v___x_1841_ = v_time_1832_;
v_isShared_1842_ = v_isSharedCheck_1869_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_nanosecond_1839_);
lean_inc(v_minute_1838_);
lean_inc(v_hour_1837_);
lean_dec(v_time_1832_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1869_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 2, v_second_1825_);
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_hour_1837_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_minute_1838_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v_second_1825_);
lean_ctor_set(v_reuseFailAlloc_1868_, 3, v_nanosecond_1839_);
v___x_1844_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 1, v___x_1844_);
v___x_1846_ = v___x_1835_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_date_1833_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v_wt_1847_; lean_object* v_ltt_1848_; lean_object* v_tz_1849_; lean_object* v_offset_1850_; lean_object* v_second_1851_; lean_object* v_nano_1852_; lean_object* v___f_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
lean_inc_ref(v___x_1846_);
v_wt_1847_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1846_);
lean_inc_ref(v_rules_1827_);
v_ltt_1848_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1827_, v_wt_1847_);
v_tz_1849_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1848_);
lean_dec_ref(v_ltt_1848_);
v_offset_1850_ = lean_ctor_get(v_tz_1849_, 0);
lean_inc(v_offset_1850_);
v_second_1851_ = lean_ctor_get(v_wt_1847_, 0);
lean_inc(v_second_1851_);
v_nano_1852_ = lean_ctor_get(v_wt_1847_, 1);
lean_inc(v_nano_1852_);
lean_dec_ref(v_wt_1847_);
v___f_1853_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1853_, 0, v___x_1846_);
v___x_1854_ = lean_mk_thunk(v___f_1853_);
v___x_1855_ = lean_int_neg(v_offset_1850_);
lean_dec(v_offset_1850_);
v___x_1856_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1857_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1858_ = lean_int_mul(v_second_1851_, v___x_1857_);
lean_dec(v_second_1851_);
v___x_1859_ = lean_int_add(v___x_1858_, v_nano_1852_);
lean_dec(v_nano_1852_);
lean_dec(v___x_1858_);
v___x_1860_ = lean_int_mul(v___x_1855_, v___x_1857_);
lean_dec(v___x_1855_);
v___x_1861_ = lean_int_add(v___x_1860_, v___x_1856_);
lean_dec(v___x_1860_);
v___x_1862_ = lean_int_add(v___x_1859_, v___x_1861_);
lean_dec(v___x_1861_);
lean_dec(v___x_1859_);
v___x_1863_ = l_Std_Time_Duration_ofNanoseconds(v___x_1862_);
lean_dec(v___x_1862_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 3, v_tz_1849_);
lean_ctor_set(v___x_1829_, 1, v___x_1863_);
lean_ctor_set(v___x_1829_, 0, v___x_1854_);
v___x_1865_ = v___x_1829_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_rules_1827_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_tz_1849_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_unsigned_to_nat(1000u);
v___x_1876_ = lean_nat_to_int(v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds(lean_object* v_dt_1877_, lean_object* v_millis_1878_){
_start:
{
lean_object* v_date_1879_; lean_object* v_rules_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1930_; 
v_date_1879_ = lean_ctor_get(v_dt_1877_, 0);
v_rules_1880_ = lean_ctor_get(v_dt_1877_, 2);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_dt_1877_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; lean_object* v_unused_1932_; 
v_unused_1931_ = lean_ctor_get(v_dt_1877_, 3);
lean_dec(v_unused_1931_);
v_unused_1932_ = lean_ctor_get(v_dt_1877_, 1);
lean_dec(v_unused_1932_);
v___x_1882_ = v_dt_1877_;
v_isShared_1883_ = v_isSharedCheck_1930_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_rules_1880_);
lean_inc(v_date_1879_);
lean_dec(v_dt_1877_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1930_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_date_1884_; lean_object* v_time_1885_; lean_object* v_date_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1929_; 
v_date_1884_ = lean_thunk_get_own(v_date_1879_);
lean_dec_ref(v_date_1879_);
v_time_1885_ = lean_ctor_get(v_date_1884_, 1);
v_date_1886_ = lean_ctor_get(v_date_1884_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_date_1884_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1888_ = v_date_1884_;
v_isShared_1889_ = v_isSharedCheck_1929_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_time_1885_);
lean_inc(v_date_1886_);
lean_dec(v_date_1884_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1929_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_hour_1890_; lean_object* v_minute_1891_; lean_object* v_second_1892_; lean_object* v_nanosecond_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1928_; 
v_hour_1890_ = lean_ctor_get(v_time_1885_, 0);
v_minute_1891_ = lean_ctor_get(v_time_1885_, 1);
v_second_1892_ = lean_ctor_get(v_time_1885_, 2);
v_nanosecond_1893_ = lean_ctor_get(v_time_1885_, 3);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_time_1885_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1895_ = v_time_1885_;
v_isShared_1896_ = v_isSharedCheck_1928_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_nanosecond_1893_);
lean_inc(v_second_1892_);
lean_inc(v_minute_1891_);
lean_inc(v_hour_1890_);
lean_dec(v_time_1885_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1928_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1897_ = lean_obj_once(&l_Std_Time_ZonedDateTime_withMilliseconds___closed__0, &l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0);
v___x_1898_ = lean_int_emod(v_nanosecond_1893_, v___x_1897_);
lean_dec(v_nanosecond_1893_);
v___x_1899_ = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
v___x_1900_ = lean_int_mul(v_millis_1878_, v___x_1899_);
v___x_1901_ = lean_int_add(v___x_1900_, v___x_1898_);
lean_dec(v___x_1898_);
lean_dec(v___x_1900_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 3, v___x_1901_);
v___x_1903_ = v___x_1895_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_hour_1890_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_minute_1891_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_second_1892_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1905_; 
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v___x_1903_);
v___x_1905_ = v___x_1888_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_date_1886_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v_wt_1906_; lean_object* v_ltt_1907_; lean_object* v_tz_1908_; lean_object* v_offset_1909_; lean_object* v_second_1910_; lean_object* v_nano_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
lean_inc_ref(v___x_1905_);
v_wt_1906_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1905_);
lean_inc_ref(v_rules_1880_);
v_ltt_1907_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1880_, v_wt_1906_);
v_tz_1908_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1907_);
lean_dec_ref(v_ltt_1907_);
v_offset_1909_ = lean_ctor_get(v_tz_1908_, 0);
lean_inc(v_offset_1909_);
v_second_1910_ = lean_ctor_get(v_wt_1906_, 0);
lean_inc(v_second_1910_);
v_nano_1911_ = lean_ctor_get(v_wt_1906_, 1);
lean_inc(v_nano_1911_);
lean_dec_ref(v_wt_1906_);
v___f_1912_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1912_, 0, v___x_1905_);
v___x_1913_ = lean_mk_thunk(v___f_1912_);
v___x_1914_ = lean_int_neg(v_offset_1909_);
lean_dec(v_offset_1909_);
v___x_1915_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1916_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1917_ = lean_int_mul(v_second_1910_, v___x_1916_);
lean_dec(v_second_1910_);
v___x_1918_ = lean_int_add(v___x_1917_, v_nano_1911_);
lean_dec(v_nano_1911_);
lean_dec(v___x_1917_);
v___x_1919_ = lean_int_mul(v___x_1914_, v___x_1916_);
lean_dec(v___x_1914_);
v___x_1920_ = lean_int_add(v___x_1919_, v___x_1915_);
lean_dec(v___x_1919_);
v___x_1921_ = lean_int_add(v___x_1918_, v___x_1920_);
lean_dec(v___x_1920_);
lean_dec(v___x_1918_);
v___x_1922_ = l_Std_Time_Duration_ofNanoseconds(v___x_1921_);
lean_dec(v___x_1921_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 3, v_tz_1908_);
lean_ctor_set(v___x_1882_, 1, v___x_1922_);
lean_ctor_set(v___x_1882_, 0, v___x_1913_);
v___x_1924_ = v___x_1882_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_rules_1880_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v_tz_1908_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds___boxed(lean_object* v_dt_1933_, lean_object* v_millis_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Std_Time_ZonedDateTime_withMilliseconds(v_dt_1933_, v_millis_1934_);
lean_dec(v_millis_1934_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withNanoseconds(lean_object* v_dt_1936_, lean_object* v_nano_1937_){
_start:
{
lean_object* v_date_1938_; lean_object* v_rules_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1984_; 
v_date_1938_ = lean_ctor_get(v_dt_1936_, 0);
v_rules_1939_ = lean_ctor_get(v_dt_1936_, 2);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_dt_1936_);
if (v_isSharedCheck_1984_ == 0)
{
lean_object* v_unused_1985_; lean_object* v_unused_1986_; 
v_unused_1985_ = lean_ctor_get(v_dt_1936_, 3);
lean_dec(v_unused_1985_);
v_unused_1986_ = lean_ctor_get(v_dt_1936_, 1);
lean_dec(v_unused_1986_);
v___x_1941_ = v_dt_1936_;
v_isShared_1942_ = v_isSharedCheck_1984_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_rules_1939_);
lean_inc(v_date_1938_);
lean_dec(v_dt_1936_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1984_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v_date_1943_; lean_object* v_time_1944_; lean_object* v_date_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1983_; 
v_date_1943_ = lean_thunk_get_own(v_date_1938_);
lean_dec_ref(v_date_1938_);
v_time_1944_ = lean_ctor_get(v_date_1943_, 1);
v_date_1945_ = lean_ctor_get(v_date_1943_, 0);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_date_1943_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1947_ = v_date_1943_;
v_isShared_1948_ = v_isSharedCheck_1983_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_time_1944_);
lean_inc(v_date_1945_);
lean_dec(v_date_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1983_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v_hour_1949_; lean_object* v_minute_1950_; lean_object* v_second_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1981_; 
v_hour_1949_ = lean_ctor_get(v_time_1944_, 0);
v_minute_1950_ = lean_ctor_get(v_time_1944_, 1);
v_second_1951_ = lean_ctor_get(v_time_1944_, 2);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_time_1944_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v_time_1944_, 3);
lean_dec(v_unused_1982_);
v___x_1953_ = v_time_1944_;
v_isShared_1954_ = v_isSharedCheck_1981_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_second_1951_);
lean_inc(v_minute_1950_);
lean_inc(v_hour_1949_);
lean_dec(v_time_1944_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1981_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 3, v_nano_1937_);
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v_hour_1949_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_minute_1950_);
lean_ctor_set(v_reuseFailAlloc_1980_, 2, v_second_1951_);
lean_ctor_set(v_reuseFailAlloc_1980_, 3, v_nano_1937_);
v___x_1956_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1958_; 
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 1, v___x_1956_);
v___x_1958_ = v___x_1947_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_date_1945_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v_wt_1959_; lean_object* v_ltt_1960_; lean_object* v_tz_1961_; lean_object* v_offset_1962_; lean_object* v_second_1963_; lean_object* v_nano_1964_; lean_object* v___f_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_inc_ref(v___x_1958_);
v_wt_1959_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1958_);
lean_inc_ref(v_rules_1939_);
v_ltt_1960_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1939_, v_wt_1959_);
v_tz_1961_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1960_);
lean_dec_ref(v_ltt_1960_);
v_offset_1962_ = lean_ctor_get(v_tz_1961_, 0);
lean_inc(v_offset_1962_);
v_second_1963_ = lean_ctor_get(v_wt_1959_, 0);
lean_inc(v_second_1963_);
v_nano_1964_ = lean_ctor_get(v_wt_1959_, 1);
lean_inc(v_nano_1964_);
lean_dec_ref(v_wt_1959_);
v___f_1965_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1965_, 0, v___x_1958_);
v___x_1966_ = lean_mk_thunk(v___f_1965_);
v___x_1967_ = lean_int_neg(v_offset_1962_);
lean_dec(v_offset_1962_);
v___x_1968_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1969_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_1970_ = lean_int_mul(v_second_1963_, v___x_1969_);
lean_dec(v_second_1963_);
v___x_1971_ = lean_int_add(v___x_1970_, v_nano_1964_);
lean_dec(v_nano_1964_);
lean_dec(v___x_1970_);
v___x_1972_ = lean_int_mul(v___x_1967_, v___x_1969_);
lean_dec(v___x_1967_);
v___x_1973_ = lean_int_add(v___x_1972_, v___x_1968_);
lean_dec(v___x_1972_);
v___x_1974_ = lean_int_add(v___x_1971_, v___x_1973_);
lean_dec(v___x_1973_);
lean_dec(v___x_1971_);
v___x_1975_ = l_Std_Time_Duration_ofNanoseconds(v___x_1974_);
lean_dec(v___x_1974_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 3, v_tz_1961_);
lean_ctor_set(v___x_1941_, 1, v___x_1975_);
lean_ctor_set(v___x_1941_, 0, v___x_1966_);
v___x_1977_ = v___x_1941_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_rules_1939_);
lean_ctor_set(v_reuseFailAlloc_1978_, 3, v_tz_1961_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_inLeapYear(lean_object* v_date_1987_){
_start:
{
lean_object* v_date_1988_; lean_object* v___x_1989_; lean_object* v_date_1990_; lean_object* v_year_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1999_; 
v_date_1988_ = lean_ctor_get(v_date_1987_, 0);
v___x_1989_ = lean_thunk_get_own(v_date_1988_);
v_date_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc_ref(v_date_1990_);
lean_dec(v___x_1989_);
v_year_1991_ = lean_ctor_get(v_date_1990_, 0);
lean_inc(v_year_1991_);
lean_dec_ref(v_date_1990_);
v___x_1992_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_1993_ = lean_int_mod(v_year_1991_, v___x_1992_);
v___x_1994_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1999_ = lean_int_dec_eq(v___x_1993_, v___x_1994_);
lean_dec(v___x_1993_);
if (v___x_1999_ == 0)
{
lean_dec(v_year_1991_);
return v___x_1999_;
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2000_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_2001_ = lean_int_mod(v_year_1991_, v___x_2000_);
v___x_2002_ = lean_int_dec_eq(v___x_2001_, v___x_1994_);
lean_dec(v___x_2001_);
if (v___x_2002_ == 0)
{
if (v___x_1999_ == 0)
{
goto v___jp_1995_;
}
else
{
lean_dec(v_year_1991_);
return v___x_1999_;
}
}
else
{
goto v___jp_1995_;
}
}
v___jp_1995_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_1997_ = lean_int_mod(v_year_1991_, v___x_1996_);
lean_dec(v_year_1991_);
v___x_1998_ = lean_int_dec_eq(v___x_1997_, v___x_1994_);
lean_dec(v___x_1997_);
return v___x_1998_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_inLeapYear___boxed(lean_object* v_date_2003_){
_start:
{
uint8_t v_res_2004_; lean_object* v_r_2005_; 
v_res_2004_ = l_Std_Time_ZonedDateTime_inLeapYear(v_date_2003_);
lean_dec_ref(v_date_2003_);
v_r_2005_ = lean_box(v_res_2004_);
return v_r_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toEpochDay(lean_object* v_date_2006_){
_start:
{
lean_object* v_date_2007_; lean_object* v___x_2008_; lean_object* v_date_2009_; lean_object* v___x_2010_; 
v_date_2007_ = lean_ctor_get(v_date_2006_, 0);
v___x_2008_ = lean_thunk_get_own(v_date_2007_);
v_date_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc_ref(v_date_2009_);
lean_dec(v___x_2008_);
v___x_2010_ = l_Std_Time_PlainDate_toEpochDay(v_date_2009_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toEpochDay___boxed(lean_object* v_date_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_Std_Time_ZonedDateTime_toEpochDay(v_date_2011_);
lean_dec_ref(v_date_2011_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofEpochDay(lean_object* v_days_2013_, lean_object* v_time_2014_, lean_object* v_zt_2015_){
_start:
{
lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v_wt_2018_; lean_object* v_ltt_2019_; lean_object* v_tz_2020_; lean_object* v_offset_2021_; lean_object* v_second_2022_; lean_object* v_nano_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2016_ = l_Std_Time_PlainDate_ofEpochDay(v_days_2013_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
lean_ctor_set(v___x_2017_, 1, v_time_2014_);
lean_inc_ref(v___x_2017_);
v_wt_2018_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2017_);
lean_inc_ref(v_zt_2015_);
v_ltt_2019_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zt_2015_, v_wt_2018_);
v_tz_2020_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_2019_);
lean_dec_ref(v_ltt_2019_);
v_offset_2021_ = lean_ctor_get(v_tz_2020_, 0);
lean_inc(v_offset_2021_);
v_second_2022_ = lean_ctor_get(v_wt_2018_, 0);
lean_inc(v_second_2022_);
v_nano_2023_ = lean_ctor_get(v_wt_2018_, 1);
lean_inc(v_nano_2023_);
lean_dec_ref(v_wt_2018_);
v___f_2024_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2024_, 0, v___x_2017_);
v___x_2025_ = lean_mk_thunk(v___f_2024_);
v___x_2026_ = lean_int_neg(v_offset_2021_);
lean_dec(v_offset_2021_);
v___x_2027_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_2028_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_2029_ = lean_int_mul(v_second_2022_, v___x_2028_);
lean_dec(v_second_2022_);
v___x_2030_ = lean_int_add(v___x_2029_, v_nano_2023_);
lean_dec(v_nano_2023_);
lean_dec(v___x_2029_);
v___x_2031_ = lean_int_mul(v___x_2026_, v___x_2028_);
lean_dec(v___x_2026_);
v___x_2032_ = lean_int_add(v___x_2031_, v___x_2027_);
lean_dec(v___x_2031_);
v___x_2033_ = lean_int_add(v___x_2030_, v___x_2032_);
lean_dec(v___x_2032_);
lean_dec(v___x_2030_);
v___x_2034_ = l_Std_Time_Duration_ofNanoseconds(v___x_2033_);
lean_dec(v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2025_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
lean_ctor_set(v___x_2035_, 2, v_zt_2015_);
lean_ctor_set(v___x_2035_, 3, v_tz_2020_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofEpochDay___boxed(lean_object* v_days_2036_, lean_object* v_time_2037_, lean_object* v_zt_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Std_Time_ZonedDateTime_ofEpochDay(v_days_2036_, v_time_2037_, v_zt_2038_);
lean_dec(v_days_2036_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(lean_object* v_x_2068_, lean_object* v_y_2069_){
_start:
{
lean_object* v_timestamp_2070_; lean_object* v_timestamp_2071_; lean_object* v_second_2072_; lean_object* v_nano_2073_; lean_object* v_second_2074_; lean_object* v_nano_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_timestamp_2070_ = lean_ctor_get(v_y_2069_, 1);
v_timestamp_2071_ = lean_ctor_get(v_x_2068_, 1);
v_second_2072_ = lean_ctor_get(v_timestamp_2070_, 0);
v_nano_2073_ = lean_ctor_get(v_timestamp_2070_, 1);
v_second_2074_ = lean_ctor_get(v_timestamp_2071_, 0);
v_nano_2075_ = lean_ctor_get(v_timestamp_2071_, 1);
v___x_2076_ = lean_int_neg(v_second_2072_);
v___x_2077_ = lean_int_neg(v_nano_2073_);
v___x_2078_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_2079_ = lean_int_mul(v_second_2074_, v___x_2078_);
v___x_2080_ = lean_int_add(v___x_2079_, v_nano_2075_);
lean_dec(v___x_2079_);
v___x_2081_ = lean_int_mul(v___x_2076_, v___x_2078_);
lean_dec(v___x_2076_);
v___x_2082_ = lean_int_add(v___x_2081_, v___x_2077_);
lean_dec(v___x_2077_);
lean_dec(v___x_2081_);
v___x_2083_ = lean_int_add(v___x_2080_, v___x_2082_);
lean_dec(v___x_2082_);
lean_dec(v___x_2080_);
v___x_2084_ = l_Std_Time_Duration_ofNanoseconds(v___x_2083_);
lean_dec(v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed(lean_object* v_x_2085_, lean_object* v_y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(v_x_2085_, v_y_2086_);
lean_dec_ref(v_y_2086_);
lean_dec_ref(v_x_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(lean_object* v_x_2090_, lean_object* v_y_2091_){
_start:
{
lean_object* v_second_2092_; lean_object* v_nano_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v_nanos_2096_; lean_object* v___x_2097_; 
v_second_2092_ = lean_ctor_get(v_y_2091_, 0);
v_nano_2093_ = lean_ctor_get(v_y_2091_, 1);
v___x_2094_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_2095_ = lean_int_mul(v_second_2092_, v___x_2094_);
v_nanos_2096_ = lean_int_add(v___x_2095_, v_nano_2093_);
lean_dec(v___x_2095_);
v___x_2097_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_x_2090_, v_nanos_2096_);
lean_dec(v_nanos_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_2098_, lean_object* v_y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(v_x_2098_, v_y_2099_);
lean_dec_ref(v_y_2099_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(lean_object* v_x_2103_, lean_object* v_y_2104_){
_start:
{
lean_object* v_second_2105_; lean_object* v_nano_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v_nanos_2109_; lean_object* v___x_2110_; 
v_second_2105_ = lean_ctor_get(v_y_2104_, 0);
v_nano_2106_ = lean_ctor_get(v_y_2104_, 1);
v___x_2107_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__1);
v___x_2108_ = lean_int_mul(v_second_2105_, v___x_2107_);
v_nanos_2109_ = lean_int_add(v___x_2108_, v_nano_2106_);
lean_dec(v___x_2108_);
v___x_2110_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_x_2103_, v_nanos_2109_);
lean_dec(v_nanos_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed(lean_object* v_x_2111_, lean_object* v_y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(v_x_2111_, v_y_2112_);
lean_dec_ref(v_y_2112_);
return v_res_2113_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_DateTime(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedZonedDateTime___private__1 = _init_l_Std_Time_instInhabitedZonedDateTime___private__1();
lean_mark_persistent(l_Std_Time_instInhabitedZonedDateTime___private__1);
l_Std_Time_instInhabitedZonedDateTime = _init_l_Std_Time_instInhabitedZonedDateTime();
lean_mark_persistent(l_Std_Time_instInhabitedZonedDateTime);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_DateTime(uint8_t builtin);
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_ZonedDateTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_ZonedDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_ZonedDateTime(builtin);
}
#ifdef __cplusplus
}
#endif

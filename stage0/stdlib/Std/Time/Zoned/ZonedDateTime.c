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
extern lean_object* l_Std_Time_instInhabitedPlainDateTime_default;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0 = (const lean_object*)&l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0_value;
lean_object* lean_mk_thunk(lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1;
extern lean_object* l_Std_Time_instInhabitedTimeZone_default;
extern lean_object* l_Std_Time_TimeZone_instInhabitedZoneRules_default;
extern lean_object* l_Std_Time_instInhabitedTimestamp_default;
static lean_once_cell_t l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedZonedDateTime;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0;
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0;
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1;
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0;
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1;
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC(lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
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
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset___boxed(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_weekday(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekday___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_dayOfYear___closed__0;
static lean_once_cell_t l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_dayOfYear___closed__1;
static lean_once_cell_t l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_dayOfYear___closed__2;
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear___boxed(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear___boxed(lean_object*);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth___boxed(lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth___boxed(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter___boxed(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
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
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_era___boxed(lean_object*);
lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysClip(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
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
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_inLeapYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_inLeapYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDaysSinceUNIXEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDaysSinceUNIXEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofDaysSinceUNIXEpoch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofDaysSinceUNIXEpoch___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedZonedDateTime___private__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_instInhabitedPlainDateTime_default;
return x_2;
}
}
static lean_object* _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Time_instInhabitedZonedDateTime___private__1___closed__0));
x_2 = lean_mk_thunk(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_Time_instInhabitedTimeZone_default;
x_2 = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
x_3 = l_Std_Time_instInhabitedTimestamp_default;
x_4 = lean_obj_once(&l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1, &l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1_once, _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__1);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Std_Time_instInhabitedZonedDateTime___private__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2, &l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2_once, _init_l_Std_Time_instInhabitedZonedDateTime___private__1___closed__2);
return x_1;
}
}
static lean_object* _init_l_Std_Time_instInhabitedZonedDateTime(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Time_instInhabitedZonedDateTime___private__1;
return x_1;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_10 = l_Std_Time_TimeZone_Transition_timezoneAt(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_10);
x_11 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_8);
x_3 = x_11;
goto block_7;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_3 = x_12;
goto block_7;
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_mk_thunk(x_4);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_3);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_6 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_int_mul(x_2, x_3);
x_10 = l_Std_Time_Duration_ofNanoseconds(x_9);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_int_mul(x_7, x_3);
lean_dec(x_7);
x_14 = lean_int_add(x_13, x_8);
lean_dec(x_8);
lean_dec(x_13);
x_15 = lean_int_mul(x_11, x_3);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_int_dec_le(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_22; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_3 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_28 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_28, 0, x_25);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_28, x_27, x_29);
if (lean_obj_tag(x_30) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_array_fget_borrowed(x_27, x_31);
x_33 = lean_ctor_get(x_32, 0);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_sub(x_31, x_34);
lean_dec(x_31);
x_36 = lean_array_fget_borrowed(x_27, x_35);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 1);
x_38 = lean_ctor_get(x_37, 0);
x_39 = lean_nat_abs(x_38);
x_40 = lean_nat_to_int(x_39);
x_41 = lean_int_sub(x_33, x_40);
lean_dec(x_40);
x_42 = lean_int_dec_lt(x_25, x_41);
lean_dec(x_41);
lean_dec(x_25);
if (x_42 == 0)
{
lean_inc(x_32);
x_22 = x_32;
goto block_24;
}
else
{
lean_inc(x_36);
x_22 = x_36;
goto block_24;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_30);
lean_dec(x_25);
x_43 = lean_array_get_size(x_27);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_43, x_44);
x_46 = lean_nat_dec_lt(x_45, x_43);
if (x_46 == 0)
{
lean_dec(x_45);
lean_inc_ref(x_26);
x_4 = x_26;
goto block_21;
}
else
{
lean_object* x_47; 
x_47 = lean_array_fget_borrowed(x_27, x_45);
lean_dec(x_45);
lean_inc(x_47);
x_22 = x_47;
goto block_24;
}
}
block_21:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_4);
lean_dec_ref(x_4);
x_8 = l_Std_Time_TimeZone_toSeconds(x_7);
x_9 = lean_int_neg(x_8);
x_10 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_11 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_12 = lean_int_mul(x_5, x_11);
lean_dec(x_5);
x_13 = lean_int_add(x_12, x_6);
lean_dec(x_6);
lean_dec(x_12);
x_14 = lean_int_mul(x_9, x_11);
lean_dec(x_9);
x_15 = lean_int_add(x_14, x_10);
lean_dec(x_14);
x_16 = lean_int_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = l_Std_Time_Duration_ofNanoseconds(x_16);
lean_dec(x_16);
lean_inc_ref(x_17);
x_18 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_18, 0, x_17);
lean_closure_set(x_18, 1, x_8);
lean_closure_set(x_18, 2, x_11);
x_19 = lean_mk_thunk(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_2);
lean_ctor_set(x_20, 3, x_7);
return x_20;
}
block_24:
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_23);
lean_dec_ref(x_22);
x_4 = x_23;
goto block_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = 0;
x_8 = 1;
lean_inc_ref(x_4);
lean_inc_ref(x_5);
lean_inc(x_3);
x_9 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 2, x_8);
x_10 = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
lean_inc_ref(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_inc_ref(x_1);
x_17 = l_Std_Time_TimeZone_Transition_timezoneAt(x_10, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_9);
lean_dec_ref(x_9);
x_12 = x_18;
goto block_16;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_9);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_12 = x_19;
goto block_16;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_1);
x_13 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed), 3, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_mk_thunk(x_13);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_ofTimestampWithZone(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0);
x_3 = lean_nat_sub(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0);
x_2 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1);
x_2 = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
x_3 = lean_array_fget(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_33; lean_object* x_36; lean_object* x_37; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_7 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = 0;
x_10 = 1;
lean_inc_ref(x_4);
lean_inc_ref(x_5);
lean_inc(x_3);
x_11 = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_6);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 1, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*3 + 2, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
lean_inc_ref(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_8);
x_36 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_8);
x_37 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_36, x_13, x_12);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec_ref(x_11);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_array_fget(x_13, x_38);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_sub(x_38, x_41);
lean_dec(x_38);
x_43 = lean_array_fget(x_13, x_42);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 1);
x_45 = lean_ctor_get(x_44, 0);
x_46 = lean_nat_abs(x_45);
x_47 = lean_nat_to_int(x_46);
x_48 = lean_int_sub(x_40, x_47);
lean_dec(x_47);
x_49 = lean_int_dec_lt(x_8, x_48);
lean_dec(x_48);
lean_dec(x_8);
if (x_49 == 0)
{
lean_dec(x_43);
x_33 = x_39;
goto block_35;
}
else
{
lean_dec(x_39);
x_33 = x_43;
goto block_35;
}
}
else
{
uint8_t x_50; 
lean_dec(x_37);
lean_dec(x_8);
x_50 = lean_uint8_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2);
if (x_50 == 0)
{
x_15 = x_11;
goto block_32;
}
else
{
lean_object* x_51; 
lean_dec_ref(x_11);
x_51 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3);
x_33 = x_51;
goto block_35;
}
}
block_32:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_7, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec_ref(x_7);
x_18 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_15);
lean_dec_ref(x_15);
x_19 = l_Std_Time_TimeZone_toSeconds(x_18);
x_20 = lean_int_neg(x_19);
x_21 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_22 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_23 = lean_int_mul(x_16, x_22);
lean_dec(x_16);
x_24 = lean_int_add(x_23, x_17);
lean_dec(x_17);
lean_dec(x_23);
x_25 = lean_int_mul(x_20, x_22);
lean_dec(x_20);
x_26 = lean_int_add(x_25, x_21);
lean_dec(x_25);
x_27 = lean_int_add(x_24, x_26);
lean_dec(x_26);
lean_dec(x_24);
x_28 = l_Std_Time_Duration_ofNanoseconds(x_27);
lean_dec(x_27);
lean_inc_ref(x_28);
x_29 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_29, 0, x_28);
lean_closure_set(x_29, 1, x_19);
lean_closure_set(x_29, 2, x_22);
x_30 = lean_mk_thunk(x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_14);
lean_ctor_set(x_31, 3, x_18);
return x_31;
}
block_35:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_33);
x_15 = x_34;
goto block_32;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_toTimestamp(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_19; 
x_3 = lean_ctor_get(x_1, 1);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 3);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_4 = x_1;
x_5 = x_19;
goto block_18;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_6; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_15 = l_Std_Time_TimeZone_Transition_timezoneAt(x_14, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_13);
x_6 = x_16;
goto block_12;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
x_6 = x_17;
goto block_12;
}
block_12:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_6);
lean_inc_ref(x_3);
x_7 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_mk_thunk(x_7);
if (x_5 == 0)
{
lean_ctor_set(x_4, 3, x_6);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 0, x_8);
x_9 = x_4;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_2);
lean_ctor_set(x_11, 3, x_6);
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
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_1);
lean_inc_ref(x_5);
x_11 = l_Std_Time_TimeZone_Transition_timezoneAt(x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec_ref(x_11);
x_12 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_3);
x_6 = x_12;
goto block_10;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_6 = x_13;
goto block_10;
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = lean_mk_thunk(x_7);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_6);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDateTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDateTime___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_toPlainDateTime(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_ZonedDateTime_toDateTime___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_4 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_mk_thunk(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_time(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_time___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_time(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_year(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_year___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_year(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_month(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_month___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_month(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_day(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_day___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_day(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_hour(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_hour___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_hour(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_minute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_minute___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_minute(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_second(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_second___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_second(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_millisecond___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 3);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
x_7 = lean_int_ediv(x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_millisecond(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_nanosecond(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_offset(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_weekday(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_weekday(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekday___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_ZonedDateTime_weekday(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(400u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(100u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_28; 
x_2 = lean_ctor_get(x_1, 0);
x_18 = lean_thunk_get_own(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
x_22 = lean_int_mod(x_20, x_21);
x_23 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
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
x_29 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
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
x_24 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
x_25 = lean_int_mod(x_20, x_24);
lean_dec(x_20);
x_26 = lean_int_dec_eq(x_25, x_23);
lean_dec(x_25);
x_3 = x_26;
goto block_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_dayOfYear(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_weekOfYear(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_weekOfYear(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = l_Std_Time_PlainDateTime_weekOfMonth(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_weekOfMonth(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_alignedWeekOfMonth(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_alignedWeekOfMonth(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_quarter(x_4);
lean_dec_ref(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_quarter(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_34; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_1, 0);
lean_dec(x_36);
x_5 = x_1;
x_6 = x_34;
goto block_33;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_32; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
x_10 = x_7;
x_11 = x_32;
goto block_31;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_15 = lean_int_add(x_14, x_2);
lean_dec(x_14);
x_16 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_15);
lean_dec(x_15);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_16);
x_17 = x_10;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_9);
x_17 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_18; lean_object* x_19; lean_object* x_26; 
x_18 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_17);
lean_inc_ref(x_18);
x_26 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec_ref(x_26);
x_27 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_19 = x_27;
goto block_25;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_19 = x_28;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_19);
lean_inc_ref(x_18);
x_20 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_mk_thunk(x_20);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_19);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_21);
x_22 = x_5;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set(x_24, 3, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addDays(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subDays(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_35; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 3);
lean_dec(x_36);
x_37 = lean_ctor_get(x_1, 0);
lean_dec(x_37);
x_5 = x_1;
x_6 = x_35;
goto block_34;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_33; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
x_10 = x_7;
x_11 = x_33;
goto block_32;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_int_neg(x_2);
x_15 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_16 = lean_int_add(x_15, x_14);
lean_dec(x_14);
lean_dec(x_15);
x_17 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_16);
lean_dec(x_16);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_17);
x_18 = x_10;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_9);
x_18 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_19; lean_object* x_20; lean_object* x_27; 
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
lean_inc_ref(x_19);
x_27 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
x_28 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_20 = x_28;
goto block_26;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_20 = x_29;
goto block_26;
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_20);
lean_inc_ref(x_19);
x_21 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_mk_thunk(x_21);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_20);
lean_ctor_set(x_5, 1, x_19);
lean_ctor_set(x_5, 0, x_22);
x_23 = x_5;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subDays___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subDays(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addWeeks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_36; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_1, 3);
lean_dec(x_37);
x_38 = lean_ctor_get(x_1, 0);
lean_dec(x_38);
x_5 = x_1;
x_6 = x_36;
goto block_35;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_34; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
x_10 = x_7;
x_11 = x_34;
goto block_33;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_15 = lean_obj_once(&l_Std_Time_ZonedDateTime_addWeeks___closed__0, &l_Std_Time_ZonedDateTime_addWeeks___closed__0_once, _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0);
x_16 = lean_int_mul(x_2, x_15);
x_17 = lean_int_add(x_14, x_16);
lean_dec(x_16);
lean_dec(x_14);
x_18 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_17);
lean_dec(x_17);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_18);
x_19 = x_10;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_9);
x_19 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_20; lean_object* x_21; lean_object* x_28; 
x_20 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_19);
lean_inc_ref(x_20);
x_28 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_dec_ref(x_28);
x_29 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_21 = x_29;
goto block_27;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
x_21 = x_30;
goto block_27;
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc_ref(x_21);
lean_inc_ref(x_20);
x_22 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
x_23 = lean_mk_thunk(x_22);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_21);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_23);
x_24 = x_5;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 3, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addWeeks___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addWeeks(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subWeeks(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_37; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_1, 3);
lean_dec(x_38);
x_39 = lean_ctor_get(x_1, 0);
lean_dec(x_39);
x_5 = x_1;
x_6 = x_37;
goto block_36;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_35; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
x_10 = x_7;
x_11 = x_35;
goto block_34;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_int_neg(x_2);
x_15 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_8);
x_16 = lean_obj_once(&l_Std_Time_ZonedDateTime_addWeeks___closed__0, &l_Std_Time_ZonedDateTime_addWeeks___closed__0_once, _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0);
x_17 = lean_int_mul(x_14, x_16);
lean_dec(x_14);
x_18 = lean_int_add(x_15, x_17);
lean_dec(x_17);
lean_dec(x_15);
x_19 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_18);
lean_dec(x_18);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_19);
x_20 = x_10;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_9);
x_20 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_21; lean_object* x_22; lean_object* x_29; 
x_21 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_20);
lean_inc_ref(x_21);
x_29 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_21);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec_ref(x_29);
x_30 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_22 = x_30;
goto block_28;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec_ref(x_29);
x_22 = x_31;
goto block_28;
}
block_28:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_22);
lean_inc_ref(x_21);
x_23 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
x_24 = lean_mk_thunk(x_23);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_22);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_24);
x_25 = x_5;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_4);
lean_ctor_set(x_27, 3, x_22);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subWeeks___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subWeeks(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_23; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_1, 1);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_5 = x_1;
x_6 = x_23;
goto block_22;
}
else
{
lean_inc(x_3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_4);
x_10 = l_Std_Time_PlainDateTime_addMonthsClip(x_9, x_2);
x_11 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_10);
lean_inc_ref(x_11);
x_19 = l_Std_Time_TimeZone_Transition_timezoneAt(x_8, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_19);
x_20 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_7);
x_12 = x_20;
goto block_18;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_12 = x_21;
goto block_18;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_mk_thunk(x_13);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_12);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_14);
x_15 = x_5;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addMonthsClip(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_33; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_1, 3);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
x_5 = x_1;
x_6 = x_33;
goto block_32;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_31; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
x_10 = x_7;
x_11 = x_31;
goto block_30;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_int_neg(x_2);
x_15 = l_Std_Time_PlainDate_addMonthsClip(x_8, x_14);
lean_dec(x_14);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_15);
x_16 = x_10;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_9);
x_16 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_17; lean_object* x_18; lean_object* x_25; 
x_17 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_16);
lean_inc_ref(x_17);
x_25 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_18 = x_26;
goto block_24;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec_ref(x_25);
x_18 = x_27;
goto block_24;
}
block_24:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc_ref(x_18);
lean_inc_ref(x_17);
x_19 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_mk_thunk(x_19);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_18);
lean_ctor_set(x_5, 1, x_17);
lean_ctor_set(x_5, 0, x_20);
x_21 = x_5;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set(x_23, 3, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subMonthsClip(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_23; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_1, 1);
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 3);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 0);
lean_dec(x_25);
x_5 = x_1;
x_6 = x_23;
goto block_22;
}
else
{
lean_inc(x_3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_4);
x_10 = l_Std_Time_PlainDateTime_addMonthsRollOver(x_9, x_2);
x_11 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_10);
lean_inc_ref(x_11);
x_19 = l_Std_Time_TimeZone_Transition_timezoneAt(x_8, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_19);
x_20 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_7);
x_12 = x_20;
goto block_18;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_12 = x_21;
goto block_18;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_mk_thunk(x_13);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_12);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_14);
x_15 = x_5;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_3);
lean_ctor_set(x_17, 3, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addMonthsRollOver(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_33; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_1, 3);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
x_5 = x_1;
x_6 = x_33;
goto block_32;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_31; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
x_10 = x_7;
x_11 = x_31;
goto block_30;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_int_neg(x_2);
x_15 = l_Std_Time_PlainDate_addMonthsRollOver(x_8, x_14);
lean_dec(x_14);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_15);
x_16 = x_10;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_9);
x_16 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_17; lean_object* x_18; lean_object* x_25; 
x_17 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_16);
lean_inc_ref(x_17);
x_25 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_18 = x_26;
goto block_24;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec_ref(x_25);
x_18 = x_27;
goto block_24;
}
block_24:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc_ref(x_18);
lean_inc_ref(x_17);
x_19 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_mk_thunk(x_19);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_18);
lean_ctor_set(x_5, 1, x_17);
lean_ctor_set(x_5, 0, x_20);
x_21 = x_5;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_4);
lean_ctor_set(x_23, 3, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subMonthsRollOver(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_34; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_1, 0);
lean_dec(x_36);
x_5 = x_1;
x_6 = x_34;
goto block_33;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_32; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
x_10 = x_7;
x_11 = x_32;
goto block_31;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
x_15 = lean_int_mul(x_2, x_14);
x_16 = l_Std_Time_PlainDate_addMonthsRollOver(x_8, x_15);
lean_dec(x_15);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_16);
x_17 = x_10;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_9);
x_17 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_18; lean_object* x_19; lean_object* x_26; 
x_18 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_17);
lean_inc_ref(x_18);
x_26 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec_ref(x_26);
x_27 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_19 = x_27;
goto block_25;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_19 = x_28;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_19);
lean_inc_ref(x_18);
x_20 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_mk_thunk(x_20);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_19);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_21);
x_22 = x_5;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set(x_24, 3, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addYearsRollOver(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_34; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 3);
lean_dec(x_35);
x_36 = lean_ctor_get(x_1, 0);
lean_dec(x_36);
x_5 = x_1;
x_6 = x_34;
goto block_33;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_32; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
x_10 = x_7;
x_11 = x_32;
goto block_31;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
x_15 = lean_int_mul(x_2, x_14);
x_16 = l_Std_Time_PlainDate_addMonthsClip(x_8, x_15);
lean_dec(x_15);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_16);
x_17 = x_10;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_9);
x_17 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_18; lean_object* x_19; lean_object* x_26; 
x_18 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_17);
lean_inc_ref(x_18);
x_26 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_18);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec_ref(x_26);
x_27 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_19 = x_27;
goto block_25;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec_ref(x_26);
x_19 = x_28;
goto block_25;
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc_ref(x_19);
lean_inc_ref(x_18);
x_20 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_mk_thunk(x_20);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_19);
lean_ctor_set(x_5, 1, x_18);
lean_ctor_set(x_5, 0, x_21);
x_22 = x_5;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set(x_24, 3, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addYearsClip(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_35; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 3);
lean_dec(x_36);
x_37 = lean_ctor_get(x_1, 0);
lean_dec(x_37);
x_5 = x_1;
x_6 = x_35;
goto block_34;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_33; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
x_10 = x_7;
x_11 = x_33;
goto block_32;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
x_15 = lean_int_mul(x_2, x_14);
x_16 = lean_int_neg(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_PlainDate_addMonthsClip(x_8, x_16);
lean_dec(x_16);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_17);
x_18 = x_10;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_9);
x_18 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_19; lean_object* x_20; lean_object* x_27; 
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
lean_inc_ref(x_19);
x_27 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
x_28 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_20 = x_28;
goto block_26;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_20 = x_29;
goto block_26;
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_20);
lean_inc_ref(x_19);
x_21 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_mk_thunk(x_21);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_20);
lean_ctor_set(x_5, 1, x_19);
lean_ctor_set(x_5, 0, x_22);
x_23 = x_5;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsClip___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subYearsClip(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_35; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_35 = !lean_is_exclusive(x_1);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 3);
lean_dec(x_36);
x_37 = lean_ctor_get(x_1, 0);
lean_dec(x_37);
x_5 = x_1;
x_6 = x_35;
goto block_34;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_33; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
x_10 = x_7;
x_11 = x_33;
goto block_32;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
x_15 = lean_int_mul(x_2, x_14);
x_16 = lean_int_neg(x_15);
lean_dec(x_15);
x_17 = l_Std_Time_PlainDate_addMonthsRollOver(x_8, x_16);
lean_dec(x_16);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_17);
x_18 = x_10;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_17);
lean_ctor_set(x_31, 1, x_9);
x_18 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_19; lean_object* x_20; lean_object* x_27; 
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
lean_inc_ref(x_19);
x_27 = l_Std_Time_TimeZone_Transition_timezoneAt(x_13, x_19);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec_ref(x_27);
x_28 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_12);
x_20 = x_28;
goto block_26;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_20 = x_29;
goto block_26;
}
block_26:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc_ref(x_20);
lean_inc_ref(x_19);
x_21 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(x_21, 0, x_19);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_mk_thunk(x_21);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_20);
lean_ctor_set(x_5, 1, x_19);
lean_ctor_set(x_5, 0, x_22);
x_23 = x_5;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subYearsRollOver(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_1);
x_6 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = l_Std_Time_TimeZone_toSeconds(x_2);
x_10 = lean_int_mul(x_9, x_3);
lean_dec(x_9);
x_11 = l_Std_Time_Duration_ofNanoseconds(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_int_mul(x_7, x_3);
lean_dec(x_7);
x_15 = lean_int_add(x_14, x_8);
lean_dec(x_8);
lean_dec(x_14);
x_16 = lean_int_mul(x_12, x_3);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Time_ZonedDateTime_addHours___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addHours___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_cstr_to_nat("3600000000000");
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_38; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_1, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_1, 0);
lean_dec(x_40);
x_5 = x_1;
x_6 = x_38;
goto block_37;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_obj_once(&l_Std_Time_ZonedDateTime_addHours___closed__0, &l_Std_Time_ZonedDateTime_addHours___closed__0_once, _init_l_Std_Time_ZonedDateTime_addHours___closed__0);
x_12 = lean_int_mul(x_2, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_19 = lean_int_mul(x_9, x_18);
lean_dec(x_9);
x_20 = lean_int_add(x_19, x_10);
lean_dec(x_10);
lean_dec(x_19);
x_21 = lean_int_mul(x_14, x_18);
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
lean_inc_ref(x_26);
x_34 = l_Std_Time_TimeZone_Transition_timezoneAt(x_17, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec_ref(x_34);
x_35 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_16);
x_27 = x_35;
goto block_33;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_27 = x_36;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_27);
lean_inc_ref(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_18);
x_29 = lean_mk_thunk(x_28);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_27);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_29);
x_30 = x_5;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_4);
lean_ctor_set(x_32, 3, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addHours(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subHours(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_39; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_39 = !lean_is_exclusive(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_1, 0);
lean_dec(x_41);
x_5 = x_1;
x_6 = x_39;
goto block_38;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_35; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_2);
x_12 = lean_obj_once(&l_Std_Time_ZonedDateTime_addHours___closed__0, &l_Std_Time_ZonedDateTime_addHours___closed__0_once, _init_l_Std_Time_ZonedDateTime_addHours___closed__0);
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_20 = lean_int_mul(x_9, x_19);
lean_dec(x_9);
x_21 = lean_int_add(x_20, x_10);
lean_dec(x_10);
lean_dec(x_20);
x_22 = lean_int_mul(x_15, x_19);
lean_dec(x_15);
x_23 = lean_int_add(x_22, x_16);
lean_dec(x_16);
lean_dec(x_22);
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_Time_Duration_ofNanoseconds(x_24);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_25);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
lean_inc_ref(x_27);
x_35 = l_Std_Time_TimeZone_Transition_timezoneAt(x_18, x_27);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_17);
x_28 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
x_28 = x_37;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_28);
lean_inc_ref(x_27);
x_29 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
lean_closure_set(x_29, 2, x_19);
x_30 = lean_mk_thunk(x_29);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_28);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_30);
x_31 = x_5;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 3, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subHours___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subHours(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_cstr_to_nat("60000000000");
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMinutes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_38; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_1, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_1, 0);
lean_dec(x_40);
x_5 = x_1;
x_6 = x_38;
goto block_37;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_obj_once(&l_Std_Time_ZonedDateTime_addMinutes___closed__0, &l_Std_Time_ZonedDateTime_addMinutes___closed__0_once, _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0);
x_12 = lean_int_mul(x_2, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_19 = lean_int_mul(x_9, x_18);
lean_dec(x_9);
x_20 = lean_int_add(x_19, x_10);
lean_dec(x_10);
lean_dec(x_19);
x_21 = lean_int_mul(x_14, x_18);
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
lean_inc_ref(x_26);
x_34 = l_Std_Time_TimeZone_Transition_timezoneAt(x_17, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec_ref(x_34);
x_35 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_16);
x_27 = x_35;
goto block_33;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_27 = x_36;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_27);
lean_inc_ref(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_18);
x_29 = lean_mk_thunk(x_28);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_27);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_29);
x_30 = x_5;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_4);
lean_ctor_set(x_32, 3, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMinutes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addMinutes(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMinutes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_39; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_39 = !lean_is_exclusive(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_1, 0);
lean_dec(x_41);
x_5 = x_1;
x_6 = x_39;
goto block_38;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_35; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_2);
x_12 = lean_obj_once(&l_Std_Time_ZonedDateTime_addMinutes___closed__0, &l_Std_Time_ZonedDateTime_addMinutes___closed__0_once, _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0);
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_20 = lean_int_mul(x_9, x_19);
lean_dec(x_9);
x_21 = lean_int_add(x_20, x_10);
lean_dec(x_10);
lean_dec(x_20);
x_22 = lean_int_mul(x_15, x_19);
lean_dec(x_15);
x_23 = lean_int_add(x_22, x_16);
lean_dec(x_16);
lean_dec(x_22);
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_Time_Duration_ofNanoseconds(x_24);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_25);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
lean_inc_ref(x_27);
x_35 = l_Std_Time_TimeZone_Transition_timezoneAt(x_18, x_27);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_17);
x_28 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
x_28 = x_37;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_28);
lean_inc_ref(x_27);
x_29 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
lean_closure_set(x_29, 2, x_19);
x_30 = lean_mk_thunk(x_29);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_28);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_30);
x_31 = x_5;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 3, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMinutes___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subMinutes(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_38; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_1, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_1, 0);
lean_dec(x_40);
x_5 = x_1;
x_6 = x_38;
goto block_37;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
x_12 = lean_int_mul(x_2, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_19 = lean_int_mul(x_9, x_18);
lean_dec(x_9);
x_20 = lean_int_add(x_19, x_10);
lean_dec(x_10);
lean_dec(x_19);
x_21 = lean_int_mul(x_14, x_18);
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
lean_inc_ref(x_26);
x_34 = l_Std_Time_TimeZone_Transition_timezoneAt(x_17, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec_ref(x_34);
x_35 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_16);
x_27 = x_35;
goto block_33;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_27 = x_36;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_27);
lean_inc_ref(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_18);
x_29 = lean_mk_thunk(x_28);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_27);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_29);
x_30 = x_5;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_4);
lean_ctor_set(x_32, 3, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addMilliseconds(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMilliseconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_39; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_39 = !lean_is_exclusive(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_1, 0);
lean_dec(x_41);
x_5 = x_1;
x_6 = x_39;
goto block_38;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_35; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_2);
x_12 = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_20 = lean_int_mul(x_9, x_19);
lean_dec(x_9);
x_21 = lean_int_add(x_20, x_10);
lean_dec(x_10);
lean_dec(x_20);
x_22 = lean_int_mul(x_15, x_19);
lean_dec(x_15);
x_23 = lean_int_add(x_22, x_16);
lean_dec(x_16);
lean_dec(x_22);
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
x_25 = l_Std_Time_Duration_ofNanoseconds(x_24);
lean_dec(x_24);
x_26 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_25);
x_27 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_26);
lean_inc_ref(x_27);
x_35 = l_Std_Time_TimeZone_Transition_timezoneAt(x_18, x_27);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
lean_dec_ref(x_35);
x_36 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_17);
x_28 = x_36;
goto block_34;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec_ref(x_35);
x_28 = x_37;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_28);
lean_inc_ref(x_27);
x_29 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_28);
lean_closure_set(x_29, 2, x_19);
x_30 = lean_mk_thunk(x_29);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_28);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_30);
x_31 = x_5;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 3, x_28);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMilliseconds___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subMilliseconds(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addSeconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_37; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_1, 3);
lean_dec(x_38);
x_39 = lean_ctor_get(x_1, 0);
lean_dec(x_39);
x_5 = x_1;
x_6 = x_37;
goto block_36;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_33; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_12 = lean_int_mul(x_2, x_11);
x_13 = l_Std_Time_Duration_ofNanoseconds(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_int_mul(x_9, x_11);
lean_dec(x_9);
x_19 = lean_int_add(x_18, x_10);
lean_dec(x_10);
lean_dec(x_18);
x_20 = lean_int_mul(x_14, x_11);
lean_dec(x_14);
x_21 = lean_int_add(x_20, x_15);
lean_dec(x_15);
lean_dec(x_20);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_Duration_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_23);
x_25 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_24);
lean_inc_ref(x_25);
x_33 = l_Std_Time_TimeZone_Transition_timezoneAt(x_17, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec_ref(x_33);
x_34 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_16);
x_26 = x_34;
goto block_32;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec_ref(x_33);
x_26 = x_35;
goto block_32;
}
block_32:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_26);
lean_inc_ref(x_25);
x_27 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
lean_closure_set(x_27, 2, x_11);
x_28 = lean_mk_thunk(x_27);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_26);
lean_ctor_set(x_5, 1, x_25);
lean_ctor_set(x_5, 0, x_28);
x_29 = x_5;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set(x_31, 3, x_26);
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
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addSeconds___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addSeconds(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subSeconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_38; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_1, 3);
lean_dec(x_39);
x_40 = lean_ctor_get(x_1, 0);
lean_dec(x_40);
x_5 = x_1;
x_6 = x_38;
goto block_37;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_34; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_2);
x_12 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_13 = lean_int_mul(x_11, x_12);
lean_dec(x_11);
x_14 = l_Std_Time_Duration_ofNanoseconds(x_13);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_int_mul(x_9, x_12);
lean_dec(x_9);
x_20 = lean_int_add(x_19, x_10);
lean_dec(x_10);
lean_dec(x_19);
x_21 = lean_int_mul(x_15, x_12);
lean_dec(x_15);
x_22 = lean_int_add(x_21, x_16);
lean_dec(x_16);
lean_dec(x_21);
x_23 = lean_int_add(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
x_24 = l_Std_Time_Duration_ofNanoseconds(x_23);
lean_dec(x_23);
x_25 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_24);
x_26 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_25);
lean_inc_ref(x_26);
x_34 = l_Std_Time_TimeZone_Transition_timezoneAt(x_18, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec_ref(x_34);
x_35 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_17);
x_27 = x_35;
goto block_33;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec_ref(x_34);
x_27 = x_36;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_27);
lean_inc_ref(x_26);
x_28 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_12);
x_29 = lean_mk_thunk(x_28);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_27);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_29);
x_30 = x_5;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_4);
lean_ctor_set(x_32, 3, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subSeconds___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subSeconds(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addNanoseconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_36; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_36 = !lean_is_exclusive(x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_1, 3);
lean_dec(x_37);
x_38 = lean_ctor_get(x_1, 0);
lean_dec(x_38);
x_5 = x_1;
x_6 = x_36;
goto block_35;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_32; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Std_Time_Duration_ofNanoseconds(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_17 = lean_int_mul(x_9, x_16);
lean_dec(x_9);
x_18 = lean_int_add(x_17, x_10);
lean_dec(x_10);
lean_dec(x_17);
x_19 = lean_int_mul(x_12, x_16);
lean_dec(x_12);
x_20 = lean_int_add(x_19, x_13);
lean_dec(x_13);
lean_dec(x_19);
x_21 = lean_int_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Std_Time_Duration_ofNanoseconds(x_21);
lean_dec(x_21);
x_23 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_22);
x_24 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_23);
lean_inc_ref(x_24);
x_32 = l_Std_Time_TimeZone_Transition_timezoneAt(x_15, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec_ref(x_32);
x_33 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_14);
x_25 = x_33;
goto block_31;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec_ref(x_32);
x_25 = x_34;
goto block_31;
}
block_31:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_inc_ref(x_25);
lean_inc_ref(x_24);
x_26 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_25);
lean_closure_set(x_26, 2, x_16);
x_27 = lean_mk_thunk(x_26);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_25);
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_27);
x_28 = x_5;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_4);
lean_ctor_set(x_30, 3, x_25);
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
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addNanoseconds___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_addNanoseconds(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subNanoseconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_37; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_1, 3);
lean_dec(x_38);
x_39 = lean_ctor_get(x_1, 0);
lean_dec(x_39);
x_5 = x_1;
x_6 = x_37;
goto block_36;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_33; 
x_7 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_3);
x_8 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_int_neg(x_2);
x_12 = l_Std_Time_Duration_ofNanoseconds(x_11);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_18 = lean_int_mul(x_9, x_17);
lean_dec(x_9);
x_19 = lean_int_add(x_18, x_10);
lean_dec(x_10);
lean_dec(x_18);
x_20 = lean_int_mul(x_13, x_17);
lean_dec(x_13);
x_21 = lean_int_add(x_20, x_14);
lean_dec(x_14);
lean_dec(x_20);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_Duration_ofNanoseconds(x_22);
lean_dec(x_22);
x_24 = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(x_23);
x_25 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_24);
lean_inc_ref(x_25);
x_33 = l_Std_Time_TimeZone_Transition_timezoneAt(x_16, x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec_ref(x_33);
x_34 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_15);
x_26 = x_34;
goto block_32;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec_ref(x_33);
x_26 = x_35;
goto block_32;
}
block_32:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_26);
lean_inc_ref(x_25);
x_27 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(x_27, 0, x_25);
lean_closure_set(x_27, 1, x_26);
lean_closure_set(x_27, 2, x_17);
x_28 = lean_mk_thunk(x_27);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_26);
lean_ctor_set(x_5, 1, x_25);
lean_ctor_set(x_5, 0, x_28);
x_29 = x_5;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_4);
lean_ctor_set(x_31, 3, x_26);
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
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subNanoseconds___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_subNanoseconds(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_era(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_era___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_ZonedDateTime_era(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_57; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_57 = !lean_is_exclusive(x_1);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_1, 3);
lean_dec(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_dec(x_59);
x_5 = x_1;
x_6 = x_57;
goto block_56;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_30; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_7 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_8 = l_Std_Time_PlainDateTime_withWeekday(x_7, x_2);
x_9 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_8);
x_33 = lean_ctor_get(x_9, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
x_36 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_36, 0, x_33);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_36, x_35, x_37);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_array_fget_borrowed(x_35, x_39);
x_41 = lean_ctor_get(x_40, 0);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_39, x_42);
lean_dec(x_39);
x_44 = lean_array_fget_borrowed(x_35, x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_44, 1);
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_nat_abs(x_46);
x_48 = lean_nat_to_int(x_47);
x_49 = lean_int_sub(x_41, x_48);
lean_dec(x_48);
x_50 = lean_int_dec_lt(x_33, x_49);
lean_dec(x_49);
lean_dec(x_33);
if (x_50 == 0)
{
lean_inc(x_40);
x_30 = x_40;
goto block_32;
}
else
{
lean_inc(x_44);
x_30 = x_44;
goto block_32;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_38);
lean_dec(x_33);
x_51 = lean_array_get_size(x_35);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_51, x_52);
x_54 = lean_nat_dec_lt(x_53, x_51);
if (x_54 == 0)
{
lean_dec(x_53);
lean_inc_ref(x_34);
x_10 = x_34;
goto block_29;
}
else
{
lean_object* x_55; 
x_55 = lean_array_fget_borrowed(x_35, x_53);
lean_dec(x_53);
lean_inc(x_55);
x_30 = x_55;
goto block_32;
}
}
block_29:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_10);
lean_dec_ref(x_10);
x_14 = l_Std_Time_TimeZone_toSeconds(x_13);
x_15 = lean_int_neg(x_14);
x_16 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_17 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_18 = lean_int_mul(x_11, x_17);
lean_dec(x_11);
x_19 = lean_int_add(x_18, x_12);
lean_dec(x_12);
lean_dec(x_18);
x_20 = lean_int_mul(x_15, x_17);
lean_dec(x_15);
x_21 = lean_int_add(x_20, x_16);
lean_dec(x_20);
x_22 = lean_int_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = l_Std_Time_Duration_ofNanoseconds(x_22);
lean_dec(x_22);
lean_inc_ref(x_23);
x_24 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_14);
lean_closure_set(x_24, 2, x_17);
x_25 = lean_mk_thunk(x_24);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_13);
lean_ctor_set(x_5, 1, x_23);
lean_ctor_set(x_5, 0, x_25);
x_26 = x_5;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_4);
lean_ctor_set(x_28, 3, x_13);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
block_32:
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_30);
x_10 = x_31;
goto block_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = l_Std_Time_ZonedDateTime_withWeekday(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_98; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_98 = !lean_is_exclusive(x_1);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_1, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_1, 1);
lean_dec(x_100);
x_5 = x_1;
x_6 = x_98;
goto block_97;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_7; lean_object* x_8; lean_object* x_28; lean_object* x_29; lean_object* x_32; lean_object* x_33; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_95; 
x_32 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_68 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_68, 0);
x_70 = lean_ctor_get(x_68, 1);
x_95 = !lean_is_exclusive(x_68);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_68, 2);
lean_dec(x_96);
x_71 = x_68;
x_72 = x_95;
goto block_94;
}
else
{
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_68);
x_71 = lean_box(0);
x_72 = x_95;
goto block_94;
}
block_27:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_8);
lean_dec_ref(x_8);
x_12 = l_Std_Time_TimeZone_toSeconds(x_11);
x_13 = lean_int_neg(x_12);
x_14 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_15 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_16 = lean_int_mul(x_9, x_15);
lean_dec(x_9);
x_17 = lean_int_add(x_16, x_10);
lean_dec(x_10);
lean_dec(x_16);
x_18 = lean_int_mul(x_13, x_15);
lean_dec(x_13);
x_19 = lean_int_add(x_18, x_14);
lean_dec(x_18);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_Duration_ofNanoseconds(x_20);
lean_dec(x_20);
lean_inc_ref(x_21);
x_22 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_12);
lean_closure_set(x_22, 2, x_15);
x_23 = lean_mk_thunk(x_22);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_11);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_23);
x_24 = x_5;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 3, x_11);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
block_31:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_7 = x_28;
x_8 = x_30;
goto block_27;
}
block_67:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_65; 
x_34 = lean_ctor_get(x_32, 1);
x_65 = !lean_is_exclusive(x_32);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_32, 0);
lean_dec(x_66);
x_35 = x_32;
x_36 = x_65;
goto block_64;
}
else
{
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_37; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_33);
x_37 = x_35;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_34);
x_37 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_42 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_42, 0, x_39);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_42, x_41, x_43);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_array_fget_borrowed(x_41, x_45);
x_47 = lean_ctor_get(x_46, 0);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_45, x_48);
lean_dec(x_45);
x_50 = lean_array_fget_borrowed(x_41, x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 1);
x_52 = lean_ctor_get(x_51, 0);
x_53 = lean_nat_abs(x_52);
x_54 = lean_nat_to_int(x_53);
x_55 = lean_int_sub(x_47, x_54);
lean_dec(x_54);
x_56 = lean_int_dec_lt(x_39, x_55);
lean_dec(x_55);
lean_dec(x_39);
if (x_56 == 0)
{
lean_inc(x_46);
x_28 = x_38;
x_29 = x_46;
goto block_31;
}
else
{
lean_inc(x_50);
x_28 = x_38;
x_29 = x_50;
goto block_31;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_44);
lean_dec(x_39);
x_57 = lean_array_get_size(x_41);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_57, x_58);
x_60 = lean_nat_dec_lt(x_59, x_57);
if (x_60 == 0)
{
lean_dec(x_59);
lean_inc_ref(x_40);
x_7 = x_38;
x_8 = x_40;
goto block_27;
}
else
{
lean_object* x_61; 
x_61 = lean_array_fget_borrowed(x_41, x_59);
lean_dec(x_59);
lean_inc(x_61);
x_28 = x_38;
x_29 = x_61;
goto block_31;
}
}
}
}
}
block_94:
{
uint8_t x_73; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_90; 
x_83 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
x_84 = lean_int_mod(x_69, x_83);
x_85 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
x_90 = lean_int_dec_eq(x_84, x_85);
lean_dec(x_84);
if (x_90 == 0)
{
x_73 = x_90;
goto block_82;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
x_92 = lean_int_mod(x_69, x_91);
x_93 = lean_int_dec_eq(x_92, x_85);
lean_dec(x_92);
if (x_93 == 0)
{
if (x_90 == 0)
{
goto block_89;
}
else
{
x_73 = x_90;
goto block_82;
}
}
else
{
goto block_89;
}
}
block_82:
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Std_Time_Month_Ordinal_days(x_73, x_70);
x_75 = lean_int_dec_lt(x_74, x_2);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_74);
if (x_72 == 0)
{
lean_ctor_set(x_71, 2, x_2);
x_76 = x_71;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_2);
x_76 = x_78;
goto block_77;
}
block_77:
{
x_33 = x_76;
goto block_67;
}
}
else
{
lean_object* x_79; 
lean_dec(x_2);
if (x_72 == 0)
{
lean_ctor_set(x_71, 2, x_74);
x_79 = x_71;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_70);
lean_ctor_set(x_81, 2, x_74);
x_79 = x_81;
goto block_80;
}
block_80:
{
x_33 = x_79;
goto block_67;
}
}
}
block_89:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
x_87 = lean_int_mod(x_69, x_86);
x_88 = lean_int_dec_eq(x_87, x_85);
lean_dec(x_87);
x_73 = x_88;
goto block_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_68; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_68 = !lean_is_exclusive(x_1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_1, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_dec(x_70);
x_5 = x_1;
x_6 = x_68;
goto block_67;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_7 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_66 = !lean_is_exclusive(x_7);
if (x_66 == 0)
{
x_10 = x_7;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = l_Std_Time_PlainDate_rollOver(x_12, x_13, x_2);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_14);
lean_ctor_set(x_64, 1, x_9);
x_15 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_16; lean_object* x_17; lean_object* x_37; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_15);
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
x_43 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_43, 0, x_40);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_43, x_42, x_44);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_array_fget_borrowed(x_42, x_46);
x_48 = lean_ctor_get(x_47, 0);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_sub(x_46, x_49);
lean_dec(x_46);
x_51 = lean_array_fget_borrowed(x_42, x_50);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 1);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_nat_abs(x_53);
x_55 = lean_nat_to_int(x_54);
x_56 = lean_int_sub(x_48, x_55);
lean_dec(x_55);
x_57 = lean_int_dec_lt(x_40, x_56);
lean_dec(x_56);
lean_dec(x_40);
if (x_57 == 0)
{
lean_inc(x_47);
x_37 = x_47;
goto block_39;
}
else
{
lean_inc(x_51);
x_37 = x_51;
goto block_39;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_45);
lean_dec(x_40);
x_58 = lean_array_get_size(x_42);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_58, x_59);
x_61 = lean_nat_dec_lt(x_60, x_58);
if (x_61 == 0)
{
lean_dec(x_60);
lean_inc_ref(x_41);
x_17 = x_41;
goto block_36;
}
else
{
lean_object* x_62; 
x_62 = lean_array_fget_borrowed(x_42, x_60);
lean_dec(x_60);
lean_inc(x_62);
x_37 = x_62;
goto block_39;
}
}
block_36:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_17);
lean_dec_ref(x_17);
x_21 = l_Std_Time_TimeZone_toSeconds(x_20);
x_22 = lean_int_neg(x_21);
x_23 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_24 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_25 = lean_int_mul(x_18, x_24);
lean_dec(x_18);
x_26 = lean_int_add(x_25, x_19);
lean_dec(x_19);
lean_dec(x_25);
x_27 = lean_int_mul(x_22, x_24);
lean_dec(x_22);
x_28 = lean_int_add(x_27, x_23);
lean_dec(x_27);
x_29 = lean_int_add(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
lean_inc_ref(x_30);
x_31 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_21);
lean_closure_set(x_31, 2, x_24);
x_32 = lean_mk_thunk(x_31);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_20);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_32);
x_33 = x_5;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_35, 3, x_20);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
block_39:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_37);
x_17 = x_38;
goto block_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysRollOver___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_withDaysRollOver(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMonthClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_98; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_98 = !lean_is_exclusive(x_1);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_1, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_1, 1);
lean_dec(x_100);
x_5 = x_1;
x_6 = x_98;
goto block_97;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_7; lean_object* x_8; lean_object* x_28; lean_object* x_29; lean_object* x_32; lean_object* x_33; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_95; 
x_32 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_68 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_68, 0);
x_70 = lean_ctor_get(x_68, 2);
x_95 = !lean_is_exclusive(x_68);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_68, 1);
lean_dec(x_96);
x_71 = x_68;
x_72 = x_95;
goto block_94;
}
else
{
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_68);
x_71 = lean_box(0);
x_72 = x_95;
goto block_94;
}
block_27:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_8);
lean_dec_ref(x_8);
x_12 = l_Std_Time_TimeZone_toSeconds(x_11);
x_13 = lean_int_neg(x_12);
x_14 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_15 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_16 = lean_int_mul(x_9, x_15);
lean_dec(x_9);
x_17 = lean_int_add(x_16, x_10);
lean_dec(x_10);
lean_dec(x_16);
x_18 = lean_int_mul(x_13, x_15);
lean_dec(x_13);
x_19 = lean_int_add(x_18, x_14);
lean_dec(x_18);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_Duration_ofNanoseconds(x_20);
lean_dec(x_20);
lean_inc_ref(x_21);
x_22 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_12);
lean_closure_set(x_22, 2, x_15);
x_23 = lean_mk_thunk(x_22);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_11);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_23);
x_24 = x_5;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 3, x_11);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
block_31:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_7 = x_28;
x_8 = x_30;
goto block_27;
}
block_67:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_65; 
x_34 = lean_ctor_get(x_32, 1);
x_65 = !lean_is_exclusive(x_32);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_32, 0);
lean_dec(x_66);
x_35 = x_32;
x_36 = x_65;
goto block_64;
}
else
{
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_37; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_33);
x_37 = x_35;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_34);
x_37 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_42 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_42, 0, x_39);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_42, x_41, x_43);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_array_fget_borrowed(x_41, x_45);
x_47 = lean_ctor_get(x_46, 0);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_45, x_48);
lean_dec(x_45);
x_50 = lean_array_fget_borrowed(x_41, x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 1);
x_52 = lean_ctor_get(x_51, 0);
x_53 = lean_nat_abs(x_52);
x_54 = lean_nat_to_int(x_53);
x_55 = lean_int_sub(x_47, x_54);
lean_dec(x_54);
x_56 = lean_int_dec_lt(x_39, x_55);
lean_dec(x_55);
lean_dec(x_39);
if (x_56 == 0)
{
lean_inc(x_46);
x_28 = x_38;
x_29 = x_46;
goto block_31;
}
else
{
lean_inc(x_50);
x_28 = x_38;
x_29 = x_50;
goto block_31;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_44);
lean_dec(x_39);
x_57 = lean_array_get_size(x_41);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_57, x_58);
x_60 = lean_nat_dec_lt(x_59, x_57);
if (x_60 == 0)
{
lean_dec(x_59);
lean_inc_ref(x_40);
x_7 = x_38;
x_8 = x_40;
goto block_27;
}
else
{
lean_object* x_61; 
x_61 = lean_array_fget_borrowed(x_41, x_59);
lean_dec(x_59);
lean_inc(x_61);
x_28 = x_38;
x_29 = x_61;
goto block_31;
}
}
}
}
}
block_94:
{
uint8_t x_73; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_90; 
x_83 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
x_84 = lean_int_mod(x_69, x_83);
x_85 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
x_90 = lean_int_dec_eq(x_84, x_85);
lean_dec(x_84);
if (x_90 == 0)
{
x_73 = x_90;
goto block_82;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
x_92 = lean_int_mod(x_69, x_91);
x_93 = lean_int_dec_eq(x_92, x_85);
lean_dec(x_92);
if (x_93 == 0)
{
if (x_90 == 0)
{
goto block_89;
}
else
{
x_73 = x_90;
goto block_82;
}
}
else
{
goto block_89;
}
}
block_82:
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Std_Time_Month_Ordinal_days(x_73, x_2);
x_75 = lean_int_dec_lt(x_74, x_70);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_74);
if (x_72 == 0)
{
lean_ctor_set(x_71, 1, x_2);
x_76 = x_71;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_2);
lean_ctor_set(x_78, 2, x_70);
x_76 = x_78;
goto block_77;
}
block_77:
{
x_33 = x_76;
goto block_67;
}
}
else
{
lean_object* x_79; 
lean_dec(x_70);
if (x_72 == 0)
{
lean_ctor_set(x_71, 2, x_74);
lean_ctor_set(x_71, 1, x_2);
x_79 = x_71;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_2);
lean_ctor_set(x_81, 2, x_74);
x_79 = x_81;
goto block_80;
}
block_80:
{
x_33 = x_79;
goto block_67;
}
}
}
block_89:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
x_87 = lean_int_mod(x_69, x_86);
x_88 = lean_int_dec_eq(x_87, x_85);
lean_dec(x_87);
x_73 = x_88;
goto block_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMonthRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_68; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_68 = !lean_is_exclusive(x_1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_1, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_dec(x_70);
x_5 = x_1;
x_6 = x_68;
goto block_67;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_7 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_66 = !lean_is_exclusive(x_7);
if (x_66 == 0)
{
x_10 = x_7;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = l_Std_Time_PlainDate_rollOver(x_12, x_2, x_13);
lean_dec(x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_14);
lean_ctor_set(x_64, 1, x_9);
x_15 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_16; lean_object* x_17; lean_object* x_37; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_15);
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
x_43 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_43, 0, x_40);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_43, x_42, x_44);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_array_fget_borrowed(x_42, x_46);
x_48 = lean_ctor_get(x_47, 0);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_sub(x_46, x_49);
lean_dec(x_46);
x_51 = lean_array_fget_borrowed(x_42, x_50);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 1);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_nat_abs(x_53);
x_55 = lean_nat_to_int(x_54);
x_56 = lean_int_sub(x_48, x_55);
lean_dec(x_55);
x_57 = lean_int_dec_lt(x_40, x_56);
lean_dec(x_56);
lean_dec(x_40);
if (x_57 == 0)
{
lean_inc(x_47);
x_37 = x_47;
goto block_39;
}
else
{
lean_inc(x_51);
x_37 = x_51;
goto block_39;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_45);
lean_dec(x_40);
x_58 = lean_array_get_size(x_42);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_58, x_59);
x_61 = lean_nat_dec_lt(x_60, x_58);
if (x_61 == 0)
{
lean_dec(x_60);
lean_inc_ref(x_41);
x_17 = x_41;
goto block_36;
}
else
{
lean_object* x_62; 
x_62 = lean_array_fget_borrowed(x_42, x_60);
lean_dec(x_60);
lean_inc(x_62);
x_37 = x_62;
goto block_39;
}
}
block_36:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_17);
lean_dec_ref(x_17);
x_21 = l_Std_Time_TimeZone_toSeconds(x_20);
x_22 = lean_int_neg(x_21);
x_23 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_24 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_25 = lean_int_mul(x_18, x_24);
lean_dec(x_18);
x_26 = lean_int_add(x_25, x_19);
lean_dec(x_19);
lean_dec(x_25);
x_27 = lean_int_mul(x_22, x_24);
lean_dec(x_22);
x_28 = lean_int_add(x_27, x_23);
lean_dec(x_27);
x_29 = lean_int_add(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
lean_inc_ref(x_30);
x_31 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_21);
lean_closure_set(x_31, 2, x_24);
x_32 = lean_mk_thunk(x_31);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_20);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_32);
x_33 = x_5;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_35, 3, x_20);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
block_39:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_37);
x_17 = x_38;
goto block_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withYearClip(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_98; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_98 = !lean_is_exclusive(x_1);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_1, 3);
lean_dec(x_99);
x_100 = lean_ctor_get(x_1, 1);
lean_dec(x_100);
x_5 = x_1;
x_6 = x_98;
goto block_97;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_7; lean_object* x_8; lean_object* x_28; lean_object* x_29; lean_object* x_32; lean_object* x_33; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_95; 
x_32 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_68 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_68, 1);
x_70 = lean_ctor_get(x_68, 2);
x_95 = !lean_is_exclusive(x_68);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_68, 0);
lean_dec(x_96);
x_71 = x_68;
x_72 = x_95;
goto block_94;
}
else
{
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_68);
x_71 = lean_box(0);
x_72 = x_95;
goto block_94;
}
block_27:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec_ref(x_7);
x_11 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_8);
lean_dec_ref(x_8);
x_12 = l_Std_Time_TimeZone_toSeconds(x_11);
x_13 = lean_int_neg(x_12);
x_14 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_15 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_16 = lean_int_mul(x_9, x_15);
lean_dec(x_9);
x_17 = lean_int_add(x_16, x_10);
lean_dec(x_10);
lean_dec(x_16);
x_18 = lean_int_mul(x_13, x_15);
lean_dec(x_13);
x_19 = lean_int_add(x_18, x_14);
lean_dec(x_18);
x_20 = lean_int_add(x_17, x_19);
lean_dec(x_19);
lean_dec(x_17);
x_21 = l_Std_Time_Duration_ofNanoseconds(x_20);
lean_dec(x_20);
lean_inc_ref(x_21);
x_22 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_12);
lean_closure_set(x_22, 2, x_15);
x_23 = lean_mk_thunk(x_22);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_11);
lean_ctor_set(x_5, 1, x_21);
lean_ctor_set(x_5, 0, x_23);
x_24 = x_5;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 3, x_11);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
block_31:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_29);
x_7 = x_28;
x_8 = x_30;
goto block_27;
}
block_67:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_65; 
x_34 = lean_ctor_get(x_32, 1);
x_65 = !lean_is_exclusive(x_32);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_32, 0);
lean_dec(x_66);
x_35 = x_32;
x_36 = x_65;
goto block_64;
}
else
{
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
x_36 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_37; 
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_33);
x_37 = x_35;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_34);
x_37 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_4, 0);
x_41 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
x_42 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_42, 0, x_39);
x_43 = lean_unsigned_to_nat(0u);
x_44 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_42, x_41, x_43);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_array_fget_borrowed(x_41, x_45);
x_47 = lean_ctor_get(x_46, 0);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_45, x_48);
lean_dec(x_45);
x_50 = lean_array_fget_borrowed(x_41, x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 1);
x_52 = lean_ctor_get(x_51, 0);
x_53 = lean_nat_abs(x_52);
x_54 = lean_nat_to_int(x_53);
x_55 = lean_int_sub(x_47, x_54);
lean_dec(x_54);
x_56 = lean_int_dec_lt(x_39, x_55);
lean_dec(x_55);
lean_dec(x_39);
if (x_56 == 0)
{
lean_inc(x_46);
x_28 = x_38;
x_29 = x_46;
goto block_31;
}
else
{
lean_inc(x_50);
x_28 = x_38;
x_29 = x_50;
goto block_31;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_44);
lean_dec(x_39);
x_57 = lean_array_get_size(x_41);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_57, x_58);
x_60 = lean_nat_dec_lt(x_59, x_57);
if (x_60 == 0)
{
lean_dec(x_59);
lean_inc_ref(x_40);
x_7 = x_38;
x_8 = x_40;
goto block_27;
}
else
{
lean_object* x_61; 
x_61 = lean_array_fget_borrowed(x_41, x_59);
lean_dec(x_59);
lean_inc(x_61);
x_28 = x_38;
x_29 = x_61;
goto block_31;
}
}
}
}
}
block_94:
{
uint8_t x_73; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_90; 
x_83 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
x_84 = lean_int_mod(x_2, x_83);
x_85 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
x_90 = lean_int_dec_eq(x_84, x_85);
lean_dec(x_84);
if (x_90 == 0)
{
x_73 = x_90;
goto block_82;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
x_92 = lean_int_mod(x_2, x_91);
x_93 = lean_int_dec_eq(x_92, x_85);
lean_dec(x_92);
if (x_93 == 0)
{
if (x_90 == 0)
{
goto block_89;
}
else
{
x_73 = x_90;
goto block_82;
}
}
else
{
goto block_89;
}
}
block_82:
{
lean_object* x_74; uint8_t x_75; 
x_74 = l_Std_Time_Month_Ordinal_days(x_73, x_69);
x_75 = lean_int_dec_lt(x_74, x_70);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_74);
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_2);
x_76 = x_71;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_2);
lean_ctor_set(x_78, 1, x_69);
lean_ctor_set(x_78, 2, x_70);
x_76 = x_78;
goto block_77;
}
block_77:
{
x_33 = x_76;
goto block_67;
}
}
else
{
lean_object* x_79; 
lean_dec(x_70);
if (x_72 == 0)
{
lean_ctor_set(x_71, 2, x_74);
lean_ctor_set(x_71, 0, x_2);
x_79 = x_71;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_69);
lean_ctor_set(x_81, 2, x_74);
x_79 = x_81;
goto block_80;
}
block_80:
{
x_33 = x_79;
goto block_67;
}
}
}
block_89:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
x_87 = lean_int_mod(x_2, x_86);
x_88 = lean_int_dec_eq(x_87, x_85);
lean_dec(x_87);
x_73 = x_88;
goto block_82;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withYearRollOver(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_68; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_68 = !lean_is_exclusive(x_1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_1, 3);
lean_dec(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_dec(x_70);
x_5 = x_1;
x_6 = x_68;
goto block_67;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_66; 
x_7 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_66 = !lean_is_exclusive(x_7);
if (x_66 == 0)
{
x_10 = x_7;
x_11 = x_66;
goto block_65;
}
else
{
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = l_Std_Time_PlainDate_rollOver(x_2, x_12, x_13);
lean_dec(x_13);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_14);
x_15 = x_10;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_14);
lean_ctor_set(x_64, 1, x_9);
x_15 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_16; lean_object* x_17; lean_object* x_37; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_16 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_15);
x_40 = lean_ctor_get(x_16, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_4, 0);
x_42 = lean_ctor_get(x_4, 1);
lean_inc(x_40);
x_43 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_43, 0, x_40);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_43, x_42, x_44);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_array_fget_borrowed(x_42, x_46);
x_48 = lean_ctor_get(x_47, 0);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_sub(x_46, x_49);
lean_dec(x_46);
x_51 = lean_array_fget_borrowed(x_42, x_50);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 1);
x_53 = lean_ctor_get(x_52, 0);
x_54 = lean_nat_abs(x_53);
x_55 = lean_nat_to_int(x_54);
x_56 = lean_int_sub(x_48, x_55);
lean_dec(x_55);
x_57 = lean_int_dec_lt(x_40, x_56);
lean_dec(x_56);
lean_dec(x_40);
if (x_57 == 0)
{
lean_inc(x_47);
x_37 = x_47;
goto block_39;
}
else
{
lean_inc(x_51);
x_37 = x_51;
goto block_39;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_45);
lean_dec(x_40);
x_58 = lean_array_get_size(x_42);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_58, x_59);
x_61 = lean_nat_dec_lt(x_60, x_58);
if (x_61 == 0)
{
lean_dec(x_60);
lean_inc_ref(x_41);
x_17 = x_41;
goto block_36;
}
else
{
lean_object* x_62; 
x_62 = lean_array_fget_borrowed(x_42, x_60);
lean_dec(x_60);
lean_inc(x_62);
x_37 = x_62;
goto block_39;
}
}
block_36:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_17);
lean_dec_ref(x_17);
x_21 = l_Std_Time_TimeZone_toSeconds(x_20);
x_22 = lean_int_neg(x_21);
x_23 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_24 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_25 = lean_int_mul(x_18, x_24);
lean_dec(x_18);
x_26 = lean_int_add(x_25, x_19);
lean_dec(x_19);
lean_dec(x_25);
x_27 = lean_int_mul(x_22, x_24);
lean_dec(x_22);
x_28 = lean_int_add(x_27, x_23);
lean_dec(x_27);
x_29 = lean_int_add(x_26, x_28);
lean_dec(x_28);
lean_dec(x_26);
x_30 = l_Std_Time_Duration_ofNanoseconds(x_29);
lean_dec(x_29);
lean_inc_ref(x_30);
x_31 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_21);
lean_closure_set(x_31, 2, x_24);
x_32 = lean_mk_thunk(x_31);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_20);
lean_ctor_set(x_5, 1, x_30);
lean_ctor_set(x_5, 0, x_32);
x_33 = x_5;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_30);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_35, 3, x_20);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
block_39:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_37);
x_17 = x_38;
goto block_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withHours(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_76; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_1, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_1, 1);
lean_dec(x_78);
x_5 = x_1;
x_6 = x_76;
goto block_75;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_74; 
x_7 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_74 = !lean_is_exclusive(x_7);
if (x_74 == 0)
{
x_10 = x_7;
x_11 = x_74;
goto block_73;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_71; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = lean_ctor_get(x_8, 2);
x_14 = lean_ctor_get(x_8, 3);
x_71 = !lean_is_exclusive(x_8);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_8, 0);
lean_dec(x_72);
x_15 = x_8;
x_16 = x_71;
goto block_70;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_2);
x_17 = x_15;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_2);
lean_ctor_set(x_69, 1, x_12);
lean_ctor_set(x_69, 2, x_13);
lean_ctor_set(x_69, 3, x_14);
x_17 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_18; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_17);
x_18 = x_10;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_9);
lean_ctor_set(x_67, 1, x_17);
x_18 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_19; lean_object* x_20; lean_object* x_40; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_46 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_46, 0, x_43);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_46, x_45, x_47);
if (lean_obj_tag(x_48) == 1)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_array_fget_borrowed(x_45, x_49);
x_51 = lean_ctor_get(x_50, 0);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_49, x_52);
lean_dec(x_49);
x_54 = lean_array_fget_borrowed(x_45, x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 1);
x_56 = lean_ctor_get(x_55, 0);
x_57 = lean_nat_abs(x_56);
x_58 = lean_nat_to_int(x_57);
x_59 = lean_int_sub(x_51, x_58);
lean_dec(x_58);
x_60 = lean_int_dec_lt(x_43, x_59);
lean_dec(x_59);
lean_dec(x_43);
if (x_60 == 0)
{
lean_inc(x_50);
x_40 = x_50;
goto block_42;
}
else
{
lean_inc(x_54);
x_40 = x_54;
goto block_42;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_48);
lean_dec(x_43);
x_61 = lean_array_get_size(x_45);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_61, x_62);
x_64 = lean_nat_dec_lt(x_63, x_61);
if (x_64 == 0)
{
lean_dec(x_63);
lean_inc_ref(x_44);
x_20 = x_44;
goto block_39;
}
else
{
lean_object* x_65; 
x_65 = lean_array_fget_borrowed(x_45, x_63);
lean_dec(x_63);
lean_inc(x_65);
x_40 = x_65;
goto block_42;
}
}
block_39:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_20);
lean_dec_ref(x_20);
x_24 = l_Std_Time_TimeZone_toSeconds(x_23);
x_25 = lean_int_neg(x_24);
x_26 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_27 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_28 = lean_int_mul(x_21, x_27);
lean_dec(x_21);
x_29 = lean_int_add(x_28, x_22);
lean_dec(x_22);
lean_dec(x_28);
x_30 = lean_int_mul(x_25, x_27);
lean_dec(x_25);
x_31 = lean_int_add(x_30, x_26);
lean_dec(x_30);
x_32 = lean_int_add(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_33 = l_Std_Time_Duration_ofNanoseconds(x_32);
lean_dec(x_32);
lean_inc_ref(x_33);
x_34 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_24);
lean_closure_set(x_34, 2, x_27);
x_35 = lean_mk_thunk(x_34);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_23);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_35);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set(x_38, 3, x_23);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
block_42:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_41);
lean_dec_ref(x_40);
x_20 = x_41;
goto block_39;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMinutes(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_76; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_1, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_1, 1);
lean_dec(x_78);
x_5 = x_1;
x_6 = x_76;
goto block_75;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_74; 
x_7 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_74 = !lean_is_exclusive(x_7);
if (x_74 == 0)
{
x_10 = x_7;
x_11 = x_74;
goto block_73;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_71; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 2);
x_14 = lean_ctor_get(x_8, 3);
x_71 = !lean_is_exclusive(x_8);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_8, 1);
lean_dec(x_72);
x_15 = x_8;
x_16 = x_71;
goto block_70;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_2);
x_17 = x_15;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_2);
lean_ctor_set(x_69, 2, x_13);
lean_ctor_set(x_69, 3, x_14);
x_17 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_18; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_17);
x_18 = x_10;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_9);
lean_ctor_set(x_67, 1, x_17);
x_18 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_19; lean_object* x_20; lean_object* x_40; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_46 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_46, 0, x_43);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_46, x_45, x_47);
if (lean_obj_tag(x_48) == 1)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_array_fget_borrowed(x_45, x_49);
x_51 = lean_ctor_get(x_50, 0);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_49, x_52);
lean_dec(x_49);
x_54 = lean_array_fget_borrowed(x_45, x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 1);
x_56 = lean_ctor_get(x_55, 0);
x_57 = lean_nat_abs(x_56);
x_58 = lean_nat_to_int(x_57);
x_59 = lean_int_sub(x_51, x_58);
lean_dec(x_58);
x_60 = lean_int_dec_lt(x_43, x_59);
lean_dec(x_59);
lean_dec(x_43);
if (x_60 == 0)
{
lean_inc(x_50);
x_40 = x_50;
goto block_42;
}
else
{
lean_inc(x_54);
x_40 = x_54;
goto block_42;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_48);
lean_dec(x_43);
x_61 = lean_array_get_size(x_45);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_61, x_62);
x_64 = lean_nat_dec_lt(x_63, x_61);
if (x_64 == 0)
{
lean_dec(x_63);
lean_inc_ref(x_44);
x_20 = x_44;
goto block_39;
}
else
{
lean_object* x_65; 
x_65 = lean_array_fget_borrowed(x_45, x_63);
lean_dec(x_63);
lean_inc(x_65);
x_40 = x_65;
goto block_42;
}
}
block_39:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_20);
lean_dec_ref(x_20);
x_24 = l_Std_Time_TimeZone_toSeconds(x_23);
x_25 = lean_int_neg(x_24);
x_26 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_27 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_28 = lean_int_mul(x_21, x_27);
lean_dec(x_21);
x_29 = lean_int_add(x_28, x_22);
lean_dec(x_22);
lean_dec(x_28);
x_30 = lean_int_mul(x_25, x_27);
lean_dec(x_25);
x_31 = lean_int_add(x_30, x_26);
lean_dec(x_30);
x_32 = lean_int_add(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_33 = l_Std_Time_Duration_ofNanoseconds(x_32);
lean_dec(x_32);
lean_inc_ref(x_33);
x_34 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_24);
lean_closure_set(x_34, 2, x_27);
x_35 = lean_mk_thunk(x_34);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_23);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_35);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set(x_38, 3, x_23);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
block_42:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_41);
lean_dec_ref(x_40);
x_20 = x_41;
goto block_39;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withSeconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_76; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_1, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_1, 1);
lean_dec(x_78);
x_5 = x_1;
x_6 = x_76;
goto block_75;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_74; 
x_7 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_74 = !lean_is_exclusive(x_7);
if (x_74 == 0)
{
x_10 = x_7;
x_11 = x_74;
goto block_73;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_71; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 3);
x_71 = !lean_is_exclusive(x_8);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_8, 2);
lean_dec(x_72);
x_15 = x_8;
x_16 = x_71;
goto block_70;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 2, x_2);
x_17 = x_15;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_13);
lean_ctor_set(x_69, 2, x_2);
lean_ctor_set(x_69, 3, x_14);
x_17 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_18; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_17);
x_18 = x_10;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_9);
lean_ctor_set(x_67, 1, x_17);
x_18 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_19; lean_object* x_20; lean_object* x_40; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_46 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_46, 0, x_43);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_46, x_45, x_47);
if (lean_obj_tag(x_48) == 1)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_array_fget_borrowed(x_45, x_49);
x_51 = lean_ctor_get(x_50, 0);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_49, x_52);
lean_dec(x_49);
x_54 = lean_array_fget_borrowed(x_45, x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 1);
x_56 = lean_ctor_get(x_55, 0);
x_57 = lean_nat_abs(x_56);
x_58 = lean_nat_to_int(x_57);
x_59 = lean_int_sub(x_51, x_58);
lean_dec(x_58);
x_60 = lean_int_dec_lt(x_43, x_59);
lean_dec(x_59);
lean_dec(x_43);
if (x_60 == 0)
{
lean_inc(x_50);
x_40 = x_50;
goto block_42;
}
else
{
lean_inc(x_54);
x_40 = x_54;
goto block_42;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_48);
lean_dec(x_43);
x_61 = lean_array_get_size(x_45);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_61, x_62);
x_64 = lean_nat_dec_lt(x_63, x_61);
if (x_64 == 0)
{
lean_dec(x_63);
lean_inc_ref(x_44);
x_20 = x_44;
goto block_39;
}
else
{
lean_object* x_65; 
x_65 = lean_array_fget_borrowed(x_45, x_63);
lean_dec(x_63);
lean_inc(x_65);
x_40 = x_65;
goto block_42;
}
}
block_39:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_20);
lean_dec_ref(x_20);
x_24 = l_Std_Time_TimeZone_toSeconds(x_23);
x_25 = lean_int_neg(x_24);
x_26 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_27 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_28 = lean_int_mul(x_21, x_27);
lean_dec(x_21);
x_29 = lean_int_add(x_28, x_22);
lean_dec(x_22);
lean_dec(x_28);
x_30 = lean_int_mul(x_25, x_27);
lean_dec(x_25);
x_31 = lean_int_add(x_30, x_26);
lean_dec(x_30);
x_32 = lean_int_add(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_33 = l_Std_Time_Duration_ofNanoseconds(x_32);
lean_dec(x_32);
lean_inc_ref(x_33);
x_34 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_24);
lean_closure_set(x_34, 2, x_27);
x_35 = lean_mk_thunk(x_34);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_23);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_35);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set(x_38, 3, x_23);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
block_42:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_41);
lean_dec_ref(x_40);
x_20 = x_41;
goto block_39;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_81; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_81 = !lean_is_exclusive(x_1);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_1, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_1, 1);
lean_dec(x_83);
x_5 = x_1;
x_6 = x_81;
goto block_80;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_79; 
x_7 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_79 = !lean_is_exclusive(x_7);
if (x_79 == 0)
{
x_10 = x_7;
x_11 = x_79;
goto block_78;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_77; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_ctor_get(x_8, 3);
x_77 = !lean_is_exclusive(x_8);
if (x_77 == 0)
{
x_16 = x_8;
x_17 = x_77;
goto block_76;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_16 = lean_box(0);
x_17 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_obj_once(&l_Std_Time_ZonedDateTime_withMilliseconds___closed__0, &l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0);
x_19 = lean_int_emod(x_15, x_18);
lean_dec(x_15);
x_20 = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
x_21 = lean_int_mul(x_2, x_20);
x_22 = lean_int_add(x_21, x_19);
lean_dec(x_19);
lean_dec(x_21);
if (x_17 == 0)
{
lean_ctor_set(x_16, 3, x_22);
x_23 = x_16;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_75, 0, x_12);
lean_ctor_set(x_75, 1, x_13);
lean_ctor_set(x_75, 2, x_14);
lean_ctor_set(x_75, 3, x_22);
x_23 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_24; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_23);
x_24 = x_10;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_9);
lean_ctor_set(x_73, 1, x_23);
x_24 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_25; lean_object* x_26; lean_object* x_46; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_25 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_24);
x_49 = lean_ctor_get(x_25, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 0);
x_51 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
x_52 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_52, 0, x_49);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_52, x_51, x_53);
if (lean_obj_tag(x_54) == 1)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = lean_array_fget_borrowed(x_51, x_55);
x_57 = lean_ctor_get(x_56, 0);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_55, x_58);
lean_dec(x_55);
x_60 = lean_array_fget_borrowed(x_51, x_59);
lean_dec(x_59);
x_61 = lean_ctor_get(x_60, 1);
x_62 = lean_ctor_get(x_61, 0);
x_63 = lean_nat_abs(x_62);
x_64 = lean_nat_to_int(x_63);
x_65 = lean_int_sub(x_57, x_64);
lean_dec(x_64);
x_66 = lean_int_dec_lt(x_49, x_65);
lean_dec(x_65);
lean_dec(x_49);
if (x_66 == 0)
{
lean_inc(x_56);
x_46 = x_56;
goto block_48;
}
else
{
lean_inc(x_60);
x_46 = x_60;
goto block_48;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_54);
lean_dec(x_49);
x_67 = lean_array_get_size(x_51);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_sub(x_67, x_68);
x_70 = lean_nat_dec_lt(x_69, x_67);
if (x_70 == 0)
{
lean_dec(x_69);
lean_inc_ref(x_50);
x_26 = x_50;
goto block_45;
}
else
{
lean_object* x_71; 
x_71 = lean_array_fget_borrowed(x_51, x_69);
lean_dec(x_69);
lean_inc(x_71);
x_46 = x_71;
goto block_48;
}
}
block_45:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_26);
lean_dec_ref(x_26);
x_30 = l_Std_Time_TimeZone_toSeconds(x_29);
x_31 = lean_int_neg(x_30);
x_32 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_33 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_34 = lean_int_mul(x_27, x_33);
lean_dec(x_27);
x_35 = lean_int_add(x_34, x_28);
lean_dec(x_28);
lean_dec(x_34);
x_36 = lean_int_mul(x_31, x_33);
lean_dec(x_31);
x_37 = lean_int_add(x_36, x_32);
lean_dec(x_36);
x_38 = lean_int_add(x_35, x_37);
lean_dec(x_37);
lean_dec(x_35);
x_39 = l_Std_Time_Duration_ofNanoseconds(x_38);
lean_dec(x_38);
lean_inc_ref(x_39);
x_40 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_40, 0, x_39);
lean_closure_set(x_40, 1, x_30);
lean_closure_set(x_40, 2, x_33);
x_41 = lean_mk_thunk(x_40);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_29);
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_41);
x_42 = x_5;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set(x_44, 3, x_29);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
block_48:
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_47);
lean_dec_ref(x_46);
x_26 = x_47;
goto block_45;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_withMilliseconds(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withNanoseconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_76; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_1, 3);
lean_dec(x_77);
x_78 = lean_ctor_get(x_1, 1);
lean_dec(x_78);
x_5 = x_1;
x_6 = x_76;
goto block_75;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_74; 
x_7 = lean_thunk_get_own(x_3);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_7, 0);
x_74 = !lean_is_exclusive(x_7);
if (x_74 == 0)
{
x_10 = x_7;
x_11 = x_74;
goto block_73;
}
else
{
lean_inc(x_8);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_71; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_71 = !lean_is_exclusive(x_8);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_8, 3);
lean_dec(x_72);
x_15 = x_8;
x_16 = x_71;
goto block_70;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 3, x_2);
x_17 = x_15;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_12);
lean_ctor_set(x_69, 1, x_13);
lean_ctor_set(x_69, 2, x_14);
lean_ctor_set(x_69, 3, x_2);
x_17 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_18; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_17);
x_18 = x_10;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_9);
lean_ctor_set(x_67, 1, x_17);
x_18 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_19; lean_object* x_20; lean_object* x_40; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_19 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_18);
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_46 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_46, 0, x_43);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_46, x_45, x_47);
if (lean_obj_tag(x_48) == 1)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = lean_array_fget_borrowed(x_45, x_49);
x_51 = lean_ctor_get(x_50, 0);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_49, x_52);
lean_dec(x_49);
x_54 = lean_array_fget_borrowed(x_45, x_53);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 1);
x_56 = lean_ctor_get(x_55, 0);
x_57 = lean_nat_abs(x_56);
x_58 = lean_nat_to_int(x_57);
x_59 = lean_int_sub(x_51, x_58);
lean_dec(x_58);
x_60 = lean_int_dec_lt(x_43, x_59);
lean_dec(x_59);
lean_dec(x_43);
if (x_60 == 0)
{
lean_inc(x_50);
x_40 = x_50;
goto block_42;
}
else
{
lean_inc(x_54);
x_40 = x_54;
goto block_42;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_48);
lean_dec(x_43);
x_61 = lean_array_get_size(x_45);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_61, x_62);
x_64 = lean_nat_dec_lt(x_63, x_61);
if (x_64 == 0)
{
lean_dec(x_63);
lean_inc_ref(x_44);
x_20 = x_44;
goto block_39;
}
else
{
lean_object* x_65; 
x_65 = lean_array_fget_borrowed(x_45, x_63);
lean_dec(x_63);
lean_inc(x_65);
x_40 = x_65;
goto block_42;
}
}
block_39:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_20);
lean_dec_ref(x_20);
x_24 = l_Std_Time_TimeZone_toSeconds(x_23);
x_25 = lean_int_neg(x_24);
x_26 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_27 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_28 = lean_int_mul(x_21, x_27);
lean_dec(x_21);
x_29 = lean_int_add(x_28, x_22);
lean_dec(x_22);
lean_dec(x_28);
x_30 = lean_int_mul(x_25, x_27);
lean_dec(x_25);
x_31 = lean_int_add(x_30, x_26);
lean_dec(x_30);
x_32 = lean_int_add(x_29, x_31);
lean_dec(x_31);
lean_dec(x_29);
x_33 = l_Std_Time_Duration_ofNanoseconds(x_32);
lean_dec(x_32);
lean_inc_ref(x_33);
x_34 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_24);
lean_closure_set(x_34, 2, x_27);
x_35 = lean_mk_thunk(x_34);
if (x_6 == 0)
{
lean_ctor_set(x_5, 3, x_23);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_35);
x_36 = x_5;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_4);
lean_ctor_set(x_38, 3, x_23);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
block_42:
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_41);
lean_dec_ref(x_40);
x_20 = x_41;
goto block_39;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_inLeapYear(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
x_7 = lean_int_mod(x_5, x_6);
x_8 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
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
x_14 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
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
x_9 = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
x_10 = lean_int_mod(x_5, x_9);
lean_dec(x_5);
x_11 = lean_int_dec_eq(x_10, x_8);
lean_dec(x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_inLeapYear___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Time_ZonedDateTime_inLeapYear(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDaysSinceUNIXEpoch(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_thunk_get_own(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDaysSinceUNIXEpoch___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_ZonedDateTime_toDaysSinceUNIXEpoch(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofDaysSinceUNIXEpoch(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_25; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_4 = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
x_6 = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(x_5);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
x_31 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_28);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), x_31, x_30, x_32);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_array_fget_borrowed(x_30, x_34);
x_36 = lean_ctor_get(x_35, 0);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_sub(x_34, x_37);
lean_dec(x_34);
x_39 = lean_array_fget_borrowed(x_30, x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 1);
x_41 = lean_ctor_get(x_40, 0);
x_42 = lean_nat_abs(x_41);
x_43 = lean_nat_to_int(x_42);
x_44 = lean_int_sub(x_36, x_43);
lean_dec(x_43);
x_45 = lean_int_dec_lt(x_28, x_44);
lean_dec(x_44);
lean_dec(x_28);
if (x_45 == 0)
{
lean_inc(x_35);
x_25 = x_35;
goto block_27;
}
else
{
lean_inc(x_39);
x_25 = x_39;
goto block_27;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_33);
lean_dec(x_28);
x_46 = lean_array_get_size(x_30);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_46, x_47);
x_49 = lean_nat_dec_lt(x_48, x_46);
if (x_49 == 0)
{
lean_dec(x_48);
lean_inc_ref(x_29);
x_7 = x_29;
goto block_24;
}
else
{
lean_object* x_50; 
x_50 = lean_array_fget_borrowed(x_30, x_48);
lean_dec(x_48);
lean_inc(x_50);
x_25 = x_50;
goto block_27;
}
}
block_24:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(x_7);
lean_dec_ref(x_7);
x_11 = l_Std_Time_TimeZone_toSeconds(x_10);
x_12 = lean_int_neg(x_11);
x_13 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
x_14 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_15 = lean_int_mul(x_8, x_14);
lean_dec(x_8);
x_16 = lean_int_add(x_15, x_9);
lean_dec(x_9);
lean_dec(x_15);
x_17 = lean_int_mul(x_12, x_14);
lean_dec(x_12);
x_18 = lean_int_add(x_17, x_13);
lean_dec(x_17);
x_19 = lean_int_add(x_16, x_18);
lean_dec(x_18);
lean_dec(x_16);
x_20 = l_Std_Time_Duration_ofNanoseconds(x_19);
lean_dec(x_19);
lean_inc_ref(x_20);
x_21 = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_11);
lean_closure_set(x_21, 2, x_14);
x_22 = lean_mk_thunk(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_3);
lean_ctor_set(x_23, 3, x_10);
return x_23;
}
block_27:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_26);
lean_dec_ref(x_25);
x_7 = x_26;
goto block_24;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofDaysSinceUNIXEpoch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Time_ZonedDateTime_ofDaysSinceUNIXEpoch(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_int_neg(x_5);
x_10 = lean_int_neg(x_6);
x_11 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_6 = lean_int_mul(x_3, x_5);
x_7 = lean_int_add(x_6, x_4);
lean_dec(x_6);
x_8 = l_Std_Time_ZonedDateTime_addNanoseconds(x_1, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
x_6 = lean_int_mul(x_3, x_5);
x_7 = lean_int_add(x_6, x_4);
lean_dec(x_6);
x_8 = l_Std_Time_ZonedDateTime_subNanoseconds(x_1, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
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
res = runtime_initialize_Std_Time_Zoned_DateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin)
;
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
res = initialize_Std_Time_Zoned_DateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Zoned_ZoneRules(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_ZonedDateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_ZonedDateTime(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_ZonedDateTime(builtin);
}
#ifdef __cplusplus
}
#endif

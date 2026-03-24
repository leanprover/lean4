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
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(lean_object*);
lean_object* l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
extern lean_object* l_Std_Time_instInhabitedTimeZone_default;
extern lean_object* l_Std_Time_TimeZone_instInhabitedZoneRules_default;
extern lean_object* l_Std_Time_instInhabitedTimestamp_default;
extern lean_object* l_Std_Time_instInhabitedPlainDateTime_default;
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0;
static lean_once_cell_t l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter___boxed(lean_object*);
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
v___x_13_ = lean_unsigned_to_nat(1000000000u);
v___x_14_ = lean_nat_to_int(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(lean_object* v_tm_15_, lean_object* v___y_16_, lean_object* v_x_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v_second_20_; lean_object* v_nano_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_second_26_; lean_object* v_nano_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_18_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_tm_15_);
v___x_19_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_18_);
v_second_20_ = lean_ctor_get(v___x_19_, 0);
lean_inc(v_second_20_);
v_nano_21_ = lean_ctor_get(v___x_19_, 1);
lean_inc(v_nano_21_);
lean_dec_ref(v___x_19_);
v___x_22_ = l_Std_Time_TimeZone_toSeconds(v___y_16_);
v___x_23_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_24_ = lean_int_mul(v___x_22_, v___x_23_);
lean_dec(v___x_22_);
v___x_25_ = l_Std_Time_Duration_ofNanoseconds(v___x_24_);
lean_dec(v___x_24_);
v_second_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_second_26_);
v_nano_27_ = lean_ctor_get(v___x_25_, 1);
lean_inc(v_nano_27_);
lean_dec_ref(v___x_25_);
v___x_28_ = lean_int_mul(v_second_20_, v___x_23_);
lean_dec(v_second_20_);
v___x_29_ = lean_int_add(v___x_28_, v_nano_21_);
lean_dec(v_nano_21_);
lean_dec(v___x_28_);
v___x_30_ = lean_int_mul(v_second_26_, v___x_23_);
lean_dec(v_second_26_);
v___x_31_ = lean_int_add(v___x_30_, v_nano_27_);
lean_dec(v_nano_27_);
lean_dec(v___x_30_);
v___x_32_ = lean_int_add(v___x_29_, v___x_31_);
lean_dec(v___x_31_);
lean_dec(v___x_29_);
v___x_33_ = l_Std_Time_Duration_ofNanoseconds(v___x_32_);
lean_dec(v___x_32_);
v___x_34_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed(lean_object* v_tm_35_, lean_object* v___y_36_, lean_object* v_x_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Std_Time_ZonedDateTime_ofTimestamp___lam__0(v_tm_35_, v___y_36_, v_x_37_);
lean_dec_ref(v___y_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestamp(lean_object* v_tm_39_, lean_object* v_rules_40_){
_start:
{
lean_object* v___y_42_; lean_object* v_initialLocalTimeType_46_; lean_object* v_transitions_47_; lean_object* v___x_48_; 
v_initialLocalTimeType_46_ = lean_ctor_get(v_rules_40_, 0);
v_transitions_47_ = lean_ctor_get(v_rules_40_, 1);
lean_inc_ref(v_tm_39_);
v___x_48_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_47_, v_tm_39_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v___x_49_; 
lean_dec_ref(v___x_48_);
v___x_49_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_46_);
v___y_42_ = v___x_49_;
goto v___jp_41_;
}
else
{
lean_object* v_a_50_; 
v_a_50_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_a_50_);
lean_dec_ref(v___x_48_);
v___y_42_ = v_a_50_;
goto v___jp_41_;
}
v___jp_41_:
{
lean_object* v___f_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
lean_inc_ref(v___y_42_);
lean_inc_ref(v_tm_39_);
v___f_43_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_43_, 0, v_tm_39_);
lean_closure_set(v___f_43_, 1, v___y_42_);
v___x_44_ = lean_mk_thunk(v___f_43_);
v___x_45_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v_tm_39_);
lean_ctor_set(v___x_45_, 2, v_rules_40_);
lean_ctor_set(v___x_45_, 3, v___y_42_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(lean_object* v_tm_51_, lean_object* v___x_52_, lean_object* v___x_53_, lean_object* v_x_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_second_57_; lean_object* v_nano_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_second_61_; lean_object* v_nano_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_55_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_tm_51_);
v___x_56_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_55_);
v_second_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_second_57_);
v_nano_58_ = lean_ctor_get(v___x_56_, 1);
lean_inc(v_nano_58_);
lean_dec_ref(v___x_56_);
v___x_59_ = lean_int_mul(v___x_52_, v___x_53_);
v___x_60_ = l_Std_Time_Duration_ofNanoseconds(v___x_59_);
lean_dec(v___x_59_);
v_second_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_second_61_);
v_nano_62_ = lean_ctor_get(v___x_60_, 1);
lean_inc(v_nano_62_);
lean_dec_ref(v___x_60_);
v___x_63_ = lean_int_mul(v_second_57_, v___x_53_);
lean_dec(v_second_57_);
v___x_64_ = lean_int_add(v___x_63_, v_nano_58_);
lean_dec(v_nano_58_);
lean_dec(v___x_63_);
v___x_65_ = lean_int_mul(v_second_61_, v___x_53_);
lean_dec(v_second_61_);
v___x_66_ = lean_int_add(v___x_65_, v_nano_62_);
lean_dec(v_nano_62_);
lean_dec(v___x_65_);
v___x_67_ = lean_int_add(v___x_64_, v___x_66_);
lean_dec(v___x_66_);
lean_dec(v___x_64_);
v___x_68_ = l_Std_Time_Duration_ofNanoseconds(v___x_67_);
lean_dec(v___x_67_);
v___x_69_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed(lean_object* v_tm_70_, lean_object* v___x_71_, lean_object* v___x_72_, lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0(v_tm_70_, v___x_71_, v___x_72_, v_x_73_);
lean_dec(v___x_72_);
lean_dec(v___x_71_);
return v_res_74_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1(lean_object* v_second_75_, lean_object* v_t_76_){
_start:
{
lean_object* v_time_77_; uint8_t v___x_78_; 
v_time_77_ = lean_ctor_get(v_t_76_, 0);
v___x_78_ = lean_int_dec_le(v_second_75_, v_time_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed(lean_object* v_second_79_, lean_object* v_t_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1(v_second_79_, v_t_80_);
lean_dec_ref(v_t_80_);
lean_dec(v_second_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_86_ = lean_int_neg(v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTime(lean_object* v_pdt_87_, lean_object* v_zr_88_){
_start:
{
lean_object* v_tm_89_; lean_object* v___y_91_; lean_object* v_val_109_; lean_object* v_second_111_; lean_object* v_initialLocalTimeType_112_; lean_object* v_transitions_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_tm_89_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_pdt_87_);
v_second_111_ = lean_ctor_get(v_tm_89_, 0);
lean_inc(v_second_111_);
v_initialLocalTimeType_112_ = lean_ctor_get(v_zr_88_, 0);
v_transitions_113_ = lean_ctor_get(v_zr_88_, 1);
lean_inc(v_second_111_);
v___f_114_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_114_, 0, v_second_111_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_114_, v_transitions_113_, v___x_115_);
if (lean_obj_tag(v___x_116_) == 1)
{
lean_object* v_val_117_; lean_object* v_next_118_; lean_object* v_time_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_last_122_; lean_object* v_localTimeType_123_; lean_object* v_gmtOffset_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_val_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_val_117_);
lean_dec_ref(v___x_116_);
v_next_118_ = lean_array_fget_borrowed(v_transitions_113_, v_val_117_);
v_time_119_ = lean_ctor_get(v_next_118_, 0);
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_sub(v_val_117_, v___x_120_);
lean_dec(v_val_117_);
v_last_122_ = lean_array_fget_borrowed(v_transitions_113_, v___x_121_);
lean_dec(v___x_121_);
v_localTimeType_123_ = lean_ctor_get(v_last_122_, 1);
v_gmtOffset_124_ = lean_ctor_get(v_localTimeType_123_, 0);
v___x_125_ = lean_nat_abs(v_gmtOffset_124_);
v___x_126_ = lean_nat_to_int(v___x_125_);
v___x_127_ = lean_int_sub(v_time_119_, v___x_126_);
lean_dec(v___x_126_);
v___x_128_ = lean_int_dec_lt(v_second_111_, v___x_127_);
lean_dec(v___x_127_);
lean_dec(v_second_111_);
if (v___x_128_ == 0)
{
lean_inc(v_next_118_);
v_val_109_ = v_next_118_;
goto v___jp_108_;
}
else
{
lean_inc(v_last_122_);
v_val_109_ = v_last_122_;
goto v___jp_108_;
}
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
lean_dec(v___x_116_);
lean_dec(v_second_111_);
v___x_129_ = lean_array_get_size(v_transitions_113_);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_nat_sub(v___x_129_, v___x_130_);
v___x_132_ = lean_nat_dec_lt(v___x_131_, v___x_129_);
if (v___x_132_ == 0)
{
lean_dec(v___x_131_);
lean_inc_ref(v_initialLocalTimeType_112_);
v___y_91_ = v_initialLocalTimeType_112_;
goto v___jp_90_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = lean_array_fget_borrowed(v_transitions_113_, v___x_131_);
lean_dec(v___x_131_);
lean_inc(v___x_133_);
v_val_109_ = v___x_133_;
goto v___jp_108_;
}
}
v___jp_90_:
{
lean_object* v_second_92_; lean_object* v_nano_93_; lean_object* v_tz_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_tm_104_; lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_second_92_ = lean_ctor_get(v_tm_89_, 0);
lean_inc(v_second_92_);
v_nano_93_ = lean_ctor_get(v_tm_89_, 1);
lean_inc(v_nano_93_);
lean_dec_ref(v_tm_89_);
v_tz_94_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_91_);
lean_dec_ref(v___y_91_);
v___x_95_ = l_Std_Time_TimeZone_toSeconds(v_tz_94_);
v___x_96_ = lean_int_neg(v___x_95_);
v___x_97_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_98_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_99_ = lean_int_mul(v_second_92_, v___x_98_);
lean_dec(v_second_92_);
v___x_100_ = lean_int_add(v___x_99_, v_nano_93_);
lean_dec(v_nano_93_);
lean_dec(v___x_99_);
v___x_101_ = lean_int_mul(v___x_96_, v___x_98_);
lean_dec(v___x_96_);
v___x_102_ = lean_int_add(v___x_101_, v___x_97_);
lean_dec(v___x_101_);
v___x_103_ = lean_int_add(v___x_100_, v___x_102_);
lean_dec(v___x_102_);
lean_dec(v___x_100_);
v_tm_104_ = l_Std_Time_Duration_ofNanoseconds(v___x_103_);
lean_dec(v___x_103_);
lean_inc_ref(v_tm_104_);
v___f_105_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_105_, 0, v_tm_104_);
lean_closure_set(v___f_105_, 1, v___x_95_);
lean_closure_set(v___f_105_, 2, v___x_98_);
v___x_106_ = lean_mk_thunk(v___f_105_);
v___x_107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_tm_104_);
lean_ctor_set(v___x_107_, 2, v_zr_88_);
lean_ctor_set(v___x_107_, 3, v_tz_94_);
return v___x_107_;
}
v___jp_108_:
{
lean_object* v_localTimeType_110_; 
v_localTimeType_110_ = lean_ctor_get(v_val_109_, 1);
lean_inc_ref(v_localTimeType_110_);
lean_dec_ref(v_val_109_);
v___y_91_ = v_localTimeType_110_;
goto v___jp_90_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone(lean_object* v_tm_136_, lean_object* v_tz_137_){
_start:
{
lean_object* v_offset_138_; lean_object* v_name_139_; lean_object* v_abbreviation_140_; uint8_t v_isDST_141_; uint8_t v___x_142_; uint8_t v___x_143_; lean_object* v_ltt_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___y_148_; lean_object* v___x_152_; 
v_offset_138_ = lean_ctor_get(v_tz_137_, 0);
v_name_139_ = lean_ctor_get(v_tz_137_, 1);
v_abbreviation_140_ = lean_ctor_get(v_tz_137_, 2);
v_isDST_141_ = lean_ctor_get_uint8(v_tz_137_, sizeof(void*)*3);
v___x_142_ = 0;
v___x_143_ = 1;
lean_inc_ref(v_name_139_);
lean_inc_ref(v_abbreviation_140_);
lean_inc(v_offset_138_);
v_ltt_144_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_144_, 0, v_offset_138_);
lean_ctor_set(v_ltt_144_, 1, v_abbreviation_140_);
lean_ctor_set(v_ltt_144_, 2, v_name_139_);
lean_ctor_set_uint8(v_ltt_144_, sizeof(void*)*3, v_isDST_141_);
lean_ctor_set_uint8(v_ltt_144_, sizeof(void*)*3 + 1, v___x_142_);
lean_ctor_set_uint8(v_ltt_144_, sizeof(void*)*3 + 2, v___x_143_);
v___x_145_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
lean_inc_ref(v_ltt_144_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v_ltt_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
lean_inc_ref(v_tm_136_);
v___x_152_ = l_Std_Time_TimeZone_Transition_timezoneAt(v___x_145_, v_tm_136_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v___x_153_; 
lean_dec_ref(v___x_152_);
v___x_153_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_144_);
lean_dec_ref(v_ltt_144_);
v___y_148_ = v___x_153_;
goto v___jp_147_;
}
else
{
lean_object* v_a_154_; 
lean_dec_ref(v_ltt_144_);
v_a_154_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_154_);
lean_dec_ref(v___x_152_);
v___y_148_ = v_a_154_;
goto v___jp_147_;
}
v___jp_147_:
{
lean_object* v___f_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_inc_ref(v___y_148_);
lean_inc_ref(v_tm_136_);
v___f_149_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_149_, 0, v_tm_136_);
lean_closure_set(v___f_149_, 1, v___y_148_);
v___x_150_ = lean_mk_thunk(v___f_149_);
v___x_151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_tm_136_);
lean_ctor_set(v___x_151_, 2, v___x_146_);
lean_ctor_set(v___x_151_, 3, v___y_148_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofTimestampWithZone___boxed(lean_object* v_tm_155_, lean_object* v_tz_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Time_ZonedDateTime_ofTimestampWithZone(v_tm_155_, v_tz_156_);
lean_dec_ref(v_tz_156_);
return v_res_157_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
v___x_159_ = lean_array_get_size(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_unsigned_to_nat(1u);
v___x_161_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0);
v___x_162_ = lean_nat_sub(v___x_161_, v___x_160_);
return v___x_162_;
}
}
static uint8_t _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__0);
v___x_164_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1);
v___x_165_ = lean_nat_dec_lt(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__1);
v___x_167_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
v___x_168_ = lean_array_fget(v___x_167_, v___x_166_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(lean_object* v_tm_169_, lean_object* v_tz_170_){
_start:
{
lean_object* v_offset_171_; lean_object* v_name_172_; lean_object* v_abbreviation_173_; uint8_t v_isDST_174_; lean_object* v_tm_175_; lean_object* v_second_176_; uint8_t v___x_177_; uint8_t v___x_178_; lean_object* v_ltt_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___y_184_; lean_object* v_val_202_; lean_object* v___f_204_; lean_object* v___x_205_; 
v_offset_171_ = lean_ctor_get(v_tz_170_, 0);
v_name_172_ = lean_ctor_get(v_tz_170_, 1);
v_abbreviation_173_ = lean_ctor_get(v_tz_170_, 2);
v_isDST_174_ = lean_ctor_get_uint8(v_tz_170_, sizeof(void*)*3);
v_tm_175_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_tm_169_);
v_second_176_ = lean_ctor_get(v_tm_175_, 0);
lean_inc(v_second_176_);
v___x_177_ = 0;
v___x_178_ = 1;
lean_inc_ref(v_name_172_);
lean_inc_ref(v_abbreviation_173_);
lean_inc(v_offset_171_);
v_ltt_179_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_179_, 0, v_offset_171_);
lean_ctor_set(v_ltt_179_, 1, v_abbreviation_173_);
lean_ctor_set(v_ltt_179_, 2, v_name_172_);
lean_ctor_set_uint8(v_ltt_179_, sizeof(void*)*3, v_isDST_174_);
lean_ctor_set_uint8(v_ltt_179_, sizeof(void*)*3 + 1, v___x_177_);
lean_ctor_set_uint8(v_ltt_179_, sizeof(void*)*3 + 2, v___x_178_);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = ((lean_object*)(l_Std_Time_ZonedDateTime_ofTimestampWithZone___closed__0));
lean_inc_ref(v_ltt_179_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_ltt_179_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
lean_inc(v_second_176_);
v___f_204_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_204_, 0, v_second_176_);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_204_, v___x_181_, v___x_180_);
if (lean_obj_tag(v___x_205_) == 1)
{
lean_object* v_val_206_; lean_object* v_next_207_; lean_object* v_time_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_last_211_; lean_object* v_localTimeType_212_; lean_object* v_gmtOffset_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; 
lean_dec_ref(v_ltt_179_);
v_val_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_206_);
lean_dec_ref(v___x_205_);
v_next_207_ = lean_array_fget(v___x_181_, v_val_206_);
v_time_208_ = lean_ctor_get(v_next_207_, 0);
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_sub(v_val_206_, v___x_209_);
lean_dec(v_val_206_);
v_last_211_ = lean_array_fget(v___x_181_, v___x_210_);
lean_dec(v___x_210_);
v_localTimeType_212_ = lean_ctor_get(v_last_211_, 1);
v_gmtOffset_213_ = lean_ctor_get(v_localTimeType_212_, 0);
v___x_214_ = lean_nat_abs(v_gmtOffset_213_);
v___x_215_ = lean_nat_to_int(v___x_214_);
v___x_216_ = lean_int_sub(v_time_208_, v___x_215_);
lean_dec(v___x_215_);
v___x_217_ = lean_int_dec_lt(v_second_176_, v___x_216_);
lean_dec(v___x_216_);
lean_dec(v_second_176_);
if (v___x_217_ == 0)
{
lean_dec(v_last_211_);
v_val_202_ = v_next_207_;
goto v___jp_201_;
}
else
{
lean_dec(v_next_207_);
v_val_202_ = v_last_211_;
goto v___jp_201_;
}
}
else
{
uint8_t v___x_218_; 
lean_dec(v___x_205_);
lean_dec(v_second_176_);
v___x_218_ = lean_uint8_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__2);
if (v___x_218_ == 0)
{
v___y_184_ = v_ltt_179_;
goto v___jp_183_;
}
else
{
lean_object* v___x_219_; 
lean_dec_ref(v_ltt_179_);
v___x_219_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3, &l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___closed__3);
v_val_202_ = v___x_219_;
goto v___jp_201_;
}
}
v___jp_183_:
{
lean_object* v_second_185_; lean_object* v_nano_186_; lean_object* v_tz_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_tm_197_; lean_object* v___f_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_second_185_ = lean_ctor_get(v_tm_175_, 0);
lean_inc(v_second_185_);
v_nano_186_ = lean_ctor_get(v_tm_175_, 1);
lean_inc(v_nano_186_);
lean_dec_ref(v_tm_175_);
v_tz_187_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_184_);
lean_dec_ref(v___y_184_);
v___x_188_ = l_Std_Time_TimeZone_toSeconds(v_tz_187_);
v___x_189_ = lean_int_neg(v___x_188_);
v___x_190_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_191_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_192_ = lean_int_mul(v_second_185_, v___x_191_);
lean_dec(v_second_185_);
v___x_193_ = lean_int_add(v___x_192_, v_nano_186_);
lean_dec(v_nano_186_);
lean_dec(v___x_192_);
v___x_194_ = lean_int_mul(v___x_189_, v___x_191_);
lean_dec(v___x_189_);
v___x_195_ = lean_int_add(v___x_194_, v___x_190_);
lean_dec(v___x_194_);
v___x_196_ = lean_int_add(v___x_193_, v___x_195_);
lean_dec(v___x_195_);
lean_dec(v___x_193_);
v_tm_197_ = l_Std_Time_Duration_ofNanoseconds(v___x_196_);
lean_dec(v___x_196_);
lean_inc_ref(v_tm_197_);
v___f_198_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_198_, 0, v_tm_197_);
lean_closure_set(v___f_198_, 1, v___x_188_);
lean_closure_set(v___f_198_, 2, v___x_191_);
v___x_199_ = lean_mk_thunk(v___f_198_);
v___x_200_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v_tm_197_);
lean_ctor_set(v___x_200_, 2, v___x_182_);
lean_ctor_set(v___x_200_, 3, v_tz_187_);
return v___x_200_;
}
v___jp_201_:
{
lean_object* v_localTimeType_203_; 
v_localTimeType_203_ = lean_ctor_get(v_val_202_, 1);
lean_inc_ref(v_localTimeType_203_);
lean_dec_ref(v_val_202_);
v___y_184_ = v_localTimeType_203_;
goto v___jp_183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone___boxed(lean_object* v_tm_220_, lean_object* v_tz_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeWithZone(v_tm_220_, v_tz_221_);
lean_dec_ref(v_tz_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp(lean_object* v_date_223_){
_start:
{
lean_object* v_timestamp_224_; 
v_timestamp_224_ = lean_ctor_get(v_date_223_, 1);
lean_inc_ref(v_timestamp_224_);
return v_timestamp_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toTimestamp___boxed(lean_object* v_date_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_Time_ZonedDateTime_toTimestamp(v_date_225_);
lean_dec_ref(v_date_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(lean_object* v_timestamp_227_, lean_object* v___y_228_, lean_object* v_x_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_second_232_; lean_object* v_nano_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v_second_238_; lean_object* v_nano_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_230_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_227_);
v___x_231_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_230_);
v_second_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_second_232_);
v_nano_233_ = lean_ctor_get(v___x_231_, 1);
lean_inc(v_nano_233_);
lean_dec_ref(v___x_231_);
v___x_234_ = l_Std_Time_TimeZone_toSeconds(v___y_228_);
v___x_235_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_236_ = lean_int_mul(v___x_234_, v___x_235_);
lean_dec(v___x_234_);
v___x_237_ = l_Std_Time_Duration_ofNanoseconds(v___x_236_);
lean_dec(v___x_236_);
v_second_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_second_238_);
v_nano_239_ = lean_ctor_get(v___x_237_, 1);
lean_inc(v_nano_239_);
lean_dec_ref(v___x_237_);
v___x_240_ = lean_int_mul(v_second_232_, v___x_235_);
lean_dec(v_second_232_);
v___x_241_ = lean_int_add(v___x_240_, v_nano_233_);
lean_dec(v_nano_233_);
lean_dec(v___x_240_);
v___x_242_ = lean_int_mul(v_second_238_, v___x_235_);
lean_dec(v_second_238_);
v___x_243_ = lean_int_add(v___x_242_, v_nano_239_);
lean_dec(v_nano_239_);
lean_dec(v___x_242_);
v___x_244_ = lean_int_add(v___x_241_, v___x_243_);
lean_dec(v___x_243_);
lean_dec(v___x_241_);
v___x_245_ = l_Std_Time_Duration_ofNanoseconds(v___x_244_);
lean_dec(v___x_244_);
v___x_246_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed(lean_object* v_timestamp_247_, lean_object* v___y_248_, lean_object* v_x_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_Time_ZonedDateTime_convertZoneRules___lam__0(v_timestamp_247_, v___y_248_, v_x_249_);
lean_dec_ref(v___y_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_convertZoneRules(lean_object* v_date_251_, lean_object* v_tz_u2081_252_){
_start:
{
lean_object* v_timestamp_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_269_; 
v_timestamp_253_ = lean_ctor_get(v_date_251_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_date_251_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; lean_object* v_unused_271_; lean_object* v_unused_272_; 
v_unused_270_ = lean_ctor_get(v_date_251_, 3);
lean_dec(v_unused_270_);
v_unused_271_ = lean_ctor_get(v_date_251_, 2);
lean_dec(v_unused_271_);
v_unused_272_ = lean_ctor_get(v_date_251_, 0);
lean_dec(v_unused_272_);
v___x_255_ = v_date_251_;
v_isShared_256_ = v_isSharedCheck_269_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_timestamp_253_);
lean_dec(v_date_251_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_269_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___y_258_; lean_object* v_initialLocalTimeType_264_; lean_object* v_transitions_265_; lean_object* v___x_266_; 
v_initialLocalTimeType_264_ = lean_ctor_get(v_tz_u2081_252_, 0);
v_transitions_265_ = lean_ctor_get(v_tz_u2081_252_, 1);
lean_inc_ref(v_timestamp_253_);
v___x_266_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_265_, v_timestamp_253_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v___x_267_; 
lean_dec_ref(v___x_266_);
v___x_267_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_264_);
v___y_258_ = v___x_267_;
goto v___jp_257_;
}
else
{
lean_object* v_a_268_; 
v_a_268_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_a_268_);
lean_dec_ref(v___x_266_);
v___y_258_ = v_a_268_;
goto v___jp_257_;
}
v___jp_257_:
{
lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
lean_inc_ref(v___y_258_);
lean_inc_ref(v_timestamp_253_);
v___f_259_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_convertZoneRules___lam__0___boxed), 3, 2);
lean_closure_set(v___f_259_, 0, v_timestamp_253_);
lean_closure_set(v___f_259_, 1, v___y_258_);
v___x_260_ = lean_mk_thunk(v___f_259_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 3, v___y_258_);
lean_ctor_set(v___x_255_, 2, v_tz_u2081_252_);
lean_ctor_set(v___x_255_, 0, v___x_260_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_timestamp_253_);
lean_ctor_set(v_reuseFailAlloc_263_, 2, v_tz_u2081_252_);
lean_ctor_set(v_reuseFailAlloc_263_, 3, v___y_258_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0(lean_object* v___x_273_, lean_object* v___y_274_, lean_object* v_x_275_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_second_278_; lean_object* v_nano_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_second_284_; lean_object* v_nano_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_276_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_273_);
v___x_277_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_276_);
v_second_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_second_278_);
v_nano_279_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_nano_279_);
lean_dec_ref(v___x_277_);
v___x_280_ = l_Std_Time_TimeZone_toSeconds(v___y_274_);
v___x_281_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_282_ = lean_int_mul(v___x_280_, v___x_281_);
lean_dec(v___x_280_);
v___x_283_ = l_Std_Time_Duration_ofNanoseconds(v___x_282_);
lean_dec(v___x_282_);
v_second_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_second_284_);
v_nano_285_ = lean_ctor_get(v___x_283_, 1);
lean_inc(v_nano_285_);
lean_dec_ref(v___x_283_);
v___x_286_ = lean_int_mul(v_second_278_, v___x_281_);
lean_dec(v_second_278_);
v___x_287_ = lean_int_add(v___x_286_, v_nano_279_);
lean_dec(v_nano_279_);
lean_dec(v___x_286_);
v___x_288_ = lean_int_mul(v_second_284_, v___x_281_);
lean_dec(v_second_284_);
v___x_289_ = lean_int_add(v___x_288_, v_nano_285_);
lean_dec(v_nano_285_);
lean_dec(v___x_288_);
v___x_290_ = lean_int_add(v___x_287_, v___x_289_);
lean_dec(v___x_289_);
lean_dec(v___x_287_);
v___x_291_ = l_Std_Time_Duration_ofNanoseconds(v___x_290_);
lean_dec(v___x_290_);
v___x_292_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed(lean_object* v___x_293_, lean_object* v___y_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0(v___x_293_, v___y_294_, v_x_295_);
lean_dec_ref(v___y_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC(lean_object* v_date_297_, lean_object* v_tz_298_){
_start:
{
lean_object* v_initialLocalTimeType_299_; lean_object* v_transitions_300_; lean_object* v___x_301_; lean_object* v___y_303_; lean_object* v___x_307_; 
v_initialLocalTimeType_299_ = lean_ctor_get(v_tz_298_, 0);
v_transitions_300_ = lean_ctor_get(v_tz_298_, 1);
v___x_301_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_297_);
lean_inc_ref(v___x_301_);
v___x_307_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_300_, v___x_301_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
lean_dec_ref(v___x_307_);
v___x_308_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_299_);
v___y_303_ = v___x_308_;
goto v___jp_302_;
}
else
{
lean_object* v_a_309_; 
v_a_309_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_a_309_);
lean_dec_ref(v___x_307_);
v___y_303_ = v_a_309_;
goto v___jp_302_;
}
v___jp_302_:
{
lean_object* v___f_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_inc_ref(v___y_303_);
lean_inc_ref(v___x_301_);
v___f_304_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_304_, 0, v___x_301_);
lean_closure_set(v___f_304_, 1, v___y_303_);
v___x_305_ = lean_mk_thunk(v___f_304_);
v___x_306_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_301_);
lean_ctor_set(v___x_306_, 2, v_tz_298_);
lean_ctor_set(v___x_306_, 3, v___y_303_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDateTime(lean_object* v_dt_310_){
_start:
{
lean_object* v_date_311_; lean_object* v___x_312_; 
v_date_311_ = lean_ctor_get(v_dt_310_, 0);
v___x_312_ = lean_thunk_get_own(v_date_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toPlainDateTime___boxed(lean_object* v_dt_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Time_ZonedDateTime_toPlainDateTime(v_dt_313_);
lean_dec_ref(v_dt_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime___lam__0(lean_object* v_timestamp_315_, lean_object* v_timezone_316_, lean_object* v_x_317_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_second_320_; lean_object* v_nano_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_second_326_; lean_object* v_nano_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_318_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_315_);
v___x_319_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_318_);
v_second_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_second_320_);
v_nano_321_ = lean_ctor_get(v___x_319_, 1);
lean_inc(v_nano_321_);
lean_dec_ref(v___x_319_);
v___x_322_ = l_Std_Time_TimeZone_toSeconds(v_timezone_316_);
v___x_323_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_324_ = lean_int_mul(v___x_322_, v___x_323_);
lean_dec(v___x_322_);
v___x_325_ = l_Std_Time_Duration_ofNanoseconds(v___x_324_);
lean_dec(v___x_324_);
v_second_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_second_326_);
v_nano_327_ = lean_ctor_get(v___x_325_, 1);
lean_inc(v_nano_327_);
lean_dec_ref(v___x_325_);
v___x_328_ = lean_int_mul(v_second_320_, v___x_323_);
lean_dec(v_second_320_);
v___x_329_ = lean_int_add(v___x_328_, v_nano_321_);
lean_dec(v_nano_321_);
lean_dec(v___x_328_);
v___x_330_ = lean_int_mul(v_second_326_, v___x_323_);
lean_dec(v_second_326_);
v___x_331_ = lean_int_add(v___x_330_, v_nano_327_);
lean_dec(v_nano_327_);
lean_dec(v___x_330_);
v___x_332_ = lean_int_add(v___x_329_, v___x_331_);
lean_dec(v___x_331_);
lean_dec(v___x_329_);
v___x_333_ = l_Std_Time_Duration_ofNanoseconds(v___x_332_);
lean_dec(v___x_332_);
v___x_334_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed(lean_object* v_timestamp_335_, lean_object* v_timezone_336_, lean_object* v_x_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Time_ZonedDateTime_toDateTime___lam__0(v_timestamp_335_, v_timezone_336_, v_x_337_);
lean_dec_ref(v_timezone_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTime(lean_object* v_dt_339_){
_start:
{
lean_object* v_timestamp_340_; lean_object* v_timezone_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_timestamp_340_ = lean_ctor_get(v_dt_339_, 1);
lean_inc_ref(v_timestamp_340_);
v_timezone_341_ = lean_ctor_get(v_dt_339_, 3);
lean_inc_ref(v_timezone_341_);
lean_dec_ref(v_dt_339_);
lean_inc_ref(v_timestamp_340_);
v___f_342_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_toDateTime___lam__0___boxed), 3, 2);
lean_closure_set(v___f_342_, 0, v_timestamp_340_);
lean_closure_set(v___f_342_, 1, v_timezone_341_);
v___x_343_ = lean_mk_thunk(v___f_342_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_timestamp_340_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_time(lean_object* v_zdt_345_){
_start:
{
lean_object* v_date_346_; lean_object* v___x_347_; lean_object* v_time_348_; 
v_date_346_ = lean_ctor_get(v_zdt_345_, 0);
v___x_347_ = lean_thunk_get_own(v_date_346_);
v_time_348_ = lean_ctor_get(v___x_347_, 1);
lean_inc_ref(v_time_348_);
lean_dec(v___x_347_);
return v_time_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_time___boxed(lean_object* v_zdt_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Time_ZonedDateTime_time(v_zdt_349_);
lean_dec_ref(v_zdt_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_year(lean_object* v_zdt_351_){
_start:
{
lean_object* v_date_352_; lean_object* v___x_353_; lean_object* v_date_354_; lean_object* v_year_355_; 
v_date_352_ = lean_ctor_get(v_zdt_351_, 0);
v___x_353_ = lean_thunk_get_own(v_date_352_);
v_date_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc_ref(v_date_354_);
lean_dec(v___x_353_);
v_year_355_ = lean_ctor_get(v_date_354_, 0);
lean_inc(v_year_355_);
lean_dec_ref(v_date_354_);
return v_year_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_year___boxed(lean_object* v_zdt_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_Time_ZonedDateTime_year(v_zdt_356_);
lean_dec_ref(v_zdt_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_month(lean_object* v_zdt_358_){
_start:
{
lean_object* v_date_359_; lean_object* v___x_360_; lean_object* v_date_361_; lean_object* v_month_362_; 
v_date_359_ = lean_ctor_get(v_zdt_358_, 0);
v___x_360_ = lean_thunk_get_own(v_date_359_);
v_date_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_date_361_);
lean_dec(v___x_360_);
v_month_362_ = lean_ctor_get(v_date_361_, 1);
lean_inc(v_month_362_);
lean_dec_ref(v_date_361_);
return v_month_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_month___boxed(lean_object* v_zdt_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_Time_ZonedDateTime_month(v_zdt_363_);
lean_dec_ref(v_zdt_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_day(lean_object* v_zdt_365_){
_start:
{
lean_object* v_date_366_; lean_object* v___x_367_; lean_object* v_date_368_; lean_object* v_day_369_; 
v_date_366_ = lean_ctor_get(v_zdt_365_, 0);
v___x_367_ = lean_thunk_get_own(v_date_366_);
v_date_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_date_368_);
lean_dec(v___x_367_);
v_day_369_ = lean_ctor_get(v_date_368_, 2);
lean_inc(v_day_369_);
lean_dec_ref(v_date_368_);
return v_day_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_day___boxed(lean_object* v_zdt_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_Time_ZonedDateTime_day(v_zdt_370_);
lean_dec_ref(v_zdt_370_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_hour(lean_object* v_zdt_372_){
_start:
{
lean_object* v_date_373_; lean_object* v___x_374_; lean_object* v_time_375_; lean_object* v_hour_376_; 
v_date_373_ = lean_ctor_get(v_zdt_372_, 0);
v___x_374_ = lean_thunk_get_own(v_date_373_);
v_time_375_ = lean_ctor_get(v___x_374_, 1);
lean_inc_ref(v_time_375_);
lean_dec(v___x_374_);
v_hour_376_ = lean_ctor_get(v_time_375_, 0);
lean_inc(v_hour_376_);
lean_dec_ref(v_time_375_);
return v_hour_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_hour___boxed(lean_object* v_zdt_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_Time_ZonedDateTime_hour(v_zdt_377_);
lean_dec_ref(v_zdt_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_minute(lean_object* v_zdt_379_){
_start:
{
lean_object* v_date_380_; lean_object* v___x_381_; lean_object* v_time_382_; lean_object* v_minute_383_; 
v_date_380_ = lean_ctor_get(v_zdt_379_, 0);
v___x_381_ = lean_thunk_get_own(v_date_380_);
v_time_382_ = lean_ctor_get(v___x_381_, 1);
lean_inc_ref(v_time_382_);
lean_dec(v___x_381_);
v_minute_383_ = lean_ctor_get(v_time_382_, 1);
lean_inc(v_minute_383_);
lean_dec_ref(v_time_382_);
return v_minute_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_minute___boxed(lean_object* v_zdt_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_Time_ZonedDateTime_minute(v_zdt_384_);
lean_dec_ref(v_zdt_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_second(lean_object* v_zdt_386_){
_start:
{
lean_object* v_date_387_; lean_object* v___x_388_; lean_object* v_time_389_; lean_object* v_second_390_; 
v_date_387_ = lean_ctor_get(v_zdt_386_, 0);
v___x_388_ = lean_thunk_get_own(v_date_387_);
v_time_389_ = lean_ctor_get(v___x_388_, 1);
lean_inc_ref(v_time_389_);
lean_dec(v___x_388_);
v_second_390_ = lean_ctor_get(v_time_389_, 2);
lean_inc(v_second_390_);
lean_dec_ref(v_time_389_);
return v_second_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_second___boxed(lean_object* v_zdt_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Time_ZonedDateTime_second(v_zdt_391_);
lean_dec_ref(v_zdt_391_);
return v_res_392_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_millisecond___closed__0(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_unsigned_to_nat(1000000u);
v___x_394_ = lean_nat_to_int(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond(lean_object* v_dt_395_){
_start:
{
lean_object* v_date_396_; lean_object* v___x_397_; lean_object* v_time_398_; lean_object* v_nanosecond_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_date_396_ = lean_ctor_get(v_dt_395_, 0);
v___x_397_ = lean_thunk_get_own(v_date_396_);
v_time_398_ = lean_ctor_get(v___x_397_, 1);
lean_inc_ref(v_time_398_);
lean_dec(v___x_397_);
v_nanosecond_399_ = lean_ctor_get(v_time_398_, 3);
lean_inc(v_nanosecond_399_);
lean_dec_ref(v_time_398_);
v___x_400_ = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
v___x_401_ = lean_int_ediv(v_nanosecond_399_, v___x_400_);
lean_dec(v_nanosecond_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_millisecond___boxed(lean_object* v_dt_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_Time_ZonedDateTime_millisecond(v_dt_402_);
lean_dec_ref(v_dt_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond(lean_object* v_zdt_404_){
_start:
{
lean_object* v_date_405_; lean_object* v___x_406_; lean_object* v_time_407_; lean_object* v_nanosecond_408_; 
v_date_405_ = lean_ctor_get(v_zdt_404_, 0);
v___x_406_ = lean_thunk_get_own(v_date_405_);
v_time_407_ = lean_ctor_get(v___x_406_, 1);
lean_inc_ref(v_time_407_);
lean_dec(v___x_406_);
v_nanosecond_408_ = lean_ctor_get(v_time_407_, 3);
lean_inc(v_nanosecond_408_);
lean_dec_ref(v_time_407_);
return v_nanosecond_408_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_nanosecond___boxed(lean_object* v_zdt_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_Time_ZonedDateTime_nanosecond(v_zdt_409_);
lean_dec_ref(v_zdt_409_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset(lean_object* v_zdt_411_){
_start:
{
lean_object* v_timezone_412_; lean_object* v_offset_413_; 
v_timezone_412_ = lean_ctor_get(v_zdt_411_, 3);
v_offset_413_ = lean_ctor_get(v_timezone_412_, 0);
lean_inc(v_offset_413_);
return v_offset_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_offset___boxed(lean_object* v_zdt_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_Time_ZonedDateTime_offset(v_zdt_414_);
lean_dec_ref(v_zdt_414_);
return v_res_415_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_weekday(lean_object* v_zdt_416_){
_start:
{
lean_object* v_date_417_; lean_object* v___x_418_; lean_object* v_date_419_; uint8_t v___x_420_; 
v_date_417_ = lean_ctor_get(v_zdt_416_, 0);
v___x_418_ = lean_thunk_get_own(v_date_417_);
v_date_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc_ref(v_date_419_);
lean_dec(v___x_418_);
v___x_420_ = l_Std_Time_PlainDate_weekday(v_date_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekday___boxed(lean_object* v_zdt_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Std_Time_ZonedDateTime_weekday(v_zdt_421_);
lean_dec_ref(v_zdt_421_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(4u);
v___x_425_ = lean_nat_to_int(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(400u);
v___x_427_ = lean_nat_to_int(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_unsigned_to_nat(100u);
v___x_429_ = lean_nat_to_int(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear(lean_object* v_date_430_){
_start:
{
lean_object* v_date_431_; uint8_t v___y_433_; lean_object* v___x_447_; lean_object* v_date_448_; lean_object* v_year_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_457_; 
v_date_431_ = lean_ctor_get(v_date_430_, 0);
v___x_447_ = lean_thunk_get_own(v_date_431_);
v_date_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_date_448_);
lean_dec(v___x_447_);
v_year_449_ = lean_ctor_get(v_date_448_, 0);
lean_inc(v_year_449_);
lean_dec_ref(v_date_448_);
v___x_450_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_451_ = lean_int_mod(v_year_449_, v___x_450_);
v___x_452_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_457_ = lean_int_dec_eq(v___x_451_, v___x_452_);
lean_dec(v___x_451_);
if (v___x_457_ == 0)
{
lean_dec(v_year_449_);
v___y_433_ = v___x_457_;
goto v___jp_432_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_459_ = lean_int_mod(v_year_449_, v___x_458_);
v___x_460_ = lean_int_dec_eq(v___x_459_, v___x_452_);
lean_dec(v___x_459_);
if (v___x_460_ == 0)
{
if (v___x_457_ == 0)
{
goto v___jp_453_;
}
else
{
lean_dec(v_year_449_);
v___y_433_ = v___x_457_;
goto v___jp_432_;
}
}
else
{
goto v___jp_453_;
}
}
v___jp_432_:
{
lean_object* v___x_434_; lean_object* v_date_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_445_; 
v___x_434_ = lean_thunk_get_own(v_date_431_);
v_date_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_434_, 1);
lean_dec(v_unused_446_);
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_date_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_445_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v_month_439_; lean_object* v_day_440_; lean_object* v___x_442_; 
v_month_439_ = lean_ctor_get(v_date_435_, 1);
lean_inc(v_month_439_);
v_day_440_ = lean_ctor_get(v_date_435_, 2);
lean_inc(v_day_440_);
lean_dec_ref(v_date_435_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v_day_440_);
lean_ctor_set(v___x_437_, 0, v_month_439_);
v___x_442_ = v___x_437_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_month_439_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_day_440_);
v___x_442_ = v_reuseFailAlloc_444_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_Time_ValidDate_dayOfYear(v___y_433_, v___x_442_);
lean_dec_ref(v___x_442_);
return v___x_443_;
}
}
}
v___jp_453_:
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_455_ = lean_int_mod(v_year_449_, v___x_454_);
lean_dec(v_year_449_);
v___x_456_ = lean_int_dec_eq(v___x_455_, v___x_452_);
lean_dec(v___x_455_);
v___y_433_ = v___x_456_;
goto v___jp_432_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_dayOfYear___boxed(lean_object* v_date_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_Time_ZonedDateTime_dayOfYear(v_date_461_);
lean_dec_ref(v_date_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear(lean_object* v_date_463_){
_start:
{
lean_object* v_date_464_; lean_object* v___x_465_; lean_object* v_date_466_; lean_object* v___x_467_; 
v_date_464_ = lean_ctor_get(v_date_463_, 0);
v___x_465_ = lean_thunk_get_own(v_date_464_);
v_date_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc_ref(v_date_466_);
lean_dec(v___x_465_);
v___x_467_ = l_Std_Time_PlainDate_weekOfYear(v_date_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfYear___boxed(lean_object* v_date_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_Time_ZonedDateTime_weekOfYear(v_date_468_);
lean_dec_ref(v_date_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth(lean_object* v_date_470_){
_start:
{
lean_object* v_date_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_date_471_ = lean_ctor_get(v_date_470_, 0);
v___x_472_ = lean_thunk_get_own(v_date_471_);
v___x_473_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_472_);
lean_dec(v___x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_weekOfMonth___boxed(lean_object* v_date_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_Time_ZonedDateTime_weekOfMonth(v_date_474_);
lean_dec_ref(v_date_474_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth(lean_object* v_date_476_){
_start:
{
lean_object* v_date_477_; lean_object* v___x_478_; lean_object* v_date_479_; lean_object* v___x_480_; 
v_date_477_ = lean_ctor_get(v_date_476_, 0);
v___x_478_ = lean_thunk_get_own(v_date_477_);
v_date_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc_ref(v_date_479_);
lean_dec(v___x_478_);
v___x_480_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_alignedWeekOfMonth___boxed(lean_object* v_date_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Time_ZonedDateTime_alignedWeekOfMonth(v_date_481_);
lean_dec_ref(v_date_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter(lean_object* v_date_483_){
_start:
{
lean_object* v_date_484_; lean_object* v___x_485_; lean_object* v_date_486_; lean_object* v___x_487_; 
v_date_484_ = lean_ctor_get(v_date_483_, 0);
v___x_485_ = lean_thunk_get_own(v_date_484_);
v_date_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc_ref(v_date_486_);
lean_dec(v___x_485_);
v___x_487_ = l_Std_Time_PlainDate_quarter(v_date_486_);
lean_dec_ref(v_date_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_quarter___boxed(lean_object* v_date_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_Time_ZonedDateTime_quarter(v_date_488_);
lean_dec_ref(v_date_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays(lean_object* v_dt_490_, lean_object* v_days_491_){
_start:
{
lean_object* v_timestamp_492_; lean_object* v_rules_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_523_; 
v_timestamp_492_ = lean_ctor_get(v_dt_490_, 1);
v_rules_493_ = lean_ctor_get(v_dt_490_, 2);
v_isSharedCheck_523_ = !lean_is_exclusive(v_dt_490_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; lean_object* v_unused_525_; 
v_unused_524_ = lean_ctor_get(v_dt_490_, 3);
lean_dec(v_unused_524_);
v_unused_525_ = lean_ctor_get(v_dt_490_, 0);
lean_dec(v_unused_525_);
v___x_495_ = v_dt_490_;
v_isShared_496_ = v_isSharedCheck_523_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_rules_493_);
lean_inc(v_timestamp_492_);
lean_dec(v_dt_490_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_523_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_date_497_; lean_object* v_date_498_; lean_object* v_time_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_522_; 
v_date_497_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_492_);
v_date_498_ = lean_ctor_get(v_date_497_, 0);
v_time_499_ = lean_ctor_get(v_date_497_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_date_497_);
if (v_isSharedCheck_522_ == 0)
{
v___x_501_ = v_date_497_;
v_isShared_502_ = v_isSharedCheck_522_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_time_499_);
lean_inc(v_date_498_);
lean_dec(v_date_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_522_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_initialLocalTimeType_503_; lean_object* v_transitions_504_; lean_object* v_dateDays_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
v_initialLocalTimeType_503_ = lean_ctor_get(v_rules_493_, 0);
v_transitions_504_ = lean_ctor_get(v_rules_493_, 1);
v_dateDays_505_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_498_);
v___x_506_ = lean_int_add(v_dateDays_505_, v_days_491_);
lean_dec(v_dateDays_505_);
v___x_507_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_506_);
lean_dec(v___x_506_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_507_);
v___x_509_ = v___x_501_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_time_499_);
v___x_509_ = v_reuseFailAlloc_521_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v___y_512_; lean_object* v___x_518_; 
v___x_510_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_509_);
lean_inc_ref(v___x_510_);
v___x_518_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_504_, v___x_510_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v___x_519_; 
lean_dec_ref(v___x_518_);
v___x_519_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_503_);
v___y_512_ = v___x_519_;
goto v___jp_511_;
}
else
{
lean_object* v_a_520_; 
v_a_520_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_520_);
lean_dec_ref(v___x_518_);
v___y_512_ = v_a_520_;
goto v___jp_511_;
}
v___jp_511_:
{
lean_object* v___f_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_inc_ref(v___y_512_);
lean_inc_ref(v___x_510_);
v___f_513_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_513_, 0, v___x_510_);
lean_closure_set(v___f_513_, 1, v___y_512_);
v___x_514_ = lean_mk_thunk(v___f_513_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 3, v___y_512_);
lean_ctor_set(v___x_495_, 1, v___x_510_);
lean_ctor_set(v___x_495_, 0, v___x_514_);
v___x_516_ = v___x_495_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_rules_493_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v___y_512_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addDays___boxed(lean_object* v_dt_526_, lean_object* v_days_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Time_ZonedDateTime_addDays(v_dt_526_, v_days_527_);
lean_dec(v_days_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subDays(lean_object* v_dt_529_, lean_object* v_days_530_){
_start:
{
lean_object* v_timestamp_531_; lean_object* v_rules_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_563_; 
v_timestamp_531_ = lean_ctor_get(v_dt_529_, 1);
v_rules_532_ = lean_ctor_get(v_dt_529_, 2);
v_isSharedCheck_563_ = !lean_is_exclusive(v_dt_529_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; 
v_unused_564_ = lean_ctor_get(v_dt_529_, 3);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_dt_529_, 0);
lean_dec(v_unused_565_);
v___x_534_ = v_dt_529_;
v_isShared_535_ = v_isSharedCheck_563_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_rules_532_);
lean_inc(v_timestamp_531_);
lean_dec(v_dt_529_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_563_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_date_536_; lean_object* v_date_537_; lean_object* v_time_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_562_; 
v_date_536_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_531_);
v_date_537_ = lean_ctor_get(v_date_536_, 0);
v_time_538_ = lean_ctor_get(v_date_536_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_date_536_);
if (v_isSharedCheck_562_ == 0)
{
v___x_540_ = v_date_536_;
v_isShared_541_ = v_isSharedCheck_562_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_time_538_);
lean_inc(v_date_537_);
lean_dec(v_date_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_562_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_initialLocalTimeType_542_; lean_object* v_transitions_543_; lean_object* v___x_544_; lean_object* v_dateDays_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v_initialLocalTimeType_542_ = lean_ctor_get(v_rules_532_, 0);
v_transitions_543_ = lean_ctor_get(v_rules_532_, 1);
v___x_544_ = lean_int_neg(v_days_530_);
v_dateDays_545_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_537_);
v___x_546_ = lean_int_add(v_dateDays_545_, v___x_544_);
lean_dec(v___x_544_);
lean_dec(v_dateDays_545_);
v___x_547_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_546_);
lean_dec(v___x_546_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_547_);
v___x_549_ = v___x_540_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_time_538_);
v___x_549_ = v_reuseFailAlloc_561_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v___y_552_; lean_object* v___x_558_; 
v___x_550_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_549_);
lean_inc_ref(v___x_550_);
v___x_558_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_543_, v___x_550_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; 
lean_dec_ref(v___x_558_);
v___x_559_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_542_);
v___y_552_ = v___x_559_;
goto v___jp_551_;
}
else
{
lean_object* v_a_560_; 
v_a_560_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_560_);
lean_dec_ref(v___x_558_);
v___y_552_ = v_a_560_;
goto v___jp_551_;
}
v___jp_551_:
{
lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
lean_inc_ref(v___y_552_);
lean_inc_ref(v___x_550_);
v___f_553_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_553_, 0, v___x_550_);
lean_closure_set(v___f_553_, 1, v___y_552_);
v___x_554_ = lean_mk_thunk(v___f_553_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 3, v___y_552_);
lean_ctor_set(v___x_534_, 1, v___x_550_);
lean_ctor_set(v___x_534_, 0, v___x_554_);
v___x_556_ = v___x_534_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_rules_532_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v___y_552_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subDays___boxed(lean_object* v_dt_566_, lean_object* v_days_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_Time_ZonedDateTime_subDays(v_dt_566_, v_days_567_);
lean_dec(v_days_567_);
return v_res_568_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(7u);
v___x_570_ = lean_nat_to_int(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addWeeks(lean_object* v_dt_571_, lean_object* v_weeks_572_){
_start:
{
lean_object* v_timestamp_573_; lean_object* v_rules_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_606_; 
v_timestamp_573_ = lean_ctor_get(v_dt_571_, 1);
v_rules_574_ = lean_ctor_get(v_dt_571_, 2);
v_isSharedCheck_606_ = !lean_is_exclusive(v_dt_571_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; lean_object* v_unused_608_; 
v_unused_607_ = lean_ctor_get(v_dt_571_, 3);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_dt_571_, 0);
lean_dec(v_unused_608_);
v___x_576_ = v_dt_571_;
v_isShared_577_ = v_isSharedCheck_606_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_rules_574_);
lean_inc(v_timestamp_573_);
lean_dec(v_dt_571_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_606_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_date_578_; lean_object* v_date_579_; lean_object* v_time_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_605_; 
v_date_578_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_573_);
v_date_579_ = lean_ctor_get(v_date_578_, 0);
v_time_580_ = lean_ctor_get(v_date_578_, 1);
v_isSharedCheck_605_ = !lean_is_exclusive(v_date_578_);
if (v_isSharedCheck_605_ == 0)
{
v___x_582_ = v_date_578_;
v_isShared_583_ = v_isSharedCheck_605_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_time_580_);
lean_inc(v_date_579_);
lean_dec(v_date_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_605_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_initialLocalTimeType_584_; lean_object* v_transitions_585_; lean_object* v_dateDays_586_; lean_object* v___x_587_; lean_object* v_daysToAdd_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v_initialLocalTimeType_584_ = lean_ctor_get(v_rules_574_, 0);
v_transitions_585_ = lean_ctor_get(v_rules_574_, 1);
v_dateDays_586_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_579_);
v___x_587_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addWeeks___closed__0, &l_Std_Time_ZonedDateTime_addWeeks___closed__0_once, _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0);
v_daysToAdd_588_ = lean_int_mul(v_weeks_572_, v___x_587_);
v___x_589_ = lean_int_add(v_dateDays_586_, v_daysToAdd_588_);
lean_dec(v_daysToAdd_588_);
lean_dec(v_dateDays_586_);
v___x_590_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_589_);
lean_dec(v___x_589_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_590_);
v___x_592_ = v___x_582_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_time_580_);
v___x_592_ = v_reuseFailAlloc_604_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v___y_595_; lean_object* v___x_601_; 
v___x_593_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_592_);
lean_inc_ref(v___x_593_);
v___x_601_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_585_, v___x_593_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v___x_602_; 
lean_dec_ref(v___x_601_);
v___x_602_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_584_);
v___y_595_ = v___x_602_;
goto v___jp_594_;
}
else
{
lean_object* v_a_603_; 
v_a_603_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_603_);
lean_dec_ref(v___x_601_);
v___y_595_ = v_a_603_;
goto v___jp_594_;
}
v___jp_594_:
{
lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
lean_inc_ref(v___y_595_);
lean_inc_ref(v___x_593_);
v___f_596_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_596_, 0, v___x_593_);
lean_closure_set(v___f_596_, 1, v___y_595_);
v___x_597_ = lean_mk_thunk(v___f_596_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 3, v___y_595_);
lean_ctor_set(v___x_576_, 1, v___x_593_);
lean_ctor_set(v___x_576_, 0, v___x_597_);
v___x_599_ = v___x_576_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_rules_574_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v___y_595_);
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
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addWeeks___boxed(lean_object* v_dt_609_, lean_object* v_weeks_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_Time_ZonedDateTime_addWeeks(v_dt_609_, v_weeks_610_);
lean_dec(v_weeks_610_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subWeeks(lean_object* v_dt_612_, lean_object* v_weeks_613_){
_start:
{
lean_object* v_timestamp_614_; lean_object* v_rules_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_648_; 
v_timestamp_614_ = lean_ctor_get(v_dt_612_, 1);
v_rules_615_ = lean_ctor_get(v_dt_612_, 2);
v_isSharedCheck_648_ = !lean_is_exclusive(v_dt_612_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; lean_object* v_unused_650_; 
v_unused_649_ = lean_ctor_get(v_dt_612_, 3);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v_dt_612_, 0);
lean_dec(v_unused_650_);
v___x_617_ = v_dt_612_;
v_isShared_618_ = v_isSharedCheck_648_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_rules_615_);
lean_inc(v_timestamp_614_);
lean_dec(v_dt_612_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_648_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_date_619_; lean_object* v_date_620_; lean_object* v_time_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_647_; 
v_date_619_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_614_);
v_date_620_ = lean_ctor_get(v_date_619_, 0);
v_time_621_ = lean_ctor_get(v_date_619_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_date_619_);
if (v_isSharedCheck_647_ == 0)
{
v___x_623_ = v_date_619_;
v_isShared_624_ = v_isSharedCheck_647_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_time_621_);
lean_inc(v_date_620_);
lean_dec(v_date_619_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_647_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v_initialLocalTimeType_625_; lean_object* v_transitions_626_; lean_object* v___x_627_; lean_object* v_dateDays_628_; lean_object* v___x_629_; lean_object* v_daysToAdd_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v_initialLocalTimeType_625_ = lean_ctor_get(v_rules_615_, 0);
v_transitions_626_ = lean_ctor_get(v_rules_615_, 1);
v___x_627_ = lean_int_neg(v_weeks_613_);
v_dateDays_628_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_620_);
v___x_629_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addWeeks___closed__0, &l_Std_Time_ZonedDateTime_addWeeks___closed__0_once, _init_l_Std_Time_ZonedDateTime_addWeeks___closed__0);
v_daysToAdd_630_ = lean_int_mul(v___x_627_, v___x_629_);
lean_dec(v___x_627_);
v___x_631_ = lean_int_add(v_dateDays_628_, v_daysToAdd_630_);
lean_dec(v_daysToAdd_630_);
lean_dec(v_dateDays_628_);
v___x_632_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v___x_631_);
lean_dec(v___x_631_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_632_);
v___x_634_ = v___x_623_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_time_621_);
v___x_634_ = v_reuseFailAlloc_646_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___y_637_; lean_object* v___x_643_; 
v___x_635_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_634_);
lean_inc_ref(v___x_635_);
v___x_643_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_626_, v___x_635_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v___x_644_; 
lean_dec_ref(v___x_643_);
v___x_644_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_625_);
v___y_637_ = v___x_644_;
goto v___jp_636_;
}
else
{
lean_object* v_a_645_; 
v_a_645_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_645_);
lean_dec_ref(v___x_643_);
v___y_637_ = v_a_645_;
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v___f_638_; lean_object* v___x_639_; lean_object* v___x_641_; 
lean_inc_ref(v___y_637_);
lean_inc_ref(v___x_635_);
v___f_638_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_638_, 0, v___x_635_);
lean_closure_set(v___f_638_, 1, v___y_637_);
v___x_639_ = lean_mk_thunk(v___f_638_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 3, v___y_637_);
lean_ctor_set(v___x_617_, 1, v___x_635_);
lean_ctor_set(v___x_617_, 0, v___x_639_);
v___x_641_ = v___x_617_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_rules_615_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v___y_637_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subWeeks___boxed(lean_object* v_dt_651_, lean_object* v_weeks_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Std_Time_ZonedDateTime_subWeeks(v_dt_651_, v_weeks_652_);
lean_dec(v_weeks_652_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip(lean_object* v_dt_654_, lean_object* v_months_655_){
_start:
{
lean_object* v_rules_656_; lean_object* v_timestamp_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_676_; 
v_rules_656_ = lean_ctor_get(v_dt_654_, 2);
v_timestamp_657_ = lean_ctor_get(v_dt_654_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_dt_654_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; lean_object* v_unused_678_; 
v_unused_677_ = lean_ctor_get(v_dt_654_, 3);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_dt_654_, 0);
lean_dec(v_unused_678_);
v___x_659_ = v_dt_654_;
v_isShared_660_ = v_isSharedCheck_676_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_rules_656_);
lean_inc(v_timestamp_657_);
lean_dec(v_dt_654_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_676_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_initialLocalTimeType_661_; lean_object* v_transitions_662_; lean_object* v_date_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___y_667_; lean_object* v___x_673_; 
v_initialLocalTimeType_661_ = lean_ctor_get(v_rules_656_, 0);
v_transitions_662_ = lean_ctor_get(v_rules_656_, 1);
v_date_663_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_657_);
v___x_664_ = l_Std_Time_PlainDateTime_addMonthsClip(v_date_663_, v_months_655_);
v___x_665_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_664_);
lean_inc_ref(v___x_665_);
v___x_673_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_662_, v___x_665_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v___x_674_; 
lean_dec_ref(v___x_673_);
v___x_674_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_661_);
v___y_667_ = v___x_674_;
goto v___jp_666_;
}
else
{
lean_object* v_a_675_; 
v_a_675_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_675_);
lean_dec_ref(v___x_673_);
v___y_667_ = v_a_675_;
goto v___jp_666_;
}
v___jp_666_:
{
lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
lean_inc_ref(v___y_667_);
lean_inc_ref(v___x_665_);
v___f_668_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_668_, 0, v___x_665_);
lean_closure_set(v___f_668_, 1, v___y_667_);
v___x_669_ = lean_mk_thunk(v___f_668_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 3, v___y_667_);
lean_ctor_set(v___x_659_, 1, v___x_665_);
lean_ctor_set(v___x_659_, 0, v___x_669_);
v___x_671_ = v___x_659_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_rules_656_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v___y_667_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsClip___boxed(lean_object* v_dt_679_, lean_object* v_months_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_Time_ZonedDateTime_addMonthsClip(v_dt_679_, v_months_680_);
lean_dec(v_months_680_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip(lean_object* v_dt_682_, lean_object* v_months_683_){
_start:
{
lean_object* v_timestamp_684_; lean_object* v_rules_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_714_; 
v_timestamp_684_ = lean_ctor_get(v_dt_682_, 1);
v_rules_685_ = lean_ctor_get(v_dt_682_, 2);
v_isSharedCheck_714_ = !lean_is_exclusive(v_dt_682_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; lean_object* v_unused_716_; 
v_unused_715_ = lean_ctor_get(v_dt_682_, 3);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_dt_682_, 0);
lean_dec(v_unused_716_);
v___x_687_ = v_dt_682_;
v_isShared_688_ = v_isSharedCheck_714_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_rules_685_);
lean_inc(v_timestamp_684_);
lean_dec(v_dt_682_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_714_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_date_689_; lean_object* v_date_690_; lean_object* v_time_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_713_; 
v_date_689_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_684_);
v_date_690_ = lean_ctor_get(v_date_689_, 0);
v_time_691_ = lean_ctor_get(v_date_689_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_date_689_);
if (v_isSharedCheck_713_ == 0)
{
v___x_693_ = v_date_689_;
v_isShared_694_ = v_isSharedCheck_713_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_time_691_);
lean_inc(v_date_690_);
lean_dec(v_date_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_713_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_initialLocalTimeType_695_; lean_object* v_transitions_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v_initialLocalTimeType_695_ = lean_ctor_get(v_rules_685_, 0);
v_transitions_696_ = lean_ctor_get(v_rules_685_, 1);
v___x_697_ = lean_int_neg(v_months_683_);
v___x_698_ = l_Std_Time_PlainDate_addMonthsClip(v_date_690_, v___x_697_);
lean_dec(v___x_697_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_698_);
v___x_700_ = v___x_693_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_time_691_);
v___x_700_ = v_reuseFailAlloc_712_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_701_; lean_object* v___y_703_; lean_object* v___x_709_; 
v___x_701_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_700_);
lean_inc_ref(v___x_701_);
v___x_709_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_696_, v___x_701_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_710_; 
lean_dec_ref(v___x_709_);
v___x_710_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_695_);
v___y_703_ = v___x_710_;
goto v___jp_702_;
}
else
{
lean_object* v_a_711_; 
v_a_711_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_711_);
lean_dec_ref(v___x_709_);
v___y_703_ = v_a_711_;
goto v___jp_702_;
}
v___jp_702_:
{
lean_object* v___f_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
lean_inc_ref(v___y_703_);
lean_inc_ref(v___x_701_);
v___f_704_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_704_, 0, v___x_701_);
lean_closure_set(v___f_704_, 1, v___y_703_);
v___x_705_ = lean_mk_thunk(v___f_704_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 3, v___y_703_);
lean_ctor_set(v___x_687_, 1, v___x_701_);
lean_ctor_set(v___x_687_, 0, v___x_705_);
v___x_707_ = v___x_687_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_rules_685_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v___y_703_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsClip___boxed(lean_object* v_dt_717_, lean_object* v_months_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_Time_ZonedDateTime_subMonthsClip(v_dt_717_, v_months_718_);
lean_dec(v_months_718_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver(lean_object* v_dt_720_, lean_object* v_months_721_){
_start:
{
lean_object* v_rules_722_; lean_object* v_timestamp_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_742_; 
v_rules_722_ = lean_ctor_get(v_dt_720_, 2);
v_timestamp_723_ = lean_ctor_get(v_dt_720_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_dt_720_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; lean_object* v_unused_744_; 
v_unused_743_ = lean_ctor_get(v_dt_720_, 3);
lean_dec(v_unused_743_);
v_unused_744_ = lean_ctor_get(v_dt_720_, 0);
lean_dec(v_unused_744_);
v___x_725_ = v_dt_720_;
v_isShared_726_ = v_isSharedCheck_742_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_rules_722_);
lean_inc(v_timestamp_723_);
lean_dec(v_dt_720_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_742_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v_initialLocalTimeType_727_; lean_object* v_transitions_728_; lean_object* v_date_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___y_733_; lean_object* v___x_739_; 
v_initialLocalTimeType_727_ = lean_ctor_get(v_rules_722_, 0);
v_transitions_728_ = lean_ctor_get(v_rules_722_, 1);
v_date_729_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_723_);
v___x_730_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_date_729_, v_months_721_);
v___x_731_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_730_);
lean_inc_ref(v___x_731_);
v___x_739_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_728_, v___x_731_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v___x_739_);
v___x_740_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_727_);
v___y_733_ = v___x_740_;
goto v___jp_732_;
}
else
{
lean_object* v_a_741_; 
v_a_741_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_741_);
lean_dec_ref(v___x_739_);
v___y_733_ = v_a_741_;
goto v___jp_732_;
}
v___jp_732_:
{
lean_object* v___f_734_; lean_object* v___x_735_; lean_object* v___x_737_; 
lean_inc_ref(v___y_733_);
lean_inc_ref(v___x_731_);
v___f_734_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_734_, 0, v___x_731_);
lean_closure_set(v___f_734_, 1, v___y_733_);
v___x_735_ = lean_mk_thunk(v___f_734_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 3, v___y_733_);
lean_ctor_set(v___x_725_, 1, v___x_731_);
lean_ctor_set(v___x_725_, 0, v___x_735_);
v___x_737_ = v___x_725_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_738_, 2, v_rules_722_);
lean_ctor_set(v_reuseFailAlloc_738_, 3, v___y_733_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMonthsRollOver___boxed(lean_object* v_dt_745_, lean_object* v_months_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_Time_ZonedDateTime_addMonthsRollOver(v_dt_745_, v_months_746_);
lean_dec(v_months_746_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsRollOver(lean_object* v_dt_748_, lean_object* v_months_749_){
_start:
{
lean_object* v_timestamp_750_; lean_object* v_rules_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_780_; 
v_timestamp_750_ = lean_ctor_get(v_dt_748_, 1);
v_rules_751_ = lean_ctor_get(v_dt_748_, 2);
v_isSharedCheck_780_ = !lean_is_exclusive(v_dt_748_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; lean_object* v_unused_782_; 
v_unused_781_ = lean_ctor_get(v_dt_748_, 3);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_dt_748_, 0);
lean_dec(v_unused_782_);
v___x_753_ = v_dt_748_;
v_isShared_754_ = v_isSharedCheck_780_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_rules_751_);
lean_inc(v_timestamp_750_);
lean_dec(v_dt_748_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_780_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_date_755_; lean_object* v_date_756_; lean_object* v_time_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_779_; 
v_date_755_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_750_);
v_date_756_ = lean_ctor_get(v_date_755_, 0);
v_time_757_ = lean_ctor_get(v_date_755_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_date_755_);
if (v_isSharedCheck_779_ == 0)
{
v___x_759_ = v_date_755_;
v_isShared_760_ = v_isSharedCheck_779_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_time_757_);
lean_inc(v_date_756_);
lean_dec(v_date_755_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_779_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_initialLocalTimeType_761_; lean_object* v_transitions_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v_initialLocalTimeType_761_ = lean_ctor_get(v_rules_751_, 0);
v_transitions_762_ = lean_ctor_get(v_rules_751_, 1);
v___x_763_ = lean_int_neg(v_months_749_);
v___x_764_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_756_, v___x_763_);
lean_dec(v___x_763_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_764_);
v___x_766_ = v___x_759_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_time_757_);
v___x_766_ = v_reuseFailAlloc_778_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
lean_object* v___x_767_; lean_object* v___y_769_; lean_object* v___x_775_; 
v___x_767_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_766_);
lean_inc_ref(v___x_767_);
v___x_775_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_762_, v___x_767_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_776_; 
lean_dec_ref(v___x_775_);
v___x_776_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_761_);
v___y_769_ = v___x_776_;
goto v___jp_768_;
}
else
{
lean_object* v_a_777_; 
v_a_777_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_777_);
lean_dec_ref(v___x_775_);
v___y_769_ = v_a_777_;
goto v___jp_768_;
}
v___jp_768_:
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_inc_ref(v___y_769_);
lean_inc_ref(v___x_767_);
v___f_770_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_770_, 0, v___x_767_);
lean_closure_set(v___f_770_, 1, v___y_769_);
v___x_771_ = lean_mk_thunk(v___f_770_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 3, v___y_769_);
lean_ctor_set(v___x_753_, 1, v___x_767_);
lean_ctor_set(v___x_753_, 0, v___x_771_);
v___x_773_ = v___x_753_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_774_, 2, v_rules_751_);
lean_ctor_set(v_reuseFailAlloc_774_, 3, v___y_769_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMonthsRollOver___boxed(lean_object* v_dt_783_, lean_object* v_months_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_Time_ZonedDateTime_subMonthsRollOver(v_dt_783_, v_months_784_);
lean_dec(v_months_784_);
return v_res_785_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_unsigned_to_nat(12u);
v___x_787_ = lean_nat_to_int(v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsRollOver(lean_object* v_dt_788_, lean_object* v_years_789_){
_start:
{
lean_object* v_timestamp_790_; lean_object* v_rules_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_821_; 
v_timestamp_790_ = lean_ctor_get(v_dt_788_, 1);
v_rules_791_ = lean_ctor_get(v_dt_788_, 2);
v_isSharedCheck_821_ = !lean_is_exclusive(v_dt_788_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; lean_object* v_unused_823_; 
v_unused_822_ = lean_ctor_get(v_dt_788_, 3);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_dt_788_, 0);
lean_dec(v_unused_823_);
v___x_793_ = v_dt_788_;
v_isShared_794_ = v_isSharedCheck_821_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_rules_791_);
lean_inc(v_timestamp_790_);
lean_dec(v_dt_788_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_821_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_date_795_; lean_object* v_date_796_; lean_object* v_time_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_820_; 
v_date_795_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_790_);
v_date_796_ = lean_ctor_get(v_date_795_, 0);
v_time_797_ = lean_ctor_get(v_date_795_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_date_795_);
if (v_isSharedCheck_820_ == 0)
{
v___x_799_ = v_date_795_;
v_isShared_800_ = v_isSharedCheck_820_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_time_797_);
lean_inc(v_date_796_);
lean_dec(v_date_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_820_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_initialLocalTimeType_801_; lean_object* v_transitions_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
v_initialLocalTimeType_801_ = lean_ctor_get(v_rules_791_, 0);
v_transitions_802_ = lean_ctor_get(v_rules_791_, 1);
v___x_803_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
v___x_804_ = lean_int_mul(v_years_789_, v___x_803_);
v___x_805_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_796_, v___x_804_);
lean_dec(v___x_804_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_805_);
v___x_807_ = v___x_799_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_time_797_);
v___x_807_ = v_reuseFailAlloc_819_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_808_; lean_object* v___y_810_; lean_object* v___x_816_; 
v___x_808_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_807_);
lean_inc_ref(v___x_808_);
v___x_816_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_802_, v___x_808_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v___x_817_; 
lean_dec_ref(v___x_816_);
v___x_817_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_801_);
v___y_810_ = v___x_817_;
goto v___jp_809_;
}
else
{
lean_object* v_a_818_; 
v_a_818_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_818_);
lean_dec_ref(v___x_816_);
v___y_810_ = v_a_818_;
goto v___jp_809_;
}
v___jp_809_:
{
lean_object* v___f_811_; lean_object* v___x_812_; lean_object* v___x_814_; 
lean_inc_ref(v___y_810_);
lean_inc_ref(v___x_808_);
v___f_811_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_811_, 0, v___x_808_);
lean_closure_set(v___f_811_, 1, v___y_810_);
v___x_812_ = lean_mk_thunk(v___f_811_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 3, v___y_810_);
lean_ctor_set(v___x_793_, 1, v___x_808_);
lean_ctor_set(v___x_793_, 0, v___x_812_);
v___x_814_ = v___x_793_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_rules_791_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v___y_810_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsRollOver___boxed(lean_object* v_dt_824_, lean_object* v_years_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_Time_ZonedDateTime_addYearsRollOver(v_dt_824_, v_years_825_);
lean_dec(v_years_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsClip(lean_object* v_dt_827_, lean_object* v_years_828_){
_start:
{
lean_object* v_timestamp_829_; lean_object* v_rules_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_860_; 
v_timestamp_829_ = lean_ctor_get(v_dt_827_, 1);
v_rules_830_ = lean_ctor_get(v_dt_827_, 2);
v_isSharedCheck_860_ = !lean_is_exclusive(v_dt_827_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; lean_object* v_unused_862_; 
v_unused_861_ = lean_ctor_get(v_dt_827_, 3);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_dt_827_, 0);
lean_dec(v_unused_862_);
v___x_832_ = v_dt_827_;
v_isShared_833_ = v_isSharedCheck_860_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_rules_830_);
lean_inc(v_timestamp_829_);
lean_dec(v_dt_827_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_860_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_date_834_; lean_object* v_date_835_; lean_object* v_time_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_859_; 
v_date_834_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_829_);
v_date_835_ = lean_ctor_get(v_date_834_, 0);
v_time_836_ = lean_ctor_get(v_date_834_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_date_834_);
if (v_isSharedCheck_859_ == 0)
{
v___x_838_ = v_date_834_;
v_isShared_839_ = v_isSharedCheck_859_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_time_836_);
lean_inc(v_date_835_);
lean_dec(v_date_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_859_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v_initialLocalTimeType_840_; lean_object* v_transitions_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v_initialLocalTimeType_840_ = lean_ctor_get(v_rules_830_, 0);
v_transitions_841_ = lean_ctor_get(v_rules_830_, 1);
v___x_842_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
v___x_843_ = lean_int_mul(v_years_828_, v___x_842_);
v___x_844_ = l_Std_Time_PlainDate_addMonthsClip(v_date_835_, v___x_843_);
lean_dec(v___x_843_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_844_);
v___x_846_ = v___x_838_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_time_836_);
v___x_846_ = v_reuseFailAlloc_858_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___y_849_; lean_object* v___x_855_; 
v___x_847_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_846_);
lean_inc_ref(v___x_847_);
v___x_855_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_841_, v___x_847_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v___x_856_; 
lean_dec_ref(v___x_855_);
v___x_856_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_840_);
v___y_849_ = v___x_856_;
goto v___jp_848_;
}
else
{
lean_object* v_a_857_; 
v_a_857_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_855_);
v___y_849_ = v_a_857_;
goto v___jp_848_;
}
v___jp_848_:
{
lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
lean_inc_ref(v___y_849_);
lean_inc_ref(v___x_847_);
v___f_850_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_850_, 0, v___x_847_);
lean_closure_set(v___f_850_, 1, v___y_849_);
v___x_851_ = lean_mk_thunk(v___f_850_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 3, v___y_849_);
lean_ctor_set(v___x_832_, 1, v___x_847_);
lean_ctor_set(v___x_832_, 0, v___x_851_);
v___x_853_ = v___x_832_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_854_, 2, v_rules_830_);
lean_ctor_set(v_reuseFailAlloc_854_, 3, v___y_849_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addYearsClip___boxed(lean_object* v_dt_863_, lean_object* v_years_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_Time_ZonedDateTime_addYearsClip(v_dt_863_, v_years_864_);
lean_dec(v_years_864_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsClip(lean_object* v_dt_866_, lean_object* v_years_867_){
_start:
{
lean_object* v_timestamp_868_; lean_object* v_rules_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_900_; 
v_timestamp_868_ = lean_ctor_get(v_dt_866_, 1);
v_rules_869_ = lean_ctor_get(v_dt_866_, 2);
v_isSharedCheck_900_ = !lean_is_exclusive(v_dt_866_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; lean_object* v_unused_902_; 
v_unused_901_ = lean_ctor_get(v_dt_866_, 3);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_dt_866_, 0);
lean_dec(v_unused_902_);
v___x_871_ = v_dt_866_;
v_isShared_872_ = v_isSharedCheck_900_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_rules_869_);
lean_inc(v_timestamp_868_);
lean_dec(v_dt_866_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_900_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_date_873_; lean_object* v_date_874_; lean_object* v_time_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_899_; 
v_date_873_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_868_);
v_date_874_ = lean_ctor_get(v_date_873_, 0);
v_time_875_ = lean_ctor_get(v_date_873_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_date_873_);
if (v_isSharedCheck_899_ == 0)
{
v___x_877_ = v_date_873_;
v_isShared_878_ = v_isSharedCheck_899_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_time_875_);
lean_inc(v_date_874_);
lean_dec(v_date_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_899_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_initialLocalTimeType_879_; lean_object* v_transitions_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v_initialLocalTimeType_879_ = lean_ctor_get(v_rules_869_, 0);
v_transitions_880_ = lean_ctor_get(v_rules_869_, 1);
v___x_881_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
v___x_882_ = lean_int_mul(v_years_867_, v___x_881_);
v___x_883_ = lean_int_neg(v___x_882_);
lean_dec(v___x_882_);
v___x_884_ = l_Std_Time_PlainDate_addMonthsClip(v_date_874_, v___x_883_);
lean_dec(v___x_883_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_884_);
v___x_886_ = v___x_877_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_time_875_);
v___x_886_ = v_reuseFailAlloc_898_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___y_889_; lean_object* v___x_895_; 
v___x_887_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_886_);
lean_inc_ref(v___x_887_);
v___x_895_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_880_, v___x_887_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_896_; 
lean_dec_ref(v___x_895_);
v___x_896_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_879_);
v___y_889_ = v___x_896_;
goto v___jp_888_;
}
else
{
lean_object* v_a_897_; 
v_a_897_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_897_);
lean_dec_ref(v___x_895_);
v___y_889_ = v_a_897_;
goto v___jp_888_;
}
v___jp_888_:
{
lean_object* v___f_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
lean_inc_ref(v___y_889_);
lean_inc_ref(v___x_887_);
v___f_890_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_890_, 0, v___x_887_);
lean_closure_set(v___f_890_, 1, v___y_889_);
v___x_891_ = lean_mk_thunk(v___f_890_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 3, v___y_889_);
lean_ctor_set(v___x_871_, 1, v___x_887_);
lean_ctor_set(v___x_871_, 0, v___x_891_);
v___x_893_ = v___x_871_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_rules_869_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v___y_889_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsClip___boxed(lean_object* v_dt_903_, lean_object* v_years_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_Time_ZonedDateTime_subYearsClip(v_dt_903_, v_years_904_);
lean_dec(v_years_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsRollOver(lean_object* v_dt_906_, lean_object* v_years_907_){
_start:
{
lean_object* v_timestamp_908_; lean_object* v_rules_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_940_; 
v_timestamp_908_ = lean_ctor_get(v_dt_906_, 1);
v_rules_909_ = lean_ctor_get(v_dt_906_, 2);
v_isSharedCheck_940_ = !lean_is_exclusive(v_dt_906_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; lean_object* v_unused_942_; 
v_unused_941_ = lean_ctor_get(v_dt_906_, 3);
lean_dec(v_unused_941_);
v_unused_942_ = lean_ctor_get(v_dt_906_, 0);
lean_dec(v_unused_942_);
v___x_911_ = v_dt_906_;
v_isShared_912_ = v_isSharedCheck_940_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_rules_909_);
lean_inc(v_timestamp_908_);
lean_dec(v_dt_906_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_940_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_date_913_; lean_object* v_date_914_; lean_object* v_time_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_939_; 
v_date_913_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_908_);
v_date_914_ = lean_ctor_get(v_date_913_, 0);
v_time_915_ = lean_ctor_get(v_date_913_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_date_913_);
if (v_isSharedCheck_939_ == 0)
{
v___x_917_ = v_date_913_;
v_isShared_918_ = v_isSharedCheck_939_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_time_915_);
lean_inc(v_date_914_);
lean_dec(v_date_913_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_939_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_initialLocalTimeType_919_; lean_object* v_transitions_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v_initialLocalTimeType_919_ = lean_ctor_get(v_rules_909_, 0);
v_transitions_920_ = lean_ctor_get(v_rules_909_, 1);
v___x_921_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0, &l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_ZonedDateTime_addYearsRollOver___closed__0);
v___x_922_ = lean_int_mul(v_years_907_, v___x_921_);
v___x_923_ = lean_int_neg(v___x_922_);
lean_dec(v___x_922_);
v___x_924_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_914_, v___x_923_);
lean_dec(v___x_923_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_924_);
v___x_926_ = v___x_917_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v_time_915_);
v___x_926_ = v_reuseFailAlloc_938_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; lean_object* v___y_929_; lean_object* v___x_935_; 
v___x_927_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_926_);
lean_inc_ref(v___x_927_);
v___x_935_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_920_, v___x_927_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; 
lean_dec_ref(v___x_935_);
v___x_936_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_919_);
v___y_929_ = v___x_936_;
goto v___jp_928_;
}
else
{
lean_object* v_a_937_; 
v_a_937_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_937_);
lean_dec_ref(v___x_935_);
v___y_929_ = v_a_937_;
goto v___jp_928_;
}
v___jp_928_:
{
lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
lean_inc_ref(v___y_929_);
lean_inc_ref(v___x_927_);
v___f_930_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTimeAssumingUTC___lam__0___boxed), 3, 2);
lean_closure_set(v___f_930_, 0, v___x_927_);
lean_closure_set(v___f_930_, 1, v___y_929_);
v___x_931_ = lean_mk_thunk(v___f_930_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 3, v___y_929_);
lean_ctor_set(v___x_911_, 1, v___x_927_);
lean_ctor_set(v___x_911_, 0, v___x_931_);
v___x_933_ = v___x_911_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_934_, 2, v_rules_909_);
lean_ctor_set(v_reuseFailAlloc_934_, 3, v___y_929_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subYearsRollOver___boxed(lean_object* v_dt_943_, lean_object* v_years_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_Time_ZonedDateTime_subYearsRollOver(v_dt_943_, v_years_944_);
lean_dec(v_years_944_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___lam__0(lean_object* v___x_946_, lean_object* v___y_947_, lean_object* v___x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_second_952_; lean_object* v_nano_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_second_957_; lean_object* v_nano_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_950_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_946_);
v___x_951_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_950_);
v_second_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_second_952_);
v_nano_953_ = lean_ctor_get(v___x_951_, 1);
lean_inc(v_nano_953_);
lean_dec_ref(v___x_951_);
v___x_954_ = l_Std_Time_TimeZone_toSeconds(v___y_947_);
v___x_955_ = lean_int_mul(v___x_954_, v___x_948_);
lean_dec(v___x_954_);
v___x_956_ = l_Std_Time_Duration_ofNanoseconds(v___x_955_);
lean_dec(v___x_955_);
v_second_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_second_957_);
v_nano_958_ = lean_ctor_get(v___x_956_, 1);
lean_inc(v_nano_958_);
lean_dec_ref(v___x_956_);
v___x_959_ = lean_int_mul(v_second_952_, v___x_948_);
lean_dec(v_second_952_);
v___x_960_ = lean_int_add(v___x_959_, v_nano_953_);
lean_dec(v_nano_953_);
lean_dec(v___x_959_);
v___x_961_ = lean_int_mul(v_second_957_, v___x_948_);
lean_dec(v_second_957_);
v___x_962_ = lean_int_add(v___x_961_, v_nano_958_);
lean_dec(v_nano_958_);
lean_dec(v___x_961_);
v___x_963_ = lean_int_add(v___x_960_, v___x_962_);
lean_dec(v___x_962_);
lean_dec(v___x_960_);
v___x_964_ = l_Std_Time_Duration_ofNanoseconds(v___x_963_);
lean_dec(v___x_963_);
v___x_965_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___lam__0___boxed(lean_object* v___x_966_, lean_object* v___y_967_, lean_object* v___x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_Time_ZonedDateTime_addHours___lam__0(v___x_966_, v___y_967_, v___x_968_, v_x_969_);
lean_dec(v___x_968_);
lean_dec_ref(v___y_967_);
return v_res_970_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_cstr_to_nat("3600000000000");
v___x_972_ = lean_nat_to_int(v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours(lean_object* v_dt_973_, lean_object* v_hours_974_){
_start:
{
lean_object* v_timestamp_975_; lean_object* v_rules_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1010_; 
v_timestamp_975_ = lean_ctor_get(v_dt_973_, 1);
v_rules_976_ = lean_ctor_get(v_dt_973_, 2);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_dt_973_);
if (v_isSharedCheck_1010_ == 0)
{
lean_object* v_unused_1011_; lean_object* v_unused_1012_; 
v_unused_1011_ = lean_ctor_get(v_dt_973_, 3);
lean_dec(v_unused_1011_);
v_unused_1012_ = lean_ctor_get(v_dt_973_, 0);
lean_dec(v_unused_1012_);
v___x_978_ = v_dt_973_;
v_isShared_979_ = v_isSharedCheck_1010_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_rules_976_);
lean_inc(v_timestamp_975_);
lean_dec(v_dt_973_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1010_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_date_980_; lean_object* v___x_981_; lean_object* v_second_982_; lean_object* v_nano_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_second_987_; lean_object* v_nano_988_; lean_object* v_initialLocalTimeType_989_; lean_object* v_transitions_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___y_1001_; lean_object* v___x_1007_; 
v_date_980_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_975_);
v___x_981_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_980_);
v_second_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_second_982_);
v_nano_983_ = lean_ctor_get(v___x_981_, 1);
lean_inc(v_nano_983_);
lean_dec_ref(v___x_981_);
v___x_984_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addHours___closed__0, &l_Std_Time_ZonedDateTime_addHours___closed__0_once, _init_l_Std_Time_ZonedDateTime_addHours___closed__0);
v___x_985_ = lean_int_mul(v_hours_974_, v___x_984_);
v___x_986_ = l_Std_Time_Duration_ofNanoseconds(v___x_985_);
lean_dec(v___x_985_);
v_second_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_second_987_);
v_nano_988_ = lean_ctor_get(v___x_986_, 1);
lean_inc(v_nano_988_);
lean_dec_ref(v___x_986_);
v_initialLocalTimeType_989_ = lean_ctor_get(v_rules_976_, 0);
v_transitions_990_ = lean_ctor_get(v_rules_976_, 1);
v___x_991_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_992_ = lean_int_mul(v_second_982_, v___x_991_);
lean_dec(v_second_982_);
v___x_993_ = lean_int_add(v___x_992_, v_nano_983_);
lean_dec(v_nano_983_);
lean_dec(v___x_992_);
v___x_994_ = lean_int_mul(v_second_987_, v___x_991_);
lean_dec(v_second_987_);
v___x_995_ = lean_int_add(v___x_994_, v_nano_988_);
lean_dec(v_nano_988_);
lean_dec(v___x_994_);
v___x_996_ = lean_int_add(v___x_993_, v___x_995_);
lean_dec(v___x_995_);
lean_dec(v___x_993_);
v___x_997_ = l_Std_Time_Duration_ofNanoseconds(v___x_996_);
lean_dec(v___x_996_);
v___x_998_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_997_);
v___x_999_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_998_);
lean_inc_ref(v___x_999_);
v___x_1007_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_990_, v___x_999_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v___x_1008_; 
lean_dec_ref(v___x_1007_);
v___x_1008_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_989_);
v___y_1001_ = v___x_1008_;
goto v___jp_1000_;
}
else
{
lean_object* v_a_1009_; 
v_a_1009_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1009_);
lean_dec_ref(v___x_1007_);
v___y_1001_ = v_a_1009_;
goto v___jp_1000_;
}
v___jp_1000_:
{
lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_inc_ref(v___y_1001_);
lean_inc_ref(v___x_999_);
v___f_1002_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1002_, 0, v___x_999_);
lean_closure_set(v___f_1002_, 1, v___y_1001_);
lean_closure_set(v___f_1002_, 2, v___x_991_);
v___x_1003_ = lean_mk_thunk(v___f_1002_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 3, v___y_1001_);
lean_ctor_set(v___x_978_, 1, v___x_999_);
lean_ctor_set(v___x_978_, 0, v___x_1003_);
v___x_1005_ = v___x_978_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1006_, 2, v_rules_976_);
lean_ctor_set(v_reuseFailAlloc_1006_, 3, v___y_1001_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addHours___boxed(lean_object* v_dt_1013_, lean_object* v_hours_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_Time_ZonedDateTime_addHours(v_dt_1013_, v_hours_1014_);
lean_dec(v_hours_1014_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subHours(lean_object* v_dt_1016_, lean_object* v_hours_1017_){
_start:
{
lean_object* v_timestamp_1018_; lean_object* v_rules_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1054_; 
v_timestamp_1018_ = lean_ctor_get(v_dt_1016_, 1);
v_rules_1019_ = lean_ctor_get(v_dt_1016_, 2);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_dt_1016_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; lean_object* v_unused_1056_; 
v_unused_1055_ = lean_ctor_get(v_dt_1016_, 3);
lean_dec(v_unused_1055_);
v_unused_1056_ = lean_ctor_get(v_dt_1016_, 0);
lean_dec(v_unused_1056_);
v___x_1021_ = v_dt_1016_;
v_isShared_1022_ = v_isSharedCheck_1054_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_rules_1019_);
lean_inc(v_timestamp_1018_);
lean_dec(v_dt_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1054_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v_date_1023_; lean_object* v___x_1024_; lean_object* v_second_1025_; lean_object* v_nano_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_second_1031_; lean_object* v_nano_1032_; lean_object* v_initialLocalTimeType_1033_; lean_object* v_transitions_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___y_1045_; lean_object* v___x_1051_; 
v_date_1023_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1018_);
v___x_1024_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_1023_);
v_second_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_second_1025_);
v_nano_1026_ = lean_ctor_get(v___x_1024_, 1);
lean_inc(v_nano_1026_);
lean_dec_ref(v___x_1024_);
v___x_1027_ = lean_int_neg(v_hours_1017_);
v___x_1028_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addHours___closed__0, &l_Std_Time_ZonedDateTime_addHours___closed__0_once, _init_l_Std_Time_ZonedDateTime_addHours___closed__0);
v___x_1029_ = lean_int_mul(v___x_1027_, v___x_1028_);
lean_dec(v___x_1027_);
v___x_1030_ = l_Std_Time_Duration_ofNanoseconds(v___x_1029_);
lean_dec(v___x_1029_);
v_second_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_second_1031_);
v_nano_1032_ = lean_ctor_get(v___x_1030_, 1);
lean_inc(v_nano_1032_);
lean_dec_ref(v___x_1030_);
v_initialLocalTimeType_1033_ = lean_ctor_get(v_rules_1019_, 0);
v_transitions_1034_ = lean_ctor_get(v_rules_1019_, 1);
v___x_1035_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1036_ = lean_int_mul(v_second_1025_, v___x_1035_);
lean_dec(v_second_1025_);
v___x_1037_ = lean_int_add(v___x_1036_, v_nano_1026_);
lean_dec(v_nano_1026_);
lean_dec(v___x_1036_);
v___x_1038_ = lean_int_mul(v_second_1031_, v___x_1035_);
lean_dec(v_second_1031_);
v___x_1039_ = lean_int_add(v___x_1038_, v_nano_1032_);
lean_dec(v_nano_1032_);
lean_dec(v___x_1038_);
v___x_1040_ = lean_int_add(v___x_1037_, v___x_1039_);
lean_dec(v___x_1039_);
lean_dec(v___x_1037_);
v___x_1041_ = l_Std_Time_Duration_ofNanoseconds(v___x_1040_);
lean_dec(v___x_1040_);
v___x_1042_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1041_);
v___x_1043_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1042_);
lean_inc_ref(v___x_1043_);
v___x_1051_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1034_, v___x_1043_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1052_; 
lean_dec_ref(v___x_1051_);
v___x_1052_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1033_);
v___y_1045_ = v___x_1052_;
goto v___jp_1044_;
}
else
{
lean_object* v_a_1053_; 
v_a_1053_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1051_);
v___y_1045_ = v_a_1053_;
goto v___jp_1044_;
}
v___jp_1044_:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_inc_ref(v___y_1045_);
lean_inc_ref(v___x_1043_);
v___f_1046_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1046_, 0, v___x_1043_);
lean_closure_set(v___f_1046_, 1, v___y_1045_);
lean_closure_set(v___f_1046_, 2, v___x_1035_);
v___x_1047_ = lean_mk_thunk(v___f_1046_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 3, v___y_1045_);
lean_ctor_set(v___x_1021_, 1, v___x_1043_);
lean_ctor_set(v___x_1021_, 0, v___x_1047_);
v___x_1049_ = v___x_1021_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_rules_1019_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v___y_1045_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subHours___boxed(lean_object* v_dt_1057_, lean_object* v_hours_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_Time_ZonedDateTime_subHours(v_dt_1057_, v_hours_1058_);
lean_dec(v_hours_1058_);
return v_res_1059_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_cstr_to_nat("60000000000");
v___x_1061_ = lean_nat_to_int(v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMinutes(lean_object* v_dt_1062_, lean_object* v_minutes_1063_){
_start:
{
lean_object* v_timestamp_1064_; lean_object* v_rules_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1099_; 
v_timestamp_1064_ = lean_ctor_get(v_dt_1062_, 1);
v_rules_1065_ = lean_ctor_get(v_dt_1062_, 2);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_dt_1062_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; lean_object* v_unused_1101_; 
v_unused_1100_ = lean_ctor_get(v_dt_1062_, 3);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_dt_1062_, 0);
lean_dec(v_unused_1101_);
v___x_1067_ = v_dt_1062_;
v_isShared_1068_ = v_isSharedCheck_1099_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_rules_1065_);
lean_inc(v_timestamp_1064_);
lean_dec(v_dt_1062_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1099_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_date_1069_; lean_object* v___x_1070_; lean_object* v_second_1071_; lean_object* v_nano_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_second_1076_; lean_object* v_nano_1077_; lean_object* v_initialLocalTimeType_1078_; lean_object* v_transitions_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___y_1090_; lean_object* v___x_1096_; 
v_date_1069_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1064_);
v___x_1070_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_1069_);
v_second_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_second_1071_);
v_nano_1072_ = lean_ctor_get(v___x_1070_, 1);
lean_inc(v_nano_1072_);
lean_dec_ref(v___x_1070_);
v___x_1073_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addMinutes___closed__0, &l_Std_Time_ZonedDateTime_addMinutes___closed__0_once, _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0);
v___x_1074_ = lean_int_mul(v_minutes_1063_, v___x_1073_);
v___x_1075_ = l_Std_Time_Duration_ofNanoseconds(v___x_1074_);
lean_dec(v___x_1074_);
v_second_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_second_1076_);
v_nano_1077_ = lean_ctor_get(v___x_1075_, 1);
lean_inc(v_nano_1077_);
lean_dec_ref(v___x_1075_);
v_initialLocalTimeType_1078_ = lean_ctor_get(v_rules_1065_, 0);
v_transitions_1079_ = lean_ctor_get(v_rules_1065_, 1);
v___x_1080_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1081_ = lean_int_mul(v_second_1071_, v___x_1080_);
lean_dec(v_second_1071_);
v___x_1082_ = lean_int_add(v___x_1081_, v_nano_1072_);
lean_dec(v_nano_1072_);
lean_dec(v___x_1081_);
v___x_1083_ = lean_int_mul(v_second_1076_, v___x_1080_);
lean_dec(v_second_1076_);
v___x_1084_ = lean_int_add(v___x_1083_, v_nano_1077_);
lean_dec(v_nano_1077_);
lean_dec(v___x_1083_);
v___x_1085_ = lean_int_add(v___x_1082_, v___x_1084_);
lean_dec(v___x_1084_);
lean_dec(v___x_1082_);
v___x_1086_ = l_Std_Time_Duration_ofNanoseconds(v___x_1085_);
lean_dec(v___x_1085_);
v___x_1087_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1086_);
v___x_1088_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1087_);
lean_inc_ref(v___x_1088_);
v___x_1096_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1079_, v___x_1088_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1097_; 
lean_dec_ref(v___x_1096_);
v___x_1097_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1078_);
v___y_1090_ = v___x_1097_;
goto v___jp_1089_;
}
else
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1098_);
lean_dec_ref(v___x_1096_);
v___y_1090_ = v_a_1098_;
goto v___jp_1089_;
}
v___jp_1089_:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_inc_ref(v___y_1090_);
lean_inc_ref(v___x_1088_);
v___f_1091_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1091_, 0, v___x_1088_);
lean_closure_set(v___f_1091_, 1, v___y_1090_);
lean_closure_set(v___f_1091_, 2, v___x_1080_);
v___x_1092_ = lean_mk_thunk(v___f_1091_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 3, v___y_1090_);
lean_ctor_set(v___x_1067_, 1, v___x_1088_);
lean_ctor_set(v___x_1067_, 0, v___x_1092_);
v___x_1094_ = v___x_1067_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_rules_1065_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v___y_1090_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMinutes___boxed(lean_object* v_dt_1102_, lean_object* v_minutes_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Std_Time_ZonedDateTime_addMinutes(v_dt_1102_, v_minutes_1103_);
lean_dec(v_minutes_1103_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMinutes(lean_object* v_dt_1105_, lean_object* v_minutes_1106_){
_start:
{
lean_object* v_timestamp_1107_; lean_object* v_rules_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1143_; 
v_timestamp_1107_ = lean_ctor_get(v_dt_1105_, 1);
v_rules_1108_ = lean_ctor_get(v_dt_1105_, 2);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_dt_1105_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1144_ = lean_ctor_get(v_dt_1105_, 3);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_dt_1105_, 0);
lean_dec(v_unused_1145_);
v___x_1110_ = v_dt_1105_;
v_isShared_1111_ = v_isSharedCheck_1143_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_rules_1108_);
lean_inc(v_timestamp_1107_);
lean_dec(v_dt_1105_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1143_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v_date_1112_; lean_object* v___x_1113_; lean_object* v_second_1114_; lean_object* v_nano_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v_second_1120_; lean_object* v_nano_1121_; lean_object* v_initialLocalTimeType_1122_; lean_object* v_transitions_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___y_1134_; lean_object* v___x_1140_; 
v_date_1112_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1107_);
v___x_1113_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_1112_);
v_second_1114_ = lean_ctor_get(v___x_1113_, 0);
lean_inc(v_second_1114_);
v_nano_1115_ = lean_ctor_get(v___x_1113_, 1);
lean_inc(v_nano_1115_);
lean_dec_ref(v___x_1113_);
v___x_1116_ = lean_int_neg(v_minutes_1106_);
v___x_1117_ = lean_obj_once(&l_Std_Time_ZonedDateTime_addMinutes___closed__0, &l_Std_Time_ZonedDateTime_addMinutes___closed__0_once, _init_l_Std_Time_ZonedDateTime_addMinutes___closed__0);
v___x_1118_ = lean_int_mul(v___x_1116_, v___x_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = l_Std_Time_Duration_ofNanoseconds(v___x_1118_);
lean_dec(v___x_1118_);
v_second_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_second_1120_);
v_nano_1121_ = lean_ctor_get(v___x_1119_, 1);
lean_inc(v_nano_1121_);
lean_dec_ref(v___x_1119_);
v_initialLocalTimeType_1122_ = lean_ctor_get(v_rules_1108_, 0);
v_transitions_1123_ = lean_ctor_get(v_rules_1108_, 1);
v___x_1124_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1125_ = lean_int_mul(v_second_1114_, v___x_1124_);
lean_dec(v_second_1114_);
v___x_1126_ = lean_int_add(v___x_1125_, v_nano_1115_);
lean_dec(v_nano_1115_);
lean_dec(v___x_1125_);
v___x_1127_ = lean_int_mul(v_second_1120_, v___x_1124_);
lean_dec(v_second_1120_);
v___x_1128_ = lean_int_add(v___x_1127_, v_nano_1121_);
lean_dec(v_nano_1121_);
lean_dec(v___x_1127_);
v___x_1129_ = lean_int_add(v___x_1126_, v___x_1128_);
lean_dec(v___x_1128_);
lean_dec(v___x_1126_);
v___x_1130_ = l_Std_Time_Duration_ofNanoseconds(v___x_1129_);
lean_dec(v___x_1129_);
v___x_1131_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1130_);
v___x_1132_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1131_);
lean_inc_ref(v___x_1132_);
v___x_1140_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1123_, v___x_1132_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref(v___x_1140_);
v___x_1141_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1122_);
v___y_1134_ = v___x_1141_;
goto v___jp_1133_;
}
else
{
lean_object* v_a_1142_; 
v_a_1142_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1142_);
lean_dec_ref(v___x_1140_);
v___y_1134_ = v_a_1142_;
goto v___jp_1133_;
}
v___jp_1133_:
{
lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_inc_ref(v___y_1134_);
lean_inc_ref(v___x_1132_);
v___f_1135_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1135_, 0, v___x_1132_);
lean_closure_set(v___f_1135_, 1, v___y_1134_);
lean_closure_set(v___f_1135_, 2, v___x_1124_);
v___x_1136_ = lean_mk_thunk(v___f_1135_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 3, v___y_1134_);
lean_ctor_set(v___x_1110_, 1, v___x_1132_);
lean_ctor_set(v___x_1110_, 0, v___x_1136_);
v___x_1138_ = v___x_1110_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1139_, 2, v_rules_1108_);
lean_ctor_set(v_reuseFailAlloc_1139_, 3, v___y_1134_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMinutes___boxed(lean_object* v_dt_1146_, lean_object* v_minutes_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_Time_ZonedDateTime_subMinutes(v_dt_1146_, v_minutes_1147_);
lean_dec(v_minutes_1147_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds(lean_object* v_dt_1149_, lean_object* v_milliseconds_1150_){
_start:
{
lean_object* v_timestamp_1151_; lean_object* v_rules_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1186_; 
v_timestamp_1151_ = lean_ctor_get(v_dt_1149_, 1);
v_rules_1152_ = lean_ctor_get(v_dt_1149_, 2);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_dt_1149_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; lean_object* v_unused_1188_; 
v_unused_1187_ = lean_ctor_get(v_dt_1149_, 3);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_dt_1149_, 0);
lean_dec(v_unused_1188_);
v___x_1154_ = v_dt_1149_;
v_isShared_1155_ = v_isSharedCheck_1186_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_rules_1152_);
lean_inc(v_timestamp_1151_);
lean_dec(v_dt_1149_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1186_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_date_1156_; lean_object* v___x_1157_; lean_object* v_second_1158_; lean_object* v_nano_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_second_1163_; lean_object* v_nano_1164_; lean_object* v_initialLocalTimeType_1165_; lean_object* v_transitions_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___y_1177_; lean_object* v___x_1183_; 
v_date_1156_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1151_);
v___x_1157_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_1156_);
v_second_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_second_1158_);
v_nano_1159_ = lean_ctor_get(v___x_1157_, 1);
lean_inc(v_nano_1159_);
lean_dec_ref(v___x_1157_);
v___x_1160_ = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
v___x_1161_ = lean_int_mul(v_milliseconds_1150_, v___x_1160_);
v___x_1162_ = l_Std_Time_Duration_ofNanoseconds(v___x_1161_);
lean_dec(v___x_1161_);
v_second_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_second_1163_);
v_nano_1164_ = lean_ctor_get(v___x_1162_, 1);
lean_inc(v_nano_1164_);
lean_dec_ref(v___x_1162_);
v_initialLocalTimeType_1165_ = lean_ctor_get(v_rules_1152_, 0);
v_transitions_1166_ = lean_ctor_get(v_rules_1152_, 1);
v___x_1167_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1168_ = lean_int_mul(v_second_1158_, v___x_1167_);
lean_dec(v_second_1158_);
v___x_1169_ = lean_int_add(v___x_1168_, v_nano_1159_);
lean_dec(v_nano_1159_);
lean_dec(v___x_1168_);
v___x_1170_ = lean_int_mul(v_second_1163_, v___x_1167_);
lean_dec(v_second_1163_);
v___x_1171_ = lean_int_add(v___x_1170_, v_nano_1164_);
lean_dec(v_nano_1164_);
lean_dec(v___x_1170_);
v___x_1172_ = lean_int_add(v___x_1169_, v___x_1171_);
lean_dec(v___x_1171_);
lean_dec(v___x_1169_);
v___x_1173_ = l_Std_Time_Duration_ofNanoseconds(v___x_1172_);
lean_dec(v___x_1172_);
v___x_1174_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1173_);
v___x_1175_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1174_);
lean_inc_ref(v___x_1175_);
v___x_1183_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1166_, v___x_1175_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v___x_1184_; 
lean_dec_ref(v___x_1183_);
v___x_1184_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1165_);
v___y_1177_ = v___x_1184_;
goto v___jp_1176_;
}
else
{
lean_object* v_a_1185_; 
v_a_1185_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1185_);
lean_dec_ref(v___x_1183_);
v___y_1177_ = v_a_1185_;
goto v___jp_1176_;
}
v___jp_1176_:
{
lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
lean_inc_ref(v___y_1177_);
lean_inc_ref(v___x_1175_);
v___f_1178_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1178_, 0, v___x_1175_);
lean_closure_set(v___f_1178_, 1, v___y_1177_);
lean_closure_set(v___f_1178_, 2, v___x_1167_);
v___x_1179_ = lean_mk_thunk(v___f_1178_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 3, v___y_1177_);
lean_ctor_set(v___x_1154_, 1, v___x_1175_);
lean_ctor_set(v___x_1154_, 0, v___x_1179_);
v___x_1181_ = v___x_1154_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_rules_1152_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v___y_1177_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addMilliseconds___boxed(lean_object* v_dt_1189_, lean_object* v_milliseconds_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Std_Time_ZonedDateTime_addMilliseconds(v_dt_1189_, v_milliseconds_1190_);
lean_dec(v_milliseconds_1190_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMilliseconds(lean_object* v_dt_1192_, lean_object* v_milliseconds_1193_){
_start:
{
lean_object* v_timestamp_1194_; lean_object* v_rules_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1230_; 
v_timestamp_1194_ = lean_ctor_get(v_dt_1192_, 1);
v_rules_1195_ = lean_ctor_get(v_dt_1192_, 2);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_dt_1192_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; lean_object* v_unused_1232_; 
v_unused_1231_ = lean_ctor_get(v_dt_1192_, 3);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_dt_1192_, 0);
lean_dec(v_unused_1232_);
v___x_1197_ = v_dt_1192_;
v_isShared_1198_ = v_isSharedCheck_1230_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_rules_1195_);
lean_inc(v_timestamp_1194_);
lean_dec(v_dt_1192_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1230_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_date_1199_; lean_object* v___x_1200_; lean_object* v_second_1201_; lean_object* v_nano_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v_second_1207_; lean_object* v_nano_1208_; lean_object* v_initialLocalTimeType_1209_; lean_object* v_transitions_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___y_1221_; lean_object* v___x_1227_; 
v_date_1199_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1194_);
v___x_1200_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_1199_);
v_second_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_second_1201_);
v_nano_1202_ = lean_ctor_get(v___x_1200_, 1);
lean_inc(v_nano_1202_);
lean_dec_ref(v___x_1200_);
v___x_1203_ = lean_int_neg(v_milliseconds_1193_);
v___x_1204_ = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
v___x_1205_ = lean_int_mul(v___x_1203_, v___x_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = l_Std_Time_Duration_ofNanoseconds(v___x_1205_);
lean_dec(v___x_1205_);
v_second_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_second_1207_);
v_nano_1208_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_nano_1208_);
lean_dec_ref(v___x_1206_);
v_initialLocalTimeType_1209_ = lean_ctor_get(v_rules_1195_, 0);
v_transitions_1210_ = lean_ctor_get(v_rules_1195_, 1);
v___x_1211_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1212_ = lean_int_mul(v_second_1201_, v___x_1211_);
lean_dec(v_second_1201_);
v___x_1213_ = lean_int_add(v___x_1212_, v_nano_1202_);
lean_dec(v_nano_1202_);
lean_dec(v___x_1212_);
v___x_1214_ = lean_int_mul(v_second_1207_, v___x_1211_);
lean_dec(v_second_1207_);
v___x_1215_ = lean_int_add(v___x_1214_, v_nano_1208_);
lean_dec(v_nano_1208_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_int_add(v___x_1213_, v___x_1215_);
lean_dec(v___x_1215_);
lean_dec(v___x_1213_);
v___x_1217_ = l_Std_Time_Duration_ofNanoseconds(v___x_1216_);
lean_dec(v___x_1216_);
v___x_1218_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1217_);
v___x_1219_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1218_);
lean_inc_ref(v___x_1219_);
v___x_1227_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1210_, v___x_1219_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref(v___x_1227_);
v___x_1228_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1209_);
v___y_1221_ = v___x_1228_;
goto v___jp_1220_;
}
else
{
lean_object* v_a_1229_; 
v_a_1229_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1229_);
lean_dec_ref(v___x_1227_);
v___y_1221_ = v_a_1229_;
goto v___jp_1220_;
}
v___jp_1220_:
{
lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
lean_inc_ref(v___y_1221_);
lean_inc_ref(v___x_1219_);
v___f_1222_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1222_, 0, v___x_1219_);
lean_closure_set(v___f_1222_, 1, v___y_1221_);
lean_closure_set(v___f_1222_, 2, v___x_1211_);
v___x_1223_ = lean_mk_thunk(v___f_1222_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 3, v___y_1221_);
lean_ctor_set(v___x_1197_, 1, v___x_1219_);
lean_ctor_set(v___x_1197_, 0, v___x_1223_);
v___x_1225_ = v___x_1197_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_rules_1195_);
lean_ctor_set(v_reuseFailAlloc_1226_, 3, v___y_1221_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subMilliseconds___boxed(lean_object* v_dt_1233_, lean_object* v_milliseconds_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_Time_ZonedDateTime_subMilliseconds(v_dt_1233_, v_milliseconds_1234_);
lean_dec(v_milliseconds_1234_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addSeconds(lean_object* v_dt_1236_, lean_object* v_seconds_1237_){
_start:
{
lean_object* v_timestamp_1238_; lean_object* v_rules_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1272_; 
v_timestamp_1238_ = lean_ctor_get(v_dt_1236_, 1);
v_rules_1239_ = lean_ctor_get(v_dt_1236_, 2);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_dt_1236_);
if (v_isSharedCheck_1272_ == 0)
{
lean_object* v_unused_1273_; lean_object* v_unused_1274_; 
v_unused_1273_ = lean_ctor_get(v_dt_1236_, 3);
lean_dec(v_unused_1273_);
v_unused_1274_ = lean_ctor_get(v_dt_1236_, 0);
lean_dec(v_unused_1274_);
v___x_1241_ = v_dt_1236_;
v_isShared_1242_ = v_isSharedCheck_1272_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_rules_1239_);
lean_inc(v_timestamp_1238_);
lean_dec(v_dt_1236_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1272_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_date_1243_; lean_object* v___x_1244_; lean_object* v_second_1245_; lean_object* v_nano_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v_second_1250_; lean_object* v_nano_1251_; lean_object* v_initialLocalTimeType_1252_; lean_object* v_transitions_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___y_1263_; lean_object* v___x_1269_; 
v_date_1243_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1238_);
v___x_1244_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_1243_);
v_second_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_second_1245_);
v_nano_1246_ = lean_ctor_get(v___x_1244_, 1);
lean_inc(v_nano_1246_);
lean_dec_ref(v___x_1244_);
v___x_1247_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1248_ = lean_int_mul(v_seconds_1237_, v___x_1247_);
v___x_1249_ = l_Std_Time_Duration_ofNanoseconds(v___x_1248_);
lean_dec(v___x_1248_);
v_second_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_second_1250_);
v_nano_1251_ = lean_ctor_get(v___x_1249_, 1);
lean_inc(v_nano_1251_);
lean_dec_ref(v___x_1249_);
v_initialLocalTimeType_1252_ = lean_ctor_get(v_rules_1239_, 0);
v_transitions_1253_ = lean_ctor_get(v_rules_1239_, 1);
v___x_1254_ = lean_int_mul(v_second_1245_, v___x_1247_);
lean_dec(v_second_1245_);
v___x_1255_ = lean_int_add(v___x_1254_, v_nano_1246_);
lean_dec(v_nano_1246_);
lean_dec(v___x_1254_);
v___x_1256_ = lean_int_mul(v_second_1250_, v___x_1247_);
lean_dec(v_second_1250_);
v___x_1257_ = lean_int_add(v___x_1256_, v_nano_1251_);
lean_dec(v_nano_1251_);
lean_dec(v___x_1256_);
v___x_1258_ = lean_int_add(v___x_1255_, v___x_1257_);
lean_dec(v___x_1257_);
lean_dec(v___x_1255_);
v___x_1259_ = l_Std_Time_Duration_ofNanoseconds(v___x_1258_);
lean_dec(v___x_1258_);
v___x_1260_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1259_);
v___x_1261_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1260_);
lean_inc_ref(v___x_1261_);
v___x_1269_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1253_, v___x_1261_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v___x_1270_; 
lean_dec_ref(v___x_1269_);
v___x_1270_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1252_);
v___y_1263_ = v___x_1270_;
goto v___jp_1262_;
}
else
{
lean_object* v_a_1271_; 
v_a_1271_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1271_);
lean_dec_ref(v___x_1269_);
v___y_1263_ = v_a_1271_;
goto v___jp_1262_;
}
v___jp_1262_:
{
lean_object* v___f_1264_; lean_object* v___x_1265_; lean_object* v___x_1267_; 
lean_inc_ref(v___y_1263_);
lean_inc_ref(v___x_1261_);
v___f_1264_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1264_, 0, v___x_1261_);
lean_closure_set(v___f_1264_, 1, v___y_1263_);
lean_closure_set(v___f_1264_, 2, v___x_1247_);
v___x_1265_ = lean_mk_thunk(v___f_1264_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 3, v___y_1263_);
lean_ctor_set(v___x_1241_, 1, v___x_1261_);
lean_ctor_set(v___x_1241_, 0, v___x_1265_);
v___x_1267_ = v___x_1241_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_rules_1239_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v___y_1263_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addSeconds___boxed(lean_object* v_dt_1275_, lean_object* v_seconds_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_Time_ZonedDateTime_addSeconds(v_dt_1275_, v_seconds_1276_);
lean_dec(v_seconds_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subSeconds(lean_object* v_dt_1278_, lean_object* v_seconds_1279_){
_start:
{
lean_object* v_timestamp_1280_; lean_object* v_rules_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1315_; 
v_timestamp_1280_ = lean_ctor_get(v_dt_1278_, 1);
v_rules_1281_ = lean_ctor_get(v_dt_1278_, 2);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_dt_1278_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; lean_object* v_unused_1317_; 
v_unused_1316_ = lean_ctor_get(v_dt_1278_, 3);
lean_dec(v_unused_1316_);
v_unused_1317_ = lean_ctor_get(v_dt_1278_, 0);
lean_dec(v_unused_1317_);
v___x_1283_ = v_dt_1278_;
v_isShared_1284_ = v_isSharedCheck_1315_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_rules_1281_);
lean_inc(v_timestamp_1280_);
lean_dec(v_dt_1278_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1315_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v_date_1285_; lean_object* v___x_1286_; lean_object* v_second_1287_; lean_object* v_nano_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v_second_1293_; lean_object* v_nano_1294_; lean_object* v_initialLocalTimeType_1295_; lean_object* v_transitions_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___y_1306_; lean_object* v___x_1312_; 
v_date_1285_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1280_);
v___x_1286_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_1285_);
v_second_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_second_1287_);
v_nano_1288_ = lean_ctor_get(v___x_1286_, 1);
lean_inc(v_nano_1288_);
lean_dec_ref(v___x_1286_);
v___x_1289_ = lean_int_neg(v_seconds_1279_);
v___x_1290_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1291_ = lean_int_mul(v___x_1289_, v___x_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = l_Std_Time_Duration_ofNanoseconds(v___x_1291_);
lean_dec(v___x_1291_);
v_second_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_second_1293_);
v_nano_1294_ = lean_ctor_get(v___x_1292_, 1);
lean_inc(v_nano_1294_);
lean_dec_ref(v___x_1292_);
v_initialLocalTimeType_1295_ = lean_ctor_get(v_rules_1281_, 0);
v_transitions_1296_ = lean_ctor_get(v_rules_1281_, 1);
v___x_1297_ = lean_int_mul(v_second_1287_, v___x_1290_);
lean_dec(v_second_1287_);
v___x_1298_ = lean_int_add(v___x_1297_, v_nano_1288_);
lean_dec(v_nano_1288_);
lean_dec(v___x_1297_);
v___x_1299_ = lean_int_mul(v_second_1293_, v___x_1290_);
lean_dec(v_second_1293_);
v___x_1300_ = lean_int_add(v___x_1299_, v_nano_1294_);
lean_dec(v_nano_1294_);
lean_dec(v___x_1299_);
v___x_1301_ = lean_int_add(v___x_1298_, v___x_1300_);
lean_dec(v___x_1300_);
lean_dec(v___x_1298_);
v___x_1302_ = l_Std_Time_Duration_ofNanoseconds(v___x_1301_);
lean_dec(v___x_1301_);
v___x_1303_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1302_);
v___x_1304_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1303_);
lean_inc_ref(v___x_1304_);
v___x_1312_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1296_, v___x_1304_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1313_; 
lean_dec_ref(v___x_1312_);
v___x_1313_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1295_);
v___y_1306_ = v___x_1313_;
goto v___jp_1305_;
}
else
{
lean_object* v_a_1314_; 
v_a_1314_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1314_);
lean_dec_ref(v___x_1312_);
v___y_1306_ = v_a_1314_;
goto v___jp_1305_;
}
v___jp_1305_:
{
lean_object* v___f_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_inc_ref(v___y_1306_);
lean_inc_ref(v___x_1304_);
v___f_1307_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1307_, 0, v___x_1304_);
lean_closure_set(v___f_1307_, 1, v___y_1306_);
lean_closure_set(v___f_1307_, 2, v___x_1290_);
v___x_1308_ = lean_mk_thunk(v___f_1307_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 3, v___y_1306_);
lean_ctor_set(v___x_1283_, 1, v___x_1304_);
lean_ctor_set(v___x_1283_, 0, v___x_1308_);
v___x_1310_ = v___x_1283_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_rules_1281_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v___y_1306_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subSeconds___boxed(lean_object* v_dt_1318_, lean_object* v_seconds_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Std_Time_ZonedDateTime_subSeconds(v_dt_1318_, v_seconds_1319_);
lean_dec(v_seconds_1319_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addNanoseconds(lean_object* v_dt_1321_, lean_object* v_nanoseconds_1322_){
_start:
{
lean_object* v_timestamp_1323_; lean_object* v_rules_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1356_; 
v_timestamp_1323_ = lean_ctor_get(v_dt_1321_, 1);
v_rules_1324_ = lean_ctor_get(v_dt_1321_, 2);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_dt_1321_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; lean_object* v_unused_1358_; 
v_unused_1357_ = lean_ctor_get(v_dt_1321_, 3);
lean_dec(v_unused_1357_);
v_unused_1358_ = lean_ctor_get(v_dt_1321_, 0);
lean_dec(v_unused_1358_);
v___x_1326_ = v_dt_1321_;
v_isShared_1327_ = v_isSharedCheck_1356_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_rules_1324_);
lean_inc(v_timestamp_1323_);
lean_dec(v_dt_1321_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1356_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_date_1328_; lean_object* v___x_1329_; lean_object* v_second_1330_; lean_object* v_nano_1331_; lean_object* v___x_1332_; lean_object* v_second_1333_; lean_object* v_nano_1334_; lean_object* v_initialLocalTimeType_1335_; lean_object* v_transitions_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___y_1347_; lean_object* v___x_1353_; 
v_date_1328_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1323_);
v___x_1329_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_1328_);
v_second_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_second_1330_);
v_nano_1331_ = lean_ctor_get(v___x_1329_, 1);
lean_inc(v_nano_1331_);
lean_dec_ref(v___x_1329_);
v___x_1332_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1322_);
v_second_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_second_1333_);
v_nano_1334_ = lean_ctor_get(v___x_1332_, 1);
lean_inc(v_nano_1334_);
lean_dec_ref(v___x_1332_);
v_initialLocalTimeType_1335_ = lean_ctor_get(v_rules_1324_, 0);
v_transitions_1336_ = lean_ctor_get(v_rules_1324_, 1);
v___x_1337_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1338_ = lean_int_mul(v_second_1330_, v___x_1337_);
lean_dec(v_second_1330_);
v___x_1339_ = lean_int_add(v___x_1338_, v_nano_1331_);
lean_dec(v_nano_1331_);
lean_dec(v___x_1338_);
v___x_1340_ = lean_int_mul(v_second_1333_, v___x_1337_);
lean_dec(v_second_1333_);
v___x_1341_ = lean_int_add(v___x_1340_, v_nano_1334_);
lean_dec(v_nano_1334_);
lean_dec(v___x_1340_);
v___x_1342_ = lean_int_add(v___x_1339_, v___x_1341_);
lean_dec(v___x_1341_);
lean_dec(v___x_1339_);
v___x_1343_ = l_Std_Time_Duration_ofNanoseconds(v___x_1342_);
lean_dec(v___x_1342_);
v___x_1344_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1343_);
v___x_1345_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1344_);
lean_inc_ref(v___x_1345_);
v___x_1353_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1336_, v___x_1345_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_object* v___x_1354_; 
lean_dec_ref(v___x_1353_);
v___x_1354_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1335_);
v___y_1347_ = v___x_1354_;
goto v___jp_1346_;
}
else
{
lean_object* v_a_1355_; 
v_a_1355_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_a_1355_);
lean_dec_ref(v___x_1353_);
v___y_1347_ = v_a_1355_;
goto v___jp_1346_;
}
v___jp_1346_:
{
lean_object* v___f_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
lean_inc_ref(v___y_1347_);
lean_inc_ref(v___x_1345_);
v___f_1348_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1348_, 0, v___x_1345_);
lean_closure_set(v___f_1348_, 1, v___y_1347_);
lean_closure_set(v___f_1348_, 2, v___x_1337_);
v___x_1349_ = lean_mk_thunk(v___f_1348_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 3, v___y_1347_);
lean_ctor_set(v___x_1326_, 1, v___x_1345_);
lean_ctor_set(v___x_1326_, 0, v___x_1349_);
v___x_1351_ = v___x_1326_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_rules_1324_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v___y_1347_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_addNanoseconds___boxed(lean_object* v_dt_1359_, lean_object* v_nanoseconds_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_dt_1359_, v_nanoseconds_1360_);
lean_dec(v_nanoseconds_1360_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subNanoseconds(lean_object* v_dt_1362_, lean_object* v_nanoseconds_1363_){
_start:
{
lean_object* v_timestamp_1364_; lean_object* v_rules_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1398_; 
v_timestamp_1364_ = lean_ctor_get(v_dt_1362_, 1);
v_rules_1365_ = lean_ctor_get(v_dt_1362_, 2);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_dt_1362_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; lean_object* v_unused_1400_; 
v_unused_1399_ = lean_ctor_get(v_dt_1362_, 3);
lean_dec(v_unused_1399_);
v_unused_1400_ = lean_ctor_get(v_dt_1362_, 0);
lean_dec(v_unused_1400_);
v___x_1367_ = v_dt_1362_;
v_isShared_1368_ = v_isSharedCheck_1398_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_rules_1365_);
lean_inc(v_timestamp_1364_);
lean_dec(v_dt_1362_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1398_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_date_1369_; lean_object* v___x_1370_; lean_object* v_second_1371_; lean_object* v_nano_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v_second_1375_; lean_object* v_nano_1376_; lean_object* v_initialLocalTimeType_1377_; lean_object* v_transitions_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___y_1389_; lean_object* v___x_1395_; 
v_date_1369_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1364_);
v___x_1370_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_date_1369_);
v_second_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_second_1371_);
v_nano_1372_ = lean_ctor_get(v___x_1370_, 1);
lean_inc(v_nano_1372_);
lean_dec_ref(v___x_1370_);
v___x_1373_ = lean_int_neg(v_nanoseconds_1363_);
v___x_1374_ = l_Std_Time_Duration_ofNanoseconds(v___x_1373_);
lean_dec(v___x_1373_);
v_second_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_second_1375_);
v_nano_1376_ = lean_ctor_get(v___x_1374_, 1);
lean_inc(v_nano_1376_);
lean_dec_ref(v___x_1374_);
v_initialLocalTimeType_1377_ = lean_ctor_get(v_rules_1365_, 0);
v_transitions_1378_ = lean_ctor_get(v_rules_1365_, 1);
v___x_1379_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1380_ = lean_int_mul(v_second_1371_, v___x_1379_);
lean_dec(v_second_1371_);
v___x_1381_ = lean_int_add(v___x_1380_, v_nano_1372_);
lean_dec(v_nano_1372_);
lean_dec(v___x_1380_);
v___x_1382_ = lean_int_mul(v_second_1375_, v___x_1379_);
lean_dec(v_second_1375_);
v___x_1383_ = lean_int_add(v___x_1382_, v_nano_1376_);
lean_dec(v_nano_1376_);
lean_dec(v___x_1382_);
v___x_1384_ = lean_int_add(v___x_1381_, v___x_1383_);
lean_dec(v___x_1383_);
lean_dec(v___x_1381_);
v___x_1385_ = l_Std_Time_Duration_ofNanoseconds(v___x_1384_);
lean_dec(v___x_1384_);
v___x_1386_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1385_);
v___x_1387_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1386_);
lean_inc_ref(v___x_1387_);
v___x_1395_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1378_, v___x_1387_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref(v___x_1395_);
v___x_1396_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1377_);
v___y_1389_ = v___x_1396_;
goto v___jp_1388_;
}
else
{
lean_object* v_a_1397_; 
v_a_1397_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1397_);
lean_dec_ref(v___x_1395_);
v___y_1389_ = v_a_1397_;
goto v___jp_1388_;
}
v___jp_1388_:
{
lean_object* v___f_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_inc_ref(v___y_1389_);
lean_inc_ref(v___x_1387_);
v___f_1390_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_addHours___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1390_, 0, v___x_1387_);
lean_closure_set(v___f_1390_, 1, v___y_1389_);
lean_closure_set(v___f_1390_, 2, v___x_1379_);
v___x_1391_ = lean_mk_thunk(v___f_1390_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 3, v___y_1389_);
lean_ctor_set(v___x_1367_, 1, v___x_1387_);
lean_ctor_set(v___x_1367_, 0, v___x_1391_);
v___x_1393_ = v___x_1367_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_rules_1365_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v___y_1389_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_subNanoseconds___boxed(lean_object* v_dt_1401_, lean_object* v_nanoseconds_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_dt_1401_, v_nanoseconds_1402_);
lean_dec(v_nanoseconds_1402_);
return v_res_1403_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_era(lean_object* v_date_1404_){
_start:
{
lean_object* v_date_1405_; lean_object* v___x_1406_; lean_object* v_date_1407_; lean_object* v_year_1408_; uint8_t v___x_1409_; 
v_date_1405_ = lean_ctor_get(v_date_1404_, 0);
v___x_1406_ = lean_thunk_get_own(v_date_1405_);
v_date_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_date_1407_);
lean_dec(v___x_1406_);
v_year_1408_ = lean_ctor_get(v_date_1407_, 0);
lean_inc(v_year_1408_);
lean_dec_ref(v_date_1407_);
v___x_1409_ = l_Std_Time_Year_Offset_era(v_year_1408_);
lean_dec(v_year_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_era___boxed(lean_object* v_date_1410_){
_start:
{
uint8_t v_res_1411_; lean_object* v_r_1412_; 
v_res_1411_ = l_Std_Time_ZonedDateTime_era(v_date_1410_);
lean_dec_ref(v_date_1410_);
v_r_1412_ = lean_box(v_res_1411_);
return v_r_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday(lean_object* v_dt_1413_, uint8_t v_desiredWeekday_1414_){
_start:
{
lean_object* v_date_1415_; lean_object* v_rules_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1469_; 
v_date_1415_ = lean_ctor_get(v_dt_1413_, 0);
v_rules_1416_ = lean_ctor_get(v_dt_1413_, 2);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_dt_1413_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; lean_object* v_unused_1471_; 
v_unused_1470_ = lean_ctor_get(v_dt_1413_, 3);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_dt_1413_, 1);
lean_dec(v_unused_1471_);
v___x_1418_ = v_dt_1413_;
v_isShared_1419_ = v_isSharedCheck_1469_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_rules_1416_);
lean_inc(v_date_1415_);
lean_dec(v_dt_1413_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1469_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_date_1420_; lean_object* v___x_1421_; lean_object* v_tm_1422_; lean_object* v___y_1424_; lean_object* v_val_1444_; lean_object* v_second_1446_; lean_object* v_initialLocalTimeType_1447_; lean_object* v_transitions_1448_; lean_object* v___f_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v_date_1420_ = lean_thunk_get_own(v_date_1415_);
lean_dec_ref(v_date_1415_);
v___x_1421_ = l_Std_Time_PlainDateTime_withWeekday(v_date_1420_, v_desiredWeekday_1414_);
v_tm_1422_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1421_);
v_second_1446_ = lean_ctor_get(v_tm_1422_, 0);
lean_inc(v_second_1446_);
v_initialLocalTimeType_1447_ = lean_ctor_get(v_rules_1416_, 0);
v_transitions_1448_ = lean_ctor_get(v_rules_1416_, 1);
lean_inc(v_second_1446_);
v___f_1449_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1449_, 0, v_second_1446_);
v___x_1450_ = lean_unsigned_to_nat(0u);
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1449_, v_transitions_1448_, v___x_1450_);
if (lean_obj_tag(v___x_1451_) == 1)
{
lean_object* v_val_1452_; lean_object* v_next_1453_; lean_object* v_time_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v_last_1457_; lean_object* v_localTimeType_1458_; lean_object* v_gmtOffset_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_val_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_val_1452_);
lean_dec_ref(v___x_1451_);
v_next_1453_ = lean_array_fget_borrowed(v_transitions_1448_, v_val_1452_);
v_time_1454_ = lean_ctor_get(v_next_1453_, 0);
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_nat_sub(v_val_1452_, v___x_1455_);
lean_dec(v_val_1452_);
v_last_1457_ = lean_array_fget_borrowed(v_transitions_1448_, v___x_1456_);
lean_dec(v___x_1456_);
v_localTimeType_1458_ = lean_ctor_get(v_last_1457_, 1);
v_gmtOffset_1459_ = lean_ctor_get(v_localTimeType_1458_, 0);
v___x_1460_ = lean_nat_abs(v_gmtOffset_1459_);
v___x_1461_ = lean_nat_to_int(v___x_1460_);
v___x_1462_ = lean_int_sub(v_time_1454_, v___x_1461_);
lean_dec(v___x_1461_);
v___x_1463_ = lean_int_dec_lt(v_second_1446_, v___x_1462_);
lean_dec(v___x_1462_);
lean_dec(v_second_1446_);
if (v___x_1463_ == 0)
{
lean_inc(v_next_1453_);
v_val_1444_ = v_next_1453_;
goto v___jp_1443_;
}
else
{
lean_inc(v_last_1457_);
v_val_1444_ = v_last_1457_;
goto v___jp_1443_;
}
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
lean_dec(v___x_1451_);
lean_dec(v_second_1446_);
v___x_1464_ = lean_array_get_size(v_transitions_1448_);
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_sub(v___x_1464_, v___x_1465_);
v___x_1467_ = lean_nat_dec_lt(v___x_1466_, v___x_1464_);
if (v___x_1467_ == 0)
{
lean_dec(v___x_1466_);
lean_inc_ref(v_initialLocalTimeType_1447_);
v___y_1424_ = v_initialLocalTimeType_1447_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_array_fget_borrowed(v_transitions_1448_, v___x_1466_);
lean_dec(v___x_1466_);
lean_inc(v___x_1468_);
v_val_1444_ = v___x_1468_;
goto v___jp_1443_;
}
}
v___jp_1423_:
{
lean_object* v_second_1425_; lean_object* v_nano_1426_; lean_object* v_tz_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_tm_1437_; lean_object* v___f_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v_second_1425_ = lean_ctor_get(v_tm_1422_, 0);
lean_inc(v_second_1425_);
v_nano_1426_ = lean_ctor_get(v_tm_1422_, 1);
lean_inc(v_nano_1426_);
lean_dec_ref(v_tm_1422_);
v_tz_1427_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_1424_);
lean_dec_ref(v___y_1424_);
v___x_1428_ = l_Std_Time_TimeZone_toSeconds(v_tz_1427_);
v___x_1429_ = lean_int_neg(v___x_1428_);
v___x_1430_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_1431_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1432_ = lean_int_mul(v_second_1425_, v___x_1431_);
lean_dec(v_second_1425_);
v___x_1433_ = lean_int_add(v___x_1432_, v_nano_1426_);
lean_dec(v_nano_1426_);
lean_dec(v___x_1432_);
v___x_1434_ = lean_int_mul(v___x_1429_, v___x_1431_);
lean_dec(v___x_1429_);
v___x_1435_ = lean_int_add(v___x_1434_, v___x_1430_);
lean_dec(v___x_1434_);
v___x_1436_ = lean_int_add(v___x_1433_, v___x_1435_);
lean_dec(v___x_1435_);
lean_dec(v___x_1433_);
v_tm_1437_ = l_Std_Time_Duration_ofNanoseconds(v___x_1436_);
lean_dec(v___x_1436_);
lean_inc_ref(v_tm_1437_);
v___f_1438_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1438_, 0, v_tm_1437_);
lean_closure_set(v___f_1438_, 1, v___x_1428_);
lean_closure_set(v___f_1438_, 2, v___x_1431_);
v___x_1439_ = lean_mk_thunk(v___f_1438_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 3, v_tz_1427_);
lean_ctor_set(v___x_1418_, 1, v_tm_1437_);
lean_ctor_set(v___x_1418_, 0, v___x_1439_);
v___x_1441_ = v___x_1418_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_tm_1437_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_rules_1416_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_tz_1427_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
v___jp_1443_:
{
lean_object* v_localTimeType_1445_; 
v_localTimeType_1445_ = lean_ctor_get(v_val_1444_, 1);
lean_inc_ref(v_localTimeType_1445_);
lean_dec_ref(v_val_1444_);
v___y_1424_ = v_localTimeType_1445_;
goto v___jp_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withWeekday___boxed(lean_object* v_dt_1472_, lean_object* v_desiredWeekday_1473_){
_start:
{
uint8_t v_desiredWeekday_boxed_1474_; lean_object* v_res_1475_; 
v_desiredWeekday_boxed_1474_ = lean_unbox(v_desiredWeekday_1473_);
v_res_1475_ = l_Std_Time_ZonedDateTime_withWeekday(v_dt_1472_, v_desiredWeekday_boxed_1474_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysClip(lean_object* v_dt_1476_, lean_object* v_days_1477_){
_start:
{
lean_object* v_date_1478_; lean_object* v_rules_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1573_; 
v_date_1478_ = lean_ctor_get(v_dt_1476_, 0);
v_rules_1479_ = lean_ctor_get(v_dt_1476_, 2);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_dt_1476_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; lean_object* v_unused_1575_; 
v_unused_1574_ = lean_ctor_get(v_dt_1476_, 3);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_dt_1476_, 1);
lean_dec(v_unused_1575_);
v___x_1481_ = v_dt_1476_;
v_isShared_1482_ = v_isSharedCheck_1573_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_rules_1479_);
lean_inc(v_date_1478_);
lean_dec(v_dt_1476_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1573_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1505_; lean_object* v_val_1506_; lean_object* v_date_1508_; lean_object* v___y_1510_; lean_object* v_date_1544_; lean_object* v_year_1545_; lean_object* v_month_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1571_; 
v_date_1508_ = lean_thunk_get_own(v_date_1478_);
lean_dec_ref(v_date_1478_);
v_date_1544_ = lean_ctor_get(v_date_1508_, 0);
lean_inc_ref(v_date_1544_);
v_year_1545_ = lean_ctor_get(v_date_1544_, 0);
v_month_1546_ = lean_ctor_get(v_date_1544_, 1);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_date_1544_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_date_1544_, 2);
lean_dec(v_unused_1572_);
v___x_1548_ = v_date_1544_;
v_isShared_1549_ = v_isSharedCheck_1571_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_month_1546_);
lean_inc(v_year_1545_);
lean_dec(v_date_1544_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1571_;
goto v_resetjp_1547_;
}
v___jp_1483_:
{
lean_object* v_second_1486_; lean_object* v_nano_1487_; lean_object* v_tz_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_tm_1498_; lean_object* v___f_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v_second_1486_ = lean_ctor_get(v___y_1484_, 0);
lean_inc(v_second_1486_);
v_nano_1487_ = lean_ctor_get(v___y_1484_, 1);
lean_inc(v_nano_1487_);
lean_dec_ref(v___y_1484_);
v_tz_1488_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_1485_);
lean_dec_ref(v___y_1485_);
v___x_1489_ = l_Std_Time_TimeZone_toSeconds(v_tz_1488_);
v___x_1490_ = lean_int_neg(v___x_1489_);
v___x_1491_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_1492_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1493_ = lean_int_mul(v_second_1486_, v___x_1492_);
lean_dec(v_second_1486_);
v___x_1494_ = lean_int_add(v___x_1493_, v_nano_1487_);
lean_dec(v_nano_1487_);
lean_dec(v___x_1493_);
v___x_1495_ = lean_int_mul(v___x_1490_, v___x_1492_);
lean_dec(v___x_1490_);
v___x_1496_ = lean_int_add(v___x_1495_, v___x_1491_);
lean_dec(v___x_1495_);
v___x_1497_ = lean_int_add(v___x_1494_, v___x_1496_);
lean_dec(v___x_1496_);
lean_dec(v___x_1494_);
v_tm_1498_ = l_Std_Time_Duration_ofNanoseconds(v___x_1497_);
lean_dec(v___x_1497_);
lean_inc_ref(v_tm_1498_);
v___f_1499_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1499_, 0, v_tm_1498_);
lean_closure_set(v___f_1499_, 1, v___x_1489_);
lean_closure_set(v___f_1499_, 2, v___x_1492_);
v___x_1500_ = lean_mk_thunk(v___f_1499_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 3, v_tz_1488_);
lean_ctor_set(v___x_1481_, 1, v_tm_1498_);
lean_ctor_set(v___x_1481_, 0, v___x_1500_);
v___x_1502_ = v___x_1481_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_tm_1498_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_rules_1479_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_tz_1488_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
v___jp_1504_:
{
lean_object* v_localTimeType_1507_; 
v_localTimeType_1507_ = lean_ctor_get(v_val_1506_, 1);
lean_inc_ref(v_localTimeType_1507_);
lean_dec_ref(v_val_1506_);
v___y_1484_ = v___y_1505_;
v___y_1485_ = v_localTimeType_1507_;
goto v___jp_1483_;
}
v___jp_1509_:
{
lean_object* v_time_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1542_; 
v_time_1511_ = lean_ctor_get(v_date_1508_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_date_1508_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v_date_1508_, 0);
lean_dec(v_unused_1543_);
v___x_1513_ = v_date_1508_;
v_isShared_1514_ = v_isSharedCheck_1542_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_time_1511_);
lean_dec(v_date_1508_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1542_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 0, v___y_1510_);
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___y_1510_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_time_1511_);
v___x_1516_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
lean_object* v_tm_1517_; lean_object* v_second_1518_; lean_object* v_initialLocalTimeType_1519_; lean_object* v_transitions_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_tm_1517_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1516_);
v_second_1518_ = lean_ctor_get(v_tm_1517_, 0);
lean_inc(v_second_1518_);
v_initialLocalTimeType_1519_ = lean_ctor_get(v_rules_1479_, 0);
v_transitions_1520_ = lean_ctor_get(v_rules_1479_, 1);
lean_inc(v_second_1518_);
v___f_1521_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1521_, 0, v_second_1518_);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1521_, v_transitions_1520_, v___x_1522_);
if (lean_obj_tag(v___x_1523_) == 1)
{
lean_object* v_val_1524_; lean_object* v_next_1525_; lean_object* v_time_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_last_1529_; lean_object* v_localTimeType_1530_; lean_object* v_gmtOffset_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v_val_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_val_1524_);
lean_dec_ref(v___x_1523_);
v_next_1525_ = lean_array_fget_borrowed(v_transitions_1520_, v_val_1524_);
v_time_1526_ = lean_ctor_get(v_next_1525_, 0);
v___x_1527_ = lean_unsigned_to_nat(1u);
v___x_1528_ = lean_nat_sub(v_val_1524_, v___x_1527_);
lean_dec(v_val_1524_);
v_last_1529_ = lean_array_fget_borrowed(v_transitions_1520_, v___x_1528_);
lean_dec(v___x_1528_);
v_localTimeType_1530_ = lean_ctor_get(v_last_1529_, 1);
v_gmtOffset_1531_ = lean_ctor_get(v_localTimeType_1530_, 0);
v___x_1532_ = lean_nat_abs(v_gmtOffset_1531_);
v___x_1533_ = lean_nat_to_int(v___x_1532_);
v___x_1534_ = lean_int_sub(v_time_1526_, v___x_1533_);
lean_dec(v___x_1533_);
v___x_1535_ = lean_int_dec_lt(v_second_1518_, v___x_1534_);
lean_dec(v___x_1534_);
lean_dec(v_second_1518_);
if (v___x_1535_ == 0)
{
lean_inc(v_next_1525_);
v___y_1505_ = v_tm_1517_;
v_val_1506_ = v_next_1525_;
goto v___jp_1504_;
}
else
{
lean_inc(v_last_1529_);
v___y_1505_ = v_tm_1517_;
v_val_1506_ = v_last_1529_;
goto v___jp_1504_;
}
}
else
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
lean_dec(v___x_1523_);
lean_dec(v_second_1518_);
v___x_1536_ = lean_array_get_size(v_transitions_1520_);
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = lean_nat_sub(v___x_1536_, v___x_1537_);
v___x_1539_ = lean_nat_dec_lt(v___x_1538_, v___x_1536_);
if (v___x_1539_ == 0)
{
lean_dec(v___x_1538_);
lean_inc_ref(v_initialLocalTimeType_1519_);
v___y_1484_ = v_tm_1517_;
v___y_1485_ = v_initialLocalTimeType_1519_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_array_fget_borrowed(v_transitions_1520_, v___x_1538_);
lean_dec(v___x_1538_);
lean_inc(v___x_1540_);
v___y_1505_ = v_tm_1517_;
v_val_1506_ = v___x_1540_;
goto v___jp_1504_;
}
}
}
}
}
v_resetjp_1547_:
{
uint8_t v___y_1551_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1567_; 
v___x_1560_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_1561_ = lean_int_mod(v_year_1545_, v___x_1560_);
v___x_1562_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1567_ = lean_int_dec_eq(v___x_1561_, v___x_1562_);
lean_dec(v___x_1561_);
if (v___x_1567_ == 0)
{
v___y_1551_ = v___x_1567_;
goto v___jp_1550_;
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1568_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_1569_ = lean_int_mod(v_year_1545_, v___x_1568_);
v___x_1570_ = lean_int_dec_eq(v___x_1569_, v___x_1562_);
lean_dec(v___x_1569_);
if (v___x_1570_ == 0)
{
if (v___x_1567_ == 0)
{
goto v___jp_1563_;
}
else
{
v___y_1551_ = v___x_1567_;
goto v___jp_1550_;
}
}
else
{
goto v___jp_1563_;
}
}
v___jp_1550_:
{
lean_object* v_max_1552_; uint8_t v___x_1553_; 
v_max_1552_ = l_Std_Time_Month_Ordinal_days(v___y_1551_, v_month_1546_);
v___x_1553_ = lean_int_dec_lt(v_max_1552_, v_days_1477_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1555_; 
lean_dec(v_max_1552_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 2, v_days_1477_);
v___x_1555_ = v___x_1548_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_year_1545_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_month_1546_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_days_1477_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
v___y_1510_ = v___x_1555_;
goto v___jp_1509_;
}
}
else
{
lean_object* v___x_1558_; 
lean_dec(v_days_1477_);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 2, v_max_1552_);
v___x_1558_ = v___x_1548_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_year_1545_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_month_1546_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_max_1552_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
v___y_1510_ = v___x_1558_;
goto v___jp_1509_;
}
}
}
v___jp_1563_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_1565_ = lean_int_mod(v_year_1545_, v___x_1564_);
v___x_1566_ = lean_int_dec_eq(v___x_1565_, v___x_1562_);
lean_dec(v___x_1565_);
v___y_1551_ = v___x_1566_;
goto v___jp_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysRollOver(lean_object* v_dt_1576_, lean_object* v_days_1577_){
_start:
{
lean_object* v_date_1578_; lean_object* v_rules_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1643_; 
v_date_1578_ = lean_ctor_get(v_dt_1576_, 0);
v_rules_1579_ = lean_ctor_get(v_dt_1576_, 2);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_dt_1576_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1644_ = lean_ctor_get(v_dt_1576_, 3);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_dt_1576_, 1);
lean_dec(v_unused_1645_);
v___x_1581_ = v_dt_1576_;
v_isShared_1582_ = v_isSharedCheck_1643_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_rules_1579_);
lean_inc(v_date_1578_);
lean_dec(v_dt_1576_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1643_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_date_1583_; lean_object* v_date_1584_; lean_object* v_time_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1642_; 
v_date_1583_ = lean_thunk_get_own(v_date_1578_);
lean_dec_ref(v_date_1578_);
v_date_1584_ = lean_ctor_get(v_date_1583_, 0);
v_time_1585_ = lean_ctor_get(v_date_1583_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_date_1583_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1587_ = v_date_1583_;
v_isShared_1588_ = v_isSharedCheck_1642_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_time_1585_);
lean_inc(v_date_1584_);
lean_dec(v_date_1583_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1642_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_year_1589_; lean_object* v_month_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v_year_1589_ = lean_ctor_get(v_date_1584_, 0);
lean_inc(v_year_1589_);
v_month_1590_ = lean_ctor_get(v_date_1584_, 1);
lean_inc(v_month_1590_);
lean_dec_ref(v_date_1584_);
v___x_1591_ = l_Std_Time_PlainDate_rollOver(v_year_1589_, v_month_1590_, v_days_1577_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1591_);
v___x_1593_ = v___x_1587_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1591_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_time_1585_);
v___x_1593_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v_tm_1594_; lean_object* v___y_1596_; lean_object* v_val_1616_; lean_object* v_second_1618_; lean_object* v_initialLocalTimeType_1619_; lean_object* v_transitions_1620_; lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v_tm_1594_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1593_);
v_second_1618_ = lean_ctor_get(v_tm_1594_, 0);
lean_inc(v_second_1618_);
v_initialLocalTimeType_1619_ = lean_ctor_get(v_rules_1579_, 0);
v_transitions_1620_ = lean_ctor_get(v_rules_1579_, 1);
lean_inc(v_second_1618_);
v___f_1621_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1621_, 0, v_second_1618_);
v___x_1622_ = lean_unsigned_to_nat(0u);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1621_, v_transitions_1620_, v___x_1622_);
if (lean_obj_tag(v___x_1623_) == 1)
{
lean_object* v_val_1624_; lean_object* v_next_1625_; lean_object* v_time_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v_last_1629_; lean_object* v_localTimeType_1630_; lean_object* v_gmtOffset_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_val_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_val_1624_);
lean_dec_ref(v___x_1623_);
v_next_1625_ = lean_array_fget_borrowed(v_transitions_1620_, v_val_1624_);
v_time_1626_ = lean_ctor_get(v_next_1625_, 0);
v___x_1627_ = lean_unsigned_to_nat(1u);
v___x_1628_ = lean_nat_sub(v_val_1624_, v___x_1627_);
lean_dec(v_val_1624_);
v_last_1629_ = lean_array_fget_borrowed(v_transitions_1620_, v___x_1628_);
lean_dec(v___x_1628_);
v_localTimeType_1630_ = lean_ctor_get(v_last_1629_, 1);
v_gmtOffset_1631_ = lean_ctor_get(v_localTimeType_1630_, 0);
v___x_1632_ = lean_nat_abs(v_gmtOffset_1631_);
v___x_1633_ = lean_nat_to_int(v___x_1632_);
v___x_1634_ = lean_int_sub(v_time_1626_, v___x_1633_);
lean_dec(v___x_1633_);
v___x_1635_ = lean_int_dec_lt(v_second_1618_, v___x_1634_);
lean_dec(v___x_1634_);
lean_dec(v_second_1618_);
if (v___x_1635_ == 0)
{
lean_inc(v_next_1625_);
v_val_1616_ = v_next_1625_;
goto v___jp_1615_;
}
else
{
lean_inc(v_last_1629_);
v_val_1616_ = v_last_1629_;
goto v___jp_1615_;
}
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
lean_dec(v___x_1623_);
lean_dec(v_second_1618_);
v___x_1636_ = lean_array_get_size(v_transitions_1620_);
v___x_1637_ = lean_unsigned_to_nat(1u);
v___x_1638_ = lean_nat_sub(v___x_1636_, v___x_1637_);
v___x_1639_ = lean_nat_dec_lt(v___x_1638_, v___x_1636_);
if (v___x_1639_ == 0)
{
lean_dec(v___x_1638_);
lean_inc_ref(v_initialLocalTimeType_1619_);
v___y_1596_ = v_initialLocalTimeType_1619_;
goto v___jp_1595_;
}
else
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_array_fget_borrowed(v_transitions_1620_, v___x_1638_);
lean_dec(v___x_1638_);
lean_inc(v___x_1640_);
v_val_1616_ = v___x_1640_;
goto v___jp_1615_;
}
}
v___jp_1595_:
{
lean_object* v_second_1597_; lean_object* v_nano_1598_; lean_object* v_tz_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_tm_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v_second_1597_ = lean_ctor_get(v_tm_1594_, 0);
lean_inc(v_second_1597_);
v_nano_1598_ = lean_ctor_get(v_tm_1594_, 1);
lean_inc(v_nano_1598_);
lean_dec_ref(v_tm_1594_);
v_tz_1599_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_1596_);
lean_dec_ref(v___y_1596_);
v___x_1600_ = l_Std_Time_TimeZone_toSeconds(v_tz_1599_);
v___x_1601_ = lean_int_neg(v___x_1600_);
v___x_1602_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_1603_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1604_ = lean_int_mul(v_second_1597_, v___x_1603_);
lean_dec(v_second_1597_);
v___x_1605_ = lean_int_add(v___x_1604_, v_nano_1598_);
lean_dec(v_nano_1598_);
lean_dec(v___x_1604_);
v___x_1606_ = lean_int_mul(v___x_1601_, v___x_1603_);
lean_dec(v___x_1601_);
v___x_1607_ = lean_int_add(v___x_1606_, v___x_1602_);
lean_dec(v___x_1606_);
v___x_1608_ = lean_int_add(v___x_1605_, v___x_1607_);
lean_dec(v___x_1607_);
lean_dec(v___x_1605_);
v_tm_1609_ = l_Std_Time_Duration_ofNanoseconds(v___x_1608_);
lean_dec(v___x_1608_);
lean_inc_ref(v_tm_1609_);
v___f_1610_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1610_, 0, v_tm_1609_);
lean_closure_set(v___f_1610_, 1, v___x_1600_);
lean_closure_set(v___f_1610_, 2, v___x_1603_);
v___x_1611_ = lean_mk_thunk(v___f_1610_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 3, v_tz_1599_);
lean_ctor_set(v___x_1581_, 1, v_tm_1609_);
lean_ctor_set(v___x_1581_, 0, v___x_1611_);
v___x_1613_ = v___x_1581_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1614_, 1, v_tm_1609_);
lean_ctor_set(v_reuseFailAlloc_1614_, 2, v_rules_1579_);
lean_ctor_set(v_reuseFailAlloc_1614_, 3, v_tz_1599_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
v___jp_1615_:
{
lean_object* v_localTimeType_1617_; 
v_localTimeType_1617_ = lean_ctor_get(v_val_1616_, 1);
lean_inc_ref(v_localTimeType_1617_);
lean_dec_ref(v_val_1616_);
v___y_1596_ = v_localTimeType_1617_;
goto v___jp_1595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withDaysRollOver___boxed(lean_object* v_dt_1646_, lean_object* v_days_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_Time_ZonedDateTime_withDaysRollOver(v_dt_1646_, v_days_1647_);
lean_dec(v_days_1647_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMonthClip(lean_object* v_dt_1649_, lean_object* v_month_1650_){
_start:
{
lean_object* v_date_1651_; lean_object* v_rules_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1746_; 
v_date_1651_ = lean_ctor_get(v_dt_1649_, 0);
v_rules_1652_ = lean_ctor_get(v_dt_1649_, 2);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_dt_1649_);
if (v_isSharedCheck_1746_ == 0)
{
lean_object* v_unused_1747_; lean_object* v_unused_1748_; 
v_unused_1747_ = lean_ctor_get(v_dt_1649_, 3);
lean_dec(v_unused_1747_);
v_unused_1748_ = lean_ctor_get(v_dt_1649_, 1);
lean_dec(v_unused_1748_);
v___x_1654_ = v_dt_1649_;
v_isShared_1655_ = v_isSharedCheck_1746_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_rules_1652_);
lean_inc(v_date_1651_);
lean_dec(v_dt_1649_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1746_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1678_; lean_object* v_val_1679_; lean_object* v_date_1681_; lean_object* v___y_1683_; lean_object* v_date_1717_; lean_object* v_year_1718_; lean_object* v_day_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1744_; 
v_date_1681_ = lean_thunk_get_own(v_date_1651_);
lean_dec_ref(v_date_1651_);
v_date_1717_ = lean_ctor_get(v_date_1681_, 0);
lean_inc_ref(v_date_1717_);
v_year_1718_ = lean_ctor_get(v_date_1717_, 0);
v_day_1719_ = lean_ctor_get(v_date_1717_, 2);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_date_1717_);
if (v_isSharedCheck_1744_ == 0)
{
lean_object* v_unused_1745_; 
v_unused_1745_ = lean_ctor_get(v_date_1717_, 1);
lean_dec(v_unused_1745_);
v___x_1721_ = v_date_1717_;
v_isShared_1722_ = v_isSharedCheck_1744_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_day_1719_);
lean_inc(v_year_1718_);
lean_dec(v_date_1717_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1744_;
goto v_resetjp_1720_;
}
v___jp_1656_:
{
lean_object* v_second_1659_; lean_object* v_nano_1660_; lean_object* v_tz_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v_tm_1671_; lean_object* v___f_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
v_second_1659_ = lean_ctor_get(v___y_1657_, 0);
lean_inc(v_second_1659_);
v_nano_1660_ = lean_ctor_get(v___y_1657_, 1);
lean_inc(v_nano_1660_);
lean_dec_ref(v___y_1657_);
v_tz_1661_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_1658_);
lean_dec_ref(v___y_1658_);
v___x_1662_ = l_Std_Time_TimeZone_toSeconds(v_tz_1661_);
v___x_1663_ = lean_int_neg(v___x_1662_);
v___x_1664_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_1665_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1666_ = lean_int_mul(v_second_1659_, v___x_1665_);
lean_dec(v_second_1659_);
v___x_1667_ = lean_int_add(v___x_1666_, v_nano_1660_);
lean_dec(v_nano_1660_);
lean_dec(v___x_1666_);
v___x_1668_ = lean_int_mul(v___x_1663_, v___x_1665_);
lean_dec(v___x_1663_);
v___x_1669_ = lean_int_add(v___x_1668_, v___x_1664_);
lean_dec(v___x_1668_);
v___x_1670_ = lean_int_add(v___x_1667_, v___x_1669_);
lean_dec(v___x_1669_);
lean_dec(v___x_1667_);
v_tm_1671_ = l_Std_Time_Duration_ofNanoseconds(v___x_1670_);
lean_dec(v___x_1670_);
lean_inc_ref(v_tm_1671_);
v___f_1672_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1672_, 0, v_tm_1671_);
lean_closure_set(v___f_1672_, 1, v___x_1662_);
lean_closure_set(v___f_1672_, 2, v___x_1665_);
v___x_1673_ = lean_mk_thunk(v___f_1672_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 3, v_tz_1661_);
lean_ctor_set(v___x_1654_, 1, v_tm_1671_);
lean_ctor_set(v___x_1654_, 0, v___x_1673_);
v___x_1675_ = v___x_1654_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_tm_1671_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_rules_1652_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_tz_1661_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
v___jp_1677_:
{
lean_object* v_localTimeType_1680_; 
v_localTimeType_1680_ = lean_ctor_get(v_val_1679_, 1);
lean_inc_ref(v_localTimeType_1680_);
lean_dec_ref(v_val_1679_);
v___y_1657_ = v___y_1678_;
v___y_1658_ = v_localTimeType_1680_;
goto v___jp_1656_;
}
v___jp_1682_:
{
lean_object* v_time_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1715_; 
v_time_1684_ = lean_ctor_get(v_date_1681_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_date_1681_);
if (v_isSharedCheck_1715_ == 0)
{
lean_object* v_unused_1716_; 
v_unused_1716_ = lean_ctor_get(v_date_1681_, 0);
lean_dec(v_unused_1716_);
v___x_1686_ = v_date_1681_;
v_isShared_1687_ = v_isSharedCheck_1715_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_time_1684_);
lean_dec(v_date_1681_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1715_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___y_1683_);
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___y_1683_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_time_1684_);
v___x_1689_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v_tm_1690_; lean_object* v_second_1691_; lean_object* v_initialLocalTimeType_1692_; lean_object* v_transitions_1693_; lean_object* v___f_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v_tm_1690_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1689_);
v_second_1691_ = lean_ctor_get(v_tm_1690_, 0);
lean_inc(v_second_1691_);
v_initialLocalTimeType_1692_ = lean_ctor_get(v_rules_1652_, 0);
v_transitions_1693_ = lean_ctor_get(v_rules_1652_, 1);
lean_inc(v_second_1691_);
v___f_1694_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1694_, 0, v_second_1691_);
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1694_, v_transitions_1693_, v___x_1695_);
if (lean_obj_tag(v___x_1696_) == 1)
{
lean_object* v_val_1697_; lean_object* v_next_1698_; lean_object* v_time_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v_last_1702_; lean_object* v_localTimeType_1703_; lean_object* v_gmtOffset_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v_val_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_val_1697_);
lean_dec_ref(v___x_1696_);
v_next_1698_ = lean_array_fget_borrowed(v_transitions_1693_, v_val_1697_);
v_time_1699_ = lean_ctor_get(v_next_1698_, 0);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_sub(v_val_1697_, v___x_1700_);
lean_dec(v_val_1697_);
v_last_1702_ = lean_array_fget_borrowed(v_transitions_1693_, v___x_1701_);
lean_dec(v___x_1701_);
v_localTimeType_1703_ = lean_ctor_get(v_last_1702_, 1);
v_gmtOffset_1704_ = lean_ctor_get(v_localTimeType_1703_, 0);
v___x_1705_ = lean_nat_abs(v_gmtOffset_1704_);
v___x_1706_ = lean_nat_to_int(v___x_1705_);
v___x_1707_ = lean_int_sub(v_time_1699_, v___x_1706_);
lean_dec(v___x_1706_);
v___x_1708_ = lean_int_dec_lt(v_second_1691_, v___x_1707_);
lean_dec(v___x_1707_);
lean_dec(v_second_1691_);
if (v___x_1708_ == 0)
{
lean_inc(v_next_1698_);
v___y_1678_ = v_tm_1690_;
v_val_1679_ = v_next_1698_;
goto v___jp_1677_;
}
else
{
lean_inc(v_last_1702_);
v___y_1678_ = v_tm_1690_;
v_val_1679_ = v_last_1702_;
goto v___jp_1677_;
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
lean_dec(v___x_1696_);
lean_dec(v_second_1691_);
v___x_1709_ = lean_array_get_size(v_transitions_1693_);
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_sub(v___x_1709_, v___x_1710_);
v___x_1712_ = lean_nat_dec_lt(v___x_1711_, v___x_1709_);
if (v___x_1712_ == 0)
{
lean_dec(v___x_1711_);
lean_inc_ref(v_initialLocalTimeType_1692_);
v___y_1657_ = v_tm_1690_;
v___y_1658_ = v_initialLocalTimeType_1692_;
goto v___jp_1656_;
}
else
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_array_fget_borrowed(v_transitions_1693_, v___x_1711_);
lean_dec(v___x_1711_);
lean_inc(v___x_1713_);
v___y_1678_ = v_tm_1690_;
v_val_1679_ = v___x_1713_;
goto v___jp_1677_;
}
}
}
}
}
v_resetjp_1720_:
{
uint8_t v___y_1724_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1740_; 
v___x_1733_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_1734_ = lean_int_mod(v_year_1718_, v___x_1733_);
v___x_1735_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1740_ = lean_int_dec_eq(v___x_1734_, v___x_1735_);
lean_dec(v___x_1734_);
if (v___x_1740_ == 0)
{
v___y_1724_ = v___x_1740_;
goto v___jp_1723_;
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1741_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_1742_ = lean_int_mod(v_year_1718_, v___x_1741_);
v___x_1743_ = lean_int_dec_eq(v___x_1742_, v___x_1735_);
lean_dec(v___x_1742_);
if (v___x_1743_ == 0)
{
if (v___x_1740_ == 0)
{
goto v___jp_1736_;
}
else
{
v___y_1724_ = v___x_1740_;
goto v___jp_1723_;
}
}
else
{
goto v___jp_1736_;
}
}
v___jp_1723_:
{
lean_object* v_max_1725_; uint8_t v___x_1726_; 
v_max_1725_ = l_Std_Time_Month_Ordinal_days(v___y_1724_, v_month_1650_);
v___x_1726_ = lean_int_dec_lt(v_max_1725_, v_day_1719_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1728_; 
lean_dec(v_max_1725_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 1, v_month_1650_);
v___x_1728_ = v___x_1721_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_year_1718_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_month_1650_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_day_1719_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v___y_1683_ = v___x_1728_;
goto v___jp_1682_;
}
}
else
{
lean_object* v___x_1731_; 
lean_dec(v_day_1719_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 2, v_max_1725_);
lean_ctor_set(v___x_1721_, 1, v_month_1650_);
v___x_1731_ = v___x_1721_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_year_1718_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_month_1650_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_max_1725_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
v___y_1683_ = v___x_1731_;
goto v___jp_1682_;
}
}
}
v___jp_1736_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v___x_1737_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_1738_ = lean_int_mod(v_year_1718_, v___x_1737_);
v___x_1739_ = lean_int_dec_eq(v___x_1738_, v___x_1735_);
lean_dec(v___x_1738_);
v___y_1724_ = v___x_1739_;
goto v___jp_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMonthRollOver(lean_object* v_dt_1749_, lean_object* v_month_1750_){
_start:
{
lean_object* v_date_1751_; lean_object* v_rules_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1816_; 
v_date_1751_ = lean_ctor_get(v_dt_1749_, 0);
v_rules_1752_ = lean_ctor_get(v_dt_1749_, 2);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_dt_1749_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; lean_object* v_unused_1818_; 
v_unused_1817_ = lean_ctor_get(v_dt_1749_, 3);
lean_dec(v_unused_1817_);
v_unused_1818_ = lean_ctor_get(v_dt_1749_, 1);
lean_dec(v_unused_1818_);
v___x_1754_ = v_dt_1749_;
v_isShared_1755_ = v_isSharedCheck_1816_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_rules_1752_);
lean_inc(v_date_1751_);
lean_dec(v_dt_1749_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1816_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_date_1756_; lean_object* v_date_1757_; lean_object* v_time_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1815_; 
v_date_1756_ = lean_thunk_get_own(v_date_1751_);
lean_dec_ref(v_date_1751_);
v_date_1757_ = lean_ctor_get(v_date_1756_, 0);
v_time_1758_ = lean_ctor_get(v_date_1756_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_date_1756_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1760_ = v_date_1756_;
v_isShared_1761_ = v_isSharedCheck_1815_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_time_1758_);
lean_inc(v_date_1757_);
lean_dec(v_date_1756_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1815_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_year_1762_; lean_object* v_day_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v_year_1762_ = lean_ctor_get(v_date_1757_, 0);
lean_inc(v_year_1762_);
v_day_1763_ = lean_ctor_get(v_date_1757_, 2);
lean_inc(v_day_1763_);
lean_dec_ref(v_date_1757_);
v___x_1764_ = l_Std_Time_PlainDate_rollOver(v_year_1762_, v_month_1750_, v_day_1763_);
lean_dec(v_day_1763_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1764_);
v___x_1766_ = v___x_1760_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_time_1758_);
v___x_1766_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v_tm_1767_; lean_object* v___y_1769_; lean_object* v_val_1789_; lean_object* v_second_1791_; lean_object* v_initialLocalTimeType_1792_; lean_object* v_transitions_1793_; lean_object* v___f_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_tm_1767_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1766_);
v_second_1791_ = lean_ctor_get(v_tm_1767_, 0);
lean_inc(v_second_1791_);
v_initialLocalTimeType_1792_ = lean_ctor_get(v_rules_1752_, 0);
v_transitions_1793_ = lean_ctor_get(v_rules_1752_, 1);
lean_inc(v_second_1791_);
v___f_1794_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1794_, 0, v_second_1791_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1794_, v_transitions_1793_, v___x_1795_);
if (lean_obj_tag(v___x_1796_) == 1)
{
lean_object* v_val_1797_; lean_object* v_next_1798_; lean_object* v_time_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v_last_1802_; lean_object* v_localTimeType_1803_; lean_object* v_gmtOffset_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_val_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_val_1797_);
lean_dec_ref(v___x_1796_);
v_next_1798_ = lean_array_fget_borrowed(v_transitions_1793_, v_val_1797_);
v_time_1799_ = lean_ctor_get(v_next_1798_, 0);
v___x_1800_ = lean_unsigned_to_nat(1u);
v___x_1801_ = lean_nat_sub(v_val_1797_, v___x_1800_);
lean_dec(v_val_1797_);
v_last_1802_ = lean_array_fget_borrowed(v_transitions_1793_, v___x_1801_);
lean_dec(v___x_1801_);
v_localTimeType_1803_ = lean_ctor_get(v_last_1802_, 1);
v_gmtOffset_1804_ = lean_ctor_get(v_localTimeType_1803_, 0);
v___x_1805_ = lean_nat_abs(v_gmtOffset_1804_);
v___x_1806_ = lean_nat_to_int(v___x_1805_);
v___x_1807_ = lean_int_sub(v_time_1799_, v___x_1806_);
lean_dec(v___x_1806_);
v___x_1808_ = lean_int_dec_lt(v_second_1791_, v___x_1807_);
lean_dec(v___x_1807_);
lean_dec(v_second_1791_);
if (v___x_1808_ == 0)
{
lean_inc(v_next_1798_);
v_val_1789_ = v_next_1798_;
goto v___jp_1788_;
}
else
{
lean_inc(v_last_1802_);
v_val_1789_ = v_last_1802_;
goto v___jp_1788_;
}
}
else
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
lean_dec(v___x_1796_);
lean_dec(v_second_1791_);
v___x_1809_ = lean_array_get_size(v_transitions_1793_);
v___x_1810_ = lean_unsigned_to_nat(1u);
v___x_1811_ = lean_nat_sub(v___x_1809_, v___x_1810_);
v___x_1812_ = lean_nat_dec_lt(v___x_1811_, v___x_1809_);
if (v___x_1812_ == 0)
{
lean_dec(v___x_1811_);
lean_inc_ref(v_initialLocalTimeType_1792_);
v___y_1769_ = v_initialLocalTimeType_1792_;
goto v___jp_1768_;
}
else
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_array_fget_borrowed(v_transitions_1793_, v___x_1811_);
lean_dec(v___x_1811_);
lean_inc(v___x_1813_);
v_val_1789_ = v___x_1813_;
goto v___jp_1788_;
}
}
v___jp_1768_:
{
lean_object* v_second_1770_; lean_object* v_nano_1771_; lean_object* v_tz_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_tm_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v_second_1770_ = lean_ctor_get(v_tm_1767_, 0);
lean_inc(v_second_1770_);
v_nano_1771_ = lean_ctor_get(v_tm_1767_, 1);
lean_inc(v_nano_1771_);
lean_dec_ref(v_tm_1767_);
v_tz_1772_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_1769_);
lean_dec_ref(v___y_1769_);
v___x_1773_ = l_Std_Time_TimeZone_toSeconds(v_tz_1772_);
v___x_1774_ = lean_int_neg(v___x_1773_);
v___x_1775_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_1776_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1777_ = lean_int_mul(v_second_1770_, v___x_1776_);
lean_dec(v_second_1770_);
v___x_1778_ = lean_int_add(v___x_1777_, v_nano_1771_);
lean_dec(v_nano_1771_);
lean_dec(v___x_1777_);
v___x_1779_ = lean_int_mul(v___x_1774_, v___x_1776_);
lean_dec(v___x_1774_);
v___x_1780_ = lean_int_add(v___x_1779_, v___x_1775_);
lean_dec(v___x_1779_);
v___x_1781_ = lean_int_add(v___x_1778_, v___x_1780_);
lean_dec(v___x_1780_);
lean_dec(v___x_1778_);
v_tm_1782_ = l_Std_Time_Duration_ofNanoseconds(v___x_1781_);
lean_dec(v___x_1781_);
lean_inc_ref(v_tm_1782_);
v___f_1783_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1783_, 0, v_tm_1782_);
lean_closure_set(v___f_1783_, 1, v___x_1773_);
lean_closure_set(v___f_1783_, 2, v___x_1776_);
v___x_1784_ = lean_mk_thunk(v___f_1783_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 3, v_tz_1772_);
lean_ctor_set(v___x_1754_, 1, v_tm_1782_);
lean_ctor_set(v___x_1754_, 0, v___x_1784_);
v___x_1786_ = v___x_1754_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_tm_1782_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_rules_1752_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v_tz_1772_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
v___jp_1788_:
{
lean_object* v_localTimeType_1790_; 
v_localTimeType_1790_ = lean_ctor_get(v_val_1789_, 1);
lean_inc_ref(v_localTimeType_1790_);
lean_dec_ref(v_val_1789_);
v___y_1769_ = v_localTimeType_1790_;
goto v___jp_1768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withYearClip(lean_object* v_dt_1819_, lean_object* v_year_1820_){
_start:
{
lean_object* v_date_1821_; lean_object* v_rules_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1916_; 
v_date_1821_ = lean_ctor_get(v_dt_1819_, 0);
v_rules_1822_ = lean_ctor_get(v_dt_1819_, 2);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_dt_1819_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; lean_object* v_unused_1918_; 
v_unused_1917_ = lean_ctor_get(v_dt_1819_, 3);
lean_dec(v_unused_1917_);
v_unused_1918_ = lean_ctor_get(v_dt_1819_, 1);
lean_dec(v_unused_1918_);
v___x_1824_ = v_dt_1819_;
v_isShared_1825_ = v_isSharedCheck_1916_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_rules_1822_);
lean_inc(v_date_1821_);
lean_dec(v_dt_1819_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1916_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1848_; lean_object* v_val_1849_; lean_object* v_date_1851_; lean_object* v___y_1853_; lean_object* v_date_1887_; lean_object* v_month_1888_; lean_object* v_day_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1914_; 
v_date_1851_ = lean_thunk_get_own(v_date_1821_);
lean_dec_ref(v_date_1821_);
v_date_1887_ = lean_ctor_get(v_date_1851_, 0);
lean_inc_ref(v_date_1887_);
v_month_1888_ = lean_ctor_get(v_date_1887_, 1);
v_day_1889_ = lean_ctor_get(v_date_1887_, 2);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_date_1887_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; 
v_unused_1915_ = lean_ctor_get(v_date_1887_, 0);
lean_dec(v_unused_1915_);
v___x_1891_ = v_date_1887_;
v_isShared_1892_ = v_isSharedCheck_1914_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_day_1889_);
lean_inc(v_month_1888_);
lean_dec(v_date_1887_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1914_;
goto v_resetjp_1890_;
}
v___jp_1826_:
{
lean_object* v_second_1829_; lean_object* v_nano_1830_; lean_object* v_tz_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v_tm_1841_; lean_object* v___f_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
v_second_1829_ = lean_ctor_get(v___y_1827_, 0);
lean_inc(v_second_1829_);
v_nano_1830_ = lean_ctor_get(v___y_1827_, 1);
lean_inc(v_nano_1830_);
lean_dec_ref(v___y_1827_);
v_tz_1831_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_1828_);
lean_dec_ref(v___y_1828_);
v___x_1832_ = l_Std_Time_TimeZone_toSeconds(v_tz_1831_);
v___x_1833_ = lean_int_neg(v___x_1832_);
v___x_1834_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_1835_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1836_ = lean_int_mul(v_second_1829_, v___x_1835_);
lean_dec(v_second_1829_);
v___x_1837_ = lean_int_add(v___x_1836_, v_nano_1830_);
lean_dec(v_nano_1830_);
lean_dec(v___x_1836_);
v___x_1838_ = lean_int_mul(v___x_1833_, v___x_1835_);
lean_dec(v___x_1833_);
v___x_1839_ = lean_int_add(v___x_1838_, v___x_1834_);
lean_dec(v___x_1838_);
v___x_1840_ = lean_int_add(v___x_1837_, v___x_1839_);
lean_dec(v___x_1839_);
lean_dec(v___x_1837_);
v_tm_1841_ = l_Std_Time_Duration_ofNanoseconds(v___x_1840_);
lean_dec(v___x_1840_);
lean_inc_ref(v_tm_1841_);
v___f_1842_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1842_, 0, v_tm_1841_);
lean_closure_set(v___f_1842_, 1, v___x_1832_);
lean_closure_set(v___f_1842_, 2, v___x_1835_);
v___x_1843_ = lean_mk_thunk(v___f_1842_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 3, v_tz_1831_);
lean_ctor_set(v___x_1824_, 1, v_tm_1841_);
lean_ctor_set(v___x_1824_, 0, v___x_1843_);
v___x_1845_ = v___x_1824_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_tm_1841_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_rules_1822_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_tz_1831_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
v___jp_1847_:
{
lean_object* v_localTimeType_1850_; 
v_localTimeType_1850_ = lean_ctor_get(v_val_1849_, 1);
lean_inc_ref(v_localTimeType_1850_);
lean_dec_ref(v_val_1849_);
v___y_1827_ = v___y_1848_;
v___y_1828_ = v_localTimeType_1850_;
goto v___jp_1826_;
}
v___jp_1852_:
{
lean_object* v_time_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1885_; 
v_time_1854_ = lean_ctor_get(v_date_1851_, 1);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_date_1851_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v_date_1851_, 0);
lean_dec(v_unused_1886_);
v___x_1856_ = v_date_1851_;
v_isShared_1857_ = v_isSharedCheck_1885_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_time_1854_);
lean_dec(v_date_1851_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1885_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___y_1853_);
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___y_1853_);
lean_ctor_set(v_reuseFailAlloc_1884_, 1, v_time_1854_);
v___x_1859_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v_tm_1860_; lean_object* v_second_1861_; lean_object* v_initialLocalTimeType_1862_; lean_object* v_transitions_1863_; lean_object* v___f_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_tm_1860_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1859_);
v_second_1861_ = lean_ctor_get(v_tm_1860_, 0);
lean_inc(v_second_1861_);
v_initialLocalTimeType_1862_ = lean_ctor_get(v_rules_1822_, 0);
v_transitions_1863_ = lean_ctor_get(v_rules_1822_, 1);
lean_inc(v_second_1861_);
v___f_1864_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1864_, 0, v_second_1861_);
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1864_, v_transitions_1863_, v___x_1865_);
if (lean_obj_tag(v___x_1866_) == 1)
{
lean_object* v_val_1867_; lean_object* v_next_1868_; lean_object* v_time_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_last_1872_; lean_object* v_localTimeType_1873_; lean_object* v_gmtOffset_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v_val_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_val_1867_);
lean_dec_ref(v___x_1866_);
v_next_1868_ = lean_array_fget_borrowed(v_transitions_1863_, v_val_1867_);
v_time_1869_ = lean_ctor_get(v_next_1868_, 0);
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = lean_nat_sub(v_val_1867_, v___x_1870_);
lean_dec(v_val_1867_);
v_last_1872_ = lean_array_fget_borrowed(v_transitions_1863_, v___x_1871_);
lean_dec(v___x_1871_);
v_localTimeType_1873_ = lean_ctor_get(v_last_1872_, 1);
v_gmtOffset_1874_ = lean_ctor_get(v_localTimeType_1873_, 0);
v___x_1875_ = lean_nat_abs(v_gmtOffset_1874_);
v___x_1876_ = lean_nat_to_int(v___x_1875_);
v___x_1877_ = lean_int_sub(v_time_1869_, v___x_1876_);
lean_dec(v___x_1876_);
v___x_1878_ = lean_int_dec_lt(v_second_1861_, v___x_1877_);
lean_dec(v___x_1877_);
lean_dec(v_second_1861_);
if (v___x_1878_ == 0)
{
lean_inc(v_next_1868_);
v___y_1848_ = v_tm_1860_;
v_val_1849_ = v_next_1868_;
goto v___jp_1847_;
}
else
{
lean_inc(v_last_1872_);
v___y_1848_ = v_tm_1860_;
v_val_1849_ = v_last_1872_;
goto v___jp_1847_;
}
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
lean_dec(v___x_1866_);
lean_dec(v_second_1861_);
v___x_1879_ = lean_array_get_size(v_transitions_1863_);
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = lean_nat_sub(v___x_1879_, v___x_1880_);
v___x_1882_ = lean_nat_dec_lt(v___x_1881_, v___x_1879_);
if (v___x_1882_ == 0)
{
lean_dec(v___x_1881_);
lean_inc_ref(v_initialLocalTimeType_1862_);
v___y_1827_ = v_tm_1860_;
v___y_1828_ = v_initialLocalTimeType_1862_;
goto v___jp_1826_;
}
else
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_array_fget_borrowed(v_transitions_1863_, v___x_1881_);
lean_dec(v___x_1881_);
lean_inc(v___x_1883_);
v___y_1848_ = v_tm_1860_;
v_val_1849_ = v___x_1883_;
goto v___jp_1847_;
}
}
}
}
}
v_resetjp_1890_:
{
uint8_t v___y_1894_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1910_; 
v___x_1903_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_1904_ = lean_int_mod(v_year_1820_, v___x_1903_);
v___x_1905_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_1910_ = lean_int_dec_eq(v___x_1904_, v___x_1905_);
lean_dec(v___x_1904_);
if (v___x_1910_ == 0)
{
v___y_1894_ = v___x_1910_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v___x_1911_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_1912_ = lean_int_mod(v_year_1820_, v___x_1911_);
v___x_1913_ = lean_int_dec_eq(v___x_1912_, v___x_1905_);
lean_dec(v___x_1912_);
if (v___x_1913_ == 0)
{
if (v___x_1910_ == 0)
{
goto v___jp_1906_;
}
else
{
v___y_1894_ = v___x_1910_;
goto v___jp_1893_;
}
}
else
{
goto v___jp_1906_;
}
}
v___jp_1893_:
{
lean_object* v_max_1895_; uint8_t v___x_1896_; 
v_max_1895_ = l_Std_Time_Month_Ordinal_days(v___y_1894_, v_month_1888_);
v___x_1896_ = lean_int_dec_lt(v_max_1895_, v_day_1889_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1898_; 
lean_dec(v_max_1895_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v_year_1820_);
v___x_1898_ = v___x_1891_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_year_1820_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_month_1888_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_day_1889_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
v___y_1853_ = v___x_1898_;
goto v___jp_1852_;
}
}
else
{
lean_object* v___x_1901_; 
lean_dec(v_day_1889_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 2, v_max_1895_);
lean_ctor_set(v___x_1891_, 0, v_year_1820_);
v___x_1901_ = v___x_1891_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_year_1820_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_month_1888_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_max_1895_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
v___y_1853_ = v___x_1901_;
goto v___jp_1852_;
}
}
}
v___jp_1906_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1907_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_1908_ = lean_int_mod(v_year_1820_, v___x_1907_);
v___x_1909_ = lean_int_dec_eq(v___x_1908_, v___x_1905_);
lean_dec(v___x_1908_);
v___y_1894_ = v___x_1909_;
goto v___jp_1893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withYearRollOver(lean_object* v_dt_1919_, lean_object* v_year_1920_){
_start:
{
lean_object* v_date_1921_; lean_object* v_rules_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1986_; 
v_date_1921_ = lean_ctor_get(v_dt_1919_, 0);
v_rules_1922_ = lean_ctor_get(v_dt_1919_, 2);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_dt_1919_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1987_ = lean_ctor_get(v_dt_1919_, 3);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_dt_1919_, 1);
lean_dec(v_unused_1988_);
v___x_1924_ = v_dt_1919_;
v_isShared_1925_ = v_isSharedCheck_1986_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_rules_1922_);
lean_inc(v_date_1921_);
lean_dec(v_dt_1919_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1986_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v_date_1926_; lean_object* v_date_1927_; lean_object* v_time_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1985_; 
v_date_1926_ = lean_thunk_get_own(v_date_1921_);
lean_dec_ref(v_date_1921_);
v_date_1927_ = lean_ctor_get(v_date_1926_, 0);
v_time_1928_ = lean_ctor_get(v_date_1926_, 1);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_date_1926_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1930_ = v_date_1926_;
v_isShared_1931_ = v_isSharedCheck_1985_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_time_1928_);
lean_inc(v_date_1927_);
lean_dec(v_date_1926_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1985_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_month_1932_; lean_object* v_day_1933_; lean_object* v___x_1934_; lean_object* v___x_1936_; 
v_month_1932_ = lean_ctor_get(v_date_1927_, 1);
lean_inc(v_month_1932_);
v_day_1933_ = lean_ctor_get(v_date_1927_, 2);
lean_inc(v_day_1933_);
lean_dec_ref(v_date_1927_);
v___x_1934_ = l_Std_Time_PlainDate_rollOver(v_year_1920_, v_month_1932_, v_day_1933_);
lean_dec(v_day_1933_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1934_);
v___x_1936_ = v___x_1930_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_time_1928_);
v___x_1936_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v_tm_1937_; lean_object* v___y_1939_; lean_object* v_val_1959_; lean_object* v_second_1961_; lean_object* v_initialLocalTimeType_1962_; lean_object* v_transitions_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v_tm_1937_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1936_);
v_second_1961_ = lean_ctor_get(v_tm_1937_, 0);
lean_inc(v_second_1961_);
v_initialLocalTimeType_1962_ = lean_ctor_get(v_rules_1922_, 0);
v_transitions_1963_ = lean_ctor_get(v_rules_1922_, 1);
lean_inc(v_second_1961_);
v___f_1964_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_1964_, 0, v_second_1961_);
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_1964_, v_transitions_1963_, v___x_1965_);
if (lean_obj_tag(v___x_1966_) == 1)
{
lean_object* v_val_1967_; lean_object* v_next_1968_; lean_object* v_time_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v_last_1972_; lean_object* v_localTimeType_1973_; lean_object* v_gmtOffset_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_val_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_val_1967_);
lean_dec_ref(v___x_1966_);
v_next_1968_ = lean_array_fget_borrowed(v_transitions_1963_, v_val_1967_);
v_time_1969_ = lean_ctor_get(v_next_1968_, 0);
v___x_1970_ = lean_unsigned_to_nat(1u);
v___x_1971_ = lean_nat_sub(v_val_1967_, v___x_1970_);
lean_dec(v_val_1967_);
v_last_1972_ = lean_array_fget_borrowed(v_transitions_1963_, v___x_1971_);
lean_dec(v___x_1971_);
v_localTimeType_1973_ = lean_ctor_get(v_last_1972_, 1);
v_gmtOffset_1974_ = lean_ctor_get(v_localTimeType_1973_, 0);
v___x_1975_ = lean_nat_abs(v_gmtOffset_1974_);
v___x_1976_ = lean_nat_to_int(v___x_1975_);
v___x_1977_ = lean_int_sub(v_time_1969_, v___x_1976_);
lean_dec(v___x_1976_);
v___x_1978_ = lean_int_dec_lt(v_second_1961_, v___x_1977_);
lean_dec(v___x_1977_);
lean_dec(v_second_1961_);
if (v___x_1978_ == 0)
{
lean_inc(v_next_1968_);
v_val_1959_ = v_next_1968_;
goto v___jp_1958_;
}
else
{
lean_inc(v_last_1972_);
v_val_1959_ = v_last_1972_;
goto v___jp_1958_;
}
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
lean_dec(v___x_1966_);
lean_dec(v_second_1961_);
v___x_1979_ = lean_array_get_size(v_transitions_1963_);
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = lean_nat_sub(v___x_1979_, v___x_1980_);
v___x_1982_ = lean_nat_dec_lt(v___x_1981_, v___x_1979_);
if (v___x_1982_ == 0)
{
lean_dec(v___x_1981_);
lean_inc_ref(v_initialLocalTimeType_1962_);
v___y_1939_ = v_initialLocalTimeType_1962_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_array_fget_borrowed(v_transitions_1963_, v___x_1981_);
lean_dec(v___x_1981_);
lean_inc(v___x_1983_);
v_val_1959_ = v___x_1983_;
goto v___jp_1958_;
}
}
v___jp_1938_:
{
lean_object* v_second_1940_; lean_object* v_nano_1941_; lean_object* v_tz_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v_tm_1952_; lean_object* v___f_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v_second_1940_ = lean_ctor_get(v_tm_1937_, 0);
lean_inc(v_second_1940_);
v_nano_1941_ = lean_ctor_get(v_tm_1937_, 1);
lean_inc(v_nano_1941_);
lean_dec_ref(v_tm_1937_);
v_tz_1942_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_1939_);
lean_dec_ref(v___y_1939_);
v___x_1943_ = l_Std_Time_TimeZone_toSeconds(v_tz_1942_);
v___x_1944_ = lean_int_neg(v___x_1943_);
v___x_1945_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_1946_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_1947_ = lean_int_mul(v_second_1940_, v___x_1946_);
lean_dec(v_second_1940_);
v___x_1948_ = lean_int_add(v___x_1947_, v_nano_1941_);
lean_dec(v_nano_1941_);
lean_dec(v___x_1947_);
v___x_1949_ = lean_int_mul(v___x_1944_, v___x_1946_);
lean_dec(v___x_1944_);
v___x_1950_ = lean_int_add(v___x_1949_, v___x_1945_);
lean_dec(v___x_1949_);
v___x_1951_ = lean_int_add(v___x_1948_, v___x_1950_);
lean_dec(v___x_1950_);
lean_dec(v___x_1948_);
v_tm_1952_ = l_Std_Time_Duration_ofNanoseconds(v___x_1951_);
lean_dec(v___x_1951_);
lean_inc_ref(v_tm_1952_);
v___f_1953_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1953_, 0, v_tm_1952_);
lean_closure_set(v___f_1953_, 1, v___x_1943_);
lean_closure_set(v___f_1953_, 2, v___x_1946_);
v___x_1954_ = lean_mk_thunk(v___f_1953_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 3, v_tz_1942_);
lean_ctor_set(v___x_1924_, 1, v_tm_1952_);
lean_ctor_set(v___x_1924_, 0, v___x_1954_);
v___x_1956_ = v___x_1924_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_tm_1952_);
lean_ctor_set(v_reuseFailAlloc_1957_, 2, v_rules_1922_);
lean_ctor_set(v_reuseFailAlloc_1957_, 3, v_tz_1942_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
v___jp_1958_:
{
lean_object* v_localTimeType_1960_; 
v_localTimeType_1960_ = lean_ctor_get(v_val_1959_, 1);
lean_inc_ref(v_localTimeType_1960_);
lean_dec_ref(v_val_1959_);
v___y_1939_ = v_localTimeType_1960_;
goto v___jp_1938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withHours(lean_object* v_dt_1989_, lean_object* v_hour_1990_){
_start:
{
lean_object* v_date_1991_; lean_object* v_rules_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2064_; 
v_date_1991_ = lean_ctor_get(v_dt_1989_, 0);
v_rules_1992_ = lean_ctor_get(v_dt_1989_, 2);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_dt_1989_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; lean_object* v_unused_2066_; 
v_unused_2065_ = lean_ctor_get(v_dt_1989_, 3);
lean_dec(v_unused_2065_);
v_unused_2066_ = lean_ctor_get(v_dt_1989_, 1);
lean_dec(v_unused_2066_);
v___x_1994_ = v_dt_1989_;
v_isShared_1995_ = v_isSharedCheck_2064_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_rules_1992_);
lean_inc(v_date_1991_);
lean_dec(v_dt_1989_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2064_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v_date_1996_; lean_object* v_time_1997_; lean_object* v_date_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2063_; 
v_date_1996_ = lean_thunk_get_own(v_date_1991_);
lean_dec_ref(v_date_1991_);
v_time_1997_ = lean_ctor_get(v_date_1996_, 1);
v_date_1998_ = lean_ctor_get(v_date_1996_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_date_1996_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2000_ = v_date_1996_;
v_isShared_2001_ = v_isSharedCheck_2063_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_time_1997_);
lean_inc(v_date_1998_);
lean_dec(v_date_1996_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2063_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_minute_2002_; lean_object* v_second_2003_; lean_object* v_nanosecond_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2061_; 
v_minute_2002_ = lean_ctor_get(v_time_1997_, 1);
v_second_2003_ = lean_ctor_get(v_time_1997_, 2);
v_nanosecond_2004_ = lean_ctor_get(v_time_1997_, 3);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_time_1997_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_time_1997_, 0);
lean_dec(v_unused_2062_);
v___x_2006_ = v_time_1997_;
v_isShared_2007_ = v_isSharedCheck_2061_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_nanosecond_2004_);
lean_inc(v_second_2003_);
lean_inc(v_minute_2002_);
lean_dec(v_time_1997_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2061_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v_hour_1990_);
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_hour_1990_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_minute_2002_);
lean_ctor_set(v_reuseFailAlloc_2060_, 2, v_second_2003_);
lean_ctor_set(v_reuseFailAlloc_2060_, 3, v_nanosecond_2004_);
v___x_2009_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
lean_object* v___x_2011_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2009_);
v___x_2011_ = v___x_2000_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_date_1998_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
lean_object* v_tm_2012_; lean_object* v___y_2014_; lean_object* v_val_2034_; lean_object* v_second_2036_; lean_object* v_initialLocalTimeType_2037_; lean_object* v_transitions_2038_; lean_object* v___f_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v_tm_2012_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2011_);
v_second_2036_ = lean_ctor_get(v_tm_2012_, 0);
lean_inc(v_second_2036_);
v_initialLocalTimeType_2037_ = lean_ctor_get(v_rules_1992_, 0);
v_transitions_2038_ = lean_ctor_get(v_rules_1992_, 1);
lean_inc(v_second_2036_);
v___f_2039_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2039_, 0, v_second_2036_);
v___x_2040_ = lean_unsigned_to_nat(0u);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_2039_, v_transitions_2038_, v___x_2040_);
if (lean_obj_tag(v___x_2041_) == 1)
{
lean_object* v_val_2042_; lean_object* v_next_2043_; lean_object* v_time_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v_last_2047_; lean_object* v_localTimeType_2048_; lean_object* v_gmtOffset_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; uint8_t v___x_2053_; 
v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_val_2042_);
lean_dec_ref(v___x_2041_);
v_next_2043_ = lean_array_fget_borrowed(v_transitions_2038_, v_val_2042_);
v_time_2044_ = lean_ctor_get(v_next_2043_, 0);
v___x_2045_ = lean_unsigned_to_nat(1u);
v___x_2046_ = lean_nat_sub(v_val_2042_, v___x_2045_);
lean_dec(v_val_2042_);
v_last_2047_ = lean_array_fget_borrowed(v_transitions_2038_, v___x_2046_);
lean_dec(v___x_2046_);
v_localTimeType_2048_ = lean_ctor_get(v_last_2047_, 1);
v_gmtOffset_2049_ = lean_ctor_get(v_localTimeType_2048_, 0);
v___x_2050_ = lean_nat_abs(v_gmtOffset_2049_);
v___x_2051_ = lean_nat_to_int(v___x_2050_);
v___x_2052_ = lean_int_sub(v_time_2044_, v___x_2051_);
lean_dec(v___x_2051_);
v___x_2053_ = lean_int_dec_lt(v_second_2036_, v___x_2052_);
lean_dec(v___x_2052_);
lean_dec(v_second_2036_);
if (v___x_2053_ == 0)
{
lean_inc(v_next_2043_);
v_val_2034_ = v_next_2043_;
goto v___jp_2033_;
}
else
{
lean_inc(v_last_2047_);
v_val_2034_ = v_last_2047_;
goto v___jp_2033_;
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
lean_dec(v___x_2041_);
lean_dec(v_second_2036_);
v___x_2054_ = lean_array_get_size(v_transitions_2038_);
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_sub(v___x_2054_, v___x_2055_);
v___x_2057_ = lean_nat_dec_lt(v___x_2056_, v___x_2054_);
if (v___x_2057_ == 0)
{
lean_dec(v___x_2056_);
lean_inc_ref(v_initialLocalTimeType_2037_);
v___y_2014_ = v_initialLocalTimeType_2037_;
goto v___jp_2013_;
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = lean_array_fget_borrowed(v_transitions_2038_, v___x_2056_);
lean_dec(v___x_2056_);
lean_inc(v___x_2058_);
v_val_2034_ = v___x_2058_;
goto v___jp_2033_;
}
}
v___jp_2013_:
{
lean_object* v_second_2015_; lean_object* v_nano_2016_; lean_object* v_tz_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v_tm_2027_; lean_object* v___f_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v_second_2015_ = lean_ctor_get(v_tm_2012_, 0);
lean_inc(v_second_2015_);
v_nano_2016_ = lean_ctor_get(v_tm_2012_, 1);
lean_inc(v_nano_2016_);
lean_dec_ref(v_tm_2012_);
v_tz_2017_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_2014_);
lean_dec_ref(v___y_2014_);
v___x_2018_ = l_Std_Time_TimeZone_toSeconds(v_tz_2017_);
v___x_2019_ = lean_int_neg(v___x_2018_);
v___x_2020_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_2021_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_2022_ = lean_int_mul(v_second_2015_, v___x_2021_);
lean_dec(v_second_2015_);
v___x_2023_ = lean_int_add(v___x_2022_, v_nano_2016_);
lean_dec(v_nano_2016_);
lean_dec(v___x_2022_);
v___x_2024_ = lean_int_mul(v___x_2019_, v___x_2021_);
lean_dec(v___x_2019_);
v___x_2025_ = lean_int_add(v___x_2024_, v___x_2020_);
lean_dec(v___x_2024_);
v___x_2026_ = lean_int_add(v___x_2023_, v___x_2025_);
lean_dec(v___x_2025_);
lean_dec(v___x_2023_);
v_tm_2027_ = l_Std_Time_Duration_ofNanoseconds(v___x_2026_);
lean_dec(v___x_2026_);
lean_inc_ref(v_tm_2027_);
v___f_2028_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2028_, 0, v_tm_2027_);
lean_closure_set(v___f_2028_, 1, v___x_2018_);
lean_closure_set(v___f_2028_, 2, v___x_2021_);
v___x_2029_ = lean_mk_thunk(v___f_2028_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 3, v_tz_2017_);
lean_ctor_set(v___x_1994_, 1, v_tm_2027_);
lean_ctor_set(v___x_1994_, 0, v___x_2029_);
v___x_2031_ = v___x_1994_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_tm_2027_);
lean_ctor_set(v_reuseFailAlloc_2032_, 2, v_rules_1992_);
lean_ctor_set(v_reuseFailAlloc_2032_, 3, v_tz_2017_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
v___jp_2033_:
{
lean_object* v_localTimeType_2035_; 
v_localTimeType_2035_ = lean_ctor_get(v_val_2034_, 1);
lean_inc_ref(v_localTimeType_2035_);
lean_dec_ref(v_val_2034_);
v___y_2014_ = v_localTimeType_2035_;
goto v___jp_2013_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMinutes(lean_object* v_dt_2067_, lean_object* v_minute_2068_){
_start:
{
lean_object* v_date_2069_; lean_object* v_rules_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2142_; 
v_date_2069_ = lean_ctor_get(v_dt_2067_, 0);
v_rules_2070_ = lean_ctor_get(v_dt_2067_, 2);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_dt_2067_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; lean_object* v_unused_2144_; 
v_unused_2143_ = lean_ctor_get(v_dt_2067_, 3);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_dt_2067_, 1);
lean_dec(v_unused_2144_);
v___x_2072_ = v_dt_2067_;
v_isShared_2073_ = v_isSharedCheck_2142_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_rules_2070_);
lean_inc(v_date_2069_);
lean_dec(v_dt_2067_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2142_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v_date_2074_; lean_object* v_time_2075_; lean_object* v_date_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2141_; 
v_date_2074_ = lean_thunk_get_own(v_date_2069_);
lean_dec_ref(v_date_2069_);
v_time_2075_ = lean_ctor_get(v_date_2074_, 1);
v_date_2076_ = lean_ctor_get(v_date_2074_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_date_2074_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2078_ = v_date_2074_;
v_isShared_2079_ = v_isSharedCheck_2141_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_time_2075_);
lean_inc(v_date_2076_);
lean_dec(v_date_2074_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2141_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v_hour_2080_; lean_object* v_second_2081_; lean_object* v_nanosecond_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2139_; 
v_hour_2080_ = lean_ctor_get(v_time_2075_, 0);
v_second_2081_ = lean_ctor_get(v_time_2075_, 2);
v_nanosecond_2082_ = lean_ctor_get(v_time_2075_, 3);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_time_2075_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; 
v_unused_2140_ = lean_ctor_get(v_time_2075_, 1);
lean_dec(v_unused_2140_);
v___x_2084_ = v_time_2075_;
v_isShared_2085_ = v_isSharedCheck_2139_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_nanosecond_2082_);
lean_inc(v_second_2081_);
lean_inc(v_hour_2080_);
lean_dec(v_time_2075_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2139_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v_minute_2068_);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_hour_2080_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v_minute_2068_);
lean_ctor_set(v_reuseFailAlloc_2138_, 2, v_second_2081_);
lean_ctor_set(v_reuseFailAlloc_2138_, 3, v_nanosecond_2082_);
v___x_2087_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2089_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 1, v___x_2087_);
v___x_2089_ = v___x_2078_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_date_2076_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v_tm_2090_; lean_object* v___y_2092_; lean_object* v_val_2112_; lean_object* v_second_2114_; lean_object* v_initialLocalTimeType_2115_; lean_object* v_transitions_2116_; lean_object* v___f_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_tm_2090_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2089_);
v_second_2114_ = lean_ctor_get(v_tm_2090_, 0);
lean_inc(v_second_2114_);
v_initialLocalTimeType_2115_ = lean_ctor_get(v_rules_2070_, 0);
v_transitions_2116_ = lean_ctor_get(v_rules_2070_, 1);
lean_inc(v_second_2114_);
v___f_2117_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2117_, 0, v_second_2114_);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_2117_, v_transitions_2116_, v___x_2118_);
if (lean_obj_tag(v___x_2119_) == 1)
{
lean_object* v_val_2120_; lean_object* v_next_2121_; lean_object* v_time_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v_last_2125_; lean_object* v_localTimeType_2126_; lean_object* v_gmtOffset_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; 
v_val_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_val_2120_);
lean_dec_ref(v___x_2119_);
v_next_2121_ = lean_array_fget_borrowed(v_transitions_2116_, v_val_2120_);
v_time_2122_ = lean_ctor_get(v_next_2121_, 0);
v___x_2123_ = lean_unsigned_to_nat(1u);
v___x_2124_ = lean_nat_sub(v_val_2120_, v___x_2123_);
lean_dec(v_val_2120_);
v_last_2125_ = lean_array_fget_borrowed(v_transitions_2116_, v___x_2124_);
lean_dec(v___x_2124_);
v_localTimeType_2126_ = lean_ctor_get(v_last_2125_, 1);
v_gmtOffset_2127_ = lean_ctor_get(v_localTimeType_2126_, 0);
v___x_2128_ = lean_nat_abs(v_gmtOffset_2127_);
v___x_2129_ = lean_nat_to_int(v___x_2128_);
v___x_2130_ = lean_int_sub(v_time_2122_, v___x_2129_);
lean_dec(v___x_2129_);
v___x_2131_ = lean_int_dec_lt(v_second_2114_, v___x_2130_);
lean_dec(v___x_2130_);
lean_dec(v_second_2114_);
if (v___x_2131_ == 0)
{
lean_inc(v_next_2121_);
v_val_2112_ = v_next_2121_;
goto v___jp_2111_;
}
else
{
lean_inc(v_last_2125_);
v_val_2112_ = v_last_2125_;
goto v___jp_2111_;
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; uint8_t v___x_2135_; 
lean_dec(v___x_2119_);
lean_dec(v_second_2114_);
v___x_2132_ = lean_array_get_size(v_transitions_2116_);
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_nat_sub(v___x_2132_, v___x_2133_);
v___x_2135_ = lean_nat_dec_lt(v___x_2134_, v___x_2132_);
if (v___x_2135_ == 0)
{
lean_dec(v___x_2134_);
lean_inc_ref(v_initialLocalTimeType_2115_);
v___y_2092_ = v_initialLocalTimeType_2115_;
goto v___jp_2091_;
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_array_fget_borrowed(v_transitions_2116_, v___x_2134_);
lean_dec(v___x_2134_);
lean_inc(v___x_2136_);
v_val_2112_ = v___x_2136_;
goto v___jp_2111_;
}
}
v___jp_2091_:
{
lean_object* v_second_2093_; lean_object* v_nano_2094_; lean_object* v_tz_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v_tm_2105_; lean_object* v___f_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; 
v_second_2093_ = lean_ctor_get(v_tm_2090_, 0);
lean_inc(v_second_2093_);
v_nano_2094_ = lean_ctor_get(v_tm_2090_, 1);
lean_inc(v_nano_2094_);
lean_dec_ref(v_tm_2090_);
v_tz_2095_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_2092_);
lean_dec_ref(v___y_2092_);
v___x_2096_ = l_Std_Time_TimeZone_toSeconds(v_tz_2095_);
v___x_2097_ = lean_int_neg(v___x_2096_);
v___x_2098_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_2099_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_2100_ = lean_int_mul(v_second_2093_, v___x_2099_);
lean_dec(v_second_2093_);
v___x_2101_ = lean_int_add(v___x_2100_, v_nano_2094_);
lean_dec(v_nano_2094_);
lean_dec(v___x_2100_);
v___x_2102_ = lean_int_mul(v___x_2097_, v___x_2099_);
lean_dec(v___x_2097_);
v___x_2103_ = lean_int_add(v___x_2102_, v___x_2098_);
lean_dec(v___x_2102_);
v___x_2104_ = lean_int_add(v___x_2101_, v___x_2103_);
lean_dec(v___x_2103_);
lean_dec(v___x_2101_);
v_tm_2105_ = l_Std_Time_Duration_ofNanoseconds(v___x_2104_);
lean_dec(v___x_2104_);
lean_inc_ref(v_tm_2105_);
v___f_2106_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2106_, 0, v_tm_2105_);
lean_closure_set(v___f_2106_, 1, v___x_2096_);
lean_closure_set(v___f_2106_, 2, v___x_2099_);
v___x_2107_ = lean_mk_thunk(v___f_2106_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 3, v_tz_2095_);
lean_ctor_set(v___x_2072_, 1, v_tm_2105_);
lean_ctor_set(v___x_2072_, 0, v___x_2107_);
v___x_2109_ = v___x_2072_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_tm_2105_);
lean_ctor_set(v_reuseFailAlloc_2110_, 2, v_rules_2070_);
lean_ctor_set(v_reuseFailAlloc_2110_, 3, v_tz_2095_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
v___jp_2111_:
{
lean_object* v_localTimeType_2113_; 
v_localTimeType_2113_ = lean_ctor_get(v_val_2112_, 1);
lean_inc_ref(v_localTimeType_2113_);
lean_dec_ref(v_val_2112_);
v___y_2092_ = v_localTimeType_2113_;
goto v___jp_2091_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withSeconds(lean_object* v_dt_2145_, lean_object* v_second_2146_){
_start:
{
lean_object* v_date_2147_; lean_object* v_rules_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2220_; 
v_date_2147_ = lean_ctor_get(v_dt_2145_, 0);
v_rules_2148_ = lean_ctor_get(v_dt_2145_, 2);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_dt_2145_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; lean_object* v_unused_2222_; 
v_unused_2221_ = lean_ctor_get(v_dt_2145_, 3);
lean_dec(v_unused_2221_);
v_unused_2222_ = lean_ctor_get(v_dt_2145_, 1);
lean_dec(v_unused_2222_);
v___x_2150_ = v_dt_2145_;
v_isShared_2151_ = v_isSharedCheck_2220_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_rules_2148_);
lean_inc(v_date_2147_);
lean_dec(v_dt_2145_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2220_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v_date_2152_; lean_object* v_time_2153_; lean_object* v_date_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2219_; 
v_date_2152_ = lean_thunk_get_own(v_date_2147_);
lean_dec_ref(v_date_2147_);
v_time_2153_ = lean_ctor_get(v_date_2152_, 1);
v_date_2154_ = lean_ctor_get(v_date_2152_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_date_2152_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2156_ = v_date_2152_;
v_isShared_2157_ = v_isSharedCheck_2219_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_time_2153_);
lean_inc(v_date_2154_);
lean_dec(v_date_2152_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2219_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v_hour_2158_; lean_object* v_minute_2159_; lean_object* v_nanosecond_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2217_; 
v_hour_2158_ = lean_ctor_get(v_time_2153_, 0);
v_minute_2159_ = lean_ctor_get(v_time_2153_, 1);
v_nanosecond_2160_ = lean_ctor_get(v_time_2153_, 3);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_time_2153_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v_time_2153_, 2);
lean_dec(v_unused_2218_);
v___x_2162_ = v_time_2153_;
v_isShared_2163_ = v_isSharedCheck_2217_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_nanosecond_2160_);
lean_inc(v_minute_2159_);
lean_inc(v_hour_2158_);
lean_dec(v_time_2153_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2217_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 2, v_second_2146_);
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_hour_2158_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_minute_2159_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_second_2146_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v_nanosecond_2160_);
v___x_2165_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
lean_object* v___x_2167_; 
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 1, v___x_2165_);
v___x_2167_ = v___x_2156_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_date_2154_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v_tm_2168_; lean_object* v___y_2170_; lean_object* v_val_2190_; lean_object* v_second_2192_; lean_object* v_initialLocalTimeType_2193_; lean_object* v_transitions_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v_tm_2168_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2167_);
v_second_2192_ = lean_ctor_get(v_tm_2168_, 0);
lean_inc(v_second_2192_);
v_initialLocalTimeType_2193_ = lean_ctor_get(v_rules_2148_, 0);
v_transitions_2194_ = lean_ctor_get(v_rules_2148_, 1);
lean_inc(v_second_2192_);
v___f_2195_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2195_, 0, v_second_2192_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_2195_, v_transitions_2194_, v___x_2196_);
if (lean_obj_tag(v___x_2197_) == 1)
{
lean_object* v_val_2198_; lean_object* v_next_2199_; lean_object* v_time_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_last_2203_; lean_object* v_localTimeType_2204_; lean_object* v_gmtOffset_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; uint8_t v___x_2209_; 
v_val_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_val_2198_);
lean_dec_ref(v___x_2197_);
v_next_2199_ = lean_array_fget_borrowed(v_transitions_2194_, v_val_2198_);
v_time_2200_ = lean_ctor_get(v_next_2199_, 0);
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_sub(v_val_2198_, v___x_2201_);
lean_dec(v_val_2198_);
v_last_2203_ = lean_array_fget_borrowed(v_transitions_2194_, v___x_2202_);
lean_dec(v___x_2202_);
v_localTimeType_2204_ = lean_ctor_get(v_last_2203_, 1);
v_gmtOffset_2205_ = lean_ctor_get(v_localTimeType_2204_, 0);
v___x_2206_ = lean_nat_abs(v_gmtOffset_2205_);
v___x_2207_ = lean_nat_to_int(v___x_2206_);
v___x_2208_ = lean_int_sub(v_time_2200_, v___x_2207_);
lean_dec(v___x_2207_);
v___x_2209_ = lean_int_dec_lt(v_second_2192_, v___x_2208_);
lean_dec(v___x_2208_);
lean_dec(v_second_2192_);
if (v___x_2209_ == 0)
{
lean_inc(v_next_2199_);
v_val_2190_ = v_next_2199_;
goto v___jp_2189_;
}
else
{
lean_inc(v_last_2203_);
v_val_2190_ = v_last_2203_;
goto v___jp_2189_;
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
lean_dec(v___x_2197_);
lean_dec(v_second_2192_);
v___x_2210_ = lean_array_get_size(v_transitions_2194_);
v___x_2211_ = lean_unsigned_to_nat(1u);
v___x_2212_ = lean_nat_sub(v___x_2210_, v___x_2211_);
v___x_2213_ = lean_nat_dec_lt(v___x_2212_, v___x_2210_);
if (v___x_2213_ == 0)
{
lean_dec(v___x_2212_);
lean_inc_ref(v_initialLocalTimeType_2193_);
v___y_2170_ = v_initialLocalTimeType_2193_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_array_fget_borrowed(v_transitions_2194_, v___x_2212_);
lean_dec(v___x_2212_);
lean_inc(v___x_2214_);
v_val_2190_ = v___x_2214_;
goto v___jp_2189_;
}
}
v___jp_2169_:
{
lean_object* v_second_2171_; lean_object* v_nano_2172_; lean_object* v_tz_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_tm_2183_; lean_object* v___f_2184_; lean_object* v___x_2185_; lean_object* v___x_2187_; 
v_second_2171_ = lean_ctor_get(v_tm_2168_, 0);
lean_inc(v_second_2171_);
v_nano_2172_ = lean_ctor_get(v_tm_2168_, 1);
lean_inc(v_nano_2172_);
lean_dec_ref(v_tm_2168_);
v_tz_2173_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_2170_);
lean_dec_ref(v___y_2170_);
v___x_2174_ = l_Std_Time_TimeZone_toSeconds(v_tz_2173_);
v___x_2175_ = lean_int_neg(v___x_2174_);
v___x_2176_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_2177_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_2178_ = lean_int_mul(v_second_2171_, v___x_2177_);
lean_dec(v_second_2171_);
v___x_2179_ = lean_int_add(v___x_2178_, v_nano_2172_);
lean_dec(v_nano_2172_);
lean_dec(v___x_2178_);
v___x_2180_ = lean_int_mul(v___x_2175_, v___x_2177_);
lean_dec(v___x_2175_);
v___x_2181_ = lean_int_add(v___x_2180_, v___x_2176_);
lean_dec(v___x_2180_);
v___x_2182_ = lean_int_add(v___x_2179_, v___x_2181_);
lean_dec(v___x_2181_);
lean_dec(v___x_2179_);
v_tm_2183_ = l_Std_Time_Duration_ofNanoseconds(v___x_2182_);
lean_dec(v___x_2182_);
lean_inc_ref(v_tm_2183_);
v___f_2184_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2184_, 0, v_tm_2183_);
lean_closure_set(v___f_2184_, 1, v___x_2174_);
lean_closure_set(v___f_2184_, 2, v___x_2177_);
v___x_2185_ = lean_mk_thunk(v___f_2184_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 3, v_tz_2173_);
lean_ctor_set(v___x_2150_, 1, v_tm_2183_);
lean_ctor_set(v___x_2150_, 0, v___x_2185_);
v___x_2187_ = v___x_2150_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2185_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_tm_2183_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_rules_2148_);
lean_ctor_set(v_reuseFailAlloc_2188_, 3, v_tz_2173_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
v___jp_2189_:
{
lean_object* v_localTimeType_2191_; 
v_localTimeType_2191_ = lean_ctor_get(v_val_2190_, 1);
lean_inc_ref(v_localTimeType_2191_);
lean_dec_ref(v_val_2190_);
v___y_2170_ = v_localTimeType_2191_;
goto v___jp_2169_;
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
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_unsigned_to_nat(1000u);
v___x_2224_ = lean_nat_to_int(v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds(lean_object* v_dt_2225_, lean_object* v_millis_2226_){
_start:
{
lean_object* v_date_2227_; lean_object* v_rules_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2305_; 
v_date_2227_ = lean_ctor_get(v_dt_2225_, 0);
v_rules_2228_ = lean_ctor_get(v_dt_2225_, 2);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_dt_2225_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; lean_object* v_unused_2307_; 
v_unused_2306_ = lean_ctor_get(v_dt_2225_, 3);
lean_dec(v_unused_2306_);
v_unused_2307_ = lean_ctor_get(v_dt_2225_, 1);
lean_dec(v_unused_2307_);
v___x_2230_ = v_dt_2225_;
v_isShared_2231_ = v_isSharedCheck_2305_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_rules_2228_);
lean_inc(v_date_2227_);
lean_dec(v_dt_2225_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2305_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v_date_2232_; lean_object* v_time_2233_; lean_object* v_date_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2304_; 
v_date_2232_ = lean_thunk_get_own(v_date_2227_);
lean_dec_ref(v_date_2227_);
v_time_2233_ = lean_ctor_get(v_date_2232_, 1);
v_date_2234_ = lean_ctor_get(v_date_2232_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_date_2232_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2236_ = v_date_2232_;
v_isShared_2237_ = v_isSharedCheck_2304_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_time_2233_);
lean_inc(v_date_2234_);
lean_dec(v_date_2232_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2304_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v_hour_2238_; lean_object* v_minute_2239_; lean_object* v_second_2240_; lean_object* v_nanosecond_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2303_; 
v_hour_2238_ = lean_ctor_get(v_time_2233_, 0);
v_minute_2239_ = lean_ctor_get(v_time_2233_, 1);
v_second_2240_ = lean_ctor_get(v_time_2233_, 2);
v_nanosecond_2241_ = lean_ctor_get(v_time_2233_, 3);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_time_2233_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2243_ = v_time_2233_;
v_isShared_2244_ = v_isSharedCheck_2303_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_nanosecond_2241_);
lean_inc(v_second_2240_);
lean_inc(v_minute_2239_);
lean_inc(v_hour_2238_);
lean_dec(v_time_2233_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2303_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2245_ = lean_obj_once(&l_Std_Time_ZonedDateTime_withMilliseconds___closed__0, &l_Std_Time_ZonedDateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_ZonedDateTime_withMilliseconds___closed__0);
v___x_2246_ = lean_int_emod(v_nanosecond_2241_, v___x_2245_);
lean_dec(v_nanosecond_2241_);
v___x_2247_ = lean_obj_once(&l_Std_Time_ZonedDateTime_millisecond___closed__0, &l_Std_Time_ZonedDateTime_millisecond___closed__0_once, _init_l_Std_Time_ZonedDateTime_millisecond___closed__0);
v___x_2248_ = lean_int_mul(v_millis_2226_, v___x_2247_);
v___x_2249_ = lean_int_add(v___x_2248_, v___x_2246_);
lean_dec(v___x_2246_);
lean_dec(v___x_2248_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 3, v___x_2249_);
v___x_2251_ = v___x_2243_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_hour_2238_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_minute_2239_);
lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_second_2240_);
lean_ctor_set(v_reuseFailAlloc_2302_, 3, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 1, v___x_2251_);
v___x_2253_ = v___x_2236_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_date_2234_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v_tm_2254_; lean_object* v___y_2256_; lean_object* v_val_2276_; lean_object* v_second_2278_; lean_object* v_initialLocalTimeType_2279_; lean_object* v_transitions_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_tm_2254_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2253_);
v_second_2278_ = lean_ctor_get(v_tm_2254_, 0);
lean_inc(v_second_2278_);
v_initialLocalTimeType_2279_ = lean_ctor_get(v_rules_2228_, 0);
v_transitions_2280_ = lean_ctor_get(v_rules_2228_, 1);
lean_inc(v_second_2278_);
v___f_2281_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2281_, 0, v_second_2278_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_2281_, v_transitions_2280_, v___x_2282_);
if (lean_obj_tag(v___x_2283_) == 1)
{
lean_object* v_val_2284_; lean_object* v_next_2285_; lean_object* v_time_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v_last_2289_; lean_object* v_localTimeType_2290_; lean_object* v_gmtOffset_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_val_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_val_2284_);
lean_dec_ref(v___x_2283_);
v_next_2285_ = lean_array_fget_borrowed(v_transitions_2280_, v_val_2284_);
v_time_2286_ = lean_ctor_get(v_next_2285_, 0);
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = lean_nat_sub(v_val_2284_, v___x_2287_);
lean_dec(v_val_2284_);
v_last_2289_ = lean_array_fget_borrowed(v_transitions_2280_, v___x_2288_);
lean_dec(v___x_2288_);
v_localTimeType_2290_ = lean_ctor_get(v_last_2289_, 1);
v_gmtOffset_2291_ = lean_ctor_get(v_localTimeType_2290_, 0);
v___x_2292_ = lean_nat_abs(v_gmtOffset_2291_);
v___x_2293_ = lean_nat_to_int(v___x_2292_);
v___x_2294_ = lean_int_sub(v_time_2286_, v___x_2293_);
lean_dec(v___x_2293_);
v___x_2295_ = lean_int_dec_lt(v_second_2278_, v___x_2294_);
lean_dec(v___x_2294_);
lean_dec(v_second_2278_);
if (v___x_2295_ == 0)
{
lean_inc(v_next_2285_);
v_val_2276_ = v_next_2285_;
goto v___jp_2275_;
}
else
{
lean_inc(v_last_2289_);
v_val_2276_ = v_last_2289_;
goto v___jp_2275_;
}
}
else
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
lean_dec(v___x_2283_);
lean_dec(v_second_2278_);
v___x_2296_ = lean_array_get_size(v_transitions_2280_);
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = lean_nat_sub(v___x_2296_, v___x_2297_);
v___x_2299_ = lean_nat_dec_lt(v___x_2298_, v___x_2296_);
if (v___x_2299_ == 0)
{
lean_dec(v___x_2298_);
lean_inc_ref(v_initialLocalTimeType_2279_);
v___y_2256_ = v_initialLocalTimeType_2279_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_array_fget_borrowed(v_transitions_2280_, v___x_2298_);
lean_dec(v___x_2298_);
lean_inc(v___x_2300_);
v_val_2276_ = v___x_2300_;
goto v___jp_2275_;
}
}
v___jp_2255_:
{
lean_object* v_second_2257_; lean_object* v_nano_2258_; lean_object* v_tz_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v_tm_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v_second_2257_ = lean_ctor_get(v_tm_2254_, 0);
lean_inc(v_second_2257_);
v_nano_2258_ = lean_ctor_get(v_tm_2254_, 1);
lean_inc(v_nano_2258_);
lean_dec_ref(v_tm_2254_);
v_tz_2259_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_2256_);
lean_dec_ref(v___y_2256_);
v___x_2260_ = l_Std_Time_TimeZone_toSeconds(v_tz_2259_);
v___x_2261_ = lean_int_neg(v___x_2260_);
v___x_2262_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_2263_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_2264_ = lean_int_mul(v_second_2257_, v___x_2263_);
lean_dec(v_second_2257_);
v___x_2265_ = lean_int_add(v___x_2264_, v_nano_2258_);
lean_dec(v_nano_2258_);
lean_dec(v___x_2264_);
v___x_2266_ = lean_int_mul(v___x_2261_, v___x_2263_);
lean_dec(v___x_2261_);
v___x_2267_ = lean_int_add(v___x_2266_, v___x_2262_);
lean_dec(v___x_2266_);
v___x_2268_ = lean_int_add(v___x_2265_, v___x_2267_);
lean_dec(v___x_2267_);
lean_dec(v___x_2265_);
v_tm_2269_ = l_Std_Time_Duration_ofNanoseconds(v___x_2268_);
lean_dec(v___x_2268_);
lean_inc_ref(v_tm_2269_);
v___f_2270_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2270_, 0, v_tm_2269_);
lean_closure_set(v___f_2270_, 1, v___x_2260_);
lean_closure_set(v___f_2270_, 2, v___x_2263_);
v___x_2271_ = lean_mk_thunk(v___f_2270_);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 3, v_tz_2259_);
lean_ctor_set(v___x_2230_, 1, v_tm_2269_);
lean_ctor_set(v___x_2230_, 0, v___x_2271_);
v___x_2273_ = v___x_2230_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_tm_2269_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_rules_2228_);
lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_tz_2259_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
v___jp_2275_:
{
lean_object* v_localTimeType_2277_; 
v_localTimeType_2277_ = lean_ctor_get(v_val_2276_, 1);
lean_inc_ref(v_localTimeType_2277_);
lean_dec_ref(v_val_2276_);
v___y_2256_ = v_localTimeType_2277_;
goto v___jp_2255_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withMilliseconds___boxed(lean_object* v_dt_2308_, lean_object* v_millis_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Std_Time_ZonedDateTime_withMilliseconds(v_dt_2308_, v_millis_2309_);
lean_dec(v_millis_2309_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_withNanoseconds(lean_object* v_dt_2311_, lean_object* v_nano_2312_){
_start:
{
lean_object* v_date_2313_; lean_object* v_rules_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2386_; 
v_date_2313_ = lean_ctor_get(v_dt_2311_, 0);
v_rules_2314_ = lean_ctor_get(v_dt_2311_, 2);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_dt_2311_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; lean_object* v_unused_2388_; 
v_unused_2387_ = lean_ctor_get(v_dt_2311_, 3);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_dt_2311_, 1);
lean_dec(v_unused_2388_);
v___x_2316_ = v_dt_2311_;
v_isShared_2317_ = v_isSharedCheck_2386_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_rules_2314_);
lean_inc(v_date_2313_);
lean_dec(v_dt_2311_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2386_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v_date_2318_; lean_object* v_time_2319_; lean_object* v_date_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2385_; 
v_date_2318_ = lean_thunk_get_own(v_date_2313_);
lean_dec_ref(v_date_2313_);
v_time_2319_ = lean_ctor_get(v_date_2318_, 1);
v_date_2320_ = lean_ctor_get(v_date_2318_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_date_2318_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2322_ = v_date_2318_;
v_isShared_2323_ = v_isSharedCheck_2385_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_time_2319_);
lean_inc(v_date_2320_);
lean_dec(v_date_2318_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2385_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v_hour_2324_; lean_object* v_minute_2325_; lean_object* v_second_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2383_; 
v_hour_2324_ = lean_ctor_get(v_time_2319_, 0);
v_minute_2325_ = lean_ctor_get(v_time_2319_, 1);
v_second_2326_ = lean_ctor_get(v_time_2319_, 2);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_time_2319_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; 
v_unused_2384_ = lean_ctor_get(v_time_2319_, 3);
lean_dec(v_unused_2384_);
v___x_2328_ = v_time_2319_;
v_isShared_2329_ = v_isSharedCheck_2383_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_second_2326_);
lean_inc(v_minute_2325_);
lean_inc(v_hour_2324_);
lean_dec(v_time_2319_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2383_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 3, v_nano_2312_);
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_hour_2324_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_minute_2325_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v_second_2326_);
lean_ctor_set(v_reuseFailAlloc_2382_, 3, v_nano_2312_);
v___x_2331_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 1, v___x_2331_);
v___x_2333_ = v___x_2322_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_date_2320_);
lean_ctor_set(v_reuseFailAlloc_2381_, 1, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v_tm_2334_; lean_object* v___y_2336_; lean_object* v_val_2356_; lean_object* v_second_2358_; lean_object* v_initialLocalTimeType_2359_; lean_object* v_transitions_2360_; lean_object* v___f_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_tm_2334_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2333_);
v_second_2358_ = lean_ctor_get(v_tm_2334_, 0);
lean_inc(v_second_2358_);
v_initialLocalTimeType_2359_ = lean_ctor_get(v_rules_2314_, 0);
v_transitions_2360_ = lean_ctor_get(v_rules_2314_, 1);
lean_inc(v_second_2358_);
v___f_2361_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2361_, 0, v_second_2358_);
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_2361_, v_transitions_2360_, v___x_2362_);
if (lean_obj_tag(v___x_2363_) == 1)
{
lean_object* v_val_2364_; lean_object* v_next_2365_; lean_object* v_time_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v_last_2369_; lean_object* v_localTimeType_2370_; lean_object* v_gmtOffset_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; uint8_t v___x_2375_; 
v_val_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_val_2364_);
lean_dec_ref(v___x_2363_);
v_next_2365_ = lean_array_fget_borrowed(v_transitions_2360_, v_val_2364_);
v_time_2366_ = lean_ctor_get(v_next_2365_, 0);
v___x_2367_ = lean_unsigned_to_nat(1u);
v___x_2368_ = lean_nat_sub(v_val_2364_, v___x_2367_);
lean_dec(v_val_2364_);
v_last_2369_ = lean_array_fget_borrowed(v_transitions_2360_, v___x_2368_);
lean_dec(v___x_2368_);
v_localTimeType_2370_ = lean_ctor_get(v_last_2369_, 1);
v_gmtOffset_2371_ = lean_ctor_get(v_localTimeType_2370_, 0);
v___x_2372_ = lean_nat_abs(v_gmtOffset_2371_);
v___x_2373_ = lean_nat_to_int(v___x_2372_);
v___x_2374_ = lean_int_sub(v_time_2366_, v___x_2373_);
lean_dec(v___x_2373_);
v___x_2375_ = lean_int_dec_lt(v_second_2358_, v___x_2374_);
lean_dec(v___x_2374_);
lean_dec(v_second_2358_);
if (v___x_2375_ == 0)
{
lean_inc(v_next_2365_);
v_val_2356_ = v_next_2365_;
goto v___jp_2355_;
}
else
{
lean_inc(v_last_2369_);
v_val_2356_ = v_last_2369_;
goto v___jp_2355_;
}
}
else
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; uint8_t v___x_2379_; 
lean_dec(v___x_2363_);
lean_dec(v_second_2358_);
v___x_2376_ = lean_array_get_size(v_transitions_2360_);
v___x_2377_ = lean_unsigned_to_nat(1u);
v___x_2378_ = lean_nat_sub(v___x_2376_, v___x_2377_);
v___x_2379_ = lean_nat_dec_lt(v___x_2378_, v___x_2376_);
if (v___x_2379_ == 0)
{
lean_dec(v___x_2378_);
lean_inc_ref(v_initialLocalTimeType_2359_);
v___y_2336_ = v_initialLocalTimeType_2359_;
goto v___jp_2335_;
}
else
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_array_fget_borrowed(v_transitions_2360_, v___x_2378_);
lean_dec(v___x_2378_);
lean_inc(v___x_2380_);
v_val_2356_ = v___x_2380_;
goto v___jp_2355_;
}
}
v___jp_2335_:
{
lean_object* v_second_2337_; lean_object* v_nano_2338_; lean_object* v_tz_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v_tm_2349_; lean_object* v___f_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v_second_2337_ = lean_ctor_get(v_tm_2334_, 0);
lean_inc(v_second_2337_);
v_nano_2338_ = lean_ctor_get(v_tm_2334_, 1);
lean_inc(v_nano_2338_);
lean_dec_ref(v_tm_2334_);
v_tz_2339_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_2336_);
lean_dec_ref(v___y_2336_);
v___x_2340_ = l_Std_Time_TimeZone_toSeconds(v_tz_2339_);
v___x_2341_ = lean_int_neg(v___x_2340_);
v___x_2342_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_2343_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_2344_ = lean_int_mul(v_second_2337_, v___x_2343_);
lean_dec(v_second_2337_);
v___x_2345_ = lean_int_add(v___x_2344_, v_nano_2338_);
lean_dec(v_nano_2338_);
lean_dec(v___x_2344_);
v___x_2346_ = lean_int_mul(v___x_2341_, v___x_2343_);
lean_dec(v___x_2341_);
v___x_2347_ = lean_int_add(v___x_2346_, v___x_2342_);
lean_dec(v___x_2346_);
v___x_2348_ = lean_int_add(v___x_2345_, v___x_2347_);
lean_dec(v___x_2347_);
lean_dec(v___x_2345_);
v_tm_2349_ = l_Std_Time_Duration_ofNanoseconds(v___x_2348_);
lean_dec(v___x_2348_);
lean_inc_ref(v_tm_2349_);
v___f_2350_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2350_, 0, v_tm_2349_);
lean_closure_set(v___f_2350_, 1, v___x_2340_);
lean_closure_set(v___f_2350_, 2, v___x_2343_);
v___x_2351_ = lean_mk_thunk(v___f_2350_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 3, v_tz_2339_);
lean_ctor_set(v___x_2316_, 1, v_tm_2349_);
lean_ctor_set(v___x_2316_, 0, v___x_2351_);
v___x_2353_ = v___x_2316_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v_tm_2349_);
lean_ctor_set(v_reuseFailAlloc_2354_, 2, v_rules_2314_);
lean_ctor_set(v_reuseFailAlloc_2354_, 3, v_tz_2339_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
v___jp_2355_:
{
lean_object* v_localTimeType_2357_; 
v_localTimeType_2357_ = lean_ctor_get(v_val_2356_, 1);
lean_inc_ref(v_localTimeType_2357_);
lean_dec_ref(v_val_2356_);
v___y_2336_ = v_localTimeType_2357_;
goto v___jp_2335_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Time_ZonedDateTime_inLeapYear(lean_object* v_date_2389_){
_start:
{
lean_object* v_date_2390_; lean_object* v___x_2391_; lean_object* v_date_2392_; lean_object* v_year_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2401_; 
v_date_2390_ = lean_ctor_get(v_date_2389_, 0);
v___x_2391_ = lean_thunk_get_own(v_date_2390_);
v_date_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc_ref(v_date_2392_);
lean_dec(v___x_2391_);
v_year_2393_ = lean_ctor_get(v_date_2392_, 0);
lean_inc(v_year_2393_);
lean_dec_ref(v_date_2392_);
v___x_2394_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__0, &l_Std_Time_ZonedDateTime_dayOfYear___closed__0_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__0);
v___x_2395_ = lean_int_mod(v_year_2393_, v___x_2394_);
v___x_2396_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__0);
v___x_2401_ = lean_int_dec_eq(v___x_2395_, v___x_2396_);
lean_dec(v___x_2395_);
if (v___x_2401_ == 0)
{
lean_dec(v_year_2393_);
return v___x_2401_;
}
else
{
lean_object* v___x_2402_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2402_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__2, &l_Std_Time_ZonedDateTime_dayOfYear___closed__2_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__2);
v___x_2403_ = lean_int_mod(v_year_2393_, v___x_2402_);
v___x_2404_ = lean_int_dec_eq(v___x_2403_, v___x_2396_);
lean_dec(v___x_2403_);
if (v___x_2404_ == 0)
{
if (v___x_2401_ == 0)
{
goto v___jp_2397_;
}
else
{
lean_dec(v_year_2393_);
return v___x_2401_;
}
}
else
{
goto v___jp_2397_;
}
}
v___jp_2397_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v___x_2398_ = lean_obj_once(&l_Std_Time_ZonedDateTime_dayOfYear___closed__1, &l_Std_Time_ZonedDateTime_dayOfYear___closed__1_once, _init_l_Std_Time_ZonedDateTime_dayOfYear___closed__1);
v___x_2399_ = lean_int_mod(v_year_2393_, v___x_2398_);
lean_dec(v_year_2393_);
v___x_2400_ = lean_int_dec_eq(v___x_2399_, v___x_2396_);
lean_dec(v___x_2399_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_inLeapYear___boxed(lean_object* v_date_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Std_Time_ZonedDateTime_inLeapYear(v_date_2405_);
lean_dec_ref(v_date_2405_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDaysSinceUNIXEpoch(lean_object* v_date_2408_){
_start:
{
lean_object* v_date_2409_; lean_object* v___x_2410_; lean_object* v_date_2411_; lean_object* v___x_2412_; 
v_date_2409_ = lean_ctor_get(v_date_2408_, 0);
v___x_2410_ = lean_thunk_get_own(v_date_2409_);
v_date_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc_ref(v_date_2411_);
lean_dec(v___x_2410_);
v___x_2412_ = l_Std_Time_PlainDate_toDaysSinceUNIXEpoch(v_date_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDaysSinceUNIXEpoch___boxed(lean_object* v_date_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Std_Time_ZonedDateTime_toDaysSinceUNIXEpoch(v_date_2413_);
lean_dec_ref(v_date_2413_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofDaysSinceUNIXEpoch(lean_object* v_days_2415_, lean_object* v_time_2416_, lean_object* v_zt_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_tm_2420_; lean_object* v___y_2422_; lean_object* v_val_2440_; lean_object* v_second_2442_; lean_object* v_initialLocalTimeType_2443_; lean_object* v_transitions_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2418_ = l_Std_Time_PlainDate_ofDaysSinceUNIXEpoch(v_days_2415_);
v___x_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v_time_2416_);
v_tm_2420_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_2419_);
v_second_2442_ = lean_ctor_get(v_tm_2420_, 0);
lean_inc(v_second_2442_);
v_initialLocalTimeType_2443_ = lean_ctor_get(v_zt_2417_, 0);
v_transitions_2444_ = lean_ctor_get(v_zt_2417_, 1);
lean_inc(v_second_2442_);
v___f_2445_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__1___boxed), 2, 1);
lean_closure_set(v___f_2445_, 0, v_second_2442_);
v___x_2446_ = lean_unsigned_to_nat(0u);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_findFinIdx_x3f_loop(lean_box(0), v___f_2445_, v_transitions_2444_, v___x_2446_);
if (lean_obj_tag(v___x_2447_) == 1)
{
lean_object* v_val_2448_; lean_object* v_next_2449_; lean_object* v_time_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v_last_2453_; lean_object* v_localTimeType_2454_; lean_object* v_gmtOffset_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; uint8_t v___x_2459_; 
v_val_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_val_2448_);
lean_dec_ref(v___x_2447_);
v_next_2449_ = lean_array_fget_borrowed(v_transitions_2444_, v_val_2448_);
v_time_2450_ = lean_ctor_get(v_next_2449_, 0);
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = lean_nat_sub(v_val_2448_, v___x_2451_);
lean_dec(v_val_2448_);
v_last_2453_ = lean_array_fget_borrowed(v_transitions_2444_, v___x_2452_);
lean_dec(v___x_2452_);
v_localTimeType_2454_ = lean_ctor_get(v_last_2453_, 1);
v_gmtOffset_2455_ = lean_ctor_get(v_localTimeType_2454_, 0);
v___x_2456_ = lean_nat_abs(v_gmtOffset_2455_);
v___x_2457_ = lean_nat_to_int(v___x_2456_);
v___x_2458_ = lean_int_sub(v_time_2450_, v___x_2457_);
lean_dec(v___x_2457_);
v___x_2459_ = lean_int_dec_lt(v_second_2442_, v___x_2458_);
lean_dec(v___x_2458_);
lean_dec(v_second_2442_);
if (v___x_2459_ == 0)
{
lean_inc(v_next_2449_);
v_val_2440_ = v_next_2449_;
goto v___jp_2439_;
}
else
{
lean_inc(v_last_2453_);
v_val_2440_ = v_last_2453_;
goto v___jp_2439_;
}
}
else
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; 
lean_dec(v___x_2447_);
lean_dec(v_second_2442_);
v___x_2460_ = lean_array_get_size(v_transitions_2444_);
v___x_2461_ = lean_unsigned_to_nat(1u);
v___x_2462_ = lean_nat_sub(v___x_2460_, v___x_2461_);
v___x_2463_ = lean_nat_dec_lt(v___x_2462_, v___x_2460_);
if (v___x_2463_ == 0)
{
lean_dec(v___x_2462_);
lean_inc_ref(v_initialLocalTimeType_2443_);
v___y_2422_ = v_initialLocalTimeType_2443_;
goto v___jp_2421_;
}
else
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_array_fget_borrowed(v_transitions_2444_, v___x_2462_);
lean_dec(v___x_2462_);
lean_inc(v___x_2464_);
v_val_2440_ = v___x_2464_;
goto v___jp_2439_;
}
}
v___jp_2421_:
{
lean_object* v_second_2423_; lean_object* v_nano_2424_; lean_object* v_tz_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v_tm_2435_; lean_object* v___f_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_second_2423_ = lean_ctor_get(v_tm_2420_, 0);
lean_inc(v_second_2423_);
v_nano_2424_ = lean_ctor_get(v_tm_2420_, 1);
lean_inc(v_nano_2424_);
lean_dec_ref(v_tm_2420_);
v_tz_2425_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v___y_2422_);
lean_dec_ref(v___y_2422_);
v___x_2426_ = l_Std_Time_TimeZone_toSeconds(v_tz_2425_);
v___x_2427_ = lean_int_neg(v___x_2426_);
v___x_2428_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1, &l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1_once, _init_l_Std_Time_ZonedDateTime_ofPlainDateTime___closed__1);
v___x_2429_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_2430_ = lean_int_mul(v_second_2423_, v___x_2429_);
lean_dec(v_second_2423_);
v___x_2431_ = lean_int_add(v___x_2430_, v_nano_2424_);
lean_dec(v_nano_2424_);
lean_dec(v___x_2430_);
v___x_2432_ = lean_int_mul(v___x_2427_, v___x_2429_);
lean_dec(v___x_2427_);
v___x_2433_ = lean_int_add(v___x_2432_, v___x_2428_);
lean_dec(v___x_2432_);
v___x_2434_ = lean_int_add(v___x_2431_, v___x_2433_);
lean_dec(v___x_2433_);
lean_dec(v___x_2431_);
v_tm_2435_ = l_Std_Time_Duration_ofNanoseconds(v___x_2434_);
lean_dec(v___x_2434_);
lean_inc_ref(v_tm_2435_);
v___f_2436_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_ofPlainDateTime___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2436_, 0, v_tm_2435_);
lean_closure_set(v___f_2436_, 1, v___x_2426_);
lean_closure_set(v___f_2436_, 2, v___x_2429_);
v___x_2437_ = lean_mk_thunk(v___f_2436_);
v___x_2438_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
lean_ctor_set(v___x_2438_, 1, v_tm_2435_);
lean_ctor_set(v___x_2438_, 2, v_zt_2417_);
lean_ctor_set(v___x_2438_, 3, v_tz_2425_);
return v___x_2438_;
}
v___jp_2439_:
{
lean_object* v_localTimeType_2441_; 
v_localTimeType_2441_ = lean_ctor_get(v_val_2440_, 1);
lean_inc_ref(v_localTimeType_2441_);
lean_dec_ref(v_val_2440_);
v___y_2422_ = v_localTimeType_2441_;
goto v___jp_2421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_ofDaysSinceUNIXEpoch___boxed(lean_object* v_days_2465_, lean_object* v_time_2466_, lean_object* v_zt_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Std_Time_ZonedDateTime_ofDaysSinceUNIXEpoch(v_days_2465_, v_time_2466_, v_zt_2467_);
lean_dec(v_days_2465_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(lean_object* v_x_2497_, lean_object* v_y_2498_){
_start:
{
lean_object* v_timestamp_2499_; lean_object* v_timestamp_2500_; lean_object* v_second_2501_; lean_object* v_nano_2502_; lean_object* v_second_2503_; lean_object* v_nano_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_timestamp_2499_ = lean_ctor_get(v_y_2498_, 1);
v_timestamp_2500_ = lean_ctor_get(v_x_2497_, 1);
v_second_2501_ = lean_ctor_get(v_timestamp_2499_, 0);
v_nano_2502_ = lean_ctor_get(v_timestamp_2499_, 1);
v_second_2503_ = lean_ctor_get(v_timestamp_2500_, 0);
v_nano_2504_ = lean_ctor_get(v_timestamp_2500_, 1);
v___x_2505_ = lean_int_neg(v_second_2501_);
v___x_2506_ = lean_int_neg(v_nano_2502_);
v___x_2507_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_2508_ = lean_int_mul(v_second_2503_, v___x_2507_);
v___x_2509_ = lean_int_add(v___x_2508_, v_nano_2504_);
lean_dec(v___x_2508_);
v___x_2510_ = lean_int_mul(v___x_2505_, v___x_2507_);
lean_dec(v___x_2505_);
v___x_2511_ = lean_int_add(v___x_2510_, v___x_2506_);
lean_dec(v___x_2506_);
lean_dec(v___x_2510_);
v___x_2512_ = lean_int_add(v___x_2509_, v___x_2511_);
lean_dec(v___x_2511_);
lean_dec(v___x_2509_);
v___x_2513_ = l_Std_Time_Duration_ofNanoseconds(v___x_2512_);
lean_dec(v___x_2512_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration___lam__0___boxed(lean_object* v_x_2514_, lean_object* v_y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Std_Time_ZonedDateTime_instHSubDuration___lam__0(v_x_2514_, v_y_2515_);
lean_dec_ref(v_y_2515_);
lean_dec_ref(v_x_2514_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(lean_object* v_x_2519_, lean_object* v_y_2520_){
_start:
{
lean_object* v_second_2521_; lean_object* v_nano_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v_nanos_2525_; lean_object* v___x_2526_; 
v_second_2521_ = lean_ctor_get(v_y_2520_, 0);
v_nano_2522_ = lean_ctor_get(v_y_2520_, 1);
v___x_2523_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_2524_ = lean_int_mul(v_second_2521_, v___x_2523_);
v_nanos_2525_ = lean_int_add(v___x_2524_, v_nano_2522_);
lean_dec(v___x_2524_);
v___x_2526_ = l_Std_Time_ZonedDateTime_addNanoseconds(v_x_2519_, v_nanos_2525_);
lean_dec(v_nanos_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_2527_, lean_object* v_y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Std_Time_ZonedDateTime_instHAddDuration___lam__0(v_x_2527_, v_y_2528_);
lean_dec_ref(v_y_2528_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(lean_object* v_x_2532_, lean_object* v_y_2533_){
_start:
{
lean_object* v_second_2534_; lean_object* v_nano_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v_nanos_2538_; lean_object* v___x_2539_; 
v_second_2534_ = lean_ctor_get(v_y_2533_, 0);
v_nano_2535_ = lean_ctor_get(v_y_2533_, 1);
v___x_2536_ = lean_obj_once(&l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_ofTimestamp___lam__0___closed__0);
v___x_2537_ = lean_int_mul(v_second_2534_, v___x_2536_);
v_nanos_2538_ = lean_int_add(v___x_2537_, v_nano_2535_);
lean_dec(v___x_2537_);
v___x_2539_ = l_Std_Time_ZonedDateTime_subNanoseconds(v_x_2532_, v_nanos_2538_);
lean_dec(v_nanos_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0___boxed(lean_object* v_x_2540_, lean_object* v_y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Std_Time_ZonedDateTime_instHSubDuration__1___lam__0(v_x_2540_, v_y_2541_);
lean_dec_ref(v_y_2541_);
return v_res_2542_;
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

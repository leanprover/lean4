// Lean compiler output
// Module: Std.Time.DateTime
// Imports: public import Std.Time.Zoned.ZoneRules public import Std.Time.DateTime.PlainDateTime
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
lean_object* l_Std_Time_TimeZone_Transition_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
extern lean_object* l_Std_Time_instInhabitedPlainDateTime_default;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
lean_object* l_Std_Time_PlainDate_ofEpochDay(lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsClip(lean_object*, lean_object*);
extern lean_object* l_Std_Time_instInhabitedTimeZone_default;
extern lean_object* l_Std_Time_TimeZone_instInhabitedZoneRules_default;
extern lean_object* l_Std_Time_instInhabitedTimestamp_default;
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDateTime_withWeekday(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDateTime_addMonthsRollOver(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime___private__1___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_instInhabitedDateTime___private__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instInhabitedDateTime___private__1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instInhabitedDateTime___private__1___closed__0 = (const lean_object*)&l_Std_Time_instInhabitedDateTime___private__1___closed__0_value;
static lean_once_cell_t l_Std_Time_instInhabitedDateTime___private__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedDateTime___private__1___closed__1;
static lean_once_cell_t l_Std_Time_instInhabitedDateTime___private__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedDateTime___private__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime___private__1;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime;
static lean_once_cell_t l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0;
static lean_once_cell_t l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_ofPlainDateTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_ofPlainDateTime___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Time_DateTime_ofTimestampWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_DateTime_ofTimestampWithZone___closed__0 = (const lean_object*)&l_Std_Time_DateTime_ofTimestampWithZone___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertZoneRules___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertZoneRules___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertZoneRules(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_millisecond___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_millisecond___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_offset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_offset___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_dayOfYear___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_dayOfYear___closed__0;
static lean_once_cell_t l_Std_Time_DateTime_dayOfYear___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_dayOfYear___closed__1;
static lean_once_cell_t l_Std_Time_DateTime_dayOfYear___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_dayOfYear___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_DateTime_addDays_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_DateTime_addDays_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_DateTime_addDays_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addYearsRollOver___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addYearsRollOver___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_addMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_addMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_withMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_withMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_DateTime_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_addDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHAddOffset = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_subDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHSubOffset = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHAddOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_addWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHAddOffset__1___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHAddOffset__1 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHSubOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_subWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubOffset__1___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHSubOffset__1 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHAddOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_addHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHAddOffset__2___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHAddOffset__2 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHSubOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_subHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubOffset__2___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHSubOffset__2 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHAddOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_addMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHAddOffset__3___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHAddOffset__3 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHSubOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_subMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubOffset__3___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHSubOffset__3 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHAddOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_addSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHAddOffset__4___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHAddOffset__4 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHSubOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_subSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubOffset__4___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHSubOffset__4 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHAddOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_addMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHAddOffset__5___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHAddOffset__5 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHSubOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_subMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubOffset__5___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHSubOffset__5 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHAddOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_addNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHAddOffset__6___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHAddOffset__6 = (const lean_object*)&l_Std_Time_DateTime_instHAddOffset__6___closed__0_value;
static const lean_closure_object l_Std_Time_DateTime_instHSubOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_subNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubOffset__6___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHSubOffset__6 = (const lean_object*)&l_Std_Time_DateTime_instHSubOffset__6___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_DateTime_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_instHSubDuration___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHSubDuration = (const lean_object*)&l_Std_Time_DateTime_instHSubDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_DateTime_instHAddDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_instHAddDuration___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHAddDuration___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHAddDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHAddDuration = (const lean_object*)&l_Std_Time_DateTime_instHAddDuration___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_DateTime_instHSubDuration__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_instHSubDuration__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instHSubDuration__1___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instHSubDuration__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instHSubDuration__1 = (const lean_object*)&l_Std_Time_DateTime_instHSubDuration__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedDateTime___private__1___lam__0(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = l_Std_Time_instInhabitedPlainDateTime_default;
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___private__1___closed__1(void){
_start:
{
lean_object* v___f_4_; lean_object* v___x_5_; 
v___f_4_ = ((lean_object*)(l_Std_Time_instInhabitedDateTime___private__1___closed__0));
v___x_5_ = lean_mk_thunk(v___f_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___private__1___closed__2(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_6_ = l_Std_Time_instInhabitedTimeZone_default;
v___x_7_ = l_Std_Time_TimeZone_instInhabitedZoneRules_default;
v___x_8_ = l_Std_Time_instInhabitedTimestamp_default;
v___x_9_ = lean_obj_once(&l_Std_Time_instInhabitedDateTime___private__1___closed__1, &l_Std_Time_instInhabitedDateTime___private__1___closed__1_once, _init_l_Std_Time_instInhabitedDateTime___private__1___closed__1);
v___x_10_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_7_);
lean_ctor_set(v___x_10_, 3, v___x_6_);
return v___x_10_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime___private__1(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Std_Time_instInhabitedDateTime___private__1___closed__2, &l_Std_Time_instInhabitedDateTime___private__1___closed__2_once, _init_l_Std_Time_instInhabitedDateTime___private__1___closed__2);
return v___x_11_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedDateTime(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Std_Time_instInhabitedDateTime___private__1___closed__2, &l_Std_Time_instInhabitedDateTime___private__1___closed__2_once, _init_l_Std_Time_instInhabitedDateTime___private__1___closed__2);
return v___x_12_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_nat_to_int(v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(1000000000u);
v___x_16_ = lean_nat_to_int(v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object* v___y_17_, lean_object* v_tm_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_offset_20_; lean_object* v_second_21_; lean_object* v_nano_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_offset_20_ = lean_ctor_get(v___y_17_, 0);
v_second_21_ = lean_ctor_get(v_tm_18_, 0);
v_nano_22_ = lean_ctor_get(v_tm_18_, 1);
v___x_23_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_24_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object* v___y_32_, lean_object* v_tm_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Time_DateTime_ofTimestamp___lam__0(v___y_32_, v_tm_33_, v_x_34_);
lean_dec_ref(v_tm_33_);
lean_dec_ref(v___y_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object* v_tm_36_, lean_object* v_rules_37_){
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
v___f_40_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestamp___lam__0___boxed), 3, 2);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object* v_pdt_48_, lean_object* v_x_49_){
_start:
{
lean_inc_ref(v_pdt_48_);
return v_pdt_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(lean_object* v_pdt_50_, lean_object* v_x_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_Time_DateTime_ofPlainDateTime___lam__0(v_pdt_50_, v_x_51_);
lean_dec_ref(v_pdt_50_);
return v_res_52_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_54_ = lean_int_neg(v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object* v_pdt_55_, lean_object* v_zr_56_){
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
v___f_63_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed), 2, 1);
lean_closure_set(v___f_63_, 0, v_pdt_55_);
v___x_64_ = lean_mk_thunk(v___f_63_);
v___x_65_ = lean_int_neg(v_offset_60_);
lean_dec(v_offset_60_);
v___x_66_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_67_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone___lam__0(lean_object* v___y_75_, lean_object* v_tm_76_, lean_object* v___x_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_offset_79_; lean_object* v_second_80_; lean_object* v_nano_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_offset_79_ = lean_ctor_get(v___y_75_, 0);
v_second_80_ = lean_ctor_get(v_tm_76_, 0);
v_nano_81_ = lean_ctor_get(v_tm_76_, 1);
v___x_82_ = lean_nat_to_int(v___x_77_);
v___x_83_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone___lam__0___boxed(lean_object* v___y_91_, lean_object* v_tm_92_, lean_object* v___x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_Time_DateTime_ofTimestampWithZone___lam__0(v___y_91_, v_tm_92_, v___x_93_, v_x_94_);
lean_dec_ref(v_tm_92_);
lean_dec_ref(v___y_91_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone(lean_object* v_tm_98_, lean_object* v_tz_99_){
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
v___x_108_ = ((lean_object*)(l_Std_Time_DateTime_ofTimestampWithZone___closed__0));
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
v___f_112_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestampWithZone___lam__0___boxed), 4, 3);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone___boxed(lean_object* v_tm_118_, lean_object* v_tz_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Time_DateTime_ofTimestampWithZone(v_tm_118_, v_tz_119_);
lean_dec_ref(v_tz_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0(lean_object* v_tm_121_, lean_object* v_x_122_){
_start:
{
lean_inc_ref(v_tm_121_);
return v_tm_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0___boxed(lean_object* v_tm_123_, lean_object* v_x_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0(v_tm_123_, v_x_124_);
lean_dec_ref(v_tm_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone(lean_object* v_tm_126_, lean_object* v_tz_127_){
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
v___x_135_ = ((lean_object*)(l_Std_Time_DateTime_ofTimestampWithZone___closed__0));
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
v___f_143_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0___boxed), 2, 1);
lean_closure_set(v___f_143_, 0, v_tm_126_);
v___x_144_ = lean_mk_thunk(v___f_143_);
v___x_145_ = lean_int_neg(v_offset_140_);
lean_dec(v_offset_140_);
v___x_146_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_147_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone___boxed(lean_object* v_tm_155_, lean_object* v_tz_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Time_DateTime_ofPlainDateTimeWithZone(v_tm_155_, v_tz_156_);
lean_dec_ref(v_tz_156_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object* v_date_158_){
_start:
{
lean_object* v_timestamp_159_; 
v_timestamp_159_ = lean_ctor_get(v_date_158_, 1);
lean_inc_ref(v_timestamp_159_);
return v_timestamp_159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object* v_date_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Time_DateTime_toTimestamp(v_date_160_);
lean_dec_ref(v_date_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertZoneRules___lam__0(lean_object* v___y_162_, lean_object* v_timestamp_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_offset_165_; lean_object* v_second_166_; lean_object* v_nano_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_offset_165_ = lean_ctor_get(v___y_162_, 0);
v_second_166_ = lean_ctor_get(v_timestamp_163_, 0);
v_nano_167_ = lean_ctor_get(v_timestamp_163_, 1);
v___x_168_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_169_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertZoneRules___lam__0___boxed(lean_object* v___y_177_, lean_object* v_timestamp_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Time_DateTime_convertZoneRules___lam__0(v___y_177_, v_timestamp_178_, v_x_179_);
lean_dec_ref(v_timestamp_178_);
lean_dec_ref(v___y_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertZoneRules(lean_object* v_date_181_, lean_object* v_tz_u2081_182_){
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
v___f_189_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertZoneRules___lam__0___boxed), 3, 2);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object* v_dt_203_){
_start:
{
lean_object* v_date_204_; lean_object* v___x_205_; 
v_date_204_ = lean_ctor_get(v_dt_203_, 0);
v___x_205_ = lean_thunk_get_own(v_date_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object* v_dt_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Time_DateTime_toPlainDateTime(v_dt_206_);
lean_dec_ref(v_dt_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object* v_zdt_208_){
_start:
{
lean_object* v_date_209_; lean_object* v___x_210_; lean_object* v_time_211_; 
v_date_209_ = lean_ctor_get(v_zdt_208_, 0);
v___x_210_ = lean_thunk_get_own(v_date_209_);
v_time_211_ = lean_ctor_get(v___x_210_, 1);
lean_inc_ref(v_time_211_);
lean_dec(v___x_210_);
return v_time_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object* v_zdt_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Time_DateTime_time(v_zdt_212_);
lean_dec_ref(v_zdt_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object* v_zdt_214_){
_start:
{
lean_object* v_date_215_; lean_object* v___x_216_; lean_object* v_date_217_; lean_object* v_year_218_; 
v_date_215_ = lean_ctor_get(v_zdt_214_, 0);
v___x_216_ = lean_thunk_get_own(v_date_215_);
v_date_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc_ref(v_date_217_);
lean_dec(v___x_216_);
v_year_218_ = lean_ctor_get(v_date_217_, 0);
lean_inc(v_year_218_);
lean_dec_ref(v_date_217_);
return v_year_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object* v_zdt_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Time_DateTime_year(v_zdt_219_);
lean_dec_ref(v_zdt_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object* v_zdt_221_){
_start:
{
lean_object* v_date_222_; lean_object* v___x_223_; lean_object* v_date_224_; lean_object* v_month_225_; 
v_date_222_ = lean_ctor_get(v_zdt_221_, 0);
v___x_223_ = lean_thunk_get_own(v_date_222_);
v_date_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc_ref(v_date_224_);
lean_dec(v___x_223_);
v_month_225_ = lean_ctor_get(v_date_224_, 1);
lean_inc(v_month_225_);
lean_dec_ref(v_date_224_);
return v_month_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object* v_zdt_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_Time_DateTime_month(v_zdt_226_);
lean_dec_ref(v_zdt_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object* v_zdt_228_){
_start:
{
lean_object* v_date_229_; lean_object* v___x_230_; lean_object* v_date_231_; lean_object* v_day_232_; 
v_date_229_ = lean_ctor_get(v_zdt_228_, 0);
v___x_230_ = lean_thunk_get_own(v_date_229_);
v_date_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref(v_date_231_);
lean_dec(v___x_230_);
v_day_232_ = lean_ctor_get(v_date_231_, 2);
lean_inc(v_day_232_);
lean_dec_ref(v_date_231_);
return v_day_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object* v_zdt_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_Time_DateTime_day(v_zdt_233_);
lean_dec_ref(v_zdt_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object* v_zdt_235_){
_start:
{
lean_object* v_date_236_; lean_object* v___x_237_; lean_object* v_time_238_; lean_object* v_hour_239_; 
v_date_236_ = lean_ctor_get(v_zdt_235_, 0);
v___x_237_ = lean_thunk_get_own(v_date_236_);
v_time_238_ = lean_ctor_get(v___x_237_, 1);
lean_inc_ref(v_time_238_);
lean_dec(v___x_237_);
v_hour_239_ = lean_ctor_get(v_time_238_, 0);
lean_inc(v_hour_239_);
lean_dec_ref(v_time_238_);
return v_hour_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object* v_zdt_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_Time_DateTime_hour(v_zdt_240_);
lean_dec_ref(v_zdt_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object* v_zdt_242_){
_start:
{
lean_object* v_date_243_; lean_object* v___x_244_; lean_object* v_time_245_; lean_object* v_minute_246_; 
v_date_243_ = lean_ctor_get(v_zdt_242_, 0);
v___x_244_ = lean_thunk_get_own(v_date_243_);
v_time_245_ = lean_ctor_get(v___x_244_, 1);
lean_inc_ref(v_time_245_);
lean_dec(v___x_244_);
v_minute_246_ = lean_ctor_get(v_time_245_, 1);
lean_inc(v_minute_246_);
lean_dec_ref(v_time_245_);
return v_minute_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object* v_zdt_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_Time_DateTime_minute(v_zdt_247_);
lean_dec_ref(v_zdt_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object* v_zdt_249_){
_start:
{
lean_object* v_date_250_; lean_object* v___x_251_; lean_object* v_time_252_; lean_object* v_second_253_; 
v_date_250_ = lean_ctor_get(v_zdt_249_, 0);
v___x_251_ = lean_thunk_get_own(v_date_250_);
v_time_252_ = lean_ctor_get(v___x_251_, 1);
lean_inc_ref(v_time_252_);
lean_dec(v___x_251_);
v_second_253_ = lean_ctor_get(v_time_252_, 2);
lean_inc(v_second_253_);
lean_dec_ref(v_time_252_);
return v_second_253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object* v_zdt_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Time_DateTime_second(v_zdt_254_);
lean_dec_ref(v_zdt_254_);
return v_res_255_;
}
}
static lean_object* _init_l_Std_Time_DateTime_millisecond___closed__0(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_unsigned_to_nat(1000000u);
v___x_257_ = lean_nat_to_int(v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object* v_dt_258_){
_start:
{
lean_object* v_date_259_; lean_object* v___x_260_; lean_object* v_time_261_; lean_object* v_nanosecond_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_date_259_ = lean_ctor_get(v_dt_258_, 0);
v___x_260_ = lean_thunk_get_own(v_date_259_);
v_time_261_ = lean_ctor_get(v___x_260_, 1);
lean_inc_ref(v_time_261_);
lean_dec(v___x_260_);
v_nanosecond_262_ = lean_ctor_get(v_time_261_, 3);
lean_inc(v_nanosecond_262_);
lean_dec_ref(v_time_261_);
v___x_263_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_264_ = lean_int_ediv(v_nanosecond_262_, v___x_263_);
lean_dec(v_nanosecond_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object* v_dt_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Std_Time_DateTime_millisecond(v_dt_265_);
lean_dec_ref(v_dt_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object* v_zdt_267_){
_start:
{
lean_object* v_date_268_; lean_object* v___x_269_; lean_object* v_time_270_; lean_object* v_nanosecond_271_; 
v_date_268_ = lean_ctor_get(v_zdt_267_, 0);
v___x_269_ = lean_thunk_get_own(v_date_268_);
v_time_270_ = lean_ctor_get(v___x_269_, 1);
lean_inc_ref(v_time_270_);
lean_dec(v___x_269_);
v_nanosecond_271_ = lean_ctor_get(v_time_270_, 3);
lean_inc(v_nanosecond_271_);
lean_dec_ref(v_time_270_);
return v_nanosecond_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object* v_zdt_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Time_DateTime_nanosecond(v_zdt_272_);
lean_dec_ref(v_zdt_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_offset(lean_object* v_zdt_274_){
_start:
{
lean_object* v_timezone_275_; lean_object* v_offset_276_; 
v_timezone_275_ = lean_ctor_get(v_zdt_274_, 3);
v_offset_276_ = lean_ctor_get(v_timezone_275_, 0);
lean_inc(v_offset_276_);
return v_offset_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_offset___boxed(lean_object* v_zdt_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Std_Time_DateTime_offset(v_zdt_277_);
lean_dec_ref(v_zdt_277_);
return v_res_278_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object* v_zdt_279_){
_start:
{
lean_object* v_date_280_; lean_object* v___x_281_; lean_object* v_date_282_; uint8_t v___x_283_; 
v_date_280_ = lean_ctor_get(v_zdt_279_, 0);
v___x_281_ = lean_thunk_get_own(v_date_280_);
v_date_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc_ref(v_date_282_);
lean_dec(v___x_281_);
v___x_283_ = l_Std_Time_PlainDate_weekday(v_date_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object* v_zdt_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_Time_DateTime_weekday(v_zdt_284_);
lean_dec_ref(v_zdt_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__0(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(4u);
v___x_288_ = lean_nat_to_int(v___x_287_);
return v___x_288_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__1(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(400u);
v___x_290_ = lean_nat_to_int(v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__2(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(100u);
v___x_292_ = lean_nat_to_int(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object* v_date_293_){
_start:
{
lean_object* v_date_294_; lean_object* v___x_295_; lean_object* v_date_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_320_; 
v_date_294_ = lean_ctor_get(v_date_293_, 0);
v___x_295_ = lean_thunk_get_own(v_date_294_);
v_date_296_ = lean_ctor_get(v___x_295_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_295_, 1);
lean_dec(v_unused_321_);
v___x_298_ = v___x_295_;
v_isShared_299_ = v_isSharedCheck_320_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_date_296_);
lean_dec(v___x_295_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_320_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v_year_300_; lean_object* v_month_301_; lean_object* v_day_302_; uint8_t v___y_304_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_316_; 
v_year_300_ = lean_ctor_get(v_date_296_, 0);
lean_inc(v_year_300_);
v_month_301_ = lean_ctor_get(v_date_296_, 1);
lean_inc(v_month_301_);
v_day_302_ = lean_ctor_get(v_date_296_, 2);
lean_inc(v_day_302_);
lean_dec_ref(v_date_296_);
v___x_309_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_310_ = lean_int_mod(v_year_300_, v___x_309_);
v___x_311_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_316_ = lean_int_dec_eq(v___x_310_, v___x_311_);
lean_dec(v___x_310_);
if (v___x_316_ == 0)
{
lean_dec(v_year_300_);
v___y_304_ = v___x_316_;
goto v___jp_303_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_318_ = lean_int_mod(v_year_300_, v___x_317_);
v___x_319_ = lean_int_dec_eq(v___x_318_, v___x_311_);
lean_dec(v___x_318_);
if (v___x_319_ == 0)
{
if (v___x_316_ == 0)
{
goto v___jp_312_;
}
else
{
lean_dec(v_year_300_);
v___y_304_ = v___x_316_;
goto v___jp_303_;
}
}
else
{
goto v___jp_312_;
}
}
v___jp_303_:
{
lean_object* v___x_306_; 
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 1, v_day_302_);
lean_ctor_set(v___x_298_, 0, v_month_301_);
v___x_306_ = v___x_298_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_month_301_);
lean_ctor_set(v_reuseFailAlloc_308_, 1, v_day_302_);
v___x_306_ = v_reuseFailAlloc_308_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; 
v___x_307_ = l_Std_Time_ValidDate_dayOfYear(v___y_304_, v___x_306_);
lean_dec_ref(v___x_306_);
return v___x_307_;
}
}
v___jp_312_:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_313_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_314_ = lean_int_mod(v_year_300_, v___x_313_);
lean_dec(v_year_300_);
v___x_315_ = lean_int_dec_eq(v___x_314_, v___x_311_);
lean_dec(v___x_314_);
v___y_304_ = v___x_315_;
goto v___jp_303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object* v_date_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_Time_DateTime_dayOfYear(v_date_322_);
lean_dec_ref(v_date_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* v_date_324_, uint8_t v_firstDay_325_){
_start:
{
lean_object* v_date_326_; lean_object* v___x_327_; lean_object* v_date_328_; lean_object* v___x_329_; 
v_date_326_ = lean_ctor_get(v_date_324_, 0);
v___x_327_ = lean_thunk_get_own(v_date_326_);
v_date_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_date_328_);
lean_dec(v___x_327_);
v___x_329_ = l_Std_Time_PlainDate_weekOfYear(v_date_328_, v_firstDay_325_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object* v_date_330_, lean_object* v_firstDay_331_){
_start:
{
uint8_t v_firstDay_boxed_332_; lean_object* v_res_333_; 
v_firstDay_boxed_332_ = lean_unbox(v_firstDay_331_);
v_res_333_ = l_Std_Time_DateTime_weekOfYear(v_date_330_, v_firstDay_boxed_332_);
lean_dec_ref(v_date_330_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear(lean_object* v_date_334_, uint8_t v_firstDay_335_){
_start:
{
lean_object* v_date_336_; lean_object* v___x_337_; lean_object* v_date_338_; lean_object* v___x_339_; 
v_date_336_ = lean_ctor_get(v_date_334_, 0);
v___x_337_ = lean_thunk_get_own(v_date_336_);
v_date_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_date_338_);
lean_dec(v___x_337_);
v___x_339_ = l_Std_Time_PlainDate_weekYear(v_date_338_, v_firstDay_335_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___boxed(lean_object* v_date_340_, lean_object* v_firstDay_341_){
_start:
{
uint8_t v_firstDay_boxed_342_; lean_object* v_res_343_; 
v_firstDay_boxed_342_ = lean_unbox(v_firstDay_341_);
v_res_343_ = l_Std_Time_DateTime_weekYear(v_date_340_, v_firstDay_boxed_342_);
lean_dec_ref(v_date_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* v_date_344_){
_start:
{
lean_object* v_date_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_date_345_ = lean_ctor_get(v_date_344_, 0);
v___x_346_ = lean_thunk_get_own(v_date_345_);
v___x_347_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_346_);
lean_dec(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object* v_date_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_Time_DateTime_weekOfMonth(v_date_348_);
lean_dec_ref(v_date_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* v_date_350_, uint8_t v_firstDay_351_){
_start:
{
lean_object* v_date_352_; lean_object* v___x_353_; lean_object* v_date_354_; lean_object* v___x_355_; 
v_date_352_ = lean_ctor_get(v_date_350_, 0);
v___x_353_ = lean_thunk_get_own(v_date_352_);
v_date_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc_ref(v_date_354_);
lean_dec(v___x_353_);
v___x_355_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_354_, v_firstDay_351_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object* v_date_356_, lean_object* v_firstDay_357_){
_start:
{
uint8_t v_firstDay_boxed_358_; lean_object* v_res_359_; 
v_firstDay_boxed_358_ = lean_unbox(v_firstDay_357_);
v_res_359_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_356_, v_firstDay_boxed_358_);
lean_dec_ref(v_date_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* v_date_360_){
_start:
{
lean_object* v_date_361_; lean_object* v___x_362_; lean_object* v_date_363_; lean_object* v___x_364_; 
v_date_361_ = lean_ctor_get(v_date_360_, 0);
v___x_362_ = lean_thunk_get_own(v_date_361_);
v_date_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_date_363_);
lean_dec(v___x_362_);
v___x_364_ = l_Std_Time_PlainDate_quarter(v_date_363_);
lean_dec_ref(v_date_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object* v_date_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_Time_DateTime_quarter(v_date_365_);
lean_dec_ref(v_date_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_DateTime_addDays_spec__1(lean_object* v_a_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Rat_ofInt(v_a_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0(lean_object* v___y_369_, lean_object* v___x_370_, lean_object* v___x_371_, lean_object* v___x_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_offset_374_; lean_object* v_second_375_; lean_object* v_nano_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_offset_374_ = lean_ctor_get(v___y_369_, 0);
v_second_375_ = lean_ctor_get(v___x_370_, 0);
v_nano_376_ = lean_ctor_get(v___x_370_, 1);
v___x_377_ = lean_int_mul(v_second_375_, v___x_371_);
v___x_378_ = lean_int_add(v___x_377_, v_nano_376_);
lean_dec(v___x_377_);
v___x_379_ = lean_int_mul(v_offset_374_, v___x_371_);
v___x_380_ = lean_int_add(v___x_379_, v___x_372_);
lean_dec(v___x_379_);
v___x_381_ = lean_int_add(v___x_378_, v___x_380_);
lean_dec(v___x_380_);
lean_dec(v___x_378_);
v___x_382_ = l_Std_Time_Duration_ofNanoseconds(v___x_381_);
lean_dec(v___x_381_);
v___x_383_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0___boxed(lean_object* v___y_384_, lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v___x_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_Time_DateTime_addDays___lam__0(v___y_384_, v___x_385_, v___x_386_, v___x_387_, v_x_388_);
lean_dec(v___x_387_);
lean_dec(v___x_386_);
lean_dec_ref(v___x_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addDays___closed__0(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_unsigned_to_nat(86400u);
v___x_391_ = lean_nat_to_int(v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object* v_dt_392_, lean_object* v_days_393_){
_start:
{
lean_object* v_timestamp_394_; lean_object* v_rules_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_423_; 
v_timestamp_394_ = lean_ctor_get(v_dt_392_, 1);
v_rules_395_ = lean_ctor_get(v_dt_392_, 2);
v_isSharedCheck_423_ = !lean_is_exclusive(v_dt_392_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; 
v_unused_424_ = lean_ctor_get(v_dt_392_, 3);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_dt_392_, 0);
lean_dec(v_unused_425_);
v___x_397_ = v_dt_392_;
v_isShared_398_ = v_isSharedCheck_423_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_rules_395_);
lean_inc(v_timestamp_394_);
lean_dec(v_dt_392_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_423_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_second_399_; lean_object* v_nano_400_; lean_object* v_initialLocalTimeType_401_; lean_object* v_transitions_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___y_414_; lean_object* v___x_420_; 
v_second_399_ = lean_ctor_get(v_timestamp_394_, 0);
lean_inc(v_second_399_);
v_nano_400_ = lean_ctor_get(v_timestamp_394_, 1);
lean_inc(v_nano_400_);
lean_dec_ref(v_timestamp_394_);
v_initialLocalTimeType_401_ = lean_ctor_get(v_rules_395_, 0);
v_transitions_402_ = lean_ctor_get(v_rules_395_, 1);
v___x_403_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_404_ = lean_int_mul(v_days_393_, v___x_403_);
v___x_405_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_406_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_407_ = lean_int_mul(v_second_399_, v___x_406_);
lean_dec(v_second_399_);
v___x_408_ = lean_int_add(v___x_407_, v_nano_400_);
lean_dec(v_nano_400_);
lean_dec(v___x_407_);
v___x_409_ = lean_int_mul(v___x_404_, v___x_406_);
lean_dec(v___x_404_);
v___x_410_ = lean_int_add(v___x_409_, v___x_405_);
lean_dec(v___x_409_);
v___x_411_ = lean_int_add(v___x_408_, v___x_410_);
lean_dec(v___x_410_);
lean_dec(v___x_408_);
v___x_412_ = l_Std_Time_Duration_ofNanoseconds(v___x_411_);
lean_dec(v___x_411_);
v___x_420_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_402_, v___x_412_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v___x_421_; 
lean_dec_ref_known(v___x_420_, 1);
v___x_421_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_401_);
v___y_414_ = v___x_421_;
goto v___jp_413_;
}
else
{
lean_object* v_a_422_; 
v_a_422_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_420_, 1);
v___y_414_ = v_a_422_;
goto v___jp_413_;
}
v___jp_413_:
{
lean_object* v___f_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
lean_inc_ref(v___x_412_);
lean_inc_ref(v___y_414_);
v___f_415_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_415_, 0, v___y_414_);
lean_closure_set(v___f_415_, 1, v___x_412_);
lean_closure_set(v___f_415_, 2, v___x_406_);
lean_closure_set(v___f_415_, 3, v___x_405_);
v___x_416_ = lean_mk_thunk(v___f_415_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 3, v___y_414_);
lean_ctor_set(v___x_397_, 1, v___x_412_);
lean_ctor_set(v___x_397_, 0, v___x_416_);
v___x_418_ = v___x_397_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_412_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_rules_395_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v___y_414_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object* v_dt_426_, lean_object* v_days_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_Time_DateTime_addDays(v_dt_426_, v_days_427_);
lean_dec(v_days_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_DateTime_addDays_spec__0_spec__0(lean_object* v_a_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_nat_to_int(v_a_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_DateTime_addDays_spec__0(lean_object* v_a_431_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_nat_to_int(v_a_431_);
v___x_433_ = l_Rat_ofInt(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object* v_dt_434_, lean_object* v_days_435_){
_start:
{
lean_object* v_timestamp_436_; lean_object* v_rules_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_467_; 
v_timestamp_436_ = lean_ctor_get(v_dt_434_, 1);
v_rules_437_ = lean_ctor_get(v_dt_434_, 2);
v_isSharedCheck_467_ = !lean_is_exclusive(v_dt_434_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; lean_object* v_unused_469_; 
v_unused_468_ = lean_ctor_get(v_dt_434_, 3);
lean_dec(v_unused_468_);
v_unused_469_ = lean_ctor_get(v_dt_434_, 0);
lean_dec(v_unused_469_);
v___x_439_ = v_dt_434_;
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_rules_437_);
lean_inc(v_timestamp_436_);
lean_dec(v_dt_434_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_second_441_; lean_object* v_nano_442_; lean_object* v_initialLocalTimeType_443_; lean_object* v_transitions_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___y_458_; lean_object* v___x_464_; 
v_second_441_ = lean_ctor_get(v_timestamp_436_, 0);
lean_inc(v_second_441_);
v_nano_442_ = lean_ctor_get(v_timestamp_436_, 1);
lean_inc(v_nano_442_);
lean_dec_ref(v_timestamp_436_);
v_initialLocalTimeType_443_ = lean_ctor_get(v_rules_437_, 0);
v_transitions_444_ = lean_ctor_get(v_rules_437_, 1);
v___x_445_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_446_ = lean_int_mul(v_days_435_, v___x_445_);
v___x_447_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_448_ = lean_int_neg(v___x_446_);
lean_dec(v___x_446_);
v___x_449_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_450_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_451_ = lean_int_mul(v_second_441_, v___x_450_);
lean_dec(v_second_441_);
v___x_452_ = lean_int_add(v___x_451_, v_nano_442_);
lean_dec(v_nano_442_);
lean_dec(v___x_451_);
v___x_453_ = lean_int_mul(v___x_448_, v___x_450_);
lean_dec(v___x_448_);
v___x_454_ = lean_int_add(v___x_453_, v___x_449_);
lean_dec(v___x_453_);
v___x_455_ = lean_int_add(v___x_452_, v___x_454_);
lean_dec(v___x_454_);
lean_dec(v___x_452_);
v___x_456_ = l_Std_Time_Duration_ofNanoseconds(v___x_455_);
lean_dec(v___x_455_);
v___x_464_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_444_, v___x_456_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v___x_465_; 
lean_dec_ref_known(v___x_464_, 1);
v___x_465_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_443_);
v___y_458_ = v___x_465_;
goto v___jp_457_;
}
else
{
lean_object* v_a_466_; 
v_a_466_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_466_);
lean_dec_ref_known(v___x_464_, 1);
v___y_458_ = v_a_466_;
goto v___jp_457_;
}
v___jp_457_:
{
lean_object* v___f_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
lean_inc_ref(v___x_456_);
lean_inc_ref(v___y_458_);
v___f_459_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_459_, 0, v___y_458_);
lean_closure_set(v___f_459_, 1, v___x_456_);
lean_closure_set(v___f_459_, 2, v___x_450_);
lean_closure_set(v___f_459_, 3, v___x_447_);
v___x_460_ = lean_mk_thunk(v___f_459_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 3, v___y_458_);
lean_ctor_set(v___x_439_, 1, v___x_456_);
lean_ctor_set(v___x_439_, 0, v___x_460_);
v___x_462_ = v___x_439_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_rules_437_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v___y_458_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object* v_dt_470_, lean_object* v_days_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_Time_DateTime_subDays(v_dt_470_, v_days_471_);
lean_dec(v_days_471_);
return v_res_472_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_unsigned_to_nat(7u);
v___x_474_ = lean_nat_to_int(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object* v_dt_475_, lean_object* v_weeks_476_){
_start:
{
lean_object* v_timestamp_477_; lean_object* v_rules_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_508_; 
v_timestamp_477_ = lean_ctor_get(v_dt_475_, 1);
v_rules_478_ = lean_ctor_get(v_dt_475_, 2);
v_isSharedCheck_508_ = !lean_is_exclusive(v_dt_475_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; lean_object* v_unused_510_; 
v_unused_509_ = lean_ctor_get(v_dt_475_, 3);
lean_dec(v_unused_509_);
v_unused_510_ = lean_ctor_get(v_dt_475_, 0);
lean_dec(v_unused_510_);
v___x_480_ = v_dt_475_;
v_isShared_481_ = v_isSharedCheck_508_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_rules_478_);
lean_inc(v_timestamp_477_);
lean_dec(v_dt_475_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_508_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_second_482_; lean_object* v_nano_483_; lean_object* v_initialLocalTimeType_484_; lean_object* v_transitions_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___y_499_; lean_object* v___x_505_; 
v_second_482_ = lean_ctor_get(v_timestamp_477_, 0);
lean_inc(v_second_482_);
v_nano_483_ = lean_ctor_get(v_timestamp_477_, 1);
lean_inc(v_nano_483_);
lean_dec_ref(v_timestamp_477_);
v_initialLocalTimeType_484_ = lean_ctor_get(v_rules_478_, 0);
v_transitions_485_ = lean_ctor_get(v_rules_478_, 1);
v___x_486_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_487_ = lean_int_mul(v_weeks_476_, v___x_486_);
v___x_488_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_489_ = lean_int_mul(v___x_487_, v___x_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_491_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_492_ = lean_int_mul(v_second_482_, v___x_491_);
lean_dec(v_second_482_);
v___x_493_ = lean_int_add(v___x_492_, v_nano_483_);
lean_dec(v_nano_483_);
lean_dec(v___x_492_);
v___x_494_ = lean_int_mul(v___x_489_, v___x_491_);
lean_dec(v___x_489_);
v___x_495_ = lean_int_add(v___x_494_, v___x_490_);
lean_dec(v___x_494_);
v___x_496_ = lean_int_add(v___x_493_, v___x_495_);
lean_dec(v___x_495_);
lean_dec(v___x_493_);
v___x_497_ = l_Std_Time_Duration_ofNanoseconds(v___x_496_);
lean_dec(v___x_496_);
v___x_505_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_485_, v___x_497_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v___x_506_; 
lean_dec_ref_known(v___x_505_, 1);
v___x_506_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_484_);
v___y_499_ = v___x_506_;
goto v___jp_498_;
}
else
{
lean_object* v_a_507_; 
v_a_507_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v___x_505_, 1);
v___y_499_ = v_a_507_;
goto v___jp_498_;
}
v___jp_498_:
{
lean_object* v___f_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
lean_inc_ref(v___x_497_);
lean_inc_ref(v___y_499_);
v___f_500_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_500_, 0, v___y_499_);
lean_closure_set(v___f_500_, 1, v___x_497_);
lean_closure_set(v___f_500_, 2, v___x_491_);
lean_closure_set(v___f_500_, 3, v___x_490_);
v___x_501_ = lean_mk_thunk(v___f_500_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 3, v___y_499_);
lean_ctor_set(v___x_480_, 1, v___x_497_);
lean_ctor_set(v___x_480_, 0, v___x_501_);
v___x_503_ = v___x_480_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_rules_478_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v___y_499_);
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
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object* v_dt_511_, lean_object* v_weeks_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_Time_DateTime_addWeeks(v_dt_511_, v_weeks_512_);
lean_dec(v_weeks_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object* v_dt_514_, lean_object* v_weeks_515_){
_start:
{
lean_object* v_timestamp_516_; lean_object* v_rules_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_549_; 
v_timestamp_516_ = lean_ctor_get(v_dt_514_, 1);
v_rules_517_ = lean_ctor_get(v_dt_514_, 2);
v_isSharedCheck_549_ = !lean_is_exclusive(v_dt_514_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; lean_object* v_unused_551_; 
v_unused_550_ = lean_ctor_get(v_dt_514_, 3);
lean_dec(v_unused_550_);
v_unused_551_ = lean_ctor_get(v_dt_514_, 0);
lean_dec(v_unused_551_);
v___x_519_ = v_dt_514_;
v_isShared_520_ = v_isSharedCheck_549_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_rules_517_);
lean_inc(v_timestamp_516_);
lean_dec(v_dt_514_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_549_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_second_521_; lean_object* v_nano_522_; lean_object* v_initialLocalTimeType_523_; lean_object* v_transitions_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___y_540_; lean_object* v___x_546_; 
v_second_521_ = lean_ctor_get(v_timestamp_516_, 0);
lean_inc(v_second_521_);
v_nano_522_ = lean_ctor_get(v_timestamp_516_, 1);
lean_inc(v_nano_522_);
lean_dec_ref(v_timestamp_516_);
v_initialLocalTimeType_523_ = lean_ctor_get(v_rules_517_, 0);
v_transitions_524_ = lean_ctor_get(v_rules_517_, 1);
v___x_525_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_526_ = lean_int_mul(v_weeks_515_, v___x_525_);
v___x_527_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_528_ = lean_int_mul(v___x_526_, v___x_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_530_ = lean_int_neg(v___x_528_);
lean_dec(v___x_528_);
v___x_531_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_532_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_533_ = lean_int_mul(v_second_521_, v___x_532_);
lean_dec(v_second_521_);
v___x_534_ = lean_int_add(v___x_533_, v_nano_522_);
lean_dec(v_nano_522_);
lean_dec(v___x_533_);
v___x_535_ = lean_int_mul(v___x_530_, v___x_532_);
lean_dec(v___x_530_);
v___x_536_ = lean_int_add(v___x_535_, v___x_531_);
lean_dec(v___x_535_);
v___x_537_ = lean_int_add(v___x_534_, v___x_536_);
lean_dec(v___x_536_);
lean_dec(v___x_534_);
v___x_538_ = l_Std_Time_Duration_ofNanoseconds(v___x_537_);
lean_dec(v___x_537_);
v___x_546_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_524_, v___x_538_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; 
lean_dec_ref_known(v___x_546_, 1);
v___x_547_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_523_);
v___y_540_ = v___x_547_;
goto v___jp_539_;
}
else
{
lean_object* v_a_548_; 
v_a_548_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_546_, 1);
v___y_540_ = v_a_548_;
goto v___jp_539_;
}
v___jp_539_:
{
lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
lean_inc_ref(v___x_538_);
lean_inc_ref(v___y_540_);
v___f_541_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_541_, 0, v___y_540_);
lean_closure_set(v___f_541_, 1, v___x_538_);
lean_closure_set(v___f_541_, 2, v___x_532_);
lean_closure_set(v___f_541_, 3, v___x_529_);
v___x_542_ = lean_mk_thunk(v___f_541_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 3, v___y_540_);
lean_ctor_set(v___x_519_, 1, v___x_538_);
lean_ctor_set(v___x_519_, 0, v___x_542_);
v___x_544_ = v___x_519_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_rules_517_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v___y_540_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object* v_dt_552_, lean_object* v_weeks_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Time_DateTime_subWeeks(v_dt_552_, v_weeks_553_);
lean_dec(v_weeks_553_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0(lean_object* v___x_555_, lean_object* v_x_556_){
_start:
{
lean_inc_ref(v___x_555_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(lean_object* v___x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_Time_DateTime_addMonthsClip___lam__0(v___x_557_, v_x_558_);
lean_dec_ref(v___x_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object* v_dt_560_, lean_object* v_months_561_){
_start:
{
lean_object* v_date_562_; lean_object* v_rules_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_589_; 
v_date_562_ = lean_ctor_get(v_dt_560_, 0);
v_rules_563_ = lean_ctor_get(v_dt_560_, 2);
v_isSharedCheck_589_ = !lean_is_exclusive(v_dt_560_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; lean_object* v_unused_591_; 
v_unused_590_ = lean_ctor_get(v_dt_560_, 3);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_dt_560_, 1);
lean_dec(v_unused_591_);
v___x_565_ = v_dt_560_;
v_isShared_566_ = v_isSharedCheck_589_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_rules_563_);
lean_inc(v_date_562_);
lean_dec(v_dt_560_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_589_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_wt_569_; lean_object* v_ltt_570_; lean_object* v_tz_571_; lean_object* v_offset_572_; lean_object* v_second_573_; lean_object* v_nano_574_; lean_object* v___f_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_567_ = lean_thunk_get_own(v_date_562_);
lean_dec_ref(v_date_562_);
v___x_568_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_567_, v_months_561_);
lean_inc_ref(v___x_568_);
v_wt_569_ = l_Std_Time_PlainDateTime_toWallTime(v___x_568_);
lean_inc_ref(v_rules_563_);
v_ltt_570_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_563_, v_wt_569_);
v_tz_571_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_570_);
lean_dec_ref(v_ltt_570_);
v_offset_572_ = lean_ctor_get(v_tz_571_, 0);
lean_inc(v_offset_572_);
v_second_573_ = lean_ctor_get(v_wt_569_, 0);
lean_inc(v_second_573_);
v_nano_574_ = lean_ctor_get(v_wt_569_, 1);
lean_inc(v_nano_574_);
lean_dec_ref(v_wt_569_);
v___f_575_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_575_, 0, v___x_568_);
v___x_576_ = lean_mk_thunk(v___f_575_);
v___x_577_ = lean_int_neg(v_offset_572_);
lean_dec(v_offset_572_);
v___x_578_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_579_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_580_ = lean_int_mul(v_second_573_, v___x_579_);
lean_dec(v_second_573_);
v___x_581_ = lean_int_add(v___x_580_, v_nano_574_);
lean_dec(v_nano_574_);
lean_dec(v___x_580_);
v___x_582_ = lean_int_mul(v___x_577_, v___x_579_);
lean_dec(v___x_577_);
v___x_583_ = lean_int_add(v___x_582_, v___x_578_);
lean_dec(v___x_582_);
v___x_584_ = lean_int_add(v___x_581_, v___x_583_);
lean_dec(v___x_583_);
lean_dec(v___x_581_);
v___x_585_ = l_Std_Time_Duration_ofNanoseconds(v___x_584_);
lean_dec(v___x_584_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 3, v_tz_571_);
lean_ctor_set(v___x_565_, 1, v___x_585_);
lean_ctor_set(v___x_565_, 0, v___x_576_);
v___x_587_ = v___x_565_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_576_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v_rules_563_);
lean_ctor_set(v_reuseFailAlloc_588_, 3, v_tz_571_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object* v_dt_592_, lean_object* v_months_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_Time_DateTime_addMonthsClip(v_dt_592_, v_months_593_);
lean_dec(v_months_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object* v_dt_595_, lean_object* v_months_596_){
_start:
{
lean_object* v_date_597_; lean_object* v_rules_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_634_; 
v_date_597_ = lean_ctor_get(v_dt_595_, 0);
v_rules_598_ = lean_ctor_get(v_dt_595_, 2);
v_isSharedCheck_634_ = !lean_is_exclusive(v_dt_595_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; lean_object* v_unused_636_; 
v_unused_635_ = lean_ctor_get(v_dt_595_, 3);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_dt_595_, 1);
lean_dec(v_unused_636_);
v___x_600_ = v_dt_595_;
v_isShared_601_ = v_isSharedCheck_634_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_rules_598_);
lean_inc(v_date_597_);
lean_dec(v_dt_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_634_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_602_; lean_object* v_date_603_; lean_object* v_time_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_633_; 
v___x_602_ = lean_thunk_get_own(v_date_597_);
lean_dec_ref(v_date_597_);
v_date_603_ = lean_ctor_get(v___x_602_, 0);
v_time_604_ = lean_ctor_get(v___x_602_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_633_ == 0)
{
v___x_606_ = v___x_602_;
v_isShared_607_ = v_isSharedCheck_633_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_time_604_);
lean_inc(v_date_603_);
lean_dec(v___x_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_633_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_608_ = lean_int_neg(v_months_596_);
v___x_609_ = l_Std_Time_PlainDate_addMonthsClip(v_date_603_, v___x_608_);
lean_dec(v___x_608_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_609_);
v___x_611_ = v___x_606_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_time_604_);
v___x_611_ = v_reuseFailAlloc_632_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v_wt_612_; lean_object* v_ltt_613_; lean_object* v_tz_614_; lean_object* v_offset_615_; lean_object* v_second_616_; lean_object* v_nano_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
lean_inc_ref(v___x_611_);
v_wt_612_ = l_Std_Time_PlainDateTime_toWallTime(v___x_611_);
lean_inc_ref(v_rules_598_);
v_ltt_613_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_598_, v_wt_612_);
v_tz_614_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_613_);
lean_dec_ref(v_ltt_613_);
v_offset_615_ = lean_ctor_get(v_tz_614_, 0);
lean_inc(v_offset_615_);
v_second_616_ = lean_ctor_get(v_wt_612_, 0);
lean_inc(v_second_616_);
v_nano_617_ = lean_ctor_get(v_wt_612_, 1);
lean_inc(v_nano_617_);
lean_dec_ref(v_wt_612_);
v___f_618_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_618_, 0, v___x_611_);
v___x_619_ = lean_mk_thunk(v___f_618_);
v___x_620_ = lean_int_neg(v_offset_615_);
lean_dec(v_offset_615_);
v___x_621_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_622_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_623_ = lean_int_mul(v_second_616_, v___x_622_);
lean_dec(v_second_616_);
v___x_624_ = lean_int_add(v___x_623_, v_nano_617_);
lean_dec(v_nano_617_);
lean_dec(v___x_623_);
v___x_625_ = lean_int_mul(v___x_620_, v___x_622_);
lean_dec(v___x_620_);
v___x_626_ = lean_int_add(v___x_625_, v___x_621_);
lean_dec(v___x_625_);
v___x_627_ = lean_int_add(v___x_624_, v___x_626_);
lean_dec(v___x_626_);
lean_dec(v___x_624_);
v___x_628_ = l_Std_Time_Duration_ofNanoseconds(v___x_627_);
lean_dec(v___x_627_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 3, v_tz_614_);
lean_ctor_set(v___x_600_, 1, v___x_628_);
lean_ctor_set(v___x_600_, 0, v___x_619_);
v___x_630_ = v___x_600_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_rules_598_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_tz_614_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object* v_dt_637_, lean_object* v_months_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_Time_DateTime_subMonthsClip(v_dt_637_, v_months_638_);
lean_dec(v_months_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object* v_dt_640_, lean_object* v_months_641_){
_start:
{
lean_object* v_date_642_; lean_object* v_rules_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_669_; 
v_date_642_ = lean_ctor_get(v_dt_640_, 0);
v_rules_643_ = lean_ctor_get(v_dt_640_, 2);
v_isSharedCheck_669_ = !lean_is_exclusive(v_dt_640_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; lean_object* v_unused_671_; 
v_unused_670_ = lean_ctor_get(v_dt_640_, 3);
lean_dec(v_unused_670_);
v_unused_671_ = lean_ctor_get(v_dt_640_, 1);
lean_dec(v_unused_671_);
v___x_645_ = v_dt_640_;
v_isShared_646_ = v_isSharedCheck_669_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_rules_643_);
lean_inc(v_date_642_);
lean_dec(v_dt_640_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_669_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_wt_649_; lean_object* v_ltt_650_; lean_object* v_tz_651_; lean_object* v_offset_652_; lean_object* v_second_653_; lean_object* v_nano_654_; lean_object* v___f_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_647_ = lean_thunk_get_own(v_date_642_);
lean_dec_ref(v_date_642_);
v___x_648_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_647_, v_months_641_);
lean_inc_ref(v___x_648_);
v_wt_649_ = l_Std_Time_PlainDateTime_toWallTime(v___x_648_);
lean_inc_ref(v_rules_643_);
v_ltt_650_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_643_, v_wt_649_);
v_tz_651_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_650_);
lean_dec_ref(v_ltt_650_);
v_offset_652_ = lean_ctor_get(v_tz_651_, 0);
lean_inc(v_offset_652_);
v_second_653_ = lean_ctor_get(v_wt_649_, 0);
lean_inc(v_second_653_);
v_nano_654_ = lean_ctor_get(v_wt_649_, 1);
lean_inc(v_nano_654_);
lean_dec_ref(v_wt_649_);
v___f_655_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_655_, 0, v___x_648_);
v___x_656_ = lean_mk_thunk(v___f_655_);
v___x_657_ = lean_int_neg(v_offset_652_);
lean_dec(v_offset_652_);
v___x_658_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_659_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_660_ = lean_int_mul(v_second_653_, v___x_659_);
lean_dec(v_second_653_);
v___x_661_ = lean_int_add(v___x_660_, v_nano_654_);
lean_dec(v_nano_654_);
lean_dec(v___x_660_);
v___x_662_ = lean_int_mul(v___x_657_, v___x_659_);
lean_dec(v___x_657_);
v___x_663_ = lean_int_add(v___x_662_, v___x_658_);
lean_dec(v___x_662_);
v___x_664_ = lean_int_add(v___x_661_, v___x_663_);
lean_dec(v___x_663_);
lean_dec(v___x_661_);
v___x_665_ = l_Std_Time_Duration_ofNanoseconds(v___x_664_);
lean_dec(v___x_664_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 3, v_tz_651_);
lean_ctor_set(v___x_645_, 1, v___x_665_);
lean_ctor_set(v___x_645_, 0, v___x_656_);
v___x_667_ = v___x_645_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_656_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_rules_643_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_tz_651_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object* v_dt_672_, lean_object* v_months_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Std_Time_DateTime_addMonthsRollOver(v_dt_672_, v_months_673_);
lean_dec(v_months_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object* v_dt_675_, lean_object* v_months_676_){
_start:
{
lean_object* v_date_677_; lean_object* v_rules_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_714_; 
v_date_677_ = lean_ctor_get(v_dt_675_, 0);
v_rules_678_ = lean_ctor_get(v_dt_675_, 2);
v_isSharedCheck_714_ = !lean_is_exclusive(v_dt_675_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; lean_object* v_unused_716_; 
v_unused_715_ = lean_ctor_get(v_dt_675_, 3);
lean_dec(v_unused_715_);
v_unused_716_ = lean_ctor_get(v_dt_675_, 1);
lean_dec(v_unused_716_);
v___x_680_ = v_dt_675_;
v_isShared_681_ = v_isSharedCheck_714_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_rules_678_);
lean_inc(v_date_677_);
lean_dec(v_dt_675_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_714_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v_date_683_; lean_object* v_time_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_713_; 
v___x_682_ = lean_thunk_get_own(v_date_677_);
lean_dec_ref(v_date_677_);
v_date_683_ = lean_ctor_get(v___x_682_, 0);
v_time_684_ = lean_ctor_get(v___x_682_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_713_ == 0)
{
v___x_686_ = v___x_682_;
v_isShared_687_ = v_isSharedCheck_713_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_time_684_);
lean_inc(v_date_683_);
lean_dec(v___x_682_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_713_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_688_ = lean_int_neg(v_months_676_);
v___x_689_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_683_, v___x_688_);
lean_dec(v___x_688_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_time_684_);
v___x_691_ = v_reuseFailAlloc_712_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v_wt_692_; lean_object* v_ltt_693_; lean_object* v_tz_694_; lean_object* v_offset_695_; lean_object* v_second_696_; lean_object* v_nano_697_; lean_object* v___f_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
lean_inc_ref(v___x_691_);
v_wt_692_ = l_Std_Time_PlainDateTime_toWallTime(v___x_691_);
lean_inc_ref(v_rules_678_);
v_ltt_693_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_678_, v_wt_692_);
v_tz_694_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_693_);
lean_dec_ref(v_ltt_693_);
v_offset_695_ = lean_ctor_get(v_tz_694_, 0);
lean_inc(v_offset_695_);
v_second_696_ = lean_ctor_get(v_wt_692_, 0);
lean_inc(v_second_696_);
v_nano_697_ = lean_ctor_get(v_wt_692_, 1);
lean_inc(v_nano_697_);
lean_dec_ref(v_wt_692_);
v___f_698_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_698_, 0, v___x_691_);
v___x_699_ = lean_mk_thunk(v___f_698_);
v___x_700_ = lean_int_neg(v_offset_695_);
lean_dec(v_offset_695_);
v___x_701_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_702_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_703_ = lean_int_mul(v_second_696_, v___x_702_);
lean_dec(v_second_696_);
v___x_704_ = lean_int_add(v___x_703_, v_nano_697_);
lean_dec(v_nano_697_);
lean_dec(v___x_703_);
v___x_705_ = lean_int_mul(v___x_700_, v___x_702_);
lean_dec(v___x_700_);
v___x_706_ = lean_int_add(v___x_705_, v___x_701_);
lean_dec(v___x_705_);
v___x_707_ = lean_int_add(v___x_704_, v___x_706_);
lean_dec(v___x_706_);
lean_dec(v___x_704_);
v___x_708_ = l_Std_Time_Duration_ofNanoseconds(v___x_707_);
lean_dec(v___x_707_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 3, v_tz_694_);
lean_ctor_set(v___x_680_, 1, v___x_708_);
lean_ctor_set(v___x_680_, 0, v___x_699_);
v___x_710_ = v___x_680_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_rules_678_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_tz_694_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object* v_dt_717_, lean_object* v_months_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_Time_DateTime_subMonthsRollOver(v_dt_717_, v_months_718_);
lean_dec(v_months_718_);
return v_res_719_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_unsigned_to_nat(12u);
v___x_721_ = lean_nat_to_int(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object* v_dt_722_, lean_object* v_years_723_){
_start:
{
lean_object* v_date_724_; lean_object* v_rules_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_762_; 
v_date_724_ = lean_ctor_get(v_dt_722_, 0);
v_rules_725_ = lean_ctor_get(v_dt_722_, 2);
v_isSharedCheck_762_ = !lean_is_exclusive(v_dt_722_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; lean_object* v_unused_764_; 
v_unused_763_ = lean_ctor_get(v_dt_722_, 3);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_dt_722_, 1);
lean_dec(v_unused_764_);
v___x_727_ = v_dt_722_;
v_isShared_728_ = v_isSharedCheck_762_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_rules_725_);
lean_inc(v_date_724_);
lean_dec(v_dt_722_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_762_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v_date_730_; lean_object* v_time_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_761_; 
v___x_729_ = lean_thunk_get_own(v_date_724_);
lean_dec_ref(v_date_724_);
v_date_730_ = lean_ctor_get(v___x_729_, 0);
v_time_731_ = lean_ctor_get(v___x_729_, 1);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_761_ == 0)
{
v___x_733_ = v___x_729_;
v_isShared_734_ = v_isSharedCheck_761_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_time_731_);
lean_inc(v_date_730_);
lean_dec(v___x_729_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_761_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_735_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_736_ = lean_int_mul(v_years_723_, v___x_735_);
v___x_737_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_730_, v___x_736_);
lean_dec(v___x_736_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v___x_737_);
v___x_739_ = v___x_733_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_time_731_);
v___x_739_ = v_reuseFailAlloc_760_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
lean_object* v_wt_740_; lean_object* v_ltt_741_; lean_object* v_tz_742_; lean_object* v_offset_743_; lean_object* v_second_744_; lean_object* v_nano_745_; lean_object* v___f_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
lean_inc_ref(v___x_739_);
v_wt_740_ = l_Std_Time_PlainDateTime_toWallTime(v___x_739_);
lean_inc_ref(v_rules_725_);
v_ltt_741_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_725_, v_wt_740_);
v_tz_742_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_741_);
lean_dec_ref(v_ltt_741_);
v_offset_743_ = lean_ctor_get(v_tz_742_, 0);
lean_inc(v_offset_743_);
v_second_744_ = lean_ctor_get(v_wt_740_, 0);
lean_inc(v_second_744_);
v_nano_745_ = lean_ctor_get(v_wt_740_, 1);
lean_inc(v_nano_745_);
lean_dec_ref(v_wt_740_);
v___f_746_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_746_, 0, v___x_739_);
v___x_747_ = lean_mk_thunk(v___f_746_);
v___x_748_ = lean_int_neg(v_offset_743_);
lean_dec(v_offset_743_);
v___x_749_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_750_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_751_ = lean_int_mul(v_second_744_, v___x_750_);
lean_dec(v_second_744_);
v___x_752_ = lean_int_add(v___x_751_, v_nano_745_);
lean_dec(v_nano_745_);
lean_dec(v___x_751_);
v___x_753_ = lean_int_mul(v___x_748_, v___x_750_);
lean_dec(v___x_748_);
v___x_754_ = lean_int_add(v___x_753_, v___x_749_);
lean_dec(v___x_753_);
v___x_755_ = lean_int_add(v___x_752_, v___x_754_);
lean_dec(v___x_754_);
lean_dec(v___x_752_);
v___x_756_ = l_Std_Time_Duration_ofNanoseconds(v___x_755_);
lean_dec(v___x_755_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 3, v_tz_742_);
lean_ctor_set(v___x_727_, 1, v___x_756_);
lean_ctor_set(v___x_727_, 0, v___x_747_);
v___x_758_ = v___x_727_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_rules_725_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_tz_742_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object* v_dt_765_, lean_object* v_years_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Std_Time_DateTime_addYearsRollOver(v_dt_765_, v_years_766_);
lean_dec(v_years_766_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object* v_dt_768_, lean_object* v_years_769_){
_start:
{
lean_object* v_date_770_; lean_object* v_rules_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_808_; 
v_date_770_ = lean_ctor_get(v_dt_768_, 0);
v_rules_771_ = lean_ctor_get(v_dt_768_, 2);
v_isSharedCheck_808_ = !lean_is_exclusive(v_dt_768_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; lean_object* v_unused_810_; 
v_unused_809_ = lean_ctor_get(v_dt_768_, 3);
lean_dec(v_unused_809_);
v_unused_810_ = lean_ctor_get(v_dt_768_, 1);
lean_dec(v_unused_810_);
v___x_773_ = v_dt_768_;
v_isShared_774_ = v_isSharedCheck_808_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_rules_771_);
lean_inc(v_date_770_);
lean_dec(v_dt_768_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_808_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v_date_776_; lean_object* v_time_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_807_; 
v___x_775_ = lean_thunk_get_own(v_date_770_);
lean_dec_ref(v_date_770_);
v_date_776_ = lean_ctor_get(v___x_775_, 0);
v_time_777_ = lean_ctor_get(v___x_775_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_807_ == 0)
{
v___x_779_ = v___x_775_;
v_isShared_780_ = v_isSharedCheck_807_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_time_777_);
lean_inc(v_date_776_);
lean_dec(v___x_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_807_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_781_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_782_ = lean_int_mul(v_years_769_, v___x_781_);
v___x_783_ = l_Std_Time_PlainDate_addMonthsClip(v_date_776_, v___x_782_);
lean_dec(v___x_782_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_783_);
v___x_785_ = v___x_779_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_time_777_);
v___x_785_ = v_reuseFailAlloc_806_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v_wt_786_; lean_object* v_ltt_787_; lean_object* v_tz_788_; lean_object* v_offset_789_; lean_object* v_second_790_; lean_object* v_nano_791_; lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_804_; 
lean_inc_ref(v___x_785_);
v_wt_786_ = l_Std_Time_PlainDateTime_toWallTime(v___x_785_);
lean_inc_ref(v_rules_771_);
v_ltt_787_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_771_, v_wt_786_);
v_tz_788_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_787_);
lean_dec_ref(v_ltt_787_);
v_offset_789_ = lean_ctor_get(v_tz_788_, 0);
lean_inc(v_offset_789_);
v_second_790_ = lean_ctor_get(v_wt_786_, 0);
lean_inc(v_second_790_);
v_nano_791_ = lean_ctor_get(v_wt_786_, 1);
lean_inc(v_nano_791_);
lean_dec_ref(v_wt_786_);
v___f_792_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_792_, 0, v___x_785_);
v___x_793_ = lean_mk_thunk(v___f_792_);
v___x_794_ = lean_int_neg(v_offset_789_);
lean_dec(v_offset_789_);
v___x_795_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_796_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_797_ = lean_int_mul(v_second_790_, v___x_796_);
lean_dec(v_second_790_);
v___x_798_ = lean_int_add(v___x_797_, v_nano_791_);
lean_dec(v_nano_791_);
lean_dec(v___x_797_);
v___x_799_ = lean_int_mul(v___x_794_, v___x_796_);
lean_dec(v___x_794_);
v___x_800_ = lean_int_add(v___x_799_, v___x_795_);
lean_dec(v___x_799_);
v___x_801_ = lean_int_add(v___x_798_, v___x_800_);
lean_dec(v___x_800_);
lean_dec(v___x_798_);
v___x_802_ = l_Std_Time_Duration_ofNanoseconds(v___x_801_);
lean_dec(v___x_801_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 3, v_tz_788_);
lean_ctor_set(v___x_773_, 1, v___x_802_);
lean_ctor_set(v___x_773_, 0, v___x_793_);
v___x_804_ = v___x_773_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_802_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_rules_771_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_tz_788_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object* v_dt_811_, lean_object* v_years_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_Time_DateTime_addYearsClip(v_dt_811_, v_years_812_);
lean_dec(v_years_812_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object* v_dt_814_, lean_object* v_years_815_){
_start:
{
lean_object* v_date_816_; lean_object* v_rules_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_855_; 
v_date_816_ = lean_ctor_get(v_dt_814_, 0);
v_rules_817_ = lean_ctor_get(v_dt_814_, 2);
v_isSharedCheck_855_ = !lean_is_exclusive(v_dt_814_);
if (v_isSharedCheck_855_ == 0)
{
lean_object* v_unused_856_; lean_object* v_unused_857_; 
v_unused_856_ = lean_ctor_get(v_dt_814_, 3);
lean_dec(v_unused_856_);
v_unused_857_ = lean_ctor_get(v_dt_814_, 1);
lean_dec(v_unused_857_);
v___x_819_ = v_dt_814_;
v_isShared_820_ = v_isSharedCheck_855_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_rules_817_);
lean_inc(v_date_816_);
lean_dec(v_dt_814_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_855_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v_date_822_; lean_object* v_time_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_854_; 
v___x_821_ = lean_thunk_get_own(v_date_816_);
lean_dec_ref(v_date_816_);
v_date_822_ = lean_ctor_get(v___x_821_, 0);
v_time_823_ = lean_ctor_get(v___x_821_, 1);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_854_ == 0)
{
v___x_825_ = v___x_821_;
v_isShared_826_ = v_isSharedCheck_854_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_time_823_);
lean_inc(v_date_822_);
lean_dec(v___x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_854_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_827_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_828_ = lean_int_mul(v_years_815_, v___x_827_);
v___x_829_ = lean_int_neg(v___x_828_);
lean_dec(v___x_828_);
v___x_830_ = l_Std_Time_PlainDate_addMonthsClip(v_date_822_, v___x_829_);
lean_dec(v___x_829_);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_830_);
v___x_832_ = v___x_825_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_time_823_);
v___x_832_ = v_reuseFailAlloc_853_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v_wt_833_; lean_object* v_ltt_834_; lean_object* v_tz_835_; lean_object* v_offset_836_; lean_object* v_second_837_; lean_object* v_nano_838_; lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
lean_inc_ref(v___x_832_);
v_wt_833_ = l_Std_Time_PlainDateTime_toWallTime(v___x_832_);
lean_inc_ref(v_rules_817_);
v_ltt_834_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_817_, v_wt_833_);
v_tz_835_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_834_);
lean_dec_ref(v_ltt_834_);
v_offset_836_ = lean_ctor_get(v_tz_835_, 0);
lean_inc(v_offset_836_);
v_second_837_ = lean_ctor_get(v_wt_833_, 0);
lean_inc(v_second_837_);
v_nano_838_ = lean_ctor_get(v_wt_833_, 1);
lean_inc(v_nano_838_);
lean_dec_ref(v_wt_833_);
v___f_839_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_839_, 0, v___x_832_);
v___x_840_ = lean_mk_thunk(v___f_839_);
v___x_841_ = lean_int_neg(v_offset_836_);
lean_dec(v_offset_836_);
v___x_842_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_843_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_844_ = lean_int_mul(v_second_837_, v___x_843_);
lean_dec(v_second_837_);
v___x_845_ = lean_int_add(v___x_844_, v_nano_838_);
lean_dec(v_nano_838_);
lean_dec(v___x_844_);
v___x_846_ = lean_int_mul(v___x_841_, v___x_843_);
lean_dec(v___x_841_);
v___x_847_ = lean_int_add(v___x_846_, v___x_842_);
lean_dec(v___x_846_);
v___x_848_ = lean_int_add(v___x_845_, v___x_847_);
lean_dec(v___x_847_);
lean_dec(v___x_845_);
v___x_849_ = l_Std_Time_Duration_ofNanoseconds(v___x_848_);
lean_dec(v___x_848_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 3, v_tz_835_);
lean_ctor_set(v___x_819_, 1, v___x_849_);
lean_ctor_set(v___x_819_, 0, v___x_840_);
v___x_851_ = v___x_819_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_852_, 2, v_rules_817_);
lean_ctor_set(v_reuseFailAlloc_852_, 3, v_tz_835_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object* v_dt_858_, lean_object* v_years_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_Time_DateTime_subYearsClip(v_dt_858_, v_years_859_);
lean_dec(v_years_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object* v_dt_861_, lean_object* v_years_862_){
_start:
{
lean_object* v_date_863_; lean_object* v_rules_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_902_; 
v_date_863_ = lean_ctor_get(v_dt_861_, 0);
v_rules_864_ = lean_ctor_get(v_dt_861_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_dt_861_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; lean_object* v_unused_904_; 
v_unused_903_ = lean_ctor_get(v_dt_861_, 3);
lean_dec(v_unused_903_);
v_unused_904_ = lean_ctor_get(v_dt_861_, 1);
lean_dec(v_unused_904_);
v___x_866_ = v_dt_861_;
v_isShared_867_ = v_isSharedCheck_902_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_rules_864_);
lean_inc(v_date_863_);
lean_dec(v_dt_861_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_902_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v_date_869_; lean_object* v_time_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_901_; 
v___x_868_ = lean_thunk_get_own(v_date_863_);
lean_dec_ref(v_date_863_);
v_date_869_ = lean_ctor_get(v___x_868_, 0);
v_time_870_ = lean_ctor_get(v___x_868_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_901_ == 0)
{
v___x_872_ = v___x_868_;
v_isShared_873_ = v_isSharedCheck_901_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_time_870_);
lean_inc(v_date_869_);
lean_dec(v___x_868_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_901_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_874_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_875_ = lean_int_mul(v_years_862_, v___x_874_);
v___x_876_ = lean_int_neg(v___x_875_);
lean_dec(v___x_875_);
v___x_877_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_869_, v___x_876_);
lean_dec(v___x_876_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_877_);
v___x_879_ = v___x_872_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_877_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_time_870_);
v___x_879_ = v_reuseFailAlloc_900_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
lean_object* v_wt_880_; lean_object* v_ltt_881_; lean_object* v_tz_882_; lean_object* v_offset_883_; lean_object* v_second_884_; lean_object* v_nano_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
lean_inc_ref(v___x_879_);
v_wt_880_ = l_Std_Time_PlainDateTime_toWallTime(v___x_879_);
lean_inc_ref(v_rules_864_);
v_ltt_881_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_864_, v_wt_880_);
v_tz_882_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_881_);
lean_dec_ref(v_ltt_881_);
v_offset_883_ = lean_ctor_get(v_tz_882_, 0);
lean_inc(v_offset_883_);
v_second_884_ = lean_ctor_get(v_wt_880_, 0);
lean_inc(v_second_884_);
v_nano_885_ = lean_ctor_get(v_wt_880_, 1);
lean_inc(v_nano_885_);
lean_dec_ref(v_wt_880_);
v___f_886_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_886_, 0, v___x_879_);
v___x_887_ = lean_mk_thunk(v___f_886_);
v___x_888_ = lean_int_neg(v_offset_883_);
lean_dec(v_offset_883_);
v___x_889_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_890_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_891_ = lean_int_mul(v_second_884_, v___x_890_);
lean_dec(v_second_884_);
v___x_892_ = lean_int_add(v___x_891_, v_nano_885_);
lean_dec(v_nano_885_);
lean_dec(v___x_891_);
v___x_893_ = lean_int_mul(v___x_888_, v___x_890_);
lean_dec(v___x_888_);
v___x_894_ = lean_int_add(v___x_893_, v___x_889_);
lean_dec(v___x_893_);
v___x_895_ = lean_int_add(v___x_892_, v___x_894_);
lean_dec(v___x_894_);
lean_dec(v___x_892_);
v___x_896_ = l_Std_Time_Duration_ofNanoseconds(v___x_895_);
lean_dec(v___x_895_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 3, v_tz_882_);
lean_ctor_set(v___x_866_, 1, v___x_896_);
lean_ctor_set(v___x_866_, 0, v___x_887_);
v___x_898_ = v___x_866_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_rules_864_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_tz_882_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object* v_dt_905_, lean_object* v_years_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_Time_DateTime_subYearsRollOver(v_dt_905_, v_years_906_);
lean_dec(v_years_906_);
return v_res_907_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_unsigned_to_nat(3600u);
v___x_909_ = lean_nat_to_int(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object* v_dt_910_, lean_object* v_hours_911_){
_start:
{
lean_object* v_timestamp_912_; lean_object* v_rules_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_941_; 
v_timestamp_912_ = lean_ctor_get(v_dt_910_, 1);
v_rules_913_ = lean_ctor_get(v_dt_910_, 2);
v_isSharedCheck_941_ = !lean_is_exclusive(v_dt_910_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; lean_object* v_unused_943_; 
v_unused_942_ = lean_ctor_get(v_dt_910_, 3);
lean_dec(v_unused_942_);
v_unused_943_ = lean_ctor_get(v_dt_910_, 0);
lean_dec(v_unused_943_);
v___x_915_ = v_dt_910_;
v_isShared_916_ = v_isSharedCheck_941_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_rules_913_);
lean_inc(v_timestamp_912_);
lean_dec(v_dt_910_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_941_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_second_917_; lean_object* v_nano_918_; lean_object* v_initialLocalTimeType_919_; lean_object* v_transitions_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___y_932_; lean_object* v___x_938_; 
v_second_917_ = lean_ctor_get(v_timestamp_912_, 0);
lean_inc(v_second_917_);
v_nano_918_ = lean_ctor_get(v_timestamp_912_, 1);
lean_inc(v_nano_918_);
lean_dec_ref(v_timestamp_912_);
v_initialLocalTimeType_919_ = lean_ctor_get(v_rules_913_, 0);
v_transitions_920_ = lean_ctor_get(v_rules_913_, 1);
v___x_921_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_922_ = lean_int_mul(v_hours_911_, v___x_921_);
v___x_923_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_924_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_925_ = lean_int_mul(v_second_917_, v___x_924_);
lean_dec(v_second_917_);
v___x_926_ = lean_int_add(v___x_925_, v_nano_918_);
lean_dec(v_nano_918_);
lean_dec(v___x_925_);
v___x_927_ = lean_int_mul(v___x_922_, v___x_924_);
lean_dec(v___x_922_);
v___x_928_ = lean_int_add(v___x_927_, v___x_923_);
lean_dec(v___x_927_);
v___x_929_ = lean_int_add(v___x_926_, v___x_928_);
lean_dec(v___x_928_);
lean_dec(v___x_926_);
v___x_930_ = l_Std_Time_Duration_ofNanoseconds(v___x_929_);
lean_dec(v___x_929_);
v___x_938_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_920_, v___x_930_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; 
lean_dec_ref_known(v___x_938_, 1);
v___x_939_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_919_);
v___y_932_ = v___x_939_;
goto v___jp_931_;
}
else
{
lean_object* v_a_940_; 
v_a_940_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_940_);
lean_dec_ref_known(v___x_938_, 1);
v___y_932_ = v_a_940_;
goto v___jp_931_;
}
v___jp_931_:
{
lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
lean_inc_ref(v___x_930_);
lean_inc_ref(v___y_932_);
v___f_933_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_933_, 0, v___y_932_);
lean_closure_set(v___f_933_, 1, v___x_930_);
lean_closure_set(v___f_933_, 2, v___x_924_);
lean_closure_set(v___f_933_, 3, v___x_923_);
v___x_934_ = lean_mk_thunk(v___f_933_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 3, v___y_932_);
lean_ctor_set(v___x_915_, 1, v___x_930_);
lean_ctor_set(v___x_915_, 0, v___x_934_);
v___x_936_ = v___x_915_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_rules_913_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v___y_932_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object* v_dt_944_, lean_object* v_hours_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Std_Time_DateTime_addHours(v_dt_944_, v_hours_945_);
lean_dec(v_hours_945_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object* v_dt_947_, lean_object* v_hours_948_){
_start:
{
lean_object* v_timestamp_949_; lean_object* v_rules_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_980_; 
v_timestamp_949_ = lean_ctor_get(v_dt_947_, 1);
v_rules_950_ = lean_ctor_get(v_dt_947_, 2);
v_isSharedCheck_980_ = !lean_is_exclusive(v_dt_947_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; lean_object* v_unused_982_; 
v_unused_981_ = lean_ctor_get(v_dt_947_, 3);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_dt_947_, 0);
lean_dec(v_unused_982_);
v___x_952_ = v_dt_947_;
v_isShared_953_ = v_isSharedCheck_980_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_rules_950_);
lean_inc(v_timestamp_949_);
lean_dec(v_dt_947_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_980_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_second_954_; lean_object* v_nano_955_; lean_object* v_initialLocalTimeType_956_; lean_object* v_transitions_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___y_971_; lean_object* v___x_977_; 
v_second_954_ = lean_ctor_get(v_timestamp_949_, 0);
lean_inc(v_second_954_);
v_nano_955_ = lean_ctor_get(v_timestamp_949_, 1);
lean_inc(v_nano_955_);
lean_dec_ref(v_timestamp_949_);
v_initialLocalTimeType_956_ = lean_ctor_get(v_rules_950_, 0);
v_transitions_957_ = lean_ctor_get(v_rules_950_, 1);
v___x_958_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_959_ = lean_int_mul(v_hours_948_, v___x_958_);
v___x_960_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_961_ = lean_int_neg(v___x_959_);
lean_dec(v___x_959_);
v___x_962_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_963_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_964_ = lean_int_mul(v_second_954_, v___x_963_);
lean_dec(v_second_954_);
v___x_965_ = lean_int_add(v___x_964_, v_nano_955_);
lean_dec(v_nano_955_);
lean_dec(v___x_964_);
v___x_966_ = lean_int_mul(v___x_961_, v___x_963_);
lean_dec(v___x_961_);
v___x_967_ = lean_int_add(v___x_966_, v___x_962_);
lean_dec(v___x_966_);
v___x_968_ = lean_int_add(v___x_965_, v___x_967_);
lean_dec(v___x_967_);
lean_dec(v___x_965_);
v___x_969_ = l_Std_Time_Duration_ofNanoseconds(v___x_968_);
lean_dec(v___x_968_);
v___x_977_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_957_, v___x_969_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_978_; 
lean_dec_ref_known(v___x_977_, 1);
v___x_978_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_956_);
v___y_971_ = v___x_978_;
goto v___jp_970_;
}
else
{
lean_object* v_a_979_; 
v_a_979_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_977_, 1);
v___y_971_ = v_a_979_;
goto v___jp_970_;
}
v___jp_970_:
{
lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
lean_inc_ref(v___x_969_);
lean_inc_ref(v___y_971_);
v___f_972_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_972_, 0, v___y_971_);
lean_closure_set(v___f_972_, 1, v___x_969_);
lean_closure_set(v___f_972_, 2, v___x_963_);
lean_closure_set(v___f_972_, 3, v___x_960_);
v___x_973_ = lean_mk_thunk(v___f_972_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 3, v___y_971_);
lean_ctor_set(v___x_952_, 1, v___x_969_);
lean_ctor_set(v___x_952_, 0, v___x_973_);
v___x_975_ = v___x_952_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_rules_950_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v___y_971_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object* v_dt_983_, lean_object* v_hours_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_Time_DateTime_subHours(v_dt_983_, v_hours_984_);
lean_dec(v_hours_984_);
return v_res_985_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_unsigned_to_nat(60u);
v___x_987_ = lean_nat_to_int(v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object* v_dt_988_, lean_object* v_minutes_989_){
_start:
{
lean_object* v_timestamp_990_; lean_object* v_rules_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1019_; 
v_timestamp_990_ = lean_ctor_get(v_dt_988_, 1);
v_rules_991_ = lean_ctor_get(v_dt_988_, 2);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_dt_988_);
if (v_isSharedCheck_1019_ == 0)
{
lean_object* v_unused_1020_; lean_object* v_unused_1021_; 
v_unused_1020_ = lean_ctor_get(v_dt_988_, 3);
lean_dec(v_unused_1020_);
v_unused_1021_ = lean_ctor_get(v_dt_988_, 0);
lean_dec(v_unused_1021_);
v___x_993_ = v_dt_988_;
v_isShared_994_ = v_isSharedCheck_1019_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_rules_991_);
lean_inc(v_timestamp_990_);
lean_dec(v_dt_988_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1019_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v_second_995_; lean_object* v_nano_996_; lean_object* v_initialLocalTimeType_997_; lean_object* v_transitions_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___y_1010_; lean_object* v___x_1016_; 
v_second_995_ = lean_ctor_get(v_timestamp_990_, 0);
lean_inc(v_second_995_);
v_nano_996_ = lean_ctor_get(v_timestamp_990_, 1);
lean_inc(v_nano_996_);
lean_dec_ref(v_timestamp_990_);
v_initialLocalTimeType_997_ = lean_ctor_get(v_rules_991_, 0);
v_transitions_998_ = lean_ctor_get(v_rules_991_, 1);
v___x_999_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_1000_ = lean_int_mul(v_minutes_989_, v___x_999_);
v___x_1001_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1002_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1003_ = lean_int_mul(v_second_995_, v___x_1002_);
lean_dec(v_second_995_);
v___x_1004_ = lean_int_add(v___x_1003_, v_nano_996_);
lean_dec(v_nano_996_);
lean_dec(v___x_1003_);
v___x_1005_ = lean_int_mul(v___x_1000_, v___x_1002_);
lean_dec(v___x_1000_);
v___x_1006_ = lean_int_add(v___x_1005_, v___x_1001_);
lean_dec(v___x_1005_);
v___x_1007_ = lean_int_add(v___x_1004_, v___x_1006_);
lean_dec(v___x_1006_);
lean_dec(v___x_1004_);
v___x_1008_ = l_Std_Time_Duration_ofNanoseconds(v___x_1007_);
lean_dec(v___x_1007_);
v___x_1016_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_998_, v___x_1008_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v___x_1017_; 
lean_dec_ref_known(v___x_1016_, 1);
v___x_1017_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_997_);
v___y_1010_ = v___x_1017_;
goto v___jp_1009_;
}
else
{
lean_object* v_a_1018_; 
v_a_1018_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v___x_1016_, 1);
v___y_1010_ = v_a_1018_;
goto v___jp_1009_;
}
v___jp_1009_:
{
lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
lean_inc_ref(v___x_1008_);
lean_inc_ref(v___y_1010_);
v___f_1011_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1011_, 0, v___y_1010_);
lean_closure_set(v___f_1011_, 1, v___x_1008_);
lean_closure_set(v___f_1011_, 2, v___x_1002_);
lean_closure_set(v___f_1011_, 3, v___x_1001_);
v___x_1012_ = lean_mk_thunk(v___f_1011_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 3, v___y_1010_);
lean_ctor_set(v___x_993_, 1, v___x_1008_);
lean_ctor_set(v___x_993_, 0, v___x_1012_);
v___x_1014_ = v___x_993_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_rules_991_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v___y_1010_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object* v_dt_1022_, lean_object* v_minutes_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_Time_DateTime_addMinutes(v_dt_1022_, v_minutes_1023_);
lean_dec(v_minutes_1023_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object* v_dt_1025_, lean_object* v_minutes_1026_){
_start:
{
lean_object* v_timestamp_1027_; lean_object* v_rules_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1058_; 
v_timestamp_1027_ = lean_ctor_get(v_dt_1025_, 1);
v_rules_1028_ = lean_ctor_get(v_dt_1025_, 2);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_dt_1025_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; lean_object* v_unused_1060_; 
v_unused_1059_ = lean_ctor_get(v_dt_1025_, 3);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_dt_1025_, 0);
lean_dec(v_unused_1060_);
v___x_1030_ = v_dt_1025_;
v_isShared_1031_ = v_isSharedCheck_1058_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_rules_1028_);
lean_inc(v_timestamp_1027_);
lean_dec(v_dt_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1058_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_second_1032_; lean_object* v_nano_1033_; lean_object* v_initialLocalTimeType_1034_; lean_object* v_transitions_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___y_1049_; lean_object* v___x_1055_; 
v_second_1032_ = lean_ctor_get(v_timestamp_1027_, 0);
lean_inc(v_second_1032_);
v_nano_1033_ = lean_ctor_get(v_timestamp_1027_, 1);
lean_inc(v_nano_1033_);
lean_dec_ref(v_timestamp_1027_);
v_initialLocalTimeType_1034_ = lean_ctor_get(v_rules_1028_, 0);
v_transitions_1035_ = lean_ctor_get(v_rules_1028_, 1);
v___x_1036_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_1037_ = lean_int_mul(v_minutes_1026_, v___x_1036_);
v___x_1038_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1039_ = lean_int_neg(v___x_1037_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1041_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1042_ = lean_int_mul(v_second_1032_, v___x_1041_);
lean_dec(v_second_1032_);
v___x_1043_ = lean_int_add(v___x_1042_, v_nano_1033_);
lean_dec(v_nano_1033_);
lean_dec(v___x_1042_);
v___x_1044_ = lean_int_mul(v___x_1039_, v___x_1041_);
lean_dec(v___x_1039_);
v___x_1045_ = lean_int_add(v___x_1044_, v___x_1040_);
lean_dec(v___x_1044_);
v___x_1046_ = lean_int_add(v___x_1043_, v___x_1045_);
lean_dec(v___x_1045_);
lean_dec(v___x_1043_);
v___x_1047_ = l_Std_Time_Duration_ofNanoseconds(v___x_1046_);
lean_dec(v___x_1046_);
v___x_1055_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1035_, v___x_1047_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1056_; 
lean_dec_ref_known(v___x_1055_, 1);
v___x_1056_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1034_);
v___y_1049_ = v___x_1056_;
goto v___jp_1048_;
}
else
{
lean_object* v_a_1057_; 
v_a_1057_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1055_, 1);
v___y_1049_ = v_a_1057_;
goto v___jp_1048_;
}
v___jp_1048_:
{
lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
lean_inc_ref(v___x_1047_);
lean_inc_ref(v___y_1049_);
v___f_1050_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1050_, 0, v___y_1049_);
lean_closure_set(v___f_1050_, 1, v___x_1047_);
lean_closure_set(v___f_1050_, 2, v___x_1041_);
lean_closure_set(v___f_1050_, 3, v___x_1038_);
v___x_1051_ = lean_mk_thunk(v___f_1050_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 3, v___y_1049_);
lean_ctor_set(v___x_1030_, 1, v___x_1047_);
lean_ctor_set(v___x_1030_, 0, v___x_1051_);
v___x_1053_ = v___x_1030_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_rules_1028_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v___y_1049_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object* v_dt_1061_, lean_object* v_minutes_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_Time_DateTime_subMinutes(v_dt_1061_, v_minutes_1062_);
lean_dec(v_minutes_1062_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0(lean_object* v___y_1064_, lean_object* v___x_1065_, lean_object* v___x_1066_, lean_object* v_x_1067_){
_start:
{
lean_object* v_offset_1068_; lean_object* v_second_1069_; lean_object* v_nano_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v_offset_1068_ = lean_ctor_get(v___y_1064_, 0);
v_second_1069_ = lean_ctor_get(v___x_1065_, 0);
v_nano_1070_ = lean_ctor_get(v___x_1065_, 1);
v___x_1071_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1072_ = lean_int_mul(v_second_1069_, v___x_1066_);
v___x_1073_ = lean_int_add(v___x_1072_, v_nano_1070_);
lean_dec(v___x_1072_);
v___x_1074_ = lean_int_mul(v_offset_1068_, v___x_1066_);
v___x_1075_ = lean_int_add(v___x_1074_, v___x_1071_);
lean_dec(v___x_1074_);
v___x_1076_ = lean_int_add(v___x_1073_, v___x_1075_);
lean_dec(v___x_1075_);
lean_dec(v___x_1073_);
v___x_1077_ = l_Std_Time_Duration_ofNanoseconds(v___x_1076_);
lean_dec(v___x_1076_);
v___x_1078_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(lean_object* v___y_1079_, lean_object* v___x_1080_, lean_object* v___x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Std_Time_DateTime_addMilliseconds___lam__0(v___y_1079_, v___x_1080_, v___x_1081_, v_x_1082_);
lean_dec(v___x_1081_);
lean_dec_ref(v___x_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object* v_dt_1084_, lean_object* v_milliseconds_1085_){
_start:
{
lean_object* v_timestamp_1086_; lean_object* v_rules_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1117_; 
v_timestamp_1086_ = lean_ctor_get(v_dt_1084_, 1);
v_rules_1087_ = lean_ctor_get(v_dt_1084_, 2);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_dt_1084_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; lean_object* v_unused_1119_; 
v_unused_1118_ = lean_ctor_get(v_dt_1084_, 3);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_dt_1084_, 0);
lean_dec(v_unused_1119_);
v___x_1089_ = v_dt_1084_;
v_isShared_1090_ = v_isSharedCheck_1117_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_rules_1087_);
lean_inc(v_timestamp_1086_);
lean_dec(v_dt_1084_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1117_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v_second_1091_; lean_object* v_nano_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_second_1096_; lean_object* v_nano_1097_; lean_object* v_initialLocalTimeType_1098_; lean_object* v_transitions_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___y_1108_; lean_object* v___x_1114_; 
v_second_1091_ = lean_ctor_get(v_timestamp_1086_, 0);
lean_inc(v_second_1091_);
v_nano_1092_ = lean_ctor_get(v_timestamp_1086_, 1);
lean_inc(v_nano_1092_);
lean_dec_ref(v_timestamp_1086_);
v___x_1093_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1094_ = lean_int_mul(v_milliseconds_1085_, v___x_1093_);
v___x_1095_ = l_Std_Time_Duration_ofNanoseconds(v___x_1094_);
lean_dec(v___x_1094_);
v_second_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_second_1096_);
v_nano_1097_ = lean_ctor_get(v___x_1095_, 1);
lean_inc(v_nano_1097_);
lean_dec_ref(v___x_1095_);
v_initialLocalTimeType_1098_ = lean_ctor_get(v_rules_1087_, 0);
v_transitions_1099_ = lean_ctor_get(v_rules_1087_, 1);
v___x_1100_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1101_ = lean_int_mul(v_second_1091_, v___x_1100_);
lean_dec(v_second_1091_);
v___x_1102_ = lean_int_add(v___x_1101_, v_nano_1092_);
lean_dec(v_nano_1092_);
lean_dec(v___x_1101_);
v___x_1103_ = lean_int_mul(v_second_1096_, v___x_1100_);
lean_dec(v_second_1096_);
v___x_1104_ = lean_int_add(v___x_1103_, v_nano_1097_);
lean_dec(v_nano_1097_);
lean_dec(v___x_1103_);
v___x_1105_ = lean_int_add(v___x_1102_, v___x_1104_);
lean_dec(v___x_1104_);
lean_dec(v___x_1102_);
v___x_1106_ = l_Std_Time_Duration_ofNanoseconds(v___x_1105_);
lean_dec(v___x_1105_);
v___x_1114_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1099_, v___x_1106_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v___x_1115_; 
lean_dec_ref_known(v___x_1114_, 1);
v___x_1115_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1098_);
v___y_1108_ = v___x_1115_;
goto v___jp_1107_;
}
else
{
lean_object* v_a_1116_; 
v_a_1116_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1114_, 1);
v___y_1108_ = v_a_1116_;
goto v___jp_1107_;
}
v___jp_1107_:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
lean_inc_ref(v___x_1106_);
lean_inc_ref(v___y_1108_);
v___f_1109_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1109_, 0, v___y_1108_);
lean_closure_set(v___f_1109_, 1, v___x_1106_);
lean_closure_set(v___f_1109_, 2, v___x_1100_);
v___x_1110_ = lean_mk_thunk(v___f_1109_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 3, v___y_1108_);
lean_ctor_set(v___x_1089_, 1, v___x_1106_);
lean_ctor_set(v___x_1089_, 0, v___x_1110_);
v___x_1112_ = v___x_1089_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_rules_1087_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v___y_1108_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object* v_dt_1120_, lean_object* v_milliseconds_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_Time_DateTime_addMilliseconds(v_dt_1120_, v_milliseconds_1121_);
lean_dec(v_milliseconds_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object* v_dt_1123_, lean_object* v_milliseconds_1124_){
_start:
{
lean_object* v_timestamp_1125_; lean_object* v_rules_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1158_; 
v_timestamp_1125_ = lean_ctor_get(v_dt_1123_, 1);
v_rules_1126_ = lean_ctor_get(v_dt_1123_, 2);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_dt_1123_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; lean_object* v_unused_1160_; 
v_unused_1159_ = lean_ctor_get(v_dt_1123_, 3);
lean_dec(v_unused_1159_);
v_unused_1160_ = lean_ctor_get(v_dt_1123_, 0);
lean_dec(v_unused_1160_);
v___x_1128_ = v_dt_1123_;
v_isShared_1129_ = v_isSharedCheck_1158_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_rules_1126_);
lean_inc(v_timestamp_1125_);
lean_dec(v_dt_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1158_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v_second_1133_; lean_object* v_nano_1134_; lean_object* v_second_1135_; lean_object* v_nano_1136_; lean_object* v_initialLocalTimeType_1137_; lean_object* v_transitions_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___y_1149_; lean_object* v___x_1155_; 
v___x_1130_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1131_ = lean_int_mul(v_milliseconds_1124_, v___x_1130_);
v___x_1132_ = l_Std_Time_Duration_ofNanoseconds(v___x_1131_);
lean_dec(v___x_1131_);
v_second_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_second_1133_);
v_nano_1134_ = lean_ctor_get(v___x_1132_, 1);
lean_inc(v_nano_1134_);
lean_dec_ref(v___x_1132_);
v_second_1135_ = lean_ctor_get(v_timestamp_1125_, 0);
lean_inc(v_second_1135_);
v_nano_1136_ = lean_ctor_get(v_timestamp_1125_, 1);
lean_inc(v_nano_1136_);
lean_dec_ref(v_timestamp_1125_);
v_initialLocalTimeType_1137_ = lean_ctor_get(v_rules_1126_, 0);
v_transitions_1138_ = lean_ctor_get(v_rules_1126_, 1);
v___x_1139_ = lean_int_neg(v_second_1133_);
lean_dec(v_second_1133_);
v___x_1140_ = lean_int_neg(v_nano_1134_);
lean_dec(v_nano_1134_);
v___x_1141_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1142_ = lean_int_mul(v_second_1135_, v___x_1141_);
lean_dec(v_second_1135_);
v___x_1143_ = lean_int_add(v___x_1142_, v_nano_1136_);
lean_dec(v_nano_1136_);
lean_dec(v___x_1142_);
v___x_1144_ = lean_int_mul(v___x_1139_, v___x_1141_);
lean_dec(v___x_1139_);
v___x_1145_ = lean_int_add(v___x_1144_, v___x_1140_);
lean_dec(v___x_1140_);
lean_dec(v___x_1144_);
v___x_1146_ = lean_int_add(v___x_1143_, v___x_1145_);
lean_dec(v___x_1145_);
lean_dec(v___x_1143_);
v___x_1147_ = l_Std_Time_Duration_ofNanoseconds(v___x_1146_);
lean_dec(v___x_1146_);
v___x_1155_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1138_, v___x_1147_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v___x_1156_; 
lean_dec_ref_known(v___x_1155_, 1);
v___x_1156_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1137_);
v___y_1149_ = v___x_1156_;
goto v___jp_1148_;
}
else
{
lean_object* v_a_1157_; 
v_a_1157_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1155_, 1);
v___y_1149_ = v_a_1157_;
goto v___jp_1148_;
}
v___jp_1148_:
{
lean_object* v___f_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
lean_inc_ref(v___x_1147_);
lean_inc_ref(v___y_1149_);
v___f_1150_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1150_, 0, v___y_1149_);
lean_closure_set(v___f_1150_, 1, v___x_1147_);
lean_closure_set(v___f_1150_, 2, v___x_1141_);
v___x_1151_ = lean_mk_thunk(v___f_1150_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 3, v___y_1149_);
lean_ctor_set(v___x_1128_, 1, v___x_1147_);
lean_ctor_set(v___x_1128_, 0, v___x_1151_);
v___x_1153_ = v___x_1128_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_rules_1126_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v___y_1149_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object* v_dt_1161_, lean_object* v_milliseconds_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_Time_DateTime_subMilliseconds(v_dt_1161_, v_milliseconds_1162_);
lean_dec(v_milliseconds_1162_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object* v_dt_1164_, lean_object* v_seconds_1165_){
_start:
{
lean_object* v_timestamp_1166_; lean_object* v_rules_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1193_; 
v_timestamp_1166_ = lean_ctor_get(v_dt_1164_, 1);
v_rules_1167_ = lean_ctor_get(v_dt_1164_, 2);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_dt_1164_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; lean_object* v_unused_1195_; 
v_unused_1194_ = lean_ctor_get(v_dt_1164_, 3);
lean_dec(v_unused_1194_);
v_unused_1195_ = lean_ctor_get(v_dt_1164_, 0);
lean_dec(v_unused_1195_);
v___x_1169_ = v_dt_1164_;
v_isShared_1170_ = v_isSharedCheck_1193_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_rules_1167_);
lean_inc(v_timestamp_1166_);
lean_dec(v_dt_1164_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1193_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_second_1171_; lean_object* v_nano_1172_; lean_object* v_initialLocalTimeType_1173_; lean_object* v_transitions_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___y_1184_; lean_object* v___x_1190_; 
v_second_1171_ = lean_ctor_get(v_timestamp_1166_, 0);
lean_inc(v_second_1171_);
v_nano_1172_ = lean_ctor_get(v_timestamp_1166_, 1);
lean_inc(v_nano_1172_);
lean_dec_ref(v_timestamp_1166_);
v_initialLocalTimeType_1173_ = lean_ctor_get(v_rules_1167_, 0);
v_transitions_1174_ = lean_ctor_get(v_rules_1167_, 1);
v___x_1175_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1176_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1177_ = lean_int_mul(v_second_1171_, v___x_1176_);
lean_dec(v_second_1171_);
v___x_1178_ = lean_int_add(v___x_1177_, v_nano_1172_);
lean_dec(v_nano_1172_);
lean_dec(v___x_1177_);
v___x_1179_ = lean_int_mul(v_seconds_1165_, v___x_1176_);
v___x_1180_ = lean_int_add(v___x_1179_, v___x_1175_);
lean_dec(v___x_1179_);
v___x_1181_ = lean_int_add(v___x_1178_, v___x_1180_);
lean_dec(v___x_1180_);
lean_dec(v___x_1178_);
v___x_1182_ = l_Std_Time_Duration_ofNanoseconds(v___x_1181_);
lean_dec(v___x_1181_);
v___x_1190_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1174_, v___x_1182_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref_known(v___x_1190_, 1);
v___x_1191_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1173_);
v___y_1184_ = v___x_1191_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1192_; 
v_a_1192_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1190_, 1);
v___y_1184_ = v_a_1192_;
goto v___jp_1183_;
}
v___jp_1183_:
{
lean_object* v___f_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_inc_ref(v___x_1182_);
lean_inc_ref(v___y_1184_);
v___f_1185_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1185_, 0, v___y_1184_);
lean_closure_set(v___f_1185_, 1, v___x_1182_);
lean_closure_set(v___f_1185_, 2, v___x_1176_);
lean_closure_set(v___f_1185_, 3, v___x_1175_);
v___x_1186_ = lean_mk_thunk(v___f_1185_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 3, v___y_1184_);
lean_ctor_set(v___x_1169_, 1, v___x_1182_);
lean_ctor_set(v___x_1169_, 0, v___x_1186_);
v___x_1188_ = v___x_1169_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_rules_1167_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v___y_1184_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object* v_dt_1196_, lean_object* v_seconds_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Std_Time_DateTime_addSeconds(v_dt_1196_, v_seconds_1197_);
lean_dec(v_seconds_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object* v_dt_1199_, lean_object* v_seconds_1200_){
_start:
{
lean_object* v_timestamp_1201_; lean_object* v_rules_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1230_; 
v_timestamp_1201_ = lean_ctor_get(v_dt_1199_, 1);
v_rules_1202_ = lean_ctor_get(v_dt_1199_, 2);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_dt_1199_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; lean_object* v_unused_1232_; 
v_unused_1231_ = lean_ctor_get(v_dt_1199_, 3);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_dt_1199_, 0);
lean_dec(v_unused_1232_);
v___x_1204_ = v_dt_1199_;
v_isShared_1205_ = v_isSharedCheck_1230_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_rules_1202_);
lean_inc(v_timestamp_1201_);
lean_dec(v_dt_1199_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1230_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v_second_1206_; lean_object* v_nano_1207_; lean_object* v_initialLocalTimeType_1208_; lean_object* v_transitions_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___y_1221_; lean_object* v___x_1227_; 
v_second_1206_ = lean_ctor_get(v_timestamp_1201_, 0);
lean_inc(v_second_1206_);
v_nano_1207_ = lean_ctor_get(v_timestamp_1201_, 1);
lean_inc(v_nano_1207_);
lean_dec_ref(v_timestamp_1201_);
v_initialLocalTimeType_1208_ = lean_ctor_get(v_rules_1202_, 0);
v_transitions_1209_ = lean_ctor_get(v_rules_1202_, 1);
v___x_1210_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1211_ = lean_int_neg(v_seconds_1200_);
v___x_1212_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1213_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1214_ = lean_int_mul(v_second_1206_, v___x_1213_);
lean_dec(v_second_1206_);
v___x_1215_ = lean_int_add(v___x_1214_, v_nano_1207_);
lean_dec(v_nano_1207_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_int_mul(v___x_1211_, v___x_1213_);
lean_dec(v___x_1211_);
v___x_1217_ = lean_int_add(v___x_1216_, v___x_1212_);
lean_dec(v___x_1216_);
v___x_1218_ = lean_int_add(v___x_1215_, v___x_1217_);
lean_dec(v___x_1217_);
lean_dec(v___x_1215_);
v___x_1219_ = l_Std_Time_Duration_ofNanoseconds(v___x_1218_);
lean_dec(v___x_1218_);
v___x_1227_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1209_, v___x_1219_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref_known(v___x_1227_, 1);
v___x_1228_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1208_);
v___y_1221_ = v___x_1228_;
goto v___jp_1220_;
}
else
{
lean_object* v_a_1229_; 
v_a_1229_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1229_);
lean_dec_ref_known(v___x_1227_, 1);
v___y_1221_ = v_a_1229_;
goto v___jp_1220_;
}
v___jp_1220_:
{
lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
lean_inc_ref(v___x_1219_);
lean_inc_ref(v___y_1221_);
v___f_1222_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1222_, 0, v___y_1221_);
lean_closure_set(v___f_1222_, 1, v___x_1219_);
lean_closure_set(v___f_1222_, 2, v___x_1213_);
lean_closure_set(v___f_1222_, 3, v___x_1210_);
v___x_1223_ = lean_mk_thunk(v___f_1222_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 3, v___y_1221_);
lean_ctor_set(v___x_1204_, 1, v___x_1219_);
lean_ctor_set(v___x_1204_, 0, v___x_1223_);
v___x_1225_ = v___x_1204_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_rules_1202_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object* v_dt_1233_, lean_object* v_seconds_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_Time_DateTime_subSeconds(v_dt_1233_, v_seconds_1234_);
lean_dec(v_seconds_1234_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object* v_dt_1236_, lean_object* v_nanoseconds_1237_){
_start:
{
lean_object* v_timestamp_1238_; lean_object* v_rules_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1267_; 
v_timestamp_1238_ = lean_ctor_get(v_dt_1236_, 1);
v_rules_1239_ = lean_ctor_get(v_dt_1236_, 2);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_dt_1236_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; lean_object* v_unused_1269_; 
v_unused_1268_ = lean_ctor_get(v_dt_1236_, 3);
lean_dec(v_unused_1268_);
v_unused_1269_ = lean_ctor_get(v_dt_1236_, 0);
lean_dec(v_unused_1269_);
v___x_1241_ = v_dt_1236_;
v_isShared_1242_ = v_isSharedCheck_1267_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_rules_1239_);
lean_inc(v_timestamp_1238_);
lean_dec(v_dt_1236_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1267_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_second_1243_; lean_object* v_nano_1244_; lean_object* v___x_1245_; lean_object* v_second_1246_; lean_object* v_nano_1247_; lean_object* v_initialLocalTimeType_1248_; lean_object* v_transitions_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___y_1258_; lean_object* v___x_1264_; 
v_second_1243_ = lean_ctor_get(v_timestamp_1238_, 0);
lean_inc(v_second_1243_);
v_nano_1244_ = lean_ctor_get(v_timestamp_1238_, 1);
lean_inc(v_nano_1244_);
lean_dec_ref(v_timestamp_1238_);
v___x_1245_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1237_);
v_second_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_second_1246_);
v_nano_1247_ = lean_ctor_get(v___x_1245_, 1);
lean_inc(v_nano_1247_);
lean_dec_ref(v___x_1245_);
v_initialLocalTimeType_1248_ = lean_ctor_get(v_rules_1239_, 0);
v_transitions_1249_ = lean_ctor_get(v_rules_1239_, 1);
v___x_1250_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1251_ = lean_int_mul(v_second_1243_, v___x_1250_);
lean_dec(v_second_1243_);
v___x_1252_ = lean_int_add(v___x_1251_, v_nano_1244_);
lean_dec(v_nano_1244_);
lean_dec(v___x_1251_);
v___x_1253_ = lean_int_mul(v_second_1246_, v___x_1250_);
lean_dec(v_second_1246_);
v___x_1254_ = lean_int_add(v___x_1253_, v_nano_1247_);
lean_dec(v_nano_1247_);
lean_dec(v___x_1253_);
v___x_1255_ = lean_int_add(v___x_1252_, v___x_1254_);
lean_dec(v___x_1254_);
lean_dec(v___x_1252_);
v___x_1256_ = l_Std_Time_Duration_ofNanoseconds(v___x_1255_);
lean_dec(v___x_1255_);
v___x_1264_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1249_, v___x_1256_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref_known(v___x_1264_, 1);
v___x_1265_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1248_);
v___y_1258_ = v___x_1265_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1266_; 
v_a_1266_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1266_);
lean_dec_ref_known(v___x_1264_, 1);
v___y_1258_ = v_a_1266_;
goto v___jp_1257_;
}
v___jp_1257_:
{
lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
lean_inc_ref(v___x_1256_);
lean_inc_ref(v___y_1258_);
v___f_1259_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1259_, 0, v___y_1258_);
lean_closure_set(v___f_1259_, 1, v___x_1256_);
lean_closure_set(v___f_1259_, 2, v___x_1250_);
v___x_1260_ = lean_mk_thunk(v___f_1259_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 3, v___y_1258_);
lean_ctor_set(v___x_1241_, 1, v___x_1256_);
lean_ctor_set(v___x_1241_, 0, v___x_1260_);
v___x_1262_ = v___x_1241_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_rules_1239_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v___y_1258_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object* v_dt_1270_, lean_object* v_nanoseconds_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Std_Time_DateTime_addNanoseconds(v_dt_1270_, v_nanoseconds_1271_);
lean_dec(v_nanoseconds_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object* v_dt_1273_, lean_object* v_nanoseconds_1274_){
_start:
{
lean_object* v_timestamp_1275_; lean_object* v_rules_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1306_; 
v_timestamp_1275_ = lean_ctor_get(v_dt_1273_, 1);
v_rules_1276_ = lean_ctor_get(v_dt_1273_, 2);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_dt_1273_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; lean_object* v_unused_1308_; 
v_unused_1307_ = lean_ctor_get(v_dt_1273_, 3);
lean_dec(v_unused_1307_);
v_unused_1308_ = lean_ctor_get(v_dt_1273_, 0);
lean_dec(v_unused_1308_);
v___x_1278_ = v_dt_1273_;
v_isShared_1279_ = v_isSharedCheck_1306_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_rules_1276_);
lean_inc(v_timestamp_1275_);
lean_dec(v_dt_1273_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1306_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1280_; lean_object* v_second_1281_; lean_object* v_nano_1282_; lean_object* v_second_1283_; lean_object* v_nano_1284_; lean_object* v_initialLocalTimeType_1285_; lean_object* v_transitions_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___y_1297_; lean_object* v___x_1303_; 
v___x_1280_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1274_);
v_second_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_second_1281_);
v_nano_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc(v_nano_1282_);
lean_dec_ref(v___x_1280_);
v_second_1283_ = lean_ctor_get(v_timestamp_1275_, 0);
lean_inc(v_second_1283_);
v_nano_1284_ = lean_ctor_get(v_timestamp_1275_, 1);
lean_inc(v_nano_1284_);
lean_dec_ref(v_timestamp_1275_);
v_initialLocalTimeType_1285_ = lean_ctor_get(v_rules_1276_, 0);
v_transitions_1286_ = lean_ctor_get(v_rules_1276_, 1);
v___x_1287_ = lean_int_neg(v_second_1281_);
lean_dec(v_second_1281_);
v___x_1288_ = lean_int_neg(v_nano_1282_);
lean_dec(v_nano_1282_);
v___x_1289_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1290_ = lean_int_mul(v_second_1283_, v___x_1289_);
lean_dec(v_second_1283_);
v___x_1291_ = lean_int_add(v___x_1290_, v_nano_1284_);
lean_dec(v_nano_1284_);
lean_dec(v___x_1290_);
v___x_1292_ = lean_int_mul(v___x_1287_, v___x_1289_);
lean_dec(v___x_1287_);
v___x_1293_ = lean_int_add(v___x_1292_, v___x_1288_);
lean_dec(v___x_1288_);
lean_dec(v___x_1292_);
v___x_1294_ = lean_int_add(v___x_1291_, v___x_1293_);
lean_dec(v___x_1293_);
lean_dec(v___x_1291_);
v___x_1295_ = l_Std_Time_Duration_ofNanoseconds(v___x_1294_);
lean_dec(v___x_1294_);
v___x_1303_ = l_Std_Time_TimeZone_Transition_timezoneAt(v_transitions_1286_, v___x_1295_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v___x_1304_; 
lean_dec_ref_known(v___x_1303_, 1);
v___x_1304_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_initialLocalTimeType_1285_);
v___y_1297_ = v___x_1304_;
goto v___jp_1296_;
}
else
{
lean_object* v_a_1305_; 
v_a_1305_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1303_, 1);
v___y_1297_ = v_a_1305_;
goto v___jp_1296_;
}
v___jp_1296_:
{
lean_object* v___f_1298_; lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_inc_ref(v___x_1295_);
lean_inc_ref(v___y_1297_);
v___f_1298_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1298_, 0, v___y_1297_);
lean_closure_set(v___f_1298_, 1, v___x_1295_);
lean_closure_set(v___f_1298_, 2, v___x_1289_);
v___x_1299_ = lean_mk_thunk(v___f_1298_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 3, v___y_1297_);
lean_ctor_set(v___x_1278_, 1, v___x_1295_);
lean_ctor_set(v___x_1278_, 0, v___x_1299_);
v___x_1301_ = v___x_1278_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_rules_1276_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v___y_1297_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object* v_dt_1309_, lean_object* v_nanoseconds_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Std_Time_DateTime_subNanoseconds(v_dt_1309_, v_nanoseconds_1310_);
lean_dec(v_nanoseconds_1310_);
return v_res_1311_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object* v_date_1312_){
_start:
{
lean_object* v_date_1313_; lean_object* v___x_1314_; lean_object* v_date_1315_; lean_object* v_year_1316_; uint8_t v___x_1317_; 
v_date_1313_ = lean_ctor_get(v_date_1312_, 0);
v___x_1314_ = lean_thunk_get_own(v_date_1313_);
v_date_1315_ = lean_ctor_get(v___x_1314_, 0);
lean_inc_ref(v_date_1315_);
lean_dec(v___x_1314_);
v_year_1316_ = lean_ctor_get(v_date_1315_, 0);
lean_inc(v_year_1316_);
lean_dec_ref(v_date_1315_);
v___x_1317_ = l_Std_Time_Year_Offset_era(v_year_1316_);
lean_dec(v_year_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object* v_date_1318_){
_start:
{
uint8_t v_res_1319_; lean_object* v_r_1320_; 
v_res_1319_ = l_Std_Time_DateTime_era(v_date_1318_);
lean_dec_ref(v_date_1318_);
v_r_1320_ = lean_box(v_res_1319_);
return v_r_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object* v_dt_1321_, uint8_t v_desiredWeekday_1322_){
_start:
{
lean_object* v_date_1323_; lean_object* v_rules_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1350_; 
v_date_1323_ = lean_ctor_get(v_dt_1321_, 0);
v_rules_1324_ = lean_ctor_get(v_dt_1321_, 2);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_dt_1321_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; 
v_unused_1351_ = lean_ctor_get(v_dt_1321_, 3);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_dt_1321_, 1);
lean_dec(v_unused_1352_);
v___x_1326_ = v_dt_1321_;
v_isShared_1327_ = v_isSharedCheck_1350_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_rules_1324_);
lean_inc(v_date_1323_);
lean_dec(v_dt_1321_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1350_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_date_1328_; lean_object* v___x_1329_; lean_object* v_wt_1330_; lean_object* v_ltt_1331_; lean_object* v_tz_1332_; lean_object* v_offset_1333_; lean_object* v_second_1334_; lean_object* v_nano_1335_; lean_object* v___f_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v_date_1328_ = lean_thunk_get_own(v_date_1323_);
lean_dec_ref(v_date_1323_);
v___x_1329_ = l_Std_Time_PlainDateTime_withWeekday(v_date_1328_, v_desiredWeekday_1322_);
lean_inc_ref(v___x_1329_);
v_wt_1330_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1329_);
lean_inc_ref(v_rules_1324_);
v_ltt_1331_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1324_, v_wt_1330_);
v_tz_1332_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1331_);
lean_dec_ref(v_ltt_1331_);
v_offset_1333_ = lean_ctor_get(v_tz_1332_, 0);
lean_inc(v_offset_1333_);
v_second_1334_ = lean_ctor_get(v_wt_1330_, 0);
lean_inc(v_second_1334_);
v_nano_1335_ = lean_ctor_get(v_wt_1330_, 1);
lean_inc(v_nano_1335_);
lean_dec_ref(v_wt_1330_);
v___f_1336_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1336_, 0, v___x_1329_);
v___x_1337_ = lean_mk_thunk(v___f_1336_);
v___x_1338_ = lean_int_neg(v_offset_1333_);
lean_dec(v_offset_1333_);
v___x_1339_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1340_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1341_ = lean_int_mul(v_second_1334_, v___x_1340_);
lean_dec(v_second_1334_);
v___x_1342_ = lean_int_add(v___x_1341_, v_nano_1335_);
lean_dec(v_nano_1335_);
lean_dec(v___x_1341_);
v___x_1343_ = lean_int_mul(v___x_1338_, v___x_1340_);
lean_dec(v___x_1338_);
v___x_1344_ = lean_int_add(v___x_1343_, v___x_1339_);
lean_dec(v___x_1343_);
v___x_1345_ = lean_int_add(v___x_1342_, v___x_1344_);
lean_dec(v___x_1344_);
lean_dec(v___x_1342_);
v___x_1346_ = l_Std_Time_Duration_ofNanoseconds(v___x_1345_);
lean_dec(v___x_1345_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 3, v_tz_1332_);
lean_ctor_set(v___x_1326_, 1, v___x_1346_);
lean_ctor_set(v___x_1326_, 0, v___x_1337_);
v___x_1348_ = v___x_1326_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_rules_1324_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_tz_1332_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object* v_dt_1353_, lean_object* v_desiredWeekday_1354_){
_start:
{
uint8_t v_desiredWeekday_boxed_1355_; lean_object* v_res_1356_; 
v_desiredWeekday_boxed_1355_ = lean_unbox(v_desiredWeekday_1354_);
v_res_1356_ = l_Std_Time_DateTime_withWeekday(v_dt_1353_, v_desiredWeekday_boxed_1355_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object* v_dt_1357_, lean_object* v_days_1358_){
_start:
{
lean_object* v_date_1359_; lean_object* v_rules_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1425_; 
v_date_1359_ = lean_ctor_get(v_dt_1357_, 0);
v_rules_1360_ = lean_ctor_get(v_dt_1357_, 2);
v_isSharedCheck_1425_ = !lean_is_exclusive(v_dt_1357_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; lean_object* v_unused_1427_; 
v_unused_1426_ = lean_ctor_get(v_dt_1357_, 3);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_dt_1357_, 1);
lean_dec(v_unused_1427_);
v___x_1362_ = v_dt_1357_;
v_isShared_1363_ = v_isSharedCheck_1425_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_rules_1360_);
lean_inc(v_date_1359_);
lean_dec(v_dt_1357_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1425_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v_date_1364_; lean_object* v___y_1366_; lean_object* v_date_1396_; lean_object* v_year_1397_; lean_object* v_month_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1423_; 
v_date_1364_ = lean_thunk_get_own(v_date_1359_);
lean_dec_ref(v_date_1359_);
v_date_1396_ = lean_ctor_get(v_date_1364_, 0);
lean_inc_ref(v_date_1396_);
v_year_1397_ = lean_ctor_get(v_date_1396_, 0);
v_month_1398_ = lean_ctor_get(v_date_1396_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_date_1396_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_date_1396_, 2);
lean_dec(v_unused_1424_);
v___x_1400_ = v_date_1396_;
v_isShared_1401_ = v_isSharedCheck_1423_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_month_1398_);
lean_inc(v_year_1397_);
lean_dec(v_date_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1423_;
goto v_resetjp_1399_;
}
v___jp_1365_:
{
lean_object* v_time_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1394_; 
v_time_1367_ = lean_ctor_get(v_date_1364_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_date_1364_);
if (v_isSharedCheck_1394_ == 0)
{
lean_object* v_unused_1395_; 
v_unused_1395_ = lean_ctor_get(v_date_1364_, 0);
lean_dec(v_unused_1395_);
v___x_1369_ = v_date_1364_;
v_isShared_1370_ = v_isSharedCheck_1394_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_time_1367_);
lean_dec(v_date_1364_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1394_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___y_1366_);
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___y_1366_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_time_1367_);
v___x_1372_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v_wt_1373_; lean_object* v_ltt_1374_; lean_object* v_tz_1375_; lean_object* v_offset_1376_; lean_object* v_second_1377_; lean_object* v_nano_1378_; lean_object* v___f_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1391_; 
lean_inc_ref(v___x_1372_);
v_wt_1373_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1372_);
lean_inc_ref(v_rules_1360_);
v_ltt_1374_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1360_, v_wt_1373_);
v_tz_1375_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1374_);
lean_dec_ref(v_ltt_1374_);
v_offset_1376_ = lean_ctor_get(v_tz_1375_, 0);
lean_inc(v_offset_1376_);
v_second_1377_ = lean_ctor_get(v_wt_1373_, 0);
lean_inc(v_second_1377_);
v_nano_1378_ = lean_ctor_get(v_wt_1373_, 1);
lean_inc(v_nano_1378_);
lean_dec_ref(v_wt_1373_);
v___f_1379_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1379_, 0, v___x_1372_);
v___x_1380_ = lean_mk_thunk(v___f_1379_);
v___x_1381_ = lean_int_neg(v_offset_1376_);
lean_dec(v_offset_1376_);
v___x_1382_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1383_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1384_ = lean_int_mul(v_second_1377_, v___x_1383_);
lean_dec(v_second_1377_);
v___x_1385_ = lean_int_add(v___x_1384_, v_nano_1378_);
lean_dec(v_nano_1378_);
lean_dec(v___x_1384_);
v___x_1386_ = lean_int_mul(v___x_1381_, v___x_1383_);
lean_dec(v___x_1381_);
v___x_1387_ = lean_int_add(v___x_1386_, v___x_1382_);
lean_dec(v___x_1386_);
v___x_1388_ = lean_int_add(v___x_1385_, v___x_1387_);
lean_dec(v___x_1387_);
lean_dec(v___x_1385_);
v___x_1389_ = l_Std_Time_Duration_ofNanoseconds(v___x_1388_);
lean_dec(v___x_1388_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 3, v_tz_1375_);
lean_ctor_set(v___x_1362_, 1, v___x_1389_);
lean_ctor_set(v___x_1362_, 0, v___x_1380_);
v___x_1391_ = v___x_1362_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_rules_1360_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_tz_1375_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
v_resetjp_1399_:
{
uint8_t v___y_1403_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1419_; 
v___x_1412_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1413_ = lean_int_mod(v_year_1397_, v___x_1412_);
v___x_1414_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1419_ = lean_int_dec_eq(v___x_1413_, v___x_1414_);
lean_dec(v___x_1413_);
if (v___x_1419_ == 0)
{
v___y_1403_ = v___x_1419_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1421_ = lean_int_mod(v_year_1397_, v___x_1420_);
v___x_1422_ = lean_int_dec_eq(v___x_1421_, v___x_1414_);
lean_dec(v___x_1421_);
if (v___x_1422_ == 0)
{
if (v___x_1419_ == 0)
{
goto v___jp_1415_;
}
else
{
v___y_1403_ = v___x_1419_;
goto v___jp_1402_;
}
}
else
{
goto v___jp_1415_;
}
}
v___jp_1402_:
{
lean_object* v_max_1404_; uint8_t v___x_1405_; 
v_max_1404_ = l_Std_Time_Month_Ordinal_days(v___y_1403_, v_month_1398_);
v___x_1405_ = lean_int_dec_lt(v_max_1404_, v_days_1358_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1407_; 
lean_dec(v_max_1404_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 2, v_days_1358_);
v___x_1407_ = v___x_1400_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_year_1397_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_month_1398_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_days_1358_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
v___y_1366_ = v___x_1407_;
goto v___jp_1365_;
}
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_days_1358_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 2, v_max_1404_);
v___x_1410_ = v___x_1400_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_year_1397_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_month_1398_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_max_1404_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
v___y_1366_ = v___x_1410_;
goto v___jp_1365_;
}
}
}
v___jp_1415_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1417_ = lean_int_mod(v_year_1397_, v___x_1416_);
v___x_1418_ = lean_int_dec_eq(v___x_1417_, v___x_1414_);
lean_dec(v___x_1417_);
v___y_1403_ = v___x_1418_;
goto v___jp_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object* v_dt_1428_, lean_object* v_days_1429_){
_start:
{
lean_object* v_date_1430_; lean_object* v_rules_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1468_; 
v_date_1430_ = lean_ctor_get(v_dt_1428_, 0);
v_rules_1431_ = lean_ctor_get(v_dt_1428_, 2);
v_isSharedCheck_1468_ = !lean_is_exclusive(v_dt_1428_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; lean_object* v_unused_1470_; 
v_unused_1469_ = lean_ctor_get(v_dt_1428_, 3);
lean_dec(v_unused_1469_);
v_unused_1470_ = lean_ctor_get(v_dt_1428_, 1);
lean_dec(v_unused_1470_);
v___x_1433_ = v_dt_1428_;
v_isShared_1434_ = v_isSharedCheck_1468_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_rules_1431_);
lean_inc(v_date_1430_);
lean_dec(v_dt_1428_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1468_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_date_1435_; lean_object* v_date_1436_; lean_object* v_time_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1467_; 
v_date_1435_ = lean_thunk_get_own(v_date_1430_);
lean_dec_ref(v_date_1430_);
v_date_1436_ = lean_ctor_get(v_date_1435_, 0);
v_time_1437_ = lean_ctor_get(v_date_1435_, 1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_date_1435_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1439_ = v_date_1435_;
v_isShared_1440_ = v_isSharedCheck_1467_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_time_1437_);
lean_inc(v_date_1436_);
lean_dec(v_date_1435_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1467_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_year_1441_; lean_object* v_month_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v_year_1441_ = lean_ctor_get(v_date_1436_, 0);
lean_inc(v_year_1441_);
v_month_1442_ = lean_ctor_get(v_date_1436_, 1);
lean_inc(v_month_1442_);
lean_dec_ref(v_date_1436_);
v___x_1443_ = l_Std_Time_PlainDate_rollOver(v_year_1441_, v_month_1442_, v_days_1429_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1443_);
v___x_1445_ = v___x_1439_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_time_1437_);
v___x_1445_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v_wt_1446_; lean_object* v_ltt_1447_; lean_object* v_tz_1448_; lean_object* v_offset_1449_; lean_object* v_second_1450_; lean_object* v_nano_1451_; lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_inc_ref(v___x_1445_);
v_wt_1446_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1445_);
lean_inc_ref(v_rules_1431_);
v_ltt_1447_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1431_, v_wt_1446_);
v_tz_1448_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1447_);
lean_dec_ref(v_ltt_1447_);
v_offset_1449_ = lean_ctor_get(v_tz_1448_, 0);
lean_inc(v_offset_1449_);
v_second_1450_ = lean_ctor_get(v_wt_1446_, 0);
lean_inc(v_second_1450_);
v_nano_1451_ = lean_ctor_get(v_wt_1446_, 1);
lean_inc(v_nano_1451_);
lean_dec_ref(v_wt_1446_);
v___f_1452_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1452_, 0, v___x_1445_);
v___x_1453_ = lean_mk_thunk(v___f_1452_);
v___x_1454_ = lean_int_neg(v_offset_1449_);
lean_dec(v_offset_1449_);
v___x_1455_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1456_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1457_ = lean_int_mul(v_second_1450_, v___x_1456_);
lean_dec(v_second_1450_);
v___x_1458_ = lean_int_add(v___x_1457_, v_nano_1451_);
lean_dec(v_nano_1451_);
lean_dec(v___x_1457_);
v___x_1459_ = lean_int_mul(v___x_1454_, v___x_1456_);
lean_dec(v___x_1454_);
v___x_1460_ = lean_int_add(v___x_1459_, v___x_1455_);
lean_dec(v___x_1459_);
v___x_1461_ = lean_int_add(v___x_1458_, v___x_1460_);
lean_dec(v___x_1460_);
lean_dec(v___x_1458_);
v___x_1462_ = l_Std_Time_Duration_ofNanoseconds(v___x_1461_);
lean_dec(v___x_1461_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 3, v_tz_1448_);
lean_ctor_set(v___x_1433_, 1, v___x_1462_);
lean_ctor_set(v___x_1433_, 0, v___x_1453_);
v___x_1464_ = v___x_1433_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_rules_1431_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_tz_1448_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object* v_dt_1471_, lean_object* v_days_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Std_Time_DateTime_withDaysRollOver(v_dt_1471_, v_days_1472_);
lean_dec(v_days_1472_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object* v_dt_1474_, lean_object* v_month_1475_){
_start:
{
lean_object* v_date_1476_; lean_object* v_rules_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1542_; 
v_date_1476_ = lean_ctor_get(v_dt_1474_, 0);
v_rules_1477_ = lean_ctor_get(v_dt_1474_, 2);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_dt_1474_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; lean_object* v_unused_1544_; 
v_unused_1543_ = lean_ctor_get(v_dt_1474_, 3);
lean_dec(v_unused_1543_);
v_unused_1544_ = lean_ctor_get(v_dt_1474_, 1);
lean_dec(v_unused_1544_);
v___x_1479_ = v_dt_1474_;
v_isShared_1480_ = v_isSharedCheck_1542_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_rules_1477_);
lean_inc(v_date_1476_);
lean_dec(v_dt_1474_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1542_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v_date_1481_; lean_object* v___y_1483_; lean_object* v_date_1513_; lean_object* v_year_1514_; lean_object* v_day_1515_; lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1540_; 
v_date_1481_ = lean_thunk_get_own(v_date_1476_);
lean_dec_ref(v_date_1476_);
v_date_1513_ = lean_ctor_get(v_date_1481_, 0);
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
v___jp_1482_:
{
lean_object* v_time_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1511_; 
v_time_1484_ = lean_ctor_get(v_date_1481_, 1);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_date_1481_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v_date_1481_, 0);
lean_dec(v_unused_1512_);
v___x_1486_ = v_date_1481_;
v_isShared_1487_ = v_isSharedCheck_1511_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_time_1484_);
lean_dec(v_date_1481_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1511_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___y_1483_);
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___y_1483_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_time_1484_);
v___x_1489_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v_wt_1490_; lean_object* v_ltt_1491_; lean_object* v_tz_1492_; lean_object* v_offset_1493_; lean_object* v_second_1494_; lean_object* v_nano_1495_; lean_object* v___f_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1508_; 
lean_inc_ref(v___x_1489_);
v_wt_1490_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1489_);
lean_inc_ref(v_rules_1477_);
v_ltt_1491_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1477_, v_wt_1490_);
v_tz_1492_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1491_);
lean_dec_ref(v_ltt_1491_);
v_offset_1493_ = lean_ctor_get(v_tz_1492_, 0);
lean_inc(v_offset_1493_);
v_second_1494_ = lean_ctor_get(v_wt_1490_, 0);
lean_inc(v_second_1494_);
v_nano_1495_ = lean_ctor_get(v_wt_1490_, 1);
lean_inc(v_nano_1495_);
lean_dec_ref(v_wt_1490_);
v___f_1496_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1496_, 0, v___x_1489_);
v___x_1497_ = lean_mk_thunk(v___f_1496_);
v___x_1498_ = lean_int_neg(v_offset_1493_);
lean_dec(v_offset_1493_);
v___x_1499_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1500_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1501_ = lean_int_mul(v_second_1494_, v___x_1500_);
lean_dec(v_second_1494_);
v___x_1502_ = lean_int_add(v___x_1501_, v_nano_1495_);
lean_dec(v_nano_1495_);
lean_dec(v___x_1501_);
v___x_1503_ = lean_int_mul(v___x_1498_, v___x_1500_);
lean_dec(v___x_1498_);
v___x_1504_ = lean_int_add(v___x_1503_, v___x_1499_);
lean_dec(v___x_1503_);
v___x_1505_ = lean_int_add(v___x_1502_, v___x_1504_);
lean_dec(v___x_1504_);
lean_dec(v___x_1502_);
v___x_1506_ = l_Std_Time_Duration_ofNanoseconds(v___x_1505_);
lean_dec(v___x_1505_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 3, v_tz_1492_);
lean_ctor_set(v___x_1479_, 1, v___x_1506_);
lean_ctor_set(v___x_1479_, 0, v___x_1497_);
v___x_1508_ = v___x_1479_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_rules_1477_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_tz_1492_);
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
v___x_1529_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1530_ = lean_int_mod(v_year_1514_, v___x_1529_);
v___x_1531_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
v___x_1537_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
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
v_max_1521_ = l_Std_Time_Month_Ordinal_days(v___y_1520_, v_month_1475_);
v___x_1522_ = lean_int_dec_lt(v_max_1521_, v_day_1515_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1524_; 
lean_dec(v_max_1521_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 1, v_month_1475_);
v___x_1524_ = v___x_1517_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_year_1514_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_month_1475_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_day_1515_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
v___y_1483_ = v___x_1524_;
goto v___jp_1482_;
}
}
else
{
lean_object* v___x_1527_; 
lean_dec(v_day_1515_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set(v___x_1517_, 2, v_max_1521_);
lean_ctor_set(v___x_1517_, 1, v_month_1475_);
v___x_1527_ = v___x_1517_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_year_1514_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_month_1475_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_max_1521_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
v___y_1483_ = v___x_1527_;
goto v___jp_1482_;
}
}
}
v___jp_1532_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; 
v___x_1533_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object* v_dt_1545_, lean_object* v_month_1546_){
_start:
{
lean_object* v_date_1547_; lean_object* v_rules_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1585_; 
v_date_1547_ = lean_ctor_get(v_dt_1545_, 0);
v_rules_1548_ = lean_ctor_get(v_dt_1545_, 2);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_dt_1545_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; lean_object* v_unused_1587_; 
v_unused_1586_ = lean_ctor_get(v_dt_1545_, 3);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_dt_1545_, 1);
lean_dec(v_unused_1587_);
v___x_1550_ = v_dt_1545_;
v_isShared_1551_ = v_isSharedCheck_1585_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_rules_1548_);
lean_inc(v_date_1547_);
lean_dec(v_dt_1545_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1585_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v_date_1552_; lean_object* v_date_1553_; lean_object* v_time_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1584_; 
v_date_1552_ = lean_thunk_get_own(v_date_1547_);
lean_dec_ref(v_date_1547_);
v_date_1553_ = lean_ctor_get(v_date_1552_, 0);
v_time_1554_ = lean_ctor_get(v_date_1552_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_date_1552_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1556_ = v_date_1552_;
v_isShared_1557_ = v_isSharedCheck_1584_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_time_1554_);
lean_inc(v_date_1553_);
lean_dec(v_date_1552_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1584_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_year_1558_; lean_object* v_day_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v_year_1558_ = lean_ctor_get(v_date_1553_, 0);
lean_inc(v_year_1558_);
v_day_1559_ = lean_ctor_get(v_date_1553_, 2);
lean_inc(v_day_1559_);
lean_dec_ref(v_date_1553_);
v___x_1560_ = l_Std_Time_PlainDate_rollOver(v_year_1558_, v_month_1546_, v_day_1559_);
lean_dec(v_day_1559_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1560_);
v___x_1562_ = v___x_1556_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_time_1554_);
v___x_1562_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v_wt_1563_; lean_object* v_ltt_1564_; lean_object* v_tz_1565_; lean_object* v_offset_1566_; lean_object* v_second_1567_; lean_object* v_nano_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_inc_ref(v___x_1562_);
v_wt_1563_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1562_);
lean_inc_ref(v_rules_1548_);
v_ltt_1564_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1548_, v_wt_1563_);
v_tz_1565_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1564_);
lean_dec_ref(v_ltt_1564_);
v_offset_1566_ = lean_ctor_get(v_tz_1565_, 0);
lean_inc(v_offset_1566_);
v_second_1567_ = lean_ctor_get(v_wt_1563_, 0);
lean_inc(v_second_1567_);
v_nano_1568_ = lean_ctor_get(v_wt_1563_, 1);
lean_inc(v_nano_1568_);
lean_dec_ref(v_wt_1563_);
v___f_1569_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1569_, 0, v___x_1562_);
v___x_1570_ = lean_mk_thunk(v___f_1569_);
v___x_1571_ = lean_int_neg(v_offset_1566_);
lean_dec(v_offset_1566_);
v___x_1572_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1573_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1574_ = lean_int_mul(v_second_1567_, v___x_1573_);
lean_dec(v_second_1567_);
v___x_1575_ = lean_int_add(v___x_1574_, v_nano_1568_);
lean_dec(v_nano_1568_);
lean_dec(v___x_1574_);
v___x_1576_ = lean_int_mul(v___x_1571_, v___x_1573_);
lean_dec(v___x_1571_);
v___x_1577_ = lean_int_add(v___x_1576_, v___x_1572_);
lean_dec(v___x_1576_);
v___x_1578_ = lean_int_add(v___x_1575_, v___x_1577_);
lean_dec(v___x_1577_);
lean_dec(v___x_1575_);
v___x_1579_ = l_Std_Time_Duration_ofNanoseconds(v___x_1578_);
lean_dec(v___x_1578_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 3, v_tz_1565_);
lean_ctor_set(v___x_1550_, 1, v___x_1579_);
lean_ctor_set(v___x_1550_, 0, v___x_1570_);
v___x_1581_ = v___x_1550_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_rules_1548_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v_tz_1565_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object* v_dt_1588_, lean_object* v_year_1589_){
_start:
{
lean_object* v_date_1590_; lean_object* v_rules_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1656_; 
v_date_1590_ = lean_ctor_get(v_dt_1588_, 0);
v_rules_1591_ = lean_ctor_get(v_dt_1588_, 2);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_dt_1588_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; lean_object* v_unused_1658_; 
v_unused_1657_ = lean_ctor_get(v_dt_1588_, 3);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_dt_1588_, 1);
lean_dec(v_unused_1658_);
v___x_1593_ = v_dt_1588_;
v_isShared_1594_ = v_isSharedCheck_1656_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_rules_1591_);
lean_inc(v_date_1590_);
lean_dec(v_dt_1588_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1656_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v_date_1595_; lean_object* v___y_1597_; lean_object* v_date_1627_; lean_object* v_month_1628_; lean_object* v_day_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1654_; 
v_date_1595_ = lean_thunk_get_own(v_date_1590_);
lean_dec_ref(v_date_1590_);
v_date_1627_ = lean_ctor_get(v_date_1595_, 0);
lean_inc_ref(v_date_1627_);
v_month_1628_ = lean_ctor_get(v_date_1627_, 1);
v_day_1629_ = lean_ctor_get(v_date_1627_, 2);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_date_1627_);
if (v_isSharedCheck_1654_ == 0)
{
lean_object* v_unused_1655_; 
v_unused_1655_ = lean_ctor_get(v_date_1627_, 0);
lean_dec(v_unused_1655_);
v___x_1631_ = v_date_1627_;
v_isShared_1632_ = v_isSharedCheck_1654_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_day_1629_);
lean_inc(v_month_1628_);
lean_dec(v_date_1627_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1654_;
goto v_resetjp_1630_;
}
v___jp_1596_:
{
lean_object* v_time_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1625_; 
v_time_1598_ = lean_ctor_get(v_date_1595_, 1);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_date_1595_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; 
v_unused_1626_ = lean_ctor_get(v_date_1595_, 0);
lean_dec(v_unused_1626_);
v___x_1600_ = v_date_1595_;
v_isShared_1601_ = v_isSharedCheck_1625_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_time_1598_);
lean_dec(v_date_1595_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1625_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___y_1597_);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___y_1597_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_time_1598_);
v___x_1603_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v_wt_1604_; lean_object* v_ltt_1605_; lean_object* v_tz_1606_; lean_object* v_offset_1607_; lean_object* v_second_1608_; lean_object* v_nano_1609_; lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_inc_ref(v___x_1603_);
v_wt_1604_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1603_);
lean_inc_ref(v_rules_1591_);
v_ltt_1605_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1591_, v_wt_1604_);
v_tz_1606_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1605_);
lean_dec_ref(v_ltt_1605_);
v_offset_1607_ = lean_ctor_get(v_tz_1606_, 0);
lean_inc(v_offset_1607_);
v_second_1608_ = lean_ctor_get(v_wt_1604_, 0);
lean_inc(v_second_1608_);
v_nano_1609_ = lean_ctor_get(v_wt_1604_, 1);
lean_inc(v_nano_1609_);
lean_dec_ref(v_wt_1604_);
v___f_1610_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1610_, 0, v___x_1603_);
v___x_1611_ = lean_mk_thunk(v___f_1610_);
v___x_1612_ = lean_int_neg(v_offset_1607_);
lean_dec(v_offset_1607_);
v___x_1613_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1614_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1615_ = lean_int_mul(v_second_1608_, v___x_1614_);
lean_dec(v_second_1608_);
v___x_1616_ = lean_int_add(v___x_1615_, v_nano_1609_);
lean_dec(v_nano_1609_);
lean_dec(v___x_1615_);
v___x_1617_ = lean_int_mul(v___x_1612_, v___x_1614_);
lean_dec(v___x_1612_);
v___x_1618_ = lean_int_add(v___x_1617_, v___x_1613_);
lean_dec(v___x_1617_);
v___x_1619_ = lean_int_add(v___x_1616_, v___x_1618_);
lean_dec(v___x_1618_);
lean_dec(v___x_1616_);
v___x_1620_ = l_Std_Time_Duration_ofNanoseconds(v___x_1619_);
lean_dec(v___x_1619_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 3, v_tz_1606_);
lean_ctor_set(v___x_1593_, 1, v___x_1620_);
lean_ctor_set(v___x_1593_, 0, v___x_1611_);
v___x_1622_ = v___x_1593_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1611_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_rules_1591_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_tz_1606_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
v_resetjp_1630_:
{
uint8_t v___y_1634_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; uint8_t v___x_1650_; 
v___x_1643_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1644_ = lean_int_mod(v_year_1589_, v___x_1643_);
v___x_1645_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1650_ = lean_int_dec_eq(v___x_1644_, v___x_1645_);
lean_dec(v___x_1644_);
if (v___x_1650_ == 0)
{
v___y_1634_ = v___x_1650_;
goto v___jp_1633_;
}
else
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1652_ = lean_int_mod(v_year_1589_, v___x_1651_);
v___x_1653_ = lean_int_dec_eq(v___x_1652_, v___x_1645_);
lean_dec(v___x_1652_);
if (v___x_1653_ == 0)
{
if (v___x_1650_ == 0)
{
goto v___jp_1646_;
}
else
{
v___y_1634_ = v___x_1650_;
goto v___jp_1633_;
}
}
else
{
goto v___jp_1646_;
}
}
v___jp_1633_:
{
lean_object* v_max_1635_; uint8_t v___x_1636_; 
v_max_1635_ = l_Std_Time_Month_Ordinal_days(v___y_1634_, v_month_1628_);
v___x_1636_ = lean_int_dec_lt(v_max_1635_, v_day_1629_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1638_; 
lean_dec(v_max_1635_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_year_1589_);
v___x_1638_ = v___x_1631_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_year_1589_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_month_1628_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_day_1629_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
v___y_1597_ = v___x_1638_;
goto v___jp_1596_;
}
}
else
{
lean_object* v___x_1641_; 
lean_dec(v_day_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 2, v_max_1635_);
lean_ctor_set(v___x_1631_, 0, v_year_1589_);
v___x_1641_ = v___x_1631_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_year_1589_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_month_1628_);
lean_ctor_set(v_reuseFailAlloc_1642_, 2, v_max_1635_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
v___y_1597_ = v___x_1641_;
goto v___jp_1596_;
}
}
}
v___jp_1646_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1647_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1648_ = lean_int_mod(v_year_1589_, v___x_1647_);
v___x_1649_ = lean_int_dec_eq(v___x_1648_, v___x_1645_);
lean_dec(v___x_1648_);
v___y_1634_ = v___x_1649_;
goto v___jp_1633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object* v_dt_1659_, lean_object* v_year_1660_){
_start:
{
lean_object* v_date_1661_; lean_object* v_rules_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1699_; 
v_date_1661_ = lean_ctor_get(v_dt_1659_, 0);
v_rules_1662_ = lean_ctor_get(v_dt_1659_, 2);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_dt_1659_);
if (v_isSharedCheck_1699_ == 0)
{
lean_object* v_unused_1700_; lean_object* v_unused_1701_; 
v_unused_1700_ = lean_ctor_get(v_dt_1659_, 3);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_dt_1659_, 1);
lean_dec(v_unused_1701_);
v___x_1664_ = v_dt_1659_;
v_isShared_1665_ = v_isSharedCheck_1699_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_rules_1662_);
lean_inc(v_date_1661_);
lean_dec(v_dt_1659_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1699_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_date_1666_; lean_object* v_date_1667_; lean_object* v_time_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1698_; 
v_date_1666_ = lean_thunk_get_own(v_date_1661_);
lean_dec_ref(v_date_1661_);
v_date_1667_ = lean_ctor_get(v_date_1666_, 0);
v_time_1668_ = lean_ctor_get(v_date_1666_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_date_1666_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1670_ = v_date_1666_;
v_isShared_1671_ = v_isSharedCheck_1698_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_time_1668_);
lean_inc(v_date_1667_);
lean_dec(v_date_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1698_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_month_1672_; lean_object* v_day_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
v_month_1672_ = lean_ctor_get(v_date_1667_, 1);
lean_inc(v_month_1672_);
v_day_1673_ = lean_ctor_get(v_date_1667_, 2);
lean_inc(v_day_1673_);
lean_dec_ref(v_date_1667_);
v___x_1674_ = l_Std_Time_PlainDate_rollOver(v_year_1660_, v_month_1672_, v_day_1673_);
lean_dec(v_day_1673_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1674_);
v___x_1676_ = v___x_1670_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_time_1668_);
v___x_1676_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v_wt_1677_; lean_object* v_ltt_1678_; lean_object* v_tz_1679_; lean_object* v_offset_1680_; lean_object* v_second_1681_; lean_object* v_nano_1682_; lean_object* v___f_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_inc_ref(v___x_1676_);
v_wt_1677_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1676_);
lean_inc_ref(v_rules_1662_);
v_ltt_1678_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1662_, v_wt_1677_);
v_tz_1679_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1678_);
lean_dec_ref(v_ltt_1678_);
v_offset_1680_ = lean_ctor_get(v_tz_1679_, 0);
lean_inc(v_offset_1680_);
v_second_1681_ = lean_ctor_get(v_wt_1677_, 0);
lean_inc(v_second_1681_);
v_nano_1682_ = lean_ctor_get(v_wt_1677_, 1);
lean_inc(v_nano_1682_);
lean_dec_ref(v_wt_1677_);
v___f_1683_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1683_, 0, v___x_1676_);
v___x_1684_ = lean_mk_thunk(v___f_1683_);
v___x_1685_ = lean_int_neg(v_offset_1680_);
lean_dec(v_offset_1680_);
v___x_1686_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1687_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1688_ = lean_int_mul(v_second_1681_, v___x_1687_);
lean_dec(v_second_1681_);
v___x_1689_ = lean_int_add(v___x_1688_, v_nano_1682_);
lean_dec(v_nano_1682_);
lean_dec(v___x_1688_);
v___x_1690_ = lean_int_mul(v___x_1685_, v___x_1687_);
lean_dec(v___x_1685_);
v___x_1691_ = lean_int_add(v___x_1690_, v___x_1686_);
lean_dec(v___x_1690_);
v___x_1692_ = lean_int_add(v___x_1689_, v___x_1691_);
lean_dec(v___x_1691_);
lean_dec(v___x_1689_);
v___x_1693_ = l_Std_Time_Duration_ofNanoseconds(v___x_1692_);
lean_dec(v___x_1692_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 3, v_tz_1679_);
lean_ctor_set(v___x_1664_, 1, v___x_1693_);
lean_ctor_set(v___x_1664_, 0, v___x_1684_);
v___x_1695_ = v___x_1664_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_rules_1662_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_tz_1679_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object* v_dt_1702_, lean_object* v_hour_1703_){
_start:
{
lean_object* v_date_1704_; lean_object* v_rules_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1750_; 
v_date_1704_ = lean_ctor_get(v_dt_1702_, 0);
v_rules_1705_ = lean_ctor_get(v_dt_1702_, 2);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_dt_1702_);
if (v_isSharedCheck_1750_ == 0)
{
lean_object* v_unused_1751_; lean_object* v_unused_1752_; 
v_unused_1751_ = lean_ctor_get(v_dt_1702_, 3);
lean_dec(v_unused_1751_);
v_unused_1752_ = lean_ctor_get(v_dt_1702_, 1);
lean_dec(v_unused_1752_);
v___x_1707_ = v_dt_1702_;
v_isShared_1708_ = v_isSharedCheck_1750_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_rules_1705_);
lean_inc(v_date_1704_);
lean_dec(v_dt_1702_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1750_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_date_1709_; lean_object* v_time_1710_; lean_object* v_date_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1749_; 
v_date_1709_ = lean_thunk_get_own(v_date_1704_);
lean_dec_ref(v_date_1704_);
v_time_1710_ = lean_ctor_get(v_date_1709_, 1);
v_date_1711_ = lean_ctor_get(v_date_1709_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_date_1709_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1713_ = v_date_1709_;
v_isShared_1714_ = v_isSharedCheck_1749_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_time_1710_);
lean_inc(v_date_1711_);
lean_dec(v_date_1709_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1749_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_minute_1715_; lean_object* v_second_1716_; lean_object* v_nanosecond_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1747_; 
v_minute_1715_ = lean_ctor_get(v_time_1710_, 1);
v_second_1716_ = lean_ctor_get(v_time_1710_, 2);
v_nanosecond_1717_ = lean_ctor_get(v_time_1710_, 3);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_time_1710_);
if (v_isSharedCheck_1747_ == 0)
{
lean_object* v_unused_1748_; 
v_unused_1748_ = lean_ctor_get(v_time_1710_, 0);
lean_dec(v_unused_1748_);
v___x_1719_ = v_time_1710_;
v_isShared_1720_ = v_isSharedCheck_1747_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_nanosecond_1717_);
lean_inc(v_second_1716_);
lean_inc(v_minute_1715_);
lean_dec(v_time_1710_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1747_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v_hour_1703_);
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_hour_1703_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_minute_1715_);
lean_ctor_set(v_reuseFailAlloc_1746_, 2, v_second_1716_);
lean_ctor_set(v_reuseFailAlloc_1746_, 3, v_nanosecond_1717_);
v___x_1722_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1724_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v___x_1722_);
v___x_1724_ = v___x_1713_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_date_1711_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v_wt_1725_; lean_object* v_ltt_1726_; lean_object* v_tz_1727_; lean_object* v_offset_1728_; lean_object* v_second_1729_; lean_object* v_nano_1730_; lean_object* v___f_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
lean_inc_ref(v___x_1724_);
v_wt_1725_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1724_);
lean_inc_ref(v_rules_1705_);
v_ltt_1726_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1705_, v_wt_1725_);
v_tz_1727_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1726_);
lean_dec_ref(v_ltt_1726_);
v_offset_1728_ = lean_ctor_get(v_tz_1727_, 0);
lean_inc(v_offset_1728_);
v_second_1729_ = lean_ctor_get(v_wt_1725_, 0);
lean_inc(v_second_1729_);
v_nano_1730_ = lean_ctor_get(v_wt_1725_, 1);
lean_inc(v_nano_1730_);
lean_dec_ref(v_wt_1725_);
v___f_1731_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1731_, 0, v___x_1724_);
v___x_1732_ = lean_mk_thunk(v___f_1731_);
v___x_1733_ = lean_int_neg(v_offset_1728_);
lean_dec(v_offset_1728_);
v___x_1734_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1735_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1736_ = lean_int_mul(v_second_1729_, v___x_1735_);
lean_dec(v_second_1729_);
v___x_1737_ = lean_int_add(v___x_1736_, v_nano_1730_);
lean_dec(v_nano_1730_);
lean_dec(v___x_1736_);
v___x_1738_ = lean_int_mul(v___x_1733_, v___x_1735_);
lean_dec(v___x_1733_);
v___x_1739_ = lean_int_add(v___x_1738_, v___x_1734_);
lean_dec(v___x_1738_);
v___x_1740_ = lean_int_add(v___x_1737_, v___x_1739_);
lean_dec(v___x_1739_);
lean_dec(v___x_1737_);
v___x_1741_ = l_Std_Time_Duration_ofNanoseconds(v___x_1740_);
lean_dec(v___x_1740_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 3, v_tz_1727_);
lean_ctor_set(v___x_1707_, 1, v___x_1741_);
lean_ctor_set(v___x_1707_, 0, v___x_1732_);
v___x_1743_ = v___x_1707_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_rules_1705_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v_tz_1727_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object* v_dt_1753_, lean_object* v_minute_1754_){
_start:
{
lean_object* v_date_1755_; lean_object* v_rules_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1801_; 
v_date_1755_ = lean_ctor_get(v_dt_1753_, 0);
v_rules_1756_ = lean_ctor_get(v_dt_1753_, 2);
v_isSharedCheck_1801_ = !lean_is_exclusive(v_dt_1753_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; lean_object* v_unused_1803_; 
v_unused_1802_ = lean_ctor_get(v_dt_1753_, 3);
lean_dec(v_unused_1802_);
v_unused_1803_ = lean_ctor_get(v_dt_1753_, 1);
lean_dec(v_unused_1803_);
v___x_1758_ = v_dt_1753_;
v_isShared_1759_ = v_isSharedCheck_1801_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_rules_1756_);
lean_inc(v_date_1755_);
lean_dec(v_dt_1753_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1801_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_date_1760_; lean_object* v_time_1761_; lean_object* v_date_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1800_; 
v_date_1760_ = lean_thunk_get_own(v_date_1755_);
lean_dec_ref(v_date_1755_);
v_time_1761_ = lean_ctor_get(v_date_1760_, 1);
v_date_1762_ = lean_ctor_get(v_date_1760_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_date_1760_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1764_ = v_date_1760_;
v_isShared_1765_ = v_isSharedCheck_1800_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_time_1761_);
lean_inc(v_date_1762_);
lean_dec(v_date_1760_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1800_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v_hour_1766_; lean_object* v_second_1767_; lean_object* v_nanosecond_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1798_; 
v_hour_1766_ = lean_ctor_get(v_time_1761_, 0);
v_second_1767_ = lean_ctor_get(v_time_1761_, 2);
v_nanosecond_1768_ = lean_ctor_get(v_time_1761_, 3);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_time_1761_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v_time_1761_, 1);
lean_dec(v_unused_1799_);
v___x_1770_ = v_time_1761_;
v_isShared_1771_ = v_isSharedCheck_1798_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_nanosecond_1768_);
lean_inc(v_second_1767_);
lean_inc(v_hour_1766_);
lean_dec(v_time_1761_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1798_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 1, v_minute_1754_);
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_hour_1766_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_minute_1754_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_second_1767_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_nanosecond_1768_);
v___x_1773_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
lean_object* v___x_1775_; 
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1773_);
v___x_1775_ = v___x_1764_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_date_1762_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v___x_1773_);
v___x_1775_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v_wt_1776_; lean_object* v_ltt_1777_; lean_object* v_tz_1778_; lean_object* v_offset_1779_; lean_object* v_second_1780_; lean_object* v_nano_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
lean_inc_ref(v___x_1775_);
v_wt_1776_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1775_);
lean_inc_ref(v_rules_1756_);
v_ltt_1777_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1756_, v_wt_1776_);
v_tz_1778_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1777_);
lean_dec_ref(v_ltt_1777_);
v_offset_1779_ = lean_ctor_get(v_tz_1778_, 0);
lean_inc(v_offset_1779_);
v_second_1780_ = lean_ctor_get(v_wt_1776_, 0);
lean_inc(v_second_1780_);
v_nano_1781_ = lean_ctor_get(v_wt_1776_, 1);
lean_inc(v_nano_1781_);
lean_dec_ref(v_wt_1776_);
v___f_1782_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1782_, 0, v___x_1775_);
v___x_1783_ = lean_mk_thunk(v___f_1782_);
v___x_1784_ = lean_int_neg(v_offset_1779_);
lean_dec(v_offset_1779_);
v___x_1785_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1786_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1787_ = lean_int_mul(v_second_1780_, v___x_1786_);
lean_dec(v_second_1780_);
v___x_1788_ = lean_int_add(v___x_1787_, v_nano_1781_);
lean_dec(v_nano_1781_);
lean_dec(v___x_1787_);
v___x_1789_ = lean_int_mul(v___x_1784_, v___x_1786_);
lean_dec(v___x_1784_);
v___x_1790_ = lean_int_add(v___x_1789_, v___x_1785_);
lean_dec(v___x_1789_);
v___x_1791_ = lean_int_add(v___x_1788_, v___x_1790_);
lean_dec(v___x_1790_);
lean_dec(v___x_1788_);
v___x_1792_ = l_Std_Time_Duration_ofNanoseconds(v___x_1791_);
lean_dec(v___x_1791_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 3, v_tz_1778_);
lean_ctor_set(v___x_1758_, 1, v___x_1792_);
lean_ctor_set(v___x_1758_, 0, v___x_1783_);
v___x_1794_ = v___x_1758_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1795_, 2, v_rules_1756_);
lean_ctor_set(v_reuseFailAlloc_1795_, 3, v_tz_1778_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object* v_dt_1804_, lean_object* v_second_1805_){
_start:
{
lean_object* v_date_1806_; lean_object* v_rules_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1852_; 
v_date_1806_ = lean_ctor_get(v_dt_1804_, 0);
v_rules_1807_ = lean_ctor_get(v_dt_1804_, 2);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_dt_1804_);
if (v_isSharedCheck_1852_ == 0)
{
lean_object* v_unused_1853_; lean_object* v_unused_1854_; 
v_unused_1853_ = lean_ctor_get(v_dt_1804_, 3);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v_dt_1804_, 1);
lean_dec(v_unused_1854_);
v___x_1809_ = v_dt_1804_;
v_isShared_1810_ = v_isSharedCheck_1852_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_rules_1807_);
lean_inc(v_date_1806_);
lean_dec(v_dt_1804_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1852_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_date_1811_; lean_object* v_time_1812_; lean_object* v_date_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1851_; 
v_date_1811_ = lean_thunk_get_own(v_date_1806_);
lean_dec_ref(v_date_1806_);
v_time_1812_ = lean_ctor_get(v_date_1811_, 1);
v_date_1813_ = lean_ctor_get(v_date_1811_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v_date_1811_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1815_ = v_date_1811_;
v_isShared_1816_ = v_isSharedCheck_1851_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_time_1812_);
lean_inc(v_date_1813_);
lean_dec(v_date_1811_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1851_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_hour_1817_; lean_object* v_minute_1818_; lean_object* v_nanosecond_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1849_; 
v_hour_1817_ = lean_ctor_get(v_time_1812_, 0);
v_minute_1818_ = lean_ctor_get(v_time_1812_, 1);
v_nanosecond_1819_ = lean_ctor_get(v_time_1812_, 3);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_time_1812_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v_time_1812_, 2);
lean_dec(v_unused_1850_);
v___x_1821_ = v_time_1812_;
v_isShared_1822_ = v_isSharedCheck_1849_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_nanosecond_1819_);
lean_inc(v_minute_1818_);
lean_inc(v_hour_1817_);
lean_dec(v_time_1812_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1849_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 2, v_second_1805_);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_hour_1817_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_minute_1818_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_second_1805_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_nanosecond_1819_);
v___x_1824_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 1, v___x_1824_);
v___x_1826_ = v___x_1815_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_date_1813_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v_wt_1827_; lean_object* v_ltt_1828_; lean_object* v_tz_1829_; lean_object* v_offset_1830_; lean_object* v_second_1831_; lean_object* v_nano_1832_; lean_object* v___f_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1845_; 
lean_inc_ref(v___x_1826_);
v_wt_1827_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1826_);
lean_inc_ref(v_rules_1807_);
v_ltt_1828_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1807_, v_wt_1827_);
v_tz_1829_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1828_);
lean_dec_ref(v_ltt_1828_);
v_offset_1830_ = lean_ctor_get(v_tz_1829_, 0);
lean_inc(v_offset_1830_);
v_second_1831_ = lean_ctor_get(v_wt_1827_, 0);
lean_inc(v_second_1831_);
v_nano_1832_ = lean_ctor_get(v_wt_1827_, 1);
lean_inc(v_nano_1832_);
lean_dec_ref(v_wt_1827_);
v___f_1833_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1833_, 0, v___x_1826_);
v___x_1834_ = lean_mk_thunk(v___f_1833_);
v___x_1835_ = lean_int_neg(v_offset_1830_);
lean_dec(v_offset_1830_);
v___x_1836_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1837_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1838_ = lean_int_mul(v_second_1831_, v___x_1837_);
lean_dec(v_second_1831_);
v___x_1839_ = lean_int_add(v___x_1838_, v_nano_1832_);
lean_dec(v_nano_1832_);
lean_dec(v___x_1838_);
v___x_1840_ = lean_int_mul(v___x_1835_, v___x_1837_);
lean_dec(v___x_1835_);
v___x_1841_ = lean_int_add(v___x_1840_, v___x_1836_);
lean_dec(v___x_1840_);
v___x_1842_ = lean_int_add(v___x_1839_, v___x_1841_);
lean_dec(v___x_1841_);
lean_dec(v___x_1839_);
v___x_1843_ = l_Std_Time_Duration_ofNanoseconds(v___x_1842_);
lean_dec(v___x_1842_);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 3, v_tz_1829_);
lean_ctor_set(v___x_1809_, 1, v___x_1843_);
lean_ctor_set(v___x_1809_, 0, v___x_1834_);
v___x_1845_ = v___x_1809_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1834_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_rules_1807_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_tz_1829_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Std_Time_DateTime_withMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_unsigned_to_nat(1000u);
v___x_1856_ = lean_nat_to_int(v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object* v_dt_1857_, lean_object* v_millis_1858_){
_start:
{
lean_object* v_date_1859_; lean_object* v_rules_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1910_; 
v_date_1859_ = lean_ctor_get(v_dt_1857_, 0);
v_rules_1860_ = lean_ctor_get(v_dt_1857_, 2);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_dt_1857_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; lean_object* v_unused_1912_; 
v_unused_1911_ = lean_ctor_get(v_dt_1857_, 3);
lean_dec(v_unused_1911_);
v_unused_1912_ = lean_ctor_get(v_dt_1857_, 1);
lean_dec(v_unused_1912_);
v___x_1862_ = v_dt_1857_;
v_isShared_1863_ = v_isSharedCheck_1910_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_rules_1860_);
lean_inc(v_date_1859_);
lean_dec(v_dt_1857_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1910_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_date_1864_; lean_object* v_time_1865_; lean_object* v_date_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1909_; 
v_date_1864_ = lean_thunk_get_own(v_date_1859_);
lean_dec_ref(v_date_1859_);
v_time_1865_ = lean_ctor_get(v_date_1864_, 1);
v_date_1866_ = lean_ctor_get(v_date_1864_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_date_1864_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1868_ = v_date_1864_;
v_isShared_1869_ = v_isSharedCheck_1909_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_time_1865_);
lean_inc(v_date_1866_);
lean_dec(v_date_1864_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1909_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v_hour_1870_; lean_object* v_minute_1871_; lean_object* v_second_1872_; lean_object* v_nanosecond_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1908_; 
v_hour_1870_ = lean_ctor_get(v_time_1865_, 0);
v_minute_1871_ = lean_ctor_get(v_time_1865_, 1);
v_second_1872_ = lean_ctor_get(v_time_1865_, 2);
v_nanosecond_1873_ = lean_ctor_get(v_time_1865_, 3);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_time_1865_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1875_ = v_time_1865_;
v_isShared_1876_ = v_isSharedCheck_1908_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_nanosecond_1873_);
lean_inc(v_second_1872_);
lean_inc(v_minute_1871_);
lean_inc(v_hour_1870_);
lean_dec(v_time_1865_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1908_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1877_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_1878_ = lean_int_emod(v_nanosecond_1873_, v___x_1877_);
lean_dec(v_nanosecond_1873_);
v___x_1879_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1880_ = lean_int_mul(v_millis_1858_, v___x_1879_);
v___x_1881_ = lean_int_add(v___x_1880_, v___x_1878_);
lean_dec(v___x_1878_);
lean_dec(v___x_1880_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 3, v___x_1881_);
v___x_1883_ = v___x_1875_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_hour_1870_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_minute_1871_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v_second_1872_);
lean_ctor_set(v_reuseFailAlloc_1907_, 3, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___x_1883_);
v___x_1885_ = v___x_1868_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_date_1866_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v_wt_1886_; lean_object* v_ltt_1887_; lean_object* v_tz_1888_; lean_object* v_offset_1889_; lean_object* v_second_1890_; lean_object* v_nano_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
lean_inc_ref(v___x_1885_);
v_wt_1886_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1885_);
lean_inc_ref(v_rules_1860_);
v_ltt_1887_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1860_, v_wt_1886_);
v_tz_1888_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1887_);
lean_dec_ref(v_ltt_1887_);
v_offset_1889_ = lean_ctor_get(v_tz_1888_, 0);
lean_inc(v_offset_1889_);
v_second_1890_ = lean_ctor_get(v_wt_1886_, 0);
lean_inc(v_second_1890_);
v_nano_1891_ = lean_ctor_get(v_wt_1886_, 1);
lean_inc(v_nano_1891_);
lean_dec_ref(v_wt_1886_);
v___f_1892_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1892_, 0, v___x_1885_);
v___x_1893_ = lean_mk_thunk(v___f_1892_);
v___x_1894_ = lean_int_neg(v_offset_1889_);
lean_dec(v_offset_1889_);
v___x_1895_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1896_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1897_ = lean_int_mul(v_second_1890_, v___x_1896_);
lean_dec(v_second_1890_);
v___x_1898_ = lean_int_add(v___x_1897_, v_nano_1891_);
lean_dec(v_nano_1891_);
lean_dec(v___x_1897_);
v___x_1899_ = lean_int_mul(v___x_1894_, v___x_1896_);
lean_dec(v___x_1894_);
v___x_1900_ = lean_int_add(v___x_1899_, v___x_1895_);
lean_dec(v___x_1899_);
v___x_1901_ = lean_int_add(v___x_1898_, v___x_1900_);
lean_dec(v___x_1900_);
lean_dec(v___x_1898_);
v___x_1902_ = l_Std_Time_Duration_ofNanoseconds(v___x_1901_);
lean_dec(v___x_1901_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 3, v_tz_1888_);
lean_ctor_set(v___x_1862_, 1, v___x_1902_);
lean_ctor_set(v___x_1862_, 0, v___x_1893_);
v___x_1904_ = v___x_1862_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v_rules_1860_);
lean_ctor_set(v_reuseFailAlloc_1905_, 3, v_tz_1888_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object* v_dt_1913_, lean_object* v_millis_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Std_Time_DateTime_withMilliseconds(v_dt_1913_, v_millis_1914_);
lean_dec(v_millis_1914_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object* v_dt_1916_, lean_object* v_nano_1917_){
_start:
{
lean_object* v_date_1918_; lean_object* v_rules_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1964_; 
v_date_1918_ = lean_ctor_get(v_dt_1916_, 0);
v_rules_1919_ = lean_ctor_get(v_dt_1916_, 2);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_dt_1916_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; lean_object* v_unused_1966_; 
v_unused_1965_ = lean_ctor_get(v_dt_1916_, 3);
lean_dec(v_unused_1965_);
v_unused_1966_ = lean_ctor_get(v_dt_1916_, 1);
lean_dec(v_unused_1966_);
v___x_1921_ = v_dt_1916_;
v_isShared_1922_ = v_isSharedCheck_1964_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_rules_1919_);
lean_inc(v_date_1918_);
lean_dec(v_dt_1916_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1964_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v_date_1923_; lean_object* v_time_1924_; lean_object* v_date_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1963_; 
v_date_1923_ = lean_thunk_get_own(v_date_1918_);
lean_dec_ref(v_date_1918_);
v_time_1924_ = lean_ctor_get(v_date_1923_, 1);
v_date_1925_ = lean_ctor_get(v_date_1923_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_date_1923_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1927_ = v_date_1923_;
v_isShared_1928_ = v_isSharedCheck_1963_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_time_1924_);
lean_inc(v_date_1925_);
lean_dec(v_date_1923_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1963_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_hour_1929_; lean_object* v_minute_1930_; lean_object* v_second_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1961_; 
v_hour_1929_ = lean_ctor_get(v_time_1924_, 0);
v_minute_1930_ = lean_ctor_get(v_time_1924_, 1);
v_second_1931_ = lean_ctor_get(v_time_1924_, 2);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_time_1924_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v_time_1924_, 3);
lean_dec(v_unused_1962_);
v___x_1933_ = v_time_1924_;
v_isShared_1934_ = v_isSharedCheck_1961_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_second_1931_);
lean_inc(v_minute_1930_);
lean_inc(v_hour_1929_);
lean_dec(v_time_1924_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1961_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 3, v_nano_1917_);
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_hour_1929_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_minute_1930_);
lean_ctor_set(v_reuseFailAlloc_1960_, 2, v_second_1931_);
lean_ctor_set(v_reuseFailAlloc_1960_, 3, v_nano_1917_);
v___x_1936_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1938_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v___x_1936_);
v___x_1938_ = v___x_1927_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_date_1925_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v_wt_1939_; lean_object* v_ltt_1940_; lean_object* v_tz_1941_; lean_object* v_offset_1942_; lean_object* v_second_1943_; lean_object* v_nano_1944_; lean_object* v___f_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_inc_ref(v___x_1938_);
v_wt_1939_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1938_);
lean_inc_ref(v_rules_1919_);
v_ltt_1940_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1919_, v_wt_1939_);
v_tz_1941_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1940_);
lean_dec_ref(v_ltt_1940_);
v_offset_1942_ = lean_ctor_get(v_tz_1941_, 0);
lean_inc(v_offset_1942_);
v_second_1943_ = lean_ctor_get(v_wt_1939_, 0);
lean_inc(v_second_1943_);
v_nano_1944_ = lean_ctor_get(v_wt_1939_, 1);
lean_inc(v_nano_1944_);
lean_dec_ref(v_wt_1939_);
v___f_1945_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1945_, 0, v___x_1938_);
v___x_1946_ = lean_mk_thunk(v___f_1945_);
v___x_1947_ = lean_int_neg(v_offset_1942_);
lean_dec(v_offset_1942_);
v___x_1948_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1949_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1950_ = lean_int_mul(v_second_1943_, v___x_1949_);
lean_dec(v_second_1943_);
v___x_1951_ = lean_int_add(v___x_1950_, v_nano_1944_);
lean_dec(v_nano_1944_);
lean_dec(v___x_1950_);
v___x_1952_ = lean_int_mul(v___x_1947_, v___x_1949_);
lean_dec(v___x_1947_);
v___x_1953_ = lean_int_add(v___x_1952_, v___x_1948_);
lean_dec(v___x_1952_);
v___x_1954_ = lean_int_add(v___x_1951_, v___x_1953_);
lean_dec(v___x_1953_);
lean_dec(v___x_1951_);
v___x_1955_ = l_Std_Time_Duration_ofNanoseconds(v___x_1954_);
lean_dec(v___x_1954_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 3, v_tz_1941_);
lean_ctor_set(v___x_1921_, 1, v___x_1955_);
lean_ctor_set(v___x_1921_, 0, v___x_1946_);
v___x_1957_ = v___x_1921_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_rules_1919_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v_tz_1941_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object* v_date_1967_){
_start:
{
lean_object* v_date_1968_; lean_object* v___x_1969_; lean_object* v_date_1970_; lean_object* v_year_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1979_; 
v_date_1968_ = lean_ctor_get(v_date_1967_, 0);
v___x_1969_ = lean_thunk_get_own(v_date_1968_);
v_date_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc_ref(v_date_1970_);
lean_dec(v___x_1969_);
v_year_1971_ = lean_ctor_get(v_date_1970_, 0);
lean_inc(v_year_1971_);
lean_dec_ref(v_date_1970_);
v___x_1972_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1973_ = lean_int_mod(v_year_1971_, v___x_1972_);
v___x_1974_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1979_ = lean_int_dec_eq(v___x_1973_, v___x_1974_);
lean_dec(v___x_1973_);
if (v___x_1979_ == 0)
{
lean_dec(v_year_1971_);
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1980_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1981_ = lean_int_mod(v_year_1971_, v___x_1980_);
v___x_1982_ = lean_int_dec_eq(v___x_1981_, v___x_1974_);
lean_dec(v___x_1981_);
if (v___x_1982_ == 0)
{
if (v___x_1979_ == 0)
{
goto v___jp_1975_;
}
else
{
lean_dec(v_year_1971_);
return v___x_1979_;
}
}
else
{
goto v___jp_1975_;
}
}
v___jp_1975_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1976_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1977_ = lean_int_mod(v_year_1971_, v___x_1976_);
lean_dec(v_year_1971_);
v___x_1978_ = lean_int_dec_eq(v___x_1977_, v___x_1974_);
lean_dec(v___x_1977_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object* v_date_1983_){
_start:
{
uint8_t v_res_1984_; lean_object* v_r_1985_; 
v_res_1984_ = l_Std_Time_DateTime_inLeapYear(v_date_1983_);
lean_dec_ref(v_date_1983_);
v_r_1985_ = lean_box(v_res_1984_);
return v_r_1985_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay(lean_object* v_date_1986_){
_start:
{
lean_object* v_date_1987_; lean_object* v___x_1988_; lean_object* v_date_1989_; lean_object* v___x_1990_; 
v_date_1987_ = lean_ctor_get(v_date_1986_, 0);
v___x_1988_ = lean_thunk_get_own(v_date_1987_);
v_date_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc_ref(v_date_1989_);
lean_dec(v___x_1988_);
v___x_1990_ = l_Std_Time_PlainDate_toEpochDay(v_date_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___boxed(lean_object* v_date_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Std_Time_DateTime_toEpochDay(v_date_1991_);
lean_dec_ref(v_date_1991_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay(lean_object* v_days_1993_, lean_object* v_time_1994_, lean_object* v_zt_1995_){
_start:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_wt_1998_; lean_object* v_ltt_1999_; lean_object* v_tz_2000_; lean_object* v_offset_2001_; lean_object* v_second_2002_; lean_object* v_nano_2003_; lean_object* v___f_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_1996_ = l_Std_Time_PlainDate_ofEpochDay(v_days_1993_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v_time_1994_);
lean_inc_ref(v___x_1997_);
v_wt_1998_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1997_);
lean_inc_ref(v_zt_1995_);
v_ltt_1999_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zt_1995_, v_wt_1998_);
v_tz_2000_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1999_);
lean_dec_ref(v_ltt_1999_);
v_offset_2001_ = lean_ctor_get(v_tz_2000_, 0);
lean_inc(v_offset_2001_);
v_second_2002_ = lean_ctor_get(v_wt_1998_, 0);
lean_inc(v_second_2002_);
v_nano_2003_ = lean_ctor_get(v_wt_1998_, 1);
lean_inc(v_nano_2003_);
lean_dec_ref(v_wt_1998_);
v___f_2004_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2004_, 0, v___x_1997_);
v___x_2005_ = lean_mk_thunk(v___f_2004_);
v___x_2006_ = lean_int_neg(v_offset_2001_);
lean_dec(v_offset_2001_);
v___x_2007_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_2008_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_2009_ = lean_int_mul(v_second_2002_, v___x_2008_);
lean_dec(v_second_2002_);
v___x_2010_ = lean_int_add(v___x_2009_, v_nano_2003_);
lean_dec(v_nano_2003_);
lean_dec(v___x_2009_);
v___x_2011_ = lean_int_mul(v___x_2006_, v___x_2008_);
lean_dec(v___x_2006_);
v___x_2012_ = lean_int_add(v___x_2011_, v___x_2007_);
lean_dec(v___x_2011_);
v___x_2013_ = lean_int_add(v___x_2010_, v___x_2012_);
lean_dec(v___x_2012_);
lean_dec(v___x_2010_);
v___x_2014_ = l_Std_Time_Duration_ofNanoseconds(v___x_2013_);
lean_dec(v___x_2013_);
v___x_2015_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2005_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
lean_ctor_set(v___x_2015_, 2, v_zt_1995_);
lean_ctor_set(v___x_2015_, 3, v_tz_2000_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay___boxed(lean_object* v_days_2016_, lean_object* v_time_2017_, lean_object* v_zt_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Std_Time_DateTime_ofEpochDay(v_days_2016_, v_time_2017_, v_zt_2018_);
lean_dec(v_days_2016_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object* v_x_2048_, lean_object* v_y_2049_){
_start:
{
lean_object* v_timestamp_2050_; lean_object* v_timestamp_2051_; lean_object* v_second_2052_; lean_object* v_nano_2053_; lean_object* v_second_2054_; lean_object* v_nano_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v_timestamp_2050_ = lean_ctor_get(v_y_2049_, 1);
v_timestamp_2051_ = lean_ctor_get(v_x_2048_, 1);
v_second_2052_ = lean_ctor_get(v_timestamp_2050_, 0);
v_nano_2053_ = lean_ctor_get(v_timestamp_2050_, 1);
v_second_2054_ = lean_ctor_get(v_timestamp_2051_, 0);
v_nano_2055_ = lean_ctor_get(v_timestamp_2051_, 1);
v___x_2056_ = lean_int_neg(v_second_2052_);
v___x_2057_ = lean_int_neg(v_nano_2053_);
v___x_2058_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_2059_ = lean_int_mul(v_second_2054_, v___x_2058_);
v___x_2060_ = lean_int_add(v___x_2059_, v_nano_2055_);
lean_dec(v___x_2059_);
v___x_2061_ = lean_int_mul(v___x_2056_, v___x_2058_);
lean_dec(v___x_2056_);
v___x_2062_ = lean_int_add(v___x_2061_, v___x_2057_);
lean_dec(v___x_2057_);
lean_dec(v___x_2061_);
v___x_2063_ = lean_int_add(v___x_2060_, v___x_2062_);
lean_dec(v___x_2062_);
lean_dec(v___x_2060_);
v___x_2064_ = l_Std_Time_Duration_ofNanoseconds(v___x_2063_);
lean_dec(v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object* v_x_2065_, lean_object* v_y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Std_Time_DateTime_instHSubDuration___lam__0(v_x_2065_, v_y_2066_);
lean_dec_ref(v_y_2066_);
lean_dec_ref(v_x_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0(lean_object* v_x_2070_, lean_object* v_y_2071_){
_start:
{
lean_object* v_second_2072_; lean_object* v_nano_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v_nanos_2076_; lean_object* v___x_2077_; 
v_second_2072_ = lean_ctor_get(v_y_2071_, 0);
v_nano_2073_ = lean_ctor_get(v_y_2071_, 1);
v___x_2074_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_2075_ = lean_int_mul(v_second_2072_, v___x_2074_);
v_nanos_2076_ = lean_int_add(v___x_2075_, v_nano_2073_);
lean_dec(v___x_2075_);
v___x_2077_ = l_Std_Time_DateTime_addNanoseconds(v_x_2070_, v_nanos_2076_);
lean_dec(v_nanos_2076_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_2078_, lean_object* v_y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Std_Time_DateTime_instHAddDuration___lam__0(v_x_2078_, v_y_2079_);
lean_dec_ref(v_y_2079_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0(lean_object* v_x_2083_, lean_object* v_y_2084_){
_start:
{
lean_object* v_second_2085_; lean_object* v_nano_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_nanos_2089_; lean_object* v___x_2090_; 
v_second_2085_ = lean_ctor_get(v_y_2084_, 0);
v_nano_2086_ = lean_ctor_get(v_y_2084_, 1);
v___x_2087_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_2088_ = lean_int_mul(v_second_2085_, v___x_2087_);
v_nanos_2089_ = lean_int_add(v___x_2088_, v_nano_2086_);
lean_dec(v___x_2088_);
v___x_2090_ = l_Std_Time_DateTime_subNanoseconds(v_x_2083_, v_nanos_2089_);
lean_dec(v_nanos_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0___boxed(lean_object* v_x_2091_, lean_object* v_y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Std_Time_DateTime_instHSubDuration__1___lam__0(v_x_2091_, v_y_2092_);
lean_dec_ref(v_y_2092_);
return v_res_2093_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedDateTime___private__1 = _init_l_Std_Time_instInhabitedDateTime___private__1();
lean_mark_persistent(l_Std_Time_instInhabitedDateTime___private__1);
l_Std_Time_instInhabitedDateTime = _init_l_Std_Time_instInhabitedDateTime();
lean_mark_persistent(l_Std_Time_instInhabitedDateTime);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_ZoneRules(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_DateTime(builtin);
}
#ifdef __cplusplus
}
#endif

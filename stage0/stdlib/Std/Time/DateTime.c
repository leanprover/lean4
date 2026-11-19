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
lean_object* l_Std_Time_TimeZone_ZoneRules_timezoneAt(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
extern lean_object* l_Std_Time_instInhabitedPlainDateTime_default;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDate_toEpochDay(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_addMonthsRollOver(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_addMonthsClip(lean_object*, lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_rollOver(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*, uint8_t);
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
lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0(lean_object* v_tz_17_, lean_object* v_tm_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_offset_20_; lean_object* v_second_21_; lean_object* v_nano_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_nanos_26_; lean_object* v___x_27_; lean_object* v_nanos_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_offset_20_ = lean_ctor_get(v_tz_17_, 0);
v_second_21_ = lean_ctor_get(v_tm_18_, 0);
v_nano_22_ = lean_ctor_get(v_tm_18_, 1);
v___x_23_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_24_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_25_ = lean_int_mul(v_second_21_, v___x_24_);
v_nanos_26_ = lean_int_add(v___x_25_, v_nano_22_);
lean_dec(v___x_25_);
v___x_27_ = lean_int_mul(v_offset_20_, v___x_24_);
v_nanos_28_ = lean_int_add(v___x_27_, v___x_23_);
lean_dec(v___x_27_);
v___x_29_ = lean_int_add(v_nanos_26_, v_nanos_28_);
lean_dec(v_nanos_28_);
lean_dec(v_nanos_26_);
v___x_30_ = l_Std_Time_Duration_ofNanoseconds(v___x_29_);
lean_dec(v___x_29_);
v___x_31_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(lean_object* v_tz_32_, lean_object* v_tm_33_, lean_object* v_x_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Time_DateTime_ofTimestamp___lam__0(v_tz_32_, v_tm_33_, v_x_34_);
lean_dec_ref(v_tm_33_);
lean_dec_ref(v_tz_32_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestamp(lean_object* v_tm_36_, lean_object* v_rules_37_){
_start:
{
lean_object* v_tz_38_; lean_object* v___f_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
lean_inc_ref(v_rules_37_);
v_tz_38_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_37_, v_tm_36_);
lean_inc_ref(v_tm_36_);
lean_inc_ref(v_tz_38_);
v___f_39_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestamp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_39_, 0, v_tz_38_);
lean_closure_set(v___f_39_, 1, v_tm_36_);
v___x_40_ = lean_mk_thunk(v___f_39_);
v___x_41_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
lean_ctor_set(v___x_41_, 1, v_tm_36_);
lean_ctor_set(v___x_41_, 2, v_rules_37_);
lean_ctor_set(v___x_41_, 3, v_tz_38_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0(lean_object* v_pdt_42_, lean_object* v_x_43_){
_start:
{
lean_inc_ref(v_pdt_42_);
return v_pdt_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(lean_object* v_pdt_44_, lean_object* v_x_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_Time_DateTime_ofPlainDateTime___lam__0(v_pdt_44_, v_x_45_);
lean_dec_ref(v_pdt_44_);
return v_res_46_;
}
}
static lean_object* _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_48_ = lean_int_neg(v___x_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTime(lean_object* v_pdt_49_, lean_object* v_zr_50_){
_start:
{
lean_object* v_wt_51_; lean_object* v_ltt_52_; lean_object* v_tz_53_; lean_object* v_offset_54_; lean_object* v_second_55_; lean_object* v_nano_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v_nanos_63_; lean_object* v___x_64_; lean_object* v_nanos_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
lean_inc_ref(v_pdt_49_);
v_wt_51_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_49_);
lean_inc_ref(v_zr_50_);
v_ltt_52_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_50_, v_wt_51_);
v_tz_53_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_52_);
lean_dec_ref(v_ltt_52_);
v_offset_54_ = lean_ctor_get(v_tz_53_, 0);
v_second_55_ = lean_ctor_get(v_wt_51_, 0);
lean_inc(v_second_55_);
v_nano_56_ = lean_ctor_get(v_wt_51_, 1);
lean_inc(v_nano_56_);
lean_dec_ref(v_wt_51_);
v___f_57_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed), 2, 1);
lean_closure_set(v___f_57_, 0, v_pdt_49_);
v___x_58_ = lean_mk_thunk(v___f_57_);
v___x_59_ = lean_int_neg(v_offset_54_);
v___x_60_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_61_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_62_ = lean_int_mul(v_second_55_, v___x_61_);
lean_dec(v_second_55_);
v_nanos_63_ = lean_int_add(v___x_62_, v_nano_56_);
lean_dec(v_nano_56_);
lean_dec(v___x_62_);
v___x_64_ = lean_int_mul(v___x_59_, v___x_61_);
lean_dec(v___x_59_);
v_nanos_65_ = lean_int_add(v___x_64_, v___x_60_);
lean_dec(v___x_64_);
v___x_66_ = lean_int_add(v_nanos_63_, v_nanos_65_);
lean_dec(v_nanos_65_);
lean_dec(v_nanos_63_);
v___x_67_ = l_Std_Time_Duration_ofNanoseconds(v___x_66_);
lean_dec(v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_68_, 0, v___x_58_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
lean_ctor_set(v___x_68_, 2, v_zr_50_);
lean_ctor_set(v___x_68_, 3, v_tz_53_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone___lam__0(lean_object* v_tz_69_, lean_object* v_tm_70_, lean_object* v___x_71_, lean_object* v_x_72_){
_start:
{
lean_object* v_offset_73_; lean_object* v_second_74_; lean_object* v_nano_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v_nanos_79_; lean_object* v___x_80_; lean_object* v_nanos_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_offset_73_ = lean_ctor_get(v_tz_69_, 0);
v_second_74_ = lean_ctor_get(v_tm_70_, 0);
v_nano_75_ = lean_ctor_get(v_tm_70_, 1);
v___x_76_ = lean_nat_to_int(v___x_71_);
v___x_77_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_78_ = lean_int_mul(v_second_74_, v___x_77_);
v_nanos_79_ = lean_int_add(v___x_78_, v_nano_75_);
lean_dec(v___x_78_);
v___x_80_ = lean_int_mul(v_offset_73_, v___x_77_);
v_nanos_81_ = lean_int_add(v___x_80_, v___x_76_);
lean_dec(v___x_76_);
lean_dec(v___x_80_);
v___x_82_ = lean_int_add(v_nanos_79_, v_nanos_81_);
lean_dec(v_nanos_81_);
lean_dec(v_nanos_79_);
v___x_83_ = l_Std_Time_Duration_ofNanoseconds(v___x_82_);
lean_dec(v___x_82_);
v___x_84_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone___lam__0___boxed(lean_object* v_tz_85_, lean_object* v_tm_86_, lean_object* v___x_87_, lean_object* v_x_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Std_Time_DateTime_ofTimestampWithZone___lam__0(v_tz_85_, v_tm_86_, v___x_87_, v_x_88_);
lean_dec_ref(v_tm_86_);
lean_dec_ref(v_tz_85_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone(lean_object* v_tm_92_, lean_object* v_tz_93_){
_start:
{
lean_object* v_offset_94_; lean_object* v_name_95_; lean_object* v_abbreviation_96_; uint8_t v_isDST_97_; uint8_t v___x_98_; uint8_t v___x_99_; lean_object* v_ltt_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_tz_105_; lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_offset_94_ = lean_ctor_get(v_tz_93_, 0);
v_name_95_ = lean_ctor_get(v_tz_93_, 1);
v_abbreviation_96_ = lean_ctor_get(v_tz_93_, 2);
v_isDST_97_ = lean_ctor_get_uint8(v_tz_93_, sizeof(void*)*3);
v___x_98_ = 0;
v___x_99_ = 1;
lean_inc_ref(v_name_95_);
lean_inc_ref(v_abbreviation_96_);
lean_inc(v_offset_94_);
v_ltt_100_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_100_, 0, v_offset_94_);
lean_ctor_set(v_ltt_100_, 1, v_abbreviation_96_);
lean_ctor_set(v_ltt_100_, 2, v_name_95_);
lean_ctor_set_uint8(v_ltt_100_, sizeof(void*)*3, v_isDST_97_);
lean_ctor_set_uint8(v_ltt_100_, sizeof(void*)*3 + 1, v___x_98_);
lean_ctor_set_uint8(v_ltt_100_, sizeof(void*)*3 + 2, v___x_99_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = ((lean_object*)(l_Std_Time_DateTime_ofTimestampWithZone___closed__0));
v___x_103_ = lean_box(0);
v___x_104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_104_, 0, v_ltt_100_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
lean_inc_ref(v___x_104_);
v_tz_105_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v___x_104_, v_tm_92_);
lean_inc_ref(v_tm_92_);
lean_inc_ref(v_tz_105_);
v___f_106_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofTimestampWithZone___lam__0___boxed), 4, 3);
lean_closure_set(v___f_106_, 0, v_tz_105_);
lean_closure_set(v___f_106_, 1, v_tm_92_);
lean_closure_set(v___f_106_, 2, v___x_101_);
v___x_107_ = lean_mk_thunk(v___f_106_);
v___x_108_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_tm_92_);
lean_ctor_set(v___x_108_, 2, v___x_104_);
lean_ctor_set(v___x_108_, 3, v_tz_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofTimestampWithZone___boxed(lean_object* v_tm_109_, lean_object* v_tz_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_Time_DateTime_ofTimestampWithZone(v_tm_109_, v_tz_110_);
lean_dec_ref(v_tz_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0(lean_object* v_tm_112_, lean_object* v_x_113_){
_start:
{
lean_inc_ref(v_tm_112_);
return v_tm_112_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0___boxed(lean_object* v_tm_114_, lean_object* v_x_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0(v_tm_114_, v_x_115_);
lean_dec_ref(v_tm_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone(lean_object* v_tm_117_, lean_object* v_tz_118_){
_start:
{
lean_object* v_offset_119_; lean_object* v_name_120_; lean_object* v_abbreviation_121_; uint8_t v_isDST_122_; uint8_t v___x_123_; uint8_t v___x_124_; lean_object* v_ltt_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_wt_129_; lean_object* v_ltt_130_; lean_object* v_tz_131_; lean_object* v_offset_132_; lean_object* v_second_133_; lean_object* v_nano_134_; lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_nanos_141_; lean_object* v___x_142_; lean_object* v_nanos_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_offset_119_ = lean_ctor_get(v_tz_118_, 0);
v_name_120_ = lean_ctor_get(v_tz_118_, 1);
v_abbreviation_121_ = lean_ctor_get(v_tz_118_, 2);
v_isDST_122_ = lean_ctor_get_uint8(v_tz_118_, sizeof(void*)*3);
v___x_123_ = 0;
v___x_124_ = 1;
lean_inc_ref(v_name_120_);
lean_inc_ref(v_abbreviation_121_);
lean_inc(v_offset_119_);
v_ltt_125_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_125_, 0, v_offset_119_);
lean_ctor_set(v_ltt_125_, 1, v_abbreviation_121_);
lean_ctor_set(v_ltt_125_, 2, v_name_120_);
lean_ctor_set_uint8(v_ltt_125_, sizeof(void*)*3, v_isDST_122_);
lean_ctor_set_uint8(v_ltt_125_, sizeof(void*)*3 + 1, v___x_123_);
lean_ctor_set_uint8(v_ltt_125_, sizeof(void*)*3 + 2, v___x_124_);
v___x_126_ = ((lean_object*)(l_Std_Time_DateTime_ofTimestampWithZone___closed__0));
v___x_127_ = lean_box(0);
v___x_128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_128_, 0, v_ltt_125_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
lean_ctor_set(v___x_128_, 2, v___x_127_);
lean_inc_ref(v_tm_117_);
v_wt_129_ = l_Std_Time_PlainDateTime_toWallTime(v_tm_117_);
lean_inc_ref(v___x_128_);
v_ltt_130_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_128_, v_wt_129_);
v_tz_131_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_130_);
lean_dec_ref(v_ltt_130_);
v_offset_132_ = lean_ctor_get(v_tz_131_, 0);
v_second_133_ = lean_ctor_get(v_wt_129_, 0);
lean_inc(v_second_133_);
v_nano_134_ = lean_ctor_get(v_wt_129_, 1);
lean_inc(v_nano_134_);
lean_dec_ref(v_wt_129_);
v___f_135_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0___boxed), 2, 1);
lean_closure_set(v___f_135_, 0, v_tm_117_);
v___x_136_ = lean_mk_thunk(v___f_135_);
v___x_137_ = lean_int_neg(v_offset_132_);
v___x_138_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_139_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_140_ = lean_int_mul(v_second_133_, v___x_139_);
lean_dec(v_second_133_);
v_nanos_141_ = lean_int_add(v___x_140_, v_nano_134_);
lean_dec(v_nano_134_);
lean_dec(v___x_140_);
v___x_142_ = lean_int_mul(v___x_137_, v___x_139_);
lean_dec(v___x_137_);
v_nanos_143_ = lean_int_add(v___x_142_, v___x_138_);
lean_dec(v___x_142_);
v___x_144_ = lean_int_add(v_nanos_141_, v_nanos_143_);
lean_dec(v_nanos_143_);
lean_dec(v_nanos_141_);
v___x_145_ = l_Std_Time_Duration_ofNanoseconds(v___x_144_);
lean_dec(v___x_144_);
v___x_146_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_146_, 0, v___x_136_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
lean_ctor_set(v___x_146_, 2, v___x_128_);
lean_ctor_set(v___x_146_, 3, v_tz_131_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofPlainDateTimeWithZone___boxed(lean_object* v_tm_147_, lean_object* v_tz_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_Time_DateTime_ofPlainDateTimeWithZone(v_tm_147_, v_tz_148_);
lean_dec_ref(v_tz_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp(lean_object* v_date_150_){
_start:
{
lean_object* v_timestamp_151_; 
v_timestamp_151_ = lean_ctor_get(v_date_150_, 1);
lean_inc_ref(v_timestamp_151_);
return v_timestamp_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toTimestamp___boxed(lean_object* v_date_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Time_DateTime_toTimestamp(v_date_152_);
lean_dec_ref(v_date_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertZoneRules___lam__0(lean_object* v_tz_154_, lean_object* v_timestamp_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_offset_157_; lean_object* v_second_158_; lean_object* v_nano_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_nanos_163_; lean_object* v___x_164_; lean_object* v_nanos_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_offset_157_ = lean_ctor_get(v_tz_154_, 0);
v_second_158_ = lean_ctor_get(v_timestamp_155_, 0);
v_nano_159_ = lean_ctor_get(v_timestamp_155_, 1);
v___x_160_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_161_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_162_ = lean_int_mul(v_second_158_, v___x_161_);
v_nanos_163_ = lean_int_add(v___x_162_, v_nano_159_);
lean_dec(v___x_162_);
v___x_164_ = lean_int_mul(v_offset_157_, v___x_161_);
v_nanos_165_ = lean_int_add(v___x_164_, v___x_160_);
lean_dec(v___x_164_);
v___x_166_ = lean_int_add(v_nanos_163_, v_nanos_165_);
lean_dec(v_nanos_165_);
lean_dec(v_nanos_163_);
v___x_167_ = l_Std_Time_Duration_ofNanoseconds(v___x_166_);
lean_dec(v___x_166_);
v___x_168_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertZoneRules___lam__0___boxed(lean_object* v_tz_169_, lean_object* v_timestamp_170_, lean_object* v_x_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_Time_DateTime_convertZoneRules___lam__0(v_tz_169_, v_timestamp_170_, v_x_171_);
lean_dec_ref(v_timestamp_170_);
lean_dec_ref(v_tz_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_convertZoneRules(lean_object* v_date_173_, lean_object* v_tz_u2081_174_){
_start:
{
lean_object* v_timestamp_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_185_; 
v_timestamp_175_ = lean_ctor_get(v_date_173_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_date_173_);
if (v_isSharedCheck_185_ == 0)
{
lean_object* v_unused_186_; lean_object* v_unused_187_; lean_object* v_unused_188_; 
v_unused_186_ = lean_ctor_get(v_date_173_, 3);
lean_dec(v_unused_186_);
v_unused_187_ = lean_ctor_get(v_date_173_, 2);
lean_dec(v_unused_187_);
v_unused_188_ = lean_ctor_get(v_date_173_, 0);
lean_dec(v_unused_188_);
v___x_177_ = v_date_173_;
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_timestamp_175_);
lean_dec(v_date_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v_tz_179_; lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
lean_inc_ref(v_tz_u2081_174_);
v_tz_179_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_tz_u2081_174_, v_timestamp_175_);
lean_inc_ref(v_timestamp_175_);
lean_inc_ref(v_tz_179_);
v___f_180_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_convertZoneRules___lam__0___boxed), 3, 2);
lean_closure_set(v___f_180_, 0, v_tz_179_);
lean_closure_set(v___f_180_, 1, v_timestamp_175_);
v___x_181_ = lean_mk_thunk(v___f_180_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 3, v_tz_179_);
lean_ctor_set(v___x_177_, 2, v_tz_u2081_174_);
lean_ctor_set(v___x_177_, 0, v___x_181_);
v___x_183_ = v___x_177_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_timestamp_175_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_tz_u2081_174_);
lean_ctor_set(v_reuseFailAlloc_184_, 3, v_tz_179_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime(lean_object* v_dt_189_){
_start:
{
lean_object* v_date_190_; lean_object* v___x_191_; 
v_date_190_ = lean_ctor_get(v_dt_189_, 0);
v___x_191_ = lean_thunk_get_own(v_date_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toPlainDateTime___boxed(lean_object* v_dt_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_Time_DateTime_toPlainDateTime(v_dt_192_);
lean_dec_ref(v_dt_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time(lean_object* v_zdt_194_){
_start:
{
lean_object* v_date_195_; lean_object* v___x_196_; lean_object* v_time_197_; 
v_date_195_ = lean_ctor_get(v_zdt_194_, 0);
v___x_196_ = lean_thunk_get_own(v_date_195_);
v_time_197_ = lean_ctor_get(v___x_196_, 1);
lean_inc_ref(v_time_197_);
lean_dec(v___x_196_);
return v_time_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_time___boxed(lean_object* v_zdt_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Time_DateTime_time(v_zdt_198_);
lean_dec_ref(v_zdt_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year(lean_object* v_zdt_200_){
_start:
{
lean_object* v_date_201_; lean_object* v___x_202_; lean_object* v_date_203_; lean_object* v_year_204_; 
v_date_201_ = lean_ctor_get(v_zdt_200_, 0);
v___x_202_ = lean_thunk_get_own(v_date_201_);
v_date_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc_ref(v_date_203_);
lean_dec(v___x_202_);
v_year_204_ = lean_ctor_get(v_date_203_, 0);
lean_inc(v_year_204_);
lean_dec_ref(v_date_203_);
return v_year_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_year___boxed(lean_object* v_zdt_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Time_DateTime_year(v_zdt_205_);
lean_dec_ref(v_zdt_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month(lean_object* v_zdt_207_){
_start:
{
lean_object* v_date_208_; lean_object* v___x_209_; lean_object* v_date_210_; lean_object* v_month_211_; 
v_date_208_ = lean_ctor_get(v_zdt_207_, 0);
v___x_209_ = lean_thunk_get_own(v_date_208_);
v_date_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc_ref(v_date_210_);
lean_dec(v___x_209_);
v_month_211_ = lean_ctor_get(v_date_210_, 1);
lean_inc(v_month_211_);
lean_dec_ref(v_date_210_);
return v_month_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_month___boxed(lean_object* v_zdt_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Time_DateTime_month(v_zdt_212_);
lean_dec_ref(v_zdt_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day(lean_object* v_zdt_214_){
_start:
{
lean_object* v_date_215_; lean_object* v___x_216_; lean_object* v_date_217_; lean_object* v_day_218_; 
v_date_215_ = lean_ctor_get(v_zdt_214_, 0);
v___x_216_ = lean_thunk_get_own(v_date_215_);
v_date_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc_ref(v_date_217_);
lean_dec(v___x_216_);
v_day_218_ = lean_ctor_get(v_date_217_, 2);
lean_inc(v_day_218_);
lean_dec_ref(v_date_217_);
return v_day_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_day___boxed(lean_object* v_zdt_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Time_DateTime_day(v_zdt_219_);
lean_dec_ref(v_zdt_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour(lean_object* v_zdt_221_){
_start:
{
lean_object* v_date_222_; lean_object* v___x_223_; lean_object* v_time_224_; lean_object* v_hour_225_; 
v_date_222_ = lean_ctor_get(v_zdt_221_, 0);
v___x_223_ = lean_thunk_get_own(v_date_222_);
v_time_224_ = lean_ctor_get(v___x_223_, 1);
lean_inc_ref(v_time_224_);
lean_dec(v___x_223_);
v_hour_225_ = lean_ctor_get(v_time_224_, 0);
lean_inc(v_hour_225_);
lean_dec_ref(v_time_224_);
return v_hour_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_hour___boxed(lean_object* v_zdt_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_Time_DateTime_hour(v_zdt_226_);
lean_dec_ref(v_zdt_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute(lean_object* v_zdt_228_){
_start:
{
lean_object* v_date_229_; lean_object* v___x_230_; lean_object* v_time_231_; lean_object* v_minute_232_; 
v_date_229_ = lean_ctor_get(v_zdt_228_, 0);
v___x_230_ = lean_thunk_get_own(v_date_229_);
v_time_231_ = lean_ctor_get(v___x_230_, 1);
lean_inc_ref(v_time_231_);
lean_dec(v___x_230_);
v_minute_232_ = lean_ctor_get(v_time_231_, 1);
lean_inc(v_minute_232_);
lean_dec_ref(v_time_231_);
return v_minute_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_minute___boxed(lean_object* v_zdt_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_Time_DateTime_minute(v_zdt_233_);
lean_dec_ref(v_zdt_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second(lean_object* v_zdt_235_){
_start:
{
lean_object* v_date_236_; lean_object* v___x_237_; lean_object* v_time_238_; lean_object* v_second_239_; 
v_date_236_ = lean_ctor_get(v_zdt_235_, 0);
v___x_237_ = lean_thunk_get_own(v_date_236_);
v_time_238_ = lean_ctor_get(v___x_237_, 1);
lean_inc_ref(v_time_238_);
lean_dec(v___x_237_);
v_second_239_ = lean_ctor_get(v_time_238_, 2);
lean_inc(v_second_239_);
lean_dec_ref(v_time_238_);
return v_second_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_second___boxed(lean_object* v_zdt_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Std_Time_DateTime_second(v_zdt_240_);
lean_dec_ref(v_zdt_240_);
return v_res_241_;
}
}
static lean_object* _init_l_Std_Time_DateTime_millisecond___closed__0(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(1000000u);
v___x_243_ = lean_nat_to_int(v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond(lean_object* v_dt_244_){
_start:
{
lean_object* v_date_245_; lean_object* v___x_246_; lean_object* v_time_247_; lean_object* v_nanosecond_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_date_245_ = lean_ctor_get(v_dt_244_, 0);
v___x_246_ = lean_thunk_get_own(v_date_245_);
v_time_247_ = lean_ctor_get(v___x_246_, 1);
lean_inc_ref(v_time_247_);
lean_dec(v___x_246_);
v_nanosecond_248_ = lean_ctor_get(v_time_247_, 3);
lean_inc(v_nanosecond_248_);
lean_dec_ref(v_time_247_);
v___x_249_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_250_ = lean_int_ediv(v_nanosecond_248_, v___x_249_);
lean_dec(v_nanosecond_248_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_millisecond___boxed(lean_object* v_dt_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Time_DateTime_millisecond(v_dt_251_);
lean_dec_ref(v_dt_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond(lean_object* v_zdt_253_){
_start:
{
lean_object* v_date_254_; lean_object* v___x_255_; lean_object* v_time_256_; lean_object* v_nanosecond_257_; 
v_date_254_ = lean_ctor_get(v_zdt_253_, 0);
v___x_255_ = lean_thunk_get_own(v_date_254_);
v_time_256_ = lean_ctor_get(v___x_255_, 1);
lean_inc_ref(v_time_256_);
lean_dec(v___x_255_);
v_nanosecond_257_ = lean_ctor_get(v_time_256_, 3);
lean_inc(v_nanosecond_257_);
lean_dec_ref(v_time_256_);
return v_nanosecond_257_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_nanosecond___boxed(lean_object* v_zdt_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Std_Time_DateTime_nanosecond(v_zdt_258_);
lean_dec_ref(v_zdt_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_offset(lean_object* v_zdt_260_){
_start:
{
lean_object* v_timezone_261_; lean_object* v_offset_262_; 
v_timezone_261_ = lean_ctor_get(v_zdt_260_, 3);
v_offset_262_ = lean_ctor_get(v_timezone_261_, 0);
lean_inc(v_offset_262_);
return v_offset_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_offset___boxed(lean_object* v_zdt_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Time_DateTime_offset(v_zdt_263_);
lean_dec_ref(v_zdt_263_);
return v_res_264_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_weekday(lean_object* v_zdt_265_){
_start:
{
lean_object* v_date_266_; lean_object* v___x_267_; lean_object* v_date_268_; uint8_t v___x_269_; 
v_date_266_ = lean_ctor_get(v_zdt_265_, 0);
v___x_267_ = lean_thunk_get_own(v_date_266_);
v_date_268_ = lean_ctor_get(v___x_267_, 0);
lean_inc_ref(v_date_268_);
lean_dec(v___x_267_);
v___x_269_ = l_Std_Time_PlainDate_weekday(v_date_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object* v_zdt_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l_Std_Time_DateTime_weekday(v_zdt_270_);
lean_dec_ref(v_zdt_270_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__0(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(4u);
v___x_274_ = lean_nat_to_int(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__1(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(100u);
v___x_276_ = lean_nat_to_int(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__2(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(400u);
v___x_278_ = lean_nat_to_int(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object* v_date_279_){
_start:
{
lean_object* v_date_280_; lean_object* v___x_281_; lean_object* v_date_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_305_; 
v_date_280_ = lean_ctor_get(v_date_279_, 0);
v___x_281_ = lean_thunk_get_own(v_date_280_);
v_date_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_281_, 1);
lean_dec(v_unused_306_);
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_305_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_date_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_305_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_year_286_; lean_object* v_month_287_; lean_object* v_day_288_; uint8_t v___y_290_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_year_286_ = lean_ctor_get(v_date_282_, 0);
lean_inc(v_year_286_);
v_month_287_ = lean_ctor_get(v_date_282_, 1);
lean_inc(v_month_287_);
v_day_288_ = lean_ctor_get(v_date_282_, 2);
lean_inc(v_day_288_);
lean_dec_ref(v_date_282_);
v___x_295_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_296_ = lean_int_mod(v_year_286_, v___x_295_);
v___x_297_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_298_ = lean_int_dec_eq(v___x_296_, v___x_297_);
lean_dec(v___x_296_);
if (v___x_298_ == 0)
{
lean_dec(v_year_286_);
v___y_290_ = v___x_298_;
goto v___jp_289_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_300_ = lean_int_mod(v_year_286_, v___x_299_);
v___x_301_ = lean_int_dec_eq(v___x_300_, v___x_297_);
lean_dec(v___x_300_);
if (v___x_301_ == 0)
{
lean_dec(v_year_286_);
v___y_290_ = v___x_298_;
goto v___jp_289_;
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_303_ = lean_int_mod(v_year_286_, v___x_302_);
lean_dec(v_year_286_);
v___x_304_ = lean_int_dec_eq(v___x_303_, v___x_297_);
lean_dec(v___x_303_);
v___y_290_ = v___x_304_;
goto v___jp_289_;
}
}
v___jp_289_:
{
lean_object* v___x_292_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v_day_288_);
lean_ctor_set(v___x_284_, 0, v_month_287_);
v___x_292_ = v___x_284_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_month_287_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_day_288_);
v___x_292_ = v_reuseFailAlloc_294_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_Time_ValidDate_dayOfYear(v___y_290_, v___x_292_);
lean_dec_ref(v___x_292_);
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object* v_date_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_Time_DateTime_dayOfYear(v_date_307_);
lean_dec_ref(v_date_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* v_dt_309_, uint8_t v_firstDay_310_, lean_object* v_minDays_311_){
_start:
{
lean_object* v_date_312_; lean_object* v___x_313_; lean_object* v_date_314_; lean_object* v___x_315_; 
v_date_312_ = lean_ctor_get(v_dt_309_, 0);
v___x_313_ = lean_thunk_get_own(v_date_312_);
v_date_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc_ref(v_date_314_);
lean_dec(v___x_313_);
v___x_315_ = l_Std_Time_PlainDate_weekOfYear(v_date_314_, v_firstDay_310_, v_minDays_311_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object* v_dt_316_, lean_object* v_firstDay_317_, lean_object* v_minDays_318_){
_start:
{
uint8_t v_firstDay_boxed_319_; lean_object* v_res_320_; 
v_firstDay_boxed_319_ = lean_unbox(v_firstDay_317_);
v_res_320_ = l_Std_Time_DateTime_weekOfYear(v_dt_316_, v_firstDay_boxed_319_, v_minDays_318_);
lean_dec(v_minDays_318_);
lean_dec_ref(v_dt_316_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear(lean_object* v_date_321_, uint8_t v_firstDay_322_, lean_object* v_minDays_323_){
_start:
{
lean_object* v_date_324_; lean_object* v___x_325_; lean_object* v_date_326_; lean_object* v___x_327_; 
v_date_324_ = lean_ctor_get(v_date_321_, 0);
v___x_325_ = lean_thunk_get_own(v_date_324_);
v_date_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc_ref(v_date_326_);
lean_dec(v___x_325_);
v___x_327_ = l_Std_Time_PlainDate_weekYear(v_date_326_, v_firstDay_322_, v_minDays_323_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___boxed(lean_object* v_date_328_, lean_object* v_firstDay_329_, lean_object* v_minDays_330_){
_start:
{
uint8_t v_firstDay_boxed_331_; lean_object* v_res_332_; 
v_firstDay_boxed_331_ = lean_unbox(v_firstDay_329_);
v_res_332_ = l_Std_Time_DateTime_weekYear(v_date_328_, v_firstDay_boxed_331_, v_minDays_330_);
lean_dec(v_minDays_330_);
lean_dec_ref(v_date_328_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* v_date_333_){
_start:
{
lean_object* v_date_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_date_334_ = lean_ctor_get(v_date_333_, 0);
v___x_335_ = lean_thunk_get_own(v_date_334_);
v___x_336_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v___x_335_);
lean_dec(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object* v_date_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_337_);
lean_dec_ref(v_date_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* v_date_339_, uint8_t v_firstDay_340_){
_start:
{
lean_object* v_date_341_; lean_object* v___x_342_; lean_object* v_date_343_; lean_object* v___x_344_; 
v_date_341_ = lean_ctor_get(v_date_339_, 0);
v___x_342_ = lean_thunk_get_own(v_date_341_);
v_date_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc_ref(v_date_343_);
lean_dec(v___x_342_);
v___x_344_ = l_Std_Time_PlainDate_weekOfMonth(v_date_343_, v_firstDay_340_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object* v_date_345_, lean_object* v_firstDay_346_){
_start:
{
uint8_t v_firstDay_boxed_347_; lean_object* v_res_348_; 
v_firstDay_boxed_347_ = lean_unbox(v_firstDay_346_);
v_res_348_ = l_Std_Time_DateTime_weekOfMonth(v_date_345_, v_firstDay_boxed_347_);
lean_dec_ref(v_date_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* v_date_349_){
_start:
{
lean_object* v_date_350_; lean_object* v___x_351_; lean_object* v_date_352_; lean_object* v___x_353_; 
v_date_350_ = lean_ctor_get(v_date_349_, 0);
v___x_351_ = lean_thunk_get_own(v_date_350_);
v_date_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc_ref(v_date_352_);
lean_dec(v___x_351_);
v___x_353_ = l_Std_Time_PlainDate_quarter(v_date_352_);
lean_dec_ref(v_date_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object* v_date_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_Time_DateTime_quarter(v_date_354_);
lean_dec_ref(v_date_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_DateTime_addDays_spec__1(lean_object* v_a_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Rat_ofInt(v_a_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0(lean_object* v_tz_358_, lean_object* v___x_359_, lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v_offset_363_; lean_object* v_second_364_; lean_object* v_nano_365_; lean_object* v___x_366_; lean_object* v_nanos_367_; lean_object* v___x_368_; lean_object* v_nanos_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v_offset_363_ = lean_ctor_get(v_tz_358_, 0);
v_second_364_ = lean_ctor_get(v___x_359_, 0);
v_nano_365_ = lean_ctor_get(v___x_359_, 1);
v___x_366_ = lean_int_mul(v_second_364_, v___x_360_);
v_nanos_367_ = lean_int_add(v___x_366_, v_nano_365_);
lean_dec(v___x_366_);
v___x_368_ = lean_int_mul(v_offset_363_, v___x_360_);
v_nanos_369_ = lean_int_add(v___x_368_, v___x_361_);
lean_dec(v___x_368_);
v___x_370_ = lean_int_add(v_nanos_367_, v_nanos_369_);
lean_dec(v_nanos_369_);
lean_dec(v_nanos_367_);
v___x_371_ = l_Std_Time_Duration_ofNanoseconds(v___x_370_);
lean_dec(v___x_370_);
v___x_372_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0___boxed(lean_object* v_tz_373_, lean_object* v___x_374_, lean_object* v___x_375_, lean_object* v___x_376_, lean_object* v_x_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_Time_DateTime_addDays___lam__0(v_tz_373_, v___x_374_, v___x_375_, v___x_376_, v_x_377_);
lean_dec(v___x_376_);
lean_dec(v___x_375_);
lean_dec_ref(v___x_374_);
lean_dec_ref(v_tz_373_);
return v_res_378_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addDays___closed__0(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = lean_unsigned_to_nat(86400u);
v___x_380_ = lean_nat_to_int(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object* v_dt_381_, lean_object* v_days_382_){
_start:
{
lean_object* v_timestamp_383_; lean_object* v_rules_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_406_; 
v_timestamp_383_ = lean_ctor_get(v_dt_381_, 1);
v_rules_384_ = lean_ctor_get(v_dt_381_, 2);
v_isSharedCheck_406_ = !lean_is_exclusive(v_dt_381_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; lean_object* v_unused_408_; 
v_unused_407_ = lean_ctor_get(v_dt_381_, 3);
lean_dec(v_unused_407_);
v_unused_408_ = lean_ctor_get(v_dt_381_, 0);
lean_dec(v_unused_408_);
v___x_386_ = v_dt_381_;
v_isShared_387_ = v_isSharedCheck_406_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_rules_384_);
lean_inc(v_timestamp_383_);
lean_dec(v_dt_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_406_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v_second_388_; lean_object* v_nano_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v_nanos_395_; lean_object* v___x_396_; lean_object* v_nanos_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_tz_400_; lean_object* v___f_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v_second_388_ = lean_ctor_get(v_timestamp_383_, 0);
lean_inc(v_second_388_);
v_nano_389_ = lean_ctor_get(v_timestamp_383_, 1);
lean_inc(v_nano_389_);
lean_dec_ref(v_timestamp_383_);
v___x_390_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_391_ = lean_int_mul(v_days_382_, v___x_390_);
v___x_392_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_393_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_394_ = lean_int_mul(v_second_388_, v___x_393_);
lean_dec(v_second_388_);
v_nanos_395_ = lean_int_add(v___x_394_, v_nano_389_);
lean_dec(v_nano_389_);
lean_dec(v___x_394_);
v___x_396_ = lean_int_mul(v___x_391_, v___x_393_);
lean_dec(v___x_391_);
v_nanos_397_ = lean_int_add(v___x_396_, v___x_392_);
lean_dec(v___x_396_);
v___x_398_ = lean_int_add(v_nanos_395_, v_nanos_397_);
lean_dec(v_nanos_397_);
lean_dec(v_nanos_395_);
v___x_399_ = l_Std_Time_Duration_ofNanoseconds(v___x_398_);
lean_dec(v___x_398_);
lean_inc_ref(v_rules_384_);
v_tz_400_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_384_, v___x_399_);
lean_inc_ref(v___x_399_);
lean_inc_ref(v_tz_400_);
v___f_401_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_401_, 0, v_tz_400_);
lean_closure_set(v___f_401_, 1, v___x_399_);
lean_closure_set(v___f_401_, 2, v___x_393_);
lean_closure_set(v___f_401_, 3, v___x_392_);
v___x_402_ = lean_mk_thunk(v___f_401_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 3, v_tz_400_);
lean_ctor_set(v___x_386_, 1, v___x_399_);
lean_ctor_set(v___x_386_, 0, v___x_402_);
v___x_404_ = v___x_386_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_rules_384_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_tz_400_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object* v_dt_409_, lean_object* v_days_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_Time_DateTime_addDays(v_dt_409_, v_days_410_);
lean_dec(v_days_410_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_DateTime_addDays_spec__0_spec__0(lean_object* v_a_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = lean_nat_to_int(v_a_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_DateTime_addDays_spec__0(lean_object* v_a_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_nat_to_int(v_a_414_);
v___x_416_ = l_Rat_ofInt(v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object* v_dt_417_, lean_object* v_days_418_){
_start:
{
lean_object* v_timestamp_419_; lean_object* v_rules_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_444_; 
v_timestamp_419_ = lean_ctor_get(v_dt_417_, 1);
v_rules_420_ = lean_ctor_get(v_dt_417_, 2);
v_isSharedCheck_444_ = !lean_is_exclusive(v_dt_417_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; 
v_unused_445_ = lean_ctor_get(v_dt_417_, 3);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_dt_417_, 0);
lean_dec(v_unused_446_);
v___x_422_ = v_dt_417_;
v_isShared_423_ = v_isSharedCheck_444_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_rules_420_);
lean_inc(v_timestamp_419_);
lean_dec(v_dt_417_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_444_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_second_424_; lean_object* v_nano_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_nanos_433_; lean_object* v___x_434_; lean_object* v_nanos_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_tz_438_; lean_object* v___f_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v_second_424_ = lean_ctor_get(v_timestamp_419_, 0);
lean_inc(v_second_424_);
v_nano_425_ = lean_ctor_get(v_timestamp_419_, 1);
lean_inc(v_nano_425_);
lean_dec_ref(v_timestamp_419_);
v___x_426_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_427_ = lean_int_mul(v_days_418_, v___x_426_);
v___x_428_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_429_ = lean_int_neg(v___x_427_);
lean_dec(v___x_427_);
v___x_430_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_431_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_432_ = lean_int_mul(v_second_424_, v___x_431_);
lean_dec(v_second_424_);
v_nanos_433_ = lean_int_add(v___x_432_, v_nano_425_);
lean_dec(v_nano_425_);
lean_dec(v___x_432_);
v___x_434_ = lean_int_mul(v___x_429_, v___x_431_);
lean_dec(v___x_429_);
v_nanos_435_ = lean_int_add(v___x_434_, v___x_430_);
lean_dec(v___x_434_);
v___x_436_ = lean_int_add(v_nanos_433_, v_nanos_435_);
lean_dec(v_nanos_435_);
lean_dec(v_nanos_433_);
v___x_437_ = l_Std_Time_Duration_ofNanoseconds(v___x_436_);
lean_dec(v___x_436_);
lean_inc_ref(v_rules_420_);
v_tz_438_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_420_, v___x_437_);
lean_inc_ref(v___x_437_);
lean_inc_ref(v_tz_438_);
v___f_439_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_439_, 0, v_tz_438_);
lean_closure_set(v___f_439_, 1, v___x_437_);
lean_closure_set(v___f_439_, 2, v___x_431_);
lean_closure_set(v___f_439_, 3, v___x_428_);
v___x_440_ = lean_mk_thunk(v___f_439_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 3, v_tz_438_);
lean_ctor_set(v___x_422_, 1, v___x_437_);
lean_ctor_set(v___x_422_, 0, v___x_440_);
v___x_442_ = v___x_422_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_rules_420_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_tz_438_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object* v_dt_447_, lean_object* v_days_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_Time_DateTime_subDays(v_dt_447_, v_days_448_);
lean_dec(v_days_448_);
return v_res_449_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(7u);
v___x_451_ = lean_nat_to_int(v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object* v_dt_452_, lean_object* v_weeks_453_){
_start:
{
lean_object* v_timestamp_454_; lean_object* v_rules_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_479_; 
v_timestamp_454_ = lean_ctor_get(v_dt_452_, 1);
v_rules_455_ = lean_ctor_get(v_dt_452_, 2);
v_isSharedCheck_479_ = !lean_is_exclusive(v_dt_452_);
if (v_isSharedCheck_479_ == 0)
{
lean_object* v_unused_480_; lean_object* v_unused_481_; 
v_unused_480_ = lean_ctor_get(v_dt_452_, 3);
lean_dec(v_unused_480_);
v_unused_481_ = lean_ctor_get(v_dt_452_, 0);
lean_dec(v_unused_481_);
v___x_457_ = v_dt_452_;
v_isShared_458_ = v_isSharedCheck_479_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_rules_455_);
lean_inc(v_timestamp_454_);
lean_dec(v_dt_452_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_479_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v_second_459_; lean_object* v_nano_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v_nanos_468_; lean_object* v___x_469_; lean_object* v_nanos_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_tz_473_; lean_object* v___f_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v_second_459_ = lean_ctor_get(v_timestamp_454_, 0);
lean_inc(v_second_459_);
v_nano_460_ = lean_ctor_get(v_timestamp_454_, 1);
lean_inc(v_nano_460_);
lean_dec_ref(v_timestamp_454_);
v___x_461_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_462_ = lean_int_mul(v_weeks_453_, v___x_461_);
v___x_463_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_464_ = lean_int_mul(v___x_462_, v___x_463_);
lean_dec(v___x_462_);
v___x_465_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_466_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_467_ = lean_int_mul(v_second_459_, v___x_466_);
lean_dec(v_second_459_);
v_nanos_468_ = lean_int_add(v___x_467_, v_nano_460_);
lean_dec(v_nano_460_);
lean_dec(v___x_467_);
v___x_469_ = lean_int_mul(v___x_464_, v___x_466_);
lean_dec(v___x_464_);
v_nanos_470_ = lean_int_add(v___x_469_, v___x_465_);
lean_dec(v___x_469_);
v___x_471_ = lean_int_add(v_nanos_468_, v_nanos_470_);
lean_dec(v_nanos_470_);
lean_dec(v_nanos_468_);
v___x_472_ = l_Std_Time_Duration_ofNanoseconds(v___x_471_);
lean_dec(v___x_471_);
lean_inc_ref(v_rules_455_);
v_tz_473_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_455_, v___x_472_);
lean_inc_ref(v___x_472_);
lean_inc_ref(v_tz_473_);
v___f_474_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_474_, 0, v_tz_473_);
lean_closure_set(v___f_474_, 1, v___x_472_);
lean_closure_set(v___f_474_, 2, v___x_466_);
lean_closure_set(v___f_474_, 3, v___x_465_);
v___x_475_ = lean_mk_thunk(v___f_474_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 3, v_tz_473_);
lean_ctor_set(v___x_457_, 1, v___x_472_);
lean_ctor_set(v___x_457_, 0, v___x_475_);
v___x_477_ = v___x_457_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v_rules_455_);
lean_ctor_set(v_reuseFailAlloc_478_, 3, v_tz_473_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object* v_dt_482_, lean_object* v_weeks_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_Time_DateTime_addWeeks(v_dt_482_, v_weeks_483_);
lean_dec(v_weeks_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object* v_dt_485_, lean_object* v_weeks_486_){
_start:
{
lean_object* v_timestamp_487_; lean_object* v_rules_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_514_; 
v_timestamp_487_ = lean_ctor_get(v_dt_485_, 1);
v_rules_488_ = lean_ctor_get(v_dt_485_, 2);
v_isSharedCheck_514_ = !lean_is_exclusive(v_dt_485_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; lean_object* v_unused_516_; 
v_unused_515_ = lean_ctor_get(v_dt_485_, 3);
lean_dec(v_unused_515_);
v_unused_516_ = lean_ctor_get(v_dt_485_, 0);
lean_dec(v_unused_516_);
v___x_490_ = v_dt_485_;
v_isShared_491_ = v_isSharedCheck_514_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_rules_488_);
lean_inc(v_timestamp_487_);
lean_dec(v_dt_485_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_514_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_second_492_; lean_object* v_nano_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_nanos_503_; lean_object* v___x_504_; lean_object* v_nanos_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_tz_508_; lean_object* v___f_509_; lean_object* v___x_510_; lean_object* v___x_512_; 
v_second_492_ = lean_ctor_get(v_timestamp_487_, 0);
lean_inc(v_second_492_);
v_nano_493_ = lean_ctor_get(v_timestamp_487_, 1);
lean_inc(v_nano_493_);
lean_dec_ref(v_timestamp_487_);
v___x_494_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_495_ = lean_int_mul(v_weeks_486_, v___x_494_);
v___x_496_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_497_ = lean_int_mul(v___x_495_, v___x_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_499_ = lean_int_neg(v___x_497_);
lean_dec(v___x_497_);
v___x_500_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_501_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_502_ = lean_int_mul(v_second_492_, v___x_501_);
lean_dec(v_second_492_);
v_nanos_503_ = lean_int_add(v___x_502_, v_nano_493_);
lean_dec(v_nano_493_);
lean_dec(v___x_502_);
v___x_504_ = lean_int_mul(v___x_499_, v___x_501_);
lean_dec(v___x_499_);
v_nanos_505_ = lean_int_add(v___x_504_, v___x_500_);
lean_dec(v___x_504_);
v___x_506_ = lean_int_add(v_nanos_503_, v_nanos_505_);
lean_dec(v_nanos_505_);
lean_dec(v_nanos_503_);
v___x_507_ = l_Std_Time_Duration_ofNanoseconds(v___x_506_);
lean_dec(v___x_506_);
lean_inc_ref(v_rules_488_);
v_tz_508_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_488_, v___x_507_);
lean_inc_ref(v___x_507_);
lean_inc_ref(v_tz_508_);
v___f_509_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_509_, 0, v_tz_508_);
lean_closure_set(v___f_509_, 1, v___x_507_);
lean_closure_set(v___f_509_, 2, v___x_501_);
lean_closure_set(v___f_509_, 3, v___x_498_);
v___x_510_ = lean_mk_thunk(v___f_509_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 3, v_tz_508_);
lean_ctor_set(v___x_490_, 1, v___x_507_);
lean_ctor_set(v___x_490_, 0, v___x_510_);
v___x_512_ = v___x_490_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_rules_488_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_tz_508_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object* v_dt_517_, lean_object* v_weeks_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_Time_DateTime_subWeeks(v_dt_517_, v_weeks_518_);
lean_dec(v_weeks_518_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0(lean_object* v___x_520_, lean_object* v_x_521_){
_start:
{
lean_inc_ref(v___x_520_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(lean_object* v___x_522_, lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_Time_DateTime_addMonthsClip___lam__0(v___x_522_, v_x_523_);
lean_dec_ref(v___x_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object* v_dt_525_, lean_object* v_months_526_){
_start:
{
lean_object* v_date_527_; lean_object* v_rules_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_554_; 
v_date_527_ = lean_ctor_get(v_dt_525_, 0);
v_rules_528_ = lean_ctor_get(v_dt_525_, 2);
v_isSharedCheck_554_ = !lean_is_exclusive(v_dt_525_);
if (v_isSharedCheck_554_ == 0)
{
lean_object* v_unused_555_; lean_object* v_unused_556_; 
v_unused_555_ = lean_ctor_get(v_dt_525_, 3);
lean_dec(v_unused_555_);
v_unused_556_ = lean_ctor_get(v_dt_525_, 1);
lean_dec(v_unused_556_);
v___x_530_ = v_dt_525_;
v_isShared_531_ = v_isSharedCheck_554_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_rules_528_);
lean_inc(v_date_527_);
lean_dec(v_dt_525_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_554_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v_wt_534_; lean_object* v_ltt_535_; lean_object* v_tz_536_; lean_object* v_offset_537_; lean_object* v_second_538_; lean_object* v_nano_539_; lean_object* v___f_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_nanos_546_; lean_object* v___x_547_; lean_object* v_nanos_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_532_ = lean_thunk_get_own(v_date_527_);
lean_dec_ref(v_date_527_);
v___x_533_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_532_, v_months_526_);
lean_inc_ref(v___x_533_);
v_wt_534_ = l_Std_Time_PlainDateTime_toWallTime(v___x_533_);
lean_inc_ref(v_rules_528_);
v_ltt_535_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_528_, v_wt_534_);
v_tz_536_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_535_);
lean_dec_ref(v_ltt_535_);
v_offset_537_ = lean_ctor_get(v_tz_536_, 0);
v_second_538_ = lean_ctor_get(v_wt_534_, 0);
lean_inc(v_second_538_);
v_nano_539_ = lean_ctor_get(v_wt_534_, 1);
lean_inc(v_nano_539_);
lean_dec_ref(v_wt_534_);
v___f_540_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_540_, 0, v___x_533_);
v___x_541_ = lean_mk_thunk(v___f_540_);
v___x_542_ = lean_int_neg(v_offset_537_);
v___x_543_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_544_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_545_ = lean_int_mul(v_second_538_, v___x_544_);
lean_dec(v_second_538_);
v_nanos_546_ = lean_int_add(v___x_545_, v_nano_539_);
lean_dec(v_nano_539_);
lean_dec(v___x_545_);
v___x_547_ = lean_int_mul(v___x_542_, v___x_544_);
lean_dec(v___x_542_);
v_nanos_548_ = lean_int_add(v___x_547_, v___x_543_);
lean_dec(v___x_547_);
v___x_549_ = lean_int_add(v_nanos_546_, v_nanos_548_);
lean_dec(v_nanos_548_);
lean_dec(v_nanos_546_);
v___x_550_ = l_Std_Time_Duration_ofNanoseconds(v___x_549_);
lean_dec(v___x_549_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 3, v_tz_536_);
lean_ctor_set(v___x_530_, 1, v___x_550_);
lean_ctor_set(v___x_530_, 0, v___x_541_);
v___x_552_ = v___x_530_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_553_, 1, v___x_550_);
lean_ctor_set(v_reuseFailAlloc_553_, 2, v_rules_528_);
lean_ctor_set(v_reuseFailAlloc_553_, 3, v_tz_536_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object* v_dt_557_, lean_object* v_months_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_Time_DateTime_addMonthsClip(v_dt_557_, v_months_558_);
lean_dec(v_months_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object* v_dt_560_, lean_object* v_months_561_){
_start:
{
lean_object* v_date_562_; lean_object* v_rules_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_599_; 
v_date_562_ = lean_ctor_get(v_dt_560_, 0);
v_rules_563_ = lean_ctor_get(v_dt_560_, 2);
v_isSharedCheck_599_ = !lean_is_exclusive(v_dt_560_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; lean_object* v_unused_601_; 
v_unused_600_ = lean_ctor_get(v_dt_560_, 3);
lean_dec(v_unused_600_);
v_unused_601_ = lean_ctor_get(v_dt_560_, 1);
lean_dec(v_unused_601_);
v___x_565_ = v_dt_560_;
v_isShared_566_ = v_isSharedCheck_599_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_rules_563_);
lean_inc(v_date_562_);
lean_dec(v_dt_560_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_599_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v_date_568_; lean_object* v_time_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_598_; 
v___x_567_ = lean_thunk_get_own(v_date_562_);
lean_dec_ref(v_date_562_);
v_date_568_ = lean_ctor_get(v___x_567_, 0);
v_time_569_ = lean_ctor_get(v___x_567_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_598_ == 0)
{
v___x_571_ = v___x_567_;
v_isShared_572_ = v_isSharedCheck_598_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_time_569_);
lean_inc(v_date_568_);
lean_dec(v___x_567_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_598_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_573_ = lean_int_neg(v_months_561_);
v___x_574_ = l_Std_Time_PlainDate_addMonthsClip(v_date_568_, v___x_573_);
lean_dec(v___x_573_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_574_);
v___x_576_ = v___x_571_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_time_569_);
v___x_576_ = v_reuseFailAlloc_597_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v_wt_577_; lean_object* v_ltt_578_; lean_object* v_tz_579_; lean_object* v_offset_580_; lean_object* v_second_581_; lean_object* v_nano_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_nanos_589_; lean_object* v___x_590_; lean_object* v_nanos_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
lean_inc_ref(v___x_576_);
v_wt_577_ = l_Std_Time_PlainDateTime_toWallTime(v___x_576_);
lean_inc_ref(v_rules_563_);
v_ltt_578_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_563_, v_wt_577_);
v_tz_579_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_578_);
lean_dec_ref(v_ltt_578_);
v_offset_580_ = lean_ctor_get(v_tz_579_, 0);
v_second_581_ = lean_ctor_get(v_wt_577_, 0);
lean_inc(v_second_581_);
v_nano_582_ = lean_ctor_get(v_wt_577_, 1);
lean_inc(v_nano_582_);
lean_dec_ref(v_wt_577_);
v___f_583_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_583_, 0, v___x_576_);
v___x_584_ = lean_mk_thunk(v___f_583_);
v___x_585_ = lean_int_neg(v_offset_580_);
v___x_586_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_587_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_588_ = lean_int_mul(v_second_581_, v___x_587_);
lean_dec(v_second_581_);
v_nanos_589_ = lean_int_add(v___x_588_, v_nano_582_);
lean_dec(v_nano_582_);
lean_dec(v___x_588_);
v___x_590_ = lean_int_mul(v___x_585_, v___x_587_);
lean_dec(v___x_585_);
v_nanos_591_ = lean_int_add(v___x_590_, v___x_586_);
lean_dec(v___x_590_);
v___x_592_ = lean_int_add(v_nanos_589_, v_nanos_591_);
lean_dec(v_nanos_591_);
lean_dec(v_nanos_589_);
v___x_593_ = l_Std_Time_Duration_ofNanoseconds(v___x_592_);
lean_dec(v___x_592_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 3, v_tz_579_);
lean_ctor_set(v___x_565_, 1, v___x_593_);
lean_ctor_set(v___x_565_, 0, v___x_584_);
v___x_595_ = v___x_565_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_rules_563_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v_tz_579_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object* v_dt_602_, lean_object* v_months_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Std_Time_DateTime_subMonthsClip(v_dt_602_, v_months_603_);
lean_dec(v_months_603_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object* v_dt_605_, lean_object* v_months_606_){
_start:
{
lean_object* v_date_607_; lean_object* v_rules_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_634_; 
v_date_607_ = lean_ctor_get(v_dt_605_, 0);
v_rules_608_ = lean_ctor_get(v_dt_605_, 2);
v_isSharedCheck_634_ = !lean_is_exclusive(v_dt_605_);
if (v_isSharedCheck_634_ == 0)
{
lean_object* v_unused_635_; lean_object* v_unused_636_; 
v_unused_635_ = lean_ctor_get(v_dt_605_, 3);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_dt_605_, 1);
lean_dec(v_unused_636_);
v___x_610_ = v_dt_605_;
v_isShared_611_ = v_isSharedCheck_634_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_rules_608_);
lean_inc(v_date_607_);
lean_dec(v_dt_605_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_634_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v_wt_614_; lean_object* v_ltt_615_; lean_object* v_tz_616_; lean_object* v_offset_617_; lean_object* v_second_618_; lean_object* v_nano_619_; lean_object* v___f_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_nanos_626_; lean_object* v___x_627_; lean_object* v_nanos_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_612_ = lean_thunk_get_own(v_date_607_);
lean_dec_ref(v_date_607_);
v___x_613_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_612_, v_months_606_);
lean_inc_ref(v___x_613_);
v_wt_614_ = l_Std_Time_PlainDateTime_toWallTime(v___x_613_);
lean_inc_ref(v_rules_608_);
v_ltt_615_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_608_, v_wt_614_);
v_tz_616_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_615_);
lean_dec_ref(v_ltt_615_);
v_offset_617_ = lean_ctor_get(v_tz_616_, 0);
v_second_618_ = lean_ctor_get(v_wt_614_, 0);
lean_inc(v_second_618_);
v_nano_619_ = lean_ctor_get(v_wt_614_, 1);
lean_inc(v_nano_619_);
lean_dec_ref(v_wt_614_);
v___f_620_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_620_, 0, v___x_613_);
v___x_621_ = lean_mk_thunk(v___f_620_);
v___x_622_ = lean_int_neg(v_offset_617_);
v___x_623_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_624_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_625_ = lean_int_mul(v_second_618_, v___x_624_);
lean_dec(v_second_618_);
v_nanos_626_ = lean_int_add(v___x_625_, v_nano_619_);
lean_dec(v_nano_619_);
lean_dec(v___x_625_);
v___x_627_ = lean_int_mul(v___x_622_, v___x_624_);
lean_dec(v___x_622_);
v_nanos_628_ = lean_int_add(v___x_627_, v___x_623_);
lean_dec(v___x_627_);
v___x_629_ = lean_int_add(v_nanos_626_, v_nanos_628_);
lean_dec(v_nanos_628_);
lean_dec(v_nanos_626_);
v___x_630_ = l_Std_Time_Duration_ofNanoseconds(v___x_629_);
lean_dec(v___x_629_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 3, v_tz_616_);
lean_ctor_set(v___x_610_, 1, v___x_630_);
lean_ctor_set(v___x_610_, 0, v___x_621_);
v___x_632_ = v___x_610_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_rules_608_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_tz_616_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object* v_dt_637_, lean_object* v_months_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_Time_DateTime_addMonthsRollOver(v_dt_637_, v_months_638_);
lean_dec(v_months_638_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object* v_dt_640_, lean_object* v_months_641_){
_start:
{
lean_object* v_date_642_; lean_object* v_rules_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_679_; 
v_date_642_ = lean_ctor_get(v_dt_640_, 0);
v_rules_643_ = lean_ctor_get(v_dt_640_, 2);
v_isSharedCheck_679_ = !lean_is_exclusive(v_dt_640_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; lean_object* v_unused_681_; 
v_unused_680_ = lean_ctor_get(v_dt_640_, 3);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_dt_640_, 1);
lean_dec(v_unused_681_);
v___x_645_ = v_dt_640_;
v_isShared_646_ = v_isSharedCheck_679_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_rules_643_);
lean_inc(v_date_642_);
lean_dec(v_dt_640_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_679_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v_date_648_; lean_object* v_time_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_678_; 
v___x_647_ = lean_thunk_get_own(v_date_642_);
lean_dec_ref(v_date_642_);
v_date_648_ = lean_ctor_get(v___x_647_, 0);
v_time_649_ = lean_ctor_get(v___x_647_, 1);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_678_ == 0)
{
v___x_651_ = v___x_647_;
v_isShared_652_ = v_isSharedCheck_678_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_time_649_);
lean_inc(v_date_648_);
lean_dec(v___x_647_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_678_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_653_ = lean_int_neg(v_months_641_);
v___x_654_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_648_, v___x_653_);
lean_dec(v___x_653_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_656_ = v___x_651_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_time_649_);
v___x_656_ = v_reuseFailAlloc_677_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v_wt_657_; lean_object* v_ltt_658_; lean_object* v_tz_659_; lean_object* v_offset_660_; lean_object* v_second_661_; lean_object* v_nano_662_; lean_object* v___f_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v_nanos_669_; lean_object* v___x_670_; lean_object* v_nanos_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
lean_inc_ref(v___x_656_);
v_wt_657_ = l_Std_Time_PlainDateTime_toWallTime(v___x_656_);
lean_inc_ref(v_rules_643_);
v_ltt_658_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_643_, v_wt_657_);
v_tz_659_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_658_);
lean_dec_ref(v_ltt_658_);
v_offset_660_ = lean_ctor_get(v_tz_659_, 0);
v_second_661_ = lean_ctor_get(v_wt_657_, 0);
lean_inc(v_second_661_);
v_nano_662_ = lean_ctor_get(v_wt_657_, 1);
lean_inc(v_nano_662_);
lean_dec_ref(v_wt_657_);
v___f_663_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_663_, 0, v___x_656_);
v___x_664_ = lean_mk_thunk(v___f_663_);
v___x_665_ = lean_int_neg(v_offset_660_);
v___x_666_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_667_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_668_ = lean_int_mul(v_second_661_, v___x_667_);
lean_dec(v_second_661_);
v_nanos_669_ = lean_int_add(v___x_668_, v_nano_662_);
lean_dec(v_nano_662_);
lean_dec(v___x_668_);
v___x_670_ = lean_int_mul(v___x_665_, v___x_667_);
lean_dec(v___x_665_);
v_nanos_671_ = lean_int_add(v___x_670_, v___x_666_);
lean_dec(v___x_670_);
v___x_672_ = lean_int_add(v_nanos_669_, v_nanos_671_);
lean_dec(v_nanos_671_);
lean_dec(v_nanos_669_);
v___x_673_ = l_Std_Time_Duration_ofNanoseconds(v___x_672_);
lean_dec(v___x_672_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 3, v_tz_659_);
lean_ctor_set(v___x_645_, 1, v___x_673_);
lean_ctor_set(v___x_645_, 0, v___x_664_);
v___x_675_ = v___x_645_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_664_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_rules_643_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_tz_659_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object* v_dt_682_, lean_object* v_months_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Std_Time_DateTime_subMonthsRollOver(v_dt_682_, v_months_683_);
lean_dec(v_months_683_);
return v_res_684_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(12u);
v___x_686_ = lean_nat_to_int(v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object* v_dt_687_, lean_object* v_years_688_){
_start:
{
lean_object* v_date_689_; lean_object* v_rules_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_727_; 
v_date_689_ = lean_ctor_get(v_dt_687_, 0);
v_rules_690_ = lean_ctor_get(v_dt_687_, 2);
v_isSharedCheck_727_ = !lean_is_exclusive(v_dt_687_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; lean_object* v_unused_729_; 
v_unused_728_ = lean_ctor_get(v_dt_687_, 3);
lean_dec(v_unused_728_);
v_unused_729_ = lean_ctor_get(v_dt_687_, 1);
lean_dec(v_unused_729_);
v___x_692_ = v_dt_687_;
v_isShared_693_ = v_isSharedCheck_727_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_rules_690_);
lean_inc(v_date_689_);
lean_dec(v_dt_687_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_727_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v_date_695_; lean_object* v_time_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_726_; 
v___x_694_ = lean_thunk_get_own(v_date_689_);
lean_dec_ref(v_date_689_);
v_date_695_ = lean_ctor_get(v___x_694_, 0);
v_time_696_ = lean_ctor_get(v___x_694_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_726_ == 0)
{
v___x_698_ = v___x_694_;
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_time_696_);
lean_inc(v_date_695_);
lean_dec(v___x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_726_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_700_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_701_ = lean_int_mul(v_years_688_, v___x_700_);
v___x_702_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_695_, v___x_701_);
lean_dec(v___x_701_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_702_);
v___x_704_ = v___x_698_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_time_696_);
v___x_704_ = v_reuseFailAlloc_725_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
lean_object* v_wt_705_; lean_object* v_ltt_706_; lean_object* v_tz_707_; lean_object* v_offset_708_; lean_object* v_second_709_; lean_object* v_nano_710_; lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_nanos_717_; lean_object* v___x_718_; lean_object* v_nanos_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
lean_inc_ref(v___x_704_);
v_wt_705_ = l_Std_Time_PlainDateTime_toWallTime(v___x_704_);
lean_inc_ref(v_rules_690_);
v_ltt_706_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_690_, v_wt_705_);
v_tz_707_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_706_);
lean_dec_ref(v_ltt_706_);
v_offset_708_ = lean_ctor_get(v_tz_707_, 0);
v_second_709_ = lean_ctor_get(v_wt_705_, 0);
lean_inc(v_second_709_);
v_nano_710_ = lean_ctor_get(v_wt_705_, 1);
lean_inc(v_nano_710_);
lean_dec_ref(v_wt_705_);
v___f_711_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_711_, 0, v___x_704_);
v___x_712_ = lean_mk_thunk(v___f_711_);
v___x_713_ = lean_int_neg(v_offset_708_);
v___x_714_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_715_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_716_ = lean_int_mul(v_second_709_, v___x_715_);
lean_dec(v_second_709_);
v_nanos_717_ = lean_int_add(v___x_716_, v_nano_710_);
lean_dec(v_nano_710_);
lean_dec(v___x_716_);
v___x_718_ = lean_int_mul(v___x_713_, v___x_715_);
lean_dec(v___x_713_);
v_nanos_719_ = lean_int_add(v___x_718_, v___x_714_);
lean_dec(v___x_718_);
v___x_720_ = lean_int_add(v_nanos_717_, v_nanos_719_);
lean_dec(v_nanos_719_);
lean_dec(v_nanos_717_);
v___x_721_ = l_Std_Time_Duration_ofNanoseconds(v___x_720_);
lean_dec(v___x_720_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 3, v_tz_707_);
lean_ctor_set(v___x_692_, 1, v___x_721_);
lean_ctor_set(v___x_692_, 0, v___x_712_);
v___x_723_ = v___x_692_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_rules_690_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_tz_707_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object* v_dt_730_, lean_object* v_years_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_Time_DateTime_addYearsRollOver(v_dt_730_, v_years_731_);
lean_dec(v_years_731_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object* v_dt_733_, lean_object* v_years_734_){
_start:
{
lean_object* v_date_735_; lean_object* v_rules_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_773_; 
v_date_735_ = lean_ctor_get(v_dt_733_, 0);
v_rules_736_ = lean_ctor_get(v_dt_733_, 2);
v_isSharedCheck_773_ = !lean_is_exclusive(v_dt_733_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; lean_object* v_unused_775_; 
v_unused_774_ = lean_ctor_get(v_dt_733_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_dt_733_, 1);
lean_dec(v_unused_775_);
v___x_738_ = v_dt_733_;
v_isShared_739_ = v_isSharedCheck_773_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_rules_736_);
lean_inc(v_date_735_);
lean_dec(v_dt_733_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_773_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v_date_741_; lean_object* v_time_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_772_; 
v___x_740_ = lean_thunk_get_own(v_date_735_);
lean_dec_ref(v_date_735_);
v_date_741_ = lean_ctor_get(v___x_740_, 0);
v_time_742_ = lean_ctor_get(v___x_740_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_772_ == 0)
{
v___x_744_ = v___x_740_;
v_isShared_745_ = v_isSharedCheck_772_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_time_742_);
lean_inc(v_date_741_);
lean_dec(v___x_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_772_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_746_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_747_ = lean_int_mul(v_years_734_, v___x_746_);
v___x_748_ = l_Std_Time_PlainDate_addMonthsClip(v_date_741_, v___x_747_);
lean_dec(v___x_747_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_748_);
v___x_750_ = v___x_744_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_time_742_);
v___x_750_ = v_reuseFailAlloc_771_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v_wt_751_; lean_object* v_ltt_752_; lean_object* v_tz_753_; lean_object* v_offset_754_; lean_object* v_second_755_; lean_object* v_nano_756_; lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_nanos_763_; lean_object* v___x_764_; lean_object* v_nanos_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_769_; 
lean_inc_ref(v___x_750_);
v_wt_751_ = l_Std_Time_PlainDateTime_toWallTime(v___x_750_);
lean_inc_ref(v_rules_736_);
v_ltt_752_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_736_, v_wt_751_);
v_tz_753_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_752_);
lean_dec_ref(v_ltt_752_);
v_offset_754_ = lean_ctor_get(v_tz_753_, 0);
v_second_755_ = lean_ctor_get(v_wt_751_, 0);
lean_inc(v_second_755_);
v_nano_756_ = lean_ctor_get(v_wt_751_, 1);
lean_inc(v_nano_756_);
lean_dec_ref(v_wt_751_);
v___f_757_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_757_, 0, v___x_750_);
v___x_758_ = lean_mk_thunk(v___f_757_);
v___x_759_ = lean_int_neg(v_offset_754_);
v___x_760_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_761_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_762_ = lean_int_mul(v_second_755_, v___x_761_);
lean_dec(v_second_755_);
v_nanos_763_ = lean_int_add(v___x_762_, v_nano_756_);
lean_dec(v_nano_756_);
lean_dec(v___x_762_);
v___x_764_ = lean_int_mul(v___x_759_, v___x_761_);
lean_dec(v___x_759_);
v_nanos_765_ = lean_int_add(v___x_764_, v___x_760_);
lean_dec(v___x_764_);
v___x_766_ = lean_int_add(v_nanos_763_, v_nanos_765_);
lean_dec(v_nanos_765_);
lean_dec(v_nanos_763_);
v___x_767_ = l_Std_Time_Duration_ofNanoseconds(v___x_766_);
lean_dec(v___x_766_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 3, v_tz_753_);
lean_ctor_set(v___x_738_, 1, v___x_767_);
lean_ctor_set(v___x_738_, 0, v___x_758_);
v___x_769_ = v___x_738_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_rules_736_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v_tz_753_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object* v_dt_776_, lean_object* v_years_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Std_Time_DateTime_addYearsClip(v_dt_776_, v_years_777_);
lean_dec(v_years_777_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object* v_dt_779_, lean_object* v_years_780_){
_start:
{
lean_object* v_date_781_; lean_object* v_rules_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_820_; 
v_date_781_ = lean_ctor_get(v_dt_779_, 0);
v_rules_782_ = lean_ctor_get(v_dt_779_, 2);
v_isSharedCheck_820_ = !lean_is_exclusive(v_dt_779_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; lean_object* v_unused_822_; 
v_unused_821_ = lean_ctor_get(v_dt_779_, 3);
lean_dec(v_unused_821_);
v_unused_822_ = lean_ctor_get(v_dt_779_, 1);
lean_dec(v_unused_822_);
v___x_784_ = v_dt_779_;
v_isShared_785_ = v_isSharedCheck_820_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_rules_782_);
lean_inc(v_date_781_);
lean_dec(v_dt_779_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_820_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v_date_787_; lean_object* v_time_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_819_; 
v___x_786_ = lean_thunk_get_own(v_date_781_);
lean_dec_ref(v_date_781_);
v_date_787_ = lean_ctor_get(v___x_786_, 0);
v_time_788_ = lean_ctor_get(v___x_786_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_819_ == 0)
{
v___x_790_ = v___x_786_;
v_isShared_791_ = v_isSharedCheck_819_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_time_788_);
lean_inc(v_date_787_);
lean_dec(v___x_786_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_819_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_792_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_793_ = lean_int_mul(v_years_780_, v___x_792_);
v___x_794_ = lean_int_neg(v___x_793_);
lean_dec(v___x_793_);
v___x_795_ = l_Std_Time_PlainDate_addMonthsClip(v_date_787_, v___x_794_);
lean_dec(v___x_794_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_795_);
v___x_797_ = v___x_790_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_time_788_);
v___x_797_ = v_reuseFailAlloc_818_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v_wt_798_; lean_object* v_ltt_799_; lean_object* v_tz_800_; lean_object* v_offset_801_; lean_object* v_second_802_; lean_object* v_nano_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_nanos_810_; lean_object* v___x_811_; lean_object* v_nanos_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_816_; 
lean_inc_ref(v___x_797_);
v_wt_798_ = l_Std_Time_PlainDateTime_toWallTime(v___x_797_);
lean_inc_ref(v_rules_782_);
v_ltt_799_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_782_, v_wt_798_);
v_tz_800_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_799_);
lean_dec_ref(v_ltt_799_);
v_offset_801_ = lean_ctor_get(v_tz_800_, 0);
v_second_802_ = lean_ctor_get(v_wt_798_, 0);
lean_inc(v_second_802_);
v_nano_803_ = lean_ctor_get(v_wt_798_, 1);
lean_inc(v_nano_803_);
lean_dec_ref(v_wt_798_);
v___f_804_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_804_, 0, v___x_797_);
v___x_805_ = lean_mk_thunk(v___f_804_);
v___x_806_ = lean_int_neg(v_offset_801_);
v___x_807_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_808_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_809_ = lean_int_mul(v_second_802_, v___x_808_);
lean_dec(v_second_802_);
v_nanos_810_ = lean_int_add(v___x_809_, v_nano_803_);
lean_dec(v_nano_803_);
lean_dec(v___x_809_);
v___x_811_ = lean_int_mul(v___x_806_, v___x_808_);
lean_dec(v___x_806_);
v_nanos_812_ = lean_int_add(v___x_811_, v___x_807_);
lean_dec(v___x_811_);
v___x_813_ = lean_int_add(v_nanos_810_, v_nanos_812_);
lean_dec(v_nanos_812_);
lean_dec(v_nanos_810_);
v___x_814_ = l_Std_Time_Duration_ofNanoseconds(v___x_813_);
lean_dec(v___x_813_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 3, v_tz_800_);
lean_ctor_set(v___x_784_, 1, v___x_814_);
lean_ctor_set(v___x_784_, 0, v___x_805_);
v___x_816_ = v___x_784_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_rules_782_);
lean_ctor_set(v_reuseFailAlloc_817_, 3, v_tz_800_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object* v_dt_823_, lean_object* v_years_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_Time_DateTime_subYearsClip(v_dt_823_, v_years_824_);
lean_dec(v_years_824_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object* v_dt_826_, lean_object* v_years_827_){
_start:
{
lean_object* v_date_828_; lean_object* v_rules_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_867_; 
v_date_828_ = lean_ctor_get(v_dt_826_, 0);
v_rules_829_ = lean_ctor_get(v_dt_826_, 2);
v_isSharedCheck_867_ = !lean_is_exclusive(v_dt_826_);
if (v_isSharedCheck_867_ == 0)
{
lean_object* v_unused_868_; lean_object* v_unused_869_; 
v_unused_868_ = lean_ctor_get(v_dt_826_, 3);
lean_dec(v_unused_868_);
v_unused_869_ = lean_ctor_get(v_dt_826_, 1);
lean_dec(v_unused_869_);
v___x_831_ = v_dt_826_;
v_isShared_832_ = v_isSharedCheck_867_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_rules_829_);
lean_inc(v_date_828_);
lean_dec(v_dt_826_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_867_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v_date_834_; lean_object* v_time_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_866_; 
v___x_833_ = lean_thunk_get_own(v_date_828_);
lean_dec_ref(v_date_828_);
v_date_834_ = lean_ctor_get(v___x_833_, 0);
v_time_835_ = lean_ctor_get(v___x_833_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_866_ == 0)
{
v___x_837_ = v___x_833_;
v_isShared_838_ = v_isSharedCheck_866_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_time_835_);
lean_inc(v_date_834_);
lean_dec(v___x_833_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_866_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_839_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_840_ = lean_int_mul(v_years_827_, v___x_839_);
v___x_841_ = lean_int_neg(v___x_840_);
lean_dec(v___x_840_);
v___x_842_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_834_, v___x_841_);
lean_dec(v___x_841_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_842_);
v___x_844_ = v___x_837_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_time_835_);
v___x_844_ = v_reuseFailAlloc_865_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v_wt_845_; lean_object* v_ltt_846_; lean_object* v_tz_847_; lean_object* v_offset_848_; lean_object* v_second_849_; lean_object* v_nano_850_; lean_object* v___f_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_nanos_857_; lean_object* v___x_858_; lean_object* v_nanos_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
lean_inc_ref(v___x_844_);
v_wt_845_ = l_Std_Time_PlainDateTime_toWallTime(v___x_844_);
lean_inc_ref(v_rules_829_);
v_ltt_846_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_829_, v_wt_845_);
v_tz_847_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_846_);
lean_dec_ref(v_ltt_846_);
v_offset_848_ = lean_ctor_get(v_tz_847_, 0);
v_second_849_ = lean_ctor_get(v_wt_845_, 0);
lean_inc(v_second_849_);
v_nano_850_ = lean_ctor_get(v_wt_845_, 1);
lean_inc(v_nano_850_);
lean_dec_ref(v_wt_845_);
v___f_851_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_851_, 0, v___x_844_);
v___x_852_ = lean_mk_thunk(v___f_851_);
v___x_853_ = lean_int_neg(v_offset_848_);
v___x_854_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_855_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_856_ = lean_int_mul(v_second_849_, v___x_855_);
lean_dec(v_second_849_);
v_nanos_857_ = lean_int_add(v___x_856_, v_nano_850_);
lean_dec(v_nano_850_);
lean_dec(v___x_856_);
v___x_858_ = lean_int_mul(v___x_853_, v___x_855_);
lean_dec(v___x_853_);
v_nanos_859_ = lean_int_add(v___x_858_, v___x_854_);
lean_dec(v___x_858_);
v___x_860_ = lean_int_add(v_nanos_857_, v_nanos_859_);
lean_dec(v_nanos_859_);
lean_dec(v_nanos_857_);
v___x_861_ = l_Std_Time_Duration_ofNanoseconds(v___x_860_);
lean_dec(v___x_860_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 3, v_tz_847_);
lean_ctor_set(v___x_831_, 1, v___x_861_);
lean_ctor_set(v___x_831_, 0, v___x_852_);
v___x_863_ = v___x_831_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_852_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_rules_829_);
lean_ctor_set(v_reuseFailAlloc_864_, 3, v_tz_847_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object* v_dt_870_, lean_object* v_years_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_Time_DateTime_subYearsRollOver(v_dt_870_, v_years_871_);
lean_dec(v_years_871_);
return v_res_872_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(3600u);
v___x_874_ = lean_nat_to_int(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object* v_dt_875_, lean_object* v_hours_876_){
_start:
{
lean_object* v_timestamp_877_; lean_object* v_rules_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_900_; 
v_timestamp_877_ = lean_ctor_get(v_dt_875_, 1);
v_rules_878_ = lean_ctor_get(v_dt_875_, 2);
v_isSharedCheck_900_ = !lean_is_exclusive(v_dt_875_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; lean_object* v_unused_902_; 
v_unused_901_ = lean_ctor_get(v_dt_875_, 3);
lean_dec(v_unused_901_);
v_unused_902_ = lean_ctor_get(v_dt_875_, 0);
lean_dec(v_unused_902_);
v___x_880_ = v_dt_875_;
v_isShared_881_ = v_isSharedCheck_900_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_rules_878_);
lean_inc(v_timestamp_877_);
lean_dec(v_dt_875_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_900_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_second_882_; lean_object* v_nano_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v_nanos_889_; lean_object* v___x_890_; lean_object* v_nanos_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_tz_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v_second_882_ = lean_ctor_get(v_timestamp_877_, 0);
lean_inc(v_second_882_);
v_nano_883_ = lean_ctor_get(v_timestamp_877_, 1);
lean_inc(v_nano_883_);
lean_dec_ref(v_timestamp_877_);
v___x_884_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_885_ = lean_int_mul(v_hours_876_, v___x_884_);
v___x_886_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_887_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_888_ = lean_int_mul(v_second_882_, v___x_887_);
lean_dec(v_second_882_);
v_nanos_889_ = lean_int_add(v___x_888_, v_nano_883_);
lean_dec(v_nano_883_);
lean_dec(v___x_888_);
v___x_890_ = lean_int_mul(v___x_885_, v___x_887_);
lean_dec(v___x_885_);
v_nanos_891_ = lean_int_add(v___x_890_, v___x_886_);
lean_dec(v___x_890_);
v___x_892_ = lean_int_add(v_nanos_889_, v_nanos_891_);
lean_dec(v_nanos_891_);
lean_dec(v_nanos_889_);
v___x_893_ = l_Std_Time_Duration_ofNanoseconds(v___x_892_);
lean_dec(v___x_892_);
lean_inc_ref(v_rules_878_);
v_tz_894_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_878_, v___x_893_);
lean_inc_ref(v___x_893_);
lean_inc_ref(v_tz_894_);
v___f_895_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_895_, 0, v_tz_894_);
lean_closure_set(v___f_895_, 1, v___x_893_);
lean_closure_set(v___f_895_, 2, v___x_887_);
lean_closure_set(v___f_895_, 3, v___x_886_);
v___x_896_ = lean_mk_thunk(v___f_895_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 3, v_tz_894_);
lean_ctor_set(v___x_880_, 1, v___x_893_);
lean_ctor_set(v___x_880_, 0, v___x_896_);
v___x_898_ = v___x_880_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_899_, 2, v_rules_878_);
lean_ctor_set(v_reuseFailAlloc_899_, 3, v_tz_894_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object* v_dt_903_, lean_object* v_hours_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_Time_DateTime_addHours(v_dt_903_, v_hours_904_);
lean_dec(v_hours_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object* v_dt_906_, lean_object* v_hours_907_){
_start:
{
lean_object* v_timestamp_908_; lean_object* v_rules_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_933_; 
v_timestamp_908_ = lean_ctor_get(v_dt_906_, 1);
v_rules_909_ = lean_ctor_get(v_dt_906_, 2);
v_isSharedCheck_933_ = !lean_is_exclusive(v_dt_906_);
if (v_isSharedCheck_933_ == 0)
{
lean_object* v_unused_934_; lean_object* v_unused_935_; 
v_unused_934_ = lean_ctor_get(v_dt_906_, 3);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_dt_906_, 0);
lean_dec(v_unused_935_);
v___x_911_ = v_dt_906_;
v_isShared_912_ = v_isSharedCheck_933_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_rules_909_);
lean_inc(v_timestamp_908_);
lean_dec(v_dt_906_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_933_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v_second_913_; lean_object* v_nano_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v_nanos_922_; lean_object* v___x_923_; lean_object* v_nanos_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_tz_927_; lean_object* v___f_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v_second_913_ = lean_ctor_get(v_timestamp_908_, 0);
lean_inc(v_second_913_);
v_nano_914_ = lean_ctor_get(v_timestamp_908_, 1);
lean_inc(v_nano_914_);
lean_dec_ref(v_timestamp_908_);
v___x_915_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_916_ = lean_int_mul(v_hours_907_, v___x_915_);
v___x_917_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_918_ = lean_int_neg(v___x_916_);
lean_dec(v___x_916_);
v___x_919_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_920_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_921_ = lean_int_mul(v_second_913_, v___x_920_);
lean_dec(v_second_913_);
v_nanos_922_ = lean_int_add(v___x_921_, v_nano_914_);
lean_dec(v_nano_914_);
lean_dec(v___x_921_);
v___x_923_ = lean_int_mul(v___x_918_, v___x_920_);
lean_dec(v___x_918_);
v_nanos_924_ = lean_int_add(v___x_923_, v___x_919_);
lean_dec(v___x_923_);
v___x_925_ = lean_int_add(v_nanos_922_, v_nanos_924_);
lean_dec(v_nanos_924_);
lean_dec(v_nanos_922_);
v___x_926_ = l_Std_Time_Duration_ofNanoseconds(v___x_925_);
lean_dec(v___x_925_);
lean_inc_ref(v_rules_909_);
v_tz_927_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_909_, v___x_926_);
lean_inc_ref(v___x_926_);
lean_inc_ref(v_tz_927_);
v___f_928_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_928_, 0, v_tz_927_);
lean_closure_set(v___f_928_, 1, v___x_926_);
lean_closure_set(v___f_928_, 2, v___x_920_);
lean_closure_set(v___f_928_, 3, v___x_917_);
v___x_929_ = lean_mk_thunk(v___f_928_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 3, v_tz_927_);
lean_ctor_set(v___x_911_, 1, v___x_926_);
lean_ctor_set(v___x_911_, 0, v___x_929_);
v___x_931_ = v___x_911_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_rules_909_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_tz_927_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object* v_dt_936_, lean_object* v_hours_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_Time_DateTime_subHours(v_dt_936_, v_hours_937_);
lean_dec(v_hours_937_);
return v_res_938_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = lean_unsigned_to_nat(60u);
v___x_940_ = lean_nat_to_int(v___x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object* v_dt_941_, lean_object* v_minutes_942_){
_start:
{
lean_object* v_timestamp_943_; lean_object* v_rules_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_966_; 
v_timestamp_943_ = lean_ctor_get(v_dt_941_, 1);
v_rules_944_ = lean_ctor_get(v_dt_941_, 2);
v_isSharedCheck_966_ = !lean_is_exclusive(v_dt_941_);
if (v_isSharedCheck_966_ == 0)
{
lean_object* v_unused_967_; lean_object* v_unused_968_; 
v_unused_967_ = lean_ctor_get(v_dt_941_, 3);
lean_dec(v_unused_967_);
v_unused_968_ = lean_ctor_get(v_dt_941_, 0);
lean_dec(v_unused_968_);
v___x_946_ = v_dt_941_;
v_isShared_947_ = v_isSharedCheck_966_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_rules_944_);
lean_inc(v_timestamp_943_);
lean_dec(v_dt_941_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_966_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_second_948_; lean_object* v_nano_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_nanos_955_; lean_object* v___x_956_; lean_object* v_nanos_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v_tz_960_; lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v_second_948_ = lean_ctor_get(v_timestamp_943_, 0);
lean_inc(v_second_948_);
v_nano_949_ = lean_ctor_get(v_timestamp_943_, 1);
lean_inc(v_nano_949_);
lean_dec_ref(v_timestamp_943_);
v___x_950_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_951_ = lean_int_mul(v_minutes_942_, v___x_950_);
v___x_952_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_953_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_954_ = lean_int_mul(v_second_948_, v___x_953_);
lean_dec(v_second_948_);
v_nanos_955_ = lean_int_add(v___x_954_, v_nano_949_);
lean_dec(v_nano_949_);
lean_dec(v___x_954_);
v___x_956_ = lean_int_mul(v___x_951_, v___x_953_);
lean_dec(v___x_951_);
v_nanos_957_ = lean_int_add(v___x_956_, v___x_952_);
lean_dec(v___x_956_);
v___x_958_ = lean_int_add(v_nanos_955_, v_nanos_957_);
lean_dec(v_nanos_957_);
lean_dec(v_nanos_955_);
v___x_959_ = l_Std_Time_Duration_ofNanoseconds(v___x_958_);
lean_dec(v___x_958_);
lean_inc_ref(v_rules_944_);
v_tz_960_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_944_, v___x_959_);
lean_inc_ref(v___x_959_);
lean_inc_ref(v_tz_960_);
v___f_961_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_961_, 0, v_tz_960_);
lean_closure_set(v___f_961_, 1, v___x_959_);
lean_closure_set(v___f_961_, 2, v___x_953_);
lean_closure_set(v___f_961_, 3, v___x_952_);
v___x_962_ = lean_mk_thunk(v___f_961_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 3, v_tz_960_);
lean_ctor_set(v___x_946_, 1, v___x_959_);
lean_ctor_set(v___x_946_, 0, v___x_962_);
v___x_964_ = v___x_946_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v___x_959_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_rules_944_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_tz_960_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object* v_dt_969_, lean_object* v_minutes_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Std_Time_DateTime_addMinutes(v_dt_969_, v_minutes_970_);
lean_dec(v_minutes_970_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object* v_dt_972_, lean_object* v_minutes_973_){
_start:
{
lean_object* v_timestamp_974_; lean_object* v_rules_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_999_; 
v_timestamp_974_ = lean_ctor_get(v_dt_972_, 1);
v_rules_975_ = lean_ctor_get(v_dt_972_, 2);
v_isSharedCheck_999_ = !lean_is_exclusive(v_dt_972_);
if (v_isSharedCheck_999_ == 0)
{
lean_object* v_unused_1000_; lean_object* v_unused_1001_; 
v_unused_1000_ = lean_ctor_get(v_dt_972_, 3);
lean_dec(v_unused_1000_);
v_unused_1001_ = lean_ctor_get(v_dt_972_, 0);
lean_dec(v_unused_1001_);
v___x_977_ = v_dt_972_;
v_isShared_978_ = v_isSharedCheck_999_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_rules_975_);
lean_inc(v_timestamp_974_);
lean_dec(v_dt_972_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_999_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_second_979_; lean_object* v_nano_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v_nanos_988_; lean_object* v___x_989_; lean_object* v_nanos_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_tz_993_; lean_object* v___f_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v_second_979_ = lean_ctor_get(v_timestamp_974_, 0);
lean_inc(v_second_979_);
v_nano_980_ = lean_ctor_get(v_timestamp_974_, 1);
lean_inc(v_nano_980_);
lean_dec_ref(v_timestamp_974_);
v___x_981_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_982_ = lean_int_mul(v_minutes_973_, v___x_981_);
v___x_983_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_984_ = lean_int_neg(v___x_982_);
lean_dec(v___x_982_);
v___x_985_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_986_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_987_ = lean_int_mul(v_second_979_, v___x_986_);
lean_dec(v_second_979_);
v_nanos_988_ = lean_int_add(v___x_987_, v_nano_980_);
lean_dec(v_nano_980_);
lean_dec(v___x_987_);
v___x_989_ = lean_int_mul(v___x_984_, v___x_986_);
lean_dec(v___x_984_);
v_nanos_990_ = lean_int_add(v___x_989_, v___x_985_);
lean_dec(v___x_989_);
v___x_991_ = lean_int_add(v_nanos_988_, v_nanos_990_);
lean_dec(v_nanos_990_);
lean_dec(v_nanos_988_);
v___x_992_ = l_Std_Time_Duration_ofNanoseconds(v___x_991_);
lean_dec(v___x_991_);
lean_inc_ref(v_rules_975_);
v_tz_993_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_975_, v___x_992_);
lean_inc_ref(v___x_992_);
lean_inc_ref(v_tz_993_);
v___f_994_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_994_, 0, v_tz_993_);
lean_closure_set(v___f_994_, 1, v___x_992_);
lean_closure_set(v___f_994_, 2, v___x_986_);
lean_closure_set(v___f_994_, 3, v___x_983_);
v___x_995_ = lean_mk_thunk(v___f_994_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 3, v_tz_993_);
lean_ctor_set(v___x_977_, 1, v___x_992_);
lean_ctor_set(v___x_977_, 0, v___x_995_);
v___x_997_ = v___x_977_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_rules_975_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_tz_993_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object* v_dt_1002_, lean_object* v_minutes_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Std_Time_DateTime_subMinutes(v_dt_1002_, v_minutes_1003_);
lean_dec(v_minutes_1003_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0(lean_object* v_tz_1005_, lean_object* v___x_1006_, lean_object* v___x_1007_, lean_object* v_x_1008_){
_start:
{
lean_object* v_offset_1009_; lean_object* v_second_1010_; lean_object* v_nano_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v_nanos_1014_; lean_object* v___x_1015_; lean_object* v_nanos_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_offset_1009_ = lean_ctor_get(v_tz_1005_, 0);
v_second_1010_ = lean_ctor_get(v___x_1006_, 0);
v_nano_1011_ = lean_ctor_get(v___x_1006_, 1);
v___x_1012_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1013_ = lean_int_mul(v_second_1010_, v___x_1007_);
v_nanos_1014_ = lean_int_add(v___x_1013_, v_nano_1011_);
lean_dec(v___x_1013_);
v___x_1015_ = lean_int_mul(v_offset_1009_, v___x_1007_);
v_nanos_1016_ = lean_int_add(v___x_1015_, v___x_1012_);
lean_dec(v___x_1015_);
v___x_1017_ = lean_int_add(v_nanos_1014_, v_nanos_1016_);
lean_dec(v_nanos_1016_);
lean_dec(v_nanos_1014_);
v___x_1018_ = l_Std_Time_Duration_ofNanoseconds(v___x_1017_);
lean_dec(v___x_1017_);
v___x_1019_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1018_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(lean_object* v_tz_1020_, lean_object* v___x_1021_, lean_object* v___x_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Std_Time_DateTime_addMilliseconds___lam__0(v_tz_1020_, v___x_1021_, v___x_1022_, v_x_1023_);
lean_dec(v___x_1022_);
lean_dec_ref(v___x_1021_);
lean_dec_ref(v_tz_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object* v_dt_1025_, lean_object* v_milliseconds_1026_){
_start:
{
lean_object* v_timestamp_1027_; lean_object* v_rules_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1052_; 
v_timestamp_1027_ = lean_ctor_get(v_dt_1025_, 1);
v_rules_1028_ = lean_ctor_get(v_dt_1025_, 2);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_dt_1025_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; lean_object* v_unused_1054_; 
v_unused_1053_ = lean_ctor_get(v_dt_1025_, 3);
lean_dec(v_unused_1053_);
v_unused_1054_ = lean_ctor_get(v_dt_1025_, 0);
lean_dec(v_unused_1054_);
v___x_1030_ = v_dt_1025_;
v_isShared_1031_ = v_isSharedCheck_1052_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_rules_1028_);
lean_inc(v_timestamp_1027_);
lean_dec(v_dt_1025_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1052_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_second_1032_; lean_object* v_nano_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v_second_1037_; lean_object* v_nano_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_nanos_1041_; lean_object* v___x_1042_; lean_object* v_nanos_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_tz_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_second_1032_ = lean_ctor_get(v_timestamp_1027_, 0);
lean_inc(v_second_1032_);
v_nano_1033_ = lean_ctor_get(v_timestamp_1027_, 1);
lean_inc(v_nano_1033_);
lean_dec_ref(v_timestamp_1027_);
v___x_1034_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1035_ = lean_int_mul(v_milliseconds_1026_, v___x_1034_);
v___x_1036_ = l_Std_Time_Duration_ofNanoseconds(v___x_1035_);
lean_dec(v___x_1035_);
v_second_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_second_1037_);
v_nano_1038_ = lean_ctor_get(v___x_1036_, 1);
lean_inc(v_nano_1038_);
lean_dec_ref(v___x_1036_);
v___x_1039_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1040_ = lean_int_mul(v_second_1032_, v___x_1039_);
lean_dec(v_second_1032_);
v_nanos_1041_ = lean_int_add(v___x_1040_, v_nano_1033_);
lean_dec(v_nano_1033_);
lean_dec(v___x_1040_);
v___x_1042_ = lean_int_mul(v_second_1037_, v___x_1039_);
lean_dec(v_second_1037_);
v_nanos_1043_ = lean_int_add(v___x_1042_, v_nano_1038_);
lean_dec(v_nano_1038_);
lean_dec(v___x_1042_);
v___x_1044_ = lean_int_add(v_nanos_1041_, v_nanos_1043_);
lean_dec(v_nanos_1043_);
lean_dec(v_nanos_1041_);
v___x_1045_ = l_Std_Time_Duration_ofNanoseconds(v___x_1044_);
lean_dec(v___x_1044_);
lean_inc_ref(v_rules_1028_);
v_tz_1046_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1028_, v___x_1045_);
lean_inc_ref(v___x_1045_);
lean_inc_ref(v_tz_1046_);
v___f_1047_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1047_, 0, v_tz_1046_);
lean_closure_set(v___f_1047_, 1, v___x_1045_);
lean_closure_set(v___f_1047_, 2, v___x_1039_);
v___x_1048_ = lean_mk_thunk(v___f_1047_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set(v___x_1030_, 3, v_tz_1046_);
lean_ctor_set(v___x_1030_, 1, v___x_1045_);
lean_ctor_set(v___x_1030_, 0, v___x_1048_);
v___x_1050_ = v___x_1030_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_rules_1028_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_tz_1046_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object* v_dt_1055_, lean_object* v_milliseconds_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Std_Time_DateTime_addMilliseconds(v_dt_1055_, v_milliseconds_1056_);
lean_dec(v_milliseconds_1056_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object* v_dt_1058_, lean_object* v_milliseconds_1059_){
_start:
{
lean_object* v_timestamp_1060_; lean_object* v_rules_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1087_; 
v_timestamp_1060_ = lean_ctor_get(v_dt_1058_, 1);
v_rules_1061_ = lean_ctor_get(v_dt_1058_, 2);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_dt_1058_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; lean_object* v_unused_1089_; 
v_unused_1088_ = lean_ctor_get(v_dt_1058_, 3);
lean_dec(v_unused_1088_);
v_unused_1089_ = lean_ctor_get(v_dt_1058_, 0);
lean_dec(v_unused_1089_);
v___x_1063_ = v_dt_1058_;
v_isShared_1064_ = v_isSharedCheck_1087_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_rules_1061_);
lean_inc(v_timestamp_1060_);
lean_dec(v_dt_1058_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1087_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_second_1068_; lean_object* v_nano_1069_; lean_object* v_second_1070_; lean_object* v_nano_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_nanos_1076_; lean_object* v___x_1077_; lean_object* v_nanos_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_tz_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1065_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1066_ = lean_int_mul(v_milliseconds_1059_, v___x_1065_);
v___x_1067_ = l_Std_Time_Duration_ofNanoseconds(v___x_1066_);
lean_dec(v___x_1066_);
v_second_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_second_1068_);
v_nano_1069_ = lean_ctor_get(v___x_1067_, 1);
lean_inc(v_nano_1069_);
lean_dec_ref(v___x_1067_);
v_second_1070_ = lean_ctor_get(v_timestamp_1060_, 0);
lean_inc(v_second_1070_);
v_nano_1071_ = lean_ctor_get(v_timestamp_1060_, 1);
lean_inc(v_nano_1071_);
lean_dec_ref(v_timestamp_1060_);
v___x_1072_ = lean_int_neg(v_second_1068_);
lean_dec(v_second_1068_);
v___x_1073_ = lean_int_neg(v_nano_1069_);
lean_dec(v_nano_1069_);
v___x_1074_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1075_ = lean_int_mul(v_second_1070_, v___x_1074_);
lean_dec(v_second_1070_);
v_nanos_1076_ = lean_int_add(v___x_1075_, v_nano_1071_);
lean_dec(v_nano_1071_);
lean_dec(v___x_1075_);
v___x_1077_ = lean_int_mul(v___x_1072_, v___x_1074_);
lean_dec(v___x_1072_);
v_nanos_1078_ = lean_int_add(v___x_1077_, v___x_1073_);
lean_dec(v___x_1073_);
lean_dec(v___x_1077_);
v___x_1079_ = lean_int_add(v_nanos_1076_, v_nanos_1078_);
lean_dec(v_nanos_1078_);
lean_dec(v_nanos_1076_);
v___x_1080_ = l_Std_Time_Duration_ofNanoseconds(v___x_1079_);
lean_dec(v___x_1079_);
lean_inc_ref(v_rules_1061_);
v_tz_1081_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1061_, v___x_1080_);
lean_inc_ref(v___x_1080_);
lean_inc_ref(v_tz_1081_);
v___f_1082_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1082_, 0, v_tz_1081_);
lean_closure_set(v___f_1082_, 1, v___x_1080_);
lean_closure_set(v___f_1082_, 2, v___x_1074_);
v___x_1083_ = lean_mk_thunk(v___f_1082_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 3, v_tz_1081_);
lean_ctor_set(v___x_1063_, 1, v___x_1080_);
lean_ctor_set(v___x_1063_, 0, v___x_1083_);
v___x_1085_ = v___x_1063_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v_rules_1061_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v_tz_1081_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object* v_dt_1090_, lean_object* v_milliseconds_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Std_Time_DateTime_subMilliseconds(v_dt_1090_, v_milliseconds_1091_);
lean_dec(v_milliseconds_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object* v_dt_1093_, lean_object* v_seconds_1094_){
_start:
{
lean_object* v_timestamp_1095_; lean_object* v_rules_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1116_; 
v_timestamp_1095_ = lean_ctor_get(v_dt_1093_, 1);
v_rules_1096_ = lean_ctor_get(v_dt_1093_, 2);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_dt_1093_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; lean_object* v_unused_1118_; 
v_unused_1117_ = lean_ctor_get(v_dt_1093_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_dt_1093_, 0);
lean_dec(v_unused_1118_);
v___x_1098_ = v_dt_1093_;
v_isShared_1099_ = v_isSharedCheck_1116_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_rules_1096_);
lean_inc(v_timestamp_1095_);
lean_dec(v_dt_1093_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1116_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_second_1100_; lean_object* v_nano_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v_nanos_1105_; lean_object* v___x_1106_; lean_object* v_nanos_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_tz_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v_second_1100_ = lean_ctor_get(v_timestamp_1095_, 0);
lean_inc(v_second_1100_);
v_nano_1101_ = lean_ctor_get(v_timestamp_1095_, 1);
lean_inc(v_nano_1101_);
lean_dec_ref(v_timestamp_1095_);
v___x_1102_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1103_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1104_ = lean_int_mul(v_second_1100_, v___x_1103_);
lean_dec(v_second_1100_);
v_nanos_1105_ = lean_int_add(v___x_1104_, v_nano_1101_);
lean_dec(v_nano_1101_);
lean_dec(v___x_1104_);
v___x_1106_ = lean_int_mul(v_seconds_1094_, v___x_1103_);
v_nanos_1107_ = lean_int_add(v___x_1106_, v___x_1102_);
lean_dec(v___x_1106_);
v___x_1108_ = lean_int_add(v_nanos_1105_, v_nanos_1107_);
lean_dec(v_nanos_1107_);
lean_dec(v_nanos_1105_);
v___x_1109_ = l_Std_Time_Duration_ofNanoseconds(v___x_1108_);
lean_dec(v___x_1108_);
lean_inc_ref(v_rules_1096_);
v_tz_1110_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1096_, v___x_1109_);
lean_inc_ref(v___x_1109_);
lean_inc_ref(v_tz_1110_);
v___f_1111_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1111_, 0, v_tz_1110_);
lean_closure_set(v___f_1111_, 1, v___x_1109_);
lean_closure_set(v___f_1111_, 2, v___x_1103_);
lean_closure_set(v___f_1111_, 3, v___x_1102_);
v___x_1112_ = lean_mk_thunk(v___f_1111_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 3, v_tz_1110_);
lean_ctor_set(v___x_1098_, 1, v___x_1109_);
lean_ctor_set(v___x_1098_, 0, v___x_1112_);
v___x_1114_ = v___x_1098_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_rules_1096_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_tz_1110_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object* v_dt_1119_, lean_object* v_seconds_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_Time_DateTime_addSeconds(v_dt_1119_, v_seconds_1120_);
lean_dec(v_seconds_1120_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object* v_dt_1122_, lean_object* v_seconds_1123_){
_start:
{
lean_object* v_timestamp_1124_; lean_object* v_rules_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1147_; 
v_timestamp_1124_ = lean_ctor_get(v_dt_1122_, 1);
v_rules_1125_ = lean_ctor_get(v_dt_1122_, 2);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_dt_1122_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; lean_object* v_unused_1149_; 
v_unused_1148_ = lean_ctor_get(v_dt_1122_, 3);
lean_dec(v_unused_1148_);
v_unused_1149_ = lean_ctor_get(v_dt_1122_, 0);
lean_dec(v_unused_1149_);
v___x_1127_ = v_dt_1122_;
v_isShared_1128_ = v_isSharedCheck_1147_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_rules_1125_);
lean_inc(v_timestamp_1124_);
lean_dec(v_dt_1122_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1147_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v_second_1129_; lean_object* v_nano_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_nanos_1136_; lean_object* v___x_1137_; lean_object* v_nanos_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v_tz_1141_; lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v_second_1129_ = lean_ctor_get(v_timestamp_1124_, 0);
lean_inc(v_second_1129_);
v_nano_1130_ = lean_ctor_get(v_timestamp_1124_, 1);
lean_inc(v_nano_1130_);
lean_dec_ref(v_timestamp_1124_);
v___x_1131_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1132_ = lean_int_neg(v_seconds_1123_);
v___x_1133_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1134_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1135_ = lean_int_mul(v_second_1129_, v___x_1134_);
lean_dec(v_second_1129_);
v_nanos_1136_ = lean_int_add(v___x_1135_, v_nano_1130_);
lean_dec(v_nano_1130_);
lean_dec(v___x_1135_);
v___x_1137_ = lean_int_mul(v___x_1132_, v___x_1134_);
lean_dec(v___x_1132_);
v_nanos_1138_ = lean_int_add(v___x_1137_, v___x_1133_);
lean_dec(v___x_1137_);
v___x_1139_ = lean_int_add(v_nanos_1136_, v_nanos_1138_);
lean_dec(v_nanos_1138_);
lean_dec(v_nanos_1136_);
v___x_1140_ = l_Std_Time_Duration_ofNanoseconds(v___x_1139_);
lean_dec(v___x_1139_);
lean_inc_ref(v_rules_1125_);
v_tz_1141_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1125_, v___x_1140_);
lean_inc_ref(v___x_1140_);
lean_inc_ref(v_tz_1141_);
v___f_1142_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1142_, 0, v_tz_1141_);
lean_closure_set(v___f_1142_, 1, v___x_1140_);
lean_closure_set(v___f_1142_, 2, v___x_1134_);
lean_closure_set(v___f_1142_, 3, v___x_1131_);
v___x_1143_ = lean_mk_thunk(v___f_1142_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 3, v_tz_1141_);
lean_ctor_set(v___x_1127_, 1, v___x_1140_);
lean_ctor_set(v___x_1127_, 0, v___x_1143_);
v___x_1145_ = v___x_1127_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_rules_1125_);
lean_ctor_set(v_reuseFailAlloc_1146_, 3, v_tz_1141_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object* v_dt_1150_, lean_object* v_seconds_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Std_Time_DateTime_subSeconds(v_dt_1150_, v_seconds_1151_);
lean_dec(v_seconds_1151_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object* v_dt_1153_, lean_object* v_nanoseconds_1154_){
_start:
{
lean_object* v_timestamp_1155_; lean_object* v_rules_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1178_; 
v_timestamp_1155_ = lean_ctor_get(v_dt_1153_, 1);
v_rules_1156_ = lean_ctor_get(v_dt_1153_, 2);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_dt_1153_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; 
v_unused_1179_ = lean_ctor_get(v_dt_1153_, 3);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_dt_1153_, 0);
lean_dec(v_unused_1180_);
v___x_1158_ = v_dt_1153_;
v_isShared_1159_ = v_isSharedCheck_1178_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_rules_1156_);
lean_inc(v_timestamp_1155_);
lean_dec(v_dt_1153_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1178_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_second_1160_; lean_object* v_nano_1161_; lean_object* v___x_1162_; lean_object* v_second_1163_; lean_object* v_nano_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_nanos_1167_; lean_object* v___x_1168_; lean_object* v_nanos_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_tz_1172_; lean_object* v___f_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v_second_1160_ = lean_ctor_get(v_timestamp_1155_, 0);
lean_inc(v_second_1160_);
v_nano_1161_ = lean_ctor_get(v_timestamp_1155_, 1);
lean_inc(v_nano_1161_);
lean_dec_ref(v_timestamp_1155_);
v___x_1162_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1154_);
v_second_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_second_1163_);
v_nano_1164_ = lean_ctor_get(v___x_1162_, 1);
lean_inc(v_nano_1164_);
lean_dec_ref(v___x_1162_);
v___x_1165_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1166_ = lean_int_mul(v_second_1160_, v___x_1165_);
lean_dec(v_second_1160_);
v_nanos_1167_ = lean_int_add(v___x_1166_, v_nano_1161_);
lean_dec(v_nano_1161_);
lean_dec(v___x_1166_);
v___x_1168_ = lean_int_mul(v_second_1163_, v___x_1165_);
lean_dec(v_second_1163_);
v_nanos_1169_ = lean_int_add(v___x_1168_, v_nano_1164_);
lean_dec(v_nano_1164_);
lean_dec(v___x_1168_);
v___x_1170_ = lean_int_add(v_nanos_1167_, v_nanos_1169_);
lean_dec(v_nanos_1169_);
lean_dec(v_nanos_1167_);
v___x_1171_ = l_Std_Time_Duration_ofNanoseconds(v___x_1170_);
lean_dec(v___x_1170_);
lean_inc_ref(v_rules_1156_);
v_tz_1172_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1156_, v___x_1171_);
lean_inc_ref(v___x_1171_);
lean_inc_ref(v_tz_1172_);
v___f_1173_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1173_, 0, v_tz_1172_);
lean_closure_set(v___f_1173_, 1, v___x_1171_);
lean_closure_set(v___f_1173_, 2, v___x_1165_);
v___x_1174_ = lean_mk_thunk(v___f_1173_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 3, v_tz_1172_);
lean_ctor_set(v___x_1158_, 1, v___x_1171_);
lean_ctor_set(v___x_1158_, 0, v___x_1174_);
v___x_1176_ = v___x_1158_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v_rules_1156_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_tz_1172_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object* v_dt_1181_, lean_object* v_nanoseconds_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Std_Time_DateTime_addNanoseconds(v_dt_1181_, v_nanoseconds_1182_);
lean_dec(v_nanoseconds_1182_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object* v_dt_1184_, lean_object* v_nanoseconds_1185_){
_start:
{
lean_object* v_timestamp_1186_; lean_object* v_rules_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1211_; 
v_timestamp_1186_ = lean_ctor_get(v_dt_1184_, 1);
v_rules_1187_ = lean_ctor_get(v_dt_1184_, 2);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_dt_1184_);
if (v_isSharedCheck_1211_ == 0)
{
lean_object* v_unused_1212_; lean_object* v_unused_1213_; 
v_unused_1212_ = lean_ctor_get(v_dt_1184_, 3);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_dt_1184_, 0);
lean_dec(v_unused_1213_);
v___x_1189_ = v_dt_1184_;
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_rules_1187_);
lean_inc(v_timestamp_1186_);
lean_dec(v_dt_1184_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1211_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v_second_1192_; lean_object* v_nano_1193_; lean_object* v_second_1194_; lean_object* v_nano_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v_nanos_1200_; lean_object* v___x_1201_; lean_object* v_nanos_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_tz_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1191_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1185_);
v_second_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_second_1192_);
v_nano_1193_ = lean_ctor_get(v___x_1191_, 1);
lean_inc(v_nano_1193_);
lean_dec_ref(v___x_1191_);
v_second_1194_ = lean_ctor_get(v_timestamp_1186_, 0);
lean_inc(v_second_1194_);
v_nano_1195_ = lean_ctor_get(v_timestamp_1186_, 1);
lean_inc(v_nano_1195_);
lean_dec_ref(v_timestamp_1186_);
v___x_1196_ = lean_int_neg(v_second_1192_);
lean_dec(v_second_1192_);
v___x_1197_ = lean_int_neg(v_nano_1193_);
lean_dec(v_nano_1193_);
v___x_1198_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1199_ = lean_int_mul(v_second_1194_, v___x_1198_);
lean_dec(v_second_1194_);
v_nanos_1200_ = lean_int_add(v___x_1199_, v_nano_1195_);
lean_dec(v_nano_1195_);
lean_dec(v___x_1199_);
v___x_1201_ = lean_int_mul(v___x_1196_, v___x_1198_);
lean_dec(v___x_1196_);
v_nanos_1202_ = lean_int_add(v___x_1201_, v___x_1197_);
lean_dec(v___x_1197_);
lean_dec(v___x_1201_);
v___x_1203_ = lean_int_add(v_nanos_1200_, v_nanos_1202_);
lean_dec(v_nanos_1202_);
lean_dec(v_nanos_1200_);
v___x_1204_ = l_Std_Time_Duration_ofNanoseconds(v___x_1203_);
lean_dec(v___x_1203_);
lean_inc_ref(v_rules_1187_);
v_tz_1205_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1187_, v___x_1204_);
lean_inc_ref(v___x_1204_);
lean_inc_ref(v_tz_1205_);
v___f_1206_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1206_, 0, v_tz_1205_);
lean_closure_set(v___f_1206_, 1, v___x_1204_);
lean_closure_set(v___f_1206_, 2, v___x_1198_);
v___x_1207_ = lean_mk_thunk(v___f_1206_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 3, v_tz_1205_);
lean_ctor_set(v___x_1189_, 1, v___x_1204_);
lean_ctor_set(v___x_1189_, 0, v___x_1207_);
v___x_1209_ = v___x_1189_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1210_, 2, v_rules_1187_);
lean_ctor_set(v_reuseFailAlloc_1210_, 3, v_tz_1205_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object* v_dt_1214_, lean_object* v_nanoseconds_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Std_Time_DateTime_subNanoseconds(v_dt_1214_, v_nanoseconds_1215_);
lean_dec(v_nanoseconds_1215_);
return v_res_1216_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object* v_date_1217_){
_start:
{
lean_object* v_date_1218_; lean_object* v___x_1219_; lean_object* v_date_1220_; lean_object* v_year_1221_; uint8_t v___x_1222_; 
v_date_1218_ = lean_ctor_get(v_date_1217_, 0);
v___x_1219_ = lean_thunk_get_own(v_date_1218_);
v_date_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc_ref(v_date_1220_);
lean_dec(v___x_1219_);
v_year_1221_ = lean_ctor_get(v_date_1220_, 0);
lean_inc(v_year_1221_);
lean_dec_ref(v_date_1220_);
v___x_1222_ = l_Std_Time_Year_Offset_era(v_year_1221_);
lean_dec(v_year_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object* v_date_1223_){
_start:
{
uint8_t v_res_1224_; lean_object* v_r_1225_; 
v_res_1224_ = l_Std_Time_DateTime_era(v_date_1223_);
lean_dec_ref(v_date_1223_);
v_r_1225_ = lean_box(v_res_1224_);
return v_r_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object* v_dt_1226_, uint8_t v_desiredWeekday_1227_){
_start:
{
lean_object* v_date_1228_; lean_object* v_rules_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1255_; 
v_date_1228_ = lean_ctor_get(v_dt_1226_, 0);
v_rules_1229_ = lean_ctor_get(v_dt_1226_, 2);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_dt_1226_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; lean_object* v_unused_1257_; 
v_unused_1256_ = lean_ctor_get(v_dt_1226_, 3);
lean_dec(v_unused_1256_);
v_unused_1257_ = lean_ctor_get(v_dt_1226_, 1);
lean_dec(v_unused_1257_);
v___x_1231_ = v_dt_1226_;
v_isShared_1232_ = v_isSharedCheck_1255_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_rules_1229_);
lean_inc(v_date_1228_);
lean_dec(v_dt_1226_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1255_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_date_1233_; lean_object* v___x_1234_; lean_object* v_wt_1235_; lean_object* v_ltt_1236_; lean_object* v_tz_1237_; lean_object* v_offset_1238_; lean_object* v_second_1239_; lean_object* v_nano_1240_; lean_object* v___f_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v_nanos_1247_; lean_object* v___x_1248_; lean_object* v_nanos_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v_date_1233_ = lean_thunk_get_own(v_date_1228_);
lean_dec_ref(v_date_1228_);
v___x_1234_ = l_Std_Time_PlainDateTime_withWeekday(v_date_1233_, v_desiredWeekday_1227_);
lean_inc_ref(v___x_1234_);
v_wt_1235_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1234_);
lean_inc_ref(v_rules_1229_);
v_ltt_1236_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1229_, v_wt_1235_);
v_tz_1237_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1236_);
lean_dec_ref(v_ltt_1236_);
v_offset_1238_ = lean_ctor_get(v_tz_1237_, 0);
v_second_1239_ = lean_ctor_get(v_wt_1235_, 0);
lean_inc(v_second_1239_);
v_nano_1240_ = lean_ctor_get(v_wt_1235_, 1);
lean_inc(v_nano_1240_);
lean_dec_ref(v_wt_1235_);
v___f_1241_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1241_, 0, v___x_1234_);
v___x_1242_ = lean_mk_thunk(v___f_1241_);
v___x_1243_ = lean_int_neg(v_offset_1238_);
v___x_1244_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1245_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1246_ = lean_int_mul(v_second_1239_, v___x_1245_);
lean_dec(v_second_1239_);
v_nanos_1247_ = lean_int_add(v___x_1246_, v_nano_1240_);
lean_dec(v_nano_1240_);
lean_dec(v___x_1246_);
v___x_1248_ = lean_int_mul(v___x_1243_, v___x_1245_);
lean_dec(v___x_1243_);
v_nanos_1249_ = lean_int_add(v___x_1248_, v___x_1244_);
lean_dec(v___x_1248_);
v___x_1250_ = lean_int_add(v_nanos_1247_, v_nanos_1249_);
lean_dec(v_nanos_1249_);
lean_dec(v_nanos_1247_);
v___x_1251_ = l_Std_Time_Duration_ofNanoseconds(v___x_1250_);
lean_dec(v___x_1250_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 3, v_tz_1237_);
lean_ctor_set(v___x_1231_, 1, v___x_1251_);
lean_ctor_set(v___x_1231_, 0, v___x_1242_);
v___x_1253_ = v___x_1231_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_rules_1229_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_tz_1237_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object* v_dt_1258_, lean_object* v_desiredWeekday_1259_){
_start:
{
uint8_t v_desiredWeekday_boxed_1260_; lean_object* v_res_1261_; 
v_desiredWeekday_boxed_1260_ = lean_unbox(v_desiredWeekday_1259_);
v_res_1261_ = l_Std_Time_DateTime_withWeekday(v_dt_1258_, v_desiredWeekday_boxed_1260_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object* v_dt_1262_, lean_object* v_days_1263_){
_start:
{
lean_object* v_date_1264_; lean_object* v_rules_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1328_; 
v_date_1264_ = lean_ctor_get(v_dt_1262_, 0);
v_rules_1265_ = lean_ctor_get(v_dt_1262_, 2);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_dt_1262_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; lean_object* v_unused_1330_; 
v_unused_1329_ = lean_ctor_get(v_dt_1262_, 3);
lean_dec(v_unused_1329_);
v_unused_1330_ = lean_ctor_get(v_dt_1262_, 1);
lean_dec(v_unused_1330_);
v___x_1267_ = v_dt_1262_;
v_isShared_1268_ = v_isSharedCheck_1328_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_rules_1265_);
lean_inc(v_date_1264_);
lean_dec(v_dt_1262_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1328_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v_date_1269_; lean_object* v_date_1270_; lean_object* v_time_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1327_; 
v_date_1269_ = lean_thunk_get_own(v_date_1264_);
lean_dec_ref(v_date_1264_);
v_date_1270_ = lean_ctor_get(v_date_1269_, 0);
v_time_1271_ = lean_ctor_get(v_date_1269_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_date_1269_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1273_ = v_date_1269_;
v_isShared_1274_ = v_isSharedCheck_1327_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_time_1271_);
lean_inc(v_date_1270_);
lean_dec(v_date_1269_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1327_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___y_1276_; lean_object* v_year_1300_; lean_object* v_month_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1325_; 
v_year_1300_ = lean_ctor_get(v_date_1270_, 0);
v_month_1301_ = lean_ctor_get(v_date_1270_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_date_1270_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v_date_1270_, 2);
lean_dec(v_unused_1326_);
v___x_1303_ = v_date_1270_;
v_isShared_1304_ = v_isSharedCheck_1325_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_month_1301_);
lean_inc(v_year_1300_);
lean_dec(v_date_1270_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1325_;
goto v_resetjp_1302_;
}
v___jp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___y_1276_);
v___x_1278_ = v___x_1273_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___y_1276_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_time_1271_);
v___x_1278_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v_wt_1279_; lean_object* v_ltt_1280_; lean_object* v_tz_1281_; lean_object* v_offset_1282_; lean_object* v_second_1283_; lean_object* v_nano_1284_; lean_object* v___f_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v_nanos_1291_; lean_object* v___x_1292_; lean_object* v_nanos_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_inc_ref(v___x_1278_);
v_wt_1279_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1278_);
lean_inc_ref(v_rules_1265_);
v_ltt_1280_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1265_, v_wt_1279_);
v_tz_1281_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1280_);
lean_dec_ref(v_ltt_1280_);
v_offset_1282_ = lean_ctor_get(v_tz_1281_, 0);
v_second_1283_ = lean_ctor_get(v_wt_1279_, 0);
lean_inc(v_second_1283_);
v_nano_1284_ = lean_ctor_get(v_wt_1279_, 1);
lean_inc(v_nano_1284_);
lean_dec_ref(v_wt_1279_);
v___f_1285_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1285_, 0, v___x_1278_);
v___x_1286_ = lean_mk_thunk(v___f_1285_);
v___x_1287_ = lean_int_neg(v_offset_1282_);
v___x_1288_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1289_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1290_ = lean_int_mul(v_second_1283_, v___x_1289_);
lean_dec(v_second_1283_);
v_nanos_1291_ = lean_int_add(v___x_1290_, v_nano_1284_);
lean_dec(v_nano_1284_);
lean_dec(v___x_1290_);
v___x_1292_ = lean_int_mul(v___x_1287_, v___x_1289_);
lean_dec(v___x_1287_);
v_nanos_1293_ = lean_int_add(v___x_1292_, v___x_1288_);
lean_dec(v___x_1292_);
v___x_1294_ = lean_int_add(v_nanos_1291_, v_nanos_1293_);
lean_dec(v_nanos_1293_);
lean_dec(v_nanos_1291_);
v___x_1295_ = l_Std_Time_Duration_ofNanoseconds(v___x_1294_);
lean_dec(v___x_1294_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 3, v_tz_1281_);
lean_ctor_set(v___x_1267_, 1, v___x_1295_);
lean_ctor_set(v___x_1267_, 0, v___x_1286_);
v___x_1297_ = v___x_1267_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_rules_1265_);
lean_ctor_set(v_reuseFailAlloc_1298_, 3, v_tz_1281_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
v_resetjp_1302_:
{
uint8_t v___y_1306_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1315_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1316_ = lean_int_mod(v_year_1300_, v___x_1315_);
v___x_1317_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1318_ = lean_int_dec_eq(v___x_1316_, v___x_1317_);
lean_dec(v___x_1316_);
if (v___x_1318_ == 0)
{
v___y_1306_ = v___x_1318_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1320_ = lean_int_mod(v_year_1300_, v___x_1319_);
v___x_1321_ = lean_int_dec_eq(v___x_1320_, v___x_1317_);
lean_dec(v___x_1320_);
if (v___x_1321_ == 0)
{
v___y_1306_ = v___x_1318_;
goto v___jp_1305_;
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1322_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1323_ = lean_int_mod(v_year_1300_, v___x_1322_);
v___x_1324_ = lean_int_dec_eq(v___x_1323_, v___x_1317_);
lean_dec(v___x_1323_);
v___y_1306_ = v___x_1324_;
goto v___jp_1305_;
}
}
v___jp_1305_:
{
lean_object* v_max_1307_; uint8_t v___x_1308_; 
v_max_1307_ = l_Std_Time_Month_Ordinal_days(v___y_1306_, v_month_1301_);
v___x_1308_ = lean_int_dec_lt(v_max_1307_, v_days_1263_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1310_; 
lean_dec(v_max_1307_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 2, v_days_1263_);
v___x_1310_ = v___x_1303_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_year_1300_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_month_1301_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_days_1263_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
v___y_1276_ = v___x_1310_;
goto v___jp_1275_;
}
}
else
{
lean_object* v___x_1313_; 
lean_dec(v_days_1263_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 2, v_max_1307_);
v___x_1313_ = v___x_1303_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_year_1300_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_month_1301_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_max_1307_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
v___y_1276_ = v___x_1313_;
goto v___jp_1275_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object* v_dt_1331_, lean_object* v_days_1332_){
_start:
{
lean_object* v_date_1333_; lean_object* v_rules_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1371_; 
v_date_1333_ = lean_ctor_get(v_dt_1331_, 0);
v_rules_1334_ = lean_ctor_get(v_dt_1331_, 2);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_dt_1331_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; lean_object* v_unused_1373_; 
v_unused_1372_ = lean_ctor_get(v_dt_1331_, 3);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_dt_1331_, 1);
lean_dec(v_unused_1373_);
v___x_1336_ = v_dt_1331_;
v_isShared_1337_ = v_isSharedCheck_1371_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_rules_1334_);
lean_inc(v_date_1333_);
lean_dec(v_dt_1331_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1371_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_date_1338_; lean_object* v_date_1339_; lean_object* v_time_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1370_; 
v_date_1338_ = lean_thunk_get_own(v_date_1333_);
lean_dec_ref(v_date_1333_);
v_date_1339_ = lean_ctor_get(v_date_1338_, 0);
v_time_1340_ = lean_ctor_get(v_date_1338_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_date_1338_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1342_ = v_date_1338_;
v_isShared_1343_ = v_isSharedCheck_1370_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_time_1340_);
lean_inc(v_date_1339_);
lean_dec(v_date_1338_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1370_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_year_1344_; lean_object* v_month_1345_; lean_object* v___x_1346_; lean_object* v___x_1348_; 
v_year_1344_ = lean_ctor_get(v_date_1339_, 0);
lean_inc(v_year_1344_);
v_month_1345_ = lean_ctor_get(v_date_1339_, 1);
lean_inc(v_month_1345_);
lean_dec_ref(v_date_1339_);
v___x_1346_ = l_Std_Time_PlainDate_rollOver(v_year_1344_, v_month_1345_, v_days_1332_);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1346_);
v___x_1348_ = v___x_1342_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_time_1340_);
v___x_1348_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v_wt_1349_; lean_object* v_ltt_1350_; lean_object* v_tz_1351_; lean_object* v_offset_1352_; lean_object* v_second_1353_; lean_object* v_nano_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_nanos_1361_; lean_object* v___x_1362_; lean_object* v_nanos_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_inc_ref(v___x_1348_);
v_wt_1349_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1348_);
lean_inc_ref(v_rules_1334_);
v_ltt_1350_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1334_, v_wt_1349_);
v_tz_1351_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1350_);
lean_dec_ref(v_ltt_1350_);
v_offset_1352_ = lean_ctor_get(v_tz_1351_, 0);
v_second_1353_ = lean_ctor_get(v_wt_1349_, 0);
lean_inc(v_second_1353_);
v_nano_1354_ = lean_ctor_get(v_wt_1349_, 1);
lean_inc(v_nano_1354_);
lean_dec_ref(v_wt_1349_);
v___f_1355_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1355_, 0, v___x_1348_);
v___x_1356_ = lean_mk_thunk(v___f_1355_);
v___x_1357_ = lean_int_neg(v_offset_1352_);
v___x_1358_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1359_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1360_ = lean_int_mul(v_second_1353_, v___x_1359_);
lean_dec(v_second_1353_);
v_nanos_1361_ = lean_int_add(v___x_1360_, v_nano_1354_);
lean_dec(v_nano_1354_);
lean_dec(v___x_1360_);
v___x_1362_ = lean_int_mul(v___x_1357_, v___x_1359_);
lean_dec(v___x_1357_);
v_nanos_1363_ = lean_int_add(v___x_1362_, v___x_1358_);
lean_dec(v___x_1362_);
v___x_1364_ = lean_int_add(v_nanos_1361_, v_nanos_1363_);
lean_dec(v_nanos_1363_);
lean_dec(v_nanos_1361_);
v___x_1365_ = l_Std_Time_Duration_ofNanoseconds(v___x_1364_);
lean_dec(v___x_1364_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 3, v_tz_1351_);
lean_ctor_set(v___x_1336_, 1, v___x_1365_);
lean_ctor_set(v___x_1336_, 0, v___x_1356_);
v___x_1367_ = v___x_1336_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_rules_1334_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_tz_1351_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object* v_dt_1374_, lean_object* v_days_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_Time_DateTime_withDaysRollOver(v_dt_1374_, v_days_1375_);
lean_dec(v_days_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object* v_dt_1377_, lean_object* v_month_1378_){
_start:
{
lean_object* v_date_1379_; lean_object* v_rules_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1443_; 
v_date_1379_ = lean_ctor_get(v_dt_1377_, 0);
v_rules_1380_ = lean_ctor_get(v_dt_1377_, 2);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_dt_1377_);
if (v_isSharedCheck_1443_ == 0)
{
lean_object* v_unused_1444_; lean_object* v_unused_1445_; 
v_unused_1444_ = lean_ctor_get(v_dt_1377_, 3);
lean_dec(v_unused_1444_);
v_unused_1445_ = lean_ctor_get(v_dt_1377_, 1);
lean_dec(v_unused_1445_);
v___x_1382_ = v_dt_1377_;
v_isShared_1383_ = v_isSharedCheck_1443_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_rules_1380_);
lean_inc(v_date_1379_);
lean_dec(v_dt_1377_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1443_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_date_1384_; lean_object* v_date_1385_; lean_object* v_time_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1442_; 
v_date_1384_ = lean_thunk_get_own(v_date_1379_);
lean_dec_ref(v_date_1379_);
v_date_1385_ = lean_ctor_get(v_date_1384_, 0);
v_time_1386_ = lean_ctor_get(v_date_1384_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_date_1384_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1388_ = v_date_1384_;
v_isShared_1389_ = v_isSharedCheck_1442_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_time_1386_);
lean_inc(v_date_1385_);
lean_dec(v_date_1384_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1442_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___y_1391_; lean_object* v_year_1415_; lean_object* v_day_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1440_; 
v_year_1415_ = lean_ctor_get(v_date_1385_, 0);
v_day_1416_ = lean_ctor_get(v_date_1385_, 2);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_date_1385_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v_date_1385_, 1);
lean_dec(v_unused_1441_);
v___x_1418_ = v_date_1385_;
v_isShared_1419_ = v_isSharedCheck_1440_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_day_1416_);
lean_inc(v_year_1415_);
lean_dec(v_date_1385_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1440_;
goto v_resetjp_1417_;
}
v___jp_1390_:
{
lean_object* v___x_1393_; 
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___y_1391_);
v___x_1393_ = v___x_1388_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___y_1391_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_time_1386_);
v___x_1393_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v_wt_1394_; lean_object* v_ltt_1395_; lean_object* v_tz_1396_; lean_object* v_offset_1397_; lean_object* v_second_1398_; lean_object* v_nano_1399_; lean_object* v___f_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_nanos_1406_; lean_object* v___x_1407_; lean_object* v_nanos_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_inc_ref(v___x_1393_);
v_wt_1394_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1393_);
lean_inc_ref(v_rules_1380_);
v_ltt_1395_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1380_, v_wt_1394_);
v_tz_1396_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1395_);
lean_dec_ref(v_ltt_1395_);
v_offset_1397_ = lean_ctor_get(v_tz_1396_, 0);
v_second_1398_ = lean_ctor_get(v_wt_1394_, 0);
lean_inc(v_second_1398_);
v_nano_1399_ = lean_ctor_get(v_wt_1394_, 1);
lean_inc(v_nano_1399_);
lean_dec_ref(v_wt_1394_);
v___f_1400_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1400_, 0, v___x_1393_);
v___x_1401_ = lean_mk_thunk(v___f_1400_);
v___x_1402_ = lean_int_neg(v_offset_1397_);
v___x_1403_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1404_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1405_ = lean_int_mul(v_second_1398_, v___x_1404_);
lean_dec(v_second_1398_);
v_nanos_1406_ = lean_int_add(v___x_1405_, v_nano_1399_);
lean_dec(v_nano_1399_);
lean_dec(v___x_1405_);
v___x_1407_ = lean_int_mul(v___x_1402_, v___x_1404_);
lean_dec(v___x_1402_);
v_nanos_1408_ = lean_int_add(v___x_1407_, v___x_1403_);
lean_dec(v___x_1407_);
v___x_1409_ = lean_int_add(v_nanos_1406_, v_nanos_1408_);
lean_dec(v_nanos_1408_);
lean_dec(v_nanos_1406_);
v___x_1410_ = l_Std_Time_Duration_ofNanoseconds(v___x_1409_);
lean_dec(v___x_1409_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 3, v_tz_1396_);
lean_ctor_set(v___x_1382_, 1, v___x_1410_);
lean_ctor_set(v___x_1382_, 0, v___x_1401_);
v___x_1412_ = v___x_1382_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_rules_1380_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v_tz_1396_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
v_resetjp_1417_:
{
uint8_t v___y_1421_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1430_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1431_ = lean_int_mod(v_year_1415_, v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1433_ = lean_int_dec_eq(v___x_1431_, v___x_1432_);
lean_dec(v___x_1431_);
if (v___x_1433_ == 0)
{
v___y_1421_ = v___x_1433_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1434_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1435_ = lean_int_mod(v_year_1415_, v___x_1434_);
v___x_1436_ = lean_int_dec_eq(v___x_1435_, v___x_1432_);
lean_dec(v___x_1435_);
if (v___x_1436_ == 0)
{
v___y_1421_ = v___x_1433_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v___x_1437_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1438_ = lean_int_mod(v_year_1415_, v___x_1437_);
v___x_1439_ = lean_int_dec_eq(v___x_1438_, v___x_1432_);
lean_dec(v___x_1438_);
v___y_1421_ = v___x_1439_;
goto v___jp_1420_;
}
}
v___jp_1420_:
{
lean_object* v_max_1422_; uint8_t v___x_1423_; 
v_max_1422_ = l_Std_Time_Month_Ordinal_days(v___y_1421_, v_month_1378_);
v___x_1423_ = lean_int_dec_lt(v_max_1422_, v_day_1416_);
if (v___x_1423_ == 0)
{
lean_object* v___x_1425_; 
lean_dec(v_max_1422_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_month_1378_);
v___x_1425_ = v___x_1418_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v_year_1415_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_month_1378_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_day_1416_);
v___x_1425_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
v___y_1391_ = v___x_1425_;
goto v___jp_1390_;
}
}
else
{
lean_object* v___x_1428_; 
lean_dec(v_day_1416_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 2, v_max_1422_);
lean_ctor_set(v___x_1418_, 1, v_month_1378_);
v___x_1428_ = v___x_1418_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1429_; 
v_reuseFailAlloc_1429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_year_1415_);
lean_ctor_set(v_reuseFailAlloc_1429_, 1, v_month_1378_);
lean_ctor_set(v_reuseFailAlloc_1429_, 2, v_max_1422_);
v___x_1428_ = v_reuseFailAlloc_1429_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
v___y_1391_ = v___x_1428_;
goto v___jp_1390_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object* v_dt_1446_, lean_object* v_month_1447_){
_start:
{
lean_object* v_date_1448_; lean_object* v_rules_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1486_; 
v_date_1448_ = lean_ctor_get(v_dt_1446_, 0);
v_rules_1449_ = lean_ctor_get(v_dt_1446_, 2);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_dt_1446_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; lean_object* v_unused_1488_; 
v_unused_1487_ = lean_ctor_get(v_dt_1446_, 3);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_dt_1446_, 1);
lean_dec(v_unused_1488_);
v___x_1451_ = v_dt_1446_;
v_isShared_1452_ = v_isSharedCheck_1486_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_rules_1449_);
lean_inc(v_date_1448_);
lean_dec(v_dt_1446_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1486_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v_date_1453_; lean_object* v_date_1454_; lean_object* v_time_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1485_; 
v_date_1453_ = lean_thunk_get_own(v_date_1448_);
lean_dec_ref(v_date_1448_);
v_date_1454_ = lean_ctor_get(v_date_1453_, 0);
v_time_1455_ = lean_ctor_get(v_date_1453_, 1);
v_isSharedCheck_1485_ = !lean_is_exclusive(v_date_1453_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1457_ = v_date_1453_;
v_isShared_1458_ = v_isSharedCheck_1485_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_time_1455_);
lean_inc(v_date_1454_);
lean_dec(v_date_1453_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1485_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_year_1459_; lean_object* v_day_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v_year_1459_ = lean_ctor_get(v_date_1454_, 0);
lean_inc(v_year_1459_);
v_day_1460_ = lean_ctor_get(v_date_1454_, 2);
lean_inc(v_day_1460_);
lean_dec_ref(v_date_1454_);
v___x_1461_ = l_Std_Time_PlainDate_rollOver(v_year_1459_, v_month_1447_, v_day_1460_);
lean_dec(v_day_1460_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1461_);
v___x_1463_ = v___x_1457_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1461_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v_time_1455_);
v___x_1463_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v_wt_1464_; lean_object* v_ltt_1465_; lean_object* v_tz_1466_; lean_object* v_offset_1467_; lean_object* v_second_1468_; lean_object* v_nano_1469_; lean_object* v___f_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v_nanos_1476_; lean_object* v___x_1477_; lean_object* v_nanos_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
lean_inc_ref(v___x_1463_);
v_wt_1464_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1463_);
lean_inc_ref(v_rules_1449_);
v_ltt_1465_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1449_, v_wt_1464_);
v_tz_1466_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1465_);
lean_dec_ref(v_ltt_1465_);
v_offset_1467_ = lean_ctor_get(v_tz_1466_, 0);
v_second_1468_ = lean_ctor_get(v_wt_1464_, 0);
lean_inc(v_second_1468_);
v_nano_1469_ = lean_ctor_get(v_wt_1464_, 1);
lean_inc(v_nano_1469_);
lean_dec_ref(v_wt_1464_);
v___f_1470_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1470_, 0, v___x_1463_);
v___x_1471_ = lean_mk_thunk(v___f_1470_);
v___x_1472_ = lean_int_neg(v_offset_1467_);
v___x_1473_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1474_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1475_ = lean_int_mul(v_second_1468_, v___x_1474_);
lean_dec(v_second_1468_);
v_nanos_1476_ = lean_int_add(v___x_1475_, v_nano_1469_);
lean_dec(v_nano_1469_);
lean_dec(v___x_1475_);
v___x_1477_ = lean_int_mul(v___x_1472_, v___x_1474_);
lean_dec(v___x_1472_);
v_nanos_1478_ = lean_int_add(v___x_1477_, v___x_1473_);
lean_dec(v___x_1477_);
v___x_1479_ = lean_int_add(v_nanos_1476_, v_nanos_1478_);
lean_dec(v_nanos_1478_);
lean_dec(v_nanos_1476_);
v___x_1480_ = l_Std_Time_Duration_ofNanoseconds(v___x_1479_);
lean_dec(v___x_1479_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 3, v_tz_1466_);
lean_ctor_set(v___x_1451_, 1, v___x_1480_);
lean_ctor_set(v___x_1451_, 0, v___x_1471_);
v___x_1482_ = v___x_1451_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_rules_1449_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v_tz_1466_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object* v_dt_1489_, lean_object* v_year_1490_){
_start:
{
lean_object* v_date_1491_; lean_object* v_rules_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1555_; 
v_date_1491_ = lean_ctor_get(v_dt_1489_, 0);
v_rules_1492_ = lean_ctor_get(v_dt_1489_, 2);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_dt_1489_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; lean_object* v_unused_1557_; 
v_unused_1556_ = lean_ctor_get(v_dt_1489_, 3);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_dt_1489_, 1);
lean_dec(v_unused_1557_);
v___x_1494_ = v_dt_1489_;
v_isShared_1495_ = v_isSharedCheck_1555_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_rules_1492_);
lean_inc(v_date_1491_);
lean_dec(v_dt_1489_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1555_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_date_1496_; lean_object* v_date_1497_; lean_object* v_time_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1554_; 
v_date_1496_ = lean_thunk_get_own(v_date_1491_);
lean_dec_ref(v_date_1491_);
v_date_1497_ = lean_ctor_get(v_date_1496_, 0);
v_time_1498_ = lean_ctor_get(v_date_1496_, 1);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_date_1496_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1500_ = v_date_1496_;
v_isShared_1501_ = v_isSharedCheck_1554_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_time_1498_);
lean_inc(v_date_1497_);
lean_dec(v_date_1496_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1554_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___y_1503_; lean_object* v_month_1527_; lean_object* v_day_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1552_; 
v_month_1527_ = lean_ctor_get(v_date_1497_, 1);
v_day_1528_ = lean_ctor_get(v_date_1497_, 2);
v_isSharedCheck_1552_ = !lean_is_exclusive(v_date_1497_);
if (v_isSharedCheck_1552_ == 0)
{
lean_object* v_unused_1553_; 
v_unused_1553_ = lean_ctor_get(v_date_1497_, 0);
lean_dec(v_unused_1553_);
v___x_1530_ = v_date_1497_;
v_isShared_1531_ = v_isSharedCheck_1552_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_day_1528_);
lean_inc(v_month_1527_);
lean_dec(v_date_1497_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1552_;
goto v_resetjp_1529_;
}
v___jp_1502_:
{
lean_object* v___x_1505_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___y_1503_);
v___x_1505_ = v___x_1500_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___y_1503_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_time_1498_);
v___x_1505_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v_wt_1506_; lean_object* v_ltt_1507_; lean_object* v_tz_1508_; lean_object* v_offset_1509_; lean_object* v_second_1510_; lean_object* v_nano_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v_nanos_1518_; lean_object* v___x_1519_; lean_object* v_nanos_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
lean_inc_ref(v___x_1505_);
v_wt_1506_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1505_);
lean_inc_ref(v_rules_1492_);
v_ltt_1507_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1492_, v_wt_1506_);
v_tz_1508_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1507_);
lean_dec_ref(v_ltt_1507_);
v_offset_1509_ = lean_ctor_get(v_tz_1508_, 0);
v_second_1510_ = lean_ctor_get(v_wt_1506_, 0);
lean_inc(v_second_1510_);
v_nano_1511_ = lean_ctor_get(v_wt_1506_, 1);
lean_inc(v_nano_1511_);
lean_dec_ref(v_wt_1506_);
v___f_1512_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1512_, 0, v___x_1505_);
v___x_1513_ = lean_mk_thunk(v___f_1512_);
v___x_1514_ = lean_int_neg(v_offset_1509_);
v___x_1515_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1516_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1517_ = lean_int_mul(v_second_1510_, v___x_1516_);
lean_dec(v_second_1510_);
v_nanos_1518_ = lean_int_add(v___x_1517_, v_nano_1511_);
lean_dec(v_nano_1511_);
lean_dec(v___x_1517_);
v___x_1519_ = lean_int_mul(v___x_1514_, v___x_1516_);
lean_dec(v___x_1514_);
v_nanos_1520_ = lean_int_add(v___x_1519_, v___x_1515_);
lean_dec(v___x_1519_);
v___x_1521_ = lean_int_add(v_nanos_1518_, v_nanos_1520_);
lean_dec(v_nanos_1520_);
lean_dec(v_nanos_1518_);
v___x_1522_ = l_Std_Time_Duration_ofNanoseconds(v___x_1521_);
lean_dec(v___x_1521_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 3, v_tz_1508_);
lean_ctor_set(v___x_1494_, 1, v___x_1522_);
lean_ctor_set(v___x_1494_, 0, v___x_1513_);
v___x_1524_ = v___x_1494_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1525_, 2, v_rules_1492_);
lean_ctor_set(v_reuseFailAlloc_1525_, 3, v_tz_1508_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
v_resetjp_1529_:
{
uint8_t v___y_1533_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; uint8_t v___x_1545_; 
v___x_1542_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1543_ = lean_int_mod(v_year_1490_, v___x_1542_);
v___x_1544_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1545_ = lean_int_dec_eq(v___x_1543_, v___x_1544_);
lean_dec(v___x_1543_);
if (v___x_1545_ == 0)
{
v___y_1533_ = v___x_1545_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1547_ = lean_int_mod(v_year_1490_, v___x_1546_);
v___x_1548_ = lean_int_dec_eq(v___x_1547_, v___x_1544_);
lean_dec(v___x_1547_);
if (v___x_1548_ == 0)
{
v___y_1533_ = v___x_1545_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v___x_1549_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1550_ = lean_int_mod(v_year_1490_, v___x_1549_);
v___x_1551_ = lean_int_dec_eq(v___x_1550_, v___x_1544_);
lean_dec(v___x_1550_);
v___y_1533_ = v___x_1551_;
goto v___jp_1532_;
}
}
v___jp_1532_:
{
lean_object* v_max_1534_; uint8_t v___x_1535_; 
v_max_1534_ = l_Std_Time_Month_Ordinal_days(v___y_1533_, v_month_1527_);
v___x_1535_ = lean_int_dec_lt(v_max_1534_, v_day_1528_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1537_; 
lean_dec(v_max_1534_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_year_1490_);
v___x_1537_ = v___x_1530_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_year_1490_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_month_1527_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_day_1528_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
v___y_1503_ = v___x_1537_;
goto v___jp_1502_;
}
}
else
{
lean_object* v___x_1540_; 
lean_dec(v_day_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 2, v_max_1534_);
lean_ctor_set(v___x_1530_, 0, v_year_1490_);
v___x_1540_ = v___x_1530_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_year_1490_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_month_1527_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_max_1534_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
v___y_1503_ = v___x_1540_;
goto v___jp_1502_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object* v_dt_1558_, lean_object* v_year_1559_){
_start:
{
lean_object* v_date_1560_; lean_object* v_rules_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1598_; 
v_date_1560_ = lean_ctor_get(v_dt_1558_, 0);
v_rules_1561_ = lean_ctor_get(v_dt_1558_, 2);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_dt_1558_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; lean_object* v_unused_1600_; 
v_unused_1599_ = lean_ctor_get(v_dt_1558_, 3);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_dt_1558_, 1);
lean_dec(v_unused_1600_);
v___x_1563_ = v_dt_1558_;
v_isShared_1564_ = v_isSharedCheck_1598_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_rules_1561_);
lean_inc(v_date_1560_);
lean_dec(v_dt_1558_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1598_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v_date_1565_; lean_object* v_date_1566_; lean_object* v_time_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1597_; 
v_date_1565_ = lean_thunk_get_own(v_date_1560_);
lean_dec_ref(v_date_1560_);
v_date_1566_ = lean_ctor_get(v_date_1565_, 0);
v_time_1567_ = lean_ctor_get(v_date_1565_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_date_1565_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1569_ = v_date_1565_;
v_isShared_1570_ = v_isSharedCheck_1597_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_time_1567_);
lean_inc(v_date_1566_);
lean_dec(v_date_1565_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1597_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v_month_1571_; lean_object* v_day_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v_month_1571_ = lean_ctor_get(v_date_1566_, 1);
lean_inc(v_month_1571_);
v_day_1572_ = lean_ctor_get(v_date_1566_, 2);
lean_inc(v_day_1572_);
lean_dec_ref(v_date_1566_);
v___x_1573_ = l_Std_Time_PlainDate_rollOver(v_year_1559_, v_month_1571_, v_day_1572_);
lean_dec(v_day_1572_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1573_);
v___x_1575_ = v___x_1569_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_time_1567_);
v___x_1575_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v_wt_1576_; lean_object* v_ltt_1577_; lean_object* v_tz_1578_; lean_object* v_offset_1579_; lean_object* v_second_1580_; lean_object* v_nano_1581_; lean_object* v___f_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_nanos_1588_; lean_object* v___x_1589_; lean_object* v_nanos_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
lean_inc_ref(v___x_1575_);
v_wt_1576_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1575_);
lean_inc_ref(v_rules_1561_);
v_ltt_1577_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1561_, v_wt_1576_);
v_tz_1578_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1577_);
lean_dec_ref(v_ltt_1577_);
v_offset_1579_ = lean_ctor_get(v_tz_1578_, 0);
v_second_1580_ = lean_ctor_get(v_wt_1576_, 0);
lean_inc(v_second_1580_);
v_nano_1581_ = lean_ctor_get(v_wt_1576_, 1);
lean_inc(v_nano_1581_);
lean_dec_ref(v_wt_1576_);
v___f_1582_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1582_, 0, v___x_1575_);
v___x_1583_ = lean_mk_thunk(v___f_1582_);
v___x_1584_ = lean_int_neg(v_offset_1579_);
v___x_1585_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1586_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1587_ = lean_int_mul(v_second_1580_, v___x_1586_);
lean_dec(v_second_1580_);
v_nanos_1588_ = lean_int_add(v___x_1587_, v_nano_1581_);
lean_dec(v_nano_1581_);
lean_dec(v___x_1587_);
v___x_1589_ = lean_int_mul(v___x_1584_, v___x_1586_);
lean_dec(v___x_1584_);
v_nanos_1590_ = lean_int_add(v___x_1589_, v___x_1585_);
lean_dec(v___x_1589_);
v___x_1591_ = lean_int_add(v_nanos_1588_, v_nanos_1590_);
lean_dec(v_nanos_1590_);
lean_dec(v_nanos_1588_);
v___x_1592_ = l_Std_Time_Duration_ofNanoseconds(v___x_1591_);
lean_dec(v___x_1591_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 3, v_tz_1578_);
lean_ctor_set(v___x_1563_, 1, v___x_1592_);
lean_ctor_set(v___x_1563_, 0, v___x_1583_);
v___x_1594_ = v___x_1563_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_rules_1561_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_tz_1578_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object* v_dt_1601_, lean_object* v_hour_1602_){
_start:
{
lean_object* v_date_1603_; lean_object* v_rules_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1649_; 
v_date_1603_ = lean_ctor_get(v_dt_1601_, 0);
v_rules_1604_ = lean_ctor_get(v_dt_1601_, 2);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_dt_1601_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; lean_object* v_unused_1651_; 
v_unused_1650_ = lean_ctor_get(v_dt_1601_, 3);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_dt_1601_, 1);
lean_dec(v_unused_1651_);
v___x_1606_ = v_dt_1601_;
v_isShared_1607_ = v_isSharedCheck_1649_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_rules_1604_);
lean_inc(v_date_1603_);
lean_dec(v_dt_1601_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1649_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_date_1608_; lean_object* v_time_1609_; lean_object* v_date_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1648_; 
v_date_1608_ = lean_thunk_get_own(v_date_1603_);
lean_dec_ref(v_date_1603_);
v_time_1609_ = lean_ctor_get(v_date_1608_, 1);
v_date_1610_ = lean_ctor_get(v_date_1608_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_date_1608_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1612_ = v_date_1608_;
v_isShared_1613_ = v_isSharedCheck_1648_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_time_1609_);
lean_inc(v_date_1610_);
lean_dec(v_date_1608_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1648_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_minute_1614_; lean_object* v_second_1615_; lean_object* v_nanosecond_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1646_; 
v_minute_1614_ = lean_ctor_get(v_time_1609_, 1);
v_second_1615_ = lean_ctor_get(v_time_1609_, 2);
v_nanosecond_1616_ = lean_ctor_get(v_time_1609_, 3);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_time_1609_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; 
v_unused_1647_ = lean_ctor_get(v_time_1609_, 0);
lean_dec(v_unused_1647_);
v___x_1618_ = v_time_1609_;
v_isShared_1619_ = v_isSharedCheck_1646_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_nanosecond_1616_);
lean_inc(v_second_1615_);
lean_inc(v_minute_1614_);
lean_dec(v_time_1609_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1646_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v_hour_1602_);
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_hour_1602_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_minute_1614_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_second_1615_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_nanosecond_1616_);
v___x_1621_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
lean_object* v___x_1623_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 1, v___x_1621_);
v___x_1623_ = v___x_1612_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_date_1610_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v_wt_1624_; lean_object* v_ltt_1625_; lean_object* v_tz_1626_; lean_object* v_offset_1627_; lean_object* v_second_1628_; lean_object* v_nano_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_nanos_1636_; lean_object* v___x_1637_; lean_object* v_nanos_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
lean_inc_ref(v___x_1623_);
v_wt_1624_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1623_);
lean_inc_ref(v_rules_1604_);
v_ltt_1625_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1604_, v_wt_1624_);
v_tz_1626_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1625_);
lean_dec_ref(v_ltt_1625_);
v_offset_1627_ = lean_ctor_get(v_tz_1626_, 0);
v_second_1628_ = lean_ctor_get(v_wt_1624_, 0);
lean_inc(v_second_1628_);
v_nano_1629_ = lean_ctor_get(v_wt_1624_, 1);
lean_inc(v_nano_1629_);
lean_dec_ref(v_wt_1624_);
v___f_1630_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1630_, 0, v___x_1623_);
v___x_1631_ = lean_mk_thunk(v___f_1630_);
v___x_1632_ = lean_int_neg(v_offset_1627_);
v___x_1633_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1634_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1635_ = lean_int_mul(v_second_1628_, v___x_1634_);
lean_dec(v_second_1628_);
v_nanos_1636_ = lean_int_add(v___x_1635_, v_nano_1629_);
lean_dec(v_nano_1629_);
lean_dec(v___x_1635_);
v___x_1637_ = lean_int_mul(v___x_1632_, v___x_1634_);
lean_dec(v___x_1632_);
v_nanos_1638_ = lean_int_add(v___x_1637_, v___x_1633_);
lean_dec(v___x_1637_);
v___x_1639_ = lean_int_add(v_nanos_1636_, v_nanos_1638_);
lean_dec(v_nanos_1638_);
lean_dec(v_nanos_1636_);
v___x_1640_ = l_Std_Time_Duration_ofNanoseconds(v___x_1639_);
lean_dec(v___x_1639_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 3, v_tz_1626_);
lean_ctor_set(v___x_1606_, 1, v___x_1640_);
lean_ctor_set(v___x_1606_, 0, v___x_1631_);
v___x_1642_ = v___x_1606_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_rules_1604_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object* v_dt_1652_, lean_object* v_minute_1653_){
_start:
{
lean_object* v_date_1654_; lean_object* v_rules_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1700_; 
v_date_1654_ = lean_ctor_get(v_dt_1652_, 0);
v_rules_1655_ = lean_ctor_get(v_dt_1652_, 2);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_dt_1652_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; lean_object* v_unused_1702_; 
v_unused_1701_ = lean_ctor_get(v_dt_1652_, 3);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_dt_1652_, 1);
lean_dec(v_unused_1702_);
v___x_1657_ = v_dt_1652_;
v_isShared_1658_ = v_isSharedCheck_1700_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_rules_1655_);
lean_inc(v_date_1654_);
lean_dec(v_dt_1652_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1700_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v_date_1659_; lean_object* v_time_1660_; lean_object* v_date_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1699_; 
v_date_1659_ = lean_thunk_get_own(v_date_1654_);
lean_dec_ref(v_date_1654_);
v_time_1660_ = lean_ctor_get(v_date_1659_, 1);
v_date_1661_ = lean_ctor_get(v_date_1659_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_date_1659_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1663_ = v_date_1659_;
v_isShared_1664_ = v_isSharedCheck_1699_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_time_1660_);
lean_inc(v_date_1661_);
lean_dec(v_date_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1699_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v_hour_1665_; lean_object* v_second_1666_; lean_object* v_nanosecond_1667_; lean_object* v___x_1669_; uint8_t v_isShared_1670_; uint8_t v_isSharedCheck_1697_; 
v_hour_1665_ = lean_ctor_get(v_time_1660_, 0);
v_second_1666_ = lean_ctor_get(v_time_1660_, 2);
v_nanosecond_1667_ = lean_ctor_get(v_time_1660_, 3);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_time_1660_);
if (v_isSharedCheck_1697_ == 0)
{
lean_object* v_unused_1698_; 
v_unused_1698_ = lean_ctor_get(v_time_1660_, 1);
lean_dec(v_unused_1698_);
v___x_1669_ = v_time_1660_;
v_isShared_1670_ = v_isSharedCheck_1697_;
goto v_resetjp_1668_;
}
else
{
lean_inc(v_nanosecond_1667_);
lean_inc(v_second_1666_);
lean_inc(v_hour_1665_);
lean_dec(v_time_1660_);
v___x_1669_ = lean_box(0);
v_isShared_1670_ = v_isSharedCheck_1697_;
goto v_resetjp_1668_;
}
v_resetjp_1668_:
{
lean_object* v___x_1672_; 
if (v_isShared_1670_ == 0)
{
lean_ctor_set(v___x_1669_, 1, v_minute_1653_);
v___x_1672_ = v___x_1669_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_hour_1665_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_minute_1653_);
lean_ctor_set(v_reuseFailAlloc_1696_, 2, v_second_1666_);
lean_ctor_set(v_reuseFailAlloc_1696_, 3, v_nanosecond_1667_);
v___x_1672_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1674_; 
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v___x_1672_);
v___x_1674_ = v___x_1663_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_date_1661_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v_wt_1675_; lean_object* v_ltt_1676_; lean_object* v_tz_1677_; lean_object* v_offset_1678_; lean_object* v_second_1679_; lean_object* v_nano_1680_; lean_object* v___f_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v_nanos_1687_; lean_object* v___x_1688_; lean_object* v_nanos_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
lean_inc_ref(v___x_1674_);
v_wt_1675_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1674_);
lean_inc_ref(v_rules_1655_);
v_ltt_1676_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1655_, v_wt_1675_);
v_tz_1677_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1676_);
lean_dec_ref(v_ltt_1676_);
v_offset_1678_ = lean_ctor_get(v_tz_1677_, 0);
v_second_1679_ = lean_ctor_get(v_wt_1675_, 0);
lean_inc(v_second_1679_);
v_nano_1680_ = lean_ctor_get(v_wt_1675_, 1);
lean_inc(v_nano_1680_);
lean_dec_ref(v_wt_1675_);
v___f_1681_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1681_, 0, v___x_1674_);
v___x_1682_ = lean_mk_thunk(v___f_1681_);
v___x_1683_ = lean_int_neg(v_offset_1678_);
v___x_1684_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1685_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1686_ = lean_int_mul(v_second_1679_, v___x_1685_);
lean_dec(v_second_1679_);
v_nanos_1687_ = lean_int_add(v___x_1686_, v_nano_1680_);
lean_dec(v_nano_1680_);
lean_dec(v___x_1686_);
v___x_1688_ = lean_int_mul(v___x_1683_, v___x_1685_);
lean_dec(v___x_1683_);
v_nanos_1689_ = lean_int_add(v___x_1688_, v___x_1684_);
lean_dec(v___x_1688_);
v___x_1690_ = lean_int_add(v_nanos_1687_, v_nanos_1689_);
lean_dec(v_nanos_1689_);
lean_dec(v_nanos_1687_);
v___x_1691_ = l_Std_Time_Duration_ofNanoseconds(v___x_1690_);
lean_dec(v___x_1690_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 3, v_tz_1677_);
lean_ctor_set(v___x_1657_, 1, v___x_1691_);
lean_ctor_set(v___x_1657_, 0, v___x_1682_);
v___x_1693_ = v___x_1657_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_rules_1655_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_tz_1677_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object* v_dt_1703_, lean_object* v_second_1704_){
_start:
{
lean_object* v_date_1705_; lean_object* v_rules_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1751_; 
v_date_1705_ = lean_ctor_get(v_dt_1703_, 0);
v_rules_1706_ = lean_ctor_get(v_dt_1703_, 2);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_dt_1703_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; lean_object* v_unused_1753_; 
v_unused_1752_ = lean_ctor_get(v_dt_1703_, 3);
lean_dec(v_unused_1752_);
v_unused_1753_ = lean_ctor_get(v_dt_1703_, 1);
lean_dec(v_unused_1753_);
v___x_1708_ = v_dt_1703_;
v_isShared_1709_ = v_isSharedCheck_1751_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_rules_1706_);
lean_inc(v_date_1705_);
lean_dec(v_dt_1703_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1751_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v_date_1710_; lean_object* v_time_1711_; lean_object* v_date_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1750_; 
v_date_1710_ = lean_thunk_get_own(v_date_1705_);
lean_dec_ref(v_date_1705_);
v_time_1711_ = lean_ctor_get(v_date_1710_, 1);
v_date_1712_ = lean_ctor_get(v_date_1710_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v_date_1710_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1714_ = v_date_1710_;
v_isShared_1715_ = v_isSharedCheck_1750_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_time_1711_);
lean_inc(v_date_1712_);
lean_dec(v_date_1710_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1750_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v_hour_1716_; lean_object* v_minute_1717_; lean_object* v_nanosecond_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1748_; 
v_hour_1716_ = lean_ctor_get(v_time_1711_, 0);
v_minute_1717_ = lean_ctor_get(v_time_1711_, 1);
v_nanosecond_1718_ = lean_ctor_get(v_time_1711_, 3);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_time_1711_);
if (v_isSharedCheck_1748_ == 0)
{
lean_object* v_unused_1749_; 
v_unused_1749_ = lean_ctor_get(v_time_1711_, 2);
lean_dec(v_unused_1749_);
v___x_1720_ = v_time_1711_;
v_isShared_1721_ = v_isSharedCheck_1748_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_nanosecond_1718_);
lean_inc(v_minute_1717_);
lean_inc(v_hour_1716_);
lean_dec(v_time_1711_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1748_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 2, v_second_1704_);
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_hour_1716_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_minute_1717_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v_second_1704_);
lean_ctor_set(v_reuseFailAlloc_1747_, 3, v_nanosecond_1718_);
v___x_1723_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
lean_object* v___x_1725_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v___x_1723_);
v___x_1725_ = v___x_1714_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_date_1712_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v_wt_1726_; lean_object* v_ltt_1727_; lean_object* v_tz_1728_; lean_object* v_offset_1729_; lean_object* v_second_1730_; lean_object* v_nano_1731_; lean_object* v___f_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_nanos_1738_; lean_object* v___x_1739_; lean_object* v_nanos_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1744_; 
lean_inc_ref(v___x_1725_);
v_wt_1726_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1725_);
lean_inc_ref(v_rules_1706_);
v_ltt_1727_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1706_, v_wt_1726_);
v_tz_1728_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1727_);
lean_dec_ref(v_ltt_1727_);
v_offset_1729_ = lean_ctor_get(v_tz_1728_, 0);
v_second_1730_ = lean_ctor_get(v_wt_1726_, 0);
lean_inc(v_second_1730_);
v_nano_1731_ = lean_ctor_get(v_wt_1726_, 1);
lean_inc(v_nano_1731_);
lean_dec_ref(v_wt_1726_);
v___f_1732_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1732_, 0, v___x_1725_);
v___x_1733_ = lean_mk_thunk(v___f_1732_);
v___x_1734_ = lean_int_neg(v_offset_1729_);
v___x_1735_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1736_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1737_ = lean_int_mul(v_second_1730_, v___x_1736_);
lean_dec(v_second_1730_);
v_nanos_1738_ = lean_int_add(v___x_1737_, v_nano_1731_);
lean_dec(v_nano_1731_);
lean_dec(v___x_1737_);
v___x_1739_ = lean_int_mul(v___x_1734_, v___x_1736_);
lean_dec(v___x_1734_);
v_nanos_1740_ = lean_int_add(v___x_1739_, v___x_1735_);
lean_dec(v___x_1739_);
v___x_1741_ = lean_int_add(v_nanos_1738_, v_nanos_1740_);
lean_dec(v_nanos_1740_);
lean_dec(v_nanos_1738_);
v___x_1742_ = l_Std_Time_Duration_ofNanoseconds(v___x_1741_);
lean_dec(v___x_1741_);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 3, v_tz_1728_);
lean_ctor_set(v___x_1708_, 1, v___x_1742_);
lean_ctor_set(v___x_1708_, 0, v___x_1733_);
v___x_1744_ = v___x_1708_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1733_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_rules_1706_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_tz_1728_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
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
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_unsigned_to_nat(1000u);
v___x_1755_ = lean_nat_to_int(v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object* v_dt_1756_, lean_object* v_millis_1757_){
_start:
{
lean_object* v_date_1758_; lean_object* v_rules_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1809_; 
v_date_1758_ = lean_ctor_get(v_dt_1756_, 0);
v_rules_1759_ = lean_ctor_get(v_dt_1756_, 2);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_dt_1756_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; lean_object* v_unused_1811_; 
v_unused_1810_ = lean_ctor_get(v_dt_1756_, 3);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v_dt_1756_, 1);
lean_dec(v_unused_1811_);
v___x_1761_ = v_dt_1756_;
v_isShared_1762_ = v_isSharedCheck_1809_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_rules_1759_);
lean_inc(v_date_1758_);
lean_dec(v_dt_1756_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1809_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v_date_1763_; lean_object* v_time_1764_; lean_object* v_date_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1808_; 
v_date_1763_ = lean_thunk_get_own(v_date_1758_);
lean_dec_ref(v_date_1758_);
v_time_1764_ = lean_ctor_get(v_date_1763_, 1);
v_date_1765_ = lean_ctor_get(v_date_1763_, 0);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_date_1763_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1767_ = v_date_1763_;
v_isShared_1768_ = v_isSharedCheck_1808_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_time_1764_);
lean_inc(v_date_1765_);
lean_dec(v_date_1763_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1808_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_hour_1769_; lean_object* v_minute_1770_; lean_object* v_second_1771_; lean_object* v_nanosecond_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1807_; 
v_hour_1769_ = lean_ctor_get(v_time_1764_, 0);
v_minute_1770_ = lean_ctor_get(v_time_1764_, 1);
v_second_1771_ = lean_ctor_get(v_time_1764_, 2);
v_nanosecond_1772_ = lean_ctor_get(v_time_1764_, 3);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_time_1764_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1774_ = v_time_1764_;
v_isShared_1775_ = v_isSharedCheck_1807_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_nanosecond_1772_);
lean_inc(v_second_1771_);
lean_inc(v_minute_1770_);
lean_inc(v_hour_1769_);
lean_dec(v_time_1764_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1807_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1782_; 
v___x_1776_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_1777_ = lean_int_emod(v_nanosecond_1772_, v___x_1776_);
lean_dec(v_nanosecond_1772_);
v___x_1778_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1779_ = lean_int_mul(v_millis_1757_, v___x_1778_);
v___x_1780_ = lean_int_add(v___x_1779_, v___x_1777_);
lean_dec(v___x_1777_);
lean_dec(v___x_1779_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 3, v___x_1780_);
v___x_1782_ = v___x_1774_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_hour_1769_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v_minute_1770_);
lean_ctor_set(v_reuseFailAlloc_1806_, 2, v_second_1771_);
lean_ctor_set(v_reuseFailAlloc_1806_, 3, v___x_1780_);
v___x_1782_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v___x_1782_);
v___x_1784_ = v___x_1767_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_date_1765_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v___x_1782_);
v___x_1784_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
lean_object* v_wt_1785_; lean_object* v_ltt_1786_; lean_object* v_tz_1787_; lean_object* v_offset_1788_; lean_object* v_second_1789_; lean_object* v_nano_1790_; lean_object* v___f_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_nanos_1797_; lean_object* v___x_1798_; lean_object* v_nanos_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_inc_ref(v___x_1784_);
v_wt_1785_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1784_);
lean_inc_ref(v_rules_1759_);
v_ltt_1786_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1759_, v_wt_1785_);
v_tz_1787_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1786_);
lean_dec_ref(v_ltt_1786_);
v_offset_1788_ = lean_ctor_get(v_tz_1787_, 0);
v_second_1789_ = lean_ctor_get(v_wt_1785_, 0);
lean_inc(v_second_1789_);
v_nano_1790_ = lean_ctor_get(v_wt_1785_, 1);
lean_inc(v_nano_1790_);
lean_dec_ref(v_wt_1785_);
v___f_1791_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1791_, 0, v___x_1784_);
v___x_1792_ = lean_mk_thunk(v___f_1791_);
v___x_1793_ = lean_int_neg(v_offset_1788_);
v___x_1794_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1795_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1796_ = lean_int_mul(v_second_1789_, v___x_1795_);
lean_dec(v_second_1789_);
v_nanos_1797_ = lean_int_add(v___x_1796_, v_nano_1790_);
lean_dec(v_nano_1790_);
lean_dec(v___x_1796_);
v___x_1798_ = lean_int_mul(v___x_1793_, v___x_1795_);
lean_dec(v___x_1793_);
v_nanos_1799_ = lean_int_add(v___x_1798_, v___x_1794_);
lean_dec(v___x_1798_);
v___x_1800_ = lean_int_add(v_nanos_1797_, v_nanos_1799_);
lean_dec(v_nanos_1799_);
lean_dec(v_nanos_1797_);
v___x_1801_ = l_Std_Time_Duration_ofNanoseconds(v___x_1800_);
lean_dec(v___x_1800_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 3, v_tz_1787_);
lean_ctor_set(v___x_1761_, 1, v___x_1801_);
lean_ctor_set(v___x_1761_, 0, v___x_1792_);
v___x_1803_ = v___x_1761_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_rules_1759_);
lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_tz_1787_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object* v_dt_1812_, lean_object* v_millis_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Std_Time_DateTime_withMilliseconds(v_dt_1812_, v_millis_1813_);
lean_dec(v_millis_1813_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object* v_dt_1815_, lean_object* v_nano_1816_){
_start:
{
lean_object* v_date_1817_; lean_object* v_rules_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1863_; 
v_date_1817_ = lean_ctor_get(v_dt_1815_, 0);
v_rules_1818_ = lean_ctor_get(v_dt_1815_, 2);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_dt_1815_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; lean_object* v_unused_1865_; 
v_unused_1864_ = lean_ctor_get(v_dt_1815_, 3);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_dt_1815_, 1);
lean_dec(v_unused_1865_);
v___x_1820_ = v_dt_1815_;
v_isShared_1821_ = v_isSharedCheck_1863_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_rules_1818_);
lean_inc(v_date_1817_);
lean_dec(v_dt_1815_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1863_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_date_1822_; lean_object* v_time_1823_; lean_object* v_date_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1862_; 
v_date_1822_ = lean_thunk_get_own(v_date_1817_);
lean_dec_ref(v_date_1817_);
v_time_1823_ = lean_ctor_get(v_date_1822_, 1);
v_date_1824_ = lean_ctor_get(v_date_1822_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_date_1822_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1826_ = v_date_1822_;
v_isShared_1827_ = v_isSharedCheck_1862_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_time_1823_);
lean_inc(v_date_1824_);
lean_dec(v_date_1822_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1862_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_hour_1828_; lean_object* v_minute_1829_; lean_object* v_second_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1860_; 
v_hour_1828_ = lean_ctor_get(v_time_1823_, 0);
v_minute_1829_ = lean_ctor_get(v_time_1823_, 1);
v_second_1830_ = lean_ctor_get(v_time_1823_, 2);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_time_1823_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v_time_1823_, 3);
lean_dec(v_unused_1861_);
v___x_1832_ = v_time_1823_;
v_isShared_1833_ = v_isSharedCheck_1860_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_second_1830_);
lean_inc(v_minute_1829_);
lean_inc(v_hour_1828_);
lean_dec(v_time_1823_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1860_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 3, v_nano_1816_);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_hour_1828_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_minute_1829_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_second_1830_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_nano_1816_);
v___x_1835_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1835_);
v___x_1837_ = v___x_1826_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_date_1824_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
lean_object* v_wt_1838_; lean_object* v_ltt_1839_; lean_object* v_tz_1840_; lean_object* v_offset_1841_; lean_object* v_second_1842_; lean_object* v_nano_1843_; lean_object* v___f_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v_nanos_1850_; lean_object* v___x_1851_; lean_object* v_nanos_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_inc_ref(v___x_1837_);
v_wt_1838_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1837_);
lean_inc_ref(v_rules_1818_);
v_ltt_1839_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1818_, v_wt_1838_);
v_tz_1840_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1839_);
lean_dec_ref(v_ltt_1839_);
v_offset_1841_ = lean_ctor_get(v_tz_1840_, 0);
v_second_1842_ = lean_ctor_get(v_wt_1838_, 0);
lean_inc(v_second_1842_);
v_nano_1843_ = lean_ctor_get(v_wt_1838_, 1);
lean_inc(v_nano_1843_);
lean_dec_ref(v_wt_1838_);
v___f_1844_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1844_, 0, v___x_1837_);
v___x_1845_ = lean_mk_thunk(v___f_1844_);
v___x_1846_ = lean_int_neg(v_offset_1841_);
v___x_1847_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1848_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1849_ = lean_int_mul(v_second_1842_, v___x_1848_);
lean_dec(v_second_1842_);
v_nanos_1850_ = lean_int_add(v___x_1849_, v_nano_1843_);
lean_dec(v_nano_1843_);
lean_dec(v___x_1849_);
v___x_1851_ = lean_int_mul(v___x_1846_, v___x_1848_);
lean_dec(v___x_1846_);
v_nanos_1852_ = lean_int_add(v___x_1851_, v___x_1847_);
lean_dec(v___x_1851_);
v___x_1853_ = lean_int_add(v_nanos_1850_, v_nanos_1852_);
lean_dec(v_nanos_1852_);
lean_dec(v_nanos_1850_);
v___x_1854_ = l_Std_Time_Duration_ofNanoseconds(v___x_1853_);
lean_dec(v___x_1853_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 3, v_tz_1840_);
lean_ctor_set(v___x_1820_, 1, v___x_1854_);
lean_ctor_set(v___x_1820_, 0, v___x_1845_);
v___x_1856_ = v___x_1820_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_rules_1818_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_tz_1840_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object* v_date_1866_){
_start:
{
lean_object* v_date_1867_; lean_object* v___x_1868_; lean_object* v_date_1869_; lean_object* v_year_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v_date_1867_ = lean_ctor_get(v_date_1866_, 0);
v___x_1868_ = lean_thunk_get_own(v_date_1867_);
v_date_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc_ref(v_date_1869_);
lean_dec(v___x_1868_);
v_year_1870_ = lean_ctor_get(v_date_1869_, 0);
lean_inc(v_year_1870_);
lean_dec_ref(v_date_1869_);
v___x_1871_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1872_ = lean_int_mod(v_year_1870_, v___x_1871_);
v___x_1873_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1874_ = lean_int_dec_eq(v___x_1872_, v___x_1873_);
lean_dec(v___x_1872_);
if (v___x_1874_ == 0)
{
lean_dec(v_year_1870_);
return v___x_1874_;
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1875_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1876_ = lean_int_mod(v_year_1870_, v___x_1875_);
v___x_1877_ = lean_int_dec_eq(v___x_1876_, v___x_1873_);
lean_dec(v___x_1876_);
if (v___x_1877_ == 0)
{
lean_dec(v_year_1870_);
return v___x_1874_;
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; 
v___x_1878_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1879_ = lean_int_mod(v_year_1870_, v___x_1878_);
lean_dec(v_year_1870_);
v___x_1880_ = lean_int_dec_eq(v___x_1879_, v___x_1873_);
lean_dec(v___x_1879_);
return v___x_1880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object* v_date_1881_){
_start:
{
uint8_t v_res_1882_; lean_object* v_r_1883_; 
v_res_1882_ = l_Std_Time_DateTime_inLeapYear(v_date_1881_);
lean_dec_ref(v_date_1881_);
v_r_1883_ = lean_box(v_res_1882_);
return v_r_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay(lean_object* v_date_1884_){
_start:
{
lean_object* v_date_1885_; lean_object* v___x_1886_; lean_object* v_date_1887_; lean_object* v___x_1888_; 
v_date_1885_ = lean_ctor_get(v_date_1884_, 0);
v___x_1886_ = lean_thunk_get_own(v_date_1885_);
v_date_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc_ref(v_date_1887_);
lean_dec(v___x_1886_);
v___x_1888_ = l_Std_Time_PlainDate_toEpochDay(v_date_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___boxed(lean_object* v_date_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Std_Time_DateTime_toEpochDay(v_date_1889_);
lean_dec_ref(v_date_1889_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay(lean_object* v_days_1891_, lean_object* v_time_1892_, lean_object* v_zt_1893_){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_wt_1896_; lean_object* v_ltt_1897_; lean_object* v_tz_1898_; lean_object* v_offset_1899_; lean_object* v_second_1900_; lean_object* v_nano_1901_; lean_object* v___f_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_nanos_1908_; lean_object* v___x_1909_; lean_object* v_nanos_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1894_ = l_Std_Time_PlainDate_ofEpochDay(v_days_1891_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v_time_1892_);
lean_inc_ref(v___x_1895_);
v_wt_1896_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1895_);
lean_inc_ref(v_zt_1893_);
v_ltt_1897_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zt_1893_, v_wt_1896_);
v_tz_1898_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1897_);
lean_dec_ref(v_ltt_1897_);
v_offset_1899_ = lean_ctor_get(v_tz_1898_, 0);
v_second_1900_ = lean_ctor_get(v_wt_1896_, 0);
lean_inc(v_second_1900_);
v_nano_1901_ = lean_ctor_get(v_wt_1896_, 1);
lean_inc(v_nano_1901_);
lean_dec_ref(v_wt_1896_);
v___f_1902_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1902_, 0, v___x_1895_);
v___x_1903_ = lean_mk_thunk(v___f_1902_);
v___x_1904_ = lean_int_neg(v_offset_1899_);
v___x_1905_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1906_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1907_ = lean_int_mul(v_second_1900_, v___x_1906_);
lean_dec(v_second_1900_);
v_nanos_1908_ = lean_int_add(v___x_1907_, v_nano_1901_);
lean_dec(v_nano_1901_);
lean_dec(v___x_1907_);
v___x_1909_ = lean_int_mul(v___x_1904_, v___x_1906_);
lean_dec(v___x_1904_);
v_nanos_1910_ = lean_int_add(v___x_1909_, v___x_1905_);
lean_dec(v___x_1909_);
v___x_1911_ = lean_int_add(v_nanos_1908_, v_nanos_1910_);
lean_dec(v_nanos_1910_);
lean_dec(v_nanos_1908_);
v___x_1912_ = l_Std_Time_Duration_ofNanoseconds(v___x_1911_);
lean_dec(v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1903_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
lean_ctor_set(v___x_1913_, 2, v_zt_1893_);
lean_ctor_set(v___x_1913_, 3, v_tz_1898_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay___boxed(lean_object* v_days_1914_, lean_object* v_time_1915_, lean_object* v_zt_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Std_Time_DateTime_ofEpochDay(v_days_1914_, v_time_1915_, v_zt_1916_);
lean_dec(v_days_1914_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object* v_x_1946_, lean_object* v_y_1947_){
_start:
{
lean_object* v_timestamp_1948_; lean_object* v_timestamp_1949_; lean_object* v_second_1950_; lean_object* v_nano_1951_; lean_object* v_second_1952_; lean_object* v_nano_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v_nanos_1958_; lean_object* v___x_1959_; lean_object* v_nanos_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_timestamp_1948_ = lean_ctor_get(v_y_1947_, 1);
v_timestamp_1949_ = lean_ctor_get(v_x_1946_, 1);
v_second_1950_ = lean_ctor_get(v_timestamp_1948_, 0);
v_nano_1951_ = lean_ctor_get(v_timestamp_1948_, 1);
v_second_1952_ = lean_ctor_get(v_timestamp_1949_, 0);
v_nano_1953_ = lean_ctor_get(v_timestamp_1949_, 1);
v___x_1954_ = lean_int_neg(v_second_1950_);
v___x_1955_ = lean_int_neg(v_nano_1951_);
v___x_1956_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1957_ = lean_int_mul(v_second_1952_, v___x_1956_);
v_nanos_1958_ = lean_int_add(v___x_1957_, v_nano_1953_);
lean_dec(v___x_1957_);
v___x_1959_ = lean_int_mul(v___x_1954_, v___x_1956_);
lean_dec(v___x_1954_);
v_nanos_1960_ = lean_int_add(v___x_1959_, v___x_1955_);
lean_dec(v___x_1955_);
lean_dec(v___x_1959_);
v___x_1961_ = lean_int_add(v_nanos_1958_, v_nanos_1960_);
lean_dec(v_nanos_1960_);
lean_dec(v_nanos_1958_);
v___x_1962_ = l_Std_Time_Duration_ofNanoseconds(v___x_1961_);
lean_dec(v___x_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object* v_x_1963_, lean_object* v_y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Std_Time_DateTime_instHSubDuration___lam__0(v_x_1963_, v_y_1964_);
lean_dec_ref(v_y_1964_);
lean_dec_ref(v_x_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0(lean_object* v_x_1968_, lean_object* v_y_1969_){
_start:
{
lean_object* v_second_1970_; lean_object* v_nano_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_nanos_1974_; lean_object* v___x_1975_; 
v_second_1970_ = lean_ctor_get(v_y_1969_, 0);
v_nano_1971_ = lean_ctor_get(v_y_1969_, 1);
v___x_1972_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1973_ = lean_int_mul(v_second_1970_, v___x_1972_);
v_nanos_1974_ = lean_int_add(v___x_1973_, v_nano_1971_);
lean_dec(v___x_1973_);
v___x_1975_ = l_Std_Time_DateTime_addNanoseconds(v_x_1968_, v_nanos_1974_);
lean_dec(v_nanos_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_1976_, lean_object* v_y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Std_Time_DateTime_instHAddDuration___lam__0(v_x_1976_, v_y_1977_);
lean_dec_ref(v_y_1977_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0(lean_object* v_x_1981_, lean_object* v_y_1982_){
_start:
{
lean_object* v_second_1983_; lean_object* v_nano_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v_nanos_1987_; lean_object* v___x_1988_; 
v_second_1983_ = lean_ctor_get(v_y_1982_, 0);
v_nano_1984_ = lean_ctor_get(v_y_1982_, 1);
v___x_1985_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1986_ = lean_int_mul(v_second_1983_, v___x_1985_);
v_nanos_1987_ = lean_int_add(v___x_1986_, v_nano_1984_);
lean_dec(v___x_1986_);
v___x_1988_ = l_Std_Time_DateTime_subNanoseconds(v_x_1981_, v_nanos_1987_);
lean_dec(v_nanos_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0___boxed(lean_object* v_x_1989_, lean_object* v_y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Std_Time_DateTime_instHSubDuration__1___lam__0(v_x_1989_, v_y_1990_);
lean_dec_ref(v_y_1990_);
return v_res_1991_;
}
}
lean_object* runtime_initialize_Std_Time_Zoned_ZoneRules(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_PlainDateTime(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

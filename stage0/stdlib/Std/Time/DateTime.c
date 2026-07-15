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
lean_object* v_offset_20_; lean_object* v_second_21_; lean_object* v_nano_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_offset_20_ = lean_ctor_get(v_tz_17_, 0);
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
lean_object* v_wt_51_; lean_object* v_ltt_52_; lean_object* v_tz_53_; lean_object* v_offset_54_; lean_object* v_second_55_; lean_object* v_nano_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
lean_inc_ref(v_pdt_49_);
v_wt_51_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_49_);
lean_inc_ref(v_zr_50_);
v_ltt_52_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zr_50_, v_wt_51_);
v_tz_53_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_52_);
lean_dec_ref(v_ltt_52_);
v_offset_54_ = lean_ctor_get(v_tz_53_, 0);
lean_inc(v_offset_54_);
v_second_55_ = lean_ctor_get(v_wt_51_, 0);
lean_inc(v_second_55_);
v_nano_56_ = lean_ctor_get(v_wt_51_, 1);
lean_inc(v_nano_56_);
lean_dec_ref(v_wt_51_);
v___f_57_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed), 2, 1);
lean_closure_set(v___f_57_, 0, v_pdt_49_);
v___x_58_ = lean_mk_thunk(v___f_57_);
v___x_59_ = lean_int_neg(v_offset_54_);
lean_dec(v_offset_54_);
v___x_60_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_61_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_62_ = lean_int_mul(v_second_55_, v___x_61_);
lean_dec(v_second_55_);
v___x_63_ = lean_int_add(v___x_62_, v_nano_56_);
lean_dec(v_nano_56_);
lean_dec(v___x_62_);
v___x_64_ = lean_int_mul(v___x_59_, v___x_61_);
lean_dec(v___x_59_);
v___x_65_ = lean_int_add(v___x_64_, v___x_60_);
lean_dec(v___x_64_);
v___x_66_ = lean_int_add(v___x_63_, v___x_65_);
lean_dec(v___x_65_);
lean_dec(v___x_63_);
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
lean_object* v_offset_73_; lean_object* v_second_74_; lean_object* v_nano_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v_offset_73_ = lean_ctor_get(v_tz_69_, 0);
v_second_74_ = lean_ctor_get(v_tm_70_, 0);
v_nano_75_ = lean_ctor_get(v_tm_70_, 1);
v___x_76_ = lean_nat_to_int(v___x_71_);
v___x_77_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_78_ = lean_int_mul(v_second_74_, v___x_77_);
v___x_79_ = lean_int_add(v___x_78_, v_nano_75_);
lean_dec(v___x_78_);
v___x_80_ = lean_int_mul(v_offset_73_, v___x_77_);
v___x_81_ = lean_int_add(v___x_80_, v___x_76_);
lean_dec(v___x_76_);
lean_dec(v___x_80_);
v___x_82_ = lean_int_add(v___x_79_, v___x_81_);
lean_dec(v___x_81_);
lean_dec(v___x_79_);
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
lean_object* v_offset_119_; lean_object* v_name_120_; lean_object* v_abbreviation_121_; uint8_t v_isDST_122_; uint8_t v___x_123_; uint8_t v___x_124_; lean_object* v_ltt_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_wt_129_; lean_object* v_ltt_130_; lean_object* v_tz_131_; lean_object* v_offset_132_; lean_object* v_second_133_; lean_object* v_nano_134_; lean_object* v___f_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
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
lean_inc(v_offset_132_);
v_second_133_ = lean_ctor_get(v_wt_129_, 0);
lean_inc(v_second_133_);
v_nano_134_ = lean_ctor_get(v_wt_129_, 1);
lean_inc(v_nano_134_);
lean_dec_ref(v_wt_129_);
v___f_135_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_ofPlainDateTimeWithZone___lam__0___boxed), 2, 1);
lean_closure_set(v___f_135_, 0, v_tm_117_);
v___x_136_ = lean_mk_thunk(v___f_135_);
v___x_137_ = lean_int_neg(v_offset_132_);
lean_dec(v_offset_132_);
v___x_138_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_139_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_140_ = lean_int_mul(v_second_133_, v___x_139_);
lean_dec(v_second_133_);
v___x_141_ = lean_int_add(v___x_140_, v_nano_134_);
lean_dec(v_nano_134_);
lean_dec(v___x_140_);
v___x_142_ = lean_int_mul(v___x_137_, v___x_139_);
lean_dec(v___x_137_);
v___x_143_ = lean_int_add(v___x_142_, v___x_138_);
lean_dec(v___x_142_);
v___x_144_ = lean_int_add(v___x_141_, v___x_143_);
lean_dec(v___x_143_);
lean_dec(v___x_141_);
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
lean_object* v_offset_157_; lean_object* v_second_158_; lean_object* v_nano_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_offset_157_ = lean_ctor_get(v_tz_154_, 0);
v_second_158_ = lean_ctor_get(v_timestamp_155_, 0);
v_nano_159_ = lean_ctor_get(v_timestamp_155_, 1);
v___x_160_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_161_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_162_ = lean_int_mul(v_second_158_, v___x_161_);
v___x_163_ = lean_int_add(v___x_162_, v_nano_159_);
lean_dec(v___x_162_);
v___x_164_ = lean_int_mul(v_offset_157_, v___x_161_);
v___x_165_ = lean_int_add(v___x_164_, v___x_160_);
lean_dec(v___x_164_);
v___x_166_ = lean_int_add(v___x_163_, v___x_165_);
lean_dec(v___x_165_);
lean_dec(v___x_163_);
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
v___x_275_ = lean_unsigned_to_nat(400u);
v___x_276_ = lean_nat_to_int(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__2(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(100u);
v___x_278_ = lean_nat_to_int(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object* v_date_279_){
_start:
{
lean_object* v_date_280_; lean_object* v___x_281_; lean_object* v_date_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_306_; 
v_date_280_ = lean_ctor_get(v_date_279_, 0);
v___x_281_ = lean_thunk_get_own(v_date_280_);
v_date_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v___x_281_, 1);
lean_dec(v_unused_307_);
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_306_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_date_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_306_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_year_286_; lean_object* v_month_287_; lean_object* v_day_288_; uint8_t v___y_290_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_302_; 
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
v___x_302_ = lean_int_dec_eq(v___x_296_, v___x_297_);
lean_dec(v___x_296_);
if (v___x_302_ == 0)
{
lean_dec(v_year_286_);
v___y_290_ = v___x_302_;
goto v___jp_289_;
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_303_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_304_ = lean_int_mod(v_year_286_, v___x_303_);
v___x_305_ = lean_int_dec_eq(v___x_304_, v___x_297_);
lean_dec(v___x_304_);
if (v___x_305_ == 0)
{
if (v___x_302_ == 0)
{
goto v___jp_298_;
}
else
{
lean_dec(v_year_286_);
v___y_290_ = v___x_302_;
goto v___jp_289_;
}
}
else
{
goto v___jp_298_;
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
v___jp_298_:
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_300_ = lean_int_mod(v_year_286_, v___x_299_);
lean_dec(v_year_286_);
v___x_301_ = lean_int_dec_eq(v___x_300_, v___x_297_);
lean_dec(v___x_300_);
v___y_290_ = v___x_301_;
goto v___jp_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object* v_date_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Time_DateTime_dayOfYear(v_date_308_);
lean_dec_ref(v_date_308_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* v_dt_310_, uint8_t v_firstDay_311_, lean_object* v_minDays_312_){
_start:
{
lean_object* v_date_313_; lean_object* v___x_314_; lean_object* v_date_315_; lean_object* v___x_316_; 
v_date_313_ = lean_ctor_get(v_dt_310_, 0);
v___x_314_ = lean_thunk_get_own(v_date_313_);
v_date_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc_ref(v_date_315_);
lean_dec(v___x_314_);
v___x_316_ = l_Std_Time_PlainDate_weekOfYear(v_date_315_, v_firstDay_311_, v_minDays_312_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object* v_dt_317_, lean_object* v_firstDay_318_, lean_object* v_minDays_319_){
_start:
{
uint8_t v_firstDay_boxed_320_; lean_object* v_res_321_; 
v_firstDay_boxed_320_ = lean_unbox(v_firstDay_318_);
v_res_321_ = l_Std_Time_DateTime_weekOfYear(v_dt_317_, v_firstDay_boxed_320_, v_minDays_319_);
lean_dec(v_minDays_319_);
lean_dec_ref(v_dt_317_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear(lean_object* v_date_322_, uint8_t v_firstDay_323_, lean_object* v_minDays_324_){
_start:
{
lean_object* v_date_325_; lean_object* v___x_326_; lean_object* v_date_327_; lean_object* v___x_328_; 
v_date_325_ = lean_ctor_get(v_date_322_, 0);
v___x_326_ = lean_thunk_get_own(v_date_325_);
v_date_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_date_327_);
lean_dec(v___x_326_);
v___x_328_ = l_Std_Time_PlainDate_weekYear(v_date_327_, v_firstDay_323_, v_minDays_324_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___boxed(lean_object* v_date_329_, lean_object* v_firstDay_330_, lean_object* v_minDays_331_){
_start:
{
uint8_t v_firstDay_boxed_332_; lean_object* v_res_333_; 
v_firstDay_boxed_332_ = lean_unbox(v_firstDay_330_);
v_res_333_ = l_Std_Time_DateTime_weekYear(v_date_329_, v_firstDay_boxed_332_, v_minDays_331_);
lean_dec(v_minDays_331_);
lean_dec_ref(v_date_329_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* v_date_334_){
_start:
{
lean_object* v_date_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_date_335_ = lean_ctor_get(v_date_334_, 0);
v___x_336_ = lean_thunk_get_own(v_date_335_);
v___x_337_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v___x_336_);
lean_dec(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object* v_date_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_338_);
lean_dec_ref(v_date_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* v_date_340_, uint8_t v_firstDay_341_){
_start:
{
lean_object* v_date_342_; lean_object* v___x_343_; lean_object* v_date_344_; lean_object* v___x_345_; 
v_date_342_ = lean_ctor_get(v_date_340_, 0);
v___x_343_ = lean_thunk_get_own(v_date_342_);
v_date_344_ = lean_ctor_get(v___x_343_, 0);
lean_inc_ref(v_date_344_);
lean_dec(v___x_343_);
v___x_345_ = l_Std_Time_PlainDate_weekOfMonth(v_date_344_, v_firstDay_341_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object* v_date_346_, lean_object* v_firstDay_347_){
_start:
{
uint8_t v_firstDay_boxed_348_; lean_object* v_res_349_; 
v_firstDay_boxed_348_ = lean_unbox(v_firstDay_347_);
v_res_349_ = l_Std_Time_DateTime_weekOfMonth(v_date_346_, v_firstDay_boxed_348_);
lean_dec_ref(v_date_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* v_date_350_){
_start:
{
lean_object* v_date_351_; lean_object* v___x_352_; lean_object* v_date_353_; lean_object* v___x_354_; 
v_date_351_ = lean_ctor_get(v_date_350_, 0);
v___x_352_ = lean_thunk_get_own(v_date_351_);
v_date_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_date_353_);
lean_dec(v___x_352_);
v___x_354_ = l_Std_Time_PlainDate_quarter(v_date_353_);
lean_dec_ref(v_date_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object* v_date_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_Time_DateTime_quarter(v_date_355_);
lean_dec_ref(v_date_355_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_DateTime_addDays_spec__1(lean_object* v_a_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Rat_ofInt(v_a_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0(lean_object* v_tz_359_, lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v___x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_offset_364_; lean_object* v_second_365_; lean_object* v_nano_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_offset_364_ = lean_ctor_get(v_tz_359_, 0);
v_second_365_ = lean_ctor_get(v___x_360_, 0);
v_nano_366_ = lean_ctor_get(v___x_360_, 1);
v___x_367_ = lean_int_mul(v_second_365_, v___x_361_);
v___x_368_ = lean_int_add(v___x_367_, v_nano_366_);
lean_dec(v___x_367_);
v___x_369_ = lean_int_mul(v_offset_364_, v___x_361_);
v___x_370_ = lean_int_add(v___x_369_, v___x_362_);
lean_dec(v___x_369_);
v___x_371_ = lean_int_add(v___x_368_, v___x_370_);
lean_dec(v___x_370_);
lean_dec(v___x_368_);
v___x_372_ = l_Std_Time_Duration_ofNanoseconds(v___x_371_);
lean_dec(v___x_371_);
v___x_373_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0___boxed(lean_object* v_tz_374_, lean_object* v___x_375_, lean_object* v___x_376_, lean_object* v___x_377_, lean_object* v_x_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Time_DateTime_addDays___lam__0(v_tz_374_, v___x_375_, v___x_376_, v___x_377_, v_x_378_);
lean_dec(v___x_377_);
lean_dec(v___x_376_);
lean_dec_ref(v___x_375_);
lean_dec_ref(v_tz_374_);
return v_res_379_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addDays___closed__0(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_unsigned_to_nat(86400u);
v___x_381_ = lean_nat_to_int(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object* v_dt_382_, lean_object* v_days_383_){
_start:
{
lean_object* v_timestamp_384_; lean_object* v_rules_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_407_; 
v_timestamp_384_ = lean_ctor_get(v_dt_382_, 1);
v_rules_385_ = lean_ctor_get(v_dt_382_, 2);
v_isSharedCheck_407_ = !lean_is_exclusive(v_dt_382_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; lean_object* v_unused_409_; 
v_unused_408_ = lean_ctor_get(v_dt_382_, 3);
lean_dec(v_unused_408_);
v_unused_409_ = lean_ctor_get(v_dt_382_, 0);
lean_dec(v_unused_409_);
v___x_387_ = v_dt_382_;
v_isShared_388_ = v_isSharedCheck_407_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_rules_385_);
lean_inc(v_timestamp_384_);
lean_dec(v_dt_382_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_407_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v_second_389_; lean_object* v_nano_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_tz_401_; lean_object* v___f_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v_second_389_ = lean_ctor_get(v_timestamp_384_, 0);
lean_inc(v_second_389_);
v_nano_390_ = lean_ctor_get(v_timestamp_384_, 1);
lean_inc(v_nano_390_);
lean_dec_ref(v_timestamp_384_);
v___x_391_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_392_ = lean_int_mul(v_days_383_, v___x_391_);
v___x_393_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_394_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_395_ = lean_int_mul(v_second_389_, v___x_394_);
lean_dec(v_second_389_);
v___x_396_ = lean_int_add(v___x_395_, v_nano_390_);
lean_dec(v_nano_390_);
lean_dec(v___x_395_);
v___x_397_ = lean_int_mul(v___x_392_, v___x_394_);
lean_dec(v___x_392_);
v___x_398_ = lean_int_add(v___x_397_, v___x_393_);
lean_dec(v___x_397_);
v___x_399_ = lean_int_add(v___x_396_, v___x_398_);
lean_dec(v___x_398_);
lean_dec(v___x_396_);
v___x_400_ = l_Std_Time_Duration_ofNanoseconds(v___x_399_);
lean_dec(v___x_399_);
lean_inc_ref(v_rules_385_);
v_tz_401_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_385_, v___x_400_);
lean_inc_ref(v___x_400_);
lean_inc_ref(v_tz_401_);
v___f_402_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_402_, 0, v_tz_401_);
lean_closure_set(v___f_402_, 1, v___x_400_);
lean_closure_set(v___f_402_, 2, v___x_394_);
lean_closure_set(v___f_402_, 3, v___x_393_);
v___x_403_ = lean_mk_thunk(v___f_402_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 3, v_tz_401_);
lean_ctor_set(v___x_387_, 1, v___x_400_);
lean_ctor_set(v___x_387_, 0, v___x_403_);
v___x_405_ = v___x_387_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_rules_385_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_tz_401_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object* v_dt_410_, lean_object* v_days_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_Time_DateTime_addDays(v_dt_410_, v_days_411_);
lean_dec(v_days_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_DateTime_addDays_spec__0_spec__0(lean_object* v_a_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = lean_nat_to_int(v_a_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_DateTime_addDays_spec__0(lean_object* v_a_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = lean_nat_to_int(v_a_415_);
v___x_417_ = l_Rat_ofInt(v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object* v_dt_418_, lean_object* v_days_419_){
_start:
{
lean_object* v_timestamp_420_; lean_object* v_rules_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_445_; 
v_timestamp_420_ = lean_ctor_get(v_dt_418_, 1);
v_rules_421_ = lean_ctor_get(v_dt_418_, 2);
v_isSharedCheck_445_ = !lean_is_exclusive(v_dt_418_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; lean_object* v_unused_447_; 
v_unused_446_ = lean_ctor_get(v_dt_418_, 3);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_dt_418_, 0);
lean_dec(v_unused_447_);
v___x_423_ = v_dt_418_;
v_isShared_424_ = v_isSharedCheck_445_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_rules_421_);
lean_inc(v_timestamp_420_);
lean_dec(v_dt_418_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_445_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v_second_425_; lean_object* v_nano_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v_tz_439_; lean_object* v___f_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v_second_425_ = lean_ctor_get(v_timestamp_420_, 0);
lean_inc(v_second_425_);
v_nano_426_ = lean_ctor_get(v_timestamp_420_, 1);
lean_inc(v_nano_426_);
lean_dec_ref(v_timestamp_420_);
v___x_427_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_428_ = lean_int_mul(v_days_419_, v___x_427_);
v___x_429_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_430_ = lean_int_neg(v___x_428_);
lean_dec(v___x_428_);
v___x_431_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_432_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_433_ = lean_int_mul(v_second_425_, v___x_432_);
lean_dec(v_second_425_);
v___x_434_ = lean_int_add(v___x_433_, v_nano_426_);
lean_dec(v_nano_426_);
lean_dec(v___x_433_);
v___x_435_ = lean_int_mul(v___x_430_, v___x_432_);
lean_dec(v___x_430_);
v___x_436_ = lean_int_add(v___x_435_, v___x_431_);
lean_dec(v___x_435_);
v___x_437_ = lean_int_add(v___x_434_, v___x_436_);
lean_dec(v___x_436_);
lean_dec(v___x_434_);
v___x_438_ = l_Std_Time_Duration_ofNanoseconds(v___x_437_);
lean_dec(v___x_437_);
lean_inc_ref(v_rules_421_);
v_tz_439_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_421_, v___x_438_);
lean_inc_ref(v___x_438_);
lean_inc_ref(v_tz_439_);
v___f_440_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_440_, 0, v_tz_439_);
lean_closure_set(v___f_440_, 1, v___x_438_);
lean_closure_set(v___f_440_, 2, v___x_432_);
lean_closure_set(v___f_440_, 3, v___x_429_);
v___x_441_ = lean_mk_thunk(v___f_440_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 3, v_tz_439_);
lean_ctor_set(v___x_423_, 1, v___x_438_);
lean_ctor_set(v___x_423_, 0, v___x_441_);
v___x_443_ = v___x_423_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_444_, 2, v_rules_421_);
lean_ctor_set(v_reuseFailAlloc_444_, 3, v_tz_439_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object* v_dt_448_, lean_object* v_days_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_Time_DateTime_subDays(v_dt_448_, v_days_449_);
lean_dec(v_days_449_);
return v_res_450_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(7u);
v___x_452_ = lean_nat_to_int(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object* v_dt_453_, lean_object* v_weeks_454_){
_start:
{
lean_object* v_timestamp_455_; lean_object* v_rules_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_480_; 
v_timestamp_455_ = lean_ctor_get(v_dt_453_, 1);
v_rules_456_ = lean_ctor_get(v_dt_453_, 2);
v_isSharedCheck_480_ = !lean_is_exclusive(v_dt_453_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; lean_object* v_unused_482_; 
v_unused_481_ = lean_ctor_get(v_dt_453_, 3);
lean_dec(v_unused_481_);
v_unused_482_ = lean_ctor_get(v_dt_453_, 0);
lean_dec(v_unused_482_);
v___x_458_ = v_dt_453_;
v_isShared_459_ = v_isSharedCheck_480_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_rules_456_);
lean_inc(v_timestamp_455_);
lean_dec(v_dt_453_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_480_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_second_460_; lean_object* v_nano_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v_tz_474_; lean_object* v___f_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
v_second_460_ = lean_ctor_get(v_timestamp_455_, 0);
lean_inc(v_second_460_);
v_nano_461_ = lean_ctor_get(v_timestamp_455_, 1);
lean_inc(v_nano_461_);
lean_dec_ref(v_timestamp_455_);
v___x_462_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_463_ = lean_int_mul(v_weeks_454_, v___x_462_);
v___x_464_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_465_ = lean_int_mul(v___x_463_, v___x_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_467_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_468_ = lean_int_mul(v_second_460_, v___x_467_);
lean_dec(v_second_460_);
v___x_469_ = lean_int_add(v___x_468_, v_nano_461_);
lean_dec(v_nano_461_);
lean_dec(v___x_468_);
v___x_470_ = lean_int_mul(v___x_465_, v___x_467_);
lean_dec(v___x_465_);
v___x_471_ = lean_int_add(v___x_470_, v___x_466_);
lean_dec(v___x_470_);
v___x_472_ = lean_int_add(v___x_469_, v___x_471_);
lean_dec(v___x_471_);
lean_dec(v___x_469_);
v___x_473_ = l_Std_Time_Duration_ofNanoseconds(v___x_472_);
lean_dec(v___x_472_);
lean_inc_ref(v_rules_456_);
v_tz_474_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_456_, v___x_473_);
lean_inc_ref(v___x_473_);
lean_inc_ref(v_tz_474_);
v___f_475_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_475_, 0, v_tz_474_);
lean_closure_set(v___f_475_, 1, v___x_473_);
lean_closure_set(v___f_475_, 2, v___x_467_);
lean_closure_set(v___f_475_, 3, v___x_466_);
v___x_476_ = lean_mk_thunk(v___f_475_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 3, v_tz_474_);
lean_ctor_set(v___x_458_, 1, v___x_473_);
lean_ctor_set(v___x_458_, 0, v___x_476_);
v___x_478_ = v___x_458_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_rules_456_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_tz_474_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object* v_dt_483_, lean_object* v_weeks_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_Time_DateTime_addWeeks(v_dt_483_, v_weeks_484_);
lean_dec(v_weeks_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object* v_dt_486_, lean_object* v_weeks_487_){
_start:
{
lean_object* v_timestamp_488_; lean_object* v_rules_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_515_; 
v_timestamp_488_ = lean_ctor_get(v_dt_486_, 1);
v_rules_489_ = lean_ctor_get(v_dt_486_, 2);
v_isSharedCheck_515_ = !lean_is_exclusive(v_dt_486_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; lean_object* v_unused_517_; 
v_unused_516_ = lean_ctor_get(v_dt_486_, 3);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_dt_486_, 0);
lean_dec(v_unused_517_);
v___x_491_ = v_dt_486_;
v_isShared_492_ = v_isSharedCheck_515_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_rules_489_);
lean_inc(v_timestamp_488_);
lean_dec(v_dt_486_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_515_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_second_493_; lean_object* v_nano_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_tz_509_; lean_object* v___f_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v_second_493_ = lean_ctor_get(v_timestamp_488_, 0);
lean_inc(v_second_493_);
v_nano_494_ = lean_ctor_get(v_timestamp_488_, 1);
lean_inc(v_nano_494_);
lean_dec_ref(v_timestamp_488_);
v___x_495_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_496_ = lean_int_mul(v_weeks_487_, v___x_495_);
v___x_497_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_498_ = lean_int_mul(v___x_496_, v___x_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_500_ = lean_int_neg(v___x_498_);
lean_dec(v___x_498_);
v___x_501_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_502_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_503_ = lean_int_mul(v_second_493_, v___x_502_);
lean_dec(v_second_493_);
v___x_504_ = lean_int_add(v___x_503_, v_nano_494_);
lean_dec(v_nano_494_);
lean_dec(v___x_503_);
v___x_505_ = lean_int_mul(v___x_500_, v___x_502_);
lean_dec(v___x_500_);
v___x_506_ = lean_int_add(v___x_505_, v___x_501_);
lean_dec(v___x_505_);
v___x_507_ = lean_int_add(v___x_504_, v___x_506_);
lean_dec(v___x_506_);
lean_dec(v___x_504_);
v___x_508_ = l_Std_Time_Duration_ofNanoseconds(v___x_507_);
lean_dec(v___x_507_);
lean_inc_ref(v_rules_489_);
v_tz_509_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_489_, v___x_508_);
lean_inc_ref(v___x_508_);
lean_inc_ref(v_tz_509_);
v___f_510_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_510_, 0, v_tz_509_);
lean_closure_set(v___f_510_, 1, v___x_508_);
lean_closure_set(v___f_510_, 2, v___x_502_);
lean_closure_set(v___f_510_, 3, v___x_499_);
v___x_511_ = lean_mk_thunk(v___f_510_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 3, v_tz_509_);
lean_ctor_set(v___x_491_, 1, v___x_508_);
lean_ctor_set(v___x_491_, 0, v___x_511_);
v___x_513_ = v___x_491_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_rules_489_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_tz_509_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object* v_dt_518_, lean_object* v_weeks_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_Time_DateTime_subWeeks(v_dt_518_, v_weeks_519_);
lean_dec(v_weeks_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0(lean_object* v___x_521_, lean_object* v_x_522_){
_start:
{
lean_inc_ref(v___x_521_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(lean_object* v___x_523_, lean_object* v_x_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Time_DateTime_addMonthsClip___lam__0(v___x_523_, v_x_524_);
lean_dec_ref(v___x_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object* v_dt_526_, lean_object* v_months_527_){
_start:
{
lean_object* v_date_528_; lean_object* v_rules_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_555_; 
v_date_528_ = lean_ctor_get(v_dt_526_, 0);
v_rules_529_ = lean_ctor_get(v_dt_526_, 2);
v_isSharedCheck_555_ = !lean_is_exclusive(v_dt_526_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; lean_object* v_unused_557_; 
v_unused_556_ = lean_ctor_get(v_dt_526_, 3);
lean_dec(v_unused_556_);
v_unused_557_ = lean_ctor_get(v_dt_526_, 1);
lean_dec(v_unused_557_);
v___x_531_ = v_dt_526_;
v_isShared_532_ = v_isSharedCheck_555_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_rules_529_);
lean_inc(v_date_528_);
lean_dec(v_dt_526_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_555_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_wt_535_; lean_object* v_ltt_536_; lean_object* v_tz_537_; lean_object* v_offset_538_; lean_object* v_second_539_; lean_object* v_nano_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_533_ = lean_thunk_get_own(v_date_528_);
lean_dec_ref(v_date_528_);
v___x_534_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_533_, v_months_527_);
lean_inc_ref(v___x_534_);
v_wt_535_ = l_Std_Time_PlainDateTime_toWallTime(v___x_534_);
lean_inc_ref(v_rules_529_);
v_ltt_536_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_529_, v_wt_535_);
v_tz_537_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_536_);
lean_dec_ref(v_ltt_536_);
v_offset_538_ = lean_ctor_get(v_tz_537_, 0);
lean_inc(v_offset_538_);
v_second_539_ = lean_ctor_get(v_wt_535_, 0);
lean_inc(v_second_539_);
v_nano_540_ = lean_ctor_get(v_wt_535_, 1);
lean_inc(v_nano_540_);
lean_dec_ref(v_wt_535_);
v___f_541_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_541_, 0, v___x_534_);
v___x_542_ = lean_mk_thunk(v___f_541_);
v___x_543_ = lean_int_neg(v_offset_538_);
lean_dec(v_offset_538_);
v___x_544_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_545_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_546_ = lean_int_mul(v_second_539_, v___x_545_);
lean_dec(v_second_539_);
v___x_547_ = lean_int_add(v___x_546_, v_nano_540_);
lean_dec(v_nano_540_);
lean_dec(v___x_546_);
v___x_548_ = lean_int_mul(v___x_543_, v___x_545_);
lean_dec(v___x_543_);
v___x_549_ = lean_int_add(v___x_548_, v___x_544_);
lean_dec(v___x_548_);
v___x_550_ = lean_int_add(v___x_547_, v___x_549_);
lean_dec(v___x_549_);
lean_dec(v___x_547_);
v___x_551_ = l_Std_Time_Duration_ofNanoseconds(v___x_550_);
lean_dec(v___x_550_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 3, v_tz_537_);
lean_ctor_set(v___x_531_, 1, v___x_551_);
lean_ctor_set(v___x_531_, 0, v___x_542_);
v___x_553_ = v___x_531_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_rules_529_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_tz_537_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object* v_dt_558_, lean_object* v_months_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Time_DateTime_addMonthsClip(v_dt_558_, v_months_559_);
lean_dec(v_months_559_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object* v_dt_561_, lean_object* v_months_562_){
_start:
{
lean_object* v_date_563_; lean_object* v_rules_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_600_; 
v_date_563_ = lean_ctor_get(v_dt_561_, 0);
v_rules_564_ = lean_ctor_get(v_dt_561_, 2);
v_isSharedCheck_600_ = !lean_is_exclusive(v_dt_561_);
if (v_isSharedCheck_600_ == 0)
{
lean_object* v_unused_601_; lean_object* v_unused_602_; 
v_unused_601_ = lean_ctor_get(v_dt_561_, 3);
lean_dec(v_unused_601_);
v_unused_602_ = lean_ctor_get(v_dt_561_, 1);
lean_dec(v_unused_602_);
v___x_566_ = v_dt_561_;
v_isShared_567_ = v_isSharedCheck_600_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_rules_564_);
lean_inc(v_date_563_);
lean_dec(v_dt_561_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_600_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v_date_569_; lean_object* v_time_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_599_; 
v___x_568_ = lean_thunk_get_own(v_date_563_);
lean_dec_ref(v_date_563_);
v_date_569_ = lean_ctor_get(v___x_568_, 0);
v_time_570_ = lean_ctor_get(v___x_568_, 1);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_599_ == 0)
{
v___x_572_ = v___x_568_;
v_isShared_573_ = v_isSharedCheck_599_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_time_570_);
lean_inc(v_date_569_);
lean_dec(v___x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_599_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_574_ = lean_int_neg(v_months_562_);
v___x_575_ = l_Std_Time_PlainDate_addMonthsClip(v_date_569_, v___x_574_);
lean_dec(v___x_574_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_575_);
v___x_577_ = v___x_572_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_time_570_);
v___x_577_ = v_reuseFailAlloc_598_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v_wt_578_; lean_object* v_ltt_579_; lean_object* v_tz_580_; lean_object* v_offset_581_; lean_object* v_second_582_; lean_object* v_nano_583_; lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
lean_inc_ref(v___x_577_);
v_wt_578_ = l_Std_Time_PlainDateTime_toWallTime(v___x_577_);
lean_inc_ref(v_rules_564_);
v_ltt_579_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_564_, v_wt_578_);
v_tz_580_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_579_);
lean_dec_ref(v_ltt_579_);
v_offset_581_ = lean_ctor_get(v_tz_580_, 0);
lean_inc(v_offset_581_);
v_second_582_ = lean_ctor_get(v_wt_578_, 0);
lean_inc(v_second_582_);
v_nano_583_ = lean_ctor_get(v_wt_578_, 1);
lean_inc(v_nano_583_);
lean_dec_ref(v_wt_578_);
v___f_584_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_584_, 0, v___x_577_);
v___x_585_ = lean_mk_thunk(v___f_584_);
v___x_586_ = lean_int_neg(v_offset_581_);
lean_dec(v_offset_581_);
v___x_587_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_588_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_589_ = lean_int_mul(v_second_582_, v___x_588_);
lean_dec(v_second_582_);
v___x_590_ = lean_int_add(v___x_589_, v_nano_583_);
lean_dec(v_nano_583_);
lean_dec(v___x_589_);
v___x_591_ = lean_int_mul(v___x_586_, v___x_588_);
lean_dec(v___x_586_);
v___x_592_ = lean_int_add(v___x_591_, v___x_587_);
lean_dec(v___x_591_);
v___x_593_ = lean_int_add(v___x_590_, v___x_592_);
lean_dec(v___x_592_);
lean_dec(v___x_590_);
v___x_594_ = l_Std_Time_Duration_ofNanoseconds(v___x_593_);
lean_dec(v___x_593_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 3, v_tz_580_);
lean_ctor_set(v___x_566_, 1, v___x_594_);
lean_ctor_set(v___x_566_, 0, v___x_585_);
v___x_596_ = v___x_566_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_rules_564_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v_tz_580_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object* v_dt_603_, lean_object* v_months_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_Time_DateTime_subMonthsClip(v_dt_603_, v_months_604_);
lean_dec(v_months_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object* v_dt_606_, lean_object* v_months_607_){
_start:
{
lean_object* v_date_608_; lean_object* v_rules_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_635_; 
v_date_608_ = lean_ctor_get(v_dt_606_, 0);
v_rules_609_ = lean_ctor_get(v_dt_606_, 2);
v_isSharedCheck_635_ = !lean_is_exclusive(v_dt_606_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; lean_object* v_unused_637_; 
v_unused_636_ = lean_ctor_get(v_dt_606_, 3);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_dt_606_, 1);
lean_dec(v_unused_637_);
v___x_611_ = v_dt_606_;
v_isShared_612_ = v_isSharedCheck_635_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_rules_609_);
lean_inc(v_date_608_);
lean_dec(v_dt_606_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_635_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_wt_615_; lean_object* v_ltt_616_; lean_object* v_tz_617_; lean_object* v_offset_618_; lean_object* v_second_619_; lean_object* v_nano_620_; lean_object* v___f_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_613_ = lean_thunk_get_own(v_date_608_);
lean_dec_ref(v_date_608_);
v___x_614_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_613_, v_months_607_);
lean_inc_ref(v___x_614_);
v_wt_615_ = l_Std_Time_PlainDateTime_toWallTime(v___x_614_);
lean_inc_ref(v_rules_609_);
v_ltt_616_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_609_, v_wt_615_);
v_tz_617_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_616_);
lean_dec_ref(v_ltt_616_);
v_offset_618_ = lean_ctor_get(v_tz_617_, 0);
lean_inc(v_offset_618_);
v_second_619_ = lean_ctor_get(v_wt_615_, 0);
lean_inc(v_second_619_);
v_nano_620_ = lean_ctor_get(v_wt_615_, 1);
lean_inc(v_nano_620_);
lean_dec_ref(v_wt_615_);
v___f_621_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_621_, 0, v___x_614_);
v___x_622_ = lean_mk_thunk(v___f_621_);
v___x_623_ = lean_int_neg(v_offset_618_);
lean_dec(v_offset_618_);
v___x_624_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_625_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_626_ = lean_int_mul(v_second_619_, v___x_625_);
lean_dec(v_second_619_);
v___x_627_ = lean_int_add(v___x_626_, v_nano_620_);
lean_dec(v_nano_620_);
lean_dec(v___x_626_);
v___x_628_ = lean_int_mul(v___x_623_, v___x_625_);
lean_dec(v___x_623_);
v___x_629_ = lean_int_add(v___x_628_, v___x_624_);
lean_dec(v___x_628_);
v___x_630_ = lean_int_add(v___x_627_, v___x_629_);
lean_dec(v___x_629_);
lean_dec(v___x_627_);
v___x_631_ = l_Std_Time_Duration_ofNanoseconds(v___x_630_);
lean_dec(v___x_630_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 3, v_tz_617_);
lean_ctor_set(v___x_611_, 1, v___x_631_);
lean_ctor_set(v___x_611_, 0, v___x_622_);
v___x_633_ = v___x_611_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_rules_609_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_tz_617_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object* v_dt_638_, lean_object* v_months_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_Time_DateTime_addMonthsRollOver(v_dt_638_, v_months_639_);
lean_dec(v_months_639_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object* v_dt_641_, lean_object* v_months_642_){
_start:
{
lean_object* v_date_643_; lean_object* v_rules_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_680_; 
v_date_643_ = lean_ctor_get(v_dt_641_, 0);
v_rules_644_ = lean_ctor_get(v_dt_641_, 2);
v_isSharedCheck_680_ = !lean_is_exclusive(v_dt_641_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; lean_object* v_unused_682_; 
v_unused_681_ = lean_ctor_get(v_dt_641_, 3);
lean_dec(v_unused_681_);
v_unused_682_ = lean_ctor_get(v_dt_641_, 1);
lean_dec(v_unused_682_);
v___x_646_ = v_dt_641_;
v_isShared_647_ = v_isSharedCheck_680_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_rules_644_);
lean_inc(v_date_643_);
lean_dec(v_dt_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_680_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v_date_649_; lean_object* v_time_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_679_; 
v___x_648_ = lean_thunk_get_own(v_date_643_);
lean_dec_ref(v_date_643_);
v_date_649_ = lean_ctor_get(v___x_648_, 0);
v_time_650_ = lean_ctor_get(v___x_648_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_679_ == 0)
{
v___x_652_ = v___x_648_;
v_isShared_653_ = v_isSharedCheck_679_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_time_650_);
lean_inc(v_date_649_);
lean_dec(v___x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_679_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_654_ = lean_int_neg(v_months_642_);
v___x_655_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_649_, v___x_654_);
lean_dec(v___x_654_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_655_);
v___x_657_ = v___x_652_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_time_650_);
v___x_657_ = v_reuseFailAlloc_678_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v_wt_658_; lean_object* v_ltt_659_; lean_object* v_tz_660_; lean_object* v_offset_661_; lean_object* v_second_662_; lean_object* v_nano_663_; lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
lean_inc_ref(v___x_657_);
v_wt_658_ = l_Std_Time_PlainDateTime_toWallTime(v___x_657_);
lean_inc_ref(v_rules_644_);
v_ltt_659_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_644_, v_wt_658_);
v_tz_660_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_659_);
lean_dec_ref(v_ltt_659_);
v_offset_661_ = lean_ctor_get(v_tz_660_, 0);
lean_inc(v_offset_661_);
v_second_662_ = lean_ctor_get(v_wt_658_, 0);
lean_inc(v_second_662_);
v_nano_663_ = lean_ctor_get(v_wt_658_, 1);
lean_inc(v_nano_663_);
lean_dec_ref(v_wt_658_);
v___f_664_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_664_, 0, v___x_657_);
v___x_665_ = lean_mk_thunk(v___f_664_);
v___x_666_ = lean_int_neg(v_offset_661_);
lean_dec(v_offset_661_);
v___x_667_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_668_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_669_ = lean_int_mul(v_second_662_, v___x_668_);
lean_dec(v_second_662_);
v___x_670_ = lean_int_add(v___x_669_, v_nano_663_);
lean_dec(v_nano_663_);
lean_dec(v___x_669_);
v___x_671_ = lean_int_mul(v___x_666_, v___x_668_);
lean_dec(v___x_666_);
v___x_672_ = lean_int_add(v___x_671_, v___x_667_);
lean_dec(v___x_671_);
v___x_673_ = lean_int_add(v___x_670_, v___x_672_);
lean_dec(v___x_672_);
lean_dec(v___x_670_);
v___x_674_ = l_Std_Time_Duration_ofNanoseconds(v___x_673_);
lean_dec(v___x_673_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 3, v_tz_660_);
lean_ctor_set(v___x_646_, 1, v___x_674_);
lean_ctor_set(v___x_646_, 0, v___x_665_);
v___x_676_ = v___x_646_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_rules_644_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_tz_660_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object* v_dt_683_, lean_object* v_months_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_Time_DateTime_subMonthsRollOver(v_dt_683_, v_months_684_);
lean_dec(v_months_684_);
return v_res_685_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(12u);
v___x_687_ = lean_nat_to_int(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object* v_dt_688_, lean_object* v_years_689_){
_start:
{
lean_object* v_date_690_; lean_object* v_rules_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_728_; 
v_date_690_ = lean_ctor_get(v_dt_688_, 0);
v_rules_691_ = lean_ctor_get(v_dt_688_, 2);
v_isSharedCheck_728_ = !lean_is_exclusive(v_dt_688_);
if (v_isSharedCheck_728_ == 0)
{
lean_object* v_unused_729_; lean_object* v_unused_730_; 
v_unused_729_ = lean_ctor_get(v_dt_688_, 3);
lean_dec(v_unused_729_);
v_unused_730_ = lean_ctor_get(v_dt_688_, 1);
lean_dec(v_unused_730_);
v___x_693_ = v_dt_688_;
v_isShared_694_ = v_isSharedCheck_728_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_rules_691_);
lean_inc(v_date_690_);
lean_dec(v_dt_688_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_728_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v_date_696_; lean_object* v_time_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_727_; 
v___x_695_ = lean_thunk_get_own(v_date_690_);
lean_dec_ref(v_date_690_);
v_date_696_ = lean_ctor_get(v___x_695_, 0);
v_time_697_ = lean_ctor_get(v___x_695_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_727_ == 0)
{
v___x_699_ = v___x_695_;
v_isShared_700_ = v_isSharedCheck_727_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_time_697_);
lean_inc(v_date_696_);
lean_dec(v___x_695_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_727_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_701_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_702_ = lean_int_mul(v_years_689_, v___x_701_);
v___x_703_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_696_, v___x_702_);
lean_dec(v___x_702_);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_703_);
v___x_705_ = v___x_699_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_time_697_);
v___x_705_ = v_reuseFailAlloc_726_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v_wt_706_; lean_object* v_ltt_707_; lean_object* v_tz_708_; lean_object* v_offset_709_; lean_object* v_second_710_; lean_object* v_nano_711_; lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
lean_inc_ref(v___x_705_);
v_wt_706_ = l_Std_Time_PlainDateTime_toWallTime(v___x_705_);
lean_inc_ref(v_rules_691_);
v_ltt_707_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_691_, v_wt_706_);
v_tz_708_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_707_);
lean_dec_ref(v_ltt_707_);
v_offset_709_ = lean_ctor_get(v_tz_708_, 0);
lean_inc(v_offset_709_);
v_second_710_ = lean_ctor_get(v_wt_706_, 0);
lean_inc(v_second_710_);
v_nano_711_ = lean_ctor_get(v_wt_706_, 1);
lean_inc(v_nano_711_);
lean_dec_ref(v_wt_706_);
v___f_712_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_712_, 0, v___x_705_);
v___x_713_ = lean_mk_thunk(v___f_712_);
v___x_714_ = lean_int_neg(v_offset_709_);
lean_dec(v_offset_709_);
v___x_715_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_716_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_717_ = lean_int_mul(v_second_710_, v___x_716_);
lean_dec(v_second_710_);
v___x_718_ = lean_int_add(v___x_717_, v_nano_711_);
lean_dec(v_nano_711_);
lean_dec(v___x_717_);
v___x_719_ = lean_int_mul(v___x_714_, v___x_716_);
lean_dec(v___x_714_);
v___x_720_ = lean_int_add(v___x_719_, v___x_715_);
lean_dec(v___x_719_);
v___x_721_ = lean_int_add(v___x_718_, v___x_720_);
lean_dec(v___x_720_);
lean_dec(v___x_718_);
v___x_722_ = l_Std_Time_Duration_ofNanoseconds(v___x_721_);
lean_dec(v___x_721_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 3, v_tz_708_);
lean_ctor_set(v___x_693_, 1, v___x_722_);
lean_ctor_set(v___x_693_, 0, v___x_713_);
v___x_724_ = v___x_693_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_725_, 2, v_rules_691_);
lean_ctor_set(v_reuseFailAlloc_725_, 3, v_tz_708_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object* v_dt_731_, lean_object* v_years_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Std_Time_DateTime_addYearsRollOver(v_dt_731_, v_years_732_);
lean_dec(v_years_732_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object* v_dt_734_, lean_object* v_years_735_){
_start:
{
lean_object* v_date_736_; lean_object* v_rules_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_774_; 
v_date_736_ = lean_ctor_get(v_dt_734_, 0);
v_rules_737_ = lean_ctor_get(v_dt_734_, 2);
v_isSharedCheck_774_ = !lean_is_exclusive(v_dt_734_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; lean_object* v_unused_776_; 
v_unused_775_ = lean_ctor_get(v_dt_734_, 3);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_dt_734_, 1);
lean_dec(v_unused_776_);
v___x_739_ = v_dt_734_;
v_isShared_740_ = v_isSharedCheck_774_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_rules_737_);
lean_inc(v_date_736_);
lean_dec(v_dt_734_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_774_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v_date_742_; lean_object* v_time_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_773_; 
v___x_741_ = lean_thunk_get_own(v_date_736_);
lean_dec_ref(v_date_736_);
v_date_742_ = lean_ctor_get(v___x_741_, 0);
v_time_743_ = lean_ctor_get(v___x_741_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_773_ == 0)
{
v___x_745_ = v___x_741_;
v_isShared_746_ = v_isSharedCheck_773_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_time_743_);
lean_inc(v_date_742_);
lean_dec(v___x_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_773_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_747_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_748_ = lean_int_mul(v_years_735_, v___x_747_);
v___x_749_ = l_Std_Time_PlainDate_addMonthsClip(v_date_742_, v___x_748_);
lean_dec(v___x_748_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_749_);
v___x_751_ = v___x_745_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_time_743_);
v___x_751_ = v_reuseFailAlloc_772_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v_wt_752_; lean_object* v_ltt_753_; lean_object* v_tz_754_; lean_object* v_offset_755_; lean_object* v_second_756_; lean_object* v_nano_757_; lean_object* v___f_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
lean_inc_ref(v___x_751_);
v_wt_752_ = l_Std_Time_PlainDateTime_toWallTime(v___x_751_);
lean_inc_ref(v_rules_737_);
v_ltt_753_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_737_, v_wt_752_);
v_tz_754_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_753_);
lean_dec_ref(v_ltt_753_);
v_offset_755_ = lean_ctor_get(v_tz_754_, 0);
lean_inc(v_offset_755_);
v_second_756_ = lean_ctor_get(v_wt_752_, 0);
lean_inc(v_second_756_);
v_nano_757_ = lean_ctor_get(v_wt_752_, 1);
lean_inc(v_nano_757_);
lean_dec_ref(v_wt_752_);
v___f_758_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_758_, 0, v___x_751_);
v___x_759_ = lean_mk_thunk(v___f_758_);
v___x_760_ = lean_int_neg(v_offset_755_);
lean_dec(v_offset_755_);
v___x_761_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_762_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_763_ = lean_int_mul(v_second_756_, v___x_762_);
lean_dec(v_second_756_);
v___x_764_ = lean_int_add(v___x_763_, v_nano_757_);
lean_dec(v_nano_757_);
lean_dec(v___x_763_);
v___x_765_ = lean_int_mul(v___x_760_, v___x_762_);
lean_dec(v___x_760_);
v___x_766_ = lean_int_add(v___x_765_, v___x_761_);
lean_dec(v___x_765_);
v___x_767_ = lean_int_add(v___x_764_, v___x_766_);
lean_dec(v___x_766_);
lean_dec(v___x_764_);
v___x_768_ = l_Std_Time_Duration_ofNanoseconds(v___x_767_);
lean_dec(v___x_767_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 3, v_tz_754_);
lean_ctor_set(v___x_739_, 1, v___x_768_);
lean_ctor_set(v___x_739_, 0, v___x_759_);
v___x_770_ = v___x_739_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_rules_737_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_tz_754_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object* v_dt_777_, lean_object* v_years_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_Time_DateTime_addYearsClip(v_dt_777_, v_years_778_);
lean_dec(v_years_778_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object* v_dt_780_, lean_object* v_years_781_){
_start:
{
lean_object* v_date_782_; lean_object* v_rules_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_821_; 
v_date_782_ = lean_ctor_get(v_dt_780_, 0);
v_rules_783_ = lean_ctor_get(v_dt_780_, 2);
v_isSharedCheck_821_ = !lean_is_exclusive(v_dt_780_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; lean_object* v_unused_823_; 
v_unused_822_ = lean_ctor_get(v_dt_780_, 3);
lean_dec(v_unused_822_);
v_unused_823_ = lean_ctor_get(v_dt_780_, 1);
lean_dec(v_unused_823_);
v___x_785_ = v_dt_780_;
v_isShared_786_ = v_isSharedCheck_821_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_rules_783_);
lean_inc(v_date_782_);
lean_dec(v_dt_780_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_821_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v_date_788_; lean_object* v_time_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_820_; 
v___x_787_ = lean_thunk_get_own(v_date_782_);
lean_dec_ref(v_date_782_);
v_date_788_ = lean_ctor_get(v___x_787_, 0);
v_time_789_ = lean_ctor_get(v___x_787_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_820_ == 0)
{
v___x_791_ = v___x_787_;
v_isShared_792_ = v_isSharedCheck_820_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_time_789_);
lean_inc(v_date_788_);
lean_dec(v___x_787_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_820_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_793_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_794_ = lean_int_mul(v_years_781_, v___x_793_);
v___x_795_ = lean_int_neg(v___x_794_);
lean_dec(v___x_794_);
v___x_796_ = l_Std_Time_PlainDate_addMonthsClip(v_date_788_, v___x_795_);
lean_dec(v___x_795_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_796_);
v___x_798_ = v___x_791_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_796_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_time_789_);
v___x_798_ = v_reuseFailAlloc_819_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v_wt_799_; lean_object* v_ltt_800_; lean_object* v_tz_801_; lean_object* v_offset_802_; lean_object* v_second_803_; lean_object* v_nano_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_inc_ref(v___x_798_);
v_wt_799_ = l_Std_Time_PlainDateTime_toWallTime(v___x_798_);
lean_inc_ref(v_rules_783_);
v_ltt_800_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_783_, v_wt_799_);
v_tz_801_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_800_);
lean_dec_ref(v_ltt_800_);
v_offset_802_ = lean_ctor_get(v_tz_801_, 0);
lean_inc(v_offset_802_);
v_second_803_ = lean_ctor_get(v_wt_799_, 0);
lean_inc(v_second_803_);
v_nano_804_ = lean_ctor_get(v_wt_799_, 1);
lean_inc(v_nano_804_);
lean_dec_ref(v_wt_799_);
v___f_805_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_805_, 0, v___x_798_);
v___x_806_ = lean_mk_thunk(v___f_805_);
v___x_807_ = lean_int_neg(v_offset_802_);
lean_dec(v_offset_802_);
v___x_808_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_809_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_810_ = lean_int_mul(v_second_803_, v___x_809_);
lean_dec(v_second_803_);
v___x_811_ = lean_int_add(v___x_810_, v_nano_804_);
lean_dec(v_nano_804_);
lean_dec(v___x_810_);
v___x_812_ = lean_int_mul(v___x_807_, v___x_809_);
lean_dec(v___x_807_);
v___x_813_ = lean_int_add(v___x_812_, v___x_808_);
lean_dec(v___x_812_);
v___x_814_ = lean_int_add(v___x_811_, v___x_813_);
lean_dec(v___x_813_);
lean_dec(v___x_811_);
v___x_815_ = l_Std_Time_Duration_ofNanoseconds(v___x_814_);
lean_dec(v___x_814_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 3, v_tz_801_);
lean_ctor_set(v___x_785_, 1, v___x_815_);
lean_ctor_set(v___x_785_, 0, v___x_806_);
v___x_817_ = v___x_785_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v_rules_783_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v_tz_801_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object* v_dt_824_, lean_object* v_years_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_Time_DateTime_subYearsClip(v_dt_824_, v_years_825_);
lean_dec(v_years_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object* v_dt_827_, lean_object* v_years_828_){
_start:
{
lean_object* v_date_829_; lean_object* v_rules_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_868_; 
v_date_829_ = lean_ctor_get(v_dt_827_, 0);
v_rules_830_ = lean_ctor_get(v_dt_827_, 2);
v_isSharedCheck_868_ = !lean_is_exclusive(v_dt_827_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; 
v_unused_869_ = lean_ctor_get(v_dt_827_, 3);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_dt_827_, 1);
lean_dec(v_unused_870_);
v___x_832_ = v_dt_827_;
v_isShared_833_ = v_isSharedCheck_868_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_rules_830_);
lean_inc(v_date_829_);
lean_dec(v_dt_827_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_868_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v_date_835_; lean_object* v_time_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_867_; 
v___x_834_ = lean_thunk_get_own(v_date_829_);
lean_dec_ref(v_date_829_);
v_date_835_ = lean_ctor_get(v___x_834_, 0);
v_time_836_ = lean_ctor_get(v___x_834_, 1);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_867_ == 0)
{
v___x_838_ = v___x_834_;
v_isShared_839_ = v_isSharedCheck_867_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_time_836_);
lean_inc(v_date_835_);
lean_dec(v___x_834_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_867_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_840_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_841_ = lean_int_mul(v_years_828_, v___x_840_);
v___x_842_ = lean_int_neg(v___x_841_);
lean_dec(v___x_841_);
v___x_843_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_835_, v___x_842_);
lean_dec(v___x_842_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_843_);
v___x_845_ = v___x_838_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_time_836_);
v___x_845_ = v_reuseFailAlloc_866_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v_wt_846_; lean_object* v_ltt_847_; lean_object* v_tz_848_; lean_object* v_offset_849_; lean_object* v_second_850_; lean_object* v_nano_851_; lean_object* v___f_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
lean_inc_ref(v___x_845_);
v_wt_846_ = l_Std_Time_PlainDateTime_toWallTime(v___x_845_);
lean_inc_ref(v_rules_830_);
v_ltt_847_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_830_, v_wt_846_);
v_tz_848_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_847_);
lean_dec_ref(v_ltt_847_);
v_offset_849_ = lean_ctor_get(v_tz_848_, 0);
lean_inc(v_offset_849_);
v_second_850_ = lean_ctor_get(v_wt_846_, 0);
lean_inc(v_second_850_);
v_nano_851_ = lean_ctor_get(v_wt_846_, 1);
lean_inc(v_nano_851_);
lean_dec_ref(v_wt_846_);
v___f_852_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_852_, 0, v___x_845_);
v___x_853_ = lean_mk_thunk(v___f_852_);
v___x_854_ = lean_int_neg(v_offset_849_);
lean_dec(v_offset_849_);
v___x_855_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_856_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_857_ = lean_int_mul(v_second_850_, v___x_856_);
lean_dec(v_second_850_);
v___x_858_ = lean_int_add(v___x_857_, v_nano_851_);
lean_dec(v_nano_851_);
lean_dec(v___x_857_);
v___x_859_ = lean_int_mul(v___x_854_, v___x_856_);
lean_dec(v___x_854_);
v___x_860_ = lean_int_add(v___x_859_, v___x_855_);
lean_dec(v___x_859_);
v___x_861_ = lean_int_add(v___x_858_, v___x_860_);
lean_dec(v___x_860_);
lean_dec(v___x_858_);
v___x_862_ = l_Std_Time_Duration_ofNanoseconds(v___x_861_);
lean_dec(v___x_861_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 3, v_tz_848_);
lean_ctor_set(v___x_832_, 1, v___x_862_);
lean_ctor_set(v___x_832_, 0, v___x_853_);
v___x_864_ = v___x_832_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_rules_830_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_tz_848_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object* v_dt_871_, lean_object* v_years_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_Time_DateTime_subYearsRollOver(v_dt_871_, v_years_872_);
lean_dec(v_years_872_);
return v_res_873_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_874_ = lean_unsigned_to_nat(3600u);
v___x_875_ = lean_nat_to_int(v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object* v_dt_876_, lean_object* v_hours_877_){
_start:
{
lean_object* v_timestamp_878_; lean_object* v_rules_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_901_; 
v_timestamp_878_ = lean_ctor_get(v_dt_876_, 1);
v_rules_879_ = lean_ctor_get(v_dt_876_, 2);
v_isSharedCheck_901_ = !lean_is_exclusive(v_dt_876_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; lean_object* v_unused_903_; 
v_unused_902_ = lean_ctor_get(v_dt_876_, 3);
lean_dec(v_unused_902_);
v_unused_903_ = lean_ctor_get(v_dt_876_, 0);
lean_dec(v_unused_903_);
v___x_881_ = v_dt_876_;
v_isShared_882_ = v_isSharedCheck_901_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_rules_879_);
lean_inc(v_timestamp_878_);
lean_dec(v_dt_876_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_901_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_second_883_; lean_object* v_nano_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_tz_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v_second_883_ = lean_ctor_get(v_timestamp_878_, 0);
lean_inc(v_second_883_);
v_nano_884_ = lean_ctor_get(v_timestamp_878_, 1);
lean_inc(v_nano_884_);
lean_dec_ref(v_timestamp_878_);
v___x_885_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_886_ = lean_int_mul(v_hours_877_, v___x_885_);
v___x_887_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_888_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_889_ = lean_int_mul(v_second_883_, v___x_888_);
lean_dec(v_second_883_);
v___x_890_ = lean_int_add(v___x_889_, v_nano_884_);
lean_dec(v_nano_884_);
lean_dec(v___x_889_);
v___x_891_ = lean_int_mul(v___x_886_, v___x_888_);
lean_dec(v___x_886_);
v___x_892_ = lean_int_add(v___x_891_, v___x_887_);
lean_dec(v___x_891_);
v___x_893_ = lean_int_add(v___x_890_, v___x_892_);
lean_dec(v___x_892_);
lean_dec(v___x_890_);
v___x_894_ = l_Std_Time_Duration_ofNanoseconds(v___x_893_);
lean_dec(v___x_893_);
lean_inc_ref(v_rules_879_);
v_tz_895_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_879_, v___x_894_);
lean_inc_ref(v___x_894_);
lean_inc_ref(v_tz_895_);
v___f_896_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_896_, 0, v_tz_895_);
lean_closure_set(v___f_896_, 1, v___x_894_);
lean_closure_set(v___f_896_, 2, v___x_888_);
lean_closure_set(v___f_896_, 3, v___x_887_);
v___x_897_ = lean_mk_thunk(v___f_896_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 3, v_tz_895_);
lean_ctor_set(v___x_881_, 1, v___x_894_);
lean_ctor_set(v___x_881_, 0, v___x_897_);
v___x_899_ = v___x_881_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_894_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_rules_879_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v_tz_895_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object* v_dt_904_, lean_object* v_hours_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_Time_DateTime_addHours(v_dt_904_, v_hours_905_);
lean_dec(v_hours_905_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object* v_dt_907_, lean_object* v_hours_908_){
_start:
{
lean_object* v_timestamp_909_; lean_object* v_rules_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_934_; 
v_timestamp_909_ = lean_ctor_get(v_dt_907_, 1);
v_rules_910_ = lean_ctor_get(v_dt_907_, 2);
v_isSharedCheck_934_ = !lean_is_exclusive(v_dt_907_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; lean_object* v_unused_936_; 
v_unused_935_ = lean_ctor_get(v_dt_907_, 3);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_dt_907_, 0);
lean_dec(v_unused_936_);
v___x_912_ = v_dt_907_;
v_isShared_913_ = v_isSharedCheck_934_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_rules_910_);
lean_inc(v_timestamp_909_);
lean_dec(v_dt_907_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_934_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v_second_914_; lean_object* v_nano_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_tz_928_; lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v_second_914_ = lean_ctor_get(v_timestamp_909_, 0);
lean_inc(v_second_914_);
v_nano_915_ = lean_ctor_get(v_timestamp_909_, 1);
lean_inc(v_nano_915_);
lean_dec_ref(v_timestamp_909_);
v___x_916_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_917_ = lean_int_mul(v_hours_908_, v___x_916_);
v___x_918_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_919_ = lean_int_neg(v___x_917_);
lean_dec(v___x_917_);
v___x_920_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_921_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_922_ = lean_int_mul(v_second_914_, v___x_921_);
lean_dec(v_second_914_);
v___x_923_ = lean_int_add(v___x_922_, v_nano_915_);
lean_dec(v_nano_915_);
lean_dec(v___x_922_);
v___x_924_ = lean_int_mul(v___x_919_, v___x_921_);
lean_dec(v___x_919_);
v___x_925_ = lean_int_add(v___x_924_, v___x_920_);
lean_dec(v___x_924_);
v___x_926_ = lean_int_add(v___x_923_, v___x_925_);
lean_dec(v___x_925_);
lean_dec(v___x_923_);
v___x_927_ = l_Std_Time_Duration_ofNanoseconds(v___x_926_);
lean_dec(v___x_926_);
lean_inc_ref(v_rules_910_);
v_tz_928_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_910_, v___x_927_);
lean_inc_ref(v___x_927_);
lean_inc_ref(v_tz_928_);
v___f_929_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_929_, 0, v_tz_928_);
lean_closure_set(v___f_929_, 1, v___x_927_);
lean_closure_set(v___f_929_, 2, v___x_921_);
lean_closure_set(v___f_929_, 3, v___x_918_);
v___x_930_ = lean_mk_thunk(v___f_929_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 3, v_tz_928_);
lean_ctor_set(v___x_912_, 1, v___x_927_);
lean_ctor_set(v___x_912_, 0, v___x_930_);
v___x_932_ = v___x_912_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_rules_910_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_tz_928_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object* v_dt_937_, lean_object* v_hours_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Std_Time_DateTime_subHours(v_dt_937_, v_hours_938_);
lean_dec(v_hours_938_);
return v_res_939_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_unsigned_to_nat(60u);
v___x_941_ = lean_nat_to_int(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object* v_dt_942_, lean_object* v_minutes_943_){
_start:
{
lean_object* v_timestamp_944_; lean_object* v_rules_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_967_; 
v_timestamp_944_ = lean_ctor_get(v_dt_942_, 1);
v_rules_945_ = lean_ctor_get(v_dt_942_, 2);
v_isSharedCheck_967_ = !lean_is_exclusive(v_dt_942_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; lean_object* v_unused_969_; 
v_unused_968_ = lean_ctor_get(v_dt_942_, 3);
lean_dec(v_unused_968_);
v_unused_969_ = lean_ctor_get(v_dt_942_, 0);
lean_dec(v_unused_969_);
v___x_947_ = v_dt_942_;
v_isShared_948_ = v_isSharedCheck_967_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_rules_945_);
lean_inc(v_timestamp_944_);
lean_dec(v_dt_942_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_967_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v_second_949_; lean_object* v_nano_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_tz_961_; lean_object* v___f_962_; lean_object* v___x_963_; lean_object* v___x_965_; 
v_second_949_ = lean_ctor_get(v_timestamp_944_, 0);
lean_inc(v_second_949_);
v_nano_950_ = lean_ctor_get(v_timestamp_944_, 1);
lean_inc(v_nano_950_);
lean_dec_ref(v_timestamp_944_);
v___x_951_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_952_ = lean_int_mul(v_minutes_943_, v___x_951_);
v___x_953_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_954_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_955_ = lean_int_mul(v_second_949_, v___x_954_);
lean_dec(v_second_949_);
v___x_956_ = lean_int_add(v___x_955_, v_nano_950_);
lean_dec(v_nano_950_);
lean_dec(v___x_955_);
v___x_957_ = lean_int_mul(v___x_952_, v___x_954_);
lean_dec(v___x_952_);
v___x_958_ = lean_int_add(v___x_957_, v___x_953_);
lean_dec(v___x_957_);
v___x_959_ = lean_int_add(v___x_956_, v___x_958_);
lean_dec(v___x_958_);
lean_dec(v___x_956_);
v___x_960_ = l_Std_Time_Duration_ofNanoseconds(v___x_959_);
lean_dec(v___x_959_);
lean_inc_ref(v_rules_945_);
v_tz_961_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_945_, v___x_960_);
lean_inc_ref(v___x_960_);
lean_inc_ref(v_tz_961_);
v___f_962_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_962_, 0, v_tz_961_);
lean_closure_set(v___f_962_, 1, v___x_960_);
lean_closure_set(v___f_962_, 2, v___x_954_);
lean_closure_set(v___f_962_, 3, v___x_953_);
v___x_963_ = lean_mk_thunk(v___f_962_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 3, v_tz_961_);
lean_ctor_set(v___x_947_, 1, v___x_960_);
lean_ctor_set(v___x_947_, 0, v___x_963_);
v___x_965_ = v___x_947_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_963_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_rules_945_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_tz_961_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object* v_dt_970_, lean_object* v_minutes_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Std_Time_DateTime_addMinutes(v_dt_970_, v_minutes_971_);
lean_dec(v_minutes_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object* v_dt_973_, lean_object* v_minutes_974_){
_start:
{
lean_object* v_timestamp_975_; lean_object* v_rules_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1000_; 
v_timestamp_975_ = lean_ctor_get(v_dt_973_, 1);
v_rules_976_ = lean_ctor_get(v_dt_973_, 2);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_dt_973_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; lean_object* v_unused_1002_; 
v_unused_1001_ = lean_ctor_get(v_dt_973_, 3);
lean_dec(v_unused_1001_);
v_unused_1002_ = lean_ctor_get(v_dt_973_, 0);
lean_dec(v_unused_1002_);
v___x_978_ = v_dt_973_;
v_isShared_979_ = v_isSharedCheck_1000_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_rules_976_);
lean_inc(v_timestamp_975_);
lean_dec(v_dt_973_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1000_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_second_980_; lean_object* v_nano_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_tz_994_; lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v_second_980_ = lean_ctor_get(v_timestamp_975_, 0);
lean_inc(v_second_980_);
v_nano_981_ = lean_ctor_get(v_timestamp_975_, 1);
lean_inc(v_nano_981_);
lean_dec_ref(v_timestamp_975_);
v___x_982_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_983_ = lean_int_mul(v_minutes_974_, v___x_982_);
v___x_984_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_985_ = lean_int_neg(v___x_983_);
lean_dec(v___x_983_);
v___x_986_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_987_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_988_ = lean_int_mul(v_second_980_, v___x_987_);
lean_dec(v_second_980_);
v___x_989_ = lean_int_add(v___x_988_, v_nano_981_);
lean_dec(v_nano_981_);
lean_dec(v___x_988_);
v___x_990_ = lean_int_mul(v___x_985_, v___x_987_);
lean_dec(v___x_985_);
v___x_991_ = lean_int_add(v___x_990_, v___x_986_);
lean_dec(v___x_990_);
v___x_992_ = lean_int_add(v___x_989_, v___x_991_);
lean_dec(v___x_991_);
lean_dec(v___x_989_);
v___x_993_ = l_Std_Time_Duration_ofNanoseconds(v___x_992_);
lean_dec(v___x_992_);
lean_inc_ref(v_rules_976_);
v_tz_994_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_976_, v___x_993_);
lean_inc_ref(v___x_993_);
lean_inc_ref(v_tz_994_);
v___f_995_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_995_, 0, v_tz_994_);
lean_closure_set(v___f_995_, 1, v___x_993_);
lean_closure_set(v___f_995_, 2, v___x_987_);
lean_closure_set(v___f_995_, 3, v___x_984_);
v___x_996_ = lean_mk_thunk(v___f_995_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 3, v_tz_994_);
lean_ctor_set(v___x_978_, 1, v___x_993_);
lean_ctor_set(v___x_978_, 0, v___x_996_);
v___x_998_ = v___x_978_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_rules_976_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_tz_994_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object* v_dt_1003_, lean_object* v_minutes_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Std_Time_DateTime_subMinutes(v_dt_1003_, v_minutes_1004_);
lean_dec(v_minutes_1004_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0(lean_object* v_tz_1006_, lean_object* v___x_1007_, lean_object* v___x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v_offset_1010_; lean_object* v_second_1011_; lean_object* v_nano_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v_offset_1010_ = lean_ctor_get(v_tz_1006_, 0);
v_second_1011_ = lean_ctor_get(v___x_1007_, 0);
v_nano_1012_ = lean_ctor_get(v___x_1007_, 1);
v___x_1013_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1014_ = lean_int_mul(v_second_1011_, v___x_1008_);
v___x_1015_ = lean_int_add(v___x_1014_, v_nano_1012_);
lean_dec(v___x_1014_);
v___x_1016_ = lean_int_mul(v_offset_1010_, v___x_1008_);
v___x_1017_ = lean_int_add(v___x_1016_, v___x_1013_);
lean_dec(v___x_1016_);
v___x_1018_ = lean_int_add(v___x_1015_, v___x_1017_);
lean_dec(v___x_1017_);
lean_dec(v___x_1015_);
v___x_1019_ = l_Std_Time_Duration_ofNanoseconds(v___x_1018_);
lean_dec(v___x_1018_);
v___x_1020_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(lean_object* v_tz_1021_, lean_object* v___x_1022_, lean_object* v___x_1023_, lean_object* v_x_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_Time_DateTime_addMilliseconds___lam__0(v_tz_1021_, v___x_1022_, v___x_1023_, v_x_1024_);
lean_dec(v___x_1023_);
lean_dec_ref(v___x_1022_);
lean_dec_ref(v_tz_1021_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object* v_dt_1026_, lean_object* v_milliseconds_1027_){
_start:
{
lean_object* v_timestamp_1028_; lean_object* v_rules_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1053_; 
v_timestamp_1028_ = lean_ctor_get(v_dt_1026_, 1);
v_rules_1029_ = lean_ctor_get(v_dt_1026_, 2);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_dt_1026_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; lean_object* v_unused_1055_; 
v_unused_1054_ = lean_ctor_get(v_dt_1026_, 3);
lean_dec(v_unused_1054_);
v_unused_1055_ = lean_ctor_get(v_dt_1026_, 0);
lean_dec(v_unused_1055_);
v___x_1031_ = v_dt_1026_;
v_isShared_1032_ = v_isSharedCheck_1053_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_rules_1029_);
lean_inc(v_timestamp_1028_);
lean_dec(v_dt_1026_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1053_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_second_1033_; lean_object* v_nano_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_second_1038_; lean_object* v_nano_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_tz_1047_; lean_object* v___f_1048_; lean_object* v___x_1049_; lean_object* v___x_1051_; 
v_second_1033_ = lean_ctor_get(v_timestamp_1028_, 0);
lean_inc(v_second_1033_);
v_nano_1034_ = lean_ctor_get(v_timestamp_1028_, 1);
lean_inc(v_nano_1034_);
lean_dec_ref(v_timestamp_1028_);
v___x_1035_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1036_ = lean_int_mul(v_milliseconds_1027_, v___x_1035_);
v___x_1037_ = l_Std_Time_Duration_ofNanoseconds(v___x_1036_);
lean_dec(v___x_1036_);
v_second_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_second_1038_);
v_nano_1039_ = lean_ctor_get(v___x_1037_, 1);
lean_inc(v_nano_1039_);
lean_dec_ref(v___x_1037_);
v___x_1040_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1041_ = lean_int_mul(v_second_1033_, v___x_1040_);
lean_dec(v_second_1033_);
v___x_1042_ = lean_int_add(v___x_1041_, v_nano_1034_);
lean_dec(v_nano_1034_);
lean_dec(v___x_1041_);
v___x_1043_ = lean_int_mul(v_second_1038_, v___x_1040_);
lean_dec(v_second_1038_);
v___x_1044_ = lean_int_add(v___x_1043_, v_nano_1039_);
lean_dec(v_nano_1039_);
lean_dec(v___x_1043_);
v___x_1045_ = lean_int_add(v___x_1042_, v___x_1044_);
lean_dec(v___x_1044_);
lean_dec(v___x_1042_);
v___x_1046_ = l_Std_Time_Duration_ofNanoseconds(v___x_1045_);
lean_dec(v___x_1045_);
lean_inc_ref(v_rules_1029_);
v_tz_1047_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1029_, v___x_1046_);
lean_inc_ref(v___x_1046_);
lean_inc_ref(v_tz_1047_);
v___f_1048_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1048_, 0, v_tz_1047_);
lean_closure_set(v___f_1048_, 1, v___x_1046_);
lean_closure_set(v___f_1048_, 2, v___x_1040_);
v___x_1049_ = lean_mk_thunk(v___f_1048_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 3, v_tz_1047_);
lean_ctor_set(v___x_1031_, 1, v___x_1046_);
lean_ctor_set(v___x_1031_, 0, v___x_1049_);
v___x_1051_ = v___x_1031_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1052_, 2, v_rules_1029_);
lean_ctor_set(v_reuseFailAlloc_1052_, 3, v_tz_1047_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object* v_dt_1056_, lean_object* v_milliseconds_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Std_Time_DateTime_addMilliseconds(v_dt_1056_, v_milliseconds_1057_);
lean_dec(v_milliseconds_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object* v_dt_1059_, lean_object* v_milliseconds_1060_){
_start:
{
lean_object* v_timestamp_1061_; lean_object* v_rules_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1088_; 
v_timestamp_1061_ = lean_ctor_get(v_dt_1059_, 1);
v_rules_1062_ = lean_ctor_get(v_dt_1059_, 2);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_dt_1059_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; lean_object* v_unused_1090_; 
v_unused_1089_ = lean_ctor_get(v_dt_1059_, 3);
lean_dec(v_unused_1089_);
v_unused_1090_ = lean_ctor_get(v_dt_1059_, 0);
lean_dec(v_unused_1090_);
v___x_1064_ = v_dt_1059_;
v_isShared_1065_ = v_isSharedCheck_1088_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_rules_1062_);
lean_inc(v_timestamp_1061_);
lean_dec(v_dt_1059_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1088_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v_second_1069_; lean_object* v_nano_1070_; lean_object* v_second_1071_; lean_object* v_nano_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v_tz_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1066_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1067_ = lean_int_mul(v_milliseconds_1060_, v___x_1066_);
v___x_1068_ = l_Std_Time_Duration_ofNanoseconds(v___x_1067_);
lean_dec(v___x_1067_);
v_second_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_second_1069_);
v_nano_1070_ = lean_ctor_get(v___x_1068_, 1);
lean_inc(v_nano_1070_);
lean_dec_ref(v___x_1068_);
v_second_1071_ = lean_ctor_get(v_timestamp_1061_, 0);
lean_inc(v_second_1071_);
v_nano_1072_ = lean_ctor_get(v_timestamp_1061_, 1);
lean_inc(v_nano_1072_);
lean_dec_ref(v_timestamp_1061_);
v___x_1073_ = lean_int_neg(v_second_1069_);
lean_dec(v_second_1069_);
v___x_1074_ = lean_int_neg(v_nano_1070_);
lean_dec(v_nano_1070_);
v___x_1075_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1076_ = lean_int_mul(v_second_1071_, v___x_1075_);
lean_dec(v_second_1071_);
v___x_1077_ = lean_int_add(v___x_1076_, v_nano_1072_);
lean_dec(v_nano_1072_);
lean_dec(v___x_1076_);
v___x_1078_ = lean_int_mul(v___x_1073_, v___x_1075_);
lean_dec(v___x_1073_);
v___x_1079_ = lean_int_add(v___x_1078_, v___x_1074_);
lean_dec(v___x_1074_);
lean_dec(v___x_1078_);
v___x_1080_ = lean_int_add(v___x_1077_, v___x_1079_);
lean_dec(v___x_1079_);
lean_dec(v___x_1077_);
v___x_1081_ = l_Std_Time_Duration_ofNanoseconds(v___x_1080_);
lean_dec(v___x_1080_);
lean_inc_ref(v_rules_1062_);
v_tz_1082_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1062_, v___x_1081_);
lean_inc_ref(v___x_1081_);
lean_inc_ref(v_tz_1082_);
v___f_1083_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1083_, 0, v_tz_1082_);
lean_closure_set(v___f_1083_, 1, v___x_1081_);
lean_closure_set(v___f_1083_, 2, v___x_1075_);
v___x_1084_ = lean_mk_thunk(v___f_1083_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 3, v_tz_1082_);
lean_ctor_set(v___x_1064_, 1, v___x_1081_);
lean_ctor_set(v___x_1064_, 0, v___x_1084_);
v___x_1086_ = v___x_1064_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1084_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_rules_1062_);
lean_ctor_set(v_reuseFailAlloc_1087_, 3, v_tz_1082_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object* v_dt_1091_, lean_object* v_milliseconds_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Std_Time_DateTime_subMilliseconds(v_dt_1091_, v_milliseconds_1092_);
lean_dec(v_milliseconds_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object* v_dt_1094_, lean_object* v_seconds_1095_){
_start:
{
lean_object* v_timestamp_1096_; lean_object* v_rules_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1117_; 
v_timestamp_1096_ = lean_ctor_get(v_dt_1094_, 1);
v_rules_1097_ = lean_ctor_get(v_dt_1094_, 2);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_dt_1094_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; lean_object* v_unused_1119_; 
v_unused_1118_ = lean_ctor_get(v_dt_1094_, 3);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_dt_1094_, 0);
lean_dec(v_unused_1119_);
v___x_1099_ = v_dt_1094_;
v_isShared_1100_ = v_isSharedCheck_1117_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_rules_1097_);
lean_inc(v_timestamp_1096_);
lean_dec(v_dt_1094_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1117_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_second_1101_; lean_object* v_nano_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v_tz_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v_second_1101_ = lean_ctor_get(v_timestamp_1096_, 0);
lean_inc(v_second_1101_);
v_nano_1102_ = lean_ctor_get(v_timestamp_1096_, 1);
lean_inc(v_nano_1102_);
lean_dec_ref(v_timestamp_1096_);
v___x_1103_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1104_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1105_ = lean_int_mul(v_second_1101_, v___x_1104_);
lean_dec(v_second_1101_);
v___x_1106_ = lean_int_add(v___x_1105_, v_nano_1102_);
lean_dec(v_nano_1102_);
lean_dec(v___x_1105_);
v___x_1107_ = lean_int_mul(v_seconds_1095_, v___x_1104_);
v___x_1108_ = lean_int_add(v___x_1107_, v___x_1103_);
lean_dec(v___x_1107_);
v___x_1109_ = lean_int_add(v___x_1106_, v___x_1108_);
lean_dec(v___x_1108_);
lean_dec(v___x_1106_);
v___x_1110_ = l_Std_Time_Duration_ofNanoseconds(v___x_1109_);
lean_dec(v___x_1109_);
lean_inc_ref(v_rules_1097_);
v_tz_1111_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1097_, v___x_1110_);
lean_inc_ref(v___x_1110_);
lean_inc_ref(v_tz_1111_);
v___f_1112_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1112_, 0, v_tz_1111_);
lean_closure_set(v___f_1112_, 1, v___x_1110_);
lean_closure_set(v___f_1112_, 2, v___x_1104_);
lean_closure_set(v___f_1112_, 3, v___x_1103_);
v___x_1113_ = lean_mk_thunk(v___f_1112_);
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 3, v_tz_1111_);
lean_ctor_set(v___x_1099_, 1, v___x_1110_);
lean_ctor_set(v___x_1099_, 0, v___x_1113_);
v___x_1115_ = v___x_1099_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_rules_1097_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_tz_1111_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object* v_dt_1120_, lean_object* v_seconds_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_Time_DateTime_addSeconds(v_dt_1120_, v_seconds_1121_);
lean_dec(v_seconds_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object* v_dt_1123_, lean_object* v_seconds_1124_){
_start:
{
lean_object* v_timestamp_1125_; lean_object* v_rules_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1148_; 
v_timestamp_1125_ = lean_ctor_get(v_dt_1123_, 1);
v_rules_1126_ = lean_ctor_get(v_dt_1123_, 2);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_dt_1123_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; lean_object* v_unused_1150_; 
v_unused_1149_ = lean_ctor_get(v_dt_1123_, 3);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_dt_1123_, 0);
lean_dec(v_unused_1150_);
v___x_1128_ = v_dt_1123_;
v_isShared_1129_ = v_isSharedCheck_1148_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_rules_1126_);
lean_inc(v_timestamp_1125_);
lean_dec(v_dt_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1148_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_second_1130_; lean_object* v_nano_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v_tz_1142_; lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v_second_1130_ = lean_ctor_get(v_timestamp_1125_, 0);
lean_inc(v_second_1130_);
v_nano_1131_ = lean_ctor_get(v_timestamp_1125_, 1);
lean_inc(v_nano_1131_);
lean_dec_ref(v_timestamp_1125_);
v___x_1132_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1133_ = lean_int_neg(v_seconds_1124_);
v___x_1134_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1135_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1136_ = lean_int_mul(v_second_1130_, v___x_1135_);
lean_dec(v_second_1130_);
v___x_1137_ = lean_int_add(v___x_1136_, v_nano_1131_);
lean_dec(v_nano_1131_);
lean_dec(v___x_1136_);
v___x_1138_ = lean_int_mul(v___x_1133_, v___x_1135_);
lean_dec(v___x_1133_);
v___x_1139_ = lean_int_add(v___x_1138_, v___x_1134_);
lean_dec(v___x_1138_);
v___x_1140_ = lean_int_add(v___x_1137_, v___x_1139_);
lean_dec(v___x_1139_);
lean_dec(v___x_1137_);
v___x_1141_ = l_Std_Time_Duration_ofNanoseconds(v___x_1140_);
lean_dec(v___x_1140_);
lean_inc_ref(v_rules_1126_);
v_tz_1142_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1126_, v___x_1141_);
lean_inc_ref(v___x_1141_);
lean_inc_ref(v_tz_1142_);
v___f_1143_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1143_, 0, v_tz_1142_);
lean_closure_set(v___f_1143_, 1, v___x_1141_);
lean_closure_set(v___f_1143_, 2, v___x_1135_);
lean_closure_set(v___f_1143_, 3, v___x_1132_);
v___x_1144_ = lean_mk_thunk(v___f_1143_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 3, v_tz_1142_);
lean_ctor_set(v___x_1128_, 1, v___x_1141_);
lean_ctor_set(v___x_1128_, 0, v___x_1144_);
v___x_1146_ = v___x_1128_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_rules_1126_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_tz_1142_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object* v_dt_1151_, lean_object* v_seconds_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Std_Time_DateTime_subSeconds(v_dt_1151_, v_seconds_1152_);
lean_dec(v_seconds_1152_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object* v_dt_1154_, lean_object* v_nanoseconds_1155_){
_start:
{
lean_object* v_timestamp_1156_; lean_object* v_rules_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1179_; 
v_timestamp_1156_ = lean_ctor_get(v_dt_1154_, 1);
v_rules_1157_ = lean_ctor_get(v_dt_1154_, 2);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_dt_1154_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; lean_object* v_unused_1181_; 
v_unused_1180_ = lean_ctor_get(v_dt_1154_, 3);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_dt_1154_, 0);
lean_dec(v_unused_1181_);
v___x_1159_ = v_dt_1154_;
v_isShared_1160_ = v_isSharedCheck_1179_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_rules_1157_);
lean_inc(v_timestamp_1156_);
lean_dec(v_dt_1154_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1179_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v_second_1161_; lean_object* v_nano_1162_; lean_object* v___x_1163_; lean_object* v_second_1164_; lean_object* v_nano_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v_tz_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v_second_1161_ = lean_ctor_get(v_timestamp_1156_, 0);
lean_inc(v_second_1161_);
v_nano_1162_ = lean_ctor_get(v_timestamp_1156_, 1);
lean_inc(v_nano_1162_);
lean_dec_ref(v_timestamp_1156_);
v___x_1163_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1155_);
v_second_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_second_1164_);
v_nano_1165_ = lean_ctor_get(v___x_1163_, 1);
lean_inc(v_nano_1165_);
lean_dec_ref(v___x_1163_);
v___x_1166_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1167_ = lean_int_mul(v_second_1161_, v___x_1166_);
lean_dec(v_second_1161_);
v___x_1168_ = lean_int_add(v___x_1167_, v_nano_1162_);
lean_dec(v_nano_1162_);
lean_dec(v___x_1167_);
v___x_1169_ = lean_int_mul(v_second_1164_, v___x_1166_);
lean_dec(v_second_1164_);
v___x_1170_ = lean_int_add(v___x_1169_, v_nano_1165_);
lean_dec(v_nano_1165_);
lean_dec(v___x_1169_);
v___x_1171_ = lean_int_add(v___x_1168_, v___x_1170_);
lean_dec(v___x_1170_);
lean_dec(v___x_1168_);
v___x_1172_ = l_Std_Time_Duration_ofNanoseconds(v___x_1171_);
lean_dec(v___x_1171_);
lean_inc_ref(v_rules_1157_);
v_tz_1173_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1157_, v___x_1172_);
lean_inc_ref(v___x_1172_);
lean_inc_ref(v_tz_1173_);
v___f_1174_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1174_, 0, v_tz_1173_);
lean_closure_set(v___f_1174_, 1, v___x_1172_);
lean_closure_set(v___f_1174_, 2, v___x_1166_);
v___x_1175_ = lean_mk_thunk(v___f_1174_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 3, v_tz_1173_);
lean_ctor_set(v___x_1159_, 1, v___x_1172_);
lean_ctor_set(v___x_1159_, 0, v___x_1175_);
v___x_1177_ = v___x_1159_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_rules_1157_);
lean_ctor_set(v_reuseFailAlloc_1178_, 3, v_tz_1173_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object* v_dt_1182_, lean_object* v_nanoseconds_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Std_Time_DateTime_addNanoseconds(v_dt_1182_, v_nanoseconds_1183_);
lean_dec(v_nanoseconds_1183_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object* v_dt_1185_, lean_object* v_nanoseconds_1186_){
_start:
{
lean_object* v_timestamp_1187_; lean_object* v_rules_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1212_; 
v_timestamp_1187_ = lean_ctor_get(v_dt_1185_, 1);
v_rules_1188_ = lean_ctor_get(v_dt_1185_, 2);
v_isSharedCheck_1212_ = !lean_is_exclusive(v_dt_1185_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; lean_object* v_unused_1214_; 
v_unused_1213_ = lean_ctor_get(v_dt_1185_, 3);
lean_dec(v_unused_1213_);
v_unused_1214_ = lean_ctor_get(v_dt_1185_, 0);
lean_dec(v_unused_1214_);
v___x_1190_ = v_dt_1185_;
v_isShared_1191_ = v_isSharedCheck_1212_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_rules_1188_);
lean_inc(v_timestamp_1187_);
lean_dec(v_dt_1185_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1212_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v_second_1193_; lean_object* v_nano_1194_; lean_object* v_second_1195_; lean_object* v_nano_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_tz_1206_; lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1192_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1186_);
v_second_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_second_1193_);
v_nano_1194_ = lean_ctor_get(v___x_1192_, 1);
lean_inc(v_nano_1194_);
lean_dec_ref(v___x_1192_);
v_second_1195_ = lean_ctor_get(v_timestamp_1187_, 0);
lean_inc(v_second_1195_);
v_nano_1196_ = lean_ctor_get(v_timestamp_1187_, 1);
lean_inc(v_nano_1196_);
lean_dec_ref(v_timestamp_1187_);
v___x_1197_ = lean_int_neg(v_second_1193_);
lean_dec(v_second_1193_);
v___x_1198_ = lean_int_neg(v_nano_1194_);
lean_dec(v_nano_1194_);
v___x_1199_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1200_ = lean_int_mul(v_second_1195_, v___x_1199_);
lean_dec(v_second_1195_);
v___x_1201_ = lean_int_add(v___x_1200_, v_nano_1196_);
lean_dec(v_nano_1196_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_int_mul(v___x_1197_, v___x_1199_);
lean_dec(v___x_1197_);
v___x_1203_ = lean_int_add(v___x_1202_, v___x_1198_);
lean_dec(v___x_1198_);
lean_dec(v___x_1202_);
v___x_1204_ = lean_int_add(v___x_1201_, v___x_1203_);
lean_dec(v___x_1203_);
lean_dec(v___x_1201_);
v___x_1205_ = l_Std_Time_Duration_ofNanoseconds(v___x_1204_);
lean_dec(v___x_1204_);
lean_inc_ref(v_rules_1188_);
v_tz_1206_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1188_, v___x_1205_);
lean_inc_ref(v___x_1205_);
lean_inc_ref(v_tz_1206_);
v___f_1207_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1207_, 0, v_tz_1206_);
lean_closure_set(v___f_1207_, 1, v___x_1205_);
lean_closure_set(v___f_1207_, 2, v___x_1199_);
v___x_1208_ = lean_mk_thunk(v___f_1207_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 3, v_tz_1206_);
lean_ctor_set(v___x_1190_, 1, v___x_1205_);
lean_ctor_set(v___x_1190_, 0, v___x_1208_);
v___x_1210_ = v___x_1190_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_rules_1188_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_tz_1206_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object* v_dt_1215_, lean_object* v_nanoseconds_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_Time_DateTime_subNanoseconds(v_dt_1215_, v_nanoseconds_1216_);
lean_dec(v_nanoseconds_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object* v_date_1218_){
_start:
{
lean_object* v_date_1219_; lean_object* v___x_1220_; lean_object* v_date_1221_; lean_object* v_year_1222_; uint8_t v___x_1223_; 
v_date_1219_ = lean_ctor_get(v_date_1218_, 0);
v___x_1220_ = lean_thunk_get_own(v_date_1219_);
v_date_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc_ref(v_date_1221_);
lean_dec(v___x_1220_);
v_year_1222_ = lean_ctor_get(v_date_1221_, 0);
lean_inc(v_year_1222_);
lean_dec_ref(v_date_1221_);
v___x_1223_ = l_Std_Time_Year_Offset_era(v_year_1222_);
lean_dec(v_year_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object* v_date_1224_){
_start:
{
uint8_t v_res_1225_; lean_object* v_r_1226_; 
v_res_1225_ = l_Std_Time_DateTime_era(v_date_1224_);
lean_dec_ref(v_date_1224_);
v_r_1226_ = lean_box(v_res_1225_);
return v_r_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object* v_dt_1227_, uint8_t v_desiredWeekday_1228_){
_start:
{
lean_object* v_date_1229_; lean_object* v_rules_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1256_; 
v_date_1229_ = lean_ctor_get(v_dt_1227_, 0);
v_rules_1230_ = lean_ctor_get(v_dt_1227_, 2);
v_isSharedCheck_1256_ = !lean_is_exclusive(v_dt_1227_);
if (v_isSharedCheck_1256_ == 0)
{
lean_object* v_unused_1257_; lean_object* v_unused_1258_; 
v_unused_1257_ = lean_ctor_get(v_dt_1227_, 3);
lean_dec(v_unused_1257_);
v_unused_1258_ = lean_ctor_get(v_dt_1227_, 1);
lean_dec(v_unused_1258_);
v___x_1232_ = v_dt_1227_;
v_isShared_1233_ = v_isSharedCheck_1256_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_rules_1230_);
lean_inc(v_date_1229_);
lean_dec(v_dt_1227_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1256_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v_date_1234_; lean_object* v___x_1235_; lean_object* v_wt_1236_; lean_object* v_ltt_1237_; lean_object* v_tz_1238_; lean_object* v_offset_1239_; lean_object* v_second_1240_; lean_object* v_nano_1241_; lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v_date_1234_ = lean_thunk_get_own(v_date_1229_);
lean_dec_ref(v_date_1229_);
v___x_1235_ = l_Std_Time_PlainDateTime_withWeekday(v_date_1234_, v_desiredWeekday_1228_);
lean_inc_ref(v___x_1235_);
v_wt_1236_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1235_);
lean_inc_ref(v_rules_1230_);
v_ltt_1237_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1230_, v_wt_1236_);
v_tz_1238_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1237_);
lean_dec_ref(v_ltt_1237_);
v_offset_1239_ = lean_ctor_get(v_tz_1238_, 0);
lean_inc(v_offset_1239_);
v_second_1240_ = lean_ctor_get(v_wt_1236_, 0);
lean_inc(v_second_1240_);
v_nano_1241_ = lean_ctor_get(v_wt_1236_, 1);
lean_inc(v_nano_1241_);
lean_dec_ref(v_wt_1236_);
v___f_1242_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1242_, 0, v___x_1235_);
v___x_1243_ = lean_mk_thunk(v___f_1242_);
v___x_1244_ = lean_int_neg(v_offset_1239_);
lean_dec(v_offset_1239_);
v___x_1245_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1246_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1247_ = lean_int_mul(v_second_1240_, v___x_1246_);
lean_dec(v_second_1240_);
v___x_1248_ = lean_int_add(v___x_1247_, v_nano_1241_);
lean_dec(v_nano_1241_);
lean_dec(v___x_1247_);
v___x_1249_ = lean_int_mul(v___x_1244_, v___x_1246_);
lean_dec(v___x_1244_);
v___x_1250_ = lean_int_add(v___x_1249_, v___x_1245_);
lean_dec(v___x_1249_);
v___x_1251_ = lean_int_add(v___x_1248_, v___x_1250_);
lean_dec(v___x_1250_);
lean_dec(v___x_1248_);
v___x_1252_ = l_Std_Time_Duration_ofNanoseconds(v___x_1251_);
lean_dec(v___x_1251_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 3, v_tz_1238_);
lean_ctor_set(v___x_1232_, 1, v___x_1252_);
lean_ctor_set(v___x_1232_, 0, v___x_1243_);
v___x_1254_ = v___x_1232_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1255_, 2, v_rules_1230_);
lean_ctor_set(v_reuseFailAlloc_1255_, 3, v_tz_1238_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object* v_dt_1259_, lean_object* v_desiredWeekday_1260_){
_start:
{
uint8_t v_desiredWeekday_boxed_1261_; lean_object* v_res_1262_; 
v_desiredWeekday_boxed_1261_ = lean_unbox(v_desiredWeekday_1260_);
v_res_1262_ = l_Std_Time_DateTime_withWeekday(v_dt_1259_, v_desiredWeekday_boxed_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object* v_dt_1263_, lean_object* v_days_1264_){
_start:
{
lean_object* v_date_1265_; lean_object* v_rules_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1331_; 
v_date_1265_ = lean_ctor_get(v_dt_1263_, 0);
v_rules_1266_ = lean_ctor_get(v_dt_1263_, 2);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_dt_1263_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; lean_object* v_unused_1333_; 
v_unused_1332_ = lean_ctor_get(v_dt_1263_, 3);
lean_dec(v_unused_1332_);
v_unused_1333_ = lean_ctor_get(v_dt_1263_, 1);
lean_dec(v_unused_1333_);
v___x_1268_ = v_dt_1263_;
v_isShared_1269_ = v_isSharedCheck_1331_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_rules_1266_);
lean_inc(v_date_1265_);
lean_dec(v_dt_1263_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1331_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v_date_1270_; lean_object* v___y_1272_; lean_object* v_date_1302_; lean_object* v_year_1303_; lean_object* v_month_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1329_; 
v_date_1270_ = lean_thunk_get_own(v_date_1265_);
lean_dec_ref(v_date_1265_);
v_date_1302_ = lean_ctor_get(v_date_1270_, 0);
lean_inc_ref(v_date_1302_);
v_year_1303_ = lean_ctor_get(v_date_1302_, 0);
v_month_1304_ = lean_ctor_get(v_date_1302_, 1);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_date_1302_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v_date_1302_, 2);
lean_dec(v_unused_1330_);
v___x_1306_ = v_date_1302_;
v_isShared_1307_ = v_isSharedCheck_1329_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_month_1304_);
lean_inc(v_year_1303_);
lean_dec(v_date_1302_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1329_;
goto v_resetjp_1305_;
}
v___jp_1271_:
{
lean_object* v_time_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1300_; 
v_time_1273_ = lean_ctor_get(v_date_1270_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v_date_1270_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v_date_1270_, 0);
lean_dec(v_unused_1301_);
v___x_1275_ = v_date_1270_;
v_isShared_1276_ = v_isSharedCheck_1300_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_time_1273_);
lean_dec(v_date_1270_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1300_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___y_1272_);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___y_1272_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_time_1273_);
v___x_1278_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v_wt_1279_; lean_object* v_ltt_1280_; lean_object* v_tz_1281_; lean_object* v_offset_1282_; lean_object* v_second_1283_; lean_object* v_nano_1284_; lean_object* v___f_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_inc_ref(v___x_1278_);
v_wt_1279_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1278_);
lean_inc_ref(v_rules_1266_);
v_ltt_1280_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1266_, v_wt_1279_);
v_tz_1281_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1280_);
lean_dec_ref(v_ltt_1280_);
v_offset_1282_ = lean_ctor_get(v_tz_1281_, 0);
lean_inc(v_offset_1282_);
v_second_1283_ = lean_ctor_get(v_wt_1279_, 0);
lean_inc(v_second_1283_);
v_nano_1284_ = lean_ctor_get(v_wt_1279_, 1);
lean_inc(v_nano_1284_);
lean_dec_ref(v_wt_1279_);
v___f_1285_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1285_, 0, v___x_1278_);
v___x_1286_ = lean_mk_thunk(v___f_1285_);
v___x_1287_ = lean_int_neg(v_offset_1282_);
lean_dec(v_offset_1282_);
v___x_1288_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1289_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1290_ = lean_int_mul(v_second_1283_, v___x_1289_);
lean_dec(v_second_1283_);
v___x_1291_ = lean_int_add(v___x_1290_, v_nano_1284_);
lean_dec(v_nano_1284_);
lean_dec(v___x_1290_);
v___x_1292_ = lean_int_mul(v___x_1287_, v___x_1289_);
lean_dec(v___x_1287_);
v___x_1293_ = lean_int_add(v___x_1292_, v___x_1288_);
lean_dec(v___x_1292_);
v___x_1294_ = lean_int_add(v___x_1291_, v___x_1293_);
lean_dec(v___x_1293_);
lean_dec(v___x_1291_);
v___x_1295_ = l_Std_Time_Duration_ofNanoseconds(v___x_1294_);
lean_dec(v___x_1294_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 3, v_tz_1281_);
lean_ctor_set(v___x_1268_, 1, v___x_1295_);
lean_ctor_set(v___x_1268_, 0, v___x_1286_);
v___x_1297_ = v___x_1268_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1298_, 2, v_rules_1266_);
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
}
v_resetjp_1305_:
{
uint8_t v___y_1309_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1325_; 
v___x_1318_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1319_ = lean_int_mod(v_year_1303_, v___x_1318_);
v___x_1320_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1325_ = lean_int_dec_eq(v___x_1319_, v___x_1320_);
lean_dec(v___x_1319_);
if (v___x_1325_ == 0)
{
v___y_1309_ = v___x_1325_;
goto v___jp_1308_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1326_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1327_ = lean_int_mod(v_year_1303_, v___x_1326_);
v___x_1328_ = lean_int_dec_eq(v___x_1327_, v___x_1320_);
lean_dec(v___x_1327_);
if (v___x_1328_ == 0)
{
if (v___x_1325_ == 0)
{
goto v___jp_1321_;
}
else
{
v___y_1309_ = v___x_1325_;
goto v___jp_1308_;
}
}
else
{
goto v___jp_1321_;
}
}
v___jp_1308_:
{
lean_object* v_max_1310_; uint8_t v___x_1311_; 
v_max_1310_ = l_Std_Time_Month_Ordinal_days(v___y_1309_, v_month_1304_);
v___x_1311_ = lean_int_dec_lt(v_max_1310_, v_days_1264_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1313_; 
lean_dec(v_max_1310_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 2, v_days_1264_);
v___x_1313_ = v___x_1306_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_year_1303_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_month_1304_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_days_1264_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
v___y_1272_ = v___x_1313_;
goto v___jp_1271_;
}
}
else
{
lean_object* v___x_1316_; 
lean_dec(v_days_1264_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 2, v_max_1310_);
v___x_1316_ = v___x_1306_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_year_1303_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_month_1304_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_max_1310_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
v___y_1272_ = v___x_1316_;
goto v___jp_1271_;
}
}
}
v___jp_1321_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1322_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1323_ = lean_int_mod(v_year_1303_, v___x_1322_);
v___x_1324_ = lean_int_dec_eq(v___x_1323_, v___x_1320_);
lean_dec(v___x_1323_);
v___y_1309_ = v___x_1324_;
goto v___jp_1308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object* v_dt_1334_, lean_object* v_days_1335_){
_start:
{
lean_object* v_date_1336_; lean_object* v_rules_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1374_; 
v_date_1336_ = lean_ctor_get(v_dt_1334_, 0);
v_rules_1337_ = lean_ctor_get(v_dt_1334_, 2);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_dt_1334_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; lean_object* v_unused_1376_; 
v_unused_1375_ = lean_ctor_get(v_dt_1334_, 3);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_dt_1334_, 1);
lean_dec(v_unused_1376_);
v___x_1339_ = v_dt_1334_;
v_isShared_1340_ = v_isSharedCheck_1374_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_rules_1337_);
lean_inc(v_date_1336_);
lean_dec(v_dt_1334_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1374_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_date_1341_; lean_object* v_date_1342_; lean_object* v_time_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1373_; 
v_date_1341_ = lean_thunk_get_own(v_date_1336_);
lean_dec_ref(v_date_1336_);
v_date_1342_ = lean_ctor_get(v_date_1341_, 0);
v_time_1343_ = lean_ctor_get(v_date_1341_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_date_1341_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1345_ = v_date_1341_;
v_isShared_1346_ = v_isSharedCheck_1373_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_time_1343_);
lean_inc(v_date_1342_);
lean_dec(v_date_1341_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1373_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_year_1347_; lean_object* v_month_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v_year_1347_ = lean_ctor_get(v_date_1342_, 0);
lean_inc(v_year_1347_);
v_month_1348_ = lean_ctor_get(v_date_1342_, 1);
lean_inc(v_month_1348_);
lean_dec_ref(v_date_1342_);
v___x_1349_ = l_Std_Time_PlainDate_rollOver(v_year_1347_, v_month_1348_, v_days_1335_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1349_);
v___x_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_time_1343_);
v___x_1351_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v_wt_1352_; lean_object* v_ltt_1353_; lean_object* v_tz_1354_; lean_object* v_offset_1355_; lean_object* v_second_1356_; lean_object* v_nano_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_inc_ref(v___x_1351_);
v_wt_1352_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1351_);
lean_inc_ref(v_rules_1337_);
v_ltt_1353_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1337_, v_wt_1352_);
v_tz_1354_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1353_);
lean_dec_ref(v_ltt_1353_);
v_offset_1355_ = lean_ctor_get(v_tz_1354_, 0);
lean_inc(v_offset_1355_);
v_second_1356_ = lean_ctor_get(v_wt_1352_, 0);
lean_inc(v_second_1356_);
v_nano_1357_ = lean_ctor_get(v_wt_1352_, 1);
lean_inc(v_nano_1357_);
lean_dec_ref(v_wt_1352_);
v___f_1358_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1358_, 0, v___x_1351_);
v___x_1359_ = lean_mk_thunk(v___f_1358_);
v___x_1360_ = lean_int_neg(v_offset_1355_);
lean_dec(v_offset_1355_);
v___x_1361_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1362_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1363_ = lean_int_mul(v_second_1356_, v___x_1362_);
lean_dec(v_second_1356_);
v___x_1364_ = lean_int_add(v___x_1363_, v_nano_1357_);
lean_dec(v_nano_1357_);
lean_dec(v___x_1363_);
v___x_1365_ = lean_int_mul(v___x_1360_, v___x_1362_);
lean_dec(v___x_1360_);
v___x_1366_ = lean_int_add(v___x_1365_, v___x_1361_);
lean_dec(v___x_1365_);
v___x_1367_ = lean_int_add(v___x_1364_, v___x_1366_);
lean_dec(v___x_1366_);
lean_dec(v___x_1364_);
v___x_1368_ = l_Std_Time_Duration_ofNanoseconds(v___x_1367_);
lean_dec(v___x_1367_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 3, v_tz_1354_);
lean_ctor_set(v___x_1339_, 1, v___x_1368_);
lean_ctor_set(v___x_1339_, 0, v___x_1359_);
v___x_1370_ = v___x_1339_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_rules_1337_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_tz_1354_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object* v_dt_1377_, lean_object* v_days_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_Time_DateTime_withDaysRollOver(v_dt_1377_, v_days_1378_);
lean_dec(v_days_1378_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object* v_dt_1380_, lean_object* v_month_1381_){
_start:
{
lean_object* v_date_1382_; lean_object* v_rules_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1448_; 
v_date_1382_ = lean_ctor_get(v_dt_1380_, 0);
v_rules_1383_ = lean_ctor_get(v_dt_1380_, 2);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_dt_1380_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; lean_object* v_unused_1450_; 
v_unused_1449_ = lean_ctor_get(v_dt_1380_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_dt_1380_, 1);
lean_dec(v_unused_1450_);
v___x_1385_ = v_dt_1380_;
v_isShared_1386_ = v_isSharedCheck_1448_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_rules_1383_);
lean_inc(v_date_1382_);
lean_dec(v_dt_1380_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1448_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v_date_1387_; lean_object* v___y_1389_; lean_object* v_date_1419_; lean_object* v_year_1420_; lean_object* v_day_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1446_; 
v_date_1387_ = lean_thunk_get_own(v_date_1382_);
lean_dec_ref(v_date_1382_);
v_date_1419_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1419_);
v_year_1420_ = lean_ctor_get(v_date_1419_, 0);
v_day_1421_ = lean_ctor_get(v_date_1419_, 2);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_date_1419_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; 
v_unused_1447_ = lean_ctor_get(v_date_1419_, 1);
lean_dec(v_unused_1447_);
v___x_1423_ = v_date_1419_;
v_isShared_1424_ = v_isSharedCheck_1446_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_day_1421_);
lean_inc(v_year_1420_);
lean_dec(v_date_1419_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1446_;
goto v_resetjp_1422_;
}
v___jp_1388_:
{
lean_object* v_time_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1417_; 
v_time_1390_ = lean_ctor_get(v_date_1387_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_date_1387_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_date_1387_, 0);
lean_dec(v_unused_1418_);
v___x_1392_ = v_date_1387_;
v_isShared_1393_ = v_isSharedCheck_1417_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_time_1390_);
lean_dec(v_date_1387_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1417_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1395_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___y_1389_);
v___x_1395_ = v___x_1392_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___y_1389_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_time_1390_);
v___x_1395_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v_wt_1396_; lean_object* v_ltt_1397_; lean_object* v_tz_1398_; lean_object* v_offset_1399_; lean_object* v_second_1400_; lean_object* v_nano_1401_; lean_object* v___f_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_inc_ref(v___x_1395_);
v_wt_1396_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1395_);
lean_inc_ref(v_rules_1383_);
v_ltt_1397_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1383_, v_wt_1396_);
v_tz_1398_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1397_);
lean_dec_ref(v_ltt_1397_);
v_offset_1399_ = lean_ctor_get(v_tz_1398_, 0);
lean_inc(v_offset_1399_);
v_second_1400_ = lean_ctor_get(v_wt_1396_, 0);
lean_inc(v_second_1400_);
v_nano_1401_ = lean_ctor_get(v_wt_1396_, 1);
lean_inc(v_nano_1401_);
lean_dec_ref(v_wt_1396_);
v___f_1402_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1402_, 0, v___x_1395_);
v___x_1403_ = lean_mk_thunk(v___f_1402_);
v___x_1404_ = lean_int_neg(v_offset_1399_);
lean_dec(v_offset_1399_);
v___x_1405_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1406_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1407_ = lean_int_mul(v_second_1400_, v___x_1406_);
lean_dec(v_second_1400_);
v___x_1408_ = lean_int_add(v___x_1407_, v_nano_1401_);
lean_dec(v_nano_1401_);
lean_dec(v___x_1407_);
v___x_1409_ = lean_int_mul(v___x_1404_, v___x_1406_);
lean_dec(v___x_1404_);
v___x_1410_ = lean_int_add(v___x_1409_, v___x_1405_);
lean_dec(v___x_1409_);
v___x_1411_ = lean_int_add(v___x_1408_, v___x_1410_);
lean_dec(v___x_1410_);
lean_dec(v___x_1408_);
v___x_1412_ = l_Std_Time_Duration_ofNanoseconds(v___x_1411_);
lean_dec(v___x_1411_);
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 3, v_tz_1398_);
lean_ctor_set(v___x_1385_, 1, v___x_1412_);
lean_ctor_set(v___x_1385_, 0, v___x_1403_);
v___x_1414_ = v___x_1385_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_rules_1383_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_tz_1398_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
v_resetjp_1422_:
{
uint8_t v___y_1426_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1442_; 
v___x_1435_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1436_ = lean_int_mod(v_year_1420_, v___x_1435_);
v___x_1437_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1442_ = lean_int_dec_eq(v___x_1436_, v___x_1437_);
lean_dec(v___x_1436_);
if (v___x_1442_ == 0)
{
v___y_1426_ = v___x_1442_;
goto v___jp_1425_;
}
else
{
lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1443_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1444_ = lean_int_mod(v_year_1420_, v___x_1443_);
v___x_1445_ = lean_int_dec_eq(v___x_1444_, v___x_1437_);
lean_dec(v___x_1444_);
if (v___x_1445_ == 0)
{
if (v___x_1442_ == 0)
{
goto v___jp_1438_;
}
else
{
v___y_1426_ = v___x_1442_;
goto v___jp_1425_;
}
}
else
{
goto v___jp_1438_;
}
}
v___jp_1425_:
{
lean_object* v_max_1427_; uint8_t v___x_1428_; 
v_max_1427_ = l_Std_Time_Month_Ordinal_days(v___y_1426_, v_month_1381_);
v___x_1428_ = lean_int_dec_lt(v_max_1427_, v_day_1421_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1430_; 
lean_dec(v_max_1427_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v_month_1381_);
v___x_1430_ = v___x_1423_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_year_1420_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_month_1381_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_day_1421_);
v___x_1430_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
v___y_1389_ = v___x_1430_;
goto v___jp_1388_;
}
}
else
{
lean_object* v___x_1433_; 
lean_dec(v_day_1421_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 2, v_max_1427_);
lean_ctor_set(v___x_1423_, 1, v_month_1381_);
v___x_1433_ = v___x_1423_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_year_1420_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_month_1381_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_max_1427_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
v___y_1389_ = v___x_1433_;
goto v___jp_1388_;
}
}
}
v___jp_1438_:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1440_ = lean_int_mod(v_year_1420_, v___x_1439_);
v___x_1441_ = lean_int_dec_eq(v___x_1440_, v___x_1437_);
lean_dec(v___x_1440_);
v___y_1426_ = v___x_1441_;
goto v___jp_1425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object* v_dt_1451_, lean_object* v_month_1452_){
_start:
{
lean_object* v_date_1453_; lean_object* v_rules_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1491_; 
v_date_1453_ = lean_ctor_get(v_dt_1451_, 0);
v_rules_1454_ = lean_ctor_get(v_dt_1451_, 2);
v_isSharedCheck_1491_ = !lean_is_exclusive(v_dt_1451_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; lean_object* v_unused_1493_; 
v_unused_1492_ = lean_ctor_get(v_dt_1451_, 3);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_dt_1451_, 1);
lean_dec(v_unused_1493_);
v___x_1456_ = v_dt_1451_;
v_isShared_1457_ = v_isSharedCheck_1491_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_rules_1454_);
lean_inc(v_date_1453_);
lean_dec(v_dt_1451_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1491_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v_date_1458_; lean_object* v_date_1459_; lean_object* v_time_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1490_; 
v_date_1458_ = lean_thunk_get_own(v_date_1453_);
lean_dec_ref(v_date_1453_);
v_date_1459_ = lean_ctor_get(v_date_1458_, 0);
v_time_1460_ = lean_ctor_get(v_date_1458_, 1);
v_isSharedCheck_1490_ = !lean_is_exclusive(v_date_1458_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1462_ = v_date_1458_;
v_isShared_1463_ = v_isSharedCheck_1490_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_time_1460_);
lean_inc(v_date_1459_);
lean_dec(v_date_1458_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1490_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v_year_1464_; lean_object* v_day_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v_year_1464_ = lean_ctor_get(v_date_1459_, 0);
lean_inc(v_year_1464_);
v_day_1465_ = lean_ctor_get(v_date_1459_, 2);
lean_inc(v_day_1465_);
lean_dec_ref(v_date_1459_);
v___x_1466_ = l_Std_Time_PlainDate_rollOver(v_year_1464_, v_month_1452_, v_day_1465_);
lean_dec(v_day_1465_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1466_);
v___x_1468_ = v___x_1462_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_time_1460_);
v___x_1468_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v_wt_1469_; lean_object* v_ltt_1470_; lean_object* v_tz_1471_; lean_object* v_offset_1472_; lean_object* v_second_1473_; lean_object* v_nano_1474_; lean_object* v___f_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
lean_inc_ref(v___x_1468_);
v_wt_1469_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1468_);
lean_inc_ref(v_rules_1454_);
v_ltt_1470_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1454_, v_wt_1469_);
v_tz_1471_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1470_);
lean_dec_ref(v_ltt_1470_);
v_offset_1472_ = lean_ctor_get(v_tz_1471_, 0);
lean_inc(v_offset_1472_);
v_second_1473_ = lean_ctor_get(v_wt_1469_, 0);
lean_inc(v_second_1473_);
v_nano_1474_ = lean_ctor_get(v_wt_1469_, 1);
lean_inc(v_nano_1474_);
lean_dec_ref(v_wt_1469_);
v___f_1475_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1475_, 0, v___x_1468_);
v___x_1476_ = lean_mk_thunk(v___f_1475_);
v___x_1477_ = lean_int_neg(v_offset_1472_);
lean_dec(v_offset_1472_);
v___x_1478_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1479_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1480_ = lean_int_mul(v_second_1473_, v___x_1479_);
lean_dec(v_second_1473_);
v___x_1481_ = lean_int_add(v___x_1480_, v_nano_1474_);
lean_dec(v_nano_1474_);
lean_dec(v___x_1480_);
v___x_1482_ = lean_int_mul(v___x_1477_, v___x_1479_);
lean_dec(v___x_1477_);
v___x_1483_ = lean_int_add(v___x_1482_, v___x_1478_);
lean_dec(v___x_1482_);
v___x_1484_ = lean_int_add(v___x_1481_, v___x_1483_);
lean_dec(v___x_1483_);
lean_dec(v___x_1481_);
v___x_1485_ = l_Std_Time_Duration_ofNanoseconds(v___x_1484_);
lean_dec(v___x_1484_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 3, v_tz_1471_);
lean_ctor_set(v___x_1456_, 1, v___x_1485_);
lean_ctor_set(v___x_1456_, 0, v___x_1476_);
v___x_1487_ = v___x_1456_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1488_, 2, v_rules_1454_);
lean_ctor_set(v_reuseFailAlloc_1488_, 3, v_tz_1471_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object* v_dt_1494_, lean_object* v_year_1495_){
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
lean_object* v_date_1501_; lean_object* v___y_1503_; lean_object* v_date_1533_; lean_object* v_month_1534_; lean_object* v_day_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1560_; 
v_date_1501_ = lean_thunk_get_own(v_date_1496_);
lean_dec_ref(v_date_1496_);
v_date_1533_ = lean_ctor_get(v_date_1501_, 0);
lean_inc_ref(v_date_1533_);
v_month_1534_ = lean_ctor_get(v_date_1533_, 1);
v_day_1535_ = lean_ctor_get(v_date_1533_, 2);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_date_1533_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v_date_1533_, 0);
lean_dec(v_unused_1561_);
v___x_1537_ = v_date_1533_;
v_isShared_1538_ = v_isSharedCheck_1560_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_day_1535_);
lean_inc(v_month_1534_);
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
v___f_1516_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1516_, 0, v___x_1509_);
v___x_1517_ = lean_mk_thunk(v___f_1516_);
v___x_1518_ = lean_int_neg(v_offset_1513_);
lean_dec(v_offset_1513_);
v___x_1519_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1520_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
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
v___x_1549_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1550_ = lean_int_mod(v_year_1495_, v___x_1549_);
v___x_1551_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
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
v___x_1557_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1558_ = lean_int_mod(v_year_1495_, v___x_1557_);
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
v_max_1541_ = l_Std_Time_Month_Ordinal_days(v___y_1540_, v_month_1534_);
v___x_1542_ = lean_int_dec_lt(v_max_1541_, v_day_1535_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1544_; 
lean_dec(v_max_1541_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v_year_1495_);
v___x_1544_ = v___x_1537_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_year_1495_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_month_1534_);
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
lean_ctor_set(v___x_1537_, 0, v_year_1495_);
v___x_1547_ = v___x_1537_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_year_1495_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_month_1534_);
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
v___x_1553_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1554_ = lean_int_mod(v_year_1495_, v___x_1553_);
v___x_1555_ = lean_int_dec_eq(v___x_1554_, v___x_1551_);
lean_dec(v___x_1554_);
v___y_1540_ = v___x_1555_;
goto v___jp_1539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object* v_dt_1565_, lean_object* v_year_1566_){
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
lean_object* v_month_1578_; lean_object* v_day_1579_; lean_object* v___x_1580_; lean_object* v___x_1582_; 
v_month_1578_ = lean_ctor_get(v_date_1573_, 1);
lean_inc(v_month_1578_);
v_day_1579_ = lean_ctor_get(v_date_1573_, 2);
lean_inc(v_day_1579_);
lean_dec_ref(v_date_1573_);
v___x_1580_ = l_Std_Time_PlainDate_rollOver(v_year_1566_, v_month_1578_, v_day_1579_);
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
v___f_1589_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1589_, 0, v___x_1582_);
v___x_1590_ = lean_mk_thunk(v___f_1589_);
v___x_1591_ = lean_int_neg(v_offset_1586_);
lean_dec(v_offset_1586_);
v___x_1592_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1593_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object* v_dt_1608_, lean_object* v_hour_1609_){
_start:
{
lean_object* v_date_1610_; lean_object* v_rules_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1656_; 
v_date_1610_ = lean_ctor_get(v_dt_1608_, 0);
v_rules_1611_ = lean_ctor_get(v_dt_1608_, 2);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_dt_1608_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; lean_object* v_unused_1658_; 
v_unused_1657_ = lean_ctor_get(v_dt_1608_, 3);
lean_dec(v_unused_1657_);
v_unused_1658_ = lean_ctor_get(v_dt_1608_, 1);
lean_dec(v_unused_1658_);
v___x_1613_ = v_dt_1608_;
v_isShared_1614_ = v_isSharedCheck_1656_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_rules_1611_);
lean_inc(v_date_1610_);
lean_dec(v_dt_1608_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1656_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_date_1615_; lean_object* v_time_1616_; lean_object* v_date_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1655_; 
v_date_1615_ = lean_thunk_get_own(v_date_1610_);
lean_dec_ref(v_date_1610_);
v_time_1616_ = lean_ctor_get(v_date_1615_, 1);
v_date_1617_ = lean_ctor_get(v_date_1615_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v_date_1615_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1619_ = v_date_1615_;
v_isShared_1620_ = v_isSharedCheck_1655_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_time_1616_);
lean_inc(v_date_1617_);
lean_dec(v_date_1615_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1655_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_minute_1621_; lean_object* v_second_1622_; lean_object* v_nanosecond_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1653_; 
v_minute_1621_ = lean_ctor_get(v_time_1616_, 1);
v_second_1622_ = lean_ctor_get(v_time_1616_, 2);
v_nanosecond_1623_ = lean_ctor_get(v_time_1616_, 3);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_time_1616_);
if (v_isSharedCheck_1653_ == 0)
{
lean_object* v_unused_1654_; 
v_unused_1654_ = lean_ctor_get(v_time_1616_, 0);
lean_dec(v_unused_1654_);
v___x_1625_ = v_time_1616_;
v_isShared_1626_ = v_isSharedCheck_1653_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_nanosecond_1623_);
lean_inc(v_second_1622_);
lean_inc(v_minute_1621_);
lean_dec(v_time_1616_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1653_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_hour_1609_);
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_hour_1609_);
lean_ctor_set(v_reuseFailAlloc_1652_, 1, v_minute_1621_);
lean_ctor_set(v_reuseFailAlloc_1652_, 2, v_second_1622_);
lean_ctor_set(v_reuseFailAlloc_1652_, 3, v_nanosecond_1623_);
v___x_1628_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1630_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 1, v___x_1628_);
v___x_1630_ = v___x_1619_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_date_1617_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
lean_object* v_wt_1631_; lean_object* v_ltt_1632_; lean_object* v_tz_1633_; lean_object* v_offset_1634_; lean_object* v_second_1635_; lean_object* v_nano_1636_; lean_object* v___f_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1649_; 
lean_inc_ref(v___x_1630_);
v_wt_1631_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1630_);
lean_inc_ref(v_rules_1611_);
v_ltt_1632_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1611_, v_wt_1631_);
v_tz_1633_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1632_);
lean_dec_ref(v_ltt_1632_);
v_offset_1634_ = lean_ctor_get(v_tz_1633_, 0);
lean_inc(v_offset_1634_);
v_second_1635_ = lean_ctor_get(v_wt_1631_, 0);
lean_inc(v_second_1635_);
v_nano_1636_ = lean_ctor_get(v_wt_1631_, 1);
lean_inc(v_nano_1636_);
lean_dec_ref(v_wt_1631_);
v___f_1637_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1637_, 0, v___x_1630_);
v___x_1638_ = lean_mk_thunk(v___f_1637_);
v___x_1639_ = lean_int_neg(v_offset_1634_);
lean_dec(v_offset_1634_);
v___x_1640_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1641_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1642_ = lean_int_mul(v_second_1635_, v___x_1641_);
lean_dec(v_second_1635_);
v___x_1643_ = lean_int_add(v___x_1642_, v_nano_1636_);
lean_dec(v_nano_1636_);
lean_dec(v___x_1642_);
v___x_1644_ = lean_int_mul(v___x_1639_, v___x_1641_);
lean_dec(v___x_1639_);
v___x_1645_ = lean_int_add(v___x_1644_, v___x_1640_);
lean_dec(v___x_1644_);
v___x_1646_ = lean_int_add(v___x_1643_, v___x_1645_);
lean_dec(v___x_1645_);
lean_dec(v___x_1643_);
v___x_1647_ = l_Std_Time_Duration_ofNanoseconds(v___x_1646_);
lean_dec(v___x_1646_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 3, v_tz_1633_);
lean_ctor_set(v___x_1613_, 1, v___x_1647_);
lean_ctor_set(v___x_1613_, 0, v___x_1638_);
v___x_1649_ = v___x_1613_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_rules_1611_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_tz_1633_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object* v_dt_1659_, lean_object* v_minute_1660_){
_start:
{
lean_object* v_date_1661_; lean_object* v_rules_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1707_; 
v_date_1661_ = lean_ctor_get(v_dt_1659_, 0);
v_rules_1662_ = lean_ctor_get(v_dt_1659_, 2);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_dt_1659_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; lean_object* v_unused_1709_; 
v_unused_1708_ = lean_ctor_get(v_dt_1659_, 3);
lean_dec(v_unused_1708_);
v_unused_1709_ = lean_ctor_get(v_dt_1659_, 1);
lean_dec(v_unused_1709_);
v___x_1664_ = v_dt_1659_;
v_isShared_1665_ = v_isSharedCheck_1707_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_rules_1662_);
lean_inc(v_date_1661_);
lean_dec(v_dt_1659_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1707_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_date_1666_; lean_object* v_time_1667_; lean_object* v_date_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1706_; 
v_date_1666_ = lean_thunk_get_own(v_date_1661_);
lean_dec_ref(v_date_1661_);
v_time_1667_ = lean_ctor_get(v_date_1666_, 1);
v_date_1668_ = lean_ctor_get(v_date_1666_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_date_1666_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1670_ = v_date_1666_;
v_isShared_1671_ = v_isSharedCheck_1706_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_time_1667_);
lean_inc(v_date_1668_);
lean_dec(v_date_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1706_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_hour_1672_; lean_object* v_second_1673_; lean_object* v_nanosecond_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1704_; 
v_hour_1672_ = lean_ctor_get(v_time_1667_, 0);
v_second_1673_ = lean_ctor_get(v_time_1667_, 2);
v_nanosecond_1674_ = lean_ctor_get(v_time_1667_, 3);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_time_1667_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v_time_1667_, 1);
lean_dec(v_unused_1705_);
v___x_1676_ = v_time_1667_;
v_isShared_1677_ = v_isSharedCheck_1704_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_nanosecond_1674_);
lean_inc(v_second_1673_);
lean_inc(v_hour_1672_);
lean_dec(v_time_1667_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1704_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v_minute_1660_);
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_hour_1672_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_minute_1660_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_second_1673_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_nanosecond_1674_);
v___x_1679_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1681_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 1, v___x_1679_);
v___x_1681_ = v___x_1670_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_date_1668_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v_wt_1682_; lean_object* v_ltt_1683_; lean_object* v_tz_1684_; lean_object* v_offset_1685_; lean_object* v_second_1686_; lean_object* v_nano_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_inc_ref(v___x_1681_);
v_wt_1682_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1681_);
lean_inc_ref(v_rules_1662_);
v_ltt_1683_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1662_, v_wt_1682_);
v_tz_1684_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1683_);
lean_dec_ref(v_ltt_1683_);
v_offset_1685_ = lean_ctor_get(v_tz_1684_, 0);
lean_inc(v_offset_1685_);
v_second_1686_ = lean_ctor_get(v_wt_1682_, 0);
lean_inc(v_second_1686_);
v_nano_1687_ = lean_ctor_get(v_wt_1682_, 1);
lean_inc(v_nano_1687_);
lean_dec_ref(v_wt_1682_);
v___f_1688_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1688_, 0, v___x_1681_);
v___x_1689_ = lean_mk_thunk(v___f_1688_);
v___x_1690_ = lean_int_neg(v_offset_1685_);
lean_dec(v_offset_1685_);
v___x_1691_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1692_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1693_ = lean_int_mul(v_second_1686_, v___x_1692_);
lean_dec(v_second_1686_);
v___x_1694_ = lean_int_add(v___x_1693_, v_nano_1687_);
lean_dec(v_nano_1687_);
lean_dec(v___x_1693_);
v___x_1695_ = lean_int_mul(v___x_1690_, v___x_1692_);
lean_dec(v___x_1690_);
v___x_1696_ = lean_int_add(v___x_1695_, v___x_1691_);
lean_dec(v___x_1695_);
v___x_1697_ = lean_int_add(v___x_1694_, v___x_1696_);
lean_dec(v___x_1696_);
lean_dec(v___x_1694_);
v___x_1698_ = l_Std_Time_Duration_ofNanoseconds(v___x_1697_);
lean_dec(v___x_1697_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 3, v_tz_1684_);
lean_ctor_set(v___x_1664_, 1, v___x_1698_);
lean_ctor_set(v___x_1664_, 0, v___x_1689_);
v___x_1700_ = v___x_1664_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_rules_1662_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_tz_1684_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object* v_dt_1710_, lean_object* v_second_1711_){
_start:
{
lean_object* v_date_1712_; lean_object* v_rules_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1758_; 
v_date_1712_ = lean_ctor_get(v_dt_1710_, 0);
v_rules_1713_ = lean_ctor_get(v_dt_1710_, 2);
v_isSharedCheck_1758_ = !lean_is_exclusive(v_dt_1710_);
if (v_isSharedCheck_1758_ == 0)
{
lean_object* v_unused_1759_; lean_object* v_unused_1760_; 
v_unused_1759_ = lean_ctor_get(v_dt_1710_, 3);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_dt_1710_, 1);
lean_dec(v_unused_1760_);
v___x_1715_ = v_dt_1710_;
v_isShared_1716_ = v_isSharedCheck_1758_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_rules_1713_);
lean_inc(v_date_1712_);
lean_dec(v_dt_1710_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1758_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v_date_1717_; lean_object* v_time_1718_; lean_object* v_date_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1757_; 
v_date_1717_ = lean_thunk_get_own(v_date_1712_);
lean_dec_ref(v_date_1712_);
v_time_1718_ = lean_ctor_get(v_date_1717_, 1);
v_date_1719_ = lean_ctor_get(v_date_1717_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_date_1717_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1721_ = v_date_1717_;
v_isShared_1722_ = v_isSharedCheck_1757_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_time_1718_);
lean_inc(v_date_1719_);
lean_dec(v_date_1717_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1757_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_hour_1723_; lean_object* v_minute_1724_; lean_object* v_nanosecond_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1755_; 
v_hour_1723_ = lean_ctor_get(v_time_1718_, 0);
v_minute_1724_ = lean_ctor_get(v_time_1718_, 1);
v_nanosecond_1725_ = lean_ctor_get(v_time_1718_, 3);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_time_1718_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_time_1718_, 2);
lean_dec(v_unused_1756_);
v___x_1727_ = v_time_1718_;
v_isShared_1728_ = v_isSharedCheck_1755_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_nanosecond_1725_);
lean_inc(v_minute_1724_);
lean_inc(v_hour_1723_);
lean_dec(v_time_1718_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1755_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 2, v_second_1711_);
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_hour_1723_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_minute_1724_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_second_1711_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v_nanosecond_1725_);
v___x_1730_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1732_; 
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 1, v___x_1730_);
v___x_1732_ = v___x_1721_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_date_1719_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v___x_1730_);
v___x_1732_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v_wt_1733_; lean_object* v_ltt_1734_; lean_object* v_tz_1735_; lean_object* v_offset_1736_; lean_object* v_second_1737_; lean_object* v_nano_1738_; lean_object* v___f_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1751_; 
lean_inc_ref(v___x_1732_);
v_wt_1733_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1732_);
lean_inc_ref(v_rules_1713_);
v_ltt_1734_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1713_, v_wt_1733_);
v_tz_1735_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1734_);
lean_dec_ref(v_ltt_1734_);
v_offset_1736_ = lean_ctor_get(v_tz_1735_, 0);
lean_inc(v_offset_1736_);
v_second_1737_ = lean_ctor_get(v_wt_1733_, 0);
lean_inc(v_second_1737_);
v_nano_1738_ = lean_ctor_get(v_wt_1733_, 1);
lean_inc(v_nano_1738_);
lean_dec_ref(v_wt_1733_);
v___f_1739_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1739_, 0, v___x_1732_);
v___x_1740_ = lean_mk_thunk(v___f_1739_);
v___x_1741_ = lean_int_neg(v_offset_1736_);
lean_dec(v_offset_1736_);
v___x_1742_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1743_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1744_ = lean_int_mul(v_second_1737_, v___x_1743_);
lean_dec(v_second_1737_);
v___x_1745_ = lean_int_add(v___x_1744_, v_nano_1738_);
lean_dec(v_nano_1738_);
lean_dec(v___x_1744_);
v___x_1746_ = lean_int_mul(v___x_1741_, v___x_1743_);
lean_dec(v___x_1741_);
v___x_1747_ = lean_int_add(v___x_1746_, v___x_1742_);
lean_dec(v___x_1746_);
v___x_1748_ = lean_int_add(v___x_1745_, v___x_1747_);
lean_dec(v___x_1747_);
lean_dec(v___x_1745_);
v___x_1749_ = l_Std_Time_Duration_ofNanoseconds(v___x_1748_);
lean_dec(v___x_1748_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 3, v_tz_1735_);
lean_ctor_set(v___x_1715_, 1, v___x_1749_);
lean_ctor_set(v___x_1715_, 0, v___x_1740_);
v___x_1751_ = v___x_1715_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_rules_1713_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_tz_1735_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
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
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_unsigned_to_nat(1000u);
v___x_1762_ = lean_nat_to_int(v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object* v_dt_1763_, lean_object* v_millis_1764_){
_start:
{
lean_object* v_date_1765_; lean_object* v_rules_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1816_; 
v_date_1765_ = lean_ctor_get(v_dt_1763_, 0);
v_rules_1766_ = lean_ctor_get(v_dt_1763_, 2);
v_isSharedCheck_1816_ = !lean_is_exclusive(v_dt_1763_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; lean_object* v_unused_1818_; 
v_unused_1817_ = lean_ctor_get(v_dt_1763_, 3);
lean_dec(v_unused_1817_);
v_unused_1818_ = lean_ctor_get(v_dt_1763_, 1);
lean_dec(v_unused_1818_);
v___x_1768_ = v_dt_1763_;
v_isShared_1769_ = v_isSharedCheck_1816_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_rules_1766_);
lean_inc(v_date_1765_);
lean_dec(v_dt_1763_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1816_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_date_1770_; lean_object* v_time_1771_; lean_object* v_date_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1815_; 
v_date_1770_ = lean_thunk_get_own(v_date_1765_);
lean_dec_ref(v_date_1765_);
v_time_1771_ = lean_ctor_get(v_date_1770_, 1);
v_date_1772_ = lean_ctor_get(v_date_1770_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v_date_1770_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1774_ = v_date_1770_;
v_isShared_1775_ = v_isSharedCheck_1815_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_time_1771_);
lean_inc(v_date_1772_);
lean_dec(v_date_1770_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1815_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_hour_1776_; lean_object* v_minute_1777_; lean_object* v_second_1778_; lean_object* v_nanosecond_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1814_; 
v_hour_1776_ = lean_ctor_get(v_time_1771_, 0);
v_minute_1777_ = lean_ctor_get(v_time_1771_, 1);
v_second_1778_ = lean_ctor_get(v_time_1771_, 2);
v_nanosecond_1779_ = lean_ctor_get(v_time_1771_, 3);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_time_1771_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1781_ = v_time_1771_;
v_isShared_1782_ = v_isSharedCheck_1814_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_nanosecond_1779_);
lean_inc(v_second_1778_);
lean_inc(v_minute_1777_);
lean_inc(v_hour_1776_);
lean_dec(v_time_1771_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1814_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1789_; 
v___x_1783_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_1784_ = lean_int_emod(v_nanosecond_1779_, v___x_1783_);
lean_dec(v_nanosecond_1779_);
v___x_1785_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1786_ = lean_int_mul(v_millis_1764_, v___x_1785_);
v___x_1787_ = lean_int_add(v___x_1786_, v___x_1784_);
lean_dec(v___x_1784_);
lean_dec(v___x_1786_);
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 3, v___x_1787_);
v___x_1789_ = v___x_1781_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_hour_1776_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_minute_1777_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_second_1778_);
lean_ctor_set(v_reuseFailAlloc_1813_, 3, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1791_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v___x_1789_);
v___x_1791_ = v___x_1774_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_date_1772_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
lean_object* v_wt_1792_; lean_object* v_ltt_1793_; lean_object* v_tz_1794_; lean_object* v_offset_1795_; lean_object* v_second_1796_; lean_object* v_nano_1797_; lean_object* v___f_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1810_; 
lean_inc_ref(v___x_1791_);
v_wt_1792_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1791_);
lean_inc_ref(v_rules_1766_);
v_ltt_1793_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1766_, v_wt_1792_);
v_tz_1794_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1793_);
lean_dec_ref(v_ltt_1793_);
v_offset_1795_ = lean_ctor_get(v_tz_1794_, 0);
lean_inc(v_offset_1795_);
v_second_1796_ = lean_ctor_get(v_wt_1792_, 0);
lean_inc(v_second_1796_);
v_nano_1797_ = lean_ctor_get(v_wt_1792_, 1);
lean_inc(v_nano_1797_);
lean_dec_ref(v_wt_1792_);
v___f_1798_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1798_, 0, v___x_1791_);
v___x_1799_ = lean_mk_thunk(v___f_1798_);
v___x_1800_ = lean_int_neg(v_offset_1795_);
lean_dec(v_offset_1795_);
v___x_1801_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1802_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1803_ = lean_int_mul(v_second_1796_, v___x_1802_);
lean_dec(v_second_1796_);
v___x_1804_ = lean_int_add(v___x_1803_, v_nano_1797_);
lean_dec(v_nano_1797_);
lean_dec(v___x_1803_);
v___x_1805_ = lean_int_mul(v___x_1800_, v___x_1802_);
lean_dec(v___x_1800_);
v___x_1806_ = lean_int_add(v___x_1805_, v___x_1801_);
lean_dec(v___x_1805_);
v___x_1807_ = lean_int_add(v___x_1804_, v___x_1806_);
lean_dec(v___x_1806_);
lean_dec(v___x_1804_);
v___x_1808_ = l_Std_Time_Duration_ofNanoseconds(v___x_1807_);
lean_dec(v___x_1807_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 3, v_tz_1794_);
lean_ctor_set(v___x_1768_, 1, v___x_1808_);
lean_ctor_set(v___x_1768_, 0, v___x_1799_);
v___x_1810_ = v___x_1768_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_rules_1766_);
lean_ctor_set(v_reuseFailAlloc_1811_, 3, v_tz_1794_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object* v_dt_1819_, lean_object* v_millis_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Std_Time_DateTime_withMilliseconds(v_dt_1819_, v_millis_1820_);
lean_dec(v_millis_1820_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object* v_dt_1822_, lean_object* v_nano_1823_){
_start:
{
lean_object* v_date_1824_; lean_object* v_rules_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1870_; 
v_date_1824_ = lean_ctor_get(v_dt_1822_, 0);
v_rules_1825_ = lean_ctor_get(v_dt_1822_, 2);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_dt_1822_);
if (v_isSharedCheck_1870_ == 0)
{
lean_object* v_unused_1871_; lean_object* v_unused_1872_; 
v_unused_1871_ = lean_ctor_get(v_dt_1822_, 3);
lean_dec(v_unused_1871_);
v_unused_1872_ = lean_ctor_get(v_dt_1822_, 1);
lean_dec(v_unused_1872_);
v___x_1827_ = v_dt_1822_;
v_isShared_1828_ = v_isSharedCheck_1870_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_rules_1825_);
lean_inc(v_date_1824_);
lean_dec(v_dt_1822_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1870_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_date_1829_; lean_object* v_time_1830_; lean_object* v_date_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1869_; 
v_date_1829_ = lean_thunk_get_own(v_date_1824_);
lean_dec_ref(v_date_1824_);
v_time_1830_ = lean_ctor_get(v_date_1829_, 1);
v_date_1831_ = lean_ctor_get(v_date_1829_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v_date_1829_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1833_ = v_date_1829_;
v_isShared_1834_ = v_isSharedCheck_1869_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_time_1830_);
lean_inc(v_date_1831_);
lean_dec(v_date_1829_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1869_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_hour_1835_; lean_object* v_minute_1836_; lean_object* v_second_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1867_; 
v_hour_1835_ = lean_ctor_get(v_time_1830_, 0);
v_minute_1836_ = lean_ctor_get(v_time_1830_, 1);
v_second_1837_ = lean_ctor_get(v_time_1830_, 2);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_time_1830_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; 
v_unused_1868_ = lean_ctor_get(v_time_1830_, 3);
lean_dec(v_unused_1868_);
v___x_1839_ = v_time_1830_;
v_isShared_1840_ = v_isSharedCheck_1867_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_second_1837_);
lean_inc(v_minute_1836_);
lean_inc(v_hour_1835_);
lean_dec(v_time_1830_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1867_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 3, v_nano_1823_);
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_hour_1835_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_minute_1836_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_second_1837_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_nano_1823_);
v___x_1842_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1842_);
v___x_1844_ = v___x_1833_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_date_1831_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v_wt_1845_; lean_object* v_ltt_1846_; lean_object* v_tz_1847_; lean_object* v_offset_1848_; lean_object* v_second_1849_; lean_object* v_nano_1850_; lean_object* v___f_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_inc_ref(v___x_1844_);
v_wt_1845_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1844_);
lean_inc_ref(v_rules_1825_);
v_ltt_1846_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1825_, v_wt_1845_);
v_tz_1847_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1846_);
lean_dec_ref(v_ltt_1846_);
v_offset_1848_ = lean_ctor_get(v_tz_1847_, 0);
lean_inc(v_offset_1848_);
v_second_1849_ = lean_ctor_get(v_wt_1845_, 0);
lean_inc(v_second_1849_);
v_nano_1850_ = lean_ctor_get(v_wt_1845_, 1);
lean_inc(v_nano_1850_);
lean_dec_ref(v_wt_1845_);
v___f_1851_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1851_, 0, v___x_1844_);
v___x_1852_ = lean_mk_thunk(v___f_1851_);
v___x_1853_ = lean_int_neg(v_offset_1848_);
lean_dec(v_offset_1848_);
v___x_1854_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1855_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1856_ = lean_int_mul(v_second_1849_, v___x_1855_);
lean_dec(v_second_1849_);
v___x_1857_ = lean_int_add(v___x_1856_, v_nano_1850_);
lean_dec(v_nano_1850_);
lean_dec(v___x_1856_);
v___x_1858_ = lean_int_mul(v___x_1853_, v___x_1855_);
lean_dec(v___x_1853_);
v___x_1859_ = lean_int_add(v___x_1858_, v___x_1854_);
lean_dec(v___x_1858_);
v___x_1860_ = lean_int_add(v___x_1857_, v___x_1859_);
lean_dec(v___x_1859_);
lean_dec(v___x_1857_);
v___x_1861_ = l_Std_Time_Duration_ofNanoseconds(v___x_1860_);
lean_dec(v___x_1860_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 3, v_tz_1847_);
lean_ctor_set(v___x_1827_, 1, v___x_1861_);
lean_ctor_set(v___x_1827_, 0, v___x_1852_);
v___x_1863_ = v___x_1827_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_rules_1825_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_tz_1847_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object* v_date_1873_){
_start:
{
lean_object* v_date_1874_; lean_object* v___x_1875_; lean_object* v_date_1876_; lean_object* v_year_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1885_; 
v_date_1874_ = lean_ctor_get(v_date_1873_, 0);
v___x_1875_ = lean_thunk_get_own(v_date_1874_);
v_date_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc_ref(v_date_1876_);
lean_dec(v___x_1875_);
v_year_1877_ = lean_ctor_get(v_date_1876_, 0);
lean_inc(v_year_1877_);
lean_dec_ref(v_date_1876_);
v___x_1878_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1879_ = lean_int_mod(v_year_1877_, v___x_1878_);
v___x_1880_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1885_ = lean_int_dec_eq(v___x_1879_, v___x_1880_);
lean_dec(v___x_1879_);
if (v___x_1885_ == 0)
{
lean_dec(v_year_1877_);
return v___x_1885_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1886_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1887_ = lean_int_mod(v_year_1877_, v___x_1886_);
v___x_1888_ = lean_int_dec_eq(v___x_1887_, v___x_1880_);
lean_dec(v___x_1887_);
if (v___x_1888_ == 0)
{
if (v___x_1885_ == 0)
{
goto v___jp_1881_;
}
else
{
lean_dec(v_year_1877_);
return v___x_1885_;
}
}
else
{
goto v___jp_1881_;
}
}
v___jp_1881_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1882_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1883_ = lean_int_mod(v_year_1877_, v___x_1882_);
lean_dec(v_year_1877_);
v___x_1884_ = lean_int_dec_eq(v___x_1883_, v___x_1880_);
lean_dec(v___x_1883_);
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object* v_date_1889_){
_start:
{
uint8_t v_res_1890_; lean_object* v_r_1891_; 
v_res_1890_ = l_Std_Time_DateTime_inLeapYear(v_date_1889_);
lean_dec_ref(v_date_1889_);
v_r_1891_ = lean_box(v_res_1890_);
return v_r_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay(lean_object* v_date_1892_){
_start:
{
lean_object* v_date_1893_; lean_object* v___x_1894_; lean_object* v_date_1895_; lean_object* v___x_1896_; 
v_date_1893_ = lean_ctor_get(v_date_1892_, 0);
v___x_1894_ = lean_thunk_get_own(v_date_1893_);
v_date_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc_ref(v_date_1895_);
lean_dec(v___x_1894_);
v___x_1896_ = l_Std_Time_PlainDate_toEpochDay(v_date_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___boxed(lean_object* v_date_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Std_Time_DateTime_toEpochDay(v_date_1897_);
lean_dec_ref(v_date_1897_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay(lean_object* v_days_1899_, lean_object* v_time_1900_, lean_object* v_zt_1901_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v_wt_1904_; lean_object* v_ltt_1905_; lean_object* v_tz_1906_; lean_object* v_offset_1907_; lean_object* v_second_1908_; lean_object* v_nano_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1902_ = l_Std_Time_PlainDate_ofEpochDay(v_days_1899_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_time_1900_);
lean_inc_ref(v___x_1903_);
v_wt_1904_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1903_);
lean_inc_ref(v_zt_1901_);
v_ltt_1905_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zt_1901_, v_wt_1904_);
v_tz_1906_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1905_);
lean_dec_ref(v_ltt_1905_);
v_offset_1907_ = lean_ctor_get(v_tz_1906_, 0);
lean_inc(v_offset_1907_);
v_second_1908_ = lean_ctor_get(v_wt_1904_, 0);
lean_inc(v_second_1908_);
v_nano_1909_ = lean_ctor_get(v_wt_1904_, 1);
lean_inc(v_nano_1909_);
lean_dec_ref(v_wt_1904_);
v___f_1910_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1910_, 0, v___x_1903_);
v___x_1911_ = lean_mk_thunk(v___f_1910_);
v___x_1912_ = lean_int_neg(v_offset_1907_);
lean_dec(v_offset_1907_);
v___x_1913_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1914_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1915_ = lean_int_mul(v_second_1908_, v___x_1914_);
lean_dec(v_second_1908_);
v___x_1916_ = lean_int_add(v___x_1915_, v_nano_1909_);
lean_dec(v_nano_1909_);
lean_dec(v___x_1915_);
v___x_1917_ = lean_int_mul(v___x_1912_, v___x_1914_);
lean_dec(v___x_1912_);
v___x_1918_ = lean_int_add(v___x_1917_, v___x_1913_);
lean_dec(v___x_1917_);
v___x_1919_ = lean_int_add(v___x_1916_, v___x_1918_);
lean_dec(v___x_1918_);
lean_dec(v___x_1916_);
v___x_1920_ = l_Std_Time_Duration_ofNanoseconds(v___x_1919_);
lean_dec(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1911_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
lean_ctor_set(v___x_1921_, 2, v_zt_1901_);
lean_ctor_set(v___x_1921_, 3, v_tz_1906_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay___boxed(lean_object* v_days_1922_, lean_object* v_time_1923_, lean_object* v_zt_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Std_Time_DateTime_ofEpochDay(v_days_1922_, v_time_1923_, v_zt_1924_);
lean_dec(v_days_1922_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object* v_x_1954_, lean_object* v_y_1955_){
_start:
{
lean_object* v_timestamp_1956_; lean_object* v_timestamp_1957_; lean_object* v_second_1958_; lean_object* v_nano_1959_; lean_object* v_second_1960_; lean_object* v_nano_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_timestamp_1956_ = lean_ctor_get(v_y_1955_, 1);
v_timestamp_1957_ = lean_ctor_get(v_x_1954_, 1);
v_second_1958_ = lean_ctor_get(v_timestamp_1956_, 0);
v_nano_1959_ = lean_ctor_get(v_timestamp_1956_, 1);
v_second_1960_ = lean_ctor_get(v_timestamp_1957_, 0);
v_nano_1961_ = lean_ctor_get(v_timestamp_1957_, 1);
v___x_1962_ = lean_int_neg(v_second_1958_);
v___x_1963_ = lean_int_neg(v_nano_1959_);
v___x_1964_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1965_ = lean_int_mul(v_second_1960_, v___x_1964_);
v___x_1966_ = lean_int_add(v___x_1965_, v_nano_1961_);
lean_dec(v___x_1965_);
v___x_1967_ = lean_int_mul(v___x_1962_, v___x_1964_);
lean_dec(v___x_1962_);
v___x_1968_ = lean_int_add(v___x_1967_, v___x_1963_);
lean_dec(v___x_1963_);
lean_dec(v___x_1967_);
v___x_1969_ = lean_int_add(v___x_1966_, v___x_1968_);
lean_dec(v___x_1968_);
lean_dec(v___x_1966_);
v___x_1970_ = l_Std_Time_Duration_ofNanoseconds(v___x_1969_);
lean_dec(v___x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object* v_x_1971_, lean_object* v_y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Std_Time_DateTime_instHSubDuration___lam__0(v_x_1971_, v_y_1972_);
lean_dec_ref(v_y_1972_);
lean_dec_ref(v_x_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0(lean_object* v_x_1976_, lean_object* v_y_1977_){
_start:
{
lean_object* v_second_1978_; lean_object* v_nano_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v_nanos_1982_; lean_object* v___x_1983_; 
v_second_1978_ = lean_ctor_get(v_y_1977_, 0);
v_nano_1979_ = lean_ctor_get(v_y_1977_, 1);
v___x_1980_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1981_ = lean_int_mul(v_second_1978_, v___x_1980_);
v_nanos_1982_ = lean_int_add(v___x_1981_, v_nano_1979_);
lean_dec(v___x_1981_);
v___x_1983_ = l_Std_Time_DateTime_addNanoseconds(v_x_1976_, v_nanos_1982_);
lean_dec(v_nanos_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_1984_, lean_object* v_y_1985_){
_start:
{
lean_object* v_res_1986_; 
v_res_1986_ = l_Std_Time_DateTime_instHAddDuration___lam__0(v_x_1984_, v_y_1985_);
lean_dec_ref(v_y_1985_);
return v_res_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0(lean_object* v_x_1989_, lean_object* v_y_1990_){
_start:
{
lean_object* v_second_1991_; lean_object* v_nano_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v_nanos_1995_; lean_object* v___x_1996_; 
v_second_1991_ = lean_ctor_get(v_y_1990_, 0);
v_nano_1992_ = lean_ctor_get(v_y_1990_, 1);
v___x_1993_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1994_ = lean_int_mul(v_second_1991_, v___x_1993_);
v_nanos_1995_ = lean_int_add(v___x_1994_, v_nano_1992_);
lean_dec(v___x_1994_);
v___x_1996_ = l_Std_Time_DateTime_subNanoseconds(v_x_1989_, v_nanos_1995_);
lean_dec(v_nanos_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0___boxed(lean_object* v_x_1997_, lean_object* v_y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Std_Time_DateTime_instHSubDuration__1___lam__0(v_x_1997_, v_y_1998_);
lean_dec_ref(v_y_1998_);
return v_res_1999_;
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

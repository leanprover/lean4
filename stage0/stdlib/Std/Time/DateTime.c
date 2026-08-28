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
lean_object* v_date_280_; lean_object* v___x_281_; lean_object* v_date_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_308_; 
v_date_280_ = lean_ctor_get(v_date_279_, 0);
v___x_281_ = lean_thunk_get_own(v_date_280_);
v_date_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_308_ == 0)
{
lean_object* v_unused_309_; 
v_unused_309_ = lean_ctor_get(v___x_281_, 1);
lean_dec(v_unused_309_);
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_308_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_date_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_308_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_year_286_; lean_object* v_month_287_; lean_object* v_day_288_; uint8_t v___y_290_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; uint8_t v___y_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
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
v___x_301_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_302_ = lean_int_mod(v_year_286_, v___x_301_);
v___x_303_ = lean_int_dec_eq(v___x_302_, v___x_297_);
lean_dec(v___x_302_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; 
lean_dec(v_year_286_);
v___x_304_ = 1;
v___y_300_ = v___x_304_;
goto v___jp_299_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_305_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_306_ = lean_int_mod(v_year_286_, v___x_305_);
lean_dec(v_year_286_);
v___x_307_ = lean_int_dec_eq(v___x_306_, v___x_297_);
lean_dec(v___x_306_);
v___y_300_ = v___x_307_;
goto v___jp_299_;
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
v___jp_299_:
{
if (v___x_298_ == 0)
{
v___y_290_ = v___x_298_;
goto v___jp_289_;
}
else
{
v___y_290_ = v___y_300_;
goto v___jp_289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object* v_date_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Std_Time_DateTime_dayOfYear(v_date_310_);
lean_dec_ref(v_date_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* v_dt_312_, uint8_t v_firstDay_313_, lean_object* v_minDays_314_){
_start:
{
lean_object* v_date_315_; lean_object* v___x_316_; lean_object* v_date_317_; lean_object* v___x_318_; 
v_date_315_ = lean_ctor_get(v_dt_312_, 0);
v___x_316_ = lean_thunk_get_own(v_date_315_);
v_date_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc_ref(v_date_317_);
lean_dec(v___x_316_);
v___x_318_ = l_Std_Time_PlainDate_weekOfYear(v_date_317_, v_firstDay_313_, v_minDays_314_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfYear___boxed(lean_object* v_dt_319_, lean_object* v_firstDay_320_, lean_object* v_minDays_321_){
_start:
{
uint8_t v_firstDay_boxed_322_; lean_object* v_res_323_; 
v_firstDay_boxed_322_ = lean_unbox(v_firstDay_320_);
v_res_323_ = l_Std_Time_DateTime_weekOfYear(v_dt_319_, v_firstDay_boxed_322_, v_minDays_321_);
lean_dec(v_minDays_321_);
lean_dec_ref(v_dt_319_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear(lean_object* v_date_324_, uint8_t v_firstDay_325_, lean_object* v_minDays_326_){
_start:
{
lean_object* v_date_327_; lean_object* v___x_328_; lean_object* v_date_329_; lean_object* v___x_330_; 
v_date_327_ = lean_ctor_get(v_date_324_, 0);
v___x_328_ = lean_thunk_get_own(v_date_327_);
v_date_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc_ref(v_date_329_);
lean_dec(v___x_328_);
v___x_330_ = l_Std_Time_PlainDate_weekYear(v_date_329_, v_firstDay_325_, v_minDays_326_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___boxed(lean_object* v_date_331_, lean_object* v_firstDay_332_, lean_object* v_minDays_333_){
_start:
{
uint8_t v_firstDay_boxed_334_; lean_object* v_res_335_; 
v_firstDay_boxed_334_ = lean_unbox(v_firstDay_332_);
v_res_335_ = l_Std_Time_DateTime_weekYear(v_date_331_, v_firstDay_boxed_334_, v_minDays_333_);
lean_dec(v_minDays_333_);
lean_dec_ref(v_date_331_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* v_date_336_){
_start:
{
lean_object* v_date_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_date_337_ = lean_ctor_get(v_date_336_, 0);
v___x_338_ = lean_thunk_get_own(v_date_337_);
v___x_339_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v___x_338_);
lean_dec(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object* v_date_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_340_);
lean_dec_ref(v_date_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* v_date_342_, uint8_t v_firstDay_343_){
_start:
{
lean_object* v_date_344_; lean_object* v___x_345_; lean_object* v_date_346_; lean_object* v___x_347_; 
v_date_344_ = lean_ctor_get(v_date_342_, 0);
v___x_345_ = lean_thunk_get_own(v_date_344_);
v_date_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_date_346_);
lean_dec(v___x_345_);
v___x_347_ = l_Std_Time_PlainDate_weekOfMonth(v_date_346_, v_firstDay_343_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object* v_date_348_, lean_object* v_firstDay_349_){
_start:
{
uint8_t v_firstDay_boxed_350_; lean_object* v_res_351_; 
v_firstDay_boxed_350_ = lean_unbox(v_firstDay_349_);
v_res_351_ = l_Std_Time_DateTime_weekOfMonth(v_date_348_, v_firstDay_boxed_350_);
lean_dec_ref(v_date_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* v_date_352_){
_start:
{
lean_object* v_date_353_; lean_object* v___x_354_; lean_object* v_date_355_; lean_object* v___x_356_; 
v_date_353_ = lean_ctor_get(v_date_352_, 0);
v___x_354_ = lean_thunk_get_own(v_date_353_);
v_date_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc_ref(v_date_355_);
lean_dec(v___x_354_);
v___x_356_ = l_Std_Time_PlainDate_quarter(v_date_355_);
lean_dec_ref(v_date_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object* v_date_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Time_DateTime_quarter(v_date_357_);
lean_dec_ref(v_date_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_DateTime_addDays_spec__1(lean_object* v_a_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Rat_ofInt(v_a_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0(lean_object* v_tz_361_, lean_object* v___x_362_, lean_object* v___x_363_, lean_object* v___x_364_, lean_object* v_x_365_){
_start:
{
lean_object* v_offset_366_; lean_object* v_second_367_; lean_object* v_nano_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_offset_366_ = lean_ctor_get(v_tz_361_, 0);
v_second_367_ = lean_ctor_get(v___x_362_, 0);
v_nano_368_ = lean_ctor_get(v___x_362_, 1);
v___x_369_ = lean_int_mul(v_second_367_, v___x_363_);
v___x_370_ = lean_int_add(v___x_369_, v_nano_368_);
lean_dec(v___x_369_);
v___x_371_ = lean_int_mul(v_offset_366_, v___x_363_);
v___x_372_ = lean_int_add(v___x_371_, v___x_364_);
lean_dec(v___x_371_);
v___x_373_ = lean_int_add(v___x_370_, v___x_372_);
lean_dec(v___x_372_);
lean_dec(v___x_370_);
v___x_374_ = l_Std_Time_Duration_ofNanoseconds(v___x_373_);
lean_dec(v___x_373_);
v___x_375_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0___boxed(lean_object* v_tz_376_, lean_object* v___x_377_, lean_object* v___x_378_, lean_object* v___x_379_, lean_object* v_x_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_Time_DateTime_addDays___lam__0(v_tz_376_, v___x_377_, v___x_378_, v___x_379_, v_x_380_);
lean_dec(v___x_379_);
lean_dec(v___x_378_);
lean_dec_ref(v___x_377_);
lean_dec_ref(v_tz_376_);
return v_res_381_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addDays___closed__0(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(86400u);
v___x_383_ = lean_nat_to_int(v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object* v_dt_384_, lean_object* v_days_385_){
_start:
{
lean_object* v_timestamp_386_; lean_object* v_rules_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_409_; 
v_timestamp_386_ = lean_ctor_get(v_dt_384_, 1);
v_rules_387_ = lean_ctor_get(v_dt_384_, 2);
v_isSharedCheck_409_ = !lean_is_exclusive(v_dt_384_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_410_ = lean_ctor_get(v_dt_384_, 3);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_dt_384_, 0);
lean_dec(v_unused_411_);
v___x_389_ = v_dt_384_;
v_isShared_390_ = v_isSharedCheck_409_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_rules_387_);
lean_inc(v_timestamp_386_);
lean_dec(v_dt_384_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_409_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v_second_391_; lean_object* v_nano_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_tz_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v_second_391_ = lean_ctor_get(v_timestamp_386_, 0);
lean_inc(v_second_391_);
v_nano_392_ = lean_ctor_get(v_timestamp_386_, 1);
lean_inc(v_nano_392_);
lean_dec_ref(v_timestamp_386_);
v___x_393_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_394_ = lean_int_mul(v_days_385_, v___x_393_);
v___x_395_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_396_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_397_ = lean_int_mul(v_second_391_, v___x_396_);
lean_dec(v_second_391_);
v___x_398_ = lean_int_add(v___x_397_, v_nano_392_);
lean_dec(v_nano_392_);
lean_dec(v___x_397_);
v___x_399_ = lean_int_mul(v___x_394_, v___x_396_);
lean_dec(v___x_394_);
v___x_400_ = lean_int_add(v___x_399_, v___x_395_);
lean_dec(v___x_399_);
v___x_401_ = lean_int_add(v___x_398_, v___x_400_);
lean_dec(v___x_400_);
lean_dec(v___x_398_);
v___x_402_ = l_Std_Time_Duration_ofNanoseconds(v___x_401_);
lean_dec(v___x_401_);
lean_inc_ref(v_rules_387_);
v_tz_403_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_387_, v___x_402_);
lean_inc_ref(v___x_402_);
lean_inc_ref(v_tz_403_);
v___f_404_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_404_, 0, v_tz_403_);
lean_closure_set(v___f_404_, 1, v___x_402_);
lean_closure_set(v___f_404_, 2, v___x_396_);
lean_closure_set(v___f_404_, 3, v___x_395_);
v___x_405_ = lean_mk_thunk(v___f_404_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 3, v_tz_403_);
lean_ctor_set(v___x_389_, 1, v___x_402_);
lean_ctor_set(v___x_389_, 0, v___x_405_);
v___x_407_ = v___x_389_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_408_, 2, v_rules_387_);
lean_ctor_set(v_reuseFailAlloc_408_, 3, v_tz_403_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object* v_dt_412_, lean_object* v_days_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Time_DateTime_addDays(v_dt_412_, v_days_413_);
lean_dec(v_days_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_DateTime_addDays_spec__0_spec__0(lean_object* v_a_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_nat_to_int(v_a_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_DateTime_addDays_spec__0(lean_object* v_a_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_nat_to_int(v_a_417_);
v___x_419_ = l_Rat_ofInt(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object* v_dt_420_, lean_object* v_days_421_){
_start:
{
lean_object* v_timestamp_422_; lean_object* v_rules_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_447_; 
v_timestamp_422_ = lean_ctor_get(v_dt_420_, 1);
v_rules_423_ = lean_ctor_get(v_dt_420_, 2);
v_isSharedCheck_447_ = !lean_is_exclusive(v_dt_420_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; lean_object* v_unused_449_; 
v_unused_448_ = lean_ctor_get(v_dt_420_, 3);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_dt_420_, 0);
lean_dec(v_unused_449_);
v___x_425_ = v_dt_420_;
v_isShared_426_ = v_isSharedCheck_447_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_rules_423_);
lean_inc(v_timestamp_422_);
lean_dec(v_dt_420_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_447_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v_second_427_; lean_object* v_nano_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_tz_441_; lean_object* v___f_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v_second_427_ = lean_ctor_get(v_timestamp_422_, 0);
lean_inc(v_second_427_);
v_nano_428_ = lean_ctor_get(v_timestamp_422_, 1);
lean_inc(v_nano_428_);
lean_dec_ref(v_timestamp_422_);
v___x_429_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_430_ = lean_int_mul(v_days_421_, v___x_429_);
v___x_431_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_432_ = lean_int_neg(v___x_430_);
lean_dec(v___x_430_);
v___x_433_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_434_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_435_ = lean_int_mul(v_second_427_, v___x_434_);
lean_dec(v_second_427_);
v___x_436_ = lean_int_add(v___x_435_, v_nano_428_);
lean_dec(v_nano_428_);
lean_dec(v___x_435_);
v___x_437_ = lean_int_mul(v___x_432_, v___x_434_);
lean_dec(v___x_432_);
v___x_438_ = lean_int_add(v___x_437_, v___x_433_);
lean_dec(v___x_437_);
v___x_439_ = lean_int_add(v___x_436_, v___x_438_);
lean_dec(v___x_438_);
lean_dec(v___x_436_);
v___x_440_ = l_Std_Time_Duration_ofNanoseconds(v___x_439_);
lean_dec(v___x_439_);
lean_inc_ref(v_rules_423_);
v_tz_441_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_423_, v___x_440_);
lean_inc_ref(v___x_440_);
lean_inc_ref(v_tz_441_);
v___f_442_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_442_, 0, v_tz_441_);
lean_closure_set(v___f_442_, 1, v___x_440_);
lean_closure_set(v___f_442_, 2, v___x_434_);
lean_closure_set(v___f_442_, 3, v___x_431_);
v___x_443_ = lean_mk_thunk(v___f_442_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 3, v_tz_441_);
lean_ctor_set(v___x_425_, 1, v___x_440_);
lean_ctor_set(v___x_425_, 0, v___x_443_);
v___x_445_ = v___x_425_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_rules_423_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_tz_441_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object* v_dt_450_, lean_object* v_days_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_Time_DateTime_subDays(v_dt_450_, v_days_451_);
lean_dec(v_days_451_);
return v_res_452_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_unsigned_to_nat(7u);
v___x_454_ = lean_nat_to_int(v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object* v_dt_455_, lean_object* v_weeks_456_){
_start:
{
lean_object* v_timestamp_457_; lean_object* v_rules_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_482_; 
v_timestamp_457_ = lean_ctor_get(v_dt_455_, 1);
v_rules_458_ = lean_ctor_get(v_dt_455_, 2);
v_isSharedCheck_482_ = !lean_is_exclusive(v_dt_455_);
if (v_isSharedCheck_482_ == 0)
{
lean_object* v_unused_483_; lean_object* v_unused_484_; 
v_unused_483_ = lean_ctor_get(v_dt_455_, 3);
lean_dec(v_unused_483_);
v_unused_484_ = lean_ctor_get(v_dt_455_, 0);
lean_dec(v_unused_484_);
v___x_460_ = v_dt_455_;
v_isShared_461_ = v_isSharedCheck_482_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_rules_458_);
lean_inc(v_timestamp_457_);
lean_dec(v_dt_455_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_482_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v_second_462_; lean_object* v_nano_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v_tz_476_; lean_object* v___f_477_; lean_object* v___x_478_; lean_object* v___x_480_; 
v_second_462_ = lean_ctor_get(v_timestamp_457_, 0);
lean_inc(v_second_462_);
v_nano_463_ = lean_ctor_get(v_timestamp_457_, 1);
lean_inc(v_nano_463_);
lean_dec_ref(v_timestamp_457_);
v___x_464_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_465_ = lean_int_mul(v_weeks_456_, v___x_464_);
v___x_466_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_467_ = lean_int_mul(v___x_465_, v___x_466_);
lean_dec(v___x_465_);
v___x_468_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_469_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_470_ = lean_int_mul(v_second_462_, v___x_469_);
lean_dec(v_second_462_);
v___x_471_ = lean_int_add(v___x_470_, v_nano_463_);
lean_dec(v_nano_463_);
lean_dec(v___x_470_);
v___x_472_ = lean_int_mul(v___x_467_, v___x_469_);
lean_dec(v___x_467_);
v___x_473_ = lean_int_add(v___x_472_, v___x_468_);
lean_dec(v___x_472_);
v___x_474_ = lean_int_add(v___x_471_, v___x_473_);
lean_dec(v___x_473_);
lean_dec(v___x_471_);
v___x_475_ = l_Std_Time_Duration_ofNanoseconds(v___x_474_);
lean_dec(v___x_474_);
lean_inc_ref(v_rules_458_);
v_tz_476_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_458_, v___x_475_);
lean_inc_ref(v___x_475_);
lean_inc_ref(v_tz_476_);
v___f_477_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_477_, 0, v_tz_476_);
lean_closure_set(v___f_477_, 1, v___x_475_);
lean_closure_set(v___f_477_, 2, v___x_469_);
lean_closure_set(v___f_477_, 3, v___x_468_);
v___x_478_ = lean_mk_thunk(v___f_477_);
if (v_isShared_461_ == 0)
{
lean_ctor_set(v___x_460_, 3, v_tz_476_);
lean_ctor_set(v___x_460_, 1, v___x_475_);
lean_ctor_set(v___x_460_, 0, v___x_478_);
v___x_480_ = v___x_460_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_rules_458_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_tz_476_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object* v_dt_485_, lean_object* v_weeks_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_Time_DateTime_addWeeks(v_dt_485_, v_weeks_486_);
lean_dec(v_weeks_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object* v_dt_488_, lean_object* v_weeks_489_){
_start:
{
lean_object* v_timestamp_490_; lean_object* v_rules_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_517_; 
v_timestamp_490_ = lean_ctor_get(v_dt_488_, 1);
v_rules_491_ = lean_ctor_get(v_dt_488_, 2);
v_isSharedCheck_517_ = !lean_is_exclusive(v_dt_488_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; lean_object* v_unused_519_; 
v_unused_518_ = lean_ctor_get(v_dt_488_, 3);
lean_dec(v_unused_518_);
v_unused_519_ = lean_ctor_get(v_dt_488_, 0);
lean_dec(v_unused_519_);
v___x_493_ = v_dt_488_;
v_isShared_494_ = v_isSharedCheck_517_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_rules_491_);
lean_inc(v_timestamp_490_);
lean_dec(v_dt_488_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_517_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_second_495_; lean_object* v_nano_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_tz_511_; lean_object* v___f_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v_second_495_ = lean_ctor_get(v_timestamp_490_, 0);
lean_inc(v_second_495_);
v_nano_496_ = lean_ctor_get(v_timestamp_490_, 1);
lean_inc(v_nano_496_);
lean_dec_ref(v_timestamp_490_);
v___x_497_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_498_ = lean_int_mul(v_weeks_489_, v___x_497_);
v___x_499_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_500_ = lean_int_mul(v___x_498_, v___x_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_502_ = lean_int_neg(v___x_500_);
lean_dec(v___x_500_);
v___x_503_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_504_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_505_ = lean_int_mul(v_second_495_, v___x_504_);
lean_dec(v_second_495_);
v___x_506_ = lean_int_add(v___x_505_, v_nano_496_);
lean_dec(v_nano_496_);
lean_dec(v___x_505_);
v___x_507_ = lean_int_mul(v___x_502_, v___x_504_);
lean_dec(v___x_502_);
v___x_508_ = lean_int_add(v___x_507_, v___x_503_);
lean_dec(v___x_507_);
v___x_509_ = lean_int_add(v___x_506_, v___x_508_);
lean_dec(v___x_508_);
lean_dec(v___x_506_);
v___x_510_ = l_Std_Time_Duration_ofNanoseconds(v___x_509_);
lean_dec(v___x_509_);
lean_inc_ref(v_rules_491_);
v_tz_511_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_491_, v___x_510_);
lean_inc_ref(v___x_510_);
lean_inc_ref(v_tz_511_);
v___f_512_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_512_, 0, v_tz_511_);
lean_closure_set(v___f_512_, 1, v___x_510_);
lean_closure_set(v___f_512_, 2, v___x_504_);
lean_closure_set(v___f_512_, 3, v___x_501_);
v___x_513_ = lean_mk_thunk(v___f_512_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 3, v_tz_511_);
lean_ctor_set(v___x_493_, 1, v___x_510_);
lean_ctor_set(v___x_493_, 0, v___x_513_);
v___x_515_ = v___x_493_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_516_, 2, v_rules_491_);
lean_ctor_set(v_reuseFailAlloc_516_, 3, v_tz_511_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object* v_dt_520_, lean_object* v_weeks_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_Time_DateTime_subWeeks(v_dt_520_, v_weeks_521_);
lean_dec(v_weeks_521_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0(lean_object* v___x_523_, lean_object* v_x_524_){
_start:
{
lean_inc_ref(v___x_523_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(lean_object* v___x_525_, lean_object* v_x_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_Time_DateTime_addMonthsClip___lam__0(v___x_525_, v_x_526_);
lean_dec_ref(v___x_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object* v_dt_528_, lean_object* v_months_529_){
_start:
{
lean_object* v_date_530_; lean_object* v_rules_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_557_; 
v_date_530_ = lean_ctor_get(v_dt_528_, 0);
v_rules_531_ = lean_ctor_get(v_dt_528_, 2);
v_isSharedCheck_557_ = !lean_is_exclusive(v_dt_528_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_558_ = lean_ctor_get(v_dt_528_, 3);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_dt_528_, 1);
lean_dec(v_unused_559_);
v___x_533_ = v_dt_528_;
v_isShared_534_ = v_isSharedCheck_557_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_rules_531_);
lean_inc(v_date_530_);
lean_dec(v_dt_528_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_557_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_wt_537_; lean_object* v_ltt_538_; lean_object* v_tz_539_; lean_object* v_offset_540_; lean_object* v_second_541_; lean_object* v_nano_542_; lean_object* v___f_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_535_ = lean_thunk_get_own(v_date_530_);
lean_dec_ref(v_date_530_);
v___x_536_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_535_, v_months_529_);
lean_inc_ref(v___x_536_);
v_wt_537_ = l_Std_Time_PlainDateTime_toWallTime(v___x_536_);
lean_inc_ref(v_rules_531_);
v_ltt_538_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_531_, v_wt_537_);
v_tz_539_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_538_);
lean_dec_ref(v_ltt_538_);
v_offset_540_ = lean_ctor_get(v_tz_539_, 0);
lean_inc(v_offset_540_);
v_second_541_ = lean_ctor_get(v_wt_537_, 0);
lean_inc(v_second_541_);
v_nano_542_ = lean_ctor_get(v_wt_537_, 1);
lean_inc(v_nano_542_);
lean_dec_ref(v_wt_537_);
v___f_543_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_543_, 0, v___x_536_);
v___x_544_ = lean_mk_thunk(v___f_543_);
v___x_545_ = lean_int_neg(v_offset_540_);
lean_dec(v_offset_540_);
v___x_546_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_547_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_548_ = lean_int_mul(v_second_541_, v___x_547_);
lean_dec(v_second_541_);
v___x_549_ = lean_int_add(v___x_548_, v_nano_542_);
lean_dec(v_nano_542_);
lean_dec(v___x_548_);
v___x_550_ = lean_int_mul(v___x_545_, v___x_547_);
lean_dec(v___x_545_);
v___x_551_ = lean_int_add(v___x_550_, v___x_546_);
lean_dec(v___x_550_);
v___x_552_ = lean_int_add(v___x_549_, v___x_551_);
lean_dec(v___x_551_);
lean_dec(v___x_549_);
v___x_553_ = l_Std_Time_Duration_ofNanoseconds(v___x_552_);
lean_dec(v___x_552_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 3, v_tz_539_);
lean_ctor_set(v___x_533_, 1, v___x_553_);
lean_ctor_set(v___x_533_, 0, v___x_544_);
v___x_555_ = v___x_533_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_544_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_rules_531_);
lean_ctor_set(v_reuseFailAlloc_556_, 3, v_tz_539_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object* v_dt_560_, lean_object* v_months_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Time_DateTime_addMonthsClip(v_dt_560_, v_months_561_);
lean_dec(v_months_561_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object* v_dt_563_, lean_object* v_months_564_){
_start:
{
lean_object* v_date_565_; lean_object* v_rules_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_602_; 
v_date_565_ = lean_ctor_get(v_dt_563_, 0);
v_rules_566_ = lean_ctor_get(v_dt_563_, 2);
v_isSharedCheck_602_ = !lean_is_exclusive(v_dt_563_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; lean_object* v_unused_604_; 
v_unused_603_ = lean_ctor_get(v_dt_563_, 3);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_dt_563_, 1);
lean_dec(v_unused_604_);
v___x_568_ = v_dt_563_;
v_isShared_569_ = v_isSharedCheck_602_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_rules_566_);
lean_inc(v_date_565_);
lean_dec(v_dt_563_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_602_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v_date_571_; lean_object* v_time_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_601_; 
v___x_570_ = lean_thunk_get_own(v_date_565_);
lean_dec_ref(v_date_565_);
v_date_571_ = lean_ctor_get(v___x_570_, 0);
v_time_572_ = lean_ctor_get(v___x_570_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_601_ == 0)
{
v___x_574_ = v___x_570_;
v_isShared_575_ = v_isSharedCheck_601_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_time_572_);
lean_inc(v_date_571_);
lean_dec(v___x_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_601_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_576_ = lean_int_neg(v_months_564_);
v___x_577_ = l_Std_Time_PlainDate_addMonthsClip(v_date_571_, v___x_576_);
lean_dec(v___x_576_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_577_);
v___x_579_ = v___x_574_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_577_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_time_572_);
v___x_579_ = v_reuseFailAlloc_600_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v_wt_580_; lean_object* v_ltt_581_; lean_object* v_tz_582_; lean_object* v_offset_583_; lean_object* v_second_584_; lean_object* v_nano_585_; lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
lean_inc_ref(v___x_579_);
v_wt_580_ = l_Std_Time_PlainDateTime_toWallTime(v___x_579_);
lean_inc_ref(v_rules_566_);
v_ltt_581_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_566_, v_wt_580_);
v_tz_582_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_581_);
lean_dec_ref(v_ltt_581_);
v_offset_583_ = lean_ctor_get(v_tz_582_, 0);
lean_inc(v_offset_583_);
v_second_584_ = lean_ctor_get(v_wt_580_, 0);
lean_inc(v_second_584_);
v_nano_585_ = lean_ctor_get(v_wt_580_, 1);
lean_inc(v_nano_585_);
lean_dec_ref(v_wt_580_);
v___f_586_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_586_, 0, v___x_579_);
v___x_587_ = lean_mk_thunk(v___f_586_);
v___x_588_ = lean_int_neg(v_offset_583_);
lean_dec(v_offset_583_);
v___x_589_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_590_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_591_ = lean_int_mul(v_second_584_, v___x_590_);
lean_dec(v_second_584_);
v___x_592_ = lean_int_add(v___x_591_, v_nano_585_);
lean_dec(v_nano_585_);
lean_dec(v___x_591_);
v___x_593_ = lean_int_mul(v___x_588_, v___x_590_);
lean_dec(v___x_588_);
v___x_594_ = lean_int_add(v___x_593_, v___x_589_);
lean_dec(v___x_593_);
v___x_595_ = lean_int_add(v___x_592_, v___x_594_);
lean_dec(v___x_594_);
lean_dec(v___x_592_);
v___x_596_ = l_Std_Time_Duration_ofNanoseconds(v___x_595_);
lean_dec(v___x_595_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 3, v_tz_582_);
lean_ctor_set(v___x_568_, 1, v___x_596_);
lean_ctor_set(v___x_568_, 0, v___x_587_);
v___x_598_ = v___x_568_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_rules_566_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_tz_582_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object* v_dt_605_, lean_object* v_months_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Std_Time_DateTime_subMonthsClip(v_dt_605_, v_months_606_);
lean_dec(v_months_606_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object* v_dt_608_, lean_object* v_months_609_){
_start:
{
lean_object* v_date_610_; lean_object* v_rules_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_637_; 
v_date_610_ = lean_ctor_get(v_dt_608_, 0);
v_rules_611_ = lean_ctor_get(v_dt_608_, 2);
v_isSharedCheck_637_ = !lean_is_exclusive(v_dt_608_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; lean_object* v_unused_639_; 
v_unused_638_ = lean_ctor_get(v_dt_608_, 3);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_dt_608_, 1);
lean_dec(v_unused_639_);
v___x_613_ = v_dt_608_;
v_isShared_614_ = v_isSharedCheck_637_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_rules_611_);
lean_inc(v_date_610_);
lean_dec(v_dt_608_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_637_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_wt_617_; lean_object* v_ltt_618_; lean_object* v_tz_619_; lean_object* v_offset_620_; lean_object* v_second_621_; lean_object* v_nano_622_; lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_615_ = lean_thunk_get_own(v_date_610_);
lean_dec_ref(v_date_610_);
v___x_616_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_615_, v_months_609_);
lean_inc_ref(v___x_616_);
v_wt_617_ = l_Std_Time_PlainDateTime_toWallTime(v___x_616_);
lean_inc_ref(v_rules_611_);
v_ltt_618_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_611_, v_wt_617_);
v_tz_619_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_618_);
lean_dec_ref(v_ltt_618_);
v_offset_620_ = lean_ctor_get(v_tz_619_, 0);
lean_inc(v_offset_620_);
v_second_621_ = lean_ctor_get(v_wt_617_, 0);
lean_inc(v_second_621_);
v_nano_622_ = lean_ctor_get(v_wt_617_, 1);
lean_inc(v_nano_622_);
lean_dec_ref(v_wt_617_);
v___f_623_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_623_, 0, v___x_616_);
v___x_624_ = lean_mk_thunk(v___f_623_);
v___x_625_ = lean_int_neg(v_offset_620_);
lean_dec(v_offset_620_);
v___x_626_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_627_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_628_ = lean_int_mul(v_second_621_, v___x_627_);
lean_dec(v_second_621_);
v___x_629_ = lean_int_add(v___x_628_, v_nano_622_);
lean_dec(v_nano_622_);
lean_dec(v___x_628_);
v___x_630_ = lean_int_mul(v___x_625_, v___x_627_);
lean_dec(v___x_625_);
v___x_631_ = lean_int_add(v___x_630_, v___x_626_);
lean_dec(v___x_630_);
v___x_632_ = lean_int_add(v___x_629_, v___x_631_);
lean_dec(v___x_631_);
lean_dec(v___x_629_);
v___x_633_ = l_Std_Time_Duration_ofNanoseconds(v___x_632_);
lean_dec(v___x_632_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 3, v_tz_619_);
lean_ctor_set(v___x_613_, 1, v___x_633_);
lean_ctor_set(v___x_613_, 0, v___x_624_);
v___x_635_ = v___x_613_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_rules_611_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_tz_619_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object* v_dt_640_, lean_object* v_months_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Std_Time_DateTime_addMonthsRollOver(v_dt_640_, v_months_641_);
lean_dec(v_months_641_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object* v_dt_643_, lean_object* v_months_644_){
_start:
{
lean_object* v_date_645_; lean_object* v_rules_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_682_; 
v_date_645_ = lean_ctor_get(v_dt_643_, 0);
v_rules_646_ = lean_ctor_get(v_dt_643_, 2);
v_isSharedCheck_682_ = !lean_is_exclusive(v_dt_643_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; lean_object* v_unused_684_; 
v_unused_683_ = lean_ctor_get(v_dt_643_, 3);
lean_dec(v_unused_683_);
v_unused_684_ = lean_ctor_get(v_dt_643_, 1);
lean_dec(v_unused_684_);
v___x_648_ = v_dt_643_;
v_isShared_649_ = v_isSharedCheck_682_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_rules_646_);
lean_inc(v_date_645_);
lean_dec(v_dt_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_682_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; lean_object* v_date_651_; lean_object* v_time_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_681_; 
v___x_650_ = lean_thunk_get_own(v_date_645_);
lean_dec_ref(v_date_645_);
v_date_651_ = lean_ctor_get(v___x_650_, 0);
v_time_652_ = lean_ctor_get(v___x_650_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_681_ == 0)
{
v___x_654_ = v___x_650_;
v_isShared_655_ = v_isSharedCheck_681_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_time_652_);
lean_inc(v_date_651_);
lean_dec(v___x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_681_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v___x_656_ = lean_int_neg(v_months_644_);
v___x_657_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_651_, v___x_656_);
lean_dec(v___x_656_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_657_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_657_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v_time_652_);
v___x_659_ = v_reuseFailAlloc_680_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
lean_object* v_wt_660_; lean_object* v_ltt_661_; lean_object* v_tz_662_; lean_object* v_offset_663_; lean_object* v_second_664_; lean_object* v_nano_665_; lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
lean_inc_ref(v___x_659_);
v_wt_660_ = l_Std_Time_PlainDateTime_toWallTime(v___x_659_);
lean_inc_ref(v_rules_646_);
v_ltt_661_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_646_, v_wt_660_);
v_tz_662_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_661_);
lean_dec_ref(v_ltt_661_);
v_offset_663_ = lean_ctor_get(v_tz_662_, 0);
lean_inc(v_offset_663_);
v_second_664_ = lean_ctor_get(v_wt_660_, 0);
lean_inc(v_second_664_);
v_nano_665_ = lean_ctor_get(v_wt_660_, 1);
lean_inc(v_nano_665_);
lean_dec_ref(v_wt_660_);
v___f_666_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_666_, 0, v___x_659_);
v___x_667_ = lean_mk_thunk(v___f_666_);
v___x_668_ = lean_int_neg(v_offset_663_);
lean_dec(v_offset_663_);
v___x_669_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_670_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_671_ = lean_int_mul(v_second_664_, v___x_670_);
lean_dec(v_second_664_);
v___x_672_ = lean_int_add(v___x_671_, v_nano_665_);
lean_dec(v_nano_665_);
lean_dec(v___x_671_);
v___x_673_ = lean_int_mul(v___x_668_, v___x_670_);
lean_dec(v___x_668_);
v___x_674_ = lean_int_add(v___x_673_, v___x_669_);
lean_dec(v___x_673_);
v___x_675_ = lean_int_add(v___x_672_, v___x_674_);
lean_dec(v___x_674_);
lean_dec(v___x_672_);
v___x_676_ = l_Std_Time_Duration_ofNanoseconds(v___x_675_);
lean_dec(v___x_675_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 3, v_tz_662_);
lean_ctor_set(v___x_648_, 1, v___x_676_);
lean_ctor_set(v___x_648_, 0, v___x_667_);
v___x_678_ = v___x_648_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_679_, 2, v_rules_646_);
lean_ctor_set(v_reuseFailAlloc_679_, 3, v_tz_662_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object* v_dt_685_, lean_object* v_months_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_Time_DateTime_subMonthsRollOver(v_dt_685_, v_months_686_);
lean_dec(v_months_686_);
return v_res_687_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_unsigned_to_nat(12u);
v___x_689_ = lean_nat_to_int(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object* v_dt_690_, lean_object* v_years_691_){
_start:
{
lean_object* v_date_692_; lean_object* v_rules_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_730_; 
v_date_692_ = lean_ctor_get(v_dt_690_, 0);
v_rules_693_ = lean_ctor_get(v_dt_690_, 2);
v_isSharedCheck_730_ = !lean_is_exclusive(v_dt_690_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; lean_object* v_unused_732_; 
v_unused_731_ = lean_ctor_get(v_dt_690_, 3);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_dt_690_, 1);
lean_dec(v_unused_732_);
v___x_695_ = v_dt_690_;
v_isShared_696_ = v_isSharedCheck_730_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_rules_693_);
lean_inc(v_date_692_);
lean_dec(v_dt_690_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_730_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v_date_698_; lean_object* v_time_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_729_; 
v___x_697_ = lean_thunk_get_own(v_date_692_);
lean_dec_ref(v_date_692_);
v_date_698_ = lean_ctor_get(v___x_697_, 0);
v_time_699_ = lean_ctor_get(v___x_697_, 1);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_729_ == 0)
{
v___x_701_ = v___x_697_;
v_isShared_702_ = v_isSharedCheck_729_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_time_699_);
lean_inc(v_date_698_);
lean_dec(v___x_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_729_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_703_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_704_ = lean_int_mul(v_years_691_, v___x_703_);
v___x_705_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_698_, v___x_704_);
lean_dec(v___x_704_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_705_);
v___x_707_ = v___x_701_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_time_699_);
v___x_707_ = v_reuseFailAlloc_728_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v_wt_708_; lean_object* v_ltt_709_; lean_object* v_tz_710_; lean_object* v_offset_711_; lean_object* v_second_712_; lean_object* v_nano_713_; lean_object* v___f_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
lean_inc_ref(v___x_707_);
v_wt_708_ = l_Std_Time_PlainDateTime_toWallTime(v___x_707_);
lean_inc_ref(v_rules_693_);
v_ltt_709_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_693_, v_wt_708_);
v_tz_710_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_709_);
lean_dec_ref(v_ltt_709_);
v_offset_711_ = lean_ctor_get(v_tz_710_, 0);
lean_inc(v_offset_711_);
v_second_712_ = lean_ctor_get(v_wt_708_, 0);
lean_inc(v_second_712_);
v_nano_713_ = lean_ctor_get(v_wt_708_, 1);
lean_inc(v_nano_713_);
lean_dec_ref(v_wt_708_);
v___f_714_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_714_, 0, v___x_707_);
v___x_715_ = lean_mk_thunk(v___f_714_);
v___x_716_ = lean_int_neg(v_offset_711_);
lean_dec(v_offset_711_);
v___x_717_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_718_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_719_ = lean_int_mul(v_second_712_, v___x_718_);
lean_dec(v_second_712_);
v___x_720_ = lean_int_add(v___x_719_, v_nano_713_);
lean_dec(v_nano_713_);
lean_dec(v___x_719_);
v___x_721_ = lean_int_mul(v___x_716_, v___x_718_);
lean_dec(v___x_716_);
v___x_722_ = lean_int_add(v___x_721_, v___x_717_);
lean_dec(v___x_721_);
v___x_723_ = lean_int_add(v___x_720_, v___x_722_);
lean_dec(v___x_722_);
lean_dec(v___x_720_);
v___x_724_ = l_Std_Time_Duration_ofNanoseconds(v___x_723_);
lean_dec(v___x_723_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 3, v_tz_710_);
lean_ctor_set(v___x_695_, 1, v___x_724_);
lean_ctor_set(v___x_695_, 0, v___x_715_);
v___x_726_ = v___x_695_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_rules_693_);
lean_ctor_set(v_reuseFailAlloc_727_, 3, v_tz_710_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object* v_dt_733_, lean_object* v_years_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_Time_DateTime_addYearsRollOver(v_dt_733_, v_years_734_);
lean_dec(v_years_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object* v_dt_736_, lean_object* v_years_737_){
_start:
{
lean_object* v_date_738_; lean_object* v_rules_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_776_; 
v_date_738_ = lean_ctor_get(v_dt_736_, 0);
v_rules_739_ = lean_ctor_get(v_dt_736_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_dt_736_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; lean_object* v_unused_778_; 
v_unused_777_ = lean_ctor_get(v_dt_736_, 3);
lean_dec(v_unused_777_);
v_unused_778_ = lean_ctor_get(v_dt_736_, 1);
lean_dec(v_unused_778_);
v___x_741_ = v_dt_736_;
v_isShared_742_ = v_isSharedCheck_776_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_rules_739_);
lean_inc(v_date_738_);
lean_dec(v_dt_736_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_776_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v_date_744_; lean_object* v_time_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_775_; 
v___x_743_ = lean_thunk_get_own(v_date_738_);
lean_dec_ref(v_date_738_);
v_date_744_ = lean_ctor_get(v___x_743_, 0);
v_time_745_ = lean_ctor_get(v___x_743_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_775_ == 0)
{
v___x_747_ = v___x_743_;
v_isShared_748_ = v_isSharedCheck_775_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_time_745_);
lean_inc(v_date_744_);
lean_dec(v___x_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_775_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_749_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_750_ = lean_int_mul(v_years_737_, v___x_749_);
v___x_751_ = l_Std_Time_PlainDate_addMonthsClip(v_date_744_, v___x_750_);
lean_dec(v___x_750_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_753_ = v___x_747_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_time_745_);
v___x_753_ = v_reuseFailAlloc_774_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v_wt_754_; lean_object* v_ltt_755_; lean_object* v_tz_756_; lean_object* v_offset_757_; lean_object* v_second_758_; lean_object* v_nano_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
lean_inc_ref(v___x_753_);
v_wt_754_ = l_Std_Time_PlainDateTime_toWallTime(v___x_753_);
lean_inc_ref(v_rules_739_);
v_ltt_755_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_739_, v_wt_754_);
v_tz_756_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_755_);
lean_dec_ref(v_ltt_755_);
v_offset_757_ = lean_ctor_get(v_tz_756_, 0);
lean_inc(v_offset_757_);
v_second_758_ = lean_ctor_get(v_wt_754_, 0);
lean_inc(v_second_758_);
v_nano_759_ = lean_ctor_get(v_wt_754_, 1);
lean_inc(v_nano_759_);
lean_dec_ref(v_wt_754_);
v___f_760_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_760_, 0, v___x_753_);
v___x_761_ = lean_mk_thunk(v___f_760_);
v___x_762_ = lean_int_neg(v_offset_757_);
lean_dec(v_offset_757_);
v___x_763_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_764_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_765_ = lean_int_mul(v_second_758_, v___x_764_);
lean_dec(v_second_758_);
v___x_766_ = lean_int_add(v___x_765_, v_nano_759_);
lean_dec(v_nano_759_);
lean_dec(v___x_765_);
v___x_767_ = lean_int_mul(v___x_762_, v___x_764_);
lean_dec(v___x_762_);
v___x_768_ = lean_int_add(v___x_767_, v___x_763_);
lean_dec(v___x_767_);
v___x_769_ = lean_int_add(v___x_766_, v___x_768_);
lean_dec(v___x_768_);
lean_dec(v___x_766_);
v___x_770_ = l_Std_Time_Duration_ofNanoseconds(v___x_769_);
lean_dec(v___x_769_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 3, v_tz_756_);
lean_ctor_set(v___x_741_, 1, v___x_770_);
lean_ctor_set(v___x_741_, 0, v___x_761_);
v___x_772_ = v___x_741_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_761_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_rules_739_);
lean_ctor_set(v_reuseFailAlloc_773_, 3, v_tz_756_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object* v_dt_779_, lean_object* v_years_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_Time_DateTime_addYearsClip(v_dt_779_, v_years_780_);
lean_dec(v_years_780_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object* v_dt_782_, lean_object* v_years_783_){
_start:
{
lean_object* v_date_784_; lean_object* v_rules_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_823_; 
v_date_784_ = lean_ctor_get(v_dt_782_, 0);
v_rules_785_ = lean_ctor_get(v_dt_782_, 2);
v_isSharedCheck_823_ = !lean_is_exclusive(v_dt_782_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; lean_object* v_unused_825_; 
v_unused_824_ = lean_ctor_get(v_dt_782_, 3);
lean_dec(v_unused_824_);
v_unused_825_ = lean_ctor_get(v_dt_782_, 1);
lean_dec(v_unused_825_);
v___x_787_ = v_dt_782_;
v_isShared_788_ = v_isSharedCheck_823_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_rules_785_);
lean_inc(v_date_784_);
lean_dec(v_dt_782_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_823_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v_date_790_; lean_object* v_time_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_822_; 
v___x_789_ = lean_thunk_get_own(v_date_784_);
lean_dec_ref(v_date_784_);
v_date_790_ = lean_ctor_get(v___x_789_, 0);
v_time_791_ = lean_ctor_get(v___x_789_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_822_ == 0)
{
v___x_793_ = v___x_789_;
v_isShared_794_ = v_isSharedCheck_822_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_time_791_);
lean_inc(v_date_790_);
lean_dec(v___x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_822_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_795_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_796_ = lean_int_mul(v_years_783_, v___x_795_);
v___x_797_ = lean_int_neg(v___x_796_);
lean_dec(v___x_796_);
v___x_798_ = l_Std_Time_PlainDate_addMonthsClip(v_date_790_, v___x_797_);
lean_dec(v___x_797_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_798_);
v___x_800_ = v___x_793_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_time_791_);
v___x_800_ = v_reuseFailAlloc_821_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v_wt_801_; lean_object* v_ltt_802_; lean_object* v_tz_803_; lean_object* v_offset_804_; lean_object* v_second_805_; lean_object* v_nano_806_; lean_object* v___f_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_819_; 
lean_inc_ref(v___x_800_);
v_wt_801_ = l_Std_Time_PlainDateTime_toWallTime(v___x_800_);
lean_inc_ref(v_rules_785_);
v_ltt_802_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_785_, v_wt_801_);
v_tz_803_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_802_);
lean_dec_ref(v_ltt_802_);
v_offset_804_ = lean_ctor_get(v_tz_803_, 0);
lean_inc(v_offset_804_);
v_second_805_ = lean_ctor_get(v_wt_801_, 0);
lean_inc(v_second_805_);
v_nano_806_ = lean_ctor_get(v_wt_801_, 1);
lean_inc(v_nano_806_);
lean_dec_ref(v_wt_801_);
v___f_807_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_807_, 0, v___x_800_);
v___x_808_ = lean_mk_thunk(v___f_807_);
v___x_809_ = lean_int_neg(v_offset_804_);
lean_dec(v_offset_804_);
v___x_810_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_811_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_812_ = lean_int_mul(v_second_805_, v___x_811_);
lean_dec(v_second_805_);
v___x_813_ = lean_int_add(v___x_812_, v_nano_806_);
lean_dec(v_nano_806_);
lean_dec(v___x_812_);
v___x_814_ = lean_int_mul(v___x_809_, v___x_811_);
lean_dec(v___x_809_);
v___x_815_ = lean_int_add(v___x_814_, v___x_810_);
lean_dec(v___x_814_);
v___x_816_ = lean_int_add(v___x_813_, v___x_815_);
lean_dec(v___x_815_);
lean_dec(v___x_813_);
v___x_817_ = l_Std_Time_Duration_ofNanoseconds(v___x_816_);
lean_dec(v___x_816_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 3, v_tz_803_);
lean_ctor_set(v___x_787_, 1, v___x_817_);
lean_ctor_set(v___x_787_, 0, v___x_808_);
v___x_819_ = v___x_787_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_rules_785_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v_tz_803_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object* v_dt_826_, lean_object* v_years_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Std_Time_DateTime_subYearsClip(v_dt_826_, v_years_827_);
lean_dec(v_years_827_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object* v_dt_829_, lean_object* v_years_830_){
_start:
{
lean_object* v_date_831_; lean_object* v_rules_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_870_; 
v_date_831_ = lean_ctor_get(v_dt_829_, 0);
v_rules_832_ = lean_ctor_get(v_dt_829_, 2);
v_isSharedCheck_870_ = !lean_is_exclusive(v_dt_829_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; lean_object* v_unused_872_; 
v_unused_871_ = lean_ctor_get(v_dt_829_, 3);
lean_dec(v_unused_871_);
v_unused_872_ = lean_ctor_get(v_dt_829_, 1);
lean_dec(v_unused_872_);
v___x_834_ = v_dt_829_;
v_isShared_835_ = v_isSharedCheck_870_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_rules_832_);
lean_inc(v_date_831_);
lean_dec(v_dt_829_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_870_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v_date_837_; lean_object* v_time_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_869_; 
v___x_836_ = lean_thunk_get_own(v_date_831_);
lean_dec_ref(v_date_831_);
v_date_837_ = lean_ctor_get(v___x_836_, 0);
v_time_838_ = lean_ctor_get(v___x_836_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_869_ == 0)
{
v___x_840_ = v___x_836_;
v_isShared_841_ = v_isSharedCheck_869_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_time_838_);
lean_inc(v_date_837_);
lean_dec(v___x_836_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_869_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_842_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_843_ = lean_int_mul(v_years_830_, v___x_842_);
v___x_844_ = lean_int_neg(v___x_843_);
lean_dec(v___x_843_);
v___x_845_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_837_, v___x_844_);
lean_dec(v___x_844_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_845_);
v___x_847_ = v___x_840_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_845_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_time_838_);
v___x_847_ = v_reuseFailAlloc_868_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v_wt_848_; lean_object* v_ltt_849_; lean_object* v_tz_850_; lean_object* v_offset_851_; lean_object* v_second_852_; lean_object* v_nano_853_; lean_object* v___f_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
lean_inc_ref(v___x_847_);
v_wt_848_ = l_Std_Time_PlainDateTime_toWallTime(v___x_847_);
lean_inc_ref(v_rules_832_);
v_ltt_849_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_832_, v_wt_848_);
v_tz_850_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_849_);
lean_dec_ref(v_ltt_849_);
v_offset_851_ = lean_ctor_get(v_tz_850_, 0);
lean_inc(v_offset_851_);
v_second_852_ = lean_ctor_get(v_wt_848_, 0);
lean_inc(v_second_852_);
v_nano_853_ = lean_ctor_get(v_wt_848_, 1);
lean_inc(v_nano_853_);
lean_dec_ref(v_wt_848_);
v___f_854_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_854_, 0, v___x_847_);
v___x_855_ = lean_mk_thunk(v___f_854_);
v___x_856_ = lean_int_neg(v_offset_851_);
lean_dec(v_offset_851_);
v___x_857_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_858_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_859_ = lean_int_mul(v_second_852_, v___x_858_);
lean_dec(v_second_852_);
v___x_860_ = lean_int_add(v___x_859_, v_nano_853_);
lean_dec(v_nano_853_);
lean_dec(v___x_859_);
v___x_861_ = lean_int_mul(v___x_856_, v___x_858_);
lean_dec(v___x_856_);
v___x_862_ = lean_int_add(v___x_861_, v___x_857_);
lean_dec(v___x_861_);
v___x_863_ = lean_int_add(v___x_860_, v___x_862_);
lean_dec(v___x_862_);
lean_dec(v___x_860_);
v___x_864_ = l_Std_Time_Duration_ofNanoseconds(v___x_863_);
lean_dec(v___x_863_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 3, v_tz_850_);
lean_ctor_set(v___x_834_, 1, v___x_864_);
lean_ctor_set(v___x_834_, 0, v___x_855_);
v___x_866_ = v___x_834_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v___x_864_);
lean_ctor_set(v_reuseFailAlloc_867_, 2, v_rules_832_);
lean_ctor_set(v_reuseFailAlloc_867_, 3, v_tz_850_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object* v_dt_873_, lean_object* v_years_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_Time_DateTime_subYearsRollOver(v_dt_873_, v_years_874_);
lean_dec(v_years_874_);
return v_res_875_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_unsigned_to_nat(3600u);
v___x_877_ = lean_nat_to_int(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object* v_dt_878_, lean_object* v_hours_879_){
_start:
{
lean_object* v_timestamp_880_; lean_object* v_rules_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_903_; 
v_timestamp_880_ = lean_ctor_get(v_dt_878_, 1);
v_rules_881_ = lean_ctor_get(v_dt_878_, 2);
v_isSharedCheck_903_ = !lean_is_exclusive(v_dt_878_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; lean_object* v_unused_905_; 
v_unused_904_ = lean_ctor_get(v_dt_878_, 3);
lean_dec(v_unused_904_);
v_unused_905_ = lean_ctor_get(v_dt_878_, 0);
lean_dec(v_unused_905_);
v___x_883_ = v_dt_878_;
v_isShared_884_ = v_isSharedCheck_903_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_rules_881_);
lean_inc(v_timestamp_880_);
lean_dec(v_dt_878_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_903_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_second_885_; lean_object* v_nano_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v_tz_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_901_; 
v_second_885_ = lean_ctor_get(v_timestamp_880_, 0);
lean_inc(v_second_885_);
v_nano_886_ = lean_ctor_get(v_timestamp_880_, 1);
lean_inc(v_nano_886_);
lean_dec_ref(v_timestamp_880_);
v___x_887_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_888_ = lean_int_mul(v_hours_879_, v___x_887_);
v___x_889_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_890_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_891_ = lean_int_mul(v_second_885_, v___x_890_);
lean_dec(v_second_885_);
v___x_892_ = lean_int_add(v___x_891_, v_nano_886_);
lean_dec(v_nano_886_);
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
lean_inc_ref(v_rules_881_);
v_tz_897_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_881_, v___x_896_);
lean_inc_ref(v___x_896_);
lean_inc_ref(v_tz_897_);
v___f_898_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_898_, 0, v_tz_897_);
lean_closure_set(v___f_898_, 1, v___x_896_);
lean_closure_set(v___f_898_, 2, v___x_890_);
lean_closure_set(v___f_898_, 3, v___x_889_);
v___x_899_ = lean_mk_thunk(v___f_898_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 3, v_tz_897_);
lean_ctor_set(v___x_883_, 1, v___x_896_);
lean_ctor_set(v___x_883_, 0, v___x_899_);
v___x_901_ = v___x_883_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v___x_896_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_rules_881_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_tz_897_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object* v_dt_906_, lean_object* v_hours_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Std_Time_DateTime_addHours(v_dt_906_, v_hours_907_);
lean_dec(v_hours_907_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object* v_dt_909_, lean_object* v_hours_910_){
_start:
{
lean_object* v_timestamp_911_; lean_object* v_rules_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_936_; 
v_timestamp_911_ = lean_ctor_get(v_dt_909_, 1);
v_rules_912_ = lean_ctor_get(v_dt_909_, 2);
v_isSharedCheck_936_ = !lean_is_exclusive(v_dt_909_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; lean_object* v_unused_938_; 
v_unused_937_ = lean_ctor_get(v_dt_909_, 3);
lean_dec(v_unused_937_);
v_unused_938_ = lean_ctor_get(v_dt_909_, 0);
lean_dec(v_unused_938_);
v___x_914_ = v_dt_909_;
v_isShared_915_ = v_isSharedCheck_936_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_rules_912_);
lean_inc(v_timestamp_911_);
lean_dec(v_dt_909_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_936_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_second_916_; lean_object* v_nano_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v_tz_930_; lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v_second_916_ = lean_ctor_get(v_timestamp_911_, 0);
lean_inc(v_second_916_);
v_nano_917_ = lean_ctor_get(v_timestamp_911_, 1);
lean_inc(v_nano_917_);
lean_dec_ref(v_timestamp_911_);
v___x_918_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_919_ = lean_int_mul(v_hours_910_, v___x_918_);
v___x_920_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_921_ = lean_int_neg(v___x_919_);
lean_dec(v___x_919_);
v___x_922_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_923_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_924_ = lean_int_mul(v_second_916_, v___x_923_);
lean_dec(v_second_916_);
v___x_925_ = lean_int_add(v___x_924_, v_nano_917_);
lean_dec(v_nano_917_);
lean_dec(v___x_924_);
v___x_926_ = lean_int_mul(v___x_921_, v___x_923_);
lean_dec(v___x_921_);
v___x_927_ = lean_int_add(v___x_926_, v___x_922_);
lean_dec(v___x_926_);
v___x_928_ = lean_int_add(v___x_925_, v___x_927_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
v___x_929_ = l_Std_Time_Duration_ofNanoseconds(v___x_928_);
lean_dec(v___x_928_);
lean_inc_ref(v_rules_912_);
v_tz_930_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_912_, v___x_929_);
lean_inc_ref(v___x_929_);
lean_inc_ref(v_tz_930_);
v___f_931_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_931_, 0, v_tz_930_);
lean_closure_set(v___f_931_, 1, v___x_929_);
lean_closure_set(v___f_931_, 2, v___x_923_);
lean_closure_set(v___f_931_, 3, v___x_920_);
v___x_932_ = lean_mk_thunk(v___f_931_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 3, v_tz_930_);
lean_ctor_set(v___x_914_, 1, v___x_929_);
lean_ctor_set(v___x_914_, 0, v___x_932_);
v___x_934_ = v___x_914_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_rules_912_);
lean_ctor_set(v_reuseFailAlloc_935_, 3, v_tz_930_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object* v_dt_939_, lean_object* v_hours_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_Time_DateTime_subHours(v_dt_939_, v_hours_940_);
lean_dec(v_hours_940_);
return v_res_941_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_unsigned_to_nat(60u);
v___x_943_ = lean_nat_to_int(v___x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object* v_dt_944_, lean_object* v_minutes_945_){
_start:
{
lean_object* v_timestamp_946_; lean_object* v_rules_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_969_; 
v_timestamp_946_ = lean_ctor_get(v_dt_944_, 1);
v_rules_947_ = lean_ctor_get(v_dt_944_, 2);
v_isSharedCheck_969_ = !lean_is_exclusive(v_dt_944_);
if (v_isSharedCheck_969_ == 0)
{
lean_object* v_unused_970_; lean_object* v_unused_971_; 
v_unused_970_ = lean_ctor_get(v_dt_944_, 3);
lean_dec(v_unused_970_);
v_unused_971_ = lean_ctor_get(v_dt_944_, 0);
lean_dec(v_unused_971_);
v___x_949_ = v_dt_944_;
v_isShared_950_ = v_isSharedCheck_969_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_rules_947_);
lean_inc(v_timestamp_946_);
lean_dec(v_dt_944_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_969_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v_second_951_; lean_object* v_nano_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v_tz_963_; lean_object* v___f_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
v_second_951_ = lean_ctor_get(v_timestamp_946_, 0);
lean_inc(v_second_951_);
v_nano_952_ = lean_ctor_get(v_timestamp_946_, 1);
lean_inc(v_nano_952_);
lean_dec_ref(v_timestamp_946_);
v___x_953_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_954_ = lean_int_mul(v_minutes_945_, v___x_953_);
v___x_955_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_956_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_957_ = lean_int_mul(v_second_951_, v___x_956_);
lean_dec(v_second_951_);
v___x_958_ = lean_int_add(v___x_957_, v_nano_952_);
lean_dec(v_nano_952_);
lean_dec(v___x_957_);
v___x_959_ = lean_int_mul(v___x_954_, v___x_956_);
lean_dec(v___x_954_);
v___x_960_ = lean_int_add(v___x_959_, v___x_955_);
lean_dec(v___x_959_);
v___x_961_ = lean_int_add(v___x_958_, v___x_960_);
lean_dec(v___x_960_);
lean_dec(v___x_958_);
v___x_962_ = l_Std_Time_Duration_ofNanoseconds(v___x_961_);
lean_dec(v___x_961_);
lean_inc_ref(v_rules_947_);
v_tz_963_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_947_, v___x_962_);
lean_inc_ref(v___x_962_);
lean_inc_ref(v_tz_963_);
v___f_964_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_964_, 0, v_tz_963_);
lean_closure_set(v___f_964_, 1, v___x_962_);
lean_closure_set(v___f_964_, 2, v___x_956_);
lean_closure_set(v___f_964_, 3, v___x_955_);
v___x_965_ = lean_mk_thunk(v___f_964_);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 3, v_tz_963_);
lean_ctor_set(v___x_949_, 1, v___x_962_);
lean_ctor_set(v___x_949_, 0, v___x_965_);
v___x_967_ = v___x_949_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_rules_947_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_tz_963_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object* v_dt_972_, lean_object* v_minutes_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Std_Time_DateTime_addMinutes(v_dt_972_, v_minutes_973_);
lean_dec(v_minutes_973_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object* v_dt_975_, lean_object* v_minutes_976_){
_start:
{
lean_object* v_timestamp_977_; lean_object* v_rules_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1002_; 
v_timestamp_977_ = lean_ctor_get(v_dt_975_, 1);
v_rules_978_ = lean_ctor_get(v_dt_975_, 2);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_dt_975_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; lean_object* v_unused_1004_; 
v_unused_1003_ = lean_ctor_get(v_dt_975_, 3);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_dt_975_, 0);
lean_dec(v_unused_1004_);
v___x_980_ = v_dt_975_;
v_isShared_981_ = v_isSharedCheck_1002_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_rules_978_);
lean_inc(v_timestamp_977_);
lean_dec(v_dt_975_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1002_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_second_982_; lean_object* v_nano_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v_tz_996_; lean_object* v___f_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v_second_982_ = lean_ctor_get(v_timestamp_977_, 0);
lean_inc(v_second_982_);
v_nano_983_ = lean_ctor_get(v_timestamp_977_, 1);
lean_inc(v_nano_983_);
lean_dec_ref(v_timestamp_977_);
v___x_984_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_985_ = lean_int_mul(v_minutes_976_, v___x_984_);
v___x_986_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_987_ = lean_int_neg(v___x_985_);
lean_dec(v___x_985_);
v___x_988_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_989_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_990_ = lean_int_mul(v_second_982_, v___x_989_);
lean_dec(v_second_982_);
v___x_991_ = lean_int_add(v___x_990_, v_nano_983_);
lean_dec(v_nano_983_);
lean_dec(v___x_990_);
v___x_992_ = lean_int_mul(v___x_987_, v___x_989_);
lean_dec(v___x_987_);
v___x_993_ = lean_int_add(v___x_992_, v___x_988_);
lean_dec(v___x_992_);
v___x_994_ = lean_int_add(v___x_991_, v___x_993_);
lean_dec(v___x_993_);
lean_dec(v___x_991_);
v___x_995_ = l_Std_Time_Duration_ofNanoseconds(v___x_994_);
lean_dec(v___x_994_);
lean_inc_ref(v_rules_978_);
v_tz_996_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_978_, v___x_995_);
lean_inc_ref(v___x_995_);
lean_inc_ref(v_tz_996_);
v___f_997_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_997_, 0, v_tz_996_);
lean_closure_set(v___f_997_, 1, v___x_995_);
lean_closure_set(v___f_997_, 2, v___x_989_);
lean_closure_set(v___f_997_, 3, v___x_986_);
v___x_998_ = lean_mk_thunk(v___f_997_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 3, v_tz_996_);
lean_ctor_set(v___x_980_, 1, v___x_995_);
lean_ctor_set(v___x_980_, 0, v___x_998_);
v___x_1000_ = v___x_980_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_rules_978_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_tz_996_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object* v_dt_1005_, lean_object* v_minutes_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_Time_DateTime_subMinutes(v_dt_1005_, v_minutes_1006_);
lean_dec(v_minutes_1006_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0(lean_object* v_tz_1008_, lean_object* v___x_1009_, lean_object* v___x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v_offset_1012_; lean_object* v_second_1013_; lean_object* v_nano_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v_offset_1012_ = lean_ctor_get(v_tz_1008_, 0);
v_second_1013_ = lean_ctor_get(v___x_1009_, 0);
v_nano_1014_ = lean_ctor_get(v___x_1009_, 1);
v___x_1015_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1016_ = lean_int_mul(v_second_1013_, v___x_1010_);
v___x_1017_ = lean_int_add(v___x_1016_, v_nano_1014_);
lean_dec(v___x_1016_);
v___x_1018_ = lean_int_mul(v_offset_1012_, v___x_1010_);
v___x_1019_ = lean_int_add(v___x_1018_, v___x_1015_);
lean_dec(v___x_1018_);
v___x_1020_ = lean_int_add(v___x_1017_, v___x_1019_);
lean_dec(v___x_1019_);
lean_dec(v___x_1017_);
v___x_1021_ = l_Std_Time_Duration_ofNanoseconds(v___x_1020_);
lean_dec(v___x_1020_);
v___x_1022_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(lean_object* v_tz_1023_, lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Std_Time_DateTime_addMilliseconds___lam__0(v_tz_1023_, v___x_1024_, v___x_1025_, v_x_1026_);
lean_dec(v___x_1025_);
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_tz_1023_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object* v_dt_1028_, lean_object* v_milliseconds_1029_){
_start:
{
lean_object* v_timestamp_1030_; lean_object* v_rules_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1055_; 
v_timestamp_1030_ = lean_ctor_get(v_dt_1028_, 1);
v_rules_1031_ = lean_ctor_get(v_dt_1028_, 2);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_dt_1028_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; lean_object* v_unused_1057_; 
v_unused_1056_ = lean_ctor_get(v_dt_1028_, 3);
lean_dec(v_unused_1056_);
v_unused_1057_ = lean_ctor_get(v_dt_1028_, 0);
lean_dec(v_unused_1057_);
v___x_1033_ = v_dt_1028_;
v_isShared_1034_ = v_isSharedCheck_1055_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_rules_1031_);
lean_inc(v_timestamp_1030_);
lean_dec(v_dt_1028_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1055_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_second_1035_; lean_object* v_nano_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_second_1040_; lean_object* v_nano_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v_tz_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v_second_1035_ = lean_ctor_get(v_timestamp_1030_, 0);
lean_inc(v_second_1035_);
v_nano_1036_ = lean_ctor_get(v_timestamp_1030_, 1);
lean_inc(v_nano_1036_);
lean_dec_ref(v_timestamp_1030_);
v___x_1037_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1038_ = lean_int_mul(v_milliseconds_1029_, v___x_1037_);
v___x_1039_ = l_Std_Time_Duration_ofNanoseconds(v___x_1038_);
lean_dec(v___x_1038_);
v_second_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_second_1040_);
v_nano_1041_ = lean_ctor_get(v___x_1039_, 1);
lean_inc(v_nano_1041_);
lean_dec_ref(v___x_1039_);
v___x_1042_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1043_ = lean_int_mul(v_second_1035_, v___x_1042_);
lean_dec(v_second_1035_);
v___x_1044_ = lean_int_add(v___x_1043_, v_nano_1036_);
lean_dec(v_nano_1036_);
lean_dec(v___x_1043_);
v___x_1045_ = lean_int_mul(v_second_1040_, v___x_1042_);
lean_dec(v_second_1040_);
v___x_1046_ = lean_int_add(v___x_1045_, v_nano_1041_);
lean_dec(v_nano_1041_);
lean_dec(v___x_1045_);
v___x_1047_ = lean_int_add(v___x_1044_, v___x_1046_);
lean_dec(v___x_1046_);
lean_dec(v___x_1044_);
v___x_1048_ = l_Std_Time_Duration_ofNanoseconds(v___x_1047_);
lean_dec(v___x_1047_);
lean_inc_ref(v_rules_1031_);
v_tz_1049_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1031_, v___x_1048_);
lean_inc_ref(v___x_1048_);
lean_inc_ref(v_tz_1049_);
v___f_1050_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1050_, 0, v_tz_1049_);
lean_closure_set(v___f_1050_, 1, v___x_1048_);
lean_closure_set(v___f_1050_, 2, v___x_1042_);
v___x_1051_ = lean_mk_thunk(v___f_1050_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 3, v_tz_1049_);
lean_ctor_set(v___x_1033_, 1, v___x_1048_);
lean_ctor_set(v___x_1033_, 0, v___x_1051_);
v___x_1053_ = v___x_1033_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_rules_1031_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_tz_1049_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object* v_dt_1058_, lean_object* v_milliseconds_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_Time_DateTime_addMilliseconds(v_dt_1058_, v_milliseconds_1059_);
lean_dec(v_milliseconds_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object* v_dt_1061_, lean_object* v_milliseconds_1062_){
_start:
{
lean_object* v_timestamp_1063_; lean_object* v_rules_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1090_; 
v_timestamp_1063_ = lean_ctor_get(v_dt_1061_, 1);
v_rules_1064_ = lean_ctor_get(v_dt_1061_, 2);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_dt_1061_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; lean_object* v_unused_1092_; 
v_unused_1091_ = lean_ctor_get(v_dt_1061_, 3);
lean_dec(v_unused_1091_);
v_unused_1092_ = lean_ctor_get(v_dt_1061_, 0);
lean_dec(v_unused_1092_);
v___x_1066_ = v_dt_1061_;
v_isShared_1067_ = v_isSharedCheck_1090_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_rules_1064_);
lean_inc(v_timestamp_1063_);
lean_dec(v_dt_1061_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1090_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v_second_1071_; lean_object* v_nano_1072_; lean_object* v_second_1073_; lean_object* v_nano_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_tz_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___x_1088_; 
v___x_1068_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1069_ = lean_int_mul(v_milliseconds_1062_, v___x_1068_);
v___x_1070_ = l_Std_Time_Duration_ofNanoseconds(v___x_1069_);
lean_dec(v___x_1069_);
v_second_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_second_1071_);
v_nano_1072_ = lean_ctor_get(v___x_1070_, 1);
lean_inc(v_nano_1072_);
lean_dec_ref(v___x_1070_);
v_second_1073_ = lean_ctor_get(v_timestamp_1063_, 0);
lean_inc(v_second_1073_);
v_nano_1074_ = lean_ctor_get(v_timestamp_1063_, 1);
lean_inc(v_nano_1074_);
lean_dec_ref(v_timestamp_1063_);
v___x_1075_ = lean_int_neg(v_second_1071_);
lean_dec(v_second_1071_);
v___x_1076_ = lean_int_neg(v_nano_1072_);
lean_dec(v_nano_1072_);
v___x_1077_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1078_ = lean_int_mul(v_second_1073_, v___x_1077_);
lean_dec(v_second_1073_);
v___x_1079_ = lean_int_add(v___x_1078_, v_nano_1074_);
lean_dec(v_nano_1074_);
lean_dec(v___x_1078_);
v___x_1080_ = lean_int_mul(v___x_1075_, v___x_1077_);
lean_dec(v___x_1075_);
v___x_1081_ = lean_int_add(v___x_1080_, v___x_1076_);
lean_dec(v___x_1076_);
lean_dec(v___x_1080_);
v___x_1082_ = lean_int_add(v___x_1079_, v___x_1081_);
lean_dec(v___x_1081_);
lean_dec(v___x_1079_);
v___x_1083_ = l_Std_Time_Duration_ofNanoseconds(v___x_1082_);
lean_dec(v___x_1082_);
lean_inc_ref(v_rules_1064_);
v_tz_1084_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1064_, v___x_1083_);
lean_inc_ref(v___x_1083_);
lean_inc_ref(v_tz_1084_);
v___f_1085_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1085_, 0, v_tz_1084_);
lean_closure_set(v___f_1085_, 1, v___x_1083_);
lean_closure_set(v___f_1085_, 2, v___x_1077_);
v___x_1086_ = lean_mk_thunk(v___f_1085_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 3, v_tz_1084_);
lean_ctor_set(v___x_1066_, 1, v___x_1083_);
lean_ctor_set(v___x_1066_, 0, v___x_1086_);
v___x_1088_ = v___x_1066_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v___x_1086_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_rules_1064_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_tz_1084_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object* v_dt_1093_, lean_object* v_milliseconds_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l_Std_Time_DateTime_subMilliseconds(v_dt_1093_, v_milliseconds_1094_);
lean_dec(v_milliseconds_1094_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object* v_dt_1096_, lean_object* v_seconds_1097_){
_start:
{
lean_object* v_timestamp_1098_; lean_object* v_rules_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1119_; 
v_timestamp_1098_ = lean_ctor_get(v_dt_1096_, 1);
v_rules_1099_ = lean_ctor_get(v_dt_1096_, 2);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_dt_1096_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; lean_object* v_unused_1121_; 
v_unused_1120_ = lean_ctor_get(v_dt_1096_, 3);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_dt_1096_, 0);
lean_dec(v_unused_1121_);
v___x_1101_ = v_dt_1096_;
v_isShared_1102_ = v_isSharedCheck_1119_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_rules_1099_);
lean_inc(v_timestamp_1098_);
lean_dec(v_dt_1096_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1119_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v_second_1103_; lean_object* v_nano_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_tz_1113_; lean_object* v___f_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v_second_1103_ = lean_ctor_get(v_timestamp_1098_, 0);
lean_inc(v_second_1103_);
v_nano_1104_ = lean_ctor_get(v_timestamp_1098_, 1);
lean_inc(v_nano_1104_);
lean_dec_ref(v_timestamp_1098_);
v___x_1105_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1106_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1107_ = lean_int_mul(v_second_1103_, v___x_1106_);
lean_dec(v_second_1103_);
v___x_1108_ = lean_int_add(v___x_1107_, v_nano_1104_);
lean_dec(v_nano_1104_);
lean_dec(v___x_1107_);
v___x_1109_ = lean_int_mul(v_seconds_1097_, v___x_1106_);
v___x_1110_ = lean_int_add(v___x_1109_, v___x_1105_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_int_add(v___x_1108_, v___x_1110_);
lean_dec(v___x_1110_);
lean_dec(v___x_1108_);
v___x_1112_ = l_Std_Time_Duration_ofNanoseconds(v___x_1111_);
lean_dec(v___x_1111_);
lean_inc_ref(v_rules_1099_);
v_tz_1113_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1099_, v___x_1112_);
lean_inc_ref(v___x_1112_);
lean_inc_ref(v_tz_1113_);
v___f_1114_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1114_, 0, v_tz_1113_);
lean_closure_set(v___f_1114_, 1, v___x_1112_);
lean_closure_set(v___f_1114_, 2, v___x_1106_);
lean_closure_set(v___f_1114_, 3, v___x_1105_);
v___x_1115_ = lean_mk_thunk(v___f_1114_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 3, v_tz_1113_);
lean_ctor_set(v___x_1101_, 1, v___x_1112_);
lean_ctor_set(v___x_1101_, 0, v___x_1115_);
v___x_1117_ = v___x_1101_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v_rules_1099_);
lean_ctor_set(v_reuseFailAlloc_1118_, 3, v_tz_1113_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object* v_dt_1122_, lean_object* v_seconds_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Std_Time_DateTime_addSeconds(v_dt_1122_, v_seconds_1123_);
lean_dec(v_seconds_1123_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object* v_dt_1125_, lean_object* v_seconds_1126_){
_start:
{
lean_object* v_timestamp_1127_; lean_object* v_rules_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1150_; 
v_timestamp_1127_ = lean_ctor_get(v_dt_1125_, 1);
v_rules_1128_ = lean_ctor_get(v_dt_1125_, 2);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_dt_1125_);
if (v_isSharedCheck_1150_ == 0)
{
lean_object* v_unused_1151_; lean_object* v_unused_1152_; 
v_unused_1151_ = lean_ctor_get(v_dt_1125_, 3);
lean_dec(v_unused_1151_);
v_unused_1152_ = lean_ctor_get(v_dt_1125_, 0);
lean_dec(v_unused_1152_);
v___x_1130_ = v_dt_1125_;
v_isShared_1131_ = v_isSharedCheck_1150_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_rules_1128_);
lean_inc(v_timestamp_1127_);
lean_dec(v_dt_1125_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1150_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v_second_1132_; lean_object* v_nano_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_tz_1144_; lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v_second_1132_ = lean_ctor_get(v_timestamp_1127_, 0);
lean_inc(v_second_1132_);
v_nano_1133_ = lean_ctor_get(v_timestamp_1127_, 1);
lean_inc(v_nano_1133_);
lean_dec_ref(v_timestamp_1127_);
v___x_1134_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1135_ = lean_int_neg(v_seconds_1126_);
v___x_1136_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1137_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1138_ = lean_int_mul(v_second_1132_, v___x_1137_);
lean_dec(v_second_1132_);
v___x_1139_ = lean_int_add(v___x_1138_, v_nano_1133_);
lean_dec(v_nano_1133_);
lean_dec(v___x_1138_);
v___x_1140_ = lean_int_mul(v___x_1135_, v___x_1137_);
lean_dec(v___x_1135_);
v___x_1141_ = lean_int_add(v___x_1140_, v___x_1136_);
lean_dec(v___x_1140_);
v___x_1142_ = lean_int_add(v___x_1139_, v___x_1141_);
lean_dec(v___x_1141_);
lean_dec(v___x_1139_);
v___x_1143_ = l_Std_Time_Duration_ofNanoseconds(v___x_1142_);
lean_dec(v___x_1142_);
lean_inc_ref(v_rules_1128_);
v_tz_1144_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1128_, v___x_1143_);
lean_inc_ref(v___x_1143_);
lean_inc_ref(v_tz_1144_);
v___f_1145_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1145_, 0, v_tz_1144_);
lean_closure_set(v___f_1145_, 1, v___x_1143_);
lean_closure_set(v___f_1145_, 2, v___x_1137_);
lean_closure_set(v___f_1145_, 3, v___x_1134_);
v___x_1146_ = lean_mk_thunk(v___f_1145_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 3, v_tz_1144_);
lean_ctor_set(v___x_1130_, 1, v___x_1143_);
lean_ctor_set(v___x_1130_, 0, v___x_1146_);
v___x_1148_ = v___x_1130_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1149_, 2, v_rules_1128_);
lean_ctor_set(v_reuseFailAlloc_1149_, 3, v_tz_1144_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object* v_dt_1153_, lean_object* v_seconds_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Std_Time_DateTime_subSeconds(v_dt_1153_, v_seconds_1154_);
lean_dec(v_seconds_1154_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object* v_dt_1156_, lean_object* v_nanoseconds_1157_){
_start:
{
lean_object* v_timestamp_1158_; lean_object* v_rules_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1181_; 
v_timestamp_1158_ = lean_ctor_get(v_dt_1156_, 1);
v_rules_1159_ = lean_ctor_get(v_dt_1156_, 2);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_dt_1156_);
if (v_isSharedCheck_1181_ == 0)
{
lean_object* v_unused_1182_; lean_object* v_unused_1183_; 
v_unused_1182_ = lean_ctor_get(v_dt_1156_, 3);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_dt_1156_, 0);
lean_dec(v_unused_1183_);
v___x_1161_ = v_dt_1156_;
v_isShared_1162_ = v_isSharedCheck_1181_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_rules_1159_);
lean_inc(v_timestamp_1158_);
lean_dec(v_dt_1156_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1181_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v_second_1163_; lean_object* v_nano_1164_; lean_object* v___x_1165_; lean_object* v_second_1166_; lean_object* v_nano_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v_tz_1175_; lean_object* v___f_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v_second_1163_ = lean_ctor_get(v_timestamp_1158_, 0);
lean_inc(v_second_1163_);
v_nano_1164_ = lean_ctor_get(v_timestamp_1158_, 1);
lean_inc(v_nano_1164_);
lean_dec_ref(v_timestamp_1158_);
v___x_1165_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1157_);
v_second_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_second_1166_);
v_nano_1167_ = lean_ctor_get(v___x_1165_, 1);
lean_inc(v_nano_1167_);
lean_dec_ref(v___x_1165_);
v___x_1168_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1169_ = lean_int_mul(v_second_1163_, v___x_1168_);
lean_dec(v_second_1163_);
v___x_1170_ = lean_int_add(v___x_1169_, v_nano_1164_);
lean_dec(v_nano_1164_);
lean_dec(v___x_1169_);
v___x_1171_ = lean_int_mul(v_second_1166_, v___x_1168_);
lean_dec(v_second_1166_);
v___x_1172_ = lean_int_add(v___x_1171_, v_nano_1167_);
lean_dec(v_nano_1167_);
lean_dec(v___x_1171_);
v___x_1173_ = lean_int_add(v___x_1170_, v___x_1172_);
lean_dec(v___x_1172_);
lean_dec(v___x_1170_);
v___x_1174_ = l_Std_Time_Duration_ofNanoseconds(v___x_1173_);
lean_dec(v___x_1173_);
lean_inc_ref(v_rules_1159_);
v_tz_1175_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1159_, v___x_1174_);
lean_inc_ref(v___x_1174_);
lean_inc_ref(v_tz_1175_);
v___f_1176_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1176_, 0, v_tz_1175_);
lean_closure_set(v___f_1176_, 1, v___x_1174_);
lean_closure_set(v___f_1176_, 2, v___x_1168_);
v___x_1177_ = lean_mk_thunk(v___f_1176_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 3, v_tz_1175_);
lean_ctor_set(v___x_1161_, 1, v___x_1174_);
lean_ctor_set(v___x_1161_, 0, v___x_1177_);
v___x_1179_ = v___x_1161_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1180_, 2, v_rules_1159_);
lean_ctor_set(v_reuseFailAlloc_1180_, 3, v_tz_1175_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object* v_dt_1184_, lean_object* v_nanoseconds_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Std_Time_DateTime_addNanoseconds(v_dt_1184_, v_nanoseconds_1185_);
lean_dec(v_nanoseconds_1185_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object* v_dt_1187_, lean_object* v_nanoseconds_1188_){
_start:
{
lean_object* v_timestamp_1189_; lean_object* v_rules_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1214_; 
v_timestamp_1189_ = lean_ctor_get(v_dt_1187_, 1);
v_rules_1190_ = lean_ctor_get(v_dt_1187_, 2);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_dt_1187_);
if (v_isSharedCheck_1214_ == 0)
{
lean_object* v_unused_1215_; lean_object* v_unused_1216_; 
v_unused_1215_ = lean_ctor_get(v_dt_1187_, 3);
lean_dec(v_unused_1215_);
v_unused_1216_ = lean_ctor_get(v_dt_1187_, 0);
lean_dec(v_unused_1216_);
v___x_1192_ = v_dt_1187_;
v_isShared_1193_ = v_isSharedCheck_1214_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_rules_1190_);
lean_inc(v_timestamp_1189_);
lean_dec(v_dt_1187_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1214_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v_second_1195_; lean_object* v_nano_1196_; lean_object* v_second_1197_; lean_object* v_nano_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v_tz_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1194_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1188_);
v_second_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_second_1195_);
v_nano_1196_ = lean_ctor_get(v___x_1194_, 1);
lean_inc(v_nano_1196_);
lean_dec_ref(v___x_1194_);
v_second_1197_ = lean_ctor_get(v_timestamp_1189_, 0);
lean_inc(v_second_1197_);
v_nano_1198_ = lean_ctor_get(v_timestamp_1189_, 1);
lean_inc(v_nano_1198_);
lean_dec_ref(v_timestamp_1189_);
v___x_1199_ = lean_int_neg(v_second_1195_);
lean_dec(v_second_1195_);
v___x_1200_ = lean_int_neg(v_nano_1196_);
lean_dec(v_nano_1196_);
v___x_1201_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1202_ = lean_int_mul(v_second_1197_, v___x_1201_);
lean_dec(v_second_1197_);
v___x_1203_ = lean_int_add(v___x_1202_, v_nano_1198_);
lean_dec(v_nano_1198_);
lean_dec(v___x_1202_);
v___x_1204_ = lean_int_mul(v___x_1199_, v___x_1201_);
lean_dec(v___x_1199_);
v___x_1205_ = lean_int_add(v___x_1204_, v___x_1200_);
lean_dec(v___x_1200_);
lean_dec(v___x_1204_);
v___x_1206_ = lean_int_add(v___x_1203_, v___x_1205_);
lean_dec(v___x_1205_);
lean_dec(v___x_1203_);
v___x_1207_ = l_Std_Time_Duration_ofNanoseconds(v___x_1206_);
lean_dec(v___x_1206_);
lean_inc_ref(v_rules_1190_);
v_tz_1208_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1190_, v___x_1207_);
lean_inc_ref(v___x_1207_);
lean_inc_ref(v_tz_1208_);
v___f_1209_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1209_, 0, v_tz_1208_);
lean_closure_set(v___f_1209_, 1, v___x_1207_);
lean_closure_set(v___f_1209_, 2, v___x_1201_);
v___x_1210_ = lean_mk_thunk(v___f_1209_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 3, v_tz_1208_);
lean_ctor_set(v___x_1192_, 1, v___x_1207_);
lean_ctor_set(v___x_1192_, 0, v___x_1210_);
v___x_1212_ = v___x_1192_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_rules_1190_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_tz_1208_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object* v_dt_1217_, lean_object* v_nanoseconds_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_Time_DateTime_subNanoseconds(v_dt_1217_, v_nanoseconds_1218_);
lean_dec(v_nanoseconds_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_era(lean_object* v_date_1220_){
_start:
{
lean_object* v_date_1221_; lean_object* v___x_1222_; lean_object* v_date_1223_; lean_object* v_year_1224_; uint8_t v___x_1225_; 
v_date_1221_ = lean_ctor_get(v_date_1220_, 0);
v___x_1222_ = lean_thunk_get_own(v_date_1221_);
v_date_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_date_1223_);
lean_dec(v___x_1222_);
v_year_1224_ = lean_ctor_get(v_date_1223_, 0);
lean_inc(v_year_1224_);
lean_dec_ref(v_date_1223_);
v___x_1225_ = l_Std_Time_Year_Offset_era(v_year_1224_);
lean_dec(v_year_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object* v_date_1226_){
_start:
{
uint8_t v_res_1227_; lean_object* v_r_1228_; 
v_res_1227_ = l_Std_Time_DateTime_era(v_date_1226_);
lean_dec_ref(v_date_1226_);
v_r_1228_ = lean_box(v_res_1227_);
return v_r_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday(lean_object* v_dt_1229_, uint8_t v_desiredWeekday_1230_){
_start:
{
lean_object* v_date_1231_; lean_object* v_rules_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1258_; 
v_date_1231_ = lean_ctor_get(v_dt_1229_, 0);
v_rules_1232_ = lean_ctor_get(v_dt_1229_, 2);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_dt_1229_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; lean_object* v_unused_1260_; 
v_unused_1259_ = lean_ctor_get(v_dt_1229_, 3);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v_dt_1229_, 1);
lean_dec(v_unused_1260_);
v___x_1234_ = v_dt_1229_;
v_isShared_1235_ = v_isSharedCheck_1258_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_rules_1232_);
lean_inc(v_date_1231_);
lean_dec(v_dt_1229_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1258_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_date_1236_; lean_object* v___x_1237_; lean_object* v_wt_1238_; lean_object* v_ltt_1239_; lean_object* v_tz_1240_; lean_object* v_offset_1241_; lean_object* v_second_1242_; lean_object* v_nano_1243_; lean_object* v___f_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v_date_1236_ = lean_thunk_get_own(v_date_1231_);
lean_dec_ref(v_date_1231_);
v___x_1237_ = l_Std_Time_PlainDateTime_withWeekday(v_date_1236_, v_desiredWeekday_1230_);
lean_inc_ref(v___x_1237_);
v_wt_1238_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1237_);
lean_inc_ref(v_rules_1232_);
v_ltt_1239_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1232_, v_wt_1238_);
v_tz_1240_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1239_);
lean_dec_ref(v_ltt_1239_);
v_offset_1241_ = lean_ctor_get(v_tz_1240_, 0);
lean_inc(v_offset_1241_);
v_second_1242_ = lean_ctor_get(v_wt_1238_, 0);
lean_inc(v_second_1242_);
v_nano_1243_ = lean_ctor_get(v_wt_1238_, 1);
lean_inc(v_nano_1243_);
lean_dec_ref(v_wt_1238_);
v___f_1244_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1244_, 0, v___x_1237_);
v___x_1245_ = lean_mk_thunk(v___f_1244_);
v___x_1246_ = lean_int_neg(v_offset_1241_);
lean_dec(v_offset_1241_);
v___x_1247_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1248_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1249_ = lean_int_mul(v_second_1242_, v___x_1248_);
lean_dec(v_second_1242_);
v___x_1250_ = lean_int_add(v___x_1249_, v_nano_1243_);
lean_dec(v_nano_1243_);
lean_dec(v___x_1249_);
v___x_1251_ = lean_int_mul(v___x_1246_, v___x_1248_);
lean_dec(v___x_1246_);
v___x_1252_ = lean_int_add(v___x_1251_, v___x_1247_);
lean_dec(v___x_1251_);
v___x_1253_ = lean_int_add(v___x_1250_, v___x_1252_);
lean_dec(v___x_1252_);
lean_dec(v___x_1250_);
v___x_1254_ = l_Std_Time_Duration_ofNanoseconds(v___x_1253_);
lean_dec(v___x_1253_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 3, v_tz_1240_);
lean_ctor_set(v___x_1234_, 1, v___x_1254_);
lean_ctor_set(v___x_1234_, 0, v___x_1245_);
v___x_1256_ = v___x_1234_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_rules_1232_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_tz_1240_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object* v_dt_1261_, lean_object* v_desiredWeekday_1262_){
_start:
{
uint8_t v_desiredWeekday_boxed_1263_; lean_object* v_res_1264_; 
v_desiredWeekday_boxed_1263_ = lean_unbox(v_desiredWeekday_1262_);
v_res_1264_ = l_Std_Time_DateTime_withWeekday(v_dt_1261_, v_desiredWeekday_boxed_1263_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object* v_dt_1265_, lean_object* v_days_1266_){
_start:
{
lean_object* v_date_1267_; lean_object* v_rules_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1335_; 
v_date_1267_ = lean_ctor_get(v_dt_1265_, 0);
v_rules_1268_ = lean_ctor_get(v_dt_1265_, 2);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_dt_1265_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; lean_object* v_unused_1337_; 
v_unused_1336_ = lean_ctor_get(v_dt_1265_, 3);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_dt_1265_, 1);
lean_dec(v_unused_1337_);
v___x_1270_ = v_dt_1265_;
v_isShared_1271_ = v_isSharedCheck_1335_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_rules_1268_);
lean_inc(v_date_1267_);
lean_dec(v_dt_1265_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1335_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_date_1272_; lean_object* v___y_1274_; lean_object* v_date_1304_; lean_object* v_year_1305_; lean_object* v_month_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1333_; 
v_date_1272_ = lean_thunk_get_own(v_date_1267_);
lean_dec_ref(v_date_1267_);
v_date_1304_ = lean_ctor_get(v_date_1272_, 0);
lean_inc_ref(v_date_1304_);
v_year_1305_ = lean_ctor_get(v_date_1304_, 0);
v_month_1306_ = lean_ctor_get(v_date_1304_, 1);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_date_1304_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_date_1304_, 2);
lean_dec(v_unused_1334_);
v___x_1308_ = v_date_1304_;
v_isShared_1309_ = v_isSharedCheck_1333_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_month_1306_);
lean_inc(v_year_1305_);
lean_dec(v_date_1304_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1333_;
goto v_resetjp_1307_;
}
v___jp_1273_:
{
lean_object* v_time_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1302_; 
v_time_1275_ = lean_ctor_get(v_date_1272_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_date_1272_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v_date_1272_, 0);
lean_dec(v_unused_1303_);
v___x_1277_ = v_date_1272_;
v_isShared_1278_ = v_isSharedCheck_1302_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_time_1275_);
lean_dec(v_date_1272_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1302_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
lean_ctor_set(v___x_1277_, 0, v___y_1274_);
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___y_1274_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_time_1275_);
v___x_1280_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v_wt_1281_; lean_object* v_ltt_1282_; lean_object* v_tz_1283_; lean_object* v_offset_1284_; lean_object* v_second_1285_; lean_object* v_nano_1286_; lean_object* v___f_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
lean_inc_ref(v___x_1280_);
v_wt_1281_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1280_);
lean_inc_ref(v_rules_1268_);
v_ltt_1282_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1268_, v_wt_1281_);
v_tz_1283_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1282_);
lean_dec_ref(v_ltt_1282_);
v_offset_1284_ = lean_ctor_get(v_tz_1283_, 0);
lean_inc(v_offset_1284_);
v_second_1285_ = lean_ctor_get(v_wt_1281_, 0);
lean_inc(v_second_1285_);
v_nano_1286_ = lean_ctor_get(v_wt_1281_, 1);
lean_inc(v_nano_1286_);
lean_dec_ref(v_wt_1281_);
v___f_1287_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1287_, 0, v___x_1280_);
v___x_1288_ = lean_mk_thunk(v___f_1287_);
v___x_1289_ = lean_int_neg(v_offset_1284_);
lean_dec(v_offset_1284_);
v___x_1290_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1291_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1292_ = lean_int_mul(v_second_1285_, v___x_1291_);
lean_dec(v_second_1285_);
v___x_1293_ = lean_int_add(v___x_1292_, v_nano_1286_);
lean_dec(v_nano_1286_);
lean_dec(v___x_1292_);
v___x_1294_ = lean_int_mul(v___x_1289_, v___x_1291_);
lean_dec(v___x_1289_);
v___x_1295_ = lean_int_add(v___x_1294_, v___x_1290_);
lean_dec(v___x_1294_);
v___x_1296_ = lean_int_add(v___x_1293_, v___x_1295_);
lean_dec(v___x_1295_);
lean_dec(v___x_1293_);
v___x_1297_ = l_Std_Time_Duration_ofNanoseconds(v___x_1296_);
lean_dec(v___x_1296_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 3, v_tz_1283_);
lean_ctor_set(v___x_1270_, 1, v___x_1297_);
lean_ctor_set(v___x_1270_, 0, v___x_1288_);
v___x_1299_ = v___x_1270_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_rules_1268_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v_tz_1283_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
v_resetjp_1307_:
{
uint8_t v___y_1311_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; uint8_t v___y_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1320_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1321_ = lean_int_mod(v_year_1305_, v___x_1320_);
v___x_1322_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1323_ = lean_int_dec_eq(v___x_1321_, v___x_1322_);
lean_dec(v___x_1321_);
v___x_1326_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1327_ = lean_int_mod(v_year_1305_, v___x_1326_);
v___x_1328_ = lean_int_dec_eq(v___x_1327_, v___x_1322_);
lean_dec(v___x_1327_);
if (v___x_1328_ == 0)
{
uint8_t v___x_1329_; 
v___x_1329_ = 1;
v___y_1325_ = v___x_1329_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1330_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1331_ = lean_int_mod(v_year_1305_, v___x_1330_);
v___x_1332_ = lean_int_dec_eq(v___x_1331_, v___x_1322_);
lean_dec(v___x_1331_);
v___y_1325_ = v___x_1332_;
goto v___jp_1324_;
}
v___jp_1310_:
{
lean_object* v_max_1312_; uint8_t v___x_1313_; 
v_max_1312_ = l_Std_Time_Month_Ordinal_days(v___y_1311_, v_month_1306_);
v___x_1313_ = lean_int_dec_lt(v_max_1312_, v_days_1266_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1315_; 
lean_dec(v_max_1312_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 2, v_days_1266_);
v___x_1315_ = v___x_1308_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_year_1305_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_month_1306_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_days_1266_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
v___y_1274_ = v___x_1315_;
goto v___jp_1273_;
}
}
else
{
lean_object* v___x_1318_; 
lean_dec(v_days_1266_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 2, v_max_1312_);
v___x_1318_ = v___x_1308_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_year_1305_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_month_1306_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_max_1312_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
v___y_1274_ = v___x_1318_;
goto v___jp_1273_;
}
}
}
v___jp_1324_:
{
if (v___x_1323_ == 0)
{
v___y_1311_ = v___x_1323_;
goto v___jp_1310_;
}
else
{
v___y_1311_ = v___y_1325_;
goto v___jp_1310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object* v_dt_1338_, lean_object* v_days_1339_){
_start:
{
lean_object* v_date_1340_; lean_object* v_rules_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1378_; 
v_date_1340_ = lean_ctor_get(v_dt_1338_, 0);
v_rules_1341_ = lean_ctor_get(v_dt_1338_, 2);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_dt_1338_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; lean_object* v_unused_1380_; 
v_unused_1379_ = lean_ctor_get(v_dt_1338_, 3);
lean_dec(v_unused_1379_);
v_unused_1380_ = lean_ctor_get(v_dt_1338_, 1);
lean_dec(v_unused_1380_);
v___x_1343_ = v_dt_1338_;
v_isShared_1344_ = v_isSharedCheck_1378_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_rules_1341_);
lean_inc(v_date_1340_);
lean_dec(v_dt_1338_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1378_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_date_1345_; lean_object* v_date_1346_; lean_object* v_time_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1377_; 
v_date_1345_ = lean_thunk_get_own(v_date_1340_);
lean_dec_ref(v_date_1340_);
v_date_1346_ = lean_ctor_get(v_date_1345_, 0);
v_time_1347_ = lean_ctor_get(v_date_1345_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_date_1345_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1349_ = v_date_1345_;
v_isShared_1350_ = v_isSharedCheck_1377_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_time_1347_);
lean_inc(v_date_1346_);
lean_dec(v_date_1345_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1377_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_year_1351_; lean_object* v_month_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v_year_1351_ = lean_ctor_get(v_date_1346_, 0);
lean_inc(v_year_1351_);
v_month_1352_ = lean_ctor_get(v_date_1346_, 1);
lean_inc(v_month_1352_);
lean_dec_ref(v_date_1346_);
v___x_1353_ = l_Std_Time_PlainDate_rollOver(v_year_1351_, v_month_1352_, v_days_1339_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v___x_1353_);
v___x_1355_ = v___x_1349_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_time_1347_);
v___x_1355_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v_wt_1356_; lean_object* v_ltt_1357_; lean_object* v_tz_1358_; lean_object* v_offset_1359_; lean_object* v_second_1360_; lean_object* v_nano_1361_; lean_object* v___f_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
lean_inc_ref(v___x_1355_);
v_wt_1356_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1355_);
lean_inc_ref(v_rules_1341_);
v_ltt_1357_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1341_, v_wt_1356_);
v_tz_1358_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1357_);
lean_dec_ref(v_ltt_1357_);
v_offset_1359_ = lean_ctor_get(v_tz_1358_, 0);
lean_inc(v_offset_1359_);
v_second_1360_ = lean_ctor_get(v_wt_1356_, 0);
lean_inc(v_second_1360_);
v_nano_1361_ = lean_ctor_get(v_wt_1356_, 1);
lean_inc(v_nano_1361_);
lean_dec_ref(v_wt_1356_);
v___f_1362_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1362_, 0, v___x_1355_);
v___x_1363_ = lean_mk_thunk(v___f_1362_);
v___x_1364_ = lean_int_neg(v_offset_1359_);
lean_dec(v_offset_1359_);
v___x_1365_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1366_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1367_ = lean_int_mul(v_second_1360_, v___x_1366_);
lean_dec(v_second_1360_);
v___x_1368_ = lean_int_add(v___x_1367_, v_nano_1361_);
lean_dec(v_nano_1361_);
lean_dec(v___x_1367_);
v___x_1369_ = lean_int_mul(v___x_1364_, v___x_1366_);
lean_dec(v___x_1364_);
v___x_1370_ = lean_int_add(v___x_1369_, v___x_1365_);
lean_dec(v___x_1369_);
v___x_1371_ = lean_int_add(v___x_1368_, v___x_1370_);
lean_dec(v___x_1370_);
lean_dec(v___x_1368_);
v___x_1372_ = l_Std_Time_Duration_ofNanoseconds(v___x_1371_);
lean_dec(v___x_1371_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 3, v_tz_1358_);
lean_ctor_set(v___x_1343_, 1, v___x_1372_);
lean_ctor_set(v___x_1343_, 0, v___x_1363_);
v___x_1374_ = v___x_1343_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_rules_1341_);
lean_ctor_set(v_reuseFailAlloc_1375_, 3, v_tz_1358_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object* v_dt_1381_, lean_object* v_days_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Std_Time_DateTime_withDaysRollOver(v_dt_1381_, v_days_1382_);
lean_dec(v_days_1382_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object* v_dt_1384_, lean_object* v_month_1385_){
_start:
{
lean_object* v_date_1386_; lean_object* v_rules_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1454_; 
v_date_1386_ = lean_ctor_get(v_dt_1384_, 0);
v_rules_1387_ = lean_ctor_get(v_dt_1384_, 2);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_dt_1384_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; lean_object* v_unused_1456_; 
v_unused_1455_ = lean_ctor_get(v_dt_1384_, 3);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_dt_1384_, 1);
lean_dec(v_unused_1456_);
v___x_1389_ = v_dt_1384_;
v_isShared_1390_ = v_isSharedCheck_1454_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_rules_1387_);
lean_inc(v_date_1386_);
lean_dec(v_dt_1384_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1454_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_date_1391_; lean_object* v___y_1393_; lean_object* v_date_1423_; lean_object* v_year_1424_; lean_object* v_day_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1452_; 
v_date_1391_ = lean_thunk_get_own(v_date_1386_);
lean_dec_ref(v_date_1386_);
v_date_1423_ = lean_ctor_get(v_date_1391_, 0);
lean_inc_ref(v_date_1423_);
v_year_1424_ = lean_ctor_get(v_date_1423_, 0);
v_day_1425_ = lean_ctor_get(v_date_1423_, 2);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_date_1423_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_date_1423_, 1);
lean_dec(v_unused_1453_);
v___x_1427_ = v_date_1423_;
v_isShared_1428_ = v_isSharedCheck_1452_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_day_1425_);
lean_inc(v_year_1424_);
lean_dec(v_date_1423_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1452_;
goto v_resetjp_1426_;
}
v___jp_1392_:
{
lean_object* v_time_1394_; lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1421_; 
v_time_1394_ = lean_ctor_get(v_date_1391_, 1);
v_isSharedCheck_1421_ = !lean_is_exclusive(v_date_1391_);
if (v_isSharedCheck_1421_ == 0)
{
lean_object* v_unused_1422_; 
v_unused_1422_ = lean_ctor_get(v_date_1391_, 0);
lean_dec(v_unused_1422_);
v___x_1396_ = v_date_1391_;
v_isShared_1397_ = v_isSharedCheck_1421_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_time_1394_);
lean_dec(v_date_1391_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1421_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v___x_1399_; 
if (v_isShared_1397_ == 0)
{
lean_ctor_set(v___x_1396_, 0, v___y_1393_);
v___x_1399_ = v___x_1396_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___y_1393_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_time_1394_);
v___x_1399_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v_wt_1400_; lean_object* v_ltt_1401_; lean_object* v_tz_1402_; lean_object* v_offset_1403_; lean_object* v_second_1404_; lean_object* v_nano_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_inc_ref(v___x_1399_);
v_wt_1400_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1399_);
lean_inc_ref(v_rules_1387_);
v_ltt_1401_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1387_, v_wt_1400_);
v_tz_1402_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1401_);
lean_dec_ref(v_ltt_1401_);
v_offset_1403_ = lean_ctor_get(v_tz_1402_, 0);
lean_inc(v_offset_1403_);
v_second_1404_ = lean_ctor_get(v_wt_1400_, 0);
lean_inc(v_second_1404_);
v_nano_1405_ = lean_ctor_get(v_wt_1400_, 1);
lean_inc(v_nano_1405_);
lean_dec_ref(v_wt_1400_);
v___f_1406_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1406_, 0, v___x_1399_);
v___x_1407_ = lean_mk_thunk(v___f_1406_);
v___x_1408_ = lean_int_neg(v_offset_1403_);
lean_dec(v_offset_1403_);
v___x_1409_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1410_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1411_ = lean_int_mul(v_second_1404_, v___x_1410_);
lean_dec(v_second_1404_);
v___x_1412_ = lean_int_add(v___x_1411_, v_nano_1405_);
lean_dec(v_nano_1405_);
lean_dec(v___x_1411_);
v___x_1413_ = lean_int_mul(v___x_1408_, v___x_1410_);
lean_dec(v___x_1408_);
v___x_1414_ = lean_int_add(v___x_1413_, v___x_1409_);
lean_dec(v___x_1413_);
v___x_1415_ = lean_int_add(v___x_1412_, v___x_1414_);
lean_dec(v___x_1414_);
lean_dec(v___x_1412_);
v___x_1416_ = l_Std_Time_Duration_ofNanoseconds(v___x_1415_);
lean_dec(v___x_1415_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 3, v_tz_1402_);
lean_ctor_set(v___x_1389_, 1, v___x_1416_);
lean_ctor_set(v___x_1389_, 0, v___x_1407_);
v___x_1418_ = v___x_1389_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1407_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_rules_1387_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v_tz_1402_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
v_resetjp_1426_:
{
uint8_t v___y_1430_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; uint8_t v___y_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1439_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1440_ = lean_int_mod(v_year_1424_, v___x_1439_);
v___x_1441_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1442_ = lean_int_dec_eq(v___x_1440_, v___x_1441_);
lean_dec(v___x_1440_);
v___x_1445_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1446_ = lean_int_mod(v_year_1424_, v___x_1445_);
v___x_1447_ = lean_int_dec_eq(v___x_1446_, v___x_1441_);
lean_dec(v___x_1446_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; 
v___x_1448_ = 1;
v___y_1444_ = v___x_1448_;
goto v___jp_1443_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1450_ = lean_int_mod(v_year_1424_, v___x_1449_);
v___x_1451_ = lean_int_dec_eq(v___x_1450_, v___x_1441_);
lean_dec(v___x_1450_);
v___y_1444_ = v___x_1451_;
goto v___jp_1443_;
}
v___jp_1429_:
{
lean_object* v_max_1431_; uint8_t v___x_1432_; 
v_max_1431_ = l_Std_Time_Month_Ordinal_days(v___y_1430_, v_month_1385_);
v___x_1432_ = lean_int_dec_lt(v_max_1431_, v_day_1425_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1434_; 
lean_dec(v_max_1431_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v_month_1385_);
v___x_1434_ = v___x_1427_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_year_1424_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_month_1385_);
lean_ctor_set(v_reuseFailAlloc_1435_, 2, v_day_1425_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
v___y_1393_ = v___x_1434_;
goto v___jp_1392_;
}
}
else
{
lean_object* v___x_1437_; 
lean_dec(v_day_1425_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 2, v_max_1431_);
lean_ctor_set(v___x_1427_, 1, v_month_1385_);
v___x_1437_ = v___x_1427_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_year_1424_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_month_1385_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_max_1431_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
v___y_1393_ = v___x_1437_;
goto v___jp_1392_;
}
}
}
v___jp_1443_:
{
if (v___x_1442_ == 0)
{
v___y_1430_ = v___x_1442_;
goto v___jp_1429_;
}
else
{
v___y_1430_ = v___y_1444_;
goto v___jp_1429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthRollOver(lean_object* v_dt_1457_, lean_object* v_month_1458_){
_start:
{
lean_object* v_date_1459_; lean_object* v_rules_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1497_; 
v_date_1459_ = lean_ctor_get(v_dt_1457_, 0);
v_rules_1460_ = lean_ctor_get(v_dt_1457_, 2);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_dt_1457_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; lean_object* v_unused_1499_; 
v_unused_1498_ = lean_ctor_get(v_dt_1457_, 3);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_dt_1457_, 1);
lean_dec(v_unused_1499_);
v___x_1462_ = v_dt_1457_;
v_isShared_1463_ = v_isSharedCheck_1497_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_rules_1460_);
lean_inc(v_date_1459_);
lean_dec(v_dt_1457_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1497_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v_date_1464_; lean_object* v_date_1465_; lean_object* v_time_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1496_; 
v_date_1464_ = lean_thunk_get_own(v_date_1459_);
lean_dec_ref(v_date_1459_);
v_date_1465_ = lean_ctor_get(v_date_1464_, 0);
v_time_1466_ = lean_ctor_get(v_date_1464_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_date_1464_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1468_ = v_date_1464_;
v_isShared_1469_ = v_isSharedCheck_1496_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_time_1466_);
lean_inc(v_date_1465_);
lean_dec(v_date_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1496_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v_year_1470_; lean_object* v_day_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
v_year_1470_ = lean_ctor_get(v_date_1465_, 0);
lean_inc(v_year_1470_);
v_day_1471_ = lean_ctor_get(v_date_1465_, 2);
lean_inc(v_day_1471_);
lean_dec_ref(v_date_1465_);
v___x_1472_ = l_Std_Time_PlainDate_rollOver(v_year_1470_, v_month_1458_, v_day_1471_);
lean_dec(v_day_1471_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 0, v___x_1472_);
v___x_1474_ = v___x_1468_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_time_1466_);
v___x_1474_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v_wt_1475_; lean_object* v_ltt_1476_; lean_object* v_tz_1477_; lean_object* v_offset_1478_; lean_object* v_second_1479_; lean_object* v_nano_1480_; lean_object* v___f_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
lean_inc_ref(v___x_1474_);
v_wt_1475_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1474_);
lean_inc_ref(v_rules_1460_);
v_ltt_1476_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1460_, v_wt_1475_);
v_tz_1477_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1476_);
lean_dec_ref(v_ltt_1476_);
v_offset_1478_ = lean_ctor_get(v_tz_1477_, 0);
lean_inc(v_offset_1478_);
v_second_1479_ = lean_ctor_get(v_wt_1475_, 0);
lean_inc(v_second_1479_);
v_nano_1480_ = lean_ctor_get(v_wt_1475_, 1);
lean_inc(v_nano_1480_);
lean_dec_ref(v_wt_1475_);
v___f_1481_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1481_, 0, v___x_1474_);
v___x_1482_ = lean_mk_thunk(v___f_1481_);
v___x_1483_ = lean_int_neg(v_offset_1478_);
lean_dec(v_offset_1478_);
v___x_1484_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1485_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1486_ = lean_int_mul(v_second_1479_, v___x_1485_);
lean_dec(v_second_1479_);
v___x_1487_ = lean_int_add(v___x_1486_, v_nano_1480_);
lean_dec(v_nano_1480_);
lean_dec(v___x_1486_);
v___x_1488_ = lean_int_mul(v___x_1483_, v___x_1485_);
lean_dec(v___x_1483_);
v___x_1489_ = lean_int_add(v___x_1488_, v___x_1484_);
lean_dec(v___x_1488_);
v___x_1490_ = lean_int_add(v___x_1487_, v___x_1489_);
lean_dec(v___x_1489_);
lean_dec(v___x_1487_);
v___x_1491_ = l_Std_Time_Duration_ofNanoseconds(v___x_1490_);
lean_dec(v___x_1490_);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 3, v_tz_1477_);
lean_ctor_set(v___x_1462_, 1, v___x_1491_);
lean_ctor_set(v___x_1462_, 0, v___x_1482_);
v___x_1493_ = v___x_1462_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_rules_1460_);
lean_ctor_set(v_reuseFailAlloc_1494_, 3, v_tz_1477_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearClip(lean_object* v_dt_1500_, lean_object* v_year_1501_){
_start:
{
lean_object* v_date_1502_; lean_object* v_rules_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1570_; 
v_date_1502_ = lean_ctor_get(v_dt_1500_, 0);
v_rules_1503_ = lean_ctor_get(v_dt_1500_, 2);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_dt_1500_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; lean_object* v_unused_1572_; 
v_unused_1571_ = lean_ctor_get(v_dt_1500_, 3);
lean_dec(v_unused_1571_);
v_unused_1572_ = lean_ctor_get(v_dt_1500_, 1);
lean_dec(v_unused_1572_);
v___x_1505_ = v_dt_1500_;
v_isShared_1506_ = v_isSharedCheck_1570_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_rules_1503_);
lean_inc(v_date_1502_);
lean_dec(v_dt_1500_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1570_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_date_1507_; lean_object* v___y_1509_; lean_object* v_date_1539_; lean_object* v_month_1540_; lean_object* v_day_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1568_; 
v_date_1507_ = lean_thunk_get_own(v_date_1502_);
lean_dec_ref(v_date_1502_);
v_date_1539_ = lean_ctor_get(v_date_1507_, 0);
lean_inc_ref(v_date_1539_);
v_month_1540_ = lean_ctor_get(v_date_1539_, 1);
v_day_1541_ = lean_ctor_get(v_date_1539_, 2);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_date_1539_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_date_1539_, 0);
lean_dec(v_unused_1569_);
v___x_1543_ = v_date_1539_;
v_isShared_1544_ = v_isSharedCheck_1568_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_day_1541_);
lean_inc(v_month_1540_);
lean_dec(v_date_1539_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1568_;
goto v_resetjp_1542_;
}
v___jp_1508_:
{
lean_object* v_time_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1537_; 
v_time_1510_ = lean_ctor_get(v_date_1507_, 1);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_date_1507_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_date_1507_, 0);
lean_dec(v_unused_1538_);
v___x_1512_ = v_date_1507_;
v_isShared_1513_ = v_isSharedCheck_1537_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_time_1510_);
lean_dec(v_date_1507_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1537_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___y_1509_);
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___y_1509_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_time_1510_);
v___x_1515_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v_wt_1516_; lean_object* v_ltt_1517_; lean_object* v_tz_1518_; lean_object* v_offset_1519_; lean_object* v_second_1520_; lean_object* v_nano_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
lean_inc_ref(v___x_1515_);
v_wt_1516_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1515_);
lean_inc_ref(v_rules_1503_);
v_ltt_1517_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1503_, v_wt_1516_);
v_tz_1518_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1517_);
lean_dec_ref(v_ltt_1517_);
v_offset_1519_ = lean_ctor_get(v_tz_1518_, 0);
lean_inc(v_offset_1519_);
v_second_1520_ = lean_ctor_get(v_wt_1516_, 0);
lean_inc(v_second_1520_);
v_nano_1521_ = lean_ctor_get(v_wt_1516_, 1);
lean_inc(v_nano_1521_);
lean_dec_ref(v_wt_1516_);
v___f_1522_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1522_, 0, v___x_1515_);
v___x_1523_ = lean_mk_thunk(v___f_1522_);
v___x_1524_ = lean_int_neg(v_offset_1519_);
lean_dec(v_offset_1519_);
v___x_1525_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1526_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1527_ = lean_int_mul(v_second_1520_, v___x_1526_);
lean_dec(v_second_1520_);
v___x_1528_ = lean_int_add(v___x_1527_, v_nano_1521_);
lean_dec(v_nano_1521_);
lean_dec(v___x_1527_);
v___x_1529_ = lean_int_mul(v___x_1524_, v___x_1526_);
lean_dec(v___x_1524_);
v___x_1530_ = lean_int_add(v___x_1529_, v___x_1525_);
lean_dec(v___x_1529_);
v___x_1531_ = lean_int_add(v___x_1528_, v___x_1530_);
lean_dec(v___x_1530_);
lean_dec(v___x_1528_);
v___x_1532_ = l_Std_Time_Duration_ofNanoseconds(v___x_1531_);
lean_dec(v___x_1531_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 3, v_tz_1518_);
lean_ctor_set(v___x_1505_, 1, v___x_1532_);
lean_ctor_set(v___x_1505_, 0, v___x_1523_);
v___x_1534_ = v___x_1505_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1523_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_rules_1503_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v_tz_1518_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
v_resetjp_1542_:
{
uint8_t v___y_1546_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; uint8_t v___y_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1555_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1556_ = lean_int_mod(v_year_1501_, v___x_1555_);
v___x_1557_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1558_ = lean_int_dec_eq(v___x_1556_, v___x_1557_);
lean_dec(v___x_1556_);
v___x_1561_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1562_ = lean_int_mod(v_year_1501_, v___x_1561_);
v___x_1563_ = lean_int_dec_eq(v___x_1562_, v___x_1557_);
lean_dec(v___x_1562_);
if (v___x_1563_ == 0)
{
uint8_t v___x_1564_; 
v___x_1564_ = 1;
v___y_1560_ = v___x_1564_;
goto v___jp_1559_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1565_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1566_ = lean_int_mod(v_year_1501_, v___x_1565_);
v___x_1567_ = lean_int_dec_eq(v___x_1566_, v___x_1557_);
lean_dec(v___x_1566_);
v___y_1560_ = v___x_1567_;
goto v___jp_1559_;
}
v___jp_1545_:
{
lean_object* v_max_1547_; uint8_t v___x_1548_; 
v_max_1547_ = l_Std_Time_Month_Ordinal_days(v___y_1546_, v_month_1540_);
v___x_1548_ = lean_int_dec_lt(v_max_1547_, v_day_1541_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1550_; 
lean_dec(v_max_1547_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v_year_1501_);
v___x_1550_ = v___x_1543_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_year_1501_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v_month_1540_);
lean_ctor_set(v_reuseFailAlloc_1551_, 2, v_day_1541_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
v___y_1509_ = v___x_1550_;
goto v___jp_1508_;
}
}
else
{
lean_object* v___x_1553_; 
lean_dec(v_day_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 2, v_max_1547_);
lean_ctor_set(v___x_1543_, 0, v_year_1501_);
v___x_1553_ = v___x_1543_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_year_1501_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_month_1540_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_max_1547_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
v___y_1509_ = v___x_1553_;
goto v___jp_1508_;
}
}
}
v___jp_1559_:
{
if (v___x_1558_ == 0)
{
v___y_1546_ = v___x_1558_;
goto v___jp_1545_;
}
else
{
v___y_1546_ = v___y_1560_;
goto v___jp_1545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object* v_dt_1573_, lean_object* v_year_1574_){
_start:
{
lean_object* v_date_1575_; lean_object* v_rules_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1613_; 
v_date_1575_ = lean_ctor_get(v_dt_1573_, 0);
v_rules_1576_ = lean_ctor_get(v_dt_1573_, 2);
v_isSharedCheck_1613_ = !lean_is_exclusive(v_dt_1573_);
if (v_isSharedCheck_1613_ == 0)
{
lean_object* v_unused_1614_; lean_object* v_unused_1615_; 
v_unused_1614_ = lean_ctor_get(v_dt_1573_, 3);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_dt_1573_, 1);
lean_dec(v_unused_1615_);
v___x_1578_ = v_dt_1573_;
v_isShared_1579_ = v_isSharedCheck_1613_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_rules_1576_);
lean_inc(v_date_1575_);
lean_dec(v_dt_1573_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1613_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v_date_1580_; lean_object* v_date_1581_; lean_object* v_time_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1612_; 
v_date_1580_ = lean_thunk_get_own(v_date_1575_);
lean_dec_ref(v_date_1575_);
v_date_1581_ = lean_ctor_get(v_date_1580_, 0);
v_time_1582_ = lean_ctor_get(v_date_1580_, 1);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_date_1580_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1584_ = v_date_1580_;
v_isShared_1585_ = v_isSharedCheck_1612_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_time_1582_);
lean_inc(v_date_1581_);
lean_dec(v_date_1580_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1612_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_month_1586_; lean_object* v_day_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v_month_1586_ = lean_ctor_get(v_date_1581_, 1);
lean_inc(v_month_1586_);
v_day_1587_ = lean_ctor_get(v_date_1581_, 2);
lean_inc(v_day_1587_);
lean_dec_ref(v_date_1581_);
v___x_1588_ = l_Std_Time_PlainDate_rollOver(v_year_1574_, v_month_1586_, v_day_1587_);
lean_dec(v_day_1587_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1588_);
v___x_1590_ = v___x_1584_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_time_1582_);
v___x_1590_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v_wt_1591_; lean_object* v_ltt_1592_; lean_object* v_tz_1593_; lean_object* v_offset_1594_; lean_object* v_second_1595_; lean_object* v_nano_1596_; lean_object* v___f_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
lean_inc_ref(v___x_1590_);
v_wt_1591_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1590_);
lean_inc_ref(v_rules_1576_);
v_ltt_1592_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1576_, v_wt_1591_);
v_tz_1593_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1592_);
lean_dec_ref(v_ltt_1592_);
v_offset_1594_ = lean_ctor_get(v_tz_1593_, 0);
lean_inc(v_offset_1594_);
v_second_1595_ = lean_ctor_get(v_wt_1591_, 0);
lean_inc(v_second_1595_);
v_nano_1596_ = lean_ctor_get(v_wt_1591_, 1);
lean_inc(v_nano_1596_);
lean_dec_ref(v_wt_1591_);
v___f_1597_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1597_, 0, v___x_1590_);
v___x_1598_ = lean_mk_thunk(v___f_1597_);
v___x_1599_ = lean_int_neg(v_offset_1594_);
lean_dec(v_offset_1594_);
v___x_1600_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1601_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1602_ = lean_int_mul(v_second_1595_, v___x_1601_);
lean_dec(v_second_1595_);
v___x_1603_ = lean_int_add(v___x_1602_, v_nano_1596_);
lean_dec(v_nano_1596_);
lean_dec(v___x_1602_);
v___x_1604_ = lean_int_mul(v___x_1599_, v___x_1601_);
lean_dec(v___x_1599_);
v___x_1605_ = lean_int_add(v___x_1604_, v___x_1600_);
lean_dec(v___x_1604_);
v___x_1606_ = lean_int_add(v___x_1603_, v___x_1605_);
lean_dec(v___x_1605_);
lean_dec(v___x_1603_);
v___x_1607_ = l_Std_Time_Duration_ofNanoseconds(v___x_1606_);
lean_dec(v___x_1606_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 3, v_tz_1593_);
lean_ctor_set(v___x_1578_, 1, v___x_1607_);
lean_ctor_set(v___x_1578_, 0, v___x_1598_);
v___x_1609_ = v___x_1578_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_rules_1576_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_tz_1593_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object* v_dt_1616_, lean_object* v_hour_1617_){
_start:
{
lean_object* v_date_1618_; lean_object* v_rules_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1664_; 
v_date_1618_ = lean_ctor_get(v_dt_1616_, 0);
v_rules_1619_ = lean_ctor_get(v_dt_1616_, 2);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_dt_1616_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; lean_object* v_unused_1666_; 
v_unused_1665_ = lean_ctor_get(v_dt_1616_, 3);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_dt_1616_, 1);
lean_dec(v_unused_1666_);
v___x_1621_ = v_dt_1616_;
v_isShared_1622_ = v_isSharedCheck_1664_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_rules_1619_);
lean_inc(v_date_1618_);
lean_dec(v_dt_1616_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1664_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_date_1623_; lean_object* v_time_1624_; lean_object* v_date_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1663_; 
v_date_1623_ = lean_thunk_get_own(v_date_1618_);
lean_dec_ref(v_date_1618_);
v_time_1624_ = lean_ctor_get(v_date_1623_, 1);
v_date_1625_ = lean_ctor_get(v_date_1623_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_date_1623_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1627_ = v_date_1623_;
v_isShared_1628_ = v_isSharedCheck_1663_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_time_1624_);
lean_inc(v_date_1625_);
lean_dec(v_date_1623_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1663_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v_minute_1629_; lean_object* v_second_1630_; lean_object* v_nanosecond_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1661_; 
v_minute_1629_ = lean_ctor_get(v_time_1624_, 1);
v_second_1630_ = lean_ctor_get(v_time_1624_, 2);
v_nanosecond_1631_ = lean_ctor_get(v_time_1624_, 3);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_time_1624_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; 
v_unused_1662_ = lean_ctor_get(v_time_1624_, 0);
lean_dec(v_unused_1662_);
v___x_1633_ = v_time_1624_;
v_isShared_1634_ = v_isSharedCheck_1661_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_nanosecond_1631_);
lean_inc(v_second_1630_);
lean_inc(v_minute_1629_);
lean_dec(v_time_1624_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1661_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_hour_1617_);
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_hour_1617_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_minute_1629_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_second_1630_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v_nanosecond_1631_);
v___x_1636_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1636_);
v___x_1638_ = v___x_1627_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_date_1625_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v_wt_1639_; lean_object* v_ltt_1640_; lean_object* v_tz_1641_; lean_object* v_offset_1642_; lean_object* v_second_1643_; lean_object* v_nano_1644_; lean_object* v___f_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1657_; 
lean_inc_ref(v___x_1638_);
v_wt_1639_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1638_);
lean_inc_ref(v_rules_1619_);
v_ltt_1640_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1619_, v_wt_1639_);
v_tz_1641_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1640_);
lean_dec_ref(v_ltt_1640_);
v_offset_1642_ = lean_ctor_get(v_tz_1641_, 0);
lean_inc(v_offset_1642_);
v_second_1643_ = lean_ctor_get(v_wt_1639_, 0);
lean_inc(v_second_1643_);
v_nano_1644_ = lean_ctor_get(v_wt_1639_, 1);
lean_inc(v_nano_1644_);
lean_dec_ref(v_wt_1639_);
v___f_1645_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1645_, 0, v___x_1638_);
v___x_1646_ = lean_mk_thunk(v___f_1645_);
v___x_1647_ = lean_int_neg(v_offset_1642_);
lean_dec(v_offset_1642_);
v___x_1648_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1649_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1650_ = lean_int_mul(v_second_1643_, v___x_1649_);
lean_dec(v_second_1643_);
v___x_1651_ = lean_int_add(v___x_1650_, v_nano_1644_);
lean_dec(v_nano_1644_);
lean_dec(v___x_1650_);
v___x_1652_ = lean_int_mul(v___x_1647_, v___x_1649_);
lean_dec(v___x_1647_);
v___x_1653_ = lean_int_add(v___x_1652_, v___x_1648_);
lean_dec(v___x_1652_);
v___x_1654_ = lean_int_add(v___x_1651_, v___x_1653_);
lean_dec(v___x_1653_);
lean_dec(v___x_1651_);
v___x_1655_ = l_Std_Time_Duration_ofNanoseconds(v___x_1654_);
lean_dec(v___x_1654_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 3, v_tz_1641_);
lean_ctor_set(v___x_1621_, 1, v___x_1655_);
lean_ctor_set(v___x_1621_, 0, v___x_1646_);
v___x_1657_ = v___x_1621_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_rules_1619_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_tz_1641_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object* v_dt_1667_, lean_object* v_minute_1668_){
_start:
{
lean_object* v_date_1669_; lean_object* v_rules_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1715_; 
v_date_1669_ = lean_ctor_get(v_dt_1667_, 0);
v_rules_1670_ = lean_ctor_get(v_dt_1667_, 2);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_dt_1667_);
if (v_isSharedCheck_1715_ == 0)
{
lean_object* v_unused_1716_; lean_object* v_unused_1717_; 
v_unused_1716_ = lean_ctor_get(v_dt_1667_, 3);
lean_dec(v_unused_1716_);
v_unused_1717_ = lean_ctor_get(v_dt_1667_, 1);
lean_dec(v_unused_1717_);
v___x_1672_ = v_dt_1667_;
v_isShared_1673_ = v_isSharedCheck_1715_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_rules_1670_);
lean_inc(v_date_1669_);
lean_dec(v_dt_1667_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1715_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v_date_1674_; lean_object* v_time_1675_; lean_object* v_date_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1714_; 
v_date_1674_ = lean_thunk_get_own(v_date_1669_);
lean_dec_ref(v_date_1669_);
v_time_1675_ = lean_ctor_get(v_date_1674_, 1);
v_date_1676_ = lean_ctor_get(v_date_1674_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_date_1674_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1678_ = v_date_1674_;
v_isShared_1679_ = v_isSharedCheck_1714_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_time_1675_);
lean_inc(v_date_1676_);
lean_dec(v_date_1674_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1714_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_hour_1680_; lean_object* v_second_1681_; lean_object* v_nanosecond_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1712_; 
v_hour_1680_ = lean_ctor_get(v_time_1675_, 0);
v_second_1681_ = lean_ctor_get(v_time_1675_, 2);
v_nanosecond_1682_ = lean_ctor_get(v_time_1675_, 3);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_time_1675_);
if (v_isSharedCheck_1712_ == 0)
{
lean_object* v_unused_1713_; 
v_unused_1713_ = lean_ctor_get(v_time_1675_, 1);
lean_dec(v_unused_1713_);
v___x_1684_ = v_time_1675_;
v_isShared_1685_ = v_isSharedCheck_1712_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_nanosecond_1682_);
lean_inc(v_second_1681_);
lean_inc(v_hour_1680_);
lean_dec(v_time_1675_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1712_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v_minute_1668_);
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_hour_1680_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v_minute_1668_);
lean_ctor_set(v_reuseFailAlloc_1711_, 2, v_second_1681_);
lean_ctor_set(v_reuseFailAlloc_1711_, 3, v_nanosecond_1682_);
v___x_1687_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v___x_1689_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v___x_1687_);
v___x_1689_ = v___x_1678_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_date_1676_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1687_);
v___x_1689_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v_wt_1690_; lean_object* v_ltt_1691_; lean_object* v_tz_1692_; lean_object* v_offset_1693_; lean_object* v_second_1694_; lean_object* v_nano_1695_; lean_object* v___f_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_inc_ref(v___x_1689_);
v_wt_1690_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1689_);
lean_inc_ref(v_rules_1670_);
v_ltt_1691_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1670_, v_wt_1690_);
v_tz_1692_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1691_);
lean_dec_ref(v_ltt_1691_);
v_offset_1693_ = lean_ctor_get(v_tz_1692_, 0);
lean_inc(v_offset_1693_);
v_second_1694_ = lean_ctor_get(v_wt_1690_, 0);
lean_inc(v_second_1694_);
v_nano_1695_ = lean_ctor_get(v_wt_1690_, 1);
lean_inc(v_nano_1695_);
lean_dec_ref(v_wt_1690_);
v___f_1696_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1696_, 0, v___x_1689_);
v___x_1697_ = lean_mk_thunk(v___f_1696_);
v___x_1698_ = lean_int_neg(v_offset_1693_);
lean_dec(v_offset_1693_);
v___x_1699_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1700_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1701_ = lean_int_mul(v_second_1694_, v___x_1700_);
lean_dec(v_second_1694_);
v___x_1702_ = lean_int_add(v___x_1701_, v_nano_1695_);
lean_dec(v_nano_1695_);
lean_dec(v___x_1701_);
v___x_1703_ = lean_int_mul(v___x_1698_, v___x_1700_);
lean_dec(v___x_1698_);
v___x_1704_ = lean_int_add(v___x_1703_, v___x_1699_);
lean_dec(v___x_1703_);
v___x_1705_ = lean_int_add(v___x_1702_, v___x_1704_);
lean_dec(v___x_1704_);
lean_dec(v___x_1702_);
v___x_1706_ = l_Std_Time_Duration_ofNanoseconds(v___x_1705_);
lean_dec(v___x_1705_);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 3, v_tz_1692_);
lean_ctor_set(v___x_1672_, 1, v___x_1706_);
lean_ctor_set(v___x_1672_, 0, v___x_1697_);
v___x_1708_ = v___x_1672_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_rules_1670_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_tz_1692_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object* v_dt_1718_, lean_object* v_second_1719_){
_start:
{
lean_object* v_date_1720_; lean_object* v_rules_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1766_; 
v_date_1720_ = lean_ctor_get(v_dt_1718_, 0);
v_rules_1721_ = lean_ctor_get(v_dt_1718_, 2);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_dt_1718_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; lean_object* v_unused_1768_; 
v_unused_1767_ = lean_ctor_get(v_dt_1718_, 3);
lean_dec(v_unused_1767_);
v_unused_1768_ = lean_ctor_get(v_dt_1718_, 1);
lean_dec(v_unused_1768_);
v___x_1723_ = v_dt_1718_;
v_isShared_1724_ = v_isSharedCheck_1766_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_rules_1721_);
lean_inc(v_date_1720_);
lean_dec(v_dt_1718_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1766_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_date_1725_; lean_object* v_time_1726_; lean_object* v_date_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1765_; 
v_date_1725_ = lean_thunk_get_own(v_date_1720_);
lean_dec_ref(v_date_1720_);
v_time_1726_ = lean_ctor_get(v_date_1725_, 1);
v_date_1727_ = lean_ctor_get(v_date_1725_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_date_1725_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1729_ = v_date_1725_;
v_isShared_1730_ = v_isSharedCheck_1765_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_time_1726_);
lean_inc(v_date_1727_);
lean_dec(v_date_1725_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1765_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_hour_1731_; lean_object* v_minute_1732_; lean_object* v_nanosecond_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1763_; 
v_hour_1731_ = lean_ctor_get(v_time_1726_, 0);
v_minute_1732_ = lean_ctor_get(v_time_1726_, 1);
v_nanosecond_1733_ = lean_ctor_get(v_time_1726_, 3);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_time_1726_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v_time_1726_, 2);
lean_dec(v_unused_1764_);
v___x_1735_ = v_time_1726_;
v_isShared_1736_ = v_isSharedCheck_1763_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_nanosecond_1733_);
lean_inc(v_minute_1732_);
lean_inc(v_hour_1731_);
lean_dec(v_time_1726_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1763_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 2, v_second_1719_);
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_hour_1731_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_minute_1732_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_second_1719_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_nanosecond_1733_);
v___x_1738_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1740_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v___x_1738_);
v___x_1740_ = v___x_1729_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_date_1727_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v_wt_1741_; lean_object* v_ltt_1742_; lean_object* v_tz_1743_; lean_object* v_offset_1744_; lean_object* v_second_1745_; lean_object* v_nano_1746_; lean_object* v___f_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; 
lean_inc_ref(v___x_1740_);
v_wt_1741_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1740_);
lean_inc_ref(v_rules_1721_);
v_ltt_1742_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1721_, v_wt_1741_);
v_tz_1743_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1742_);
lean_dec_ref(v_ltt_1742_);
v_offset_1744_ = lean_ctor_get(v_tz_1743_, 0);
lean_inc(v_offset_1744_);
v_second_1745_ = lean_ctor_get(v_wt_1741_, 0);
lean_inc(v_second_1745_);
v_nano_1746_ = lean_ctor_get(v_wt_1741_, 1);
lean_inc(v_nano_1746_);
lean_dec_ref(v_wt_1741_);
v___f_1747_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1747_, 0, v___x_1740_);
v___x_1748_ = lean_mk_thunk(v___f_1747_);
v___x_1749_ = lean_int_neg(v_offset_1744_);
lean_dec(v_offset_1744_);
v___x_1750_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1751_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1752_ = lean_int_mul(v_second_1745_, v___x_1751_);
lean_dec(v_second_1745_);
v___x_1753_ = lean_int_add(v___x_1752_, v_nano_1746_);
lean_dec(v_nano_1746_);
lean_dec(v___x_1752_);
v___x_1754_ = lean_int_mul(v___x_1749_, v___x_1751_);
lean_dec(v___x_1749_);
v___x_1755_ = lean_int_add(v___x_1754_, v___x_1750_);
lean_dec(v___x_1754_);
v___x_1756_ = lean_int_add(v___x_1753_, v___x_1755_);
lean_dec(v___x_1755_);
lean_dec(v___x_1753_);
v___x_1757_ = l_Std_Time_Duration_ofNanoseconds(v___x_1756_);
lean_dec(v___x_1756_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 3, v_tz_1743_);
lean_ctor_set(v___x_1723_, 1, v___x_1757_);
lean_ctor_set(v___x_1723_, 0, v___x_1748_);
v___x_1759_ = v___x_1723_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_rules_1721_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_tz_1743_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
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
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = lean_unsigned_to_nat(1000u);
v___x_1770_ = lean_nat_to_int(v___x_1769_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object* v_dt_1771_, lean_object* v_millis_1772_){
_start:
{
lean_object* v_date_1773_; lean_object* v_rules_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1824_; 
v_date_1773_ = lean_ctor_get(v_dt_1771_, 0);
v_rules_1774_ = lean_ctor_get(v_dt_1771_, 2);
v_isSharedCheck_1824_ = !lean_is_exclusive(v_dt_1771_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; lean_object* v_unused_1826_; 
v_unused_1825_ = lean_ctor_get(v_dt_1771_, 3);
lean_dec(v_unused_1825_);
v_unused_1826_ = lean_ctor_get(v_dt_1771_, 1);
lean_dec(v_unused_1826_);
v___x_1776_ = v_dt_1771_;
v_isShared_1777_ = v_isSharedCheck_1824_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_rules_1774_);
lean_inc(v_date_1773_);
lean_dec(v_dt_1771_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1824_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v_date_1778_; lean_object* v_time_1779_; lean_object* v_date_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1823_; 
v_date_1778_ = lean_thunk_get_own(v_date_1773_);
lean_dec_ref(v_date_1773_);
v_time_1779_ = lean_ctor_get(v_date_1778_, 1);
v_date_1780_ = lean_ctor_get(v_date_1778_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_date_1778_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1782_ = v_date_1778_;
v_isShared_1783_ = v_isSharedCheck_1823_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_time_1779_);
lean_inc(v_date_1780_);
lean_dec(v_date_1778_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1823_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v_hour_1784_; lean_object* v_minute_1785_; lean_object* v_second_1786_; lean_object* v_nanosecond_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1822_; 
v_hour_1784_ = lean_ctor_get(v_time_1779_, 0);
v_minute_1785_ = lean_ctor_get(v_time_1779_, 1);
v_second_1786_ = lean_ctor_get(v_time_1779_, 2);
v_nanosecond_1787_ = lean_ctor_get(v_time_1779_, 3);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_time_1779_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1789_ = v_time_1779_;
v_isShared_1790_ = v_isSharedCheck_1822_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_nanosecond_1787_);
lean_inc(v_second_1786_);
lean_inc(v_minute_1785_);
lean_inc(v_hour_1784_);
lean_dec(v_time_1779_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1822_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1791_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_1792_ = lean_int_emod(v_nanosecond_1787_, v___x_1791_);
lean_dec(v_nanosecond_1787_);
v___x_1793_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1794_ = lean_int_mul(v_millis_1772_, v___x_1793_);
v___x_1795_ = lean_int_add(v___x_1794_, v___x_1792_);
lean_dec(v___x_1792_);
lean_dec(v___x_1794_);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 3, v___x_1795_);
v___x_1797_ = v___x_1789_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_hour_1784_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_minute_1785_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_second_1786_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 1, v___x_1797_);
v___x_1799_ = v___x_1782_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_date_1780_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v_wt_1800_; lean_object* v_ltt_1801_; lean_object* v_tz_1802_; lean_object* v_offset_1803_; lean_object* v_second_1804_; lean_object* v_nano_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1818_; 
lean_inc_ref(v___x_1799_);
v_wt_1800_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1799_);
lean_inc_ref(v_rules_1774_);
v_ltt_1801_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1774_, v_wt_1800_);
v_tz_1802_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1801_);
lean_dec_ref(v_ltt_1801_);
v_offset_1803_ = lean_ctor_get(v_tz_1802_, 0);
lean_inc(v_offset_1803_);
v_second_1804_ = lean_ctor_get(v_wt_1800_, 0);
lean_inc(v_second_1804_);
v_nano_1805_ = lean_ctor_get(v_wt_1800_, 1);
lean_inc(v_nano_1805_);
lean_dec_ref(v_wt_1800_);
v___f_1806_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1806_, 0, v___x_1799_);
v___x_1807_ = lean_mk_thunk(v___f_1806_);
v___x_1808_ = lean_int_neg(v_offset_1803_);
lean_dec(v_offset_1803_);
v___x_1809_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1810_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1811_ = lean_int_mul(v_second_1804_, v___x_1810_);
lean_dec(v_second_1804_);
v___x_1812_ = lean_int_add(v___x_1811_, v_nano_1805_);
lean_dec(v_nano_1805_);
lean_dec(v___x_1811_);
v___x_1813_ = lean_int_mul(v___x_1808_, v___x_1810_);
lean_dec(v___x_1808_);
v___x_1814_ = lean_int_add(v___x_1813_, v___x_1809_);
lean_dec(v___x_1813_);
v___x_1815_ = lean_int_add(v___x_1812_, v___x_1814_);
lean_dec(v___x_1814_);
lean_dec(v___x_1812_);
v___x_1816_ = l_Std_Time_Duration_ofNanoseconds(v___x_1815_);
lean_dec(v___x_1815_);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 3, v_tz_1802_);
lean_ctor_set(v___x_1776_, 1, v___x_1816_);
lean_ctor_set(v___x_1776_, 0, v___x_1807_);
v___x_1818_ = v___x_1776_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1807_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_rules_1774_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_tz_1802_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object* v_dt_1827_, lean_object* v_millis_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Std_Time_DateTime_withMilliseconds(v_dt_1827_, v_millis_1828_);
lean_dec(v_millis_1828_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object* v_dt_1830_, lean_object* v_nano_1831_){
_start:
{
lean_object* v_date_1832_; lean_object* v_rules_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1878_; 
v_date_1832_ = lean_ctor_get(v_dt_1830_, 0);
v_rules_1833_ = lean_ctor_get(v_dt_1830_, 2);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_dt_1830_);
if (v_isSharedCheck_1878_ == 0)
{
lean_object* v_unused_1879_; lean_object* v_unused_1880_; 
v_unused_1879_ = lean_ctor_get(v_dt_1830_, 3);
lean_dec(v_unused_1879_);
v_unused_1880_ = lean_ctor_get(v_dt_1830_, 1);
lean_dec(v_unused_1880_);
v___x_1835_ = v_dt_1830_;
v_isShared_1836_ = v_isSharedCheck_1878_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_rules_1833_);
lean_inc(v_date_1832_);
lean_dec(v_dt_1830_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1878_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_date_1837_; lean_object* v_time_1838_; lean_object* v_date_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1877_; 
v_date_1837_ = lean_thunk_get_own(v_date_1832_);
lean_dec_ref(v_date_1832_);
v_time_1838_ = lean_ctor_get(v_date_1837_, 1);
v_date_1839_ = lean_ctor_get(v_date_1837_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_date_1837_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1841_ = v_date_1837_;
v_isShared_1842_ = v_isSharedCheck_1877_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_time_1838_);
lean_inc(v_date_1839_);
lean_dec(v_date_1837_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1877_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v_hour_1843_; lean_object* v_minute_1844_; lean_object* v_second_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1875_; 
v_hour_1843_ = lean_ctor_get(v_time_1838_, 0);
v_minute_1844_ = lean_ctor_get(v_time_1838_, 1);
v_second_1845_ = lean_ctor_get(v_time_1838_, 2);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_time_1838_);
if (v_isSharedCheck_1875_ == 0)
{
lean_object* v_unused_1876_; 
v_unused_1876_ = lean_ctor_get(v_time_1838_, 3);
lean_dec(v_unused_1876_);
v___x_1847_ = v_time_1838_;
v_isShared_1848_ = v_isSharedCheck_1875_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_second_1845_);
lean_inc(v_minute_1844_);
lean_inc(v_hour_1843_);
lean_dec(v_time_1838_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1875_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 3, v_nano_1831_);
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_hour_1843_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_minute_1844_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_second_1845_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_nano_1831_);
v___x_1850_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v___x_1850_);
v___x_1852_ = v___x_1841_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_date_1839_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v_wt_1853_; lean_object* v_ltt_1854_; lean_object* v_tz_1855_; lean_object* v_offset_1856_; lean_object* v_second_1857_; lean_object* v_nano_1858_; lean_object* v___f_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_inc_ref(v___x_1852_);
v_wt_1853_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1852_);
lean_inc_ref(v_rules_1833_);
v_ltt_1854_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1833_, v_wt_1853_);
v_tz_1855_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1854_);
lean_dec_ref(v_ltt_1854_);
v_offset_1856_ = lean_ctor_get(v_tz_1855_, 0);
lean_inc(v_offset_1856_);
v_second_1857_ = lean_ctor_get(v_wt_1853_, 0);
lean_inc(v_second_1857_);
v_nano_1858_ = lean_ctor_get(v_wt_1853_, 1);
lean_inc(v_nano_1858_);
lean_dec_ref(v_wt_1853_);
v___f_1859_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1859_, 0, v___x_1852_);
v___x_1860_ = lean_mk_thunk(v___f_1859_);
v___x_1861_ = lean_int_neg(v_offset_1856_);
lean_dec(v_offset_1856_);
v___x_1862_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1863_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1864_ = lean_int_mul(v_second_1857_, v___x_1863_);
lean_dec(v_second_1857_);
v___x_1865_ = lean_int_add(v___x_1864_, v_nano_1858_);
lean_dec(v_nano_1858_);
lean_dec(v___x_1864_);
v___x_1866_ = lean_int_mul(v___x_1861_, v___x_1863_);
lean_dec(v___x_1861_);
v___x_1867_ = lean_int_add(v___x_1866_, v___x_1862_);
lean_dec(v___x_1866_);
v___x_1868_ = lean_int_add(v___x_1865_, v___x_1867_);
lean_dec(v___x_1867_);
lean_dec(v___x_1865_);
v___x_1869_ = l_Std_Time_Duration_ofNanoseconds(v___x_1868_);
lean_dec(v___x_1868_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 3, v_tz_1855_);
lean_ctor_set(v___x_1835_, 1, v___x_1869_);
lean_ctor_set(v___x_1835_, 0, v___x_1860_);
v___x_1871_ = v___x_1835_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_rules_1833_);
lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_tz_1855_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Time_DateTime_inLeapYear(lean_object* v_date_1881_){
_start:
{
lean_object* v_date_1882_; lean_object* v___x_1883_; lean_object* v_date_1884_; lean_object* v_year_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_date_1882_ = lean_ctor_get(v_date_1881_, 0);
v___x_1883_ = lean_thunk_get_own(v_date_1882_);
v_date_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc_ref(v_date_1884_);
lean_dec(v___x_1883_);
v_year_1885_ = lean_ctor_get(v_date_1884_, 0);
lean_inc(v_year_1885_);
lean_dec_ref(v_date_1884_);
v___x_1886_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1887_ = lean_int_mod(v_year_1885_, v___x_1886_);
v___x_1888_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1889_ = lean_int_dec_eq(v___x_1887_, v___x_1888_);
lean_dec(v___x_1887_);
v___x_1890_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1891_ = lean_int_mod(v_year_1885_, v___x_1890_);
v___x_1892_ = lean_int_dec_eq(v___x_1891_, v___x_1888_);
lean_dec(v___x_1891_);
if (v___x_1892_ == 0)
{
lean_dec(v_year_1885_);
return v___x_1889_;
}
else
{
if (v___x_1889_ == 0)
{
lean_dec(v_year_1885_);
return v___x_1889_;
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1893_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1894_ = lean_int_mod(v_year_1885_, v___x_1893_);
lean_dec(v_year_1885_);
v___x_1895_ = lean_int_dec_eq(v___x_1894_, v___x_1888_);
lean_dec(v___x_1894_);
return v___x_1895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_inLeapYear___boxed(lean_object* v_date_1896_){
_start:
{
uint8_t v_res_1897_; lean_object* v_r_1898_; 
v_res_1897_ = l_Std_Time_DateTime_inLeapYear(v_date_1896_);
lean_dec_ref(v_date_1896_);
v_r_1898_ = lean_box(v_res_1897_);
return v_r_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay(lean_object* v_date_1899_){
_start:
{
lean_object* v_date_1900_; lean_object* v___x_1901_; lean_object* v_date_1902_; lean_object* v___x_1903_; 
v_date_1900_ = lean_ctor_get(v_date_1899_, 0);
v___x_1901_ = lean_thunk_get_own(v_date_1900_);
v_date_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc_ref(v_date_1902_);
lean_dec(v___x_1901_);
v___x_1903_ = l_Std_Time_PlainDate_toEpochDay(v_date_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toEpochDay___boxed(lean_object* v_date_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Std_Time_DateTime_toEpochDay(v_date_1904_);
lean_dec_ref(v_date_1904_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay(lean_object* v_days_1906_, lean_object* v_time_1907_, lean_object* v_zt_1908_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_wt_1911_; lean_object* v_ltt_1912_; lean_object* v_tz_1913_; lean_object* v_offset_1914_; lean_object* v_second_1915_; lean_object* v_nano_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1909_ = l_Std_Time_PlainDate_ofEpochDay(v_days_1906_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v_time_1907_);
lean_inc_ref(v___x_1910_);
v_wt_1911_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1910_);
lean_inc_ref(v_zt_1908_);
v_ltt_1912_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_zt_1908_, v_wt_1911_);
v_tz_1913_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1912_);
lean_dec_ref(v_ltt_1912_);
v_offset_1914_ = lean_ctor_get(v_tz_1913_, 0);
lean_inc(v_offset_1914_);
v_second_1915_ = lean_ctor_get(v_wt_1911_, 0);
lean_inc(v_second_1915_);
v_nano_1916_ = lean_ctor_get(v_wt_1911_, 1);
lean_inc(v_nano_1916_);
lean_dec_ref(v_wt_1911_);
v___f_1917_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1917_, 0, v___x_1910_);
v___x_1918_ = lean_mk_thunk(v___f_1917_);
v___x_1919_ = lean_int_neg(v_offset_1914_);
lean_dec(v_offset_1914_);
v___x_1920_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1921_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1922_ = lean_int_mul(v_second_1915_, v___x_1921_);
lean_dec(v_second_1915_);
v___x_1923_ = lean_int_add(v___x_1922_, v_nano_1916_);
lean_dec(v_nano_1916_);
lean_dec(v___x_1922_);
v___x_1924_ = lean_int_mul(v___x_1919_, v___x_1921_);
lean_dec(v___x_1919_);
v___x_1925_ = lean_int_add(v___x_1924_, v___x_1920_);
lean_dec(v___x_1924_);
v___x_1926_ = lean_int_add(v___x_1923_, v___x_1925_);
lean_dec(v___x_1925_);
lean_dec(v___x_1923_);
v___x_1927_ = l_Std_Time_Duration_ofNanoseconds(v___x_1926_);
lean_dec(v___x_1926_);
v___x_1928_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1918_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
lean_ctor_set(v___x_1928_, 2, v_zt_1908_);
lean_ctor_set(v___x_1928_, 3, v_tz_1913_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_ofEpochDay___boxed(lean_object* v_days_1929_, lean_object* v_time_1930_, lean_object* v_zt_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Std_Time_DateTime_ofEpochDay(v_days_1929_, v_time_1930_, v_zt_1931_);
lean_dec(v_days_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0(lean_object* v_x_1961_, lean_object* v_y_1962_){
_start:
{
lean_object* v_timestamp_1963_; lean_object* v_timestamp_1964_; lean_object* v_second_1965_; lean_object* v_nano_1966_; lean_object* v_second_1967_; lean_object* v_nano_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_timestamp_1963_ = lean_ctor_get(v_y_1962_, 1);
v_timestamp_1964_ = lean_ctor_get(v_x_1961_, 1);
v_second_1965_ = lean_ctor_get(v_timestamp_1963_, 0);
v_nano_1966_ = lean_ctor_get(v_timestamp_1963_, 1);
v_second_1967_ = lean_ctor_get(v_timestamp_1964_, 0);
v_nano_1968_ = lean_ctor_get(v_timestamp_1964_, 1);
v___x_1969_ = lean_int_neg(v_second_1965_);
v___x_1970_ = lean_int_neg(v_nano_1966_);
v___x_1971_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1972_ = lean_int_mul(v_second_1967_, v___x_1971_);
v___x_1973_ = lean_int_add(v___x_1972_, v_nano_1968_);
lean_dec(v___x_1972_);
v___x_1974_ = lean_int_mul(v___x_1969_, v___x_1971_);
lean_dec(v___x_1969_);
v___x_1975_ = lean_int_add(v___x_1974_, v___x_1970_);
lean_dec(v___x_1970_);
lean_dec(v___x_1974_);
v___x_1976_ = lean_int_add(v___x_1973_, v___x_1975_);
lean_dec(v___x_1975_);
lean_dec(v___x_1973_);
v___x_1977_ = l_Std_Time_Duration_ofNanoseconds(v___x_1976_);
lean_dec(v___x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(lean_object* v_x_1978_, lean_object* v_y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Std_Time_DateTime_instHSubDuration___lam__0(v_x_1978_, v_y_1979_);
lean_dec_ref(v_y_1979_);
lean_dec_ref(v_x_1978_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0(lean_object* v_x_1983_, lean_object* v_y_1984_){
_start:
{
lean_object* v_second_1985_; lean_object* v_nano_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v_nanos_1989_; lean_object* v___x_1990_; 
v_second_1985_ = lean_ctor_get(v_y_1984_, 0);
v_nano_1986_ = lean_ctor_get(v_y_1984_, 1);
v___x_1987_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1988_ = lean_int_mul(v_second_1985_, v___x_1987_);
v_nanos_1989_ = lean_int_add(v___x_1988_, v_nano_1986_);
lean_dec(v___x_1988_);
v___x_1990_ = l_Std_Time_DateTime_addNanoseconds(v_x_1983_, v_nanos_1989_);
lean_dec(v_nanos_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHAddDuration___lam__0___boxed(lean_object* v_x_1991_, lean_object* v_y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Std_Time_DateTime_instHAddDuration___lam__0(v_x_1991_, v_y_1992_);
lean_dec_ref(v_y_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0(lean_object* v_x_1996_, lean_object* v_y_1997_){
_start:
{
lean_object* v_second_1998_; lean_object* v_nano_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v_nanos_2002_; lean_object* v___x_2003_; 
v_second_1998_ = lean_ctor_get(v_y_1997_, 0);
v_nano_1999_ = lean_ctor_get(v_y_1997_, 1);
v___x_2000_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_2001_ = lean_int_mul(v_second_1998_, v___x_2000_);
v_nanos_2002_ = lean_int_add(v___x_2001_, v_nano_1999_);
lean_dec(v___x_2001_);
v___x_2003_ = l_Std_Time_DateTime_subNanoseconds(v_x_1996_, v_nanos_2002_);
lean_dec(v_nanos_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instHSubDuration__1___lam__0___boxed(lean_object* v_x_2004_, lean_object* v_y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Std_Time_DateTime_instHSubDuration__1___lam__0(v_x_2004_, v_y_2005_);
lean_dec_ref(v_y_2005_);
return v_res_2006_;
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

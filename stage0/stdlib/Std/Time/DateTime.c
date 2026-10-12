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
uint8_t l_Std_Time_DateTime_weekday(lean_object* v_zdt_265_){
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
LEAN_EXPORT void l_Std_Time_DateTime_weekday_0interp(lean_interpreter_value* stack)
{
lean_object* v_zdt_265_ = stack[0].m_obj;
uint8_t v_res_270_;
v_res_270_ = l_Std_Time_DateTime_weekday(v_zdt_265_);
stack->m_num = v_res_270_;
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekday___boxed(lean_object* v_zdt_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Std_Time_DateTime_weekday(v_zdt_271_);
lean_dec_ref(v_zdt_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__0(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = lean_unsigned_to_nat(4u);
v___x_275_ = lean_nat_to_int(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__1(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_unsigned_to_nat(400u);
v___x_277_ = lean_nat_to_int(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Std_Time_DateTime_dayOfYear___closed__2(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_unsigned_to_nat(100u);
v___x_279_ = lean_nat_to_int(v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear(lean_object* v_date_280_){
_start:
{
lean_object* v_date_281_; lean_object* v___x_282_; lean_object* v_date_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_307_; 
v_date_281_ = lean_ctor_get(v_date_280_, 0);
v___x_282_ = lean_thunk_get_own(v_date_281_);
v_date_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_307_ == 0)
{
lean_object* v_unused_308_; 
v_unused_308_ = lean_ctor_get(v___x_282_, 1);
lean_dec(v_unused_308_);
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_307_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_date_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_307_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_year_287_; lean_object* v_month_288_; lean_object* v_day_289_; uint8_t v___y_291_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_303_; 
v_year_287_ = lean_ctor_get(v_date_283_, 0);
lean_inc(v_year_287_);
v_month_288_ = lean_ctor_get(v_date_283_, 1);
lean_inc(v_month_288_);
v_day_289_ = lean_ctor_get(v_date_283_, 2);
lean_inc(v_day_289_);
lean_dec_ref(v_date_283_);
v___x_296_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_297_ = lean_int_mod(v_year_287_, v___x_296_);
v___x_298_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_303_ = lean_int_dec_eq(v___x_297_, v___x_298_);
lean_dec(v___x_297_);
if (v___x_303_ == 0)
{
lean_dec(v_year_287_);
v___y_291_ = v___x_303_;
goto v___jp_290_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_305_ = lean_int_mod(v_year_287_, v___x_304_);
v___x_306_ = lean_int_dec_eq(v___x_305_, v___x_298_);
lean_dec(v___x_305_);
if (v___x_306_ == 0)
{
if (v___x_303_ == 0)
{
goto v___jp_299_;
}
else
{
lean_dec(v_year_287_);
v___y_291_ = v___x_303_;
goto v___jp_290_;
}
}
else
{
goto v___jp_299_;
}
}
v___jp_290_:
{
lean_object* v___x_293_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v_day_289_);
lean_ctor_set(v___x_285_, 0, v_month_288_);
v___x_293_ = v___x_285_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_month_288_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_day_289_);
v___x_293_ = v_reuseFailAlloc_295_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; 
v___x_294_ = l_Std_Time_ValidDate_dayOfYear(v___y_291_, v___x_293_);
lean_dec_ref(v___x_293_);
return v___x_294_;
}
}
v___jp_299_:
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_301_ = lean_int_mod(v_year_287_, v___x_300_);
lean_dec(v_year_287_);
v___x_302_ = lean_int_dec_eq(v___x_301_, v___x_298_);
lean_dec(v___x_301_);
v___y_291_ = v___x_302_;
goto v___jp_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_dayOfYear___boxed(lean_object* v_date_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Time_DateTime_dayOfYear(v_date_309_);
lean_dec_ref(v_date_309_);
return v_res_310_;
}
}
lean_object* l_Std_Time_DateTime_weekOfYear(lean_object* v_dt_311_, uint8_t v_firstDay_312_, lean_object* v_minDays_313_){
_start:
{
lean_object* v_date_314_; lean_object* v___x_315_; lean_object* v_date_316_; lean_object* v___x_317_; 
v_date_314_ = lean_ctor_get(v_dt_311_, 0);
v___x_315_ = lean_thunk_get_own(v_date_314_);
v_date_316_ = lean_ctor_get(v___x_315_, 0);
lean_inc_ref(v_date_316_);
lean_dec(v___x_315_);
v___x_317_ = l_Std_Time_PlainDate_weekOfYear(v_date_316_, v_firstDay_312_, v_minDays_313_);
return v___x_317_;
}
}
LEAN_EXPORT void l_Std_Time_DateTime_weekOfYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_dt_311_ = stack[0].m_obj;
uint8_t v_firstDay_312_ = stack[1].m_num;
lean_object* v_minDays_313_ = stack[2].m_obj;
lean_object* v_res_318_;
v_res_318_ = l_Std_Time_DateTime_weekOfYear(v_dt_311_, v_firstDay_312_, v_minDays_313_);
stack->m_obj
 = v_res_318_;
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
lean_object* l_Std_Time_DateTime_weekYear(lean_object* v_date_324_, uint8_t v_firstDay_325_, lean_object* v_minDays_326_){
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
LEAN_EXPORT void l_Std_Time_DateTime_weekYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_324_ = stack[0].m_obj;
uint8_t v_firstDay_325_ = stack[1].m_num;
lean_object* v_minDays_326_ = stack[2].m_obj;
lean_object* v_res_331_;
v_res_331_ = l_Std_Time_DateTime_weekYear(v_date_324_, v_firstDay_325_, v_minDays_326_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekYear___boxed(lean_object* v_date_332_, lean_object* v_firstDay_333_, lean_object* v_minDays_334_){
_start:
{
uint8_t v_firstDay_boxed_335_; lean_object* v_res_336_; 
v_firstDay_boxed_335_ = lean_unbox(v_firstDay_333_);
v_res_336_ = l_Std_Time_DateTime_weekYear(v_date_332_, v_firstDay_boxed_335_, v_minDays_334_);
lean_dec(v_minDays_334_);
lean_dec_ref(v_date_332_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth(lean_object* v_date_337_){
_start:
{
lean_object* v_date_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_date_338_ = lean_ctor_get(v_date_337_, 0);
v___x_339_ = lean_thunk_get_own(v_date_338_);
v___x_340_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v___x_339_);
lean_dec(v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_alignedWeekOfMonth___boxed(lean_object* v_date_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Time_DateTime_alignedWeekOfMonth(v_date_341_);
lean_dec_ref(v_date_341_);
return v_res_342_;
}
}
lean_object* l_Std_Time_DateTime_weekOfMonth(lean_object* v_date_343_, uint8_t v_firstDay_344_){
_start:
{
lean_object* v_date_345_; lean_object* v___x_346_; lean_object* v_date_347_; lean_object* v___x_348_; 
v_date_345_ = lean_ctor_get(v_date_343_, 0);
v___x_346_ = lean_thunk_get_own(v_date_345_);
v_date_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_date_347_);
lean_dec(v___x_346_);
v___x_348_ = l_Std_Time_PlainDate_weekOfMonth(v_date_347_, v_firstDay_344_);
return v___x_348_;
}
}
LEAN_EXPORT void l_Std_Time_DateTime_weekOfMonth_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_343_ = stack[0].m_obj;
uint8_t v_firstDay_344_ = stack[1].m_num;
lean_object* v_res_349_;
v_res_349_ = l_Std_Time_DateTime_weekOfMonth(v_date_343_, v_firstDay_344_);
stack->m_obj
 = v_res_349_;
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_weekOfMonth___boxed(lean_object* v_date_350_, lean_object* v_firstDay_351_){
_start:
{
uint8_t v_firstDay_boxed_352_; lean_object* v_res_353_; 
v_firstDay_boxed_352_ = lean_unbox(v_firstDay_351_);
v_res_353_ = l_Std_Time_DateTime_weekOfMonth(v_date_350_, v_firstDay_boxed_352_);
lean_dec_ref(v_date_350_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter(lean_object* v_date_354_){
_start:
{
lean_object* v_date_355_; lean_object* v___x_356_; lean_object* v_date_357_; lean_object* v___x_358_; 
v_date_355_ = lean_ctor_get(v_date_354_, 0);
v___x_356_ = lean_thunk_get_own(v_date_355_);
v_date_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_date_357_);
lean_dec(v___x_356_);
v___x_358_ = l_Std_Time_PlainDate_quarter(v_date_357_);
lean_dec_ref(v_date_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_quarter___boxed(lean_object* v_date_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Std_Time_DateTime_quarter(v_date_359_);
lean_dec_ref(v_date_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_DateTime_addDays_spec__1(lean_object* v_a_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Rat_ofInt(v_a_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0(lean_object* v_tz_363_, lean_object* v___x_364_, lean_object* v___x_365_, lean_object* v___x_366_, lean_object* v_x_367_){
_start:
{
lean_object* v_offset_368_; lean_object* v_second_369_; lean_object* v_nano_370_; lean_object* v___x_371_; lean_object* v_nanos_372_; lean_object* v___x_373_; lean_object* v_nanos_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_offset_368_ = lean_ctor_get(v_tz_363_, 0);
v_second_369_ = lean_ctor_get(v___x_364_, 0);
v_nano_370_ = lean_ctor_get(v___x_364_, 1);
v___x_371_ = lean_int_mul(v_second_369_, v___x_365_);
v_nanos_372_ = lean_int_add(v___x_371_, v_nano_370_);
lean_dec(v___x_371_);
v___x_373_ = lean_int_mul(v_offset_368_, v___x_365_);
v_nanos_374_ = lean_int_add(v___x_373_, v___x_366_);
lean_dec(v___x_373_);
v___x_375_ = lean_int_add(v_nanos_372_, v_nanos_374_);
lean_dec(v_nanos_374_);
lean_dec(v_nanos_372_);
v___x_376_ = l_Std_Time_Duration_ofNanoseconds(v___x_375_);
lean_dec(v___x_375_);
v___x_377_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___lam__0___boxed(lean_object* v_tz_378_, lean_object* v___x_379_, lean_object* v___x_380_, lean_object* v___x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Time_DateTime_addDays___lam__0(v_tz_378_, v___x_379_, v___x_380_, v___x_381_, v_x_382_);
lean_dec(v___x_381_);
lean_dec(v___x_380_);
lean_dec_ref(v___x_379_);
lean_dec_ref(v_tz_378_);
return v_res_383_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addDays___closed__0(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_unsigned_to_nat(86400u);
v___x_385_ = lean_nat_to_int(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays(lean_object* v_dt_386_, lean_object* v_days_387_){
_start:
{
lean_object* v_timestamp_388_; lean_object* v_rules_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_411_; 
v_timestamp_388_ = lean_ctor_get(v_dt_386_, 1);
v_rules_389_ = lean_ctor_get(v_dt_386_, 2);
v_isSharedCheck_411_ = !lean_is_exclusive(v_dt_386_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; lean_object* v_unused_413_; 
v_unused_412_ = lean_ctor_get(v_dt_386_, 3);
lean_dec(v_unused_412_);
v_unused_413_ = lean_ctor_get(v_dt_386_, 0);
lean_dec(v_unused_413_);
v___x_391_ = v_dt_386_;
v_isShared_392_ = v_isSharedCheck_411_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_rules_389_);
lean_inc(v_timestamp_388_);
lean_dec(v_dt_386_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_411_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v_second_393_; lean_object* v_nano_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_nanos_400_; lean_object* v___x_401_; lean_object* v_nanos_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_tz_405_; lean_object* v___f_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
v_second_393_ = lean_ctor_get(v_timestamp_388_, 0);
lean_inc(v_second_393_);
v_nano_394_ = lean_ctor_get(v_timestamp_388_, 1);
lean_inc(v_nano_394_);
lean_dec_ref(v_timestamp_388_);
v___x_395_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_396_ = lean_int_mul(v_days_387_, v___x_395_);
v___x_397_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_398_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_399_ = lean_int_mul(v_second_393_, v___x_398_);
lean_dec(v_second_393_);
v_nanos_400_ = lean_int_add(v___x_399_, v_nano_394_);
lean_dec(v_nano_394_);
lean_dec(v___x_399_);
v___x_401_ = lean_int_mul(v___x_396_, v___x_398_);
lean_dec(v___x_396_);
v_nanos_402_ = lean_int_add(v___x_401_, v___x_397_);
lean_dec(v___x_401_);
v___x_403_ = lean_int_add(v_nanos_400_, v_nanos_402_);
lean_dec(v_nanos_402_);
lean_dec(v_nanos_400_);
v___x_404_ = l_Std_Time_Duration_ofNanoseconds(v___x_403_);
lean_dec(v___x_403_);
lean_inc_ref(v_rules_389_);
v_tz_405_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_389_, v___x_404_);
lean_inc_ref(v___x_404_);
lean_inc_ref(v_tz_405_);
v___f_406_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_406_, 0, v_tz_405_);
lean_closure_set(v___f_406_, 1, v___x_404_);
lean_closure_set(v___f_406_, 2, v___x_398_);
lean_closure_set(v___f_406_, 3, v___x_397_);
v___x_407_ = lean_mk_thunk(v___f_406_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 3, v_tz_405_);
lean_ctor_set(v___x_391_, 1, v___x_404_);
lean_ctor_set(v___x_391_, 0, v___x_407_);
v___x_409_ = v___x_391_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_rules_389_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_tz_405_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addDays___boxed(lean_object* v_dt_414_, lean_object* v_days_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_Time_DateTime_addDays(v_dt_414_, v_days_415_);
lean_dec(v_days_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Std_Time_DateTime_addDays_spec__0_spec__0(lean_object* v_a_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_nat_to_int(v_a_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_DateTime_addDays_spec__0(lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_nat_to_int(v_a_419_);
v___x_421_ = l_Rat_ofInt(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays(lean_object* v_dt_422_, lean_object* v_days_423_){
_start:
{
lean_object* v_timestamp_424_; lean_object* v_rules_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_449_; 
v_timestamp_424_ = lean_ctor_get(v_dt_422_, 1);
v_rules_425_ = lean_ctor_get(v_dt_422_, 2);
v_isSharedCheck_449_ = !lean_is_exclusive(v_dt_422_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; lean_object* v_unused_451_; 
v_unused_450_ = lean_ctor_get(v_dt_422_, 3);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_dt_422_, 0);
lean_dec(v_unused_451_);
v___x_427_ = v_dt_422_;
v_isShared_428_ = v_isSharedCheck_449_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_rules_425_);
lean_inc(v_timestamp_424_);
lean_dec(v_dt_422_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_449_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_second_429_; lean_object* v_nano_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_nanos_438_; lean_object* v___x_439_; lean_object* v_nanos_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_tz_443_; lean_object* v___f_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v_second_429_ = lean_ctor_get(v_timestamp_424_, 0);
lean_inc(v_second_429_);
v_nano_430_ = lean_ctor_get(v_timestamp_424_, 1);
lean_inc(v_nano_430_);
lean_dec_ref(v_timestamp_424_);
v___x_431_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_432_ = lean_int_mul(v_days_423_, v___x_431_);
v___x_433_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_434_ = lean_int_neg(v___x_432_);
lean_dec(v___x_432_);
v___x_435_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_436_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_437_ = lean_int_mul(v_second_429_, v___x_436_);
lean_dec(v_second_429_);
v_nanos_438_ = lean_int_add(v___x_437_, v_nano_430_);
lean_dec(v_nano_430_);
lean_dec(v___x_437_);
v___x_439_ = lean_int_mul(v___x_434_, v___x_436_);
lean_dec(v___x_434_);
v_nanos_440_ = lean_int_add(v___x_439_, v___x_435_);
lean_dec(v___x_439_);
v___x_441_ = lean_int_add(v_nanos_438_, v_nanos_440_);
lean_dec(v_nanos_440_);
lean_dec(v_nanos_438_);
v___x_442_ = l_Std_Time_Duration_ofNanoseconds(v___x_441_);
lean_dec(v___x_441_);
lean_inc_ref(v_rules_425_);
v_tz_443_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_425_, v___x_442_);
lean_inc_ref(v___x_442_);
lean_inc_ref(v_tz_443_);
v___f_444_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_444_, 0, v_tz_443_);
lean_closure_set(v___f_444_, 1, v___x_442_);
lean_closure_set(v___f_444_, 2, v___x_436_);
lean_closure_set(v___f_444_, 3, v___x_433_);
v___x_445_ = lean_mk_thunk(v___f_444_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 3, v_tz_443_);
lean_ctor_set(v___x_427_, 1, v___x_442_);
lean_ctor_set(v___x_427_, 0, v___x_445_);
v___x_447_ = v___x_427_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_rules_425_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_tz_443_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subDays___boxed(lean_object* v_dt_452_, lean_object* v_days_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Time_DateTime_subDays(v_dt_452_, v_days_453_);
lean_dec(v_days_453_);
return v_res_454_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addWeeks___closed__0(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(7u);
v___x_456_ = lean_nat_to_int(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks(lean_object* v_dt_457_, lean_object* v_weeks_458_){
_start:
{
lean_object* v_timestamp_459_; lean_object* v_rules_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_484_; 
v_timestamp_459_ = lean_ctor_get(v_dt_457_, 1);
v_rules_460_ = lean_ctor_get(v_dt_457_, 2);
v_isSharedCheck_484_ = !lean_is_exclusive(v_dt_457_);
if (v_isSharedCheck_484_ == 0)
{
lean_object* v_unused_485_; lean_object* v_unused_486_; 
v_unused_485_ = lean_ctor_get(v_dt_457_, 3);
lean_dec(v_unused_485_);
v_unused_486_ = lean_ctor_get(v_dt_457_, 0);
lean_dec(v_unused_486_);
v___x_462_ = v_dt_457_;
v_isShared_463_ = v_isSharedCheck_484_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_rules_460_);
lean_inc(v_timestamp_459_);
lean_dec(v_dt_457_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_484_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v_second_464_; lean_object* v_nano_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_nanos_473_; lean_object* v___x_474_; lean_object* v_nanos_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v_tz_478_; lean_object* v___f_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v_second_464_ = lean_ctor_get(v_timestamp_459_, 0);
lean_inc(v_second_464_);
v_nano_465_ = lean_ctor_get(v_timestamp_459_, 1);
lean_inc(v_nano_465_);
lean_dec_ref(v_timestamp_459_);
v___x_466_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_467_ = lean_int_mul(v_weeks_458_, v___x_466_);
v___x_468_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_469_ = lean_int_mul(v___x_467_, v___x_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_471_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_472_ = lean_int_mul(v_second_464_, v___x_471_);
lean_dec(v_second_464_);
v_nanos_473_ = lean_int_add(v___x_472_, v_nano_465_);
lean_dec(v_nano_465_);
lean_dec(v___x_472_);
v___x_474_ = lean_int_mul(v___x_469_, v___x_471_);
lean_dec(v___x_469_);
v_nanos_475_ = lean_int_add(v___x_474_, v___x_470_);
lean_dec(v___x_474_);
v___x_476_ = lean_int_add(v_nanos_473_, v_nanos_475_);
lean_dec(v_nanos_475_);
lean_dec(v_nanos_473_);
v___x_477_ = l_Std_Time_Duration_ofNanoseconds(v___x_476_);
lean_dec(v___x_476_);
lean_inc_ref(v_rules_460_);
v_tz_478_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_460_, v___x_477_);
lean_inc_ref(v___x_477_);
lean_inc_ref(v_tz_478_);
v___f_479_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_479_, 0, v_tz_478_);
lean_closure_set(v___f_479_, 1, v___x_477_);
lean_closure_set(v___f_479_, 2, v___x_471_);
lean_closure_set(v___f_479_, 3, v___x_470_);
v___x_480_ = lean_mk_thunk(v___f_479_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 3, v_tz_478_);
lean_ctor_set(v___x_462_, 1, v___x_477_);
lean_ctor_set(v___x_462_, 0, v___x_480_);
v___x_482_ = v___x_462_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_rules_460_);
lean_ctor_set(v_reuseFailAlloc_483_, 3, v_tz_478_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addWeeks___boxed(lean_object* v_dt_487_, lean_object* v_weeks_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_Time_DateTime_addWeeks(v_dt_487_, v_weeks_488_);
lean_dec(v_weeks_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks(lean_object* v_dt_490_, lean_object* v_weeks_491_){
_start:
{
lean_object* v_timestamp_492_; lean_object* v_rules_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_519_; 
v_timestamp_492_ = lean_ctor_get(v_dt_490_, 1);
v_rules_493_ = lean_ctor_get(v_dt_490_, 2);
v_isSharedCheck_519_ = !lean_is_exclusive(v_dt_490_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; lean_object* v_unused_521_; 
v_unused_520_ = lean_ctor_get(v_dt_490_, 3);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_dt_490_, 0);
lean_dec(v_unused_521_);
v___x_495_ = v_dt_490_;
v_isShared_496_ = v_isSharedCheck_519_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_rules_493_);
lean_inc(v_timestamp_492_);
lean_dec(v_dt_490_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_519_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_second_497_; lean_object* v_nano_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_nanos_508_; lean_object* v___x_509_; lean_object* v_nanos_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v_tz_513_; lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v_second_497_ = lean_ctor_get(v_timestamp_492_, 0);
lean_inc(v_second_497_);
v_nano_498_ = lean_ctor_get(v_timestamp_492_, 1);
lean_inc(v_nano_498_);
lean_dec_ref(v_timestamp_492_);
v___x_499_ = lean_obj_once(&l_Std_Time_DateTime_addWeeks___closed__0, &l_Std_Time_DateTime_addWeeks___closed__0_once, _init_l_Std_Time_DateTime_addWeeks___closed__0);
v___x_500_ = lean_int_mul(v_weeks_491_, v___x_499_);
v___x_501_ = lean_obj_once(&l_Std_Time_DateTime_addDays___closed__0, &l_Std_Time_DateTime_addDays___closed__0_once, _init_l_Std_Time_DateTime_addDays___closed__0);
v___x_502_ = lean_int_mul(v___x_500_, v___x_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_504_ = lean_int_neg(v___x_502_);
lean_dec(v___x_502_);
v___x_505_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_506_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_507_ = lean_int_mul(v_second_497_, v___x_506_);
lean_dec(v_second_497_);
v_nanos_508_ = lean_int_add(v___x_507_, v_nano_498_);
lean_dec(v_nano_498_);
lean_dec(v___x_507_);
v___x_509_ = lean_int_mul(v___x_504_, v___x_506_);
lean_dec(v___x_504_);
v_nanos_510_ = lean_int_add(v___x_509_, v___x_505_);
lean_dec(v___x_509_);
v___x_511_ = lean_int_add(v_nanos_508_, v_nanos_510_);
lean_dec(v_nanos_510_);
lean_dec(v_nanos_508_);
v___x_512_ = l_Std_Time_Duration_ofNanoseconds(v___x_511_);
lean_dec(v___x_511_);
lean_inc_ref(v_rules_493_);
v_tz_513_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_493_, v___x_512_);
lean_inc_ref(v___x_512_);
lean_inc_ref(v_tz_513_);
v___f_514_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_514_, 0, v_tz_513_);
lean_closure_set(v___f_514_, 1, v___x_512_);
lean_closure_set(v___f_514_, 2, v___x_506_);
lean_closure_set(v___f_514_, 3, v___x_503_);
v___x_515_ = lean_mk_thunk(v___f_514_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 3, v_tz_513_);
lean_ctor_set(v___x_495_, 1, v___x_512_);
lean_ctor_set(v___x_495_, 0, v___x_515_);
v___x_517_ = v___x_495_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_rules_493_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_tz_513_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subWeeks___boxed(lean_object* v_dt_522_, lean_object* v_weeks_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_Time_DateTime_subWeeks(v_dt_522_, v_weeks_523_);
lean_dec(v_weeks_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0(lean_object* v___x_525_, lean_object* v_x_526_){
_start:
{
lean_inc_ref(v___x_525_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(lean_object* v___x_527_, lean_object* v_x_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_Time_DateTime_addMonthsClip___lam__0(v___x_527_, v_x_528_);
lean_dec_ref(v___x_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip(lean_object* v_dt_530_, lean_object* v_months_531_){
_start:
{
lean_object* v_date_532_; lean_object* v_rules_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_559_; 
v_date_532_ = lean_ctor_get(v_dt_530_, 0);
v_rules_533_ = lean_ctor_get(v_dt_530_, 2);
v_isSharedCheck_559_ = !lean_is_exclusive(v_dt_530_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; lean_object* v_unused_561_; 
v_unused_560_ = lean_ctor_get(v_dt_530_, 3);
lean_dec(v_unused_560_);
v_unused_561_ = lean_ctor_get(v_dt_530_, 1);
lean_dec(v_unused_561_);
v___x_535_ = v_dt_530_;
v_isShared_536_ = v_isSharedCheck_559_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_rules_533_);
lean_inc(v_date_532_);
lean_dec(v_dt_530_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_559_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_wt_539_; lean_object* v_ltt_540_; lean_object* v_tz_541_; lean_object* v_offset_542_; lean_object* v_second_543_; lean_object* v_nano_544_; lean_object* v___f_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_nanos_551_; lean_object* v___x_552_; lean_object* v_nanos_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_537_ = lean_thunk_get_own(v_date_532_);
lean_dec_ref(v_date_532_);
v___x_538_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_537_, v_months_531_);
lean_inc_ref(v___x_538_);
v_wt_539_ = l_Std_Time_PlainDateTime_toWallTime(v___x_538_);
lean_inc_ref(v_rules_533_);
v_ltt_540_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_533_, v_wt_539_);
v_tz_541_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_540_);
lean_dec_ref(v_ltt_540_);
v_offset_542_ = lean_ctor_get(v_tz_541_, 0);
v_second_543_ = lean_ctor_get(v_wt_539_, 0);
lean_inc(v_second_543_);
v_nano_544_ = lean_ctor_get(v_wt_539_, 1);
lean_inc(v_nano_544_);
lean_dec_ref(v_wt_539_);
v___f_545_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_545_, 0, v___x_538_);
v___x_546_ = lean_mk_thunk(v___f_545_);
v___x_547_ = lean_int_neg(v_offset_542_);
v___x_548_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_549_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_550_ = lean_int_mul(v_second_543_, v___x_549_);
lean_dec(v_second_543_);
v_nanos_551_ = lean_int_add(v___x_550_, v_nano_544_);
lean_dec(v_nano_544_);
lean_dec(v___x_550_);
v___x_552_ = lean_int_mul(v___x_547_, v___x_549_);
lean_dec(v___x_547_);
v_nanos_553_ = lean_int_add(v___x_552_, v___x_548_);
lean_dec(v___x_552_);
v___x_554_ = lean_int_add(v_nanos_551_, v_nanos_553_);
lean_dec(v_nanos_553_);
lean_dec(v_nanos_551_);
v___x_555_ = l_Std_Time_Duration_ofNanoseconds(v___x_554_);
lean_dec(v___x_554_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 3, v_tz_541_);
lean_ctor_set(v___x_535_, 1, v___x_555_);
lean_ctor_set(v___x_535_, 0, v___x_546_);
v___x_557_ = v___x_535_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_rules_533_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_tz_541_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsClip___boxed(lean_object* v_dt_562_, lean_object* v_months_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_Time_DateTime_addMonthsClip(v_dt_562_, v_months_563_);
lean_dec(v_months_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip(lean_object* v_dt_565_, lean_object* v_months_566_){
_start:
{
lean_object* v_date_567_; lean_object* v_rules_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_604_; 
v_date_567_ = lean_ctor_get(v_dt_565_, 0);
v_rules_568_ = lean_ctor_get(v_dt_565_, 2);
v_isSharedCheck_604_ = !lean_is_exclusive(v_dt_565_);
if (v_isSharedCheck_604_ == 0)
{
lean_object* v_unused_605_; lean_object* v_unused_606_; 
v_unused_605_ = lean_ctor_get(v_dt_565_, 3);
lean_dec(v_unused_605_);
v_unused_606_ = lean_ctor_get(v_dt_565_, 1);
lean_dec(v_unused_606_);
v___x_570_ = v_dt_565_;
v_isShared_571_ = v_isSharedCheck_604_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_rules_568_);
lean_inc(v_date_567_);
lean_dec(v_dt_565_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_604_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v_date_573_; lean_object* v_time_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_603_; 
v___x_572_ = lean_thunk_get_own(v_date_567_);
lean_dec_ref(v_date_567_);
v_date_573_ = lean_ctor_get(v___x_572_, 0);
v_time_574_ = lean_ctor_get(v___x_572_, 1);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_572_);
if (v_isSharedCheck_603_ == 0)
{
v___x_576_ = v___x_572_;
v_isShared_577_ = v_isSharedCheck_603_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_time_574_);
lean_inc(v_date_573_);
lean_dec(v___x_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_603_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_578_ = lean_int_neg(v_months_566_);
v___x_579_ = l_Std_Time_PlainDate_addMonthsClip(v_date_573_, v___x_578_);
lean_dec(v___x_578_);
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 0, v___x_579_);
v___x_581_ = v___x_576_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v_time_574_);
v___x_581_ = v_reuseFailAlloc_602_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v_wt_582_; lean_object* v_ltt_583_; lean_object* v_tz_584_; lean_object* v_offset_585_; lean_object* v_second_586_; lean_object* v_nano_587_; lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_nanos_594_; lean_object* v___x_595_; lean_object* v_nanos_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
lean_inc_ref(v___x_581_);
v_wt_582_ = l_Std_Time_PlainDateTime_toWallTime(v___x_581_);
lean_inc_ref(v_rules_568_);
v_ltt_583_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_568_, v_wt_582_);
v_tz_584_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_583_);
lean_dec_ref(v_ltt_583_);
v_offset_585_ = lean_ctor_get(v_tz_584_, 0);
v_second_586_ = lean_ctor_get(v_wt_582_, 0);
lean_inc(v_second_586_);
v_nano_587_ = lean_ctor_get(v_wt_582_, 1);
lean_inc(v_nano_587_);
lean_dec_ref(v_wt_582_);
v___f_588_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_588_, 0, v___x_581_);
v___x_589_ = lean_mk_thunk(v___f_588_);
v___x_590_ = lean_int_neg(v_offset_585_);
v___x_591_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_592_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_593_ = lean_int_mul(v_second_586_, v___x_592_);
lean_dec(v_second_586_);
v_nanos_594_ = lean_int_add(v___x_593_, v_nano_587_);
lean_dec(v_nano_587_);
lean_dec(v___x_593_);
v___x_595_ = lean_int_mul(v___x_590_, v___x_592_);
lean_dec(v___x_590_);
v_nanos_596_ = lean_int_add(v___x_595_, v___x_591_);
lean_dec(v___x_595_);
v___x_597_ = lean_int_add(v_nanos_594_, v_nanos_596_);
lean_dec(v_nanos_596_);
lean_dec(v_nanos_594_);
v___x_598_ = l_Std_Time_Duration_ofNanoseconds(v___x_597_);
lean_dec(v___x_597_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 3, v_tz_584_);
lean_ctor_set(v___x_570_, 1, v___x_598_);
lean_ctor_set(v___x_570_, 0, v___x_589_);
v___x_600_ = v___x_570_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_rules_568_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_tz_584_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsClip___boxed(lean_object* v_dt_607_, lean_object* v_months_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Time_DateTime_subMonthsClip(v_dt_607_, v_months_608_);
lean_dec(v_months_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver(lean_object* v_dt_610_, lean_object* v_months_611_){
_start:
{
lean_object* v_date_612_; lean_object* v_rules_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_639_; 
v_date_612_ = lean_ctor_get(v_dt_610_, 0);
v_rules_613_ = lean_ctor_get(v_dt_610_, 2);
v_isSharedCheck_639_ = !lean_is_exclusive(v_dt_610_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; lean_object* v_unused_641_; 
v_unused_640_ = lean_ctor_get(v_dt_610_, 3);
lean_dec(v_unused_640_);
v_unused_641_ = lean_ctor_get(v_dt_610_, 1);
lean_dec(v_unused_641_);
v___x_615_ = v_dt_610_;
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_rules_613_);
lean_inc(v_date_612_);
lean_dec(v_dt_610_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v_wt_619_; lean_object* v_ltt_620_; lean_object* v_tz_621_; lean_object* v_offset_622_; lean_object* v_second_623_; lean_object* v_nano_624_; lean_object* v___f_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v_nanos_631_; lean_object* v___x_632_; lean_object* v_nanos_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_617_ = lean_thunk_get_own(v_date_612_);
lean_dec_ref(v_date_612_);
v___x_618_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_617_, v_months_611_);
lean_inc_ref(v___x_618_);
v_wt_619_ = l_Std_Time_PlainDateTime_toWallTime(v___x_618_);
lean_inc_ref(v_rules_613_);
v_ltt_620_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_613_, v_wt_619_);
v_tz_621_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_620_);
lean_dec_ref(v_ltt_620_);
v_offset_622_ = lean_ctor_get(v_tz_621_, 0);
v_second_623_ = lean_ctor_get(v_wt_619_, 0);
lean_inc(v_second_623_);
v_nano_624_ = lean_ctor_get(v_wt_619_, 1);
lean_inc(v_nano_624_);
lean_dec_ref(v_wt_619_);
v___f_625_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_625_, 0, v___x_618_);
v___x_626_ = lean_mk_thunk(v___f_625_);
v___x_627_ = lean_int_neg(v_offset_622_);
v___x_628_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_629_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_630_ = lean_int_mul(v_second_623_, v___x_629_);
lean_dec(v_second_623_);
v_nanos_631_ = lean_int_add(v___x_630_, v_nano_624_);
lean_dec(v_nano_624_);
lean_dec(v___x_630_);
v___x_632_ = lean_int_mul(v___x_627_, v___x_629_);
lean_dec(v___x_627_);
v_nanos_633_ = lean_int_add(v___x_632_, v___x_628_);
lean_dec(v___x_632_);
v___x_634_ = lean_int_add(v_nanos_631_, v_nanos_633_);
lean_dec(v_nanos_633_);
lean_dec(v_nanos_631_);
v___x_635_ = l_Std_Time_Duration_ofNanoseconds(v___x_634_);
lean_dec(v___x_634_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 3, v_tz_621_);
lean_ctor_set(v___x_615_, 1, v___x_635_);
lean_ctor_set(v___x_615_, 0, v___x_626_);
v___x_637_ = v___x_615_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_626_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_rules_613_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_tz_621_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMonthsRollOver___boxed(lean_object* v_dt_642_, lean_object* v_months_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_Time_DateTime_addMonthsRollOver(v_dt_642_, v_months_643_);
lean_dec(v_months_643_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver(lean_object* v_dt_645_, lean_object* v_months_646_){
_start:
{
lean_object* v_date_647_; lean_object* v_rules_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_684_; 
v_date_647_ = lean_ctor_get(v_dt_645_, 0);
v_rules_648_ = lean_ctor_get(v_dt_645_, 2);
v_isSharedCheck_684_ = !lean_is_exclusive(v_dt_645_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; lean_object* v_unused_686_; 
v_unused_685_ = lean_ctor_get(v_dt_645_, 3);
lean_dec(v_unused_685_);
v_unused_686_ = lean_ctor_get(v_dt_645_, 1);
lean_dec(v_unused_686_);
v___x_650_ = v_dt_645_;
v_isShared_651_ = v_isSharedCheck_684_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_rules_648_);
lean_inc(v_date_647_);
lean_dec(v_dt_645_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_684_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v_date_653_; lean_object* v_time_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_683_; 
v___x_652_ = lean_thunk_get_own(v_date_647_);
lean_dec_ref(v_date_647_);
v_date_653_ = lean_ctor_get(v___x_652_, 0);
v_time_654_ = lean_ctor_get(v___x_652_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_683_ == 0)
{
v___x_656_ = v___x_652_;
v_isShared_657_ = v_isSharedCheck_683_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_time_654_);
lean_inc(v_date_653_);
lean_dec(v___x_652_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_683_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_658_ = lean_int_neg(v_months_646_);
v___x_659_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_653_, v___x_658_);
lean_dec(v___x_658_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_659_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_time_654_);
v___x_661_ = v_reuseFailAlloc_682_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
lean_object* v_wt_662_; lean_object* v_ltt_663_; lean_object* v_tz_664_; lean_object* v_offset_665_; lean_object* v_second_666_; lean_object* v_nano_667_; lean_object* v___f_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_nanos_674_; lean_object* v___x_675_; lean_object* v_nanos_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
lean_inc_ref(v___x_661_);
v_wt_662_ = l_Std_Time_PlainDateTime_toWallTime(v___x_661_);
lean_inc_ref(v_rules_648_);
v_ltt_663_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_648_, v_wt_662_);
v_tz_664_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_663_);
lean_dec_ref(v_ltt_663_);
v_offset_665_ = lean_ctor_get(v_tz_664_, 0);
v_second_666_ = lean_ctor_get(v_wt_662_, 0);
lean_inc(v_second_666_);
v_nano_667_ = lean_ctor_get(v_wt_662_, 1);
lean_inc(v_nano_667_);
lean_dec_ref(v_wt_662_);
v___f_668_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_668_, 0, v___x_661_);
v___x_669_ = lean_mk_thunk(v___f_668_);
v___x_670_ = lean_int_neg(v_offset_665_);
v___x_671_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_672_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_673_ = lean_int_mul(v_second_666_, v___x_672_);
lean_dec(v_second_666_);
v_nanos_674_ = lean_int_add(v___x_673_, v_nano_667_);
lean_dec(v_nano_667_);
lean_dec(v___x_673_);
v___x_675_ = lean_int_mul(v___x_670_, v___x_672_);
lean_dec(v___x_670_);
v_nanos_676_ = lean_int_add(v___x_675_, v___x_671_);
lean_dec(v___x_675_);
v___x_677_ = lean_int_add(v_nanos_674_, v_nanos_676_);
lean_dec(v_nanos_676_);
lean_dec(v_nanos_674_);
v___x_678_ = l_Std_Time_Duration_ofNanoseconds(v___x_677_);
lean_dec(v___x_677_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 3, v_tz_664_);
lean_ctor_set(v___x_650_, 1, v___x_678_);
lean_ctor_set(v___x_650_, 0, v___x_669_);
v___x_680_ = v___x_650_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_rules_648_);
lean_ctor_set(v_reuseFailAlloc_681_, 3, v_tz_664_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMonthsRollOver___boxed(lean_object* v_dt_687_, lean_object* v_months_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_Time_DateTime_subMonthsRollOver(v_dt_687_, v_months_688_);
lean_dec(v_months_688_);
return v_res_689_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addYearsRollOver___closed__0(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_unsigned_to_nat(12u);
v___x_691_ = lean_nat_to_int(v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver(lean_object* v_dt_692_, lean_object* v_years_693_){
_start:
{
lean_object* v_date_694_; lean_object* v_rules_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_732_; 
v_date_694_ = lean_ctor_get(v_dt_692_, 0);
v_rules_695_ = lean_ctor_get(v_dt_692_, 2);
v_isSharedCheck_732_ = !lean_is_exclusive(v_dt_692_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; lean_object* v_unused_734_; 
v_unused_733_ = lean_ctor_get(v_dt_692_, 3);
lean_dec(v_unused_733_);
v_unused_734_ = lean_ctor_get(v_dt_692_, 1);
lean_dec(v_unused_734_);
v___x_697_ = v_dt_692_;
v_isShared_698_ = v_isSharedCheck_732_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_rules_695_);
lean_inc(v_date_694_);
lean_dec(v_dt_692_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_732_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v_date_700_; lean_object* v_time_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_731_; 
v___x_699_ = lean_thunk_get_own(v_date_694_);
lean_dec_ref(v_date_694_);
v_date_700_ = lean_ctor_get(v___x_699_, 0);
v_time_701_ = lean_ctor_get(v___x_699_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_731_ == 0)
{
v___x_703_ = v___x_699_;
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_time_701_);
lean_inc(v_date_700_);
lean_dec(v___x_699_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_705_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_706_ = lean_int_mul(v_years_693_, v___x_705_);
v___x_707_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_700_, v___x_706_);
lean_dec(v___x_706_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_707_);
v___x_709_ = v___x_703_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_time_701_);
v___x_709_ = v_reuseFailAlloc_730_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v_wt_710_; lean_object* v_ltt_711_; lean_object* v_tz_712_; lean_object* v_offset_713_; lean_object* v_second_714_; lean_object* v_nano_715_; lean_object* v___f_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v_nanos_722_; lean_object* v___x_723_; lean_object* v_nanos_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
lean_inc_ref(v___x_709_);
v_wt_710_ = l_Std_Time_PlainDateTime_toWallTime(v___x_709_);
lean_inc_ref(v_rules_695_);
v_ltt_711_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_695_, v_wt_710_);
v_tz_712_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_711_);
lean_dec_ref(v_ltt_711_);
v_offset_713_ = lean_ctor_get(v_tz_712_, 0);
v_second_714_ = lean_ctor_get(v_wt_710_, 0);
lean_inc(v_second_714_);
v_nano_715_ = lean_ctor_get(v_wt_710_, 1);
lean_inc(v_nano_715_);
lean_dec_ref(v_wt_710_);
v___f_716_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_716_, 0, v___x_709_);
v___x_717_ = lean_mk_thunk(v___f_716_);
v___x_718_ = lean_int_neg(v_offset_713_);
v___x_719_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_720_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_721_ = lean_int_mul(v_second_714_, v___x_720_);
lean_dec(v_second_714_);
v_nanos_722_ = lean_int_add(v___x_721_, v_nano_715_);
lean_dec(v_nano_715_);
lean_dec(v___x_721_);
v___x_723_ = lean_int_mul(v___x_718_, v___x_720_);
lean_dec(v___x_718_);
v_nanos_724_ = lean_int_add(v___x_723_, v___x_719_);
lean_dec(v___x_723_);
v___x_725_ = lean_int_add(v_nanos_722_, v_nanos_724_);
lean_dec(v_nanos_724_);
lean_dec(v_nanos_722_);
v___x_726_ = l_Std_Time_Duration_ofNanoseconds(v___x_725_);
lean_dec(v___x_725_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 3, v_tz_712_);
lean_ctor_set(v___x_697_, 1, v___x_726_);
lean_ctor_set(v___x_697_, 0, v___x_717_);
v___x_728_ = v___x_697_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_rules_695_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_tz_712_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsRollOver___boxed(lean_object* v_dt_735_, lean_object* v_years_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Std_Time_DateTime_addYearsRollOver(v_dt_735_, v_years_736_);
lean_dec(v_years_736_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip(lean_object* v_dt_738_, lean_object* v_years_739_){
_start:
{
lean_object* v_date_740_; lean_object* v_rules_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_778_; 
v_date_740_ = lean_ctor_get(v_dt_738_, 0);
v_rules_741_ = lean_ctor_get(v_dt_738_, 2);
v_isSharedCheck_778_ = !lean_is_exclusive(v_dt_738_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; lean_object* v_unused_780_; 
v_unused_779_ = lean_ctor_get(v_dt_738_, 3);
lean_dec(v_unused_779_);
v_unused_780_ = lean_ctor_get(v_dt_738_, 1);
lean_dec(v_unused_780_);
v___x_743_ = v_dt_738_;
v_isShared_744_ = v_isSharedCheck_778_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_rules_741_);
lean_inc(v_date_740_);
lean_dec(v_dt_738_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_778_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v_date_746_; lean_object* v_time_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_777_; 
v___x_745_ = lean_thunk_get_own(v_date_740_);
lean_dec_ref(v_date_740_);
v_date_746_ = lean_ctor_get(v___x_745_, 0);
v_time_747_ = lean_ctor_get(v___x_745_, 1);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_777_ == 0)
{
v___x_749_ = v___x_745_;
v_isShared_750_ = v_isSharedCheck_777_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_time_747_);
lean_inc(v_date_746_);
lean_dec(v___x_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_777_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_751_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_752_ = lean_int_mul(v_years_739_, v___x_751_);
v___x_753_ = l_Std_Time_PlainDate_addMonthsClip(v_date_746_, v___x_752_);
lean_dec(v___x_752_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_753_);
v___x_755_ = v___x_749_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_time_747_);
v___x_755_ = v_reuseFailAlloc_776_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v_wt_756_; lean_object* v_ltt_757_; lean_object* v_tz_758_; lean_object* v_offset_759_; lean_object* v_second_760_; lean_object* v_nano_761_; lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v_nanos_768_; lean_object* v___x_769_; lean_object* v_nanos_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
lean_inc_ref(v___x_755_);
v_wt_756_ = l_Std_Time_PlainDateTime_toWallTime(v___x_755_);
lean_inc_ref(v_rules_741_);
v_ltt_757_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_741_, v_wt_756_);
v_tz_758_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_757_);
lean_dec_ref(v_ltt_757_);
v_offset_759_ = lean_ctor_get(v_tz_758_, 0);
v_second_760_ = lean_ctor_get(v_wt_756_, 0);
lean_inc(v_second_760_);
v_nano_761_ = lean_ctor_get(v_wt_756_, 1);
lean_inc(v_nano_761_);
lean_dec_ref(v_wt_756_);
v___f_762_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_762_, 0, v___x_755_);
v___x_763_ = lean_mk_thunk(v___f_762_);
v___x_764_ = lean_int_neg(v_offset_759_);
v___x_765_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_766_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_767_ = lean_int_mul(v_second_760_, v___x_766_);
lean_dec(v_second_760_);
v_nanos_768_ = lean_int_add(v___x_767_, v_nano_761_);
lean_dec(v_nano_761_);
lean_dec(v___x_767_);
v___x_769_ = lean_int_mul(v___x_764_, v___x_766_);
lean_dec(v___x_764_);
v_nanos_770_ = lean_int_add(v___x_769_, v___x_765_);
lean_dec(v___x_769_);
v___x_771_ = lean_int_add(v_nanos_768_, v_nanos_770_);
lean_dec(v_nanos_770_);
lean_dec(v_nanos_768_);
v___x_772_ = l_Std_Time_Duration_ofNanoseconds(v___x_771_);
lean_dec(v___x_771_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 3, v_tz_758_);
lean_ctor_set(v___x_743_, 1, v___x_772_);
lean_ctor_set(v___x_743_, 0, v___x_763_);
v___x_774_ = v___x_743_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_763_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_rules_741_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_tz_758_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addYearsClip___boxed(lean_object* v_dt_781_, lean_object* v_years_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_Time_DateTime_addYearsClip(v_dt_781_, v_years_782_);
lean_dec(v_years_782_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip(lean_object* v_dt_784_, lean_object* v_years_785_){
_start:
{
lean_object* v_date_786_; lean_object* v_rules_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_825_; 
v_date_786_ = lean_ctor_get(v_dt_784_, 0);
v_rules_787_ = lean_ctor_get(v_dt_784_, 2);
v_isSharedCheck_825_ = !lean_is_exclusive(v_dt_784_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; lean_object* v_unused_827_; 
v_unused_826_ = lean_ctor_get(v_dt_784_, 3);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_dt_784_, 1);
lean_dec(v_unused_827_);
v___x_789_ = v_dt_784_;
v_isShared_790_ = v_isSharedCheck_825_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_rules_787_);
lean_inc(v_date_786_);
lean_dec(v_dt_784_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_825_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v_date_792_; lean_object* v_time_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_824_; 
v___x_791_ = lean_thunk_get_own(v_date_786_);
lean_dec_ref(v_date_786_);
v_date_792_ = lean_ctor_get(v___x_791_, 0);
v_time_793_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_824_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_824_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_time_793_);
lean_inc(v_date_792_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_824_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_797_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_798_ = lean_int_mul(v_years_785_, v___x_797_);
v___x_799_ = lean_int_neg(v___x_798_);
lean_dec(v___x_798_);
v___x_800_ = l_Std_Time_PlainDate_addMonthsClip(v_date_792_, v___x_799_);
lean_dec(v___x_799_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_800_);
v___x_802_ = v___x_795_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_time_793_);
v___x_802_ = v_reuseFailAlloc_823_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v_wt_803_; lean_object* v_ltt_804_; lean_object* v_tz_805_; lean_object* v_offset_806_; lean_object* v_second_807_; lean_object* v_nano_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_nanos_815_; lean_object* v___x_816_; lean_object* v_nanos_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc_ref(v___x_802_);
v_wt_803_ = l_Std_Time_PlainDateTime_toWallTime(v___x_802_);
lean_inc_ref(v_rules_787_);
v_ltt_804_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_787_, v_wt_803_);
v_tz_805_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_804_);
lean_dec_ref(v_ltt_804_);
v_offset_806_ = lean_ctor_get(v_tz_805_, 0);
v_second_807_ = lean_ctor_get(v_wt_803_, 0);
lean_inc(v_second_807_);
v_nano_808_ = lean_ctor_get(v_wt_803_, 1);
lean_inc(v_nano_808_);
lean_dec_ref(v_wt_803_);
v___f_809_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_809_, 0, v___x_802_);
v___x_810_ = lean_mk_thunk(v___f_809_);
v___x_811_ = lean_int_neg(v_offset_806_);
v___x_812_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_813_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_814_ = lean_int_mul(v_second_807_, v___x_813_);
lean_dec(v_second_807_);
v_nanos_815_ = lean_int_add(v___x_814_, v_nano_808_);
lean_dec(v_nano_808_);
lean_dec(v___x_814_);
v___x_816_ = lean_int_mul(v___x_811_, v___x_813_);
lean_dec(v___x_811_);
v_nanos_817_ = lean_int_add(v___x_816_, v___x_812_);
lean_dec(v___x_816_);
v___x_818_ = lean_int_add(v_nanos_815_, v_nanos_817_);
lean_dec(v_nanos_817_);
lean_dec(v_nanos_815_);
v___x_819_ = l_Std_Time_Duration_ofNanoseconds(v___x_818_);
lean_dec(v___x_818_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 3, v_tz_805_);
lean_ctor_set(v___x_789_, 1, v___x_819_);
lean_ctor_set(v___x_789_, 0, v___x_810_);
v___x_821_ = v___x_789_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
lean_ctor_set(v_reuseFailAlloc_822_, 2, v_rules_787_);
lean_ctor_set(v_reuseFailAlloc_822_, 3, v_tz_805_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsClip___boxed(lean_object* v_dt_828_, lean_object* v_years_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_Time_DateTime_subYearsClip(v_dt_828_, v_years_829_);
lean_dec(v_years_829_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver(lean_object* v_dt_831_, lean_object* v_years_832_){
_start:
{
lean_object* v_date_833_; lean_object* v_rules_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_872_; 
v_date_833_ = lean_ctor_get(v_dt_831_, 0);
v_rules_834_ = lean_ctor_get(v_dt_831_, 2);
v_isSharedCheck_872_ = !lean_is_exclusive(v_dt_831_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; lean_object* v_unused_874_; 
v_unused_873_ = lean_ctor_get(v_dt_831_, 3);
lean_dec(v_unused_873_);
v_unused_874_ = lean_ctor_get(v_dt_831_, 1);
lean_dec(v_unused_874_);
v___x_836_ = v_dt_831_;
v_isShared_837_ = v_isSharedCheck_872_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_rules_834_);
lean_inc(v_date_833_);
lean_dec(v_dt_831_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_872_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v_date_839_; lean_object* v_time_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_871_; 
v___x_838_ = lean_thunk_get_own(v_date_833_);
lean_dec_ref(v_date_833_);
v_date_839_ = lean_ctor_get(v___x_838_, 0);
v_time_840_ = lean_ctor_get(v___x_838_, 1);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_871_ == 0)
{
v___x_842_ = v___x_838_;
v_isShared_843_ = v_isSharedCheck_871_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_time_840_);
lean_inc(v_date_839_);
lean_dec(v___x_838_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_871_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_844_ = lean_obj_once(&l_Std_Time_DateTime_addYearsRollOver___closed__0, &l_Std_Time_DateTime_addYearsRollOver___closed__0_once, _init_l_Std_Time_DateTime_addYearsRollOver___closed__0);
v___x_845_ = lean_int_mul(v_years_832_, v___x_844_);
v___x_846_ = lean_int_neg(v___x_845_);
lean_dec(v___x_845_);
v___x_847_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_839_, v___x_846_);
lean_dec(v___x_846_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_847_);
v___x_849_ = v___x_842_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_time_840_);
v___x_849_ = v_reuseFailAlloc_870_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v_wt_850_; lean_object* v_ltt_851_; lean_object* v_tz_852_; lean_object* v_offset_853_; lean_object* v_second_854_; lean_object* v_nano_855_; lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v_nanos_862_; lean_object* v___x_863_; lean_object* v_nanos_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_868_; 
lean_inc_ref(v___x_849_);
v_wt_850_ = l_Std_Time_PlainDateTime_toWallTime(v___x_849_);
lean_inc_ref(v_rules_834_);
v_ltt_851_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_834_, v_wt_850_);
v_tz_852_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_851_);
lean_dec_ref(v_ltt_851_);
v_offset_853_ = lean_ctor_get(v_tz_852_, 0);
v_second_854_ = lean_ctor_get(v_wt_850_, 0);
lean_inc(v_second_854_);
v_nano_855_ = lean_ctor_get(v_wt_850_, 1);
lean_inc(v_nano_855_);
lean_dec_ref(v_wt_850_);
v___f_856_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_856_, 0, v___x_849_);
v___x_857_ = lean_mk_thunk(v___f_856_);
v___x_858_ = lean_int_neg(v_offset_853_);
v___x_859_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_860_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_861_ = lean_int_mul(v_second_854_, v___x_860_);
lean_dec(v_second_854_);
v_nanos_862_ = lean_int_add(v___x_861_, v_nano_855_);
lean_dec(v_nano_855_);
lean_dec(v___x_861_);
v___x_863_ = lean_int_mul(v___x_858_, v___x_860_);
lean_dec(v___x_858_);
v_nanos_864_ = lean_int_add(v___x_863_, v___x_859_);
lean_dec(v___x_863_);
v___x_865_ = lean_int_add(v_nanos_862_, v_nanos_864_);
lean_dec(v_nanos_864_);
lean_dec(v_nanos_862_);
v___x_866_ = l_Std_Time_Duration_ofNanoseconds(v___x_865_);
lean_dec(v___x_865_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 3, v_tz_852_);
lean_ctor_set(v___x_836_, 1, v___x_866_);
lean_ctor_set(v___x_836_, 0, v___x_857_);
v___x_868_ = v___x_836_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_rules_834_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_tz_852_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subYearsRollOver___boxed(lean_object* v_dt_875_, lean_object* v_years_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_Time_DateTime_subYearsRollOver(v_dt_875_, v_years_876_);
lean_dec(v_years_876_);
return v_res_877_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_unsigned_to_nat(3600u);
v___x_879_ = lean_nat_to_int(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours(lean_object* v_dt_880_, lean_object* v_hours_881_){
_start:
{
lean_object* v_timestamp_882_; lean_object* v_rules_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_905_; 
v_timestamp_882_ = lean_ctor_get(v_dt_880_, 1);
v_rules_883_ = lean_ctor_get(v_dt_880_, 2);
v_isSharedCheck_905_ = !lean_is_exclusive(v_dt_880_);
if (v_isSharedCheck_905_ == 0)
{
lean_object* v_unused_906_; lean_object* v_unused_907_; 
v_unused_906_ = lean_ctor_get(v_dt_880_, 3);
lean_dec(v_unused_906_);
v_unused_907_ = lean_ctor_get(v_dt_880_, 0);
lean_dec(v_unused_907_);
v___x_885_ = v_dt_880_;
v_isShared_886_ = v_isSharedCheck_905_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_rules_883_);
lean_inc(v_timestamp_882_);
lean_dec(v_dt_880_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_905_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_second_887_; lean_object* v_nano_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_nanos_894_; lean_object* v___x_895_; lean_object* v_nanos_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_tz_899_; lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___x_903_; 
v_second_887_ = lean_ctor_get(v_timestamp_882_, 0);
lean_inc(v_second_887_);
v_nano_888_ = lean_ctor_get(v_timestamp_882_, 1);
lean_inc(v_nano_888_);
lean_dec_ref(v_timestamp_882_);
v___x_889_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_890_ = lean_int_mul(v_hours_881_, v___x_889_);
v___x_891_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_892_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_893_ = lean_int_mul(v_second_887_, v___x_892_);
lean_dec(v_second_887_);
v_nanos_894_ = lean_int_add(v___x_893_, v_nano_888_);
lean_dec(v_nano_888_);
lean_dec(v___x_893_);
v___x_895_ = lean_int_mul(v___x_890_, v___x_892_);
lean_dec(v___x_890_);
v_nanos_896_ = lean_int_add(v___x_895_, v___x_891_);
lean_dec(v___x_895_);
v___x_897_ = lean_int_add(v_nanos_894_, v_nanos_896_);
lean_dec(v_nanos_896_);
lean_dec(v_nanos_894_);
v___x_898_ = l_Std_Time_Duration_ofNanoseconds(v___x_897_);
lean_dec(v___x_897_);
lean_inc_ref(v_rules_883_);
v_tz_899_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_883_, v___x_898_);
lean_inc_ref(v___x_898_);
lean_inc_ref(v_tz_899_);
v___f_900_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_900_, 0, v_tz_899_);
lean_closure_set(v___f_900_, 1, v___x_898_);
lean_closure_set(v___f_900_, 2, v___x_892_);
lean_closure_set(v___f_900_, 3, v___x_891_);
v___x_901_ = lean_mk_thunk(v___f_900_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 3, v_tz_899_);
lean_ctor_set(v___x_885_, 1, v___x_898_);
lean_ctor_set(v___x_885_, 0, v___x_901_);
v___x_903_ = v___x_885_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_904_, 2, v_rules_883_);
lean_ctor_set(v_reuseFailAlloc_904_, 3, v_tz_899_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addHours___boxed(lean_object* v_dt_908_, lean_object* v_hours_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Std_Time_DateTime_addHours(v_dt_908_, v_hours_909_);
lean_dec(v_hours_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours(lean_object* v_dt_911_, lean_object* v_hours_912_){
_start:
{
lean_object* v_timestamp_913_; lean_object* v_rules_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_938_; 
v_timestamp_913_ = lean_ctor_get(v_dt_911_, 1);
v_rules_914_ = lean_ctor_get(v_dt_911_, 2);
v_isSharedCheck_938_ = !lean_is_exclusive(v_dt_911_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; lean_object* v_unused_940_; 
v_unused_939_ = lean_ctor_get(v_dt_911_, 3);
lean_dec(v_unused_939_);
v_unused_940_ = lean_ctor_get(v_dt_911_, 0);
lean_dec(v_unused_940_);
v___x_916_ = v_dt_911_;
v_isShared_917_ = v_isSharedCheck_938_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_rules_914_);
lean_inc(v_timestamp_913_);
lean_dec(v_dt_911_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_938_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v_second_918_; lean_object* v_nano_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_nanos_927_; lean_object* v___x_928_; lean_object* v_nanos_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v_tz_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_936_; 
v_second_918_ = lean_ctor_get(v_timestamp_913_, 0);
lean_inc(v_second_918_);
v_nano_919_ = lean_ctor_get(v_timestamp_913_, 1);
lean_inc(v_nano_919_);
lean_dec_ref(v_timestamp_913_);
v___x_920_ = lean_obj_once(&l_Std_Time_DateTime_addHours___closed__0, &l_Std_Time_DateTime_addHours___closed__0_once, _init_l_Std_Time_DateTime_addHours___closed__0);
v___x_921_ = lean_int_mul(v_hours_912_, v___x_920_);
v___x_922_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_923_ = lean_int_neg(v___x_921_);
lean_dec(v___x_921_);
v___x_924_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_925_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_926_ = lean_int_mul(v_second_918_, v___x_925_);
lean_dec(v_second_918_);
v_nanos_927_ = lean_int_add(v___x_926_, v_nano_919_);
lean_dec(v_nano_919_);
lean_dec(v___x_926_);
v___x_928_ = lean_int_mul(v___x_923_, v___x_925_);
lean_dec(v___x_923_);
v_nanos_929_ = lean_int_add(v___x_928_, v___x_924_);
lean_dec(v___x_928_);
v___x_930_ = lean_int_add(v_nanos_927_, v_nanos_929_);
lean_dec(v_nanos_929_);
lean_dec(v_nanos_927_);
v___x_931_ = l_Std_Time_Duration_ofNanoseconds(v___x_930_);
lean_dec(v___x_930_);
lean_inc_ref(v_rules_914_);
v_tz_932_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_914_, v___x_931_);
lean_inc_ref(v___x_931_);
lean_inc_ref(v_tz_932_);
v___f_933_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_933_, 0, v_tz_932_);
lean_closure_set(v___f_933_, 1, v___x_931_);
lean_closure_set(v___f_933_, 2, v___x_925_);
lean_closure_set(v___f_933_, 3, v___x_922_);
v___x_934_ = lean_mk_thunk(v___f_933_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 3, v_tz_932_);
lean_ctor_set(v___x_916_, 1, v___x_931_);
lean_ctor_set(v___x_916_, 0, v___x_934_);
v___x_936_ = v___x_916_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_rules_914_);
lean_ctor_set(v_reuseFailAlloc_937_, 3, v_tz_932_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subHours___boxed(lean_object* v_dt_941_, lean_object* v_hours_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Std_Time_DateTime_subHours(v_dt_941_, v_hours_942_);
lean_dec(v_hours_942_);
return v_res_943_;
}
}
static lean_object* _init_l_Std_Time_DateTime_addMinutes___closed__0(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(60u);
v___x_945_ = lean_nat_to_int(v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes(lean_object* v_dt_946_, lean_object* v_minutes_947_){
_start:
{
lean_object* v_timestamp_948_; lean_object* v_rules_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_971_; 
v_timestamp_948_ = lean_ctor_get(v_dt_946_, 1);
v_rules_949_ = lean_ctor_get(v_dt_946_, 2);
v_isSharedCheck_971_ = !lean_is_exclusive(v_dt_946_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; lean_object* v_unused_973_; 
v_unused_972_ = lean_ctor_get(v_dt_946_, 3);
lean_dec(v_unused_972_);
v_unused_973_ = lean_ctor_get(v_dt_946_, 0);
lean_dec(v_unused_973_);
v___x_951_ = v_dt_946_;
v_isShared_952_ = v_isSharedCheck_971_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_rules_949_);
lean_inc(v_timestamp_948_);
lean_dec(v_dt_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_971_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v_second_953_; lean_object* v_nano_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v_nanos_960_; lean_object* v___x_961_; lean_object* v_nanos_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v_tz_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v_second_953_ = lean_ctor_get(v_timestamp_948_, 0);
lean_inc(v_second_953_);
v_nano_954_ = lean_ctor_get(v_timestamp_948_, 1);
lean_inc(v_nano_954_);
lean_dec_ref(v_timestamp_948_);
v___x_955_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_956_ = lean_int_mul(v_minutes_947_, v___x_955_);
v___x_957_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_958_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_959_ = lean_int_mul(v_second_953_, v___x_958_);
lean_dec(v_second_953_);
v_nanos_960_ = lean_int_add(v___x_959_, v_nano_954_);
lean_dec(v_nano_954_);
lean_dec(v___x_959_);
v___x_961_ = lean_int_mul(v___x_956_, v___x_958_);
lean_dec(v___x_956_);
v_nanos_962_ = lean_int_add(v___x_961_, v___x_957_);
lean_dec(v___x_961_);
v___x_963_ = lean_int_add(v_nanos_960_, v_nanos_962_);
lean_dec(v_nanos_962_);
lean_dec(v_nanos_960_);
v___x_964_ = l_Std_Time_Duration_ofNanoseconds(v___x_963_);
lean_dec(v___x_963_);
lean_inc_ref(v_rules_949_);
v_tz_965_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_949_, v___x_964_);
lean_inc_ref(v___x_964_);
lean_inc_ref(v_tz_965_);
v___f_966_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_966_, 0, v_tz_965_);
lean_closure_set(v___f_966_, 1, v___x_964_);
lean_closure_set(v___f_966_, 2, v___x_958_);
lean_closure_set(v___f_966_, 3, v___x_957_);
v___x_967_ = lean_mk_thunk(v___f_966_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 3, v_tz_965_);
lean_ctor_set(v___x_951_, 1, v___x_964_);
lean_ctor_set(v___x_951_, 0, v___x_967_);
v___x_969_ = v___x_951_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_rules_949_);
lean_ctor_set(v_reuseFailAlloc_970_, 3, v_tz_965_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMinutes___boxed(lean_object* v_dt_974_, lean_object* v_minutes_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Std_Time_DateTime_addMinutes(v_dt_974_, v_minutes_975_);
lean_dec(v_minutes_975_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes(lean_object* v_dt_977_, lean_object* v_minutes_978_){
_start:
{
lean_object* v_timestamp_979_; lean_object* v_rules_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1004_; 
v_timestamp_979_ = lean_ctor_get(v_dt_977_, 1);
v_rules_980_ = lean_ctor_get(v_dt_977_, 2);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_dt_977_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; lean_object* v_unused_1006_; 
v_unused_1005_ = lean_ctor_get(v_dt_977_, 3);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_dt_977_, 0);
lean_dec(v_unused_1006_);
v___x_982_ = v_dt_977_;
v_isShared_983_ = v_isSharedCheck_1004_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_rules_980_);
lean_inc(v_timestamp_979_);
lean_dec(v_dt_977_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1004_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_second_984_; lean_object* v_nano_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_nanos_993_; lean_object* v___x_994_; lean_object* v_nanos_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v_tz_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v_second_984_ = lean_ctor_get(v_timestamp_979_, 0);
lean_inc(v_second_984_);
v_nano_985_ = lean_ctor_get(v_timestamp_979_, 1);
lean_inc(v_nano_985_);
lean_dec_ref(v_timestamp_979_);
v___x_986_ = lean_obj_once(&l_Std_Time_DateTime_addMinutes___closed__0, &l_Std_Time_DateTime_addMinutes___closed__0_once, _init_l_Std_Time_DateTime_addMinutes___closed__0);
v___x_987_ = lean_int_mul(v_minutes_978_, v___x_986_);
v___x_988_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_989_ = lean_int_neg(v___x_987_);
lean_dec(v___x_987_);
v___x_990_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_991_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_992_ = lean_int_mul(v_second_984_, v___x_991_);
lean_dec(v_second_984_);
v_nanos_993_ = lean_int_add(v___x_992_, v_nano_985_);
lean_dec(v_nano_985_);
lean_dec(v___x_992_);
v___x_994_ = lean_int_mul(v___x_989_, v___x_991_);
lean_dec(v___x_989_);
v_nanos_995_ = lean_int_add(v___x_994_, v___x_990_);
lean_dec(v___x_994_);
v___x_996_ = lean_int_add(v_nanos_993_, v_nanos_995_);
lean_dec(v_nanos_995_);
lean_dec(v_nanos_993_);
v___x_997_ = l_Std_Time_Duration_ofNanoseconds(v___x_996_);
lean_dec(v___x_996_);
lean_inc_ref(v_rules_980_);
v_tz_998_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_980_, v___x_997_);
lean_inc_ref(v___x_997_);
lean_inc_ref(v_tz_998_);
v___f_999_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_999_, 0, v_tz_998_);
lean_closure_set(v___f_999_, 1, v___x_997_);
lean_closure_set(v___f_999_, 2, v___x_991_);
lean_closure_set(v___f_999_, 3, v___x_988_);
v___x_1000_ = lean_mk_thunk(v___f_999_);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 3, v_tz_998_);
lean_ctor_set(v___x_982_, 1, v___x_997_);
lean_ctor_set(v___x_982_, 0, v___x_1000_);
v___x_1002_ = v___x_982_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v_rules_980_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_tz_998_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMinutes___boxed(lean_object* v_dt_1007_, lean_object* v_minutes_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Std_Time_DateTime_subMinutes(v_dt_1007_, v_minutes_1008_);
lean_dec(v_minutes_1008_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0(lean_object* v_tz_1010_, lean_object* v___x_1011_, lean_object* v___x_1012_, lean_object* v_x_1013_){
_start:
{
lean_object* v_offset_1014_; lean_object* v_second_1015_; lean_object* v_nano_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v_nanos_1019_; lean_object* v___x_1020_; lean_object* v_nanos_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_offset_1014_ = lean_ctor_get(v_tz_1010_, 0);
v_second_1015_ = lean_ctor_get(v___x_1011_, 0);
v_nano_1016_ = lean_ctor_get(v___x_1011_, 1);
v___x_1017_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1018_ = lean_int_mul(v_second_1015_, v___x_1012_);
v_nanos_1019_ = lean_int_add(v___x_1018_, v_nano_1016_);
lean_dec(v___x_1018_);
v___x_1020_ = lean_int_mul(v_offset_1014_, v___x_1012_);
v_nanos_1021_ = lean_int_add(v___x_1020_, v___x_1017_);
lean_dec(v___x_1020_);
v___x_1022_ = lean_int_add(v_nanos_1019_, v_nanos_1021_);
lean_dec(v_nanos_1021_);
lean_dec(v_nanos_1019_);
v___x_1023_ = l_Std_Time_Duration_ofNanoseconds(v___x_1022_);
lean_dec(v___x_1022_);
v___x_1024_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(lean_object* v_tz_1025_, lean_object* v___x_1026_, lean_object* v___x_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_Time_DateTime_addMilliseconds___lam__0(v_tz_1025_, v___x_1026_, v___x_1027_, v_x_1028_);
lean_dec(v___x_1027_);
lean_dec_ref(v___x_1026_);
lean_dec_ref(v_tz_1025_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds(lean_object* v_dt_1030_, lean_object* v_milliseconds_1031_){
_start:
{
lean_object* v_timestamp_1032_; lean_object* v_rules_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1057_; 
v_timestamp_1032_ = lean_ctor_get(v_dt_1030_, 1);
v_rules_1033_ = lean_ctor_get(v_dt_1030_, 2);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_dt_1030_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; lean_object* v_unused_1059_; 
v_unused_1058_ = lean_ctor_get(v_dt_1030_, 3);
lean_dec(v_unused_1058_);
v_unused_1059_ = lean_ctor_get(v_dt_1030_, 0);
lean_dec(v_unused_1059_);
v___x_1035_ = v_dt_1030_;
v_isShared_1036_ = v_isSharedCheck_1057_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_rules_1033_);
lean_inc(v_timestamp_1032_);
lean_dec(v_dt_1030_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1057_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_second_1037_; lean_object* v_nano_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_second_1042_; lean_object* v_nano_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_nanos_1046_; lean_object* v___x_1047_; lean_object* v_nanos_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_tz_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v_second_1037_ = lean_ctor_get(v_timestamp_1032_, 0);
lean_inc(v_second_1037_);
v_nano_1038_ = lean_ctor_get(v_timestamp_1032_, 1);
lean_inc(v_nano_1038_);
lean_dec_ref(v_timestamp_1032_);
v___x_1039_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1040_ = lean_int_mul(v_milliseconds_1031_, v___x_1039_);
v___x_1041_ = l_Std_Time_Duration_ofNanoseconds(v___x_1040_);
lean_dec(v___x_1040_);
v_second_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_second_1042_);
v_nano_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_nano_1043_);
lean_dec_ref(v___x_1041_);
v___x_1044_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1045_ = lean_int_mul(v_second_1037_, v___x_1044_);
lean_dec(v_second_1037_);
v_nanos_1046_ = lean_int_add(v___x_1045_, v_nano_1038_);
lean_dec(v_nano_1038_);
lean_dec(v___x_1045_);
v___x_1047_ = lean_int_mul(v_second_1042_, v___x_1044_);
lean_dec(v_second_1042_);
v_nanos_1048_ = lean_int_add(v___x_1047_, v_nano_1043_);
lean_dec(v_nano_1043_);
lean_dec(v___x_1047_);
v___x_1049_ = lean_int_add(v_nanos_1046_, v_nanos_1048_);
lean_dec(v_nanos_1048_);
lean_dec(v_nanos_1046_);
v___x_1050_ = l_Std_Time_Duration_ofNanoseconds(v___x_1049_);
lean_dec(v___x_1049_);
lean_inc_ref(v_rules_1033_);
v_tz_1051_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1033_, v___x_1050_);
lean_inc_ref(v___x_1050_);
lean_inc_ref(v_tz_1051_);
v___f_1052_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1052_, 0, v_tz_1051_);
lean_closure_set(v___f_1052_, 1, v___x_1050_);
lean_closure_set(v___f_1052_, 2, v___x_1044_);
v___x_1053_ = lean_mk_thunk(v___f_1052_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 3, v_tz_1051_);
lean_ctor_set(v___x_1035_, 1, v___x_1050_);
lean_ctor_set(v___x_1035_, 0, v___x_1053_);
v___x_1055_ = v___x_1035_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___x_1050_);
lean_ctor_set(v_reuseFailAlloc_1056_, 2, v_rules_1033_);
lean_ctor_set(v_reuseFailAlloc_1056_, 3, v_tz_1051_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addMilliseconds___boxed(lean_object* v_dt_1060_, lean_object* v_milliseconds_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Std_Time_DateTime_addMilliseconds(v_dt_1060_, v_milliseconds_1061_);
lean_dec(v_milliseconds_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds(lean_object* v_dt_1063_, lean_object* v_milliseconds_1064_){
_start:
{
lean_object* v_timestamp_1065_; lean_object* v_rules_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1092_; 
v_timestamp_1065_ = lean_ctor_get(v_dt_1063_, 1);
v_rules_1066_ = lean_ctor_get(v_dt_1063_, 2);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_dt_1063_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; lean_object* v_unused_1094_; 
v_unused_1093_ = lean_ctor_get(v_dt_1063_, 3);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_dt_1063_, 0);
lean_dec(v_unused_1094_);
v___x_1068_ = v_dt_1063_;
v_isShared_1069_ = v_isSharedCheck_1092_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_rules_1066_);
lean_inc(v_timestamp_1065_);
lean_dec(v_dt_1063_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1092_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v_second_1073_; lean_object* v_nano_1074_; lean_object* v_second_1075_; lean_object* v_nano_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_nanos_1081_; lean_object* v___x_1082_; lean_object* v_nanos_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_tz_1086_; lean_object* v___f_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1070_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1071_ = lean_int_mul(v_milliseconds_1064_, v___x_1070_);
v___x_1072_ = l_Std_Time_Duration_ofNanoseconds(v___x_1071_);
lean_dec(v___x_1071_);
v_second_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_second_1073_);
v_nano_1074_ = lean_ctor_get(v___x_1072_, 1);
lean_inc(v_nano_1074_);
lean_dec_ref(v___x_1072_);
v_second_1075_ = lean_ctor_get(v_timestamp_1065_, 0);
lean_inc(v_second_1075_);
v_nano_1076_ = lean_ctor_get(v_timestamp_1065_, 1);
lean_inc(v_nano_1076_);
lean_dec_ref(v_timestamp_1065_);
v___x_1077_ = lean_int_neg(v_second_1073_);
lean_dec(v_second_1073_);
v___x_1078_ = lean_int_neg(v_nano_1074_);
lean_dec(v_nano_1074_);
v___x_1079_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1080_ = lean_int_mul(v_second_1075_, v___x_1079_);
lean_dec(v_second_1075_);
v_nanos_1081_ = lean_int_add(v___x_1080_, v_nano_1076_);
lean_dec(v_nano_1076_);
lean_dec(v___x_1080_);
v___x_1082_ = lean_int_mul(v___x_1077_, v___x_1079_);
lean_dec(v___x_1077_);
v_nanos_1083_ = lean_int_add(v___x_1082_, v___x_1078_);
lean_dec(v___x_1078_);
lean_dec(v___x_1082_);
v___x_1084_ = lean_int_add(v_nanos_1081_, v_nanos_1083_);
lean_dec(v_nanos_1083_);
lean_dec(v_nanos_1081_);
v___x_1085_ = l_Std_Time_Duration_ofNanoseconds(v___x_1084_);
lean_dec(v___x_1084_);
lean_inc_ref(v_rules_1066_);
v_tz_1086_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1066_, v___x_1085_);
lean_inc_ref(v___x_1085_);
lean_inc_ref(v_tz_1086_);
v___f_1087_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1087_, 0, v_tz_1086_);
lean_closure_set(v___f_1087_, 1, v___x_1085_);
lean_closure_set(v___f_1087_, 2, v___x_1079_);
v___x_1088_ = lean_mk_thunk(v___f_1087_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 3, v_tz_1086_);
lean_ctor_set(v___x_1068_, 1, v___x_1085_);
lean_ctor_set(v___x_1068_, 0, v___x_1088_);
v___x_1090_ = v___x_1068_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_rules_1066_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_tz_1086_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subMilliseconds___boxed(lean_object* v_dt_1095_, lean_object* v_milliseconds_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_Time_DateTime_subMilliseconds(v_dt_1095_, v_milliseconds_1096_);
lean_dec(v_milliseconds_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds(lean_object* v_dt_1098_, lean_object* v_seconds_1099_){
_start:
{
lean_object* v_timestamp_1100_; lean_object* v_rules_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1121_; 
v_timestamp_1100_ = lean_ctor_get(v_dt_1098_, 1);
v_rules_1101_ = lean_ctor_get(v_dt_1098_, 2);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_dt_1098_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; lean_object* v_unused_1123_; 
v_unused_1122_ = lean_ctor_get(v_dt_1098_, 3);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_dt_1098_, 0);
lean_dec(v_unused_1123_);
v___x_1103_ = v_dt_1098_;
v_isShared_1104_ = v_isSharedCheck_1121_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_rules_1101_);
lean_inc(v_timestamp_1100_);
lean_dec(v_dt_1098_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1121_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v_second_1105_; lean_object* v_nano_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_nanos_1110_; lean_object* v___x_1111_; lean_object* v_nanos_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v_tz_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v_second_1105_ = lean_ctor_get(v_timestamp_1100_, 0);
lean_inc(v_second_1105_);
v_nano_1106_ = lean_ctor_get(v_timestamp_1100_, 1);
lean_inc(v_nano_1106_);
lean_dec_ref(v_timestamp_1100_);
v___x_1107_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1108_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1109_ = lean_int_mul(v_second_1105_, v___x_1108_);
lean_dec(v_second_1105_);
v_nanos_1110_ = lean_int_add(v___x_1109_, v_nano_1106_);
lean_dec(v_nano_1106_);
lean_dec(v___x_1109_);
v___x_1111_ = lean_int_mul(v_seconds_1099_, v___x_1108_);
v_nanos_1112_ = lean_int_add(v___x_1111_, v___x_1107_);
lean_dec(v___x_1111_);
v___x_1113_ = lean_int_add(v_nanos_1110_, v_nanos_1112_);
lean_dec(v_nanos_1112_);
lean_dec(v_nanos_1110_);
v___x_1114_ = l_Std_Time_Duration_ofNanoseconds(v___x_1113_);
lean_dec(v___x_1113_);
lean_inc_ref(v_rules_1101_);
v_tz_1115_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1101_, v___x_1114_);
lean_inc_ref(v___x_1114_);
lean_inc_ref(v_tz_1115_);
v___f_1116_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1116_, 0, v_tz_1115_);
lean_closure_set(v___f_1116_, 1, v___x_1114_);
lean_closure_set(v___f_1116_, 2, v___x_1108_);
lean_closure_set(v___f_1116_, 3, v___x_1107_);
v___x_1117_ = lean_mk_thunk(v___f_1116_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 3, v_tz_1115_);
lean_ctor_set(v___x_1103_, 1, v___x_1114_);
lean_ctor_set(v___x_1103_, 0, v___x_1117_);
v___x_1119_ = v___x_1103_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1114_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_rules_1101_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_tz_1115_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addSeconds___boxed(lean_object* v_dt_1124_, lean_object* v_seconds_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Std_Time_DateTime_addSeconds(v_dt_1124_, v_seconds_1125_);
lean_dec(v_seconds_1125_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds(lean_object* v_dt_1127_, lean_object* v_seconds_1128_){
_start:
{
lean_object* v_timestamp_1129_; lean_object* v_rules_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1152_; 
v_timestamp_1129_ = lean_ctor_get(v_dt_1127_, 1);
v_rules_1130_ = lean_ctor_get(v_dt_1127_, 2);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_dt_1127_);
if (v_isSharedCheck_1152_ == 0)
{
lean_object* v_unused_1153_; lean_object* v_unused_1154_; 
v_unused_1153_ = lean_ctor_get(v_dt_1127_, 3);
lean_dec(v_unused_1153_);
v_unused_1154_ = lean_ctor_get(v_dt_1127_, 0);
lean_dec(v_unused_1154_);
v___x_1132_ = v_dt_1127_;
v_isShared_1133_ = v_isSharedCheck_1152_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_rules_1130_);
lean_inc(v_timestamp_1129_);
lean_dec(v_dt_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1152_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_second_1134_; lean_object* v_nano_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v_nanos_1141_; lean_object* v___x_1142_; lean_object* v_nanos_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v_tz_1146_; lean_object* v___f_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v_second_1134_ = lean_ctor_get(v_timestamp_1129_, 0);
lean_inc(v_second_1134_);
v_nano_1135_ = lean_ctor_get(v_timestamp_1129_, 1);
lean_inc(v_nano_1135_);
lean_dec_ref(v_timestamp_1129_);
v___x_1136_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1137_ = lean_int_neg(v_seconds_1128_);
v___x_1138_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1139_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1140_ = lean_int_mul(v_second_1134_, v___x_1139_);
lean_dec(v_second_1134_);
v_nanos_1141_ = lean_int_add(v___x_1140_, v_nano_1135_);
lean_dec(v_nano_1135_);
lean_dec(v___x_1140_);
v___x_1142_ = lean_int_mul(v___x_1137_, v___x_1139_);
lean_dec(v___x_1137_);
v_nanos_1143_ = lean_int_add(v___x_1142_, v___x_1138_);
lean_dec(v___x_1142_);
v___x_1144_ = lean_int_add(v_nanos_1141_, v_nanos_1143_);
lean_dec(v_nanos_1143_);
lean_dec(v_nanos_1141_);
v___x_1145_ = l_Std_Time_Duration_ofNanoseconds(v___x_1144_);
lean_dec(v___x_1144_);
lean_inc_ref(v_rules_1130_);
v_tz_1146_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1130_, v___x_1145_);
lean_inc_ref(v___x_1145_);
lean_inc_ref(v_tz_1146_);
v___f_1147_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addDays___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1147_, 0, v_tz_1146_);
lean_closure_set(v___f_1147_, 1, v___x_1145_);
lean_closure_set(v___f_1147_, 2, v___x_1139_);
lean_closure_set(v___f_1147_, 3, v___x_1136_);
v___x_1148_ = lean_mk_thunk(v___f_1147_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 3, v_tz_1146_);
lean_ctor_set(v___x_1132_, 1, v___x_1145_);
lean_ctor_set(v___x_1132_, 0, v___x_1148_);
v___x_1150_ = v___x_1132_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_rules_1130_);
lean_ctor_set(v_reuseFailAlloc_1151_, 3, v_tz_1146_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subSeconds___boxed(lean_object* v_dt_1155_, lean_object* v_seconds_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std_Time_DateTime_subSeconds(v_dt_1155_, v_seconds_1156_);
lean_dec(v_seconds_1156_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds(lean_object* v_dt_1158_, lean_object* v_nanoseconds_1159_){
_start:
{
lean_object* v_timestamp_1160_; lean_object* v_rules_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1183_; 
v_timestamp_1160_ = lean_ctor_get(v_dt_1158_, 1);
v_rules_1161_ = lean_ctor_get(v_dt_1158_, 2);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_dt_1158_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; lean_object* v_unused_1185_; 
v_unused_1184_ = lean_ctor_get(v_dt_1158_, 3);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_dt_1158_, 0);
lean_dec(v_unused_1185_);
v___x_1163_ = v_dt_1158_;
v_isShared_1164_ = v_isSharedCheck_1183_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_rules_1161_);
lean_inc(v_timestamp_1160_);
lean_dec(v_dt_1158_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1183_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v_second_1165_; lean_object* v_nano_1166_; lean_object* v___x_1167_; lean_object* v_second_1168_; lean_object* v_nano_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v_nanos_1172_; lean_object* v___x_1173_; lean_object* v_nanos_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v_tz_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v_second_1165_ = lean_ctor_get(v_timestamp_1160_, 0);
lean_inc(v_second_1165_);
v_nano_1166_ = lean_ctor_get(v_timestamp_1160_, 1);
lean_inc(v_nano_1166_);
lean_dec_ref(v_timestamp_1160_);
v___x_1167_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1159_);
v_second_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_second_1168_);
v_nano_1169_ = lean_ctor_get(v___x_1167_, 1);
lean_inc(v_nano_1169_);
lean_dec_ref(v___x_1167_);
v___x_1170_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1171_ = lean_int_mul(v_second_1165_, v___x_1170_);
lean_dec(v_second_1165_);
v_nanos_1172_ = lean_int_add(v___x_1171_, v_nano_1166_);
lean_dec(v_nano_1166_);
lean_dec(v___x_1171_);
v___x_1173_ = lean_int_mul(v_second_1168_, v___x_1170_);
lean_dec(v_second_1168_);
v_nanos_1174_ = lean_int_add(v___x_1173_, v_nano_1169_);
lean_dec(v_nano_1169_);
lean_dec(v___x_1173_);
v___x_1175_ = lean_int_add(v_nanos_1172_, v_nanos_1174_);
lean_dec(v_nanos_1174_);
lean_dec(v_nanos_1172_);
v___x_1176_ = l_Std_Time_Duration_ofNanoseconds(v___x_1175_);
lean_dec(v___x_1175_);
lean_inc_ref(v_rules_1161_);
v_tz_1177_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1161_, v___x_1176_);
lean_inc_ref(v___x_1176_);
lean_inc_ref(v_tz_1177_);
v___f_1178_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1178_, 0, v_tz_1177_);
lean_closure_set(v___f_1178_, 1, v___x_1176_);
lean_closure_set(v___f_1178_, 2, v___x_1170_);
v___x_1179_ = lean_mk_thunk(v___f_1178_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 3, v_tz_1177_);
lean_ctor_set(v___x_1163_, 1, v___x_1176_);
lean_ctor_set(v___x_1163_, 0, v___x_1179_);
v___x_1181_ = v___x_1163_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_rules_1161_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v_tz_1177_);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_addNanoseconds___boxed(lean_object* v_dt_1186_, lean_object* v_nanoseconds_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Std_Time_DateTime_addNanoseconds(v_dt_1186_, v_nanoseconds_1187_);
lean_dec(v_nanoseconds_1187_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds(lean_object* v_dt_1189_, lean_object* v_nanoseconds_1190_){
_start:
{
lean_object* v_timestamp_1191_; lean_object* v_rules_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1216_; 
v_timestamp_1191_ = lean_ctor_get(v_dt_1189_, 1);
v_rules_1192_ = lean_ctor_get(v_dt_1189_, 2);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_dt_1189_);
if (v_isSharedCheck_1216_ == 0)
{
lean_object* v_unused_1217_; lean_object* v_unused_1218_; 
v_unused_1217_ = lean_ctor_get(v_dt_1189_, 3);
lean_dec(v_unused_1217_);
v_unused_1218_ = lean_ctor_get(v_dt_1189_, 0);
lean_dec(v_unused_1218_);
v___x_1194_ = v_dt_1189_;
v_isShared_1195_ = v_isSharedCheck_1216_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_rules_1192_);
lean_inc(v_timestamp_1191_);
lean_dec(v_dt_1189_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1216_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v_second_1197_; lean_object* v_nano_1198_; lean_object* v_second_1199_; lean_object* v_nano_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v_nanos_1205_; lean_object* v___x_1206_; lean_object* v_nanos_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_tz_1210_; lean_object* v___f_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1196_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_1190_);
v_second_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_second_1197_);
v_nano_1198_ = lean_ctor_get(v___x_1196_, 1);
lean_inc(v_nano_1198_);
lean_dec_ref(v___x_1196_);
v_second_1199_ = lean_ctor_get(v_timestamp_1191_, 0);
lean_inc(v_second_1199_);
v_nano_1200_ = lean_ctor_get(v_timestamp_1191_, 1);
lean_inc(v_nano_1200_);
lean_dec_ref(v_timestamp_1191_);
v___x_1201_ = lean_int_neg(v_second_1197_);
lean_dec(v_second_1197_);
v___x_1202_ = lean_int_neg(v_nano_1198_);
lean_dec(v_nano_1198_);
v___x_1203_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1204_ = lean_int_mul(v_second_1199_, v___x_1203_);
lean_dec(v_second_1199_);
v_nanos_1205_ = lean_int_add(v___x_1204_, v_nano_1200_);
lean_dec(v_nano_1200_);
lean_dec(v___x_1204_);
v___x_1206_ = lean_int_mul(v___x_1201_, v___x_1203_);
lean_dec(v___x_1201_);
v_nanos_1207_ = lean_int_add(v___x_1206_, v___x_1202_);
lean_dec(v___x_1202_);
lean_dec(v___x_1206_);
v___x_1208_ = lean_int_add(v_nanos_1205_, v_nanos_1207_);
lean_dec(v_nanos_1207_);
lean_dec(v_nanos_1205_);
v___x_1209_ = l_Std_Time_Duration_ofNanoseconds(v___x_1208_);
lean_dec(v___x_1208_);
lean_inc_ref(v_rules_1192_);
v_tz_1210_ = l_Std_Time_TimeZone_ZoneRules_timezoneAt(v_rules_1192_, v___x_1209_);
lean_inc_ref(v___x_1209_);
lean_inc_ref(v_tz_1210_);
v___f_1211_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMilliseconds___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1211_, 0, v_tz_1210_);
lean_closure_set(v___f_1211_, 1, v___x_1209_);
lean_closure_set(v___f_1211_, 2, v___x_1203_);
v___x_1212_ = lean_mk_thunk(v___f_1211_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 3, v_tz_1210_);
lean_ctor_set(v___x_1194_, 1, v___x_1209_);
lean_ctor_set(v___x_1194_, 0, v___x_1212_);
v___x_1214_ = v___x_1194_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_rules_1192_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_tz_1210_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_subNanoseconds___boxed(lean_object* v_dt_1219_, lean_object* v_nanoseconds_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Std_Time_DateTime_subNanoseconds(v_dt_1219_, v_nanoseconds_1220_);
lean_dec(v_nanoseconds_1220_);
return v_res_1221_;
}
}
uint8_t l_Std_Time_DateTime_era(lean_object* v_date_1222_){
_start:
{
lean_object* v_date_1223_; lean_object* v___x_1224_; lean_object* v_date_1225_; lean_object* v_year_1226_; uint8_t v___x_1227_; 
v_date_1223_ = lean_ctor_get(v_date_1222_, 0);
v___x_1224_ = lean_thunk_get_own(v_date_1223_);
v_date_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc_ref(v_date_1225_);
lean_dec(v___x_1224_);
v_year_1226_ = lean_ctor_get(v_date_1225_, 0);
lean_inc(v_year_1226_);
lean_dec_ref(v_date_1225_);
v___x_1227_ = l_Std_Time_Year_Offset_era(v_year_1226_);
lean_dec(v_year_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT void l_Std_Time_DateTime_era_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1222_ = stack[0].m_obj;
uint8_t v_res_1228_;
v_res_1228_ = l_Std_Time_DateTime_era(v_date_1222_);
stack->m_num = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_era___boxed(lean_object* v_date_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_Std_Time_DateTime_era(v_date_1229_);
lean_dec_ref(v_date_1229_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
lean_object* l_Std_Time_DateTime_withWeekday(lean_object* v_dt_1232_, uint8_t v_desiredWeekday_1233_){
_start:
{
lean_object* v_date_1234_; lean_object* v_rules_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1261_; 
v_date_1234_ = lean_ctor_get(v_dt_1232_, 0);
v_rules_1235_ = lean_ctor_get(v_dt_1232_, 2);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_dt_1232_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; lean_object* v_unused_1263_; 
v_unused_1262_ = lean_ctor_get(v_dt_1232_, 3);
lean_dec(v_unused_1262_);
v_unused_1263_ = lean_ctor_get(v_dt_1232_, 1);
lean_dec(v_unused_1263_);
v___x_1237_ = v_dt_1232_;
v_isShared_1238_ = v_isSharedCheck_1261_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_rules_1235_);
lean_inc(v_date_1234_);
lean_dec(v_dt_1232_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1261_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v_date_1239_; lean_object* v___x_1240_; lean_object* v_wt_1241_; lean_object* v_ltt_1242_; lean_object* v_tz_1243_; lean_object* v_offset_1244_; lean_object* v_second_1245_; lean_object* v_nano_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v_nanos_1253_; lean_object* v___x_1254_; lean_object* v_nanos_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_date_1239_ = lean_thunk_get_own(v_date_1234_);
lean_dec_ref(v_date_1234_);
v___x_1240_ = l_Std_Time_PlainDateTime_withWeekday(v_date_1239_, v_desiredWeekday_1233_);
lean_inc_ref(v___x_1240_);
v_wt_1241_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1240_);
lean_inc_ref(v_rules_1235_);
v_ltt_1242_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1235_, v_wt_1241_);
v_tz_1243_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1242_);
lean_dec_ref(v_ltt_1242_);
v_offset_1244_ = lean_ctor_get(v_tz_1243_, 0);
v_second_1245_ = lean_ctor_get(v_wt_1241_, 0);
lean_inc(v_second_1245_);
v_nano_1246_ = lean_ctor_get(v_wt_1241_, 1);
lean_inc(v_nano_1246_);
lean_dec_ref(v_wt_1241_);
v___f_1247_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1247_, 0, v___x_1240_);
v___x_1248_ = lean_mk_thunk(v___f_1247_);
v___x_1249_ = lean_int_neg(v_offset_1244_);
v___x_1250_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1251_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1252_ = lean_int_mul(v_second_1245_, v___x_1251_);
lean_dec(v_second_1245_);
v_nanos_1253_ = lean_int_add(v___x_1252_, v_nano_1246_);
lean_dec(v_nano_1246_);
lean_dec(v___x_1252_);
v___x_1254_ = lean_int_mul(v___x_1249_, v___x_1251_);
lean_dec(v___x_1249_);
v_nanos_1255_ = lean_int_add(v___x_1254_, v___x_1250_);
lean_dec(v___x_1254_);
v___x_1256_ = lean_int_add(v_nanos_1253_, v_nanos_1255_);
lean_dec(v_nanos_1255_);
lean_dec(v_nanos_1253_);
v___x_1257_ = l_Std_Time_Duration_ofNanoseconds(v___x_1256_);
lean_dec(v___x_1256_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 3, v_tz_1243_);
lean_ctor_set(v___x_1237_, 1, v___x_1257_);
lean_ctor_set(v___x_1237_, 0, v___x_1248_);
v___x_1259_ = v___x_1237_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_rules_1235_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_tz_1243_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
LEAN_EXPORT void l_Std_Time_DateTime_withWeekday_0interp(lean_interpreter_value* stack)
{
lean_object* v_dt_1232_ = stack[0].m_obj;
uint8_t v_desiredWeekday_1233_ = stack[1].m_num;
lean_object* v_res_1264_;
v_res_1264_ = l_Std_Time_DateTime_withWeekday(v_dt_1232_, v_desiredWeekday_1233_);
stack->m_obj
 = v_res_1264_;
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withWeekday___boxed(lean_object* v_dt_1265_, lean_object* v_desiredWeekday_1266_){
_start:
{
uint8_t v_desiredWeekday_boxed_1267_; lean_object* v_res_1268_; 
v_desiredWeekday_boxed_1267_ = lean_unbox(v_desiredWeekday_1266_);
v_res_1268_ = l_Std_Time_DateTime_withWeekday(v_dt_1265_, v_desiredWeekday_boxed_1267_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysClip(lean_object* v_dt_1269_, lean_object* v_days_1270_){
_start:
{
lean_object* v_date_1271_; lean_object* v_rules_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1337_; 
v_date_1271_ = lean_ctor_get(v_dt_1269_, 0);
v_rules_1272_ = lean_ctor_get(v_dt_1269_, 2);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_dt_1269_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; lean_object* v_unused_1339_; 
v_unused_1338_ = lean_ctor_get(v_dt_1269_, 3);
lean_dec(v_unused_1338_);
v_unused_1339_ = lean_ctor_get(v_dt_1269_, 1);
lean_dec(v_unused_1339_);
v___x_1274_ = v_dt_1269_;
v_isShared_1275_ = v_isSharedCheck_1337_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_rules_1272_);
lean_inc(v_date_1271_);
lean_dec(v_dt_1269_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1337_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v_date_1276_; lean_object* v___y_1278_; lean_object* v_date_1308_; lean_object* v_year_1309_; lean_object* v_month_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1335_; 
v_date_1276_ = lean_thunk_get_own(v_date_1271_);
lean_dec_ref(v_date_1271_);
v_date_1308_ = lean_ctor_get(v_date_1276_, 0);
lean_inc_ref(v_date_1308_);
v_year_1309_ = lean_ctor_get(v_date_1308_, 0);
v_month_1310_ = lean_ctor_get(v_date_1308_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_date_1308_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_date_1308_, 2);
lean_dec(v_unused_1336_);
v___x_1312_ = v_date_1308_;
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_month_1310_);
lean_inc(v_year_1309_);
lean_dec(v_date_1308_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1335_;
goto v_resetjp_1311_;
}
v___jp_1277_:
{
lean_object* v_time_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1306_; 
v_time_1279_ = lean_ctor_get(v_date_1276_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_date_1276_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_date_1276_, 0);
lean_dec(v_unused_1307_);
v___x_1281_ = v_date_1276_;
v_isShared_1282_ = v_isSharedCheck_1306_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_time_1279_);
lean_dec(v_date_1276_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1306_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___y_1278_);
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___y_1278_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_time_1279_);
v___x_1284_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v_wt_1285_; lean_object* v_ltt_1286_; lean_object* v_tz_1287_; lean_object* v_offset_1288_; lean_object* v_second_1289_; lean_object* v_nano_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v_nanos_1297_; lean_object* v___x_1298_; lean_object* v_nanos_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1303_; 
lean_inc_ref(v___x_1284_);
v_wt_1285_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1284_);
lean_inc_ref(v_rules_1272_);
v_ltt_1286_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1272_, v_wt_1285_);
v_tz_1287_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1286_);
lean_dec_ref(v_ltt_1286_);
v_offset_1288_ = lean_ctor_get(v_tz_1287_, 0);
v_second_1289_ = lean_ctor_get(v_wt_1285_, 0);
lean_inc(v_second_1289_);
v_nano_1290_ = lean_ctor_get(v_wt_1285_, 1);
lean_inc(v_nano_1290_);
lean_dec_ref(v_wt_1285_);
v___f_1291_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1291_, 0, v___x_1284_);
v___x_1292_ = lean_mk_thunk(v___f_1291_);
v___x_1293_ = lean_int_neg(v_offset_1288_);
v___x_1294_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1295_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1296_ = lean_int_mul(v_second_1289_, v___x_1295_);
lean_dec(v_second_1289_);
v_nanos_1297_ = lean_int_add(v___x_1296_, v_nano_1290_);
lean_dec(v_nano_1290_);
lean_dec(v___x_1296_);
v___x_1298_ = lean_int_mul(v___x_1293_, v___x_1295_);
lean_dec(v___x_1293_);
v_nanos_1299_ = lean_int_add(v___x_1298_, v___x_1294_);
lean_dec(v___x_1298_);
v___x_1300_ = lean_int_add(v_nanos_1297_, v_nanos_1299_);
lean_dec(v_nanos_1299_);
lean_dec(v_nanos_1297_);
v___x_1301_ = l_Std_Time_Duration_ofNanoseconds(v___x_1300_);
lean_dec(v___x_1300_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 3, v_tz_1287_);
lean_ctor_set(v___x_1274_, 1, v___x_1301_);
lean_ctor_set(v___x_1274_, 0, v___x_1292_);
v___x_1303_ = v___x_1274_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v_rules_1272_);
lean_ctor_set(v_reuseFailAlloc_1304_, 3, v_tz_1287_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
v_resetjp_1311_:
{
uint8_t v___y_1315_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; uint8_t v___x_1331_; 
v___x_1324_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1325_ = lean_int_mod(v_year_1309_, v___x_1324_);
v___x_1326_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1331_ = lean_int_dec_eq(v___x_1325_, v___x_1326_);
lean_dec(v___x_1325_);
if (v___x_1331_ == 0)
{
v___y_1315_ = v___x_1331_;
goto v___jp_1314_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1332_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1333_ = lean_int_mod(v_year_1309_, v___x_1332_);
v___x_1334_ = lean_int_dec_eq(v___x_1333_, v___x_1326_);
lean_dec(v___x_1333_);
if (v___x_1334_ == 0)
{
if (v___x_1331_ == 0)
{
goto v___jp_1327_;
}
else
{
v___y_1315_ = v___x_1331_;
goto v___jp_1314_;
}
}
else
{
goto v___jp_1327_;
}
}
v___jp_1314_:
{
lean_object* v_max_1316_; uint8_t v___x_1317_; 
v_max_1316_ = l_Std_Time_Month_Ordinal_days(v___y_1315_, v_month_1310_);
v___x_1317_ = lean_int_dec_lt(v_max_1316_, v_days_1270_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1319_; 
lean_dec(v_max_1316_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 2, v_days_1270_);
v___x_1319_ = v___x_1312_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_year_1309_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_month_1310_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_days_1270_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
v___y_1278_ = v___x_1319_;
goto v___jp_1277_;
}
}
else
{
lean_object* v___x_1322_; 
lean_dec(v_days_1270_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 2, v_max_1316_);
v___x_1322_ = v___x_1312_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_year_1309_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_month_1310_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_max_1316_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
v___y_1278_ = v___x_1322_;
goto v___jp_1277_;
}
}
}
v___jp_1327_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1329_ = lean_int_mod(v_year_1309_, v___x_1328_);
v___x_1330_ = lean_int_dec_eq(v___x_1329_, v___x_1326_);
lean_dec(v___x_1329_);
v___y_1315_ = v___x_1330_;
goto v___jp_1314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver(lean_object* v_dt_1340_, lean_object* v_days_1341_){
_start:
{
lean_object* v_date_1342_; lean_object* v_rules_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1380_; 
v_date_1342_ = lean_ctor_get(v_dt_1340_, 0);
v_rules_1343_ = lean_ctor_get(v_dt_1340_, 2);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_dt_1340_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; lean_object* v_unused_1382_; 
v_unused_1381_ = lean_ctor_get(v_dt_1340_, 3);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_dt_1340_, 1);
lean_dec(v_unused_1382_);
v___x_1345_ = v_dt_1340_;
v_isShared_1346_ = v_isSharedCheck_1380_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_rules_1343_);
lean_inc(v_date_1342_);
lean_dec(v_dt_1340_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1380_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_date_1347_; lean_object* v_date_1348_; lean_object* v_time_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1379_; 
v_date_1347_ = lean_thunk_get_own(v_date_1342_);
lean_dec_ref(v_date_1342_);
v_date_1348_ = lean_ctor_get(v_date_1347_, 0);
v_time_1349_ = lean_ctor_get(v_date_1347_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_date_1347_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1351_ = v_date_1347_;
v_isShared_1352_ = v_isSharedCheck_1379_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_time_1349_);
lean_inc(v_date_1348_);
lean_dec(v_date_1347_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1379_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v_year_1353_; lean_object* v_month_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v_year_1353_ = lean_ctor_get(v_date_1348_, 0);
lean_inc(v_year_1353_);
v_month_1354_ = lean_ctor_get(v_date_1348_, 1);
lean_inc(v_month_1354_);
lean_dec_ref(v_date_1348_);
v___x_1355_ = l_Std_Time_PlainDate_rollOver(v_year_1353_, v_month_1354_, v_days_1341_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 0, v___x_1355_);
v___x_1357_ = v___x_1351_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_time_1349_);
v___x_1357_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v_wt_1358_; lean_object* v_ltt_1359_; lean_object* v_tz_1360_; lean_object* v_offset_1361_; lean_object* v_second_1362_; lean_object* v_nano_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_nanos_1370_; lean_object* v___x_1371_; lean_object* v_nanos_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_inc_ref(v___x_1357_);
v_wt_1358_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1357_);
lean_inc_ref(v_rules_1343_);
v_ltt_1359_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1343_, v_wt_1358_);
v_tz_1360_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1359_);
lean_dec_ref(v_ltt_1359_);
v_offset_1361_ = lean_ctor_get(v_tz_1360_, 0);
v_second_1362_ = lean_ctor_get(v_wt_1358_, 0);
lean_inc(v_second_1362_);
v_nano_1363_ = lean_ctor_get(v_wt_1358_, 1);
lean_inc(v_nano_1363_);
lean_dec_ref(v_wt_1358_);
v___f_1364_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1364_, 0, v___x_1357_);
v___x_1365_ = lean_mk_thunk(v___f_1364_);
v___x_1366_ = lean_int_neg(v_offset_1361_);
v___x_1367_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1368_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1369_ = lean_int_mul(v_second_1362_, v___x_1368_);
lean_dec(v_second_1362_);
v_nanos_1370_ = lean_int_add(v___x_1369_, v_nano_1363_);
lean_dec(v_nano_1363_);
lean_dec(v___x_1369_);
v___x_1371_ = lean_int_mul(v___x_1366_, v___x_1368_);
lean_dec(v___x_1366_);
v_nanos_1372_ = lean_int_add(v___x_1371_, v___x_1367_);
lean_dec(v___x_1371_);
v___x_1373_ = lean_int_add(v_nanos_1370_, v_nanos_1372_);
lean_dec(v_nanos_1372_);
lean_dec(v_nanos_1370_);
v___x_1374_ = l_Std_Time_Duration_ofNanoseconds(v___x_1373_);
lean_dec(v___x_1373_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 3, v_tz_1360_);
lean_ctor_set(v___x_1345_, 1, v___x_1374_);
lean_ctor_set(v___x_1345_, 0, v___x_1365_);
v___x_1376_ = v___x_1345_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_rules_1343_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_tz_1360_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withDaysRollOver___boxed(lean_object* v_dt_1383_, lean_object* v_days_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Std_Time_DateTime_withDaysRollOver(v_dt_1383_, v_days_1384_);
lean_dec(v_days_1384_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMonthClip(lean_object* v_dt_1386_, lean_object* v_month_1387_){
_start:
{
lean_object* v_date_1388_; lean_object* v_rules_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1454_; 
v_date_1388_ = lean_ctor_get(v_dt_1386_, 0);
v_rules_1389_ = lean_ctor_get(v_dt_1386_, 2);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_dt_1386_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; lean_object* v_unused_1456_; 
v_unused_1455_ = lean_ctor_get(v_dt_1386_, 3);
lean_dec(v_unused_1455_);
v_unused_1456_ = lean_ctor_get(v_dt_1386_, 1);
lean_dec(v_unused_1456_);
v___x_1391_ = v_dt_1386_;
v_isShared_1392_ = v_isSharedCheck_1454_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_rules_1389_);
lean_inc(v_date_1388_);
lean_dec(v_dt_1386_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1454_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_date_1393_; lean_object* v___y_1395_; lean_object* v_date_1425_; lean_object* v_year_1426_; lean_object* v_day_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1452_; 
v_date_1393_ = lean_thunk_get_own(v_date_1388_);
lean_dec_ref(v_date_1388_);
v_date_1425_ = lean_ctor_get(v_date_1393_, 0);
lean_inc_ref(v_date_1425_);
v_year_1426_ = lean_ctor_get(v_date_1425_, 0);
v_day_1427_ = lean_ctor_get(v_date_1425_, 2);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_date_1425_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_date_1425_, 1);
lean_dec(v_unused_1453_);
v___x_1429_ = v_date_1425_;
v_isShared_1430_ = v_isSharedCheck_1452_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_day_1427_);
lean_inc(v_year_1426_);
lean_dec(v_date_1425_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1452_;
goto v_resetjp_1428_;
}
v___jp_1394_:
{
lean_object* v_time_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1423_; 
v_time_1396_ = lean_ctor_get(v_date_1393_, 1);
v_isSharedCheck_1423_ = !lean_is_exclusive(v_date_1393_);
if (v_isSharedCheck_1423_ == 0)
{
lean_object* v_unused_1424_; 
v_unused_1424_ = lean_ctor_get(v_date_1393_, 0);
lean_dec(v_unused_1424_);
v___x_1398_ = v_date_1393_;
v_isShared_1399_ = v_isSharedCheck_1423_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_time_1396_);
lean_dec(v_date_1393_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1423_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___y_1395_);
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___y_1395_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_time_1396_);
v___x_1401_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v_wt_1402_; lean_object* v_ltt_1403_; lean_object* v_tz_1404_; lean_object* v_offset_1405_; lean_object* v_second_1406_; lean_object* v_nano_1407_; lean_object* v___f_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v_nanos_1414_; lean_object* v___x_1415_; lean_object* v_nanos_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1420_; 
lean_inc_ref(v___x_1401_);
v_wt_1402_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1401_);
lean_inc_ref(v_rules_1389_);
v_ltt_1403_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1389_, v_wt_1402_);
v_tz_1404_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1403_);
lean_dec_ref(v_ltt_1403_);
v_offset_1405_ = lean_ctor_get(v_tz_1404_, 0);
v_second_1406_ = lean_ctor_get(v_wt_1402_, 0);
lean_inc(v_second_1406_);
v_nano_1407_ = lean_ctor_get(v_wt_1402_, 1);
lean_inc(v_nano_1407_);
lean_dec_ref(v_wt_1402_);
v___f_1408_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1408_, 0, v___x_1401_);
v___x_1409_ = lean_mk_thunk(v___f_1408_);
v___x_1410_ = lean_int_neg(v_offset_1405_);
v___x_1411_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1412_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1413_ = lean_int_mul(v_second_1406_, v___x_1412_);
lean_dec(v_second_1406_);
v_nanos_1414_ = lean_int_add(v___x_1413_, v_nano_1407_);
lean_dec(v_nano_1407_);
lean_dec(v___x_1413_);
v___x_1415_ = lean_int_mul(v___x_1410_, v___x_1412_);
lean_dec(v___x_1410_);
v_nanos_1416_ = lean_int_add(v___x_1415_, v___x_1411_);
lean_dec(v___x_1415_);
v___x_1417_ = lean_int_add(v_nanos_1414_, v_nanos_1416_);
lean_dec(v_nanos_1416_);
lean_dec(v_nanos_1414_);
v___x_1418_ = l_Std_Time_Duration_ofNanoseconds(v___x_1417_);
lean_dec(v___x_1417_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 3, v_tz_1404_);
lean_ctor_set(v___x_1391_, 1, v___x_1418_);
lean_ctor_set(v___x_1391_, 0, v___x_1409_);
v___x_1420_ = v___x_1391_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1409_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_rules_1389_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_tz_1404_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
v_resetjp_1428_:
{
uint8_t v___y_1432_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1448_; 
v___x_1441_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1442_ = lean_int_mod(v_year_1426_, v___x_1441_);
v___x_1443_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1448_ = lean_int_dec_eq(v___x_1442_, v___x_1443_);
lean_dec(v___x_1442_);
if (v___x_1448_ == 0)
{
v___y_1432_ = v___x_1448_;
goto v___jp_1431_;
}
else
{
lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v___x_1449_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1450_ = lean_int_mod(v_year_1426_, v___x_1449_);
v___x_1451_ = lean_int_dec_eq(v___x_1450_, v___x_1443_);
lean_dec(v___x_1450_);
if (v___x_1451_ == 0)
{
if (v___x_1448_ == 0)
{
goto v___jp_1444_;
}
else
{
v___y_1432_ = v___x_1448_;
goto v___jp_1431_;
}
}
else
{
goto v___jp_1444_;
}
}
v___jp_1431_:
{
lean_object* v_max_1433_; uint8_t v___x_1434_; 
v_max_1433_ = l_Std_Time_Month_Ordinal_days(v___y_1432_, v_month_1387_);
v___x_1434_ = lean_int_dec_lt(v_max_1433_, v_day_1427_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1436_; 
lean_dec(v_max_1433_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 1, v_month_1387_);
v___x_1436_ = v___x_1429_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_year_1426_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_month_1387_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_day_1427_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
v___y_1395_ = v___x_1436_;
goto v___jp_1394_;
}
}
else
{
lean_object* v___x_1439_; 
lean_dec(v_day_1427_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 2, v_max_1433_);
lean_ctor_set(v___x_1429_, 1, v_month_1387_);
v___x_1439_ = v___x_1429_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_year_1426_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_month_1387_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_max_1433_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v___y_1395_ = v___x_1439_;
goto v___jp_1394_;
}
}
}
v___jp_1444_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1445_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1446_ = lean_int_mod(v_year_1426_, v___x_1445_);
v___x_1447_ = lean_int_dec_eq(v___x_1446_, v___x_1443_);
lean_dec(v___x_1446_);
v___y_1432_ = v___x_1447_;
goto v___jp_1431_;
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
lean_object* v_wt_1475_; lean_object* v_ltt_1476_; lean_object* v_tz_1477_; lean_object* v_offset_1478_; lean_object* v_second_1479_; lean_object* v_nano_1480_; lean_object* v___f_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_nanos_1487_; lean_object* v___x_1488_; lean_object* v_nanos_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
lean_inc_ref(v___x_1474_);
v_wt_1475_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1474_);
lean_inc_ref(v_rules_1460_);
v_ltt_1476_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1460_, v_wt_1475_);
v_tz_1477_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1476_);
lean_dec_ref(v_ltt_1476_);
v_offset_1478_ = lean_ctor_get(v_tz_1477_, 0);
v_second_1479_ = lean_ctor_get(v_wt_1475_, 0);
lean_inc(v_second_1479_);
v_nano_1480_ = lean_ctor_get(v_wt_1475_, 1);
lean_inc(v_nano_1480_);
lean_dec_ref(v_wt_1475_);
v___f_1481_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1481_, 0, v___x_1474_);
v___x_1482_ = lean_mk_thunk(v___f_1481_);
v___x_1483_ = lean_int_neg(v_offset_1478_);
v___x_1484_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1485_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1486_ = lean_int_mul(v_second_1479_, v___x_1485_);
lean_dec(v_second_1479_);
v_nanos_1487_ = lean_int_add(v___x_1486_, v_nano_1480_);
lean_dec(v_nano_1480_);
lean_dec(v___x_1486_);
v___x_1488_ = lean_int_mul(v___x_1483_, v___x_1485_);
lean_dec(v___x_1483_);
v_nanos_1489_ = lean_int_add(v___x_1488_, v___x_1484_);
lean_dec(v___x_1488_);
v___x_1490_ = lean_int_add(v_nanos_1487_, v_nanos_1489_);
lean_dec(v_nanos_1489_);
lean_dec(v_nanos_1487_);
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
lean_object* v_date_1502_; lean_object* v_rules_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1568_; 
v_date_1502_ = lean_ctor_get(v_dt_1500_, 0);
v_rules_1503_ = lean_ctor_get(v_dt_1500_, 2);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_dt_1500_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; lean_object* v_unused_1570_; 
v_unused_1569_ = lean_ctor_get(v_dt_1500_, 3);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_dt_1500_, 1);
lean_dec(v_unused_1570_);
v___x_1505_ = v_dt_1500_;
v_isShared_1506_ = v_isSharedCheck_1568_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_rules_1503_);
lean_inc(v_date_1502_);
lean_dec(v_dt_1500_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1568_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_date_1507_; lean_object* v___y_1509_; lean_object* v_date_1539_; lean_object* v_month_1540_; lean_object* v_day_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1566_; 
v_date_1507_ = lean_thunk_get_own(v_date_1502_);
lean_dec_ref(v_date_1502_);
v_date_1539_ = lean_ctor_get(v_date_1507_, 0);
lean_inc_ref(v_date_1539_);
v_month_1540_ = lean_ctor_get(v_date_1539_, 1);
v_day_1541_ = lean_ctor_get(v_date_1539_, 2);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_date_1539_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v_date_1539_, 0);
lean_dec(v_unused_1567_);
v___x_1543_ = v_date_1539_;
v_isShared_1544_ = v_isSharedCheck_1566_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_day_1541_);
lean_inc(v_month_1540_);
lean_dec(v_date_1539_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1566_;
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
lean_object* v_wt_1516_; lean_object* v_ltt_1517_; lean_object* v_tz_1518_; lean_object* v_offset_1519_; lean_object* v_second_1520_; lean_object* v_nano_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_nanos_1528_; lean_object* v___x_1529_; lean_object* v_nanos_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
lean_inc_ref(v___x_1515_);
v_wt_1516_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1515_);
lean_inc_ref(v_rules_1503_);
v_ltt_1517_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1503_, v_wt_1516_);
v_tz_1518_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1517_);
lean_dec_ref(v_ltt_1517_);
v_offset_1519_ = lean_ctor_get(v_tz_1518_, 0);
v_second_1520_ = lean_ctor_get(v_wt_1516_, 0);
lean_inc(v_second_1520_);
v_nano_1521_ = lean_ctor_get(v_wt_1516_, 1);
lean_inc(v_nano_1521_);
lean_dec_ref(v_wt_1516_);
v___f_1522_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1522_, 0, v___x_1515_);
v___x_1523_ = lean_mk_thunk(v___f_1522_);
v___x_1524_ = lean_int_neg(v_offset_1519_);
v___x_1525_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1526_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1527_ = lean_int_mul(v_second_1520_, v___x_1526_);
lean_dec(v_second_1520_);
v_nanos_1528_ = lean_int_add(v___x_1527_, v_nano_1521_);
lean_dec(v_nano_1521_);
lean_dec(v___x_1527_);
v___x_1529_ = lean_int_mul(v___x_1524_, v___x_1526_);
lean_dec(v___x_1524_);
v_nanos_1530_ = lean_int_add(v___x_1529_, v___x_1525_);
lean_dec(v___x_1529_);
v___x_1531_ = lean_int_add(v_nanos_1528_, v_nanos_1530_);
lean_dec(v_nanos_1530_);
lean_dec(v_nanos_1528_);
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
uint8_t v___y_1546_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1562_; 
v___x_1555_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1556_ = lean_int_mod(v_year_1501_, v___x_1555_);
v___x_1557_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1562_ = lean_int_dec_eq(v___x_1556_, v___x_1557_);
lean_dec(v___x_1556_);
if (v___x_1562_ == 0)
{
v___y_1546_ = v___x_1562_;
goto v___jp_1545_;
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1563_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1564_ = lean_int_mod(v_year_1501_, v___x_1563_);
v___x_1565_ = lean_int_dec_eq(v___x_1564_, v___x_1557_);
lean_dec(v___x_1564_);
if (v___x_1565_ == 0)
{
if (v___x_1562_ == 0)
{
goto v___jp_1558_;
}
else
{
v___y_1546_ = v___x_1562_;
goto v___jp_1545_;
}
}
else
{
goto v___jp_1558_;
}
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
v___jp_1558_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1559_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1560_ = lean_int_mod(v_year_1501_, v___x_1559_);
v___x_1561_ = lean_int_dec_eq(v___x_1560_, v___x_1557_);
lean_dec(v___x_1560_);
v___y_1546_ = v___x_1561_;
goto v___jp_1545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withYearRollOver(lean_object* v_dt_1571_, lean_object* v_year_1572_){
_start:
{
lean_object* v_date_1573_; lean_object* v_rules_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1611_; 
v_date_1573_ = lean_ctor_get(v_dt_1571_, 0);
v_rules_1574_ = lean_ctor_get(v_dt_1571_, 2);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_dt_1571_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; lean_object* v_unused_1613_; 
v_unused_1612_ = lean_ctor_get(v_dt_1571_, 3);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_dt_1571_, 1);
lean_dec(v_unused_1613_);
v___x_1576_ = v_dt_1571_;
v_isShared_1577_ = v_isSharedCheck_1611_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_rules_1574_);
lean_inc(v_date_1573_);
lean_dec(v_dt_1571_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1611_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v_date_1578_; lean_object* v_date_1579_; lean_object* v_time_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1610_; 
v_date_1578_ = lean_thunk_get_own(v_date_1573_);
lean_dec_ref(v_date_1573_);
v_date_1579_ = lean_ctor_get(v_date_1578_, 0);
v_time_1580_ = lean_ctor_get(v_date_1578_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_date_1578_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1582_ = v_date_1578_;
v_isShared_1583_ = v_isSharedCheck_1610_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_time_1580_);
lean_inc(v_date_1579_);
lean_dec(v_date_1578_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1610_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_month_1584_; lean_object* v_day_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v_month_1584_ = lean_ctor_get(v_date_1579_, 1);
lean_inc(v_month_1584_);
v_day_1585_ = lean_ctor_get(v_date_1579_, 2);
lean_inc(v_day_1585_);
lean_dec_ref(v_date_1579_);
v___x_1586_ = l_Std_Time_PlainDate_rollOver(v_year_1572_, v_month_1584_, v_day_1585_);
lean_dec(v_day_1585_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1586_);
v___x_1588_ = v___x_1582_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_time_1580_);
v___x_1588_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v_wt_1589_; lean_object* v_ltt_1590_; lean_object* v_tz_1591_; lean_object* v_offset_1592_; lean_object* v_second_1593_; lean_object* v_nano_1594_; lean_object* v___f_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v_nanos_1601_; lean_object* v___x_1602_; lean_object* v_nanos_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1607_; 
lean_inc_ref(v___x_1588_);
v_wt_1589_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1588_);
lean_inc_ref(v_rules_1574_);
v_ltt_1590_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1574_, v_wt_1589_);
v_tz_1591_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1590_);
lean_dec_ref(v_ltt_1590_);
v_offset_1592_ = lean_ctor_get(v_tz_1591_, 0);
v_second_1593_ = lean_ctor_get(v_wt_1589_, 0);
lean_inc(v_second_1593_);
v_nano_1594_ = lean_ctor_get(v_wt_1589_, 1);
lean_inc(v_nano_1594_);
lean_dec_ref(v_wt_1589_);
v___f_1595_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1595_, 0, v___x_1588_);
v___x_1596_ = lean_mk_thunk(v___f_1595_);
v___x_1597_ = lean_int_neg(v_offset_1592_);
v___x_1598_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1599_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1600_ = lean_int_mul(v_second_1593_, v___x_1599_);
lean_dec(v_second_1593_);
v_nanos_1601_ = lean_int_add(v___x_1600_, v_nano_1594_);
lean_dec(v_nano_1594_);
lean_dec(v___x_1600_);
v___x_1602_ = lean_int_mul(v___x_1597_, v___x_1599_);
lean_dec(v___x_1597_);
v_nanos_1603_ = lean_int_add(v___x_1602_, v___x_1598_);
lean_dec(v___x_1602_);
v___x_1604_ = lean_int_add(v_nanos_1601_, v_nanos_1603_);
lean_dec(v_nanos_1603_);
lean_dec(v_nanos_1601_);
v___x_1605_ = l_Std_Time_Duration_ofNanoseconds(v___x_1604_);
lean_dec(v___x_1604_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 3, v_tz_1591_);
lean_ctor_set(v___x_1576_, 1, v___x_1605_);
lean_ctor_set(v___x_1576_, 0, v___x_1596_);
v___x_1607_ = v___x_1576_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_rules_1574_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_tz_1591_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withHours(lean_object* v_dt_1614_, lean_object* v_hour_1615_){
_start:
{
lean_object* v_date_1616_; lean_object* v_rules_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1662_; 
v_date_1616_ = lean_ctor_get(v_dt_1614_, 0);
v_rules_1617_ = lean_ctor_get(v_dt_1614_, 2);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_dt_1614_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; lean_object* v_unused_1664_; 
v_unused_1663_ = lean_ctor_get(v_dt_1614_, 3);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_dt_1614_, 1);
lean_dec(v_unused_1664_);
v___x_1619_ = v_dt_1614_;
v_isShared_1620_ = v_isSharedCheck_1662_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_rules_1617_);
lean_inc(v_date_1616_);
lean_dec(v_dt_1614_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1662_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_date_1621_; lean_object* v_time_1622_; lean_object* v_date_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1661_; 
v_date_1621_ = lean_thunk_get_own(v_date_1616_);
lean_dec_ref(v_date_1616_);
v_time_1622_ = lean_ctor_get(v_date_1621_, 1);
v_date_1623_ = lean_ctor_get(v_date_1621_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_date_1621_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1625_ = v_date_1621_;
v_isShared_1626_ = v_isSharedCheck_1661_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_time_1622_);
lean_inc(v_date_1623_);
lean_dec(v_date_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1661_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_minute_1627_; lean_object* v_second_1628_; lean_object* v_nanosecond_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1659_; 
v_minute_1627_ = lean_ctor_get(v_time_1622_, 1);
v_second_1628_ = lean_ctor_get(v_time_1622_, 2);
v_nanosecond_1629_ = lean_ctor_get(v_time_1622_, 3);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_time_1622_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v_time_1622_, 0);
lean_dec(v_unused_1660_);
v___x_1631_ = v_time_1622_;
v_isShared_1632_ = v_isSharedCheck_1659_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_nanosecond_1629_);
lean_inc(v_second_1628_);
lean_inc(v_minute_1627_);
lean_dec(v_time_1622_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1659_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_hour_1615_);
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_hour_1615_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_minute_1627_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_second_1628_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_nanosecond_1629_);
v___x_1634_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1636_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 1, v___x_1634_);
v___x_1636_ = v___x_1625_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_date_1623_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v_wt_1637_; lean_object* v_ltt_1638_; lean_object* v_tz_1639_; lean_object* v_offset_1640_; lean_object* v_second_1641_; lean_object* v_nano_1642_; lean_object* v___f_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v_nanos_1649_; lean_object* v___x_1650_; lean_object* v_nanos_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
lean_inc_ref(v___x_1636_);
v_wt_1637_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1636_);
lean_inc_ref(v_rules_1617_);
v_ltt_1638_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1617_, v_wt_1637_);
v_tz_1639_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1638_);
lean_dec_ref(v_ltt_1638_);
v_offset_1640_ = lean_ctor_get(v_tz_1639_, 0);
v_second_1641_ = lean_ctor_get(v_wt_1637_, 0);
lean_inc(v_second_1641_);
v_nano_1642_ = lean_ctor_get(v_wt_1637_, 1);
lean_inc(v_nano_1642_);
lean_dec_ref(v_wt_1637_);
v___f_1643_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1643_, 0, v___x_1636_);
v___x_1644_ = lean_mk_thunk(v___f_1643_);
v___x_1645_ = lean_int_neg(v_offset_1640_);
v___x_1646_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1647_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1648_ = lean_int_mul(v_second_1641_, v___x_1647_);
lean_dec(v_second_1641_);
v_nanos_1649_ = lean_int_add(v___x_1648_, v_nano_1642_);
lean_dec(v_nano_1642_);
lean_dec(v___x_1648_);
v___x_1650_ = lean_int_mul(v___x_1645_, v___x_1647_);
lean_dec(v___x_1645_);
v_nanos_1651_ = lean_int_add(v___x_1650_, v___x_1646_);
lean_dec(v___x_1650_);
v___x_1652_ = lean_int_add(v_nanos_1649_, v_nanos_1651_);
lean_dec(v_nanos_1651_);
lean_dec(v_nanos_1649_);
v___x_1653_ = l_Std_Time_Duration_ofNanoseconds(v___x_1652_);
lean_dec(v___x_1652_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 3, v_tz_1639_);
lean_ctor_set(v___x_1619_, 1, v___x_1653_);
lean_ctor_set(v___x_1619_, 0, v___x_1644_);
v___x_1655_ = v___x_1619_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_rules_1617_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_tz_1639_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMinutes(lean_object* v_dt_1665_, lean_object* v_minute_1666_){
_start:
{
lean_object* v_date_1667_; lean_object* v_rules_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1713_; 
v_date_1667_ = lean_ctor_get(v_dt_1665_, 0);
v_rules_1668_ = lean_ctor_get(v_dt_1665_, 2);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_dt_1665_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; lean_object* v_unused_1715_; 
v_unused_1714_ = lean_ctor_get(v_dt_1665_, 3);
lean_dec(v_unused_1714_);
v_unused_1715_ = lean_ctor_get(v_dt_1665_, 1);
lean_dec(v_unused_1715_);
v___x_1670_ = v_dt_1665_;
v_isShared_1671_ = v_isSharedCheck_1713_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_rules_1668_);
lean_inc(v_date_1667_);
lean_dec(v_dt_1665_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1713_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v_date_1672_; lean_object* v_time_1673_; lean_object* v_date_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1712_; 
v_date_1672_ = lean_thunk_get_own(v_date_1667_);
lean_dec_ref(v_date_1667_);
v_time_1673_ = lean_ctor_get(v_date_1672_, 1);
v_date_1674_ = lean_ctor_get(v_date_1672_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_date_1672_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1676_ = v_date_1672_;
v_isShared_1677_ = v_isSharedCheck_1712_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_time_1673_);
lean_inc(v_date_1674_);
lean_dec(v_date_1672_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1712_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v_hour_1678_; lean_object* v_second_1679_; lean_object* v_nanosecond_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1710_; 
v_hour_1678_ = lean_ctor_get(v_time_1673_, 0);
v_second_1679_ = lean_ctor_get(v_time_1673_, 2);
v_nanosecond_1680_ = lean_ctor_get(v_time_1673_, 3);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_time_1673_);
if (v_isSharedCheck_1710_ == 0)
{
lean_object* v_unused_1711_; 
v_unused_1711_ = lean_ctor_get(v_time_1673_, 1);
lean_dec(v_unused_1711_);
v___x_1682_ = v_time_1673_;
v_isShared_1683_ = v_isSharedCheck_1710_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_nanosecond_1680_);
lean_inc(v_second_1679_);
lean_inc(v_hour_1678_);
lean_dec(v_time_1673_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1710_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 1, v_minute_1666_);
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_hour_1678_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_minute_1666_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_second_1679_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_nanosecond_1680_);
v___x_1685_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1687_; 
if (v_isShared_1677_ == 0)
{
lean_ctor_set(v___x_1676_, 1, v___x_1685_);
v___x_1687_ = v___x_1676_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_date_1674_);
lean_ctor_set(v_reuseFailAlloc_1708_, 1, v___x_1685_);
v___x_1687_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
lean_object* v_wt_1688_; lean_object* v_ltt_1689_; lean_object* v_tz_1690_; lean_object* v_offset_1691_; lean_object* v_second_1692_; lean_object* v_nano_1693_; lean_object* v___f_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_nanos_1700_; lean_object* v___x_1701_; lean_object* v_nanos_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
lean_inc_ref(v___x_1687_);
v_wt_1688_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1687_);
lean_inc_ref(v_rules_1668_);
v_ltt_1689_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1668_, v_wt_1688_);
v_tz_1690_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1689_);
lean_dec_ref(v_ltt_1689_);
v_offset_1691_ = lean_ctor_get(v_tz_1690_, 0);
v_second_1692_ = lean_ctor_get(v_wt_1688_, 0);
lean_inc(v_second_1692_);
v_nano_1693_ = lean_ctor_get(v_wt_1688_, 1);
lean_inc(v_nano_1693_);
lean_dec_ref(v_wt_1688_);
v___f_1694_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1694_, 0, v___x_1687_);
v___x_1695_ = lean_mk_thunk(v___f_1694_);
v___x_1696_ = lean_int_neg(v_offset_1691_);
v___x_1697_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1698_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1699_ = lean_int_mul(v_second_1692_, v___x_1698_);
lean_dec(v_second_1692_);
v_nanos_1700_ = lean_int_add(v___x_1699_, v_nano_1693_);
lean_dec(v_nano_1693_);
lean_dec(v___x_1699_);
v___x_1701_ = lean_int_mul(v___x_1696_, v___x_1698_);
lean_dec(v___x_1696_);
v_nanos_1702_ = lean_int_add(v___x_1701_, v___x_1697_);
lean_dec(v___x_1701_);
v___x_1703_ = lean_int_add(v_nanos_1700_, v_nanos_1702_);
lean_dec(v_nanos_1702_);
lean_dec(v_nanos_1700_);
v___x_1704_ = l_Std_Time_Duration_ofNanoseconds(v___x_1703_);
lean_dec(v___x_1703_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 3, v_tz_1690_);
lean_ctor_set(v___x_1670_, 1, v___x_1704_);
lean_ctor_set(v___x_1670_, 0, v___x_1695_);
v___x_1706_ = v___x_1670_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_rules_1668_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_tz_1690_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withSeconds(lean_object* v_dt_1716_, lean_object* v_second_1717_){
_start:
{
lean_object* v_date_1718_; lean_object* v_rules_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1764_; 
v_date_1718_ = lean_ctor_get(v_dt_1716_, 0);
v_rules_1719_ = lean_ctor_get(v_dt_1716_, 2);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_dt_1716_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; lean_object* v_unused_1766_; 
v_unused_1765_ = lean_ctor_get(v_dt_1716_, 3);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v_dt_1716_, 1);
lean_dec(v_unused_1766_);
v___x_1721_ = v_dt_1716_;
v_isShared_1722_ = v_isSharedCheck_1764_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_rules_1719_);
lean_inc(v_date_1718_);
lean_dec(v_dt_1716_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1764_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v_date_1723_; lean_object* v_time_1724_; lean_object* v_date_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1763_; 
v_date_1723_ = lean_thunk_get_own(v_date_1718_);
lean_dec_ref(v_date_1718_);
v_time_1724_ = lean_ctor_get(v_date_1723_, 1);
v_date_1725_ = lean_ctor_get(v_date_1723_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_date_1723_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1727_ = v_date_1723_;
v_isShared_1728_ = v_isSharedCheck_1763_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_time_1724_);
lean_inc(v_date_1725_);
lean_dec(v_date_1723_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1763_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_hour_1729_; lean_object* v_minute_1730_; lean_object* v_nanosecond_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1761_; 
v_hour_1729_ = lean_ctor_get(v_time_1724_, 0);
v_minute_1730_ = lean_ctor_get(v_time_1724_, 1);
v_nanosecond_1731_ = lean_ctor_get(v_time_1724_, 3);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_time_1724_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_time_1724_, 2);
lean_dec(v_unused_1762_);
v___x_1733_ = v_time_1724_;
v_isShared_1734_ = v_isSharedCheck_1761_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_nanosecond_1731_);
lean_inc(v_minute_1730_);
lean_inc(v_hour_1729_);
lean_dec(v_time_1724_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1761_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 2, v_second_1717_);
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_hour_1729_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_minute_1730_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_second_1717_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_nanosecond_1731_);
v___x_1736_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v___x_1736_);
v___x_1738_ = v___x_1727_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_date_1725_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v_wt_1739_; lean_object* v_ltt_1740_; lean_object* v_tz_1741_; lean_object* v_offset_1742_; lean_object* v_second_1743_; lean_object* v_nano_1744_; lean_object* v___f_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_nanos_1751_; lean_object* v___x_1752_; lean_object* v_nanos_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_inc_ref(v___x_1738_);
v_wt_1739_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1738_);
lean_inc_ref(v_rules_1719_);
v_ltt_1740_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1719_, v_wt_1739_);
v_tz_1741_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1740_);
lean_dec_ref(v_ltt_1740_);
v_offset_1742_ = lean_ctor_get(v_tz_1741_, 0);
v_second_1743_ = lean_ctor_get(v_wt_1739_, 0);
lean_inc(v_second_1743_);
v_nano_1744_ = lean_ctor_get(v_wt_1739_, 1);
lean_inc(v_nano_1744_);
lean_dec_ref(v_wt_1739_);
v___f_1745_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1745_, 0, v___x_1738_);
v___x_1746_ = lean_mk_thunk(v___f_1745_);
v___x_1747_ = lean_int_neg(v_offset_1742_);
v___x_1748_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1749_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1750_ = lean_int_mul(v_second_1743_, v___x_1749_);
lean_dec(v_second_1743_);
v_nanos_1751_ = lean_int_add(v___x_1750_, v_nano_1744_);
lean_dec(v_nano_1744_);
lean_dec(v___x_1750_);
v___x_1752_ = lean_int_mul(v___x_1747_, v___x_1749_);
lean_dec(v___x_1747_);
v_nanos_1753_ = lean_int_add(v___x_1752_, v___x_1748_);
lean_dec(v___x_1752_);
v___x_1754_ = lean_int_add(v_nanos_1751_, v_nanos_1753_);
lean_dec(v_nanos_1753_);
lean_dec(v_nanos_1751_);
v___x_1755_ = l_Std_Time_Duration_ofNanoseconds(v___x_1754_);
lean_dec(v___x_1754_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 3, v_tz_1741_);
lean_ctor_set(v___x_1721_, 1, v___x_1755_);
lean_ctor_set(v___x_1721_, 0, v___x_1746_);
v___x_1757_ = v___x_1721_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_rules_1719_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_tz_1741_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
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
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_unsigned_to_nat(1000u);
v___x_1768_ = lean_nat_to_int(v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds(lean_object* v_dt_1769_, lean_object* v_millis_1770_){
_start:
{
lean_object* v_date_1771_; lean_object* v_rules_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1822_; 
v_date_1771_ = lean_ctor_get(v_dt_1769_, 0);
v_rules_1772_ = lean_ctor_get(v_dt_1769_, 2);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_dt_1769_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; lean_object* v_unused_1824_; 
v_unused_1823_ = lean_ctor_get(v_dt_1769_, 3);
lean_dec(v_unused_1823_);
v_unused_1824_ = lean_ctor_get(v_dt_1769_, 1);
lean_dec(v_unused_1824_);
v___x_1774_ = v_dt_1769_;
v_isShared_1775_ = v_isSharedCheck_1822_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_rules_1772_);
lean_inc(v_date_1771_);
lean_dec(v_dt_1769_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1822_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_date_1776_; lean_object* v_time_1777_; lean_object* v_date_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1821_; 
v_date_1776_ = lean_thunk_get_own(v_date_1771_);
lean_dec_ref(v_date_1771_);
v_time_1777_ = lean_ctor_get(v_date_1776_, 1);
v_date_1778_ = lean_ctor_get(v_date_1776_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v_date_1776_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1780_ = v_date_1776_;
v_isShared_1781_ = v_isSharedCheck_1821_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_time_1777_);
lean_inc(v_date_1778_);
lean_dec(v_date_1776_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1821_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_hour_1782_; lean_object* v_minute_1783_; lean_object* v_second_1784_; lean_object* v_nanosecond_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1820_; 
v_hour_1782_ = lean_ctor_get(v_time_1777_, 0);
v_minute_1783_ = lean_ctor_get(v_time_1777_, 1);
v_second_1784_ = lean_ctor_get(v_time_1777_, 2);
v_nanosecond_1785_ = lean_ctor_get(v_time_1777_, 3);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_time_1777_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1787_ = v_time_1777_;
v_isShared_1788_ = v_isSharedCheck_1820_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_nanosecond_1785_);
lean_inc(v_second_1784_);
lean_inc(v_minute_1783_);
lean_inc(v_hour_1782_);
lean_dec(v_time_1777_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1820_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1789_ = lean_obj_once(&l_Std_Time_DateTime_withMilliseconds___closed__0, &l_Std_Time_DateTime_withMilliseconds___closed__0_once, _init_l_Std_Time_DateTime_withMilliseconds___closed__0);
v___x_1790_ = lean_int_emod(v_nanosecond_1785_, v___x_1789_);
lean_dec(v_nanosecond_1785_);
v___x_1791_ = lean_obj_once(&l_Std_Time_DateTime_millisecond___closed__0, &l_Std_Time_DateTime_millisecond___closed__0_once, _init_l_Std_Time_DateTime_millisecond___closed__0);
v___x_1792_ = lean_int_mul(v_millis_1770_, v___x_1791_);
v___x_1793_ = lean_int_add(v___x_1792_, v___x_1790_);
lean_dec(v___x_1790_);
lean_dec(v___x_1792_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 3, v___x_1793_);
v___x_1795_ = v___x_1787_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_hour_1782_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_minute_1783_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_second_1784_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v___x_1793_);
v___x_1795_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
lean_object* v___x_1797_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v___x_1795_);
v___x_1797_ = v___x_1780_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_date_1778_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v_wt_1798_; lean_object* v_ltt_1799_; lean_object* v_tz_1800_; lean_object* v_offset_1801_; lean_object* v_second_1802_; lean_object* v_nano_1803_; lean_object* v___f_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_nanos_1810_; lean_object* v___x_1811_; lean_object* v_nanos_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
lean_inc_ref(v___x_1797_);
v_wt_1798_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1797_);
lean_inc_ref(v_rules_1772_);
v_ltt_1799_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1772_, v_wt_1798_);
v_tz_1800_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1799_);
lean_dec_ref(v_ltt_1799_);
v_offset_1801_ = lean_ctor_get(v_tz_1800_, 0);
v_second_1802_ = lean_ctor_get(v_wt_1798_, 0);
lean_inc(v_second_1802_);
v_nano_1803_ = lean_ctor_get(v_wt_1798_, 1);
lean_inc(v_nano_1803_);
lean_dec_ref(v_wt_1798_);
v___f_1804_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1804_, 0, v___x_1797_);
v___x_1805_ = lean_mk_thunk(v___f_1804_);
v___x_1806_ = lean_int_neg(v_offset_1801_);
v___x_1807_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1808_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1809_ = lean_int_mul(v_second_1802_, v___x_1808_);
lean_dec(v_second_1802_);
v_nanos_1810_ = lean_int_add(v___x_1809_, v_nano_1803_);
lean_dec(v_nano_1803_);
lean_dec(v___x_1809_);
v___x_1811_ = lean_int_mul(v___x_1806_, v___x_1808_);
lean_dec(v___x_1806_);
v_nanos_1812_ = lean_int_add(v___x_1811_, v___x_1807_);
lean_dec(v___x_1811_);
v___x_1813_ = lean_int_add(v_nanos_1810_, v_nanos_1812_);
lean_dec(v_nanos_1812_);
lean_dec(v_nanos_1810_);
v___x_1814_ = l_Std_Time_Duration_ofNanoseconds(v___x_1813_);
lean_dec(v___x_1813_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 3, v_tz_1800_);
lean_ctor_set(v___x_1774_, 1, v___x_1814_);
lean_ctor_set(v___x_1774_, 0, v___x_1805_);
v___x_1816_ = v___x_1774_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_rules_1772_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_tz_1800_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withMilliseconds___boxed(lean_object* v_dt_1825_, lean_object* v_millis_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_Time_DateTime_withMilliseconds(v_dt_1825_, v_millis_1826_);
lean_dec(v_millis_1826_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_withNanoseconds(lean_object* v_dt_1828_, lean_object* v_nano_1829_){
_start:
{
lean_object* v_date_1830_; lean_object* v_rules_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1876_; 
v_date_1830_ = lean_ctor_get(v_dt_1828_, 0);
v_rules_1831_ = lean_ctor_get(v_dt_1828_, 2);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_dt_1828_);
if (v_isSharedCheck_1876_ == 0)
{
lean_object* v_unused_1877_; lean_object* v_unused_1878_; 
v_unused_1877_ = lean_ctor_get(v_dt_1828_, 3);
lean_dec(v_unused_1877_);
v_unused_1878_ = lean_ctor_get(v_dt_1828_, 1);
lean_dec(v_unused_1878_);
v___x_1833_ = v_dt_1828_;
v_isShared_1834_ = v_isSharedCheck_1876_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_rules_1831_);
lean_inc(v_date_1830_);
lean_dec(v_dt_1828_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1876_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_date_1835_; lean_object* v_time_1836_; lean_object* v_date_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1875_; 
v_date_1835_ = lean_thunk_get_own(v_date_1830_);
lean_dec_ref(v_date_1830_);
v_time_1836_ = lean_ctor_get(v_date_1835_, 1);
v_date_1837_ = lean_ctor_get(v_date_1835_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_date_1835_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1839_ = v_date_1835_;
v_isShared_1840_ = v_isSharedCheck_1875_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_time_1836_);
lean_inc(v_date_1837_);
lean_dec(v_date_1835_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1875_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_hour_1841_; lean_object* v_minute_1842_; lean_object* v_second_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1873_; 
v_hour_1841_ = lean_ctor_get(v_time_1836_, 0);
v_minute_1842_ = lean_ctor_get(v_time_1836_, 1);
v_second_1843_ = lean_ctor_get(v_time_1836_, 2);
v_isSharedCheck_1873_ = !lean_is_exclusive(v_time_1836_);
if (v_isSharedCheck_1873_ == 0)
{
lean_object* v_unused_1874_; 
v_unused_1874_ = lean_ctor_get(v_time_1836_, 3);
lean_dec(v_unused_1874_);
v___x_1845_ = v_time_1836_;
v_isShared_1846_ = v_isSharedCheck_1873_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_second_1843_);
lean_inc(v_minute_1842_);
lean_inc(v_hour_1841_);
lean_dec(v_time_1836_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1873_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 3, v_nano_1829_);
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_hour_1841_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_minute_1842_);
lean_ctor_set(v_reuseFailAlloc_1872_, 2, v_second_1843_);
lean_ctor_set(v_reuseFailAlloc_1872_, 3, v_nano_1829_);
v___x_1848_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___x_1848_);
v___x_1850_ = v___x_1839_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_date_1837_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v_wt_1851_; lean_object* v_ltt_1852_; lean_object* v_tz_1853_; lean_object* v_offset_1854_; lean_object* v_second_1855_; lean_object* v_nano_1856_; lean_object* v___f_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v_nanos_1863_; lean_object* v___x_1864_; lean_object* v_nanos_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
lean_inc_ref(v___x_1850_);
v_wt_1851_ = l_Std_Time_PlainDateTime_toWallTime(v___x_1850_);
lean_inc_ref(v_rules_1831_);
v_ltt_1852_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v_rules_1831_, v_wt_1851_);
v_tz_1853_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1852_);
lean_dec_ref(v_ltt_1852_);
v_offset_1854_ = lean_ctor_get(v_tz_1853_, 0);
v_second_1855_ = lean_ctor_get(v_wt_1851_, 0);
lean_inc(v_second_1855_);
v_nano_1856_ = lean_ctor_get(v_wt_1851_, 1);
lean_inc(v_nano_1856_);
lean_dec_ref(v_wt_1851_);
v___f_1857_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1857_, 0, v___x_1850_);
v___x_1858_ = lean_mk_thunk(v___f_1857_);
v___x_1859_ = lean_int_neg(v_offset_1854_);
v___x_1860_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1861_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1862_ = lean_int_mul(v_second_1855_, v___x_1861_);
lean_dec(v_second_1855_);
v_nanos_1863_ = lean_int_add(v___x_1862_, v_nano_1856_);
lean_dec(v_nano_1856_);
lean_dec(v___x_1862_);
v___x_1864_ = lean_int_mul(v___x_1859_, v___x_1861_);
lean_dec(v___x_1859_);
v_nanos_1865_ = lean_int_add(v___x_1864_, v___x_1860_);
lean_dec(v___x_1864_);
v___x_1866_ = lean_int_add(v_nanos_1863_, v_nanos_1865_);
lean_dec(v_nanos_1865_);
lean_dec(v_nanos_1863_);
v___x_1867_ = l_Std_Time_Duration_ofNanoseconds(v___x_1866_);
lean_dec(v___x_1866_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 3, v_tz_1853_);
lean_ctor_set(v___x_1833_, 1, v___x_1867_);
lean_ctor_set(v___x_1833_, 0, v___x_1858_);
v___x_1869_ = v___x_1833_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1870_, 2, v_rules_1831_);
lean_ctor_set(v_reuseFailAlloc_1870_, 3, v_tz_1853_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
}
}
}
uint8_t l_Std_Time_DateTime_inLeapYear(lean_object* v_date_1879_){
_start:
{
lean_object* v_date_1880_; lean_object* v___x_1881_; lean_object* v_date_1882_; lean_object* v_year_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1891_; 
v_date_1880_ = lean_ctor_get(v_date_1879_, 0);
v___x_1881_ = lean_thunk_get_own(v_date_1880_);
v_date_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc_ref(v_date_1882_);
lean_dec(v___x_1881_);
v_year_1883_ = lean_ctor_get(v_date_1882_, 0);
lean_inc(v_year_1883_);
lean_dec_ref(v_date_1882_);
v___x_1884_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__0, &l_Std_Time_DateTime_dayOfYear___closed__0_once, _init_l_Std_Time_DateTime_dayOfYear___closed__0);
v___x_1885_ = lean_int_mod(v_year_1883_, v___x_1884_);
v___x_1886_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0);
v___x_1891_ = lean_int_dec_eq(v___x_1885_, v___x_1886_);
lean_dec(v___x_1885_);
if (v___x_1891_ == 0)
{
lean_dec(v_year_1883_);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v___x_1892_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__2, &l_Std_Time_DateTime_dayOfYear___closed__2_once, _init_l_Std_Time_DateTime_dayOfYear___closed__2);
v___x_1893_ = lean_int_mod(v_year_1883_, v___x_1892_);
v___x_1894_ = lean_int_dec_eq(v___x_1893_, v___x_1886_);
lean_dec(v___x_1893_);
if (v___x_1894_ == 0)
{
if (v___x_1891_ == 0)
{
goto v___jp_1887_;
}
else
{
lean_dec(v_year_1883_);
return v___x_1891_;
}
}
else
{
goto v___jp_1887_;
}
}
v___jp_1887_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1888_ = lean_obj_once(&l_Std_Time_DateTime_dayOfYear___closed__1, &l_Std_Time_DateTime_dayOfYear___closed__1_once, _init_l_Std_Time_DateTime_dayOfYear___closed__1);
v___x_1889_ = lean_int_mod(v_year_1883_, v___x_1888_);
lean_dec(v_year_1883_);
v___x_1890_ = lean_int_dec_eq(v___x_1889_, v___x_1886_);
lean_dec(v___x_1889_);
return v___x_1890_;
}
}
}
LEAN_EXPORT void l_Std_Time_DateTime_inLeapYear_0interp(lean_interpreter_value* stack)
{
lean_object* v_date_1879_ = stack[0].m_obj;
uint8_t v_res_1895_;
v_res_1895_ = l_Std_Time_DateTime_inLeapYear(v_date_1879_);
stack->m_num = v_res_1895_;
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
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_wt_1911_; lean_object* v_ltt_1912_; lean_object* v_tz_1913_; lean_object* v_offset_1914_; lean_object* v_second_1915_; lean_object* v_nano_1916_; lean_object* v___f_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v_nanos_1923_; lean_object* v___x_1924_; lean_object* v_nanos_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
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
v_second_1915_ = lean_ctor_get(v_wt_1911_, 0);
lean_inc(v_second_1915_);
v_nano_1916_ = lean_ctor_get(v_wt_1911_, 1);
lean_inc(v_nano_1916_);
lean_dec_ref(v_wt_1911_);
v___f_1917_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_addMonthsClip___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1917_, 0, v___x_1910_);
v___x_1918_ = lean_mk_thunk(v___f_1917_);
v___x_1919_ = lean_int_neg(v_offset_1914_);
v___x_1920_ = lean_obj_once(&l_Std_Time_DateTime_ofPlainDateTime___closed__0, &l_Std_Time_DateTime_ofPlainDateTime___closed__0_once, _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0);
v___x_1921_ = lean_obj_once(&l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1, &l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once, _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1);
v___x_1922_ = lean_int_mul(v_second_1915_, v___x_1921_);
lean_dec(v_second_1915_);
v_nanos_1923_ = lean_int_add(v___x_1922_, v_nano_1916_);
lean_dec(v_nano_1916_);
lean_dec(v___x_1922_);
v___x_1924_ = lean_int_mul(v___x_1919_, v___x_1921_);
lean_dec(v___x_1919_);
v_nanos_1925_ = lean_int_add(v___x_1924_, v___x_1920_);
lean_dec(v___x_1924_);
v___x_1926_ = lean_int_add(v_nanos_1923_, v_nanos_1925_);
lean_dec(v_nanos_1925_);
lean_dec(v_nanos_1923_);
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
lean_object* v_timestamp_1963_; lean_object* v_timestamp_1964_; lean_object* v_second_1965_; lean_object* v_nano_1966_; lean_object* v_second_1967_; lean_object* v_nano_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v_nanos_1973_; lean_object* v___x_1974_; lean_object* v_nanos_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
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
v_nanos_1973_ = lean_int_add(v___x_1972_, v_nano_1968_);
lean_dec(v___x_1972_);
v___x_1974_ = lean_int_mul(v___x_1969_, v___x_1971_);
lean_dec(v___x_1969_);
v_nanos_1975_ = lean_int_add(v___x_1974_, v___x_1970_);
lean_dec(v___x_1970_);
lean_dec(v___x_1974_);
v___x_1976_ = lean_int_add(v_nanos_1973_, v_nanos_1975_);
lean_dec(v_nanos_1975_);
lean_dec(v_nanos_1973_);
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

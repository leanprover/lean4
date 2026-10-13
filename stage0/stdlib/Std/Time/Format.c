// Lean compiler output
// Module: Std.Time.Format
// Imports: public import Std.Time.Notation.Spec public import Std.Time.Format.Basic import all Std.Time.Format.Basic
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
extern lean_object* l_Std_Time_DateFormat_enUS;
lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*, uint8_t);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
extern lean_object* l_Std_Time_TimeZone_GMT;
lean_object* l_Std_Time_GenericFormat_parse(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Time_GenericFormat_format(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
lean_object* l_Std_Time_DateTime_subYearsClip(lean_object*, lean_object*);
lean_object* l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(lean_object*);
uint8_t l_Std_Time_HourMarker_ofOrdinal(lean_object*);
uint8_t l_Std_Time_classifyDayPeriod(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_classifyExtendedDayPeriod(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Hour_Ordinal_toRelative(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object*);
lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object*);
lean_object* l_Std_Time_HourMarker_toAbsolute(uint8_t, lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDateTime_alignedWeekOfMonth(lean_object*);
extern lean_object* l_Std_Time_TimeZone_UTC;
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
lean_object* l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_LocalTimeType_getTimeZone(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
static lean_once_cell_t l_Std_Time_Formats_iso8601___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_iso8601___closed__0;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__1 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__2 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value;
static const lean_string_object l_Std_Time_Formats_iso8601___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_Formats_iso8601___closed__3 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__4 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__5 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__6 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__7 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__8 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__9 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value;
static const lean_string_object l_Std_Time_Formats_iso8601___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "T"};
static const lean_object* l_Std_Time_Formats_iso8601___closed__10 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__11 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 22}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__12 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__13 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value;
static const lean_string_object l_Std_Time_Formats_iso8601___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Time_Formats_iso8601___closed__14 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__15 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 23}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__16 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__17 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 24}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__18 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__19 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 33}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__20 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__20_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__20_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__21 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__21_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__22 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__22_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__22_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__23 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__23_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__23_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__24 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__24_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__24_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__25 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__25_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__25_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__26 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__26_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__26_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__27 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__27_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__27_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__28 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__28_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__28_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__29 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__29_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__29_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__30 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__30_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__30_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__31 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__31_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__31_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__32 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__32_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__32_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__33 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__33_value;
static lean_once_cell_t l_Std_Time_Formats_iso8601___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_iso8601___closed__34;
LEAN_EXPORT lean_object* l_Std_Time_Formats_iso8601;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__0 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__1 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__2 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__3 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__4 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__4_value;
static lean_once_cell_t l_Std_Time_Formats_americanDate___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_americanDate___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Formats_americanDate;
static const lean_ctor_object l_Std_Time_Formats_europeanDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_europeanDate___closed__0 = (const lean_object*)&l_Std_Time_Formats_europeanDate___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_europeanDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_europeanDate___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_europeanDate___closed__1 = (const lean_object*)&l_Std_Time_Formats_europeanDate___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_europeanDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_europeanDate___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_europeanDate___closed__2 = (const lean_object*)&l_Std_Time_Formats_europeanDate___closed__2_value;
static lean_once_cell_t l_Std_Time_Formats_europeanDate___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_europeanDate___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_Formats_europeanDate;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 19}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__1 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__1_value;
static const lean_string_object l_Std_Time_Formats_time12Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__2 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__3 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 16}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__4 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__5 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__6 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__7 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__8 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__9 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__10 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__11 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__12 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__12_value;
static lean_once_cell_t l_Std_Time_Formats_time12Hour___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_time12Hour___closed__13;
LEAN_EXPORT lean_object* l_Std_Time_Formats_time12Hour;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__1 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__2 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__3 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__4 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__4_value;
static lean_once_cell_t l_Std_Time_Formats_time24Hour___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_time24Hour___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Formats_time24Hour;
static const lean_string_object l_Std_Time_Formats_dateTime24Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__1 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 25}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__2 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__3 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__4 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__5 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__6 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__7 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__8 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__9 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__10 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__11 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__12 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__13 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__14 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__15 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__15_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__16 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__16_value;
static lean_once_cell_t l_Std_Time_Formats_dateTime24Hour___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_dateTime24Hour___closed__17;
LEAN_EXPORT lean_object* l_Std_Time_Formats_dateTime24Hour;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 35}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__0 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__1 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__2 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__3 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__4 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__5 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__6 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__7 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__8 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__9 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__10 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__11 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__12 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__13 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__14 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__15 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__15_value;
static lean_once_cell_t l_Std_Time_Formats_dateTimeWithZone___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__16;
LEAN_EXPORT lean_object* l_Std_Time_Formats_dateTimeWithZone;
static lean_once_cell_t l_Std_Time_Formats_leanTime24Hour___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_leanTime24Hour___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Formats_leanTime24Hour;
LEAN_EXPORT lean_object* l_Std_Time_Formats_leanTime24HourNoNanos;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__5_value;
static lean_once_cell_t l_Std_Time_Formats_leanDateTime24Hour___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__6;
LEAN_EXPORT lean_object* l_Std_Time_Formats_leanDateTime24Hour;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5_value;
static lean_once_cell_t l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6;
LEAN_EXPORT lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 35}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__6 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__7 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__8 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__9 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__10 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__11 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__12 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__13 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__14 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__15 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__15_value;
static lean_once_cell_t l_Std_Time_Formats_leanDateTimeWithZone___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__16;
LEAN_EXPORT lean_object* l_Std_Time_Formats_leanDateTimeWithZone;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10_value;
static lean_once_cell_t l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11;
LEAN_EXPORT lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos;
static const lean_string_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 30}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3_value;
static const lean_string_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19_value;
static lean_once_cell_t l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20;
LEAN_EXPORT lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12_value;
static lean_once_cell_t l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13;
LEAN_EXPORT lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDate___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_leanDate___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_leanDate___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_leanDate___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__4_value;
static lean_once_cell_t l_Std_Time_Formats_leanDate___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_leanDate___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_Formats_leanDate;
LEAN_EXPORT lean_object* l_Std_Time_Formats_sqlDate;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 12}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__0 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__1 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__1_value;
static const lean_string_object l_Std_Time_Formats_longDateFormat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__2 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__3 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__4 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__5 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__6 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__7 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__8 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__9 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__10 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value),((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__11 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__8_value),((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__12 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__13 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__6_value),((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__14 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value),((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__15 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__1_value),((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__15_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__16 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__16_value;
static lean_once_cell_t l_Std_Time_Formats_longDateFormat___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_longDateFormat___closed__17;
LEAN_EXPORT lean_object* l_Std_Time_Formats_longDateFormat;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 12}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__0 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__1 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__2 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__3 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__4 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__5 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__6 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__7 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__8 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__9 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__10 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__11 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__8_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__12 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__13 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__4_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__14 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__15 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__1_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__15_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__16 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__16_value;
static lean_once_cell_t l_Std_Time_Formats_ascTime___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_ascTime___closed__17;
LEAN_EXPORT lean_object* l_Std_Time_Formats_ascTime;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 13}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__0 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__1 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__2 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__3 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__4 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__5 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__6 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__7 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__8 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__9 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__10 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__4_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__11 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__12 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__13 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__14 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__1_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__15 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__15_value;
static lean_once_cell_t l_Std_Time_Formats_rfc822___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_rfc822___closed__16;
LEAN_EXPORT lean_object* l_Std_Time_Formats_rfc822;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__0 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__1 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__2 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__3 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__4 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__1_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__5 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__5_value;
static lean_once_cell_t l_Std_Time_Formats_rfc850___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_rfc850___closed__6;
LEAN_EXPORT lean_object* l_Std_Time_Formats_rfc850;
static const lean_string_object l_Std_Time_Formats_httpDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GMT"};
static const lean_object* l_Std_Time_Formats_httpDate___closed__0 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_httpDate___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__1 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_httpDate___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__2 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__3 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__4 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__5 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__6 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__7 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__8 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__9 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__10 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__11 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__4_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__12 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__13 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__14 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__15 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_httpDate___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__1_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__15_value)}};
static const lean_object* l_Std_Time_Formats_httpDate___closed__16 = (const lean_object*)&l_Std_Time_Formats_httpDate___closed__16_value;
static lean_once_cell_t l_Std_Time_Formats_httpDate___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Formats_httpDate___closed__17;
LEAN_EXPORT lean_object* l_Std_Time_Formats_httpDate;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 13}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__4_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__0 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__1 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__2 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__2_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__3 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__3_value),((lean_object*)&l_Std_Time_Formats_httpDate___closed__9_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__4 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__4_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__5 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__5_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__4_value),((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__5_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__6 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__6_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value),((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__6_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__7 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__7_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value),((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__7_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__8 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__8_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value),((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__8_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__9 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__9_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__1_value),((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__9_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__10 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__10_value;
static lean_once_cell_t l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__11;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__1_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__15_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__0 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__0_value;
static lean_once_cell_t l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime;
static const lean_string_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "  "};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__0 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__0_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__0_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__1 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__1_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__1_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__12_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__2 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__2_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__4_value),((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__2_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__3 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__3_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__3_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__4 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__4_value;
static const lean_ctor_object l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__1_value),((lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__4_value)}};
static const lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__5 = (const lean_object*)&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__5_value;
static lean_once_cell_t l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__6;
LEAN_EXPORT lean_object* l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_fromTimeZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 29}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__3_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__3_value)}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__4_value;
static lean_once_cell_t l_Std_Time_TimeZone_fromTimeZone___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__5;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_Offset_fromOffset___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 34}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_Offset_fromOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__3_value;
static lean_once_cell_t l_Std_Time_TimeZone_Offset_fromOffset___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_format___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_format___lam__0___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_format___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_format___lam__0___closed__1;
static lean_once_cell_t l_Std_Time_PlainDate_format___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_format___lam__0___closed__2;
static lean_once_cell_t l_Std_Time_PlainDate_format___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_format___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Time_PlainDate_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Std_Time_PlainDate_format___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_format___closed__0_value;
static const lean_string_object l_Std_Time_PlainDate_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invalid time"};
static const lean_object* l_Std_Time_PlainDate_format___closed__1 = (const lean_object*)&l_Std_Time_PlainDate_format___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDate_fromAmericanDateString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_fromAmericanDateString___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_fromAmericanDateString___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_fromAmericanDateString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toAmericanDateString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDate_fromSQLDateString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_fromSQLDateString___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_fromSQLDateString___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_fromSQLDateString___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toSQLDateString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromLeanDateString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toLeanDateString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_parse(lean_object*);
static const lean_closure_object l_Std_Time_PlainDate_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_toLeanDateString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instToString___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instToString = (const lean_object*)&l_Std_Time_PlainDate_instToString___closed__0_value;
static const lean_string_object l_Std_Time_PlainDate_instRepr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "date(\""};
static const lean_object* l_Std_Time_PlainDate_instRepr___lam__0___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instRepr___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Time_PlainDate_instRepr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_PlainDate_instRepr___lam__0___closed__0_value)}};
static const lean_object* l_Std_Time_PlainDate_instRepr___lam__0___closed__1 = (const lean_object*)&l_Std_Time_PlainDate_instRepr___lam__0___closed__1_value;
static const lean_string_object l_Std_Time_PlainDate_instRepr___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\")"};
static const lean_object* l_Std_Time_PlainDate_instRepr___lam__0___closed__2 = (const lean_object*)&l_Std_Time_PlainDate_instRepr___lam__0___closed__2_value;
static const lean_ctor_object l_Std_Time_PlainDate_instRepr___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_PlainDate_instRepr___lam__0___closed__2_value)}};
static const lean_object* l_Std_Time_PlainDate_instRepr___lam__0___closed__3 = (const lean_object*)&l_Std_Time_PlainDate_instRepr___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDate_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDate_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDate_instRepr___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDate_instRepr = (const lean_object*)&l_Std_Time_PlainDate_instRepr___closed__0_value;
static lean_once_cell_t l_Std_Time_PlainTime_format___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_format___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainTime_fromTime24Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_fromTime24Hour___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_fromTime24Hour___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_fromTime24Hour___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime24Hour(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toLeanTime24Hour(lean_object*);
static lean_once_cell_t l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainTime_fromTime12Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_fromTime12Hour___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_fromTime12Hour___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime12Hour(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_parse(lean_object*);
static const lean_closure_object l_Std_Time_PlainTime_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_toLeanTime24Hour, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instToString___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instToString = (const lean_object*)&l_Std_Time_PlainTime_instToString___closed__0_value;
static const lean_string_object l_Std_Time_PlainTime_instRepr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "time(\""};
static const lean_object* l_Std_Time_PlainTime_instRepr___lam__0___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instRepr___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Time_PlainTime_instRepr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_PlainTime_instRepr___lam__0___closed__0_value)}};
static const lean_object* l_Std_Time_PlainTime_instRepr___lam__0___closed__1 = (const lean_object*)&l_Std_Time_PlainTime_instRepr___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainTime_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainTime_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainTime_instRepr___closed__0 = (const lean_object*)&l_Std_Time_PlainTime_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainTime_instRepr = (const lean_object*)&l_Std_Time_PlainTime_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromISO8601String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC822String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC850String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String(lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_toHTTPDateString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_toHTTPDateString___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toHTTPDateString(lean_object*);
static lean_once_cell_t l_Std_Time_DateTime_fromHTTPDateString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateTime_fromHTTPDateString___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromHTTPDateString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromDateTimeWithZoneString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithZoneString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithIdentifierString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_parse(lean_object*);
static const lean_closure_object l_Std_Time_DateTime_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_toLeanDateTimeWithIdentifierString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instToString___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instToString = (const lean_object*)&l_Std_Time_DateTime_instToString___closed__0_value;
static const lean_string_object l_Std_Time_DateTime_instRepr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "zoned(\""};
static const lean_object* l_Std_Time_DateTime_instRepr___lam__0___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instRepr___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Time_DateTime_instRepr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_DateTime_instRepr___lam__0___closed__0_value)}};
static const lean_object* l_Std_Time_DateTime_instRepr___lam__0___closed__1 = (const lean_object*)&l_Std_Time_DateTime_instRepr___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_DateTime_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_DateTime_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_DateTime_instRepr___closed__0 = (const lean_object*)&l_Std_Time_DateTime_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateTime_instRepr = (const lean_object*)&l_Std_Time_DateTime_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromAscTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Std_Time_PlainDateTime_toAscTimeString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Time_PlainDateTime_toAscTimeString___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_toAscTimeString___closed__0_value;
static lean_once_cell_t l_Std_Time_PlainDateTime_toAscTimeString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_toAscTimeString___closed__1;
static lean_once_cell_t l_Std_Time_PlainDateTime_toAscTimeString___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_toAscTimeString___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLongDateFormatString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLongDateFormatString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromDateTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toDateTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLeanDateTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLeanDateTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_parse(lean_object*);
static const lean_closure_object l_Std_Time_PlainDateTime_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_toLeanDateTimeString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instToString___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instToString = (const lean_object*)&l_Std_Time_PlainDateTime_instToString___closed__0_value;
static const lean_string_object l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "datetime(\""};
static const lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0_value)}};
static const lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1 = (const lean_object*)&l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_PlainDateTime_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_PlainDateTime_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_PlainDateTime_instRepr___closed__0 = (const lean_object*)&l_Std_Time_PlainDateTime_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_PlainDateTime_instRepr = (const lean_object*)&l_Std_Time_PlainDateTime_instRepr___closed__0_value;
static lean_object* _init_l_Std_Time_Formats_iso8601___closed__0(void){
_start:
{
lean_object* v___x_1_; uint8_t v___x_2_; lean_object* v___x_3_; 
v___x_1_ = l_Std_Time_DateFormat_enUS;
v___x_2_ = 0;
v___x_3_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3_, 0, v___x_1_);
lean_ctor_set_uint8(v___x_3_, sizeof(void*)*1, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Std_Time_Formats_iso8601___closed__34(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = ((lean_object*)(l_Std_Time_Formats_iso8601___closed__33));
v___x_80_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Std_Time_Formats_iso8601(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__34, &l_Std_Time_Formats_iso8601___closed__34_once, _init_l_Std_Time_Formats_iso8601___closed__34);
return v___x_82_;
}
}
static lean_object* _init_l_Std_Time_Formats_americanDate___closed__5(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = ((lean_object*)(l_Std_Time_Formats_americanDate___closed__4));
v___x_99_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
return v___x_100_;
}
}
static lean_object* _init_l_Std_Time_Formats_americanDate(void){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_Time_Formats_americanDate___closed__5, &l_Std_Time_Formats_americanDate___closed__5_once, _init_l_Std_Time_Formats_americanDate___closed__5);
return v___x_101_;
}
}
static lean_object* _init_l_Std_Time_Formats_europeanDate___closed__3(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((lean_object*)(l_Std_Time_Formats_europeanDate___closed__2));
v___x_112_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l_Std_Time_Formats_europeanDate(void){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Std_Time_Formats_europeanDate___closed__3, &l_Std_Time_Formats_europeanDate___closed__3_once, _init_l_Std_Time_Formats_europeanDate___closed__3);
return v___x_114_;
}
}
static lean_object* _init_l_Std_Time_Formats_time12Hour___closed__13(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((lean_object*)(l_Std_Time_Formats_time12Hour___closed__12));
v___x_148_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_Std_Time_Formats_time12Hour(void){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_obj_once(&l_Std_Time_Formats_time12Hour___closed__13, &l_Std_Time_Formats_time12Hour___closed__13_once, _init_l_Std_Time_Formats_time12Hour___closed__13);
return v___x_150_;
}
}
static lean_object* _init_l_Std_Time_Formats_time24Hour___closed__5(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((lean_object*)(l_Std_Time_Formats_time24Hour___closed__4));
v___x_167_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
return v___x_168_;
}
}
static lean_object* _init_l_Std_Time_Formats_time24Hour(void){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_obj_once(&l_Std_Time_Formats_time24Hour___closed__5, &l_Std_Time_Formats_time24Hour___closed__5_once, _init_l_Std_Time_Formats_time24Hour___closed__5);
return v___x_169_;
}
}
static lean_object* _init_l_Std_Time_Formats_dateTime24Hour___closed__17(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = ((lean_object*)(l_Std_Time_Formats_dateTime24Hour___closed__16));
v___x_217_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_216_);
return v___x_218_;
}
}
static lean_object* _init_l_Std_Time_Formats_dateTime24Hour(void){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lean_obj_once(&l_Std_Time_Formats_dateTime24Hour___closed__17, &l_Std_Time_Formats_dateTime24Hour___closed__17_once, _init_l_Std_Time_Formats_dateTime24Hour___closed__17);
return v___x_219_;
}
}
static lean_object* _init_l_Std_Time_Formats_dateTimeWithZone___closed__16(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = ((lean_object*)(l_Std_Time_Formats_dateTimeWithZone___closed__15));
v___x_267_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Std_Time_Formats_dateTimeWithZone(void){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Std_Time_Formats_dateTimeWithZone___closed__16, &l_Std_Time_Formats_dateTimeWithZone___closed__16_once, _init_l_Std_Time_Formats_dateTimeWithZone___closed__16);
return v___x_269_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanTime24Hour___closed__0(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = ((lean_object*)(l_Std_Time_Formats_dateTime24Hour___closed__10));
v___x_271_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanTime24Hour(void){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Std_Time_Formats_leanTime24Hour___closed__0, &l_Std_Time_Formats_leanTime24Hour___closed__0_once, _init_l_Std_Time_Formats_leanTime24Hour___closed__0);
return v___x_273_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanTime24HourNoNanos(void){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Std_Time_Formats_time24Hour___closed__5, &l_Std_Time_Formats_time24Hour___closed__5_once, _init_l_Std_Time_Formats_time24Hour___closed__5);
return v___x_274_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTime24Hour___closed__6(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((lean_object*)(l_Std_Time_Formats_leanDateTime24Hour___closed__5));
v___x_294_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTime24Hour(void){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&l_Std_Time_Formats_leanDateTime24Hour___closed__6, &l_Std_Time_Formats_leanDateTime24Hour___closed__6_once, _init_l_Std_Time_Formats_leanDateTime24Hour___closed__6);
return v___x_296_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((lean_object*)(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5));
v___x_316_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTime24HourNoNanos(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6, &l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6_once, _init_l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6);
return v___x_318_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTimeWithZone___closed__16(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithZone___closed__15));
v___x_366_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTimeWithZone(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&l_Std_Time_Formats_leanDateTimeWithZone___closed__16, &l_Std_Time_Formats_leanDateTimeWithZone___closed__16_once, _init_l_Std_Time_Formats_leanDateTimeWithZone___closed__16);
return v___x_368_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10));
v___x_403_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
return v___x_404_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos(void){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_obj_once(&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11, &l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11_once, _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11);
return v___x_405_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19));
v___x_459_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTimeWithIdentifier(void){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lean_obj_once(&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20, &l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20_once, _init_l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20);
return v___x_461_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12));
v___x_502_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13, &l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13_once, _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13);
return v___x_504_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDate___closed__5(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((lean_object*)(l_Std_Time_Formats_leanDate___closed__4));
v___x_521_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Std_Time_Formats_leanDate(void){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_obj_once(&l_Std_Time_Formats_leanDate___closed__5, &l_Std_Time_Formats_leanDate___closed__5_once, _init_l_Std_Time_Formats_leanDate___closed__5);
return v___x_523_;
}
}
static lean_object* _init_l_Std_Time_Formats_sqlDate(void){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l_Std_Time_Formats_leanDate___closed__5, &l_Std_Time_Formats_leanDate___closed__5_once, _init_l_Std_Time_Formats_leanDate___closed__5);
return v___x_524_;
}
}
static lean_object* _init_l_Std_Time_Formats_longDateFormat___closed__17(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((lean_object*)(l_Std_Time_Formats_longDateFormat___closed__16));
v___x_568_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l_Std_Time_Formats_longDateFormat(void){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_obj_once(&l_Std_Time_Formats_longDateFormat___closed__17, &l_Std_Time_Formats_longDateFormat___closed__17_once, _init_l_Std_Time_Formats_longDateFormat___closed__17);
return v___x_570_;
}
}
static lean_object* _init_l_Std_Time_Formats_ascTime___closed__17(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_618_ = ((lean_object*)(l_Std_Time_Formats_ascTime___closed__16));
v___x_619_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
return v___x_620_;
}
}
static lean_object* _init_l_Std_Time_Formats_ascTime(void){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_obj_once(&l_Std_Time_Formats_ascTime___closed__17, &l_Std_Time_Formats_ascTime___closed__17_once, _init_l_Std_Time_Formats_ascTime___closed__17);
return v___x_621_;
}
}
static lean_object* _init_l_Std_Time_Formats_rfc822___closed__16(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((lean_object*)(l_Std_Time_Formats_rfc822___closed__15));
v___x_669_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l_Std_Time_Formats_rfc822(void){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = lean_obj_once(&l_Std_Time_Formats_rfc822___closed__16, &l_Std_Time_Formats_rfc822___closed__16_once, _init_l_Std_Time_Formats_rfc822___closed__16);
return v___x_671_;
}
}
static lean_object* _init_l_Std_Time_Formats_rfc850___closed__6(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((lean_object*)(l_Std_Time_Formats_rfc850___closed__5));
v___x_691_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_690_);
return v___x_692_;
}
}
static lean_object* _init_l_Std_Time_Formats_rfc850(void){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_once(&l_Std_Time_Formats_rfc850___closed__6, &l_Std_Time_Formats_rfc850___closed__6_once, _init_l_Std_Time_Formats_rfc850___closed__6);
return v___x_693_;
}
}
static lean_object* _init_l_Std_Time_Formats_httpDate___closed__17(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = ((lean_object*)(l_Std_Time_Formats_httpDate___closed__16));
v___x_743_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
return v___x_744_;
}
}
static lean_object* _init_l_Std_Time_Formats_httpDate(void){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_obj_once(&l_Std_Time_Formats_httpDate___closed__17, &l_Std_Time_Formats_httpDate___closed__17_once, _init_l_Std_Time_Formats_httpDate___closed__17);
return v___x_745_;
}
}
static lean_object* _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__11(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((lean_object*)(l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__10));
v___x_776_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_775_);
return v___x_777_;
}
}
static lean_object* _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850(void){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = lean_obj_once(&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__11, &l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__11_once, _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850___closed__11);
return v___x_778_;
}
}
static lean_object* _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__1(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((lean_object*)(l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__0));
v___x_783_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime(void){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = lean_obj_once(&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__1, &l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__1_once, _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime___closed__1);
return v___x_785_;
}
}
static lean_object* _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__6(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = ((lean_object*)(l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__5));
v___x_802_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
return v___x_803_;
}
}
static lean_object* _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded(void){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = lean_obj_once(&l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__6, &l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__6_once, _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded___closed__6);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0(uint8_t v___x_805_, lean_object* v_id_806_, lean_object* v_off_807_){
_start:
{
uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_808_ = 1;
lean_inc(v_off_807_);
v___x_809_ = l_Std_Time_TimeZone_Offset_toIsoString(v_off_807_, v___x_808_);
v___x_810_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_810_, 0, v_off_807_);
lean_ctor_set(v___x_810_, 1, v_id_806_);
lean_ctor_set(v___x_810_, 2, v___x_809_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*3, v___x_805_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed(lean_object* v___x_812_, lean_object* v_id_813_, lean_object* v_off_814_){
_start:
{
uint8_t v___x_32__boxed_815_; lean_object* v_res_816_; 
v___x_32__boxed_815_ = lean_unbox(v___x_812_);
v_res_816_ = l_Std_Time_TimeZone_fromTimeZone___lam__0(v___x_32__boxed_815_, v_id_813_, v_off_814_);
return v_res_816_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_fromTimeZone___closed__5(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_spec_832_; 
v___x_830_ = ((lean_object*)(l_Std_Time_TimeZone_fromTimeZone___closed__4));
v___x_831_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_spec_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_spec_832_, 0, v___x_831_);
lean_ctor_set(v_spec_832_, 1, v___x_830_);
return v_spec_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone(lean_object* v_input_833_){
_start:
{
lean_object* v___f_834_; lean_object* v_spec_835_; lean_object* v___x_836_; 
v___f_834_ = ((lean_object*)(l_Std_Time_TimeZone_fromTimeZone___closed__0));
v_spec_835_ = lean_obj_once(&l_Std_Time_TimeZone_fromTimeZone___closed__5, &l_Std_Time_TimeZone_fromTimeZone___closed__5_once, _init_l_Std_Time_TimeZone_fromTimeZone___closed__5);
v___x_836_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_835_, v___f_834_, v_input_833_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset___lam__0(lean_object* v_val_837_){
_start:
{
lean_object* v___x_838_; 
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v_val_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_spec_849_; 
v___x_847_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_fromOffset___closed__3));
v___x_848_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_spec_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_spec_849_, 0, v___x_848_);
lean_ctor_set(v_spec_849_, 1, v___x_847_);
return v_spec_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset(lean_object* v_input_850_){
_start:
{
lean_object* v___f_851_; lean_object* v_spec_852_; lean_object* v___x_853_; 
v___f_851_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_fromOffset___closed__0));
v_spec_852_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_fromOffset___closed__4, &l_Std_Time_TimeZone_Offset_fromOffset___closed__4_once, _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4);
v___x_853_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_852_, v___f_851_, v_input_850_);
return v___x_853_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_unsigned_to_nat(4u);
v___x_855_ = lean_nat_to_int(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__1(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_nat_to_int(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__2(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(400u);
v___x_859_ = lean_nat_to_int(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__3(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(100u);
v___x_861_ = lean_nat_to_int(v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0(lean_object* v_date_862_, lean_object* v_locale_863_, lean_object* v_x_864_){
_start:
{
uint8_t v___y_866_; 
switch(lean_obj_tag(v_x_864_))
{
case 0:
{
lean_object* v_year_871_; uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref_known(v_x_864_, 0);
v_year_871_ = lean_ctor_get(v_date_862_, 0);
lean_inc(v_year_871_);
lean_dec_ref(v_date_862_);
v___x_872_ = l_Std_Time_Year_Offset_era(v_year_871_);
lean_dec(v_year_871_);
v___x_873_ = lean_box(v___x_872_);
v___x_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
return v___x_874_;
}
case 2:
{
lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_882_; 
v_isSharedCheck_882_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_883_);
v___x_876_ = v_x_864_;
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
else
{
lean_dec(v_x_864_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_882_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v_year_878_; lean_object* v___x_880_; 
v_year_878_ = lean_ctor_get(v_date_862_, 0);
lean_inc(v_year_878_);
lean_dec_ref(v_date_862_);
if (v_isShared_877_ == 0)
{
lean_ctor_set_tag(v___x_876_, 1);
lean_ctor_set(v___x_876_, 0, v_year_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_year_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
case 1:
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
v_isSharedCheck_891_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; 
v_unused_892_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_892_);
v___x_885_ = v_x_864_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_x_864_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_year_887_; lean_object* v___x_889_; 
v_year_887_ = lean_ctor_get(v_date_862_, 0);
lean_inc(v_year_887_);
lean_dec_ref(v_date_862_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_year_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_year_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
case 9:
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_902_; 
v_isSharedCheck_902_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_902_ == 0)
{
lean_object* v_unused_903_; 
v_unused_903_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_903_);
v___x_894_ = v_x_864_;
v_isShared_895_ = v_isSharedCheck_902_;
goto v_resetjp_893_;
}
else
{
lean_dec(v_x_864_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_902_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
uint8_t v_firstDayOfWeek_896_; lean_object* v_minimalDaysInFirstWeek_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v_firstDayOfWeek_896_ = lean_ctor_get_uint8(v_locale_863_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_897_ = lean_ctor_get(v_locale_863_, 0);
v___x_898_ = l_Std_Time_PlainDate_weekYear(v_date_862_, v_firstDayOfWeek_896_, v_minimalDaysInFirstWeek_897_);
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 1);
lean_ctor_set(v___x_894_, 0, v___x_898_);
v___x_900_ = v___x_894_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
case 3:
{
lean_object* v_year_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_912_; 
lean_dec_ref_known(v_x_864_, 1);
v_year_904_ = lean_ctor_get(v_date_862_, 0);
v___x_905_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_906_ = lean_int_mod(v_year_904_, v___x_905_);
v___x_907_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_912_ = lean_int_dec_eq(v___x_906_, v___x_907_);
lean_dec(v___x_906_);
if (v___x_912_ == 0)
{
v___y_866_ = v___x_912_;
goto v___jp_865_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v___x_913_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_914_ = lean_int_mod(v_year_904_, v___x_913_);
v___x_915_ = lean_int_dec_eq(v___x_914_, v___x_907_);
lean_dec(v___x_914_);
if (v___x_915_ == 0)
{
if (v___x_912_ == 0)
{
goto v___jp_908_;
}
else
{
v___y_866_ = v___x_912_;
goto v___jp_865_;
}
}
else
{
goto v___jp_908_;
}
}
v___jp_908_:
{
lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_909_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_910_ = lean_int_mod(v_year_904_, v___x_909_);
v___x_911_ = lean_int_dec_eq(v___x_910_, v___x_907_);
lean_dec(v___x_910_);
v___y_866_ = v___x_911_;
goto v___jp_865_;
}
}
case 7:
{
lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_923_; 
v_isSharedCheck_923_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_923_ == 0)
{
lean_object* v_unused_924_; 
v_unused_924_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_924_);
v___x_917_ = v_x_864_;
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
else
{
lean_dec(v_x_864_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_923_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = l_Std_Time_PlainDate_quarter(v_date_862_);
lean_dec_ref(v_date_862_);
if (v_isShared_918_ == 0)
{
lean_ctor_set_tag(v___x_917_, 1);
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
case 8:
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_932_; 
v_isSharedCheck_932_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_932_ == 0)
{
lean_object* v_unused_933_; 
v_unused_933_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_933_);
v___x_926_ = v_x_864_;
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
else
{
lean_dec(v_x_864_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = l_Std_Time_PlainDate_quarter(v_date_862_);
lean_dec_ref(v_date_862_);
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 1);
lean_ctor_set(v___x_926_, 0, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
case 10:
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_944_);
v___x_935_ = v_x_864_;
v_isShared_936_ = v_isSharedCheck_943_;
goto v_resetjp_934_;
}
else
{
lean_dec(v_x_864_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_943_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
uint8_t v_firstDayOfWeek_937_; lean_object* v_minimalDaysInFirstWeek_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v_firstDayOfWeek_937_ = lean_ctor_get_uint8(v_locale_863_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_938_ = lean_ctor_get(v_locale_863_, 0);
v___x_939_ = l_Std_Time_PlainDate_weekOfYear(v_date_862_, v_firstDayOfWeek_937_, v_minimalDaysInFirstWeek_938_);
if (v_isShared_936_ == 0)
{
lean_ctor_set_tag(v___x_935_, 1);
lean_ctor_set(v___x_935_, 0, v___x_939_);
v___x_941_ = v___x_935_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
case 11:
{
lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_953_; 
v_isSharedCheck_953_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_954_);
v___x_946_ = v_x_864_;
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
else
{
lean_dec(v_x_864_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_953_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
uint8_t v_firstDayOfWeek_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v_firstDayOfWeek_948_ = lean_ctor_get_uint8(v_locale_863_, sizeof(void*)*2);
v___x_949_ = l_Std_Time_PlainDate_weekOfMonth(v_date_862_, v_firstDayOfWeek_948_);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 1);
lean_ctor_set(v___x_946_, 0, v___x_949_);
v___x_951_ = v___x_946_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
case 4:
{
lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_962_; 
v_isSharedCheck_962_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_963_);
v___x_956_ = v_x_864_;
v_isShared_957_ = v_isSharedCheck_962_;
goto v_resetjp_955_;
}
else
{
lean_dec(v_x_864_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_962_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_month_958_; lean_object* v___x_960_; 
v_month_958_ = lean_ctor_get(v_date_862_, 1);
lean_inc(v_month_958_);
lean_dec_ref(v_date_862_);
if (v_isShared_957_ == 0)
{
lean_ctor_set_tag(v___x_956_, 1);
lean_ctor_set(v___x_956_, 0, v_month_958_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_month_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
case 5:
{
lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_971_; 
v_isSharedCheck_971_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_972_);
v___x_965_ = v_x_864_;
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
else
{
lean_dec(v_x_864_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_971_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_month_967_; lean_object* v___x_969_; 
v_month_967_ = lean_ctor_get(v_date_862_, 1);
lean_inc(v_month_967_);
lean_dec_ref(v_date_862_);
if (v_isShared_966_ == 0)
{
lean_ctor_set_tag(v___x_965_, 1);
lean_ctor_set(v___x_965_, 0, v_month_967_);
v___x_969_ = v___x_965_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_month_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
case 6:
{
lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_980_; 
v_isSharedCheck_980_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_980_ == 0)
{
lean_object* v_unused_981_; 
v_unused_981_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_981_);
v___x_974_ = v_x_864_;
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
else
{
lean_dec(v_x_864_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_day_976_; lean_object* v___x_978_; 
v_day_976_ = lean_ctor_get(v_date_862_, 2);
lean_inc(v_day_976_);
lean_dec_ref(v_date_862_);
if (v_isShared_975_ == 0)
{
lean_ctor_set_tag(v___x_974_, 1);
lean_ctor_set(v___x_974_, 0, v_day_976_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_day_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
case 12:
{
uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec_ref_known(v_x_864_, 0);
v___x_982_ = l_Std_Time_PlainDate_weekday(v_date_862_);
v___x_983_ = lean_box(v___x_982_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
case 13:
{
lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_993_; 
v_isSharedCheck_993_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_994_);
v___x_986_ = v_x_864_;
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
else
{
lean_dec(v_x_864_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_988_ = l_Std_Time_PlainDate_weekday(v_date_862_);
v___x_989_ = lean_box(v___x_988_);
if (v_isShared_987_ == 0)
{
lean_ctor_set_tag(v___x_986_, 1);
lean_ctor_set(v___x_986_, 0, v___x_989_);
v___x_991_ = v___x_986_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_989_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
case 14:
{
lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1003_; 
v_isSharedCheck_1003_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_1004_);
v___x_996_ = v_x_864_;
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
else
{
lean_dec(v_x_864_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
uint8_t v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_998_ = l_Std_Time_PlainDate_weekday(v_date_862_);
v___x_999_ = lean_box(v___x_998_);
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 1);
lean_ctor_set(v___x_996_, 0, v___x_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
case 15:
{
lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1012_; 
v_isSharedCheck_1012_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_1013_);
v___x_1006_ = v_x_864_;
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
else
{
lean_dec(v_x_864_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_862_);
lean_dec_ref(v_date_862_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 1);
lean_ctor_set(v___x_1006_, 0, v___x_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
default: 
{
lean_object* v___x_1014_; 
lean_dec_ref(v_x_864_);
lean_dec_ref(v_date_862_);
v___x_1014_ = lean_box(0);
return v___x_1014_;
}
}
v___jp_865_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_867_ = l_Std_Time_PlainDate_dayOfYear(v_date_862_);
lean_dec_ref(v_date_862_);
v___x_868_ = lean_box(v___y_866_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
v___x_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0___boxed(lean_object* v_date_1015_, lean_object* v_locale_1016_, lean_object* v_x_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Std_Time_PlainDate_format___lam__0(v_date_1015_, v_locale_1016_, v_x_1017_);
lean_dec_ref(v_locale_1016_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format(lean_object* v_date_1021_, lean_object* v_format_1022_, lean_object* v_locale_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v_format_1025_; 
v___x_1024_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1025_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1022_, v___x_1024_);
if (lean_obj_tag(v_format_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec_ref(v_locale_1023_);
lean_dec_ref(v_date_1021_);
v_a_1026_ = lean_ctor_get(v_format_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v_format_1025_, 1);
v___x_1027_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1028_ = lean_string_append(v___x_1027_, v_a_1026_);
lean_dec(v_a_1026_);
return v___x_1028_;
}
else
{
lean_object* v_a_1029_; lean_object* v___f_1030_; lean_object* v_res_1031_; 
v_a_1029_ = lean_ctor_get(v_format_1025_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v_format_1025_, 1);
v___f_1030_ = lean_alloc_closure((void*)(l_Std_Time_PlainDate_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1030_, 0, v_date_1021_);
lean_closure_set(v___f_1030_, 1, v_locale_1023_);
v_res_1031_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1029_, v___f_1030_);
if (lean_obj_tag(v_res_1031_) == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1032_;
}
else
{
lean_object* v_val_1033_; 
v_val_1033_ = lean_ctor_get(v_res_1031_, 0);
lean_inc(v_val_1033_);
lean_dec_ref_known(v_res_1031_, 1);
return v_val_1033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString___lam__0(lean_object* v_m_1034_, lean_object* v_d_1035_, lean_object* v_y_1036_){
_start:
{
uint8_t v___y_1038_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1051_; 
v___x_1044_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1045_ = lean_int_mod(v_y_1036_, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1051_ = lean_int_dec_eq(v___x_1045_, v___x_1046_);
lean_dec(v___x_1045_);
if (v___x_1051_ == 0)
{
v___y_1038_ = v___x_1051_;
goto v___jp_1037_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1052_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1053_ = lean_int_mod(v_y_1036_, v___x_1052_);
v___x_1054_ = lean_int_dec_eq(v___x_1053_, v___x_1046_);
lean_dec(v___x_1053_);
if (v___x_1054_ == 0)
{
if (v___x_1051_ == 0)
{
goto v___jp_1047_;
}
else
{
v___y_1038_ = v___x_1051_;
goto v___jp_1037_;
}
}
else
{
goto v___jp_1047_;
}
}
v___jp_1037_:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = l_Std_Time_Month_Ordinal_days(v___y_1038_, v_m_1034_);
v___x_1040_ = lean_int_dec_le(v_d_1035_, v___x_1039_);
lean_dec(v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_dec(v_y_1036_);
lean_dec(v_d_1035_);
lean_dec(v_m_1034_);
v___x_1041_ = lean_box(0);
return v___x_1041_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1042_, 0, v_y_1036_);
lean_ctor_set(v___x_1042_, 1, v_m_1034_);
lean_ctor_set(v___x_1042_, 2, v_d_1035_);
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
v___jp_1047_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v___x_1048_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1049_ = lean_int_mod(v_y_1036_, v___x_1048_);
v___x_1050_ = lean_int_dec_eq(v___x_1049_, v___x_1046_);
lean_dec(v___x_1049_);
v___y_1038_ = v___x_1050_;
goto v___jp_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString(lean_object* v_input_1056_){
_start:
{
lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___f_1057_ = ((lean_object*)(l_Std_Time_PlainDate_fromAmericanDateString___closed__0));
v___x_1058_ = l_Std_Time_Formats_americanDate;
v___x_1059_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1058_, v___f_1057_, v_input_1056_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toAmericanDateString(lean_object* v_input_1060_){
_start:
{
lean_object* v_year_1061_; lean_object* v_month_1062_; lean_object* v_day_1063_; lean_object* v___x_1064_; lean_object* v___x_9__overap_1065_; lean_object* v___x_1066_; 
v_year_1061_ = lean_ctor_get(v_input_1060_, 0);
lean_inc(v_year_1061_);
v_month_1062_ = lean_ctor_get(v_input_1060_, 1);
lean_inc(v_month_1062_);
v_day_1063_ = lean_ctor_get(v_input_1060_, 2);
lean_inc(v_day_1063_);
lean_dec_ref(v_input_1060_);
v___x_1064_ = l_Std_Time_Formats_americanDate;
v___x_9__overap_1065_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1064_);
v___x_1066_ = lean_apply_3(v___x_9__overap_1065_, v_month_1062_, v_day_1063_, v_year_1061_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString___lam__0(lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
uint8_t v___y_1071_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1084_; 
v___x_1077_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1078_ = lean_int_mod(v___y_1067_, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1084_ = lean_int_dec_eq(v___x_1078_, v___x_1079_);
lean_dec(v___x_1078_);
if (v___x_1084_ == 0)
{
v___y_1071_ = v___x_1084_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1085_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1086_ = lean_int_mod(v___y_1067_, v___x_1085_);
v___x_1087_ = lean_int_dec_eq(v___x_1086_, v___x_1079_);
lean_dec(v___x_1086_);
if (v___x_1087_ == 0)
{
if (v___x_1084_ == 0)
{
goto v___jp_1080_;
}
else
{
v___y_1071_ = v___x_1084_;
goto v___jp_1070_;
}
}
else
{
goto v___jp_1080_;
}
}
v___jp_1070_:
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = l_Std_Time_Month_Ordinal_days(v___y_1071_, v___y_1068_);
v___x_1073_ = lean_int_dec_le(v___y_1069_, v___x_1072_);
lean_dec(v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
lean_dec(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec(v___y_1067_);
v___x_1074_ = lean_box(0);
return v___x_1074_;
}
else
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1075_, 0, v___y_1067_);
lean_ctor_set(v___x_1075_, 1, v___y_1068_);
lean_ctor_set(v___x_1075_, 2, v___y_1069_);
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
}
v___jp_1080_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1081_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1082_ = lean_int_mod(v___y_1067_, v___x_1081_);
v___x_1083_ = lean_int_dec_eq(v___x_1082_, v___x_1079_);
lean_dec(v___x_1082_);
v___y_1071_ = v___x_1083_;
goto v___jp_1070_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString(lean_object* v_input_1089_){
_start:
{
lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___f_1090_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_1091_ = l_Std_Time_Formats_sqlDate;
v___x_1092_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1091_, v___f_1090_, v_input_1089_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toSQLDateString(lean_object* v_input_1093_){
_start:
{
lean_object* v_year_1094_; lean_object* v_month_1095_; lean_object* v_day_1096_; lean_object* v___x_1097_; lean_object* v___x_9__overap_1098_; lean_object* v___x_1099_; 
v_year_1094_ = lean_ctor_get(v_input_1093_, 0);
lean_inc(v_year_1094_);
v_month_1095_ = lean_ctor_get(v_input_1093_, 1);
lean_inc(v_month_1095_);
v_day_1096_ = lean_ctor_get(v_input_1093_, 2);
lean_inc(v_day_1096_);
lean_dec_ref(v_input_1093_);
v___x_1097_ = l_Std_Time_Formats_sqlDate;
v___x_9__overap_1098_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1097_);
v___x_1099_ = lean_apply_3(v___x_9__overap_1098_, v_year_1094_, v_month_1095_, v_day_1096_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromLeanDateString(lean_object* v_input_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___f_1101_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_1102_ = l_Std_Time_Formats_leanDate;
v___x_1103_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1102_, v___f_1101_, v_input_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toLeanDateString(lean_object* v_input_1104_){
_start:
{
lean_object* v_year_1105_; lean_object* v_month_1106_; lean_object* v_day_1107_; lean_object* v___x_1108_; lean_object* v___x_9__overap_1109_; lean_object* v___x_1110_; 
v_year_1105_ = lean_ctor_get(v_input_1104_, 0);
lean_inc(v_year_1105_);
v_month_1106_ = lean_ctor_get(v_input_1104_, 1);
lean_inc(v_month_1106_);
v_day_1107_ = lean_ctor_get(v_input_1104_, 2);
lean_inc(v_day_1107_);
lean_dec_ref(v_input_1104_);
v___x_1108_ = l_Std_Time_Formats_leanDate;
v___x_9__overap_1109_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1108_);
v___x_1110_ = lean_apply_3(v___x_9__overap_1109_, v_year_1105_, v_month_1106_, v_day_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_parse(lean_object* v_input_1111_){
_start:
{
lean_object* v___x_1112_; 
lean_inc_ref(v_input_1111_);
v___x_1112_ = l_Std_Time_PlainDate_fromAmericanDateString(v_input_1111_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1113_; 
lean_dec_ref_known(v___x_1112_, 1);
v___x_1113_ = l_Std_Time_PlainDate_fromSQLDateString(v_input_1111_);
return v___x_1113_;
}
else
{
lean_dec_ref(v_input_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0(lean_object* v_data_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1124_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__1));
v___x_1125_ = l_Std_Time_PlainDate_toLeanDateString(v_data_1122_);
v___x_1126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1124_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Repr_addAppParen(v___x_1129_, v___y_1123_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0___boxed(lean_object* v_data_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Std_Time_PlainDate_instRepr___lam__0(v_data_1131_, v___y_1132_);
lean_dec(v___y_1132_);
return v_res_1133_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1136_ = lean_unsigned_to_nat(12u);
v___x_1137_ = lean_nat_to_int(v___x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0(lean_object* v_time_1138_, lean_object* v_x_1139_){
_start:
{
switch(lean_obj_tag(v_x_1139_))
{
case 22:
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1147_; 
v_isSharedCheck_1147_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; 
v_unused_1148_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1148_);
v___x_1141_ = v_x_1139_;
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v_x_1139_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_hour_1143_; lean_object* v___x_1145_; 
v_hour_1143_ = lean_ctor_get(v_time_1138_, 0);
lean_inc(v_hour_1143_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 1);
lean_ctor_set(v___x_1141_, 0, v_hour_1143_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_hour_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
case 21:
{
lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1157_; 
v_isSharedCheck_1157_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; 
v_unused_1158_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1158_);
v___x_1150_ = v_x_1139_;
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
else
{
lean_dec(v_x_1139_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1157_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_hour_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v_hour_1152_ = lean_ctor_get(v_time_1138_, 0);
v___x_1153_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1152_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 1);
lean_ctor_set(v___x_1150_, 0, v___x_1153_);
v___x_1155_ = v___x_1150_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
case 23:
{
lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1166_; 
v_isSharedCheck_1166_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1167_);
v___x_1160_ = v_x_1139_;
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
else
{
lean_dec(v_x_1139_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1166_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_minute_1162_; lean_object* v___x_1164_; 
v_minute_1162_ = lean_ctor_get(v_time_1138_, 1);
lean_inc(v_minute_1162_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set_tag(v___x_1160_, 1);
lean_ctor_set(v___x_1160_, 0, v_minute_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_minute_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
case 27:
{
lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
v_isSharedCheck_1175_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1176_);
v___x_1169_ = v_x_1139_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_dec(v_x_1139_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_nanosecond_1171_; lean_object* v___x_1173_; 
v_nanosecond_1171_ = lean_ctor_get(v_time_1138_, 3);
lean_inc(v_nanosecond_1171_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 1);
lean_ctor_set(v___x_1169_, 0, v_nanosecond_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_nanosecond_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
case 24:
{
lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1184_; 
v_isSharedCheck_1184_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; 
v_unused_1185_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1185_);
v___x_1178_ = v_x_1139_;
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v_x_1139_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_second_1180_; lean_object* v___x_1182_; 
v_second_1180_ = lean_ctor_get(v_time_1138_, 2);
lean_inc(v_second_1180_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set_tag(v___x_1178_, 1);
lean_ctor_set(v___x_1178_, 0, v_second_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_second_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
case 16:
{
lean_object* v_hour_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref_known(v_x_1139_, 0);
v_hour_1186_ = lean_ctor_get(v_time_1138_, 0);
v___x_1187_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1186_);
v___x_1188_ = lean_box(v___x_1187_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
case 17:
{
lean_object* v_hour_1190_; lean_object* v_minute_1191_; lean_object* v_second_1192_; uint8_t v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec_ref_known(v_x_1139_, 0);
v_hour_1190_ = lean_ctor_get(v_time_1138_, 0);
v_minute_1191_ = lean_ctor_get(v_time_1138_, 1);
v_second_1192_ = lean_ctor_get(v_time_1138_, 2);
v___x_1193_ = l_Std_Time_classifyDayPeriod(v_hour_1190_, v_minute_1191_, v_second_1192_);
v___x_1194_ = lean_box(v___x_1193_);
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
case 18:
{
lean_object* v_hour_1196_; lean_object* v_minute_1197_; lean_object* v_second_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec_ref_known(v_x_1139_, 0);
v_hour_1196_ = lean_ctor_get(v_time_1138_, 0);
v_minute_1197_ = lean_ctor_get(v_time_1138_, 1);
v_second_1198_ = lean_ctor_get(v_time_1138_, 2);
v___x_1199_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1196_, v_minute_1197_, v_second_1198_);
v___x_1200_ = lean_box(v___x_1199_);
v___x_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1200_);
return v___x_1201_;
}
case 19:
{
lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1210_; 
v_isSharedCheck_1210_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1211_);
v___x_1203_ = v_x_1139_;
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
else
{
lean_dec(v_x_1139_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1210_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_hour_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v_hour_1205_ = lean_ctor_get(v_time_1138_, 0);
v___x_1206_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1205_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set_tag(v___x_1203_, 1);
lean_ctor_set(v___x_1203_, 0, v___x_1206_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
case 20:
{
lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1221_; 
v_isSharedCheck_1221_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1222_);
v___x_1213_ = v_x_1139_;
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
else
{
lean_dec(v_x_1139_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1221_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_hour_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v_hour_1215_ = lean_ctor_get(v_time_1138_, 0);
v___x_1216_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1217_ = lean_int_emod(v_hour_1215_, v___x_1216_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 1);
lean_ctor_set(v___x_1213_, 0, v___x_1217_);
v___x_1219_ = v___x_1213_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
case 25:
{
lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
v_isSharedCheck_1230_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1231_);
v___x_1224_ = v_x_1139_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v_x_1139_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_nanosecond_1226_; lean_object* v___x_1228_; 
v_nanosecond_1226_ = lean_ctor_get(v_time_1138_, 3);
lean_inc(v_nanosecond_1226_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 1);
lean_ctor_set(v___x_1224_, 0, v_nanosecond_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_nanosecond_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
case 26:
{
lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1239_; 
v_isSharedCheck_1239_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1240_);
v___x_1233_ = v_x_1139_;
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
else
{
lean_dec(v_x_1139_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1138_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set_tag(v___x_1233_, 1);
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
case 28:
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1248_; 
v_isSharedCheck_1248_ = !lean_is_exclusive(v_x_1139_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v_x_1139_, 0);
lean_dec(v_unused_1249_);
v___x_1242_ = v_x_1139_;
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v_x_1139_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1248_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1244_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1138_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set_tag(v___x_1242_, 1);
lean_ctor_set(v___x_1242_, 0, v___x_1244_);
v___x_1246_ = v___x_1242_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
default: 
{
lean_object* v___x_1250_; 
lean_dec_ref(v_x_1139_);
v___x_1250_ = lean_box(0);
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0___boxed(lean_object* v_time_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Std_Time_PlainTime_format___lam__0(v_time_1251_, v_x_1252_);
lean_dec_ref(v_time_1251_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format(lean_object* v_time_1254_, lean_object* v_format_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v_format_1257_; 
v___x_1256_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1257_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1255_, v___x_1256_);
if (lean_obj_tag(v_format_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref(v_time_1254_);
v_a_1258_ = lean_ctor_get(v_format_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v_format_1257_, 1);
v___x_1259_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1260_ = lean_string_append(v___x_1259_, v_a_1258_);
lean_dec(v_a_1258_);
return v___x_1260_;
}
else
{
lean_object* v_a_1261_; lean_object* v___f_1262_; lean_object* v_res_1263_; 
v_a_1261_ = lean_ctor_get(v_format_1257_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v_format_1257_, 1);
v___f_1262_ = lean_alloc_closure((void*)(l_Std_Time_PlainTime_format___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1262_, 0, v_time_1254_);
v_res_1263_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1261_, v___f_1262_);
if (lean_obj_tag(v_res_1263_) == 0)
{
lean_object* v___x_1264_; 
v___x_1264_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1264_;
}
else
{
lean_object* v_val_1265_; 
v_val_1265_ = lean_ctor_get(v_res_1263_, 0);
lean_inc(v_val_1265_);
lean_dec_ref_known(v_res_1263_, 1);
return v_val_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour___lam__0(lean_object* v_h_1266_, lean_object* v_m_1267_, lean_object* v_s_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1270_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1270_, 0, v_h_1266_);
lean_ctor_set(v___x_1270_, 1, v_m_1267_);
lean_ctor_set(v___x_1270_, 2, v_s_1268_);
lean_ctor_set(v___x_1270_, 3, v___x_1269_);
v___x_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour(lean_object* v_input_1273_){
_start:
{
lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___f_1274_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1275_ = l_Std_Time_Formats_time24Hour;
v___x_1276_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1275_, v___f_1274_, v_input_1273_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime24Hour(lean_object* v_input_1277_){
_start:
{
lean_object* v_hour_1278_; lean_object* v_minute_1279_; lean_object* v_second_1280_; lean_object* v___x_1281_; lean_object* v___x_9__overap_1282_; lean_object* v___x_1283_; 
v_hour_1278_ = lean_ctor_get(v_input_1277_, 0);
lean_inc(v_hour_1278_);
v_minute_1279_ = lean_ctor_get(v_input_1277_, 1);
lean_inc(v_minute_1279_);
v_second_1280_ = lean_ctor_get(v_input_1277_, 2);
lean_inc(v_second_1280_);
lean_dec_ref(v_input_1277_);
v___x_1281_ = l_Std_Time_Formats_time24Hour;
v___x_9__overap_1282_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1281_);
v___x_1283_ = lean_apply_3(v___x_9__overap_1282_, v_hour_1278_, v_minute_1279_, v_second_1280_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0(lean_object* v_h_1284_, lean_object* v_m_1285_, lean_object* v_s_1286_, lean_object* v_n_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1288_, 0, v_h_1284_);
lean_ctor_set(v___x_1288_, 1, v_m_1285_);
lean_ctor_set(v___x_1288_, 2, v_s_1286_);
lean_ctor_set(v___x_1288_, 3, v_n_1287_);
v___x_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1288_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour(lean_object* v_input_1291_){
_start:
{
lean_object* v___f_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___f_1292_ = ((lean_object*)(l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0));
v___x_1293_ = l_Std_Time_Formats_leanTime24Hour;
lean_inc_ref(v_input_1291_);
v___x_1294_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1293_, v___f_1292_, v_input_1291_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v___f_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec_ref_known(v___x_1294_, 1);
v___f_1295_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1296_ = l_Std_Time_Formats_leanTime24HourNoNanos;
v___x_1297_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1296_, v___f_1295_, v_input_1291_);
return v___x_1297_;
}
else
{
lean_dec_ref(v_input_1291_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toLeanTime24Hour(lean_object* v_input_1298_){
_start:
{
lean_object* v_hour_1299_; lean_object* v_minute_1300_; lean_object* v_second_1301_; lean_object* v_nanosecond_1302_; lean_object* v___x_1303_; lean_object* v___x_10__overap_1304_; lean_object* v___x_1305_; 
v_hour_1299_ = lean_ctor_get(v_input_1298_, 0);
lean_inc(v_hour_1299_);
v_minute_1300_ = lean_ctor_get(v_input_1298_, 1);
lean_inc(v_minute_1300_);
v_second_1301_ = lean_ctor_get(v_input_1298_, 2);
lean_inc(v_second_1301_);
v_nanosecond_1302_ = lean_ctor_get(v_input_1298_, 3);
lean_inc(v_nanosecond_1302_);
lean_dec_ref(v_input_1298_);
v___x_1303_ = l_Std_Time_Formats_leanTime24Hour;
v___x_10__overap_1304_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1303_);
v___x_1305_ = lean_apply_4(v___x_10__overap_1304_, v_hour_1299_, v_minute_1300_, v_second_1301_, v_nanosecond_1302_);
return v___x_1305_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_nat_to_int(v___x_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0(lean_object* v_h_1308_, lean_object* v_m_1309_, lean_object* v_s_1310_, uint8_t v_a_1311_){
_start:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1313_ = lean_int_dec_le(v___x_1312_, v_h_1308_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
lean_dec(v_s_1310_);
lean_dec(v_m_1309_);
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1316_ = lean_int_dec_le(v_h_1308_, v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec(v_s_1310_);
lean_dec(v_m_1309_);
v___x_1317_ = lean_box(0);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = l_Std_Time_HourMarker_toAbsolute(v_a_1311_, v_h_1308_);
v___x_1319_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1320_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1318_);
lean_ctor_set(v___x_1320_, 1, v_m_1309_);
lean_ctor_set(v___x_1320_, 2, v_s_1310_);
lean_ctor_set(v___x_1320_, 3, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
return v___x_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed(lean_object* v_h_1322_, lean_object* v_m_1323_, lean_object* v_s_1324_, lean_object* v_a_1325_){
_start:
{
uint8_t v_a_boxed_1326_; lean_object* v_res_1327_; 
v_a_boxed_1326_ = lean_unbox(v_a_1325_);
v_res_1327_ = l_Std_Time_PlainTime_fromTime12Hour___lam__0(v_h_1322_, v_m_1323_, v_s_1324_, v_a_boxed_1326_);
lean_dec(v_h_1322_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour(lean_object* v_input_1329_){
_start:
{
lean_object* v_builder_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v_builder_1330_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime12Hour___closed__0));
v___x_1331_ = l_Std_Time_Formats_time12Hour;
v___x_1332_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1331_, v_builder_1330_, v_input_1329_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime12Hour(lean_object* v_input_1333_){
_start:
{
lean_object* v_hour_1334_; lean_object* v_minute_1335_; lean_object* v_second_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_hour_1334_ = lean_ctor_get(v_input_1333_, 0);
lean_inc(v_hour_1334_);
v_minute_1335_ = lean_ctor_get(v_input_1333_, 1);
lean_inc(v_minute_1335_);
v_second_1336_ = lean_ctor_get(v_input_1333_, 2);
lean_inc(v_second_1336_);
lean_dec_ref(v_input_1333_);
v___x_1337_ = l_Std_Time_Formats_time12Hour;
v___x_1338_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1339_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1340_ = lean_int_emod(v_hour_1334_, v___x_1338_);
v___x_1341_ = lean_int_add(v___x_1340_, v___x_1339_);
lean_dec(v___x_1340_);
v___x_1342_ = lean_int_dec_le(v___x_1338_, v_hour_1334_);
lean_dec(v_hour_1334_);
if (v___x_1342_ == 0)
{
uint8_t v___x_1343_; lean_object* v___x_58__overap_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1343_ = 0;
v___x_58__overap_1344_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1337_);
v___x_1345_ = lean_box(v___x_1343_);
v___x_1346_ = lean_apply_4(v___x_58__overap_1344_, v___x_1341_, v_minute_1335_, v_second_1336_, v___x_1345_);
return v___x_1346_;
}
else
{
uint8_t v___x_1347_; lean_object* v___x_60__overap_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1347_ = 1;
v___x_60__overap_1348_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1337_);
v___x_1349_ = lean_box(v___x_1347_);
v___x_1350_ = lean_apply_4(v___x_60__overap_1348_, v___x_1341_, v_minute_1335_, v_second_1336_, v___x_1349_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_parse(lean_object* v_input_1351_){
_start:
{
lean_object* v___x_1352_; 
lean_inc_ref(v_input_1351_);
v___x_1352_ = l_Std_Time_PlainTime_fromTime12Hour(v_input_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v___x_1353_; 
lean_dec_ref_known(v___x_1352_, 1);
v___x_1353_ = l_Std_Time_PlainTime_fromTime24Hour(v_input_1351_);
return v___x_1353_;
}
else
{
lean_dec_ref(v_input_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0(lean_object* v_data_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1361_ = ((lean_object*)(l_Std_Time_PlainTime_instRepr___lam__0___closed__1));
v___x_1362_ = l_Std_Time_PlainTime_toLeanTime24Hour(v_data_1359_);
v___x_1363_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
v___x_1364_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1361_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1364_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = l_Repr_addAppParen(v___x_1366_, v___y_1360_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0___boxed(lean_object* v_data_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Std_Time_PlainTime_instRepr___lam__0(v_data_1368_, v___y_1369_);
lean_dec(v___y_1369_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format(lean_object* v_data_1373_, lean_object* v_format_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v_format_1376_; 
v___x_1375_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1376_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1374_, v___x_1375_);
if (lean_obj_tag(v_format_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec_ref(v_data_1373_);
v_a_1377_ = lean_ctor_get(v_format_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v_format_1376_, 1);
v___x_1378_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1379_ = lean_string_append(v___x_1378_, v_a_1377_);
lean_dec(v_a_1377_);
return v___x_1379_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v_a_1380_ = lean_ctor_get(v_format_1376_, 0);
lean_inc(v_a_1380_);
lean_dec_ref_known(v_format_1376_, 1);
v___x_1381_ = lean_box(1);
v___x_1382_ = l_Std_Time_GenericFormat_format(v___x_1381_, v_a_1380_, v_data_1373_);
return v___x_1382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromISO8601String(lean_object* v_input_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = lean_box(1);
v___x_1385_ = l_Std_Time_Formats_iso8601;
v___x_1386_ = l_Std_Time_GenericFormat_parse(v___x_1384_, v___x_1385_, v_input_1383_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String(lean_object* v_date_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_box(1);
v___x_1389_ = l_Std_Time_Formats_iso8601;
v___x_1390_ = l_Std_Time_GenericFormat_format(v___x_1388_, v___x_1389_, v_date_1387_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC822String(lean_object* v_input_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_box(1);
v___x_1393_ = l_Std_Time_Formats_rfc822;
v___x_1394_ = l_Std_Time_GenericFormat_parse(v___x_1392_, v___x_1393_, v_input_1391_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String(lean_object* v_date_1395_){
_start:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = lean_box(1);
v___x_1397_ = l_Std_Time_Formats_rfc822;
v___x_1398_ = l_Std_Time_GenericFormat_format(v___x_1396_, v___x_1397_, v_date_1395_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC850String(lean_object* v_input_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_box(1);
v___x_1401_ = l_Std_Time_Formats_rfc850;
v___x_1402_ = l_Std_Time_GenericFormat_parse(v___x_1400_, v___x_1401_, v_input_1399_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String(lean_object* v_date_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_box(1);
v___x_1405_ = l_Std_Time_Formats_rfc850;
v___x_1406_ = l_Std_Time_GenericFormat_format(v___x_1404_, v___x_1405_, v_date_1403_);
return v___x_1406_;
}
}
static lean_object* _init_l_Std_Time_DateTime_toHTTPDateString___closed__0(void){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = l_Std_Time_TimeZone_GMT;
v___x_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toHTTPDateString(lean_object* v_date_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = lean_obj_once(&l_Std_Time_DateTime_toHTTPDateString___closed__0, &l_Std_Time_DateTime_toHTTPDateString___closed__0_once, _init_l_Std_Time_DateTime_toHTTPDateString___closed__0);
v___x_1411_ = l_Std_Time_Formats_httpDate;
v___x_1412_ = l_Std_Time_GenericFormat_format(v___x_1410_, v___x_1411_, v_date_1409_);
return v___x_1412_;
}
}
static lean_object* _init_l_Std_Time_DateTime_fromHTTPDateString___closed__0(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(2070u);
v___x_1414_ = lean_nat_to_int(v___x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromHTTPDateString(lean_object* v_input_1415_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_obj_once(&l_Std_Time_DateTime_toHTTPDateString___closed__0, &l_Std_Time_DateTime_toHTTPDateString___closed__0_once, _init_l_Std_Time_DateTime_toHTTPDateString___closed__0);
v___x_1417_ = l_Std_Time_Formats_httpDate;
lean_inc_ref(v_input_1415_);
v___x_1418_ = l_Std_Time_GenericFormat_parse(v___x_1416_, v___x_1417_, v_input_1415_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec_ref_known(v___x_1418_, 1);
v___x_1419_ = l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850;
lean_inc_ref(v_input_1415_);
v___x_1420_ = l_Std_Time_GenericFormat_parse(v___x_1416_, v___x_1419_, v_input_1415_);
if (lean_obj_tag(v___x_1420_) == 0)
{
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_dec_ref_known(v___x_1420_, 1);
v___x_1421_ = l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime;
lean_inc_ref(v_input_1415_);
v___x_1422_ = l_Std_Time_GenericFormat_parse(v___x_1416_, v___x_1421_, v_input_1415_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_dec_ref_known(v___x_1422_, 1);
v___x_1423_ = l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded;
v___x_1424_ = l_Std_Time_GenericFormat_parse(v___x_1416_, v___x_1423_, v_input_1415_);
return v___x_1424_;
}
else
{
lean_dec_ref(v_input_1415_);
return v___x_1422_;
}
}
else
{
lean_dec_ref(v_input_1415_);
return v___x_1420_;
}
}
else
{
lean_object* v_a_1425_; lean_object* v_date_1426_; lean_object* v___x_1427_; lean_object* v_date_1428_; lean_object* v_year_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
lean_dec_ref(v_input_1415_);
v_a_1425_ = lean_ctor_get(v___x_1420_, 0);
v_date_1426_ = lean_ctor_get(v_a_1425_, 0);
v___x_1427_ = lean_thunk_get_own(v_date_1426_);
v_date_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc_ref(v_date_1428_);
lean_dec(v___x_1427_);
v_year_1429_ = lean_ctor_get(v_date_1428_, 0);
lean_inc(v_year_1429_);
lean_dec_ref(v_date_1428_);
v___x_1430_ = lean_obj_once(&l_Std_Time_DateTime_fromHTTPDateString___closed__0, &l_Std_Time_DateTime_fromHTTPDateString___closed__0_once, _init_l_Std_Time_DateTime_fromHTTPDateString___closed__0);
v___x_1431_ = lean_int_dec_le(v___x_1430_, v_year_1429_);
lean_dec(v_year_1429_);
if (v___x_1431_ == 0)
{
return v___x_1420_;
}
else
{
lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1440_; 
lean_inc(v_a_1425_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; 
v_unused_1441_ = lean_ctor_get(v___x_1420_, 0);
lean_dec(v_unused_1441_);
v___x_1433_ = v___x_1420_;
v_isShared_1434_ = v_isSharedCheck_1440_;
goto v_resetjp_1432_;
}
else
{
lean_dec(v___x_1420_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1440_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1435_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1436_ = l_Std_Time_DateTime_subYearsClip(v_a_1425_, v___x_1435_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1436_);
v___x_1438_ = v___x_1433_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
else
{
lean_dec_ref(v_input_1415_);
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromDateTimeWithZoneString(lean_object* v_input_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_box(1);
v___x_1444_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1445_ = l_Std_Time_GenericFormat_parse(v___x_1443_, v___x_1444_, v_input_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString(lean_object* v_pdt_1446_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1447_ = lean_box(1);
v___x_1448_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1449_ = l_Std_Time_GenericFormat_format(v___x_1447_, v___x_1448_, v_pdt_1446_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithZoneString(lean_object* v_input_1450_){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = lean_box(1);
v___x_1452_ = l_Std_Time_Formats_leanDateTimeWithZone;
lean_inc_ref(v_input_1450_);
v___x_1453_ = l_Std_Time_GenericFormat_parse(v___x_1451_, v___x_1452_, v_input_1450_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref_known(v___x_1453_, 1);
v___x_1454_ = l_Std_Time_Formats_leanDateTimeWithZoneNoNanos;
v___x_1455_ = l_Std_Time_GenericFormat_parse(v___x_1451_, v___x_1454_, v_input_1450_);
return v___x_1455_;
}
else
{
lean_dec_ref(v_input_1450_);
return v___x_1453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(lean_object* v_input_1456_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_box(1);
v___x_1458_ = l_Std_Time_Formats_leanDateTimeWithIdentifier;
lean_inc_ref(v_input_1456_);
v___x_1459_ = l_Std_Time_GenericFormat_parse(v___x_1457_, v___x_1458_, v_input_1456_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec_ref_known(v___x_1459_, 1);
v___x_1460_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_1461_ = l_Std_Time_GenericFormat_parse(v___x_1457_, v___x_1460_, v_input_1456_);
return v___x_1461_;
}
else
{
lean_dec_ref(v_input_1456_);
return v___x_1459_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString(lean_object* v_zdt_1462_){
_start:
{
lean_object* v_date_1463_; lean_object* v_timezone_1464_; lean_object* v___x_1465_; lean_object* v_date_1466_; lean_object* v_time_1467_; lean_object* v_year_1468_; lean_object* v_month_1469_; lean_object* v_day_1470_; lean_object* v_hour_1471_; lean_object* v_minute_1472_; lean_object* v_second_1473_; lean_object* v_nanosecond_1474_; lean_object* v_offset_1475_; lean_object* v___x_1476_; lean_object* v___x_43__overap_1477_; lean_object* v___x_1478_; 
v_date_1463_ = lean_ctor_get(v_zdt_1462_, 0);
lean_inc_ref(v_date_1463_);
v_timezone_1464_ = lean_ctor_get(v_zdt_1462_, 3);
lean_inc_ref(v_timezone_1464_);
lean_dec_ref(v_zdt_1462_);
v___x_1465_ = lean_thunk_get_own(v_date_1463_);
lean_dec_ref(v_date_1463_);
v_date_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc_ref(v_date_1466_);
v_time_1467_ = lean_ctor_get(v___x_1465_, 1);
lean_inc_ref(v_time_1467_);
lean_dec(v___x_1465_);
v_year_1468_ = lean_ctor_get(v_date_1466_, 0);
lean_inc(v_year_1468_);
v_month_1469_ = lean_ctor_get(v_date_1466_, 1);
lean_inc(v_month_1469_);
v_day_1470_ = lean_ctor_get(v_date_1466_, 2);
lean_inc(v_day_1470_);
lean_dec_ref(v_date_1466_);
v_hour_1471_ = lean_ctor_get(v_time_1467_, 0);
lean_inc(v_hour_1471_);
v_minute_1472_ = lean_ctor_get(v_time_1467_, 1);
lean_inc(v_minute_1472_);
v_second_1473_ = lean_ctor_get(v_time_1467_, 2);
lean_inc(v_second_1473_);
v_nanosecond_1474_ = lean_ctor_get(v_time_1467_, 3);
lean_inc(v_nanosecond_1474_);
lean_dec_ref(v_time_1467_);
v_offset_1475_ = lean_ctor_get(v_timezone_1464_, 0);
lean_inc(v_offset_1475_);
lean_dec_ref(v_timezone_1464_);
v___x_1476_ = l_Std_Time_Formats_leanDateTimeWithZone;
v___x_43__overap_1477_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1476_);
v___x_1478_ = lean_apply_8(v___x_43__overap_1477_, v_year_1468_, v_month_1469_, v_day_1470_, v_hour_1471_, v_minute_1472_, v_second_1473_, v_nanosecond_1474_, v_offset_1475_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithIdentifierString(lean_object* v_zdt_1479_){
_start:
{
lean_object* v_date_1480_; lean_object* v_timezone_1481_; lean_object* v___x_1482_; lean_object* v_date_1483_; lean_object* v_time_1484_; lean_object* v_year_1485_; lean_object* v_month_1486_; lean_object* v_day_1487_; lean_object* v_hour_1488_; lean_object* v_minute_1489_; lean_object* v_second_1490_; lean_object* v_nanosecond_1491_; lean_object* v_name_1492_; lean_object* v___x_1493_; lean_object* v___x_42__overap_1494_; lean_object* v___x_1495_; 
v_date_1480_ = lean_ctor_get(v_zdt_1479_, 0);
lean_inc_ref(v_date_1480_);
v_timezone_1481_ = lean_ctor_get(v_zdt_1479_, 3);
lean_inc_ref(v_timezone_1481_);
lean_dec_ref(v_zdt_1479_);
v___x_1482_ = lean_thunk_get_own(v_date_1480_);
lean_dec_ref(v_date_1480_);
v_date_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc_ref(v_date_1483_);
v_time_1484_ = lean_ctor_get(v___x_1482_, 1);
lean_inc_ref(v_time_1484_);
lean_dec(v___x_1482_);
v_year_1485_ = lean_ctor_get(v_date_1483_, 0);
lean_inc(v_year_1485_);
v_month_1486_ = lean_ctor_get(v_date_1483_, 1);
lean_inc(v_month_1486_);
v_day_1487_ = lean_ctor_get(v_date_1483_, 2);
lean_inc(v_day_1487_);
lean_dec_ref(v_date_1483_);
v_hour_1488_ = lean_ctor_get(v_time_1484_, 0);
lean_inc(v_hour_1488_);
v_minute_1489_ = lean_ctor_get(v_time_1484_, 1);
lean_inc(v_minute_1489_);
v_second_1490_ = lean_ctor_get(v_time_1484_, 2);
lean_inc(v_second_1490_);
v_nanosecond_1491_ = lean_ctor_get(v_time_1484_, 3);
lean_inc(v_nanosecond_1491_);
lean_dec_ref(v_time_1484_);
v_name_1492_ = lean_ctor_get(v_timezone_1481_, 1);
lean_inc_ref(v_name_1492_);
lean_dec_ref(v_timezone_1481_);
v___x_1493_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_42__overap_1494_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1493_);
v___x_1495_ = lean_apply_8(v___x_42__overap_1494_, v_year_1485_, v_month_1486_, v_day_1487_, v_hour_1488_, v_minute_1489_, v_second_1490_, v_nanosecond_1491_, v_name_1492_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_parse(lean_object* v_input_1496_){
_start:
{
lean_object* v___x_1497_; 
lean_inc_ref(v_input_1496_);
v___x_1497_ = l_Std_Time_DateTime_fromISO8601String(v_input_1496_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v___x_1498_; 
lean_dec_ref_known(v___x_1497_, 1);
lean_inc_ref(v_input_1496_);
v___x_1498_ = l_Std_Time_DateTime_fromRFC822String(v_input_1496_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v___x_1499_; 
lean_dec_ref_known(v___x_1498_, 1);
lean_inc_ref(v_input_1496_);
v___x_1499_ = l_Std_Time_DateTime_fromRFC850String(v_input_1496_);
if (lean_obj_tag(v___x_1499_) == 0)
{
lean_object* v___x_1500_; 
lean_dec_ref_known(v___x_1499_, 1);
lean_inc_ref(v_input_1496_);
v___x_1500_ = l_Std_Time_DateTime_fromDateTimeWithZoneString(v_input_1496_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v___x_1501_; 
lean_dec_ref_known(v___x_1500_, 1);
v___x_1501_ = l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(v_input_1496_);
return v___x_1501_;
}
else
{
lean_dec_ref(v_input_1496_);
return v___x_1500_;
}
}
else
{
lean_dec_ref(v_input_1496_);
return v___x_1499_;
}
}
else
{
lean_dec_ref(v_input_1496_);
return v___x_1498_;
}
}
else
{
lean_dec_ref(v_input_1496_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0(lean_object* v_data_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1509_ = ((lean_object*)(l_Std_Time_DateTime_instRepr___lam__0___closed__1));
v___x_1510_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_data_1507_);
v___x_1511_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
v___x_1512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1509_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1512_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = l_Repr_addAppParen(v___x_1514_, v___y_1508_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0___boxed(lean_object* v_data_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_Time_DateTime_instRepr___lam__0(v_data_1516_, v___y_1517_);
lean_dec(v___y_1517_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0(lean_object* v_date_1521_, lean_object* v_locale_1522_, lean_object* v_x_1523_){
_start:
{
switch(lean_obj_tag(v_x_1523_))
{
case 0:
{
lean_object* v_date_1524_; lean_object* v_year_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec_ref_known(v_x_1523_, 0);
v_date_1524_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1524_);
lean_dec_ref(v_date_1521_);
v_year_1525_ = lean_ctor_get(v_date_1524_, 0);
lean_inc(v_year_1525_);
lean_dec_ref(v_date_1524_);
v___x_1526_ = l_Std_Time_Year_Offset_era(v_year_1525_);
lean_dec(v_year_1525_);
v___x_1527_ = lean_box(v___x_1526_);
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1527_);
return v___x_1528_;
}
case 2:
{
lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1537_; 
v_isSharedCheck_1537_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1538_);
v___x_1530_ = v_x_1523_;
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v_x_1523_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_date_1532_; lean_object* v_year_1533_; lean_object* v___x_1535_; 
v_date_1532_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1532_);
lean_dec_ref(v_date_1521_);
v_year_1533_ = lean_ctor_get(v_date_1532_, 0);
lean_inc(v_year_1533_);
lean_dec_ref(v_date_1532_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 1);
lean_ctor_set(v___x_1530_, 0, v_year_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_year_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
case 1:
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1547_; 
v_isSharedCheck_1547_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1548_);
v___x_1540_ = v_x_1523_;
v_isShared_1541_ = v_isSharedCheck_1547_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v_x_1523_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1547_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v_date_1542_; lean_object* v_year_1543_; lean_object* v___x_1545_; 
v_date_1542_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1542_);
lean_dec_ref(v_date_1521_);
v_year_1543_ = lean_ctor_get(v_date_1542_, 0);
lean_inc(v_year_1543_);
lean_dec_ref(v_date_1542_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v_year_1543_);
v___x_1545_ = v___x_1540_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_year_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
case 9:
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1559_; 
v_isSharedCheck_1559_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1560_);
v___x_1550_ = v_x_1523_;
v_isShared_1551_ = v_isSharedCheck_1559_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_x_1523_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1559_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
uint8_t v_firstDayOfWeek_1552_; lean_object* v_minimalDaysInFirstWeek_1553_; lean_object* v_date_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v_firstDayOfWeek_1552_ = lean_ctor_get_uint8(v_locale_1522_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1553_ = lean_ctor_get(v_locale_1522_, 0);
v_date_1554_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1554_);
lean_dec_ref(v_date_1521_);
v___x_1555_ = l_Std_Time_PlainDate_weekYear(v_date_1554_, v_firstDayOfWeek_1552_, v_minimalDaysInFirstWeek_1553_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set_tag(v___x_1550_, 1);
lean_ctor_set(v___x_1550_, 0, v___x_1555_);
v___x_1557_ = v___x_1550_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
case 3:
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1612_; 
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1613_);
v___x_1562_ = v_x_1523_;
v_isShared_1563_ = v_isSharedCheck_1612_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_x_1523_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1612_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_date_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1610_; 
v_date_1564_ = lean_ctor_get(v_date_1521_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_date_1521_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v_date_1521_, 1);
lean_dec(v_unused_1611_);
v___x_1566_ = v_date_1521_;
v_isShared_1567_ = v_isSharedCheck_1610_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_date_1564_);
lean_dec(v_date_1521_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1610_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_year_1568_; lean_object* v_month_1569_; lean_object* v_day_1570_; uint8_t v___y_1572_; uint8_t v___y_1573_; uint8_t v___y_1584_; lean_object* v___y_1585_; lean_object* v___y_1586_; uint8_t v___y_1591_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1606_; 
v_year_1568_ = lean_ctor_get(v_date_1564_, 0);
lean_inc(v_year_1568_);
v_month_1569_ = lean_ctor_get(v_date_1564_, 1);
lean_inc(v_month_1569_);
v_day_1570_ = lean_ctor_get(v_date_1564_, 2);
lean_inc(v_day_1570_);
lean_dec_ref(v_date_1564_);
v___x_1599_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1600_ = lean_int_mod(v_year_1568_, v___x_1599_);
v___x_1601_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1606_ = lean_int_dec_eq(v___x_1600_, v___x_1601_);
lean_dec(v___x_1600_);
if (v___x_1606_ == 0)
{
v___y_1591_ = v___x_1606_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1607_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1608_ = lean_int_mod(v_year_1568_, v___x_1607_);
v___x_1609_ = lean_int_dec_eq(v___x_1608_, v___x_1601_);
lean_dec(v___x_1608_);
if (v___x_1609_ == 0)
{
if (v___x_1606_ == 0)
{
goto v___jp_1602_;
}
else
{
v___y_1591_ = v___x_1606_;
goto v___jp_1590_;
}
}
else
{
goto v___jp_1602_;
}
}
v___jp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 1, v_day_1570_);
lean_ctor_set(v___x_1566_, 0, v_month_1569_);
v___x_1575_ = v___x_1566_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_month_1569_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_day_1570_);
v___x_1575_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1576_ = l_Std_Time_ValidDate_dayOfYear(v___y_1573_, v___x_1575_);
lean_dec_ref(v___x_1575_);
v___x_1577_ = lean_box(v___y_1572_);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
lean_ctor_set(v___x_1578_, 1, v___x_1576_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 1);
lean_ctor_set(v___x_1562_, 0, v___x_1578_);
v___x_1580_ = v___x_1562_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
v___jp_1583_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1587_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1588_ = lean_int_mod(v___y_1585_, v___x_1587_);
lean_dec(v___y_1585_);
v___x_1589_ = lean_int_dec_eq(v___x_1588_, v___y_1586_);
lean_dec(v___x_1588_);
v___y_1572_ = v___y_1584_;
v___y_1573_ = v___x_1589_;
goto v___jp_1571_;
}
v___jp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1592_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1593_ = lean_int_mod(v_year_1568_, v___x_1592_);
v___x_1594_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1595_ = lean_int_dec_eq(v___x_1593_, v___x_1594_);
lean_dec(v___x_1593_);
if (v___x_1595_ == 0)
{
lean_dec(v_year_1568_);
v___y_1572_ = v___y_1591_;
v___y_1573_ = v___x_1595_;
goto v___jp_1571_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1596_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1597_ = lean_int_mod(v_year_1568_, v___x_1596_);
v___x_1598_ = lean_int_dec_eq(v___x_1597_, v___x_1594_);
lean_dec(v___x_1597_);
if (v___x_1598_ == 0)
{
if (v___x_1595_ == 0)
{
v___y_1584_ = v___y_1591_;
v___y_1585_ = v_year_1568_;
v___y_1586_ = v___x_1594_;
goto v___jp_1583_;
}
else
{
lean_dec(v_year_1568_);
v___y_1572_ = v___y_1591_;
v___y_1573_ = v___x_1595_;
goto v___jp_1571_;
}
}
else
{
v___y_1584_ = v___y_1591_;
v___y_1585_ = v_year_1568_;
v___y_1586_ = v___x_1594_;
goto v___jp_1583_;
}
}
}
v___jp_1602_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; uint8_t v___x_1605_; 
v___x_1603_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1604_ = lean_int_mod(v_year_1568_, v___x_1603_);
v___x_1605_ = lean_int_dec_eq(v___x_1604_, v___x_1601_);
lean_dec(v___x_1604_);
v___y_1591_ = v___x_1605_;
goto v___jp_1590_;
}
}
}
}
case 7:
{
lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1622_; 
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1623_);
v___x_1615_ = v_x_1523_;
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
else
{
lean_dec(v_x_1523_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_date_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v_date_1617_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1617_);
lean_dec_ref(v_date_1521_);
v___x_1618_ = l_Std_Time_PlainDate_quarter(v_date_1617_);
lean_dec_ref(v_date_1617_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set_tag(v___x_1615_, 1);
lean_ctor_set(v___x_1615_, 0, v___x_1618_);
v___x_1620_ = v___x_1615_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
case 8:
{
lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1632_; 
v_isSharedCheck_1632_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; 
v_unused_1633_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1633_);
v___x_1625_ = v_x_1523_;
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
else
{
lean_dec(v_x_1523_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1632_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_date_1627_; lean_object* v___x_1628_; lean_object* v___x_1630_; 
v_date_1627_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1627_);
lean_dec_ref(v_date_1521_);
v___x_1628_ = l_Std_Time_PlainDate_quarter(v_date_1627_);
lean_dec_ref(v_date_1627_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set_tag(v___x_1625_, 1);
lean_ctor_set(v___x_1625_, 0, v___x_1628_);
v___x_1630_ = v___x_1625_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
case 10:
{
lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1644_; 
v_isSharedCheck_1644_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1644_ == 0)
{
lean_object* v_unused_1645_; 
v_unused_1645_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1645_);
v___x_1635_ = v_x_1523_;
v_isShared_1636_ = v_isSharedCheck_1644_;
goto v_resetjp_1634_;
}
else
{
lean_dec(v_x_1523_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1644_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
uint8_t v_firstDayOfWeek_1637_; lean_object* v_minimalDaysInFirstWeek_1638_; lean_object* v_date_1639_; lean_object* v___x_1640_; lean_object* v___x_1642_; 
v_firstDayOfWeek_1637_ = lean_ctor_get_uint8(v_locale_1522_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1638_ = lean_ctor_get(v_locale_1522_, 0);
v_date_1639_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1639_);
lean_dec_ref(v_date_1521_);
v___x_1640_ = l_Std_Time_PlainDate_weekOfYear(v_date_1639_, v_firstDayOfWeek_1637_, v_minimalDaysInFirstWeek_1638_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set_tag(v___x_1635_, 1);
lean_ctor_set(v___x_1635_, 0, v___x_1640_);
v___x_1642_ = v___x_1635_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
case 11:
{
lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1655_; 
v_isSharedCheck_1655_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; 
v_unused_1656_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1656_);
v___x_1647_ = v_x_1523_;
v_isShared_1648_ = v_isSharedCheck_1655_;
goto v_resetjp_1646_;
}
else
{
lean_dec(v_x_1523_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1655_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
uint8_t v_firstDayOfWeek_1649_; lean_object* v_date_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
v_firstDayOfWeek_1649_ = lean_ctor_get_uint8(v_locale_1522_, sizeof(void*)*2);
v_date_1650_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1650_);
lean_dec_ref(v_date_1521_);
v___x_1651_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1650_, v_firstDayOfWeek_1649_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set_tag(v___x_1647_, 1);
lean_ctor_set(v___x_1647_, 0, v___x_1651_);
v___x_1653_ = v___x_1647_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
case 4:
{
lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1665_; 
v_isSharedCheck_1665_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1665_ == 0)
{
lean_object* v_unused_1666_; 
v_unused_1666_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1666_);
v___x_1658_ = v_x_1523_;
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
else
{
lean_dec(v_x_1523_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1665_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_date_1660_; lean_object* v_month_1661_; lean_object* v___x_1663_; 
v_date_1660_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1660_);
lean_dec_ref(v_date_1521_);
v_month_1661_ = lean_ctor_get(v_date_1660_, 1);
lean_inc(v_month_1661_);
lean_dec_ref(v_date_1660_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set_tag(v___x_1658_, 1);
lean_ctor_set(v___x_1658_, 0, v_month_1661_);
v___x_1663_ = v___x_1658_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_month_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
case 5:
{
lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1675_; 
v_isSharedCheck_1675_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1675_ == 0)
{
lean_object* v_unused_1676_; 
v_unused_1676_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1676_);
v___x_1668_ = v_x_1523_;
v_isShared_1669_ = v_isSharedCheck_1675_;
goto v_resetjp_1667_;
}
else
{
lean_dec(v_x_1523_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1675_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v_date_1670_; lean_object* v_month_1671_; lean_object* v___x_1673_; 
v_date_1670_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1670_);
lean_dec_ref(v_date_1521_);
v_month_1671_ = lean_ctor_get(v_date_1670_, 1);
lean_inc(v_month_1671_);
lean_dec_ref(v_date_1670_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set_tag(v___x_1668_, 1);
lean_ctor_set(v___x_1668_, 0, v_month_1671_);
v___x_1673_ = v___x_1668_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_month_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
case 6:
{
lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1685_; 
v_isSharedCheck_1685_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1686_);
v___x_1678_ = v_x_1523_;
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
else
{
lean_dec(v_x_1523_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_date_1680_; lean_object* v_day_1681_; lean_object* v___x_1683_; 
v_date_1680_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1680_);
lean_dec_ref(v_date_1521_);
v_day_1681_ = lean_ctor_get(v_date_1680_, 2);
lean_inc(v_day_1681_);
lean_dec_ref(v_date_1680_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 1);
lean_ctor_set(v___x_1678_, 0, v_day_1681_);
v___x_1683_ = v___x_1678_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_day_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
case 12:
{
lean_object* v_date_1687_; uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
lean_dec_ref_known(v_x_1523_, 0);
v_date_1687_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1687_);
lean_dec_ref(v_date_1521_);
v___x_1688_ = l_Std_Time_PlainDate_weekday(v_date_1687_);
v___x_1689_ = lean_box(v___x_1688_);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
return v___x_1690_;
}
case 13:
{
lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1700_; 
v_isSharedCheck_1700_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; 
v_unused_1701_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1701_);
v___x_1692_ = v_x_1523_;
v_isShared_1693_ = v_isSharedCheck_1700_;
goto v_resetjp_1691_;
}
else
{
lean_dec(v_x_1523_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1700_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v_date_1694_; uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v_date_1694_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1694_);
lean_dec_ref(v_date_1521_);
v___x_1695_ = l_Std_Time_PlainDate_weekday(v_date_1694_);
v___x_1696_ = lean_box(v___x_1695_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 1);
lean_ctor_set(v___x_1692_, 0, v___x_1696_);
v___x_1698_ = v___x_1692_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
case 14:
{
lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1711_; 
v_isSharedCheck_1711_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; 
v_unused_1712_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1712_);
v___x_1703_ = v_x_1523_;
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v_x_1523_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_date_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v_date_1705_ = lean_ctor_get(v_date_1521_, 0);
lean_inc_ref(v_date_1705_);
lean_dec_ref(v_date_1521_);
v___x_1706_ = l_Std_Time_PlainDate_weekday(v_date_1705_);
v___x_1707_ = lean_box(v___x_1706_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set_tag(v___x_1703_, 1);
lean_ctor_set(v___x_1703_, 0, v___x_1707_);
v___x_1709_ = v___x_1703_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
case 15:
{
lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1720_; 
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; 
v_unused_1721_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1721_);
v___x_1714_ = v_x_1523_;
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
else
{
lean_dec(v_x_1523_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1720_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_1521_);
lean_dec_ref(v_date_1521_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set_tag(v___x_1714_, 1);
lean_ctor_set(v___x_1714_, 0, v___x_1716_);
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
}
case 22:
{
lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1730_; 
v_isSharedCheck_1730_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1731_);
v___x_1723_ = v_x_1523_;
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
else
{
lean_dec(v_x_1523_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_time_1725_; lean_object* v_hour_1726_; lean_object* v___x_1728_; 
v_time_1725_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1725_);
lean_dec_ref(v_date_1521_);
v_hour_1726_ = lean_ctor_get(v_time_1725_, 0);
lean_inc(v_hour_1726_);
lean_dec_ref(v_time_1725_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set_tag(v___x_1723_, 1);
lean_ctor_set(v___x_1723_, 0, v_hour_1726_);
v___x_1728_ = v___x_1723_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_hour_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
case 21:
{
lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1741_; 
v_isSharedCheck_1741_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1742_);
v___x_1733_ = v_x_1523_;
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
else
{
lean_dec(v_x_1523_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v_time_1735_; lean_object* v_hour_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v_time_1735_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1735_);
lean_dec_ref(v_date_1521_);
v_hour_1736_ = lean_ctor_get(v_time_1735_, 0);
lean_inc(v_hour_1736_);
lean_dec_ref(v_time_1735_);
v___x_1737_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1736_);
lean_dec(v_hour_1736_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set_tag(v___x_1733_, 1);
lean_ctor_set(v___x_1733_, 0, v___x_1737_);
v___x_1739_ = v___x_1733_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
case 23:
{
lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1751_; 
v_isSharedCheck_1751_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; 
v_unused_1752_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1752_);
v___x_1744_ = v_x_1523_;
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
else
{
lean_dec(v_x_1523_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v_time_1746_; lean_object* v_minute_1747_; lean_object* v___x_1749_; 
v_time_1746_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1746_);
lean_dec_ref(v_date_1521_);
v_minute_1747_ = lean_ctor_get(v_time_1746_, 1);
lean_inc(v_minute_1747_);
lean_dec_ref(v_time_1746_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set_tag(v___x_1744_, 1);
lean_ctor_set(v___x_1744_, 0, v_minute_1747_);
v___x_1749_ = v___x_1744_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_minute_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
case 27:
{
lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1761_; 
v_isSharedCheck_1761_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1762_);
v___x_1754_ = v_x_1523_;
v_isShared_1755_ = v_isSharedCheck_1761_;
goto v_resetjp_1753_;
}
else
{
lean_dec(v_x_1523_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1761_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_time_1756_; lean_object* v_nanosecond_1757_; lean_object* v___x_1759_; 
v_time_1756_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1756_);
lean_dec_ref(v_date_1521_);
v_nanosecond_1757_ = lean_ctor_get(v_time_1756_, 3);
lean_inc(v_nanosecond_1757_);
lean_dec_ref(v_time_1756_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set_tag(v___x_1754_, 1);
lean_ctor_set(v___x_1754_, 0, v_nanosecond_1757_);
v___x_1759_ = v___x_1754_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_nanosecond_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
case 24:
{
lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1771_; 
v_isSharedCheck_1771_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1771_ == 0)
{
lean_object* v_unused_1772_; 
v_unused_1772_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1772_);
v___x_1764_ = v_x_1523_;
v_isShared_1765_ = v_isSharedCheck_1771_;
goto v_resetjp_1763_;
}
else
{
lean_dec(v_x_1523_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1771_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v_time_1766_; lean_object* v_second_1767_; lean_object* v___x_1769_; 
v_time_1766_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1766_);
lean_dec_ref(v_date_1521_);
v_second_1767_ = lean_ctor_get(v_time_1766_, 2);
lean_inc(v_second_1767_);
lean_dec_ref(v_time_1766_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
lean_ctor_set(v___x_1764_, 0, v_second_1767_);
v___x_1769_ = v___x_1764_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_second_1767_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
case 16:
{
lean_object* v_time_1773_; lean_object* v_hour_1774_; uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec_ref_known(v_x_1523_, 0);
v_time_1773_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1773_);
lean_dec_ref(v_date_1521_);
v_hour_1774_ = lean_ctor_get(v_time_1773_, 0);
lean_inc(v_hour_1774_);
lean_dec_ref(v_time_1773_);
v___x_1775_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1774_);
lean_dec(v_hour_1774_);
v___x_1776_ = lean_box(v___x_1775_);
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
return v___x_1777_;
}
case 17:
{
lean_object* v_time_1778_; lean_object* v_hour_1779_; lean_object* v_minute_1780_; lean_object* v_second_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec_ref_known(v_x_1523_, 0);
v_time_1778_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1778_);
lean_dec_ref(v_date_1521_);
v_hour_1779_ = lean_ctor_get(v_time_1778_, 0);
lean_inc(v_hour_1779_);
v_minute_1780_ = lean_ctor_get(v_time_1778_, 1);
lean_inc(v_minute_1780_);
v_second_1781_ = lean_ctor_get(v_time_1778_, 2);
lean_inc(v_second_1781_);
lean_dec_ref(v_time_1778_);
v___x_1782_ = l_Std_Time_classifyDayPeriod(v_hour_1779_, v_minute_1780_, v_second_1781_);
lean_dec(v_second_1781_);
lean_dec(v_minute_1780_);
lean_dec(v_hour_1779_);
v___x_1783_ = lean_box(v___x_1782_);
v___x_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
case 18:
{
lean_object* v_time_1785_; lean_object* v_hour_1786_; lean_object* v_minute_1787_; lean_object* v_second_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec_ref_known(v_x_1523_, 0);
v_time_1785_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1785_);
lean_dec_ref(v_date_1521_);
v_hour_1786_ = lean_ctor_get(v_time_1785_, 0);
lean_inc(v_hour_1786_);
v_minute_1787_ = lean_ctor_get(v_time_1785_, 1);
lean_inc(v_minute_1787_);
v_second_1788_ = lean_ctor_get(v_time_1785_, 2);
lean_inc(v_second_1788_);
lean_dec_ref(v_time_1785_);
v___x_1789_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1786_, v_minute_1787_, v_second_1788_);
lean_dec(v_second_1788_);
lean_dec(v_minute_1787_);
lean_dec(v_hour_1786_);
v___x_1790_ = lean_box(v___x_1789_);
v___x_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
case 19:
{
lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1801_; 
v_isSharedCheck_1801_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1801_ == 0)
{
lean_object* v_unused_1802_; 
v_unused_1802_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1802_);
v___x_1793_ = v_x_1523_;
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
else
{
lean_dec(v_x_1523_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1801_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v_time_1795_; lean_object* v_hour_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
v_time_1795_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1795_);
lean_dec_ref(v_date_1521_);
v_hour_1796_ = lean_ctor_get(v_time_1795_, 0);
lean_inc(v_hour_1796_);
lean_dec_ref(v_time_1795_);
v___x_1797_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1796_);
lean_dec(v_hour_1796_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set_tag(v___x_1793_, 1);
lean_ctor_set(v___x_1793_, 0, v___x_1797_);
v___x_1799_ = v___x_1793_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
case 20:
{
lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1813_; 
v_isSharedCheck_1813_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1813_ == 0)
{
lean_object* v_unused_1814_; 
v_unused_1814_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1814_);
v___x_1804_ = v_x_1523_;
v_isShared_1805_ = v_isSharedCheck_1813_;
goto v_resetjp_1803_;
}
else
{
lean_dec(v_x_1523_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1813_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_time_1806_; lean_object* v_hour_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v_time_1806_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1806_);
lean_dec_ref(v_date_1521_);
v_hour_1807_ = lean_ctor_get(v_time_1806_, 0);
lean_inc(v_hour_1807_);
lean_dec_ref(v_time_1806_);
v___x_1808_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1809_ = lean_int_emod(v_hour_1807_, v___x_1808_);
lean_dec(v_hour_1807_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set_tag(v___x_1804_, 1);
lean_ctor_set(v___x_1804_, 0, v___x_1809_);
v___x_1811_ = v___x_1804_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
case 25:
{
lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1823_; 
v_isSharedCheck_1823_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1824_);
v___x_1816_ = v_x_1523_;
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v_x_1523_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_time_1818_; lean_object* v_nanosecond_1819_; lean_object* v___x_1821_; 
v_time_1818_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1818_);
lean_dec_ref(v_date_1521_);
v_nanosecond_1819_ = lean_ctor_get(v_time_1818_, 3);
lean_inc(v_nanosecond_1819_);
lean_dec_ref(v_time_1818_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set_tag(v___x_1816_, 1);
lean_ctor_set(v___x_1816_, 0, v_nanosecond_1819_);
v___x_1821_ = v___x_1816_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_nanosecond_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
case 26:
{
lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1833_; 
v_isSharedCheck_1833_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1833_ == 0)
{
lean_object* v_unused_1834_; 
v_unused_1834_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1834_);
v___x_1826_ = v_x_1523_;
v_isShared_1827_ = v_isSharedCheck_1833_;
goto v_resetjp_1825_;
}
else
{
lean_dec(v_x_1523_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1833_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_time_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v_time_1828_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1828_);
lean_dec_ref(v_date_1521_);
v___x_1829_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1828_);
lean_dec_ref(v_time_1828_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set_tag(v___x_1826_, 1);
lean_ctor_set(v___x_1826_, 0, v___x_1829_);
v___x_1831_ = v___x_1826_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
case 28:
{
lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1843_; 
v_isSharedCheck_1843_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v_x_1523_, 0);
lean_dec(v_unused_1844_);
v___x_1836_ = v_x_1523_;
v_isShared_1837_ = v_isSharedCheck_1843_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v_x_1523_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1843_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_time_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v_time_1838_ = lean_ctor_get(v_date_1521_, 1);
lean_inc_ref(v_time_1838_);
lean_dec_ref(v_date_1521_);
v___x_1839_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1838_);
lean_dec_ref(v_time_1838_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set_tag(v___x_1836_, 1);
lean_ctor_set(v___x_1836_, 0, v___x_1839_);
v___x_1841_ = v___x_1836_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
default: 
{
lean_object* v___x_1845_; 
lean_dec_ref(v_x_1523_);
lean_dec_ref(v_date_1521_);
v___x_1845_ = lean_box(0);
return v___x_1845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0___boxed(lean_object* v_date_1846_, lean_object* v_locale_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_Time_PlainDateTime_format___lam__0(v_date_1846_, v_locale_1847_, v_x_1848_);
lean_dec_ref(v_locale_1847_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format(lean_object* v_date_1850_, lean_object* v_format_1851_, lean_object* v_locale_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v_format_1854_; 
v___x_1853_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1854_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1851_, v___x_1853_);
if (lean_obj_tag(v_format_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec_ref(v_locale_1852_);
lean_dec_ref(v_date_1850_);
v_a_1855_ = lean_ctor_get(v_format_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v_format_1854_, 1);
v___x_1856_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1857_ = lean_string_append(v___x_1856_, v_a_1855_);
lean_dec(v_a_1855_);
return v___x_1857_;
}
else
{
lean_object* v_a_1858_; lean_object* v___f_1859_; lean_object* v_res_1860_; 
v_a_1858_ = lean_ctor_get(v_format_1854_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v_format_1854_, 1);
v___f_1859_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1859_, 0, v_date_1850_);
lean_closure_set(v___f_1859_, 1, v_locale_1852_);
v_res_1860_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1858_, v___f_1859_);
if (lean_obj_tag(v_res_1860_) == 0)
{
lean_object* v___x_1861_; 
v___x_1861_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1861_;
}
else
{
lean_object* v_val_1862_; 
v_val_1862_ = lean_ctor_get(v_res_1860_, 0);
lean_inc(v_val_1862_);
lean_dec_ref_known(v_res_1860_, 1);
return v_val_1862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromAscTimeString(lean_object* v_input_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1864_ = lean_obj_once(&l_Std_Time_DateTime_toHTTPDateString___closed__0, &l_Std_Time_DateTime_toHTTPDateString___closed__0_once, _init_l_Std_Time_DateTime_toHTTPDateString___closed__0);
v___x_1865_ = l_Std_Time_Formats_ascTime;
v___x_1866_ = l_Std_Time_GenericFormat_parse(v___x_1864_, v___x_1865_, v_input_1863_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1874_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1869_ = v___x_1866_;
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_a_1867_);
lean_dec(v___x_1866_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1874_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1872_; 
if (v_isShared_1870_ == 0)
{
v___x_1872_ = v___x_1869_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1884_; 
v_a_1875_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1877_ = v___x_1866_;
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1866_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1884_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_date_1879_; lean_object* v___x_1880_; lean_object* v___x_1882_; 
v_date_1879_ = lean_ctor_get(v_a_1875_, 0);
lean_inc_ref(v_date_1879_);
lean_dec(v_a_1875_);
v___x_1880_ = lean_thunk_get_own(v_date_1879_);
lean_dec_ref(v_date_1879_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1880_);
v___x_1882_ = v___x_1877_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1880_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0(lean_object* v_pdt_1885_, lean_object* v_x_1886_){
_start:
{
lean_inc_ref(v_pdt_1885_);
return v_pdt_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(lean_object* v_pdt_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Std_Time_PlainDateTime_toAscTimeString___lam__0(v_pdt_1887_, v_x_1888_);
lean_dec_ref(v_pdt_1887_);
return v_res_1889_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1893_ = lean_int_neg(v___x_1892_);
return v___x_1893_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1894_ = lean_unsigned_to_nat(1000000000u);
v___x_1895_ = lean_nat_to_int(v___x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString(lean_object* v_pdt_1896_){
_start:
{
lean_object* v___x_1897_; lean_object* v_offset_1898_; lean_object* v_name_1899_; lean_object* v_abbreviation_1900_; uint8_t v_isDST_1901_; uint8_t v___x_1902_; uint8_t v___x_1903_; lean_object* v_ltt_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_wt_1908_; lean_object* v_ltt_1909_; lean_object* v_tz_1910_; lean_object* v_offset_1911_; lean_object* v_second_1912_; lean_object* v_nano_1913_; lean_object* v___f_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v_nanos_1922_; lean_object* v___x_1923_; lean_object* v_nanos_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1897_ = l_Std_Time_TimeZone_UTC;
v_offset_1898_ = lean_ctor_get(v___x_1897_, 0);
v_name_1899_ = lean_ctor_get(v___x_1897_, 1);
v_abbreviation_1900_ = lean_ctor_get(v___x_1897_, 2);
v_isDST_1901_ = lean_ctor_get_uint8(v___x_1897_, sizeof(void*)*3);
v___x_1902_ = 0;
v___x_1903_ = 1;
lean_inc_ref(v_name_1899_);
lean_inc_ref(v_abbreviation_1900_);
lean_inc(v_offset_1898_);
v_ltt_1904_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_1904_, 0, v_offset_1898_);
lean_ctor_set(v_ltt_1904_, 1, v_abbreviation_1900_);
lean_ctor_set(v_ltt_1904_, 2, v_name_1899_);
lean_ctor_set_uint8(v_ltt_1904_, sizeof(void*)*3, v_isDST_1901_);
lean_ctor_set_uint8(v_ltt_1904_, sizeof(void*)*3 + 1, v___x_1902_);
lean_ctor_set_uint8(v_ltt_1904_, sizeof(void*)*3 + 2, v___x_1903_);
v___x_1905_ = ((lean_object*)(l_Std_Time_PlainDateTime_toAscTimeString___closed__0));
v___x_1906_ = lean_box(0);
v___x_1907_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1907_, 0, v_ltt_1904_);
lean_ctor_set(v___x_1907_, 1, v___x_1905_);
lean_ctor_set(v___x_1907_, 2, v___x_1906_);
lean_inc_ref(v_pdt_1896_);
v_wt_1908_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1896_);
lean_inc_ref(v___x_1907_);
v_ltt_1909_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1907_, v_wt_1908_);
v_tz_1910_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1909_);
lean_dec_ref(v_ltt_1909_);
v_offset_1911_ = lean_ctor_get(v_tz_1910_, 0);
v_second_1912_ = lean_ctor_get(v_wt_1908_, 0);
lean_inc(v_second_1912_);
v_nano_1913_ = lean_ctor_get(v_wt_1908_, 1);
lean_inc(v_nano_1913_);
lean_dec_ref(v_wt_1908_);
v___f_1914_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1914_, 0, v_pdt_1896_);
v___x_1915_ = lean_obj_once(&l_Std_Time_DateTime_toHTTPDateString___closed__0, &l_Std_Time_DateTime_toHTTPDateString___closed__0_once, _init_l_Std_Time_DateTime_toHTTPDateString___closed__0);
v___x_1916_ = l_Std_Time_Formats_ascTime;
v___x_1917_ = lean_mk_thunk(v___f_1914_);
v___x_1918_ = lean_int_neg(v_offset_1911_);
v___x_1919_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__1, &l_Std_Time_PlainDateTime_toAscTimeString___closed__1_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1);
v___x_1920_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__2, &l_Std_Time_PlainDateTime_toAscTimeString___closed__2_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2);
v___x_1921_ = lean_int_mul(v_second_1912_, v___x_1920_);
lean_dec(v_second_1912_);
v_nanos_1922_ = lean_int_add(v___x_1921_, v_nano_1913_);
lean_dec(v_nano_1913_);
lean_dec(v___x_1921_);
v___x_1923_ = lean_int_mul(v___x_1918_, v___x_1920_);
lean_dec(v___x_1918_);
v_nanos_1924_ = lean_int_add(v___x_1923_, v___x_1919_);
lean_dec(v___x_1923_);
v___x_1925_ = lean_int_add(v_nanos_1922_, v_nanos_1924_);
lean_dec(v_nanos_1924_);
lean_dec(v_nanos_1922_);
v___x_1926_ = l_Std_Time_Duration_ofNanoseconds(v___x_1925_);
lean_dec(v___x_1925_);
v___x_1927_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1917_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
lean_ctor_set(v___x_1927_, 2, v___x_1907_);
lean_ctor_set(v___x_1927_, 3, v_tz_1910_);
v___x_1928_ = l_Std_Time_GenericFormat_format(v___x_1915_, v___x_1916_, v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLongDateFormatString(lean_object* v_input_1929_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_obj_once(&l_Std_Time_DateTime_toHTTPDateString___closed__0, &l_Std_Time_DateTime_toHTTPDateString___closed__0_once, _init_l_Std_Time_DateTime_toHTTPDateString___closed__0);
v___x_1931_ = l_Std_Time_Formats_longDateFormat;
v___x_1932_ = l_Std_Time_GenericFormat_parse(v___x_1930_, v___x_1931_, v_input_1929_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1950_; 
v_a_1941_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1943_ = v___x_1932_;
v_isShared_1944_ = v_isSharedCheck_1950_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1932_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1950_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v_date_1945_; lean_object* v___x_1946_; lean_object* v___x_1948_; 
v_date_1945_ = lean_ctor_get(v_a_1941_, 0);
lean_inc_ref(v_date_1945_);
lean_dec(v_a_1941_);
v___x_1946_ = lean_thunk_get_own(v_date_1945_);
lean_dec_ref(v_date_1945_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1946_);
v___x_1948_ = v___x_1943_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLongDateFormatString(lean_object* v_pdt_1951_){
_start:
{
lean_object* v___x_1952_; lean_object* v_offset_1953_; lean_object* v_name_1954_; lean_object* v_abbreviation_1955_; uint8_t v_isDST_1956_; uint8_t v___x_1957_; uint8_t v___x_1958_; lean_object* v_ltt_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_wt_1963_; lean_object* v_ltt_1964_; lean_object* v_tz_1965_; lean_object* v_offset_1966_; lean_object* v_second_1967_; lean_object* v_nano_1968_; lean_object* v___f_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_nanos_1977_; lean_object* v___x_1978_; lean_object* v_nanos_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1952_ = l_Std_Time_TimeZone_UTC;
v_offset_1953_ = lean_ctor_get(v___x_1952_, 0);
v_name_1954_ = lean_ctor_get(v___x_1952_, 1);
v_abbreviation_1955_ = lean_ctor_get(v___x_1952_, 2);
v_isDST_1956_ = lean_ctor_get_uint8(v___x_1952_, sizeof(void*)*3);
v___x_1957_ = 0;
v___x_1958_ = 1;
lean_inc_ref(v_name_1954_);
lean_inc_ref(v_abbreviation_1955_);
lean_inc(v_offset_1953_);
v_ltt_1959_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_1959_, 0, v_offset_1953_);
lean_ctor_set(v_ltt_1959_, 1, v_abbreviation_1955_);
lean_ctor_set(v_ltt_1959_, 2, v_name_1954_);
lean_ctor_set_uint8(v_ltt_1959_, sizeof(void*)*3, v_isDST_1956_);
lean_ctor_set_uint8(v_ltt_1959_, sizeof(void*)*3 + 1, v___x_1957_);
lean_ctor_set_uint8(v_ltt_1959_, sizeof(void*)*3 + 2, v___x_1958_);
v___x_1960_ = ((lean_object*)(l_Std_Time_PlainDateTime_toAscTimeString___closed__0));
v___x_1961_ = lean_box(0);
v___x_1962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1962_, 0, v_ltt_1959_);
lean_ctor_set(v___x_1962_, 1, v___x_1960_);
lean_ctor_set(v___x_1962_, 2, v___x_1961_);
lean_inc_ref(v_pdt_1951_);
v_wt_1963_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1951_);
lean_inc_ref(v___x_1962_);
v_ltt_1964_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1962_, v_wt_1963_);
v_tz_1965_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1964_);
lean_dec_ref(v_ltt_1964_);
v_offset_1966_ = lean_ctor_get(v_tz_1965_, 0);
v_second_1967_ = lean_ctor_get(v_wt_1963_, 0);
lean_inc(v_second_1967_);
v_nano_1968_ = lean_ctor_get(v_wt_1963_, 1);
lean_inc(v_nano_1968_);
lean_dec_ref(v_wt_1963_);
v___f_1969_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1969_, 0, v_pdt_1951_);
v___x_1970_ = lean_obj_once(&l_Std_Time_DateTime_toHTTPDateString___closed__0, &l_Std_Time_DateTime_toHTTPDateString___closed__0_once, _init_l_Std_Time_DateTime_toHTTPDateString___closed__0);
v___x_1971_ = l_Std_Time_Formats_longDateFormat;
v___x_1972_ = lean_mk_thunk(v___f_1969_);
v___x_1973_ = lean_int_neg(v_offset_1966_);
v___x_1974_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__1, &l_Std_Time_PlainDateTime_toAscTimeString___closed__1_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1);
v___x_1975_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__2, &l_Std_Time_PlainDateTime_toAscTimeString___closed__2_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2);
v___x_1976_ = lean_int_mul(v_second_1967_, v___x_1975_);
lean_dec(v_second_1967_);
v_nanos_1977_ = lean_int_add(v___x_1976_, v_nano_1968_);
lean_dec(v_nano_1968_);
lean_dec(v___x_1976_);
v___x_1978_ = lean_int_mul(v___x_1973_, v___x_1975_);
lean_dec(v___x_1973_);
v_nanos_1979_ = lean_int_add(v___x_1978_, v___x_1974_);
lean_dec(v___x_1978_);
v___x_1980_ = lean_int_add(v_nanos_1977_, v_nanos_1979_);
lean_dec(v_nanos_1979_);
lean_dec(v_nanos_1977_);
v___x_1981_ = l_Std_Time_Duration_ofNanoseconds(v___x_1980_);
lean_dec(v___x_1980_);
v___x_1982_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1972_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
lean_ctor_set(v___x_1982_, 2, v___x_1962_);
lean_ctor_set(v___x_1982_, 3, v_tz_1965_);
v___x_1983_ = l_Std_Time_GenericFormat_format(v___x_1970_, v___x_1971_, v___x_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromDateTimeString(lean_object* v_input_1984_){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = lean_obj_once(&l_Std_Time_DateTime_toHTTPDateString___closed__0, &l_Std_Time_DateTime_toHTTPDateString___closed__0_once, _init_l_Std_Time_DateTime_toHTTPDateString___closed__0);
v___x_1986_ = l_Std_Time_Formats_dateTime24Hour;
v___x_1987_ = l_Std_Time_GenericFormat_parse(v___x_1985_, v___x_1986_, v_input_1984_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1987_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2005_; 
v_a_1996_ = lean_ctor_get(v___x_1987_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1998_ = v___x_1987_;
v_isShared_1999_ = v_isSharedCheck_2005_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1987_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2005_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_date_2000_; lean_object* v___x_2001_; lean_object* v___x_2003_; 
v_date_2000_ = lean_ctor_get(v_a_1996_, 0);
lean_inc_ref(v_date_2000_);
lean_dec(v_a_1996_);
v___x_2001_ = lean_thunk_get_own(v_date_2000_);
lean_dec_ref(v_date_2000_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2001_);
v___x_2003_ = v___x_1998_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toDateTimeString(lean_object* v_pdt_2006_){
_start:
{
lean_object* v_date_2007_; lean_object* v_time_2008_; lean_object* v_year_2009_; lean_object* v_month_2010_; lean_object* v_day_2011_; lean_object* v_hour_2012_; lean_object* v_minute_2013_; lean_object* v_second_2014_; lean_object* v_nanosecond_2015_; lean_object* v___x_2016_; lean_object* v___x_27__overap_2017_; lean_object* v___x_2018_; 
v_date_2007_ = lean_ctor_get(v_pdt_2006_, 0);
lean_inc_ref(v_date_2007_);
v_time_2008_ = lean_ctor_get(v_pdt_2006_, 1);
lean_inc_ref(v_time_2008_);
lean_dec_ref(v_pdt_2006_);
v_year_2009_ = lean_ctor_get(v_date_2007_, 0);
lean_inc(v_year_2009_);
v_month_2010_ = lean_ctor_get(v_date_2007_, 1);
lean_inc(v_month_2010_);
v_day_2011_ = lean_ctor_get(v_date_2007_, 2);
lean_inc(v_day_2011_);
lean_dec_ref(v_date_2007_);
v_hour_2012_ = lean_ctor_get(v_time_2008_, 0);
lean_inc(v_hour_2012_);
v_minute_2013_ = lean_ctor_get(v_time_2008_, 1);
lean_inc(v_minute_2013_);
v_second_2014_ = lean_ctor_get(v_time_2008_, 2);
lean_inc(v_second_2014_);
v_nanosecond_2015_ = lean_ctor_get(v_time_2008_, 3);
lean_inc(v_nanosecond_2015_);
lean_dec_ref(v_time_2008_);
v___x_2016_ = l_Std_Time_Formats_dateTime24Hour;
v___x_27__overap_2017_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_2016_);
v___x_2018_ = lean_apply_7(v___x_27__overap_2017_, v_year_2009_, v_month_2010_, v_day_2011_, v_hour_2012_, v_minute_2013_, v_second_2014_, v_nanosecond_2015_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLeanDateTimeString(lean_object* v_input_2019_){
_start:
{
lean_object* v___y_2021_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_obj_once(&l_Std_Time_DateTime_toHTTPDateString___closed__0, &l_Std_Time_DateTime_toHTTPDateString___closed__0_once, _init_l_Std_Time_DateTime_toHTTPDateString___closed__0);
v___x_2041_ = l_Std_Time_Formats_leanDateTime24Hour;
lean_inc_ref(v_input_2019_);
v___x_2042_ = l_Std_Time_GenericFormat_parse(v___x_2040_, v___x_2041_, v_input_2019_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec_ref_known(v___x_2042_, 1);
v___x_2043_ = l_Std_Time_Formats_leanDateTime24HourNoNanos;
v___x_2044_ = l_Std_Time_GenericFormat_parse(v___x_2040_, v___x_2043_, v_input_2019_);
v___y_2021_ = v___x_2044_;
goto v___jp_2020_;
}
else
{
lean_dec_ref(v_input_2019_);
v___y_2021_ = v___x_2042_;
goto v___jp_2020_;
}
v___jp_2020_:
{
if (lean_obj_tag(v___y_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v_a_2022_ = lean_ctor_get(v___y_2021_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___y_2021_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___y_2021_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___y_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2039_; 
v_a_2030_ = lean_ctor_get(v___y_2021_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___y_2021_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2032_ = v___y_2021_;
v_isShared_2033_ = v_isSharedCheck_2039_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___y_2021_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2039_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v_date_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v_date_2034_ = lean_ctor_get(v_a_2030_, 0);
lean_inc_ref(v_date_2034_);
lean_dec(v_a_2030_);
v___x_2035_ = lean_thunk_get_own(v_date_2034_);
lean_dec_ref(v_date_2034_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2035_);
v___x_2037_ = v___x_2032_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLeanDateTimeString(lean_object* v_pdt_2045_){
_start:
{
lean_object* v_date_2046_; lean_object* v_time_2047_; lean_object* v_year_2048_; lean_object* v_month_2049_; lean_object* v_day_2050_; lean_object* v_hour_2051_; lean_object* v_minute_2052_; lean_object* v_second_2053_; lean_object* v_nanosecond_2054_; lean_object* v___x_2055_; lean_object* v___x_27__overap_2056_; lean_object* v___x_2057_; 
v_date_2046_ = lean_ctor_get(v_pdt_2045_, 0);
lean_inc_ref(v_date_2046_);
v_time_2047_ = lean_ctor_get(v_pdt_2045_, 1);
lean_inc_ref(v_time_2047_);
lean_dec_ref(v_pdt_2045_);
v_year_2048_ = lean_ctor_get(v_date_2046_, 0);
lean_inc(v_year_2048_);
v_month_2049_ = lean_ctor_get(v_date_2046_, 1);
lean_inc(v_month_2049_);
v_day_2050_ = lean_ctor_get(v_date_2046_, 2);
lean_inc(v_day_2050_);
lean_dec_ref(v_date_2046_);
v_hour_2051_ = lean_ctor_get(v_time_2047_, 0);
lean_inc(v_hour_2051_);
v_minute_2052_ = lean_ctor_get(v_time_2047_, 1);
lean_inc(v_minute_2052_);
v_second_2053_ = lean_ctor_get(v_time_2047_, 2);
lean_inc(v_second_2053_);
v_nanosecond_2054_ = lean_ctor_get(v_time_2047_, 3);
lean_inc(v_nanosecond_2054_);
lean_dec_ref(v_time_2047_);
v___x_2055_ = l_Std_Time_Formats_leanDateTime24Hour;
v___x_27__overap_2056_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_2055_);
v___x_2057_ = lean_apply_7(v___x_27__overap_2056_, v_year_2048_, v_month_2049_, v_day_2050_, v_hour_2051_, v_minute_2052_, v_second_2053_, v_nanosecond_2054_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_parse(lean_object* v_date_2058_){
_start:
{
lean_object* v___x_2059_; 
lean_inc_ref(v_date_2058_);
v___x_2059_ = l_Std_Time_PlainDateTime_fromAscTimeString(v_date_2058_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v___x_2060_; 
lean_dec_ref_known(v___x_2059_, 1);
lean_inc_ref(v_date_2058_);
v___x_2060_ = l_Std_Time_PlainDateTime_fromLongDateFormatString(v_date_2058_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v___x_2061_; 
lean_dec_ref_known(v___x_2060_, 1);
lean_inc_ref(v_date_2058_);
v___x_2061_ = l_Std_Time_PlainDateTime_fromDateTimeString(v_date_2058_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v___x_2062_; 
lean_dec_ref_known(v___x_2061_, 1);
v___x_2062_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v_date_2058_);
return v___x_2062_;
}
else
{
lean_dec_ref(v_date_2058_);
return v___x_2061_;
}
}
else
{
lean_dec_ref(v_date_2058_);
return v___x_2060_;
}
}
else
{
lean_dec_ref(v_date_2058_);
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0(lean_object* v_data_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2070_ = ((lean_object*)(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1));
v___x_2071_ = l_Std_Time_PlainDateTime_toLeanDateTimeString(v_data_2068_);
v___x_2072_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2070_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_2075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = l_Repr_addAppParen(v___x_2075_, v___y_2069_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0___boxed(lean_object* v_data_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Std_Time_PlainDateTime_instRepr___lam__0(v_data_2077_, v___y_2078_);
lean_dec(v___y_2078_);
return v_res_2079_;
}
}
lean_object* runtime_initialize_Std_Time_Notation_Spec(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Format_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Format_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Format(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_Formats_iso8601 = _init_l_Std_Time_Formats_iso8601();
lean_mark_persistent(l_Std_Time_Formats_iso8601);
l_Std_Time_Formats_americanDate = _init_l_Std_Time_Formats_americanDate();
lean_mark_persistent(l_Std_Time_Formats_americanDate);
l_Std_Time_Formats_europeanDate = _init_l_Std_Time_Formats_europeanDate();
lean_mark_persistent(l_Std_Time_Formats_europeanDate);
l_Std_Time_Formats_time12Hour = _init_l_Std_Time_Formats_time12Hour();
lean_mark_persistent(l_Std_Time_Formats_time12Hour);
l_Std_Time_Formats_time24Hour = _init_l_Std_Time_Formats_time24Hour();
lean_mark_persistent(l_Std_Time_Formats_time24Hour);
l_Std_Time_Formats_dateTime24Hour = _init_l_Std_Time_Formats_dateTime24Hour();
lean_mark_persistent(l_Std_Time_Formats_dateTime24Hour);
l_Std_Time_Formats_dateTimeWithZone = _init_l_Std_Time_Formats_dateTimeWithZone();
lean_mark_persistent(l_Std_Time_Formats_dateTimeWithZone);
l_Std_Time_Formats_leanTime24Hour = _init_l_Std_Time_Formats_leanTime24Hour();
lean_mark_persistent(l_Std_Time_Formats_leanTime24Hour);
l_Std_Time_Formats_leanTime24HourNoNanos = _init_l_Std_Time_Formats_leanTime24HourNoNanos();
lean_mark_persistent(l_Std_Time_Formats_leanTime24HourNoNanos);
l_Std_Time_Formats_leanDateTime24Hour = _init_l_Std_Time_Formats_leanDateTime24Hour();
lean_mark_persistent(l_Std_Time_Formats_leanDateTime24Hour);
l_Std_Time_Formats_leanDateTime24HourNoNanos = _init_l_Std_Time_Formats_leanDateTime24HourNoNanos();
lean_mark_persistent(l_Std_Time_Formats_leanDateTime24HourNoNanos);
l_Std_Time_Formats_leanDateTimeWithZone = _init_l_Std_Time_Formats_leanDateTimeWithZone();
lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithZone);
l_Std_Time_Formats_leanDateTimeWithZoneNoNanos = _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos();
lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos);
l_Std_Time_Formats_leanDateTimeWithIdentifier = _init_l_Std_Time_Formats_leanDateTimeWithIdentifier();
lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithIdentifier);
l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos = _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos();
lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos);
l_Std_Time_Formats_leanDate = _init_l_Std_Time_Formats_leanDate();
lean_mark_persistent(l_Std_Time_Formats_leanDate);
l_Std_Time_Formats_sqlDate = _init_l_Std_Time_Formats_sqlDate();
lean_mark_persistent(l_Std_Time_Formats_sqlDate);
l_Std_Time_Formats_longDateFormat = _init_l_Std_Time_Formats_longDateFormat();
lean_mark_persistent(l_Std_Time_Formats_longDateFormat);
l_Std_Time_Formats_ascTime = _init_l_Std_Time_Formats_ascTime();
lean_mark_persistent(l_Std_Time_Formats_ascTime);
l_Std_Time_Formats_rfc822 = _init_l_Std_Time_Formats_rfc822();
lean_mark_persistent(l_Std_Time_Formats_rfc822);
l_Std_Time_Formats_rfc850 = _init_l_Std_Time_Formats_rfc850();
lean_mark_persistent(l_Std_Time_Formats_rfc850);
l_Std_Time_Formats_httpDate = _init_l_Std_Time_Formats_httpDate();
lean_mark_persistent(l_Std_Time_Formats_httpDate);
l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850 = _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850();
lean_mark_persistent(l___private_Std_Time_Format_0__Std_Time_Formats_httpDateRFC850);
l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime = _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime();
lean_mark_persistent(l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTime);
l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded = _init_l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded();
lean_mark_persistent(l___private_Std_Time_Format_0__Std_Time_Formats_httpDateAscTimePadded);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Format(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Notation_Spec(uint8_t builtin);
lean_object* initialize_Std_Time_Format_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Format_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Format(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Format_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Format(builtin);
}
#ifdef __cplusplus
}
#endif

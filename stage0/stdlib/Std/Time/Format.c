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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Time_GenericFormat_format(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_GenericFormat_formatGeneric___redArg(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
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
static lean_once_cell_t l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0;
static lean_once_cell_t l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1;
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
static lean_once_cell_t l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_fromAscTimeString___closed__0;
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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0(uint8_t v___x_694_, lean_object* v_id_695_, lean_object* v_off_696_){
_start:
{
uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = 1;
lean_inc(v_off_696_);
v___x_698_ = l_Std_Time_TimeZone_Offset_toIsoString(v_off_696_, v___x_697_);
v___x_699_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_699_, 0, v_off_696_);
lean_ctor_set(v___x_699_, 1, v_id_695_);
lean_ctor_set(v___x_699_, 2, v___x_698_);
lean_ctor_set_uint8(v___x_699_, sizeof(void*)*3, v___x_694_);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed(lean_object* v___x_701_, lean_object* v_id_702_, lean_object* v_off_703_){
_start:
{
uint8_t v___x_31__boxed_704_; lean_object* v_res_705_; 
v___x_31__boxed_704_ = lean_unbox(v___x_701_);
v_res_705_ = l_Std_Time_TimeZone_fromTimeZone___lam__0(v___x_31__boxed_704_, v_id_702_, v_off_703_);
return v_res_705_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_fromTimeZone___closed__5(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v_spec_721_; 
v___x_719_ = ((lean_object*)(l_Std_Time_TimeZone_fromTimeZone___closed__4));
v___x_720_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_spec_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_spec_721_, 0, v___x_720_);
lean_ctor_set(v_spec_721_, 1, v___x_719_);
return v_spec_721_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone(lean_object* v_input_722_){
_start:
{
lean_object* v___f_723_; lean_object* v_spec_724_; lean_object* v___x_725_; 
v___f_723_ = ((lean_object*)(l_Std_Time_TimeZone_fromTimeZone___closed__0));
v_spec_724_ = lean_obj_once(&l_Std_Time_TimeZone_fromTimeZone___closed__5, &l_Std_Time_TimeZone_fromTimeZone___closed__5_once, _init_l_Std_Time_TimeZone_fromTimeZone___closed__5);
v___x_725_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_724_, v___f_723_, v_input_722_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset___lam__0(lean_object* v_val_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_val_726_);
return v___x_727_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_spec_738_; 
v___x_736_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_fromOffset___closed__3));
v___x_737_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_spec_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_spec_738_, 0, v___x_737_);
lean_ctor_set(v_spec_738_, 1, v___x_736_);
return v_spec_738_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset(lean_object* v_input_739_){
_start:
{
lean_object* v___f_740_; lean_object* v_spec_741_; lean_object* v___x_742_; 
v___f_740_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_fromOffset___closed__0));
v_spec_741_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_fromOffset___closed__4, &l_Std_Time_TimeZone_Offset_fromOffset___closed__4_once, _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4);
v___x_742_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_741_, v___f_740_, v_input_739_);
return v___x_742_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(4u);
v___x_744_ = lean_nat_to_int(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__1(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_nat_to_int(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__2(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(400u);
v___x_748_ = lean_nat_to_int(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__3(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(100u);
v___x_750_ = lean_nat_to_int(v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0(lean_object* v_date_751_, lean_object* v_locale_752_, lean_object* v_x_753_){
_start:
{
uint8_t v___y_755_; 
switch(lean_obj_tag(v_x_753_))
{
case 0:
{
lean_object* v_year_760_; uint8_t v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec_ref_known(v_x_753_, 0);
v_year_760_ = lean_ctor_get(v_date_751_, 0);
lean_inc(v_year_760_);
lean_dec_ref(v_date_751_);
v___x_761_ = l_Std_Time_Year_Offset_era(v_year_760_);
lean_dec(v_year_760_);
v___x_762_ = lean_box(v___x_761_);
v___x_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
case 2:
{
lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_771_; 
v_isSharedCheck_771_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_772_);
v___x_765_ = v_x_753_;
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
else
{
lean_dec(v_x_753_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_771_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_year_767_; lean_object* v___x_769_; 
v_year_767_ = lean_ctor_get(v_date_751_, 0);
lean_inc(v_year_767_);
lean_dec_ref(v_date_751_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 1);
lean_ctor_set(v___x_765_, 0, v_year_767_);
v___x_769_ = v___x_765_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_year_767_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
case 1:
{
lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_780_; 
v_isSharedCheck_780_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_781_);
v___x_774_ = v_x_753_;
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
else
{
lean_dec(v_x_753_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_year_776_; lean_object* v___x_778_; 
v_year_776_ = lean_ctor_get(v_date_751_, 0);
lean_inc(v_year_776_);
lean_dec_ref(v_date_751_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_year_776_);
v___x_778_ = v___x_774_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_year_776_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
case 9:
{
lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_791_; 
v_isSharedCheck_791_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_792_);
v___x_783_ = v_x_753_;
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
else
{
lean_dec(v_x_753_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
uint8_t v_firstDayOfWeek_785_; lean_object* v_minimalDaysInFirstWeek_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v_firstDayOfWeek_785_ = lean_ctor_get_uint8(v_locale_752_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_786_ = lean_ctor_get(v_locale_752_, 0);
v___x_787_ = l_Std_Time_PlainDate_weekYear(v_date_751_, v_firstDayOfWeek_785_, v_minimalDaysInFirstWeek_786_);
if (v_isShared_784_ == 0)
{
lean_ctor_set_tag(v___x_783_, 1);
lean_ctor_set(v___x_783_, 0, v___x_787_);
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
case 3:
{
lean_object* v_year_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_801_; 
lean_dec_ref_known(v_x_753_, 1);
v_year_793_ = lean_ctor_get(v_date_751_, 0);
v___x_794_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_795_ = lean_int_mod(v_year_793_, v___x_794_);
v___x_796_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_801_ = lean_int_dec_eq(v___x_795_, v___x_796_);
lean_dec(v___x_795_);
if (v___x_801_ == 0)
{
v___y_755_ = v___x_801_;
goto v___jp_754_;
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_802_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_803_ = lean_int_mod(v_year_793_, v___x_802_);
v___x_804_ = lean_int_dec_eq(v___x_803_, v___x_796_);
lean_dec(v___x_803_);
if (v___x_804_ == 0)
{
if (v___x_801_ == 0)
{
goto v___jp_797_;
}
else
{
v___y_755_ = v___x_801_;
goto v___jp_754_;
}
}
else
{
goto v___jp_797_;
}
}
v___jp_797_:
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_799_ = lean_int_mod(v_year_793_, v___x_798_);
v___x_800_ = lean_int_dec_eq(v___x_799_, v___x_796_);
lean_dec(v___x_799_);
v___y_755_ = v___x_800_;
goto v___jp_754_;
}
}
case 7:
{
lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_812_; 
v_isSharedCheck_812_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_813_);
v___x_806_ = v_x_753_;
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
else
{
lean_dec(v_x_753_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_812_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_810_; 
v___x_808_ = l_Std_Time_PlainDate_quarter(v_date_751_);
lean_dec_ref(v_date_751_);
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 1);
lean_ctor_set(v___x_806_, 0, v___x_808_);
v___x_810_ = v___x_806_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
case 8:
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_821_; 
v_isSharedCheck_821_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_822_);
v___x_815_ = v_x_753_;
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
else
{
lean_dec(v_x_753_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_821_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = l_Std_Time_PlainDate_quarter(v_date_751_);
lean_dec_ref(v_date_751_);
if (v_isShared_816_ == 0)
{
lean_ctor_set_tag(v___x_815_, 1);
lean_ctor_set(v___x_815_, 0, v___x_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
case 10:
{
lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_832_; 
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_833_);
v___x_824_ = v_x_753_;
v_isShared_825_ = v_isSharedCheck_832_;
goto v_resetjp_823_;
}
else
{
lean_dec(v_x_753_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_832_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
uint8_t v_firstDayOfWeek_826_; lean_object* v_minimalDaysInFirstWeek_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v_firstDayOfWeek_826_ = lean_ctor_get_uint8(v_locale_752_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_827_ = lean_ctor_get(v_locale_752_, 0);
v___x_828_ = l_Std_Time_PlainDate_weekOfYear(v_date_751_, v_firstDayOfWeek_826_, v_minimalDaysInFirstWeek_827_);
if (v_isShared_825_ == 0)
{
lean_ctor_set_tag(v___x_824_, 1);
lean_ctor_set(v___x_824_, 0, v___x_828_);
v___x_830_ = v___x_824_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
case 11:
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_842_; 
v_isSharedCheck_842_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_843_);
v___x_835_ = v_x_753_;
v_isShared_836_ = v_isSharedCheck_842_;
goto v_resetjp_834_;
}
else
{
lean_dec(v_x_753_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_842_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
uint8_t v_firstDayOfWeek_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v_firstDayOfWeek_837_ = lean_ctor_get_uint8(v_locale_752_, sizeof(void*)*2);
v___x_838_ = l_Std_Time_PlainDate_weekOfMonth(v_date_751_, v_firstDayOfWeek_837_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 1);
lean_ctor_set(v___x_835_, 0, v___x_838_);
v___x_840_ = v___x_835_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
case 4:
{
lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_851_; 
v_isSharedCheck_851_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_851_ == 0)
{
lean_object* v_unused_852_; 
v_unused_852_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_852_);
v___x_845_ = v_x_753_;
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
else
{
lean_dec(v_x_753_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_851_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_month_847_; lean_object* v___x_849_; 
v_month_847_ = lean_ctor_get(v_date_751_, 1);
lean_inc(v_month_847_);
lean_dec_ref(v_date_751_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 1);
lean_ctor_set(v___x_845_, 0, v_month_847_);
v___x_849_ = v___x_845_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_month_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
case 5:
{
lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_860_; 
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_861_);
v___x_854_ = v_x_753_;
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
else
{
lean_dec(v_x_753_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_860_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_month_856_; lean_object* v___x_858_; 
v_month_856_ = lean_ctor_get(v_date_751_, 1);
lean_inc(v_month_856_);
lean_dec_ref(v_date_751_);
if (v_isShared_855_ == 0)
{
lean_ctor_set_tag(v___x_854_, 1);
lean_ctor_set(v___x_854_, 0, v_month_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_month_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
case 6:
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_isSharedCheck_869_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_870_);
v___x_863_ = v_x_753_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_dec(v_x_753_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_day_865_; lean_object* v___x_867_; 
v_day_865_ = lean_ctor_get(v_date_751_, 2);
lean_inc(v_day_865_);
lean_dec_ref(v_date_751_);
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 1);
lean_ctor_set(v___x_863_, 0, v_day_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_day_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
case 12:
{
uint8_t v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec_ref_known(v_x_753_, 0);
v___x_871_ = l_Std_Time_PlainDate_weekday(v_date_751_);
v___x_872_ = lean_box(v___x_871_);
v___x_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
return v___x_873_;
}
case 13:
{
lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_882_; 
v_isSharedCheck_882_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_883_);
v___x_875_ = v_x_753_;
v_isShared_876_ = v_isSharedCheck_882_;
goto v_resetjp_874_;
}
else
{
lean_dec(v_x_753_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_882_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
uint8_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_877_ = l_Std_Time_PlainDate_weekday(v_date_751_);
v___x_878_ = lean_box(v___x_877_);
if (v_isShared_876_ == 0)
{
lean_ctor_set_tag(v___x_875_, 1);
lean_ctor_set(v___x_875_, 0, v___x_878_);
v___x_880_ = v___x_875_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
case 14:
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_892_; 
v_isSharedCheck_892_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_893_);
v___x_885_ = v_x_753_;
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
else
{
lean_dec(v_x_753_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_892_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_887_ = l_Std_Time_PlainDate_weekday(v_date_751_);
v___x_888_ = lean_box(v___x_887_);
if (v_isShared_886_ == 0)
{
lean_ctor_set_tag(v___x_885_, 1);
lean_ctor_set(v___x_885_, 0, v___x_888_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
case 15:
{
lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_901_; 
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_902_);
v___x_895_ = v_x_753_;
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
else
{
lean_dec(v_x_753_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_751_);
lean_dec_ref(v_date_751_);
if (v_isShared_896_ == 0)
{
lean_ctor_set_tag(v___x_895_, 1);
lean_ctor_set(v___x_895_, 0, v___x_897_);
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
default: 
{
lean_object* v___x_903_; 
lean_dec_ref(v_x_753_);
lean_dec_ref(v_date_751_);
v___x_903_ = lean_box(0);
return v___x_903_;
}
}
v___jp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_756_ = l_Std_Time_PlainDate_dayOfYear(v_date_751_);
lean_dec_ref(v_date_751_);
v___x_757_ = lean_box(v___y_755_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
lean_ctor_set(v___x_758_, 1, v___x_756_);
v___x_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0___boxed(lean_object* v_date_904_, lean_object* v_locale_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_Time_PlainDate_format___lam__0(v_date_904_, v_locale_905_, v_x_906_);
lean_dec_ref(v_locale_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format(lean_object* v_date_910_, lean_object* v_format_911_, lean_object* v_locale_912_){
_start:
{
lean_object* v___x_913_; lean_object* v_format_914_; 
v___x_913_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_914_ = l_Std_Time_GenericFormat_spec___redArg(v_format_911_, v___x_913_);
if (lean_obj_tag(v_format_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec_ref(v_locale_912_);
lean_dec_ref(v_date_910_);
v_a_915_ = lean_ctor_get(v_format_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v_format_914_, 1);
v___x_916_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_917_ = lean_string_append(v___x_916_, v_a_915_);
lean_dec(v_a_915_);
return v___x_917_;
}
else
{
lean_object* v_a_918_; lean_object* v___f_919_; lean_object* v_res_920_; 
v_a_918_ = lean_ctor_get(v_format_914_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v_format_914_, 1);
v___f_919_ = lean_alloc_closure((void*)(l_Std_Time_PlainDate_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_919_, 0, v_date_910_);
lean_closure_set(v___f_919_, 1, v_locale_912_);
v_res_920_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_918_, v___f_919_);
if (lean_obj_tag(v_res_920_) == 0)
{
lean_object* v___x_921_; 
v___x_921_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_921_;
}
else
{
lean_object* v_val_922_; 
v_val_922_ = lean_ctor_get(v_res_920_, 0);
lean_inc(v_val_922_);
lean_dec_ref_known(v_res_920_, 1);
return v_val_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString___lam__0(lean_object* v_m_923_, lean_object* v_d_924_, lean_object* v_y_925_){
_start:
{
uint8_t v___y_927_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; uint8_t v___x_940_; 
v___x_933_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_934_ = lean_int_mod(v_y_925_, v___x_933_);
v___x_935_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_940_ = lean_int_dec_eq(v___x_934_, v___x_935_);
lean_dec(v___x_934_);
if (v___x_940_ == 0)
{
v___y_927_ = v___x_940_;
goto v___jp_926_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_941_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_942_ = lean_int_mod(v_y_925_, v___x_941_);
v___x_943_ = lean_int_dec_eq(v___x_942_, v___x_935_);
lean_dec(v___x_942_);
if (v___x_943_ == 0)
{
if (v___x_940_ == 0)
{
goto v___jp_936_;
}
else
{
v___y_927_ = v___x_940_;
goto v___jp_926_;
}
}
else
{
goto v___jp_936_;
}
}
v___jp_926_:
{
lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_928_ = l_Std_Time_Month_Ordinal_days(v___y_927_, v_m_923_);
v___x_929_ = lean_int_dec_le(v_d_924_, v___x_928_);
lean_dec(v___x_928_);
if (v___x_929_ == 0)
{
lean_object* v___x_930_; 
lean_dec(v_y_925_);
lean_dec(v_d_924_);
lean_dec(v_m_923_);
v___x_930_ = lean_box(0);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_931_, 0, v_y_925_);
lean_ctor_set(v___x_931_, 1, v_m_923_);
lean_ctor_set(v___x_931_, 2, v_d_924_);
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
v___jp_936_:
{
lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v___x_937_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_938_ = lean_int_mod(v_y_925_, v___x_937_);
v___x_939_ = lean_int_dec_eq(v___x_938_, v___x_935_);
lean_dec(v___x_938_);
v___y_927_ = v___x_939_;
goto v___jp_926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString(lean_object* v_input_945_){
_start:
{
lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___f_946_ = ((lean_object*)(l_Std_Time_PlainDate_fromAmericanDateString___closed__0));
v___x_947_ = l_Std_Time_Formats_americanDate;
v___x_948_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_947_, v___f_946_, v_input_945_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toAmericanDateString(lean_object* v_input_949_){
_start:
{
lean_object* v_year_950_; lean_object* v_month_951_; lean_object* v_day_952_; lean_object* v___x_953_; lean_object* v___x_6__overap_954_; lean_object* v___x_955_; 
v_year_950_ = lean_ctor_get(v_input_949_, 0);
lean_inc(v_year_950_);
v_month_951_ = lean_ctor_get(v_input_949_, 1);
lean_inc(v_month_951_);
v_day_952_ = lean_ctor_get(v_input_949_, 2);
lean_inc(v_day_952_);
lean_dec_ref(v_input_949_);
v___x_953_ = l_Std_Time_Formats_americanDate;
v___x_6__overap_954_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_953_);
v___x_955_ = lean_apply_3(v___x_6__overap_954_, v_month_951_, v_day_952_, v_year_950_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString___lam__0(lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
uint8_t v___y_960_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_973_; 
v___x_966_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_967_ = lean_int_mod(v___y_956_, v___x_966_);
v___x_968_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_973_ = lean_int_dec_eq(v___x_967_, v___x_968_);
lean_dec(v___x_967_);
if (v___x_973_ == 0)
{
v___y_960_ = v___x_973_;
goto v___jp_959_;
}
else
{
lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_974_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_975_ = lean_int_mod(v___y_956_, v___x_974_);
v___x_976_ = lean_int_dec_eq(v___x_975_, v___x_968_);
lean_dec(v___x_975_);
if (v___x_976_ == 0)
{
if (v___x_973_ == 0)
{
goto v___jp_969_;
}
else
{
v___y_960_ = v___x_973_;
goto v___jp_959_;
}
}
else
{
goto v___jp_969_;
}
}
v___jp_959_:
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = l_Std_Time_Month_Ordinal_days(v___y_960_, v___y_957_);
v___x_962_ = lean_int_dec_le(v___y_958_, v___x_961_);
lean_dec(v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_dec(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
v___x_963_ = lean_box(0);
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_964_, 0, v___y_956_);
lean_ctor_set(v___x_964_, 1, v___y_957_);
lean_ctor_set(v___x_964_, 2, v___y_958_);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
v___jp_969_:
{
lean_object* v___x_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v___x_970_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_971_ = lean_int_mod(v___y_956_, v___x_970_);
v___x_972_ = lean_int_dec_eq(v___x_971_, v___x_968_);
lean_dec(v___x_971_);
v___y_960_ = v___x_972_;
goto v___jp_959_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString(lean_object* v_input_978_){
_start:
{
lean_object* v___f_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___f_979_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_980_ = l_Std_Time_Formats_sqlDate;
v___x_981_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_980_, v___f_979_, v_input_978_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toSQLDateString(lean_object* v_input_982_){
_start:
{
lean_object* v_year_983_; lean_object* v_month_984_; lean_object* v_day_985_; lean_object* v___x_986_; lean_object* v___x_6__overap_987_; lean_object* v___x_988_; 
v_year_983_ = lean_ctor_get(v_input_982_, 0);
lean_inc(v_year_983_);
v_month_984_ = lean_ctor_get(v_input_982_, 1);
lean_inc(v_month_984_);
v_day_985_ = lean_ctor_get(v_input_982_, 2);
lean_inc(v_day_985_);
lean_dec_ref(v_input_982_);
v___x_986_ = l_Std_Time_Formats_sqlDate;
v___x_6__overap_987_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_986_);
v___x_988_ = lean_apply_3(v___x_6__overap_987_, v_year_983_, v_month_984_, v_day_985_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromLeanDateString(lean_object* v_input_989_){
_start:
{
lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___f_990_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_991_ = l_Std_Time_Formats_leanDate;
v___x_992_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_991_, v___f_990_, v_input_989_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toLeanDateString(lean_object* v_input_993_){
_start:
{
lean_object* v_year_994_; lean_object* v_month_995_; lean_object* v_day_996_; lean_object* v___x_997_; lean_object* v___x_6__overap_998_; lean_object* v___x_999_; 
v_year_994_ = lean_ctor_get(v_input_993_, 0);
lean_inc(v_year_994_);
v_month_995_ = lean_ctor_get(v_input_993_, 1);
lean_inc(v_month_995_);
v_day_996_ = lean_ctor_get(v_input_993_, 2);
lean_inc(v_day_996_);
lean_dec_ref(v_input_993_);
v___x_997_ = l_Std_Time_Formats_leanDate;
v___x_6__overap_998_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_997_);
v___x_999_ = lean_apply_3(v___x_6__overap_998_, v_year_994_, v_month_995_, v_day_996_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_parse(lean_object* v_input_1000_){
_start:
{
lean_object* v___x_1001_; 
lean_inc_ref(v_input_1000_);
v___x_1001_ = l_Std_Time_PlainDate_fromAmericanDateString(v_input_1000_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v___x_1002_; 
lean_dec_ref_known(v___x_1001_, 1);
v___x_1002_ = l_Std_Time_PlainDate_fromSQLDateString(v_input_1000_);
return v___x_1002_;
}
else
{
lean_dec_ref(v_input_1000_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0(lean_object* v_data_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1013_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__1));
v___x_1014_ = l_Std_Time_PlainDate_toLeanDateString(v_data_1011_);
v___x_1015_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1013_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = l_Repr_addAppParen(v___x_1018_, v___y_1012_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0___boxed(lean_object* v_data_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Std_Time_PlainDate_instRepr___lam__0(v_data_1020_, v___y_1021_);
lean_dec(v___y_1021_);
return v_res_1022_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = lean_unsigned_to_nat(12u);
v___x_1026_ = lean_nat_to_int(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0(lean_object* v_time_1027_, lean_object* v_x_1028_){
_start:
{
switch(lean_obj_tag(v_x_1028_))
{
case 22:
{
lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1036_; 
v_isSharedCheck_1036_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1036_ == 0)
{
lean_object* v_unused_1037_; 
v_unused_1037_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1037_);
v___x_1030_ = v_x_1028_;
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
else
{
lean_dec(v_x_1028_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1036_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v_hour_1032_; lean_object* v___x_1034_; 
v_hour_1032_ = lean_ctor_get(v_time_1027_, 0);
lean_inc(v_hour_1032_);
if (v_isShared_1031_ == 0)
{
lean_ctor_set_tag(v___x_1030_, 1);
lean_ctor_set(v___x_1030_, 0, v_hour_1032_);
v___x_1034_ = v___x_1030_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_hour_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
case 21:
{
lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1046_; 
v_isSharedCheck_1046_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1047_);
v___x_1039_ = v_x_1028_;
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
else
{
lean_dec(v_x_1028_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1046_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_hour_1041_; lean_object* v___x_1042_; lean_object* v___x_1044_; 
v_hour_1041_ = lean_ctor_get(v_time_1027_, 0);
v___x_1042_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1041_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set_tag(v___x_1039_, 1);
lean_ctor_set(v___x_1039_, 0, v___x_1042_);
v___x_1044_ = v___x_1039_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
case 23:
{
lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1055_; 
v_isSharedCheck_1055_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1056_);
v___x_1049_ = v_x_1028_;
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
else
{
lean_dec(v_x_1028_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1055_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v_minute_1051_; lean_object* v___x_1053_; 
v_minute_1051_ = lean_ctor_get(v_time_1027_, 1);
lean_inc(v_minute_1051_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 1);
lean_ctor_set(v___x_1049_, 0, v_minute_1051_);
v___x_1053_ = v___x_1049_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_minute_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
case 27:
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1064_; 
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1065_);
v___x_1058_ = v_x_1028_;
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v_x_1028_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_nanosecond_1060_; lean_object* v___x_1062_; 
v_nanosecond_1060_ = lean_ctor_get(v_time_1027_, 3);
lean_inc(v_nanosecond_1060_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 1);
lean_ctor_set(v___x_1058_, 0, v_nanosecond_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_nanosecond_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
case 24:
{
lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1073_; 
v_isSharedCheck_1073_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1073_ == 0)
{
lean_object* v_unused_1074_; 
v_unused_1074_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1074_);
v___x_1067_ = v_x_1028_;
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
else
{
lean_dec(v_x_1028_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1073_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_second_1069_; lean_object* v___x_1071_; 
v_second_1069_ = lean_ctor_get(v_time_1027_, 2);
lean_inc(v_second_1069_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set_tag(v___x_1067_, 1);
lean_ctor_set(v___x_1067_, 0, v_second_1069_);
v___x_1071_ = v___x_1067_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_second_1069_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
case 16:
{
lean_object* v_hour_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec_ref_known(v_x_1028_, 0);
v_hour_1075_ = lean_ctor_get(v_time_1027_, 0);
v___x_1076_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1075_);
v___x_1077_ = lean_box(v___x_1076_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
case 17:
{
lean_object* v_hour_1079_; lean_object* v_minute_1080_; lean_object* v_second_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref_known(v_x_1028_, 0);
v_hour_1079_ = lean_ctor_get(v_time_1027_, 0);
v_minute_1080_ = lean_ctor_get(v_time_1027_, 1);
v_second_1081_ = lean_ctor_get(v_time_1027_, 2);
v___x_1082_ = l_Std_Time_classifyDayPeriod(v_hour_1079_, v_minute_1080_, v_second_1081_);
v___x_1083_ = lean_box(v___x_1082_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
case 18:
{
lean_object* v_hour_1085_; lean_object* v_minute_1086_; lean_object* v_second_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec_ref_known(v_x_1028_, 0);
v_hour_1085_ = lean_ctor_get(v_time_1027_, 0);
v_minute_1086_ = lean_ctor_get(v_time_1027_, 1);
v_second_1087_ = lean_ctor_get(v_time_1027_, 2);
v___x_1088_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1085_, v_minute_1086_, v_second_1087_);
v___x_1089_ = lean_box(v___x_1088_);
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
case 19:
{
lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1099_; 
v_isSharedCheck_1099_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1100_);
v___x_1092_ = v_x_1028_;
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
else
{
lean_dec(v_x_1028_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1099_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_hour_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v_hour_1094_ = lean_ctor_get(v_time_1027_, 0);
v___x_1095_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1094_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set_tag(v___x_1092_, 1);
lean_ctor_set(v___x_1092_, 0, v___x_1095_);
v___x_1097_ = v___x_1092_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
case 20:
{
lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1110_; 
v_isSharedCheck_1110_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1111_);
v___x_1102_ = v_x_1028_;
v_isShared_1103_ = v_isSharedCheck_1110_;
goto v_resetjp_1101_;
}
else
{
lean_dec(v_x_1028_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1110_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v_hour_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v_hour_1104_ = lean_ctor_get(v_time_1027_, 0);
v___x_1105_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1106_ = lean_int_emod(v_hour_1104_, v___x_1105_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 1);
lean_ctor_set(v___x_1102_, 0, v___x_1106_);
v___x_1108_ = v___x_1102_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
case 25:
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1119_; 
v_isSharedCheck_1119_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1120_);
v___x_1113_ = v_x_1028_;
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v_x_1028_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1119_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_nanosecond_1115_; lean_object* v___x_1117_; 
v_nanosecond_1115_ = lean_ctor_get(v_time_1027_, 3);
lean_inc(v_nanosecond_1115_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 1);
lean_ctor_set(v___x_1113_, 0, v_nanosecond_1115_);
v___x_1117_ = v___x_1113_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_nanosecond_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
case 26:
{
lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_isSharedCheck_1128_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1128_ == 0)
{
lean_object* v_unused_1129_; 
v_unused_1129_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1129_);
v___x_1122_ = v_x_1028_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_dec(v_x_1028_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1027_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 1);
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
case 28:
{
lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_isSharedCheck_1137_ = !lean_is_exclusive(v_x_1028_);
if (v_isSharedCheck_1137_ == 0)
{
lean_object* v_unused_1138_; 
v_unused_1138_ = lean_ctor_get(v_x_1028_, 0);
lean_dec(v_unused_1138_);
v___x_1131_ = v_x_1028_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_dec(v_x_1028_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1027_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set_tag(v___x_1131_, 1);
lean_ctor_set(v___x_1131_, 0, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
default: 
{
lean_object* v___x_1139_; 
lean_dec_ref(v_x_1028_);
v___x_1139_ = lean_box(0);
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0___boxed(lean_object* v_time_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_Time_PlainTime_format___lam__0(v_time_1140_, v_x_1141_);
lean_dec_ref(v_time_1140_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format(lean_object* v_time_1143_, lean_object* v_format_1144_){
_start:
{
lean_object* v___x_1145_; lean_object* v_format_1146_; 
v___x_1145_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1146_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1144_, v___x_1145_);
if (lean_obj_tag(v_format_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v_time_1143_);
v_a_1147_ = lean_ctor_get(v_format_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v_format_1146_, 1);
v___x_1148_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1149_ = lean_string_append(v___x_1148_, v_a_1147_);
lean_dec(v_a_1147_);
return v___x_1149_;
}
else
{
lean_object* v_a_1150_; lean_object* v___f_1151_; lean_object* v_res_1152_; 
v_a_1150_ = lean_ctor_get(v_format_1146_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v_format_1146_, 1);
v___f_1151_ = lean_alloc_closure((void*)(l_Std_Time_PlainTime_format___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1151_, 0, v_time_1143_);
v_res_1152_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1150_, v___f_1151_);
if (lean_obj_tag(v_res_1152_) == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1153_;
}
else
{
lean_object* v_val_1154_; 
v_val_1154_ = lean_ctor_get(v_res_1152_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v_res_1152_, 1);
return v_val_1154_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = lean_unsigned_to_nat(1000000000u);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_nat_mod(v___x_1156_, v___x_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0);
v___x_1159_ = lean_nat_to_int(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour___lam__0(lean_object* v_h_1160_, lean_object* v_m_1161_, lean_object* v_s_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1163_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1);
v___x_1164_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1164_, 0, v_h_1160_);
lean_ctor_set(v___x_1164_, 1, v_m_1161_);
lean_ctor_set(v___x_1164_, 2, v_s_1162_);
lean_ctor_set(v___x_1164_, 3, v___x_1163_);
v___x_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour(lean_object* v_input_1167_){
_start:
{
lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___f_1168_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1169_ = l_Std_Time_Formats_time24Hour;
v___x_1170_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1169_, v___f_1168_, v_input_1167_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime24Hour(lean_object* v_input_1171_){
_start:
{
lean_object* v_hour_1172_; lean_object* v_minute_1173_; lean_object* v_second_1174_; lean_object* v___x_1175_; lean_object* v___x_6__overap_1176_; lean_object* v___x_1177_; 
v_hour_1172_ = lean_ctor_get(v_input_1171_, 0);
lean_inc(v_hour_1172_);
v_minute_1173_ = lean_ctor_get(v_input_1171_, 1);
lean_inc(v_minute_1173_);
v_second_1174_ = lean_ctor_get(v_input_1171_, 2);
lean_inc(v_second_1174_);
lean_dec_ref(v_input_1171_);
v___x_1175_ = l_Std_Time_Formats_time24Hour;
v___x_6__overap_1176_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1175_);
v___x_1177_ = lean_apply_3(v___x_6__overap_1176_, v_hour_1172_, v_minute_1173_, v_second_1174_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0(lean_object* v_h_1178_, lean_object* v_m_1179_, lean_object* v_s_1180_, lean_object* v_n_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1182_, 0, v_h_1178_);
lean_ctor_set(v___x_1182_, 1, v_m_1179_);
lean_ctor_set(v___x_1182_, 2, v_s_1180_);
lean_ctor_set(v___x_1182_, 3, v_n_1181_);
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour(lean_object* v_input_1185_){
_start:
{
lean_object* v___f_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___f_1186_ = ((lean_object*)(l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0));
v___x_1187_ = l_Std_Time_Formats_leanTime24Hour;
lean_inc_ref(v_input_1185_);
v___x_1188_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1187_, v___f_1186_, v_input_1185_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
lean_dec_ref_known(v___x_1188_, 1);
v___f_1189_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1190_ = l_Std_Time_Formats_leanTime24HourNoNanos;
v___x_1191_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1190_, v___f_1189_, v_input_1185_);
return v___x_1191_;
}
else
{
lean_dec_ref(v_input_1185_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toLeanTime24Hour(lean_object* v_input_1192_){
_start:
{
lean_object* v_hour_1193_; lean_object* v_minute_1194_; lean_object* v_second_1195_; lean_object* v_nanosecond_1196_; lean_object* v___x_1197_; lean_object* v___x_7__overap_1198_; lean_object* v___x_1199_; 
v_hour_1193_ = lean_ctor_get(v_input_1192_, 0);
lean_inc(v_hour_1193_);
v_minute_1194_ = lean_ctor_get(v_input_1192_, 1);
lean_inc(v_minute_1194_);
v_second_1195_ = lean_ctor_get(v_input_1192_, 2);
lean_inc(v_second_1195_);
v_nanosecond_1196_ = lean_ctor_get(v_input_1192_, 3);
lean_inc(v_nanosecond_1196_);
lean_dec_ref(v_input_1192_);
v___x_1197_ = l_Std_Time_Formats_leanTime24Hour;
v___x_7__overap_1198_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1197_);
v___x_1199_ = lean_apply_4(v___x_7__overap_1198_, v_hour_1193_, v_minute_1194_, v_second_1195_, v_nanosecond_1196_);
return v___x_1199_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = lean_nat_to_int(v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0(lean_object* v_h_1202_, lean_object* v_m_1203_, lean_object* v_s_1204_, uint8_t v_a_1205_){
_start:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1207_ = lean_int_dec_le(v___x_1206_, v_h_1202_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
lean_dec(v_s_1204_);
lean_dec(v_m_1203_);
v___x_1208_ = lean_box(0);
return v___x_1208_;
}
else
{
lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1209_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1210_ = lean_int_dec_le(v_h_1202_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_dec(v_s_1204_);
lean_dec(v_m_1203_);
v___x_1211_ = lean_box(0);
return v___x_1211_;
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = l_Std_Time_HourMarker_toAbsolute(v_a_1205_, v_h_1202_);
v___x_1213_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1);
v___x_1214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v_m_1203_);
lean_ctor_set(v___x_1214_, 2, v_s_1204_);
lean_ctor_set(v___x_1214_, 3, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed(lean_object* v_h_1216_, lean_object* v_m_1217_, lean_object* v_s_1218_, lean_object* v_a_1219_){
_start:
{
uint8_t v_a_boxed_1220_; lean_object* v_res_1221_; 
v_a_boxed_1220_ = lean_unbox(v_a_1219_);
v_res_1221_ = l_Std_Time_PlainTime_fromTime12Hour___lam__0(v_h_1216_, v_m_1217_, v_s_1218_, v_a_boxed_1220_);
lean_dec(v_h_1216_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour(lean_object* v_input_1223_){
_start:
{
lean_object* v_builder_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_builder_1224_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime12Hour___closed__0));
v___x_1225_ = l_Std_Time_Formats_time12Hour;
v___x_1226_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1225_, v_builder_1224_, v_input_1223_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime12Hour(lean_object* v_input_1227_){
_start:
{
lean_object* v_hour_1228_; lean_object* v_minute_1229_; lean_object* v_second_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_hour_1228_ = lean_ctor_get(v_input_1227_, 0);
lean_inc(v_hour_1228_);
v_minute_1229_ = lean_ctor_get(v_input_1227_, 1);
lean_inc(v_minute_1229_);
v_second_1230_ = lean_ctor_get(v_input_1227_, 2);
lean_inc(v_second_1230_);
lean_dec_ref(v_input_1227_);
v___x_1231_ = l_Std_Time_Formats_time12Hour;
v___x_1232_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1233_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1234_ = lean_int_emod(v_hour_1228_, v___x_1232_);
v___x_1235_ = lean_int_add(v___x_1234_, v___x_1233_);
lean_dec(v___x_1234_);
v___x_1236_ = lean_int_dec_le(v___x_1232_, v_hour_1228_);
lean_dec(v_hour_1228_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; lean_object* v___x_56__overap_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1237_ = 0;
v___x_56__overap_1238_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1231_);
v___x_1239_ = lean_box(v___x_1237_);
v___x_1240_ = lean_apply_4(v___x_56__overap_1238_, v___x_1235_, v_minute_1229_, v_second_1230_, v___x_1239_);
return v___x_1240_;
}
else
{
uint8_t v___x_1241_; lean_object* v___x_57__overap_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1241_ = 1;
v___x_57__overap_1242_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1231_);
v___x_1243_ = lean_box(v___x_1241_);
v___x_1244_ = lean_apply_4(v___x_57__overap_1242_, v___x_1235_, v_minute_1229_, v_second_1230_, v___x_1243_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_parse(lean_object* v_input_1245_){
_start:
{
lean_object* v___x_1246_; 
lean_inc_ref(v_input_1245_);
v___x_1246_ = l_Std_Time_PlainTime_fromTime12Hour(v_input_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v___x_1247_; 
lean_dec_ref_known(v___x_1246_, 1);
v___x_1247_ = l_Std_Time_PlainTime_fromTime24Hour(v_input_1245_);
return v___x_1247_;
}
else
{
lean_dec_ref(v_input_1245_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0(lean_object* v_data_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1255_ = ((lean_object*)(l_Std_Time_PlainTime_instRepr___lam__0___closed__1));
v___x_1256_ = l_Std_Time_PlainTime_toLeanTime24Hour(v_data_1253_);
v___x_1257_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1255_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Repr_addAppParen(v___x_1260_, v___y_1254_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0___boxed(lean_object* v_data_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Std_Time_PlainTime_instRepr___lam__0(v_data_1262_, v___y_1263_);
lean_dec(v___y_1263_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format(lean_object* v_data_1267_, lean_object* v_format_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v_format_1270_; 
v___x_1269_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1270_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1268_, v___x_1269_);
if (lean_obj_tag(v_format_1270_) == 0)
{
lean_object* v_a_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref(v_data_1267_);
v_a_1271_ = lean_ctor_get(v_format_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v_format_1270_, 1);
v___x_1272_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1273_ = lean_string_append(v___x_1272_, v_a_1271_);
lean_dec(v_a_1271_);
return v___x_1273_;
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_a_1274_ = lean_ctor_get(v_format_1270_, 0);
lean_inc(v_a_1274_);
lean_dec_ref_known(v_format_1270_, 1);
v___x_1275_ = lean_box(1);
v___x_1276_ = l_Std_Time_GenericFormat_format(v___x_1275_, v_a_1274_, v_data_1267_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromISO8601String(lean_object* v_input_1277_){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_box(1);
v___x_1279_ = l_Std_Time_Formats_iso8601;
v___x_1280_ = l_Std_Time_GenericFormat_parse(v___x_1278_, v___x_1279_, v_input_1277_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String(lean_object* v_date_1281_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_box(1);
v___x_1283_ = l_Std_Time_Formats_iso8601;
v___x_1284_ = l_Std_Time_GenericFormat_format(v___x_1282_, v___x_1283_, v_date_1281_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC822String(lean_object* v_input_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_box(1);
v___x_1287_ = l_Std_Time_Formats_rfc822;
v___x_1288_ = l_Std_Time_GenericFormat_parse(v___x_1286_, v___x_1287_, v_input_1285_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String(lean_object* v_date_1289_){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_box(1);
v___x_1291_ = l_Std_Time_Formats_rfc822;
v___x_1292_ = l_Std_Time_GenericFormat_format(v___x_1290_, v___x_1291_, v_date_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC850String(lean_object* v_input_1293_){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = lean_box(1);
v___x_1295_ = l_Std_Time_Formats_rfc850;
v___x_1296_ = l_Std_Time_GenericFormat_parse(v___x_1294_, v___x_1295_, v_input_1293_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String(lean_object* v_date_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_box(1);
v___x_1299_ = l_Std_Time_Formats_rfc850;
v___x_1300_ = l_Std_Time_GenericFormat_format(v___x_1298_, v___x_1299_, v_date_1297_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromDateTimeWithZoneString(lean_object* v_input_1301_){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = lean_box(1);
v___x_1303_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1304_ = l_Std_Time_GenericFormat_parse(v___x_1302_, v___x_1303_, v_input_1301_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString(lean_object* v_pdt_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_box(1);
v___x_1307_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1308_ = l_Std_Time_GenericFormat_format(v___x_1306_, v___x_1307_, v_pdt_1305_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithZoneString(lean_object* v_input_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_box(1);
v___x_1311_ = l_Std_Time_Formats_leanDateTimeWithZone;
lean_inc_ref(v_input_1309_);
v___x_1312_ = l_Std_Time_GenericFormat_parse(v___x_1310_, v___x_1311_, v_input_1309_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec_ref_known(v___x_1312_, 1);
v___x_1313_ = l_Std_Time_Formats_leanDateTimeWithZoneNoNanos;
v___x_1314_ = l_Std_Time_GenericFormat_parse(v___x_1310_, v___x_1313_, v_input_1309_);
return v___x_1314_;
}
else
{
lean_dec_ref(v_input_1309_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(lean_object* v_input_1315_){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_box(1);
v___x_1317_ = l_Std_Time_Formats_leanDateTimeWithIdentifier;
lean_inc_ref(v_input_1315_);
v___x_1318_ = l_Std_Time_GenericFormat_parse(v___x_1316_, v___x_1317_, v_input_1315_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec_ref_known(v___x_1318_, 1);
v___x_1319_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_1320_ = l_Std_Time_GenericFormat_parse(v___x_1316_, v___x_1319_, v_input_1315_);
return v___x_1320_;
}
else
{
lean_dec_ref(v_input_1315_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString(lean_object* v_zdt_1321_){
_start:
{
lean_object* v_date_1322_; lean_object* v_timezone_1323_; lean_object* v___x_1324_; lean_object* v_date_1325_; lean_object* v_time_1326_; lean_object* v_year_1327_; lean_object* v_month_1328_; lean_object* v_day_1329_; lean_object* v_hour_1330_; lean_object* v_minute_1331_; lean_object* v_second_1332_; lean_object* v_nanosecond_1333_; lean_object* v_offset_1334_; lean_object* v___x_1335_; lean_object* v___x_14__overap_1336_; lean_object* v___x_1337_; 
v_date_1322_ = lean_ctor_get(v_zdt_1321_, 0);
lean_inc_ref(v_date_1322_);
v_timezone_1323_ = lean_ctor_get(v_zdt_1321_, 3);
lean_inc_ref(v_timezone_1323_);
lean_dec_ref(v_zdt_1321_);
v___x_1324_ = lean_thunk_get_own(v_date_1322_);
lean_dec_ref(v_date_1322_);
v_date_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc_ref(v_date_1325_);
v_time_1326_ = lean_ctor_get(v___x_1324_, 1);
lean_inc_ref(v_time_1326_);
lean_dec(v___x_1324_);
v_year_1327_ = lean_ctor_get(v_date_1325_, 0);
lean_inc(v_year_1327_);
v_month_1328_ = lean_ctor_get(v_date_1325_, 1);
lean_inc(v_month_1328_);
v_day_1329_ = lean_ctor_get(v_date_1325_, 2);
lean_inc(v_day_1329_);
lean_dec_ref(v_date_1325_);
v_hour_1330_ = lean_ctor_get(v_time_1326_, 0);
lean_inc(v_hour_1330_);
v_minute_1331_ = lean_ctor_get(v_time_1326_, 1);
lean_inc(v_minute_1331_);
v_second_1332_ = lean_ctor_get(v_time_1326_, 2);
lean_inc(v_second_1332_);
v_nanosecond_1333_ = lean_ctor_get(v_time_1326_, 3);
lean_inc(v_nanosecond_1333_);
lean_dec_ref(v_time_1326_);
v_offset_1334_ = lean_ctor_get(v_timezone_1323_, 0);
lean_inc(v_offset_1334_);
lean_dec_ref(v_timezone_1323_);
v___x_1335_ = l_Std_Time_Formats_leanDateTimeWithZone;
v___x_14__overap_1336_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1335_);
v___x_1337_ = lean_apply_8(v___x_14__overap_1336_, v_year_1327_, v_month_1328_, v_day_1329_, v_hour_1330_, v_minute_1331_, v_second_1332_, v_nanosecond_1333_, v_offset_1334_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithIdentifierString(lean_object* v_zdt_1338_){
_start:
{
lean_object* v_date_1339_; lean_object* v_timezone_1340_; lean_object* v___x_1341_; lean_object* v_date_1342_; lean_object* v_time_1343_; lean_object* v_year_1344_; lean_object* v_month_1345_; lean_object* v_day_1346_; lean_object* v_hour_1347_; lean_object* v_minute_1348_; lean_object* v_second_1349_; lean_object* v_nanosecond_1350_; lean_object* v_name_1351_; lean_object* v___x_1352_; lean_object* v___x_15__overap_1353_; lean_object* v___x_1354_; 
v_date_1339_ = lean_ctor_get(v_zdt_1338_, 0);
lean_inc_ref(v_date_1339_);
v_timezone_1340_ = lean_ctor_get(v_zdt_1338_, 3);
lean_inc_ref(v_timezone_1340_);
lean_dec_ref(v_zdt_1338_);
v___x_1341_ = lean_thunk_get_own(v_date_1339_);
lean_dec_ref(v_date_1339_);
v_date_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc_ref(v_date_1342_);
v_time_1343_ = lean_ctor_get(v___x_1341_, 1);
lean_inc_ref(v_time_1343_);
lean_dec(v___x_1341_);
v_year_1344_ = lean_ctor_get(v_date_1342_, 0);
lean_inc(v_year_1344_);
v_month_1345_ = lean_ctor_get(v_date_1342_, 1);
lean_inc(v_month_1345_);
v_day_1346_ = lean_ctor_get(v_date_1342_, 2);
lean_inc(v_day_1346_);
lean_dec_ref(v_date_1342_);
v_hour_1347_ = lean_ctor_get(v_time_1343_, 0);
lean_inc(v_hour_1347_);
v_minute_1348_ = lean_ctor_get(v_time_1343_, 1);
lean_inc(v_minute_1348_);
v_second_1349_ = lean_ctor_get(v_time_1343_, 2);
lean_inc(v_second_1349_);
v_nanosecond_1350_ = lean_ctor_get(v_time_1343_, 3);
lean_inc(v_nanosecond_1350_);
lean_dec_ref(v_time_1343_);
v_name_1351_ = lean_ctor_get(v_timezone_1340_, 1);
lean_inc_ref(v_name_1351_);
lean_dec_ref(v_timezone_1340_);
v___x_1352_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_15__overap_1353_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1352_);
v___x_1354_ = lean_apply_8(v___x_15__overap_1353_, v_year_1344_, v_month_1345_, v_day_1346_, v_hour_1347_, v_minute_1348_, v_second_1349_, v_nanosecond_1350_, v_name_1351_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_parse(lean_object* v_input_1355_){
_start:
{
lean_object* v___x_1356_; 
lean_inc_ref(v_input_1355_);
v___x_1356_ = l_Std_Time_DateTime_fromISO8601String(v_input_1355_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v___x_1357_; 
lean_dec_ref_known(v___x_1356_, 1);
lean_inc_ref(v_input_1355_);
v___x_1357_ = l_Std_Time_DateTime_fromRFC822String(v_input_1355_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v___x_1358_; 
lean_dec_ref_known(v___x_1357_, 1);
lean_inc_ref(v_input_1355_);
v___x_1358_ = l_Std_Time_DateTime_fromRFC850String(v_input_1355_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref_known(v___x_1358_, 1);
lean_inc_ref(v_input_1355_);
v___x_1359_ = l_Std_Time_DateTime_fromDateTimeWithZoneString(v_input_1355_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1360_; 
lean_dec_ref_known(v___x_1359_, 1);
v___x_1360_ = l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(v_input_1355_);
return v___x_1360_;
}
else
{
lean_dec_ref(v_input_1355_);
return v___x_1359_;
}
}
else
{
lean_dec_ref(v_input_1355_);
return v___x_1358_;
}
}
else
{
lean_dec_ref(v_input_1355_);
return v___x_1357_;
}
}
else
{
lean_dec_ref(v_input_1355_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0(lean_object* v_data_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1368_ = ((lean_object*)(l_Std_Time_DateTime_instRepr___lam__0___closed__1));
v___x_1369_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_data_1366_);
v___x_1370_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
v___x_1371_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1368_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1371_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Repr_addAppParen(v___x_1373_, v___y_1367_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0___boxed(lean_object* v_data_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Std_Time_DateTime_instRepr___lam__0(v_data_1375_, v___y_1376_);
lean_dec(v___y_1376_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0(lean_object* v_date_1380_, lean_object* v_locale_1381_, lean_object* v_x_1382_){
_start:
{
switch(lean_obj_tag(v_x_1382_))
{
case 0:
{
lean_object* v_date_1383_; lean_object* v_year_1384_; uint8_t v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec_ref_known(v_x_1382_, 0);
v_date_1383_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1383_);
lean_dec_ref(v_date_1380_);
v_year_1384_ = lean_ctor_get(v_date_1383_, 0);
lean_inc(v_year_1384_);
lean_dec_ref(v_date_1383_);
v___x_1385_ = l_Std_Time_Year_Offset_era(v_year_1384_);
lean_dec(v_year_1384_);
v___x_1386_ = lean_box(v___x_1385_);
v___x_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1387_, 0, v___x_1386_);
return v___x_1387_;
}
case 2:
{
lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1396_; 
v_isSharedCheck_1396_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; 
v_unused_1397_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1397_);
v___x_1389_ = v_x_1382_;
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
else
{
lean_dec(v_x_1382_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v_date_1391_; lean_object* v_year_1392_; lean_object* v___x_1394_; 
v_date_1391_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1391_);
lean_dec_ref(v_date_1380_);
v_year_1392_ = lean_ctor_get(v_date_1391_, 0);
lean_inc(v_year_1392_);
lean_dec_ref(v_date_1391_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set_tag(v___x_1389_, 1);
lean_ctor_set(v___x_1389_, 0, v_year_1392_);
v___x_1394_ = v___x_1389_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_year_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
case 1:
{
lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1406_; 
v_isSharedCheck_1406_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1407_);
v___x_1399_ = v_x_1382_;
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
else
{
lean_dec(v_x_1382_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1406_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_date_1401_; lean_object* v_year_1402_; lean_object* v___x_1404_; 
v_date_1401_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1401_);
lean_dec_ref(v_date_1380_);
v_year_1402_ = lean_ctor_get(v_date_1401_, 0);
lean_inc(v_year_1402_);
lean_dec_ref(v_date_1401_);
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 0, v_year_1402_);
v___x_1404_ = v___x_1399_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_year_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
case 9:
{
lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1418_; 
v_isSharedCheck_1418_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; 
v_unused_1419_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1419_);
v___x_1409_ = v_x_1382_;
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
else
{
lean_dec(v_x_1382_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1418_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
uint8_t v_firstDayOfWeek_1411_; lean_object* v_minimalDaysInFirstWeek_1412_; lean_object* v_date_1413_; lean_object* v___x_1414_; lean_object* v___x_1416_; 
v_firstDayOfWeek_1411_ = lean_ctor_get_uint8(v_locale_1381_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1412_ = lean_ctor_get(v_locale_1381_, 0);
v_date_1413_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1413_);
lean_dec_ref(v_date_1380_);
v___x_1414_ = l_Std_Time_PlainDate_weekYear(v_date_1413_, v_firstDayOfWeek_1411_, v_minimalDaysInFirstWeek_1412_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 1);
lean_ctor_set(v___x_1409_, 0, v___x_1414_);
v___x_1416_ = v___x_1409_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1414_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
case 3:
{
lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1471_; 
v_isSharedCheck_1471_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1472_);
v___x_1421_ = v_x_1382_;
v_isShared_1422_ = v_isSharedCheck_1471_;
goto v_resetjp_1420_;
}
else
{
lean_dec(v_x_1382_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1471_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v_date_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1469_; 
v_date_1423_ = lean_ctor_get(v_date_1380_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_date_1380_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v_date_1380_, 1);
lean_dec(v_unused_1470_);
v___x_1425_ = v_date_1380_;
v_isShared_1426_ = v_isSharedCheck_1469_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_date_1423_);
lean_dec(v_date_1380_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1469_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_year_1427_; lean_object* v_month_1428_; lean_object* v_day_1429_; uint8_t v___y_1431_; uint8_t v___y_1432_; lean_object* v___y_1443_; lean_object* v___y_1444_; uint8_t v___y_1445_; uint8_t v___y_1450_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1465_; 
v_year_1427_ = lean_ctor_get(v_date_1423_, 0);
lean_inc(v_year_1427_);
v_month_1428_ = lean_ctor_get(v_date_1423_, 1);
lean_inc(v_month_1428_);
v_day_1429_ = lean_ctor_get(v_date_1423_, 2);
lean_inc(v_day_1429_);
lean_dec_ref(v_date_1423_);
v___x_1458_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1459_ = lean_int_mod(v_year_1427_, v___x_1458_);
v___x_1460_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1465_ = lean_int_dec_eq(v___x_1459_, v___x_1460_);
lean_dec(v___x_1459_);
if (v___x_1465_ == 0)
{
v___y_1450_ = v___x_1465_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1467_ = lean_int_mod(v_year_1427_, v___x_1466_);
v___x_1468_ = lean_int_dec_eq(v___x_1467_, v___x_1460_);
lean_dec(v___x_1467_);
if (v___x_1468_ == 0)
{
if (v___x_1465_ == 0)
{
goto v___jp_1461_;
}
else
{
v___y_1450_ = v___x_1465_;
goto v___jp_1449_;
}
}
else
{
goto v___jp_1461_;
}
}
v___jp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 1, v_day_1429_);
lean_ctor_set(v___x_1425_, 0, v_month_1428_);
v___x_1434_ = v___x_1425_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_month_1428_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_day_1429_);
v___x_1434_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1435_ = l_Std_Time_ValidDate_dayOfYear(v___y_1432_, v___x_1434_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = lean_box(v___y_1431_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
lean_ctor_set(v___x_1437_, 1, v___x_1435_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set_tag(v___x_1421_, 1);
lean_ctor_set(v___x_1421_, 0, v___x_1437_);
v___x_1439_ = v___x_1421_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
v___jp_1442_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1447_ = lean_int_mod(v___y_1444_, v___x_1446_);
lean_dec(v___y_1444_);
v___x_1448_ = lean_int_dec_eq(v___x_1447_, v___y_1443_);
lean_dec(v___x_1447_);
v___y_1431_ = v___y_1445_;
v___y_1432_ = v___x_1448_;
goto v___jp_1430_;
}
v___jp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1451_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1452_ = lean_int_mod(v_year_1427_, v___x_1451_);
v___x_1453_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1454_ = lean_int_dec_eq(v___x_1452_, v___x_1453_);
lean_dec(v___x_1452_);
if (v___x_1454_ == 0)
{
lean_dec(v_year_1427_);
v___y_1431_ = v___y_1450_;
v___y_1432_ = v___x_1454_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; 
v___x_1455_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1456_ = lean_int_mod(v_year_1427_, v___x_1455_);
v___x_1457_ = lean_int_dec_eq(v___x_1456_, v___x_1453_);
lean_dec(v___x_1456_);
if (v___x_1457_ == 0)
{
if (v___x_1454_ == 0)
{
v___y_1443_ = v___x_1453_;
v___y_1444_ = v_year_1427_;
v___y_1445_ = v___y_1450_;
goto v___jp_1442_;
}
else
{
lean_dec(v_year_1427_);
v___y_1431_ = v___y_1450_;
v___y_1432_ = v___x_1454_;
goto v___jp_1430_;
}
}
else
{
v___y_1443_ = v___x_1453_;
v___y_1444_ = v_year_1427_;
v___y_1445_ = v___y_1450_;
goto v___jp_1442_;
}
}
}
v___jp_1461_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v___x_1462_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1463_ = lean_int_mod(v_year_1427_, v___x_1462_);
v___x_1464_ = lean_int_dec_eq(v___x_1463_, v___x_1460_);
lean_dec(v___x_1463_);
v___y_1450_ = v___x_1464_;
goto v___jp_1449_;
}
}
}
}
case 7:
{
lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1481_; 
v_isSharedCheck_1481_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1482_);
v___x_1474_ = v_x_1382_;
v_isShared_1475_ = v_isSharedCheck_1481_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v_x_1382_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1481_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_date_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
v_date_1476_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1476_);
lean_dec_ref(v_date_1380_);
v___x_1477_ = l_Std_Time_PlainDate_quarter(v_date_1476_);
lean_dec_ref(v_date_1476_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 1);
lean_ctor_set(v___x_1474_, 0, v___x_1477_);
v___x_1479_ = v___x_1474_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
case 8:
{
lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1491_; 
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1492_);
v___x_1484_ = v_x_1382_;
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
else
{
lean_dec(v_x_1382_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_date_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v_date_1486_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1486_);
lean_dec_ref(v_date_1380_);
v___x_1487_ = l_Std_Time_PlainDate_quarter(v_date_1486_);
lean_dec_ref(v_date_1486_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 1);
lean_ctor_set(v___x_1484_, 0, v___x_1487_);
v___x_1489_ = v___x_1484_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
case 10:
{
lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1503_; 
v_isSharedCheck_1503_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1504_);
v___x_1494_ = v_x_1382_;
v_isShared_1495_ = v_isSharedCheck_1503_;
goto v_resetjp_1493_;
}
else
{
lean_dec(v_x_1382_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1503_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
uint8_t v_firstDayOfWeek_1496_; lean_object* v_minimalDaysInFirstWeek_1497_; lean_object* v_date_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; 
v_firstDayOfWeek_1496_ = lean_ctor_get_uint8(v_locale_1381_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1497_ = lean_ctor_get(v_locale_1381_, 0);
v_date_1498_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1498_);
lean_dec_ref(v_date_1380_);
v___x_1499_ = l_Std_Time_PlainDate_weekOfYear(v_date_1498_, v_firstDayOfWeek_1496_, v_minimalDaysInFirstWeek_1497_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set_tag(v___x_1494_, 1);
lean_ctor_set(v___x_1494_, 0, v___x_1499_);
v___x_1501_ = v___x_1494_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
case 11:
{
lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1514_; 
v_isSharedCheck_1514_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1515_);
v___x_1506_ = v_x_1382_;
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
else
{
lean_dec(v_x_1382_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1514_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
uint8_t v_firstDayOfWeek_1508_; lean_object* v_date_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v_firstDayOfWeek_1508_ = lean_ctor_get_uint8(v_locale_1381_, sizeof(void*)*2);
v_date_1509_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1509_);
lean_dec_ref(v_date_1380_);
v___x_1510_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1509_, v_firstDayOfWeek_1508_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set_tag(v___x_1506_, 1);
lean_ctor_set(v___x_1506_, 0, v___x_1510_);
v___x_1512_ = v___x_1506_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
case 4:
{
lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1524_; 
v_isSharedCheck_1524_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1525_);
v___x_1517_ = v_x_1382_;
v_isShared_1518_ = v_isSharedCheck_1524_;
goto v_resetjp_1516_;
}
else
{
lean_dec(v_x_1382_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1524_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_date_1519_; lean_object* v_month_1520_; lean_object* v___x_1522_; 
v_date_1519_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1519_);
lean_dec_ref(v_date_1380_);
v_month_1520_ = lean_ctor_get(v_date_1519_, 1);
lean_inc(v_month_1520_);
lean_dec_ref(v_date_1519_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 1);
lean_ctor_set(v___x_1517_, 0, v_month_1520_);
v___x_1522_ = v___x_1517_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_month_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
case 5:
{
lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1534_; 
v_isSharedCheck_1534_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1535_);
v___x_1527_ = v_x_1382_;
v_isShared_1528_ = v_isSharedCheck_1534_;
goto v_resetjp_1526_;
}
else
{
lean_dec(v_x_1382_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1534_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_date_1529_; lean_object* v_month_1530_; lean_object* v___x_1532_; 
v_date_1529_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1529_);
lean_dec_ref(v_date_1380_);
v_month_1530_ = lean_ctor_get(v_date_1529_, 1);
lean_inc(v_month_1530_);
lean_dec_ref(v_date_1529_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 1);
lean_ctor_set(v___x_1527_, 0, v_month_1530_);
v___x_1532_ = v___x_1527_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_month_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
case 6:
{
lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1544_; 
v_isSharedCheck_1544_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1545_);
v___x_1537_ = v_x_1382_;
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
else
{
lean_dec(v_x_1382_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1544_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v_date_1539_; lean_object* v_day_1540_; lean_object* v___x_1542_; 
v_date_1539_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1539_);
lean_dec_ref(v_date_1380_);
v_day_1540_ = lean_ctor_get(v_date_1539_, 2);
lean_inc(v_day_1540_);
lean_dec_ref(v_date_1539_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 1);
lean_ctor_set(v___x_1537_, 0, v_day_1540_);
v___x_1542_ = v___x_1537_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_day_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
case 12:
{
lean_object* v_date_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec_ref_known(v_x_1382_, 0);
v_date_1546_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1546_);
lean_dec_ref(v_date_1380_);
v___x_1547_ = l_Std_Time_PlainDate_weekday(v_date_1546_);
v___x_1548_ = lean_box(v___x_1547_);
v___x_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
return v___x_1549_;
}
case 13:
{
lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1559_; 
v_isSharedCheck_1559_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1559_ == 0)
{
lean_object* v_unused_1560_; 
v_unused_1560_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1560_);
v___x_1551_ = v_x_1382_;
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
else
{
lean_dec(v_x_1382_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_date_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v_date_1553_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1553_);
lean_dec_ref(v_date_1380_);
v___x_1554_ = l_Std_Time_PlainDate_weekday(v_date_1553_);
v___x_1555_ = lean_box(v___x_1554_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 1);
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1557_ = v___x_1551_;
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
case 14:
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1570_; 
v_isSharedCheck_1570_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1571_);
v___x_1562_ = v_x_1382_;
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_x_1382_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1570_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_date_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; 
v_date_1564_ = lean_ctor_get(v_date_1380_, 0);
lean_inc_ref(v_date_1564_);
lean_dec_ref(v_date_1380_);
v___x_1565_ = l_Std_Time_PlainDate_weekday(v_date_1564_);
v___x_1566_ = lean_box(v___x_1565_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 1);
lean_ctor_set(v___x_1562_, 0, v___x_1566_);
v___x_1568_ = v___x_1562_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
case 15:
{
lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1579_; 
v_isSharedCheck_1579_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1580_);
v___x_1573_ = v_x_1382_;
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v_x_1382_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1579_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; lean_object* v___x_1577_; 
v___x_1575_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_1380_);
lean_dec_ref(v_date_1380_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 1);
lean_ctor_set(v___x_1573_, 0, v___x_1575_);
v___x_1577_ = v___x_1573_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
case 22:
{
lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1589_; 
v_isSharedCheck_1589_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1590_);
v___x_1582_ = v_x_1382_;
v_isShared_1583_ = v_isSharedCheck_1589_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v_x_1382_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1589_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_time_1584_; lean_object* v_hour_1585_; lean_object* v___x_1587_; 
v_time_1584_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1584_);
lean_dec_ref(v_date_1380_);
v_hour_1585_ = lean_ctor_get(v_time_1584_, 0);
lean_inc(v_hour_1585_);
lean_dec_ref(v_time_1584_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 1);
lean_ctor_set(v___x_1582_, 0, v_hour_1585_);
v___x_1587_ = v___x_1582_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_hour_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
case 21:
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1600_; 
v_isSharedCheck_1600_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1601_);
v___x_1592_ = v_x_1382_;
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v_x_1382_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_time_1594_; lean_object* v_hour_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v_time_1594_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1594_);
lean_dec_ref(v_date_1380_);
v_hour_1595_ = lean_ctor_get(v_time_1594_, 0);
lean_inc(v_hour_1595_);
lean_dec_ref(v_time_1594_);
v___x_1596_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1595_);
lean_dec(v_hour_1595_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 1);
lean_ctor_set(v___x_1592_, 0, v___x_1596_);
v___x_1598_ = v___x_1592_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
case 23:
{
lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1610_; 
v_isSharedCheck_1610_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1611_);
v___x_1603_ = v_x_1382_;
v_isShared_1604_ = v_isSharedCheck_1610_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v_x_1382_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1610_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v_time_1605_; lean_object* v_minute_1606_; lean_object* v___x_1608_; 
v_time_1605_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1605_);
lean_dec_ref(v_date_1380_);
v_minute_1606_ = lean_ctor_get(v_time_1605_, 1);
lean_inc(v_minute_1606_);
lean_dec_ref(v_time_1605_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 1);
lean_ctor_set(v___x_1603_, 0, v_minute_1606_);
v___x_1608_ = v___x_1603_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_minute_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
case 27:
{
lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1620_; 
v_isSharedCheck_1620_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1620_ == 0)
{
lean_object* v_unused_1621_; 
v_unused_1621_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1621_);
v___x_1613_ = v_x_1382_;
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
else
{
lean_dec(v_x_1382_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1620_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_time_1615_; lean_object* v_nanosecond_1616_; lean_object* v___x_1618_; 
v_time_1615_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1615_);
lean_dec_ref(v_date_1380_);
v_nanosecond_1616_ = lean_ctor_get(v_time_1615_, 3);
lean_inc(v_nanosecond_1616_);
lean_dec_ref(v_time_1615_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set_tag(v___x_1613_, 1);
lean_ctor_set(v___x_1613_, 0, v_nanosecond_1616_);
v___x_1618_ = v___x_1613_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_nanosecond_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
case 24:
{
lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1630_; 
v_isSharedCheck_1630_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1631_);
v___x_1623_ = v_x_1382_;
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
else
{
lean_dec(v_x_1382_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v_time_1625_; lean_object* v_second_1626_; lean_object* v___x_1628_; 
v_time_1625_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1625_);
lean_dec_ref(v_date_1380_);
v_second_1626_ = lean_ctor_get(v_time_1625_, 2);
lean_inc(v_second_1626_);
lean_dec_ref(v_time_1625_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set_tag(v___x_1623_, 1);
lean_ctor_set(v___x_1623_, 0, v_second_1626_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_second_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
case 16:
{
lean_object* v_time_1632_; lean_object* v_hour_1633_; uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref_known(v_x_1382_, 0);
v_time_1632_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1632_);
lean_dec_ref(v_date_1380_);
v_hour_1633_ = lean_ctor_get(v_time_1632_, 0);
lean_inc(v_hour_1633_);
lean_dec_ref(v_time_1632_);
v___x_1634_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1633_);
lean_dec(v_hour_1633_);
v___x_1635_ = lean_box(v___x_1634_);
v___x_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
case 17:
{
lean_object* v_time_1637_; lean_object* v_hour_1638_; lean_object* v_minute_1639_; lean_object* v_second_1640_; uint8_t v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
lean_dec_ref_known(v_x_1382_, 0);
v_time_1637_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1637_);
lean_dec_ref(v_date_1380_);
v_hour_1638_ = lean_ctor_get(v_time_1637_, 0);
lean_inc(v_hour_1638_);
v_minute_1639_ = lean_ctor_get(v_time_1637_, 1);
lean_inc(v_minute_1639_);
v_second_1640_ = lean_ctor_get(v_time_1637_, 2);
lean_inc(v_second_1640_);
lean_dec_ref(v_time_1637_);
v___x_1641_ = l_Std_Time_classifyDayPeriod(v_hour_1638_, v_minute_1639_, v_second_1640_);
lean_dec(v_second_1640_);
lean_dec(v_minute_1639_);
lean_dec(v_hour_1638_);
v___x_1642_ = lean_box(v___x_1641_);
v___x_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
return v___x_1643_;
}
case 18:
{
lean_object* v_time_1644_; lean_object* v_hour_1645_; lean_object* v_minute_1646_; lean_object* v_second_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_dec_ref_known(v_x_1382_, 0);
v_time_1644_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1644_);
lean_dec_ref(v_date_1380_);
v_hour_1645_ = lean_ctor_get(v_time_1644_, 0);
lean_inc(v_hour_1645_);
v_minute_1646_ = lean_ctor_get(v_time_1644_, 1);
lean_inc(v_minute_1646_);
v_second_1647_ = lean_ctor_get(v_time_1644_, 2);
lean_inc(v_second_1647_);
lean_dec_ref(v_time_1644_);
v___x_1648_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1645_, v_minute_1646_, v_second_1647_);
lean_dec(v_second_1647_);
lean_dec(v_minute_1646_);
lean_dec(v_hour_1645_);
v___x_1649_ = lean_box(v___x_1648_);
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
return v___x_1650_;
}
case 19:
{
lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1660_; 
v_isSharedCheck_1660_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1660_ == 0)
{
lean_object* v_unused_1661_; 
v_unused_1661_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1661_);
v___x_1652_ = v_x_1382_;
v_isShared_1653_ = v_isSharedCheck_1660_;
goto v_resetjp_1651_;
}
else
{
lean_dec(v_x_1382_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1660_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v_time_1654_; lean_object* v_hour_1655_; lean_object* v___x_1656_; lean_object* v___x_1658_; 
v_time_1654_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1654_);
lean_dec_ref(v_date_1380_);
v_hour_1655_ = lean_ctor_get(v_time_1654_, 0);
lean_inc(v_hour_1655_);
lean_dec_ref(v_time_1654_);
v___x_1656_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1655_);
lean_dec(v_hour_1655_);
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 1);
lean_ctor_set(v___x_1652_, 0, v___x_1656_);
v___x_1658_ = v___x_1652_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
case 20:
{
lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1672_; 
v_isSharedCheck_1672_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; 
v_unused_1673_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1673_);
v___x_1663_ = v_x_1382_;
v_isShared_1664_ = v_isSharedCheck_1672_;
goto v_resetjp_1662_;
}
else
{
lean_dec(v_x_1382_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1672_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v_time_1665_; lean_object* v_hour_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
v_time_1665_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1665_);
lean_dec_ref(v_date_1380_);
v_hour_1666_ = lean_ctor_get(v_time_1665_, 0);
lean_inc(v_hour_1666_);
lean_dec_ref(v_time_1665_);
v___x_1667_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1668_ = lean_int_emod(v_hour_1666_, v___x_1667_);
lean_dec(v_hour_1666_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set_tag(v___x_1663_, 1);
lean_ctor_set(v___x_1663_, 0, v___x_1668_);
v___x_1670_ = v___x_1663_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
case 25:
{
lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1682_; 
v_isSharedCheck_1682_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; 
v_unused_1683_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1683_);
v___x_1675_ = v_x_1382_;
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
else
{
lean_dec(v_x_1382_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_time_1677_; lean_object* v_nanosecond_1678_; lean_object* v___x_1680_; 
v_time_1677_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1677_);
lean_dec_ref(v_date_1380_);
v_nanosecond_1678_ = lean_ctor_get(v_time_1677_, 3);
lean_inc(v_nanosecond_1678_);
lean_dec_ref(v_time_1677_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set_tag(v___x_1675_, 1);
lean_ctor_set(v___x_1675_, 0, v_nanosecond_1678_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_nanosecond_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
case 26:
{
lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1692_; 
v_isSharedCheck_1692_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1693_);
v___x_1685_ = v_x_1382_;
v_isShared_1686_ = v_isSharedCheck_1692_;
goto v_resetjp_1684_;
}
else
{
lean_dec(v_x_1382_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1692_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v_time_1687_; lean_object* v___x_1688_; lean_object* v___x_1690_; 
v_time_1687_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1687_);
lean_dec_ref(v_date_1380_);
v___x_1688_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1687_);
lean_dec_ref(v_time_1687_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 1);
lean_ctor_set(v___x_1685_, 0, v___x_1688_);
v___x_1690_ = v___x_1685_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
case 28:
{
lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1702_; 
v_isSharedCheck_1702_ = !lean_is_exclusive(v_x_1382_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; 
v_unused_1703_ = lean_ctor_get(v_x_1382_, 0);
lean_dec(v_unused_1703_);
v___x_1695_ = v_x_1382_;
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
else
{
lean_dec(v_x_1382_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1702_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v_time_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v_time_1697_ = lean_ctor_get(v_date_1380_, 1);
lean_inc_ref(v_time_1697_);
lean_dec_ref(v_date_1380_);
v___x_1698_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1697_);
lean_dec_ref(v_time_1697_);
if (v_isShared_1696_ == 0)
{
lean_ctor_set_tag(v___x_1695_, 1);
lean_ctor_set(v___x_1695_, 0, v___x_1698_);
v___x_1700_ = v___x_1695_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
default: 
{
lean_object* v___x_1704_; 
lean_dec_ref(v_x_1382_);
lean_dec_ref(v_date_1380_);
v___x_1704_ = lean_box(0);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0___boxed(lean_object* v_date_1705_, lean_object* v_locale_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Std_Time_PlainDateTime_format___lam__0(v_date_1705_, v_locale_1706_, v_x_1707_);
lean_dec_ref(v_locale_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format(lean_object* v_date_1709_, lean_object* v_format_1710_, lean_object* v_locale_1711_){
_start:
{
lean_object* v___x_1712_; lean_object* v_format_1713_; 
v___x_1712_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1713_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1710_, v___x_1712_);
if (lean_obj_tag(v_format_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_dec_ref(v_locale_1711_);
lean_dec_ref(v_date_1709_);
v_a_1714_ = lean_ctor_get(v_format_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref_known(v_format_1713_, 1);
v___x_1715_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1716_ = lean_string_append(v___x_1715_, v_a_1714_);
lean_dec(v_a_1714_);
return v___x_1716_;
}
else
{
lean_object* v_a_1717_; lean_object* v___f_1718_; lean_object* v_res_1719_; 
v_a_1717_ = lean_ctor_get(v_format_1713_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v_format_1713_, 1);
v___f_1718_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1718_, 0, v_date_1709_);
lean_closure_set(v___f_1718_, 1, v_locale_1711_);
v_res_1719_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1717_, v___f_1718_);
if (lean_obj_tag(v_res_1719_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1720_;
}
else
{
lean_object* v_val_1721_; 
v_val_1721_ = lean_ctor_get(v_res_1719_, 0);
lean_inc(v_val_1721_);
lean_dec_ref_known(v_res_1719_, 1);
return v_val_1721_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1722_ = l_Std_Time_TimeZone_GMT;
v___x_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromAscTimeString(lean_object* v_input_1724_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1726_ = l_Std_Time_Formats_ascTime;
v___x_1727_ = l_Std_Time_GenericFormat_parse(v___x_1725_, v___x_1726_, v_input_1724_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1745_; 
v_a_1736_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1745_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1745_ == 0)
{
v___x_1738_ = v___x_1727_;
v_isShared_1739_ = v_isSharedCheck_1745_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1727_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1745_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v_date_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v_date_1740_ = lean_ctor_get(v_a_1736_, 0);
lean_inc_ref(v_date_1740_);
lean_dec(v_a_1736_);
v___x_1741_ = lean_thunk_get_own(v_date_1740_);
lean_dec_ref(v_date_1740_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v___x_1741_);
v___x_1743_ = v___x_1738_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0(lean_object* v_pdt_1746_, lean_object* v_x_1747_){
_start:
{
lean_inc_ref(v_pdt_1746_);
return v_pdt_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(lean_object* v_pdt_1748_, lean_object* v_x_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_Time_PlainDateTime_toAscTimeString___lam__0(v_pdt_1748_, v_x_1749_);
lean_dec_ref(v_pdt_1748_);
return v_res_1750_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1754_ = lean_int_neg(v___x_1753_);
return v___x_1754_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2(void){
_start:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_unsigned_to_nat(1000000000u);
v___x_1756_ = lean_nat_to_int(v___x_1755_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString(lean_object* v_pdt_1757_){
_start:
{
lean_object* v___x_1758_; lean_object* v_offset_1759_; lean_object* v_name_1760_; lean_object* v_abbreviation_1761_; uint8_t v_isDST_1762_; uint8_t v___x_1763_; uint8_t v___x_1764_; lean_object* v_ltt_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v_wt_1769_; lean_object* v_ltt_1770_; lean_object* v_tz_1771_; lean_object* v_offset_1772_; lean_object* v_second_1773_; lean_object* v_nano_1774_; lean_object* v___f_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1758_ = l_Std_Time_TimeZone_UTC;
v_offset_1759_ = lean_ctor_get(v___x_1758_, 0);
v_name_1760_ = lean_ctor_get(v___x_1758_, 1);
v_abbreviation_1761_ = lean_ctor_get(v___x_1758_, 2);
v_isDST_1762_ = lean_ctor_get_uint8(v___x_1758_, sizeof(void*)*3);
v___x_1763_ = 0;
v___x_1764_ = 1;
lean_inc_ref(v_name_1760_);
lean_inc_ref(v_abbreviation_1761_);
lean_inc(v_offset_1759_);
v_ltt_1765_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_1765_, 0, v_offset_1759_);
lean_ctor_set(v_ltt_1765_, 1, v_abbreviation_1761_);
lean_ctor_set(v_ltt_1765_, 2, v_name_1760_);
lean_ctor_set_uint8(v_ltt_1765_, sizeof(void*)*3, v_isDST_1762_);
lean_ctor_set_uint8(v_ltt_1765_, sizeof(void*)*3 + 1, v___x_1763_);
lean_ctor_set_uint8(v_ltt_1765_, sizeof(void*)*3 + 2, v___x_1764_);
v___x_1766_ = ((lean_object*)(l_Std_Time_PlainDateTime_toAscTimeString___closed__0));
v___x_1767_ = lean_box(0);
v___x_1768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1768_, 0, v_ltt_1765_);
lean_ctor_set(v___x_1768_, 1, v___x_1766_);
lean_ctor_set(v___x_1768_, 2, v___x_1767_);
lean_inc_ref(v_pdt_1757_);
v_wt_1769_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1757_);
lean_inc_ref(v___x_1768_);
v_ltt_1770_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1768_, v_wt_1769_);
v_tz_1771_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1770_);
lean_dec_ref(v_ltt_1770_);
v_offset_1772_ = lean_ctor_get(v_tz_1771_, 0);
lean_inc(v_offset_1772_);
v_second_1773_ = lean_ctor_get(v_wt_1769_, 0);
lean_inc(v_second_1773_);
v_nano_1774_ = lean_ctor_get(v_wt_1769_, 1);
lean_inc(v_nano_1774_);
lean_dec_ref(v_wt_1769_);
v___f_1775_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1775_, 0, v_pdt_1757_);
v___x_1776_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1777_ = l_Std_Time_Formats_ascTime;
v___x_1778_ = lean_mk_thunk(v___f_1775_);
v___x_1779_ = lean_int_neg(v_offset_1772_);
lean_dec(v_offset_1772_);
v___x_1780_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__1, &l_Std_Time_PlainDateTime_toAscTimeString___closed__1_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1);
v___x_1781_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__2, &l_Std_Time_PlainDateTime_toAscTimeString___closed__2_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2);
v___x_1782_ = lean_int_mul(v_second_1773_, v___x_1781_);
lean_dec(v_second_1773_);
v___x_1783_ = lean_int_add(v___x_1782_, v_nano_1774_);
lean_dec(v_nano_1774_);
lean_dec(v___x_1782_);
v___x_1784_ = lean_int_mul(v___x_1779_, v___x_1781_);
lean_dec(v___x_1779_);
v___x_1785_ = lean_int_add(v___x_1784_, v___x_1780_);
lean_dec(v___x_1784_);
v___x_1786_ = lean_int_add(v___x_1783_, v___x_1785_);
lean_dec(v___x_1785_);
lean_dec(v___x_1783_);
v___x_1787_ = l_Std_Time_Duration_ofNanoseconds(v___x_1786_);
lean_dec(v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1778_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
lean_ctor_set(v___x_1788_, 2, v___x_1768_);
lean_ctor_set(v___x_1788_, 3, v_tz_1771_);
v___x_1789_ = l_Std_Time_GenericFormat_format(v___x_1776_, v___x_1777_, v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLongDateFormatString(lean_object* v_input_1790_){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1792_ = l_Std_Time_Formats_longDateFormat;
v___x_1793_ = l_Std_Time_GenericFormat_parse(v___x_1791_, v___x_1792_, v_input_1790_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1793_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1793_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1811_; 
v_a_1802_ = lean_ctor_get(v___x_1793_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1793_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1804_ = v___x_1793_;
v_isShared_1805_ = v_isSharedCheck_1811_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1793_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1811_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_date_1806_; lean_object* v___x_1807_; lean_object* v___x_1809_; 
v_date_1806_ = lean_ctor_get(v_a_1802_, 0);
lean_inc_ref(v_date_1806_);
lean_dec(v_a_1802_);
v___x_1807_ = lean_thunk_get_own(v_date_1806_);
lean_dec_ref(v_date_1806_);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 0, v___x_1807_);
v___x_1809_ = v___x_1804_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLongDateFormatString(lean_object* v_pdt_1812_){
_start:
{
lean_object* v___x_1813_; lean_object* v_offset_1814_; lean_object* v_name_1815_; lean_object* v_abbreviation_1816_; uint8_t v_isDST_1817_; uint8_t v___x_1818_; uint8_t v___x_1819_; lean_object* v_ltt_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v_wt_1824_; lean_object* v_ltt_1825_; lean_object* v_tz_1826_; lean_object* v_offset_1827_; lean_object* v_second_1828_; lean_object* v_nano_1829_; lean_object* v___f_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1813_ = l_Std_Time_TimeZone_UTC;
v_offset_1814_ = lean_ctor_get(v___x_1813_, 0);
v_name_1815_ = lean_ctor_get(v___x_1813_, 1);
v_abbreviation_1816_ = lean_ctor_get(v___x_1813_, 2);
v_isDST_1817_ = lean_ctor_get_uint8(v___x_1813_, sizeof(void*)*3);
v___x_1818_ = 0;
v___x_1819_ = 1;
lean_inc_ref(v_name_1815_);
lean_inc_ref(v_abbreviation_1816_);
lean_inc(v_offset_1814_);
v_ltt_1820_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_1820_, 0, v_offset_1814_);
lean_ctor_set(v_ltt_1820_, 1, v_abbreviation_1816_);
lean_ctor_set(v_ltt_1820_, 2, v_name_1815_);
lean_ctor_set_uint8(v_ltt_1820_, sizeof(void*)*3, v_isDST_1817_);
lean_ctor_set_uint8(v_ltt_1820_, sizeof(void*)*3 + 1, v___x_1818_);
lean_ctor_set_uint8(v_ltt_1820_, sizeof(void*)*3 + 2, v___x_1819_);
v___x_1821_ = ((lean_object*)(l_Std_Time_PlainDateTime_toAscTimeString___closed__0));
v___x_1822_ = lean_box(0);
v___x_1823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1823_, 0, v_ltt_1820_);
lean_ctor_set(v___x_1823_, 1, v___x_1821_);
lean_ctor_set(v___x_1823_, 2, v___x_1822_);
lean_inc_ref(v_pdt_1812_);
v_wt_1824_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1812_);
lean_inc_ref(v___x_1823_);
v_ltt_1825_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1823_, v_wt_1824_);
v_tz_1826_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1825_);
lean_dec_ref(v_ltt_1825_);
v_offset_1827_ = lean_ctor_get(v_tz_1826_, 0);
lean_inc(v_offset_1827_);
v_second_1828_ = lean_ctor_get(v_wt_1824_, 0);
lean_inc(v_second_1828_);
v_nano_1829_ = lean_ctor_get(v_wt_1824_, 1);
lean_inc(v_nano_1829_);
lean_dec_ref(v_wt_1824_);
v___f_1830_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1830_, 0, v_pdt_1812_);
v___x_1831_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1832_ = l_Std_Time_Formats_longDateFormat;
v___x_1833_ = lean_mk_thunk(v___f_1830_);
v___x_1834_ = lean_int_neg(v_offset_1827_);
lean_dec(v_offset_1827_);
v___x_1835_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__1, &l_Std_Time_PlainDateTime_toAscTimeString___closed__1_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1);
v___x_1836_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__2, &l_Std_Time_PlainDateTime_toAscTimeString___closed__2_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2);
v___x_1837_ = lean_int_mul(v_second_1828_, v___x_1836_);
lean_dec(v_second_1828_);
v___x_1838_ = lean_int_add(v___x_1837_, v_nano_1829_);
lean_dec(v_nano_1829_);
lean_dec(v___x_1837_);
v___x_1839_ = lean_int_mul(v___x_1834_, v___x_1836_);
lean_dec(v___x_1834_);
v___x_1840_ = lean_int_add(v___x_1839_, v___x_1835_);
lean_dec(v___x_1839_);
v___x_1841_ = lean_int_add(v___x_1838_, v___x_1840_);
lean_dec(v___x_1840_);
lean_dec(v___x_1838_);
v___x_1842_ = l_Std_Time_Duration_ofNanoseconds(v___x_1841_);
lean_dec(v___x_1841_);
v___x_1843_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1833_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
lean_ctor_set(v___x_1843_, 2, v___x_1823_);
lean_ctor_set(v___x_1843_, 3, v_tz_1826_);
v___x_1844_ = l_Std_Time_GenericFormat_format(v___x_1831_, v___x_1832_, v___x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromDateTimeString(lean_object* v_input_1845_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1847_ = l_Std_Time_Formats_dateTime24Hour;
v___x_1848_ = l_Std_Time_GenericFormat_parse(v___x_1846_, v___x_1847_, v_input_1845_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1866_; 
v_a_1857_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1859_ = v___x_1848_;
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1848_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1866_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_date_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v_date_1861_ = lean_ctor_get(v_a_1857_, 0);
lean_inc_ref(v_date_1861_);
lean_dec(v_a_1857_);
v___x_1862_ = lean_thunk_get_own(v_date_1861_);
lean_dec_ref(v_date_1861_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1862_);
v___x_1864_ = v___x_1859_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toDateTimeString(lean_object* v_pdt_1867_){
_start:
{
lean_object* v_date_1868_; lean_object* v_time_1869_; lean_object* v_year_1870_; lean_object* v_month_1871_; lean_object* v_day_1872_; lean_object* v_hour_1873_; lean_object* v_minute_1874_; lean_object* v_second_1875_; lean_object* v_nanosecond_1876_; lean_object* v___x_1877_; lean_object* v___x_12__overap_1878_; lean_object* v___x_1879_; 
v_date_1868_ = lean_ctor_get(v_pdt_1867_, 0);
lean_inc_ref(v_date_1868_);
v_time_1869_ = lean_ctor_get(v_pdt_1867_, 1);
lean_inc_ref(v_time_1869_);
lean_dec_ref(v_pdt_1867_);
v_year_1870_ = lean_ctor_get(v_date_1868_, 0);
lean_inc(v_year_1870_);
v_month_1871_ = lean_ctor_get(v_date_1868_, 1);
lean_inc(v_month_1871_);
v_day_1872_ = lean_ctor_get(v_date_1868_, 2);
lean_inc(v_day_1872_);
lean_dec_ref(v_date_1868_);
v_hour_1873_ = lean_ctor_get(v_time_1869_, 0);
lean_inc(v_hour_1873_);
v_minute_1874_ = lean_ctor_get(v_time_1869_, 1);
lean_inc(v_minute_1874_);
v_second_1875_ = lean_ctor_get(v_time_1869_, 2);
lean_inc(v_second_1875_);
v_nanosecond_1876_ = lean_ctor_get(v_time_1869_, 3);
lean_inc(v_nanosecond_1876_);
lean_dec_ref(v_time_1869_);
v___x_1877_ = l_Std_Time_Formats_dateTime24Hour;
v___x_12__overap_1878_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1877_);
v___x_1879_ = lean_apply_7(v___x_12__overap_1878_, v_year_1870_, v_month_1871_, v_day_1872_, v_hour_1873_, v_minute_1874_, v_second_1875_, v_nanosecond_1876_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLeanDateTimeString(lean_object* v_input_1880_){
_start:
{
lean_object* v___y_1882_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1902_ = l_Std_Time_Formats_leanDateTime24Hour;
lean_inc_ref(v_input_1880_);
v___x_1903_ = l_Std_Time_GenericFormat_parse(v___x_1901_, v___x_1902_, v_input_1880_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec_ref_known(v___x_1903_, 1);
v___x_1904_ = l_Std_Time_Formats_leanDateTime24HourNoNanos;
v___x_1905_ = l_Std_Time_GenericFormat_parse(v___x_1901_, v___x_1904_, v_input_1880_);
v___y_1882_ = v___x_1905_;
goto v___jp_1881_;
}
else
{
lean_dec_ref(v_input_1880_);
v___y_1882_ = v___x_1903_;
goto v___jp_1881_;
}
v___jp_1881_:
{
if (lean_obj_tag(v___y_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
v_a_1883_ = lean_ctor_get(v___y_1882_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___y_1882_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___y_1882_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___y_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1900_; 
v_a_1891_ = lean_ctor_get(v___y_1882_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___y_1882_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1893_ = v___y_1882_;
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___y_1882_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1900_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_date_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v_date_1895_ = lean_ctor_get(v_a_1891_, 0);
lean_inc_ref(v_date_1895_);
lean_dec(v_a_1891_);
v___x_1896_ = lean_thunk_get_own(v_date_1895_);
lean_dec_ref(v_date_1895_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1896_);
v___x_1898_ = v___x_1893_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLeanDateTimeString(lean_object* v_pdt_1906_){
_start:
{
lean_object* v_date_1907_; lean_object* v_time_1908_; lean_object* v_year_1909_; lean_object* v_month_1910_; lean_object* v_day_1911_; lean_object* v_hour_1912_; lean_object* v_minute_1913_; lean_object* v_second_1914_; lean_object* v_nanosecond_1915_; lean_object* v___x_1916_; lean_object* v___x_12__overap_1917_; lean_object* v___x_1918_; 
v_date_1907_ = lean_ctor_get(v_pdt_1906_, 0);
lean_inc_ref(v_date_1907_);
v_time_1908_ = lean_ctor_get(v_pdt_1906_, 1);
lean_inc_ref(v_time_1908_);
lean_dec_ref(v_pdt_1906_);
v_year_1909_ = lean_ctor_get(v_date_1907_, 0);
lean_inc(v_year_1909_);
v_month_1910_ = lean_ctor_get(v_date_1907_, 1);
lean_inc(v_month_1910_);
v_day_1911_ = lean_ctor_get(v_date_1907_, 2);
lean_inc(v_day_1911_);
lean_dec_ref(v_date_1907_);
v_hour_1912_ = lean_ctor_get(v_time_1908_, 0);
lean_inc(v_hour_1912_);
v_minute_1913_ = lean_ctor_get(v_time_1908_, 1);
lean_inc(v_minute_1913_);
v_second_1914_ = lean_ctor_get(v_time_1908_, 2);
lean_inc(v_second_1914_);
v_nanosecond_1915_ = lean_ctor_get(v_time_1908_, 3);
lean_inc(v_nanosecond_1915_);
lean_dec_ref(v_time_1908_);
v___x_1916_ = l_Std_Time_Formats_leanDateTime24Hour;
v___x_12__overap_1917_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1916_);
v___x_1918_ = lean_apply_7(v___x_12__overap_1917_, v_year_1909_, v_month_1910_, v_day_1911_, v_hour_1912_, v_minute_1913_, v_second_1914_, v_nanosecond_1915_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_parse(lean_object* v_date_1919_){
_start:
{
lean_object* v___x_1920_; 
lean_inc_ref(v_date_1919_);
v___x_1920_ = l_Std_Time_PlainDateTime_fromAscTimeString(v_date_1919_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1921_; 
lean_dec_ref_known(v___x_1920_, 1);
lean_inc_ref(v_date_1919_);
v___x_1921_ = l_Std_Time_PlainDateTime_fromLongDateFormatString(v_date_1919_);
if (lean_obj_tag(v___x_1921_) == 0)
{
lean_object* v___x_1922_; 
lean_dec_ref_known(v___x_1921_, 1);
lean_inc_ref(v_date_1919_);
v___x_1922_ = l_Std_Time_PlainDateTime_fromDateTimeString(v_date_1919_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v___x_1923_; 
lean_dec_ref_known(v___x_1922_, 1);
v___x_1923_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v_date_1919_);
return v___x_1923_;
}
else
{
lean_dec_ref(v_date_1919_);
return v___x_1922_;
}
}
else
{
lean_dec_ref(v_date_1919_);
return v___x_1921_;
}
}
else
{
lean_dec_ref(v_date_1919_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0(lean_object* v_data_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1931_ = ((lean_object*)(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1));
v___x_1932_ = l_Std_Time_PlainDateTime_toLeanDateTimeString(v_data_1929_);
v___x_1933_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1931_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l_Repr_addAppParen(v___x_1936_, v___y_1930_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0___boxed(lean_object* v_data_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Std_Time_PlainDateTime_instRepr___lam__0(v_data_1938_, v___y_1939_);
lean_dec(v___y_1939_);
return v_res_1940_;
}
}
lean_object* runtime_initialize_Std_Time_Notation_Spec(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Format_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Format_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Format(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

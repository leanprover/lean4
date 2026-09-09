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
v___x_747_ = lean_unsigned_to_nat(100u);
v___x_748_ = lean_nat_to_int(v___x_747_);
return v___x_748_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__3(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(400u);
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
lean_object* v_year_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; uint8_t v___y_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
lean_dec_ref_known(v_x_753_, 1);
v_year_793_ = lean_ctor_get(v_date_751_, 0);
v___x_794_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_795_ = lean_int_mod(v_year_793_, v___x_794_);
v___x_796_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_797_ = lean_int_dec_eq(v___x_795_, v___x_796_);
lean_dec(v___x_795_);
v___x_800_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_801_ = lean_int_mod(v_year_793_, v___x_800_);
v___x_802_ = lean_int_dec_eq(v___x_801_, v___x_796_);
lean_dec(v___x_801_);
if (v___x_802_ == 0)
{
uint8_t v___x_803_; 
v___x_803_ = 1;
v___y_799_ = v___x_803_;
goto v___jp_798_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_805_ = lean_int_mod(v_year_793_, v___x_804_);
v___x_806_ = lean_int_dec_eq(v___x_805_, v___x_796_);
lean_dec(v___x_805_);
v___y_799_ = v___x_806_;
goto v___jp_798_;
}
v___jp_798_:
{
if (v___x_797_ == 0)
{
v___y_755_ = v___x_797_;
goto v___jp_754_;
}
else
{
v___y_755_ = v___y_799_;
goto v___jp_754_;
}
}
}
case 7:
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_814_; 
v_isSharedCheck_814_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_815_);
v___x_808_ = v_x_753_;
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
else
{
lean_dec(v_x_753_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_814_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = l_Std_Time_PlainDate_quarter(v_date_751_);
lean_dec_ref(v_date_751_);
if (v_isShared_809_ == 0)
{
lean_ctor_set_tag(v___x_808_, 1);
lean_ctor_set(v___x_808_, 0, v___x_810_);
v___x_812_ = v___x_808_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
case 8:
{
lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_823_; 
v_isSharedCheck_823_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_824_);
v___x_817_ = v_x_753_;
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
else
{
lean_dec(v_x_753_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_819_ = l_Std_Time_PlainDate_quarter(v_date_751_);
lean_dec_ref(v_date_751_);
if (v_isShared_818_ == 0)
{
lean_ctor_set_tag(v___x_817_, 1);
lean_ctor_set(v___x_817_, 0, v___x_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
case 10:
{
lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_834_; 
v_isSharedCheck_834_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_835_);
v___x_826_ = v_x_753_;
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
else
{
lean_dec(v_x_753_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
uint8_t v_firstDayOfWeek_828_; lean_object* v_minimalDaysInFirstWeek_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v_firstDayOfWeek_828_ = lean_ctor_get_uint8(v_locale_752_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_829_ = lean_ctor_get(v_locale_752_, 0);
v___x_830_ = l_Std_Time_PlainDate_weekOfYear(v_date_751_, v_firstDayOfWeek_828_, v_minimalDaysInFirstWeek_829_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 1);
lean_ctor_set(v___x_826_, 0, v___x_830_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
case 11:
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_844_; 
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_845_);
v___x_837_ = v_x_753_;
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_x_753_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v_firstDayOfWeek_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v_firstDayOfWeek_839_ = lean_ctor_get_uint8(v_locale_752_, sizeof(void*)*2);
v___x_840_ = l_Std_Time_PlainDate_weekOfMonth(v_date_751_, v_firstDayOfWeek_839_);
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 1);
lean_ctor_set(v___x_837_, 0, v___x_840_);
v___x_842_ = v___x_837_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
case 4:
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_isSharedCheck_853_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_854_);
v___x_847_ = v_x_753_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_x_753_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_month_849_; lean_object* v___x_851_; 
v_month_849_ = lean_ctor_get(v_date_751_, 1);
lean_inc(v_month_849_);
lean_dec_ref(v_date_751_);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 1);
lean_ctor_set(v___x_847_, 0, v_month_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_month_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
case 5:
{
lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_862_; 
v_isSharedCheck_862_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_862_ == 0)
{
lean_object* v_unused_863_; 
v_unused_863_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_863_);
v___x_856_ = v_x_753_;
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
else
{
lean_dec(v_x_753_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_862_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_month_858_; lean_object* v___x_860_; 
v_month_858_ = lean_ctor_get(v_date_751_, 1);
lean_inc(v_month_858_);
lean_dec_ref(v_date_751_);
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 1);
lean_ctor_set(v___x_856_, 0, v_month_858_);
v___x_860_ = v___x_856_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_month_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
case 6:
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_871_ == 0)
{
lean_object* v_unused_872_; 
v_unused_872_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_872_);
v___x_865_ = v_x_753_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_dec(v_x_753_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_day_867_; lean_object* v___x_869_; 
v_day_867_ = lean_ctor_get(v_date_751_, 2);
lean_inc(v_day_867_);
lean_dec_ref(v_date_751_);
if (v_isShared_866_ == 0)
{
lean_ctor_set_tag(v___x_865_, 1);
lean_ctor_set(v___x_865_, 0, v_day_867_);
v___x_869_ = v___x_865_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_day_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
case 12:
{
uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec_ref_known(v_x_753_, 0);
v___x_873_ = l_Std_Time_PlainDate_weekday(v_date_751_);
v___x_874_ = lean_box(v___x_873_);
v___x_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
case 13:
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_884_; 
v_isSharedCheck_884_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_885_);
v___x_877_ = v_x_753_;
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
else
{
lean_dec(v_x_753_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_879_ = l_Std_Time_PlainDate_weekday(v_date_751_);
v___x_880_ = lean_box(v___x_879_);
if (v_isShared_878_ == 0)
{
lean_ctor_set_tag(v___x_877_, 1);
lean_ctor_set(v___x_877_, 0, v___x_880_);
v___x_882_ = v___x_877_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
case 14:
{
lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_894_; 
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_895_);
v___x_887_ = v_x_753_;
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
else
{
lean_dec(v_x_753_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_889_ = l_Std_Time_PlainDate_weekday(v_date_751_);
v___x_890_ = lean_box(v___x_889_);
if (v_isShared_888_ == 0)
{
lean_ctor_set_tag(v___x_887_, 1);
lean_ctor_set(v___x_887_, 0, v___x_890_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
case 15:
{
lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_903_; 
v_isSharedCheck_903_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v_x_753_, 0);
lean_dec(v_unused_904_);
v___x_897_ = v_x_753_;
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
else
{
lean_dec(v_x_753_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_903_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_751_);
lean_dec_ref(v_date_751_);
if (v_isShared_898_ == 0)
{
lean_ctor_set_tag(v___x_897_, 1);
lean_ctor_set(v___x_897_, 0, v___x_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
default: 
{
lean_object* v___x_905_; 
lean_dec_ref(v_x_753_);
lean_dec_ref(v_date_751_);
v___x_905_ = lean_box(0);
return v___x_905_;
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0___boxed(lean_object* v_date_906_, lean_object* v_locale_907_, lean_object* v_x_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_Time_PlainDate_format___lam__0(v_date_906_, v_locale_907_, v_x_908_);
lean_dec_ref(v_locale_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format(lean_object* v_date_912_, lean_object* v_format_913_, lean_object* v_locale_914_){
_start:
{
lean_object* v___x_915_; lean_object* v_format_916_; 
v___x_915_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_916_ = l_Std_Time_GenericFormat_spec___redArg(v_format_913_, v___x_915_);
if (lean_obj_tag(v_format_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec_ref(v_locale_914_);
lean_dec_ref(v_date_912_);
v_a_917_ = lean_ctor_get(v_format_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v_format_916_, 1);
v___x_918_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_919_ = lean_string_append(v___x_918_, v_a_917_);
lean_dec(v_a_917_);
return v___x_919_;
}
else
{
lean_object* v_a_920_; lean_object* v___f_921_; lean_object* v_res_922_; 
v_a_920_ = lean_ctor_get(v_format_916_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v_format_916_, 1);
v___f_921_ = lean_alloc_closure((void*)(l_Std_Time_PlainDate_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_921_, 0, v_date_912_);
lean_closure_set(v___f_921_, 1, v_locale_914_);
v_res_922_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_920_, v___f_921_);
if (lean_obj_tag(v_res_922_) == 0)
{
lean_object* v___x_923_; 
v___x_923_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_923_;
}
else
{
lean_object* v_val_924_; 
v_val_924_ = lean_ctor_get(v_res_922_, 0);
lean_inc(v_val_924_);
lean_dec_ref_known(v_res_922_, 1);
return v_val_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString___lam__0(lean_object* v_m_925_, lean_object* v_d_926_, lean_object* v_y_927_){
_start:
{
uint8_t v___y_929_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; uint8_t v___y_940_; lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_935_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_936_ = lean_int_mod(v_y_927_, v___x_935_);
v___x_937_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_938_ = lean_int_dec_eq(v___x_936_, v___x_937_);
lean_dec(v___x_936_);
v___x_941_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_942_ = lean_int_mod(v_y_927_, v___x_941_);
v___x_943_ = lean_int_dec_eq(v___x_942_, v___x_937_);
lean_dec(v___x_942_);
if (v___x_943_ == 0)
{
uint8_t v___x_944_; 
v___x_944_ = 1;
v___y_940_ = v___x_944_;
goto v___jp_939_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v___x_945_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_946_ = lean_int_mod(v_y_927_, v___x_945_);
v___x_947_ = lean_int_dec_eq(v___x_946_, v___x_937_);
lean_dec(v___x_946_);
v___y_940_ = v___x_947_;
goto v___jp_939_;
}
v___jp_928_:
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = l_Std_Time_Month_Ordinal_days(v___y_929_, v_m_925_);
v___x_931_ = lean_int_dec_le(v_d_926_, v___x_930_);
lean_dec(v___x_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v_y_927_);
lean_dec(v_d_926_);
lean_dec(v_m_925_);
v___x_932_ = lean_box(0);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_933_, 0, v_y_927_);
lean_ctor_set(v___x_933_, 1, v_m_925_);
lean_ctor_set(v___x_933_, 2, v_d_926_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
v___jp_939_:
{
if (v___x_938_ == 0)
{
v___y_929_ = v___x_938_;
goto v___jp_928_;
}
else
{
v___y_929_ = v___y_940_;
goto v___jp_928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString(lean_object* v_input_949_){
_start:
{
lean_object* v___f_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___f_950_ = ((lean_object*)(l_Std_Time_PlainDate_fromAmericanDateString___closed__0));
v___x_951_ = l_Std_Time_Formats_americanDate;
v___x_952_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_951_, v___f_950_, v_input_949_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toAmericanDateString(lean_object* v_input_953_){
_start:
{
lean_object* v_year_954_; lean_object* v_month_955_; lean_object* v_day_956_; lean_object* v___x_957_; lean_object* v___x_6__overap_958_; lean_object* v___x_959_; 
v_year_954_ = lean_ctor_get(v_input_953_, 0);
lean_inc(v_year_954_);
v_month_955_ = lean_ctor_get(v_input_953_, 1);
lean_inc(v_month_955_);
v_day_956_ = lean_ctor_get(v_input_953_, 2);
lean_inc(v_day_956_);
lean_dec_ref(v_input_953_);
v___x_957_ = l_Std_Time_Formats_americanDate;
v___x_6__overap_958_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_957_);
v___x_959_ = lean_apply_3(v___x_6__overap_958_, v_month_955_, v_day_956_, v_year_954_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString___lam__0(lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
uint8_t v___y_964_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; uint8_t v___y_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_970_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_971_ = lean_int_mod(v___y_960_, v___x_970_);
v___x_972_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_973_ = lean_int_dec_eq(v___x_971_, v___x_972_);
lean_dec(v___x_971_);
v___x_976_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_977_ = lean_int_mod(v___y_960_, v___x_976_);
v___x_978_ = lean_int_dec_eq(v___x_977_, v___x_972_);
lean_dec(v___x_977_);
if (v___x_978_ == 0)
{
uint8_t v___x_979_; 
v___x_979_ = 1;
v___y_975_ = v___x_979_;
goto v___jp_974_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_981_ = lean_int_mod(v___y_960_, v___x_980_);
v___x_982_ = lean_int_dec_eq(v___x_981_, v___x_972_);
lean_dec(v___x_981_);
v___y_975_ = v___x_982_;
goto v___jp_974_;
}
v___jp_963_:
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = l_Std_Time_Month_Ordinal_days(v___y_964_, v___y_961_);
v___x_966_ = lean_int_dec_le(v___y_962_, v___x_965_);
lean_dec(v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec(v___y_962_);
lean_dec(v___y_961_);
lean_dec(v___y_960_);
v___x_967_ = lean_box(0);
return v___x_967_;
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_968_, 0, v___y_960_);
lean_ctor_set(v___x_968_, 1, v___y_961_);
lean_ctor_set(v___x_968_, 2, v___y_962_);
v___x_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
v___jp_974_:
{
if (v___x_973_ == 0)
{
v___y_964_ = v___x_973_;
goto v___jp_963_;
}
else
{
v___y_964_ = v___y_975_;
goto v___jp_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString(lean_object* v_input_984_){
_start:
{
lean_object* v___f_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___f_985_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_986_ = l_Std_Time_Formats_sqlDate;
v___x_987_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_986_, v___f_985_, v_input_984_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toSQLDateString(lean_object* v_input_988_){
_start:
{
lean_object* v_year_989_; lean_object* v_month_990_; lean_object* v_day_991_; lean_object* v___x_992_; lean_object* v___x_6__overap_993_; lean_object* v___x_994_; 
v_year_989_ = lean_ctor_get(v_input_988_, 0);
lean_inc(v_year_989_);
v_month_990_ = lean_ctor_get(v_input_988_, 1);
lean_inc(v_month_990_);
v_day_991_ = lean_ctor_get(v_input_988_, 2);
lean_inc(v_day_991_);
lean_dec_ref(v_input_988_);
v___x_992_ = l_Std_Time_Formats_sqlDate;
v___x_6__overap_993_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_992_);
v___x_994_ = lean_apply_3(v___x_6__overap_993_, v_year_989_, v_month_990_, v_day_991_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromLeanDateString(lean_object* v_input_995_){
_start:
{
lean_object* v___f_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___f_996_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_997_ = l_Std_Time_Formats_leanDate;
v___x_998_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_997_, v___f_996_, v_input_995_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toLeanDateString(lean_object* v_input_999_){
_start:
{
lean_object* v_year_1000_; lean_object* v_month_1001_; lean_object* v_day_1002_; lean_object* v___x_1003_; lean_object* v___x_6__overap_1004_; lean_object* v___x_1005_; 
v_year_1000_ = lean_ctor_get(v_input_999_, 0);
lean_inc(v_year_1000_);
v_month_1001_ = lean_ctor_get(v_input_999_, 1);
lean_inc(v_month_1001_);
v_day_1002_ = lean_ctor_get(v_input_999_, 2);
lean_inc(v_day_1002_);
lean_dec_ref(v_input_999_);
v___x_1003_ = l_Std_Time_Formats_leanDate;
v___x_6__overap_1004_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1003_);
v___x_1005_ = lean_apply_3(v___x_6__overap_1004_, v_year_1000_, v_month_1001_, v_day_1002_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_parse(lean_object* v_input_1006_){
_start:
{
lean_object* v___x_1007_; 
lean_inc_ref(v_input_1006_);
v___x_1007_ = l_Std_Time_PlainDate_fromAmericanDateString(v_input_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v___x_1008_; 
lean_dec_ref_known(v___x_1007_, 1);
v___x_1008_ = l_Std_Time_PlainDate_fromSQLDateString(v_input_1006_);
return v___x_1008_;
}
else
{
lean_dec_ref(v_input_1006_);
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0(lean_object* v_data_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1019_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__1));
v___x_1020_ = l_Std_Time_PlainDate_toLeanDateString(v_data_1017_);
v___x_1021_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1019_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l_Repr_addAppParen(v___x_1024_, v___y_1018_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0___boxed(lean_object* v_data_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Std_Time_PlainDate_instRepr___lam__0(v_data_1026_, v___y_1027_);
lean_dec(v___y_1027_);
return v_res_1028_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_unsigned_to_nat(12u);
v___x_1032_ = lean_nat_to_int(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0(lean_object* v_time_1033_, lean_object* v_x_1034_){
_start:
{
switch(lean_obj_tag(v_x_1034_))
{
case 22:
{
lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1042_; 
v_isSharedCheck_1042_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1043_);
v___x_1036_ = v_x_1034_;
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
else
{
lean_dec(v_x_1034_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_hour_1038_; lean_object* v___x_1040_; 
v_hour_1038_ = lean_ctor_get(v_time_1033_, 0);
lean_inc(v_hour_1038_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 1);
lean_ctor_set(v___x_1036_, 0, v_hour_1038_);
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_hour_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
case 21:
{
lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1052_; 
v_isSharedCheck_1052_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1053_);
v___x_1045_ = v_x_1034_;
v_isShared_1046_ = v_isSharedCheck_1052_;
goto v_resetjp_1044_;
}
else
{
lean_dec(v_x_1034_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1052_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v_hour_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v_hour_1047_ = lean_ctor_get(v_time_1033_, 0);
v___x_1048_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1047_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set_tag(v___x_1045_, 1);
lean_ctor_set(v___x_1045_, 0, v___x_1048_);
v___x_1050_ = v___x_1045_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
case 23:
{
lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_isSharedCheck_1061_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; 
v_unused_1062_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1062_);
v___x_1055_ = v_x_1034_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_dec(v_x_1034_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_minute_1057_; lean_object* v___x_1059_; 
v_minute_1057_ = lean_ctor_get(v_time_1033_, 1);
lean_inc(v_minute_1057_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set_tag(v___x_1055_, 1);
lean_ctor_set(v___x_1055_, 0, v_minute_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_minute_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
case 27:
{
lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1070_; 
v_isSharedCheck_1070_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; 
v_unused_1071_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1071_);
v___x_1064_ = v_x_1034_;
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
else
{
lean_dec(v_x_1034_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1070_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v_nanosecond_1066_; lean_object* v___x_1068_; 
v_nanosecond_1066_ = lean_ctor_get(v_time_1033_, 3);
lean_inc(v_nanosecond_1066_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set_tag(v___x_1064_, 1);
lean_ctor_set(v___x_1064_, 0, v_nanosecond_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_nanosecond_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
case 24:
{
lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1079_; 
v_isSharedCheck_1079_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1080_);
v___x_1073_ = v_x_1034_;
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
else
{
lean_dec(v_x_1034_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1079_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v_second_1075_; lean_object* v___x_1077_; 
v_second_1075_ = lean_ctor_get(v_time_1033_, 2);
lean_inc(v_second_1075_);
if (v_isShared_1074_ == 0)
{
lean_ctor_set_tag(v___x_1073_, 1);
lean_ctor_set(v___x_1073_, 0, v_second_1075_);
v___x_1077_ = v___x_1073_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_second_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
case 16:
{
lean_object* v_hour_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref_known(v_x_1034_, 0);
v_hour_1081_ = lean_ctor_get(v_time_1033_, 0);
v___x_1082_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1081_);
v___x_1083_ = lean_box(v___x_1082_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
case 17:
{
lean_object* v_hour_1085_; lean_object* v_minute_1086_; lean_object* v_second_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec_ref_known(v_x_1034_, 0);
v_hour_1085_ = lean_ctor_get(v_time_1033_, 0);
v_minute_1086_ = lean_ctor_get(v_time_1033_, 1);
v_second_1087_ = lean_ctor_get(v_time_1033_, 2);
v___x_1088_ = l_Std_Time_classifyDayPeriod(v_hour_1085_, v_minute_1086_, v_second_1087_);
v___x_1089_ = lean_box(v___x_1088_);
v___x_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
return v___x_1090_;
}
case 18:
{
lean_object* v_hour_1091_; lean_object* v_minute_1092_; lean_object* v_second_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec_ref_known(v_x_1034_, 0);
v_hour_1091_ = lean_ctor_get(v_time_1033_, 0);
v_minute_1092_ = lean_ctor_get(v_time_1033_, 1);
v_second_1093_ = lean_ctor_get(v_time_1033_, 2);
v___x_1094_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1091_, v_minute_1092_, v_second_1093_);
v___x_1095_ = lean_box(v___x_1094_);
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
case 19:
{
lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1105_; 
v_isSharedCheck_1105_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1106_);
v___x_1098_ = v_x_1034_;
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
else
{
lean_dec(v_x_1034_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_hour_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v_hour_1100_ = lean_ctor_get(v_time_1033_, 0);
v___x_1101_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1100_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 1);
lean_ctor_set(v___x_1098_, 0, v___x_1101_);
v___x_1103_ = v___x_1098_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
case 20:
{
lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1116_; 
v_isSharedCheck_1116_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1116_ == 0)
{
lean_object* v_unused_1117_; 
v_unused_1117_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1117_);
v___x_1108_ = v_x_1034_;
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
else
{
lean_dec(v_x_1034_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1116_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_hour_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v_hour_1110_ = lean_ctor_get(v_time_1033_, 0);
v___x_1111_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1112_ = lean_int_emod(v_hour_1110_, v___x_1111_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 1);
lean_ctor_set(v___x_1108_, 0, v___x_1112_);
v___x_1114_ = v___x_1108_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
case 25:
{
lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1125_; 
v_isSharedCheck_1125_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1126_);
v___x_1119_ = v_x_1034_;
v_isShared_1120_ = v_isSharedCheck_1125_;
goto v_resetjp_1118_;
}
else
{
lean_dec(v_x_1034_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1125_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v_nanosecond_1121_; lean_object* v___x_1123_; 
v_nanosecond_1121_ = lean_ctor_get(v_time_1033_, 3);
lean_inc(v_nanosecond_1121_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 1);
lean_ctor_set(v___x_1119_, 0, v_nanosecond_1121_);
v___x_1123_ = v___x_1119_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_nanosecond_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
case 26:
{
lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v_isSharedCheck_1134_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1134_ == 0)
{
lean_object* v_unused_1135_; 
v_unused_1135_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1135_);
v___x_1128_ = v_x_1034_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_dec(v_x_1034_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1033_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set_tag(v___x_1128_, 1);
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
case 28:
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_isSharedCheck_1143_ = !lean_is_exclusive(v_x_1034_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v_x_1034_, 0);
lean_dec(v_unused_1144_);
v___x_1137_ = v_x_1034_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v_x_1034_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1033_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 1);
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
default: 
{
lean_object* v___x_1145_; 
lean_dec_ref(v_x_1034_);
v___x_1145_ = lean_box(0);
return v___x_1145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0___boxed(lean_object* v_time_1146_, lean_object* v_x_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_Time_PlainTime_format___lam__0(v_time_1146_, v_x_1147_);
lean_dec_ref(v_time_1146_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format(lean_object* v_time_1149_, lean_object* v_format_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v_format_1152_; 
v___x_1151_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1152_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1150_, v___x_1151_);
if (lean_obj_tag(v_format_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec_ref(v_time_1149_);
v_a_1153_ = lean_ctor_get(v_format_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref_known(v_format_1152_, 1);
v___x_1154_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1155_ = lean_string_append(v___x_1154_, v_a_1153_);
lean_dec(v_a_1153_);
return v___x_1155_;
}
else
{
lean_object* v_a_1156_; lean_object* v___f_1157_; lean_object* v_res_1158_; 
v_a_1156_ = lean_ctor_get(v_format_1152_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v_format_1152_, 1);
v___f_1157_ = lean_alloc_closure((void*)(l_Std_Time_PlainTime_format___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1157_, 0, v_time_1149_);
v_res_1158_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1156_, v___f_1157_);
if (lean_obj_tag(v_res_1158_) == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1159_;
}
else
{
lean_object* v_val_1160_; 
v_val_1160_ = lean_ctor_get(v_res_1158_, 0);
lean_inc(v_val_1160_);
lean_dec_ref_known(v_res_1158_, 1);
return v_val_1160_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_unsigned_to_nat(1000000000u);
v___x_1162_ = lean_unsigned_to_nat(0u);
v___x_1163_ = lean_nat_mod(v___x_1162_, v___x_1161_);
return v___x_1163_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0);
v___x_1165_ = lean_nat_to_int(v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour___lam__0(lean_object* v_h_1166_, lean_object* v_m_1167_, lean_object* v_s_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1);
v___x_1170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1170_, 0, v_h_1166_);
lean_ctor_set(v___x_1170_, 1, v_m_1167_);
lean_ctor_set(v___x_1170_, 2, v_s_1168_);
lean_ctor_set(v___x_1170_, 3, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour(lean_object* v_input_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___f_1174_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1175_ = l_Std_Time_Formats_time24Hour;
v___x_1176_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1175_, v___f_1174_, v_input_1173_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime24Hour(lean_object* v_input_1177_){
_start:
{
lean_object* v_hour_1178_; lean_object* v_minute_1179_; lean_object* v_second_1180_; lean_object* v___x_1181_; lean_object* v___x_6__overap_1182_; lean_object* v___x_1183_; 
v_hour_1178_ = lean_ctor_get(v_input_1177_, 0);
lean_inc(v_hour_1178_);
v_minute_1179_ = lean_ctor_get(v_input_1177_, 1);
lean_inc(v_minute_1179_);
v_second_1180_ = lean_ctor_get(v_input_1177_, 2);
lean_inc(v_second_1180_);
lean_dec_ref(v_input_1177_);
v___x_1181_ = l_Std_Time_Formats_time24Hour;
v___x_6__overap_1182_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1181_);
v___x_1183_ = lean_apply_3(v___x_6__overap_1182_, v_hour_1178_, v_minute_1179_, v_second_1180_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0(lean_object* v_h_1184_, lean_object* v_m_1185_, lean_object* v_s_1186_, lean_object* v_n_1187_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1188_, 0, v_h_1184_);
lean_ctor_set(v___x_1188_, 1, v_m_1185_);
lean_ctor_set(v___x_1188_, 2, v_s_1186_);
lean_ctor_set(v___x_1188_, 3, v_n_1187_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour(lean_object* v_input_1191_){
_start:
{
lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___f_1192_ = ((lean_object*)(l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0));
v___x_1193_ = l_Std_Time_Formats_leanTime24Hour;
lean_inc_ref(v_input_1191_);
v___x_1194_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1193_, v___f_1192_, v_input_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
lean_dec_ref_known(v___x_1194_, 1);
v___f_1195_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1196_ = l_Std_Time_Formats_leanTime24HourNoNanos;
v___x_1197_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1196_, v___f_1195_, v_input_1191_);
return v___x_1197_;
}
else
{
lean_dec_ref(v_input_1191_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toLeanTime24Hour(lean_object* v_input_1198_){
_start:
{
lean_object* v_hour_1199_; lean_object* v_minute_1200_; lean_object* v_second_1201_; lean_object* v_nanosecond_1202_; lean_object* v___x_1203_; lean_object* v___x_7__overap_1204_; lean_object* v___x_1205_; 
v_hour_1199_ = lean_ctor_get(v_input_1198_, 0);
lean_inc(v_hour_1199_);
v_minute_1200_ = lean_ctor_get(v_input_1198_, 1);
lean_inc(v_minute_1200_);
v_second_1201_ = lean_ctor_get(v_input_1198_, 2);
lean_inc(v_second_1201_);
v_nanosecond_1202_ = lean_ctor_get(v_input_1198_, 3);
lean_inc(v_nanosecond_1202_);
lean_dec_ref(v_input_1198_);
v___x_1203_ = l_Std_Time_Formats_leanTime24Hour;
v___x_7__overap_1204_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1203_);
v___x_1205_ = lean_apply_4(v___x_7__overap_1204_, v_hour_1199_, v_minute_1200_, v_second_1201_, v_nanosecond_1202_);
return v___x_1205_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_to_int(v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0(lean_object* v_h_1208_, lean_object* v_m_1209_, lean_object* v_s_1210_, uint8_t v_a_1211_){
_start:
{
uint8_t v___y_1213_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1220_ = lean_int_dec_le(v___x_1219_, v_h_1208_);
if (v___x_1220_ == 0)
{
v___y_1213_ = v___x_1220_;
goto v___jp_1212_;
}
else
{
lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1221_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1222_ = lean_int_dec_le(v_h_1208_, v___x_1221_);
v___y_1213_ = v___x_1222_;
goto v___jp_1212_;
}
v___jp_1212_:
{
if (v___y_1213_ == 0)
{
lean_object* v___x_1214_; 
lean_dec(v_s_1210_);
lean_dec(v_m_1209_);
v___x_1214_ = lean_box(0);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1215_ = l_Std_Time_HourMarker_toAbsolute(v_a_1211_, v_h_1208_);
v___x_1216_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1);
v___x_1217_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v_m_1209_);
lean_ctor_set(v___x_1217_, 2, v_s_1210_);
lean_ctor_set(v___x_1217_, 3, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
return v___x_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed(lean_object* v_h_1223_, lean_object* v_m_1224_, lean_object* v_s_1225_, lean_object* v_a_1226_){
_start:
{
uint8_t v_a_boxed_1227_; lean_object* v_res_1228_; 
v_a_boxed_1227_ = lean_unbox(v_a_1226_);
v_res_1228_ = l_Std_Time_PlainTime_fromTime12Hour___lam__0(v_h_1223_, v_m_1224_, v_s_1225_, v_a_boxed_1227_);
lean_dec(v_h_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour(lean_object* v_input_1230_){
_start:
{
lean_object* v_builder_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_builder_1231_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime12Hour___closed__0));
v___x_1232_ = l_Std_Time_Formats_time12Hour;
v___x_1233_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1232_, v_builder_1231_, v_input_1230_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime12Hour(lean_object* v_input_1234_){
_start:
{
lean_object* v_hour_1235_; lean_object* v_minute_1236_; lean_object* v_second_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; 
v_hour_1235_ = lean_ctor_get(v_input_1234_, 0);
lean_inc(v_hour_1235_);
v_minute_1236_ = lean_ctor_get(v_input_1234_, 1);
lean_inc(v_minute_1236_);
v_second_1237_ = lean_ctor_get(v_input_1234_, 2);
lean_inc(v_second_1237_);
lean_dec_ref(v_input_1234_);
v___x_1238_ = l_Std_Time_Formats_time12Hour;
v___x_1239_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1240_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1241_ = lean_int_emod(v_hour_1235_, v___x_1239_);
v___x_1242_ = lean_int_add(v___x_1241_, v___x_1240_);
lean_dec(v___x_1241_);
v___x_1243_ = lean_int_dec_le(v___x_1239_, v_hour_1235_);
lean_dec(v_hour_1235_);
if (v___x_1243_ == 0)
{
uint8_t v___x_1244_; lean_object* v___x_55__overap_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1244_ = 0;
v___x_55__overap_1245_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1238_);
v___x_1246_ = lean_box(v___x_1244_);
v___x_1247_ = lean_apply_4(v___x_55__overap_1245_, v___x_1242_, v_minute_1236_, v_second_1237_, v___x_1246_);
return v___x_1247_;
}
else
{
uint8_t v___x_1248_; lean_object* v___x_56__overap_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1248_ = 1;
v___x_56__overap_1249_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1238_);
v___x_1250_ = lean_box(v___x_1248_);
v___x_1251_ = lean_apply_4(v___x_56__overap_1249_, v___x_1242_, v_minute_1236_, v_second_1237_, v___x_1250_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_parse(lean_object* v_input_1252_){
_start:
{
lean_object* v___x_1253_; 
lean_inc_ref(v_input_1252_);
v___x_1253_ = l_Std_Time_PlainTime_fromTime12Hour(v_input_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1254_; 
lean_dec_ref_known(v___x_1253_, 1);
v___x_1254_ = l_Std_Time_PlainTime_fromTime24Hour(v_input_1252_);
return v___x_1254_;
}
else
{
lean_dec_ref(v_input_1252_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0(lean_object* v_data_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1262_ = ((lean_object*)(l_Std_Time_PlainTime_instRepr___lam__0___closed__1));
v___x_1263_ = l_Std_Time_PlainTime_toLeanTime24Hour(v_data_1260_);
v___x_1264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
v___x_1265_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1262_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1267_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1265_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Repr_addAppParen(v___x_1267_, v___y_1261_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0___boxed(lean_object* v_data_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Std_Time_PlainTime_instRepr___lam__0(v_data_1269_, v___y_1270_);
lean_dec(v___y_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format(lean_object* v_data_1274_, lean_object* v_format_1275_){
_start:
{
lean_object* v___x_1276_; lean_object* v_format_1277_; 
v___x_1276_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1277_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1275_, v___x_1276_);
if (lean_obj_tag(v_format_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec_ref(v_data_1274_);
v_a_1278_ = lean_ctor_get(v_format_1277_, 0);
lean_inc(v_a_1278_);
lean_dec_ref_known(v_format_1277_, 1);
v___x_1279_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1280_ = lean_string_append(v___x_1279_, v_a_1278_);
lean_dec(v_a_1278_);
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_a_1281_ = lean_ctor_get(v_format_1277_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v_format_1277_, 1);
v___x_1282_ = lean_box(1);
v___x_1283_ = l_Std_Time_GenericFormat_format(v___x_1282_, v_a_1281_, v_data_1274_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromISO8601String(lean_object* v_input_1284_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_box(1);
v___x_1286_ = l_Std_Time_Formats_iso8601;
v___x_1287_ = l_Std_Time_GenericFormat_parse(v___x_1285_, v___x_1286_, v_input_1284_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String(lean_object* v_date_1288_){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_box(1);
v___x_1290_ = l_Std_Time_Formats_iso8601;
v___x_1291_ = l_Std_Time_GenericFormat_format(v___x_1289_, v___x_1290_, v_date_1288_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC822String(lean_object* v_input_1292_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_box(1);
v___x_1294_ = l_Std_Time_Formats_rfc822;
v___x_1295_ = l_Std_Time_GenericFormat_parse(v___x_1293_, v___x_1294_, v_input_1292_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String(lean_object* v_date_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = lean_box(1);
v___x_1298_ = l_Std_Time_Formats_rfc822;
v___x_1299_ = l_Std_Time_GenericFormat_format(v___x_1297_, v___x_1298_, v_date_1296_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC850String(lean_object* v_input_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_box(1);
v___x_1302_ = l_Std_Time_Formats_rfc850;
v___x_1303_ = l_Std_Time_GenericFormat_parse(v___x_1301_, v___x_1302_, v_input_1300_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String(lean_object* v_date_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_box(1);
v___x_1306_ = l_Std_Time_Formats_rfc850;
v___x_1307_ = l_Std_Time_GenericFormat_format(v___x_1305_, v___x_1306_, v_date_1304_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromDateTimeWithZoneString(lean_object* v_input_1308_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_box(1);
v___x_1310_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1311_ = l_Std_Time_GenericFormat_parse(v___x_1309_, v___x_1310_, v_input_1308_);
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString(lean_object* v_pdt_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = lean_box(1);
v___x_1314_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1315_ = l_Std_Time_GenericFormat_format(v___x_1313_, v___x_1314_, v_pdt_1312_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithZoneString(lean_object* v_input_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1317_ = lean_box(1);
v___x_1318_ = l_Std_Time_Formats_leanDateTimeWithZone;
lean_inc_ref(v_input_1316_);
v___x_1319_ = l_Std_Time_GenericFormat_parse(v___x_1317_, v___x_1318_, v_input_1316_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref_known(v___x_1319_, 1);
v___x_1320_ = l_Std_Time_Formats_leanDateTimeWithZoneNoNanos;
v___x_1321_ = l_Std_Time_GenericFormat_parse(v___x_1317_, v___x_1320_, v_input_1316_);
return v___x_1321_;
}
else
{
lean_dec_ref(v_input_1316_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(lean_object* v_input_1322_){
_start:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v___x_1323_ = lean_box(1);
v___x_1324_ = l_Std_Time_Formats_leanDateTimeWithIdentifier;
lean_inc_ref(v_input_1322_);
v___x_1325_ = l_Std_Time_GenericFormat_parse(v___x_1323_, v___x_1324_, v_input_1322_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec_ref_known(v___x_1325_, 1);
v___x_1326_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_1327_ = l_Std_Time_GenericFormat_parse(v___x_1323_, v___x_1326_, v_input_1322_);
return v___x_1327_;
}
else
{
lean_dec_ref(v_input_1322_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString(lean_object* v_zdt_1328_){
_start:
{
lean_object* v_date_1329_; lean_object* v_timezone_1330_; lean_object* v___x_1331_; lean_object* v_date_1332_; lean_object* v_time_1333_; lean_object* v_year_1334_; lean_object* v_month_1335_; lean_object* v_day_1336_; lean_object* v_hour_1337_; lean_object* v_minute_1338_; lean_object* v_second_1339_; lean_object* v_nanosecond_1340_; lean_object* v_offset_1341_; lean_object* v___x_1342_; lean_object* v___x_14__overap_1343_; lean_object* v___x_1344_; 
v_date_1329_ = lean_ctor_get(v_zdt_1328_, 0);
lean_inc_ref(v_date_1329_);
v_timezone_1330_ = lean_ctor_get(v_zdt_1328_, 3);
lean_inc_ref(v_timezone_1330_);
lean_dec_ref(v_zdt_1328_);
v___x_1331_ = lean_thunk_get_own(v_date_1329_);
lean_dec_ref(v_date_1329_);
v_date_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc_ref(v_date_1332_);
v_time_1333_ = lean_ctor_get(v___x_1331_, 1);
lean_inc_ref(v_time_1333_);
lean_dec(v___x_1331_);
v_year_1334_ = lean_ctor_get(v_date_1332_, 0);
lean_inc(v_year_1334_);
v_month_1335_ = lean_ctor_get(v_date_1332_, 1);
lean_inc(v_month_1335_);
v_day_1336_ = lean_ctor_get(v_date_1332_, 2);
lean_inc(v_day_1336_);
lean_dec_ref(v_date_1332_);
v_hour_1337_ = lean_ctor_get(v_time_1333_, 0);
lean_inc(v_hour_1337_);
v_minute_1338_ = lean_ctor_get(v_time_1333_, 1);
lean_inc(v_minute_1338_);
v_second_1339_ = lean_ctor_get(v_time_1333_, 2);
lean_inc(v_second_1339_);
v_nanosecond_1340_ = lean_ctor_get(v_time_1333_, 3);
lean_inc(v_nanosecond_1340_);
lean_dec_ref(v_time_1333_);
v_offset_1341_ = lean_ctor_get(v_timezone_1330_, 0);
lean_inc(v_offset_1341_);
lean_dec_ref(v_timezone_1330_);
v___x_1342_ = l_Std_Time_Formats_leanDateTimeWithZone;
v___x_14__overap_1343_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1342_);
v___x_1344_ = lean_apply_8(v___x_14__overap_1343_, v_year_1334_, v_month_1335_, v_day_1336_, v_hour_1337_, v_minute_1338_, v_second_1339_, v_nanosecond_1340_, v_offset_1341_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithIdentifierString(lean_object* v_zdt_1345_){
_start:
{
lean_object* v_date_1346_; lean_object* v_timezone_1347_; lean_object* v___x_1348_; lean_object* v_date_1349_; lean_object* v_time_1350_; lean_object* v_year_1351_; lean_object* v_month_1352_; lean_object* v_day_1353_; lean_object* v_hour_1354_; lean_object* v_minute_1355_; lean_object* v_second_1356_; lean_object* v_nanosecond_1357_; lean_object* v_name_1358_; lean_object* v___x_1359_; lean_object* v___x_15__overap_1360_; lean_object* v___x_1361_; 
v_date_1346_ = lean_ctor_get(v_zdt_1345_, 0);
lean_inc_ref(v_date_1346_);
v_timezone_1347_ = lean_ctor_get(v_zdt_1345_, 3);
lean_inc_ref(v_timezone_1347_);
lean_dec_ref(v_zdt_1345_);
v___x_1348_ = lean_thunk_get_own(v_date_1346_);
lean_dec_ref(v_date_1346_);
v_date_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc_ref(v_date_1349_);
v_time_1350_ = lean_ctor_get(v___x_1348_, 1);
lean_inc_ref(v_time_1350_);
lean_dec(v___x_1348_);
v_year_1351_ = lean_ctor_get(v_date_1349_, 0);
lean_inc(v_year_1351_);
v_month_1352_ = lean_ctor_get(v_date_1349_, 1);
lean_inc(v_month_1352_);
v_day_1353_ = lean_ctor_get(v_date_1349_, 2);
lean_inc(v_day_1353_);
lean_dec_ref(v_date_1349_);
v_hour_1354_ = lean_ctor_get(v_time_1350_, 0);
lean_inc(v_hour_1354_);
v_minute_1355_ = lean_ctor_get(v_time_1350_, 1);
lean_inc(v_minute_1355_);
v_second_1356_ = lean_ctor_get(v_time_1350_, 2);
lean_inc(v_second_1356_);
v_nanosecond_1357_ = lean_ctor_get(v_time_1350_, 3);
lean_inc(v_nanosecond_1357_);
lean_dec_ref(v_time_1350_);
v_name_1358_ = lean_ctor_get(v_timezone_1347_, 1);
lean_inc_ref(v_name_1358_);
lean_dec_ref(v_timezone_1347_);
v___x_1359_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_15__overap_1360_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1359_);
v___x_1361_ = lean_apply_8(v___x_15__overap_1360_, v_year_1351_, v_month_1352_, v_day_1353_, v_hour_1354_, v_minute_1355_, v_second_1356_, v_nanosecond_1357_, v_name_1358_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_parse(lean_object* v_input_1362_){
_start:
{
lean_object* v___x_1363_; 
lean_inc_ref(v_input_1362_);
v___x_1363_ = l_Std_Time_DateTime_fromISO8601String(v_input_1362_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v___x_1364_; 
lean_dec_ref_known(v___x_1363_, 1);
lean_inc_ref(v_input_1362_);
v___x_1364_ = l_Std_Time_DateTime_fromRFC822String(v_input_1362_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v___x_1365_; 
lean_dec_ref_known(v___x_1364_, 1);
lean_inc_ref(v_input_1362_);
v___x_1365_ = l_Std_Time_DateTime_fromRFC850String(v_input_1362_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref_known(v___x_1365_, 1);
lean_inc_ref(v_input_1362_);
v___x_1366_ = l_Std_Time_DateTime_fromDateTimeWithZoneString(v_input_1362_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1367_; 
lean_dec_ref_known(v___x_1366_, 1);
v___x_1367_ = l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(v_input_1362_);
return v___x_1367_;
}
else
{
lean_dec_ref(v_input_1362_);
return v___x_1366_;
}
}
else
{
lean_dec_ref(v_input_1362_);
return v___x_1365_;
}
}
else
{
lean_dec_ref(v_input_1362_);
return v___x_1364_;
}
}
else
{
lean_dec_ref(v_input_1362_);
return v___x_1363_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0(lean_object* v_data_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1375_ = ((lean_object*)(l_Std_Time_DateTime_instRepr___lam__0___closed__1));
v___x_1376_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_data_1373_);
v___x_1377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1376_);
v___x_1378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1375_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1381_ = l_Repr_addAppParen(v___x_1380_, v___y_1374_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0___boxed(lean_object* v_data_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Std_Time_DateTime_instRepr___lam__0(v_data_1382_, v___y_1383_);
lean_dec(v___y_1383_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0(lean_object* v_date_1387_, lean_object* v_locale_1388_, lean_object* v_x_1389_){
_start:
{
switch(lean_obj_tag(v_x_1389_))
{
case 0:
{
lean_object* v_date_1390_; lean_object* v_year_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
lean_dec_ref_known(v_x_1389_, 0);
v_date_1390_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1390_);
lean_dec_ref(v_date_1387_);
v_year_1391_ = lean_ctor_get(v_date_1390_, 0);
lean_inc(v_year_1391_);
lean_dec_ref(v_date_1390_);
v___x_1392_ = l_Std_Time_Year_Offset_era(v_year_1391_);
lean_dec(v_year_1391_);
v___x_1393_ = lean_box(v___x_1392_);
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
return v___x_1394_;
}
case 2:
{
lean_object* v___x_1396_; uint8_t v_isShared_1397_; uint8_t v_isSharedCheck_1403_; 
v_isSharedCheck_1403_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1404_);
v___x_1396_ = v_x_1389_;
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
else
{
lean_dec(v_x_1389_);
v___x_1396_ = lean_box(0);
v_isShared_1397_ = v_isSharedCheck_1403_;
goto v_resetjp_1395_;
}
v_resetjp_1395_:
{
lean_object* v_date_1398_; lean_object* v_year_1399_; lean_object* v___x_1401_; 
v_date_1398_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1398_);
lean_dec_ref(v_date_1387_);
v_year_1399_ = lean_ctor_get(v_date_1398_, 0);
lean_inc(v_year_1399_);
lean_dec_ref(v_date_1398_);
if (v_isShared_1397_ == 0)
{
lean_ctor_set_tag(v___x_1396_, 1);
lean_ctor_set(v___x_1396_, 0, v_year_1399_);
v___x_1401_ = v___x_1396_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_year_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
case 1:
{
lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1413_; 
v_isSharedCheck_1413_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1414_);
v___x_1406_ = v_x_1389_;
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
else
{
lean_dec(v_x_1389_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_date_1408_; lean_object* v_year_1409_; lean_object* v___x_1411_; 
v_date_1408_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1408_);
lean_dec_ref(v_date_1387_);
v_year_1409_ = lean_ctor_get(v_date_1408_, 0);
lean_inc(v_year_1409_);
lean_dec_ref(v_date_1408_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v_year_1409_);
v___x_1411_ = v___x_1406_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_year_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
case 9:
{
lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1425_; 
v_isSharedCheck_1425_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1425_ == 0)
{
lean_object* v_unused_1426_; 
v_unused_1426_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1426_);
v___x_1416_ = v_x_1389_;
v_isShared_1417_ = v_isSharedCheck_1425_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v_x_1389_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1425_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
uint8_t v_firstDayOfWeek_1418_; lean_object* v_minimalDaysInFirstWeek_1419_; lean_object* v_date_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v_firstDayOfWeek_1418_ = lean_ctor_get_uint8(v_locale_1388_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1419_ = lean_ctor_get(v_locale_1388_, 0);
v_date_1420_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1420_);
lean_dec_ref(v_date_1387_);
v___x_1421_ = l_Std_Time_PlainDate_weekYear(v_date_1420_, v_firstDayOfWeek_1418_, v_minimalDaysInFirstWeek_1419_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 1);
lean_ctor_set(v___x_1416_, 0, v___x_1421_);
v___x_1423_ = v___x_1416_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
}
case 3:
{
lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1463_; 
v_isSharedCheck_1463_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1464_);
v___x_1428_ = v_x_1389_;
v_isShared_1429_ = v_isSharedCheck_1463_;
goto v_resetjp_1427_;
}
else
{
lean_dec(v_x_1389_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1463_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v_date_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1461_; 
v_date_1430_ = lean_ctor_get(v_date_1387_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_date_1387_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_date_1387_, 1);
lean_dec(v_unused_1462_);
v___x_1432_ = v_date_1387_;
v_isShared_1433_ = v_isSharedCheck_1461_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_date_1430_);
lean_dec(v_date_1387_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1461_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v_year_1434_; lean_object* v_month_1435_; lean_object* v_day_1436_; uint8_t v___y_1438_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; uint8_t v___y_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_year_1434_ = lean_ctor_get(v_date_1430_, 0);
lean_inc(v_year_1434_);
v_month_1435_ = lean_ctor_get(v_date_1430_, 1);
lean_inc(v_month_1435_);
v_day_1436_ = lean_ctor_get(v_date_1430_, 2);
lean_inc(v_day_1436_);
lean_dec_ref(v_date_1430_);
v___x_1448_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1449_ = lean_int_mod(v_year_1434_, v___x_1448_);
v___x_1450_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1451_ = lean_int_dec_eq(v___x_1449_, v___x_1450_);
lean_dec(v___x_1449_);
v___x_1454_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1455_ = lean_int_mod(v_year_1434_, v___x_1454_);
v___x_1456_ = lean_int_dec_eq(v___x_1455_, v___x_1450_);
lean_dec(v___x_1455_);
if (v___x_1456_ == 0)
{
uint8_t v___x_1457_; 
lean_dec(v_year_1434_);
v___x_1457_ = 1;
v___y_1453_ = v___x_1457_;
goto v___jp_1452_;
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v___x_1458_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1459_ = lean_int_mod(v_year_1434_, v___x_1458_);
lean_dec(v_year_1434_);
v___x_1460_ = lean_int_dec_eq(v___x_1459_, v___x_1450_);
lean_dec(v___x_1459_);
v___y_1453_ = v___x_1460_;
goto v___jp_1452_;
}
v___jp_1437_:
{
lean_object* v___x_1440_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v_day_1436_);
lean_ctor_set(v___x_1432_, 0, v_month_1435_);
v___x_1440_ = v___x_1432_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_month_1435_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_day_1436_);
v___x_1440_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1441_ = l_Std_Time_ValidDate_dayOfYear(v___y_1438_, v___x_1440_);
lean_dec_ref(v___x_1440_);
v___x_1442_ = lean_box(v___y_1438_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v___x_1441_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set_tag(v___x_1428_, 1);
lean_ctor_set(v___x_1428_, 0, v___x_1443_);
v___x_1445_ = v___x_1428_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
v___jp_1452_:
{
if (v___x_1451_ == 0)
{
v___y_1438_ = v___x_1451_;
goto v___jp_1437_;
}
else
{
v___y_1438_ = v___y_1453_;
goto v___jp_1437_;
}
}
}
}
}
case 7:
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1473_; 
v_isSharedCheck_1473_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; 
v_unused_1474_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1474_);
v___x_1466_ = v_x_1389_;
v_isShared_1467_ = v_isSharedCheck_1473_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_x_1389_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1473_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v_date_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v_date_1468_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1468_);
lean_dec_ref(v_date_1387_);
v___x_1469_ = l_Std_Time_PlainDate_quarter(v_date_1468_);
lean_dec_ref(v_date_1468_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set_tag(v___x_1466_, 1);
lean_ctor_set(v___x_1466_, 0, v___x_1469_);
v___x_1471_ = v___x_1466_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
case 8:
{
lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1483_; 
v_isSharedCheck_1483_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1483_ == 0)
{
lean_object* v_unused_1484_; 
v_unused_1484_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1484_);
v___x_1476_ = v_x_1389_;
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
else
{
lean_dec(v_x_1389_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1483_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v_date_1478_; lean_object* v___x_1479_; lean_object* v___x_1481_; 
v_date_1478_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1478_);
lean_dec_ref(v_date_1387_);
v___x_1479_ = l_Std_Time_PlainDate_quarter(v_date_1478_);
lean_dec_ref(v_date_1478_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set_tag(v___x_1476_, 1);
lean_ctor_set(v___x_1476_, 0, v___x_1479_);
v___x_1481_ = v___x_1476_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
case 10:
{
lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1495_; 
v_isSharedCheck_1495_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; 
v_unused_1496_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1496_);
v___x_1486_ = v_x_1389_;
v_isShared_1487_ = v_isSharedCheck_1495_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v_x_1389_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1495_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
uint8_t v_firstDayOfWeek_1488_; lean_object* v_minimalDaysInFirstWeek_1489_; lean_object* v_date_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; 
v_firstDayOfWeek_1488_ = lean_ctor_get_uint8(v_locale_1388_, sizeof(void*)*2);
v_minimalDaysInFirstWeek_1489_ = lean_ctor_get(v_locale_1388_, 0);
v_date_1490_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1490_);
lean_dec_ref(v_date_1387_);
v___x_1491_ = l_Std_Time_PlainDate_weekOfYear(v_date_1490_, v_firstDayOfWeek_1488_, v_minimalDaysInFirstWeek_1489_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set_tag(v___x_1486_, 1);
lean_ctor_set(v___x_1486_, 0, v___x_1491_);
v___x_1493_ = v___x_1486_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
case 11:
{
lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1506_; 
v_isSharedCheck_1506_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1507_);
v___x_1498_ = v_x_1389_;
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v_x_1389_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
uint8_t v_firstDayOfWeek_1500_; lean_object* v_date_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v_firstDayOfWeek_1500_ = lean_ctor_get_uint8(v_locale_1388_, sizeof(void*)*2);
v_date_1501_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1501_);
lean_dec_ref(v_date_1387_);
v___x_1502_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1501_, v_firstDayOfWeek_1500_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set_tag(v___x_1498_, 1);
lean_ctor_set(v___x_1498_, 0, v___x_1502_);
v___x_1504_ = v___x_1498_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
case 4:
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1516_; 
v_isSharedCheck_1516_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1517_);
v___x_1509_ = v_x_1389_;
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_x_1389_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v_date_1511_; lean_object* v_month_1512_; lean_object* v___x_1514_; 
v_date_1511_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1511_);
lean_dec_ref(v_date_1387_);
v_month_1512_ = lean_ctor_get(v_date_1511_, 1);
lean_inc(v_month_1512_);
lean_dec_ref(v_date_1511_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set_tag(v___x_1509_, 1);
lean_ctor_set(v___x_1509_, 0, v_month_1512_);
v___x_1514_ = v___x_1509_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_month_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
case 5:
{
lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1526_; 
v_isSharedCheck_1526_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1527_);
v___x_1519_ = v_x_1389_;
v_isShared_1520_ = v_isSharedCheck_1526_;
goto v_resetjp_1518_;
}
else
{
lean_dec(v_x_1389_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1526_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_date_1521_; lean_object* v_month_1522_; lean_object* v___x_1524_; 
v_date_1521_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1521_);
lean_dec_ref(v_date_1387_);
v_month_1522_ = lean_ctor_get(v_date_1521_, 1);
lean_inc(v_month_1522_);
lean_dec_ref(v_date_1521_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 1);
lean_ctor_set(v___x_1519_, 0, v_month_1522_);
v___x_1524_ = v___x_1519_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_month_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
case 6:
{
lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1536_; 
v_isSharedCheck_1536_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1537_);
v___x_1529_ = v_x_1389_;
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
else
{
lean_dec(v_x_1389_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1536_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v_date_1531_; lean_object* v_day_1532_; lean_object* v___x_1534_; 
v_date_1531_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1531_);
lean_dec_ref(v_date_1387_);
v_day_1532_ = lean_ctor_get(v_date_1531_, 2);
lean_inc(v_day_1532_);
lean_dec_ref(v_date_1531_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set_tag(v___x_1529_, 1);
lean_ctor_set(v___x_1529_, 0, v_day_1532_);
v___x_1534_ = v___x_1529_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_day_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
case 12:
{
lean_object* v_date_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec_ref_known(v_x_1389_, 0);
v_date_1538_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1538_);
lean_dec_ref(v_date_1387_);
v___x_1539_ = l_Std_Time_PlainDate_weekday(v_date_1538_);
v___x_1540_ = lean_box(v___x_1539_);
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
case 13:
{
lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1551_; 
v_isSharedCheck_1551_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1552_);
v___x_1543_ = v_x_1389_;
v_isShared_1544_ = v_isSharedCheck_1551_;
goto v_resetjp_1542_;
}
else
{
lean_dec(v_x_1389_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1551_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_date_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v_date_1545_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1545_);
lean_dec_ref(v_date_1387_);
v___x_1546_ = l_Std_Time_PlainDate_weekday(v_date_1545_);
v___x_1547_ = lean_box(v___x_1546_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set_tag(v___x_1543_, 1);
lean_ctor_set(v___x_1543_, 0, v___x_1547_);
v___x_1549_ = v___x_1543_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
case 14:
{
lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1562_; 
v_isSharedCheck_1562_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; 
v_unused_1563_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1563_);
v___x_1554_ = v_x_1389_;
v_isShared_1555_ = v_isSharedCheck_1562_;
goto v_resetjp_1553_;
}
else
{
lean_dec(v_x_1389_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1562_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_date_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1560_; 
v_date_1556_ = lean_ctor_get(v_date_1387_, 0);
lean_inc_ref(v_date_1556_);
lean_dec_ref(v_date_1387_);
v___x_1557_ = l_Std_Time_PlainDate_weekday(v_date_1556_);
v___x_1558_ = lean_box(v___x_1557_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set_tag(v___x_1554_, 1);
lean_ctor_set(v___x_1554_, 0, v___x_1558_);
v___x_1560_ = v___x_1554_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v___x_1558_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
case 15:
{
lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1571_; 
v_isSharedCheck_1571_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1572_);
v___x_1565_ = v_x_1389_;
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
else
{
lean_dec(v_x_1389_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_1387_);
lean_dec_ref(v_date_1387_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set_tag(v___x_1565_, 1);
lean_ctor_set(v___x_1565_, 0, v___x_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
case 22:
{
lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1581_; 
v_isSharedCheck_1581_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; 
v_unused_1582_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1582_);
v___x_1574_ = v_x_1389_;
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v_x_1389_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_time_1576_; lean_object* v_hour_1577_; lean_object* v___x_1579_; 
v_time_1576_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1576_);
lean_dec_ref(v_date_1387_);
v_hour_1577_ = lean_ctor_get(v_time_1576_, 0);
lean_inc(v_hour_1577_);
lean_dec_ref(v_time_1576_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 1);
lean_ctor_set(v___x_1574_, 0, v_hour_1577_);
v___x_1579_ = v___x_1574_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_hour_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
case 21:
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1592_; 
v_isSharedCheck_1592_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1593_);
v___x_1584_ = v_x_1389_;
v_isShared_1585_ = v_isSharedCheck_1592_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v_x_1389_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1592_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_time_1586_; lean_object* v_hour_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v_time_1586_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1586_);
lean_dec_ref(v_date_1387_);
v_hour_1587_ = lean_ctor_get(v_time_1586_, 0);
lean_inc(v_hour_1587_);
lean_dec_ref(v_time_1586_);
v___x_1588_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1587_);
lean_dec(v_hour_1587_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 1);
lean_ctor_set(v___x_1584_, 0, v___x_1588_);
v___x_1590_ = v___x_1584_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
case 23:
{
lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1602_; 
v_isSharedCheck_1602_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; 
v_unused_1603_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1603_);
v___x_1595_ = v_x_1389_;
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
else
{
lean_dec(v_x_1389_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v_time_1597_; lean_object* v_minute_1598_; lean_object* v___x_1600_; 
v_time_1597_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1597_);
lean_dec_ref(v_date_1387_);
v_minute_1598_ = lean_ctor_get(v_time_1597_, 1);
lean_inc(v_minute_1598_);
lean_dec_ref(v_time_1597_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set_tag(v___x_1595_, 1);
lean_ctor_set(v___x_1595_, 0, v_minute_1598_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_minute_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
case 27:
{
lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1612_; 
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; 
v_unused_1613_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1613_);
v___x_1605_ = v_x_1389_;
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
else
{
lean_dec(v_x_1389_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v_time_1607_; lean_object* v_nanosecond_1608_; lean_object* v___x_1610_; 
v_time_1607_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1607_);
lean_dec_ref(v_date_1387_);
v_nanosecond_1608_ = lean_ctor_get(v_time_1607_, 3);
lean_inc(v_nanosecond_1608_);
lean_dec_ref(v_time_1607_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set_tag(v___x_1605_, 1);
lean_ctor_set(v___x_1605_, 0, v_nanosecond_1608_);
v___x_1610_ = v___x_1605_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_nanosecond_1608_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
case 24:
{
lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1622_; 
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1622_ == 0)
{
lean_object* v_unused_1623_; 
v_unused_1623_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1623_);
v___x_1615_ = v_x_1389_;
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
else
{
lean_dec(v_x_1389_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v_time_1617_; lean_object* v_second_1618_; lean_object* v___x_1620_; 
v_time_1617_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1617_);
lean_dec_ref(v_date_1387_);
v_second_1618_ = lean_ctor_get(v_time_1617_, 2);
lean_inc(v_second_1618_);
lean_dec_ref(v_time_1617_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set_tag(v___x_1615_, 1);
lean_ctor_set(v___x_1615_, 0, v_second_1618_);
v___x_1620_ = v___x_1615_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_second_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
case 16:
{
lean_object* v_time_1624_; lean_object* v_hour_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_dec_ref_known(v_x_1389_, 0);
v_time_1624_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1624_);
lean_dec_ref(v_date_1387_);
v_hour_1625_ = lean_ctor_get(v_time_1624_, 0);
lean_inc(v_hour_1625_);
lean_dec_ref(v_time_1624_);
v___x_1626_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1625_);
lean_dec(v_hour_1625_);
v___x_1627_ = lean_box(v___x_1626_);
v___x_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
return v___x_1628_;
}
case 17:
{
lean_object* v_time_1629_; lean_object* v_hour_1630_; lean_object* v_minute_1631_; lean_object* v_second_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec_ref_known(v_x_1389_, 0);
v_time_1629_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1629_);
lean_dec_ref(v_date_1387_);
v_hour_1630_ = lean_ctor_get(v_time_1629_, 0);
lean_inc(v_hour_1630_);
v_minute_1631_ = lean_ctor_get(v_time_1629_, 1);
lean_inc(v_minute_1631_);
v_second_1632_ = lean_ctor_get(v_time_1629_, 2);
lean_inc(v_second_1632_);
lean_dec_ref(v_time_1629_);
v___x_1633_ = l_Std_Time_classifyDayPeriod(v_hour_1630_, v_minute_1631_, v_second_1632_);
lean_dec(v_second_1632_);
lean_dec(v_minute_1631_);
lean_dec(v_hour_1630_);
v___x_1634_ = lean_box(v___x_1633_);
v___x_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1634_);
return v___x_1635_;
}
case 18:
{
lean_object* v_time_1636_; lean_object* v_hour_1637_; lean_object* v_minute_1638_; lean_object* v_second_1639_; uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
lean_dec_ref_known(v_x_1389_, 0);
v_time_1636_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1636_);
lean_dec_ref(v_date_1387_);
v_hour_1637_ = lean_ctor_get(v_time_1636_, 0);
lean_inc(v_hour_1637_);
v_minute_1638_ = lean_ctor_get(v_time_1636_, 1);
lean_inc(v_minute_1638_);
v_second_1639_ = lean_ctor_get(v_time_1636_, 2);
lean_inc(v_second_1639_);
lean_dec_ref(v_time_1636_);
v___x_1640_ = l_Std_Time_classifyExtendedDayPeriod(v_hour_1637_, v_minute_1638_, v_second_1639_);
lean_dec(v_second_1639_);
lean_dec(v_minute_1638_);
lean_dec(v_hour_1637_);
v___x_1641_ = lean_box(v___x_1640_);
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
case 19:
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1652_; 
v_isSharedCheck_1652_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; 
v_unused_1653_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1653_);
v___x_1644_ = v_x_1389_;
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v_x_1389_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1652_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_time_1646_; lean_object* v_hour_1647_; lean_object* v___x_1648_; lean_object* v___x_1650_; 
v_time_1646_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1646_);
lean_dec_ref(v_date_1387_);
v_hour_1647_ = lean_ctor_get(v_time_1646_, 0);
lean_inc(v_hour_1647_);
lean_dec_ref(v_time_1646_);
v___x_1648_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1647_);
lean_dec(v_hour_1647_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set_tag(v___x_1644_, 1);
lean_ctor_set(v___x_1644_, 0, v___x_1648_);
v___x_1650_ = v___x_1644_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
case 20:
{
lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1664_; 
v_isSharedCheck_1664_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; 
v_unused_1665_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1665_);
v___x_1655_ = v_x_1389_;
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v_x_1389_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1664_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_time_1657_; lean_object* v_hour_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1662_; 
v_time_1657_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1657_);
lean_dec_ref(v_date_1387_);
v_hour_1658_ = lean_ctor_get(v_time_1657_, 0);
lean_inc(v_hour_1658_);
lean_dec_ref(v_time_1657_);
v___x_1659_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1660_ = lean_int_emod(v_hour_1658_, v___x_1659_);
lean_dec(v_hour_1658_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set_tag(v___x_1655_, 1);
lean_ctor_set(v___x_1655_, 0, v___x_1660_);
v___x_1662_ = v___x_1655_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
case 25:
{
lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1674_; 
v_isSharedCheck_1674_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1675_);
v___x_1667_ = v_x_1389_;
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
else
{
lean_dec(v_x_1389_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v_time_1669_; lean_object* v_nanosecond_1670_; lean_object* v___x_1672_; 
v_time_1669_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1669_);
lean_dec_ref(v_date_1387_);
v_nanosecond_1670_ = lean_ctor_get(v_time_1669_, 3);
lean_inc(v_nanosecond_1670_);
lean_dec_ref(v_time_1669_);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 1);
lean_ctor_set(v___x_1667_, 0, v_nanosecond_1670_);
v___x_1672_ = v___x_1667_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_nanosecond_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
case 26:
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1684_; 
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1685_);
v___x_1677_ = v_x_1389_;
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v_x_1389_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v_time_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v_time_1679_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1679_);
lean_dec_ref(v_date_1387_);
v___x_1680_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1679_);
lean_dec_ref(v_time_1679_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set_tag(v___x_1677_, 1);
lean_ctor_set(v___x_1677_, 0, v___x_1680_);
v___x_1682_ = v___x_1677_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
case 28:
{
lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1694_; 
v_isSharedCheck_1694_ = !lean_is_exclusive(v_x_1389_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v_x_1389_, 0);
lean_dec(v_unused_1695_);
v___x_1687_ = v_x_1389_;
v_isShared_1688_ = v_isSharedCheck_1694_;
goto v_resetjp_1686_;
}
else
{
lean_dec(v_x_1389_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1694_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v_time_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v_time_1689_ = lean_ctor_get(v_date_1387_, 1);
lean_inc_ref(v_time_1689_);
lean_dec_ref(v_date_1387_);
v___x_1690_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1689_);
lean_dec_ref(v_time_1689_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set_tag(v___x_1687_, 1);
lean_ctor_set(v___x_1687_, 0, v___x_1690_);
v___x_1692_ = v___x_1687_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
default: 
{
lean_object* v___x_1696_; 
lean_dec_ref(v_x_1389_);
lean_dec_ref(v_date_1387_);
v___x_1696_ = lean_box(0);
return v___x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0___boxed(lean_object* v_date_1697_, lean_object* v_locale_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_Time_PlainDateTime_format___lam__0(v_date_1697_, v_locale_1698_, v_x_1699_);
lean_dec_ref(v_locale_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format(lean_object* v_date_1701_, lean_object* v_format_1702_, lean_object* v_locale_1703_){
_start:
{
lean_object* v___x_1704_; lean_object* v_format_1705_; 
v___x_1704_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1705_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1702_, v___x_1704_);
if (lean_obj_tag(v_format_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_dec_ref(v_locale_1703_);
lean_dec_ref(v_date_1701_);
v_a_1706_ = lean_ctor_get(v_format_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref_known(v_format_1705_, 1);
v___x_1707_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1708_ = lean_string_append(v___x_1707_, v_a_1706_);
lean_dec(v_a_1706_);
return v___x_1708_;
}
else
{
lean_object* v_a_1709_; lean_object* v___f_1710_; lean_object* v_res_1711_; 
v_a_1709_ = lean_ctor_get(v_format_1705_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v_format_1705_, 1);
v___f_1710_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1710_, 0, v_date_1701_);
lean_closure_set(v___f_1710_, 1, v_locale_1703_);
v_res_1711_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1709_, v___f_1710_);
if (lean_obj_tag(v_res_1711_) == 0)
{
lean_object* v___x_1712_; 
v___x_1712_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1712_;
}
else
{
lean_object* v_val_1713_; 
v_val_1713_ = lean_ctor_get(v_res_1711_, 0);
lean_inc(v_val_1713_);
lean_dec_ref_known(v_res_1711_, 1);
return v_val_1713_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = l_Std_Time_TimeZone_GMT;
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromAscTimeString(lean_object* v_input_1716_){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1718_ = l_Std_Time_Formats_ascTime;
v___x_1719_ = l_Std_Time_GenericFormat_parse(v___x_1717_, v___x_1718_, v_input_1716_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1719_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1719_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1737_; 
v_a_1728_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1730_ = v___x_1719_;
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1719_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v_date_1732_; lean_object* v___x_1733_; lean_object* v___x_1735_; 
v_date_1732_ = lean_ctor_get(v_a_1728_, 0);
lean_inc_ref(v_date_1732_);
lean_dec(v_a_1728_);
v___x_1733_ = lean_thunk_get_own(v_date_1732_);
lean_dec_ref(v_date_1732_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1733_);
v___x_1735_ = v___x_1730_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0(lean_object* v_pdt_1738_, lean_object* v_x_1739_){
_start:
{
lean_inc_ref(v_pdt_1738_);
return v_pdt_1738_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(lean_object* v_pdt_1740_, lean_object* v_x_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Std_Time_PlainDateTime_toAscTimeString___lam__0(v_pdt_1740_, v_x_1741_);
lean_dec_ref(v_pdt_1740_);
return v_res_1742_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1745_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1746_ = lean_int_neg(v___x_1745_);
return v___x_1746_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2(void){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_unsigned_to_nat(1000000000u);
v___x_1748_ = lean_nat_to_int(v___x_1747_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString(lean_object* v_pdt_1749_){
_start:
{
lean_object* v___x_1750_; lean_object* v_offset_1751_; lean_object* v_name_1752_; lean_object* v_abbreviation_1753_; uint8_t v_isDST_1754_; uint8_t v___x_1755_; uint8_t v___x_1756_; lean_object* v_ltt_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v_wt_1761_; lean_object* v_ltt_1762_; lean_object* v_tz_1763_; lean_object* v_offset_1764_; lean_object* v_second_1765_; lean_object* v_nano_1766_; lean_object* v___f_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1750_ = l_Std_Time_TimeZone_UTC;
v_offset_1751_ = lean_ctor_get(v___x_1750_, 0);
v_name_1752_ = lean_ctor_get(v___x_1750_, 1);
v_abbreviation_1753_ = lean_ctor_get(v___x_1750_, 2);
v_isDST_1754_ = lean_ctor_get_uint8(v___x_1750_, sizeof(void*)*3);
v___x_1755_ = 0;
v___x_1756_ = 1;
lean_inc_ref(v_name_1752_);
lean_inc_ref(v_abbreviation_1753_);
lean_inc(v_offset_1751_);
v_ltt_1757_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_1757_, 0, v_offset_1751_);
lean_ctor_set(v_ltt_1757_, 1, v_abbreviation_1753_);
lean_ctor_set(v_ltt_1757_, 2, v_name_1752_);
lean_ctor_set_uint8(v_ltt_1757_, sizeof(void*)*3, v_isDST_1754_);
lean_ctor_set_uint8(v_ltt_1757_, sizeof(void*)*3 + 1, v___x_1755_);
lean_ctor_set_uint8(v_ltt_1757_, sizeof(void*)*3 + 2, v___x_1756_);
v___x_1758_ = ((lean_object*)(l_Std_Time_PlainDateTime_toAscTimeString___closed__0));
v___x_1759_ = lean_box(0);
v___x_1760_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1760_, 0, v_ltt_1757_);
lean_ctor_set(v___x_1760_, 1, v___x_1758_);
lean_ctor_set(v___x_1760_, 2, v___x_1759_);
lean_inc_ref(v_pdt_1749_);
v_wt_1761_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1749_);
lean_inc_ref(v___x_1760_);
v_ltt_1762_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1760_, v_wt_1761_);
v_tz_1763_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1762_);
lean_dec_ref(v_ltt_1762_);
v_offset_1764_ = lean_ctor_get(v_tz_1763_, 0);
lean_inc(v_offset_1764_);
v_second_1765_ = lean_ctor_get(v_wt_1761_, 0);
lean_inc(v_second_1765_);
v_nano_1766_ = lean_ctor_get(v_wt_1761_, 1);
lean_inc(v_nano_1766_);
lean_dec_ref(v_wt_1761_);
v___f_1767_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1767_, 0, v_pdt_1749_);
v___x_1768_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1769_ = l_Std_Time_Formats_ascTime;
v___x_1770_ = lean_mk_thunk(v___f_1767_);
v___x_1771_ = lean_int_neg(v_offset_1764_);
lean_dec(v_offset_1764_);
v___x_1772_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__1, &l_Std_Time_PlainDateTime_toAscTimeString___closed__1_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1);
v___x_1773_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__2, &l_Std_Time_PlainDateTime_toAscTimeString___closed__2_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2);
v___x_1774_ = lean_int_mul(v_second_1765_, v___x_1773_);
lean_dec(v_second_1765_);
v___x_1775_ = lean_int_add(v___x_1774_, v_nano_1766_);
lean_dec(v_nano_1766_);
lean_dec(v___x_1774_);
v___x_1776_ = lean_int_mul(v___x_1771_, v___x_1773_);
lean_dec(v___x_1771_);
v___x_1777_ = lean_int_add(v___x_1776_, v___x_1772_);
lean_dec(v___x_1776_);
v___x_1778_ = lean_int_add(v___x_1775_, v___x_1777_);
lean_dec(v___x_1777_);
lean_dec(v___x_1775_);
v___x_1779_ = l_Std_Time_Duration_ofNanoseconds(v___x_1778_);
lean_dec(v___x_1778_);
v___x_1780_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1770_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
lean_ctor_set(v___x_1780_, 2, v___x_1760_);
lean_ctor_set(v___x_1780_, 3, v_tz_1763_);
v___x_1781_ = l_Std_Time_GenericFormat_format(v___x_1768_, v___x_1769_, v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLongDateFormatString(lean_object* v_input_1782_){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1784_ = l_Std_Time_Formats_longDateFormat;
v___x_1785_ = l_Std_Time_GenericFormat_parse(v___x_1783_, v___x_1784_, v_input_1782_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1803_; 
v_a_1794_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1796_ = v___x_1785_;
v_isShared_1797_ = v_isSharedCheck_1803_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1785_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1803_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v_date_1798_; lean_object* v___x_1799_; lean_object* v___x_1801_; 
v_date_1798_ = lean_ctor_get(v_a_1794_, 0);
lean_inc_ref(v_date_1798_);
lean_dec(v_a_1794_);
v___x_1799_ = lean_thunk_get_own(v_date_1798_);
lean_dec_ref(v_date_1798_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 0, v___x_1799_);
v___x_1801_ = v___x_1796_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLongDateFormatString(lean_object* v_pdt_1804_){
_start:
{
lean_object* v___x_1805_; lean_object* v_offset_1806_; lean_object* v_name_1807_; lean_object* v_abbreviation_1808_; uint8_t v_isDST_1809_; uint8_t v___x_1810_; uint8_t v___x_1811_; lean_object* v_ltt_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v_wt_1816_; lean_object* v_ltt_1817_; lean_object* v_tz_1818_; lean_object* v_offset_1819_; lean_object* v_second_1820_; lean_object* v_nano_1821_; lean_object* v___f_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1805_ = l_Std_Time_TimeZone_UTC;
v_offset_1806_ = lean_ctor_get(v___x_1805_, 0);
v_name_1807_ = lean_ctor_get(v___x_1805_, 1);
v_abbreviation_1808_ = lean_ctor_get(v___x_1805_, 2);
v_isDST_1809_ = lean_ctor_get_uint8(v___x_1805_, sizeof(void*)*3);
v___x_1810_ = 0;
v___x_1811_ = 1;
lean_inc_ref(v_name_1807_);
lean_inc_ref(v_abbreviation_1808_);
lean_inc(v_offset_1806_);
v_ltt_1812_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_1812_, 0, v_offset_1806_);
lean_ctor_set(v_ltt_1812_, 1, v_abbreviation_1808_);
lean_ctor_set(v_ltt_1812_, 2, v_name_1807_);
lean_ctor_set_uint8(v_ltt_1812_, sizeof(void*)*3, v_isDST_1809_);
lean_ctor_set_uint8(v_ltt_1812_, sizeof(void*)*3 + 1, v___x_1810_);
lean_ctor_set_uint8(v_ltt_1812_, sizeof(void*)*3 + 2, v___x_1811_);
v___x_1813_ = ((lean_object*)(l_Std_Time_PlainDateTime_toAscTimeString___closed__0));
v___x_1814_ = lean_box(0);
v___x_1815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1815_, 0, v_ltt_1812_);
lean_ctor_set(v___x_1815_, 1, v___x_1813_);
lean_ctor_set(v___x_1815_, 2, v___x_1814_);
lean_inc_ref(v_pdt_1804_);
v_wt_1816_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1804_);
lean_inc_ref(v___x_1815_);
v_ltt_1817_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1815_, v_wt_1816_);
v_tz_1818_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1817_);
lean_dec_ref(v_ltt_1817_);
v_offset_1819_ = lean_ctor_get(v_tz_1818_, 0);
lean_inc(v_offset_1819_);
v_second_1820_ = lean_ctor_get(v_wt_1816_, 0);
lean_inc(v_second_1820_);
v_nano_1821_ = lean_ctor_get(v_wt_1816_, 1);
lean_inc(v_nano_1821_);
lean_dec_ref(v_wt_1816_);
v___f_1822_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1822_, 0, v_pdt_1804_);
v___x_1823_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1824_ = l_Std_Time_Formats_longDateFormat;
v___x_1825_ = lean_mk_thunk(v___f_1822_);
v___x_1826_ = lean_int_neg(v_offset_1819_);
lean_dec(v_offset_1819_);
v___x_1827_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__1, &l_Std_Time_PlainDateTime_toAscTimeString___closed__1_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1);
v___x_1828_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__2, &l_Std_Time_PlainDateTime_toAscTimeString___closed__2_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2);
v___x_1829_ = lean_int_mul(v_second_1820_, v___x_1828_);
lean_dec(v_second_1820_);
v___x_1830_ = lean_int_add(v___x_1829_, v_nano_1821_);
lean_dec(v_nano_1821_);
lean_dec(v___x_1829_);
v___x_1831_ = lean_int_mul(v___x_1826_, v___x_1828_);
lean_dec(v___x_1826_);
v___x_1832_ = lean_int_add(v___x_1831_, v___x_1827_);
lean_dec(v___x_1831_);
v___x_1833_ = lean_int_add(v___x_1830_, v___x_1832_);
lean_dec(v___x_1832_);
lean_dec(v___x_1830_);
v___x_1834_ = l_Std_Time_Duration_ofNanoseconds(v___x_1833_);
lean_dec(v___x_1833_);
v___x_1835_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1825_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
lean_ctor_set(v___x_1835_, 2, v___x_1815_);
lean_ctor_set(v___x_1835_, 3, v_tz_1818_);
v___x_1836_ = l_Std_Time_GenericFormat_format(v___x_1823_, v___x_1824_, v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromDateTimeString(lean_object* v_input_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1839_ = l_Std_Time_Formats_dateTime24Hour;
v___x_1840_ = l_Std_Time_GenericFormat_parse(v___x_1838_, v___x_1839_, v_input_1837_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1858_; 
v_a_1849_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1851_ = v___x_1840_;
v_isShared_1852_ = v_isSharedCheck_1858_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1840_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1858_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_date_1853_; lean_object* v___x_1854_; lean_object* v___x_1856_; 
v_date_1853_ = lean_ctor_get(v_a_1849_, 0);
lean_inc_ref(v_date_1853_);
lean_dec(v_a_1849_);
v___x_1854_ = lean_thunk_get_own(v_date_1853_);
lean_dec_ref(v_date_1853_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1854_);
v___x_1856_ = v___x_1851_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toDateTimeString(lean_object* v_pdt_1859_){
_start:
{
lean_object* v_date_1860_; lean_object* v_time_1861_; lean_object* v_year_1862_; lean_object* v_month_1863_; lean_object* v_day_1864_; lean_object* v_hour_1865_; lean_object* v_minute_1866_; lean_object* v_second_1867_; lean_object* v_nanosecond_1868_; lean_object* v___x_1869_; lean_object* v___x_12__overap_1870_; lean_object* v___x_1871_; 
v_date_1860_ = lean_ctor_get(v_pdt_1859_, 0);
lean_inc_ref(v_date_1860_);
v_time_1861_ = lean_ctor_get(v_pdt_1859_, 1);
lean_inc_ref(v_time_1861_);
lean_dec_ref(v_pdt_1859_);
v_year_1862_ = lean_ctor_get(v_date_1860_, 0);
lean_inc(v_year_1862_);
v_month_1863_ = lean_ctor_get(v_date_1860_, 1);
lean_inc(v_month_1863_);
v_day_1864_ = lean_ctor_get(v_date_1860_, 2);
lean_inc(v_day_1864_);
lean_dec_ref(v_date_1860_);
v_hour_1865_ = lean_ctor_get(v_time_1861_, 0);
lean_inc(v_hour_1865_);
v_minute_1866_ = lean_ctor_get(v_time_1861_, 1);
lean_inc(v_minute_1866_);
v_second_1867_ = lean_ctor_get(v_time_1861_, 2);
lean_inc(v_second_1867_);
v_nanosecond_1868_ = lean_ctor_get(v_time_1861_, 3);
lean_inc(v_nanosecond_1868_);
lean_dec_ref(v_time_1861_);
v___x_1869_ = l_Std_Time_Formats_dateTime24Hour;
v___x_12__overap_1870_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1869_);
v___x_1871_ = lean_apply_7(v___x_12__overap_1870_, v_year_1862_, v_month_1863_, v_day_1864_, v_hour_1865_, v_minute_1866_, v_second_1867_, v_nanosecond_1868_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLeanDateTimeString(lean_object* v_input_1872_){
_start:
{
lean_object* v___y_1874_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1894_ = l_Std_Time_Formats_leanDateTime24Hour;
lean_inc_ref(v_input_1872_);
v___x_1895_ = l_Std_Time_GenericFormat_parse(v___x_1893_, v___x_1894_, v_input_1872_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec_ref_known(v___x_1895_, 1);
v___x_1896_ = l_Std_Time_Formats_leanDateTime24HourNoNanos;
v___x_1897_ = l_Std_Time_GenericFormat_parse(v___x_1893_, v___x_1896_, v_input_1872_);
v___y_1874_ = v___x_1897_;
goto v___jp_1873_;
}
else
{
lean_dec_ref(v_input_1872_);
v___y_1874_ = v___x_1895_;
goto v___jp_1873_;
}
v___jp_1873_:
{
if (lean_obj_tag(v___y_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_a_1875_ = lean_ctor_get(v___y_1874_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___y_1874_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___y_1874_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___y_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1892_; 
v_a_1883_ = lean_ctor_get(v___y_1874_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___y_1874_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1885_ = v___y_1874_;
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___y_1874_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1892_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v_date_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v_date_1887_ = lean_ctor_get(v_a_1883_, 0);
lean_inc_ref(v_date_1887_);
lean_dec(v_a_1883_);
v___x_1888_ = lean_thunk_get_own(v_date_1887_);
lean_dec_ref(v_date_1887_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLeanDateTimeString(lean_object* v_pdt_1898_){
_start:
{
lean_object* v_date_1899_; lean_object* v_time_1900_; lean_object* v_year_1901_; lean_object* v_month_1902_; lean_object* v_day_1903_; lean_object* v_hour_1904_; lean_object* v_minute_1905_; lean_object* v_second_1906_; lean_object* v_nanosecond_1907_; lean_object* v___x_1908_; lean_object* v___x_12__overap_1909_; lean_object* v___x_1910_; 
v_date_1899_ = lean_ctor_get(v_pdt_1898_, 0);
lean_inc_ref(v_date_1899_);
v_time_1900_ = lean_ctor_get(v_pdt_1898_, 1);
lean_inc_ref(v_time_1900_);
lean_dec_ref(v_pdt_1898_);
v_year_1901_ = lean_ctor_get(v_date_1899_, 0);
lean_inc(v_year_1901_);
v_month_1902_ = lean_ctor_get(v_date_1899_, 1);
lean_inc(v_month_1902_);
v_day_1903_ = lean_ctor_get(v_date_1899_, 2);
lean_inc(v_day_1903_);
lean_dec_ref(v_date_1899_);
v_hour_1904_ = lean_ctor_get(v_time_1900_, 0);
lean_inc(v_hour_1904_);
v_minute_1905_ = lean_ctor_get(v_time_1900_, 1);
lean_inc(v_minute_1905_);
v_second_1906_ = lean_ctor_get(v_time_1900_, 2);
lean_inc(v_second_1906_);
v_nanosecond_1907_ = lean_ctor_get(v_time_1900_, 3);
lean_inc(v_nanosecond_1907_);
lean_dec_ref(v_time_1900_);
v___x_1908_ = l_Std_Time_Formats_leanDateTime24Hour;
v___x_12__overap_1909_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1908_);
v___x_1910_ = lean_apply_7(v___x_12__overap_1909_, v_year_1901_, v_month_1902_, v_day_1903_, v_hour_1904_, v_minute_1905_, v_second_1906_, v_nanosecond_1907_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_parse(lean_object* v_date_1911_){
_start:
{
lean_object* v___x_1912_; 
lean_inc_ref(v_date_1911_);
v___x_1912_ = l_Std_Time_PlainDateTime_fromAscTimeString(v_date_1911_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v___x_1913_; 
lean_dec_ref_known(v___x_1912_, 1);
lean_inc_ref(v_date_1911_);
v___x_1913_ = l_Std_Time_PlainDateTime_fromLongDateFormatString(v_date_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v___x_1914_; 
lean_dec_ref_known(v___x_1913_, 1);
lean_inc_ref(v_date_1911_);
v___x_1914_ = l_Std_Time_PlainDateTime_fromDateTimeString(v_date_1911_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v___x_1915_; 
lean_dec_ref_known(v___x_1914_, 1);
v___x_1915_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v_date_1911_);
return v___x_1915_;
}
else
{
lean_dec_ref(v_date_1911_);
return v___x_1914_;
}
}
else
{
lean_dec_ref(v_date_1911_);
return v___x_1913_;
}
}
else
{
lean_dec_ref(v_date_1911_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0(lean_object* v_data_1921_, lean_object* v___y_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1923_ = ((lean_object*)(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1));
v___x_1924_ = l_Std_Time_PlainDateTime_toLeanDateTimeString(v_data_1921_);
v___x_1925_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
v___x_1926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1923_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = l_Repr_addAppParen(v___x_1928_, v___y_1922_);
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0___boxed(lean_object* v_data_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Std_Time_PlainDateTime_instRepr___lam__0(v_data_1930_, v___y_1931_);
lean_dec(v___y_1931_);
return v_res_1932_;
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

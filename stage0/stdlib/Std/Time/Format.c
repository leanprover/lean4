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
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*, uint8_t);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*);
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
lean_object* l_Std_Time_Hour_Ordinal_toRelative(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Std_Time_PlainTime_toMilliseconds(lean_object*);
lean_object* l_Std_Time_PlainTime_toNanoseconds(lean_object*);
lean_object* l_Std_Time_HourMarker_toAbsolute(uint8_t, lean_object*);
lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
lean_object* l_Std_Time_PlainDateTime_weekOfMonth(lean_object*);
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
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__1 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__2 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value;
static const lean_string_object l_Std_Time_Formats_iso8601___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_Formats_iso8601___closed__3 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__4 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__5 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__5_value)}};
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
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 17}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__12 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__13 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value;
static const lean_string_object l_Std_Time_Formats_iso8601___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Time_Formats_iso8601___closed__14 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__15 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__16 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__17 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 19}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__18 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__19 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 27}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 14}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__1 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__1_value;
static const lean_string_object l_Std_Time_Formats_time12Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__2 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__3 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 13}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 20}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 29}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 29}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 25}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 10}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__0 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__1 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__1_value;
static const lean_string_object l_Std_Time_Formats_longDateFormat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__2 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__3 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__4 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__4_value)}};
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
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 10}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__0 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__1 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__2 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__2_value)}};
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
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 11}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__2_value)}};
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
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(24) << 1) | 1))}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__1_value),((lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__3_value;
static lean_once_cell_t l_Std_Time_TimeZone_fromTimeZone___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__4;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_Offset_fromOffset___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 28}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
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
uint8_t v___x_30__boxed_704_; lean_object* v_res_705_; 
v___x_30__boxed_704_ = lean_unbox(v___x_701_);
v_res_705_ = l_Std_Time_TimeZone_fromTimeZone___lam__0(v___x_30__boxed_704_, v_id_702_, v_off_703_);
return v_res_705_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_fromTimeZone___closed__4(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_spec_719_; 
v___x_717_ = ((lean_object*)(l_Std_Time_TimeZone_fromTimeZone___closed__3));
v___x_718_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_spec_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_spec_719_, 0, v___x_718_);
lean_ctor_set(v_spec_719_, 1, v___x_717_);
return v_spec_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone(lean_object* v_input_720_){
_start:
{
lean_object* v___f_721_; lean_object* v_spec_722_; lean_object* v___x_723_; 
v___f_721_ = ((lean_object*)(l_Std_Time_TimeZone_fromTimeZone___closed__0));
v_spec_722_ = lean_obj_once(&l_Std_Time_TimeZone_fromTimeZone___closed__4, &l_Std_Time_TimeZone_fromTimeZone___closed__4_once, _init_l_Std_Time_TimeZone_fromTimeZone___closed__4);
v___x_723_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_722_, v___f_721_, v_input_720_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset___lam__0(lean_object* v_val_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_725_, 0, v_val_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_spec_736_; 
v___x_734_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_fromOffset___closed__3));
v___x_735_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_spec_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_spec_736_, 0, v___x_735_);
lean_ctor_set(v_spec_736_, 1, v___x_734_);
return v_spec_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset(lean_object* v_input_737_){
_start:
{
lean_object* v___f_738_; lean_object* v_spec_739_; lean_object* v___x_740_; 
v___f_738_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_fromOffset___closed__0));
v_spec_739_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_fromOffset___closed__4, &l_Std_Time_TimeZone_Offset_fromOffset___closed__4_once, _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4);
v___x_740_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_739_, v___f_738_, v_input_737_);
return v___x_740_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_741_ = lean_unsigned_to_nat(4u);
v___x_742_ = lean_nat_to_int(v___x_741_);
return v___x_742_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__1(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_nat_to_int(v___x_743_);
return v___x_744_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__2(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(400u);
v___x_746_ = lean_nat_to_int(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__3(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(100u);
v___x_748_ = lean_nat_to_int(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0(lean_object* v_date_749_, lean_object* v_locale_750_, lean_object* v_x_751_){
_start:
{
uint8_t v___y_753_; 
switch(lean_obj_tag(v_x_751_))
{
case 0:
{
lean_object* v_year_758_; uint8_t v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
lean_dec_ref_known(v_x_751_, 0);
v_year_758_ = lean_ctor_get(v_date_749_, 0);
lean_inc(v_year_758_);
lean_dec_ref(v_date_749_);
v___x_759_ = l_Std_Time_Year_Offset_era(v_year_758_);
lean_dec(v_year_758_);
v___x_760_ = lean_box(v___x_759_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
case 1:
{
lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
v_isSharedCheck_769_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; 
v_unused_770_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_770_);
v___x_763_ = v_x_751_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_dec(v_x_751_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v_year_765_; lean_object* v___x_767_; 
v_year_765_ = lean_ctor_get(v_date_749_, 0);
lean_inc(v_year_765_);
lean_dec_ref(v_date_749_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_year_765_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_year_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
case 2:
{
lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_778_; 
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_779_);
v___x_772_ = v_x_751_;
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
else
{
lean_dec(v_x_751_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_year_774_; lean_object* v___x_776_; 
v_year_774_ = lean_ctor_get(v_date_749_, 0);
lean_inc(v_year_774_);
lean_dec_ref(v_date_749_);
if (v_isShared_773_ == 0)
{
lean_ctor_set_tag(v___x_772_, 1);
lean_ctor_set(v___x_772_, 0, v_year_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_year_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
case 3:
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_788_; 
v_isSharedCheck_788_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_789_);
v___x_781_ = v_x_751_;
v_isShared_782_ = v_isSharedCheck_788_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_x_751_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_788_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v_firstDayOfWeek_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v_firstDayOfWeek_783_ = lean_ctor_get_uint8(v_locale_750_, sizeof(void*)*1);
v___x_784_ = l_Std_Time_PlainDate_weekYear(v_date_749_, v_firstDayOfWeek_783_);
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 1);
lean_ctor_set(v___x_781_, 0, v___x_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
case 4:
{
lean_object* v_year_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_798_; 
lean_dec_ref_known(v_x_751_, 1);
v_year_790_ = lean_ctor_get(v_date_749_, 0);
v___x_791_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_792_ = lean_int_mod(v_year_790_, v___x_791_);
v___x_793_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_798_ = lean_int_dec_eq(v___x_792_, v___x_793_);
lean_dec(v___x_792_);
if (v___x_798_ == 0)
{
v___y_753_ = v___x_798_;
goto v___jp_752_;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_799_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_800_ = lean_int_mod(v_year_790_, v___x_799_);
v___x_801_ = lean_int_dec_eq(v___x_800_, v___x_793_);
lean_dec(v___x_800_);
if (v___x_801_ == 0)
{
if (v___x_798_ == 0)
{
goto v___jp_794_;
}
else
{
v___y_753_ = v___x_798_;
goto v___jp_752_;
}
}
else
{
goto v___jp_794_;
}
}
v___jp_794_:
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_796_ = lean_int_mod(v_year_790_, v___x_795_);
v___x_797_ = lean_int_dec_eq(v___x_796_, v___x_793_);
lean_dec(v___x_796_);
v___y_753_ = v___x_797_;
goto v___jp_752_;
}
}
case 7:
{
lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_809_; 
v_isSharedCheck_809_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; 
v_unused_810_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_810_);
v___x_803_ = v_x_751_;
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
else
{
lean_dec(v_x_751_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_809_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_807_; 
v___x_805_ = l_Std_Time_PlainDate_quarter(v_date_749_);
lean_dec_ref(v_date_749_);
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 1);
lean_ctor_set(v___x_803_, 0, v___x_805_);
v___x_807_ = v___x_803_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
case 8:
{
lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_819_; 
v_isSharedCheck_819_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_820_);
v___x_812_ = v_x_751_;
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
else
{
lean_dec(v_x_751_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_819_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
uint8_t v_firstDayOfWeek_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
v_firstDayOfWeek_814_ = lean_ctor_get_uint8(v_locale_750_, sizeof(void*)*1);
v___x_815_ = l_Std_Time_PlainDate_weekOfYear(v_date_749_, v_firstDayOfWeek_814_);
if (v_isShared_813_ == 0)
{
lean_ctor_set_tag(v___x_812_, 1);
lean_ctor_set(v___x_812_, 0, v___x_815_);
v___x_817_ = v___x_812_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
case 9:
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_829_; 
v_isSharedCheck_829_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_830_);
v___x_822_ = v_x_751_;
v_isShared_823_ = v_isSharedCheck_829_;
goto v_resetjp_821_;
}
else
{
lean_dec(v_x_751_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_829_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v_firstDayOfWeek_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v_firstDayOfWeek_824_ = lean_ctor_get_uint8(v_locale_750_, sizeof(void*)*1);
v___x_825_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_749_, v_firstDayOfWeek_824_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 1);
lean_ctor_set(v___x_822_, 0, v___x_825_);
v___x_827_ = v___x_822_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
case 5:
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_isSharedCheck_838_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_839_);
v___x_832_ = v_x_751_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_dec(v_x_751_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_month_834_; lean_object* v___x_836_; 
v_month_834_ = lean_ctor_get(v_date_749_, 1);
lean_inc(v_month_834_);
lean_dec_ref(v_date_749_);
if (v_isShared_833_ == 0)
{
lean_ctor_set_tag(v___x_832_, 1);
lean_ctor_set(v___x_832_, 0, v_month_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_month_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
case 6:
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_isSharedCheck_847_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_848_);
v___x_841_ = v_x_751_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_dec(v_x_751_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v_day_843_; lean_object* v___x_845_; 
v_day_843_ = lean_ctor_get(v_date_749_, 2);
lean_inc(v_day_843_);
lean_dec_ref(v_date_749_);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 1);
lean_ctor_set(v___x_841_, 0, v_day_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_day_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
case 10:
{
uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec_ref_known(v_x_751_, 0);
v___x_849_ = l_Std_Time_PlainDate_weekday(v_date_749_);
v___x_850_ = lean_box(v___x_849_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
return v___x_851_;
}
case 11:
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_860_; 
v_isSharedCheck_860_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; 
v_unused_861_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_861_);
v___x_853_ = v_x_751_;
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
else
{
lean_dec(v_x_751_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_855_ = l_Std_Time_PlainDate_weekday(v_date_749_);
v___x_856_ = lean_box(v___x_855_);
if (v_isShared_854_ == 0)
{
lean_ctor_set_tag(v___x_853_, 1);
lean_ctor_set(v___x_853_, 0, v___x_856_);
v___x_858_ = v___x_853_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
case 12:
{
lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_isSharedCheck_869_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_869_ == 0)
{
lean_object* v_unused_870_; 
v_unused_870_ = lean_ctor_get(v_x_751_, 0);
lean_dec(v_unused_870_);
v___x_863_ = v_x_751_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_dec(v_x_751_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = l_Std_Time_PlainDate_weekOfMonth(v_date_749_);
lean_dec_ref(v_date_749_);
if (v_isShared_864_ == 0)
{
lean_ctor_set_tag(v___x_863_, 1);
lean_ctor_set(v___x_863_, 0, v___x_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
default: 
{
lean_object* v___x_871_; 
lean_dec(v_x_751_);
lean_dec_ref(v_date_749_);
v___x_871_ = lean_box(0);
return v___x_871_;
}
}
v___jp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = l_Std_Time_PlainDate_dayOfYear(v_date_749_);
lean_dec_ref(v_date_749_);
v___x_755_ = lean_box(v___y_753_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0___boxed(lean_object* v_date_872_, lean_object* v_locale_873_, lean_object* v_x_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Std_Time_PlainDate_format___lam__0(v_date_872_, v_locale_873_, v_x_874_);
lean_dec_ref(v_locale_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format(lean_object* v_date_878_, lean_object* v_format_879_, lean_object* v_locale_880_){
_start:
{
lean_object* v___x_881_; lean_object* v_format_882_; 
v___x_881_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_882_ = l_Std_Time_GenericFormat_spec___redArg(v_format_879_, v___x_881_);
if (lean_obj_tag(v_format_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec_ref(v_locale_880_);
lean_dec_ref(v_date_878_);
v_a_883_ = lean_ctor_get(v_format_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v_format_882_, 1);
v___x_884_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_885_ = lean_string_append(v___x_884_, v_a_883_);
lean_dec(v_a_883_);
return v___x_885_;
}
else
{
lean_object* v_a_886_; lean_object* v___f_887_; lean_object* v_res_888_; 
v_a_886_ = lean_ctor_get(v_format_882_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v_format_882_, 1);
v___f_887_ = lean_alloc_closure((void*)(l_Std_Time_PlainDate_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_887_, 0, v_date_878_);
lean_closure_set(v___f_887_, 1, v_locale_880_);
v_res_888_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_886_, v___f_887_);
if (lean_obj_tag(v_res_888_) == 0)
{
lean_object* v___x_889_; 
v___x_889_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_889_;
}
else
{
lean_object* v_val_890_; 
v_val_890_ = lean_ctor_get(v_res_888_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v_res_888_, 1);
return v_val_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString___lam__0(lean_object* v_m_891_, lean_object* v_d_892_, lean_object* v_y_893_){
_start:
{
uint8_t v___y_895_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_908_; 
v___x_901_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_902_ = lean_int_mod(v_y_893_, v___x_901_);
v___x_903_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_908_ = lean_int_dec_eq(v___x_902_, v___x_903_);
lean_dec(v___x_902_);
if (v___x_908_ == 0)
{
v___y_895_ = v___x_908_;
goto v___jp_894_;
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_909_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_910_ = lean_int_mod(v_y_893_, v___x_909_);
v___x_911_ = lean_int_dec_eq(v___x_910_, v___x_903_);
lean_dec(v___x_910_);
if (v___x_911_ == 0)
{
if (v___x_908_ == 0)
{
goto v___jp_904_;
}
else
{
v___y_895_ = v___x_908_;
goto v___jp_894_;
}
}
else
{
goto v___jp_904_;
}
}
v___jp_894_:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = l_Std_Time_Month_Ordinal_days(v___y_895_, v_m_891_);
v___x_897_ = lean_int_dec_le(v_d_892_, v___x_896_);
lean_dec(v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec(v_y_893_);
lean_dec(v_d_892_);
lean_dec(v_m_891_);
v___x_898_ = lean_box(0);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_899_, 0, v_y_893_);
lean_ctor_set(v___x_899_, 1, v_m_891_);
lean_ctor_set(v___x_899_, 2, v_d_892_);
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
v___jp_904_:
{
lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_905_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_906_ = lean_int_mod(v_y_893_, v___x_905_);
v___x_907_ = lean_int_dec_eq(v___x_906_, v___x_903_);
lean_dec(v___x_906_);
v___y_895_ = v___x_907_;
goto v___jp_894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString(lean_object* v_input_913_){
_start:
{
lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___f_914_ = ((lean_object*)(l_Std_Time_PlainDate_fromAmericanDateString___closed__0));
v___x_915_ = l_Std_Time_Formats_americanDate;
v___x_916_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_915_, v___f_914_, v_input_913_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toAmericanDateString(lean_object* v_input_917_){
_start:
{
lean_object* v_year_918_; lean_object* v_month_919_; lean_object* v_day_920_; lean_object* v___x_921_; lean_object* v___x_6__overap_922_; lean_object* v___x_923_; 
v_year_918_ = lean_ctor_get(v_input_917_, 0);
lean_inc(v_year_918_);
v_month_919_ = lean_ctor_get(v_input_917_, 1);
lean_inc(v_month_919_);
v_day_920_ = lean_ctor_get(v_input_917_, 2);
lean_inc(v_day_920_);
lean_dec_ref(v_input_917_);
v___x_921_ = l_Std_Time_Formats_americanDate;
v___x_6__overap_922_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_921_);
v___x_923_ = lean_apply_3(v___x_6__overap_922_, v_month_919_, v_day_920_, v_year_918_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString___lam__0(lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
uint8_t v___y_928_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_941_; 
v___x_934_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_935_ = lean_int_mod(v___y_924_, v___x_934_);
v___x_936_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_941_ = lean_int_dec_eq(v___x_935_, v___x_936_);
lean_dec(v___x_935_);
if (v___x_941_ == 0)
{
v___y_928_ = v___x_941_;
goto v___jp_927_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_942_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_943_ = lean_int_mod(v___y_924_, v___x_942_);
v___x_944_ = lean_int_dec_eq(v___x_943_, v___x_936_);
lean_dec(v___x_943_);
if (v___x_944_ == 0)
{
if (v___x_941_ == 0)
{
goto v___jp_937_;
}
else
{
v___y_928_ = v___x_941_;
goto v___jp_927_;
}
}
else
{
goto v___jp_937_;
}
}
v___jp_927_:
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = l_Std_Time_Month_Ordinal_days(v___y_928_, v___y_925_);
v___x_930_ = lean_int_dec_le(v___y_926_, v___x_929_);
lean_dec(v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; 
lean_dec(v___y_926_);
lean_dec(v___y_925_);
lean_dec(v___y_924_);
v___x_931_ = lean_box(0);
return v___x_931_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_932_, 0, v___y_924_);
lean_ctor_set(v___x_932_, 1, v___y_925_);
lean_ctor_set(v___x_932_, 2, v___y_926_);
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
v___jp_937_:
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_939_ = lean_int_mod(v___y_924_, v___x_938_);
v___x_940_ = lean_int_dec_eq(v___x_939_, v___x_936_);
lean_dec(v___x_939_);
v___y_928_ = v___x_940_;
goto v___jp_927_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString(lean_object* v_input_946_){
_start:
{
lean_object* v___f_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___f_947_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_948_ = l_Std_Time_Formats_sqlDate;
v___x_949_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_948_, v___f_947_, v_input_946_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toSQLDateString(lean_object* v_input_950_){
_start:
{
lean_object* v_year_951_; lean_object* v_month_952_; lean_object* v_day_953_; lean_object* v___x_954_; lean_object* v___x_6__overap_955_; lean_object* v___x_956_; 
v_year_951_ = lean_ctor_get(v_input_950_, 0);
lean_inc(v_year_951_);
v_month_952_ = lean_ctor_get(v_input_950_, 1);
lean_inc(v_month_952_);
v_day_953_ = lean_ctor_get(v_input_950_, 2);
lean_inc(v_day_953_);
lean_dec_ref(v_input_950_);
v___x_954_ = l_Std_Time_Formats_sqlDate;
v___x_6__overap_955_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_954_);
v___x_956_ = lean_apply_3(v___x_6__overap_955_, v_year_951_, v_month_952_, v_day_953_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromLeanDateString(lean_object* v_input_957_){
_start:
{
lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___f_958_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_959_ = l_Std_Time_Formats_leanDate;
v___x_960_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_959_, v___f_958_, v_input_957_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toLeanDateString(lean_object* v_input_961_){
_start:
{
lean_object* v_year_962_; lean_object* v_month_963_; lean_object* v_day_964_; lean_object* v___x_965_; lean_object* v___x_6__overap_966_; lean_object* v___x_967_; 
v_year_962_ = lean_ctor_get(v_input_961_, 0);
lean_inc(v_year_962_);
v_month_963_ = lean_ctor_get(v_input_961_, 1);
lean_inc(v_month_963_);
v_day_964_ = lean_ctor_get(v_input_961_, 2);
lean_inc(v_day_964_);
lean_dec_ref(v_input_961_);
v___x_965_ = l_Std_Time_Formats_leanDate;
v___x_6__overap_966_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_965_);
v___x_967_ = lean_apply_3(v___x_6__overap_966_, v_year_962_, v_month_963_, v_day_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_parse(lean_object* v_input_968_){
_start:
{
lean_object* v___x_969_; 
lean_inc_ref(v_input_968_);
v___x_969_ = l_Std_Time_PlainDate_fromAmericanDateString(v_input_968_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_970_; 
lean_dec_ref_known(v___x_969_, 1);
v___x_970_ = l_Std_Time_PlainDate_fromSQLDateString(v_input_968_);
return v___x_970_;
}
else
{
lean_dec_ref(v_input_968_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0(lean_object* v_data_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_981_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__1));
v___x_982_ = l_Std_Time_PlainDate_toLeanDateString(v_data_979_);
v___x_983_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_981_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Repr_addAppParen(v___x_986_, v___y_980_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0___boxed(lean_object* v_data_988_, lean_object* v___y_989_){
_start:
{
lean_object* v_res_990_; 
v_res_990_ = l_Std_Time_PlainDate_instRepr___lam__0(v_data_988_, v___y_989_);
lean_dec(v___y_989_);
return v_res_990_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(12u);
v___x_994_ = lean_nat_to_int(v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0(lean_object* v_time_995_, lean_object* v_x_996_){
_start:
{
switch(lean_obj_tag(v_x_996_))
{
case 17:
{
lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1004_; 
v_isSharedCheck_1004_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1004_ == 0)
{
lean_object* v_unused_1005_; 
v_unused_1005_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1005_);
v___x_998_ = v_x_996_;
v_isShared_999_ = v_isSharedCheck_1004_;
goto v_resetjp_997_;
}
else
{
lean_dec(v_x_996_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1004_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_hour_1000_; lean_object* v___x_1002_; 
v_hour_1000_ = lean_ctor_get(v_time_995_, 0);
lean_inc(v_hour_1000_);
if (v_isShared_999_ == 0)
{
lean_ctor_set_tag(v___x_998_, 1);
lean_ctor_set(v___x_998_, 0, v_hour_1000_);
v___x_1002_ = v___x_998_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_hour_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
case 16:
{
lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1014_; 
v_isSharedCheck_1014_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1015_);
v___x_1007_ = v_x_996_;
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
else
{
lean_dec(v_x_996_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_hour_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v_hour_1009_ = lean_ctor_get(v_time_995_, 0);
v___x_1010_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1009_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set_tag(v___x_1007_, 1);
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
case 18:
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1023_; 
v_isSharedCheck_1023_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1024_);
v___x_1017_ = v_x_996_;
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v_x_996_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v_minute_1019_; lean_object* v___x_1021_; 
v_minute_1019_ = lean_ctor_get(v_time_995_, 1);
lean_inc(v_minute_1019_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 1);
lean_ctor_set(v___x_1017_, 0, v_minute_1019_);
v___x_1021_ = v___x_1017_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_minute_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
case 22:
{
lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1032_; 
v_isSharedCheck_1032_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1033_);
v___x_1026_ = v_x_996_;
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
else
{
lean_dec(v_x_996_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_nanosecond_1028_; lean_object* v___x_1030_; 
v_nanosecond_1028_ = lean_ctor_get(v_time_995_, 3);
lean_inc(v_nanosecond_1028_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set_tag(v___x_1026_, 1);
lean_ctor_set(v___x_1026_, 0, v_nanosecond_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_nanosecond_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
case 19:
{
lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1041_; 
v_isSharedCheck_1041_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1042_);
v___x_1035_ = v_x_996_;
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
else
{
lean_dec(v_x_996_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v_second_1037_; lean_object* v___x_1039_; 
v_second_1037_ = lean_ctor_get(v_time_995_, 2);
lean_inc(v_second_1037_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 1);
lean_ctor_set(v___x_1035_, 0, v_second_1037_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_second_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
case 13:
{
lean_object* v_hour_1043_; uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec_ref_known(v_x_996_, 0);
v_hour_1043_ = lean_ctor_get(v_time_995_, 0);
v___x_1044_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1043_);
v___x_1045_ = lean_box(v___x_1044_);
v___x_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
case 14:
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1055_; 
v_isSharedCheck_1055_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1055_ == 0)
{
lean_object* v_unused_1056_; 
v_unused_1056_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1056_);
v___x_1048_ = v_x_996_;
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v_x_996_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1055_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_hour_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v_hour_1050_ = lean_ctor_get(v_time_995_, 0);
v___x_1051_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1050_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 1);
lean_ctor_set(v___x_1048_, 0, v___x_1051_);
v___x_1053_ = v___x_1048_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
case 15:
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1066_; 
v_isSharedCheck_1066_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1067_);
v___x_1058_ = v_x_996_;
v_isShared_1059_ = v_isSharedCheck_1066_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v_x_996_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1066_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v_hour_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v_hour_1060_ = lean_ctor_get(v_time_995_, 0);
v___x_1061_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1062_ = lean_int_emod(v_hour_1060_, v___x_1061_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 1);
lean_ctor_set(v___x_1058_, 0, v___x_1062_);
v___x_1064_ = v___x_1058_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
case 20:
{
lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1075_; 
v_isSharedCheck_1075_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1075_ == 0)
{
lean_object* v_unused_1076_; 
v_unused_1076_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1076_);
v___x_1069_ = v_x_996_;
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v_x_996_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v_nanosecond_1071_; lean_object* v___x_1073_; 
v_nanosecond_1071_ = lean_ctor_get(v_time_995_, 3);
lean_inc(v_nanosecond_1071_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set_tag(v___x_1069_, 1);
lean_ctor_set(v___x_1069_, 0, v_nanosecond_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_nanosecond_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
case 21:
{
lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_isSharedCheck_1084_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1085_);
v___x_1078_ = v_x_996_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_dec(v_x_996_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = l_Std_Time_PlainTime_toMilliseconds(v_time_995_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set_tag(v___x_1078_, 1);
lean_ctor_set(v___x_1078_, 0, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
case 23:
{
lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1093_; 
v_isSharedCheck_1093_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v_x_996_, 0);
lean_dec(v_unused_1094_);
v___x_1087_ = v_x_996_;
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
else
{
lean_dec(v_x_996_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1093_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = l_Std_Time_PlainTime_toNanoseconds(v_time_995_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 1);
lean_ctor_set(v___x_1087_, 0, v___x_1089_);
v___x_1091_ = v___x_1087_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
default: 
{
lean_object* v___x_1095_; 
lean_dec(v_x_996_);
v___x_1095_ = lean_box(0);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0___boxed(lean_object* v_time_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_Time_PlainTime_format___lam__0(v_time_1096_, v_x_1097_);
lean_dec_ref(v_time_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format(lean_object* v_time_1099_, lean_object* v_format_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v_format_1102_; 
v___x_1101_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1102_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1100_, v___x_1101_);
if (lean_obj_tag(v_format_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_dec_ref(v_time_1099_);
v_a_1103_ = lean_ctor_get(v_format_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v_format_1102_, 1);
v___x_1104_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1105_ = lean_string_append(v___x_1104_, v_a_1103_);
lean_dec(v_a_1103_);
return v___x_1105_;
}
else
{
lean_object* v_a_1106_; lean_object* v___f_1107_; lean_object* v_res_1108_; 
v_a_1106_ = lean_ctor_get(v_format_1102_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v_format_1102_, 1);
v___f_1107_ = lean_alloc_closure((void*)(l_Std_Time_PlainTime_format___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1107_, 0, v_time_1099_);
v_res_1108_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1106_, v___f_1107_);
if (lean_obj_tag(v_res_1108_) == 0)
{
lean_object* v___x_1109_; 
v___x_1109_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1109_;
}
else
{
lean_object* v_val_1110_; 
v_val_1110_ = lean_ctor_get(v_res_1108_, 0);
lean_inc(v_val_1110_);
lean_dec_ref_known(v_res_1108_, 1);
return v_val_1110_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1111_ = lean_unsigned_to_nat(1000000000u);
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = lean_nat_mod(v___x_1112_, v___x_1111_);
return v___x_1113_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0);
v___x_1115_ = lean_nat_to_int(v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour___lam__0(lean_object* v_h_1116_, lean_object* v_m_1117_, lean_object* v_s_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1);
v___x_1120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1120_, 0, v_h_1116_);
lean_ctor_set(v___x_1120_, 1, v_m_1117_);
lean_ctor_set(v___x_1120_, 2, v_s_1118_);
lean_ctor_set(v___x_1120_, 3, v___x_1119_);
v___x_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour(lean_object* v_input_1123_){
_start:
{
lean_object* v___f_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___f_1124_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1125_ = l_Std_Time_Formats_time24Hour;
v___x_1126_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1125_, v___f_1124_, v_input_1123_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime24Hour(lean_object* v_input_1127_){
_start:
{
lean_object* v_hour_1128_; lean_object* v_minute_1129_; lean_object* v_second_1130_; lean_object* v___x_1131_; lean_object* v___x_6__overap_1132_; lean_object* v___x_1133_; 
v_hour_1128_ = lean_ctor_get(v_input_1127_, 0);
lean_inc(v_hour_1128_);
v_minute_1129_ = lean_ctor_get(v_input_1127_, 1);
lean_inc(v_minute_1129_);
v_second_1130_ = lean_ctor_get(v_input_1127_, 2);
lean_inc(v_second_1130_);
lean_dec_ref(v_input_1127_);
v___x_1131_ = l_Std_Time_Formats_time24Hour;
v___x_6__overap_1132_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1131_);
v___x_1133_ = lean_apply_3(v___x_6__overap_1132_, v_hour_1128_, v_minute_1129_, v_second_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0(lean_object* v_h_1134_, lean_object* v_m_1135_, lean_object* v_s_1136_, lean_object* v_n_1137_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1138_, 0, v_h_1134_);
lean_ctor_set(v___x_1138_, 1, v_m_1135_);
lean_ctor_set(v___x_1138_, 2, v_s_1136_);
lean_ctor_set(v___x_1138_, 3, v_n_1137_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour(lean_object* v_input_1141_){
_start:
{
lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___f_1142_ = ((lean_object*)(l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0));
v___x_1143_ = l_Std_Time_Formats_leanTime24Hour;
lean_inc_ref(v_input_1141_);
v___x_1144_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1143_, v___f_1142_, v_input_1141_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
lean_dec_ref_known(v___x_1144_, 1);
v___f_1145_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1146_ = l_Std_Time_Formats_leanTime24HourNoNanos;
v___x_1147_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1146_, v___f_1145_, v_input_1141_);
return v___x_1147_;
}
else
{
lean_dec_ref(v_input_1141_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toLeanTime24Hour(lean_object* v_input_1148_){
_start:
{
lean_object* v_hour_1149_; lean_object* v_minute_1150_; lean_object* v_second_1151_; lean_object* v_nanosecond_1152_; lean_object* v___x_1153_; lean_object* v___x_7__overap_1154_; lean_object* v___x_1155_; 
v_hour_1149_ = lean_ctor_get(v_input_1148_, 0);
lean_inc(v_hour_1149_);
v_minute_1150_ = lean_ctor_get(v_input_1148_, 1);
lean_inc(v_minute_1150_);
v_second_1151_ = lean_ctor_get(v_input_1148_, 2);
lean_inc(v_second_1151_);
v_nanosecond_1152_ = lean_ctor_get(v_input_1148_, 3);
lean_inc(v_nanosecond_1152_);
lean_dec_ref(v_input_1148_);
v___x_1153_ = l_Std_Time_Formats_leanTime24Hour;
v___x_7__overap_1154_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1153_);
v___x_1155_ = lean_apply_4(v___x_7__overap_1154_, v_hour_1149_, v_minute_1150_, v_second_1151_, v_nanosecond_1152_);
return v___x_1155_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_to_int(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0(lean_object* v_h_1158_, lean_object* v_m_1159_, lean_object* v_s_1160_, uint8_t v_a_1161_){
_start:
{
lean_object* v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1163_ = lean_int_dec_le(v___x_1162_, v_h_1158_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_dec(v_s_1160_);
lean_dec(v_m_1159_);
v___x_1164_ = lean_box(0);
return v___x_1164_;
}
else
{
lean_object* v___x_1165_; uint8_t v___x_1166_; 
v___x_1165_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1166_ = lean_int_dec_le(v_h_1158_, v___x_1165_);
if (v___x_1166_ == 0)
{
lean_object* v___x_1167_; 
lean_dec(v_s_1160_);
lean_dec(v_m_1159_);
v___x_1167_ = lean_box(0);
return v___x_1167_;
}
else
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1168_ = l_Std_Time_HourMarker_toAbsolute(v_a_1161_, v_h_1158_);
v___x_1169_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1);
v___x_1170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1168_);
lean_ctor_set(v___x_1170_, 1, v_m_1159_);
lean_ctor_set(v___x_1170_, 2, v_s_1160_);
lean_ctor_set(v___x_1170_, 3, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed(lean_object* v_h_1172_, lean_object* v_m_1173_, lean_object* v_s_1174_, lean_object* v_a_1175_){
_start:
{
uint8_t v_a_boxed_1176_; lean_object* v_res_1177_; 
v_a_boxed_1176_ = lean_unbox(v_a_1175_);
v_res_1177_ = l_Std_Time_PlainTime_fromTime12Hour___lam__0(v_h_1172_, v_m_1173_, v_s_1174_, v_a_boxed_1176_);
lean_dec(v_h_1172_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour(lean_object* v_input_1179_){
_start:
{
lean_object* v_builder_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_builder_1180_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime12Hour___closed__0));
v___x_1181_ = l_Std_Time_Formats_time12Hour;
v___x_1182_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1181_, v_builder_1180_, v_input_1179_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime12Hour(lean_object* v_input_1183_){
_start:
{
lean_object* v_hour_1184_; lean_object* v_minute_1185_; lean_object* v_second_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_hour_1184_ = lean_ctor_get(v_input_1183_, 0);
lean_inc(v_hour_1184_);
v_minute_1185_ = lean_ctor_get(v_input_1183_, 1);
lean_inc(v_minute_1185_);
v_second_1186_ = lean_ctor_get(v_input_1183_, 2);
lean_inc(v_second_1186_);
lean_dec_ref(v_input_1183_);
v___x_1187_ = l_Std_Time_Formats_time12Hour;
v___x_1188_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1189_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1190_ = lean_int_emod(v_hour_1184_, v___x_1188_);
v___x_1191_ = lean_int_add(v___x_1190_, v___x_1189_);
lean_dec(v___x_1190_);
v___x_1192_ = lean_int_dec_le(v___x_1188_, v_hour_1184_);
lean_dec(v_hour_1184_);
if (v___x_1192_ == 0)
{
uint8_t v___x_1193_; lean_object* v___x_56__overap_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1193_ = 0;
v___x_56__overap_1194_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1187_);
v___x_1195_ = lean_box(v___x_1193_);
v___x_1196_ = lean_apply_4(v___x_56__overap_1194_, v___x_1191_, v_minute_1185_, v_second_1186_, v___x_1195_);
return v___x_1196_;
}
else
{
uint8_t v___x_1197_; lean_object* v___x_57__overap_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1197_ = 1;
v___x_57__overap_1198_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1187_);
v___x_1199_ = lean_box(v___x_1197_);
v___x_1200_ = lean_apply_4(v___x_57__overap_1198_, v___x_1191_, v_minute_1185_, v_second_1186_, v___x_1199_);
return v___x_1200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_parse(lean_object* v_input_1201_){
_start:
{
lean_object* v___x_1202_; 
lean_inc_ref(v_input_1201_);
v___x_1202_ = l_Std_Time_PlainTime_fromTime12Hour(v_input_1201_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v___x_1203_; 
lean_dec_ref_known(v___x_1202_, 1);
v___x_1203_ = l_Std_Time_PlainTime_fromTime24Hour(v_input_1201_);
return v___x_1203_;
}
else
{
lean_dec_ref(v_input_1201_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0(lean_object* v_data_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1211_ = ((lean_object*)(l_Std_Time_PlainTime_instRepr___lam__0___closed__1));
v___x_1212_ = l_Std_Time_PlainTime_toLeanTime24Hour(v_data_1209_);
v___x_1213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1211_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = l_Repr_addAppParen(v___x_1216_, v___y_1210_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0___boxed(lean_object* v_data_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Std_Time_PlainTime_instRepr___lam__0(v_data_1218_, v___y_1219_);
lean_dec(v___y_1219_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format(lean_object* v_data_1223_, lean_object* v_format_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v_format_1226_; 
v___x_1225_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1226_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1224_, v___x_1225_);
if (lean_obj_tag(v_format_1226_) == 0)
{
lean_object* v_a_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec_ref(v_data_1223_);
v_a_1227_ = lean_ctor_get(v_format_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v_format_1226_, 1);
v___x_1228_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1229_ = lean_string_append(v___x_1228_, v_a_1227_);
lean_dec(v_a_1227_);
return v___x_1229_;
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_a_1230_ = lean_ctor_get(v_format_1226_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v_format_1226_, 1);
v___x_1231_ = lean_box(1);
v___x_1232_ = l_Std_Time_GenericFormat_format(v___x_1231_, v_a_1230_, v_data_1223_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromISO8601String(lean_object* v_input_1233_){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_box(1);
v___x_1235_ = l_Std_Time_Formats_iso8601;
v___x_1236_ = l_Std_Time_GenericFormat_parse(v___x_1234_, v___x_1235_, v_input_1233_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String(lean_object* v_date_1237_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_box(1);
v___x_1239_ = l_Std_Time_Formats_iso8601;
v___x_1240_ = l_Std_Time_GenericFormat_format(v___x_1238_, v___x_1239_, v_date_1237_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC822String(lean_object* v_input_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_box(1);
v___x_1243_ = l_Std_Time_Formats_rfc822;
v___x_1244_ = l_Std_Time_GenericFormat_parse(v___x_1242_, v___x_1243_, v_input_1241_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String(lean_object* v_date_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1246_ = lean_box(1);
v___x_1247_ = l_Std_Time_Formats_rfc822;
v___x_1248_ = l_Std_Time_GenericFormat_format(v___x_1246_, v___x_1247_, v_date_1245_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromRFC850String(lean_object* v_input_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_box(1);
v___x_1251_ = l_Std_Time_Formats_rfc850;
v___x_1252_ = l_Std_Time_GenericFormat_parse(v___x_1250_, v___x_1251_, v_input_1249_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String(lean_object* v_date_1253_){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_box(1);
v___x_1255_ = l_Std_Time_Formats_rfc850;
v___x_1256_ = l_Std_Time_GenericFormat_format(v___x_1254_, v___x_1255_, v_date_1253_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromDateTimeWithZoneString(lean_object* v_input_1257_){
_start:
{
lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = lean_box(1);
v___x_1259_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1260_ = l_Std_Time_GenericFormat_parse(v___x_1258_, v___x_1259_, v_input_1257_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString(lean_object* v_pdt_1261_){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_box(1);
v___x_1263_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1264_ = l_Std_Time_GenericFormat_format(v___x_1262_, v___x_1263_, v_pdt_1261_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithZoneString(lean_object* v_input_1265_){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_box(1);
v___x_1267_ = l_Std_Time_Formats_leanDateTimeWithZone;
lean_inc_ref(v_input_1265_);
v___x_1268_ = l_Std_Time_GenericFormat_parse(v___x_1266_, v___x_1267_, v_input_1265_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec_ref_known(v___x_1268_, 1);
v___x_1269_ = l_Std_Time_Formats_leanDateTimeWithZoneNoNanos;
v___x_1270_ = l_Std_Time_GenericFormat_parse(v___x_1266_, v___x_1269_, v_input_1265_);
return v___x_1270_;
}
else
{
lean_dec_ref(v_input_1265_);
return v___x_1268_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(lean_object* v_input_1271_){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = lean_box(1);
v___x_1273_ = l_Std_Time_Formats_leanDateTimeWithIdentifier;
lean_inc_ref(v_input_1271_);
v___x_1274_ = l_Std_Time_GenericFormat_parse(v___x_1272_, v___x_1273_, v_input_1271_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref_known(v___x_1274_, 1);
v___x_1275_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_1276_ = l_Std_Time_GenericFormat_parse(v___x_1272_, v___x_1275_, v_input_1271_);
return v___x_1276_;
}
else
{
lean_dec_ref(v_input_1271_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString(lean_object* v_zdt_1277_){
_start:
{
lean_object* v_date_1278_; lean_object* v_timezone_1279_; lean_object* v___x_1280_; lean_object* v_date_1281_; lean_object* v_time_1282_; lean_object* v_year_1283_; lean_object* v_month_1284_; lean_object* v_day_1285_; lean_object* v_hour_1286_; lean_object* v_minute_1287_; lean_object* v_second_1288_; lean_object* v_nanosecond_1289_; lean_object* v_offset_1290_; lean_object* v___x_1291_; lean_object* v___x_14__overap_1292_; lean_object* v___x_1293_; 
v_date_1278_ = lean_ctor_get(v_zdt_1277_, 0);
lean_inc_ref(v_date_1278_);
v_timezone_1279_ = lean_ctor_get(v_zdt_1277_, 3);
lean_inc_ref(v_timezone_1279_);
lean_dec_ref(v_zdt_1277_);
v___x_1280_ = lean_thunk_get_own(v_date_1278_);
lean_dec_ref(v_date_1278_);
v_date_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc_ref(v_date_1281_);
v_time_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc_ref(v_time_1282_);
lean_dec(v___x_1280_);
v_year_1283_ = lean_ctor_get(v_date_1281_, 0);
lean_inc(v_year_1283_);
v_month_1284_ = lean_ctor_get(v_date_1281_, 1);
lean_inc(v_month_1284_);
v_day_1285_ = lean_ctor_get(v_date_1281_, 2);
lean_inc(v_day_1285_);
lean_dec_ref(v_date_1281_);
v_hour_1286_ = lean_ctor_get(v_time_1282_, 0);
lean_inc(v_hour_1286_);
v_minute_1287_ = lean_ctor_get(v_time_1282_, 1);
lean_inc(v_minute_1287_);
v_second_1288_ = lean_ctor_get(v_time_1282_, 2);
lean_inc(v_second_1288_);
v_nanosecond_1289_ = lean_ctor_get(v_time_1282_, 3);
lean_inc(v_nanosecond_1289_);
lean_dec_ref(v_time_1282_);
v_offset_1290_ = lean_ctor_get(v_timezone_1279_, 0);
lean_inc(v_offset_1290_);
lean_dec_ref(v_timezone_1279_);
v___x_1291_ = l_Std_Time_Formats_leanDateTimeWithZone;
v___x_14__overap_1292_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1291_);
v___x_1293_ = lean_apply_8(v___x_14__overap_1292_, v_year_1283_, v_month_1284_, v_day_1285_, v_hour_1286_, v_minute_1287_, v_second_1288_, v_nanosecond_1289_, v_offset_1290_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithIdentifierString(lean_object* v_zdt_1294_){
_start:
{
lean_object* v_date_1295_; lean_object* v_timezone_1296_; lean_object* v___x_1297_; lean_object* v_date_1298_; lean_object* v_time_1299_; lean_object* v_year_1300_; lean_object* v_month_1301_; lean_object* v_day_1302_; lean_object* v_hour_1303_; lean_object* v_minute_1304_; lean_object* v_second_1305_; lean_object* v_nanosecond_1306_; lean_object* v_name_1307_; lean_object* v___x_1308_; lean_object* v___x_15__overap_1309_; lean_object* v___x_1310_; 
v_date_1295_ = lean_ctor_get(v_zdt_1294_, 0);
lean_inc_ref(v_date_1295_);
v_timezone_1296_ = lean_ctor_get(v_zdt_1294_, 3);
lean_inc_ref(v_timezone_1296_);
lean_dec_ref(v_zdt_1294_);
v___x_1297_ = lean_thunk_get_own(v_date_1295_);
lean_dec_ref(v_date_1295_);
v_date_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc_ref(v_date_1298_);
v_time_1299_ = lean_ctor_get(v___x_1297_, 1);
lean_inc_ref(v_time_1299_);
lean_dec(v___x_1297_);
v_year_1300_ = lean_ctor_get(v_date_1298_, 0);
lean_inc(v_year_1300_);
v_month_1301_ = lean_ctor_get(v_date_1298_, 1);
lean_inc(v_month_1301_);
v_day_1302_ = lean_ctor_get(v_date_1298_, 2);
lean_inc(v_day_1302_);
lean_dec_ref(v_date_1298_);
v_hour_1303_ = lean_ctor_get(v_time_1299_, 0);
lean_inc(v_hour_1303_);
v_minute_1304_ = lean_ctor_get(v_time_1299_, 1);
lean_inc(v_minute_1304_);
v_second_1305_ = lean_ctor_get(v_time_1299_, 2);
lean_inc(v_second_1305_);
v_nanosecond_1306_ = lean_ctor_get(v_time_1299_, 3);
lean_inc(v_nanosecond_1306_);
lean_dec_ref(v_time_1299_);
v_name_1307_ = lean_ctor_get(v_timezone_1296_, 1);
lean_inc_ref(v_name_1307_);
lean_dec_ref(v_timezone_1296_);
v___x_1308_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_15__overap_1309_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1308_);
v___x_1310_ = lean_apply_8(v___x_15__overap_1309_, v_year_1300_, v_month_1301_, v_day_1302_, v_hour_1303_, v_minute_1304_, v_second_1305_, v_nanosecond_1306_, v_name_1307_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_parse(lean_object* v_input_1311_){
_start:
{
lean_object* v___x_1312_; 
lean_inc_ref(v_input_1311_);
v___x_1312_ = l_Std_Time_DateTime_fromISO8601String(v_input_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1313_; 
lean_dec_ref_known(v___x_1312_, 1);
lean_inc_ref(v_input_1311_);
v___x_1313_ = l_Std_Time_DateTime_fromRFC822String(v_input_1311_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v___x_1314_; 
lean_dec_ref_known(v___x_1313_, 1);
lean_inc_ref(v_input_1311_);
v___x_1314_ = l_Std_Time_DateTime_fromRFC850String(v_input_1311_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref_known(v___x_1314_, 1);
lean_inc_ref(v_input_1311_);
v___x_1315_ = l_Std_Time_DateTime_fromDateTimeWithZoneString(v_input_1311_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1316_; 
lean_dec_ref_known(v___x_1315_, 1);
v___x_1316_ = l_Std_Time_DateTime_fromLeanDateTimeWithIdentifierString(v_input_1311_);
return v___x_1316_;
}
else
{
lean_dec_ref(v_input_1311_);
return v___x_1315_;
}
}
else
{
lean_dec_ref(v_input_1311_);
return v___x_1314_;
}
}
else
{
lean_dec_ref(v_input_1311_);
return v___x_1313_;
}
}
else
{
lean_dec_ref(v_input_1311_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0(lean_object* v_data_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1324_ = ((lean_object*)(l_Std_Time_DateTime_instRepr___lam__0___closed__1));
v___x_1325_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_data_1322_);
v___x_1326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1324_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = l_Repr_addAppParen(v___x_1329_, v___y_1323_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0___boxed(lean_object* v_data_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_Time_DateTime_instRepr___lam__0(v_data_1331_, v___y_1332_);
lean_dec(v___y_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0(lean_object* v_date_1336_, lean_object* v_locale_1337_, lean_object* v_x_1338_){
_start:
{
switch(lean_obj_tag(v_x_1338_))
{
case 0:
{
lean_object* v_date_1339_; lean_object* v_year_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref_known(v_x_1338_, 0);
v_date_1339_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1339_);
lean_dec_ref(v_date_1336_);
v_year_1340_ = lean_ctor_get(v_date_1339_, 0);
lean_inc(v_year_1340_);
lean_dec_ref(v_date_1339_);
v___x_1341_ = l_Std_Time_Year_Offset_era(v_year_1340_);
lean_dec(v_year_1340_);
v___x_1342_ = lean_box(v___x_1341_);
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
return v___x_1343_;
}
case 1:
{
lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1352_; 
v_isSharedCheck_1352_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1353_);
v___x_1345_ = v_x_1338_;
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
else
{
lean_dec(v_x_1338_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1352_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v_date_1347_; lean_object* v_year_1348_; lean_object* v___x_1350_; 
v_date_1347_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1347_);
lean_dec_ref(v_date_1336_);
v_year_1348_ = lean_ctor_get(v_date_1347_, 0);
lean_inc(v_year_1348_);
lean_dec_ref(v_date_1347_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v_year_1348_);
v___x_1350_ = v___x_1345_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_year_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
case 2:
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1362_; 
v_isSharedCheck_1362_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1362_ == 0)
{
lean_object* v_unused_1363_; 
v_unused_1363_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1363_);
v___x_1355_ = v_x_1338_;
v_isShared_1356_ = v_isSharedCheck_1362_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v_x_1338_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1362_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v_date_1357_; lean_object* v_year_1358_; lean_object* v___x_1360_; 
v_date_1357_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1357_);
lean_dec_ref(v_date_1336_);
v_year_1358_ = lean_ctor_get(v_date_1357_, 0);
lean_inc(v_year_1358_);
lean_dec_ref(v_date_1357_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set_tag(v___x_1355_, 1);
lean_ctor_set(v___x_1355_, 0, v_year_1358_);
v___x_1360_ = v___x_1355_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_year_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
case 3:
{
lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1373_; 
v_isSharedCheck_1373_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; 
v_unused_1374_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1374_);
v___x_1365_ = v_x_1338_;
v_isShared_1366_ = v_isSharedCheck_1373_;
goto v_resetjp_1364_;
}
else
{
lean_dec(v_x_1338_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1373_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
uint8_t v_firstDayOfWeek_1367_; lean_object* v_date_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
v_firstDayOfWeek_1367_ = lean_ctor_get_uint8(v_locale_1337_, sizeof(void*)*1);
v_date_1368_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1368_);
lean_dec_ref(v_date_1336_);
v___x_1369_ = l_Std_Time_PlainDate_weekYear(v_date_1368_, v_firstDayOfWeek_1367_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set_tag(v___x_1365_, 1);
lean_ctor_set(v___x_1365_, 0, v___x_1369_);
v___x_1371_ = v___x_1365_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
case 4:
{
lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1426_; 
v_isSharedCheck_1426_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1427_);
v___x_1376_ = v_x_1338_;
v_isShared_1377_ = v_isSharedCheck_1426_;
goto v_resetjp_1375_;
}
else
{
lean_dec(v_x_1338_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1426_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_date_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1424_; 
v_date_1378_ = lean_ctor_get(v_date_1336_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_date_1336_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; 
v_unused_1425_ = lean_ctor_get(v_date_1336_, 1);
lean_dec(v_unused_1425_);
v___x_1380_ = v_date_1336_;
v_isShared_1381_ = v_isSharedCheck_1424_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_date_1378_);
lean_dec(v_date_1336_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1424_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_year_1382_; lean_object* v_month_1383_; lean_object* v_day_1384_; uint8_t v___y_1386_; uint8_t v___y_1387_; uint8_t v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; uint8_t v___y_1405_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1420_; 
v_year_1382_ = lean_ctor_get(v_date_1378_, 0);
lean_inc(v_year_1382_);
v_month_1383_ = lean_ctor_get(v_date_1378_, 1);
lean_inc(v_month_1383_);
v_day_1384_ = lean_ctor_get(v_date_1378_, 2);
lean_inc(v_day_1384_);
lean_dec_ref(v_date_1378_);
v___x_1413_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1414_ = lean_int_mod(v_year_1382_, v___x_1413_);
v___x_1415_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1420_ = lean_int_dec_eq(v___x_1414_, v___x_1415_);
lean_dec(v___x_1414_);
if (v___x_1420_ == 0)
{
v___y_1405_ = v___x_1420_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1421_; lean_object* v___x_1422_; uint8_t v___x_1423_; 
v___x_1421_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1422_ = lean_int_mod(v_year_1382_, v___x_1421_);
v___x_1423_ = lean_int_dec_eq(v___x_1422_, v___x_1415_);
lean_dec(v___x_1422_);
if (v___x_1423_ == 0)
{
if (v___x_1420_ == 0)
{
goto v___jp_1416_;
}
else
{
v___y_1405_ = v___x_1420_;
goto v___jp_1404_;
}
}
else
{
goto v___jp_1416_;
}
}
v___jp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 1, v_day_1384_);
lean_ctor_set(v___x_1380_, 0, v_month_1383_);
v___x_1389_ = v___x_1380_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_month_1383_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_day_1384_);
v___x_1389_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1390_ = l_Std_Time_ValidDate_dayOfYear(v___y_1387_, v___x_1389_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = lean_box(v___y_1386_);
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v___x_1390_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set_tag(v___x_1376_, 1);
lean_ctor_set(v___x_1376_, 0, v___x_1392_);
v___x_1394_ = v___x_1376_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
v___jp_1397_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1401_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1402_ = lean_int_mod(v___y_1400_, v___x_1401_);
lean_dec(v___y_1400_);
v___x_1403_ = lean_int_dec_eq(v___x_1402_, v___y_1399_);
lean_dec(v___x_1402_);
v___y_1386_ = v___y_1398_;
v___y_1387_ = v___x_1403_;
goto v___jp_1385_;
}
v___jp_1404_:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1406_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1407_ = lean_int_mod(v_year_1382_, v___x_1406_);
v___x_1408_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1409_ = lean_int_dec_eq(v___x_1407_, v___x_1408_);
lean_dec(v___x_1407_);
if (v___x_1409_ == 0)
{
lean_dec(v_year_1382_);
v___y_1386_ = v___y_1405_;
v___y_1387_ = v___x_1409_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1410_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1411_ = lean_int_mod(v_year_1382_, v___x_1410_);
v___x_1412_ = lean_int_dec_eq(v___x_1411_, v___x_1408_);
lean_dec(v___x_1411_);
if (v___x_1412_ == 0)
{
if (v___x_1409_ == 0)
{
v___y_1398_ = v___y_1405_;
v___y_1399_ = v___x_1408_;
v___y_1400_ = v_year_1382_;
goto v___jp_1397_;
}
else
{
lean_dec(v_year_1382_);
v___y_1386_ = v___y_1405_;
v___y_1387_ = v___x_1409_;
goto v___jp_1385_;
}
}
else
{
v___y_1398_ = v___y_1405_;
v___y_1399_ = v___x_1408_;
v___y_1400_ = v_year_1382_;
goto v___jp_1397_;
}
}
}
v___jp_1416_:
{
lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v___x_1417_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1418_ = lean_int_mod(v_year_1382_, v___x_1417_);
v___x_1419_ = lean_int_dec_eq(v___x_1418_, v___x_1415_);
lean_dec(v___x_1418_);
v___y_1405_ = v___x_1419_;
goto v___jp_1404_;
}
}
}
}
case 7:
{
lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1436_; 
v_isSharedCheck_1436_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1437_);
v___x_1429_ = v_x_1338_;
v_isShared_1430_ = v_isSharedCheck_1436_;
goto v_resetjp_1428_;
}
else
{
lean_dec(v_x_1338_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1436_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_date_1431_; lean_object* v___x_1432_; lean_object* v___x_1434_; 
v_date_1431_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1431_);
lean_dec_ref(v_date_1336_);
v___x_1432_ = l_Std_Time_PlainDate_quarter(v_date_1431_);
lean_dec_ref(v_date_1431_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 1);
lean_ctor_set(v___x_1429_, 0, v___x_1432_);
v___x_1434_ = v___x_1429_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
case 8:
{
lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1447_; 
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1448_);
v___x_1439_ = v_x_1338_;
v_isShared_1440_ = v_isSharedCheck_1447_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v_x_1338_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1447_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
uint8_t v_firstDayOfWeek_1441_; lean_object* v_date_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v_firstDayOfWeek_1441_ = lean_ctor_get_uint8(v_locale_1337_, sizeof(void*)*1);
v_date_1442_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1442_);
lean_dec_ref(v_date_1336_);
v___x_1443_ = l_Std_Time_PlainDate_weekOfYear(v_date_1442_, v_firstDayOfWeek_1441_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set_tag(v___x_1439_, 1);
lean_ctor_set(v___x_1439_, 0, v___x_1443_);
v___x_1445_ = v___x_1439_;
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
case 9:
{
lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1458_; 
v_isSharedCheck_1458_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1459_);
v___x_1450_ = v_x_1338_;
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v_x_1338_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1458_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
uint8_t v_firstDayOfWeek_1452_; lean_object* v_date_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v_firstDayOfWeek_1452_ = lean_ctor_get_uint8(v_locale_1337_, sizeof(void*)*1);
v_date_1453_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1453_);
lean_dec_ref(v_date_1336_);
v___x_1454_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1453_, v_firstDayOfWeek_1452_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set_tag(v___x_1450_, 1);
lean_ctor_set(v___x_1450_, 0, v___x_1454_);
v___x_1456_ = v___x_1450_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
case 5:
{
lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1468_; 
v_isSharedCheck_1468_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1468_ == 0)
{
lean_object* v_unused_1469_; 
v_unused_1469_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1469_);
v___x_1461_ = v_x_1338_;
v_isShared_1462_ = v_isSharedCheck_1468_;
goto v_resetjp_1460_;
}
else
{
lean_dec(v_x_1338_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1468_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_date_1463_; lean_object* v_month_1464_; lean_object* v___x_1466_; 
v_date_1463_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1463_);
lean_dec_ref(v_date_1336_);
v_month_1464_ = lean_ctor_get(v_date_1463_, 1);
lean_inc(v_month_1464_);
lean_dec_ref(v_date_1463_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 1);
lean_ctor_set(v___x_1461_, 0, v_month_1464_);
v___x_1466_ = v___x_1461_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_month_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
case 6:
{
lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1478_; 
v_isSharedCheck_1478_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1479_);
v___x_1471_ = v_x_1338_;
v_isShared_1472_ = v_isSharedCheck_1478_;
goto v_resetjp_1470_;
}
else
{
lean_dec(v_x_1338_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1478_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v_date_1473_; lean_object* v_day_1474_; lean_object* v___x_1476_; 
v_date_1473_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1473_);
lean_dec_ref(v_date_1336_);
v_day_1474_ = lean_ctor_get(v_date_1473_, 2);
lean_inc(v_day_1474_);
lean_dec_ref(v_date_1473_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set_tag(v___x_1471_, 1);
lean_ctor_set(v___x_1471_, 0, v_day_1474_);
v___x_1476_ = v___x_1471_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_day_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
case 10:
{
lean_object* v_date_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec_ref_known(v_x_1338_, 0);
v_date_1480_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1480_);
lean_dec_ref(v_date_1336_);
v___x_1481_ = l_Std_Time_PlainDate_weekday(v_date_1480_);
v___x_1482_ = lean_box(v___x_1481_);
v___x_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
case 11:
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1493_; 
v_isSharedCheck_1493_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1494_);
v___x_1485_ = v_x_1338_;
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v_x_1338_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_date_1487_; uint8_t v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v_date_1487_ = lean_ctor_get(v_date_1336_, 0);
lean_inc_ref(v_date_1487_);
lean_dec_ref(v_date_1336_);
v___x_1488_ = l_Std_Time_PlainDate_weekday(v_date_1487_);
v___x_1489_ = lean_box(v___x_1488_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set_tag(v___x_1485_, 1);
lean_ctor_set(v___x_1485_, 0, v___x_1489_);
v___x_1491_ = v___x_1485_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
case 12:
{
lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; 
v_unused_1503_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1503_);
v___x_1496_ = v_x_1338_;
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
else
{
lean_dec(v_x_1338_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1336_);
lean_dec_ref(v_date_1336_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 1);
lean_ctor_set(v___x_1496_, 0, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
case 17:
{
lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1512_; 
v_isSharedCheck_1512_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1512_ == 0)
{
lean_object* v_unused_1513_; 
v_unused_1513_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1513_);
v___x_1505_ = v_x_1338_;
v_isShared_1506_ = v_isSharedCheck_1512_;
goto v_resetjp_1504_;
}
else
{
lean_dec(v_x_1338_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1512_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v_time_1507_; lean_object* v_hour_1508_; lean_object* v___x_1510_; 
v_time_1507_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1507_);
lean_dec_ref(v_date_1336_);
v_hour_1508_ = lean_ctor_get(v_time_1507_, 0);
lean_inc(v_hour_1508_);
lean_dec_ref(v_time_1507_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set_tag(v___x_1505_, 1);
lean_ctor_set(v___x_1505_, 0, v_hour_1508_);
v___x_1510_ = v___x_1505_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_hour_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
case 16:
{
lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1523_; 
v_isSharedCheck_1523_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1523_ == 0)
{
lean_object* v_unused_1524_; 
v_unused_1524_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1524_);
v___x_1515_ = v_x_1338_;
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
else
{
lean_dec(v_x_1338_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1523_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_time_1517_; lean_object* v_hour_1518_; lean_object* v___x_1519_; lean_object* v___x_1521_; 
v_time_1517_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1517_);
lean_dec_ref(v_date_1336_);
v_hour_1518_ = lean_ctor_get(v_time_1517_, 0);
lean_inc(v_hour_1518_);
lean_dec_ref(v_time_1517_);
v___x_1519_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1518_);
lean_dec(v_hour_1518_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set_tag(v___x_1515_, 1);
lean_ctor_set(v___x_1515_, 0, v___x_1519_);
v___x_1521_ = v___x_1515_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
case 18:
{
lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1533_; 
v_isSharedCheck_1533_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1533_ == 0)
{
lean_object* v_unused_1534_; 
v_unused_1534_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1534_);
v___x_1526_ = v_x_1338_;
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v_x_1338_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1533_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_time_1528_; lean_object* v_minute_1529_; lean_object* v___x_1531_; 
v_time_1528_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1528_);
lean_dec_ref(v_date_1336_);
v_minute_1529_ = lean_ctor_get(v_time_1528_, 1);
lean_inc(v_minute_1529_);
lean_dec_ref(v_time_1528_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set_tag(v___x_1526_, 1);
lean_ctor_set(v___x_1526_, 0, v_minute_1529_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_minute_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
case 22:
{
lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1543_; 
v_isSharedCheck_1543_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1544_);
v___x_1536_ = v_x_1338_;
v_isShared_1537_ = v_isSharedCheck_1543_;
goto v_resetjp_1535_;
}
else
{
lean_dec(v_x_1338_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1543_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v_time_1538_; lean_object* v_nanosecond_1539_; lean_object* v___x_1541_; 
v_time_1538_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1538_);
lean_dec_ref(v_date_1336_);
v_nanosecond_1539_ = lean_ctor_get(v_time_1538_, 3);
lean_inc(v_nanosecond_1539_);
lean_dec_ref(v_time_1538_);
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 1);
lean_ctor_set(v___x_1536_, 0, v_nanosecond_1539_);
v___x_1541_ = v___x_1536_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_nanosecond_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
case 19:
{
lean_object* v___x_1546_; uint8_t v_isShared_1547_; uint8_t v_isSharedCheck_1553_; 
v_isSharedCheck_1553_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; 
v_unused_1554_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1554_);
v___x_1546_ = v_x_1338_;
v_isShared_1547_ = v_isSharedCheck_1553_;
goto v_resetjp_1545_;
}
else
{
lean_dec(v_x_1338_);
v___x_1546_ = lean_box(0);
v_isShared_1547_ = v_isSharedCheck_1553_;
goto v_resetjp_1545_;
}
v_resetjp_1545_:
{
lean_object* v_time_1548_; lean_object* v_second_1549_; lean_object* v___x_1551_; 
v_time_1548_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1548_);
lean_dec_ref(v_date_1336_);
v_second_1549_ = lean_ctor_get(v_time_1548_, 2);
lean_inc(v_second_1549_);
lean_dec_ref(v_time_1548_);
if (v_isShared_1547_ == 0)
{
lean_ctor_set_tag(v___x_1546_, 1);
lean_ctor_set(v___x_1546_, 0, v_second_1549_);
v___x_1551_ = v___x_1546_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_second_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
case 13:
{
lean_object* v_time_1555_; lean_object* v_hour_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
lean_dec_ref_known(v_x_1338_, 0);
v_time_1555_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1555_);
lean_dec_ref(v_date_1336_);
v_hour_1556_ = lean_ctor_get(v_time_1555_, 0);
lean_inc(v_hour_1556_);
lean_dec_ref(v_time_1555_);
v___x_1557_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1556_);
lean_dec(v_hour_1556_);
v___x_1558_ = lean_box(v___x_1557_);
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
case 14:
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1569_; 
v_isSharedCheck_1569_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1570_);
v___x_1561_ = v_x_1338_;
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v_x_1338_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_time_1563_; lean_object* v_hour_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v_time_1563_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1563_);
lean_dec_ref(v_date_1336_);
v_hour_1564_ = lean_ctor_get(v_time_1563_, 0);
lean_inc(v_hour_1564_);
lean_dec_ref(v_time_1563_);
v___x_1565_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1564_);
lean_dec(v_hour_1564_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set_tag(v___x_1561_, 1);
lean_ctor_set(v___x_1561_, 0, v___x_1565_);
v___x_1567_ = v___x_1561_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
case 15:
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1581_; 
v_isSharedCheck_1581_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; 
v_unused_1582_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1582_);
v___x_1572_ = v_x_1338_;
v_isShared_1573_ = v_isSharedCheck_1581_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v_x_1338_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1581_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_time_1574_; lean_object* v_hour_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1579_; 
v_time_1574_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1574_);
lean_dec_ref(v_date_1336_);
v_hour_1575_ = lean_ctor_get(v_time_1574_, 0);
lean_inc(v_hour_1575_);
lean_dec_ref(v_time_1574_);
v___x_1576_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1577_ = lean_int_emod(v_hour_1575_, v___x_1576_);
lean_dec(v_hour_1575_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 1);
lean_ctor_set(v___x_1572_, 0, v___x_1577_);
v___x_1579_ = v___x_1572_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
case 20:
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1591_; 
v_isSharedCheck_1591_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1592_);
v___x_1584_ = v_x_1338_;
v_isShared_1585_ = v_isSharedCheck_1591_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v_x_1338_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1591_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_time_1586_; lean_object* v_nanosecond_1587_; lean_object* v___x_1589_; 
v_time_1586_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1586_);
lean_dec_ref(v_date_1336_);
v_nanosecond_1587_ = lean_ctor_get(v_time_1586_, 3);
lean_inc(v_nanosecond_1587_);
lean_dec_ref(v_time_1586_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 1);
lean_ctor_set(v___x_1584_, 0, v_nanosecond_1587_);
v___x_1589_ = v___x_1584_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_nanosecond_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
case 21:
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1601_; 
v_isSharedCheck_1601_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1602_);
v___x_1594_ = v_x_1338_;
v_isShared_1595_ = v_isSharedCheck_1601_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v_x_1338_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1601_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_time_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v_time_1596_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1596_);
lean_dec_ref(v_date_1336_);
v___x_1597_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1596_);
lean_dec_ref(v_time_1596_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 1);
lean_ctor_set(v___x_1594_, 0, v___x_1597_);
v___x_1599_ = v___x_1594_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
case 23:
{
lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1611_; 
v_isSharedCheck_1611_ = !lean_is_exclusive(v_x_1338_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v_x_1338_, 0);
lean_dec(v_unused_1612_);
v___x_1604_ = v_x_1338_;
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
else
{
lean_dec(v_x_1338_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1611_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_time_1606_; lean_object* v___x_1607_; lean_object* v___x_1609_; 
v_time_1606_ = lean_ctor_get(v_date_1336_, 1);
lean_inc_ref(v_time_1606_);
lean_dec_ref(v_date_1336_);
v___x_1607_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1606_);
lean_dec_ref(v_time_1606_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 1);
lean_ctor_set(v___x_1604_, 0, v___x_1607_);
v___x_1609_ = v___x_1604_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
default: 
{
lean_object* v___x_1613_; 
lean_dec(v_x_1338_);
lean_dec_ref(v_date_1336_);
v___x_1613_ = lean_box(0);
return v___x_1613_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0___boxed(lean_object* v_date_1614_, lean_object* v_locale_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Std_Time_PlainDateTime_format___lam__0(v_date_1614_, v_locale_1615_, v_x_1616_);
lean_dec_ref(v_locale_1615_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format(lean_object* v_date_1618_, lean_object* v_format_1619_, lean_object* v_locale_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v_format_1622_; 
v___x_1621_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1622_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1619_, v___x_1621_);
if (lean_obj_tag(v_format_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec_ref(v_locale_1620_);
lean_dec_ref(v_date_1618_);
v_a_1623_ = lean_ctor_get(v_format_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v_format_1622_, 1);
v___x_1624_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1625_ = lean_string_append(v___x_1624_, v_a_1623_);
lean_dec(v_a_1623_);
return v___x_1625_;
}
else
{
lean_object* v_a_1626_; lean_object* v___f_1627_; lean_object* v_res_1628_; 
v_a_1626_ = lean_ctor_get(v_format_1622_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v_format_1622_, 1);
v___f_1627_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1627_, 0, v_date_1618_);
lean_closure_set(v___f_1627_, 1, v_locale_1620_);
v_res_1628_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1626_, v___f_1627_);
if (lean_obj_tag(v_res_1628_) == 0)
{
lean_object* v___x_1629_; 
v___x_1629_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1629_;
}
else
{
lean_object* v_val_1630_; 
v_val_1630_ = lean_ctor_get(v_res_1628_, 0);
lean_inc(v_val_1630_);
lean_dec_ref_known(v_res_1628_, 1);
return v_val_1630_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = l_Std_Time_TimeZone_GMT;
v___x_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromAscTimeString(lean_object* v_input_1633_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1634_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1635_ = l_Std_Time_Formats_ascTime;
v___x_1636_ = l_Std_Time_GenericFormat_parse(v___x_1634_, v___x_1635_, v_input_1633_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1654_; 
v_a_1645_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1647_ = v___x_1636_;
v_isShared_1648_ = v_isSharedCheck_1654_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1636_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1654_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v_date_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
v_date_1649_ = lean_ctor_get(v_a_1645_, 0);
lean_inc_ref(v_date_1649_);
lean_dec(v_a_1645_);
v___x_1650_ = lean_thunk_get_own(v_date_1649_);
lean_dec_ref(v_date_1649_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1650_);
v___x_1652_ = v___x_1647_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0(lean_object* v_pdt_1655_, lean_object* v_x_1656_){
_start:
{
lean_inc_ref(v_pdt_1655_);
return v_pdt_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(lean_object* v_pdt_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_Time_PlainDateTime_toAscTimeString___lam__0(v_pdt_1657_, v_x_1658_);
lean_dec_ref(v_pdt_1657_);
return v_res_1659_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1663_ = lean_int_neg(v___x_1662_);
return v___x_1663_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_unsigned_to_nat(1000000000u);
v___x_1665_ = lean_nat_to_int(v___x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString(lean_object* v_pdt_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v_offset_1668_; lean_object* v_name_1669_; lean_object* v_abbreviation_1670_; uint8_t v_isDST_1671_; uint8_t v___x_1672_; uint8_t v___x_1673_; lean_object* v_ltt_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v_wt_1677_; lean_object* v_ltt_1678_; lean_object* v_tz_1679_; lean_object* v_offset_1680_; lean_object* v_second_1681_; lean_object* v_nano_1682_; lean_object* v___f_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1667_ = l_Std_Time_TimeZone_UTC;
v_offset_1668_ = lean_ctor_get(v___x_1667_, 0);
v_name_1669_ = lean_ctor_get(v___x_1667_, 1);
v_abbreviation_1670_ = lean_ctor_get(v___x_1667_, 2);
v_isDST_1671_ = lean_ctor_get_uint8(v___x_1667_, sizeof(void*)*3);
v___x_1672_ = 0;
v___x_1673_ = 1;
lean_inc_ref(v_name_1669_);
lean_inc_ref(v_abbreviation_1670_);
lean_inc(v_offset_1668_);
v_ltt_1674_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_1674_, 0, v_offset_1668_);
lean_ctor_set(v_ltt_1674_, 1, v_abbreviation_1670_);
lean_ctor_set(v_ltt_1674_, 2, v_name_1669_);
lean_ctor_set_uint8(v_ltt_1674_, sizeof(void*)*3, v_isDST_1671_);
lean_ctor_set_uint8(v_ltt_1674_, sizeof(void*)*3 + 1, v___x_1672_);
lean_ctor_set_uint8(v_ltt_1674_, sizeof(void*)*3 + 2, v___x_1673_);
v___x_1675_ = ((lean_object*)(l_Std_Time_PlainDateTime_toAscTimeString___closed__0));
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_ltt_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
lean_inc_ref(v_pdt_1666_);
v_wt_1677_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1666_);
lean_inc_ref(v___x_1676_);
v_ltt_1678_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1676_, v_wt_1677_);
v_tz_1679_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1678_);
lean_dec_ref(v_ltt_1678_);
v_offset_1680_ = lean_ctor_get(v_tz_1679_, 0);
lean_inc(v_offset_1680_);
v_second_1681_ = lean_ctor_get(v_wt_1677_, 0);
lean_inc(v_second_1681_);
v_nano_1682_ = lean_ctor_get(v_wt_1677_, 1);
lean_inc(v_nano_1682_);
lean_dec_ref(v_wt_1677_);
v___f_1683_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1683_, 0, v_pdt_1666_);
v___x_1684_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1685_ = l_Std_Time_Formats_ascTime;
v___x_1686_ = lean_mk_thunk(v___f_1683_);
v___x_1687_ = lean_int_neg(v_offset_1680_);
lean_dec(v_offset_1680_);
v___x_1688_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__1, &l_Std_Time_PlainDateTime_toAscTimeString___closed__1_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1);
v___x_1689_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__2, &l_Std_Time_PlainDateTime_toAscTimeString___closed__2_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2);
v___x_1690_ = lean_int_mul(v_second_1681_, v___x_1689_);
lean_dec(v_second_1681_);
v___x_1691_ = lean_int_add(v___x_1690_, v_nano_1682_);
lean_dec(v_nano_1682_);
lean_dec(v___x_1690_);
v___x_1692_ = lean_int_mul(v___x_1687_, v___x_1689_);
lean_dec(v___x_1687_);
v___x_1693_ = lean_int_add(v___x_1692_, v___x_1688_);
lean_dec(v___x_1692_);
v___x_1694_ = lean_int_add(v___x_1691_, v___x_1693_);
lean_dec(v___x_1693_);
lean_dec(v___x_1691_);
v___x_1695_ = l_Std_Time_Duration_ofNanoseconds(v___x_1694_);
lean_dec(v___x_1694_);
v___x_1696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1686_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
lean_ctor_set(v___x_1696_, 2, v___x_1676_);
lean_ctor_set(v___x_1696_, 3, v_tz_1679_);
v___x_1697_ = l_Std_Time_GenericFormat_format(v___x_1684_, v___x_1685_, v___x_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLongDateFormatString(lean_object* v_input_1698_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1700_ = l_Std_Time_Formats_longDateFormat;
v___x_1701_ = l_Std_Time_GenericFormat_parse(v___x_1699_, v___x_1700_, v_input_1698_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1719_; 
v_a_1710_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1712_ = v___x_1701_;
v_isShared_1713_ = v_isSharedCheck_1719_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1701_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1719_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_date_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v_date_1714_ = lean_ctor_get(v_a_1710_, 0);
lean_inc_ref(v_date_1714_);
lean_dec(v_a_1710_);
v___x_1715_ = lean_thunk_get_own(v_date_1714_);
lean_dec_ref(v_date_1714_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 0, v___x_1715_);
v___x_1717_ = v___x_1712_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLongDateFormatString(lean_object* v_pdt_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v_offset_1722_; lean_object* v_name_1723_; lean_object* v_abbreviation_1724_; uint8_t v_isDST_1725_; uint8_t v___x_1726_; uint8_t v___x_1727_; lean_object* v_ltt_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v_wt_1731_; lean_object* v_ltt_1732_; lean_object* v_tz_1733_; lean_object* v_offset_1734_; lean_object* v_second_1735_; lean_object* v_nano_1736_; lean_object* v___f_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1721_ = l_Std_Time_TimeZone_UTC;
v_offset_1722_ = lean_ctor_get(v___x_1721_, 0);
v_name_1723_ = lean_ctor_get(v___x_1721_, 1);
v_abbreviation_1724_ = lean_ctor_get(v___x_1721_, 2);
v_isDST_1725_ = lean_ctor_get_uint8(v___x_1721_, sizeof(void*)*3);
v___x_1726_ = 0;
v___x_1727_ = 1;
lean_inc_ref(v_name_1723_);
lean_inc_ref(v_abbreviation_1724_);
lean_inc(v_offset_1722_);
v_ltt_1728_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_ltt_1728_, 0, v_offset_1722_);
lean_ctor_set(v_ltt_1728_, 1, v_abbreviation_1724_);
lean_ctor_set(v_ltt_1728_, 2, v_name_1723_);
lean_ctor_set_uint8(v_ltt_1728_, sizeof(void*)*3, v_isDST_1725_);
lean_ctor_set_uint8(v_ltt_1728_, sizeof(void*)*3 + 1, v___x_1726_);
lean_ctor_set_uint8(v_ltt_1728_, sizeof(void*)*3 + 2, v___x_1727_);
v___x_1729_ = ((lean_object*)(l_Std_Time_PlainDateTime_toAscTimeString___closed__0));
v___x_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_ltt_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
lean_inc_ref(v_pdt_1720_);
v_wt_1731_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1720_);
lean_inc_ref(v___x_1730_);
v_ltt_1732_ = l_Std_Time_TimeZone_ZoneRules_findLocalTimeTypeForWallTime(v___x_1730_, v_wt_1731_);
v_tz_1733_ = l_Std_Time_TimeZone_LocalTimeType_getTimeZone(v_ltt_1732_);
lean_dec_ref(v_ltt_1732_);
v_offset_1734_ = lean_ctor_get(v_tz_1733_, 0);
lean_inc(v_offset_1734_);
v_second_1735_ = lean_ctor_get(v_wt_1731_, 0);
lean_inc(v_second_1735_);
v_nano_1736_ = lean_ctor_get(v_wt_1731_, 1);
lean_inc(v_nano_1736_);
lean_dec_ref(v_wt_1731_);
v___f_1737_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1737_, 0, v_pdt_1720_);
v___x_1738_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1739_ = l_Std_Time_Formats_longDateFormat;
v___x_1740_ = lean_mk_thunk(v___f_1737_);
v___x_1741_ = lean_int_neg(v_offset_1734_);
lean_dec(v_offset_1734_);
v___x_1742_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__1, &l_Std_Time_PlainDateTime_toAscTimeString___closed__1_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__1);
v___x_1743_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__2, &l_Std_Time_PlainDateTime_toAscTimeString___closed__2_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__2);
v___x_1744_ = lean_int_mul(v_second_1735_, v___x_1743_);
lean_dec(v_second_1735_);
v___x_1745_ = lean_int_add(v___x_1744_, v_nano_1736_);
lean_dec(v_nano_1736_);
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
v___x_1750_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1740_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
lean_ctor_set(v___x_1750_, 2, v___x_1730_);
lean_ctor_set(v___x_1750_, 3, v_tz_1733_);
v___x_1751_ = l_Std_Time_GenericFormat_format(v___x_1738_, v___x_1739_, v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromDateTimeString(lean_object* v_input_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1754_ = l_Std_Time_Formats_dateTime24Hour;
v___x_1755_ = l_Std_Time_GenericFormat_parse(v___x_1753_, v___x_1754_, v_input_1752_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1773_; 
v_a_1764_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1766_ = v___x_1755_;
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1755_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1773_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v_date_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v_date_1768_ = lean_ctor_get(v_a_1764_, 0);
lean_inc_ref(v_date_1768_);
lean_dec(v_a_1764_);
v___x_1769_ = lean_thunk_get_own(v_date_1768_);
lean_dec_ref(v_date_1768_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1769_);
v___x_1771_ = v___x_1766_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toDateTimeString(lean_object* v_pdt_1774_){
_start:
{
lean_object* v_date_1775_; lean_object* v_time_1776_; lean_object* v_year_1777_; lean_object* v_month_1778_; lean_object* v_day_1779_; lean_object* v_hour_1780_; lean_object* v_minute_1781_; lean_object* v_second_1782_; lean_object* v_nanosecond_1783_; lean_object* v___x_1784_; lean_object* v___x_12__overap_1785_; lean_object* v___x_1786_; 
v_date_1775_ = lean_ctor_get(v_pdt_1774_, 0);
lean_inc_ref(v_date_1775_);
v_time_1776_ = lean_ctor_get(v_pdt_1774_, 1);
lean_inc_ref(v_time_1776_);
lean_dec_ref(v_pdt_1774_);
v_year_1777_ = lean_ctor_get(v_date_1775_, 0);
lean_inc(v_year_1777_);
v_month_1778_ = lean_ctor_get(v_date_1775_, 1);
lean_inc(v_month_1778_);
v_day_1779_ = lean_ctor_get(v_date_1775_, 2);
lean_inc(v_day_1779_);
lean_dec_ref(v_date_1775_);
v_hour_1780_ = lean_ctor_get(v_time_1776_, 0);
lean_inc(v_hour_1780_);
v_minute_1781_ = lean_ctor_get(v_time_1776_, 1);
lean_inc(v_minute_1781_);
v_second_1782_ = lean_ctor_get(v_time_1776_, 2);
lean_inc(v_second_1782_);
v_nanosecond_1783_ = lean_ctor_get(v_time_1776_, 3);
lean_inc(v_nanosecond_1783_);
lean_dec_ref(v_time_1776_);
v___x_1784_ = l_Std_Time_Formats_dateTime24Hour;
v___x_12__overap_1785_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1784_);
v___x_1786_ = lean_apply_7(v___x_12__overap_1785_, v_year_1777_, v_month_1778_, v_day_1779_, v_hour_1780_, v_minute_1781_, v_second_1782_, v_nanosecond_1783_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLeanDateTimeString(lean_object* v_input_1787_){
_start:
{
lean_object* v___y_1789_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1809_ = l_Std_Time_Formats_leanDateTime24Hour;
lean_inc_ref(v_input_1787_);
v___x_1810_ = l_Std_Time_GenericFormat_parse(v___x_1808_, v___x_1809_, v_input_1787_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_dec_ref_known(v___x_1810_, 1);
v___x_1811_ = l_Std_Time_Formats_leanDateTime24HourNoNanos;
v___x_1812_ = l_Std_Time_GenericFormat_parse(v___x_1808_, v___x_1811_, v_input_1787_);
v___y_1789_ = v___x_1812_;
goto v___jp_1788_;
}
else
{
lean_dec_ref(v_input_1787_);
v___y_1789_ = v___x_1810_;
goto v___jp_1788_;
}
v___jp_1788_:
{
if (lean_obj_tag(v___y_1789_) == 0)
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
v_a_1790_ = lean_ctor_get(v___y_1789_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___y_1789_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___y_1789_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___y_1789_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1807_; 
v_a_1798_ = lean_ctor_get(v___y_1789_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___y_1789_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1800_ = v___y_1789_;
v_isShared_1801_ = v_isSharedCheck_1807_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___y_1789_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1807_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v_date_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v_date_1802_ = lean_ctor_get(v_a_1798_, 0);
lean_inc_ref(v_date_1802_);
lean_dec(v_a_1798_);
v___x_1803_ = lean_thunk_get_own(v_date_1802_);
lean_dec_ref(v_date_1802_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1803_);
v___x_1805_ = v___x_1800_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLeanDateTimeString(lean_object* v_pdt_1813_){
_start:
{
lean_object* v_date_1814_; lean_object* v_time_1815_; lean_object* v_year_1816_; lean_object* v_month_1817_; lean_object* v_day_1818_; lean_object* v_hour_1819_; lean_object* v_minute_1820_; lean_object* v_second_1821_; lean_object* v_nanosecond_1822_; lean_object* v___x_1823_; lean_object* v___x_12__overap_1824_; lean_object* v___x_1825_; 
v_date_1814_ = lean_ctor_get(v_pdt_1813_, 0);
lean_inc_ref(v_date_1814_);
v_time_1815_ = lean_ctor_get(v_pdt_1813_, 1);
lean_inc_ref(v_time_1815_);
lean_dec_ref(v_pdt_1813_);
v_year_1816_ = lean_ctor_get(v_date_1814_, 0);
lean_inc(v_year_1816_);
v_month_1817_ = lean_ctor_get(v_date_1814_, 1);
lean_inc(v_month_1817_);
v_day_1818_ = lean_ctor_get(v_date_1814_, 2);
lean_inc(v_day_1818_);
lean_dec_ref(v_date_1814_);
v_hour_1819_ = lean_ctor_get(v_time_1815_, 0);
lean_inc(v_hour_1819_);
v_minute_1820_ = lean_ctor_get(v_time_1815_, 1);
lean_inc(v_minute_1820_);
v_second_1821_ = lean_ctor_get(v_time_1815_, 2);
lean_inc(v_second_1821_);
v_nanosecond_1822_ = lean_ctor_get(v_time_1815_, 3);
lean_inc(v_nanosecond_1822_);
lean_dec_ref(v_time_1815_);
v___x_1823_ = l_Std_Time_Formats_leanDateTime24Hour;
v___x_12__overap_1824_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1823_);
v___x_1825_ = lean_apply_7(v___x_12__overap_1824_, v_year_1816_, v_month_1817_, v_day_1818_, v_hour_1819_, v_minute_1820_, v_second_1821_, v_nanosecond_1822_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_parse(lean_object* v_date_1826_){
_start:
{
lean_object* v___x_1827_; 
lean_inc_ref(v_date_1826_);
v___x_1827_ = l_Std_Time_PlainDateTime_fromAscTimeString(v_date_1826_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v___x_1828_; 
lean_dec_ref_known(v___x_1827_, 1);
lean_inc_ref(v_date_1826_);
v___x_1828_ = l_Std_Time_PlainDateTime_fromLongDateFormatString(v_date_1826_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v___x_1829_; 
lean_dec_ref_known(v___x_1828_, 1);
lean_inc_ref(v_date_1826_);
v___x_1829_ = l_Std_Time_PlainDateTime_fromDateTimeString(v_date_1826_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1830_; 
lean_dec_ref_known(v___x_1829_, 1);
v___x_1830_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v_date_1826_);
return v___x_1830_;
}
else
{
lean_dec_ref(v_date_1826_);
return v___x_1829_;
}
}
else
{
lean_dec_ref(v_date_1826_);
return v___x_1828_;
}
}
else
{
lean_dec_ref(v_date_1826_);
return v___x_1827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0(lean_object* v_data_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1838_ = ((lean_object*)(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1));
v___x_1839_ = l_Std_Time_PlainDateTime_toLeanDateTimeString(v_data_1836_);
v___x_1840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
v___x_1841_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1838_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1843_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = l_Repr_addAppParen(v___x_1843_, v___y_1837_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0___boxed(lean_object* v_data_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Std_Time_PlainDateTime_instRepr___lam__0(v_data_1845_, v___y_1846_);
lean_dec(v___y_1846_);
return v_res_1847_;
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

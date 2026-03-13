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
lean_object* l_Std_Time_GenericFormat_formatBuilder___redArg(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_GenericFormat_parseBuilder___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*);
extern lean_object* l_Std_Time_TimeZone_GMT;
lean_object* l_Std_Time_GenericFormat_format(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_PlainDateTime_toTimestampAssumingUTC(lean_object*);
lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_GenericFormat_parse(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__0 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__1 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value;
static const lean_string_object l_Std_Time_Formats_iso8601___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_Formats_iso8601___closed__2 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__3 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__4 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__5 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__6 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__7 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__8 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value;
static const lean_string_object l_Std_Time_Formats_iso8601___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "T"};
static const lean_object* l_Std_Time_Formats_iso8601___closed__9 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__10 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 16}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__11 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__12 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value;
static const lean_string_object l_Std_Time_Formats_iso8601___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Time_Formats_iso8601___closed__13 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__14 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 17}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__15 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__15_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__16 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__17 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__17_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__18 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 26}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__19 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__19_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__20 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__20_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__21 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__21_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__21_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__22 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__22_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__22_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__23 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__23_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__23_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__24 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__24_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__24_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__25 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__25_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__25_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__26 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__26_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__26_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__27 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__27_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__27_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__28 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__28_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__28_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__29 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__29_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__29_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__30 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__30_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__30_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__31 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__31_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_iso8601___closed__31_value)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__32 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__32_value;
static const lean_ctor_object l_Std_Time_Formats_iso8601___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__32_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_iso8601___closed__33 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__33_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_iso8601 = (const lean_object*)&l_Std_Time_Formats_iso8601___closed__33_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__0 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__1 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__2 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__3 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__4 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_americanDate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_americanDate___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_americanDate___closed__5 = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_americanDate = (const lean_object*)&l_Std_Time_Formats_americanDate___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_europeanDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_americanDate___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_europeanDate___closed__0 = (const lean_object*)&l_Std_Time_Formats_europeanDate___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_europeanDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_europeanDate___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_europeanDate___closed__1 = (const lean_object*)&l_Std_Time_Formats_europeanDate___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_europeanDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_europeanDate___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_europeanDate___closed__2 = (const lean_object*)&l_Std_Time_Formats_europeanDate___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_europeanDate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_europeanDate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_europeanDate___closed__3 = (const lean_object*)&l_Std_Time_Formats_europeanDate___closed__3_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_europeanDate = (const lean_object*)&l_Std_Time_Formats_europeanDate___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 13}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__1 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__1_value;
static const lean_string_object l_Std_Time_Formats_time12Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__2 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__3 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 12}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__4 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__5 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__6 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__7 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__8 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__9 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__10 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__11 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_time12Hour___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__12 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_time12Hour___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__12_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_time12Hour___closed__13 = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__13_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_time12Hour = (const lean_object*)&l_Std_Time_Formats_time12Hour___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__1 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__2 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__3 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__4 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_time24Hour___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time24Hour___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_time24Hour___closed__5 = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_time24Hour = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__5_value;
static const lean_string_object l_Std_Time_Formats_dateTime24Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__1 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 19}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__2 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__3 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__4 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__5 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__6 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__7 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__8 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__9 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__10 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__11 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__12 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__13 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__14 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__15 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__15_value)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__16 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__16_value;
static const lean_ctor_object l_Std_Time_Formats_dateTime24Hour___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__16_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_dateTime24Hour___closed__17 = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__17_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_dateTime24Hour = (const lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__17_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 28}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__0 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__1 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__2 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__3 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__4 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__5 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__6 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__7 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__8 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__9 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__10 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__11 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__12 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__13 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__14 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__15 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_dateTimeWithZone___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_dateTimeWithZone___closed__16 = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__16_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_dateTimeWithZone = (const lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__16_value;
static const lean_ctor_object l_Std_Time_Formats_leanTime24Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__10_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanTime24Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanTime24Hour___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_leanTime24Hour = (const lean_object*)&l_Std_Time_Formats_leanTime24Hour___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_leanTime24HourNoNanos = (const lean_object*)&l_Std_Time_Formats_time24Hour___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value),((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24Hour___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24Hour___closed__6 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_leanDateTime24Hour = (const lean_object*)&l_Std_Time_Formats_leanDateTime24Hour___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6 = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_leanDateTime24HourNoNanos = (const lean_object*)&l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 28}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__6 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__7 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__8 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__9 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__10 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__11 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__12 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__13 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__14 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__15 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZone___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZone___closed__16 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__16_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_leanDateTimeWithZone = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__16_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_leanDateTimeWithZoneNoNanos = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11_value;
static const lean_string_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 24}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifier = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_dateTime24Hour___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__10_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13 = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos = (const lean_object*)&l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__0 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDate___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__1 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_leanDate___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__2 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDate___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__3 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_leanDate___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__4 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_leanDate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_leanDate___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_leanDate___closed__5 = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_leanDate = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_sqlDate = (const lean_object*)&l_Std_Time_Formats_leanDate___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 9}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__7 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__8 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_time24Hour___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__9 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__9_value)}};
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
static const lean_ctor_object l_Std_Time_Formats_longDateFormat___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__16_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_longDateFormat___closed__17 = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__17_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_longDateFormat = (const lean_object*)&l_Std_Time_Formats_longDateFormat___closed__17_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 9}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__6 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__7 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__8 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__9 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_ascTime___closed__9_value)}};
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
static const lean_ctor_object l_Std_Time_Formats_ascTime___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__16_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_ascTime___closed__17 = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__17_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_ascTime = (const lean_object*)&l_Std_Time_Formats_ascTime___closed__17_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 10}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__0 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__1 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_dateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__2 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__18_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__3 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__4 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__16_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__5 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__14_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__5_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__6 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__6_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__12_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__6_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__7 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__7_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__7_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__8 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__8_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__1_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__8_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__9 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__9_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__10 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__10_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_ascTime___closed__4_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__10_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__11 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__11_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__11_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__12 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__12_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__12_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__13 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__13_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__13_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__14 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__14_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__1_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__14_value)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__15 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__15_value;
static const lean_ctor_object l_Std_Time_Formats_rfc822___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__15_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_rfc822___closed__16 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__16_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_rfc822 = (const lean_object*)&l_Std_Time_Formats_rfc822___closed__16_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc822___closed__9_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__0 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__0_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__6_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__0_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__1 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__1_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__1_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__2 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__2_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_iso8601___closed__8_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__2_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__3 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__3_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_longDateFormat___closed__3_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__3_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__4 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__4_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc822___closed__1_value),((lean_object*)&l_Std_Time_Formats_rfc850___closed__4_value)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__5 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__5_value;
static const lean_ctor_object l_Std_Time_Formats_rfc850___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_Formats_rfc850___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_Formats_rfc850___closed__6 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Time_Formats_rfc850 = (const lean_object*)&l_Std_Time_Formats_rfc850___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_fromTimeZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(23) << 1) | 1))}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_Formats_time12Hour___closed__3_value),((lean_object*)&l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__1_value),((lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__3_value;
static const lean_ctor_object l_Std_Time_TimeZone_fromTimeZone___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_TimeZone_fromTimeZone___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_fromTimeZone___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset___lam__0(lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_Offset_fromOffset___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value;
static const lean_ctor_object l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 27}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(2, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_Offset_fromOffset___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__3_value;
static const lean_ctor_object l_Std_Time_TimeZone_Offset_fromOffset___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_TimeZone_Offset_fromOffset___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_Offset_fromOffset___closed__4_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset(lean_object*);
static lean_once_cell_t l_Std_Time_PlainDate_format___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_format___lam__0___closed__0;
static lean_once_cell_t l_Std_Time_PlainDate_format___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_format___lam__0___closed__1;
static lean_once_cell_t l_Std_Time_PlainDate_format___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_format___lam__0___closed__2;
static lean_once_cell_t l_Std_Time_PlainDate_format___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDate_format___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_PlainDate_format___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "error: "};
static const lean_object* l_Std_Time_PlainDate_format___closed__0 = (const lean_object*)&l_Std_Time_PlainDate_format___closed__0_value;
static const lean_string_object l_Std_Time_PlainDate_format___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invalid time"};
static const lean_object* l_Std_Time_PlainDate_format___closed__1 = (const lean_object*)&l_Std_Time_PlainDate_format___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_ZonedDateTime_format___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_format___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_format___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_format(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromISO8601String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toISO8601String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromRFC822String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toRFC822String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromRFC850String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toRFC850String(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromDateTimeWithZoneString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTimeWithZoneString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromLeanDateTimeWithZoneString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toLeanDateTimeWithZoneString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toLeanDateTimeWithIdentifierString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_parse(lean_object*);
static const lean_closure_object l_Std_Time_ZonedDateTime_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_toLeanDateTimeWithIdentifierString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instToString___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instToString = (const lean_object*)&l_Std_Time_ZonedDateTime_instToString___closed__0_value;
static const lean_string_object l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "zoned(\""};
static const lean_object* l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0_value)}};
static const lean_object* l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1 = (const lean_object*)&l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instRepr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instRepr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_ZonedDateTime_instRepr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_ZonedDateTime_instRepr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_ZonedDateTime_instRepr___closed__0 = (const lean_object*)&l_Std_Time_ZonedDateTime_instRepr___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_ZonedDateTime_instRepr = (const lean_object*)&l_Std_Time_ZonedDateTime_instRepr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_fromAscTimeString___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromAscTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromAscTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toAscTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLongDateFormatString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLongDateFormatString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_parse(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instToString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0(uint8_t v___x_691_, lean_object* v_id_692_, lean_object* v_off_693_){
_start:
{
uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_694_ = 1;
lean_inc(v_off_693_);
v___x_695_ = l_Std_Time_TimeZone_Offset_toIsoString(v_off_693_, v___x_694_);
v___x_696_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_696_, 0, v_off_693_);
lean_ctor_set(v___x_696_, 1, v_id_692_);
lean_ctor_set(v___x_696_, 2, v___x_695_);
lean_ctor_set_uint8(v___x_696_, sizeof(void*)*3, v___x_691_);
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed(lean_object* v___x_698_, lean_object* v_id_699_, lean_object* v_off_700_){
_start:
{
uint8_t v___x_28__boxed_701_; lean_object* v_res_702_; 
v___x_28__boxed_701_ = lean_unbox(v___x_698_);
v_res_702_ = l_Std_Time_TimeZone_fromTimeZone___lam__0(v___x_28__boxed_701_, v_id_699_, v_off_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_fromTimeZone(lean_object* v_input_717_){
_start:
{
lean_object* v___f_718_; lean_object* v_spec_719_; lean_object* v___x_720_; 
v___f_718_ = ((lean_object*)(l_Std_Time_TimeZone_fromTimeZone___closed__0));
v_spec_719_ = ((lean_object*)(l_Std_Time_TimeZone_fromTimeZone___closed__4));
v___x_720_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_719_, v___f_718_, v_input_717_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset___lam__0(lean_object* v_val_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v_val_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_fromOffset(lean_object* v_input_734_){
_start:
{
lean_object* v___f_735_; lean_object* v_spec_736_; lean_object* v___x_737_; 
v___f_735_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_fromOffset___closed__0));
v_spec_736_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_fromOffset___closed__4));
v___x_737_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_736_, v___f_735_, v_input_734_);
return v___x_737_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(4u);
v___x_739_ = lean_nat_to_int(v___x_738_);
return v___x_739_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__1(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_nat_to_int(v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__2(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(400u);
v___x_743_ = lean_nat_to_int(v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Std_Time_PlainDate_format___lam__0___closed__3(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_unsigned_to_nat(100u);
v___x_745_ = lean_nat_to_int(v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format___lam__0(lean_object* v_date_746_, lean_object* v_x_747_){
_start:
{
uint8_t v___y_749_; 
switch(lean_obj_tag(v_x_747_))
{
case 0:
{
lean_object* v_year_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
lean_dec_ref(v_x_747_);
v_year_754_ = lean_ctor_get(v_date_746_, 0);
lean_inc(v_year_754_);
lean_dec_ref(v_date_746_);
v___x_755_ = l_Std_Time_Year_Offset_era(v_year_754_);
lean_dec(v_year_754_);
v___x_756_ = lean_box(v___x_755_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
case 1:
{
lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_isSharedCheck_765_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_766_);
v___x_759_ = v_x_747_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_dec(v_x_747_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_year_761_; lean_object* v___x_763_; 
v_year_761_ = lean_ctor_get(v_date_746_, 0);
lean_inc(v_year_761_);
lean_dec_ref(v_date_746_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v_year_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_year_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
case 2:
{
lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_774_; 
v_isSharedCheck_774_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_775_);
v___x_768_ = v_x_747_;
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
else
{
lean_dec(v_x_747_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_year_770_; lean_object* v___x_772_; 
v_year_770_ = lean_ctor_get(v_date_746_, 0);
lean_inc(v_year_770_);
lean_dec_ref(v_date_746_);
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 1);
lean_ctor_set(v___x_768_, 0, v_year_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_year_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
case 3:
{
lean_object* v_year_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_784_; 
lean_dec_ref(v_x_747_);
v_year_776_ = lean_ctor_get(v_date_746_, 0);
v___x_777_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_778_ = lean_int_mod(v_year_776_, v___x_777_);
v___x_779_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_784_ = lean_int_dec_eq(v___x_778_, v___x_779_);
lean_dec(v___x_778_);
if (v___x_784_ == 0)
{
v___y_749_ = v___x_784_;
goto v___jp_748_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_786_ = lean_int_mod(v_year_776_, v___x_785_);
v___x_787_ = lean_int_dec_eq(v___x_786_, v___x_779_);
lean_dec(v___x_786_);
if (v___x_787_ == 0)
{
if (v___x_784_ == 0)
{
goto v___jp_780_;
}
else
{
v___y_749_ = v___x_784_;
goto v___jp_748_;
}
}
else
{
goto v___jp_780_;
}
}
v___jp_780_:
{
lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_781_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_782_ = lean_int_mod(v_year_776_, v___x_781_);
v___x_783_ = lean_int_dec_eq(v___x_782_, v___x_779_);
lean_dec(v___x_782_);
v___y_749_ = v___x_783_;
goto v___jp_748_;
}
}
case 6:
{
lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_795_; 
v_isSharedCheck_795_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_796_);
v___x_789_ = v_x_747_;
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
else
{
lean_dec(v_x_747_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_795_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = l_Std_Time_PlainDate_quarter(v_date_746_);
lean_dec_ref(v_date_746_);
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 1);
lean_ctor_set(v___x_789_, 0, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
case 7:
{
lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_804_; 
v_isSharedCheck_804_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_805_);
v___x_798_ = v_x_747_;
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
else
{
lean_dec(v_x_747_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = l_Std_Time_PlainDate_weekOfYear(v_date_746_);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 1);
lean_ctor_set(v___x_798_, 0, v___x_800_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
case 8:
{
lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_isSharedCheck_813_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_814_);
v___x_807_ = v_x_747_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_dec(v_x_747_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_746_);
if (v_isShared_808_ == 0)
{
lean_ctor_set_tag(v___x_807_, 1);
lean_ctor_set(v___x_807_, 0, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
case 4:
{
lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_822_; 
v_isSharedCheck_822_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_823_);
v___x_816_ = v_x_747_;
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
else
{
lean_dec(v_x_747_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_822_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_month_818_; lean_object* v___x_820_; 
v_month_818_ = lean_ctor_get(v_date_746_, 1);
lean_inc(v_month_818_);
lean_dec_ref(v_date_746_);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 1);
lean_ctor_set(v___x_816_, 0, v_month_818_);
v___x_820_ = v___x_816_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_month_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
case 5:
{
lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_831_; 
v_isSharedCheck_831_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; 
v_unused_832_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_832_);
v___x_825_ = v_x_747_;
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
else
{
lean_dec(v_x_747_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_831_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_day_827_; lean_object* v___x_829_; 
v_day_827_ = lean_ctor_get(v_date_746_, 2);
lean_inc(v_day_827_);
lean_dec_ref(v_date_746_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 1);
lean_ctor_set(v___x_825_, 0, v_day_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_day_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
case 9:
{
uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
lean_dec_ref(v_x_747_);
v___x_833_ = l_Std_Time_PlainDate_weekday(v_date_746_);
v___x_834_ = lean_box(v___x_833_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
case 10:
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_844_; 
v_isSharedCheck_844_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_845_);
v___x_837_ = v_x_747_;
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_x_747_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_844_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_839_ = l_Std_Time_PlainDate_weekday(v_date_746_);
v___x_840_ = lean_box(v___x_839_);
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
case 11:
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_isSharedCheck_853_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v_x_747_, 0);
lean_dec(v_unused_854_);
v___x_847_ = v_x_747_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_dec(v_x_747_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = l_Std_Time_PlainDate_weekOfMonth(v_date_746_);
lean_dec_ref(v_date_746_);
if (v_isShared_848_ == 0)
{
lean_ctor_set_tag(v___x_847_, 1);
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
default: 
{
lean_object* v___x_855_; 
lean_dec(v_x_747_);
lean_dec_ref(v_date_746_);
v___x_855_ = lean_box(0);
return v___x_855_;
}
}
v___jp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = l_Std_Time_PlainDate_dayOfYear(v_date_746_);
lean_dec_ref(v_date_746_);
v___x_751_ = lean_box(v___y_749_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_format(lean_object* v_date_858_, lean_object* v_format_859_){
_start:
{
uint8_t v___x_860_; lean_object* v_format_861_; 
v___x_860_ = 0;
v_format_861_ = l_Std_Time_GenericFormat_spec___redArg(v_format_859_, v___x_860_);
if (lean_obj_tag(v_format_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
lean_dec_ref(v_date_858_);
v_a_862_ = lean_ctor_get(v_format_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v_format_861_);
v___x_863_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_864_ = lean_string_append(v___x_863_, v_a_862_);
lean_dec(v_a_862_);
return v___x_864_;
}
else
{
lean_object* v_a_865_; lean_object* v___f_866_; lean_object* v_res_867_; 
v_a_865_ = lean_ctor_get(v_format_861_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v_format_861_);
v___f_866_ = lean_alloc_closure((void*)(l_Std_Time_PlainDate_format___lam__0), 2, 1);
lean_closure_set(v___f_866_, 0, v_date_858_);
v_res_867_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_865_, v___f_866_);
if (lean_obj_tag(v_res_867_) == 0)
{
lean_object* v___x_868_; 
v___x_868_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_868_;
}
else
{
lean_object* v_val_869_; 
v_val_869_ = lean_ctor_get(v_res_867_, 0);
lean_inc(v_val_869_);
lean_dec_ref(v_res_867_);
return v_val_869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString___lam__0(lean_object* v_m_870_, lean_object* v_d_871_, lean_object* v_y_872_){
_start:
{
uint8_t v___y_874_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_887_; 
v___x_880_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_881_ = lean_int_mod(v_y_872_, v___x_880_);
v___x_882_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_887_ = lean_int_dec_eq(v___x_881_, v___x_882_);
lean_dec(v___x_881_);
if (v___x_887_ == 0)
{
v___y_874_ = v___x_887_;
goto v___jp_873_;
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_889_ = lean_int_mod(v_y_872_, v___x_888_);
v___x_890_ = lean_int_dec_eq(v___x_889_, v___x_882_);
lean_dec(v___x_889_);
if (v___x_890_ == 0)
{
if (v___x_887_ == 0)
{
goto v___jp_883_;
}
else
{
v___y_874_ = v___x_887_;
goto v___jp_873_;
}
}
else
{
goto v___jp_883_;
}
}
v___jp_873_:
{
lean_object* v___x_875_; uint8_t v___x_876_; 
v___x_875_ = l_Std_Time_Month_Ordinal_days(v___y_874_, v_m_870_);
v___x_876_ = lean_int_dec_le(v_d_871_, v___x_875_);
lean_dec(v___x_875_);
if (v___x_876_ == 0)
{
lean_object* v___x_877_; 
lean_dec(v_y_872_);
lean_dec(v_d_871_);
lean_dec(v_m_870_);
v___x_877_ = lean_box(0);
return v___x_877_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_878_, 0, v_y_872_);
lean_ctor_set(v___x_878_, 1, v_m_870_);
lean_ctor_set(v___x_878_, 2, v_d_871_);
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
return v___x_879_;
}
}
v___jp_883_:
{
lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v___x_884_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_885_ = lean_int_mod(v_y_872_, v___x_884_);
v___x_886_ = lean_int_dec_eq(v___x_885_, v___x_882_);
lean_dec(v___x_885_);
v___y_874_ = v___x_886_;
goto v___jp_873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromAmericanDateString(lean_object* v_input_892_){
_start:
{
lean_object* v___f_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___f_893_ = ((lean_object*)(l_Std_Time_PlainDate_fromAmericanDateString___closed__0));
v___x_894_ = ((lean_object*)(l_Std_Time_Formats_americanDate));
v___x_895_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_894_, v___f_893_, v_input_892_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toAmericanDateString(lean_object* v_input_896_){
_start:
{
lean_object* v_year_897_; lean_object* v_month_898_; lean_object* v_day_899_; lean_object* v___x_900_; lean_object* v___x_6__overap_901_; lean_object* v___x_902_; 
v_year_897_ = lean_ctor_get(v_input_896_, 0);
lean_inc(v_year_897_);
v_month_898_ = lean_ctor_get(v_input_896_, 1);
lean_inc(v_month_898_);
v_day_899_ = lean_ctor_get(v_input_896_, 2);
lean_inc(v_day_899_);
lean_dec_ref(v_input_896_);
v___x_900_ = ((lean_object*)(l_Std_Time_Formats_americanDate));
v___x_6__overap_901_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_900_);
v___x_902_ = lean_apply_3(v___x_6__overap_901_, v_month_898_, v_day_899_, v_year_897_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString___lam__0(lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
uint8_t v___y_907_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_920_; 
v___x_913_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_914_ = lean_int_mod(v___y_903_, v___x_913_);
v___x_915_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_920_ = lean_int_dec_eq(v___x_914_, v___x_915_);
lean_dec(v___x_914_);
if (v___x_920_ == 0)
{
v___y_907_ = v___x_920_;
goto v___jp_906_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_921_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_922_ = lean_int_mod(v___y_903_, v___x_921_);
v___x_923_ = lean_int_dec_eq(v___x_922_, v___x_915_);
lean_dec(v___x_922_);
if (v___x_923_ == 0)
{
if (v___x_920_ == 0)
{
goto v___jp_916_;
}
else
{
v___y_907_ = v___x_920_;
goto v___jp_906_;
}
}
else
{
goto v___jp_916_;
}
}
v___jp_906_:
{
lean_object* v___x_908_; uint8_t v___x_909_; 
v___x_908_ = l_Std_Time_Month_Ordinal_days(v___y_907_, v___y_904_);
v___x_909_ = lean_int_dec_le(v___y_905_, v___x_908_);
lean_dec(v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec(v___y_905_);
lean_dec(v___y_904_);
lean_dec(v___y_903_);
v___x_910_ = lean_box(0);
return v___x_910_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_911_, 0, v___y_903_);
lean_ctor_set(v___x_911_, 1, v___y_904_);
lean_ctor_set(v___x_911_, 2, v___y_905_);
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
v___jp_916_:
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_918_ = lean_int_mod(v___y_903_, v___x_917_);
v___x_919_ = lean_int_dec_eq(v___x_918_, v___x_915_);
lean_dec(v___x_918_);
v___y_907_ = v___x_919_;
goto v___jp_906_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromSQLDateString(lean_object* v_input_925_){
_start:
{
lean_object* v___f_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___f_926_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_927_ = ((lean_object*)(l_Std_Time_Formats_sqlDate));
v___x_928_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_927_, v___f_926_, v_input_925_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toSQLDateString(lean_object* v_input_929_){
_start:
{
lean_object* v_year_930_; lean_object* v_month_931_; lean_object* v_day_932_; lean_object* v___x_933_; lean_object* v___x_6__overap_934_; lean_object* v___x_935_; 
v_year_930_ = lean_ctor_get(v_input_929_, 0);
lean_inc(v_year_930_);
v_month_931_ = lean_ctor_get(v_input_929_, 1);
lean_inc(v_month_931_);
v_day_932_ = lean_ctor_get(v_input_929_, 2);
lean_inc(v_day_932_);
lean_dec_ref(v_input_929_);
v___x_933_ = ((lean_object*)(l_Std_Time_Formats_sqlDate));
v___x_6__overap_934_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_933_);
v___x_935_ = lean_apply_3(v___x_6__overap_934_, v_year_930_, v_month_931_, v_day_932_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_fromLeanDateString(lean_object* v_input_936_){
_start:
{
lean_object* v___f_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___f_937_ = ((lean_object*)(l_Std_Time_PlainDate_fromSQLDateString___closed__0));
v___x_938_ = ((lean_object*)(l_Std_Time_Formats_leanDate));
v___x_939_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_938_, v___f_937_, v_input_936_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_toLeanDateString(lean_object* v_input_940_){
_start:
{
lean_object* v_year_941_; lean_object* v_month_942_; lean_object* v_day_943_; lean_object* v___x_944_; lean_object* v___x_6__overap_945_; lean_object* v___x_946_; 
v_year_941_ = lean_ctor_get(v_input_940_, 0);
lean_inc(v_year_941_);
v_month_942_ = lean_ctor_get(v_input_940_, 1);
lean_inc(v_month_942_);
v_day_943_ = lean_ctor_get(v_input_940_, 2);
lean_inc(v_day_943_);
lean_dec_ref(v_input_940_);
v___x_944_ = ((lean_object*)(l_Std_Time_Formats_leanDate));
v___x_6__overap_945_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_944_);
v___x_946_ = lean_apply_3(v___x_6__overap_945_, v_year_941_, v_month_942_, v_day_943_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_parse(lean_object* v_input_947_){
_start:
{
lean_object* v___x_948_; 
lean_inc_ref(v_input_947_);
v___x_948_ = l_Std_Time_PlainDate_fromAmericanDateString(v_input_947_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v___x_949_; 
lean_dec_ref(v___x_948_);
v___x_949_ = l_Std_Time_PlainDate_fromSQLDateString(v_input_947_);
return v___x_949_;
}
else
{
lean_dec_ref(v_input_947_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0(lean_object* v_data_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v___x_960_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__1));
v___x_961_ = l_Std_Time_PlainDate_toLeanDateString(v_data_958_);
v___x_962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_960_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = l_Repr_addAppParen(v___x_965_, v___y_959_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDate_instRepr___lam__0___boxed(lean_object* v_data_967_, lean_object* v___y_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_Time_PlainDate_instRepr___lam__0(v_data_967_, v___y_968_);
lean_dec(v___y_968_);
return v_res_969_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_972_ = lean_unsigned_to_nat(12u);
v___x_973_ = lean_nat_to_int(v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format___lam__0(lean_object* v_time_974_, lean_object* v_x_975_){
_start:
{
switch(lean_obj_tag(v_x_975_))
{
case 16:
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_983_; 
v_isSharedCheck_983_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; 
v_unused_984_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_984_);
v___x_977_ = v_x_975_;
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
else
{
lean_dec(v_x_975_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_983_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_hour_979_; lean_object* v___x_981_; 
v_hour_979_ = lean_ctor_get(v_time_974_, 0);
lean_inc(v_hour_979_);
lean_dec_ref(v_time_974_);
if (v_isShared_978_ == 0)
{
lean_ctor_set_tag(v___x_977_, 1);
lean_ctor_set(v___x_977_, 0, v_hour_979_);
v___x_981_ = v___x_977_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_hour_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
case 15:
{
lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_993_; 
v_isSharedCheck_993_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_993_ == 0)
{
lean_object* v_unused_994_; 
v_unused_994_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_994_);
v___x_986_ = v_x_975_;
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
else
{
lean_dec(v_x_975_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_993_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v_hour_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v_hour_988_ = lean_ctor_get(v_time_974_, 0);
lean_inc(v_hour_988_);
lean_dec_ref(v_time_974_);
v___x_989_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_988_);
lean_dec(v_hour_988_);
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
case 17:
{
lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1002_; 
v_isSharedCheck_1002_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; 
v_unused_1003_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_1003_);
v___x_996_ = v_x_975_;
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
else
{
lean_dec(v_x_975_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1002_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_minute_998_; lean_object* v___x_1000_; 
v_minute_998_ = lean_ctor_get(v_time_974_, 1);
lean_inc(v_minute_998_);
lean_dec_ref(v_time_974_);
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 1);
lean_ctor_set(v___x_996_, 0, v_minute_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_minute_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
case 21:
{
lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
v_isSharedCheck_1011_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_1012_);
v___x_1005_ = v_x_975_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_dec(v_x_975_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_nanosecond_1007_; lean_object* v___x_1009_; 
v_nanosecond_1007_ = lean_ctor_get(v_time_974_, 3);
lean_inc(v_nanosecond_1007_);
lean_dec_ref(v_time_974_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set_tag(v___x_1005_, 1);
lean_ctor_set(v___x_1005_, 0, v_nanosecond_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_nanosecond_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
case 18:
{
lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_isSharedCheck_1020_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_1021_);
v___x_1014_ = v_x_975_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_dec(v_x_975_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v_second_1016_; lean_object* v___x_1018_; 
v_second_1016_ = lean_ctor_get(v_time_974_, 2);
lean_inc(v_second_1016_);
lean_dec_ref(v_time_974_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 1);
lean_ctor_set(v___x_1014_, 0, v_second_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_second_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
case 12:
{
lean_object* v_hour_1022_; uint8_t v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
lean_dec_ref(v_x_975_);
v_hour_1022_ = lean_ctor_get(v_time_974_, 0);
lean_inc(v_hour_1022_);
lean_dec_ref(v_time_974_);
v___x_1023_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1022_);
lean_dec(v_hour_1022_);
v___x_1024_ = lean_box(v___x_1023_);
v___x_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
return v___x_1025_;
}
case 13:
{
lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1034_; 
v_isSharedCheck_1034_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_1035_);
v___x_1027_ = v_x_975_;
v_isShared_1028_ = v_isSharedCheck_1034_;
goto v_resetjp_1026_;
}
else
{
lean_dec(v_x_975_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1034_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_hour_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v_hour_1029_ = lean_ctor_get(v_time_974_, 0);
lean_inc(v_hour_1029_);
lean_dec_ref(v_time_974_);
v___x_1030_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1029_);
lean_dec(v_hour_1029_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1030_);
v___x_1032_ = v___x_1027_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
case 14:
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1045_; 
v_isSharedCheck_1045_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1045_ == 0)
{
lean_object* v_unused_1046_; 
v_unused_1046_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_1046_);
v___x_1037_ = v_x_975_;
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v_x_975_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1045_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v_hour_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v_hour_1039_ = lean_ctor_get(v_time_974_, 0);
lean_inc(v_hour_1039_);
lean_dec_ref(v_time_974_);
v___x_1040_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1041_ = lean_int_emod(v_hour_1039_, v___x_1040_);
lean_dec(v_hour_1039_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 1);
lean_ctor_set(v___x_1037_, 0, v___x_1041_);
v___x_1043_ = v___x_1037_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
case 19:
{
lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1054_; 
v_isSharedCheck_1054_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_1055_);
v___x_1048_ = v_x_975_;
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
else
{
lean_dec(v_x_975_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1054_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_nanosecond_1050_; lean_object* v___x_1052_; 
v_nanosecond_1050_ = lean_ctor_get(v_time_974_, 3);
lean_inc(v_nanosecond_1050_);
lean_dec_ref(v_time_974_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 1);
lean_ctor_set(v___x_1048_, 0, v_nanosecond_1050_);
v___x_1052_ = v___x_1048_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_nanosecond_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
case 20:
{
lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1063_; 
v_isSharedCheck_1063_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; 
v_unused_1064_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_1064_);
v___x_1057_ = v_x_975_;
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
else
{
lean_dec(v_x_975_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = l_Std_Time_PlainTime_toMilliseconds(v_time_974_);
lean_dec_ref(v_time_974_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 1);
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
case 22:
{
lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1072_; 
v_isSharedCheck_1072_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v_x_975_, 0);
lean_dec(v_unused_1073_);
v___x_1066_ = v_x_975_;
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
else
{
lean_dec(v_x_975_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = l_Std_Time_PlainTime_toNanoseconds(v_time_974_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set_tag(v___x_1066_, 1);
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
default: 
{
lean_object* v___x_1074_; 
lean_dec(v_x_975_);
lean_dec_ref(v_time_974_);
v___x_1074_ = lean_box(0);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_format(lean_object* v_time_1075_, lean_object* v_format_1076_){
_start:
{
uint8_t v___x_1077_; lean_object* v_format_1078_; 
v___x_1077_ = 0;
v_format_1078_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1076_, v___x_1077_);
if (lean_obj_tag(v_format_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec_ref(v_time_1075_);
v_a_1079_ = lean_ctor_get(v_format_1078_, 0);
lean_inc(v_a_1079_);
lean_dec_ref(v_format_1078_);
v___x_1080_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1081_ = lean_string_append(v___x_1080_, v_a_1079_);
lean_dec(v_a_1079_);
return v___x_1081_;
}
else
{
lean_object* v_a_1082_; lean_object* v___f_1083_; lean_object* v_res_1084_; 
v_a_1082_ = lean_ctor_get(v_format_1078_, 0);
lean_inc(v_a_1082_);
lean_dec_ref(v_format_1078_);
v___f_1083_ = lean_alloc_closure((void*)(l_Std_Time_PlainTime_format___lam__0), 2, 1);
lean_closure_set(v___f_1083_, 0, v_time_1075_);
v_res_1084_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1082_, v___f_1083_);
if (lean_obj_tag(v_res_1084_) == 0)
{
lean_object* v___x_1085_; 
v___x_1085_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1085_;
}
else
{
lean_object* v_val_1086_; 
v_val_1086_ = lean_ctor_get(v_res_1084_, 0);
lean_inc(v_val_1086_);
lean_dec_ref(v_res_1084_);
return v_val_1086_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_unsigned_to_nat(1000000000u);
v___x_1088_ = lean_unsigned_to_nat(0u);
v___x_1089_ = lean_nat_mod(v___x_1088_, v___x_1087_);
return v___x_1089_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0);
v___x_1091_ = lean_nat_to_int(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour___lam__0(lean_object* v_h_1092_, lean_object* v_m_1093_, lean_object* v_s_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1);
v___x_1096_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1096_, 0, v_h_1092_);
lean_ctor_set(v___x_1096_, 1, v_m_1093_);
lean_ctor_set(v___x_1096_, 2, v_s_1094_);
lean_ctor_set(v___x_1096_, 3, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime24Hour(lean_object* v_input_1099_){
_start:
{
lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___f_1100_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1101_ = ((lean_object*)(l_Std_Time_Formats_time24Hour));
v___x_1102_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1101_, v___f_1100_, v_input_1099_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime24Hour(lean_object* v_input_1103_){
_start:
{
lean_object* v_hour_1104_; lean_object* v_minute_1105_; lean_object* v_second_1106_; lean_object* v___x_1107_; lean_object* v___x_6__overap_1108_; lean_object* v___x_1109_; 
v_hour_1104_ = lean_ctor_get(v_input_1103_, 0);
lean_inc(v_hour_1104_);
v_minute_1105_ = lean_ctor_get(v_input_1103_, 1);
lean_inc(v_minute_1105_);
v_second_1106_ = lean_ctor_get(v_input_1103_, 2);
lean_inc(v_second_1106_);
lean_dec_ref(v_input_1103_);
v___x_1107_ = ((lean_object*)(l_Std_Time_Formats_time24Hour));
v___x_6__overap_1108_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1107_);
v___x_1109_ = lean_apply_3(v___x_6__overap_1108_, v_hour_1104_, v_minute_1105_, v_second_1106_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0(lean_object* v_h_1110_, lean_object* v_m_1111_, lean_object* v_s_1112_, lean_object* v_n_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1114_, 0, v_h_1110_);
lean_ctor_set(v___x_1114_, 1, v_m_1111_);
lean_ctor_set(v___x_1114_, 2, v_s_1112_);
lean_ctor_set(v___x_1114_, 3, v_n_1113_);
v___x_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromLeanTime24Hour(lean_object* v_input_1117_){
_start:
{
lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___f_1118_ = ((lean_object*)(l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0));
v___x_1119_ = ((lean_object*)(l_Std_Time_Formats_leanTime24Hour));
lean_inc_ref(v_input_1117_);
v___x_1120_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1119_, v___f_1118_, v_input_1117_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v___f_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v___x_1120_);
v___f_1121_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime24Hour___closed__0));
v___x_1122_ = ((lean_object*)(l_Std_Time_Formats_leanTime24HourNoNanos));
v___x_1123_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1122_, v___f_1121_, v_input_1117_);
return v___x_1123_;
}
else
{
lean_dec_ref(v_input_1117_);
return v___x_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toLeanTime24Hour(lean_object* v_input_1124_){
_start:
{
lean_object* v_hour_1125_; lean_object* v_minute_1126_; lean_object* v_second_1127_; lean_object* v_nanosecond_1128_; lean_object* v___x_1129_; lean_object* v___x_7__overap_1130_; lean_object* v___x_1131_; 
v_hour_1125_ = lean_ctor_get(v_input_1124_, 0);
lean_inc(v_hour_1125_);
v_minute_1126_ = lean_ctor_get(v_input_1124_, 1);
lean_inc(v_minute_1126_);
v_second_1127_ = lean_ctor_get(v_input_1124_, 2);
lean_inc(v_second_1127_);
v_nanosecond_1128_ = lean_ctor_get(v_input_1124_, 3);
lean_inc(v_nanosecond_1128_);
lean_dec_ref(v_input_1124_);
v___x_1129_ = ((lean_object*)(l_Std_Time_Formats_leanTime24Hour));
v___x_7__overap_1130_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1129_);
v___x_1131_ = lean_apply_4(v___x_7__overap_1130_, v_hour_1125_, v_minute_1126_, v_second_1127_, v_nanosecond_1128_);
return v___x_1131_;
}
}
static lean_object* _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_to_int(v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0(lean_object* v_h_1134_, lean_object* v_m_1135_, lean_object* v_s_1136_, uint8_t v_a_1137_){
_start:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1139_ = lean_int_dec_le(v___x_1138_, v_h_1134_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_dec(v_s_1136_);
lean_dec(v_m_1135_);
v___x_1140_ = lean_box(0);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1142_ = lean_int_dec_le(v_h_1134_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec(v_s_1136_);
lean_dec(v_m_1135_);
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = l_Std_Time_HourMarker_toAbsolute(v_a_1137_, v_h_1134_);
v___x_1145_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1, &l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once, _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1);
v___x_1146_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v_m_1135_);
lean_ctor_set(v___x_1146_, 2, v_s_1136_);
lean_ctor_set(v___x_1146_, 3, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed(lean_object* v_h_1148_, lean_object* v_m_1149_, lean_object* v_s_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v_a_boxed_1152_; lean_object* v_res_1153_; 
v_a_boxed_1152_ = lean_unbox(v_a_1151_);
v_res_1153_ = l_Std_Time_PlainTime_fromTime12Hour___lam__0(v_h_1148_, v_m_1149_, v_s_1150_, v_a_boxed_1152_);
lean_dec(v_h_1148_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_fromTime12Hour(lean_object* v_input_1155_){
_start:
{
lean_object* v_builder_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_builder_1156_ = ((lean_object*)(l_Std_Time_PlainTime_fromTime12Hour___closed__0));
v___x_1157_ = ((lean_object*)(l_Std_Time_Formats_time12Hour));
v___x_1158_ = l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_1157_, v_builder_1156_, v_input_1155_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_toTime12Hour(lean_object* v_input_1159_){
_start:
{
lean_object* v_hour_1160_; lean_object* v_minute_1161_; lean_object* v_second_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v_hour_1160_ = lean_ctor_get(v_input_1159_, 0);
lean_inc(v_hour_1160_);
v_minute_1161_ = lean_ctor_get(v_input_1159_, 1);
lean_inc(v_minute_1161_);
v_second_1162_ = lean_ctor_get(v_input_1159_, 2);
lean_inc(v_second_1162_);
lean_dec_ref(v_input_1159_);
v___x_1163_ = ((lean_object*)(l_Std_Time_Formats_time12Hour));
v___x_1164_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1165_ = lean_obj_once(&l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0, &l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0);
v___x_1166_ = lean_int_emod(v_hour_1160_, v___x_1164_);
v___x_1167_ = lean_int_add(v___x_1166_, v___x_1165_);
lean_dec(v___x_1166_);
v___x_1168_ = lean_int_dec_le(v___x_1164_, v_hour_1160_);
lean_dec(v_hour_1160_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; lean_object* v___x_56__overap_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1169_ = 0;
v___x_56__overap_1170_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1163_);
v___x_1171_ = lean_box(v___x_1169_);
v___x_1172_ = lean_apply_4(v___x_56__overap_1170_, v___x_1167_, v_minute_1161_, v_second_1162_, v___x_1171_);
return v___x_1172_;
}
else
{
uint8_t v___x_1173_; lean_object* v___x_57__overap_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = 1;
v___x_57__overap_1174_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1163_);
v___x_1175_ = lean_box(v___x_1173_);
v___x_1176_ = lean_apply_4(v___x_57__overap_1174_, v___x_1167_, v_minute_1161_, v_second_1162_, v___x_1175_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_parse(lean_object* v_input_1177_){
_start:
{
lean_object* v___x_1178_; 
lean_inc_ref(v_input_1177_);
v___x_1178_ = l_Std_Time_PlainTime_fromTime12Hour(v_input_1177_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v___x_1179_; 
lean_dec_ref(v___x_1178_);
v___x_1179_ = l_Std_Time_PlainTime_fromTime24Hour(v_input_1177_);
return v___x_1179_;
}
else
{
lean_dec_ref(v_input_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0(lean_object* v_data_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1187_ = ((lean_object*)(l_Std_Time_PlainTime_instRepr___lam__0___closed__1));
v___x_1188_ = l_Std_Time_PlainTime_toLeanTime24Hour(v_data_1185_);
v___x_1189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
v___x_1190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1187_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Repr_addAppParen(v___x_1192_, v___y_1186_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainTime_instRepr___lam__0___boxed(lean_object* v_data_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Std_Time_PlainTime_instRepr___lam__0(v_data_1194_, v___y_1195_);
lean_dec(v___y_1195_);
return v_res_1196_;
}
}
static lean_object* _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_unsigned_to_nat(1000000000u);
v___x_1200_ = lean_nat_to_int(v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_format___lam__0(lean_object* v_timestamp_1201_, lean_object* v_timezone_1202_, lean_object* v_x_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_second_1206_; lean_object* v_nano_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v_second_1212_; lean_object* v_nano_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1204_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v_timestamp_1201_);
v___x_1205_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v___x_1204_);
v_second_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_second_1206_);
v_nano_1207_ = lean_ctor_get(v___x_1205_, 1);
lean_inc(v_nano_1207_);
lean_dec_ref(v___x_1205_);
v___x_1208_ = l_Std_Time_TimeZone_toSeconds(v_timezone_1202_);
v___x_1209_ = lean_obj_once(&l_Std_Time_ZonedDateTime_format___lam__0___closed__0, &l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0);
v___x_1210_ = lean_int_mul(v___x_1208_, v___x_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = l_Std_Time_Duration_ofNanoseconds(v___x_1210_);
lean_dec(v___x_1210_);
v_second_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_second_1212_);
v_nano_1213_ = lean_ctor_get(v___x_1211_, 1);
lean_inc(v_nano_1213_);
lean_dec_ref(v___x_1211_);
v___x_1214_ = lean_int_mul(v_second_1206_, v___x_1209_);
lean_dec(v_second_1206_);
v___x_1215_ = lean_int_add(v___x_1214_, v_nano_1207_);
lean_dec(v_nano_1207_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_int_mul(v_second_1212_, v___x_1209_);
lean_dec(v_second_1212_);
v___x_1217_ = lean_int_add(v___x_1216_, v_nano_1213_);
lean_dec(v_nano_1213_);
lean_dec(v___x_1216_);
v___x_1218_ = lean_int_add(v___x_1215_, v___x_1217_);
lean_dec(v___x_1217_);
lean_dec(v___x_1215_);
v___x_1219_ = l_Std_Time_Duration_ofNanoseconds(v___x_1218_);
lean_dec(v___x_1218_);
v___x_1220_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_format___lam__0___boxed(lean_object* v_timestamp_1221_, lean_object* v_timezone_1222_, lean_object* v_x_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Std_Time_ZonedDateTime_format___lam__0(v_timestamp_1221_, v_timezone_1222_, v_x_1223_);
lean_dec_ref(v_timezone_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_format(lean_object* v_data_1225_, lean_object* v_format_1226_){
_start:
{
uint8_t v___x_1227_; lean_object* v_format_1228_; 
v___x_1227_ = 0;
v_format_1228_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1226_, v___x_1227_);
if (lean_obj_tag(v_format_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
lean_dec_ref(v_data_1225_);
v_a_1229_ = lean_ctor_get(v_format_1228_, 0);
lean_inc(v_a_1229_);
lean_dec_ref(v_format_1228_);
v___x_1230_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1231_ = lean_string_append(v___x_1230_, v_a_1229_);
lean_dec(v_a_1229_);
return v___x_1231_;
}
else
{
lean_object* v_a_1232_; lean_object* v_timestamp_1233_; lean_object* v_timezone_1234_; lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_a_1232_ = lean_ctor_get(v_format_1228_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v_format_1228_);
v_timestamp_1233_ = lean_ctor_get(v_data_1225_, 1);
lean_inc_ref(v_timestamp_1233_);
v_timezone_1234_ = lean_ctor_get(v_data_1225_, 3);
lean_inc_ref(v_timezone_1234_);
lean_dec_ref(v_data_1225_);
v___x_1235_ = lean_box(1);
lean_inc_ref(v_timezone_1234_);
lean_inc_ref(v_timestamp_1233_);
v___f_1236_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1236_, 0, v_timestamp_1233_);
lean_closure_set(v___f_1236_, 1, v_timezone_1234_);
v___x_1237_ = lean_mk_thunk(v___f_1236_);
v___x_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1238_, 0, v_timestamp_1233_);
lean_ctor_set(v___x_1238_, 1, v___x_1237_);
v___x_1239_ = l_Std_Time_GenericFormat_format(v___x_1235_, v_timezone_1234_, v_a_1232_, v___x_1238_);
lean_dec_ref(v_timezone_1234_);
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromISO8601String(lean_object* v_input_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_box(1);
v___x_1242_ = ((lean_object*)(l_Std_Time_Formats_iso8601));
v___x_1243_ = l_Std_Time_GenericFormat_parse(v___x_1241_, v___x_1242_, v_input_1240_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toISO8601String(lean_object* v_date_1244_){
_start:
{
lean_object* v_timestamp_1245_; lean_object* v_timezone_1246_; lean_object* v___x_1247_; lean_object* v___f_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_timestamp_1245_ = lean_ctor_get(v_date_1244_, 1);
lean_inc_ref(v_timestamp_1245_);
v_timezone_1246_ = lean_ctor_get(v_date_1244_, 3);
lean_inc_ref(v_timezone_1246_);
lean_dec_ref(v_date_1244_);
v___x_1247_ = lean_box(1);
lean_inc_ref(v_timezone_1246_);
lean_inc_ref(v_timestamp_1245_);
v___f_1248_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1248_, 0, v_timestamp_1245_);
lean_closure_set(v___f_1248_, 1, v_timezone_1246_);
v___x_1249_ = ((lean_object*)(l_Std_Time_Formats_iso8601));
v___x_1250_ = lean_mk_thunk(v___f_1248_);
v___x_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1251_, 0, v_timestamp_1245_);
lean_ctor_set(v___x_1251_, 1, v___x_1250_);
v___x_1252_ = l_Std_Time_GenericFormat_format(v___x_1247_, v_timezone_1246_, v___x_1249_, v___x_1251_);
lean_dec_ref(v_timezone_1246_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromRFC822String(lean_object* v_input_1253_){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_box(1);
v___x_1255_ = ((lean_object*)(l_Std_Time_Formats_rfc822));
v___x_1256_ = l_Std_Time_GenericFormat_parse(v___x_1254_, v___x_1255_, v_input_1253_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toRFC822String(lean_object* v_date_1257_){
_start:
{
lean_object* v_timestamp_1258_; lean_object* v_timezone_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v_timestamp_1258_ = lean_ctor_get(v_date_1257_, 1);
lean_inc_ref(v_timestamp_1258_);
v_timezone_1259_ = lean_ctor_get(v_date_1257_, 3);
lean_inc_ref(v_timezone_1259_);
lean_dec_ref(v_date_1257_);
v___x_1260_ = lean_box(1);
lean_inc_ref(v_timezone_1259_);
lean_inc_ref(v_timestamp_1258_);
v___f_1261_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1261_, 0, v_timestamp_1258_);
lean_closure_set(v___f_1261_, 1, v_timezone_1259_);
v___x_1262_ = ((lean_object*)(l_Std_Time_Formats_rfc822));
v___x_1263_ = lean_mk_thunk(v___f_1261_);
v___x_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1264_, 0, v_timestamp_1258_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
v___x_1265_ = l_Std_Time_GenericFormat_format(v___x_1260_, v_timezone_1259_, v___x_1262_, v___x_1264_);
lean_dec_ref(v_timezone_1259_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromRFC850String(lean_object* v_input_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_box(1);
v___x_1268_ = ((lean_object*)(l_Std_Time_Formats_rfc850));
v___x_1269_ = l_Std_Time_GenericFormat_parse(v___x_1267_, v___x_1268_, v_input_1266_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toRFC850String(lean_object* v_date_1270_){
_start:
{
lean_object* v_timestamp_1271_; lean_object* v_timezone_1272_; lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v_timestamp_1271_ = lean_ctor_get(v_date_1270_, 1);
lean_inc_ref(v_timestamp_1271_);
v_timezone_1272_ = lean_ctor_get(v_date_1270_, 3);
lean_inc_ref(v_timezone_1272_);
lean_dec_ref(v_date_1270_);
v___x_1273_ = lean_box(1);
lean_inc_ref(v_timezone_1272_);
lean_inc_ref(v_timestamp_1271_);
v___f_1274_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1274_, 0, v_timestamp_1271_);
lean_closure_set(v___f_1274_, 1, v_timezone_1272_);
v___x_1275_ = ((lean_object*)(l_Std_Time_Formats_rfc850));
v___x_1276_ = lean_mk_thunk(v___f_1274_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v_timestamp_1271_);
lean_ctor_set(v___x_1277_, 1, v___x_1276_);
v___x_1278_ = l_Std_Time_GenericFormat_format(v___x_1273_, v_timezone_1272_, v___x_1275_, v___x_1277_);
lean_dec_ref(v_timezone_1272_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromDateTimeWithZoneString(lean_object* v_input_1279_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = lean_box(1);
v___x_1281_ = ((lean_object*)(l_Std_Time_Formats_dateTimeWithZone));
v___x_1282_ = l_Std_Time_GenericFormat_parse(v___x_1280_, v___x_1281_, v_input_1279_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTimeWithZoneString(lean_object* v_pdt_1283_){
_start:
{
lean_object* v_timestamp_1284_; lean_object* v_timezone_1285_; lean_object* v___x_1286_; lean_object* v___f_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_timestamp_1284_ = lean_ctor_get(v_pdt_1283_, 1);
lean_inc_ref(v_timestamp_1284_);
v_timezone_1285_ = lean_ctor_get(v_pdt_1283_, 3);
lean_inc_ref(v_timezone_1285_);
lean_dec_ref(v_pdt_1283_);
v___x_1286_ = lean_box(1);
lean_inc_ref(v_timezone_1285_);
lean_inc_ref(v_timestamp_1284_);
v___f_1287_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1287_, 0, v_timestamp_1284_);
lean_closure_set(v___f_1287_, 1, v_timezone_1285_);
v___x_1288_ = ((lean_object*)(l_Std_Time_Formats_dateTimeWithZone));
v___x_1289_ = lean_mk_thunk(v___f_1287_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v_timestamp_1284_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Std_Time_GenericFormat_format(v___x_1286_, v_timezone_1285_, v___x_1288_, v___x_1290_);
lean_dec_ref(v_timezone_1285_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromLeanDateTimeWithZoneString(lean_object* v_input_1292_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1293_ = lean_box(1);
v___x_1294_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithZone));
lean_inc_ref(v_input_1292_);
v___x_1295_ = l_Std_Time_GenericFormat_parse(v___x_1293_, v___x_1294_, v_input_1292_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v___x_1295_);
v___x_1296_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos));
v___x_1297_ = l_Std_Time_GenericFormat_parse(v___x_1293_, v___x_1296_, v_input_1292_);
return v___x_1297_;
}
else
{
lean_dec_ref(v_input_1292_);
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(lean_object* v_input_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_box(1);
v___x_1300_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithIdentifier));
lean_inc_ref(v_input_1298_);
v___x_1301_ = l_Std_Time_GenericFormat_parse(v___x_1299_, v___x_1300_, v_input_1298_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec_ref(v___x_1301_);
v___x_1302_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos));
v___x_1303_ = l_Std_Time_GenericFormat_parse(v___x_1299_, v___x_1302_, v_input_1298_);
return v___x_1303_;
}
else
{
lean_dec_ref(v_input_1298_);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toLeanDateTimeWithZoneString(lean_object* v_zdt_1304_){
_start:
{
lean_object* v_date_1305_; lean_object* v_timezone_1306_; lean_object* v___x_1307_; lean_object* v_date_1308_; lean_object* v_time_1309_; lean_object* v_year_1310_; lean_object* v_month_1311_; lean_object* v_day_1312_; lean_object* v_hour_1313_; lean_object* v_minute_1314_; lean_object* v_second_1315_; lean_object* v_nanosecond_1316_; lean_object* v_offset_1317_; lean_object* v___x_1318_; lean_object* v___x_14__overap_1319_; lean_object* v___x_1320_; 
v_date_1305_ = lean_ctor_get(v_zdt_1304_, 0);
lean_inc_ref(v_date_1305_);
v_timezone_1306_ = lean_ctor_get(v_zdt_1304_, 3);
lean_inc_ref(v_timezone_1306_);
lean_dec_ref(v_zdt_1304_);
v___x_1307_ = lean_thunk_get_own(v_date_1305_);
lean_dec_ref(v_date_1305_);
v_date_1308_ = lean_ctor_get(v___x_1307_, 0);
lean_inc_ref(v_date_1308_);
v_time_1309_ = lean_ctor_get(v___x_1307_, 1);
lean_inc_ref(v_time_1309_);
lean_dec(v___x_1307_);
v_year_1310_ = lean_ctor_get(v_date_1308_, 0);
lean_inc(v_year_1310_);
v_month_1311_ = lean_ctor_get(v_date_1308_, 1);
lean_inc(v_month_1311_);
v_day_1312_ = lean_ctor_get(v_date_1308_, 2);
lean_inc(v_day_1312_);
lean_dec_ref(v_date_1308_);
v_hour_1313_ = lean_ctor_get(v_time_1309_, 0);
lean_inc(v_hour_1313_);
v_minute_1314_ = lean_ctor_get(v_time_1309_, 1);
lean_inc(v_minute_1314_);
v_second_1315_ = lean_ctor_get(v_time_1309_, 2);
lean_inc(v_second_1315_);
v_nanosecond_1316_ = lean_ctor_get(v_time_1309_, 3);
lean_inc(v_nanosecond_1316_);
lean_dec_ref(v_time_1309_);
v_offset_1317_ = lean_ctor_get(v_timezone_1306_, 0);
lean_inc(v_offset_1317_);
lean_dec_ref(v_timezone_1306_);
v___x_1318_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithZone));
v___x_14__overap_1319_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1318_);
v___x_1320_ = lean_apply_8(v___x_14__overap_1319_, v_year_1310_, v_month_1311_, v_day_1312_, v_hour_1313_, v_minute_1314_, v_second_1315_, v_nanosecond_1316_, v_offset_1317_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toLeanDateTimeWithIdentifierString(lean_object* v_zdt_1321_){
_start:
{
lean_object* v_date_1322_; lean_object* v_timezone_1323_; lean_object* v___x_1324_; lean_object* v_date_1325_; lean_object* v_time_1326_; lean_object* v_year_1327_; lean_object* v_month_1328_; lean_object* v_day_1329_; lean_object* v_hour_1330_; lean_object* v_minute_1331_; lean_object* v_second_1332_; lean_object* v_nanosecond_1333_; lean_object* v_name_1334_; lean_object* v___x_1335_; lean_object* v___x_15__overap_1336_; lean_object* v___x_1337_; 
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
v_name_1334_ = lean_ctor_get(v_timezone_1323_, 1);
lean_inc_ref(v_name_1334_);
lean_dec_ref(v_timezone_1323_);
v___x_1335_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos));
v___x_15__overap_1336_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1335_);
v___x_1337_ = lean_apply_8(v___x_15__overap_1336_, v_year_1327_, v_month_1328_, v_day_1329_, v_hour_1330_, v_minute_1331_, v_second_1332_, v_nanosecond_1333_, v_name_1334_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_parse(lean_object* v_input_1338_){
_start:
{
lean_object* v___x_1339_; 
lean_inc_ref(v_input_1338_);
v___x_1339_ = l_Std_Time_ZonedDateTime_fromISO8601String(v_input_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; 
lean_dec_ref(v___x_1339_);
lean_inc_ref(v_input_1338_);
v___x_1340_ = l_Std_Time_ZonedDateTime_fromRFC822String(v_input_1338_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1341_; 
lean_dec_ref(v___x_1340_);
lean_inc_ref(v_input_1338_);
v___x_1341_ = l_Std_Time_ZonedDateTime_fromRFC850String(v_input_1338_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v___x_1342_; 
lean_dec_ref(v___x_1341_);
lean_inc_ref(v_input_1338_);
v___x_1342_ = l_Std_Time_ZonedDateTime_fromDateTimeWithZoneString(v_input_1338_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v___x_1343_; 
lean_dec_ref(v___x_1342_);
v___x_1343_ = l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(v_input_1338_);
return v___x_1343_;
}
else
{
lean_dec_ref(v_input_1338_);
return v___x_1342_;
}
}
else
{
lean_dec_ref(v_input_1338_);
return v___x_1341_;
}
}
else
{
lean_dec_ref(v_input_1338_);
return v___x_1340_;
}
}
else
{
lean_dec_ref(v_input_1338_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instRepr___lam__0(lean_object* v_data_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1351_ = ((lean_object*)(l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1));
v___x_1352_ = l_Std_Time_ZonedDateTime_toLeanDateTimeWithZoneString(v_data_1349_);
v___x_1353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
v___x_1354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1351_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Repr_addAppParen(v___x_1356_, v___y_1350_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instRepr___lam__0___boxed(lean_object* v_data_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Std_Time_ZonedDateTime_instRepr___lam__0(v_data_1358_, v___y_1359_);
lean_dec(v___y_1359_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0(lean_object* v_date_1363_, lean_object* v_x_1364_){
_start:
{
switch(lean_obj_tag(v_x_1364_))
{
case 0:
{
lean_object* v_date_1365_; lean_object* v_year_1366_; uint8_t v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec_ref(v_x_1364_);
v_date_1365_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1365_);
lean_dec_ref(v_date_1363_);
v_year_1366_ = lean_ctor_get(v_date_1365_, 0);
lean_inc(v_year_1366_);
lean_dec_ref(v_date_1365_);
v___x_1367_ = l_Std_Time_Year_Offset_era(v_year_1366_);
lean_dec(v_year_1366_);
v___x_1368_ = lean_box(v___x_1367_);
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
case 1:
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1379_);
v___x_1371_ = v_x_1364_;
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_x_1364_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1378_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_date_1373_; lean_object* v_year_1374_; lean_object* v___x_1376_; 
v_date_1373_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1373_);
lean_dec_ref(v_date_1363_);
v_year_1374_ = lean_ctor_get(v_date_1373_, 0);
lean_inc(v_year_1374_);
lean_dec_ref(v_date_1373_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_year_1374_);
v___x_1376_ = v___x_1371_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_year_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
case 2:
{
lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1388_; 
v_isSharedCheck_1388_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1389_);
v___x_1381_ = v_x_1364_;
v_isShared_1382_ = v_isSharedCheck_1388_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v_x_1364_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1388_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_date_1383_; lean_object* v_year_1384_; lean_object* v___x_1386_; 
v_date_1383_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1383_);
lean_dec_ref(v_date_1363_);
v_year_1384_ = lean_ctor_get(v_date_1383_, 0);
lean_inc(v_year_1384_);
lean_dec_ref(v_date_1383_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set_tag(v___x_1381_, 1);
lean_ctor_set(v___x_1381_, 0, v_year_1384_);
v___x_1386_ = v___x_1381_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_year_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
case 3:
{
lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1441_; 
v_isSharedCheck_1441_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1442_);
v___x_1391_ = v_x_1364_;
v_isShared_1392_ = v_isSharedCheck_1441_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v_x_1364_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1441_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_date_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1439_; 
v_date_1393_ = lean_ctor_get(v_date_1363_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_date_1363_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_date_1363_, 1);
lean_dec(v_unused_1440_);
v___x_1395_ = v_date_1363_;
v_isShared_1396_ = v_isSharedCheck_1439_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_date_1393_);
lean_dec(v_date_1363_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1439_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_year_1397_; lean_object* v_month_1398_; lean_object* v_day_1399_; uint8_t v___y_1401_; uint8_t v___y_1402_; lean_object* v___y_1413_; lean_object* v___y_1414_; uint8_t v___y_1415_; uint8_t v___y_1420_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1435_; 
v_year_1397_ = lean_ctor_get(v_date_1393_, 0);
lean_inc(v_year_1397_);
v_month_1398_ = lean_ctor_get(v_date_1393_, 1);
lean_inc(v_month_1398_);
v_day_1399_ = lean_ctor_get(v_date_1393_, 2);
lean_inc(v_day_1399_);
lean_dec_ref(v_date_1393_);
v___x_1428_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1429_ = lean_int_mod(v_year_1397_, v___x_1428_);
v___x_1430_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1435_ = lean_int_dec_eq(v___x_1429_, v___x_1430_);
lean_dec(v___x_1429_);
if (v___x_1435_ == 0)
{
v___y_1420_ = v___x_1435_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1436_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1437_ = lean_int_mod(v_year_1397_, v___x_1436_);
v___x_1438_ = lean_int_dec_eq(v___x_1437_, v___x_1430_);
lean_dec(v___x_1437_);
if (v___x_1438_ == 0)
{
if (v___x_1435_ == 0)
{
goto v___jp_1431_;
}
else
{
v___y_1420_ = v___x_1435_;
goto v___jp_1419_;
}
}
else
{
goto v___jp_1431_;
}
}
v___jp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 1, v_day_1399_);
lean_ctor_set(v___x_1395_, 0, v_month_1398_);
v___x_1404_ = v___x_1395_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_month_1398_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_day_1399_);
v___x_1404_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
v___x_1405_ = l_Std_Time_ValidDate_dayOfYear(v___y_1402_, v___x_1404_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = lean_box(v___y_1401_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v___x_1405_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 1);
lean_ctor_set(v___x_1391_, 0, v___x_1407_);
v___x_1409_ = v___x_1391_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
v___jp_1412_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1416_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1417_ = lean_int_mod(v___y_1414_, v___x_1416_);
lean_dec(v___y_1414_);
v___x_1418_ = lean_int_dec_eq(v___x_1417_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec(v___x_1417_);
v___y_1401_ = v___y_1415_;
v___y_1402_ = v___x_1418_;
goto v___jp_1400_;
}
v___jp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1421_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1422_ = lean_int_mod(v_year_1397_, v___x_1421_);
v___x_1423_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1424_ = lean_int_dec_eq(v___x_1422_, v___x_1423_);
lean_dec(v___x_1422_);
if (v___x_1424_ == 0)
{
lean_dec(v_year_1397_);
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___x_1424_;
goto v___jp_1400_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1425_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1426_ = lean_int_mod(v_year_1397_, v___x_1425_);
v___x_1427_ = lean_int_dec_eq(v___x_1426_, v___x_1423_);
lean_dec(v___x_1426_);
if (v___x_1427_ == 0)
{
if (v___x_1424_ == 0)
{
v___y_1413_ = v___x_1423_;
v___y_1414_ = v_year_1397_;
v___y_1415_ = v___y_1420_;
goto v___jp_1412_;
}
else
{
lean_dec(v_year_1397_);
v___y_1401_ = v___y_1420_;
v___y_1402_ = v___x_1424_;
goto v___jp_1400_;
}
}
else
{
v___y_1413_ = v___x_1423_;
v___y_1414_ = v_year_1397_;
v___y_1415_ = v___y_1420_;
goto v___jp_1412_;
}
}
}
v___jp_1431_:
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1433_ = lean_int_mod(v_year_1397_, v___x_1432_);
v___x_1434_ = lean_int_dec_eq(v___x_1433_, v___x_1430_);
lean_dec(v___x_1433_);
v___y_1420_ = v___x_1434_;
goto v___jp_1419_;
}
}
}
}
case 6:
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1451_; 
v_isSharedCheck_1451_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; 
v_unused_1452_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1452_);
v___x_1444_ = v_x_1364_;
v_isShared_1445_ = v_isSharedCheck_1451_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v_x_1364_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1451_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v_date_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v_date_1446_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1446_);
lean_dec_ref(v_date_1363_);
v___x_1447_ = l_Std_Time_PlainDate_quarter(v_date_1446_);
lean_dec_ref(v_date_1446_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set_tag(v___x_1444_, 1);
lean_ctor_set(v___x_1444_, 0, v___x_1447_);
v___x_1449_ = v___x_1444_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
case 7:
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1461_; 
v_isSharedCheck_1461_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1462_);
v___x_1454_ = v_x_1364_;
v_isShared_1455_ = v_isSharedCheck_1461_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v_x_1364_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1461_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v_date_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v_date_1456_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1456_);
lean_dec_ref(v_date_1363_);
v___x_1457_ = l_Std_Time_PlainDate_weekOfYear(v_date_1456_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 1);
lean_ctor_set(v___x_1454_, 0, v___x_1457_);
v___x_1459_ = v___x_1454_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
case 8:
{
lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1471_; 
v_isSharedCheck_1471_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1472_);
v___x_1464_ = v_x_1364_;
v_isShared_1465_ = v_isSharedCheck_1471_;
goto v_resetjp_1463_;
}
else
{
lean_dec(v_x_1364_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1471_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v_date_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; 
v_date_1466_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1466_);
lean_dec_ref(v_date_1363_);
v___x_1467_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1466_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set_tag(v___x_1464_, 1);
lean_ctor_set(v___x_1464_, 0, v___x_1467_);
v___x_1469_ = v___x_1464_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1467_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
case 4:
{
lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1481_; 
v_isSharedCheck_1481_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1481_ == 0)
{
lean_object* v_unused_1482_; 
v_unused_1482_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1482_);
v___x_1474_ = v_x_1364_;
v_isShared_1475_ = v_isSharedCheck_1481_;
goto v_resetjp_1473_;
}
else
{
lean_dec(v_x_1364_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1481_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v_date_1476_; lean_object* v_month_1477_; lean_object* v___x_1479_; 
v_date_1476_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1476_);
lean_dec_ref(v_date_1363_);
v_month_1477_ = lean_ctor_get(v_date_1476_, 1);
lean_inc(v_month_1477_);
lean_dec_ref(v_date_1476_);
if (v_isShared_1475_ == 0)
{
lean_ctor_set_tag(v___x_1474_, 1);
lean_ctor_set(v___x_1474_, 0, v_month_1477_);
v___x_1479_ = v___x_1474_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_month_1477_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
case 5:
{
lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1491_; 
v_isSharedCheck_1491_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1491_ == 0)
{
lean_object* v_unused_1492_; 
v_unused_1492_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1492_);
v___x_1484_ = v_x_1364_;
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
else
{
lean_dec(v_x_1364_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1491_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_date_1486_; lean_object* v_day_1487_; lean_object* v___x_1489_; 
v_date_1486_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1486_);
lean_dec_ref(v_date_1363_);
v_day_1487_ = lean_ctor_get(v_date_1486_, 2);
lean_inc(v_day_1487_);
lean_dec_ref(v_date_1486_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set_tag(v___x_1484_, 1);
lean_ctor_set(v___x_1484_, 0, v_day_1487_);
v___x_1489_ = v___x_1484_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_day_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
case 9:
{
lean_object* v_date_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v_x_1364_);
v_date_1493_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1493_);
lean_dec_ref(v_date_1363_);
v___x_1494_ = l_Std_Time_PlainDate_weekday(v_date_1493_);
v___x_1495_ = lean_box(v___x_1494_);
v___x_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
case 10:
{
lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1506_; 
v_isSharedCheck_1506_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1507_);
v___x_1498_ = v_x_1364_;
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v_x_1364_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1506_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_date_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1504_; 
v_date_1500_ = lean_ctor_get(v_date_1363_, 0);
lean_inc_ref(v_date_1500_);
lean_dec_ref(v_date_1363_);
v___x_1501_ = l_Std_Time_PlainDate_weekday(v_date_1500_);
v___x_1502_ = lean_box(v___x_1501_);
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
case 11:
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1515_; 
v_isSharedCheck_1515_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1516_);
v___x_1509_ = v_x_1364_;
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_x_1364_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1515_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1363_);
lean_dec_ref(v_date_1363_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set_tag(v___x_1509_, 1);
lean_ctor_set(v___x_1509_, 0, v___x_1511_);
v___x_1513_ = v___x_1509_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
case 16:
{
lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1525_; 
v_isSharedCheck_1525_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1526_);
v___x_1518_ = v_x_1364_;
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
else
{
lean_dec(v_x_1364_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1525_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v_time_1520_; lean_object* v_hour_1521_; lean_object* v___x_1523_; 
v_time_1520_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1520_);
lean_dec_ref(v_date_1363_);
v_hour_1521_ = lean_ctor_get(v_time_1520_, 0);
lean_inc(v_hour_1521_);
lean_dec_ref(v_time_1520_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set_tag(v___x_1518_, 1);
lean_ctor_set(v___x_1518_, 0, v_hour_1521_);
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_hour_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
case 15:
{
lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1536_; 
v_isSharedCheck_1536_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; 
v_unused_1537_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1537_);
v___x_1528_ = v_x_1364_;
v_isShared_1529_ = v_isSharedCheck_1536_;
goto v_resetjp_1527_;
}
else
{
lean_dec(v_x_1364_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1536_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v_time_1530_; lean_object* v_hour_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v_time_1530_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1530_);
lean_dec_ref(v_date_1363_);
v_hour_1531_ = lean_ctor_get(v_time_1530_, 0);
lean_inc(v_hour_1531_);
lean_dec_ref(v_time_1530_);
v___x_1532_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1531_);
lean_dec(v_hour_1531_);
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 1);
lean_ctor_set(v___x_1528_, 0, v___x_1532_);
v___x_1534_ = v___x_1528_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
case 17:
{
lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1546_; 
v_isSharedCheck_1546_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1547_);
v___x_1539_ = v_x_1364_;
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
else
{
lean_dec(v_x_1364_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1546_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_time_1541_; lean_object* v_minute_1542_; lean_object* v___x_1544_; 
v_time_1541_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1541_);
lean_dec_ref(v_date_1363_);
v_minute_1542_ = lean_ctor_get(v_time_1541_, 1);
lean_inc(v_minute_1542_);
lean_dec_ref(v_time_1541_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v_minute_1542_);
v___x_1544_ = v___x_1539_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_minute_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
case 21:
{
lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1556_; 
v_isSharedCheck_1556_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; 
v_unused_1557_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1557_);
v___x_1549_ = v_x_1364_;
v_isShared_1550_ = v_isSharedCheck_1556_;
goto v_resetjp_1548_;
}
else
{
lean_dec(v_x_1364_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1556_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v_time_1551_; lean_object* v_nanosecond_1552_; lean_object* v___x_1554_; 
v_time_1551_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1551_);
lean_dec_ref(v_date_1363_);
v_nanosecond_1552_ = lean_ctor_get(v_time_1551_, 3);
lean_inc(v_nanosecond_1552_);
lean_dec_ref(v_time_1551_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set_tag(v___x_1549_, 1);
lean_ctor_set(v___x_1549_, 0, v_nanosecond_1552_);
v___x_1554_ = v___x_1549_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_nanosecond_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
case 18:
{
lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1566_; 
v_isSharedCheck_1566_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1567_);
v___x_1559_ = v_x_1364_;
v_isShared_1560_ = v_isSharedCheck_1566_;
goto v_resetjp_1558_;
}
else
{
lean_dec(v_x_1364_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1566_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_time_1561_; lean_object* v_second_1562_; lean_object* v___x_1564_; 
v_time_1561_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1561_);
lean_dec_ref(v_date_1363_);
v_second_1562_ = lean_ctor_get(v_time_1561_, 2);
lean_inc(v_second_1562_);
lean_dec_ref(v_time_1561_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set_tag(v___x_1559_, 1);
lean_ctor_set(v___x_1559_, 0, v_second_1562_);
v___x_1564_ = v___x_1559_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_second_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
case 12:
{
lean_object* v_time_1568_; lean_object* v_hour_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec_ref(v_x_1364_);
v_time_1568_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1568_);
lean_dec_ref(v_date_1363_);
v_hour_1569_ = lean_ctor_get(v_time_1568_, 0);
lean_inc(v_hour_1569_);
lean_dec_ref(v_time_1568_);
v___x_1570_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1569_);
lean_dec(v_hour_1569_);
v___x_1571_ = lean_box(v___x_1570_);
v___x_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
case 13:
{
lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1582_; 
v_isSharedCheck_1582_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1583_);
v___x_1574_ = v_x_1364_;
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v_x_1364_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1582_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v_time_1576_; lean_object* v_hour_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v_time_1576_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1576_);
lean_dec_ref(v_date_1363_);
v_hour_1577_ = lean_ctor_get(v_time_1576_, 0);
lean_inc(v_hour_1577_);
lean_dec_ref(v_time_1576_);
v___x_1578_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1577_);
lean_dec(v_hour_1577_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 1);
lean_ctor_set(v___x_1574_, 0, v___x_1578_);
v___x_1580_ = v___x_1574_;
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
case 14:
{
lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1594_; 
v_isSharedCheck_1594_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1595_);
v___x_1585_ = v_x_1364_;
v_isShared_1586_ = v_isSharedCheck_1594_;
goto v_resetjp_1584_;
}
else
{
lean_dec(v_x_1364_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1594_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_time_1587_; lean_object* v_hour_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v_time_1587_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1587_);
lean_dec_ref(v_date_1363_);
v_hour_1588_ = lean_ctor_get(v_time_1587_, 0);
lean_inc(v_hour_1588_);
lean_dec_ref(v_time_1587_);
v___x_1589_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1590_ = lean_int_emod(v_hour_1588_, v___x_1589_);
lean_dec(v_hour_1588_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 1);
lean_ctor_set(v___x_1585_, 0, v___x_1590_);
v___x_1592_ = v___x_1585_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
case 19:
{
lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1604_; 
v_isSharedCheck_1604_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1605_);
v___x_1597_ = v_x_1364_;
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v_x_1364_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_time_1599_; lean_object* v_nanosecond_1600_; lean_object* v___x_1602_; 
v_time_1599_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1599_);
lean_dec_ref(v_date_1363_);
v_nanosecond_1600_ = lean_ctor_get(v_time_1599_, 3);
lean_inc(v_nanosecond_1600_);
lean_dec_ref(v_time_1599_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set_tag(v___x_1597_, 1);
lean_ctor_set(v___x_1597_, 0, v_nanosecond_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_nanosecond_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
case 20:
{
lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1614_; 
v_isSharedCheck_1614_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1615_);
v___x_1607_ = v_x_1364_;
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
else
{
lean_dec(v_x_1364_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_time_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v_time_1609_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1609_);
lean_dec_ref(v_date_1363_);
v___x_1610_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1609_);
lean_dec_ref(v_time_1609_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 1);
lean_ctor_set(v___x_1607_, 0, v___x_1610_);
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
case 22:
{
lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1624_; 
v_isSharedCheck_1624_ = !lean_is_exclusive(v_x_1364_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v_x_1364_, 0);
lean_dec(v_unused_1625_);
v___x_1617_ = v_x_1364_;
v_isShared_1618_ = v_isSharedCheck_1624_;
goto v_resetjp_1616_;
}
else
{
lean_dec(v_x_1364_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1624_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v_time_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v_time_1619_ = lean_ctor_get(v_date_1363_, 1);
lean_inc_ref(v_time_1619_);
lean_dec_ref(v_date_1363_);
v___x_1620_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1619_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set_tag(v___x_1617_, 1);
lean_ctor_set(v___x_1617_, 0, v___x_1620_);
v___x_1622_ = v___x_1617_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
default: 
{
lean_object* v___x_1626_; 
lean_dec(v_x_1364_);
lean_dec_ref(v_date_1363_);
v___x_1626_ = lean_box(0);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format(lean_object* v_date_1627_, lean_object* v_format_1628_){
_start:
{
uint8_t v___x_1629_; lean_object* v_format_1630_; 
v___x_1629_ = 0;
v_format_1630_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1628_, v___x_1629_);
if (lean_obj_tag(v_format_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec_ref(v_date_1627_);
v_a_1631_ = lean_ctor_get(v_format_1630_, 0);
lean_inc(v_a_1631_);
lean_dec_ref(v_format_1630_);
v___x_1632_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1633_ = lean_string_append(v___x_1632_, v_a_1631_);
lean_dec(v_a_1631_);
return v___x_1633_;
}
else
{
lean_object* v_a_1634_; lean_object* v___f_1635_; lean_object* v_res_1636_; 
v_a_1634_ = lean_ctor_get(v_format_1630_, 0);
lean_inc(v_a_1634_);
lean_dec_ref(v_format_1630_);
v___f_1635_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_format___lam__0), 2, 1);
lean_closure_set(v___f_1635_, 0, v_date_1627_);
v_res_1636_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1634_, v___f_1635_);
if (lean_obj_tag(v_res_1636_) == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1637_;
}
else
{
lean_object* v_val_1638_; 
v_val_1638_ = lean_ctor_get(v_res_1636_, 0);
lean_inc(v_val_1638_);
lean_dec_ref(v_res_1636_);
return v_val_1638_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = l_Std_Time_TimeZone_GMT;
v___x_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromAscTimeString(lean_object* v_input_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1642_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1643_ = ((lean_object*)(l_Std_Time_Formats_ascTime));
v___x_1644_ = l_Std_Time_GenericFormat_parse(v___x_1642_, v___x_1643_, v_input_1641_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
else
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1662_; 
v_a_1653_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1655_ = v___x_1644_;
v_isShared_1656_ = v_isSharedCheck_1662_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1644_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1662_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v_date_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; 
v_date_1657_ = lean_ctor_get(v_a_1653_, 1);
lean_inc_ref(v_date_1657_);
lean_dec(v_a_1653_);
v___x_1658_ = lean_thunk_get_own(v_date_1657_);
lean_dec_ref(v_date_1657_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1658_);
v___x_1660_ = v___x_1655_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0(lean_object* v_pdt_1663_, lean_object* v___x_1664_, lean_object* v_x_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v_second_1667_; lean_object* v_nano_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_second_1673_; lean_object* v_nano_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1666_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_pdt_1663_);
v_second_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_second_1667_);
v_nano_1668_ = lean_ctor_get(v___x_1666_, 1);
lean_inc(v_nano_1668_);
lean_dec_ref(v___x_1666_);
v___x_1669_ = l_Std_Time_TimeZone_toSeconds(v___x_1664_);
v___x_1670_ = lean_obj_once(&l_Std_Time_ZonedDateTime_format___lam__0___closed__0, &l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0);
v___x_1671_ = lean_int_mul(v___x_1669_, v___x_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = l_Std_Time_Duration_ofNanoseconds(v___x_1671_);
lean_dec(v___x_1671_);
v_second_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_second_1673_);
v_nano_1674_ = lean_ctor_get(v___x_1672_, 1);
lean_inc(v_nano_1674_);
lean_dec_ref(v___x_1672_);
v___x_1675_ = lean_int_mul(v_second_1667_, v___x_1670_);
lean_dec(v_second_1667_);
v___x_1676_ = lean_int_add(v___x_1675_, v_nano_1668_);
lean_dec(v_nano_1668_);
lean_dec(v___x_1675_);
v___x_1677_ = lean_int_mul(v_second_1673_, v___x_1670_);
lean_dec(v_second_1673_);
v___x_1678_ = lean_int_add(v___x_1677_, v_nano_1674_);
lean_dec(v_nano_1674_);
lean_dec(v___x_1677_);
v___x_1679_ = lean_int_add(v___x_1676_, v___x_1678_);
lean_dec(v___x_1678_);
lean_dec(v___x_1676_);
v___x_1680_ = l_Std_Time_Duration_ofNanoseconds(v___x_1679_);
lean_dec(v___x_1679_);
v___x_1681_ = l_Std_Time_PlainDateTime_ofTimestampAssumingUTC(v___x_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(lean_object* v_pdt_1682_, lean_object* v___x_1683_, lean_object* v_x_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Std_Time_PlainDateTime_toAscTimeString___lam__0(v_pdt_1682_, v___x_1683_, v_x_1684_);
lean_dec_ref(v___x_1683_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString(lean_object* v_pdt_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; lean_object* v_tm_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1687_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1688_ = l_Std_Time_TimeZone_UTC;
lean_inc_ref(v_pdt_1686_);
v___f_1689_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1689_, 0, v_pdt_1686_);
lean_closure_set(v___f_1689_, 1, v___x_1688_);
v___x_1690_ = ((lean_object*)(l_Std_Time_Formats_ascTime));
v_tm_1691_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_pdt_1686_);
v___x_1692_ = lean_mk_thunk(v___f_1689_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_tm_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Std_Time_GenericFormat_format(v___x_1687_, v___x_1688_, v___x_1690_, v___x_1693_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLongDateFormatString(lean_object* v_input_1695_){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1697_ = ((lean_object*)(l_Std_Time_Formats_longDateFormat));
v___x_1698_ = l_Std_Time_GenericFormat_parse(v___x_1696_, v___x_1697_, v_input_1695_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1716_; 
v_a_1707_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1709_ = v___x_1698_;
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1698_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1716_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v_date_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v_date_1711_ = lean_ctor_get(v_a_1707_, 1);
lean_inc_ref(v_date_1711_);
lean_dec(v_a_1707_);
v___x_1712_ = lean_thunk_get_own(v_date_1711_);
lean_dec_ref(v_date_1711_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1712_);
v___x_1714_ = v___x_1709_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLongDateFormatString(lean_object* v_pdt_1717_){
_start:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___f_1720_; lean_object* v___x_1721_; lean_object* v_tm_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1718_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1719_ = l_Std_Time_TimeZone_UTC;
lean_inc_ref(v_pdt_1717_);
v___f_1720_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1720_, 0, v_pdt_1717_);
lean_closure_set(v___f_1720_, 1, v___x_1719_);
v___x_1721_ = ((lean_object*)(l_Std_Time_Formats_longDateFormat));
v_tm_1722_ = l_Std_Time_PlainDateTime_toTimestampAssumingUTC(v_pdt_1717_);
v___x_1723_ = lean_mk_thunk(v___f_1720_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_tm_1722_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = l_Std_Time_GenericFormat_format(v___x_1718_, v___x_1719_, v___x_1721_, v___x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromDateTimeString(lean_object* v_input_1726_){
_start:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1728_ = ((lean_object*)(l_Std_Time_Formats_dateTime24Hour));
v___x_1729_ = l_Std_Time_GenericFormat_parse(v___x_1727_, v___x_1728_, v_input_1726_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1737_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1737_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1735_; 
if (v_isShared_1733_ == 0)
{
v___x_1735_ = v___x_1732_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1747_; 
v_a_1738_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1740_ = v___x_1729_;
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1729_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1747_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_date_1742_; lean_object* v___x_1743_; lean_object* v___x_1745_; 
v_date_1742_ = lean_ctor_get(v_a_1738_, 1);
lean_inc_ref(v_date_1742_);
lean_dec(v_a_1738_);
v___x_1743_ = lean_thunk_get_own(v_date_1742_);
lean_dec_ref(v_date_1742_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toDateTimeString(lean_object* v_pdt_1748_){
_start:
{
lean_object* v_date_1749_; lean_object* v_time_1750_; lean_object* v_year_1751_; lean_object* v_month_1752_; lean_object* v_day_1753_; lean_object* v_hour_1754_; lean_object* v_minute_1755_; lean_object* v_second_1756_; lean_object* v_nanosecond_1757_; lean_object* v___x_1758_; lean_object* v___x_12__overap_1759_; lean_object* v___x_1760_; 
v_date_1749_ = lean_ctor_get(v_pdt_1748_, 0);
lean_inc_ref(v_date_1749_);
v_time_1750_ = lean_ctor_get(v_pdt_1748_, 1);
lean_inc_ref(v_time_1750_);
lean_dec_ref(v_pdt_1748_);
v_year_1751_ = lean_ctor_get(v_date_1749_, 0);
lean_inc(v_year_1751_);
v_month_1752_ = lean_ctor_get(v_date_1749_, 1);
lean_inc(v_month_1752_);
v_day_1753_ = lean_ctor_get(v_date_1749_, 2);
lean_inc(v_day_1753_);
lean_dec_ref(v_date_1749_);
v_hour_1754_ = lean_ctor_get(v_time_1750_, 0);
lean_inc(v_hour_1754_);
v_minute_1755_ = lean_ctor_get(v_time_1750_, 1);
lean_inc(v_minute_1755_);
v_second_1756_ = lean_ctor_get(v_time_1750_, 2);
lean_inc(v_second_1756_);
v_nanosecond_1757_ = lean_ctor_get(v_time_1750_, 3);
lean_inc(v_nanosecond_1757_);
lean_dec_ref(v_time_1750_);
v___x_1758_ = ((lean_object*)(l_Std_Time_Formats_dateTime24Hour));
v___x_12__overap_1759_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1758_);
v___x_1760_ = lean_apply_7(v___x_12__overap_1759_, v_year_1751_, v_month_1752_, v_day_1753_, v_hour_1754_, v_minute_1755_, v_second_1756_, v_nanosecond_1757_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLeanDateTimeString(lean_object* v_input_1761_){
_start:
{
lean_object* v___y_1763_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1783_ = ((lean_object*)(l_Std_Time_Formats_leanDateTime24Hour));
lean_inc_ref(v_input_1761_);
v___x_1784_ = l_Std_Time_GenericFormat_parse(v___x_1782_, v___x_1783_, v_input_1761_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
lean_dec_ref(v___x_1784_);
v___x_1785_ = ((lean_object*)(l_Std_Time_Formats_leanDateTime24HourNoNanos));
v___x_1786_ = l_Std_Time_GenericFormat_parse(v___x_1782_, v___x_1785_, v_input_1761_);
v___y_1763_ = v___x_1786_;
goto v___jp_1762_;
}
else
{
lean_dec_ref(v_input_1761_);
v___y_1763_ = v___x_1784_;
goto v___jp_1762_;
}
v___jp_1762_:
{
if (lean_obj_tag(v___y_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
v_a_1764_ = lean_ctor_get(v___y_1763_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___y_1763_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___y_1763_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___y_1763_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1781_; 
v_a_1772_ = lean_ctor_get(v___y_1763_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___y_1763_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1774_ = v___y_1763_;
v_isShared_1775_ = v_isSharedCheck_1781_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___y_1763_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1781_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v_date_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v_date_1776_ = lean_ctor_get(v_a_1772_, 1);
lean_inc_ref(v_date_1776_);
lean_dec(v_a_1772_);
v___x_1777_ = lean_thunk_get_own(v_date_1776_);
lean_dec_ref(v_date_1776_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1777_);
v___x_1779_ = v___x_1774_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLeanDateTimeString(lean_object* v_pdt_1787_){
_start:
{
lean_object* v_date_1788_; lean_object* v_time_1789_; lean_object* v_year_1790_; lean_object* v_month_1791_; lean_object* v_day_1792_; lean_object* v_hour_1793_; lean_object* v_minute_1794_; lean_object* v_second_1795_; lean_object* v_nanosecond_1796_; lean_object* v___x_1797_; lean_object* v___x_12__overap_1798_; lean_object* v___x_1799_; 
v_date_1788_ = lean_ctor_get(v_pdt_1787_, 0);
lean_inc_ref(v_date_1788_);
v_time_1789_ = lean_ctor_get(v_pdt_1787_, 1);
lean_inc_ref(v_time_1789_);
lean_dec_ref(v_pdt_1787_);
v_year_1790_ = lean_ctor_get(v_date_1788_, 0);
lean_inc(v_year_1790_);
v_month_1791_ = lean_ctor_get(v_date_1788_, 1);
lean_inc(v_month_1791_);
v_day_1792_ = lean_ctor_get(v_date_1788_, 2);
lean_inc(v_day_1792_);
lean_dec_ref(v_date_1788_);
v_hour_1793_ = lean_ctor_get(v_time_1789_, 0);
lean_inc(v_hour_1793_);
v_minute_1794_ = lean_ctor_get(v_time_1789_, 1);
lean_inc(v_minute_1794_);
v_second_1795_ = lean_ctor_get(v_time_1789_, 2);
lean_inc(v_second_1795_);
v_nanosecond_1796_ = lean_ctor_get(v_time_1789_, 3);
lean_inc(v_nanosecond_1796_);
lean_dec_ref(v_time_1789_);
v___x_1797_ = ((lean_object*)(l_Std_Time_Formats_leanDateTime24Hour));
v___x_12__overap_1798_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1797_);
v___x_1799_ = lean_apply_7(v___x_12__overap_1798_, v_year_1790_, v_month_1791_, v_day_1792_, v_hour_1793_, v_minute_1794_, v_second_1795_, v_nanosecond_1796_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_parse(lean_object* v_date_1800_){
_start:
{
lean_object* v___x_1801_; 
lean_inc_ref(v_date_1800_);
v___x_1801_ = l_Std_Time_PlainDateTime_fromAscTimeString(v_date_1800_);
if (lean_obj_tag(v___x_1801_) == 0)
{
lean_object* v___x_1802_; 
lean_dec_ref(v___x_1801_);
lean_inc_ref(v_date_1800_);
v___x_1802_ = l_Std_Time_PlainDateTime_fromLongDateFormatString(v_date_1800_);
if (lean_obj_tag(v___x_1802_) == 0)
{
lean_object* v___x_1803_; 
lean_dec_ref(v___x_1802_);
lean_inc_ref(v_date_1800_);
v___x_1803_ = l_Std_Time_PlainDateTime_fromDateTimeString(v_date_1800_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref(v___x_1803_);
v___x_1804_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v_date_1800_);
return v___x_1804_;
}
else
{
lean_dec_ref(v_date_1800_);
return v___x_1803_;
}
}
else
{
lean_dec_ref(v_date_1800_);
return v___x_1802_;
}
}
else
{
lean_dec_ref(v_date_1800_);
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0(lean_object* v_data_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1812_ = ((lean_object*)(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1));
v___x_1813_ = l_Std_Time_PlainDateTime_toLeanDateTimeString(v_data_1810_);
v___x_1814_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
v___x_1815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1812_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
v___x_1816_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1815_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
v___x_1818_ = l_Repr_addAppParen(v___x_1817_, v___y_1811_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0___boxed(lean_object* v_data_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Std_Time_PlainDateTime_instRepr___lam__0(v_data_1819_, v___y_1820_);
lean_dec(v___y_1820_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format(lean_object* v_tz_1824_, lean_object* v_data_1825_, lean_object* v_format_1826_){
_start:
{
uint8_t v___x_1827_; lean_object* v_format_1828_; 
v___x_1827_ = 0;
v_format_1828_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1826_, v___x_1827_);
if (lean_obj_tag(v_format_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
lean_dec_ref(v_data_1825_);
v_a_1829_ = lean_ctor_get(v_format_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v_format_1828_);
v___x_1830_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1831_ = lean_string_append(v___x_1830_, v_a_1829_);
lean_dec(v_a_1829_);
return v___x_1831_;
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v_a_1832_ = lean_ctor_get(v_format_1828_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v_format_1828_);
v___x_1833_ = lean_box(1);
v___x_1834_ = l_Std_Time_GenericFormat_format(v___x_1833_, v_tz_1824_, v_a_1832_, v_data_1825_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format___boxed(lean_object* v_tz_1835_, lean_object* v_data_1836_, lean_object* v_format_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Std_Time_DateTime_format(v_tz_1835_, v_data_1836_, v_format_1837_);
lean_dec_ref(v_tz_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromAscTimeString(lean_object* v_input_1839_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1841_ = ((lean_object*)(l_Std_Time_Formats_ascTime));
v___x_1842_ = l_Std_Time_GenericFormat_parse(v___x_1840_, v___x_1841_, v_input_1839_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toAscTimeString(lean_object* v_datetime_1843_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1844_ = l_Std_Time_TimeZone_GMT;
v___x_1845_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1846_ = ((lean_object*)(l_Std_Time_Formats_ascTime));
v___x_1847_ = l_Std_Time_GenericFormat_format(v___x_1845_, v___x_1844_, v___x_1846_, v_datetime_1843_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLongDateFormatString(lean_object* v_input_1848_){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1850_ = ((lean_object*)(l_Std_Time_Formats_longDateFormat));
v___x_1851_ = l_Std_Time_GenericFormat_parse(v___x_1849_, v___x_1850_, v_input_1848_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLongDateFormatString(lean_object* v_datetime_1852_){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1853_ = l_Std_Time_TimeZone_GMT;
v___x_1854_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1855_ = ((lean_object*)(l_Std_Time_Formats_longDateFormat));
v___x_1856_ = l_Std_Time_GenericFormat_format(v___x_1854_, v___x_1853_, v___x_1855_, v_datetime_1852_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String(lean_object* v_tz_1857_, lean_object* v_date_1858_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = lean_box(1);
v___x_1860_ = ((lean_object*)(l_Std_Time_Formats_iso8601));
v___x_1861_ = l_Std_Time_GenericFormat_format(v___x_1859_, v_tz_1857_, v___x_1860_, v_date_1858_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String___boxed(lean_object* v_tz_1862_, lean_object* v_date_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Std_Time_DateTime_toISO8601String(v_tz_1862_, v_date_1863_);
lean_dec_ref(v_tz_1862_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String(lean_object* v_tz_1865_, lean_object* v_date_1866_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_box(1);
v___x_1868_ = ((lean_object*)(l_Std_Time_Formats_rfc822));
v___x_1869_ = l_Std_Time_GenericFormat_format(v___x_1867_, v_tz_1865_, v___x_1868_, v_date_1866_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String___boxed(lean_object* v_tz_1870_, lean_object* v_date_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Std_Time_DateTime_toRFC822String(v_tz_1870_, v_date_1871_);
lean_dec_ref(v_tz_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String(lean_object* v_tz_1873_, lean_object* v_date_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_box(1);
v___x_1876_ = ((lean_object*)(l_Std_Time_Formats_rfc850));
v___x_1877_ = l_Std_Time_GenericFormat_format(v___x_1875_, v_tz_1873_, v___x_1876_, v_date_1874_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String___boxed(lean_object* v_tz_1878_, lean_object* v_date_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Std_Time_DateTime_toRFC850String(v_tz_1878_, v_date_1879_);
lean_dec_ref(v_tz_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString(lean_object* v_tz_1881_, lean_object* v_pdt_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_box(1);
v___x_1884_ = ((lean_object*)(l_Std_Time_Formats_dateTimeWithZone));
v___x_1885_ = l_Std_Time_GenericFormat_format(v___x_1883_, v_tz_1881_, v___x_1884_, v_pdt_1882_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString___boxed(lean_object* v_tz_1886_, lean_object* v_pdt_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_Std_Time_DateTime_toDateTimeWithZoneString(v_tz_1886_, v_pdt_1887_);
lean_dec_ref(v_tz_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString(lean_object* v_tz_1889_, lean_object* v_pdt_1890_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = lean_box(1);
v___x_1892_ = ((lean_object*)(l_Std_Time_Formats_leanDateTimeWithZone));
v___x_1893_ = l_Std_Time_GenericFormat_format(v___x_1891_, v_tz_1889_, v___x_1892_, v_pdt_1890_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString___boxed(lean_object* v_tz_1894_, lean_object* v_pdt_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_tz_1894_, v_pdt_1895_);
lean_dec_ref(v_tz_1894_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_parse(lean_object* v_date_1897_){
_start:
{
lean_object* v___x_1898_; 
lean_inc_ref(v_date_1897_);
v___x_1898_ = l_Std_Time_DateTime_fromAscTimeString(v_date_1897_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v___x_1899_; 
lean_dec_ref(v___x_1898_);
v___x_1899_ = l_Std_Time_DateTime_fromLongDateFormatString(v_date_1897_);
return v___x_1899_;
}
else
{
lean_dec_ref(v_date_1897_);
return v___x_1898_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0(lean_object* v_tz_1900_, lean_object* v_data_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_tz_1900_, v_data_1901_);
v___x_1904_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
v___x_1905_ = l_Repr_addAppParen(v___x_1904_, v___y_1902_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0___boxed(lean_object* v_tz_1906_, lean_object* v_data_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Std_Time_DateTime_instRepr___lam__0(v_tz_1906_, v_data_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v_tz_1906_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr(lean_object* v_tz_1910_){
_start:
{
lean_object* v___f_1911_; 
v___f_1911_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_instRepr___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1911_, 0, v_tz_1910_);
return v___f_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instToString(lean_object* v_tz_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_toLeanDateTimeWithZoneString___boxed), 2, 1);
lean_closure_set(v___x_1913_, 0, v_tz_1912_);
return v___x_1913_;
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

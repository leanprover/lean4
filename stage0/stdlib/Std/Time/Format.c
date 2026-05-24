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
lean_object* lean_thunk_get_own(lean_object*);
lean_object* l_Std_Time_PlainDate_dayOfYear(lean_object*);
uint8_t l_Std_Time_Year_Offset_era(lean_object*);
lean_object* l_Std_Time_PlainDate_weekYear(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDate_quarter(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfYear(lean_object*, uint8_t);
lean_object* l_Std_Time_PlainDate_alignedWeekOfMonth(lean_object*, uint8_t);
uint8_t l_Std_Time_PlainDate_weekday(lean_object*);
lean_object* l_Std_Time_PlainDate_weekOfMonth(lean_object*);
extern lean_object* l_Std_Time_TimeZone_GMT;
lean_object* l_Std_Time_GenericFormat_format(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* l_Std_Time_PlainDateTime_ofWallTime(lean_object*);
lean_object* lean_mk_thunk(lean_object*);
lean_object* l_Std_Time_GenericFormat_parse(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Std_Time_GenericFormat_spec___redArg(lean_object*, lean_object*);
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
lean_object* l_Std_Time_PlainDateTime_toWallTime(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_fromAscTimeString___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromAscTimeString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_PlainDateTime_toAscTimeString___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_PlainDateTime_toAscTimeString___closed__0;
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
static lean_object* _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = lean_unsigned_to_nat(1000000000u);
v___x_1224_ = lean_nat_to_int(v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_format___lam__0(lean_object* v_timezone_1225_, lean_object* v_timestamp_1226_, lean_object* v_x_1227_){
_start:
{
lean_object* v_offset_1228_; lean_object* v_second_1229_; lean_object* v_nano_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_offset_1228_ = lean_ctor_get(v_timezone_1225_, 0);
v_second_1229_ = lean_ctor_get(v_timestamp_1226_, 0);
v_nano_1230_ = lean_ctor_get(v_timestamp_1226_, 1);
v___x_1231_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1232_ = lean_obj_once(&l_Std_Time_ZonedDateTime_format___lam__0___closed__0, &l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0);
v___x_1233_ = lean_int_mul(v_second_1229_, v___x_1232_);
v___x_1234_ = lean_int_add(v___x_1233_, v_nano_1230_);
lean_dec(v___x_1233_);
v___x_1235_ = lean_int_mul(v_offset_1228_, v___x_1232_);
v___x_1236_ = lean_int_add(v___x_1235_, v___x_1231_);
lean_dec(v___x_1235_);
v___x_1237_ = lean_int_add(v___x_1234_, v___x_1236_);
lean_dec(v___x_1236_);
lean_dec(v___x_1234_);
v___x_1238_ = l_Std_Time_Duration_ofNanoseconds(v___x_1237_);
lean_dec(v___x_1237_);
v___x_1239_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_format___lam__0___boxed(lean_object* v_timezone_1240_, lean_object* v_timestamp_1241_, lean_object* v_x_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Std_Time_ZonedDateTime_format___lam__0(v_timezone_1240_, v_timestamp_1241_, v_x_1242_);
lean_dec_ref(v_timestamp_1241_);
lean_dec_ref(v_timezone_1240_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_format(lean_object* v_data_1244_, lean_object* v_format_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v_format_1247_; 
v___x_1246_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1247_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1245_, v___x_1246_);
if (lean_obj_tag(v_format_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec_ref(v_data_1244_);
v_a_1248_ = lean_ctor_get(v_format_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v_format_1247_, 1);
v___x_1249_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1250_ = lean_string_append(v___x_1249_, v_a_1248_);
lean_dec(v_a_1248_);
return v___x_1250_;
}
else
{
lean_object* v_a_1251_; lean_object* v_timestamp_1252_; lean_object* v_timezone_1253_; lean_object* v___x_1254_; lean_object* v___f_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_a_1251_ = lean_ctor_get(v_format_1247_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v_format_1247_, 1);
v_timestamp_1252_ = lean_ctor_get(v_data_1244_, 1);
lean_inc_ref_n(v_timestamp_1252_, 2);
v_timezone_1253_ = lean_ctor_get(v_data_1244_, 3);
lean_inc_ref_n(v_timezone_1253_, 2);
lean_dec_ref(v_data_1244_);
v___x_1254_ = lean_box(1);
v___f_1255_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1255_, 0, v_timezone_1253_);
lean_closure_set(v___f_1255_, 1, v_timestamp_1252_);
v___x_1256_ = lean_mk_thunk(v___f_1255_);
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_timestamp_1252_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = l_Std_Time_GenericFormat_format(v___x_1254_, v_timezone_1253_, v_a_1251_, v___x_1257_);
lean_dec_ref(v_timezone_1253_);
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromISO8601String(lean_object* v_input_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1260_ = lean_box(1);
v___x_1261_ = l_Std_Time_Formats_iso8601;
v___x_1262_ = l_Std_Time_GenericFormat_parse(v___x_1260_, v___x_1261_, v_input_1259_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toISO8601String(lean_object* v_date_1263_){
_start:
{
lean_object* v_timestamp_1264_; lean_object* v_timezone_1265_; lean_object* v___x_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_timestamp_1264_ = lean_ctor_get(v_date_1263_, 1);
lean_inc_ref_n(v_timestamp_1264_, 2);
v_timezone_1265_ = lean_ctor_get(v_date_1263_, 3);
lean_inc_ref_n(v_timezone_1265_, 2);
lean_dec_ref(v_date_1263_);
v___x_1266_ = lean_box(1);
v___f_1267_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1267_, 0, v_timezone_1265_);
lean_closure_set(v___f_1267_, 1, v_timestamp_1264_);
v___x_1268_ = l_Std_Time_Formats_iso8601;
v___x_1269_ = lean_mk_thunk(v___f_1267_);
v___x_1270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1270_, 0, v_timestamp_1264_);
lean_ctor_set(v___x_1270_, 1, v___x_1269_);
v___x_1271_ = l_Std_Time_GenericFormat_format(v___x_1266_, v_timezone_1265_, v___x_1268_, v___x_1270_);
lean_dec_ref(v_timezone_1265_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromRFC822String(lean_object* v_input_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_box(1);
v___x_1274_ = l_Std_Time_Formats_rfc822;
v___x_1275_ = l_Std_Time_GenericFormat_parse(v___x_1273_, v___x_1274_, v_input_1272_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toRFC822String(lean_object* v_date_1276_){
_start:
{
lean_object* v_timestamp_1277_; lean_object* v_timezone_1278_; lean_object* v___x_1279_; lean_object* v___f_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_timestamp_1277_ = lean_ctor_get(v_date_1276_, 1);
lean_inc_ref_n(v_timestamp_1277_, 2);
v_timezone_1278_ = lean_ctor_get(v_date_1276_, 3);
lean_inc_ref_n(v_timezone_1278_, 2);
lean_dec_ref(v_date_1276_);
v___x_1279_ = lean_box(1);
v___f_1280_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1280_, 0, v_timezone_1278_);
lean_closure_set(v___f_1280_, 1, v_timestamp_1277_);
v___x_1281_ = l_Std_Time_Formats_rfc822;
v___x_1282_ = lean_mk_thunk(v___f_1280_);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v_timestamp_1277_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = l_Std_Time_GenericFormat_format(v___x_1279_, v_timezone_1278_, v___x_1281_, v___x_1283_);
lean_dec_ref(v_timezone_1278_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromRFC850String(lean_object* v_input_1285_){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_box(1);
v___x_1287_ = l_Std_Time_Formats_rfc850;
v___x_1288_ = l_Std_Time_GenericFormat_parse(v___x_1286_, v___x_1287_, v_input_1285_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toRFC850String(lean_object* v_date_1289_){
_start:
{
lean_object* v_timestamp_1290_; lean_object* v_timezone_1291_; lean_object* v___x_1292_; lean_object* v___f_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_timestamp_1290_ = lean_ctor_get(v_date_1289_, 1);
lean_inc_ref_n(v_timestamp_1290_, 2);
v_timezone_1291_ = lean_ctor_get(v_date_1289_, 3);
lean_inc_ref_n(v_timezone_1291_, 2);
lean_dec_ref(v_date_1289_);
v___x_1292_ = lean_box(1);
v___f_1293_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1293_, 0, v_timezone_1291_);
lean_closure_set(v___f_1293_, 1, v_timestamp_1290_);
v___x_1294_ = l_Std_Time_Formats_rfc850;
v___x_1295_ = lean_mk_thunk(v___f_1293_);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v_timestamp_1290_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = l_Std_Time_GenericFormat_format(v___x_1292_, v_timezone_1291_, v___x_1294_, v___x_1296_);
lean_dec_ref(v_timezone_1291_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromDateTimeWithZoneString(lean_object* v_input_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
v___x_1299_ = lean_box(1);
v___x_1300_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1301_ = l_Std_Time_GenericFormat_parse(v___x_1299_, v___x_1300_, v_input_1298_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toDateTimeWithZoneString(lean_object* v_pdt_1302_){
_start:
{
lean_object* v_timestamp_1303_; lean_object* v_timezone_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v_timestamp_1303_ = lean_ctor_get(v_pdt_1302_, 1);
lean_inc_ref_n(v_timestamp_1303_, 2);
v_timezone_1304_ = lean_ctor_get(v_pdt_1302_, 3);
lean_inc_ref_n(v_timezone_1304_, 2);
lean_dec_ref(v_pdt_1302_);
v___x_1305_ = lean_box(1);
v___f_1306_ = lean_alloc_closure((void*)(l_Std_Time_ZonedDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1306_, 0, v_timezone_1304_);
lean_closure_set(v___f_1306_, 1, v_timestamp_1303_);
v___x_1307_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1308_ = lean_mk_thunk(v___f_1306_);
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v_timestamp_1303_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = l_Std_Time_GenericFormat_format(v___x_1305_, v_timezone_1304_, v___x_1307_, v___x_1309_);
lean_dec_ref(v_timezone_1304_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromLeanDateTimeWithZoneString(lean_object* v_input_1311_){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_box(1);
v___x_1313_ = l_Std_Time_Formats_leanDateTimeWithZone;
lean_inc_ref(v_input_1311_);
v___x_1314_ = l_Std_Time_GenericFormat_parse(v___x_1312_, v___x_1313_, v_input_1311_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_dec_ref_known(v___x_1314_, 1);
v___x_1315_ = l_Std_Time_Formats_leanDateTimeWithZoneNoNanos;
v___x_1316_ = l_Std_Time_GenericFormat_parse(v___x_1312_, v___x_1315_, v_input_1311_);
return v___x_1316_;
}
else
{
lean_dec_ref(v_input_1311_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(lean_object* v_input_1317_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_box(1);
v___x_1319_ = l_Std_Time_Formats_leanDateTimeWithIdentifier;
lean_inc_ref(v_input_1317_);
v___x_1320_ = l_Std_Time_GenericFormat_parse(v___x_1318_, v___x_1319_, v_input_1317_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref_known(v___x_1320_, 1);
v___x_1321_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_1322_ = l_Std_Time_GenericFormat_parse(v___x_1318_, v___x_1321_, v_input_1317_);
return v___x_1322_;
}
else
{
lean_dec_ref(v_input_1317_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toLeanDateTimeWithZoneString(lean_object* v_zdt_1323_){
_start:
{
lean_object* v_date_1324_; lean_object* v_timezone_1325_; lean_object* v___x_1326_; lean_object* v_date_1327_; lean_object* v_time_1328_; lean_object* v_year_1329_; lean_object* v_month_1330_; lean_object* v_day_1331_; lean_object* v_hour_1332_; lean_object* v_minute_1333_; lean_object* v_second_1334_; lean_object* v_nanosecond_1335_; lean_object* v_offset_1336_; lean_object* v___x_1337_; lean_object* v___x_14__overap_1338_; lean_object* v___x_1339_; 
v_date_1324_ = lean_ctor_get(v_zdt_1323_, 0);
lean_inc_ref(v_date_1324_);
v_timezone_1325_ = lean_ctor_get(v_zdt_1323_, 3);
lean_inc_ref(v_timezone_1325_);
lean_dec_ref(v_zdt_1323_);
v___x_1326_ = lean_thunk_get_own(v_date_1324_);
lean_dec_ref(v_date_1324_);
v_date_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc_ref(v_date_1327_);
v_time_1328_ = lean_ctor_get(v___x_1326_, 1);
lean_inc_ref(v_time_1328_);
lean_dec(v___x_1326_);
v_year_1329_ = lean_ctor_get(v_date_1327_, 0);
lean_inc(v_year_1329_);
v_month_1330_ = lean_ctor_get(v_date_1327_, 1);
lean_inc(v_month_1330_);
v_day_1331_ = lean_ctor_get(v_date_1327_, 2);
lean_inc(v_day_1331_);
lean_dec_ref(v_date_1327_);
v_hour_1332_ = lean_ctor_get(v_time_1328_, 0);
lean_inc(v_hour_1332_);
v_minute_1333_ = lean_ctor_get(v_time_1328_, 1);
lean_inc(v_minute_1333_);
v_second_1334_ = lean_ctor_get(v_time_1328_, 2);
lean_inc(v_second_1334_);
v_nanosecond_1335_ = lean_ctor_get(v_time_1328_, 3);
lean_inc(v_nanosecond_1335_);
lean_dec_ref(v_time_1328_);
v_offset_1336_ = lean_ctor_get(v_timezone_1325_, 0);
lean_inc(v_offset_1336_);
lean_dec_ref(v_timezone_1325_);
v___x_1337_ = l_Std_Time_Formats_leanDateTimeWithZone;
v___x_14__overap_1338_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1337_);
v___x_1339_ = lean_apply_8(v___x_14__overap_1338_, v_year_1329_, v_month_1330_, v_day_1331_, v_hour_1332_, v_minute_1333_, v_second_1334_, v_nanosecond_1335_, v_offset_1336_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_toLeanDateTimeWithIdentifierString(lean_object* v_zdt_1340_){
_start:
{
lean_object* v_date_1341_; lean_object* v_timezone_1342_; lean_object* v___x_1343_; lean_object* v_date_1344_; lean_object* v_time_1345_; lean_object* v_year_1346_; lean_object* v_month_1347_; lean_object* v_day_1348_; lean_object* v_hour_1349_; lean_object* v_minute_1350_; lean_object* v_second_1351_; lean_object* v_nanosecond_1352_; lean_object* v_name_1353_; lean_object* v___x_1354_; lean_object* v___x_15__overap_1355_; lean_object* v___x_1356_; 
v_date_1341_ = lean_ctor_get(v_zdt_1340_, 0);
lean_inc_ref(v_date_1341_);
v_timezone_1342_ = lean_ctor_get(v_zdt_1340_, 3);
lean_inc_ref(v_timezone_1342_);
lean_dec_ref(v_zdt_1340_);
v___x_1343_ = lean_thunk_get_own(v_date_1341_);
lean_dec_ref(v_date_1341_);
v_date_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc_ref(v_date_1344_);
v_time_1345_ = lean_ctor_get(v___x_1343_, 1);
lean_inc_ref(v_time_1345_);
lean_dec(v___x_1343_);
v_year_1346_ = lean_ctor_get(v_date_1344_, 0);
lean_inc(v_year_1346_);
v_month_1347_ = lean_ctor_get(v_date_1344_, 1);
lean_inc(v_month_1347_);
v_day_1348_ = lean_ctor_get(v_date_1344_, 2);
lean_inc(v_day_1348_);
lean_dec_ref(v_date_1344_);
v_hour_1349_ = lean_ctor_get(v_time_1345_, 0);
lean_inc(v_hour_1349_);
v_minute_1350_ = lean_ctor_get(v_time_1345_, 1);
lean_inc(v_minute_1350_);
v_second_1351_ = lean_ctor_get(v_time_1345_, 2);
lean_inc(v_second_1351_);
v_nanosecond_1352_ = lean_ctor_get(v_time_1345_, 3);
lean_inc(v_nanosecond_1352_);
lean_dec_ref(v_time_1345_);
v_name_1353_ = lean_ctor_get(v_timezone_1342_, 1);
lean_inc_ref(v_name_1353_);
lean_dec_ref(v_timezone_1342_);
v___x_1354_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
v___x_15__overap_1355_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1354_);
v___x_1356_ = lean_apply_8(v___x_15__overap_1355_, v_year_1346_, v_month_1347_, v_day_1348_, v_hour_1349_, v_minute_1350_, v_second_1351_, v_nanosecond_1352_, v_name_1353_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_parse(lean_object* v_input_1357_){
_start:
{
lean_object* v___x_1358_; 
lean_inc_ref(v_input_1357_);
v___x_1358_ = l_Std_Time_ZonedDateTime_fromISO8601String(v_input_1357_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref_known(v___x_1358_, 1);
lean_inc_ref(v_input_1357_);
v___x_1359_ = l_Std_Time_ZonedDateTime_fromRFC822String(v_input_1357_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1360_; 
lean_dec_ref_known(v___x_1359_, 1);
lean_inc_ref(v_input_1357_);
v___x_1360_ = l_Std_Time_ZonedDateTime_fromRFC850String(v_input_1357_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v___x_1361_; 
lean_dec_ref_known(v___x_1360_, 1);
lean_inc_ref(v_input_1357_);
v___x_1361_ = l_Std_Time_ZonedDateTime_fromDateTimeWithZoneString(v_input_1357_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v___x_1362_; 
lean_dec_ref_known(v___x_1361_, 1);
v___x_1362_ = l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(v_input_1357_);
return v___x_1362_;
}
else
{
lean_dec_ref(v_input_1357_);
return v___x_1361_;
}
}
else
{
lean_dec_ref(v_input_1357_);
return v___x_1360_;
}
}
else
{
lean_dec_ref(v_input_1357_);
return v___x_1359_;
}
}
else
{
lean_dec_ref(v_input_1357_);
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instRepr___lam__0(lean_object* v_data_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1370_ = ((lean_object*)(l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1));
v___x_1371_ = l_Std_Time_ZonedDateTime_toLeanDateTimeWithZoneString(v_data_1368_);
v___x_1372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1371_);
v___x_1373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1370_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Repr_addAppParen(v___x_1375_, v___y_1369_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ZonedDateTime_instRepr___lam__0___boxed(lean_object* v_data_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_Time_ZonedDateTime_instRepr___lam__0(v_data_1377_, v___y_1378_);
lean_dec(v___y_1378_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0(lean_object* v_date_1382_, lean_object* v_locale_1383_, lean_object* v_x_1384_){
_start:
{
switch(lean_obj_tag(v_x_1384_))
{
case 0:
{
lean_object* v_date_1385_; lean_object* v_year_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref_known(v_x_1384_, 0);
v_date_1385_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1385_);
lean_dec_ref(v_date_1382_);
v_year_1386_ = lean_ctor_get(v_date_1385_, 0);
lean_inc(v_year_1386_);
lean_dec_ref(v_date_1385_);
v___x_1387_ = l_Std_Time_Year_Offset_era(v_year_1386_);
lean_dec(v_year_1386_);
v___x_1388_ = lean_box(v___x_1387_);
v___x_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
case 1:
{
lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1398_; 
v_isSharedCheck_1398_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1398_ == 0)
{
lean_object* v_unused_1399_; 
v_unused_1399_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1399_);
v___x_1391_ = v_x_1384_;
v_isShared_1392_ = v_isSharedCheck_1398_;
goto v_resetjp_1390_;
}
else
{
lean_dec(v_x_1384_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1398_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v_date_1393_; lean_object* v_year_1394_; lean_object* v___x_1396_; 
v_date_1393_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1393_);
lean_dec_ref(v_date_1382_);
v_year_1394_ = lean_ctor_get(v_date_1393_, 0);
lean_inc(v_year_1394_);
lean_dec_ref(v_date_1393_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v_year_1394_);
v___x_1396_ = v___x_1391_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_year_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
case 2:
{
lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1408_; 
v_isSharedCheck_1408_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1409_);
v___x_1401_ = v_x_1384_;
v_isShared_1402_ = v_isSharedCheck_1408_;
goto v_resetjp_1400_;
}
else
{
lean_dec(v_x_1384_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1408_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_date_1403_; lean_object* v_year_1404_; lean_object* v___x_1406_; 
v_date_1403_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1403_);
lean_dec_ref(v_date_1382_);
v_year_1404_ = lean_ctor_get(v_date_1403_, 0);
lean_inc(v_year_1404_);
lean_dec_ref(v_date_1403_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set_tag(v___x_1401_, 1);
lean_ctor_set(v___x_1401_, 0, v_year_1404_);
v___x_1406_ = v___x_1401_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_year_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
case 3:
{
lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1419_; 
v_isSharedCheck_1419_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1419_ == 0)
{
lean_object* v_unused_1420_; 
v_unused_1420_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1420_);
v___x_1411_ = v_x_1384_;
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
else
{
lean_dec(v_x_1384_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1419_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
uint8_t v_firstDayOfWeek_1413_; lean_object* v_date_1414_; lean_object* v___x_1415_; lean_object* v___x_1417_; 
v_firstDayOfWeek_1413_ = lean_ctor_get_uint8(v_locale_1383_, sizeof(void*)*1);
v_date_1414_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1414_);
lean_dec_ref(v_date_1382_);
v___x_1415_ = l_Std_Time_PlainDate_weekYear(v_date_1414_, v_firstDayOfWeek_1413_);
if (v_isShared_1412_ == 0)
{
lean_ctor_set_tag(v___x_1411_, 1);
lean_ctor_set(v___x_1411_, 0, v___x_1415_);
v___x_1417_ = v___x_1411_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
case 4:
{
lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1472_; 
v_isSharedCheck_1472_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1473_);
v___x_1422_ = v_x_1384_;
v_isShared_1423_ = v_isSharedCheck_1472_;
goto v_resetjp_1421_;
}
else
{
lean_dec(v_x_1384_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1472_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_date_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1470_; 
v_date_1424_ = lean_ctor_get(v_date_1382_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_date_1382_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v_date_1382_, 1);
lean_dec(v_unused_1471_);
v___x_1426_ = v_date_1382_;
v_isShared_1427_ = v_isSharedCheck_1470_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_date_1424_);
lean_dec(v_date_1382_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1470_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v_year_1428_; lean_object* v_month_1429_; lean_object* v_day_1430_; uint8_t v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1444_; uint8_t v___y_1445_; lean_object* v___y_1446_; uint8_t v___y_1451_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; uint8_t v___x_1466_; 
v_year_1428_ = lean_ctor_get(v_date_1424_, 0);
lean_inc(v_year_1428_);
v_month_1429_ = lean_ctor_get(v_date_1424_, 1);
lean_inc(v_month_1429_);
v_day_1430_ = lean_ctor_get(v_date_1424_, 2);
lean_inc(v_day_1430_);
lean_dec_ref(v_date_1424_);
v___x_1459_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1460_ = lean_int_mod(v_year_1428_, v___x_1459_);
v___x_1461_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1466_ = lean_int_dec_eq(v___x_1460_, v___x_1461_);
lean_dec(v___x_1460_);
if (v___x_1466_ == 0)
{
v___y_1451_ = v___x_1466_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1467_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1468_ = lean_int_mod(v_year_1428_, v___x_1467_);
v___x_1469_ = lean_int_dec_eq(v___x_1468_, v___x_1461_);
lean_dec(v___x_1468_);
if (v___x_1469_ == 0)
{
if (v___x_1466_ == 0)
{
goto v___jp_1462_;
}
else
{
v___y_1451_ = v___x_1466_;
goto v___jp_1450_;
}
}
else
{
goto v___jp_1462_;
}
}
v___jp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 1, v_day_1430_);
lean_ctor_set(v___x_1426_, 0, v_month_1429_);
v___x_1435_ = v___x_1426_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_month_1429_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_day_1430_);
v___x_1435_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1436_ = l_Std_Time_ValidDate_dayOfYear(v___y_1433_, v___x_1435_);
lean_dec_ref(v___x_1435_);
v___x_1437_ = lean_box(v___y_1432_);
v___x_1438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___x_1436_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set_tag(v___x_1422_, 1);
lean_ctor_set(v___x_1422_, 0, v___x_1438_);
v___x_1440_ = v___x_1422_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
v___jp_1443_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v___x_1447_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1448_ = lean_int_mod(v___y_1446_, v___x_1447_);
lean_dec(v___y_1446_);
v___x_1449_ = lean_int_dec_eq(v___x_1448_, v___y_1444_);
lean_dec(v___x_1448_);
v___y_1432_ = v___y_1445_;
v___y_1433_ = v___x_1449_;
goto v___jp_1431_;
}
v___jp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1452_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__0, &l_Std_Time_PlainDate_format___lam__0___closed__0_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__0);
v___x_1453_ = lean_int_mod(v_year_1428_, v___x_1452_);
v___x_1454_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1455_ = lean_int_dec_eq(v___x_1453_, v___x_1454_);
lean_dec(v___x_1453_);
if (v___x_1455_ == 0)
{
lean_dec(v_year_1428_);
v___y_1432_ = v___y_1451_;
v___y_1433_ = v___x_1455_;
goto v___jp_1431_;
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; uint8_t v___x_1458_; 
v___x_1456_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__3, &l_Std_Time_PlainDate_format___lam__0___closed__3_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__3);
v___x_1457_ = lean_int_mod(v_year_1428_, v___x_1456_);
v___x_1458_ = lean_int_dec_eq(v___x_1457_, v___x_1454_);
lean_dec(v___x_1457_);
if (v___x_1458_ == 0)
{
if (v___x_1455_ == 0)
{
v___y_1444_ = v___x_1454_;
v___y_1445_ = v___y_1451_;
v___y_1446_ = v_year_1428_;
goto v___jp_1443_;
}
else
{
lean_dec(v_year_1428_);
v___y_1432_ = v___y_1451_;
v___y_1433_ = v___x_1455_;
goto v___jp_1431_;
}
}
else
{
v___y_1444_ = v___x_1454_;
v___y_1445_ = v___y_1451_;
v___y_1446_ = v_year_1428_;
goto v___jp_1443_;
}
}
}
v___jp_1462_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1463_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__2, &l_Std_Time_PlainDate_format___lam__0___closed__2_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__2);
v___x_1464_ = lean_int_mod(v_year_1428_, v___x_1463_);
v___x_1465_ = lean_int_dec_eq(v___x_1464_, v___x_1461_);
lean_dec(v___x_1464_);
v___y_1451_ = v___x_1465_;
goto v___jp_1450_;
}
}
}
}
case 7:
{
lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1482_; 
v_isSharedCheck_1482_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1482_ == 0)
{
lean_object* v_unused_1483_; 
v_unused_1483_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1483_);
v___x_1475_ = v_x_1384_;
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v_x_1384_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v_date_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v_date_1477_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1477_);
lean_dec_ref(v_date_1382_);
v___x_1478_ = l_Std_Time_PlainDate_quarter(v_date_1477_);
lean_dec_ref(v_date_1477_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set_tag(v___x_1475_, 1);
lean_ctor_set(v___x_1475_, 0, v___x_1478_);
v___x_1480_ = v___x_1475_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
case 8:
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1493_; 
v_isSharedCheck_1493_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1494_);
v___x_1485_ = v_x_1384_;
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v_x_1384_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1493_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
uint8_t v_firstDayOfWeek_1487_; lean_object* v_date_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v_firstDayOfWeek_1487_ = lean_ctor_get_uint8(v_locale_1383_, sizeof(void*)*1);
v_date_1488_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1488_);
lean_dec_ref(v_date_1382_);
v___x_1489_ = l_Std_Time_PlainDate_weekOfYear(v_date_1488_, v_firstDayOfWeek_1487_);
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
case 9:
{
lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1504_; 
v_isSharedCheck_1504_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1505_);
v___x_1496_ = v_x_1384_;
v_isShared_1497_ = v_isSharedCheck_1504_;
goto v_resetjp_1495_;
}
else
{
lean_dec(v_x_1384_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1504_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
uint8_t v_firstDayOfWeek_1498_; lean_object* v_date_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
v_firstDayOfWeek_1498_ = lean_ctor_get_uint8(v_locale_1383_, sizeof(void*)*1);
v_date_1499_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1499_);
lean_dec_ref(v_date_1382_);
v___x_1500_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_1499_, v_firstDayOfWeek_1498_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 1);
lean_ctor_set(v___x_1496_, 0, v___x_1500_);
v___x_1502_ = v___x_1496_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
case 5:
{
lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1514_; 
v_isSharedCheck_1514_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1515_);
v___x_1507_ = v_x_1384_;
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v_x_1384_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1514_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v_date_1509_; lean_object* v_month_1510_; lean_object* v___x_1512_; 
v_date_1509_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1509_);
lean_dec_ref(v_date_1382_);
v_month_1510_ = lean_ctor_get(v_date_1509_, 1);
lean_inc(v_month_1510_);
lean_dec_ref(v_date_1509_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set_tag(v___x_1507_, 1);
lean_ctor_set(v___x_1507_, 0, v_month_1510_);
v___x_1512_ = v___x_1507_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_month_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
case 6:
{
lean_object* v___x_1517_; uint8_t v_isShared_1518_; uint8_t v_isSharedCheck_1524_; 
v_isSharedCheck_1524_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1524_ == 0)
{
lean_object* v_unused_1525_; 
v_unused_1525_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1525_);
v___x_1517_ = v_x_1384_;
v_isShared_1518_ = v_isSharedCheck_1524_;
goto v_resetjp_1516_;
}
else
{
lean_dec(v_x_1384_);
v___x_1517_ = lean_box(0);
v_isShared_1518_ = v_isSharedCheck_1524_;
goto v_resetjp_1516_;
}
v_resetjp_1516_:
{
lean_object* v_date_1519_; lean_object* v_day_1520_; lean_object* v___x_1522_; 
v_date_1519_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1519_);
lean_dec_ref(v_date_1382_);
v_day_1520_ = lean_ctor_get(v_date_1519_, 2);
lean_inc(v_day_1520_);
lean_dec_ref(v_date_1519_);
if (v_isShared_1518_ == 0)
{
lean_ctor_set_tag(v___x_1517_, 1);
lean_ctor_set(v___x_1517_, 0, v_day_1520_);
v___x_1522_ = v___x_1517_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_day_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
case 10:
{
lean_object* v_date_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec_ref_known(v_x_1384_, 0);
v_date_1526_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1526_);
lean_dec_ref(v_date_1382_);
v___x_1527_ = l_Std_Time_PlainDate_weekday(v_date_1526_);
v___x_1528_ = lean_box(v___x_1527_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
case 11:
{
lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1539_; 
v_isSharedCheck_1539_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; 
v_unused_1540_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1540_);
v___x_1531_ = v_x_1384_;
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
else
{
lean_dec(v_x_1384_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1539_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v_date_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1537_; 
v_date_1533_ = lean_ctor_get(v_date_1382_, 0);
lean_inc_ref(v_date_1533_);
lean_dec_ref(v_date_1382_);
v___x_1534_ = l_Std_Time_PlainDate_weekday(v_date_1533_);
v___x_1535_ = lean_box(v___x_1534_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set_tag(v___x_1531_, 1);
lean_ctor_set(v___x_1531_, 0, v___x_1535_);
v___x_1537_ = v___x_1531_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1535_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
case 12:
{
lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1548_; 
v_isSharedCheck_1548_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; 
v_unused_1549_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1549_);
v___x_1542_ = v_x_1384_;
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
else
{
lean_dec(v_x_1384_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1548_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
v___x_1544_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_1382_);
lean_dec_ref(v_date_1382_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set_tag(v___x_1542_, 1);
lean_ctor_set(v___x_1542_, 0, v___x_1544_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
case 17:
{
lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1558_; 
v_isSharedCheck_1558_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1559_);
v___x_1551_ = v_x_1384_;
v_isShared_1552_ = v_isSharedCheck_1558_;
goto v_resetjp_1550_;
}
else
{
lean_dec(v_x_1384_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1558_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_time_1553_; lean_object* v_hour_1554_; lean_object* v___x_1556_; 
v_time_1553_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1553_);
lean_dec_ref(v_date_1382_);
v_hour_1554_ = lean_ctor_get(v_time_1553_, 0);
lean_inc(v_hour_1554_);
lean_dec_ref(v_time_1553_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 1);
lean_ctor_set(v___x_1551_, 0, v_hour_1554_);
v___x_1556_ = v___x_1551_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_hour_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
case 16:
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1569_; 
v_isSharedCheck_1569_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1570_);
v___x_1561_ = v_x_1384_;
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v_x_1384_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1569_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_time_1563_; lean_object* v_hour_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v_time_1563_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1563_);
lean_dec_ref(v_date_1382_);
v_hour_1564_ = lean_ctor_get(v_time_1563_, 0);
lean_inc(v_hour_1564_);
lean_dec_ref(v_time_1563_);
v___x_1565_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_1564_);
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
case 18:
{
lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1579_; 
v_isSharedCheck_1579_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1580_);
v___x_1572_ = v_x_1384_;
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
else
{
lean_dec(v_x_1384_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1579_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v_time_1574_; lean_object* v_minute_1575_; lean_object* v___x_1577_; 
v_time_1574_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1574_);
lean_dec_ref(v_date_1382_);
v_minute_1575_ = lean_ctor_get(v_time_1574_, 1);
lean_inc(v_minute_1575_);
lean_dec_ref(v_time_1574_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 1);
lean_ctor_set(v___x_1572_, 0, v_minute_1575_);
v___x_1577_ = v___x_1572_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_minute_1575_);
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
v_isSharedCheck_1589_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1590_);
v___x_1582_ = v_x_1384_;
v_isShared_1583_ = v_isSharedCheck_1589_;
goto v_resetjp_1581_;
}
else
{
lean_dec(v_x_1384_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1589_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v_time_1584_; lean_object* v_nanosecond_1585_; lean_object* v___x_1587_; 
v_time_1584_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1584_);
lean_dec_ref(v_date_1382_);
v_nanosecond_1585_ = lean_ctor_get(v_time_1584_, 3);
lean_inc(v_nanosecond_1585_);
lean_dec_ref(v_time_1584_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 1);
lean_ctor_set(v___x_1582_, 0, v_nanosecond_1585_);
v___x_1587_ = v___x_1582_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_nanosecond_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
case 19:
{
lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1599_; 
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1600_);
v___x_1592_ = v_x_1384_;
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
else
{
lean_dec(v_x_1384_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1599_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_time_1594_; lean_object* v_second_1595_; lean_object* v___x_1597_; 
v_time_1594_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1594_);
lean_dec_ref(v_date_1382_);
v_second_1595_ = lean_ctor_get(v_time_1594_, 2);
lean_inc(v_second_1595_);
lean_dec_ref(v_time_1594_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 1);
lean_ctor_set(v___x_1592_, 0, v_second_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_second_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
case 13:
{
lean_object* v_time_1601_; lean_object* v_hour_1602_; uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec_ref_known(v_x_1384_, 0);
v_time_1601_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1601_);
lean_dec_ref(v_date_1382_);
v_hour_1602_ = lean_ctor_get(v_time_1601_, 0);
lean_inc(v_hour_1602_);
lean_dec_ref(v_time_1601_);
v___x_1603_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_1602_);
lean_dec(v_hour_1602_);
v___x_1604_ = lean_box(v___x_1603_);
v___x_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
case 14:
{
lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1615_; 
v_isSharedCheck_1615_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; 
v_unused_1616_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1616_);
v___x_1607_ = v_x_1384_;
v_isShared_1608_ = v_isSharedCheck_1615_;
goto v_resetjp_1606_;
}
else
{
lean_dec(v_x_1384_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1615_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v_time_1609_; lean_object* v_hour_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v_time_1609_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1609_);
lean_dec_ref(v_date_1382_);
v_hour_1610_ = lean_ctor_get(v_time_1609_, 0);
lean_inc(v_hour_1610_);
lean_dec_ref(v_time_1609_);
v___x_1611_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_1610_);
lean_dec(v_hour_1610_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 1);
lean_ctor_set(v___x_1607_, 0, v___x_1611_);
v___x_1613_ = v___x_1607_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
case 15:
{
lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1627_; 
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1628_);
v___x_1618_ = v_x_1384_;
v_isShared_1619_ = v_isSharedCheck_1627_;
goto v_resetjp_1617_;
}
else
{
lean_dec(v_x_1384_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1627_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v_time_1620_; lean_object* v_hour_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v_time_1620_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1620_);
lean_dec_ref(v_date_1382_);
v_hour_1621_ = lean_ctor_get(v_time_1620_, 0);
lean_inc(v_hour_1621_);
lean_dec_ref(v_time_1620_);
v___x_1622_ = lean_obj_once(&l_Std_Time_PlainTime_format___lam__0___closed__0, &l_Std_Time_PlainTime_format___lam__0___closed__0_once, _init_l_Std_Time_PlainTime_format___lam__0___closed__0);
v___x_1623_ = lean_int_emod(v_hour_1621_, v___x_1622_);
lean_dec(v_hour_1621_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set_tag(v___x_1618_, 1);
lean_ctor_set(v___x_1618_, 0, v___x_1623_);
v___x_1625_ = v___x_1618_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
case 20:
{
lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1637_; 
v_isSharedCheck_1637_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1638_);
v___x_1630_ = v_x_1384_;
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
else
{
lean_dec(v_x_1384_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_time_1632_; lean_object* v_nanosecond_1633_; lean_object* v___x_1635_; 
v_time_1632_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1632_);
lean_dec_ref(v_date_1382_);
v_nanosecond_1633_ = lean_ctor_get(v_time_1632_, 3);
lean_inc(v_nanosecond_1633_);
lean_dec_ref(v_time_1632_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set_tag(v___x_1630_, 1);
lean_ctor_set(v___x_1630_, 0, v_nanosecond_1633_);
v___x_1635_ = v___x_1630_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_nanosecond_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
case 21:
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1647_; 
v_isSharedCheck_1647_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1648_);
v___x_1640_ = v_x_1384_;
v_isShared_1641_ = v_isSharedCheck_1647_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v_x_1384_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1647_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_time_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v_time_1642_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1642_);
lean_dec_ref(v_date_1382_);
v___x_1643_ = l_Std_Time_PlainTime_toMilliseconds(v_time_1642_);
lean_dec_ref(v_time_1642_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 0, v___x_1643_);
v___x_1645_ = v___x_1640_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
case 23:
{
lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1657_; 
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1384_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_x_1384_, 0);
lean_dec(v_unused_1658_);
v___x_1650_ = v_x_1384_;
v_isShared_1651_ = v_isSharedCheck_1657_;
goto v_resetjp_1649_;
}
else
{
lean_dec(v_x_1384_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1657_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v_time_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; 
v_time_1652_ = lean_ctor_get(v_date_1382_, 1);
lean_inc_ref(v_time_1652_);
lean_dec_ref(v_date_1382_);
v___x_1653_ = l_Std_Time_PlainTime_toNanoseconds(v_time_1652_);
lean_dec_ref(v_time_1652_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 1);
lean_ctor_set(v___x_1650_, 0, v___x_1653_);
v___x_1655_ = v___x_1650_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
default: 
{
lean_object* v___x_1659_; 
lean_dec(v_x_1384_);
lean_dec_ref(v_date_1382_);
v___x_1659_ = lean_box(0);
return v___x_1659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format___lam__0___boxed(lean_object* v_date_1660_, lean_object* v_locale_1661_, lean_object* v_x_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Std_Time_PlainDateTime_format___lam__0(v_date_1660_, v_locale_1661_, v_x_1662_);
lean_dec_ref(v_locale_1661_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_format(lean_object* v_date_1664_, lean_object* v_format_1665_, lean_object* v_locale_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v_format_1668_; 
v___x_1667_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1668_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1665_, v___x_1667_);
if (lean_obj_tag(v_format_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref(v_locale_1666_);
lean_dec_ref(v_date_1664_);
v_a_1669_ = lean_ctor_get(v_format_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref_known(v_format_1668_, 1);
v___x_1670_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1671_ = lean_string_append(v___x_1670_, v_a_1669_);
lean_dec(v_a_1669_);
return v___x_1671_;
}
else
{
lean_object* v_a_1672_; lean_object* v___f_1673_; lean_object* v_res_1674_; 
v_a_1672_ = lean_ctor_get(v_format_1668_, 0);
lean_inc(v_a_1672_);
lean_dec_ref_known(v_format_1668_, 1);
v___f_1673_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_format___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1673_, 0, v_date_1664_);
lean_closure_set(v___f_1673_, 1, v_locale_1666_);
v_res_1674_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_1672_, v___f_1673_);
if (lean_obj_tag(v_res_1674_) == 0)
{
lean_object* v___x_1675_; 
v___x_1675_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__1));
return v___x_1675_;
}
else
{
lean_object* v_val_1676_; 
v_val_1676_ = lean_ctor_get(v_res_1674_, 0);
lean_inc(v_val_1676_);
lean_dec_ref_known(v_res_1674_, 1);
return v_val_1676_;
}
}
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = l_Std_Time_TimeZone_GMT;
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromAscTimeString(lean_object* v_input_1679_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1681_ = l_Std_Time_Formats_ascTime;
v___x_1682_ = l_Std_Time_GenericFormat_parse(v___x_1680_, v___x_1681_, v_input_1679_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1682_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1682_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1700_; 
v_a_1691_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1693_ = v___x_1682_;
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1682_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_date_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v_date_1695_ = lean_ctor_get(v_a_1691_, 1);
lean_inc_ref(v_date_1695_);
lean_dec(v_a_1691_);
v___x_1696_ = lean_thunk_get_own(v_date_1695_);
lean_dec_ref(v_date_1695_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1696_);
v___x_1698_ = v___x_1693_;
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
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0(lean_object* v_pdt_1701_, lean_object* v_x_1702_){
_start:
{
lean_inc_ref(v_pdt_1701_);
return v_pdt_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(lean_object* v_pdt_1703_, lean_object* v_x_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Std_Time_PlainDateTime_toAscTimeString___lam__0(v_pdt_1703_, v_x_1704_);
lean_dec_ref(v_pdt_1703_);
return v_res_1705_;
}
}
static lean_object* _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__0(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_obj_once(&l_Std_Time_PlainDate_format___lam__0___closed__1, &l_Std_Time_PlainDate_format___lam__0___closed__1_once, _init_l_Std_Time_PlainDate_format___lam__0___closed__1);
v___x_1707_ = lean_int_neg(v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toAscTimeString(lean_object* v_pdt_1708_){
_start:
{
lean_object* v___x_1709_; lean_object* v_offset_1710_; lean_object* v___x_1711_; lean_object* v_second_1712_; lean_object* v_nano_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1734_; 
v___x_1709_ = l_Std_Time_TimeZone_UTC;
v_offset_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc_ref(v_pdt_1708_);
v___x_1711_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1708_);
v_second_1712_ = lean_ctor_get(v___x_1711_, 0);
v_nano_1713_ = lean_ctor_get(v___x_1711_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1715_ = v___x_1711_;
v_isShared_1716_ = v_isSharedCheck_1734_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_nano_1713_);
lean_inc(v_second_1712_);
lean_dec(v___x_1711_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1734_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___f_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v_tm_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___f_1717_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1717_, 0, v_pdt_1708_);
v___x_1718_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1719_ = l_Std_Time_Formats_ascTime;
v___x_1720_ = lean_int_neg(v_offset_1710_);
v___x_1721_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__0, &l_Std_Time_PlainDateTime_toAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__0);
v___x_1722_ = lean_obj_once(&l_Std_Time_ZonedDateTime_format___lam__0___closed__0, &l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0);
v___x_1723_ = lean_int_mul(v_second_1712_, v___x_1722_);
lean_dec(v_second_1712_);
v___x_1724_ = lean_int_add(v___x_1723_, v_nano_1713_);
lean_dec(v_nano_1713_);
lean_dec(v___x_1723_);
v___x_1725_ = lean_int_mul(v___x_1720_, v___x_1722_);
lean_dec(v___x_1720_);
v___x_1726_ = lean_int_add(v___x_1725_, v___x_1721_);
lean_dec(v___x_1725_);
v___x_1727_ = lean_int_add(v___x_1724_, v___x_1726_);
lean_dec(v___x_1726_);
lean_dec(v___x_1724_);
v_tm_1728_ = l_Std_Time_Duration_ofNanoseconds(v___x_1727_);
lean_dec(v___x_1727_);
v___x_1729_ = lean_mk_thunk(v___f_1717_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1729_);
lean_ctor_set(v___x_1715_, 0, v_tm_1728_);
v___x_1731_ = v___x_1715_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_tm_1728_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Std_Time_GenericFormat_format(v___x_1718_, v___x_1709_, v___x_1719_, v___x_1731_);
return v___x_1732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLongDateFormatString(lean_object* v_input_1735_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1737_ = l_Std_Time_Formats_longDateFormat;
v___x_1738_ = l_Std_Time_GenericFormat_parse(v___x_1736_, v___x_1737_, v_input_1735_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1756_; 
v_a_1747_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1749_ = v___x_1738_;
v_isShared_1750_ = v_isSharedCheck_1756_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1738_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1756_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_date_1751_; lean_object* v___x_1752_; lean_object* v___x_1754_; 
v_date_1751_ = lean_ctor_get(v_a_1747_, 1);
lean_inc_ref(v_date_1751_);
lean_dec(v_a_1747_);
v___x_1752_ = lean_thunk_get_own(v_date_1751_);
lean_dec_ref(v_date_1751_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1752_);
v___x_1754_ = v___x_1749_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1752_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLongDateFormatString(lean_object* v_pdt_1757_){
_start:
{
lean_object* v___x_1758_; lean_object* v_offset_1759_; lean_object* v___x_1760_; lean_object* v_second_1761_; lean_object* v_nano_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1783_; 
v___x_1758_ = l_Std_Time_TimeZone_UTC;
v_offset_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc_ref(v_pdt_1757_);
v___x_1760_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_1757_);
v_second_1761_ = lean_ctor_get(v___x_1760_, 0);
v_nano_1762_ = lean_ctor_get(v___x_1760_, 1);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1764_ = v___x_1760_;
v_isShared_1765_ = v_isSharedCheck_1783_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_nano_1762_);
lean_inc(v_second_1761_);
lean_dec(v___x_1760_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1783_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___f_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v_tm_1777_; lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___f_1766_ = lean_alloc_closure((void*)(l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1766_, 0, v_pdt_1757_);
v___x_1767_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1768_ = l_Std_Time_Formats_longDateFormat;
v___x_1769_ = lean_int_neg(v_offset_1759_);
v___x_1770_ = lean_obj_once(&l_Std_Time_PlainDateTime_toAscTimeString___closed__0, &l_Std_Time_PlainDateTime_toAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__0);
v___x_1771_ = lean_obj_once(&l_Std_Time_ZonedDateTime_format___lam__0___closed__0, &l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once, _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0);
v___x_1772_ = lean_int_mul(v_second_1761_, v___x_1771_);
lean_dec(v_second_1761_);
v___x_1773_ = lean_int_add(v___x_1772_, v_nano_1762_);
lean_dec(v_nano_1762_);
lean_dec(v___x_1772_);
v___x_1774_ = lean_int_mul(v___x_1769_, v___x_1771_);
lean_dec(v___x_1769_);
v___x_1775_ = lean_int_add(v___x_1774_, v___x_1770_);
lean_dec(v___x_1774_);
v___x_1776_ = lean_int_add(v___x_1773_, v___x_1775_);
lean_dec(v___x_1775_);
lean_dec(v___x_1773_);
v_tm_1777_ = l_Std_Time_Duration_ofNanoseconds(v___x_1776_);
lean_dec(v___x_1776_);
v___x_1778_ = lean_mk_thunk(v___f_1766_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1778_);
lean_ctor_set(v___x_1764_, 0, v_tm_1777_);
v___x_1780_ = v___x_1764_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_tm_1777_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v___x_1778_);
v___x_1780_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Std_Time_GenericFormat_format(v___x_1767_, v___x_1758_, v___x_1768_, v___x_1780_);
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromDateTimeString(lean_object* v_input_1784_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1786_ = l_Std_Time_Formats_dateTime24Hour;
v___x_1787_ = l_Std_Time_GenericFormat_parse(v___x_1785_, v___x_1786_, v_input_1784_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1805_; 
v_a_1796_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1798_ = v___x_1787_;
v_isShared_1799_ = v_isSharedCheck_1805_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1787_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1805_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v_date_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v_date_1800_ = lean_ctor_get(v_a_1796_, 1);
lean_inc_ref(v_date_1800_);
lean_dec(v_a_1796_);
v___x_1801_ = lean_thunk_get_own(v_date_1800_);
lean_dec_ref(v_date_1800_);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 0, v___x_1801_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
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
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toDateTimeString(lean_object* v_pdt_1806_){
_start:
{
lean_object* v_date_1807_; lean_object* v_time_1808_; lean_object* v_year_1809_; lean_object* v_month_1810_; lean_object* v_day_1811_; lean_object* v_hour_1812_; lean_object* v_minute_1813_; lean_object* v_second_1814_; lean_object* v_nanosecond_1815_; lean_object* v___x_1816_; lean_object* v___x_12__overap_1817_; lean_object* v___x_1818_; 
v_date_1807_ = lean_ctor_get(v_pdt_1806_, 0);
lean_inc_ref(v_date_1807_);
v_time_1808_ = lean_ctor_get(v_pdt_1806_, 1);
lean_inc_ref(v_time_1808_);
lean_dec_ref(v_pdt_1806_);
v_year_1809_ = lean_ctor_get(v_date_1807_, 0);
lean_inc(v_year_1809_);
v_month_1810_ = lean_ctor_get(v_date_1807_, 1);
lean_inc(v_month_1810_);
v_day_1811_ = lean_ctor_get(v_date_1807_, 2);
lean_inc(v_day_1811_);
lean_dec_ref(v_date_1807_);
v_hour_1812_ = lean_ctor_get(v_time_1808_, 0);
lean_inc(v_hour_1812_);
v_minute_1813_ = lean_ctor_get(v_time_1808_, 1);
lean_inc(v_minute_1813_);
v_second_1814_ = lean_ctor_get(v_time_1808_, 2);
lean_inc(v_second_1814_);
v_nanosecond_1815_ = lean_ctor_get(v_time_1808_, 3);
lean_inc(v_nanosecond_1815_);
lean_dec_ref(v_time_1808_);
v___x_1816_ = l_Std_Time_Formats_dateTime24Hour;
v___x_12__overap_1817_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1816_);
v___x_1818_ = lean_apply_7(v___x_12__overap_1817_, v_year_1809_, v_month_1810_, v_day_1811_, v_hour_1812_, v_minute_1813_, v_second_1814_, v_nanosecond_1815_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_fromLeanDateTimeString(lean_object* v_input_1819_){
_start:
{
lean_object* v___y_1821_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1841_ = l_Std_Time_Formats_leanDateTime24Hour;
lean_inc_ref(v_input_1819_);
v___x_1842_ = l_Std_Time_GenericFormat_parse(v___x_1840_, v___x_1841_, v_input_1819_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec_ref_known(v___x_1842_, 1);
v___x_1843_ = l_Std_Time_Formats_leanDateTime24HourNoNanos;
v___x_1844_ = l_Std_Time_GenericFormat_parse(v___x_1840_, v___x_1843_, v_input_1819_);
v___y_1821_ = v___x_1844_;
goto v___jp_1820_;
}
else
{
lean_dec_ref(v_input_1819_);
v___y_1821_ = v___x_1842_;
goto v___jp_1820_;
}
v___jp_1820_:
{
if (lean_obj_tag(v___y_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___y_1821_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___y_1821_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___y_1821_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___y_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1839_; 
v_a_1830_ = lean_ctor_get(v___y_1821_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___y_1821_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1832_ = v___y_1821_;
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___y_1821_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_date_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v_date_1834_ = lean_ctor_get(v_a_1830_, 1);
lean_inc_ref(v_date_1834_);
lean_dec(v_a_1830_);
v___x_1835_ = lean_thunk_get_own(v_date_1834_);
lean_dec_ref(v_date_1834_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1835_);
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_toLeanDateTimeString(lean_object* v_pdt_1845_){
_start:
{
lean_object* v_date_1846_; lean_object* v_time_1847_; lean_object* v_year_1848_; lean_object* v_month_1849_; lean_object* v_day_1850_; lean_object* v_hour_1851_; lean_object* v_minute_1852_; lean_object* v_second_1853_; lean_object* v_nanosecond_1854_; lean_object* v___x_1855_; lean_object* v___x_12__overap_1856_; lean_object* v___x_1857_; 
v_date_1846_ = lean_ctor_get(v_pdt_1845_, 0);
lean_inc_ref(v_date_1846_);
v_time_1847_ = lean_ctor_get(v_pdt_1845_, 1);
lean_inc_ref(v_time_1847_);
lean_dec_ref(v_pdt_1845_);
v_year_1848_ = lean_ctor_get(v_date_1846_, 0);
lean_inc(v_year_1848_);
v_month_1849_ = lean_ctor_get(v_date_1846_, 1);
lean_inc(v_month_1849_);
v_day_1850_ = lean_ctor_get(v_date_1846_, 2);
lean_inc(v_day_1850_);
lean_dec_ref(v_date_1846_);
v_hour_1851_ = lean_ctor_get(v_time_1847_, 0);
lean_inc(v_hour_1851_);
v_minute_1852_ = lean_ctor_get(v_time_1847_, 1);
lean_inc(v_minute_1852_);
v_second_1853_ = lean_ctor_get(v_time_1847_, 2);
lean_inc(v_second_1853_);
v_nanosecond_1854_ = lean_ctor_get(v_time_1847_, 3);
lean_inc(v_nanosecond_1854_);
lean_dec_ref(v_time_1847_);
v___x_1855_ = l_Std_Time_Formats_leanDateTime24Hour;
v___x_12__overap_1856_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_1855_);
v___x_1857_ = lean_apply_7(v___x_12__overap_1856_, v_year_1848_, v_month_1849_, v_day_1850_, v_hour_1851_, v_minute_1852_, v_second_1853_, v_nanosecond_1854_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_parse(lean_object* v_date_1858_){
_start:
{
lean_object* v___x_1859_; 
lean_inc_ref(v_date_1858_);
v___x_1859_ = l_Std_Time_PlainDateTime_fromAscTimeString(v_date_1858_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref_known(v___x_1859_, 1);
lean_inc_ref(v_date_1858_);
v___x_1860_ = l_Std_Time_PlainDateTime_fromLongDateFormatString(v_date_1858_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref_known(v___x_1860_, 1);
lean_inc_ref(v_date_1858_);
v___x_1861_ = l_Std_Time_PlainDateTime_fromDateTimeString(v_date_1858_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref_known(v___x_1861_, 1);
v___x_1862_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v_date_1858_);
return v___x_1862_;
}
else
{
lean_dec_ref(v_date_1858_);
return v___x_1861_;
}
}
else
{
lean_dec_ref(v_date_1858_);
return v___x_1860_;
}
}
else
{
lean_dec_ref(v_date_1858_);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0(lean_object* v_data_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1870_ = ((lean_object*)(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1));
v___x_1871_ = l_Std_Time_PlainDateTime_toLeanDateTimeString(v_data_1868_);
v___x_1872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
v___x_1873_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1870_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = ((lean_object*)(l_Std_Time_PlainDate_instRepr___lam__0___closed__3));
v___x_1875_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l_Repr_addAppParen(v___x_1875_, v___y_1869_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_PlainDateTime_instRepr___lam__0___boxed(lean_object* v_data_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Std_Time_PlainDateTime_instRepr___lam__0(v_data_1877_, v___y_1878_);
lean_dec(v___y_1878_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format(lean_object* v_tz_1882_, lean_object* v_data_1883_, lean_object* v_format_1884_){
_start:
{
lean_object* v___x_1885_; lean_object* v_format_1886_; 
v___x_1885_ = lean_obj_once(&l_Std_Time_Formats_iso8601___closed__0, &l_Std_Time_Formats_iso8601___closed__0_once, _init_l_Std_Time_Formats_iso8601___closed__0);
v_format_1886_ = l_Std_Time_GenericFormat_spec___redArg(v_format_1884_, v___x_1885_);
if (lean_obj_tag(v_format_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_dec_ref(v_data_1883_);
v_a_1887_ = lean_ctor_get(v_format_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v_format_1886_, 1);
v___x_1888_ = ((lean_object*)(l_Std_Time_PlainDate_format___closed__0));
v___x_1889_ = lean_string_append(v___x_1888_, v_a_1887_);
lean_dec(v_a_1887_);
return v___x_1889_;
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v_a_1890_ = lean_ctor_get(v_format_1886_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v_format_1886_, 1);
v___x_1891_ = lean_box(1);
v___x_1892_ = l_Std_Time_GenericFormat_format(v___x_1891_, v_tz_1882_, v_a_1890_, v_data_1883_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_format___boxed(lean_object* v_tz_1893_, lean_object* v_data_1894_, lean_object* v_format_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_Time_DateTime_format(v_tz_1893_, v_data_1894_, v_format_1895_);
lean_dec_ref(v_tz_1893_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromAscTimeString(lean_object* v_input_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1899_ = l_Std_Time_Formats_ascTime;
v___x_1900_ = l_Std_Time_GenericFormat_parse(v___x_1898_, v___x_1899_, v_input_1897_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toAscTimeString(lean_object* v_datetime_1901_){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1902_ = l_Std_Time_TimeZone_GMT;
v___x_1903_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1904_ = l_Std_Time_Formats_ascTime;
v___x_1905_ = l_Std_Time_GenericFormat_format(v___x_1903_, v___x_1902_, v___x_1904_, v_datetime_1901_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_fromLongDateFormatString(lean_object* v_input_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1908_ = l_Std_Time_Formats_longDateFormat;
v___x_1909_ = l_Std_Time_GenericFormat_parse(v___x_1907_, v___x_1908_, v_input_1906_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLongDateFormatString(lean_object* v_datetime_1910_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1911_ = l_Std_Time_TimeZone_GMT;
v___x_1912_ = lean_obj_once(&l_Std_Time_PlainDateTime_fromAscTimeString___closed__0, &l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once, _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0);
v___x_1913_ = l_Std_Time_Formats_longDateFormat;
v___x_1914_ = l_Std_Time_GenericFormat_format(v___x_1912_, v___x_1911_, v___x_1913_, v_datetime_1910_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String(lean_object* v_tz_1915_, lean_object* v_date_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_box(1);
v___x_1918_ = l_Std_Time_Formats_iso8601;
v___x_1919_ = l_Std_Time_GenericFormat_format(v___x_1917_, v_tz_1915_, v___x_1918_, v_date_1916_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toISO8601String___boxed(lean_object* v_tz_1920_, lean_object* v_date_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Std_Time_DateTime_toISO8601String(v_tz_1920_, v_date_1921_);
lean_dec_ref(v_tz_1920_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String(lean_object* v_tz_1923_, lean_object* v_date_1924_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_box(1);
v___x_1926_ = l_Std_Time_Formats_rfc822;
v___x_1927_ = l_Std_Time_GenericFormat_format(v___x_1925_, v_tz_1923_, v___x_1926_, v_date_1924_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC822String___boxed(lean_object* v_tz_1928_, lean_object* v_date_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Std_Time_DateTime_toRFC822String(v_tz_1928_, v_date_1929_);
lean_dec_ref(v_tz_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String(lean_object* v_tz_1931_, lean_object* v_date_1932_){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = lean_box(1);
v___x_1934_ = l_Std_Time_Formats_rfc850;
v___x_1935_ = l_Std_Time_GenericFormat_format(v___x_1933_, v_tz_1931_, v___x_1934_, v_date_1932_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toRFC850String___boxed(lean_object* v_tz_1936_, lean_object* v_date_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Std_Time_DateTime_toRFC850String(v_tz_1936_, v_date_1937_);
lean_dec_ref(v_tz_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString(lean_object* v_tz_1939_, lean_object* v_pdt_1940_){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = lean_box(1);
v___x_1942_ = l_Std_Time_Formats_dateTimeWithZone;
v___x_1943_ = l_Std_Time_GenericFormat_format(v___x_1941_, v_tz_1939_, v___x_1942_, v_pdt_1940_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toDateTimeWithZoneString___boxed(lean_object* v_tz_1944_, lean_object* v_pdt_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Std_Time_DateTime_toDateTimeWithZoneString(v_tz_1944_, v_pdt_1945_);
lean_dec_ref(v_tz_1944_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString(lean_object* v_tz_1947_, lean_object* v_pdt_1948_){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = lean_box(1);
v___x_1950_ = l_Std_Time_Formats_leanDateTimeWithZone;
v___x_1951_ = l_Std_Time_GenericFormat_format(v___x_1949_, v_tz_1947_, v___x_1950_, v_pdt_1948_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_toLeanDateTimeWithZoneString___boxed(lean_object* v_tz_1952_, lean_object* v_pdt_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_tz_1952_, v_pdt_1953_);
lean_dec_ref(v_tz_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_parse(lean_object* v_date_1955_){
_start:
{
lean_object* v___x_1956_; 
lean_inc_ref(v_date_1955_);
v___x_1956_ = l_Std_Time_DateTime_fromAscTimeString(v_date_1955_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v___x_1957_; 
lean_dec_ref_known(v___x_1956_, 1);
v___x_1957_ = l_Std_Time_DateTime_fromLongDateFormatString(v_date_1955_);
return v___x_1957_;
}
else
{
lean_dec_ref(v_date_1955_);
return v___x_1956_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0(lean_object* v_tz_1958_, lean_object* v_data_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_tz_1958_, v_data_1959_);
v___x_1962_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
v___x_1963_ = l_Repr_addAppParen(v___x_1962_, v___y_1960_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr___lam__0___boxed(lean_object* v_tz_1964_, lean_object* v_data_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Std_Time_DateTime_instRepr___lam__0(v_tz_1964_, v_data_1965_, v___y_1966_);
lean_dec(v___y_1966_);
lean_dec_ref(v_tz_1964_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instRepr(lean_object* v_tz_1968_){
_start:
{
lean_object* v___f_1969_; 
v___f_1969_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_instRepr___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1969_, 0, v_tz_1968_);
return v___f_1969_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_DateTime_instToString(lean_object* v_tz_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_closure((void*)(l_Std_Time_DateTime_toLeanDateTimeWithZoneString___boxed), 2, 1);
lean_closure_set(v___x_1971_, 0, v_tz_1970_);
return v___x_1971_;
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

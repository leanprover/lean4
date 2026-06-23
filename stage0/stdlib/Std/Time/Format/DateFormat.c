// Lean compiler output
// Module: Std.Time.Format.DateFormat
// Imports: public import Init.Data.Vector.Extract public import Std.Time.Date.Unit.Weekday
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "January"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__0 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__0_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "February"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__1 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__1_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "March"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__2 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__2_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "April"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__3 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__3_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "May"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__4 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__4_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "June"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__5 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__5_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "July"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__6 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__6_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "August"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__7 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__7_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "September"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__8 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__8_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "October"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__9 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__9_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "November"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__10 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__10_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "December"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__11 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__11_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*12, .m_other = 0, .m_tag = 246}, .m_size = 12, .m_capacity = 12, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__0_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__1_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__2_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__3_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__4_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__5_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__6_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__7_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__8_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__9_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__10_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__11_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__12 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__12_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Jan"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__13 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__13_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Feb"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__14 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__14_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mar"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__15 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__15_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Apr"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__16 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__16_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Jun"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__17 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__17_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Jul"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__18 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__18_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Aug"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__19 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__19_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sep"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__20 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__20_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Oct"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__21 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__21_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nov"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__22 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__22_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dec"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__23 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__23_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*12, .m_other = 0, .m_tag = 246}, .m_size = 12, .m_capacity = 12, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__13_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__14_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__15_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__16_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__4_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__17_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__18_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__19_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__20_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__21_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__22_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__23_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__24 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__24_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "J"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__25 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__25_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "F"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__26 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__26_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "M"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__27 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__27_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "A"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__28 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__28_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "S"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__29 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__29_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "O"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__30 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__30_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "N"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__31 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__31_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "D"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__32 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__32_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*12, .m_other = 0, .m_tag = 246}, .m_size = 12, .m_capacity = 12, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__25_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__26_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__27_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__28_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__27_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__25_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__25_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__28_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__29_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__30_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__31_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__32_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__33 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__33_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Monday"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__34 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__34_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Tuesday"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__35 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__35_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Wednesday"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__36 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__36_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Thursday"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__37 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__37_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Friday"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__38 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__38_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Saturday"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__39 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__39_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Sunday"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__40 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__40_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__34_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__35_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__36_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__37_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__38_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__39_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__40_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__41 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__41_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mon"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__42 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__42_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Tue"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__43 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__43_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Wed"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__44 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__44_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Thu"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__45 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__45_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fri"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__46 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__46_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sat"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__47 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__47_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sun"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__48 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__48_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__42_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__43_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__44_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__45_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__46_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__47_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__48_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__49 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__49_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "T"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__50 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__50_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "W"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__51 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__51_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__27_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__50_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__51_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__50_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__26_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__29_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__29_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__52 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__52_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BCE"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__53 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__53_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "CE"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__54 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__54_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__53_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__54_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__55 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__55_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Before Common Era"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__56 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__56_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Common Era"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__57 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__57_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__56_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__57_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__58 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__58_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "B"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__59 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__59_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "C"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__60 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__60_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__59_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__60_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__61 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__61_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Q1"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__62 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__62_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Q2"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__63 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__63_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Q3"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__64 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__64_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Q4"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__65 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__65_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__62_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__63_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__64_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__65_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__66 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__66_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "1st quarter"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__67 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__67_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "2nd quarter"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__68 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__68_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "3rd quarter"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__69 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__69_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "4th quarter"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__70 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__70_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__67_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__68_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__69_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__70_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__71 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__71_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__72 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__72_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__73 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__73_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__74 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__74_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "4"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__75 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__75_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__72_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__73_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__74_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__75_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__76 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__76_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AM"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__77 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__77_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "PM"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__78 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__78_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Ante Meridiem"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__79 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__79_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Post Meridiem"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__80 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__80_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "P"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__81 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__81_value;
static const lean_ctor_object l_Std_Time_DateFormatSymbols_enUS___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*18 + 0, .m_other = 18, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__12_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__24_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__33_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__41_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__49_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__52_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__55_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__58_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__61_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__66_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__71_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__76_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__77_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__78_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__79_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__80_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__28_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__81_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__82 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__82_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateFormatSymbols_enUS = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__82_value;
static const lean_ctor_object l_Std_Time_DateFormat_enUS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__82_value),LEAN_SCALAR_PTR_LITERAL(6, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Time_DateFormat_enUS___closed__0 = (const lean_object*)&l_Std_Time_DateFormat_enUS___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateFormat_enUS = (const lean_object*)&l_Std_Time_DateFormat_enUS___closed__0_value;
lean_object* runtime_initialize_Init_Data_Vector_Extract(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Format_DateFormat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Vector_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Unit_Weekday(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Format_DateFormat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Vector_Extract(uint8_t builtin);
lean_object* initialize_Std_Time_Date_Unit_Weekday(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Format_DateFormat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Vector_Extract(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Weekday(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Format_DateFormat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Format_DateFormat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Format_DateFormat(builtin);
}
#ifdef __cplusplus
}
#endif

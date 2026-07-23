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
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprDayPeriodSymbols_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "am"};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__8_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pm"};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__10_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__10_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__11_value;
static const lean_string_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "noon"};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__13_value;
static lean_once_cell_t l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__14;
static const lean_string_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "midnight"};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__15 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__16_value;
static lean_once_cell_t l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__17;
static const lean_string_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__18 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__18_value;
static lean_once_cell_t l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__19;
static lean_once_cell_t l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__20;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__21 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__21_value;
static const lean_ctor_object l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__18_value)}};
static const lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__22 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__22_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriodSymbols_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprDayPeriodSymbols___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprDayPeriodSymbols_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprDayPeriodSymbols___closed__0 = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprDayPeriodSymbols = (const lean_object*)&l_Std_Time_instReprDayPeriodSymbols___closed__0_value;
static const lean_string_object l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__0 = (const lean_object*)&l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__0_value;
static const lean_ctor_object l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__0_value),((lean_object*)&l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__0_value),((lean_object*)&l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__0_value),((lean_object*)&l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__0_value)}};
static const lean_object* l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__1 = (const lean_object*)&l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Time_instInhabitedDayPeriodSymbols_default = (const lean_object*)&l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Std_Time_instInhabitedDayPeriodSymbols = (const lean_object*)&l_Std_Time_instInhabitedDayPeriodSymbols_default___closed__1_value;
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
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Mo"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__53 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__53_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Tu"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__54 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__54_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "We"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__55 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__55_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Th"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__56 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__56_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Fr"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__57 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__57_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Sa"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__58 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__58_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Su"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__59 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__59_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 246}, .m_size = 7, .m_capacity = 7, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__53_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__54_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__55_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__56_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__57_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__58_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__59_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__60 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__60_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "BC"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__61 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__61_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AD"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__62 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__62_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__61_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__62_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__63 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__63_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Before Christ"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__64 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__64_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Anno Domini"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__65 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__65_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__64_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__65_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__66 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__66_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "B"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__67 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__67_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__67_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__28_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__68 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__68_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Q1"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__69 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__69_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Q2"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__70 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__70_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Q3"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__71 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__71_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Q4"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__72 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__72_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__69_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__70_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__71_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__72_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__73 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__73_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "1st quarter"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__74 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__74_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "2nd quarter"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__75 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__75_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "3rd quarter"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__76 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__76_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "4th quarter"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__77 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__77_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__74_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__75_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__76_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__77_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__78 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__78_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__79 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__79_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__80 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__80_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "3"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__81 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__81_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "4"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__82 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__82_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__79_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__80_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__81_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__82_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__83 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__83_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "AM"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__84 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__84_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "PM"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__85 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__85_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ante meridiem"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__86 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__86_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "post meridiem"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__87 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__87_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__88 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__88_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "p"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__89 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__89_value;
static const lean_ctor_object l_Std_Time_DateFormatSymbols_enUS___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__84_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__85_value),((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__12_value),((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__90 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__90_value;
static const lean_ctor_object l_Std_Time_DateFormatSymbols_enUS___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__86_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__87_value),((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__12_value),((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__15_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__91 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__91_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__92 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__92_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mi"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__93 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__93_value;
static const lean_ctor_object l_Std_Time_DateFormatSymbols_enUS___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__88_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__89_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__92_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__93_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__94 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__94_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "at night"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__95 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__95_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "in the morning"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__96 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__96_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "in the afternoon"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__97 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__97_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "in the evening"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__98 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__98_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__15_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__95_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__96_value),((lean_object*)&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__12_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__97_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__98_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__99 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__99_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "night"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__100 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__100_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "morning"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__101 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__101_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "afternoon"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__102 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__102_value;
static const lean_string_object l_Std_Time_DateFormatSymbols_enUS___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "evening"};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__103 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__103_value;
static const lean_array_object l_Std_Time_DateFormatSymbols_enUS___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__93_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__100_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__101_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__92_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__102_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__103_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__104 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__104_value;
static const lean_ctor_object l_Std_Time_DateFormatSymbols_enUS___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*25 + 0, .m_other = 25, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__12_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__24_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__33_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__41_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__49_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__52_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__60_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__63_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__66_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__68_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__73_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__78_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__83_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__84_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__85_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__86_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__87_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__88_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__89_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__90_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__91_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__94_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__99_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__99_value),((lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__104_value)}};
static const lean_object* l_Std_Time_DateFormatSymbols_enUS___closed__105 = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__105_value;
LEAN_EXPORT const lean_object* l_Std_Time_DateFormatSymbols_enUS = (const lean_object*)&l_Std_Time_DateFormatSymbols_enUS___closed__105_value;
static lean_once_cell_t l_Std_Time_DateFormat_enUS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateFormat_enUS___closed__0;
static lean_once_cell_t l_Std_Time_DateFormat_enUS___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_DateFormat_enUS___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_DateFormat_enUS;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprDayPeriodSymbols_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(6u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = lean_unsigned_to_nat(8u);
v___x_28_ = lean_nat_to_int(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = lean_unsigned_to_nat(12u);
v___x_33_ = lean_nat_to_int(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = ((lean_object*)(l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__0));
v___x_36_ = lean_string_length(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_obj_once(&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__19, &l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__19_once, _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__19);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___redArg(lean_object* v_x_43_){
_start:
{
lean_object* v_am_44_; lean_object* v_pm_45_; lean_object* v_noon_46_; lean_object* v_midnight_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_am_44_ = lean_ctor_get(v_x_43_, 0);
lean_inc_ref(v_am_44_);
v_pm_45_ = lean_ctor_get(v_x_43_, 1);
lean_inc_ref(v_pm_45_);
v_noon_46_ = lean_ctor_get(v_x_43_, 2);
lean_inc_ref(v_noon_46_);
v_midnight_47_ = lean_ctor_get(v_x_43_, 3);
lean_inc_ref(v_midnight_47_);
lean_dec_ref(v_x_43_);
v___x_48_ = ((lean_object*)(l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__5));
v___x_49_ = ((lean_object*)(l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__6));
v___x_50_ = lean_obj_once(&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__7, &l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__7_once, _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__7);
v___x_51_ = l_String_quote(v_am_44_);
v___x_52_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
v___x_53_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_50_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = 0;
v___x_55_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_55_, 0, v___x_53_);
lean_ctor_set_uint8(v___x_55_, sizeof(void*)*1, v___x_54_);
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_49_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = ((lean_object*)(l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__9));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_box(1);
v___x_60_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set(v___x_60_, 1, v___x_59_);
v___x_61_ = ((lean_object*)(l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__11));
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_60_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_48_);
v___x_64_ = l_String_quote(v_pm_45_);
v___x_65_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
v___x_66_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_50_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*1, v___x_54_);
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_63_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_57_);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_59_);
v___x_71_ = ((lean_object*)(l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__13));
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_48_);
v___x_74_ = lean_obj_once(&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__14, &l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__14_once, _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__14);
v___x_75_ = l_String_quote(v_noon_46_);
v___x_76_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
v___x_77_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_74_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*1, v___x_54_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_73_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_57_);
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_59_);
v___x_82_ = ((lean_object*)(l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__16));
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_48_);
v___x_85_ = lean_obj_once(&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__17, &l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__17_once, _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__17);
v___x_86_ = l_String_quote(v_midnight_47_);
v___x_87_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
v___x_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_85_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_54_);
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_84_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_obj_once(&l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__20, &l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__20_once, _init_l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__20);
v___x_92_ = ((lean_object*)(l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__21));
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_90_);
v___x_94_ = ((lean_object*)(l_Std_Time_instReprDayPeriodSymbols_repr___redArg___closed__22));
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_91_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*1, v___x_54_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriodSymbols_repr(lean_object* v_x_98_, lean_object* v_prec_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Std_Time_instReprDayPeriodSymbols_repr___redArg(v_x_98_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprDayPeriodSymbols_repr___boxed(lean_object* v_x_101_, lean_object* v_prec_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_Time_instReprDayPeriodSymbols_repr(v_x_101_, v_prec_102_);
lean_dec(v_prec_102_);
return v_res_103_;
}
}
static lean_object* _init_l_Std_Time_DateFormat_enUS___closed__0(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_to_int(v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Std_Time_DateFormat_enUS___closed__1(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; 
v___x_453_ = ((lean_object*)(l_Std_Time_DateFormatSymbols_enUS));
v___x_454_ = lean_obj_once(&l_Std_Time_DateFormat_enUS___closed__0, &l_Std_Time_DateFormat_enUS___closed__0_once, _init_l_Std_Time_DateFormat_enUS___closed__0);
v___x_455_ = 6;
v___x_456_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_456_, 0, v___x_454_);
lean_ctor_set(v___x_456_, 1, v___x_453_);
lean_ctor_set_uint8(v___x_456_, sizeof(void*)*2, v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Std_Time_DateFormat_enUS(void){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_obj_once(&l_Std_Time_DateFormat_enUS___closed__1, &l_Std_Time_DateFormat_enUS___closed__1_once, _init_l_Std_Time_DateFormat_enUS___closed__1);
return v___x_457_;
}
}
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
l_Std_Time_DateFormat_enUS = _init_l_Std_Time_DateFormat_enUS();
lean_mark_persistent(l_Std_Time_DateFormat_enUS);
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
